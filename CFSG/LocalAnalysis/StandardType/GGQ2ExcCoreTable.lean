module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section

private def excTableC (τ : Tag) (k j : Fin τ.rank) : ℤ :=
  corootPair (Pi.single k 1) (Pi.single j 1)

private noncomputable def excTableB {m : Fin 6} {τ : Tag} (hdim : ExcRaw.dim m = τ.rank)
    {L : Type} [Field L] (ζ : Lˣ) (v : Fin τ.rank → ZMod 3) : Fin τ.rank → Lˣ :=
  fun j => ζ ^ (∑ k : Fin (ExcRaw.dim m),
    excTableC τ (Fin.cast hdim k) j * ((v (Fin.cast hdim k)).val : ℤ))

private noncomputable def excTablePhi {m : Fin 6} {τ : Tag} (hdim : ExcRaw.dim m = τ.rank)
    {L : Type} [Field L] (ζ : Lˣ) (v : Fin τ.rank → ZMod 3) : ModGL τ L :=
  rootDiagUnit τ (excTableB hdim ζ v)

private noncomputable def excTableReindex {m : Fin 6} {τ : Tag}
    (hdim : ExcRaw.dim m = τ.rank) : ExcRaw.V m ≃+ (Fin τ.rank → ZMod 3) where
  toFun v j := v (Fin.cast hdim.symm j)
  invFun u k := u (Fin.cast hdim k)
  left_inv v := by funext k; simp
  right_inv u := by funext j; simp
  map_add' v w := by funext j; rfl

private theorem excTableReindex_apply {m : Fin 6} {τ : Tag} (hdim : ExcRaw.dim m = τ.rank)
    (v : ExcRaw.V m) (j : Fin τ.rank) :
    excTableReindex hdim v j = v (Fin.cast hdim.symm j) := rfl

private theorem excTable_charP_two {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} (hS : NegLangTwo S) : CharP L 2 := by
  have halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (S.D.q ^ n) = c := hS.2.1
  obtain ⟨n, hn, hc⟩ := halg (-1)
  rw [hS.1] at hc
  have heven : Even (2 ^ n) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨m, rfl⟩
    rw [pow_succ]
    exact ⟨2 ^ m, by ring⟩
  obtain ⟨m, hm⟩ := heven
  have hone : (-1 : L) ^ (2 ^ n) = 1 := by
    rw [hm, show m + m = 2 * m by ring, pow_mul, neg_one_sq, one_pow]
  have hneg : (-1 : L) = 1 := hc ▸ hone
  have htwo : (2 : L) = 0 := by linear_combination -hneg
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo

private theorem excTable_zeta_zpow_eq_of_modEq {G : Type} [Group G] {ζ : G}
    (hζ : ζ ^ 3 = 1) {a b : ℤ} (h : a ≡ b [ZMOD 3]) : ζ ^ a = ζ ^ b := by
  have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hζ
  exact (zpow_eq_zpow_iff_modEq).mpr (Int.ModEq.of_dvd (by exact_mod_cast hdvd) h)

private theorem excTable_zmod_eq_of_zeta_zpow_eq {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1) {a b : ℤ} (h : ζ ^ a = ζ ^ b) :
    ((a : ZMod 3) = (b : ZMod 3)) := by
  have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hζ
  have hord : orderOf ζ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exfalso
      apply hζne
      exact orderOf_eq_one_iff.mp h1
    · exact h3
  have hmod : a ≡ b [ZMOD (orderOf ζ : ℤ)] := (zpow_eq_zpow_iff_modEq).mp h
  rw [hord] at hmod
  exact (ZMod.intCast_eq_intCast_iff a b 3).2 (by simpa using hmod)

private theorem excTable_int_modEq_of_intCast_eq {a b : ℤ}
    (h : (a : ZMod 3) = (b : ZMod 3)) : a ≡ b [ZMOD 3] :=
  (ZMod.intCast_eq_intCast_iff a b 3).1 h

private theorem excTable_val_add_modEq (a b : ZMod 3) :
    (((a + b).val : ℤ) ≡ (a.val : ℤ) + (b.val : ℤ) [ZMOD 3]) := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 3).1 ?_
  push_cast
  simp

private theorem excTable_sum_val_modEq {r d : ℕ} (hdim : d = r)
    (f : Fin r → ℤ) (u : Fin r → ZMod 3) :
    (∑ k : Fin d, f (Fin.cast hdim k) * ((u (Fin.cast hdim k)).val : ℤ)) ≡
      (((∑ k : Fin d, (f (Fin.cast hdim k) : ZMod 3) * u (Fin.cast hdim k)).val : ℤ))
        [ZMOD 3] := by
  refine excTable_int_modEq_of_intCast_eq ?_
  push_cast
  simp

private theorem excTable_rootDiagUnit_list_prod {τ : Tag} {L : Type} [Field L]
    {ι : Type*} (l : List ι) (f : ι → Fin τ.rank → Lˣ) :
    rootDiagUnit τ (l.map f).prod = (l.map fun i => rootDiagUnit τ (f i)).prod := by
  induction l with
  | nil => simp [rootDiagUnit_one]
  | cons a l ih => simp [rootDiagUnit_mul, ih]

private theorem excTable_list_prod_mem {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} {S : LangSetup τ L p} {ι : Type*} (l : List ι) (f : ι → ModGL τ L)
    (hf : ∀ i ∈ l, f i ∈ fullThreeTorus S) :
    (l.map f).prod ∈ fullThreeTorus S := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons]
      exact (fullThreeTorus S).mul_mem (hf a (by simp))
        (ih fun i hi => hf i (by simp [hi]))

private theorem excTableB_zero {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) (ζ : Lˣ) :
    excTableB hdim ζ (0 : Fin τ.rank → ZMod 3) = 1 := by
  funext j
  simp [excTableB]

private theorem excTablePhi_zero {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) (ζ : Lˣ) :
    excTablePhi hdim ζ (0 : Fin τ.rank → ZMod 3) = 1 := by
  rw [excTablePhi, excTableB_zero, rootDiagUnit_one]

private theorem excTable_exp_add_modEq {m : Fin 6} {τ : Tag}
    (hdim : ExcRaw.dim m = τ.rank) (C : Fin τ.rank → Fin τ.rank → ℤ)
    (v w : Fin τ.rank → ZMod 3) (j : Fin τ.rank) :
    (∑ k : Fin (ExcRaw.dim m),
        C (Fin.cast hdim k) j * (((v + w) (Fin.cast hdim k)).val : ℤ)) ≡
      (∑ k : Fin (ExcRaw.dim m),
        C (Fin.cast hdim k) j * ((v (Fin.cast hdim k)).val : ℤ)) +
      (∑ k : Fin (ExcRaw.dim m),
        C (Fin.cast hdim k) j * ((w (Fin.cast hdim k)).val : ℤ)) [ZMOD 3] := by
  rw [← Finset.sum_add_distrib]
  refine Int.ModEq.sum fun k _ => ?_
  calc
    C (Fin.cast hdim k) j * (((v + w) (Fin.cast hdim k)).val : ℤ)
        ≡ C (Fin.cast hdim k) j *
            (((v (Fin.cast hdim k)).val : ℤ) + ((w (Fin.cast hdim k)).val : ℤ))
            [ZMOD 3] := (excTable_val_add_modEq _ _).mul_left _
    _ = C (Fin.cast hdim k) j * ((v (Fin.cast hdim k)).val : ℤ) +
        C (Fin.cast hdim k) j * ((w (Fin.cast hdim k)).val : ℤ) := by ring

private theorem excTableB_add {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v w : Fin τ.rank → ZMod 3) :
    excTableB hdim ζ (v + w) = excTableB hdim ζ v * excTableB hdim ζ w := by
  funext j
  rw [Pi.mul_apply, excTableB, excTableB, excTableB, ← zpow_add]
  exact excTable_zeta_zpow_eq_of_modEq hζ (excTable_exp_add_modEq hdim (excTableC τ) v w j)

private theorem excTablePhi_add {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v w : Fin τ.rank → ZMod 3) :
    excTablePhi hdim ζ (v + w) = excTablePhi hdim ζ v * excTablePhi hdim ζ w := by
  rw [excTablePhi, excTablePhi, excTablePhi, excTableB_add hdim hζ, rootDiagUnit_mul]

private def excTableCm (τ : Tag) : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3) :=
  fun j l => (excTableC τ l j : ZMod 3)

private theorem excTable_inverse_matrix {τ : Tag}
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) :
    Cinv * excTableCm τ = 1 := by
  ext j l
  simpa [excTableCm, excTableC, Matrix.mul_apply, Matrix.one_apply] using hCinv j l

private theorem excTablePhi_injective {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) :
    Function.Injective (excTablePhi (L := L) hdim ζ) := by
  have hCinv' : Cinv * excTableCm τ = 1 := excTable_inverse_matrix Cinv hCinv
  have hmul : ∀ v : Fin τ.rank → ZMod 3,
      Matrix.mulVec Cinv (Matrix.mulVec (excTableCm τ) v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hCinv', Matrix.one_mulVec]
  intro u w huw
  have hb : excTableB hdim ζ u = excTableB hdim ζ w := by
    apply rootDiagUnit_injective
    simpa [excTablePhi] using huw
  have hz : ∀ j, Matrix.mulVec (excTableCm τ) u j = Matrix.mulVec (excTableCm τ) w j := by
    intro j
    have hpow : ζ ^ (∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) =
        ζ ^ (∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((w (Fin.cast hdim k)).val : ℤ)) :=
      congrFun hb j
    have hcast : (((∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) : ℤ) : ZMod 3) =
        (((∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((w (Fin.cast hdim k)).val : ℤ)) : ℤ) : ZMod 3) :=
      excTable_zmod_eq_of_zeta_zpow_eq hζ hζne hpow
    have hcast' : (∑ k : Fin (ExcRaw.dim m),
          (excTableC τ (Fin.cast hdim k) j : ZMod 3) * u (Fin.cast hdim k)) =
        (∑ k : Fin (ExcRaw.dim m),
          (excTableC τ (Fin.cast hdim k) j : ZMod 3) * w (Fin.cast hdim k)) := by
      simpa [ZMod.natCast_zmod_val] using hcast
    rw [Fin.sum_congr' (fun k : Fin τ.rank => (excTableC τ k j : ZMod 3) * u k) hdim,
      Fin.sum_congr' (fun k : Fin τ.rank => (excTableC τ k j : ZMod 3) * w k) hdim] at hcast'
    simpa [excTableCm, Matrix.mulVec, dotProduct] using hcast'
  calc
    u = Matrix.mulVec Cinv (Matrix.mulVec (excTableCm τ) u) := (hmul u).symm
    _ = Matrix.mulVec Cinv (Matrix.mulVec (excTableCm τ) w) := by rw [funext hz]
    _ = w := hmul w

private theorem excTable_exists_zpow_val_eq {τ : Tag} {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {a : Fin τ.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1) :
    ∃ y : Fin τ.rank → ZMod 3, (fun j => ζ ^ ((y j).val : ℤ)) = a := by
  have hlog : ∀ j, ∃ e : ℕ, e < 3 ∧ ζ ^ e = a j := fun j =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (a j)).2 (ha j))
  choose e he hea using hlog
  exact ⟨fun j => (e j : ZMod 3), funext fun j => by
    rw [ZMod.val_cast_of_lt (he j), zpow_natCast, hea j]⟩

private theorem excTable_recover {τ : Tag}
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0)
    (a : Fin τ.rank → ZMod 3) :
    ∀ j, (∑ k : Fin τ.rank, (excTableC τ k j : ZMod 3) * (Matrix.mulVec Cinv a) k) = a j := by
  have hCinv' : Cinv * excTableCm τ = 1 := excTable_inverse_matrix Cinv hCinv
  have hright : excTableCm τ * Cinv = 1 := mul_eq_one_comm.1 hCinv'
  have hdelta : ∀ j i : Fin τ.rank,
      (∑ k : Fin τ.rank, (excTableC τ k j : ZMod 3) * Cinv k i) =
        if j = i then 1 else 0 := by
    intro j i
    have h := congrArg (fun M : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3) => M j i) hright
    simpa [excTableCm, Matrix.mul_apply, Matrix.one_apply] using h
  intro j
  calc
    (∑ k : Fin τ.rank, (excTableC τ k j : ZMod 3) * (Matrix.mulVec Cinv a) k)
        = ∑ k : Fin τ.rank, ∑ i : Fin τ.rank,
            (excTableC τ k j : ZMod 3) * (Cinv k i * a i) := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ i : Fin τ.rank,
          (∑ k : Fin τ.rank, (excTableC τ k j : ZMod 3) * Cinv k i) * a i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i : Fin τ.rank, (if j = i then 1 else 0) * a i := by
          refine Finset.sum_congr rfl fun i _ => by rw [hdelta j i]
    _ = a j := by simp

private theorem excTablePhi_surjective_mem {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0)
    (t : ModGL τ L) (ht : t ∈ fullThreeTorus S) :
    ∃ v : Fin τ.rank → ZMod 3, excTablePhi hdim ζ v = t := by
  have hT : t ∈ torusGroup τ L := (inf_le_left : S.D.torus ≤ torusGroup τ L) ht.1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hb3 : ∀ j, b j ^ 3 = 1 := by
    have hpow : rootDiagUnit τ (b ^ 3) = rootDiagUnit τ (1 : Fin τ.rank → Lˣ) := by
      rw [← rootDiagUnit_pow, ← hb, ht.2, rootDiagUnit_one]
    have hb3' := rootDiagUnit_injective hpow
    intro j
    simpa using congrFun hb3' j
  have hζprim : IsPrimitiveRoot ζ 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime hζ hζne
  obtain ⟨a, ha⟩ := excTable_exists_zpow_val_eq (τ := τ) hζprim hb3
  let u : Fin τ.rank → ZMod 3 := Matrix.mulVec Cinv a
  have hrec : ∀ j, (∑ k : Fin τ.rank, (excTableC τ k j : ZMod 3) * u k) = a j :=
    excTable_recover Cinv hCinv a
  refine ⟨u, ?_⟩
  rw [hb, ← ha]
  change rootDiagUnit τ (excTableB hdim ζ u) =
    rootDiagUnit τ (fun j => ζ ^ ((a j).val : ℤ))
  congr 1
  funext j
  rw [excTableB]
  refine excTable_zeta_zpow_eq_of_modEq hζ (excTable_int_modEq_of_intCast_eq ?_)
  push_cast
  simp only [ZMod.natCast_zmod_val]
  exact (Fin.sum_congr' (f := fun k : Fin τ.rank => (excTableC τ k j : ZMod 3) * u k)
    hdim).trans (hrec j)

private theorem excTable_pairing_eq {m : Fin 6} {τ : Tag}
    (hdim : ExcRaw.dim m = τ.rank) (hm : m.val ≠ 3)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ) (hroot : ∀ i, IsRoot τ (γ i))
    (hF : ∀ i k, ExcRaw.F m i k = corootPair (Pi.single (Fin.cast hdim k) 1) (γ i))
    (hH : ∀ i (j : Fin τ.rank), corootPair (γ i) (Pi.single j 1) =
      ∑ k, ExcRaw.H m i k * corootPair (Pi.single (Fin.cast hdim k) 1) (Pi.single j 1))
    (i j : ExcRaw.Root m) :
    ExcRaw.pairing m i j = corootPair (γ j) (γ i) := by
  have hγsum : γ i = ∑ l, γ i l • (Pi.single l 1 : Fin τ.rank → ℤ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ k : Fin (ExcRaw.dim m),
      corootPair (Pi.single (Fin.cast hdim k) 1) (γ i) =
        ∑ l : Fin τ.rank, γ i l * excTableC τ (Fin.cast hdim k) l := by
    intro k
    conv_lhs => rw [hγsum]
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum
      (IsRoot.basis (Fin.cast hdim k)) Finset.univ (fun l => γ i l) (fun l => Pi.single l 1)]
    exact Finset.sum_congr rfl fun l _ => by simp [excTableC]
  rw [ExcRaw.pairing, if_neg hm]
  calc
    ∑ k, ExcRaw.F m i k * ExcRaw.H m j k
        = ∑ k, corootPair (Pi.single (Fin.cast hdim k) 1) (γ i) * ExcRaw.H m j k := by
          refine Finset.sum_congr rfl fun k _ => by rw [hF i k]
    _ = ∑ k, ExcRaw.H m j k *
          (∑ l : Fin τ.rank, γ i l * excTableC τ (Fin.cast hdim k) l) := by
          refine Finset.sum_congr rfl fun k _ => by rw [hlin k]; ring
    _ = ∑ l, γ i l *
          (∑ k, ExcRaw.H m j k * excTableC τ (Fin.cast hdim k) l) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by
            ring
    _ = ∑ l, γ i l * corootPair (γ j) (Pi.single l 1) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 1
          simpa [excTableC] using (hH j l).symm
    _ = corootPair (γ j) (γ i) := by
          conv_rhs => rw [hγsum]
          exact (CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum (hroot j) Finset.univ
            (fun l => γ i l) (fun l => Pi.single l 1)).symm

private theorem excTable_exp_identity {m : Fin 6} {τ : Tag}
    (hdim : ExcRaw.dim m = τ.rank) (γi : Fin τ.rank → ℤ) (u : Fin τ.rank → ZMod 3) :
    (∑ j : Fin τ.rank, (∑ k : Fin (ExcRaw.dim m),
        excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γi j) =
      ∑ k : Fin (ExcRaw.dim m), corootPair (Pi.single (Fin.cast hdim k) 1) γi *
        ((u (Fin.cast hdim k)).val : ℤ) := by
  have hγsum : γi = ∑ l, γi l • (Pi.single l 1 : Fin τ.rank → ℤ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ k : Fin (ExcRaw.dim m),
      corootPair (Pi.single (Fin.cast hdim k) 1) γi =
        ∑ l : Fin τ.rank, γi l * excTableC τ (Fin.cast hdim k) l := by
    intro k
    conv_lhs => rw [hγsum]
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum
      (IsRoot.basis (Fin.cast hdim k)) Finset.univ (fun l => γi l) (fun l => Pi.single l 1)]
    exact Finset.sum_congr rfl fun l _ => by simp [excTableC]
  calc
    (∑ j : Fin τ.rank, (∑ k : Fin (ExcRaw.dim m),
        excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γi j)
        = ∑ j : Fin τ.rank, ∑ k : Fin (ExcRaw.dim m),
            (excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γi j := by
          simp [Finset.sum_mul]
    _ = ∑ k : Fin (ExcRaw.dim m), ∑ j : Fin τ.rank,
            (excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γi j :=
          Finset.sum_comm
    _ = ∑ k : Fin (ExcRaw.dim m),
          (∑ j : Fin τ.rank, γi j * excTableC τ (Fin.cast hdim k) j) *
            ((u (Fin.cast hdim k)).val : ℤ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ k : Fin (ExcRaw.dim m),
          corootPair (Pi.single (Fin.cast hdim k) 1) γi *
            ((u (Fin.cast hdim k)).val : ℤ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hlin k]

private theorem excTable_rootChar_eq {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (hF : ∀ i k, ExcRaw.F m i k = corootPair (Pi.single (Fin.cast hdim k) 1) (γ i))
    (i : ExcRaw.Root m) (u : Fin τ.rank → ZMod 3) :
    rootChar (excTableB hdim ζ u) (γ i) =
      ζ ^ (ExcRaw.root m i ((excTableReindex hdim).symm u)).val := by
  have hroot : (∑ k : Fin (ExcRaw.dim m),
        ((corootPair (Pi.single (Fin.cast hdim k) 1) (γ i) : ℤ) : ZMod 3) *
          u (Fin.cast hdim k)) =
      ExcRaw.root m i ((excTableReindex hdim).symm u) := by
    rw [ExcRaw.root_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF i k]
    rfl
  have hx : rootChar (excTableB hdim ζ u) (γ i) =
      ζ ^ (∑ j : Fin τ.rank,
        (∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γ i j) := by
    have hb : excTableB hdim ζ u = fun j => ζ ^ (∑ k : Fin (ExcRaw.dim m),
        excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) := rfl
    rw [hb, rootChar_zpow]
    simp only [dotProduct]
  have hmod : (∑ j : Fin τ.rank,
        (∑ k : Fin (ExcRaw.dim m),
          excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γ i j) ≡
      ((ExcRaw.root m i ((excTableReindex hdim).symm u)).val : ℤ) [ZMOD 3] := by
    rw [excTable_exp_identity hdim (γ i) u]
    have h := excTable_sum_val_modEq hdim
      (fun k : Fin τ.rank => corootPair (Pi.single k 1) (γ i)) u
    rw [hroot] at h
    exact h
  calc
    rootChar (excTableB hdim ζ u) (γ i)
        = ζ ^ (∑ j : Fin τ.rank,
            (∑ k : Fin (ExcRaw.dim m),
              excTableC τ (Fin.cast hdim k) j * ((u (Fin.cast hdim k)).val : ℤ)) * γ i j) := hx
    _ = ζ ^ (((ExcRaw.root m i ((excTableReindex hdim).symm u)).val : ℕ) : ℤ) :=
          excTable_zeta_zpow_eq_of_modEq hζ hmod
    _ = ζ ^ (ExcRaw.root m i ((excTableReindex hdim).symm u)).val := by rw [zpow_natCast]

private theorem excTablePhi_coroot {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (hH : ∀ i (j : Fin τ.rank), corootPair (γ i) (Pi.single j 1) =
      ∑ k, ExcRaw.H m i k * corootPair (Pi.single (Fin.cast hdim k) 1) (Pi.single j 1))
    (i : ExcRaw.Root m) :
    excTablePhi hdim ζ (excTableReindex hdim (ExcRaw.coroot m i)) =
      rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)) := by
  change rootDiagUnit τ (excTableB hdim ζ (excTableReindex hdim (ExcRaw.coroot m i))) =
    rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1))
  congr 1
  funext j
  rw [excTableB]
  have hv : ∀ k : Fin (ExcRaw.dim m),
      excTableReindex hdim (ExcRaw.coroot m i) (Fin.cast hdim k) = ExcRaw.coroot m i k := by
    intro k
    rw [excTableReindex_apply]
    exact Fin.ext rfl
  simp only [hv]
  refine excTable_zeta_zpow_eq_of_modEq hζ (excTable_int_modEq_of_intCast_eq ?_)
  push_cast
  simp only [ZMod.natCast_zmod_val, ExcRaw.coroot]
  rw [hH i j]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [excTableC, mul_comm]

private theorem excTablePhi_mem {m : Fin 6} {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} {S : LangSetup τ L p}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin τ.rank → ZMod 3) :
    excTablePhi hdim ζ v ∈ fullThreeTorus S := by
  have hb : excTableB hdim ζ v = ∏ k : Fin (ExcRaw.dim m),
      (fun j => ζ ^ excTableC τ (Fin.cast hdim k) j) ^ ((v (Fin.cast hdim k)).val) := by
    funext j
    simp only [excTableB, Finset.prod_apply, Pi.pow_apply]
    simp_rw [← zpow_natCast, ← zpow_mul]
    rw [Finset.prod_zpow_eq_zpow_sum]
  rw [excTablePhi, hb, Fin.prod_univ_def, excTable_rootDiagUnit_list_prod]
  refine excTable_list_prod_mem (List.finRange (ExcRaw.dim m)) _ fun k _ => ?_
  rw [← rootDiagUnit_pow]
  exact (fullThreeTorus S).pow_mem
    (corootTuple_mem_fullThreeTorus S hτ hS.1 hS.2.2 (IsRoot.basis (Fin.cast hdim k)) hζ) _

private noncomputable def excTablePhiHom {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    ExcRaw.V m →+ Additive ↥(fullThreeTorus S) where
  toFun v := Additive.ofMul ⟨excTablePhi hdim ζ (excTableReindex hdim v),
    excTablePhi_mem hτ hS hdim hζ (excTableReindex hdim v)⟩
  map_zero' := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    show excTablePhi hdim ζ (excTableReindex hdim 0) = 1
    rw [(excTableReindex hdim).map_zero, excTablePhi_zero]
  map_add' v w := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    show excTablePhi hdim ζ (excTableReindex hdim (v + w)) =
      excTablePhi hdim ζ (excTableReindex hdim v) * excTablePhi hdim ζ (excTableReindex hdim w)
    rw [(excTableReindex hdim).map_add, excTablePhi_add hdim hζ]

private theorem excTablePhiHom_bijective {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) :
    Function.Bijective (excTablePhiHom hτ hS hdim hζ) := by
  constructor
  · intro u w huw
    have h : excTablePhi hdim ζ (excTableReindex hdim u) =
        excTablePhi hdim ζ (excTableReindex hdim w) := by
      simpa [excTablePhiHom] using congrArg (fun z : Additive ↥(fullThreeTorus S) =>
        ((Additive.toMul z : ↥(fullThreeTorus S)) : ModGL τ L)) huw
    exact (excTableReindex hdim).injective
      (excTablePhi_injective hdim hζ hζne Cinv hCinv h)
  · intro y
    obtain ⟨v, hv⟩ := excTablePhi_surjective_mem hdim hζ hζne Cinv hCinv
      ((Additive.toMul y : ↥(fullThreeTorus S)) : ModGL τ L) (Additive.toMul y).2
    refine ⟨(excTableReindex hdim).symm v, ?_⟩
    apply Additive.ofMul.injective
    apply Subtype.ext
    show excTablePhi hdim ζ (excTableReindex hdim ((excTableReindex hdim).symm v)) =
      ((Additive.toMul y : ↥(fullThreeTorus S)) : ModGL τ L)
    rw [(excTableReindex hdim).apply_symm_apply, hv]

private noncomputable def excTablePhiEquiv {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) :
    ExcRaw.V m ≃+ Additive ↥(fullThreeTorus S) :=
  AddEquiv.ofBijective (excTablePhiHom hτ hS hdim hζ)
    (excTablePhiHom_bijective hτ hS hdim hζ hζne Cinv hCinv)

private noncomputable def excTableCoord {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) :
    Additive ↥(fullThreeTorus S) ≃+ ExcRaw.V m :=
  (excTablePhiEquiv hτ hS hdim hζ hζne Cinv hCinv).symm

private theorem excTableCoord_apply_phi {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) (v : ExcRaw.V m) :
    excTableCoord hτ hS hdim hζ hζne Cinv hCinv (excTablePhiHom hτ hS hdim hζ v) = v :=
  AddEquiv.symm_apply_apply (excTablePhiEquiv hτ hS hdim hζ hζne Cinv hCinv) v

private theorem excTablePhiHom_coord {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) (y : Additive ↥(fullThreeTorus S)) :
    excTablePhiHom hτ hS hdim hζ
      (excTableCoord hτ hS hdim hζ hζne Cinv hCinv y) = y :=
  AddEquiv.apply_symm_apply (excTablePhiEquiv hτ hS hdim hζ hζne Cinv hCinv) y

private theorem excTablePhi_coord_eq {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0) (y : Additive ↥(fullThreeTorus S)) :
    excTablePhi hdim ζ (excTableReindex hdim
      (excTableCoord hτ hS hdim hζ hζne Cinv hCinv y)) =
        ((Additive.toMul y : ↥(fullThreeTorus S)) : ModGL τ L) := by
  have h := congrArg (fun z : Additive ↥(fullThreeTorus S) =>
    ((Additive.toMul z : ↥(fullThreeTorus S)) : ModGL τ L))
    (excTablePhiHom_coord hτ hS hdim hζ hζne Cinv hCinv y)
  simpa [excTablePhiHom] using h

private theorem excTable_rootChar_coord {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (hF : ∀ i k, ExcRaw.F m i k = corootPair (Pi.single (Fin.cast hdim k) 1) (γ i))
    (t : ↥(fullThreeTorus S)) (b : Fin τ.rank → Lˣ)
    (hb : (t : ModGL τ L) = rootDiagUnit τ b) (i : ExcRaw.Root m) :
    rootChar b (γ i) = ζ ^ (ExcRaw.root m i
      (excTableCoord hτ hS hdim hζ hζne Cinv hCinv (Additive.ofMul t))).val := by
  let v : ExcRaw.V m := excTableCoord hτ hS hdim hζ hζne Cinv hCinv (Additive.ofMul t)
  change rootChar b (γ i) = ζ ^ (ExcRaw.root m i v).val
  have hcoord := excTablePhi_coord_eq hτ hS hdim hζ hζne Cinv hCinv (Additive.ofMul t)
  have hcoord' : rootDiagUnit τ (excTableB hdim ζ (excTableReindex hdim v)) =
      (t : ModGL τ L) := hcoord
  have hb' : rootDiagUnit τ b = rootDiagUnit τ (excTableB hdim ζ (excTableReindex hdim v)) := by
    rw [← hb]
    exact hcoord'.symm
  have hb'' : b = excTableB hdim ζ (excTableReindex hdim v) := rootDiagUnit_injective hb'
  calc
    rootChar b (γ i)
        = rootChar (excTableB hdim ζ (excTableReindex hdim v)) (γ i) := by rw [hb'']
    _ = ζ ^ (ExcRaw.root m i ((excTableReindex hdim).symm (excTableReindex hdim v))).val :=
          excTable_rootChar_eq hdim hζ γ hF i (excTableReindex hdim v)
    _ = ζ ^ (ExcRaw.root m i v).val := by rw [AddEquiv.symm_apply_apply]

private theorem excTable_coord_coroot {m : Fin 6} {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p} {ζ : Lˣ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hS : NegLangTwo S)
    (hdim : ExcRaw.dim m = τ.rank) (hζ : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ) (hroot : ∀ i, IsRoot τ (γ i))
    (hH : ∀ i (j : Fin τ.rank), corootPair (γ i) (Pi.single j 1) =
      ∑ k, ExcRaw.H m i k * corootPair (Pi.single (Fin.cast hdim k) 1) (Pi.single j 1))
    (i : ExcRaw.Root m) :
    excTableCoord hτ hS hdim hζ hζne Cinv hCinv
      (Additive.ofMul ⟨rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)),
        corootTuple_mem_fullThreeTorus S hτ hS.1 hS.2.2 (hroot i) hζ⟩) =
      ExcRaw.coroot m i := by
  have hphi : excTablePhiHom hτ hS hdim hζ (ExcRaw.coroot m i) =
      Additive.ofMul ⟨rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)),
        corootTuple_mem_fullThreeTorus S hτ hS.1 hS.2.2 (hroot i) hζ⟩ := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    show excTablePhi hdim ζ (excTableReindex hdim (ExcRaw.coroot m i)) =
      rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1))
    exact excTablePhi_coroot hdim hζ γ hH i
  calc
    excTableCoord hτ hS hdim hζ hζne Cinv hCinv
        (Additive.ofMul ⟨rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)),
          corootTuple_mem_fullThreeTorus S hτ hS.1 hS.2.2 (hroot i) hζ⟩)
        = excTableCoord hτ hS hdim hζ hζne Cinv hCinv
            (excTablePhiHom hτ hS hdim hζ (ExcRaw.coroot m i)) := by rw [hphi]
    _ = ExcRaw.coroot m i :=
          excTableCoord_apply_phi hτ hS hdim hζ hζne Cinv hCinv _

theorem nonempty_excCoordDatum_of_table {m : Fin 6} {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hm : m.val ≠ 3)
    (hdim : ExcRaw.dim m = τ.rank) (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (hroot : ∀ i, IsRoot τ (γ i)) (hcover : ∀ δ, IsRoot τ δ → ∃ i, δ = γ i ∨ δ = -γ i)
    (hinj : ∀ i j, (γ i = γ j ∨ γ i = -γ j) → i = j)
    (hF : ∀ i k, ExcRaw.F m i k = corootPair (Pi.single (Fin.cast hdim k) 1) (γ i))
    (hH : ∀ i (j : Fin τ.rank), corootPair (γ i) (Pi.single j 1) =
      ∑ k, ExcRaw.H m i k * corootPair (Pi.single (Fin.cast hdim k) 1) (Pi.single j 1))
    (Cinv : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3))
    (hCinv : ∀ j l : Fin τ.rank,
      ∑ k, Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
        if j = l then 1 else 0)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hS : NegLangTwo S) :
    Nonempty (ExcCoordDatum S (fullThreeTorus S) m) := by
  have hchar : CharP L 2 := excTable_charP_two hS
  obtain ⟨ζ, hζ3, hζne⟩ := exists_primitive_cube_root (L := L)
  refine ⟨γ, ζ, excTableCoord hτ hS hdim hζ3 hζne Cinv hCinv, le_rfl, hζ3, hζne,
    hroot, hcover, hinj, ?_, ?_, ?_, ?_⟩
  · exact excTable_pairing_eq hdim hm γ hroot hF hH
  · intro t b hb i
    exact excTable_rootChar_coord hτ hS hdim hζ3 hζne Cinv hCinv γ hF t b hb i
  · exact fun i => corootTuple_mem_fullThreeTorus S hτ hS.1 hS.2.2 (hroot i) hζ3
  · intro i
    exact excTable_coord_coroot hτ hS hdim hζ3 hζne Cinv hCinv γ hroot hH i

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
