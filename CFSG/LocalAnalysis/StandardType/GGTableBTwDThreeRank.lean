module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThreeHerm
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.StandardType.TwDThree

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.LIT

variable {K : Type} [Field K] {n d p : ℕ}

theorem bar_eq_self_of_pow_eq_one (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n - 1) {c : K}
    (hc : c ^ p = 1) : h.bar c = c := by
  obtain ⟨m, hm⟩ := hpq
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [UnitaryFieldData.bar_apply, show (2 : ℕ) ^ n = 2 ^ n - 1 + 1 by omega, pow_succ, hm,
    pow_mul, hc, one_pow, one_mul]

theorem cast_ne_zero_of_ne_two (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : K) ≠ 0 := by
  have : CharP K 2 := h.charP
  intro h0
  rw [CharP.cast_eq_zero_iff K 2] at h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h0).symm

theorem coprime_two_pow_add_one (hp : p.Prime) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n - 1) :
    Nat.Coprime p (2 ^ n + 1) := by
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hn hpq
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd'
  have h1 : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hd' hpq
  have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h2] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)

theorem card_le_pow_half_of_unitary_gl (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (E : Subgroup (GL (Fin d) K)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) (hexp : ∀ g ∈ E, g ^ p = 1)
    (hU : ∀ g ∈ E,
      ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K) = 1) :
    Nat.card E ≤ p ^ (d / 2) := by
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one h.one_le hpq
  have : Finite (E.map (glAut (Fin d) K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut (Fin d) K) glAut_injective).toEquiv
  set B : (Fin d → K) →ₗ[K] (Fin d → K) →ₛₗ[h.bar] K :=
    (gramForm h (1 : Matrix (Fin d) (Fin d) K)).flip
  have hBapp : ∀ u v, B u v = gramForm h 1 v u := fun u v => rfl
  have hB : ∀ u : Fin d → K, (∀ w, B u w = 0) → u = 0 := by
    intro u hu
    funext j
    have h1 := hu (Pi.single j 1)
    have hs : (fun c => h.bar ((Pi.single j (1 : K) : Fin d → K) c)) = Pi.single j 1 := by
      funext c
      by_cases hc : c = j
      · subst hc
        simp
      · simp [hc]
    rw [hBapp, gramForm_apply, hs, Matrix.one_mulVec, single_dotProduct, one_mul] at h1
    exact h1
  have hpres : ∀ g ∈ E.map (glAut (Fin d) K), ∀ u w, B (g u) (g w) = B u w := by
    rintro _ ⟨a, ha, rfl⟩ u w
    rw [hBapp, hBapp, glAut_apply, glAut_apply, gramForm_mulVec, Matrix.mul_one, hU a ha]
  have hle := card_le_pow_half_of_sesq hp hp2 (cast_ne_zero_of_ne_two h hp hp2)
    (fun c hc => bar_eq_self_of_pow_eq_one h hpq hc) d (Fin d → K)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) B hB
    (E.map (glAut (Fin d) K)) (map_glAut_comm hcomm) (map_glAut_exp hexp) hpres
  rwa [card_map_glAut] at hle

theorem card_le_of_subset_unitaryConj [Finite K] (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    Nat.card X ≤ p ^ (d / 2) := by
  classical
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hd0 : NeZero d := ⟨by omega⟩
  have hbar : ∀ M : Matrix (Fin d) (Fin d) K, M.map h.bar = M.map (· ^ 2 ^ n) := fun M => by
    ext i j
    rfl
  set U : Subgroup (GL (Fin d) K) := TableB.unitGroup h.bar with hUdef
  have hUN : U ≤
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
    fun A hA => TableBUE.gu_subset_normalizer h ⟨1, one_ne_zero, one_pow _, by
      rw [one_smul, ← hbar]
      exact TableB.mem_unitGroup.mp hA⟩
  set κ : U →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))).comp (Subgroup.inclusion hUN) with hκ
  set Γ : Subgroup U := X.comap κ
  set π : Γ →* X := (κ.comp Γ.subtype).codRestrict X (fun g => g.2)
  have hq1 : 2 ^ n + 1 ≠ 1 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  have hp'p : (Nat.minFac (2 ^ n + 1)).Prime := Nat.minFac_prime hq1
  have hp'q : Nat.minFac (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.minFac_dvd _
  have hsurj : Function.Surjective π := by
    rintro ⟨φ, hφ⟩
    obtain ⟨A, hA, hφA⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h) (hXI hφ)
    obtain ⟨μ, hμ0, hμq, hAμ⟩ := id hA
    obtain ⟨l, hl⟩ := TableB.exists_norm_eq (q := 2 ^ n) (by
      have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp h.one_le); omega) hK hμ0 hμq
    set Bm := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * A with hBm
    have hAμ' : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
        μ • 1 := by rw [hbar]; exact hAμ
    have hBu : Bm ∈ U := by
      rw [hUdef, TableB.mem_unitGroup, hBm, TableB.coe_scalar_mul, TableB.transpose_map_smul,
        Matrix.smul_mul, Matrix.mul_smul, hAμ', smul_smul, smul_smul, UnitaryFieldData.bar_apply,
        ← hl]
      have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
      have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) = 1 := by
        calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) =
              (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ n * (((l⁻¹ : Kˣ) : K) * l) := by ring
          _ = 1 := by rw [hinv, one_pow, one_mul]
      rw [h0, one_smul]
    have hzs : Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ ∈ LargeEvenScalars (Fin d) K :=
      ⟨l⁻¹, rfl⟩
    have hκB : κ ⟨Bm, hBu⟩ = φ := by
      have hsplit : (Subgroup.inclusion hUN ⟨Bm, hBu⟩ :
          Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) =
          ⟨_, TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n)) hzs⟩ *
            ⟨A, TableBUE.gu_subset_normalizer h hA⟩ := Subtype.ext rfl
      rw [hκ, MonoidHom.comp_apply, hsplit, map_mul,
        TableB.projConj_of_scalar (LargeEvenSUGroup (Fin d) K (2 ^ n)) hzs, one_mul]
      exact hφA.symm
    have hmem : (⟨Bm, hBu⟩ : U) ∈ Γ := by
      show κ ⟨Bm, hBu⟩ ∈ X
      rw [hκB]
      exact hφ
    exact ⟨⟨⟨Bm, hBu⟩, hmem⟩, Subtype.ext hκB⟩
  have hcop := coprime_two_pow_add_one hp h.one_le hpq
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hz1 :
        TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) (Subgroup.inclusion hUN (z : U)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_projConj_eq_one h hK hd hdq hp'p hp'q hz1
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = ((z : U) : GL (Fin d) K) := hc
    have hzpGL : ((z : U) : GL (Fin d) K) ^ p = 1 := by
      have := congrArg (fun w : Γ => ((w : U) : GL (Fin d) K)) hzp
      simpa using this
    have hcp : c ^ p = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin d) (c ^ p) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) = 1 := by
        rw [map_pow, hc', hzpGL, Units.val_one]
      have h2 := congrFun (congrFun h1 0) 0
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
      exact Units.ext (by rw [h2, Units.val_one])
    have hcq : c ^ (2 ^ n + 1) = 1 := by
      have h1 := TableB.mem_unitGroup.mp (z : U).2
      rw [← hc'] at h1
      have h2 := congrFun (congrFun h1 0) 0
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map
        (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq, Matrix.one_apply_eq, UnitaryFieldData.bar_apply] at h2
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
      exact h2
    have hc1 : c = 1 := by
      have h3 : orderOf c ∣ Nat.gcd p (2 ^ n + 1) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_of_pow_eq_one hcq)
      rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    apply Subtype.ext
    apply Subtype.ext
    show ((z : U) : GL (Fin d) K) = 1
    rw [← hc', hc1, map_one]
  have hXtop : IsElemAbelian p (⊤ : Subgroup X) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext
      (TableB.IsElemAbelian.comm hX (a : X).2 (b : X).2))⟩⟩,
      fun y _ => Subtype.ext (hX.2 y y.2)⟩
  obtain ⟨A, -, -, hAab, hAcard⟩ := TableBUE.exists_lift_of_noTorsion π hsurj hp hnp hXtop
  set f : Γ →* GL (Fin d) K := U.subtype.comp Γ.subtype
  have hfinj : Function.Injective f := U.subtype_injective.comp Γ.subtype_injective
  have hA'ab : IsElemAbelian p (A.map f) := TableB.isElemAbelian_map hAab f
  have hA'U : ∀ g ∈ A.map f,
      ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K) = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact TableB.mem_unitGroup.mp (a : U).2
  have hle := card_le_pow_half_of_unitary_gl h hp hpq (A.map f)
    (fun g hg g' hg' => TableB.IsElemAbelian.comm hA'ab hg hg') hA'ab.2 hA'U
  rwa [Subgroup.card_map_of_injective hfinj, hAcard, Subgroup.card_top] at hle

end CFSG.StandardType.TwDThree
