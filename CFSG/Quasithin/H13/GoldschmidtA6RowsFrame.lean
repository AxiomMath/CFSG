module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsCode
public import CFSG.Quasithin.H13.A5S1521b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR

structure Frame (V : Type) [CommGroup V] (L : Subgroup (MulAut V)) (Γ : Type) [Group Γ]
    (d : ℕ) where
  e : V ≃* Multiplicative (Fin d → ZMod 2)
  ψ : Γ →* ↥L
  bij : Function.Bijective ψ
  mat : Γ → Matrix (Fin d) (Fin d) (ZMod 2)
  act : ∀ (γ : Γ) (w : V), Multiplicative.toAdd (e (((ψ γ : ↥L) : MulAut V) w)) =
      mat γ *ᵥ Multiplicative.toAdd (e w)

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Γ : Type} [Group Γ] {d : ℕ}

namespace Frame

@[expose] def vec (fr : Frame V L Γ d) (w : V) : Fin d → ZMod 2 := Multiplicative.toAdd (fr.e w)

theorem vec_surj (fr : Frame V L Γ d) (y : Fin d → ZMod 2) : ∃ w, fr.vec w = y :=
  ⟨fr.e.symm (Multiplicative.ofAdd y), by simp [vec]⟩

theorem act' (fr : Frame V L Γ d) (γ : Γ) (w : V) :
    fr.vec (((fr.ψ γ : ↥L) : MulAut V) w) = fr.mat γ *ᵥ fr.vec w := fr.act γ w

theorem mat_mul (fr : Frame V L Γ d) (γ δ : Γ) : fr.mat (γ * δ) = fr.mat γ * fr.mat δ := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  obtain ⟨w, rfl⟩ := fr.vec_surj y
  rw [← Matrix.mulVec_mulVec, ← fr.act' δ w, ← fr.act' γ, ← fr.act', map_mul]
  rfl

theorem mat_one (fr : Frame V L Γ d) : fr.mat 1 = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  obtain ⟨w, rfl⟩ := fr.vec_surj y
  rw [Matrix.one_mulVec, ← fr.act', map_one]
  rfl

theorem eq_one_of_mat (fr : Frame V L Γ d) {γ : Γ} (h : fr.mat γ = 1) : γ = 1 := by
  apply fr.bij.1
  rw [map_one]
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have := fr.act' γ w
  rw [h, Matrix.one_mulVec] at this
  have h2 : fr.e (((fr.ψ γ : ↥L) : MulAut V) w) = fr.e w := by
    apply Multiplicative.toAdd.injective
    exact this
  exact fr.e.injective h2


@[expose] def conj (fr : Frame V L Γ d) (g : Γ) : Frame V L Γ d where
  e := ((fr.ψ g : ↥L) : MulAut V)⁻¹ |>.trans fr.e
  ψ := fr.ψ.comp (MulAut.conj g).toMonoidHom
  bij := fr.bij.comp (MulAut.conj g).bijective
  mat := fr.mat
  act := by
    intro γ w
    have h1 : (((fr.ψ (g * γ * g⁻¹) : ↥L) : MulAut V)) =
        ((fr.ψ g : ↥L) : MulAut V) * ((fr.ψ γ : ↥L) : MulAut V) *
          ((fr.ψ g : ↥L) : MulAut V)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rfl
    have h2 : (((fr.ψ g : ↥L) : MulAut V)⁻¹) ((((fr.ψ (g * γ * g⁻¹) : ↥L) : MulAut V)) w) =
        ((fr.ψ γ : ↥L) : MulAut V) ((((fr.ψ g : ↥L) : MulAut V)⁻¹) w) := by
      rw [h1]
      simp [MulAut.mul_apply]
    show Multiplicative.toAdd (fr.e ((((fr.ψ g : ↥L) : MulAut V)⁻¹)
        ((((fr.ψ (g * γ * g⁻¹) : ↥L) : MulAut V)) w))) = _
    rw [h2, fr.act]
    rfl


theorem exists_conj_sylow [Finite Γ] (fr : Frame V L Γ d) {S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {S0 : Subgroup Γ} (h2 : IsPGroup 2 S0) :
    ∃ g : Γ, ∀ s ∈ S0, ((fr.ψ (g * s * g⁻¹) : ↥L) : MulAut V) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSL, hSp, hSi⟩ := hS
  have hT : IsPGroup 2 (S.subgroupOf L) :=
    IsPGroup.of_surjective (G := ↥S) hSp (Subgroup.subgroupOfEquivOfLe hSL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSL).symm.surjective
  have hS' : IsPGroup 2 ((S.subgroupOf L).comap fr.ψ) := hT.comap_of_injective fr.ψ fr.bij.1
  have hi : ¬ 2 ∣ ((S.subgroupOf L).comap fr.ψ).index := by
    rw [Subgroup.index_comap_of_surjective (S.subgroupOf L) fr.bij.2]
    exact hSi
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q (hS'.toSylow hi)
  refine ⟨g, fun s hs => ?_⟩
  have h1 : g * s * g⁻¹ ∈ ((hS'.toSylow hi : Sylow 2 Γ) : Subgroup Γ) := by
    rw [← hg]
    have : g * s * g⁻¹ ∈ ((g • Q : Sylow 2 Γ) : Subgroup Γ) := by
      have := (Sylow.coe_smul (g := g) (P := Q))
      have hmem : g * s * g⁻¹ ∈ ((g • Q : Sylow 2 Γ) : Set Γ) := by
        rw [this]
        exact ⟨s, hQ hs, rfl⟩
      exact hmem
    exact this
  have h1' : g * s * g⁻¹ ∈ (S.subgroupOf L).comap fr.ψ := by
    rw [← IsPGroup.toSylow_coe hS' hi]
    exact h1
  exact Subgroup.mem_subgroupOf.mp h1'


@[expose] noncomputable def pa (fr : Frame V L Γ d) (v : MulAut V) :
    (Fin d → ZMod 2) →+ (Fin d → ZMod 2) :=
  AddMonoidHom.mk' (fun y : Fin d → ZMod 2 =>
    Multiplicative.toAdd (fr.e (v (fr.e.symm (Multiplicative.ofAdd y))))) (by
      intro a b
      simp [ofAdd_add, map_mul, toAdd_mul])

@[expose] noncomputable def pm (fr : Frame V L Γ d) (v : MulAut V) :
    Matrix (Fin d) (Fin d) (ZMod 2) :=
  LinearMap.toMatrix' ((fr.pa v).toZModLinearMap 2)

theorem pm_mulVec (fr : Frame V L Γ d) (v : MulAut V) (w : V) :
    fr.pm v *ᵥ fr.vec w = fr.vec (v w) := by
  unfold pm
  rw [LinearMap.toMatrix'_mulVec]
  simp [vec, pa]

theorem pm_mul (fr : Frame V L Γ d) (v v' : MulAut V) : fr.pm (v * v') = fr.pm v * fr.pm v' := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  obtain ⟨w, rfl⟩ := fr.vec_surj y
  rw [← Matrix.mulVec_mulVec, pm_mulVec, pm_mulVec, pm_mulVec]
  rfl

theorem pm_one (fr : Frame V L Γ d) : fr.pm 1 = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  obtain ⟨w, rfl⟩ := fr.vec_surj y
  rw [pm_mulVec, Matrix.one_mulVec]
  rfl

theorem pm_comm (fr : Frame V L Γ d) {v u : MulAut V} (γ : Γ)
    (hu : u = ((fr.ψ γ : ↥L) : MulAut V)) (h : v * u = u * v) :
    fr.pm v * fr.mat γ = fr.mat γ * fr.pm v := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  obtain ⟨w, rfl⟩ := fr.vec_surj y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← fr.act', ← hu, pm_mulVec, pm_mulVec,
    ← fr.act' γ, ← hu]
  have := congrArg (fun f : MulAut V => f w) h
  simp only [MulAut.mul_apply] at this
  rw [this]

theorem mem_fixV_zpowers {v : MulAut V} {w : V} :
    w ∈ fixV (Subgroup.zpowers v) ↔ v w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_V (fr : Frame V L Γ d) : Nat.card V = 2 ^ d := by
  rw [Nat.card_congr fr.e.toEquiv]
  change Nat.card (Fin d → ZMod 2) = 2 ^ d
  rw [Nat.card_pi]
  simp

theorem card_fixV (fr : Frame V L Γ d) (v : MulAut V) :
    Nat.card ↥(fixV (Subgroup.zpowers v)) = Nat.card {y : Fin d → ZMod 2 // fr.pm v *ᵥ y = y} := by
  refine Nat.card_congr
    { toFun := fun w => ⟨fr.vec w.1, ?_⟩
      invFun := fun y => ⟨fr.e.symm (Multiplicative.ofAdd y.1), ?_⟩
      left_inv := fun w => ?_
      right_inv := fun y => ?_ }
  · rw [pm_mulVec, mem_fixV_zpowers.mp w.2]
  · rw [mem_fixV_zpowers]
    apply fr.e.injective
    apply Multiplicative.toAdd.injective
    have h := pm_mulVec fr v (fr.e.symm (Multiplicative.ofAdd y.1))
    have h2 : fr.vec (fr.e.symm (Multiplicative.ofAdd y.1)) = y.1 := by simp [vec]
    rw [h2, y.2] at h
    rw [vec] at h
    rw [← h]
    simp
  · apply Subtype.ext
    simp [vec]
  · apply Subtype.ext
    simp [vec]


theorem mat_pow (fr : Frame V L Γ d) (γ : Γ) (n : ℕ) : fr.mat (γ ^ n) = fr.mat γ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

end Frame

theorem exists_odd_of_oTwoRes {G : Type} [Group G] {X : Subgroup G} (hXO : X ≤ oTwoRes X)
    (hX1 : X ≠ ⊥) : ∃ x ∈ X, x ≠ 1 ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1 := by
  by_contra hcon
  push Not at hcon
  apply hX1
  rw [eq_bot_iff]
  refine hXO.trans ?_
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hxX, m, hm, hxm⟩
  by_contra hne
  exact hcon x hxX (by simpa using hne) m hm hxm

theorem pow_three_of_odd {M : Type} [Monoid M] (K : M) (a m : ℕ) (hm : Odd m) (h1 : K ^ m = 1)
    (h2 : K ^ (3 * 2 ^ a) = 1) : K ^ 3 = 1 := by
  have hg : K ^ Nat.gcd m (3 * 2 ^ a) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  have hd : Nat.gcd m (3 * 2 ^ a) ∣ 3 := by
    have h3 : Nat.gcd m (3 * 2 ^ a) ∣ 3 * 2 ^ a := Nat.gcd_dvd_right _ _
    have hc : Nat.Coprime (Nat.gcd m (3 * 2 ^ a)) (2 ^ a) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop
    exact hc.dvd_of_dvd_mul_right h3
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_mul, hg, one_pow]

theorem index_eq_four {W : Type} [CommGroup W] [Finite W] {d : ℕ} (hW : Nat.card W = 2 ^ d)
    (H : Subgroup W) (h : rkIdx H = 2) : H.index = 4 := by
  have hdvd : H.index ∣ 2 ^ d := hW ▸ Subgroup.index_dvd_card H
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold rkIdx at h
  rw [hk, padicValNat.prime_pow] at h
  rw [hk, h]
  norm_num


theorem span_top {d : ℕ} (N : AddSubgroup (Fin d → ZMod 2))
    (T : List (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hN : ∀ K ∈ T, ∀ y, K *ᵥ y - y ∈ N) (hT : Span T) : N = ⊤ := by
  by_contra hne
  have hlt : AddSubgroup.toZModSubmodule 2 N < ⊤ := by
    have h := (OrderIso.lt_iff_lt (AddSubgroup.toZModSubmodule 2)).2 (lt_top_iff_ne_top.2 hne)
    rwa [OrderIso.map_top] at h
  obtain ⟨f, hf0, hfp⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Fin d → ZMod 2 := fun i => f (fun j => if i = j then 1 else 0) with hc
  have hfy : ∀ y, f y = c ⬝ᵥ y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc0 : c ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfy y, h0]
    simp
  obtain ⟨q, hq, y, hy⟩ := hT c hc0
  apply hy
  have h1 : f (q *ᵥ y - y) = 0 := by
    have hmem : q *ᵥ y - y ∈ AddSubgroup.toZModSubmodule 2 N := hN q hq y
    exact hfp hmem
  rw [map_sub, sub_eq_zero] at h1
  rw [← hfy, ← hfy, h1]


structure ModelHyp (d : ℕ) (Γ : Type) [Group Γ] (mat : Γ → Matrix (Fin d) (Fin d) (ZMod 2)) where
  S0 : Subgroup Γ
  p2 : IsPGroup 2 S0
  gens : List Γ
  gens_mem : ∀ g ∈ gens, g ∈ S0
  cyc : CycData d
  cyc_gm : cyc.gm = gens.map mat
  hB : cyc.Bmat * cyc.Binv = 1
  Mem : Matrix (Fin d) (Fin d) (ZMod 2) → Prop
  hMem : ∀ γ, Mem (mat γ)
  a : ℕ
  hd : 2 ≤ d
  leaf : ∀ w : Fin d → ZMod 2, cyc.Pmat w * cyc.Pmat w = 1 →
    (∀ A ∈ cyc.gm, cyc.Pmat w * A = A * cyc.Pmat w) → fixCard (cyc.Pmat w) = 2 ^ (d - 2) →
    ∀ K, Mem K → K * cyc.Pmat w = cyc.Pmat w * K →
      K ^ (3 * 2 ^ a) = 1 ∧ (K ^ 3 = 1 → K ≠ 1 →
        Span (conjM (gens.map fun s => (mat s, mat s⁻¹)) K))


open CFSG.Quasithin.H13.A5 in
theorem comm_core [Finite V] [Finite Γ] (fr : Frame V L Γ d) (M : ModelHyp d Γ fr.mat)
    {v : MulAut V} (hv2 : v * v = 1) (hrk : rkIdx (fixV (Subgroup.zpowers v)) = 2)
    {S X : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) (hSv : S ≤ Subgroup.centralizer {v})
    (hXL : X ≤ L) (hXv : X ≤ Subgroup.centralizer {v})
    (hSX : S ≤ Subgroup.normalizer (X : Set (MulAut V))) (hXO : X ≤ oTwoRes X) (hX1 : X ≠ ⊥) :
    commSubOf ⊤ X = ⊤ := by
  classical
  obtain ⟨x, hxX, hx1, m, hm, hxm⟩ := exists_odd_of_oTwoRes hXO hX1
  obtain ⟨g, hg⟩ := fr.exists_conj_sylow hS M.p2
  let fr' := fr.conj g
  have hψ' : ∀ s ∈ M.S0, ((fr'.ψ s : ↥L) : MulAut V) ∈ S := fun s hs => hg s hs
  have hmat : fr'.mat = fr.mat := rfl
  set P := fr'.pm v with hP
  have hPP : P * P = 1 := by rw [hP, ← Frame.pm_mul, hv2, Frame.pm_one]
  have hcomm : ∀ s ∈ M.S0, P * fr'.mat s = fr'.mat s * P := by
    intro s hs
    refine Frame.pm_comm fr' s rfl ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSv (hψ' s hs))).symm
  have hcommgm : ∀ A ∈ M.cyc.gm, P * A = A * P := by
    intro A hA
    rw [M.cyc_gm, List.mem_map] at hA
    obtain ⟨s, hs, rfl⟩ := hA
    exact hcomm s (M.gens_mem s hs)
  have hcard : fixCard P = 2 ^ (d - 2) := by
    have h4 := index_eq_four fr'.card_V _ hrk
    have hc := Subgroup.card_mul_index (fixV (Subgroup.zpowers v))
    rw [h4, fr'.card_V] at hc
    have h5 : Nat.card ↥(fixV (Subgroup.zpowers v)) = 2 ^ (d - 2) := by
      have : 2 ^ d = 2 ^ (d - 2) * 4 := by
        have : d = (d - 2) + 2 := by have := M.hd; omega
        conv_lhs => rw [this]
        rw [pow_add]; norm_num
      omega
    rw [fr'.card_fixV v] at h5
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h5
    simpa [fixCard] using h5
  have hPcyc : P = M.cyc.Pmat (P *ᵥ M.cyc.u) := M.cyc.eq_Pmat M.hB hcommgm
  obtain ⟨γ, hγ⟩ := fr'.bij.2 ⟨x, hXL hxX⟩
  have hγx : ((fr'.ψ γ : ↥L) : MulAut V) = x := by rw [hγ]
  set K := fr'.mat γ with hK
  have hKP : K * P = P * K := by
    have := Frame.pm_comm fr' (v := v) (u := x) γ hγx.symm
      (Subgroup.mem_centralizer_singleton_iff.mp (hXv hxX)).symm
    exact this.symm
  have hγm : γ ^ m = 1 := by
    apply fr'.bij.1
    rw [map_pow, hγ, map_one]
    apply Subtype.ext
    simpa using hxm
  have hKm : K ^ m = 1 := by rw [hK, ← Frame.mat_pow, hγm, Frame.mat_one]
  have hK1 : K ≠ 1 := by
    intro h1
    apply hx1
    rw [← hγx, Frame.eq_one_of_mat fr' h1, map_one]
    rfl
  obtain ⟨hKE, hspan⟩ := M.leaf (P *ᵥ M.cyc.u) (by rw [← hPcyc]; exact hPP)
    (by rw [← hPcyc]; exact hcommgm) (by rw [← hPcyc]; simpa using hcard) K (M.hMem γ)
    (by rw [← hPcyc]; exact hKP)
  have hK3 : K ^ 3 = 1 := pow_three_of_odd K M.a m hm hKm hKE
  have hSp := hspan hK3 hK1
  let N : AddSubgroup (Fin d → ZMod 2) :=
    { carrier := {y | fr'.e.symm (Multiplicative.ofAdd y) ∈ commSubOf ⊤ X}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, ofAdd_zero, map_one]
        exact Subgroup.one_mem _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at ha hb ⊢
        exact Subgroup.mul_mem _ ha hb
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq, ofAdd_neg, map_inv] at ha ⊢
        exact Subgroup.inv_mem _ ha }
  have hq : ∀ q ∈ conjM (M.gens.map fun s => (fr.mat s, fr.mat s⁻¹)) K,
      ∃ γ' : Γ, fr'.mat γ' = q ∧ ((fr'.ψ γ' : ↥L) : MulAut V) ∈ X := by
    intro q hq
    simp only [conjM, List.mem_cons, List.mem_flatMap, List.mem_map, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | ⟨p, ⟨s, hs, rfl⟩, hq⟩
    · exact ⟨γ, rfl, by rw [hγx]; exact hxX⟩
    · have hsS : ((fr'.ψ s : ↥L) : MulAut V) ∈ S := hψ' s (M.gens_mem s hs)
      have hsiS : ((fr'.ψ s : ↥L) : MulAut V)⁻¹ ∈ S := S.inv_mem hsS
      rcases hq with rfl | rfl
      · refine ⟨s * γ * s⁻¹, ?_, ?_⟩
        · rw [Frame.mat_mul, Frame.mat_mul]
          rfl
        · have h := (Subgroup.mem_normalizer_iff.mp (hSX hsS) x).mp hxX
          have e1 : ((fr'.ψ (s * γ * s⁻¹) : ↥L) : MulAut V) =
              ((fr'.ψ s : ↥L) : MulAut V) * x * ((fr'.ψ s : ↥L) : MulAut V)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            rw [← hγx]
            rfl
          rw [e1]
          exact h
      · refine ⟨s⁻¹ * γ * s, ?_, ?_⟩
        · rw [Frame.mat_mul, Frame.mat_mul]
          rfl
        · have h := (Subgroup.mem_normalizer_iff.mp (hSX hsiS) x).mp hxX
          have e1 : ((fr'.ψ (s⁻¹ * γ * s) : ↥L) : MulAut V) =
              ((fr'.ψ s : ↥L) : MulAut V)⁻¹ * x * ((fr'.ψ s : ↥L) : MulAut V)⁻¹⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            rw [← hγx]
            simp
          rw [e1]
          exact h
  have hN : ∀ q ∈ conjM (M.gens.map fun s => (fr.mat s, fr.mat s⁻¹)) K, ∀ y, q *ᵥ y - y ∈ N := by
    intro q hqm y
    obtain ⟨γ', hγ', hk⟩ := hq q hqm
    have hmem := A5.mem_commSubOf (K := X) (U := ⊤) hk (u := fr'.e.symm (Multiplicative.ofAdd y))
      (Subgroup.mem_top _)
    have hact := fr'.act γ' (fr'.e.symm (Multiplicative.ofAdd y))
    rw [hγ'] at hact
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hact
    have hv : fr'.e (((fr'.ψ γ' : ↥L) : MulAut V) (fr'.e.symm (Multiplicative.ofAdd y))) =
        Multiplicative.ofAdd (q *ᵥ y) := by
      apply Multiplicative.toAdd.injective
      rw [hact]
      rfl
    show fr'.e.symm (Multiplicative.ofAdd (q *ᵥ y - y)) ∈ commSubOf ⊤ X
    have : fr'.e.symm (Multiplicative.ofAdd (q *ᵥ y - y)) =
        ((fr'.ψ γ' : ↥L) : MulAut V) (fr'.e.symm (Multiplicative.ofAdd y)) *
          (fr'.e.symm (Multiplicative.ofAdd y))⁻¹ := by
      have h2 : fr'.e.symm (Multiplicative.ofAdd (q *ᵥ y)) =
          ((fr'.ψ γ' : ↥L) : MulAut V) (fr'.e.symm (Multiplicative.ofAdd y)) := by
        rw [MulEquiv.symm_apply_eq]
        exact hv.symm
      rw [ofAdd_sub, map_div, h2, div_eq_mul_inv]
    rw [this]
    exact hmem
  have hNtop : N = ⊤ := span_top N _ hN hSp
  rw [eq_top_iff]
  intro w _
  have hw : (Multiplicative.toAdd (fr'.e w)) ∈ N := by rw [hNtop]; exact AddSubgroup.mem_top _
  simpa [N] using hw

end CFSG.Quasithin.H13.A6.GR
