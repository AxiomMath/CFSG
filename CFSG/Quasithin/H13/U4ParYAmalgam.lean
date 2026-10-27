module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34U4Vertex
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem hypUnitriangular_le_parH : hypUnitriangular h 2 0 ≤ parH h := by
  intro u hu
  obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hu
  refine ⟨UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num)
    (hypUnitriangular_le_hypBorel h hu), hdiag ie1, ?_⟩
  have h0 : ((u : GL Ix K) : Matrix Ix Ix K) if2 ie2 = 0 := hbt (by decide)
  simp only [rho, det_fin_two_of, hdiag, h0, mul_zero, sub_zero, mul_one]

theorem parH_le_radQ_sup : parH h ≤ radQ h ⊔ (levHom h).range := by
  intro g hg
  set A := rhoF h ⟨g, hg⟩ with hA
  have hl : levHom h A ∈ parH h := levHom_range_le_parH h ⟨A, rfl⟩
  have hmem : g * (levHom h A)⁻¹ ∈ parH h := (parH h).mul_mem hg ((parH h).inv_mem hl)
  have hq : g * (levHom h A)⁻¹ ∈ radQ h := by
    refine U4V.mem_radQ_of_rhoF_eq_one h (g := ⟨_, hmem⟩) ?_
    have e : (⟨g * (levHom h A)⁻¹, hmem⟩ : parH h) = ⟨g, hg⟩ * (⟨levHom h A, hl⟩ : parH h)⁻¹ :=
      rfl
    rw [e, map_mul, map_inv, rhoF_levHom, ← hA, mul_inv_cancel]
  have e : g = g * (levHom h A)⁻¹ * levHom h A := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right ⟨A, rfl⟩)

theorem hypUnitriangular_le_perfectCore_parP (hm : 2 ≤ m) :
    hypUnitriangular h 2 0 ≤ perfectCore (parP h) :=
  (hypUnitriangular_le_parH h).trans ((parH_le_radQ_sup h).trans
    (sup_le (radQ_le_perfectCore h hm) (levHom_range_le_perfectCore h hm)))

theorem hypUnitriangular_le_parH2 : hypUnitriangular h 2 0 ≤ parH2 h := by
  intro u hu
  obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hu
  refine ⟨UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl
    (hypUnitriangular_le_hypBorel h hu), ?_⟩
  have h0 : ((u : GL Ix K) : Matrix Ix Ix K) ie2 ie1 = 0 := hbt (by decide)
  simp only [rho2, det_fin_two_of, hdiag, h0, mul_zero, sub_zero, mul_one]

theorem parH2_le_radQ2_sup : parH2 h ≤ radQ2 h ⊔ (lev2Hom h).range := by
  intro g hg
  set A := rho2F h ⟨g, hg⟩ with hA
  have hl : lev2Hom h A ∈ parH2 h := lev2Hom_le_parH2 h ⟨A, rfl⟩
  have hmem : g * (lev2Hom h A)⁻¹ ∈ parH2 h := (parH2 h).mul_mem hg ((parH2 h).inv_mem hl)
  have hq : g * (lev2Hom h A)⁻¹ ∈ radQ2 h := by
    refine mem_radQ2_of_rho2 h (parH2_le_parP2 h hmem) ?_
    have e : (⟨g * (lev2Hom h A)⁻¹, hmem⟩ : parH2 h) =
        ⟨g, hg⟩ * (⟨lev2Hom h A, hl⟩ : parH2 h)⁻¹ := rfl
    have h1 : rho2F h ⟨g * (lev2Hom h A)⁻¹, hmem⟩ = 1 := by
      rw [e, map_mul, map_inv, rho2F_lev2Hom, ← hA, mul_inv_cancel]
    have h2 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K)) h1
    rw [Matrix.SpecialLinearGroup.coe_one] at h2
    exact h2
  have e : g = g * (lev2Hom h A)⁻¹ * lev2Hom h A := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right ⟨A, rfl⟩)

include h in
theorem exists_torus_param (hm : 2 ≤ m) :
    ∃ c : K, c ≠ 0 ∧ c * h.bar c ≠ 1 ∧ h.bar c ≠ c := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ (2 * m) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, h.card]
  have hq4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hsq : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  have hbar : h.bar (g : K) = ((g ^ 2 ^ m : Kˣ) : K) := by
    rw [UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val]
  refine ⟨g, g.ne_zero, fun h1 => ?_, fun h1 => ?_⟩
  · have h2 : g ^ (2 ^ m + 1) = 1 := by
      apply Units.ext
      rw [pow_succ', Units.val_mul, Units.val_one, ← hbar]
      exact h1
    have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
    rw [hord, hsq] at h3
    have key : 2 ^ m * 2 ^ m ≥ 2 ^ m * 4 := Nat.mul_le_mul_left _ hq4
    generalize 2 ^ m * 2 ^ m = y at h3 key
    generalize 2 ^ m = x at h3 key hq4
    omega
  · have h2 : g ^ (2 ^ m - 1) = 1 := by
      have h3 : g ^ (2 ^ m - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        apply Units.ext
        rw [← hbar]
        exact h1
      exact mul_right_cancel h3
    have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
    rw [hord, hsq] at h3
    have key : 2 ^ m * 2 ^ m ≥ 2 ^ m * 4 := Nat.mul_le_mul_left _ hq4
    generalize 2 ^ m * 2 ^ m = y at h3 key
    generalize 2 ^ m = x at h3 key hq4
    omega

theorem eq_one_of_comm_lev2 {c : K} (hc0 : c ≠ 0) (hc1 : c * h.bar c ≠ 1) (hc2 : h.bar c ≠ c)
    {d : Matrix.SpecialLinearGroup (Fin 2) K}
    (hd : (d : Matrix (Fin 2) (Fin 2) K) = !![c, 0; 0, c⁻¹]) {g : hypSU h 2 0}
    (hg : g ∈ radQ2 h) (hcomm : g * lev2Hom h d = lev2Hom h d * g) : g = 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hg
  have hb0 : h.bar c ≠ 0 := by
    intro e
    apply hc0
    have := congrArg h.bar e
    rwa [h.bar_bar, map_zero] at this
  have hbi : h.bar c⁻¹ = (h.bar c)⁻¹ := map_inv₀ h.bar c
  have hM : ((g : GL Ix K) : Matrix Ix Ix K) * lev2Mat h d =
      lev2Mat h d * ((g : GL Ix K) : Matrix Ix Ix K) := by
    have := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) hcomm
    simpa only [coe_mul_hypSU, coe_lev2Hom] using this
  have hz : ∀ x a b : K, a ≠ b → x * a = b * x → x = 0 := fun x a b hab e => by
    have h1 : x * (a - b) = 0 := by rw [mul_sub, e, mul_comm]; ring
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2) hab
  have e11 := congrFun (congrFun hM ie1) if1
  have e12 := congrFun (congrFun hM ie1) if2
  have e21 := congrFun (congrFun hM ie2) if1
  have e22 := congrFun (congrFun hM ie2) if2
  rw [mul_apply, mul_apply, sum_ix, sum_ix] at e11 e12 e21 e22
  simp [lev2Mat_apply, hd, a1, a2, a3, a4, a7, a8, a11, a12, hbi] at e11 e12 e21 e22
  have n11 : (h.bar c)⁻¹ ≠ c := fun e => hc1 (by
    calc c * h.bar c = (h.bar c)⁻¹ * h.bar c := by rw [e]
      _ = 1 := inv_mul_cancel₀ hb0)
  have n21 : (h.bar c)⁻¹ ≠ c⁻¹ := fun e => hc2 (inv_injective e)
  have n22 : h.bar c ≠ c⁻¹ := fun e => hc1 (by rw [e, mul_inv_cancel₀ hc0])
  have z11 := hz _ _ _ n11 e11
  have z12 := hz _ _ _ hc2 e12
  have z21 := hz _ _ _ n21 e21
  have z22 := hz _ _ _ n22 e22
  apply hypSU_ext
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, z11, z12, z21, z22, one_apply]

theorem radQ2_le_perfectCore_parP2 (hm : 2 ≤ m) : radQ2 h ≤ perfectCore (parP2 h) := by
  have := U4Par.finite_hypSU h
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_torus_param h hm
  set d : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![c, 0; 0, c⁻¹], by simp [det_fin_two_of, hc0]⟩ with hd
  set t := lev2Hom h d with ht
  have htC : t ∈ perfectCore (parP2 h) := lev2Hom_range_le_perfectCore h ⟨d, rfl⟩
  have htP : t ∈ parP2 h := lev2Hom_le_parP2 h ⟨d, rfl⟩
  have hmaps : ∀ x ∈ radQ2 h, x * t * x⁻¹ * t⁻¹ ∈ radQ2 h := fun x hx => by
    have h1 : t * x⁻¹ * t⁻¹ ∈ radQ2 h :=
      (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h htP) x⁻¹).mp
        ((radQ2 h).inv_mem hx)
    have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [e]
    exact (radQ2 h).mul_mem hx h1
  let f : ↥(radQ2 h) → ↥(radQ2 h) := fun x =>
    ⟨(x : hypSU h 2 0) * t * (x : hypSU h 2 0)⁻¹ * t⁻¹, hmaps x x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hxy
    have e : a * t * a⁻¹ * t⁻¹ = b * t * b⁻¹ * t⁻¹ := congrArg Subtype.val hxy
    have hz : b⁻¹ * a ∈ radQ2 h := (radQ2 h).mul_mem ((radQ2 h).inv_mem hb) ha
    have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
      calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹ * t⁻¹) * t * a := by group
        _ = b⁻¹ * (b * t * b⁻¹ * t⁻¹) * t * a := by rw [e]
        _ = t * (b⁻¹ * a) := by group
    have h1 := eq_one_of_comm_lev2 h hc0 hc1 hc2 (d := d) rfl hz hc
    apply Subtype.ext
    show a = b
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  intro z hz
  obtain ⟨⟨a, ha⟩, hx⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
  have e : z = a * t * a⁻¹ * t⁻¹ := (congrArg Subtype.val hx).symm
  rw [e]
  have hxN : a ∈ Subgroup.normalizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP2 h)))
      (radQ2_le_parP2 h ha)
  exact (perfectCore (parP2 h)).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN t).mp htC)
    ((perfectCore (parP2 h)).inv_mem htC)

theorem hypUnitriangular_le_perfectCore_parP2 (hm : 2 ≤ m) :
    hypUnitriangular h 2 0 ≤ perfectCore (parP2 h) :=
  (hypUnitriangular_le_parH2 h).trans ((parH2_le_radQ2_sup h).trans
    (sup_le (radQ2_le_perfectCore_parP2 h hm) (lev2Hom_range_le_perfectCore h)))

omit h in
theorem relIndex_sup_dvd_card {Y : Type} [Group Y] {N X : Subgroup Y}
    (hX : X ≤ Subgroup.normalizer (N : Set Y)) : N.relIndex (N ⊔ X) ∣ Nat.card X := by
  have hNX : N ≤ N ⊔ X := le_sup_left
  have hXX : X ≤ N ⊔ X := le_sup_right
  have : (N.subgroupOf (N ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr (sup_le Subgroup.le_normalizer hX)
  have htop : X.subgroupOf (N ⊔ X) ⊔ N.subgroupOf (N ⊔ X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXX hNX, sup_comm, Subgroup.subgroupOf_self]
  have h2 : (N.subgroupOf (N ⊔ X)).index =
      (N.subgroupOf (N ⊔ X)).relIndex (X.subgroupOf (N ⊔ X)) := by
    rw [← Subgroup.relIndex_sup_right, htop, Subgroup.relIndex_top_right]
  have hcX : Nat.card ↥(X.subgroupOf (N ⊔ X)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXX).toEquiv
  show (N.subgroupOf (N ⊔ X)).index ∣ Nat.card X
  rw [h2, ← hcX]
  exact Subgroup.relIndex_dvd_card _ _

omit h in
theorem le_of_isPGroup_of_sylow_le {Y : Type} [Group Y] [Finite Y] {P N U X : Subgroup Y}
    (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set Y)) (hUN : U ≤ N)
    (hU : IsSylowTwoOf U ⊤) (hX : IsPGroup 2 X) (hXP : X ≤ P) : X ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUidx : ¬ 2 ∣ U.index := by
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  have hNP2 : ¬ 2 ∣ N.relIndex P := fun h2 => hUidx (by
    rw [← Subgroup.relIndex_mul_index (hUN.trans hNP),
      ← Subgroup.relIndex_mul_relIndex U N P hUN hNP]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h2 _) _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have hd1 : N.relIndex (N ⊔ X) ∣ 2 ^ k := hk ▸ relIndex_sup_dvd_card (hXP.trans hPN)
  have hd2 : N.relIndex (N ⊔ X) ∣ N.relIndex P :=
    ⟨_, (Subgroup.relIndex_mul_relIndex N (N ⊔ X) P le_sup_left (sup_le hNP hXP)).symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hi0 : i = 0 := by
    by_contra hne
    exact hNP2 ((hi ▸ dvd_pow_self 2 hne).trans hd2)
  rw [hi0, pow_zero, Subgroup.relIndex_eq_one] at hi
  exact le_sup_right.trans hi

theorem ne_top_of_isTwoLocal {M : Subgroup (hypSU h 2 0)} (hM : IsTwoLocal M) : M ≠ ⊤ := by
  obtain ⟨R, hR1, hR2, rfl⟩ := hM
  intro htop
  have := isSimpleGroup_hypSU h
  have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h0 | h0
  · exact hR1 h0
  · apply not_isPGroup_hypSU h
    rw [h0] at hR2
    exact hR2.of_equiv Subgroup.topEquiv

theorem isMaximalTwoLocal_of_isCoatom {A : Subgroup (hypSU h 2 0)} (hA : IsCoatom A)
    (hO : pCoreOf 2 A ≠ ⊥) : IsMaximalTwoLocal A := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 A : Set (hypSU h 2 0))) :=
    ⟨pCoreOf 2 A, hO, pCoreOf_isPGroup 2 A, rfl⟩
  have hN : Subgroup.normalizer (pCoreOf 2 A : Set (hypSU h 2 0)) = A := by
    rcases hA.le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A) with h1 | h1
    · exact absurd h1 (ne_top_of_isTwoLocal h hloc)
    · exact h1
  refine ⟨hN ▸ hloc, fun M' hM' hAM' => ?_⟩
  rcases hA.le_iff.mp hAM' with h1 | h1
  · exact absurd h1 (ne_top_of_isTwoLocal h hM')
  · exact h1

theorem isMaximalTwoLocal_parP : IsMaximalTwoLocal (parP h) :=
  isMaximalTwoLocal_of_isCoatom h (isCoatom_parP h) (pCoreOf_parP_ne_bot h)

theorem isMaximalTwoLocal_parP2 : IsMaximalTwoLocal (parP2 h) :=
  isMaximalTwoLocal_of_isCoatom h (isCoatom_parP2 h) (pCoreOf_parP2_ne_bot h)

omit h in
theorem isSylowTwoOf_top_of_sylow {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) :
    IsSylowTwoOf (P : Subgroup Y) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup Y).subgroupOf ⊤).index = (P : Subgroup Y).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

theorem isSylowTwoOf_hypUnitriangular : IsSylowTwoOf (hypUnitriangular h 2 0) ⊤ := by
  have := U4Par.finite_hypSU h
  obtain ⟨P, hP⟩ :=
    (unitary_order_and_Sylow (r := 2) (ε := 0) h (by norm_num) (by norm_num)).2.1
  rw [← hP]
  exact isSylowTwoOf_top_of_sylow P

theorem isYAmalgamPair_parP_parP2 :
    IsYAmalgamPair (hypUnitriangular h 2 0) (parP h) (parP2 h) := by
  have := U4Par.finite_hypSU h
  have hB : Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) = hypBorel h 2 0 :=
    UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)
  have hBP : hypBorel h 2 0 ≤ parP h :=
    UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num)
  have hBP2 : hypBorel h 2 0 ≤ parP2 h :=
    UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl
  refine ⟨isSylowTwoOf_hypUnitriangular h, parP_ne_parP2 h, fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨hM, hBM⟩
    rw [hB] at hBM
    obtain ⟨A, hA, hMA⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom M).resolve_left (ne_top_of_isTwoLocal h hM.1)
    have hAP := eq_parP_or_eq_parP2 h hA (hBM.trans hMA)
    have hAloc : IsTwoLocal A := by
      rcases hAP with rfl | rfl
      · exact (isMaximalTwoLocal_parP h).1
      · exact (isMaximalTwoLocal_parP2 h).1
    have hMA' : A = M := hM.2 A hAloc hMA
    rcases hAP with h1 | h1
    · exact Or.inl (hMA'.symm.trans h1)
    · exact Or.inr (hMA'.symm.trans h1)
  · rintro (rfl | rfl)
    · exact ⟨isMaximalTwoLocal_parP h, hB ▸ hBP⟩
    · exact ⟨isMaximalTwoLocal_parP2 h, hB ▸ hBP2⟩

theorem le_perfectCore_parP_of_isPGroup (hm : 2 ≤ m) {X : Subgroup (hypSU h 2 0)}
    (hX : IsPGroup 2 X) (hXP : X ≤ parP h) : X ≤ perfectCore (parP h) := by
  have := U4Par.finite_hypSU h
  exact le_of_isPGroup_of_sylow_le (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
    (hypUnitriangular_le_perfectCore_parP h hm) (isSylowTwoOf_hypUnitriangular h) hX hXP

theorem le_perfectCore_parP2_of_isPGroup (hm : 2 ≤ m) {X : Subgroup (hypSU h 2 0)}
    (hX : IsPGroup 2 X) (hXP : X ≤ parP2 h) : X ≤ perfectCore (parP2 h) := by
  have := U4Par.finite_hypSU h
  exact le_of_isPGroup_of_sylow_le (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
    (hypUnitriangular_le_perfectCore_parP2 h hm) (isSylowTwoOf_hypUnitriangular h) hX hXP

omit h in
theorem isPGroup_zpowers_of_pow {Y : Type} [Group Y] {x : Y} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem mem_perfectCore_parP_of_pow (hm : 2 ≤ m) {x : hypSU h 2 0} (hxP : x ∈ parP h) {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ perfectCore (parP h) :=
  le_perfectCore_parP_of_isPGroup h hm (isPGroup_zpowers_of_pow hx)
    ((Subgroup.zpowers_le (H := parP h)).mpr hxP) (Subgroup.mem_zpowers x)

theorem mem_perfectCore_parP2_of_pow (hm : 2 ≤ m) {x : hypSU h 2 0} (hxP : x ∈ parP2 h) {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ perfectCore (parP2 h) :=
  le_perfectCore_parP2_of_isPGroup h hm (isPGroup_zpowers_of_pow hx)
    ((Subgroup.zpowers_le (H := parP2 h)).mpr hxP) (Subgroup.mem_zpowers x)

end CFSG.Quasithin.H13.U4Par
