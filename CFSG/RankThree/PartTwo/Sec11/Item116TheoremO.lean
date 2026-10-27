module

public import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace TheoremO

section General

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem exists_commute_lift {p : ℕ} [Fact p.Prime] (N : Subgroup Γ) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup Γ} (hP : IsPGroup p P) {z : Γ}
    (hz : ∀ t ∈ P, t * z * t⁻¹ * z⁻¹ ∈ N) :
    ∃ x : Γ, x⁻¹ * z ∈ N ∧ ∀ t ∈ P, t * x = x * t := by
  have hNn : N.Normal := inferInstance
  have hmem : ∀ t ∈ P, ∀ x : Γ, x⁻¹ * z ∈ N → (t * x * t⁻¹)⁻¹ * z ∈ N := by
    intro t ht x hx
    have h1 : t * z⁻¹ * t⁻¹ * z ∈ N := by
      have h2 : z * t * z⁻¹ * t⁻¹ ∈ N := by
        have := N.inv_mem (hz t ht)
        rwa [show (t * z * t⁻¹ * z⁻¹)⁻¹ = z * t * z⁻¹ * t⁻¹ by group] at this
      have := hNn.conj_mem _ h2 z⁻¹
      rwa [show z⁻¹ * (z * t * z⁻¹ * t⁻¹) * z⁻¹⁻¹ = t * z⁻¹ * t⁻¹ * z by group] at this
    have := N.mul_mem (hNn.conj_mem _ hx t) h1
    rwa [show t * (x⁻¹ * z) * t⁻¹ * (t * z⁻¹ * t⁻¹ * z) = (t * x * t⁻¹)⁻¹ * z by group] at this
  let S := {x : Γ // x⁻¹ * z ∈ N}
  let : MulAction P S :=
    { smul := fun t x => ⟨(t : Γ) * x.1 * (t : Γ)⁻¹, hmem t t.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : P) : Γ) * x.1 * ((1 : P) : Γ)⁻¹ = x.1
        simp)
      mul_smul := fun t u x => Subtype.ext (by
        change ((t * u : P) : Γ) * x.1 * ((t * u : P) : Γ)⁻¹ =
          (t : Γ) * ((u : Γ) * x.1 * (u : Γ)⁻¹) * (t : Γ)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card S = Nat.card N := Nat.card_congr
    { toFun := fun x => ⟨x.1⁻¹ * z, x.2⟩
      invFun := fun n => ⟨z * (n : Γ)⁻¹, by
        rw [show (z * (n : Γ)⁻¹)⁻¹ * z = n by group]
        exact n.2⟩
      left_inv := fun x => Subtype.ext (by
        change z * (x.1⁻¹ * z)⁻¹ = x.1
        group)
      right_inv := fun n => Subtype.ext (by
        change (z * (n : Γ)⁻¹)⁻¹ * z = n
        group) }
  obtain ⟨x, hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S (hcard ▸ hN)
  refine ⟨x.1, x.2, fun t ht => ?_⟩
  have h : t * x.1 * t⁻¹ = x.1 := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx ⟨t, ht⟩)
  calc t * x.1 = t * x.1 * t⁻¹ * t := by group
    _ = x.1 * t := by rw [h]

theorem commutator_eq_bot_of_isComponent_le_normalizer {J P : Subgroup Γ} (hJ : IsComponent J)
    (hP : Group.IsSolvable P) (hJP : J ≤ Subgroup.normalizer (P : Set Γ)) : ⁅J, P⁆ = ⊥ := by
  have hJM : J ≤ J ⊔ P := le_sup_left
  have hPM : P ≤ J ⊔ P := le_sup_right
  have hPn : (P.subgroupOf (J ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr (sup_le hJP Subgroup.le_normalizer)
  have hPs : Group.IsSolvable (P.subgroupOf (J ⊔ P)) := by
    have := hP
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPM).injective
  have h := (LocalCores.component_solvable_centralizer hPs hPn.isSubnormal).1 _
    (LocalCores.component_overgroup hJ hJM)
  have h2 := LocalCores.commutator_inf_eq_bot_of_subgroupOf hJM h
  rwa [inf_eq_left.mpr hPM] at h2

theorem inf_eq_bot_of_isPGroup_of_odd {P M : Subgroup Γ} (hP : IsPGroup 2 P)
    (hM : Odd (Nat.card M)) : P ⊓ M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hP.to_le (inf_le_left : P ⊓ M ≤ P)).exists_card_eq
  have hd : Nat.card (P ⊓ M : Subgroup Γ) ∣ Nat.card M := Subgroup.card_dvd_of_le inf_le_right
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
  · exfalso
    have h2 : 2 ∣ Nat.card M := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hd)
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h2)

end General

variable {G : Type} [Group G] [Finite G]

theorem exists_not_mem_zpowers_commutator_ne_bot (hchar : CFSG.Assembly.IsCharTwoType G)
    {F T₀ : Subgroup G} {c : G} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : 9 ≤ Nat.card F)
    (hcF : c ∈ F) (hc1 : c ≠ 1) (hT₀ : IsPGroup 2 T₀) (hT₀1 : T₀ ≠ ⊥)
    (hFT : F ≤ Subgroup.centralizer (T₀ : Set G)) :
    ∃ e ∈ F, e ∉ Subgroup.zpowers c ∧
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T₀ : Set G)) ⊓
        Subgroup.centralizer ({e} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ := by
  obtain ⟨e, heF, he1, hne⟩ := Sec6.exists_commutator_inf_centralizer_ne_bot hchar hT₀ hT₀1 hF
    hF9 hFT (Subgroup.zpowers_le.mpr hcF) (fun h => hc1 (Subgroup.zpowers_eq_bot.mp h))
  refine ⟨e, heF, fun hec => hne ?_, hne⟩
  have he3 : orderOf e = 3 := orderOf_eq_prime (hF.2 e heF) he1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hF.2 c hcF) hc1
  have heq : Subgroup.zpowers e = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, he3, hc3])
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine inf_le_right.trans ?_
  rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, heq]

theorem le_centralizer_of_split_thetaComponents {C T₀ Q : Subgroup G} {c : G}
    {Z Z' : Subgroup C} (hZ : Z ∈ thetaComponents 3 C) (hZ' : Z' ∈ thetaComponents 3 C)
    (hne : Z ≠ Z') (hTZ : T₀ ≤ Z.map C.subtype) (hcZ : c ∈ Z'.map C.subtype)
    (hcT : c ∈ Subgroup.centralizer (T₀ : Set G)) (hT₀ : IsPGroup 2 T₀)
    (hodd : Odd (Nat.card (aschbacherSolvableCore 3 C))) (hQ : IsPGroup 2 Q)
    (hQN : Subgroup.centralizer (T₀ : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    Q ⊓ C ≤ Subgroup.centralizer ({c} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 C with hNdef
  have hN2 : ¬ 2 ∣ Nat.card N := fun h2 =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hTC : T₀ ≤ C := hTZ.trans (Subgroup.map_subtype_le Z)
  set T₁ := T₀.comap C.subtype with hT₁
  have hT₁Z : T₁ ≤ Z := by
    intro t ht
    obtain ⟨z, hz, hzt⟩ := hTZ ht
    rwa [show t = z from Subtype.ext hzt.symm]
  have hcC : c ∈ C := by
    obtain ⟨z, -, hzc⟩ := hcZ
    rw [← hzc]
    exact z.2
  set c₁ : C := ⟨c, hcC⟩ with hc₁
  have hc₁Z' : c₁ ∈ Z' := by
    obtain ⟨z, hz, hzc⟩ := hcZ
    rwa [show c₁ = z from Subtype.ext hzc.symm]
  have hJ := isComponent_map_of_mem_thetaComponents Nat.prime_three hZ
  have hJ' := isComponent_map_of_mem_thetaComponents Nat.prime_three hZ'
  have hJne : Z.map (QuotientGroup.mk' N) ≠ Z'.map (QuotientGroup.mk' N) := fun h =>
    hne ((theta_component_quotient_correspondence (H := C) Nat.prime_three).1.injOn hZ hZ' h)
  have hcomm := (LocalCores.distinct_components_commute hJ hJ').resolve_left hJne
  have hO2 : ∀ t ∈ T₁, ∀ z ∈ Z', t * z * t⁻¹ * z⁻¹ ∈ N := by
    intro t ht z hz
    have h1 : QuotientGroup.mk' N t ∈ Z.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ (hT₁Z ht)
    have h2 : QuotientGroup.mk' N z ∈ Z'.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hz
    have h3 := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm h1) _ h2
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h3
    rw [← h3]
    group
  set X := (Z'.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ⊓
    Subgroup.centralizer (T₁ : Set C) with hX
  have hXmap : X.map (QuotientGroup.mk' N) = Z'.map (QuotientGroup.mk' N) := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hxz, hxT⟩ := exists_commute_lift N hN2 hT₀.comap_subtype (hO2 · · z hz)
      have hπx : QuotientGroup.mk' N x = QuotientGroup.mk' N z := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact hxz
      refine ⟨x, ⟨?_, Subgroup.mem_centralizer_iff.mpr hxT⟩, hπx⟩
      show QuotientGroup.mk' N x ∈ Z'.map (QuotientGroup.mk' N)
      rw [hπx]
      exact Subgroup.mem_map_of_mem _ hz
  have hc₁X : c₁ ∈ X := by
    refine ⟨Subgroup.mem_map_of_mem _ hc₁Z', Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcT (t : G) ht)
  set Q₁ := Q.comap C.subtype with hQ₁
  have hQ₁2 : IsPGroup 2 Q₁ := hQ.comap_subtype
  have hXN : X ≤ Subgroup.normalizer (Q₁ : Set C) := by
    intro x hx
    have hxT : (x : G) ∈ Subgroup.centralizer (T₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx.2 ⟨t, hTC ht⟩ ht)
    have hxQ := hQN hxT
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact Subgroup.mem_normalizer_iff.mp hxQ q
  have hJN : Z'.map (QuotientGroup.mk' N) ≤
      Subgroup.normalizer ((Q₁.map (QuotientGroup.mk' N) : Subgroup (C ⧸ N)) : Set (C ⧸ N)) := by
    rw [← hXmap]
    exact (Subgroup.map_mono hXN).trans (Subgroup.le_normalizer_map _)
  have hsolv : Group.IsSolvable (Q₁.map (QuotientGroup.mk' N)) := by
    have := (hQ₁2.map (QuotientGroup.mk' N)).isNilpotent
    infer_instance
  have h5 := commutator_eq_bot_of_isComponent_le_normalizer hJ' hsolv hJN
  have hXQN : ⁅X, Q₁⁆ ≤ N := by
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, hXmap]
    exact h5
  have hXQ : ⁅X, Q₁⁆ ≤ Q₁ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hXN
  have hbot : ⁅X, Q₁⁆ = ⊥ := by
    rw [eq_bot_iff, ← inf_eq_bot_of_isPGroup_of_odd hQ₁2 hodd]
    exact le_inf hXQ hXQN
  have hc₁Q : c₁ ∈ Subgroup.centralizer (Q₁ : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hc₁X
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.mem_centralizer_iff.mp hc₁Q ⟨q, hq.2⟩ (show q ∈ Q from hq.1)
  exact congrArg Subtype.val h

theorem false_of_charTwo_split_thetaComponents (hchar : CFSG.Assembly.IsCharTwoType G)
    {F T₀ : Subgroup G} {c : G} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : 9 ≤ Nat.card F)
    (hcF : c ∈ F) (hc1 : c ≠ 1) (hT₀ : IsPGroup 2 T₀) (hT₀1 : T₀ ≠ ⊥)
    (hFT : F ≤ Subgroup.centralizer (T₀ : Set G))
    (hY : ∀ e ∈ F, e ∉ Subgroup.zpowers c →
      ∃ Y ∈ thetaComponentsAt 3 e, ∃ Y' ∈ thetaComponentsAt 3 e, T₀ ≤ Y ∧ c ∈ Y' ∧ Y ≠ Y' ∧
        Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({e} : Set G))))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heF, hec, hQe⟩ :=
    exists_not_mem_zpowers_commutator_ne_bot hchar hF hF9 hcF hc1 hT₀ hT₀1 hFT
  obtain ⟨Y, hY, Y', hY', hTY, hcY', hne, hodd⟩ := hY e heF hec
  apply hQe
  obtain ⟨Z, hZ, rfl⟩ := hY
  obtain ⟨Z', hZ', rfl⟩ := hY'
  beta_reduce at hTY hcY' hne
  have hNodd : Odd (Nat.card (aschbacherSolvableCore 3 (Subgroup.centralizer ({e} : Set G)))) := by
    rwa [inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hodd
  have hQN : Subgroup.centralizer (T₀ : Set G) ≤ Subgroup.normalizer
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T₀ : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T₀ : Set G))))
  have h := le_centralizer_of_split_thetaComponents hZ hZ' (fun h => hne (by rw [h])) hTY hcY'
    (hFT hcF) hT₀ hNodd (CFSG.pCore_isPGroup.map _) hQN
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    ← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact h

end TheoremO

end CFSG.RankThree.PartTwo.Sec11
