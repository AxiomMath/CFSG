module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwoAction
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item1012ResProof

open CFSG

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {p k : ℕ} {y : G} (hy : y ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy,
    one_zpow, Subgroup.coe_one]

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hy, one_zpow, Subgroup.coe_one]

theorem perfect_hom_eq_one {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 3 Q) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 2)
    {H : Type*} [Group H] [Group.IsPerfect H] (α : H →* MulAut Q) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hα
  have : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hα (MonoidHom.ext fun y => MulEquiv.ext fun q => Subsingleton.elim _ _)
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ :=
    CFSG.SectionRank.Ccomm.supercritical_witness (p := 3) (by norm_num) hQ
  obtain ⟨-, -, -, -, h5, -⟩ := CFSG.SectionRank.Ccomm.critical_rank_two_action_recognition
    (p := 3) (by norm_num) hQ hrank D hDexp hker α hα _ rfl
  omega

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_mem_sylow {F : Type*} [Group F] [Finite F]
    [Group.IsPerfect F] {p : ℕ} [Fact p.Prime] (R : Sylow p F)
    (hR : IsMulCommutative (R : Subgroup F)) {z : F} (hz : z ∈ Subgroup.center F)
    (hzR : z ∈ (R : Subgroup F)) : z = 1 := by
  have key : ∀ (k : ℕ) (g₀ : F), g₀⁻¹ * z ^ k * g₀ ∈ (R : Subgroup F) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have hc := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (R : Subgroup F)) z key
  have h2 : MonoidHom.transfer (MonoidHom.id (R : Subgroup F)) z = 1 :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  rw [h2] at h1
  have h3 : z ^ (R : Subgroup F).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  obtain ⟨k, hk⟩ := R.isPGroup' ⟨z, hzR⟩
  have hk' : z ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (p ^ k) (R : Subgroup F).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr R.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3))

theorem pRank_le_two_of_le {X : Type*} [Group X] [Finite X] {C Q : Subgroup X} (hQC : Q ≤ C)
    (hrank : ∀ E : Subgroup X, E ≤ C → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 2 := by
  refine csSup_le ?_ ?_
  · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => ?_⟩, by simp⟩
    rw [Subgroup.mem_bot.mp hx, one_pow]
  rintro k ⟨E, -, hE, hEk⟩
  have hEC : E.map Q.subtype ≤ C := (Subgroup.map_subtype_le E).trans hQC
  have hEe : CFSG.Assembly.IsElemAbelian 3 (E.map Q.subtype) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      have hab := congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      change (a : X) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val hab
    · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hE.2 y' hy', Subgroup.coe_one]
  have h9 := hrank _ hEC hEe
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hEk] at h9
  by_contra hk
  have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_lift {X Y : Type*} [Group X] [Finite X] [Group Y]
    [Finite Y] (π : X →* Y)
    (hrank : ∀ E : Subgroup X, E ≤ π.ker → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {F : Subgroup Y} (hFperf : Group.IsPerfect F) (hF3 : 3 ∣ Nat.card F)
    (hFp : ∀ P : Subgroup Y, P ≤ F → IsPGroup 3 P → Nat.card P ≤ 3)
    (hFle : F ≤ (perfectResidual π.range).map π.range.subtype)
    {x : X} (hx : x ∈ π.ker) (hx3 : x ^ 3 = 1) :
    ∃ t : X, t ^ 3 = 1 ∧ t * x = x * t ∧ π t ∈ F ∧ π t ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := π.ker with hC
  have hx3' : (⟨x, hx⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_pow_three hx3').exists_le_sylow
  set Q : Subgroup X := (P : Subgroup C).map C.subtype with hQ
  have hxQ : x ∈ Q := ⟨⟨x, hx⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hQp : IsPGroup 3 Q := P.isPGroup'.map C.subtype
  set M := Subgroup.normalizer (Q : Set X) with hM
  have hFrat : M ⊔ C = ⊤ := Sylow.normalizer_sup_eq_top P
  have hMrange : M.map π = π.range := by
    rw [MonoidHom.range_eq_map, ← hFrat, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  set J : Subgroup X := (perfectResidual M).map M.subtype with hJ
  have hJM : J ≤ M := Subgroup.map_subtype_le _
  have hJmap : J.map π = (perfectResidual π.range).map π.range.subtype := by
    rw [hJ, Subgroup.map_map, (perfect_residual_transport (π.comp M.subtype)).1]
    have hr : (π.comp M.subtype).range = π.range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hMrange]
    rw [hr]
  have hJQ : ∀ j ∈ J, ∀ q ∈ Q, j * q = q * j := by
    have : Group.IsPerfect (perfectResidual M) :=
      (perfect_residual_characterization (G := M)).2.2.1
    have : Finite Q := inferInstance
    have hα := perfect_hom_eq_one hQp (pRank_le_two_of_le hQC (hC ▸ hrank))
      (Q.normalizerMonoidHom.comp (perfectResidual M).subtype)
    intro j hj q hq
    obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.mp hj
    have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : X))
      (DFunLike.congr_fun hα ⟨j', hj'⟩)
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.one_apply,
      MulAut.one_apply] at h1
    change (j' : X) * q * (j' : X)⁻¹ = q at h1
    calc (j' : X) * q = (j' : X) * q * (j' : X)⁻¹ * j' := by group
      _ = q * j' := by rw [h1]
  have hJC3 : ∀ y ∈ J, y ∈ C → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ Q := by
    intro y hyJ hyC ⟨k, hk⟩
    set y' : C := ⟨y, hyC⟩ with hy'
    have hy'k : y' ^ 3 ^ k = 1 := Subtype.ext (by simpa [hy'] using hk)
    have hy'N : y' ∈ Subgroup.normalizer ((P : Subgroup C) : Set C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hyM := hJM hyJ
      rw [hM, Subgroup.mem_normalizer_iff] at hyM
      have h1 : C.subtype c ∈ (P : Subgroup C).map C.subtype ↔
          C.subtype (y' * c * y'⁻¹) ∈ (P : Subgroup C).map C.subtype := hyM (c : X)
      rwa [Subgroup.mem_map_iff_mem C.subtype_injective,
        Subgroup.mem_map_iff_mem C.subtype_injective] at h1
    have h2 := (isPGroup_zpowers_of_pow hy'k).inf_normalizer_sylow P
    have hmem : y' ∈ Subgroup.zpowers y' ⊓ (P : Subgroup C) := by
      rw [← h2]
      exact ⟨Subgroup.mem_zpowers _, hy'N⟩
    exact ⟨y', hmem.2, rfl⟩
  set F₁ : Subgroup X := J ⊓ F.comap π with hF₁
  set F₀ : Subgroup X := (perfectResidual F₁).map F₁.subtype with hF₀
  have hF₀F₁ : F₀ ≤ F₁ := Subgroup.map_subtype_le _
  have hF₀J : F₀ ≤ J := hF₀F₁.trans inf_le_left
  have hF₁map : F₁.map π = F := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_right
    · intro f hf
      have hf' : f ∈ J.map π := hJmap ▸ hFle hf
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hf'
      exact Subgroup.mem_map_of_mem π ⟨hj, hf⟩
  have hF₀map : F₀.map π = F := by
    rw [hF₀, Subgroup.map_map, (perfect_residual_transport (π.comp F₁.subtype)).1]
    have hr : (π.comp F₁.subtype).range = F := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₁map]
    rw [hr]
    exact CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect hFperf
  have hF₀perf : Group.IsPerfect F₀ := CFSG.RankThree.PartTwo.isPerfect_map_subtype
    (perfect_residual_characterization (G := F₁)).2.2.1
  have h3F₀ : 3 ∣ Nat.card F₀ := by
    have h := Subgroup.card_map_dvd (H := F₀) π
    rw [hF₀map] at h
    exact hF3.trans h
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := F₀) 3 h3F₀
  have ht₀3 : t₀ ^ 3 = 1 := ht₀ ▸ pow_orderOf_eq_one t₀
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_pow_three ht₀3).exists_le_sylow
  have ht₀R : t₀ ∈ (R : Subgroup F₀) := hR (Subgroup.mem_zpowers _)
  have hRC : ∀ r ∈ (R : Subgroup F₀), ((r : X) ∈ C) → ∀ f : F₀, f * r = r * f := by
    intro r hr hrC f
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
    have hk' : (r : X) ^ 3 ^ k = 1 := by
      simpa using congrArg (fun z : (R : Subgroup F₀) => ((z : F₀) : X)) hk
    have hrQ : (r : X) ∈ Q := hJC3 r (hF₀J r.2) hrC ⟨k, hk'⟩
    exact Subtype.ext (hJQ f (hF₀J f.2) r hrQ)
  have hRab : IsMulCommutative (R : Subgroup F₀) := by
    set fR : (R : Subgroup F₀) →* Y := π.comp (F₀.subtype.comp (R : Subgroup F₀).subtype)
      with hfR
    have hker : fR.rangeRestrict.ker ≤ Subgroup.center _ := by
      intro r hr
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hr
      rw [Subgroup.mem_center_iff]
      intro r'
      exact Subtype.ext (hRC r r.2 hr r')
    have hle : fR.range ≤ F := by
      rintro _ ⟨r, rfl⟩
      exact (hF₀F₁ (r : F₀).2).2
    have hp : IsPGroup 3 fR.range :=
      R.isPGroup'.of_surjective fR.rangeRestrict fR.rangeRestrict_surjective
    have hcard := hFp _ hle hp
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    have hcyc : IsCyclic fR.range := by
      have hm1 : m ≤ 1 := by
        by_contra hlt
        have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m
      · rw [pow_zero] at hm
        have : Subsingleton fR.range := (Nat.card_eq_one_iff_unique.mp hm).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hm
        exact isCyclic_of_prime_card (p := 3) hm
    exact fR.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have ht₀C : (t₀ : X) ∉ C := by
    intro hC'
    have hz : t₀ ∈ Subgroup.center F₀ :=
      Subgroup.mem_center_iff.mpr fun f => hRC t₀ ht₀R hC' f
    have h1 := eq_one_of_mem_center_of_mem_sylow R hRab hz ht₀R
    rw [h1, orderOf_one] at ht₀
    norm_num at ht₀
  refine ⟨t₀, ?_, hJQ t₀ (hF₀J t₀.2) x hxQ, (hF₀F₁ t₀.2).2, fun h => ht₀C h⟩
  simpa using congrArg Subtype.val ht₀3

end CFSG.RankThree.PartTwo.Sec10.Item1012ResProof
