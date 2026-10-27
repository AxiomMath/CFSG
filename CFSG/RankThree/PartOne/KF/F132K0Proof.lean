module

public import CFSG.RankThree.PartOne.KF.F132KtExc
public import CFSG.RankThree.PartOne.KF.K0Unique

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.PartOne.KFK0 CFSG.RankThree.PartOne.KFU

theorem exists_finset_card_four {F : Type} [Field F] [Finite F] (h : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  have hle : 4 ≤ (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  exact ⟨s, hs⟩

theorem exists_SL2_equiv {G : Type} [Group G] {K : Subgroup G} {f : ℕ}
    (h : StatedClassicalModel ↥K .PSL 2 2 f) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : Finite F₁) (_ : CharP F₁ 2), Nat.card F₁ = 2 ^ f ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) F₁ ≃* ↥K) := by
  obtain ⟨-, F₁, hF₁, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP F₁ 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  obtain ⟨e'⟩ := nonempty_SL2_mulEquiv_statedProj (F := F₁)
  exact ⟨F₁, hF₁, hfin, inferInstance, hcard, ⟨e'.trans e.symm⟩⟩

theorem eq_one_of_central_of_SL2 {M₀ : Type} [Group M₀] {B : Subgroup M₀} {F₁ : Type} [Field F₁]
    [CharP F₁ 2] (ψ : Matrix.SpecialLinearGroup (Fin 2) F₁ ≃* ↥B) {x : M₀} (hx : x ∈ B)
    (hxc : x ∈ Subgroup.center M₀) : x = 1 := by
  set y := ψ.symm ⟨x, hx⟩ with hy
  have hyc : y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply ψ.injective
    rw [map_mul, map_mul, hy, MulEquiv.apply_symm_apply]
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hxc) (ψ g : M₀))
  rw [center_SL2_eq_bot] at hyc
  have : y = 1 := hyc
  have h1 : (⟨x, hx⟩ : ↥B) = 1 := by
    rw [← ψ.apply_symm_apply ⟨x, hx⟩, ← hy, this, map_one]
  exact congrArg Subtype.val h1

theorem kfK0 : KFK0 := by
  intro G _ _ p E t f hp hp5 hE hmov hexc K K' hK hK' hKm hK'm hNK hNK'
  classical
  obtain ⟨hf1, hpq, hmod⟩ := hexc
  have hf3 : 3 ≤ f := three_le_of_dvd hp5 hf1 hpq
  obtain ⟨⟨u₀, hu₀N⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hmov
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hu₀E : u₀ ∈ E := by
    obtain ⟨x, -, hx⟩ := hu₀N
    rw [← hx]
    exact x.2
  have hu₀p : u₀ ^ p = 1 := by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian u₀ hu₀E
  obtain ⟨hadm, F, hFf, hFfin, hFcard, ⟨e⟩⟩ := hmod
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := f * 2) (by rw [hFcard, pow_mul])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₀ := kZero p E t with hK₀
  have hne : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  obtain ⟨-, hZ⟩ := isQuasisimple_statedSU_of_card (n := 3) hFcard le_rfl hne
  let eSU := equivStatedSU hFcard 3
  let N : Subgroup (StatedSU 3 (2 ^ f) F) := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ f) F)
  let π : ↥(SU (unitaryInvolution F 2 f) 3) →* ↥K₀ ⧸ Subgroup.center ↥K₀ :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp eSU.toMonoidHom)
  have hπ : Function.Surjective π := by
    show Function.Surjective (e.symm ∘ (QuotientGroup.mk' N) ∘ eSU)
    exact e.symm.surjective.comp ((QuotientGroup.mk'_surjective N).comp eSU.surjective)
  have hker : ∀ z, π z = 1 → z ^ 3 = 1 ∧ ∀ g, g * z = z * g := by
    intro z hz
    have h1 : QuotientGroup.mk' N (eSU z) = 1 := by
      have := congrArg e hz
      simpa [π] using this
    have hmem : eSU z ∈ N := (QuotientGroup.eq_one_iff _).1 h1
    constructor
    · have hN3 : Nat.card N ∣ 3 := by
        have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hFcard (n := 3)
          (by norm_num)).2.2
        rw [this]
        exact Nat.gcd_dvd_left 3 _
      have h2 : orderOf (⟨eSU z, hmem⟩ : ↥N) ∣ 3 := (orderOf_dvd_natCard _).trans hN3
      have h3 : (⟨eSU z, hmem⟩ : ↥N) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h2
      have h4 : (eSU z) ^ 3 = 1 := congrArg Subtype.val h3
      apply eSU.injective
      rw [map_pow, h4, map_one]
    · intro g
      have hc : eSU z ∈ Subgroup.center (StatedSU 3 (2 ^ f) F) := by rw [hZ]; exact hmem
      apply eSU.injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.1 hc) (eSU g)
  let κ : ↥K₀ →* ↥K₀ ⧸ Subgroup.center ↥K₀ := QuotientGroup.mk' _
  obtain ⟨F₁, hF₁f, hF₁fin, hF₁c, hF₁card, ⟨ψ₀⟩⟩ := exists_SL2_equiv hKm
  obtain ⟨F₂, hF₂f, hF₂fin, hF₂c, hF₂card, ⟨ψ₀'⟩⟩ := exists_SL2_equiv hK'm
  let B : Subgroup ↥K₀ := K.subgroupOf K₀
  let B' : Subgroup ↥K₀ := K'.subgroupOf K₀
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F₁ ≃* ↥B :=
    ψ₀.trans (Subgroup.subgroupOfEquivOfLe hK).symm
  let ψ' : Matrix.SpecialLinearGroup (Fin 2) F₂ ≃* ↥B' :=
    ψ₀'.trans (Subgroup.subgroupOfEquivOfLe hK').symm
  have hinj : ∀ x ∈ B, κ x = 1 → x = 1 := fun x hx h =>
    eq_one_of_central_of_SL2 ψ hx ((QuotientGroup.eq_one_iff _).1 h)
  have hinj' : ∀ x ∈ B', κ x = 1 → x = 1 := fun x hx h =>
    eq_one_of_central_of_SL2 ψ' hx ((QuotientGroup.eq_one_iff _).1 h)
  let u₀' : ↥K₀ := ⟨u₀, hK (hNK hu₀N)⟩
  have hu₀B : u₀' ∈ B := Subgroup.mem_subgroupOf.2 (hNK hu₀N)
  have hu₀B' : u₀' ∈ B' := Subgroup.mem_subgroupOf.2 (hNK' hu₀N)
  have hu₀'p : u₀' ^ p = 1 := Subtype.ext (by simpa using hu₀p)
  have hκu₀ : κ u₀' ≠ 1 := fun h => hu₀1' (congrArg Subtype.val (hinj _ hu₀B h))
  have hmap : B.map κ = B'.map κ :=
    subgroups_SL2_unique hFcard hf1 κ π hπ hker hp hp5 hpq hu₀'p hκu₀ hF₁card hF₂card ψ ψ' hinj hinj'
      hu₀B hu₀B'
  have h4 : ∀ {F₃ : Type} [Field F₃] [Finite F₃], Nat.card F₃ = 2 ^ f → 4 ≤ Nat.card F₃ := by
    intro F₃ _ _ h
    rw [h]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperf : ⁅B, B⁆ = B := by
    have : Group.IsPerfect ↥B :=
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ
        (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_card_four (h4 hF₁card)))).1
    exact Subgroup.commutator_eq_self
  have hperf' : ⁅B', B'⁆ = B' := by
    have : Group.IsPerfect ↥B' :=
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ'
        (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_card_four (h4 hF₂card)))).1
    exact Subgroup.commutator_eq_self
  have hBB : B = B' := eq_of_perfect_of_map_center_eq hperf hperf' hmap
  have := Subgroup.subgroupOf_inj.1 hBB
  rwa [inf_of_le_left hK, inf_of_le_left hK'] at this

end CFSG.RankThree.PartOne.KF132
