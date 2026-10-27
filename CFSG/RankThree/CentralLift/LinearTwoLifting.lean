module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.CentralLift

open Matrix
open CFSG.RankThree.Automorphisms (card_map_of_injective_comp)

variable {F : Type*} [Group F]

theorem eq_one_of_isPerfect_of_mem_center {H : Type*} [Group H] [Group.IsPerfect H]
    (δ : H →* F) (hδ : ∀ x, δ x ∈ Subgroup.center F) : δ = 1 := by
  have hle : commutator H ≤ δ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (hδ y) (δ x))
  have htop : commutator H = ⊤ := Group.isPerfect_def.1 inferInstance
  ext x
  rw [MonoidHom.one_apply]
  exact MonoidHom.mem_ker.1 (hle (htop ▸ Subgroup.mem_top x))

theorem eq_one_of_coprime {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {A : Subgroup F} (hA : IsPGroup p A) (hcop : Nat.Coprime p (Nat.card H)) (δ : H →* F)
    (hδ : ∀ x, δ x ∈ A) : δ = 1 := by
  ext x
  rw [MonoidHom.one_apply]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hA) ⟨δ x, hδ x⟩
  rw [Subgroup.orderOf_mk] at hm
  have hdvd : p ^ m ∣ Nat.card H := hm ▸ (orderOf_map_dvd δ x).trans (orderOf_dvd_natCard x)
  have h1 : orderOf (δ x) = 1 := hm.trans (Nat.Coprime.eq_one_of_dvd (hcop.pow_left m) hdvd)
  exact orderOf_eq_one_iff.1 h1

theorem section_eq_of_forall {H : Type*} [Group H] (ρ : F →* H)
    (hA : ρ.ker ≤ Subgroup.center F) (htriv : ∀ δ : H →* F, (∀ x, δ x ∈ ρ.ker) → δ = 1)
    {σ σ' : H →* F} (hσ : ρ.comp σ = MonoidHom.id H) (hσ' : ρ.comp σ' = MonoidHom.id H) :
    σ = σ' := by
  have hmem : ∀ x, (σ x)⁻¹ * σ' x ∈ ρ.ker := fun x => by
    have h1 := DFunLike.congr_fun hσ x
    have h2 := DFunLike.congr_fun hσ' x
    rw [MonoidHom.comp_apply, MonoidHom.id_apply] at h1 h2
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, inv_mul_cancel]
  let δ : H →* F :=
    { toFun := fun x => (σ x)⁻¹ * σ' x
      map_one' := by rw [map_one, map_one, inv_one, one_mul]
      map_mul' := fun x y => by
        have hc := Subgroup.mem_center_iff.1 (hA (hmem x)) (σ y)⁻¹
        change (σ (x * y))⁻¹ * σ' (x * y) = (σ x)⁻¹ * σ' x * ((σ y)⁻¹ * σ' y)
        calc (σ (x * y))⁻¹ * σ' (x * y) = (σ y)⁻¹ * ((σ x)⁻¹ * σ' x) * σ' y := by
              rw [map_mul, map_mul]
              group
          _ = (σ x)⁻¹ * σ' x * (σ y)⁻¹ * σ' y := by rw [hc]
          _ = (σ x)⁻¹ * σ' x * ((σ y)⁻¹ * σ' y) := by group }
  have h := htriv δ hmem
  ext x
  have hx := DFunLike.congr_fun h x
  rw [MonoidHom.one_apply] at hx
  exact inv_mul_eq_one.1 hx

theorem exists_section_of_coprime {H : Type*} [Group H] [Finite H] [Finite F] (ρ : F →* H)
    (hρ : Function.Surjective ρ) (hA : ρ.ker ≤ Subgroup.center F)
    (hcop : Nat.Coprime (Nat.card ρ.ker) (Nat.card H)) :
    ∃ σ : H →* F, ρ.comp σ = MonoidHom.id H := by
  have hidx : ρ.ker.index = Nat.card H := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top]
  obtain ⟨K, hKcard, -, hAK, -⟩ :=
    CFSG.LyonsUnitaryFour.central_hall_direct_complement ρ.ker hA (hidx ▸ hcop)
  have hinj : Function.Injective (ρ.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : F) ∈ ρ.ker ⊓ K := ⟨hx, x.2⟩
    rw [hAK, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hbij : Function.Bijective (ρ.comp K.subtype) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [hKcard, hidx]⟩
  let e := MulEquiv.ofBijective (ρ.comp K.subtype) hbij
  exact ⟨K.subtype.comp e.symm.toMonoidHom, MonoidHom.ext fun x => e.apply_symm_apply x⟩

variable {k : Type} [Field k] [Finite k]

theorem exists_section_of_isPerfect {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hk : Nat.card k = ℓ ^ f) [Group.IsPerfect (SpecialLinearGroup (Fin 2) k)] [Finite F]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (ρ : F →* SpecialLinearGroup (Fin 2) k)
    (hρ : Function.Surjective ρ) (hA : ρ.ker ≤ Subgroup.center F) (hAp : IsPGroup p ρ.ker) :
    ∃ σ : SpecialLinearGroup (Fin 2) k →* F, ρ.comp σ = MonoidHom.id _ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hperf, hsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective ρ hρ hA inferInstance
  set D := commutator F with hD
  have : Group.IsPerfect D := hperf
  set ρ' := ρ.comp D.subtype with hρ'
  have hker' : ρ'.ker ≤ Subgroup.center D := fun x hx =>
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 (hA hx) (y : F))
  have hZ := CFSG.LocalCores.comap_center_eq_of_perfect hperf ρ' hsurj hker'
  set ψ := (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k))).comp ρ'
    with hψ
  have hψker : ψ.ker = Subgroup.center D := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ]
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hsurj
  obtain ⟨S⟩ : Nonempty (Sylow 2 (Subgroup.center D)) := inferInstance
  set Z₂ : Subgroup D := (S : Subgroup (Subgroup.center D)).map (Subgroup.center D).subtype
    with hZ₂
  have hZ₂c : Z₂ ≤ Subgroup.center D := Subgroup.map_subtype_le _
  have : Z₂.Normal := Subgroup.normal_of_le_center hZ₂c
  have hZ₂ψ : Z₂ ≤ ψ.ker := hψker ▸ hZ₂c
  set ψb := QuotientGroup.lift Z₂ ψ hZ₂ψ with hψb
  have hψbs : Function.Surjective ψb :=
    QuotientGroup.lift_surjective_of_surjective _ _ hψs hZ₂ψ
  have hψbker : ψb.ker = (Subgroup.center D).map (QuotientGroup.mk' Z₂) := by
    rw [hψb, QuotientGroup.ker_lift, hψker]
  have hψbc : ψb.ker ≤ Subgroup.center (D ⧸ Z₂) := by
    rw [hψbker]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z₂)
  set r := (QuotientGroup.mk' Z₂).comp (Subgroup.center D).subtype with hr
  have hrker : r.ker = (S : Subgroup (Subgroup.center D)) := by
    rw [hr, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ₂,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  have hrrange : r.range = ψb.ker := by
    rw [hψbker, hr, MonoidHom.range_comp, Subgroup.range_subtype]
  have hodd : Odd (Nat.card ψb.ker) := by
    rw [← hrrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv, hrker,
      ← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 S.not_dvd_index)
  obtain ⟨h1, h9⟩ :=
    CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hℓ2 hk ψb hψbs hψbc hodd
  have hle3 : Nat.card ψb.ker ≤ 3 := by
    by_cases hq9 : ℓ ^ f = 9
    · exact (h9 hq9).2
    · rw [h1 hq9, Subgroup.card_bot]
      omega
  have hA₀p : IsPGroup p ρ'.ker := by
    refine hAp.of_injective ((D.subtype.comp ρ'.ker.subtype).codRestrict ρ.ker fun x => ?_)
      fun x y hxy => ?_
    · exact x.2
    · have h : ((x : D) : F) = ((y : D) : F) := congrArg (fun z : ρ.ker => (z : F)) hxy
      exact Subtype.ext (Subtype.ext h)
  have hZ₂p : IsPGroup 2 Z₂ := S.isPGroup'.map _
  have hdisj : ρ'.ker ⊓ Z₂ = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne p 2 (by omega) _ _ hA₀p hZ₂p)
  have hinj : Function.Injective ((QuotientGroup.mk' Z₂).comp ρ'.ker.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hmem : (x : D) ∈ ρ'.ker ⊓ Z₂ := ⟨x.2, hx⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcardA₀ : Nat.card ρ'.ker ≤ 3 := by
    rw [← card_map_of_injective_comp _ _ hinj]
    refine le_trans (Subgroup.card_le_of_le ?_) hle3
    rw [hψbker]
    exact Subgroup.map_mono hker'
  have hA₀ : ρ'.ker = ⊥ := by
    obtain ⟨m, hm⟩ := hA₀p.exists_card_eq
    rcases m with _ | m
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero])
    · rw [hm, pow_succ] at hcardA₀
      have : p ≤ p ^ m * p := Nat.le_mul_of_pos_left p (pow_pos hp.pos m)
      omega
  have hbij : Function.Bijective ρ' := ⟨(MonoidHom.ker_eq_bot_iff ρ').1 hA₀, hsurj⟩
  let e := MulEquiv.ofBijective ρ' hbij
  exact ⟨D.subtype.comp e.symm.toMonoidHom, MonoidHom.ext fun x => e.apply_symm_apply x⟩

theorem existsUnique_section_specialLinearGroup_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hk : Nat.card k = ℓ ^ f) [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (ρ : F →* SpecialLinearGroup (Fin 2) k) (hρ : Function.Surjective ρ)
    (hA : ρ.ker ≤ Subgroup.center F) (hAp : IsPGroup p ρ.ker) :
    (∃ σ : SpecialLinearGroup (Fin 2) k →* F, ρ.comp σ = MonoidHom.id _) ∧
    ∀ σ σ' : SpecialLinearGroup (Fin 2) k →* F, ρ.comp σ = MonoidHom.id _ →
      ρ.comp σ' = MonoidHom.id _ → σ = σ' := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype k := Fintype.ofFinite k
  have hq2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have hq3 : 3 ≤ Nat.card k := by
    rw [hk]
    have hℓ3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    exact hℓ3.trans (Nat.le_self_pow hf ℓ)
  rcases (show Nat.card k = 3 ∨ 4 ≤ Nat.card k by omega) with h3 | h4
  ·
    have hSL : Nat.card (SpecialLinearGroup (Fin 2) k) = 24 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), h3,
        Finset.Icc_self, Finset.prod_singleton]
      norm_num
    have hp24 : Nat.Coprime p 24 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3'
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h3'
        omega
    have hcop : Nat.Coprime (Nat.card ρ.ker) (Nat.card (SpecialLinearGroup (Fin 2) k)) := by
      obtain ⟨m, hm⟩ := hAp.exists_card_eq
      rw [hm, hSL]
      exact hp24.pow_left m
    refine ⟨exists_section_of_coprime ρ hρ hA hcop, fun σ σ' hσ hσ' =>
      section_eq_of_forall ρ hA (fun δ hδ => eq_one_of_coprime hAp (hSL ▸ hp24) δ hδ) hσ hσ'⟩
  ·
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) := by
      refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (Finset.univ : Finset k).card by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4)
      exact ⟨s, hs⟩
    refine ⟨exists_section_of_isPerfect hℓ2 hk hp hp3 ρ hρ hA hAp, fun σ σ' hσ hσ' =>
      section_eq_of_forall ρ hA (fun δ hδ => eq_one_of_isPerfect_of_mem_center δ
        fun x => hA (hδ x)) hσ hσ'⟩

theorem odd_field_linear_two_central_large_prime_homomorphism_lifting {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (_hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = ℓ ^ f) {E G : Type*} [Group E] [Group G] [Finite E] [Finite G]
    (π : E →* G) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (α : SpecialLinearGroup (Fin 2) k →* G) :
    (∃! αh : SpecialLinearGroup (Fin 2) k →* E, π.comp αh = α) ∧
    ∀ αh : SpecialLinearGroup (Fin 2) k →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : SpecialLinearGroup (Fin 2) k →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have hℓ2 : ℓ ≠ 2 := hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  have hlift : ∀ β : SpecialLinearGroup (Fin 2) k →* G,
      (∃ βh : SpecialLinearGroup (Fin 2) k →* E, π.comp βh = β) ∧
      ∀ β₁ β₂ : SpecialLinearGroup (Fin 2) k →* E, π.comp β₁ = β → π.comp β₂ = β → β₁ = β₂ := by
    intro β
    set P := (β.comp (MonoidHom.fst _ E)).eqLocus (π.comp (MonoidHom.snd _ E)) with hP
    set ρ := (MonoidHom.fst _ E).comp P.subtype with hρ
    have hmemP : ∀ y : SpecialLinearGroup (Fin 2) k × E, y ∈ P ↔ β y.1 = π y.2 := fun _ =>
      Iff.rfl
    have hρs : Function.Surjective ρ := by
      intro x
      obtain ⟨e, he⟩ := hπ (β x)
      exact ⟨⟨(x, e), (hmemP _).2 he.symm⟩, rfl⟩
    have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : SpecialLinearGroup (Fin 2) k × E).1 = 1 :=
      fun _ => Iff.rfl
    have hkerπ : ∀ y : P, y ∈ ρ.ker → (y : SpecialLinearGroup (Fin 2) k × E).2 ∈ π.ker := by
      intro y hy
      rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
    have hA : ρ.ker ≤ Subgroup.center P := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro z
      have hc := Subgroup.mem_center_iff.1 (hC (hkerπ y hy))
        (z : SpecialLinearGroup (Fin 2) k × E).2
      have h1 : (y : SpecialLinearGroup (Fin 2) k × E).1 = 1 := (hρker y).1 hy
      refine Subtype.ext (Prod.ext ?_ hc)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
    have hAp : IsPGroup p ρ.ker := by
      refine hCp.of_injective
        ((MonoidHom.snd _ E).comp (P.subtype.comp ρ.ker.subtype) |>.codRestrict π.ker
          fun y => hkerπ y y.2) fun y z hyz => ?_
      have h2 : (y : P).1.2 = (z : P).1.2 := congrArg Subtype.val hyz
      exact Subtype.ext (Subtype.ext (Prod.ext (((hρker y).1 y.2).trans ((hρker z).1 z.2).symm)
        h2))
    obtain ⟨⟨σ, hσ⟩, huniq⟩ :=
      existsUnique_section_specialLinearGroup_two hℓ hℓ2 hk hp hp3 ρ hρs hA hAp
    have hsec : ∀ β₁ : SpecialLinearGroup (Fin 2) k →* E, π.comp β₁ = β →
        ∃ σ₁ : SpecialLinearGroup (Fin 2) k →* P, ρ.comp σ₁ = MonoidHom.id _ ∧
          (MonoidHom.snd _ E).comp (P.subtype.comp σ₁) = β₁ := by
      intro β₁ hβ₁
      refine ⟨((MonoidHom.id _).prod β₁).codRestrict P fun x => ?_, ?_, ?_⟩
      · rw [hmemP]
        exact (DFunLike.congr_fun hβ₁ x).symm
      · ext x
        rfl
      · ext x
        rfl
    refine ⟨⟨(MonoidHom.snd _ E).comp (P.subtype.comp σ), ?_⟩, fun β₁ β₂ hβ₁ hβ₂ => ?_⟩
    · ext x
      have hx := DFunLike.congr_fun hσ x
      change ((σ x : P) : SpecialLinearGroup (Fin 2) k × E).1 = x at hx
      change π ((σ x : P) : SpecialLinearGroup (Fin 2) k × E).2 = β x
      rw [← (hmemP _).1 (σ x).2, hx]
    · obtain ⟨σ₁, hσ₁, rfl⟩ := hsec β₁ hβ₁
      obtain ⟨σ₂, hσ₂, rfl⟩ := hsec β₂ hβ₂
      rw [huniq σ₁ σ₂ hσ₁ hσ₂]
  obtain ⟨⟨αh, hαh⟩, -⟩ := hlift α
  refine ⟨⟨αh, hαh, fun β hβ => (hlift α).2 β αh hβ hαh⟩, fun αh' hαh' => ?_⟩
  have hconj : ∀ e : E, π.comp ((MulAut.conj e).toMonoidHom.comp αh') =
      (MulAut.conj (π e)).toMonoidHom.comp α := by
    intro e
    ext x
    change π (e * αh' x * e⁻¹) = π e * α x * (π e)⁻¹
    rw [map_mul, map_mul, map_inv, ← DFunLike.congr_fun hαh' x]
    rfl
  refine ⟨fun hα x y hxy => hα ?_, fun e β => ⟨fun hβ => ?_, fun hβ => ?_⟩,
    fun g hg e he x => ?_⟩
  · rw [← DFunLike.congr_fun hαh' x, ← DFunLike.congr_fun hαh' y]
    exact congrArg π hxy
  · exact (hlift _).2 β _ hβ (hconj e)
  · rw [hβ]
    exact hconj e
  ·
    have hα : (MulAut.conj (π e)).toMonoidHom.comp α = α := by
      ext y
      change π e * α y * (π e)⁻¹ = α y
      rw [he, hg y, mul_inv_cancel_right]
    have h := (hlift α).2 _ αh' ((hconj e).trans hα) hαh'
    have hx := DFunLike.congr_fun h x
    change e * αh' x * e⁻¹ = αh' x at hx
    calc e * αh' x = e * αh' x * e⁻¹ * e := by group
      _ = αh' x * e := by rw [hx]

end CFSG.RankThree.CentralLift
