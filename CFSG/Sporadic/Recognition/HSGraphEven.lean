module

public import CFSG.Sporadic.Recognition.HSGraphAut
public import CFSG.Sporadic.Recognition.HSGraphSimple
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign MulAction

universe u

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {𝓑 : Finset (Finset Ω)}

variable (𝓑) in
@[expose] def signHom : autGroup 𝓑 →* ℤˣ := Equiv.Perm.sign.comp (autGroup 𝓑).subtype

@[expose] def evenSubgroup (𝓑 : Finset (Finset Ω)) : Subgroup (autGroup 𝓑) := (signHom 𝓑).ker

theorem index_evenSubgroup (hodd : ∃ s ∈ autGroup 𝓑, Equiv.Perm.sign s = -1) :
    (evenSubgroup 𝓑).index = 2 := by
  obtain ⟨s, hs, hsign⟩ := hodd
  have hsurj : Function.Surjective (signHom 𝓑) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨⟨s, hs⟩, hsign⟩
  rw [evenSubgroup, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  exact Fintype.card_units_int

@[expose] noncomputable def MData.toStab (D : MData 𝓑) :
    D.carrier →* stabilizer (autGroup 𝓑) (vInf : Vert 𝓑) :=
  (stabEquiv (𝓑 := 𝓑)).symm.toMonoidHom.comp (Subgroup.inclusion D.le)

omit [Fintype Ω] [DecidableEq Ω] in
theorem MData.restrictΩ_toStab (D : MData 𝓑) (τ : D.carrier) :
    restrictΩ 𝓑 (D.toStab τ) = τ :=
  congrArg Subtype.val ((stabEquiv (𝓑 := 𝓑)).apply_symm_apply (Subgroup.inclusion D.le τ))

omit [Fintype Ω] [DecidableEq Ω] in
theorem MData.toStab_smul_vPt (D : MData 𝓑) (τ : D.carrier) (a : Ω) :
    D.toStab τ • (vPt a : Vert 𝓑) = vPt ((τ : Equiv.Perm Ω) a) := by
  rw [restrictΩ_smul, D.restrictΩ_toStab]

omit [Fintype Ω] [DecidableEq Ω] in
theorem MData.toStab_smul_vBlk (D : MData 𝓑) (τ : D.carrier) (B C : {B // B ∈ 𝓑})
    (h : B.1.map (τ : Equiv.Perm Ω).toEmbedding = C.1) :
    D.toStab τ • (vBlk B : Vert 𝓑) = vBlk C := by
  obtain ⟨C', hC', hC'B⟩ := apply_vBlk (D.toStab τ).1.2 (D.toStab τ).2 B
  have hres : resPerm (D.toStab τ).1.1 (D.toStab τ).1.2 (D.toStab τ).2 = (τ : Equiv.Perm Ω) :=
    D.restrictΩ_toStab τ
  rw [hres, h] at hC'B
  exact hC'.trans (congrArg vBlk (Subtype.ext hC'B))

theorem MData.signHom_toStab (D : MData 𝓑) (τ : D.carrier) : signHom 𝓑 (D.toStab τ).1 = 1 := by
  have : Finite D.carrier := Nat.finite_of_card_ne_zero (by rw [D.card]; norm_num)
  have := D.simple
  have h := eq_one_of_simple_of_two_lt (G := D.carrier) (by rw [D.card]; norm_num)
    ((signHom 𝓑).comp ((stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)).subtype.comp D.toStab))
  exact DFunLike.congr_fun h τ

@[expose] def stabEvenToStab :
    stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑) →* stabilizer (autGroup 𝓑) (vInf : Vert 𝓑) where
  toFun g := ⟨g.1.1, g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabEvenToStab_injective :
    Function.Injective (stabEvenToStab (𝓑 := 𝓑)) := by
  intro g g' h
  have h2 := Subtype.ext_iff.1 h
  exact Subtype.ext (Subtype.ext h2)

@[expose] noncomputable def MData.toStabEven (D : MData 𝓑) (τ : D.carrier) :
    stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑) :=
  ⟨⟨(D.toStab τ).1, D.signHom_toStab τ⟩, (D.toStab τ).2⟩

theorem MData.exists_stabEven_vPt (D : MData 𝓑) (a b : Ω) :
    ∃ g : stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑), g • (vPt a : Vert 𝓑) = vPt b := by
  obtain ⟨τ, hτ, hab⟩ := D.pt a b
  exact ⟨D.toStabEven ⟨τ, hτ⟩, by
    change D.toStab ⟨τ, hτ⟩ • (vPt a : Vert 𝓑) = _
    rw [D.toStab_smul_vPt, hab]⟩

theorem MData.exists_stabEven_vBlk (D : MData 𝓑) (B C : {B // B ∈ 𝓑}) :
    ∃ g : stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑), g • (vBlk B : Vert 𝓑) = vBlk C := by
  obtain ⟨τ, hτ, h⟩ := D.blk B.1 B.2 C.1 C.2
  exact ⟨D.toStabEven ⟨τ, hτ⟩, D.toStab_smul_vBlk ⟨τ, hτ⟩ B C h⟩

theorem range_orbit_stabilizer_even [Nonempty Ω] (hne : 𝓑.Nonempty) (D : MData 𝓑) :
    Set.range (orbit (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) : Vert 𝓑 → Set (Vert 𝓑)) =
      {{vInf}, Set.range vPt, Set.range vBlk} :=
  range_orbit_eq _ hne (fun g => g.2) (fun g u v => g.1.1.2 u v) D.exists_stabEven_vPt
    D.exists_stabEven_vBlk

theorem isPretransitive_evenSubgroup (D : MData 𝓑)
    (hψ : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B)
    (hodd : ∃ s ∈ autGroup 𝓑, s vInf = vInf ∧ Equiv.Perm.sign s = -1) :
    IsPretransitive (evenSubgroup 𝓑) (Vert 𝓑) := by
  obtain ⟨ψ, hψ, a₀, B₀, h1, h2⟩ := hψ
  obtain ⟨s, hs, hsinf, hsign⟩ := hodd
  let ψ' : autGroup 𝓑 := ⟨ψ, hψ⟩
  let s' : autGroup 𝓑 := ⟨s, hs⟩
  have hs'sign : signHom 𝓑 s' = -1 := hsign
  have hp : ∃ g : evenSubgroup 𝓑, g • (vInf : Vert 𝓑) = vPt a₀ := by
    rcases Int.units_eq_one_or (signHom 𝓑 ψ') with h | h
    · exact ⟨⟨ψ', MonoidHom.mem_ker.2 h⟩, h1⟩
    · refine ⟨⟨ψ' * s', MonoidHom.mem_ker.2 ?_⟩, ?_⟩
      · rw [map_mul, h, hs'sign]
        norm_num
      · change ψ (s vInf) = _
        rw [hsinf, h1]
  have hb : ∃ g : evenSubgroup 𝓑, g • (vInf : Vert 𝓑) = vBlk B₀ := by
    refine ⟨⟨ψ' * ψ', MonoidHom.mem_ker.2 ?_⟩, ?_⟩
    · rw [map_mul]
      exact Int.units_mul_self _
    · change ψ (ψ vInf) = _
      rw [h1, h2]
  have hall : ∀ u : Vert 𝓑, ∃ g : evenSubgroup 𝓑, g • (vInf : Vert 𝓑) = u := by
    intro u
    rcases u with _ | b | C
    · exact ⟨1, one_smul _ _⟩
    · obtain ⟨m, hm⟩ := D.exists_stabEven_vPt a₀ b
      obtain ⟨g, hg⟩ := hp
      exact ⟨m.1 * g, by rw [mul_smul, hg]; exact hm⟩
    · obtain ⟨m, hm⟩ := D.exists_stabEven_vBlk B₀ C
      obtain ⟨g, hg⟩ := hb
      exact ⟨m.1 * g, by rw [mul_smul, hg]; exact hm⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨g₁, h₁⟩ := hall x
  obtain ⟨g₂, h₂⟩ := hall y
  exact ⟨g₂ * g₁⁻¹, by rw [mul_smul, ← h₁, inv_smul_smul, h₂]⟩

theorem card_evenSubgroup (hodd : ∃ s ∈ autGroup 𝓑, Equiv.Perm.sign s = -1)
    (hA : Nat.card (autGroup 𝓑) = 88704000) : Nat.card (evenSubgroup 𝓑) = 44352000 := by
  have h := Subgroup.card_mul_index (evenSubgroup 𝓑)
  rw [index_evenSubgroup hodd, hA] at h
  omega

theorem card_stabilizer_even (D : MData 𝓑)
    (hψ : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B)
    (hodd : ∃ s ∈ autGroup 𝓑, s vInf = vInf ∧ Equiv.Perm.sign s = -1)
    (hΩ : Fintype.card Ω = 22) (h𝓑 : 𝓑.card = 77) (hA : Nat.card (autGroup 𝓑) = 88704000) :
    Nat.card (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) = 443520 := by
  have := isPretransitive_evenSubgroup D hψ hodd
  have h := ncard_orbit_mul_card_stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)
  rw [orbit_eq_univ, Set.ncard_univ, natCard_vert hΩ h𝓑,
    card_evenSubgroup (let ⟨s, hs, _, h⟩ := hodd; ⟨s, hs, h⟩) hA] at h
  omega

omit [DecidableEq Ω] in
theorem ncard_invariant (G : Type*) [Group G] [MulAction G (Vert 𝓑)] (hΩ : Fintype.card Ω = 22)
    (h𝓑 : 𝓑.card = 77) (h1 : ∀ g : G, g • (vInf : Vert 𝓑) = vInf)
    (h2 : ∀ (g : G) (u v : Vert 𝓑), (hsGraph 𝓑).Adj (g • u) (g • v) ↔ (hsGraph 𝓑).Adj u v)
    (h3 : ∀ a b : Ω, ∃ g : G, g • (vPt a : Vert 𝓑) = vPt b)
    (h4 : ∀ B C : {B // B ∈ 𝓑}, ∃ g : G, g • (vBlk B : Vert 𝓑) = vBlk C)
    (T : Set (Vert 𝓑)) (hv : vInf ∈ T) (hT : ∀ g : G, ∀ t ∈ T, g • t ∈ T) :
    T.ncard = 1 ∨ T.ncard = 23 ∨ T.ncard = 78 ∨ T.ncard = 100 := by
  have o2 := orbit_vPt_eq G h1 h2 h3
  have o3 := orbit_vBlk_eq G h1 h2 h4
  have hP : (∃ a, (vPt a : Vert 𝓑) ∈ T) → Set.range (vPt : Ω → Vert 𝓑) ⊆ T := by
    rintro ⟨a, ha⟩ _ ⟨b, rfl⟩
    have : (vPt b : Vert 𝓑) ∈ orbit G (vPt a : Vert 𝓑) := by
      rw [o2 a]
      exact ⟨b, rfl⟩
    obtain ⟨g, hg⟩ := this
    rw [← hg]
    exact hT g _ ha
  have hQ : (∃ B, (vBlk B : Vert 𝓑) ∈ T) → Set.range (vBlk : {B // B ∈ 𝓑} → Vert 𝓑) ⊆ T := by
    rintro ⟨B, hB⟩ _ ⟨C, rfl⟩
    have : (vBlk C : Vert 𝓑) ∈ orbit G (vBlk B : Vert 𝓑) := by
      rw [o3 B]
      exact ⟨C, rfl⟩
    obtain ⟨g, hg⟩ := this
    rw [← hg]
    exact hT g _ hB
  have hcP : (Set.range (vPt : Ω → Vert 𝓑)).ncard = 22 := by
    rw [Set.ncard_range_of_injective vPt_injective, Nat.card_eq_fintype_card, hΩ]
  have hcQ : (Set.range (vBlk : {B // B ∈ 𝓑} → Vert 𝓑)).ncard = 77 := by
    rw [Set.ncard_range_of_injective vBlk_injective, Nat.card_eq_fintype_card, Fintype.card_coe,
      h𝓑]
  have hnP : (vInf : Vert 𝓑) ∉ Set.range (vPt : Ω → Vert 𝓑) := by
    rintro ⟨a, ha⟩
    exact absurd ha (by simp)
  have hnQ : (vInf : Vert 𝓑) ∉ Set.range (vBlk : {B // B ∈ 𝓑} → Vert 𝓑) := by
    rintro ⟨a, ha⟩
    exact absurd ha (by simp)
  by_cases hi : ∃ a, (vPt a : Vert 𝓑) ∈ T <;> by_cases hj : ∃ B, (vBlk B : Vert 𝓑) ∈ T
  · refine Or.inr (Or.inr (Or.inr ?_))
    have : T = Set.univ := by
      refine Set.eq_univ_of_forall fun u => ?_
      rcases u with _ | a | B
      · exact hv
      · exact hP hi ⟨a, rfl⟩
      · exact hQ hj ⟨B, rfl⟩
    rw [this, Set.ncard_univ, natCard_vert hΩ h𝓑]
  · refine Or.inr (Or.inl ?_)
    have : T = insert vInf (Set.range (vPt : Ω → Vert 𝓑)) := by
      refine Set.Subset.antisymm (fun u hu => ?_) (Set.insert_subset hv (hP hi))
      rcases u with _ | a | B
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨a, rfl⟩
      · exact absurd ⟨B, hu⟩ hj
    rw [this, Set.ncard_insert_of_notMem hnP, hcP]
  · refine Or.inr (Or.inr (Or.inl ?_))
    have : T = insert vInf (Set.range (vBlk : {B // B ∈ 𝓑} → Vert 𝓑)) := by
      refine Set.Subset.antisymm (fun u hu => ?_) (Set.insert_subset hv (hQ hj))
      rcases u with _ | a | B
      · exact Set.mem_insert _ _
      · exact absurd ⟨a, hu⟩ hi
      · exact Set.mem_insert_of_mem _ ⟨B, rfl⟩
    rw [this, Set.ncard_insert_of_notMem hnQ, hcQ]
  · refine Or.inl ?_
    have : T = {vInf} := by
      refine Set.Subset.antisymm (fun u hu => ?_) (Set.singleton_subset_iff.2 hv)
      rcases u with _ | a | B
      · exact Set.mem_singleton _
      · exact absurd ⟨a, hu⟩ hi
      · exact absurd ⟨B, hu⟩ hj
    rw [this, Set.ncard_singleton]

noncomputable def MData.stabilizerEvenEquiv (D : MData 𝓑)
    (hcard : Nat.card (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) = 443520) :
    stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑) ≃* D.carrier := by
  let r : stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑) →* Equiv.Perm Ω :=
    (restrictΩ 𝓑).comp stabEvenToStab
  have hr : Function.Injective r := restrictΩ_injective.comp stabEvenToStab_injective
  have hle : D.carrier ≤ r.range := fun τ hτ =>
    ⟨D.toStabEven ⟨τ, hτ⟩, D.restrictΩ_toStab ⟨τ, hτ⟩⟩
  have hcard' : Nat.card r.range ≤ Nat.card D.carrier := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hr).toEquiv, hcard, D.card]
  have heq : D.carrier = r.range := Subgroup.eq_of_le_of_card_ge hle hcard'
  exact (MonoidHom.ofInjective hr).trans (MulEquiv.subgroupCongr heq.symm)

theorem isSimpleGroup_evenSubgroup (D : MData 𝓑)
    (hψ : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B)
    (hodd : ∃ s ∈ autGroup 𝓑, s vInf = vInf ∧ Equiv.Perm.sign s = -1)
    (hΩ : Fintype.card Ω = 22) (h𝓑 : 𝓑.card = 77) (hA : Nat.card (autGroup 𝓑) = 88704000) :
    IsSimpleGroup (evenSubgroup 𝓑) := by
  have hodd' : ∃ s ∈ autGroup 𝓑, Equiv.Perm.sign s = -1 :=
    let ⟨s, hs, _, h⟩ := hodd
    ⟨s, hs, h⟩
  have hGs := card_stabilizer_even D hψ hodd hΩ h𝓑 hA
  have hsimple : IsSimpleGroup (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) := by
    have := D.simple
    exact (D.stabilizerEvenEquiv hGs).isSimpleGroup
  have h1 : ∀ g : stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑), g • (vInf : Vert 𝓑) = vInf :=
    fun g => g.2
  have h2 : ∀ (g : stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) (u v : Vert 𝓑),
      (hsGraph 𝓑).Adj (g • u) (g • v) ↔ (hsGraph 𝓑).Adj u v := fun g u v => g.1.1.2 u v
  refine isSimpleGroup_of_stabilizer_simple (vInf : Vert 𝓑) (fun g hg => ?_)
    (card_evenSubgroup hodd' hA) (natCard_vert hΩ h𝓑) (isPretransitive_evenSubgroup D hψ hodd)
    hsimple (fun T hv hT => ?_) ?_
  · exact Subtype.ext (Subtype.ext (Equiv.ext hg))
  · exact ncard_invariant _ hΩ h𝓑 h1 h2 D.exists_stabEven_vPt D.exists_stabEven_vBlk T hv
      (fun g t ht => hT g.1 g.2 t ht)
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨h, hord⟩ := exists_prime_orderOf_dvd_card'
      (G := stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) 11 (by rw [hGs]; norm_num)
    have o2 := orbit_vPt_eq (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) h1 h2
      D.exists_stabEven_vPt
    have o3 := orbit_vBlk_eq (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) h1 h2
      D.exists_stabEven_vBlk
    refine ⟨h.1, h.2, ?_, fun w hw => ?_⟩
    · have := pow_orderOf_eq_one h
      rw [hord] at this
      exact congrArg Subtype.val this
    · rcases w with _ | a | B
      · rfl
      · exfalso
        have hmem : h ∈ stabilizer (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑))
            (vPt a : Vert 𝓑) := mem_stabilizer_iff.2 hw
        have hd := Subgroup.orderOf_dvd_natCard _ hmem
        have hc := ncard_orbit_mul_card_stabilizer
          (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) (vPt a : Vert 𝓑)
        rw [o2 a, Set.ncard_range_of_injective vPt_injective, Nat.card_eq_fintype_card, hΩ,
          hGs] at hc
        rw [hord] at hd
        omega
      · exfalso
        have hmem : h ∈ stabilizer (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑))
            (vBlk B : Vert 𝓑) := mem_stabilizer_iff.2 hw
        have hd := Subgroup.orderOf_dvd_natCard _ hmem
        have hc := ncard_orbit_mul_card_stabilizer
          (stabilizer (evenSubgroup 𝓑) (vInf : Vert 𝓑)) (vBlk B : Vert 𝓑)
        rw [o3 B, Set.ncard_range_of_injective vBlk_injective, Nat.card_eq_fintype_card,
          Fintype.card_coe, h𝓑, hGs] at hc
        rw [hord] at hd
        omega

theorem eq_evenSubgroup_of_index_two (hsimple : IsSimpleGroup (evenSubgroup 𝓑))
    (hH : Nat.card (evenSubgroup 𝓑) = 44352000) (hA : Nat.card (autGroup 𝓑) = 88704000)
    (K : Subgroup (autGroup 𝓑)) (hK : K.index = 2) : K = evenSubgroup 𝓑 := by
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hK
  have hKc : Nat.card K = 44352000 := by
    have h := Subgroup.card_mul_index K
    rw [hK, hA] at h
    omega
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (evenSubgroup 𝓑)) with h | h
  · exfalso
    have hinj : Function.Injective
        ((QuotientGroup.mk' K).comp (evenSubgroup 𝓑).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have hx' : x ∈ K.subgroupOf (evenSubgroup 𝓑) := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 hx'
    have := Nat.card_le_card_of_injective _ hinj
    rw [hH, ← Subgroup.index, hK] at this
    omega
  · have hle : evenSubgroup 𝓑 ≤ K := Subgroup.subgroupOf_eq_top.1 h
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hKc, hH])).symm

end CFSG.Sporadic.Recognition.HSGraph
