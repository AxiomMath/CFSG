module

public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupE
public import CFSG.RankThree.GF2n.Parrott.SpinFixedSConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}
variable {ψ : ↥(H z) →* A45} {κ : G → V}

@[expose] def kappaRestrictHom (hκ : IsSpinCoord ψ κ) {B : Subgroup G} (hB : B ≤ J z) :
    ↥B →* Multiplicative V where
  toFun f := Multiplicative.ofAdd (κ (f : G))
  map_one' := by
    show Multiplicative.ofAdd (κ ((1 : ↥B) : G)) = 1
    rw [Subgroup.coe_one, hκ.kappa_one]
    rfl
  map_mul' f f' := by
    show Multiplicative.ofAdd (κ ((f * f' : ↥B) : G)) = _
    rw [Subgroup.coe_mul, hκ.add f (hB f.2) f' (hB f'.2)]
    rfl

theorem mem_ker_kappaRestrictHom (hκ : IsSpinCoord ψ κ) {B : Subgroup G} (hB : B ≤ J z) (f : ↥B) :
    f ∈ (kappaRestrictHom hκ hB).ker ↔ κ (f : G) = 0 := Iff.rfl

theorem card_range_kappaRestrictHom (hκ : IsSpinCoord ψ κ) {B : Subgroup G} (hB : B ≤ J z) :
    Nat.card (kappaRestrictHom hκ hB).range = (κ '' (B : Set G)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative V), ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd (v : V), ?_⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  · obtain ⟨f, hf⟩ := x.2
    rw [← hf]
    exact ⟨f, f.2, rfl⟩
  · obtain ⟨b, hb, hbv⟩ := v.2
    exact ⟨⟨b, hb⟩, by
      show Multiplicative.ofAdd (κ b) = _
      rw [hbv]⟩

theorem card_eq_two_mul_ncard_of_z_mem (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ)
    {B : Subgroup G} (hB : B ≤ J z) (hzB : z ∈ B) :
    Nat.card B = 2 * (κ '' (B : Set G)).ncard := by
  have hz := orderOf_z_A h
  have hker : (kappaRestrictHom hκ hB).ker = (Subgroup.zpowers z).subgroupOf B := by
    ext f
    rw [mem_ker_kappaRestrictHom, Subgroup.mem_subgroupOf,
      Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz, hκ.eq_zero_iff _ (hB f.2)]
  have hcard : Nat.card (kappaRestrictHom hκ hB).ker = 2 := by
    rw [hker]
    have hle : Subgroup.zpowers z ≤ B := Subgroup.zpowers_le.mpr hzB
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hz]
  have h1 := Subgroup.card_ker_mul_card_range (kappaRestrictHom hκ hB)
  rw [hcard, card_range_kappaRestrictHom hκ hB] at h1
  exact h1.symm

theorem card_eq_ncard_of_z_not_mem (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ)
    {B : Subgroup G} (hB : B ≤ J z) (hzB : z ∉ B) :
    Nat.card B = (κ '' (B : Set G)).ncard := by
  have hker : (kappaRestrictHom hκ hB).ker = ⊥ := by
    ext f
    rw [mem_ker_kappaRestrictHom, Subgroup.mem_bot, hκ.eq_zero_iff _ (hB f.2)]
    constructor
    · rintro (h1 | h1)
      · exact Subtype.ext h1
      · exact absurd (h1 ▸ f.2) hzB
    · intro h1
      left
      rw [h1]
      rfl
  have h1 := Subgroup.card_ker_mul_card_range (kappaRestrictHom hκ hB)
  rw [hker, Subgroup.card_bot, card_range_kappaRestrictHom hκ hB, one_mul] at h1
  exact h1.symm

private theorem mem_conjugate_iff' {S : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    exact hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩

section ElemAbelian

variable (D : QuotientData (z := z) (J_subgroupOf_normal z))

theorem exists_conjugate_spinFixE_of_isElemAbelian (h : Tim79a.ParrottHypA z)
    (hκ : IsSpinCoord (qH D) κ) {E' : Subgroup G} (hE'H : E' ≤ H z) (hE'ab : IsElemAbelian 2 E')
    (hE'card : Nat.card E' = 2 ^ 9) :
    ∃ x ∈ H z, E' = CFSG.conjugate (spinFixE hκ) x := by
  have hz1 := z_ne_one_A h
  set B : Subgroup G := E' ⊓ J z with hBdef
  have hBJ : B ≤ J z := inf_le_right
  have hBE : B ≤ E' := inf_le_left
  set S' : Subgroup A45 := imageQA45 D hE'H with hS'def
  have hS'ab : IsElemAbelian 2 S' := isElemAbelian_imageQA45 D hE'H hE'ab
  have hS'le : Nat.card S' ≤ 16 := qa45_elemAbelian_card_le_sixteen S' hS'ab
  have hcardEB : Nat.card E' = Nat.card B * Nat.card S' :=
    card_eq_card_inf_J_mul_card_imageQA45 D hE'H
  have hadd : ∀ x ∈ κ '' (B : Set G), ∀ y ∈ κ '' (B : Set G), x + y ∈ κ '' (B : Set G) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    exact ⟨b * b', mul_mem hb hb', hκ.add b (hBJ hb) b' (hBJ hb')⟩
  have hsing : ∀ x ∈ κ '' (B : Set G), q x = 0 := by
    rintro _ ⟨b, hb, rfl⟩
    exact (hκ.mul_self_eq_one_iff hz1 (hBJ hb)).mp (hE'ab.mul_self_eq_one (hBE hb))
  have hn16 := ncard_le_sixteen_of_totally_singular _ hadd hsing
  have hB32 : Nat.card B ≤ 32 := by
    by_cases hzB : z ∈ B
    · rw [card_eq_two_mul_ncard_of_z_mem h hκ hBJ hzB]
      omega
    · rw [card_eq_ncard_of_z_not_mem h hκ hBJ hzB]
      omega
  have hBeq : Nat.card B = 32 := by
    by_contra hne
    have h1 : Nat.card B ≤ 31 := by omega
    have h2 := Nat.mul_le_mul h1 hS'le
    rw [hE'card] at hcardEB
    omega
  have hS'card : Nat.card S' = 16 := by
    rw [hE'card, hBeq] at hcardEB
    omega
  have hzB : z ∈ B := by
    by_contra hzB
    rw [card_eq_ncard_of_z_not_mem h hκ hBJ hzB] at hBeq
    omega
  have hncard : (κ '' (B : Set G)).ncard = 16 := by
    rw [card_eq_two_mul_ncard_of_z_mem h hκ hBJ hzB] at hBeq
    omega
  have hfix : κ '' (B : Set G) ⊆ {v : V | ∀ s ∈ S', SpinFixes s v} := by
    rintro _ ⟨b, hb, rfl⟩ s hs
    obtain ⟨k, hkE', hks⟩ := (mem_imageQA45_iff D hE'H s).mp hs
    have hks' : qH D ⟨k, hE'H hkE'⟩ = s := hks
    have hbE' : b ∈ E' := hBE hb
    have hcomm : k * b = b * k := hE'ab.comm hkE' hbE'
    have h1 := hκ.act k (hE'H hkE') b (hBJ hb)
    rw [show k * b * k⁻¹ = b by rw [hcomm]; group, hks'] at h1
    exact h1.symm
  have hfixcard : 16 ≤ Set.ncard {v : V | ∀ s ∈ S', SpinFixes s v} := by
    rw [← hncard]
    exact Set.ncard_le_ncard hfix (Set.toFinite _)
  obtain ⟨g, hg⟩ := qa45SubgroupConj_sQA45_of_fixed S' hS'ab hS'card hfixcard
  let T : Set V := (fun u => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ u) '' (spinFixS : Set V)
  have hTinj : Function.Injective (fun u : V => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ u) :=
    Function.LeftInverse.injective (g := fun v : V => ((rhoA g : GL8) : Mat8) *ᵥ v)
      (fun u => rhoA_mulVec_mul_inv g u)
  have hTcard : T.ncard = 16 := by
    show ((fun u : V => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ u) '' (spinFixS : Set V)).ncard = 16
    rw [Set.ncard_image_of_injective _ hTinj, ← Nat.card_coe_set_eq]
    exact card_spinFixS
  have hsub : κ '' (B : Set G) ⊆ T := by
    intro v hv
    refine ⟨((rhoA g : GL8) : Mat8) *ᵥ v, ?_, ?_⟩
    · intro s hs
      have hs' : s ∈ S'.map (MulAut.conj g).toMonoidHom := by
        rw [hg]
        exact hs
      obtain ⟨s', hs'S, hs'e⟩ := Subgroup.mem_map.mp hs'
      have hss : g⁻¹ * s * g = s' := by
        rw [← hs'e]
        show g⁻¹ * (g * s' * g⁻¹) * g = s'
        group
      exact spinFixes_mulVec_of_conj (by rw [hss]; exact hfix hv s' hs'S)
    · exact rhoA_mulVec_inv g v
  have hEq : κ '' (B : Set G) = T :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hTcard, hncard]) (Set.toFinite _)
  obtain ⟨x, hx⟩ := hκ.surjective g
  have hxH : (x : G) ∈ H z := x.2
  have hxg : qH D ⟨(x : G), hxH⟩ = g := hx
  have hconj_F : ∀ f ∈ spinFixF hκ, (x : G)⁻¹ * f * (x : G) ∈ B := by
    intro f hf
    have hxi : (x : G)⁻¹ ∈ H z := inv_mem hxH
    have hf' : (x : G)⁻¹ * f * (x : G) ∈ J z := by
      have := (mem_normalizer_iff.mp (J_le_normalizer_A hxi) f).mp hf.1
      rwa [inv_inv] at this
    have hκ' : κ ((x : G)⁻¹ * f * (x : G)) = ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ κ f := by
      have h1 := hκ.act (x : G)⁻¹ hxi f hf.1
      rw [inv_inv] at h1
      have h2 : qH D ⟨(x : G)⁻¹, hxi⟩ = g⁻¹ := by
        have : (⟨(x : G)⁻¹, hxi⟩ : ↥(H z)) = ⟨(x : G), hxH⟩⁻¹ := rfl
        rw [this, map_inv, hxg]
      rw [h1, h2]
    have hmem : κ ((x : G)⁻¹ * f * (x : G)) ∈ κ '' (B : Set G) := by
      rw [hEq, hκ']
      exact ⟨κ f, hf.2, rfl⟩
    obtain ⟨b, hbB, hbκ⟩ := hmem
    rcases (hκ.kappa_eq_iff (hBJ hbB) hf').mp hbκ.symm with e | e
    · rw [e]
      exact hbB
    · rw [e]
      exact mul_mem hbB hzB
  have hle : E' ≤ CFSG.conjugate (spinFixE hκ) (x : G) := by
    intro y hy
    rw [mem_conjugate_iff', mem_spinFixE_iff]
    refine ⟨mul_mem (mul_mem hxH (hE'H hy)) (inv_mem hxH), fun f hf => ?_⟩
    have hb := hconj_F f hf
    have hc : ((x : G)⁻¹ * f * (x : G)) * y = y * ((x : G)⁻¹ * f * (x : G)) :=
      hE'ab.comm (hBE hb) hy
    calc f * ((x : G) * y * (x : G)⁻¹)
        = (x : G) * (((x : G)⁻¹ * f * (x : G)) * y) * (x : G)⁻¹ := by group
      _ = (x : G) * (y * ((x : G)⁻¹ * f * (x : G))) * (x : G)⁻¹ := by rw [hc]
      _ = ((x : G) * y * (x : G)⁻¹) * f := by group
  refine ⟨x, hxH, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hE'card, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj (x : G)⁻¹).injective,
    card_spinFixE D h hκ]

end ElemAbelian

end CFSG.RankThree.GF2n.Parrott
