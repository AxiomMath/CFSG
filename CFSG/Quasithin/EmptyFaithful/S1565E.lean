module

public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.T1531Stage2

public section

namespace CFSG.Quasithin.S1565

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Z_le_ZS153 (c : Ctx153 G T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ ZS153 T M V₁ := by
  refine le_inf c.hyp.Z_le_VZ ?_
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_right
  exact hZT.trans (Subgroup.centralizer_le fun x hx => hx.1)

theorem T_le_normalizer_ZS153 (c : Ctx153 G T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (ZS153 T M V₁ : Set G) := by
  have hTV : T ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.T_le.trans c.hyp.le_normalizer
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    c.hyp.T_le_normalizer_Sgp153 c.decomp
  exact le_normalizer_inf hTV (hTS.trans (normalizer_le_normalizer_centralizer _))

theorem commutator_T_ZS153 (c : Ctx153 G T Mc M V₁ V₂ t) {a : G} (ha : a ∈ ZS153 T M V₁) {x : G}
    (hx : x ∈ T) : a * x * a⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := c.hyp.lemma_15_3_2_two.2
  have hZS4 : Nat.card (ZS153 T M V₁) = 4 := Decomp153.card_ZS c.hyp c.decomp
  have hZle : quasithinOmegaOneCenter T ≤ ZS153 T M V₁ := Z_le_ZS153 c
  have hxa : x * a * x⁻¹ ∈ ZS153 T M V₁ :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_ZS153 c hx) a).mp ha
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_right
  have hZc : ∀ s ∈ T, ∀ z ∈ quasithinOmegaOneCenter T, s * z * s⁻¹ = z := fun s hs z hz => by
    have := Subgroup.mem_centralizer_iff.mp (hZT hz) s hs
    rw [this]
    group
  have hidx : ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, hZ2] at h1
    omega
  have hmain : x * a * x⁻¹ * a⁻¹ ∈ quasithinOmegaOneCenter T := by
    by_cases haZ : a ∈ quasithinOmegaOneCenter T
    · rw [hZc x hx a haZ]
      simp
    · have hyZ : x * a * x⁻¹ ∉ quasithinOmegaOneCenter T := fun hy => by
        have h1 := hZc x⁻¹ (T.inv_mem hx) _ hy
        have e : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
        rw [e] at h1
        exact haZ (h1.symm ▸ hy)
      have hy' : (⟨x * a * x⁻¹, hxa⟩ : ZS153 T M V₁) ∉
          (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) := hyZ
      have ha' : (⟨a⁻¹, (ZS153 T M V₁).inv_mem ha⟩ : ZS153 T M V₁) ∉
          (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) := fun h =>
        haZ (by simpa using (quasithinOmegaOneCenter T).inv_mem (Subgroup.mem_subgroupOf.mp h))
      have key := (Subgroup.mul_mem_iff_of_index_two hidx
        (a := ⟨x * a * x⁻¹, hxa⟩) (b := ⟨a⁻¹, (ZS153 T M V₁).inv_mem ha⟩)).mpr
          (iff_of_false hy' ha')
      exact Subgroup.mem_subgroupOf.mp key
  have e : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem hmain

theorem exists_mul_of_isSylowTwoOf {X T : Subgroup G} (hT : IsSylowTwoOf T X) {b : G} (hb : b ∈ X) :
    ∃ t ∈ T, ∃ o ∈ oTwoUpper X, b = t * o := by
  have hsup : T ⊔ oTwoUpper X = X := by
    rw [← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hT
  have hN : T ≤ Subgroup.normalizer (oTwoUpper X : Set G) := hT.1.trans (le_normalizer_oTwoUpper X)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right T (oTwoUpper X) hN
  rw [hsup] at hcoe
  have hb' : b ∈ (T : Set G) * (oTwoUpper X : Set G) := by
    rw [← hcoe]
    exact hb
  obtain ⟨t, ht, o, ho, hto⟩ := hb'
  exact ⟨t, ht, o, ho, hto.symm⟩

theorem commutator_MH_ZS153 (c : Ctx153 G T Mc M V₁ V₂ t) (r49 : Res15349 T Mc M V₁)
    {H : Subgroup G} (hH : IsHTM153 T M H) {a : G} (ha : a ∈ ZS153 T M V₁) {b : G}
    (hb : b ∈ H ⊓ M) : a * b * a⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hTMH : T ≤ M ⊓ H := le_inf c.hyp.T_le hH.1.1
  have hsyl : IsSylowTwoOf T (M ⊓ H) :=
    isSylowTwoOf_mono_right c.hyp.isSylowTwoOf hTMH inf_le_left
  obtain ⟨t', ht', o, ho, rfl⟩ := exists_mul_of_isSylowTwoOf hsyl (inf_comm H M ▸ hb)
  have hoC : o ∈ Subgroup.centralizer (VZ T M : Set G) := r49.oTwoUpper_le H hH ho
  have haV : a ∈ VZ T M := ha.1
  have hoa : o * a⁻¹ * o⁻¹ = a⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hoC a⁻¹ ((VZ T M).inv_mem haV)
    rw [← this]
    group
  have e : a * (t' * o) * a⁻¹ * (t' * o)⁻¹ = (a * t' * a⁻¹ * t'⁻¹) := by
    calc a * (t' * o) * a⁻¹ * (t' * o)⁻¹ = a * t' * (o * a⁻¹ * o⁻¹) * t'⁻¹ := by group
      _ = a * t' * a⁻¹ * t'⁻¹ := by rw [hoa]
  rw [e]
  exact commutator_T_ZS153 c ha ht'

end CFSG.Quasithin.S1565
