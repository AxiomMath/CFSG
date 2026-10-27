module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Z
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Pre

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Basic

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] def TfG (c : AutCtx G M₁ M₂ z) : Subgroup G :=
  c.iso.imgG That ⊓ cenOf (c.iso.toG fhB)

theorem TfG_le_cen : TfG c ≤ cenOf (c.iso.toG fhB) := inf_le_right

theorem TfG_le_M1 : TfG c ≤ M₁ := inf_le_left.trans ((c.iso.imgG_le That).trans inf_le_left)

theorem card_TfG : Nat.card ↥(TfG c) = 32 := card_Tf c.iso

theorem Tf_relIndex (hTR : TfG c ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6) :
    (TfG c).relIndex R = 2 := by
  have h3 := Subgroup.card_mul_index ((TfG c).subgroupOf R)
  have h4 : Nat.card ↥((TfG c).subgroupOf R) = Nat.card ↥(TfG c) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
  rw [h4, card_TfG, hR64] at h3
  have h5 : ((TfG c).subgroupOf R).index = (TfG c).relIndex R := rfl
  omega

theorem Tf_conj (hTR : TfG c ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6) {n : G} (hn : n ∈ R) {t : G}
    (ht : t ∈ TfG c) : n * t * n⁻¹ ∈ TfG c := by
  have hnorm : ((TfG c).subgroupOf R).Normal :=
    Subgroup.normal_of_index_eq_two (Tf_relIndex c hTR hR64)
  have := hnorm.conj_mem ⟨t, hTR ht⟩ (Subgroup.mem_subgroupOf.2 ht) ⟨n, hn⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem R_le_normalizer_Tf (hTR : TfG c ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6) :
    R ≤ Subgroup.normalizer (TfG c : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact fun ht => Tf_conj c hTR hR64 hn ht
  · intro h
    have := Tf_conj c hTR hR64 (R.inv_mem hn) h
    simpa [mul_assoc] using this

theorem R_inf_M1 (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB))) (hTR : TfG c ≤ R) :
    R ⊓ M₁ = TfG c := by
  have hle : R ⊓ M₁ ≤ M₁ ⊓ cenOf (c.iso.toG fhB) := fun x hx => ⟨hx.2, hR.1 hx.1⟩
  have hp : IsPGroup 2 ↥(R ⊓ M₁) := hR.2.1.to_le inf_le_left
  have h1 := card_le_twoPart hle hp
  have h2 := twoPart_E1 c.iso
  have hTM : TfG c ≤ R ⊓ M₁ := le_inf hTR (TfG_le_M1 c)
  exact (Subgroup.eq_of_le_of_card_ge hTM (by rw [card_TfG]; omega)).symm

theorem conj_z_R (h5 : U42AutFusionZ) (h6 : FusionTStmt)
    (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)) (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : TfG c ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6) {n : G} (hn : n ∈ R) :
    n * z * n⁻¹ = z ∨ n * z * n⁻¹ = c.iso.toG fhB * z := by
  refine conj_z_cases c h5 h6 ht0 (R_le_normalizer_Tf c hTR hR64 hn) ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (hR.1 hn)

theorem conj_z_of_not_mem (h5 : U42AutFusionZ) (h6 : FusionTStmt)
    (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)) (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : TfG c ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6) {n : G} (hn : n ∈ R) (hnT : n ∉ TfG c) :
    n * z * n⁻¹ = c.iso.toG fhB * z := by
  rcases conj_z_R c h5 h6 ht0 hR hTR hR64 hn with h | h
  · exfalso
    apply hnT
    rw [← R_inf_M1 c hR hTR]
    refine ⟨hn, ?_⟩
    rw [← c.cenOf_z]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h]
  · exact h

end Basic

end CFSG.Quasithin.H13.F431.U42Aut
