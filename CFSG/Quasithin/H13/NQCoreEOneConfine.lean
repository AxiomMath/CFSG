module

public import CFSG.Quasithin.H13.NQCoreHyperplane
public import CFSG.Quasithin.Background.E3Bar

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem normalizer_qtnqU_eq {T L M : Subgroup G} (h : QTNQ T L M) :
    normalizer (qtnqU L M : Set G) = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨hU1, -, -, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUp : IsPGroup 2 ↥(qtnqU L M) := by
    have := hUe
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥(qtnqU L M)
  exact h.max_two_local.2 _ ⟨qtnqU L M, hU1, hUp, rfl⟩ (NQRigid.le_normalizer_qtnqU h)

theorem centralizer_qtnqU_le {T L M : Subgroup G} (h : QTNQ T L M) :
    centralizer (qtnqU L M : Set G) ≤ M :=
  (centralizer_le_normalizer _).trans (normalizer_qtnqU_eq h).le

theorem isElementaryAbelian_conjugate_qtnqU {T L M : Subgroup G} (h : QTNQ T L M) (g : G) :
    CFSG.IsElementaryAbelian 2 (CFSG.conjugate (qtnqU L M) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨-, -, -, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have := hUe
  exact CFSG.IsElementaryAbelian.map _

theorem isElemAbelian_conjugate_qtnqU {T L M : Subgroup G} (h : QTNQ T L M) (g : G) :
    IsElemAbelian 2 (CFSG.conjugate (qtnqU L M) g) := by
  have := isElementaryAbelian_conjugate_qtnqU h g
  exact ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩

theorem le_of_isE_one_conjugate {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    {P : Subgroup G} (hTP : T ≤ P) {g : G} (hAT : CFSG.conjugate (qtnqU L M) g ≤ T)
    {K : Subgroup G} (hK : E1.IsE 1 P T (CFSG.conjugate (qtnqU L M) g) K) : K ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := qtnqU L M with hUdef
  set A : Subgroup G := CFSG.conjugate U g with hAdef
  have hTsyl : IsSylowIn 2 T P :=
    ⟨hTP, h.sylow.1, fun hd => h.sylow.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTP))⟩
  obtain ⟨-, hcard⟩ := E3.card_le_of_isE hTsyl hAT (isElemAbelian_conjugate_qtnqU h g) hK
  set Q₂ : Subgroup G := pCoreOf 2 K with hQ₂
  have hQ₂K : Q₂ ≤ K := map_subtype_le _
  have hQ₂n : (Q₂.subgroupOf K).Normal := by
    have h1 : Q₂.subgroupOf K = CFSG.Open.pCore 2 ↥K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h1]
    infer_instance
  have hQ₂p : IsPGroup 2 Q₂ := (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
  have hQ₂T : Q₂ ≤ T := (hK.2.2.1.le_of_normal hQ₂K hQ₂n hQ₂p).trans inf_le_left
  have hKN : K ≤ normalizer (Q₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₂K).mp hQ₂n
  have hApos : 0 < Nat.card ↥(A ⊓ Q₂) := Nat.card_pos
  have hconj : ∀ k ∈ K, ⁅U, CFSG.conjugate U (g * k⁻¹)⁆ = ⊥ := by
    intro k hk
    set Ak : Subgroup G := CFSG.conjugate U (g * k⁻¹) with hAk
    have hAkA : ∀ x : G, x ∈ Ak ↔ k⁻¹ * x * k ∈ A := by
      intro x
      rw [mem_conjugate_iff', hAdef, mem_conjugate_iff']
      constructor <;> intro hx <;> simpa [mul_assoc] using hx
    have hQk : ∀ x : G, x ∈ Q₂ ↔ k⁻¹ * x * k ∈ Q₂ := by
      intro x
      have := mem_normalizer_iff.mp (hKN (K.inv_mem hk)) x
      rwa [inv_inv] at this
    have hB₀eq : Ak ⊓ Q₂ = (A ⊓ Q₂).map (MulAut.conj k).toMonoidHom := by
      ext x
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_inf, mem_inf, hAkA x, hQk x]
    have hcardB₀ : Nat.card ↥(Ak ⊓ Q₂) = Nat.card ↥(A ⊓ Q₂) := by
      rw [hB₀eq]
      exact Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hcardAk : Nat.card Ak = Nat.card A := by
      rw [hAk, hAdef, CFSG.conjugate, CFSG.conjugate,
        Subgroup.card_map_of_injective (MulAut.conj (g * k⁻¹)⁻¹).injective,
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    have hrel : (Ak ⊓ Q₂).relIndex Ak * Nat.card ↥(Ak ⊓ Q₂) = Nat.card Ak := by
      have h1 := Subgroup.relIndex_mul_card (H := Ak ⊓ Q₂) (K := Ak)
      rwa [inf_eq_left.mpr inf_le_left] at h1
    have hidx : (Ak ⊓ Q₂).relIndex Ak ≤ 2 := by
      have h1 : (Ak ⊓ Q₂).relIndex Ak * Nat.card ↥(A ⊓ Q₂) ≤ 2 * Nat.card ↥(A ⊓ Q₂) := by
        rw [← hcardB₀, hrel, hcardAk, hcardB₀]
        simpa using hcard
      exact Nat.le_of_mul_le_mul_right h1 hApos
    exact (nq_original_TI_hyperplane_conjugates_centralize_internal_module h hTI).2.2 (g * k⁻¹)
      (Ak ⊓ Q₂) (inf_le_inf_left _ hQ₂T) hidx
  have hcl : conjClosure A K ≤ centralizer (U : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, hk, a, ha, rfl⟩
    have hmem : k * a * k⁻¹ ∈ CFSG.conjugate U (g * k⁻¹) := by
      rw [mem_conjugate_iff']
      have h1 : g * a * g⁻¹ ∈ U := mem_conjugate_iff'.mp ha
      simpa [mul_assoc] using h1
    have h2 := commutator_eq_bot_iff_le_centralizer.mp (hconj k hk)
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro u hu
    exact (mem_centralizer_iff.mp (h2 hu) _ hmem).symm
  have hres : twoResidual K ≤ M :=
    (E1.twoResidual_le_conjClosure ⟨1, hK⟩).trans (hcl.trans (centralizer_qtnqU_le h))
  have hsyl2 : QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := hK.2.2.1
  calc K = T ⊓ K ⊔ twoResidual K := (sup_twoResidual_eq hsyl2).symm
    _ ≤ M := sup_le (inf_le_left.trans h.t_le) hres

theorem le_of_inEFor_one {T L M : Subgroup G} (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {P : Subgroup G} (hTP : T ≤ P) (hE : E1.InEFor 1 P T) : P ≤ M := by
  classical
  set U : Subgroup G := qtnqU L M with hUdef
  set Ω : Set (Subgroup G) := {X | (∃ g : G, CFSG.conjugate U g = X) ∧ X ≤ P} with hΩ
  have hcoll : E1.IsInvColl P Ω := by
    refine ⟨fun A hA => hA.2, fun A hA => ?_, fun A hA x hx => ?_⟩
    · obtain ⟨⟨g, rfl⟩, -⟩ := hA
      exact isElemAbelian_conjugate_qtnqU h g
    · obtain ⟨⟨g, rfl⟩, hle⟩ := hA
      refine ⟨⟨g * x⁻¹, ?_⟩, ?_⟩
      · ext y
        rw [mem_conjugate_iff', A1b.mem_conjSub_iff, mem_conjugate_iff']
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      · intro y hy
        rw [A1b.mem_conjSub_iff] at hy
        have h1 := hle hy
        have h2 : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
        rw [h2]
        exact P.mul_mem (P.mul_mem hx h1) (P.inv_mem hx)
  have hgen := hE Ω hcoll
  have hwc : E1.weakClosure T Ω =
      sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate U g = X) ∧ X ≤ T} := by
    apply le_antisymm
    · exact iSup₂_le fun A hA => iSup_le fun hAT => le_sSup ⟨hA.1, hAT⟩
    · refine sSup_le fun X hX => ?_
      exact le_iSup₂_of_le X ⟨hX.1, hX.2.trans hTP⟩ (le_iSup_of_le hX.2 le_rfl)
  rw [← hgen]
  refine sup_le ?_ ?_
  · refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    obtain ⟨⟨g, rfl⟩, -⟩ := hA
    exact le_of_isE_one_conjugate h hTI hTP hAT hK
  · rw [hwc]
    exact inf_le_right.trans hW

end CFSG.Quasithin.H13.NQCore
