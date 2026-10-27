module

public import CFSG.Quasithin.H13.A6S13821u
public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.A6S1372L76G
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_QH_iff (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {x : G} (hx : x ∈ H) :
    x ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure S.V3 H, x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hF := (hS.hF H hH).toHypF91
  rw [hF.pCoreOf_eq_centralizerMod, mem_centralizerMod]
  exact ⟨fun h => h.2.2, fun h => ⟨hx, hF.H_normalizes_V₁ hx, h⟩⟩

theorem secMod_UH (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {θ : ↥H →* H6.Γ}
    (hθs : Function.Surjective θ) (hker : ∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) :
    L32A.SecMod H (conjClosure S.V3 H) (fsuV1 T V) θ := by
  have hF := (hS.hF H hH).toHypF91
  have hab := L13825.isElemAbelian_UH hS hH
  refine ⟨hF.V₁_le_Vp.trans (le_conjClosure S.V3 H), le_normalizer_conjClosure S.V3 H,
    hF.H_normalizes_V₁, fun a ha b hb => ?_, fun a ha => ?_, hθs, fun l hl x hx => ?_,
    fun l hl => ?_⟩
  · have h1 : a * b = b * a := congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have e : a * b * a⁻¹ * b⁻¹ = 1 := by rw [h1]; group
    rw [e]
    exact Subgroup.one_mem _
  · rw [hab.2 a ha]
    exact Subgroup.one_mem _
  · exact (S.mem_QH_iff hS hH l.2).mp ((hker l).mp hl) x hx
  · exact (hker l).mpr ((S.mem_QH_iff hS hH l.2).mpr hl)

theorem comm_v2_of_borel (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {θ : ↥H →* H6.Γ}
    (hker : ∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hθT : (T.subgroupOf H).map θ = H6.borel) (l : ↥H) (hl : θ l ∈ H6.borel) :
    (l : G) * S.v2 * (l : G)⁻¹ * S.v2⁻¹ ∈ fsuV1 T V := by
  have hF := (hS.hF H hH).toHypF91
  rw [← hθT] at hl
  obtain ⟨t, ht, hθt⟩ := hl
  have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have hq : ((t⁻¹ * l : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← hker, map_mul, map_inv, hθt, inv_mul_cancel]
  have hqv := (S.mem_QH_iff hS hH (t⁻¹ * l).2).mp hq S.v2 (S.v2_mem_UH H)
  have htv : (t : G) * S.v2 * (t : G)⁻¹ * S.v2⁻¹ ∈ fsuV1 T V := by
    have hmem : (t : G) * S.v2 * (t : G)⁻¹ ∈ S.V2 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V2 htT) _).mp S.v2_mem_V2
    rcases S.mem_V1_or_of_mem_V2 S.v2_mem_V2 S.v2_not_mem_V1 hmem with h | h
    · exfalso
      apply S.v2_not_mem_V1
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (hF.H_normalizes_V₁ (H.inv_mem t.2)) _).mp h
      have e : (t : G)⁻¹ * ((t : G) * S.v2 * (t : G)⁻¹) * (t : G)⁻¹⁻¹ = S.v2 := by group
      rwa [e] at h2
    · exact h
  set q : G := ((t⁻¹ * l : ↥H) : G) with hqdef
  have hl' : (l : G) = (t : G) * q := by
    rw [hqdef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have hc : (t : G) * (q * S.v2 * q⁻¹ * S.v2⁻¹) * (t : G)⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ t.2) _).mp hqv
  have e : (l : G) * S.v2 * (l : G)⁻¹ * S.v2⁻¹ =
      ((t : G) * (q * S.v2 * q⁻¹ * S.v2⁻¹) * (t : G)⁻¹) *
        ((t : G) * S.v2 * (t : G)⁻¹ * S.v2⁻¹) := by
    rw [hl']
    group
  rw [e]
  exact (fsuV1 T V).mul_mem hc htv

theorem conj_V3_mem {C : Subgroup G} {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = Equiv.swap 0 1 * Equiv.swap 1 2) {h : G}
    (hV1 : ∀ w ∈ fsuV1 T V, h * w * h⁻¹ ∈ C)
    (hv : ∀ a ∈ ({1, (g : G), ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)} : Set G),
      (h * a) * S.v2 * (h * a)⁻¹ ∈ C) {z : G} (hz : z ∈ S.V3) :
    h * z * h⁻¹ ∈ C := by
  have key : ∀ a ∈ ({1, (g : G), ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)} : Set G),
      z * (a * S.v2 * a⁻¹) ∈ fsuV1 T V → h * z * h⁻¹ ∈ C := by
    intro a ha hza
    have e : h * z * h⁻¹ =
        (h * (z * (a * S.v2 * a⁻¹)) * h⁻¹) * ((h * a) * S.v2 * (h * a)⁻¹)⁻¹ := by
      group
    rw [e]
    exact C.mul_mem (hV1 _ hza) (C.inv_mem (hv a ha))
  rcases S.mem_V3_cases hg hz with h1 | h1 | h1 | h1
  · exact hV1 z h1
  · exact key 1 (Set.mem_insert _ _) (by simpa using h1)
  · exact key _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) h1
  · exact key _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)) h1

theorem mem_closure_v2 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) :
    ∀ s ∈ conjClosure S.V3 H, s ∈ Subgroup.closure
      ({y | ∃ l : ↥H, (l : G) * S.v2 * (l : G)⁻¹ = y} ∪ (fsuV1 T V : Set G)) := by
  have hF := (hS.hF H hH).toHypF91
  obtain ⟨g, hgL1, hg⟩ := S.exists_g012
  have hgH : (g : G) ∈ H := le_sup_left.trans hH.1.1 hgL1
  intro s hs
  refine conjClosure_le (fun h hh z hz => ?_) hs
  refine S.conj_V3_mem hg (fun w hw => Subgroup.subset_closure (Or.inr ?_)) ?_ hz
  · exact (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ hh) w).mp hw
  · intro a ha
    have haH : a ∈ H := by
      rcases ha with rfl | rfl | rfl
      · exact H.one_mem
      · exact hgH
      · rw [Subgroup.coe_pow]
        exact H.pow_mem hgH 2
    exact Subgroup.subset_closure (Or.inl ⟨⟨h * a, H.mul_mem hh haH⟩, rfl⟩)

theorem closure_v2_Ll_eq (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {θ : ↥H →* H6.Γ}
    (hker : ∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hθL : ((S.L1 ⊔ T).subgroupOf H).map θ = H6.Ll) :
    Subgroup.closure ({y | ∃ l : ↥H, θ l ∈ H6.Ll ∧ (l : G) * S.v2 * (l : G)⁻¹ = y} ∪
      (fsuV1 T V : Set G)) = S.V3 := by
  have hF := (hS.hF H hH).toHypF91
  have hV1V3 : fsuV1 T V ≤ S.V3 := hF.V₁_le_Vp
  have hv2V3 : S.v2 ∈ S.V3 := S.V2_le_V3 S.v2_mem_V2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (⟨l, hl, rfl⟩ | hy)
    · rw [← hθL] at hl
      obtain ⟨y, hy, hθy⟩ := hl
      have hyN := S.L1T_le_NV3 (Subgroup.mem_subgroupOf.mp hy)
      have hq : ((y⁻¹ * l : ↥H) : G) ∈ pCoreOf 2 H := by
        rw [← hker, map_mul, map_inv, hθy, inv_mul_cancel]
      have hqv := (S.mem_QH_iff hS hH (y⁻¹ * l).2).mp hq S.v2 (S.v2_mem_UH H)
      set q : G := ((y⁻¹ * l : ↥H) : G) with hqdef
      have hl' : (l : G) = (y : G) * q := by
        rw [hqdef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      have e : (l : G) * S.v2 * (l : G)⁻¹ =
          (y : G) * ((q * S.v2 * q⁻¹ * S.v2⁻¹) * S.v2) * (y : G)⁻¹ := by
        rw [hl']
        group
      rw [SetLike.mem_coe, e]
      exact (Subgroup.mem_normalizer_iff.mp hyN _).mp (S.V3.mul_mem (hV1V3 hqv) hv2V3)
    · exact hV1V3 hy
  · obtain ⟨g, hgL1, hg⟩ := S.exists_g012
    have hgH : (g : G) ∈ H := le_sup_left.trans hH.1.1 hgL1
    intro z hz
    have hz' := S.conj_V3_mem (C := Subgroup.closure ({y | ∃ l : ↥H, θ l ∈ H6.Ll ∧
        (l : G) * S.v2 * (l : G)⁻¹ = y} ∪ (fsuV1 T V : Set G))) hg (h := 1)
      (fun w hw => Subgroup.subset_closure (Or.inr (by simpa using hw))) ?_ hz
    · simpa using hz'
    · intro a ha
      have haH : a ∈ H ∧ a ∈ S.L1 ⊔ T := by
        rcases ha with rfl | rfl | rfl
        · exact ⟨H.one_mem, Subgroup.one_mem _⟩
        · exact ⟨hgH, Subgroup.mem_sup_left hgL1⟩
        · rw [Subgroup.coe_pow]
          exact ⟨H.pow_mem hgH 2, Subgroup.pow_mem _ (Subgroup.mem_sup_left hgL1) 2⟩
      refine Subgroup.subset_closure (Or.inl ⟨⟨a, haH.1⟩, ?_, by simp⟩)
      rw [← hθL]
      exact ⟨⟨a, haH.1⟩, Subgroup.mem_subgroupOf.mpr haH.2, rfl⟩

theorem relIndex_closure_v2_Ll (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {θ : ↥H →* H6.Γ} (hker : ∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hθL : ((S.L1 ⊔ T).subgroupOf H).map θ = H6.Ll) :
    (fsuV1 T V).relIndex (Subgroup.closure ({y | ∃ l : ↥H, θ l ∈ H6.Ll ∧
      (l : G) * S.v2 * (l : G)⁻¹ = y} ∪ (fsuV1 T V : Set G))) = 4 := by
  have hF := (hS.hF H hH).toHypF91
  rw [S.closure_v2_Ll_eq hS hH hker hθL]
  have h3 := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := S.V3)
  rw [inf_of_le_left hF.V₁_le_Vp, S.card_V3, hF.card_V₁] at h3
  omega

theorem theta_mem_Ul {H : Subgroup G} {θ : ↥H →* H6.Γ} (hθT : (T.subgroupOf H).map θ = H6.borel)
    (hθL : ((S.L1 ⊔ T).subgroupOf H).map θ = H6.Ll) {x : ↥H}
    (hx : (x : G) ∈ pCoreOf 2 (S.L1 ⊔ T)) : θ x ∈ A6S19.Ul := by
  obtain ⟨c₀, hc₀, hc₀3, hc₀1⟩ := A6S19.exists_three_Ll
  have hc₀' := hc₀
  rw [← hθL] at hc₀'
  obtain ⟨c, hc, hθc⟩ := hc₀'
  have hcLT : (c : G) ∈ S.L1 ⊔ T := Subgroup.mem_subgroupOf.mp hc
  have hR : pCoreOf 2 (S.L1 ⊔ T) ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hN := le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hcLT
  have hmemT : ∀ y : ↥H, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → θ y ∈ H6.borel := fun y hy => by
    rw [← hθT]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hR hy), rfl⟩
  refine A6S19.mem_Ul_of_conj hc₀ hc₀3 hc₀1 (hmemT x hx) ?_ ?_
  · rw [← hθc, ← map_inv, ← map_mul, ← map_mul]
    apply hmemT
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hx
  · rw [← hθc, ← map_inv, ← map_mul, ← map_mul]
    apply hmemT
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) _).mp hx
    rw [inv_inv] at h1
    exact h1

end Setting4

end CFSG.Quasithin.H13.A6
