module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isPGroup_of_not_dvd_relIndex {p : ℕ} [Fact p.Prime] {W R L : Subgroup G}
    (hWR : W ≤ R) (hRL : R ≤ L) (hR : IsPGroup p R) (hW : ¬ p ∣ W.relIndex L) : R = W := by
  obtain ⟨n, hn⟩ := hR.index (W.subgroupOf R)
  have hdvd : W.relIndex R ∣ W.relIndex L :=
    ⟨R.relIndex L, (Subgroup.relIndex_mul_relIndex W R L hWR hRL).symm⟩
  have h1 : W.relIndex R = 1 := by
    change (W.subgroupOf R).index = 1
    rw [hn]
    rcases n with _ | n
    · rfl
    · exact absurd ((dvd_pow_self p n.succ_ne_zero).trans (hn ▸ hdvd)) hW
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hWR

theorem mem_normalizer_of_conj_mem {W : Subgroup G} {g : G}
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hg w hw
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mul_mem_normalizer_of_sylow {p : ℕ} [Fact p.Prime] {H C W : Subgroup G}
    (hHC : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) (S : Sylow p C)
    (hS : (S : Subgroup C).map C.subtype = W) {h : G} (hh : h ∈ H) :
    ∃ c ∈ C, c * h ∈ Subgroup.normalizer (W : Set G) := by
  have hhN : h ∈ Subgroup.normalizer (C : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hHC h hh x hx, fun hx => ?_⟩
    have := hHC h⁻¹ (H.inv_mem hh) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  let φ : MulAut C := C.normalizerMonoidHom ⟨h, hhN⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (φ • S) S
  refine ⟨c, c.2, mem_normalizer_of_conj_mem fun w hw => ?_⟩
  rw [← hS] at hw ⊢
  obtain ⟨s, hs, rfl⟩ := hw
  have hmem : c * φ s * c⁻¹ ∈ (S : Subgroup C) := by
    rw [← hc, coe_smul_sylow', coe_mulAut_smul_sylow']
    exact ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
  refine ⟨_, hmem, ?_⟩
  change (c : G) * (h * s * h⁻¹) * (c : G)⁻¹ = (c : G) * h * s * ((c : G) * h)⁻¹
  group

theorem relIndex_eq_relIndex_normalizer {p : ℕ} [Fact p.Prime] {H C W : Subgroup G}
    (hCH : C ≤ H) (hHC : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) (S : Sylow p C)
    (hS : (S : Subgroup C).map C.subtype = W) :
    C.relIndex H = C.relIndex (H ⊓ Subgroup.normalizer (W : Set G)) := by
  have hfrat : ∀ h ∈ H, ∃ c ∈ C, c * h ∈ Subgroup.normalizer (W : Set G) := fun h hh =>
    exists_mul_mem_normalizer_of_sylow hHC S hS hh
  have hnormal : (C.subgroupOf H).Normal := ⟨fun n hn g => hHC g g.2 n hn⟩
  have hsup : (H ⊓ Subgroup.normalizer (W : Set G)).subgroupOf H ⊔ C.subgroupOf H = ⊤ := by
    refine eq_top_iff.mpr fun h _ => ?_
    obtain ⟨c, hc, hch⟩ := hfrat h h.2
    have hn : (⟨c * h, H.mul_mem (hCH hc) h.2⟩ : H) ∈
        (H ⊓ Subgroup.normalizer (W : Set G)).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr ⟨H.mul_mem (hCH hc) h.2, hch⟩
    have hc' : (⟨c⁻¹, H.inv_mem (hCH hc)⟩ : H) ∈ C.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (C.inv_mem hc)
    have := Subgroup.mul_mem_sup hc' hn
    rwa [sup_comm, show (⟨c⁻¹, H.inv_mem (hCH hc)⟩ : H) * ⟨c * h, _⟩ = h from
      Subtype.ext (by simp)] at this
  have h1 := Subgroup.relIndex_sup_right ((H ⊓ Subgroup.normalizer (W : Set G)).subgroupOf H)
    (C.subgroupOf H)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf inf_le_left] at h1
  exact h1

theorem eq_of_trivial_translation {Q C W J K : Subgroup G} {u : G}
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G)) (huW : u ∈ W) (hu2 : u ^ 2 = 1)
    (hdecomp : ∀ v ∈ W, v ^ 2 = 1 → ∃ y ∈ Q, ∃ j ∈ J, v = y * j)
    (hJQ : J ≤ Subgroup.centralizer (Q : Set G))
    (hX : ∀ y ∈ Q, y ≠ 1 → ∃ x : G, x * y * x⁻¹ ≠ y ∧ x * y * x⁻¹ ∈ Q ∧
      (∀ c ∈ C, x * c * x⁻¹ ∈ C) ∧ x * u = u * x ∧ ∀ j ∈ J, x * j = j * x)
    (htriv : ∀ c ∈ C, u⁻¹ * (c * u * c⁻¹) ∈ Q → c * u * c⁻¹ = u)
    (hnorm : ∀ g : G, g * u * g⁻¹ ∈ J → g ∈ Subgroup.normalizer (K : Set G))
    (hWN : W ≤ C ⊓ Subgroup.normalizer (K : Set G))
    (hWodd : ¬ 2 ∣ W.relIndex (C ⊓ Subgroup.normalizer (K : Set G)))
    {S : Subgroup G} (hSC : S ≤ C) (hS2 : IsPGroup 2 S) (hWS : W ≤ S) : S = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : W.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm (fun x hx => ?_) hWS)
    have hx' : (⟨x, hx⟩ : S) ∈ W.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact hx'
  obtain ⟨g, hgN, hgW⟩ := IsConcreteLE.exists_of_lt (p_group_normalizer_condition hS2 hlt)
  have hgW' : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hgN ⟨w, hWS hw⟩).mp (Subgroup.mem_subgroupOf.mpr hw)
  have hgC : (g : G) ∈ C := hSC g.2
  have hgWnot : (g : G) ∉ W := fun h => hgW (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨v, hv⟩ : ∃ v, v = (g : G) * u * (g : G)⁻¹ := ⟨_, rfl⟩
  have hvW : v ∈ W := hv ▸ hgW' u huW
  have hv2 : v ^ 2 = 1 := by rw [hv, conj_pow, hu2, mul_one, mul_inv_cancel]
  obtain ⟨y, hyQ, j, hjJ, hvyj⟩ := hdecomp v hvW hv2
  by_cases hy : y = 1
  · have hvJ : (g : G) * u * (g : G)⁻¹ ∈ J := by rw [← hv, hvyj, hy, one_mul]; exact hjJ
    have hR := eq_of_isPGroup_of_not_dvd_relIndex (le_inf hWS hWN) inf_le_right hS2.to_inf_left
      hWodd
    exact hgWnot (hR ▸ ⟨g.2, hgC, hnorm g hvJ⟩)
  obtain ⟨x, hxy, hxyQ, hxC, hxu, hxJ⟩ := hX y hyQ hy
  have hjx : x * j * x⁻¹ = j := by rw [hxJ j hjJ, mul_inv_cancel_right]
  have hd : y⁻¹ * (x * y * x⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hyQ) hxyQ
  have hd1 : y⁻¹ * (x * y * x⁻¹) ≠ 1 := fun h1 => hxy (inv_mul_eq_one.mp h1).symm
  have hjd : (y⁻¹ * (x * y * x⁻¹)) * j = j * (y⁻¹ * (x * y * x⁻¹)) :=
    Subgroup.mem_centralizer_iff.mp (hJQ hjJ) _ hd
  have h1 : x * v * x⁻¹ = v * (y⁻¹ * (x * y * x⁻¹)) := by
    calc x * v * x⁻¹ = (x * y * x⁻¹) * (x * j * x⁻¹) := by rw [hvyj]; group
      _ = y * ((y⁻¹ * (x * y * x⁻¹)) * j) := by rw [hjx]; group
      _ = v * (y⁻¹ * (x * y * x⁻¹)) := by rw [hjd, hvyj]; group
  have hgd : (g : G)⁻¹ * (y⁻¹ * (x * y * x⁻¹)) * g = y⁻¹ * (x * y * x⁻¹) := by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.mp (hCQ hgC) _ hd, inv_mul_cancel_left]
  have hxux : x⁻¹ * u * x = u := by rw [mul_assoc, ← hxu, inv_mul_cancel_left]
  have hcC : (g : G)⁻¹ * (x * g * x⁻¹) ∈ C := C.mul_mem (C.inv_mem hgC) (hxC _ hgC)
  have hc : (g : G)⁻¹ * (x * g * x⁻¹) * u * ((g : G)⁻¹ * (x * g * x⁻¹))⁻¹ =
      u * (y⁻¹ * (x * y * x⁻¹)) := by
    calc (g : G)⁻¹ * (x * g * x⁻¹) * u * ((g : G)⁻¹ * (x * g * x⁻¹))⁻¹
        = (g : G)⁻¹ * x * g * (x⁻¹ * u * x) * (g : G)⁻¹ * x⁻¹ * g := by group
      _ = (g : G)⁻¹ * (x * v * x⁻¹) * g := by rw [hxux, hv]; group
      _ = ((g : G)⁻¹ * v * g) * ((g : G)⁻¹ * (y⁻¹ * (x * y * x⁻¹)) * g) := by rw [h1]; group
      _ = u * (y⁻¹ * (x * y * x⁻¹)) := by rw [hgd, hv]; group
  have h2 := htriv _ hcC (by rw [hc, inv_mul_cancel_left]; exact hd)
  rw [hc, mul_eq_left] at h2
  exact hd1 h2

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
