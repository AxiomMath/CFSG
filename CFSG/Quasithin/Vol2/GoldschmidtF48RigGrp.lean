module

public import CFSG.Quasithin.Recognition.F4Basic

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin

variable {N : Type*} [Group N]

theorem normalizer_le_of_complement {Q C H : Subgroup N} [hQ : Q.Normal]
    (hC : IsComplementIn C Q ⊤) (hHC : H ≤ C)
    (hfix : ∀ q ∈ Q, (∀ h ∈ H, h * q * h⁻¹ = q) → q = 1) {x : N}
    (hx : x ∈ Subgroup.normalizer (H : Set N)) : x ∈ C := by
  obtain ⟨q, hq, c, hc, rfl⟩ := hC.2.2.2 x (Subgroup.mem_top x)
  have hQC : ∀ y ∈ Q, y ∈ C → y = 1 := fun y hy hyC => by
    have : y ∈ Q ⊓ C := ⟨hy, hyC⟩
    rw [hC.2.2.1] at this
    exact this
  have hx' := Subgroup.mem_normalizer_iff.mp hx
  have hconj : ∀ h ∈ H, q * c * h * (q * c)⁻¹ = c * h * c⁻¹ := by
    intro h hh
    have h1 : q * c * h * (q * c)⁻¹ ∈ C := hHC ((hx' h).mp hh)
    have h2 : c * h * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc (hHC hh)) (C.inv_mem hc)
    have h3 : (c * h * c⁻¹)⁻¹ * (q * c * h * (q * c)⁻¹) ∈ Q := by
      have e : (c * h * c⁻¹)⁻¹ * (q * c * h * (q * c)⁻¹) =
          ((c * h * c⁻¹)⁻¹ * q * (c * h * c⁻¹)⁻¹⁻¹) * q⁻¹ := by group
      rw [e]
      exact Q.mul_mem (hQ.conj_mem q hq _) (Q.inv_mem hq)
    have := hQC _ h3 (C.mul_mem (C.inv_mem h2) h1)
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hcn : c ∈ Subgroup.normalizer (H : Set N) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    constructor
    · intro hh
      rw [← hconj h hh]
      exact (hx' h).mp hh
    · intro hh
      obtain ⟨n, hn⟩ : ∃ n : N, n = (q * c)⁻¹ * (c * h * c⁻¹) * (q * c) := ⟨_, rfl⟩
      have e : q * c * n * (q * c)⁻¹ = c * h * c⁻¹ := by rw [hn]; group
      have hnH : n ∈ H := (hx' n).mpr (by rw [e]; exact hh)
      have e1 := hconj n hnH
      rw [e] at e1
      have : n = h := mul_left_cancel (mul_right_cancel e1.symm)
      rw [← this]
      exact hnH
  have hqn : q ∈ Subgroup.normalizer (H : Set N) := by
    have := (Subgroup.normalizer (H : Set N)).mul_mem hx
      ((Subgroup.normalizer (H : Set N)).inv_mem hcn)
    simpa using this
  have hq' := Subgroup.mem_normalizer_iff.mp hqn
  have hq1 : q = 1 := by
    refine hfix q hq fun h hh => ?_
    have h1 : q * h * q⁻¹ ∈ H := (hq' h).mp hh
    have h2 : q * h * q⁻¹ * h⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem hh)
    have h3 : q * h * q⁻¹ * h⁻¹ ∈ Q := by
      have e : q * h * q⁻¹ * h⁻¹ = q * (h * q⁻¹ * h⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq (hQ.conj_mem q⁻¹ (Q.inv_mem hq) h)
    have h4 := hQC _ h3 (hHC h2)
    have h5 : q * h = h * q := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)
    calc h * q * h⁻¹ = (q * h) * h⁻¹ := by rw [h5]
      _ = q := by group
  rw [hq1, one_mul]
  exact hc

theorem complement_unique {Q C C' G H : Subgroup N} [Q.Normal]
    (hC' : IsComplementIn C' Q ⊤) (hGC : G ≤ C) (hGC' : G ≤ C')
    (hmax : ∀ M : Subgroup N, G ≤ M → M ≤ C → M = G ∨ M = C)
    (hmax' : ∀ M : Subgroup N, G ≤ M → M ≤ C' → M = G ∨ M = C')
    (hHG : H ≤ G) (hfix : ∀ q ∈ Q, (∀ h ∈ H, h * q * h⁻¹ = q) → q = 1) {w : N} (hwC : w ∈ C)
    (hwG : w ∉ G) (hw : w ∈ Subgroup.normalizer (H : Set N)) : C = C' := by
  have hwC' : w ∈ C' := normalizer_le_of_complement hC' (hHG.trans hGC') hfix hw
  have hM : G ⊔ Subgroup.zpowers w ≤ C :=
    sup_le hGC ((Subgroup.zpowers_le).mpr hwC)
  have hM' : G ⊔ Subgroup.zpowers w ≤ C' :=
    sup_le hGC' ((Subgroup.zpowers_le).mpr hwC')
  have hne : G ≠ G ⊔ Subgroup.zpowers w := fun h =>
    hwG (h ▸ (le_sup_right : Subgroup.zpowers w ≤ G ⊔ _) (Subgroup.mem_zpowers w))
  have e1 : G ⊔ Subgroup.zpowers w = C :=
    (hmax _ le_sup_left hM).resolve_left hne.symm
  have e2 : G ⊔ Subgroup.zpowers w = C' :=
    (hmax' _ le_sup_left hM').resolve_left hne.symm
  rw [← e1, e2]

theorem maximal_of_twoTrans {X : Type*} [MulAction N X] {C G : Subgroup N} {S : Set X} {u : X}
    (hu : u ∈ S) (hS : ∀ g ∈ C, ∀ x ∈ S, g • x ∈ S)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → c ≠ d →
      ∃ g ∈ C, g • a = c ∧ g • b = d)
    (hG : ∀ g ∈ C, g ∈ G ↔ g • u = u) :
    ∀ M : Subgroup N, G ≤ M → M ≤ C → M = G ∨ M = C := by
  intro M hGM hMC
  by_cases hMG : M ≤ G
  · exact Or.inl (le_antisymm hMG hGM)
  right
  obtain ⟨m, hm, hmG⟩ := Set.not_subset.mp hMG
  have hmu : m • u ≠ u := fun h => hmG ((hG m (hMC hm)).mpr h)
  refine le_antisymm hMC fun c hc => ?_
  by_cases hcu : c • u = u
  · exact hGM ((hG c hc).mpr hcu)
  · obtain ⟨g, hgC, hg1, hg2⟩ := h2 u hu (m • u) (hS m (hMC hm) u hu) u hu (c • u)
      (hS c hc u hu) (Ne.symm hmu) (Ne.symm hcu)
    have hgM : g ∈ M := hGM ((hG g hgC).mpr hg1)
    have hk : (c⁻¹ * (g * m)) • u = u := by
      rw [mul_smul, mul_smul, hg2, ← mul_smul, inv_mul_cancel, one_smul]
    have hkM : c⁻¹ * (g * m) ∈ M :=
      hGM ((hG _ (C.mul_mem (C.inv_mem hc) (C.mul_mem hgC (hMC hm)))).mpr hk)
    have e : c = (g * m) * (c⁻¹ * (g * m))⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hgM hm) (M.inv_mem hkM)

end CFSG.Quasithin.H13.F48Rig
