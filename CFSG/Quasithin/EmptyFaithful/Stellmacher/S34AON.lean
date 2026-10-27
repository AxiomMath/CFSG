module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CommZvSurj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] {H M S : Subgroup G}

theorem commutator_iSup_le_iSup {ι : Type*} (Z : ι → Subgroup G) (X : Subgroup G)
    (hab : ∀ a ∈ ⨆ i, Z i, ∀ b ∈ ⨆ i, Z i, a * b = b * a)
    (hX : ∀ x ∈ X, ∀ v ∈ ⨆ i, Z i, x * v * x⁻¹ ∈ ⨆ i, Z i) :
    ⁅⨆ i, Z i, X⁆ ≤ ⨆ i, ⁅Z i, X⁆ := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  induction hv using Subgroup.iSup_induction' with
  | hp i v hv =>
    exact le_iSup (fun i => ⁅Z i, X⁆) i (Subgroup.commutator_mem_commutator hv hx)
  | h1 => simp
  | hmul a b ha hb iha ihb =>
    have hcV : b * x * b⁻¹ * x⁻¹ ∈ ⨆ i, Z i := by
      have h := hX x hx b⁻¹ ((⨆ i, Z i).inv_mem hb)
      have h2 := (⨆ i, Z i).mul_mem hb h
      simpa [mul_assoc] using h2
    have hc : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ = b * x * b⁻¹ * x⁻¹ := by
      rw [hab a ha _ hcV]; group
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    show a * b * x * (a * b)⁻¹ * x⁻¹ ∈ _
    rw [e, hc]
    exact Subgroup.mul_mem _ ihb iha

variable [Finite G]

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs in
theorem aon_edge (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ)
    {g : G} (hg : g ∈ stab μ ⊓ stab δ) :
    (g ∈ Qv μ → ⁅Zv μ, Subgroup.zpowers g⁆ = ⊥) ∧
      (g ∉ Qv μ → ⁅Zv μ, Subgroup.zpowers g⁆ = Zv δ) := by
  have hA := hG.amalg
  have hz := hG.central δ hδ
  have hQc : ∀ q ∈ Qv μ, ∀ y ∈ Zv μ, q * y = y * q := fun q hq y hy =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hy).2 q hq
  refine ⟨fun hgQ => ?_, fun hgQ => ?_⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    exact hQc b (Subgroup.zpowers_le.mpr hgQ hb) y hy
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro y hy b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      show y * g ^ i * y⁻¹ * (g ^ i)⁻¹ ∈ Zv δ
      by_cases hiQ : g ^ i ∈ Qv μ
      · rw [← hQc _ hiQ y hy]; simp
      · have hgi : g ^ i ∈ stab μ ⊓ stab δ := Subgroup.zpow_mem _ hg i
        have h := comm_Zv_into hA hδ hμ hz hgi hiQ y hy
        have e : y * g ^ i * y⁻¹ * (g ^ i)⁻¹ = (g ^ i * y * (g ^ i)⁻¹ * y⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ h
    · intro z hz'
      obtain ⟨y, hy, hyz⟩ := (comm_Zv_surj hA hδ hμ hz hg hgQ).2 z hz'
      have hmem : y * g * y⁻¹ * g⁻¹ ∈ ⁅Zv μ, Subgroup.zpowers g⁆ :=
        Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers g)
      have e : z = (y * g * y⁻¹ * g⁻¹)⁻¹ := by rw [← hyz]; group
      rw [e]
      exact Subgroup.inv_mem _ hmem

theorem aon_Vn (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) {x : G} (hx : x ∈ Qv δ) :
    ⁅Vn δ, Subgroup.zpowers x⁆ = ⊥ ∨ ⁅Vn δ, Subgroup.zpowers x⁆ = Zv δ := by
  have hA := hG.amalg
  have hVn : Vn δ = ⨆ μ : {μ : Geo H M // μ ∈ nbrs δ}, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  have hxδ : x ∈ stab δ := pCoreOf_le 2 (stab δ) hx
  have hab : ∀ a ∈ Vn δ, ∀ b ∈ Vn δ, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElemAbelian_Vn hA hG.three_le δ).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hX : ∀ y ∈ Subgroup.zpowers x, ∀ v ∈ Vn δ, y * v * y⁻¹ ∈ Vn δ := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ
      (Subgroup.zpowers_le.mpr hxδ hy)) v).mp hv
  have hle := commutator_iSup_le_iSup (fun μ : {μ : Geo H M // μ ∈ nbrs δ} => Zv μ.1)
    (Subgroup.zpowers x) (by rwa [← hVn]) (by rwa [← hVn])
  have hge : (⨆ μ : {μ : Geo H M // μ ∈ nbrs δ}, ⁅Zv μ.1, Subgroup.zpowers x⁆) ≤
      ⁅Vn δ, Subgroup.zpowers x⁆ :=
    iSup_le fun μ => Subgroup.commutator_mono (Zv_le_Vn_of_mem_nbrs μ.2) le_rfl
  have heq : ⁅Vn δ, Subgroup.zpowers x⁆ = ⨆ μ : {μ : Geo H M // μ ∈ nbrs δ},
      ⁅Zv μ.1, Subgroup.zpowers x⁆ := by
    apply le_antisymm _ hge
    rw [hVn]; exact hle
  have hedge : ∀ μ : {μ : Geo H M // μ ∈ nbrs δ},
      ⁅Zv μ.1, Subgroup.zpowers x⁆ = ⊥ ∨ ⁅Zv μ.1, Subgroup.zpowers x⁆ = Zv δ := fun μ => by
    have hxμ : x ∈ stab μ.1 ⊓ stab δ := ⟨Qv_le_stab_of_mem_nbrs hA μ.2 hx, hxδ⟩
    by_cases h : x ∈ Qv μ.1
    · exact Or.inl ((aon_edge hG hδ μ.2 hxμ).1 h)
    · exact Or.inr ((aon_edge hG hδ μ.2 hxμ).2 h)
  rw [heq]
  by_cases hall : ∀ μ : {μ : Geo H M // μ ∈ nbrs δ}, ⁅Zv μ.1, Subgroup.zpowers x⁆ = ⊥
  · left
    exact le_bot_iff.mp (iSup_le fun μ => (hall μ).le)
  · right
    push Not at hall
    obtain ⟨μ₀, hμ₀⟩ := hall
    have h0 : ⁅Zv μ₀.1, Subgroup.zpowers x⁆ = Zv δ := (hedge μ₀).resolve_left hμ₀
    apply le_antisymm
    · exact iSup_le fun μ => (hedge μ).elim (fun h => h ▸ bot_le) (fun h => h.le)
    · exact h0.symm.le.trans (le_iSup (fun μ : {μ : Geo H M // μ ∈ nbrs δ} =>
        ⁅Zv μ.1, Subgroup.zpowers x⁆) μ₀)

end S34

end F53.Stellmacher

end CFSG.Quasithin
