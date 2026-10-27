module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {K : Type*} [Group K] [Finite K]

theorem overgroups_transport {X T : Subgroup G} {P₀ X₁ X₂ : Subgroup K}
    (hiso : quasithinO2QuotientIso X K) (hT : IsSylowTwoOf T X)
    (hP₀ : IsPGroup 2 P₀) (hP₀' : ¬ 2 ∣ P₀.index)
    (hcls : ∀ Y : Subgroup K, P₀ ≤ Y → Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤)
    (h₁ : P₀ ≤ X₁) (h₂ : P₀ ≤ X₂) (h₁₂ : ¬ X₁ ≤ X₂) (h₂₁ : ¬ X₂ ≤ X₁) :
    ∃ A₁ A₂ : Subgroup G, T ≤ A₁ ∧ T ≤ A₂ ∧ A₁ ≤ X ∧ A₂ ≤ X ∧ ¬ A₁ ≤ A₂ ∧ ¬ A₂ ≤ A₁ ∧
      A₁ ≠ X ∧ A₂ ≠ X ∧
      ∀ Y : Subgroup G, T ≤ Y → Y ≤ X → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hiso
  let S : Sylow 2 ↥X := A4.toSylow hT
  let SK : Sylow 2 K := S.mapSurjective hφ
  let P : Sylow 2 K := hP₀.toSylow hP₀'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P SK
  let c : K →* K := MulDistribMulAction.toMonoidEnd (MulAut K) K (MulAut.conj k)
  have hc : ∀ x : K, c x = k * x * k⁻¹ := fun x => rfl
  have hcinj : Function.Injective c := fun x y h => by
    rw [hc, hc] at h
    simpa using h
  have hcsurj : Function.Surjective c := fun y => ⟨k⁻¹ * y * k, by rw [hc]; group⟩
  have hTK : (T.subgroupOf X).map φ = P₀.map c := by
    have := congrArg (fun Q : Sylow 2 K => (Q : Subgroup K)) hk
    exact this.symm
  have hkerT : φ.ker ≤ T.subgroupOf X := by
    rw [hker]
    exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) S
  let pull : Subgroup K → Subgroup G := fun W => (W.comap φ).map X.subtype
  have hpullX : ∀ W, pull W ≤ X := fun W => Subgroup.map_subtype_le _
  have hpull_le : ∀ W W' : Subgroup K, pull W ≤ pull W' ↔ W ≤ W' := by
    intro W W'
    rw [Subgroup.map_subtype_le_map_subtype, Subgroup.comap_le_comap_of_surjective hφ]
  have hY : ∀ Y : Subgroup G, T ≤ Y → Y ≤ X → Y = pull ((Y.subgroupOf X).map φ) := by
    intro Y hTY hYX
    show Y = ((((Y.subgroupOf X).map φ).comap φ).map X.subtype)
    rw [Subgroup.comap_map_eq, sup_eq_left.2 (hkerT.trans (Subgroup.subgroupOf_mono _ hTY)),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYX]
  have hpullT : pull (P₀.map c) = T := by
    rw [← hTK]
    exact (hY T le_rfl hT.1).symm
  have hpullTop : pull ⊤ = X := by
    show ((⊤ : Subgroup K).comap φ).map X.subtype = X
    rw [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcle : ∀ W W' : Subgroup K, W.map c ≤ W'.map c ↔ W ≤ W' := fun W W' =>
    Subgroup.map_le_map_iff_of_injective hcinj
  refine ⟨pull (X₁.map c), pull (X₂.map c), ?_, ?_, hpullX _, hpullX _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hpullT, hpull_le]
    exact Subgroup.map_mono h₁
  · rw [← hpullT, hpull_le]
    exact Subgroup.map_mono h₂
  · rw [hpull_le, hcle]
    exact h₁₂
  · rw [hpull_le, hcle]
    exact h₂₁
  · intro h
    apply h₂₁
    have : pull (X₂.map c) ≤ pull (X₁.map c) := h ▸ hpullX _
    rwa [hpull_le, hcle] at this
  · intro h
    apply h₁₂
    have : pull (X₁.map c) ≤ pull (X₂.map c) := h ▸ hpullX _
    rwa [hpull_le, hcle] at this
  · intro Y hTY hYX
    set W := (Y.subgroupOf X).map φ with hW
    have hPW : P₀ ≤ W.comap c := by
      rw [← Subgroup.map_le_iff_le_comap, ← hTK]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hTY)
    have hWc : W = (W.comap c).map c := (Subgroup.map_comap_eq_self_of_surjective hcsurj W).symm
    rw [hY Y hTY hYX, ← hW, hWc]
    rcases hcls _ hPW with h | h | h | h <;> rw [h]
    · exact Or.inl hpullT
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · rw [Subgroup.map_top_of_surjective c hcsurj]
      exact Or.inr (Or.inr (Or.inr hpullTop))

end CFSG.Quasithin.H13.A6
