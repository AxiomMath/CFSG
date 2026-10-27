module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem_ch614 {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  rw [← this]
  exact hy

theorem not_commutator_le_pCoreOf_ch614 {T M₁ K₁ X : Subgroup G} (hsyl : IsSylowTwoOf T M₁)
    (hK₁ : K₁ ∈ cComp M₁) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXK₀ : X ≤ conjClosure K₁ T)
    (hnot : ¬ X ≤ Subgroup.normalizer ((T ⊓ conjClosure K₁ T : Subgroup G) : Set G)) :
    ¬ ⁅X, K₁⁆ ≤ pCoreOf 2 K₁ := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 M₁ with hP
  have hTM₁ : T ≤ M₁ := hsyl.1
  have hPT : P ≤ T := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hM₁P : M₁ ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁
  have hO2K : pCoreOf 2 K₁ ≤ P :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₁)
  have hK₁M : K₁ ≤ M₁ := le_of_mem_cComp hK₁
  have hK₀C : conjClosure K₁ T ≤ centralizerMod P M₁ X := by
    refine conjClosure_le fun t ht k hk => ?_
    have htM : t ∈ M₁ := hTM₁ ht
    have hg : t * k * t⁻¹ ∈ M₁ := M₁.mul_mem (M₁.mul_mem htM (hK₁M hk)) (M₁.inv_mem htM)
    refine ⟨hg, hM₁P hg, fun x hx => ?_⟩
    have hx' : t⁻¹ * x * t ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) x).mp hx
      simpa using this
    have hkx : k * (t⁻¹ * x * t) * k⁻¹ * (t⁻¹ * x * t)⁻¹ ∈ P := by
      have h1 : ⁅t⁻¹ * x * t, k⁆ ∈ ⁅X, K₁⁆ := Subgroup.commutator_mem_commutator hx' hk
      have h2 := hO2K (hc h1)
      have h3 : (⁅t⁻¹ * x * t, k⁆)⁻¹ ∈ P := P.inv_mem h2
      rw [commutatorElement_def] at h3
      convert h3 using 1
      group
    have e : t * k * t⁻¹ * x * (t * k * t⁻¹)⁻¹ * x⁻¹ =
        t * (k * (t⁻¹ * x * t) * k⁻¹ * (t⁻¹ * x * t)⁻¹) * t⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hM₁P htM) _).mp hkx
  apply hnot
  intro x hx
  apply mem_normalizer_of_conj_mem_ch614
  intro s hs
  have hsC := hK₀C hs.2
  have hxs : s * x * s⁻¹ * x⁻¹ ∈ P := hsC.2.2 x hx
  have hcomm : x * s * x⁻¹ * s⁻¹ ∈ P := by
    have := P.inv_mem hxs
    convert this using 1
    group
  refine ⟨?_, ?_⟩
  · have e : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact T.mul_mem (hPT hcomm) hs.1
  · exact (conjClosure K₁ T).mul_mem ((conjClosure K₁ T).mul_mem (hXK₀ hx) hs.2)
      ((conjClosure K₁ T).inv_mem (hXK₀ hx))

end CFSG.Quasithin.H13
