module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs
import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTorusLift_mono {p r r' : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (h : GGTorusLift p r R) (hr : r' ≤ r) : GGTorusLift p r' R := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, hEker⟩ := h L' ψ hψ hker hperf
  obtain ⟨E', hE'E, hE', hcard', -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_elemAbelian_le_inf_eq_bot hp hE
      (bot_le : (⊥ : Subgroup L') ≤ E) r'
      (by rw [Subgroup.card_bot, mul_one, hcard]; exact Nat.pow_le_pow_right hp.pos hr)
  exact ⟨U, E', hU, hU2, hE'E.trans hEU, hE', hcard',
    eq_bot_iff.mpr (hEker ▸ inf_le_inf_right _ hE'E)⟩

theorem largeEvenMarking_label_or {X : Type*} [Group X] {S T : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => S lab ∨ T lab)) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => S lab) ∨
      LargeEvenMarking X (fun lab _ _ _ _ _ => T lab) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hST⟩ := largeEvenRawDatum_exists hraw
  rcases hST with hS | hT
  · exact Or.inl ⟨hX, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ =>
      ⟨hs, hna, θ, hS⟩) hraw⟩
  · exact Or.inr ⟨hX, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ =>
      ⟨hs, hna, θ, hT⟩) hraw⟩

theorem ggUnitaryCommLifts_ggGamma_of_le {G : Type} [Group G] {Bs K L J : Subgroup G}
    (hNK : Bs ≤ Subgroup.normalizer (K : Set G)) (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hJK : J ≤ K) (hJL : J ≤ L) {n d : ℕ}
    (h : GGUnitaryCommLifts (J.subgroupOf L) n d (ggGamma L hNL).range) :
    GGUnitaryCommLifts (J.subgroupOf K) n d (ggGamma K hNK).range := by
  intro K' _ _ hK' θ a₁ ha₁ a₂ ha₂ hn₁ hn₂ A₁ hA₁ A₂ hA₂ ⟨φ₁, hφ₁, hi₁⟩ ⟨φ₂, hφ₂, hi₂⟩
  obtain ⟨b₁, rfl⟩ := ha₁
  obtain ⟨b₂, rfl⟩ := ha₂
  let e : ↥(J.subgroupOf K) ≃* ↥(J.subgroupOf L) :=
    (Subgroup.subgroupOfEquivOfLe hJK).trans (Subgroup.subgroupOfEquivOfLe hJL).symm
  have he : ∀ l : ↥(J.subgroupOf K), (((e l : ↥(J.subgroupOf L)) : ↥L) : G) = ((l : ↥K) : G) :=
    fun _ => rfl
  set θ' := (centerQuotCongr e).symm.trans θ with hθ'
  have hθ : (centerQuotCongr e).trans θ' = θ := centerQuotCongr_trans_symm_trans e θ
  have hnL : ∀ b : Bs, (∀ l ∈ J.subgroupOf K, ggGamma K hNK b l ∈ J.subgroupOf K) →
      ∀ l ∈ J.subgroupOf L, ggGamma L hNL b l ∈ J.subgroupOf L := by
    intro b hb l hl
    have hlJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.mp hl
    have h1 := Subgroup.mem_subgroupOf.mp
      (hb ⟨(l : G), hJK hlJ⟩ (Subgroup.mem_subgroupOf.mpr hlJ))
    rw [ggGamma_coe] at h1
    rw [Subgroup.mem_subgroupOf, ggGamma_coe]
    exact h1
  have key : ∀ (b : Bs) (φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K' (2 ^ n)))),
      LargeEvenInduces θ (fun l l' : ↥(J.subgroupOf K) => (l' : ↥K) = ggGamma K hNK b l) φ →
      LargeEvenInduces θ' (fun l l' : ↥(J.subgroupOf L) => (l' : ↥L) = ggGamma L hNL b l) φ := by
    intro b φ hφ
    have := largeEvenInduces_congr_equiv e θ'
      (fun l l' : ↥(J.subgroupOf K) => (l' : ↥K) = ggGamma K hNK b l)
      (fun l l' : ↥(J.subgroupOf L) => (l' : ↥L) = ggGamma L hNL b l)
      (fun l l' => by simp only [Subtype.ext_iff, ggGamma_coe, he]) φ
    rw [hθ] at this
    exact this.1 hφ
  exact h K' hK' θ' (ggGamma L hNL b₁) ⟨b₁, rfl⟩ (ggGamma L hNL b₂) ⟨b₂, rfl⟩
    (hnL b₁ hn₁) (hnL b₂ hn₂) A₁ hA₁ A₂ hA₂ ⟨φ₁, hφ₁, key b₁ φ₁ hi₁⟩ ⟨φ₂, hφ₂, key b₂ φ₂ hi₂⟩

end CFSG.StandardType

end
