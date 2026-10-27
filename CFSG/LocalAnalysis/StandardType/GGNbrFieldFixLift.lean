module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

theorem ggFixDer_perfect {R R₀ : Type} [Group R] [Group R₀] {x : MulAut R}
    (θ₀ : ggFixDer x ≃* R₀) (hs : IsSimpleGroup R₀) (hna : ∃ a b : R₀, a * b ≠ b * a) :
    ⁅ggFixDer x, ggFixDer x⁆ = ggFixDer x := by
  haveI := hs
  haveI : IsSimpleGroup (ggFixDer x) := MulEquiv.isSimpleGroup θ₀
  have hnc : ¬ ∀ g h : ggFixDer x, g * h = h * g := by
    intro hc
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have := congrArg θ₀ (hc (θ₀.symm a) (θ₀.symm b))
    simpa using this
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (ggFixDer x)) with h | h
  · exfalso
    apply hnc
    intro g k
    have hmem : ⁅g, k⁆ ∈ commutator (ggFixDer x) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

theorem ggFixDer_le_ggFixSub {R : Type} [Group R] (x : MulAut R) : ggFixDer x ≤ ggFixSub x := by
  rw [ggFixDer, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
    (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)

theorem ggTorusLift_pushforward {p r : ℕ} {L' R R₀ : Type} [Group L'] [Finite L'] [Group R]
    [Group R₀] (ψ : L' →* R) (H : Subgroup L') (ψ'' : H →* R₀) (hsurj : Function.Surjective ψ'')
    (hker : ψ''.ker ≤ Subgroup.center H) (hperf : commutator H = ⊤)
    (hker' : ∀ l, ψ'' l = 1 ↔ ψ l = 1) (hlift : GGTorusLift p r R₀) (f : MulAut L')
    (hf : ∀ l ∈ H, f l = l) :
    ∃ U E : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set L') ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ ψ.ker = ⊥ ∧
      (∀ l ∈ U, f l = l) ∧ (∀ l ∈ E, f l = l) := by
  obtain ⟨U₀, E₀, hU₀ne, hU₀p, hE₀norm, hE₀el, hE₀card, hE₀ker⟩ :=
    hlift (↥H) ψ'' hsurj hker hperf
  refine ⟨U₀.map H.subtype, E₀.map H.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hU₀ne ((Subgroup.map_eq_bot_iff_of_injective U₀ H.subtype_injective).mp hbot)
  · exact hU₀p.map H.subtype
  · exact (Subgroup.map_mono hE₀norm).trans
      (Subgroup.le_normalizer_map (H := U₀) H.subtype)
  · exact hE₀el.map H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hE₀card
  · rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heK⟩ := Subgroup.mem_inf.mp he
    obtain ⟨e₀, he₀E, rfl⟩ := Subgroup.mem_map.mp heE
    rw [Subgroup.mem_bot]
    have hψ : ψ (H.subtype e₀) = 1 := MonoidHom.mem_ker.mp heK
    have hψ'' : ψ'' e₀ = 1 := (hker' e₀).2 hψ
    have he₀bot : e₀ ∈ (⊥ : Subgroup H) := by
      rw [← hE₀ker]
      exact ⟨he₀E, MonoidHom.mem_ker.mpr hψ''⟩
    rw [Subgroup.mem_bot.mp he₀bot, map_one]
  · intro l hl
    obtain ⟨u₀, -, rfl⟩ := Subgroup.mem_map.mp hl
    exact hf (H.subtype u₀) u₀.2
  · intro l hl
    obtain ⟨e₀, -, rfl⟩ := Subgroup.mem_map.mp hl
    exact hf (H.subtype e₀) e₀.2

theorem ggTorusLiftFix_of_fixData {p r : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixData p r I x) :
    GGTorusLiftFix p r R I F := by
  intro L' _ _ ψ hψ hker hperf f hfp hind hnot
  obtain ⟨x, hx, hxψ⟩ := hind
  have hxI : x ∉ I := fun h => hnot ⟨x, h, hxψ⟩
  have hxp : x ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggInduced_pow ψ hxψ p l, hfp]
    rfl
  obtain ⟨R₀, _, I₀, θ₀, hs, hna, -, hlift, -⟩ := hfix x hx hxI hxp
  obtain ⟨ψ'', -, hsurj, hker', hkerc, hperf''⟩ :=
    ggSubfieldCore ψ hψ hker (ggFixDer x) (ggFixDer_perfect θ₀ hs hna) θ₀
  have hfH : ∀ l ∈ ggCore ψ (ggFixDer x), f l = l := fun l hl =>
    ggFixes_core ψ hker f x (fun l => (hxψ l).symm) ((ggFixDer x).comap ψ)
      (fun l hl => ggFixDer_le_ggFixSub x hl) hl
  exact ggTorusLift_pushforward ψ (ggCore ψ (ggFixDer x)) ψ'' hsurj hkerc hperf'' hker' hlift f hfH

end CFSG.StandardType

end
