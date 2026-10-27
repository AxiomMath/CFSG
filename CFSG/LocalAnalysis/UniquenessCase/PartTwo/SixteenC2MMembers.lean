module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrAbs
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16c2m_perm_exists_two :
    ∀ a b i j : Fin 3, a ≠ b → i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ a = i ∧ σ b = j := by
  decide

private theorem s16c2m_perm_exists_one :
    ∀ a i : Fin 3, ∃ σ : Equiv.Perm (Fin 3), σ a = i := by
  decide

theorem s16c2m_members {W : Type} [CommGroup W] [Finite W] {X L K : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hK : IsSym ↥K 3)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁) :
    ∃ (G3 : Fin 3 → Subgroup W) (π : ↥X →* Equiv.Perm (Fin 3)), Function.Injective G3 ∧
      irrSet L = Set.range G3 ∧ J₀ ∈ Set.range G3 ∧ J₁ ∈ Set.range G3 ∧
      (∀ (x : ↥X) (i : Fin 3), (G3 i).map (x : MulAut W).toMonoidHom = G3 (π x i)) ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = σ) ∧
      (∀ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = 1 → k = 1) ∧
      (∀ i j : Fin 3, i ≠ j → G3 i ⊓ G3 j = ⊥ ∧ G3 i ⊔ G3 j = ⊤) ∧
      (∀ i : Fin 3, rk ↥(G3 i) = rk ↥J₀) ∧
      (∀ g : ↥X, (∀ k ∈ K, (g : MulAut W) * k = k * (g : MulAut W)) → π g = 1) := by
  classical
  obtain ⟨G3, π, hinj, hrange, hact, hsurjK, hfaith⟩ :=
    s16c167_irr_three_abs F hKX hKL hK hE₀ hE₁
  have hirr : ∀ I ∈ irrSet L, IsIrrOn L I ⊥ := by
    intro I hI
    obtain ⟨-, h⟩ := hI
    rwa [F.fix, inf_bot_eq] at h
  have hmem : ∀ i, IsIrrOn L (G3 i) ⊥ := fun i => hirr _ (hrange ▸ Set.mem_range_self i)
  have hJ0 : J₀ ∈ Set.range G3 := hrange ▸ F.irr₀
  have hJ1 : J₁ ∈ Set.range G3 := hrange ▸ F.irr₁
  obtain ⟨a, ha⟩ := hJ0
  obtain ⟨b, hb⟩ := hJ1
  have hJ0bot : ⊥ < J₀ := (hirr J₀ F.irr₀).1
  have hab : a ≠ b := by
    rintro rfl
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [← ha, ← hb, inf_idem]
    rw [F.inf_eq] at h1
    exact hJ0bot.ne h1
  have hmeet : ∀ i j : Fin 3, i ≠ j → G3 i ⊓ G3 j = ⊥ := by
    intro i j hij
    have hstab : StableUnder L (G3 i ⊓ G3 j) := by
      intro l hl u hu
      exact ⟨(hmem i).2.1 l hl u hu.1, (hmem j).2.1 l hl u hu.2⟩
    rcases (hmem i).2.2.2 (G3 i ⊓ G3 j) hstab bot_le inf_le_left with h | h
    · exact h
    · exfalso
      have hle : G3 i ≤ G3 j := inf_eq_left.1 h
      rcases (hmem j).2.2.2 (G3 i) (hmem i).2.1 bot_le hle with h' | h'
      · exact (hmem i).1.ne h'.symm
      · exact hij (hinj h')
  have hxK : ∀ (k : ↥K) (i : Fin 3), (G3 i).map (k : MulAut W).toMonoidHom =
      G3 (π ⟨(k : MulAut W), hKX k.2⟩ i) := fun k i => hact ⟨(k : MulAut W), hKX k.2⟩ i
  have hrkeq : ∀ i, rk ↥(G3 i) = rk ↥J₀ := by
    intro i
    obtain ⟨σ, hσ⟩ := s16c2m_perm_exists_one a i
    obtain ⟨k, hk⟩ := hsurjK σ
    have h1 := hxK k a
    rw [hk, hσ] at h1
    rw [← ha, ← h1]
    unfold rk
    rw [Subgroup.card_map_of_injective (k : MulAut W).injective]
  have hjoin : ∀ i j : Fin 3, i ≠ j → G3 i ⊔ G3 j = ⊤ := by
    intro i j hij
    obtain ⟨σ, hσa, hσb⟩ := s16c2m_perm_exists_two a b i j hab hij
    obtain ⟨k, hk⟩ := hsurjK σ
    have h1 := hxK k a
    have h2 := hxK k b
    rw [hk, hσa] at h1
    rw [hk, hσb] at h2
    have h3 : (G3 a ⊔ G3 b).map (k : MulAut W).toMonoidHom = G3 i ⊔ G3 j := by
      rw [Subgroup.map_sup, h1, h2]
    have h4 : G3 a ⊔ G3 b = ⊤ := by rw [ha, hb]; exact F.sup_eq
    rw [h4, Subgroup.map_top_of_surjective _ (k : MulAut W).surjective] at h3
    exact h3.symm
  have hcomm : ∀ g : ↥X, (∀ k ∈ K, (g : MulAut W) * k = k * (g : MulAut W)) → π g = 1 := by
    intro g hg
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    obtain ⟨k, hk⟩ := hsurjK τ
    have h1 : (⟨(k : MulAut W), hKX k.2⟩ : ↥X) * g = g * ⟨(k : MulAut W), hKX k.2⟩ :=
      Subtype.ext (hg k k.2).symm
    calc π g * τ = π g * π ⟨(k : MulAut W), hKX k.2⟩ := by rw [hk]
      _ = π (g * ⟨(k : MulAut W), hKX k.2⟩) := (map_mul π _ _).symm
      _ = π (⟨(k : MulAut W), hKX k.2⟩ * g) := by rw [h1]
      _ = π ⟨(k : MulAut W), hKX k.2⟩ * π g := map_mul π _ _
      _ = τ * π g := by rw [hk]
  exact ⟨G3, π, hinj, hrange, ⟨a, ha⟩, ⟨b, hb⟩, hact, hsurjK, hfaith,
    fun i j hij => ⟨hmeet i j hij, hjoin i j hij⟩, hrkeq, hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
