module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSp

public section

namespace CFSG.StandardType

namespace OrdPNsSp

open Matrix Module SUTB NoOffOm OrdPNsGen CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank

variable {n : ℕ} {K : Type} [Field K]

variable (n K) in
@[expose] noncomputable def statedSpGL : StatedSp n K →* GL (Fin (n + n)) K :=
  (spReindex n K).toMonoidHom.comp (StatedSp n K).subtype

theorem statedSpGL_injective : Function.Injective (statedSpGL n K) := fun a b hab =>
  Subtype.ext ((spReindex n K).injective hab)

theorem statedSpGL_mem_isoGL (s : StatedSp n K) : statedSpGL n K s ∈ isoGL (spFormD n K) :=
  (spReindex_mem_isoGL_iff (s : GL (Fin n ⊕ Fin n) K)).mpr s.2

theorem exists_statedSpGL_eq {g : GL (Fin (n + n)) K} (hg : g ∈ isoGL (spFormD n K)) :
    ∃ s : StatedSp n K, statedSpGL n K s = g := by
  refine ⟨⟨(spReindex n K).symm g, ?_⟩, ?_⟩
  · rw [← spReindex_mem_isoGL_iff, MulEquiv.apply_symm_apply]
    exact hg
  · change spReindex n K ((spReindex n K).symm g) = g
    exact MulEquiv.apply_symm_apply _ g

theorem genMax_map_statedSpGL [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (StatedSp n K)} (hpow : ∀ a ∈ E, a ^ p = 1)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hmax : ∀ g : StatedSp n K, g ^ p = 1 → (∀ a ∈ E, g * a = a * g) → g ∈ E) :
    GenMax (spFormD n K) (isoGL (spFormD n K)) p (E.map (statedSpGL n K)) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  refine ⟨spFormD_isSymm, spFormD_sep, hp, hp2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact statedSpGL_mem_isoGL s
  · rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, hpow s hs, map_one]
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hcomm s hs t ht]
  · intro g hg hgp hgA
    obtain ⟨s, rfl⟩ := exists_statedSpGL_eq hg
    have hsp : s ^ p = 1 := statedSpGL_injective (by rw [map_pow, hgp, map_one])
    refine ⟨s, hmax s hsp fun a ha => statedSpGL_injective ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hgA _ ⟨a, ha, rfl⟩
  · intro g hg v w
    obtain ⟨s, -, rfl⟩ := hg
    exact statedSpGL_mem_isoGL s v w
  · intro c hc W hW hWA
    have hcp : glin c ^ p = 1 := by
      obtain ⟨s, hs, rfl⟩ := hc
      rw [← glin_pow, ← map_pow, hpow s hs, map_one, glin_one]
    have hciso : c ∈ isoGL (spFormD n K) := by
      obtain ⟨s, -, rfl⟩ := hc
      exact statedSpGL_mem_isoGL s
    have hzp := restrictElt_pow_eq_one hW (hWA c hc) hcp
    obtain ⟨g, hg⟩ := exists_gl_of_pow hp1 hzp
    refine ⟨g, ?_, hg⟩
    intro v w
    rw [hg]
    exact restrictElt_isometry hW _ spFormD_isSymm hciso v w

theorem card_eq_of_maximal [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E₁ E₂ : Subgroup (StatedSp n K)} (hpow₁ : ∀ a ∈ E₁, a ^ p = 1)
    (hcomm₁ : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a)
    (hmax₁ : ∀ g : StatedSp n K, g ^ p = 1 → (∀ a ∈ E₁, g * a = a * g) → g ∈ E₁)
    (hpow₂ : ∀ a ∈ E₂, a ^ p = 1) (hcomm₂ : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a)
    (hmax₂ : ∀ g : StatedSp n K, g ^ p = 1 → (∀ a ∈ E₂, g * a = a * g) → g ∈ E₂)
    (hne : E₁ ≠ ⊥) : Nat.card E₁ = Nat.card E₂ := by
  have hA₁ := genMax_map_statedSpGL hp hp2 hpow₁ hcomm₁ hmax₁
  have hA₂ := genMax_map_statedSpGL hp hp2 hpow₂ hcomm₂ hmax₂
  have hΓ : ∀ g : GL (Fin (n + n)) K,
      (∀ v w, spFormD n K (glin g v) (glin g w) = spFormD n K v w) → g ∈ isoGL (spFormD n K) :=
    fun g hg => hg
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hne₁ : ∃ c ∈ E₁.map (statedSpGL n K), c ≠ 1 :=
    ⟨statedSpGL n K s, ⟨s, hs, rfl⟩, fun h => hs1' (statedSpGL_injective (h.trans (map_one _).symm))⟩
  have hne₂ : ∃ c ∈ E₂.map (statedSpGL n K), c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE₂ : ∀ a ∈ E₂, a = 1 := fun a ha =>
      statedSpGL_injective ((hcon _ ⟨a, ha, rfl⟩).trans (map_one _).symm)
    have hsE₂ : s ∈ E₂ := hmax₂ s (hpow₁ s hs) fun a ha => by rw [hE₂ a ha]; simp
    exact hs1' (hE₂ s hsE₂)
  have h12 := (card_le_pow_lcm spFormD_isAlt hA₁).trans (pow_lcm_le_card spFormD_isAlt hA₂ hΓ hne₂)
  have h21 := (card_le_pow_lcm spFormD_isAlt hA₂).trans (pow_lcm_le_card spFormD_isAlt hA₁ hΓ hne₁)
  rw [Subgroup.card_map_of_injective statedSpGL_injective,
    Subgroup.card_map_of_injective statedSpGL_injective] at h12 h21
  exact le_antisymm h12 h21

end OrdPNsSp

end CFSG.StandardType
