module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Pointwise

variable {L : Type*} [Group L] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]

private def s16kA₁ : Subgroup (Q₁ × Q₂) := Subgroup.prod (⊤ : Subgroup Q₁) (⊥ : Subgroup Q₂)

private def s16kA₂ : Subgroup (Q₁ × Q₂) := Subgroup.prod (⊥ : Subgroup Q₁) (⊤ : Subgroup Q₂)

private theorem s16kA₁_mem {q : Q₁ × Q₂} : q ∈ s16kA₁ ↔ q.2 = 1 := by
  simp [s16kA₁, Subgroup.mem_prod]

private theorem s16kA₂_mem {q : Q₁ × Q₂} : q ∈ s16kA₂ ↔ q.1 = 1 := by
  simp [s16kA₂, Subgroup.mem_prod]

private theorem s16kA₁_inf_s16kA₂ : (s16kA₁ : Subgroup (Q₁ × Q₂)) ⊓ s16kA₂ = ⊥ := by
  ext q
  rw [Subgroup.mem_inf, s16kA₁_mem, s16kA₂_mem, Subgroup.mem_bot]
  exact ⟨fun h => Prod.ext h.2 h.1, fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩

private def s16kInvariant (ρ : L →* MulAut (Q₁ × Q₂)) (B : Subgroup (Q₁ × Q₂)) : Prop :=
  ∀ (l : L) (b : Q₁ × Q₂), b ∈ B → ρ l b ∈ B

private def s16kMinimal (ρ : L →* MulAut (Q₁ × Q₂)) (J : Subgroup (Q₁ × Q₂)) : Prop :=
  s16kInvariant ρ J ∧ J ≠ ⊥ ∧
    ∀ J' : Subgroup (Q₁ × Q₂), J' ≤ J → s16kInvariant ρ J' → J' ≠ ⊥ → J' = J

private def s16kShift (c : MulAut (Q₁ × Q₂)) (J : Subgroup (Q₁ × Q₂)) : Subgroup (Q₁ × Q₂) :=
  J.map c.toMonoidHom

private theorem s16kShift_mem (c : MulAut (Q₁ × Q₂)) (J : Subgroup (Q₁ × Q₂)) {x : Q₁ × Q₂} :
    x ∈ s16kShift c J ↔ ∃ j ∈ J, c j = x :=
  Subgroup.mem_map

private theorem s16kShift_one (J : Subgroup (Q₁ × Q₂)) :
    s16kShift (1 : MulAut (Q₁ × Q₂)) J = J := by
  rw [s16kShift]
  have h : (1 : MulAut (Q₁ × Q₂)).toMonoidHom = MonoidHom.id (Q₁ × Q₂) :=
    MonoidHom.ext fun x => by simp
  rw [h, Subgroup.map_id]

private theorem s16kShift_shift (c d : MulAut (Q₁ × Q₂)) (J : Subgroup (Q₁ × Q₂)) :
    s16kShift c (s16kShift d J) = s16kShift (c * d) J := by
  rw [s16kShift, s16kShift, s16kShift, Subgroup.map_map]
  congr 1

private theorem s16kShift_ne_bot (c : MulAut (Q₁ × Q₂)) (J : Subgroup (Q₁ × Q₂)) :
    s16kShift c J ≠ ⊥ ↔ J ≠ ⊥ := by
  constructor
  · intro h hJ
    exact h (by rw [hJ, s16kShift, Subgroup.map_bot])
  · intro h hc
    have h1 : s16kShift c⁻¹ (s16kShift c J) = s16kShift c⁻¹ ⊥ := by rw [hc]
    rw [s16kShift_shift, inv_mul_cancel, s16kShift_one, s16kShift, Subgroup.map_bot] at h1
    exact h h1

private theorem s16kInvariant_inf {ρ : L →* MulAut (Q₁ × Q₂)} {B C : Subgroup (Q₁ × Q₂)}
    (hB : s16kInvariant ρ B) (hC : s16kInvariant ρ C) : s16kInvariant ρ (B ⊓ C) :=
  fun l b hb => ⟨hB l b hb.1, hC l b hb.2⟩

private theorem s16kInvariant_fst {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂}
    {ρ : L →* MulAut (Q₁ × Q₂)}
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2))
    {J : Subgroup (Q₁ × Q₂)} (hJ : s16kInvariant ρ J) :
    ∀ l : L, ∀ b ∈ J.map (MonoidHom.fst Q₁ Q₂), ρ₁ l b ∈ J.map (MonoidHom.fst Q₁ Q₂) := by
  intro l b hb
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hb
  simpa [hρ l j] using Subgroup.mem_map_of_mem (MonoidHom.fst Q₁ Q₂) (hJ l j hj)

private theorem s16kInvariant_snd {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂}
    {ρ : L →* MulAut (Q₁ × Q₂)}
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2))
    {J : Subgroup (Q₁ × Q₂)} (hJ : s16kInvariant ρ J) :
    ∀ l : L, ∀ b ∈ J.map (MonoidHom.snd Q₁ Q₂), ρ₂ l b ∈ J.map (MonoidHom.snd Q₁ Q₂) := by
  intro l b hb
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hb
  simpa [hρ l j] using Subgroup.mem_map_of_mem (MonoidHom.snd Q₁ Q₂) (hJ l j hj)

private theorem s16kInvariant_prod_top_bot {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂}
    {ρ : L →* MulAut (Q₁ × Q₂)}
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2)) :
    s16kInvariant ρ (s16kA₁ : Subgroup (Q₁ × Q₂)) := by
  intro l b hb
  rw [s16kA₁_mem] at hb ⊢
  rw [hρ l b]
  simp [hb]

private theorem s16kInvariant_prod_bot_top {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂}
    {ρ : L →* MulAut (Q₁ × Q₂)}
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2)) :
    s16kInvariant ρ (s16kA₂ : Subgroup (Q₁ × Q₂)) := by
  intro l b hb
  rw [s16kA₂_mem] at hb ⊢
  rw [hρ l b]
  simp [hb]

private theorem s16k_eq_prod_top_bot_of_invariant_ne_bot
    {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂} {ρ : L →* MulAut (Q₁ × Q₂)}
    (hirr₁ : ∀ B : Subgroup Q₁, (∀ l : L, ∀ b ∈ B, ρ₁ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2))
    {J : Subgroup (Q₁ × Q₂)} (hJle : J ≤ s16kA₁) (hJ : s16kInvariant ρ J)
    (hJne : J ≠ ⊥) : J = s16kA₁ := by
  have hBne : J.map (MonoidHom.fst Q₁ Q₂) ≠ ⊥ := by
    intro hBbot
    have hJleA₂ : J ≤ s16kA₂ := by
      intro j hj
      rw [s16kA₂_mem]
      have h1 : j.1 ∈ J.map (MonoidHom.fst Q₁ Q₂) := Subgroup.mem_map_of_mem _ hj
      rw [hBbot, Subgroup.mem_bot] at h1
      exact h1
    have hle : J ≤ (⊥ : Subgroup (Q₁ × Q₂)) := by
      calc J ≤ s16kA₁ ⊓ s16kA₂ := le_inf hJle hJleA₂
        _ = ⊥ := s16kA₁_inf_s16kA₂
    exact hJne (le_bot_iff.mp hle)
  rcases hirr₁ (J.map (MonoidHom.fst Q₁ Q₂)) (s16kInvariant_fst hρ hJ) with h | h
  · exact absurd h hBne
  · apply le_antisymm hJle
    intro q hq
    have hq2 : q.2 = 1 := s16kA₁_mem.mp hq
    have hq1 : q.1 ∈ J.map (MonoidHom.fst Q₁ Q₂) := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hj1⟩ := Subgroup.mem_map.mp hq1
    have hj2 : j.2 = 1 := s16kA₁_mem.mp (hJle hj)
    have hjeq : j = q := Prod.ext hj1 (by rw [hj2, hq2])
    rwa [← hjeq]

private theorem s16k_eq_prod_bot_top_of_invariant_ne_bot
    {ρ₁ : L →* MulAut Q₁} {ρ₂ : L →* MulAut Q₂} {ρ : L →* MulAut (Q₁ × Q₂)}
    (hirr₂ : ∀ B : Subgroup Q₂, (∀ l : L, ∀ b ∈ B, ρ₂ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2))
    {J : Subgroup (Q₁ × Q₂)} (hJle : J ≤ s16kA₂) (hJ : s16kInvariant ρ J)
    (hJne : J ≠ ⊥) : J = s16kA₂ := by
  have hBne : J.map (MonoidHom.snd Q₁ Q₂) ≠ ⊥ := by
    intro hBbot
    have hJleA₁ : J ≤ s16kA₁ := by
      intro j hj
      rw [s16kA₁_mem]
      have h1 : j.2 ∈ J.map (MonoidHom.snd Q₁ Q₂) := Subgroup.mem_map_of_mem _ hj
      rw [hBbot, Subgroup.mem_bot] at h1
      exact h1
    have hle : J ≤ (⊥ : Subgroup (Q₁ × Q₂)) := by
      calc J ≤ s16kA₂ ⊓ s16kA₁ := le_inf hJle hJleA₁
        _ = ⊥ := by rw [inf_comm, s16kA₁_inf_s16kA₂]
    exact hJne (le_bot_iff.mp hle)
  rcases hirr₂ (J.map (MonoidHom.snd Q₁ Q₂)) (s16kInvariant_snd hρ hJ) with h | h
  · exact absurd h hBne
  · apply le_antisymm hJle
    intro q hq
    have hq1 : q.1 = 1 := s16kA₂_mem.mp hq
    have hq2 : q.2 ∈ J.map (MonoidHom.snd Q₁ Q₂) := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hj2⟩ := Subgroup.mem_map.mp hq2
    have hj1 : j.1 = 1 := s16kA₂_mem.mp (hJle hj)
    have hjeq : j = q := Prod.ext (by rw [hj1, hq1]) hj2
    rwa [← hjeq]

theorem s16k_pRank_centralizer_prod {L : Type} [Group L] {Q₁ Q₂ : Type} [CommGroup Q₁]
    [CommGroup Q₂] [Finite Q₁] [Finite Q₂] (ρ₁ : L →* MulAut Q₁) (ρ₂ : L →* MulAut Q₂)
    (h₁ : ∀ x : Q₁, x ^ 2 = 1) (h₂ : ∀ x : Q₂, x ^ 2 = 1)
    (hirr₁ : ∀ B : Subgroup Q₁, (∀ l : L, ∀ b ∈ B, ρ₁ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hirr₂ : ∀ B : Subgroup Q₂, (∀ l : L, ∀ b ∈ B, ρ₂ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hC₁ : Subgroup.centralizer ((ρ₁.range : Subgroup (MulAut Q₁)) : Set (MulAut Q₁)) = ⊥)
    (hC₂ : Subgroup.centralizer ((ρ₂.range : Subgroup (MulAut Q₂)) : Set (MulAut Q₂)) = ⊥)
    (ρ : L →* MulAut (Q₁ × Q₂)) (hρ : ∀ (l : L) (q : Q₁ × Q₂), ρ l q = (ρ₁ l q.1, ρ₂ l q.2))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.centralizer ((ρ.range : Subgroup (MulAut (Q₁ × Q₂))) :
      Set (MulAut (Q₁ × Q₂)))) ≤ if p = 3 then 1 else 0 := by
  classical
  let C : Subgroup (MulAut (Q₁ × Q₂)) :=
    Subgroup.centralizer ((ρ.range : Subgroup (MulAut (Q₁ × Q₂))) : Set (MulAut (Q₁ × Q₂)))
  have invA₁ : s16kInvariant ρ (s16kA₁ : Subgroup (Q₁ × Q₂)) :=
    s16kInvariant_prod_top_bot hρ
  have invA₂ : s16kInvariant ρ (s16kA₂ : Subgroup (Q₁ × Q₂)) :=
    s16kInvariant_prod_bot_top hρ
  have eqA₁ : ∀ {J : Subgroup (Q₁ × Q₂)}, J ≤ s16kA₁ → s16kInvariant ρ J → J ≠ ⊥ →
      J = s16kA₁ :=
    fun hle hinv hne => s16k_eq_prod_top_bot_of_invariant_ne_bot hirr₁ hρ hle hinv hne
  have eqA₂ : ∀ {J : Subgroup (Q₁ × Q₂)}, J ≤ s16kA₂ → s16kInvariant ρ J → J ≠ ⊥ →
      J = s16kA₂ :=
    fun hle hinv hne => s16k_eq_prod_bot_top_of_invariant_ne_bot hirr₂ hρ hle hinv hne
  have infA₁ : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₁ →
      J ⊓ s16kA₁ = ⊥ := by
    intro J hmin hJne
    by_contra hne
    have hJle : J ⊓ s16kA₁ ≤ J := inf_le_left
    have hinv : s16kInvariant ρ (J ⊓ s16kA₁) := s16kInvariant_inf hmin.1 invA₁
    have heq : J ⊓ s16kA₁ = J := hmin.2.2 (J ⊓ s16kA₁) hJle hinv hne
    have hJA₁ : J ≤ s16kA₁ := by rw [← heq]; exact inf_le_right
    exact hJne (eqA₁ hJA₁ hmin.1 hmin.2.1)
  have infA₂ : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₂ →
      J ⊓ s16kA₂ = ⊥ := by
    intro J hmin hJne
    by_contra hne
    have hJle : J ⊓ s16kA₂ ≤ J := inf_le_left
    have hinv : s16kInvariant ρ (J ⊓ s16kA₂) := s16kInvariant_inf hmin.1 invA₂
    have heq : J ⊓ s16kA₂ = J := hmin.2.2 (J ⊓ s16kA₂) hJle hinv hne
    have hJA₂ : J ≤ s16kA₂ := by rw [← heq]; exact inf_le_right
    exact hJne (eqA₂ hJA₂ hmin.1 hmin.2.1)
  have mapfst : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₂ →
      J.map (MonoidHom.fst Q₁ Q₂) = ⊤ := by
    intro J hmin hJne₂
    have hBne : J.map (MonoidHom.fst Q₁ Q₂) ≠ ⊥ := by
      intro hBbot
      have hJleA₂ : J ≤ s16kA₂ := by
        intro j hj
        rw [s16kA₂_mem]
        have h1 : j.1 ∈ J.map (MonoidHom.fst Q₁ Q₂) := Subgroup.mem_map_of_mem _ hj
        rw [hBbot, Subgroup.mem_bot] at h1
        exact h1
      exact hJne₂ (eqA₂ hJleA₂ hmin.1 hmin.2.1)
    rcases hirr₁ _ (s16kInvariant_fst hρ hmin.1) with h | h
    · exact absurd h hBne
    · exact h
  have mapsnd : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₁ →
      J.map (MonoidHom.snd Q₁ Q₂) = ⊤ := by
    intro J hmin hJne₁
    have hBne : J.map (MonoidHom.snd Q₁ Q₂) ≠ ⊥ := by
      intro hBbot
      have hJleA₁ : J ≤ s16kA₁ := by
        intro j hj
        rw [s16kA₁_mem]
        have h1 : j.2 ∈ J.map (MonoidHom.snd Q₁ Q₂) := Subgroup.mem_map_of_mem _ hj
        rw [hBbot, Subgroup.mem_bot] at h1
        exact h1
      exact hJne₁ (eqA₁ hJleA₁ hmin.1 hmin.2.1)
    rcases hirr₂ _ (s16kInvariant_snd hρ hmin.1) with h | h
    · exact absurd h hBne
    · exact h
  have hfst_bij : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₁ → J ≠ s16kA₂ →
      Function.Bijective ((MonoidHom.fst Q₁ Q₂).comp J.subtype) := by
    intro J hmin hJ₁ hJ₂
    refine ⟨?_, ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro j hj
      rw [MonoidHom.mem_ker] at hj
      have hmem : (j : Q₁ × Q₂) ∈ J ⊓ s16kA₂ := ⟨j.2, s16kA₂_mem.mpr hj⟩
      rw [infA₂ hmin hJ₂, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro q
      have hq : q ∈ J.map (MonoidHom.fst Q₁ Q₂) := by
        rw [mapfst hmin hJ₂]; exact Subgroup.mem_top q
      obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨j, hj⟩, hjq⟩
  have hsnd_bij : ∀ {J : Subgroup (Q₁ × Q₂)}, s16kMinimal ρ J → J ≠ s16kA₁ → J ≠ s16kA₂ →
      Function.Bijective ((MonoidHom.snd Q₁ Q₂).comp J.subtype) := by
    intro J hmin hJ₁ hJ₂
    refine ⟨?_, ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro j hj
      rw [MonoidHom.mem_ker] at hj
      have hmem : (j : Q₁ × Q₂) ∈ J ⊓ s16kA₁ := ⟨j.2, s16kA₁_mem.mpr hj⟩
      rw [infA₁ hmin hJ₁, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro q
      have hq : q ∈ J.map (MonoidHom.snd Q₁ Q₂) := by
        rw [mapsnd hmin hJ₁]; exact Subgroup.mem_top q
      obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨j, hj⟩, hjq⟩
  have unique : ∀ {J J' : Subgroup (Q₁ × Q₂)},
      s16kMinimal ρ J → J ≠ s16kA₁ → J ≠ s16kA₂ →
      s16kMinimal ρ J' → J' ≠ s16kA₁ → J' ≠ s16kA₂ → J = J' := by
    intro J J' hJ hJ₁ hJ₂ hJ' hJ'₁ hJ'₂
    let e : J ≃* Q₁ := MulEquiv.ofBijective _ (hfst_bij hJ hJ₁ hJ₂)
    let d : J ≃* Q₂ := MulEquiv.ofBijective _ (hsnd_bij hJ hJ₁ hJ₂)
    let φ : Q₁ ≃* Q₂ := e.symm.trans d
    have he : ∀ j : J, (e j : Q₁) = (j : Q₁ × Q₂).1 := by
      intro j
      simp [e, MulEquiv.ofBijective_apply, MonoidHom.comp_apply]
    have hd : ∀ j : J, (d j : Q₂) = (j : Q₁ × Q₂).2 := by
      intro j
      simp [d, MulEquiv.ofBijective_apply, MonoidHom.comp_apply]
    have hφapply : ∀ j : J, φ (j : Q₁ × Q₂).1 = (j : Q₁ × Q₂).2 := by
      intro j
      calc φ (j : Q₁ × Q₂).1 = d (e.symm (j : Q₁ × Q₂).1) := rfl
        _ = d j := by
              congr 1
              apply e.injective
              simpa [he j] using MulEquiv.apply_symm_apply e (j : Q₁ × Q₂).1
        _ = (j : Q₁ × Q₂).2 := hd j
    have hφmem : ∀ q : Q₁ × Q₂, q.2 = φ q.1 → q ∈ J := by
      intro q hq
      have hmem : ((e.symm q.1 : J) : Q₁ × Q₂) ∈ J := (e.symm q.1).2
      have heq : ((e.symm q.1 : J) : Q₁ × Q₂) = q := by
        ext
        · rw [← he (e.symm q.1), MulEquiv.apply_symm_apply]
        · rw [← hd (e.symm q.1), hq]
          rfl
      rwa [heq] at hmem
    have hφequiv : ∀ (l : L) (q : Q₁), φ (ρ₁ l q) = ρ₂ l (φ q) := by
      intro l q
      let j : J := e.symm q
      have hjl : (j : Q₁ × Q₂).1 = q := by
        rw [← he j]
        exact MulEquiv.apply_symm_apply e q
      have hj : (ρ l (j : Q₁ × Q₂)) ∈ J := hJ.1 l (j : Q₁ × Q₂) j.2
      have h1 : e ⟨ρ l (j : Q₁ × Q₂), hj⟩ = ρ₁ l q := by
        rw [he ⟨ρ l (j : Q₁ × Q₂), hj⟩]
        simp [hρ l (j : Q₁ × Q₂), hjl]
      have h2 : e.symm (ρ₁ l q) = ⟨ρ l (j : Q₁ × Q₂), hj⟩ := by
        rw [← h1, MulEquiv.symm_apply_apply]
      calc φ (ρ₁ l q) = d (e.symm (ρ₁ l q)) := rfl
        _ = d ⟨ρ l (j : Q₁ × Q₂), hj⟩ := by rw [h2]
        _ = ((ρ l (j : Q₁ × Q₂)) : Q₁ × Q₂).2 := hd _
        _ = ρ₂ l ((j : Q₁ × Q₂).2) := by rw [hρ l (j : Q₁ × Q₂)]
        _ = ρ₂ l (d j) := by rw [hd j]
        _ = ρ₂ l (φ q) := rfl
    let e' : J' ≃* Q₁ := MulEquiv.ofBijective _ (hfst_bij hJ' hJ'₁ hJ'₂)
    let d' : J' ≃* Q₂ := MulEquiv.ofBijective _ (hsnd_bij hJ' hJ'₁ hJ'₂)
    let φ' : Q₁ ≃* Q₂ := e'.symm.trans d'
    have he' : ∀ j : J', (e' j : Q₁) = (j : Q₁ × Q₂).1 := by
      intro j
      simp [e', MulEquiv.ofBijective_apply, MonoidHom.comp_apply]
    have hd' : ∀ j : J', (d' j : Q₂) = (j : Q₁ × Q₂).2 := by
      intro j
      simp [d', MulEquiv.ofBijective_apply, MonoidHom.comp_apply]
    have hφ'apply : ∀ j : J', φ' (j : Q₁ × Q₂).1 = (j : Q₁ × Q₂).2 := by
      intro j
      calc φ' (j : Q₁ × Q₂).1 = d' (e'.symm (j : Q₁ × Q₂).1) := rfl
        _ = d' j := by
              congr 1
              apply e'.injective
              simpa [he' j] using MulEquiv.apply_symm_apply e' (j : Q₁ × Q₂).1
        _ = (j : Q₁ × Q₂).2 := hd' j
    have hφ'mem : ∀ q : Q₁ × Q₂, q.2 = φ' q.1 → q ∈ J' := by
      intro q hq
      have hmem : ((e'.symm q.1 : J') : Q₁ × Q₂) ∈ J' := (e'.symm q.1).2
      have heq : ((e'.symm q.1 : J') : Q₁ × Q₂) = q := by
        ext
        · rw [← he' (e'.symm q.1), MulEquiv.apply_symm_apply]
        · rw [← hd' (e'.symm q.1), hq]
          rfl
      rwa [heq] at hmem
    have hφ'equiv : ∀ (l : L) (q : Q₁), φ' (ρ₁ l q) = ρ₂ l (φ' q) := by
      intro l q
      let j : J' := e'.symm q
      have hjl : (j : Q₁ × Q₂).1 = q := by
        rw [← he' j]
        exact MulEquiv.apply_symm_apply e' q
      have hj : (ρ l (j : Q₁ × Q₂)) ∈ J' := hJ'.1 l (j : Q₁ × Q₂) j.2
      have h1 : e' ⟨ρ l (j : Q₁ × Q₂), hj⟩ = ρ₁ l q := by
        rw [he' ⟨ρ l (j : Q₁ × Q₂), hj⟩]
        simp [hρ l (j : Q₁ × Q₂), hjl]
      have h2 : e'.symm (ρ₁ l q) = ⟨ρ l (j : Q₁ × Q₂), hj⟩ := by
        rw [← h1, MulEquiv.symm_apply_apply]
      calc φ' (ρ₁ l q) = d' (e'.symm (ρ₁ l q)) := rfl
        _ = d' ⟨ρ l (j : Q₁ × Q₂), hj⟩ := by rw [h2]
        _ = ((ρ l (j : Q₁ × Q₂)) : Q₁ × Q₂).2 := hd' _
        _ = ρ₂ l ((j : Q₁ × Q₂).2) := by rw [hρ l (j : Q₁ × Q₂)]
        _ = ρ₂ l (d' j) := by rw [hd' j]
        _ = ρ₂ l (φ' q) := rfl
    let g : Q₁ ≃* Q₁ := φ.trans φ'.symm
    have hgmem : g ∈
        Subgroup.centralizer ((ρ₁.range : Subgroup (MulAut Q₁)) : Set (MulAut Q₁)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hh
      apply MulEquiv.ext
      intro q
      change ρ₁ l (g q) = g (ρ₁ l q)
      change ρ₁ l (φ'.symm (φ q)) = φ'.symm (φ (ρ₁ l q))
      rw [hφequiv l q]
      have h2 : φ' (ρ₁ l (φ'.symm (φ q))) = ρ₂ l (φ q) := by
        rw [hφ'equiv l (φ'.symm (φ q)), MulEquiv.apply_symm_apply]
      rw [← h2, MulEquiv.symm_apply_apply]
    have hg1 : g = 1 := by
      rw [hC₁, Subgroup.mem_bot] at hgmem
      exact hgmem
    have hφeq : φ = φ' := by
      apply MulEquiv.ext
      intro q
      have h2 : φ'.symm (φ q) = q := by
        have h3 := congrArg (fun e : Q₁ ≃* Q₁ => e q) hg1
        simpa [g] using h3
      calc φ q = φ' (φ'.symm (φ q)) := (MulEquiv.apply_symm_apply φ' (φ q)).symm
        _ = φ' q := by rw [h2]
    apply Subgroup.ext
    intro q
    constructor
    · intro hq
      have h1 : q.2 = φ q.1 := (hφapply ⟨q, hq⟩).symm
      rw [hφeq] at h1
      exact hφ'mem q h1
    · intro hq
      have h1 : q.2 = φ' q.1 := (hφ'apply ⟨q, hq⟩).symm
      rw [← hφeq] at h1
      exact hφmem q h1
  have hshift_inv : ∀ (c : MulAut (Q₁ × Q₂)), c ∈ C → ∀ {J : Subgroup (Q₁ × Q₂)},
      s16kInvariant ρ J → s16kInvariant ρ (s16kShift c J) := by
    intro c hc J hJ
    have hcρ : ∀ l : L, ρ l * c = c * ρ l := fun l =>
      (Subgroup.mem_centralizer_iff.mp hc) (ρ l) (MonoidHom.mem_range.mpr ⟨l, rfl⟩)
    intro l b hb
    rw [s16kShift_mem] at hb ⊢
    obtain ⟨j, hj, rfl⟩ := hb
    refine ⟨ρ l j, hJ l j hj, ?_⟩
    have h3 := congrArg (fun e : MulAut (Q₁ × Q₂) => e j) (hcρ l)
    simp only [MulAut.mul_apply] at h3
    rw [← h3]
  have hshift_min : ∀ (c : MulAut (Q₁ × Q₂)), c ∈ C → ∀ J, s16kMinimal ρ J →
      s16kMinimal ρ (s16kShift c J) := by
    intro c hc J hJ
    refine ⟨hshift_inv c hc hJ.1, ?_, ?_⟩
    · rw [s16kShift_ne_bot]; exact hJ.2.1
    · intro J' hJ'le hJ'inv hJ'ne
      have h1 : s16kShift c⁻¹ J' ≤ J := by
        calc s16kShift c⁻¹ J' ≤ s16kShift c⁻¹ (s16kShift c J) := Subgroup.map_mono hJ'le
          _ = J := by rw [s16kShift_shift, inv_mul_cancel, s16kShift_one]
      have h2 : s16kInvariant ρ (s16kShift c⁻¹ J') := hshift_inv c⁻¹ (inv_mem hc) hJ'inv
      have h3 : s16kShift c⁻¹ J' ≠ ⊥ := by rw [s16kShift_ne_bot]; exact hJ'ne
      have h4 : s16kShift c⁻¹ J' = J := hJ.2.2 _ h1 h2 h3
      have h5 := congrArg (s16kShift c) h4
      rwa [s16kShift_shift, mul_inv_cancel, s16kShift_one] at h5
  have hfix_triv : ∀ c : MulAut (Q₁ × Q₂), c ∈ C →
      (∀ J, s16kMinimal ρ J → s16kShift c J = J) → c = 1 := by
    intro c hc hfix
    have hcρ : ∀ l : L, ρ l * c = c * ρ l := fun l =>
      (Subgroup.mem_centralizer_iff.mp hc) (ρ l) (MonoidHom.mem_range.mpr ⟨l, rfl⟩)
    have hcA₁ : s16kShift c s16kA₁ = s16kA₁ := by
      by_cases h : s16kA₁ = (⊥ : Subgroup (Q₁ × Q₂))
      · rw [h, s16kShift, Subgroup.map_bot]
      · exact hfix s16kA₁ ⟨invA₁, h, fun J' hle hinv hne => eqA₁ hle hinv hne⟩
    have hcA₂ : s16kShift c s16kA₂ = s16kA₂ := by
      by_cases h : s16kA₂ = (⊥ : Subgroup (Q₁ × Q₂))
      · rw [h, s16kShift, Subgroup.map_bot]
      · exact hfix s16kA₂ ⟨invA₂, h, fun J' hle hinv hne => eqA₂ hle hinv hne⟩
    have hcA₁' : s16kShift c⁻¹ s16kA₁ = s16kA₁ := by
      calc s16kShift c⁻¹ s16kA₁ = s16kShift c⁻¹ (s16kShift c s16kA₁) := by rw [hcA₁]
        _ = s16kA₁ := by rw [s16kShift_shift, inv_mul_cancel, s16kShift_one]
    have hcA₂' : s16kShift c⁻¹ s16kA₂ = s16kA₂ := by
      calc s16kShift c⁻¹ s16kA₂ = s16kShift c⁻¹ (s16kShift c s16kA₂) := by rw [hcA₂]
        _ = s16kA₂ := by rw [s16kShift_shift, inv_mul_cancel, s16kShift_one]
    have hmA₁ : ∀ {q : Q₁ × Q₂}, q ∈ s16kA₁ → c q ∈ s16kA₁ := by
      intro q hq
      have h : c q ∈ s16kShift c s16kA₁ := Subgroup.mem_map_of_mem c.toMonoidHom hq
      rwa [hcA₁] at h
    have hmA₂ : ∀ {q : Q₁ × Q₂}, q ∈ s16kA₂ → c q ∈ s16kA₂ := by
      intro q hq
      have h : c q ∈ s16kShift c s16kA₂ := Subgroup.mem_map_of_mem c.toMonoidHom hq
      rwa [hcA₂] at h
    have hmA₁' : ∀ {q : Q₁ × Q₂}, q ∈ s16kA₁ → c⁻¹ q ∈ s16kA₁ := by
      intro q hq
      have h : c⁻¹ q ∈ s16kShift c⁻¹ s16kA₁ := Subgroup.mem_map_of_mem c⁻¹.toMonoidHom hq
      rwa [hcA₁'] at h
    have hmA₂' : ∀ {q : Q₁ × Q₂}, q ∈ s16kA₂ → c⁻¹ q ∈ s16kA₂ := by
      intro q hq
      have h : c⁻¹ q ∈ s16kShift c⁻¹ s16kA₂ := Subgroup.mem_map_of_mem c⁻¹.toMonoidHom hq
      rwa [hcA₂'] at h
    let f : Q₁ →* Q₁ :=
      { toFun := fun x => (c (x, 1)).1
        map_one' := by
          show (c (1 : Q₁ × Q₂)).1 = 1
          rw [map_one]
          rfl
        map_mul' := fun x y => by
          have h1 : c (x * y, 1) = c (x, 1) * c (y, 1) := by
            simpa using map_mul c (x, 1) (y, 1)
          show (c (x * y, 1)).1 = (c (x, 1)).1 * (c (y, 1)).1
          rw [h1]
          rfl }
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxA₁ : c (x, 1) ∈ s16kA₁ := hmA₁ (by simp [s16kA₁_mem])
      have hxA₂ : c (x, 1) ∈ s16kA₂ := by
        rw [s16kA₂_mem]
        simpa [f] using hx
      have hbot : c (x, 1) ∈ (⊥ : Subgroup (Q₁ × Q₂)) := by
        rw [← s16kA₁_inf_s16kA₂]
        exact ⟨hxA₁, hxA₂⟩
      rw [Subgroup.mem_bot] at hbot
      have hx1 : (x, 1) = (1 : Q₁ × Q₂) := by
        have h6 := congrArg c⁻¹ hbot
        simpa using h6
      exact (Prod.ext_iff.mp hx1).1
    have hfsurj : Function.Surjective f := by
      intro y
      refine ⟨(c⁻¹ (y, 1)).1, ?_⟩
      have hmem : c⁻¹ (y, 1) ∈ s16kA₁ := by
        have hq : (y, (1 : Q₂)) ∈ s16kA₁ := by simp [s16kA₁_mem]
        have h : c⁻¹ (y, (1 : Q₂)) ∈ s16kShift c⁻¹ s16kA₁ :=
          Subgroup.mem_map_of_mem c⁻¹.toMonoidHom hq
        rwa [hcA₁'] at h
      have hmem2 : (c⁻¹ (y, 1)).2 = 1 := s16kA₁_mem.mp hmem
      have hthis : ((c⁻¹ (y, 1)).1, (1 : Q₂)) = c⁻¹ (y, 1) :=
        Prod.ext rfl hmem2.symm
      change (c ((c⁻¹ (y, 1)).1, 1)).1 = y
      rw [hthis]
      simpa using congrArg Prod.fst (MulEquiv.apply_symm_apply c (y, 1))
    let c₁ : MulAut Q₁ := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
    have hc₁comm : c₁ ∈
        Subgroup.centralizer ((ρ₁.range : Subgroup (MulAut Q₁)) : Set (MulAut Q₁)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hh
      apply MulEquiv.ext
      intro x
      have hc₁x : c₁ x = (c (x, 1)).1 := by
        change f x = (c (x, 1)).1
        rfl
      have hstep : (c (ρ l (x, 1))).1 = (ρ l (c (x, 1))).1 := by
        have h3 := congrArg (fun e : MulAut (Q₁ × Q₂) => e (x, 1)) (hcρ l)
        simp only [MulAut.mul_apply] at h3
        rw [← h3]
      calc (ρ₁ l * c₁) x = ρ₁ l (c₁ x) := rfl
        _ = ρ₁ l ((c (x, 1)).1) := by rw [hc₁x]
        _ = (ρ l (c (x, 1))).1 := by rw [hρ l (c (x, 1))]
        _ = (c (ρ l (x, 1))).1 := hstep.symm
        _ = (c (ρ₁ l x, (1 : Q₂))).1 := by rw [hρ l (x, 1)]; simp
        _ = c₁ (ρ₁ l x) := by
              change (c (ρ₁ l x, (1 : Q₂))).1 = f (ρ₁ l x)
              rfl
    have hc₁one : c₁ = 1 := by
      rw [hC₁, Subgroup.mem_bot] at hc₁comm
      exact hc₁comm
    have hc₁apply : ∀ x : Q₁, (c (x, 1)).1 = x := by
      intro x
      have h3 : c₁ x = x := by
        have h4 := congrArg (fun e : MulAut Q₁ => e x) hc₁one
        simpa using h4
      change f x = x
      exact h3
    let f₂ : Q₂ →* Q₂ :=
      { toFun := fun y => (c (1, y)).2
        map_one' := by
          show (c (1 : Q₁ × Q₂)).2 = 1
          rw [map_one]
          rfl
        map_mul' := fun x y => by
          have h1 : c (1, x * y) = c (1, x) * c (1, y) := by
            simpa using map_mul c (1, x) (1, y)
          show (c (1, x * y)).2 = (c (1, x)).2 * (c (1, y)).2
          rw [h1]
          rfl }
    have hf₂inj : Function.Injective f₂ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have hyA₂ : c (1, y) ∈ s16kA₂ := hmA₂ (by simp [s16kA₂_mem])
      have hyA₁ : c (1, y) ∈ s16kA₁ := by
        rw [s16kA₁_mem]
        simpa [f₂] using hy
      have hbot : c (1, y) ∈ (⊥ : Subgroup (Q₁ × Q₂)) := by
        rw [← s16kA₁_inf_s16kA₂]
        exact ⟨hyA₁, hyA₂⟩
      rw [Subgroup.mem_bot] at hbot
      have hy1 : (1, y) = (1 : Q₁ × Q₂) := by
        have h6 := congrArg c⁻¹ hbot
        simpa using h6
      exact (Prod.ext_iff.mp hy1).2
    have hf₂surj : Function.Surjective f₂ := by
      intro y
      refine ⟨(c⁻¹ (1, y)).2, ?_⟩
      have hmem : c⁻¹ (1, y) ∈ s16kA₂ := by
        have hq : ((1 : Q₁), y) ∈ s16kA₂ := by simp [s16kA₂_mem]
        have h : c⁻¹ ((1 : Q₁), y) ∈ s16kShift c⁻¹ s16kA₂ :=
          Subgroup.mem_map_of_mem c⁻¹.toMonoidHom hq
        rwa [hcA₂'] at h
      have hmem1 : (c⁻¹ (1, y)).1 = 1 := s16kA₂_mem.mp hmem
      have hthis : ((1 : Q₁), (c⁻¹ (1, y)).2) = c⁻¹ (1, y) :=
        Prod.ext hmem1.symm rfl
      change (c (1, (c⁻¹ (1, y)).2)).2 = y
      rw [hthis]
      simpa using congrArg Prod.snd (MulEquiv.apply_symm_apply c (1, y))
    let c₂ : MulAut Q₂ := MulEquiv.ofBijective f₂ ⟨hf₂inj, hf₂surj⟩
    have hc₂comm : c₂ ∈
        Subgroup.centralizer ((ρ₂.range : Subgroup (MulAut Q₂)) : Set (MulAut Q₂)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hh
      apply MulEquiv.ext
      intro y
      have hc₂y : c₂ y = (c (1, y)).2 := by
        change f₂ y = (c (1, y)).2
        rfl
      have hstep : (c (ρ l (1, y))).2 = (ρ l (c (1, y))).2 := by
        have h3 := congrArg (fun e : MulAut (Q₁ × Q₂) => e (1, y)) (hcρ l)
        simp only [MulAut.mul_apply] at h3
        rw [← h3]
      calc (ρ₂ l * c₂) y = ρ₂ l (c₂ y) := rfl
        _ = ρ₂ l ((c (1, y)).2) := by rw [hc₂y]
        _ = (ρ l (c (1, y))).2 := by rw [hρ l (c (1, y))]
        _ = (c (ρ l (1, y))).2 := hstep.symm
        _ = (c (1, ρ₂ l y)).2 := by rw [hρ l (1, y)]; simp
        _ = c₂ (ρ₂ l y) := by
              change (c (1, ρ₂ l y)).2 = f₂ (ρ₂ l y)
              rfl
    have hc₂one : c₂ = 1 := by
      rw [hC₂, Subgroup.mem_bot] at hc₂comm
      exact hc₂comm
    have hc₂apply : ∀ y : Q₂, (c (1, y)).2 = y := by
      intro y
      have h3 : c₂ y = y := by
        have h4 := congrArg (fun e : MulAut Q₂ => e y) hc₂one
        simpa using h4
      change f₂ y = y
      exact h3
    apply MulEquiv.ext
    intro q
    have hq₁ : c (q.1, 1) = (q.1, 1) := by
      apply Prod.ext
      · exact hc₁apply q.1
      · exact s16kA₁_mem.mp (hmA₁ (by simp [s16kA₁_mem]))
    have hq₂ : c (1, q.2) = (1, q.2) := by
      apply Prod.ext
      · exact s16kA₂_mem.mp (hmA₂ (by simp [s16kA₂_mem]))
      · exact hc₂apply q.2
    calc c q = c ((q.1, 1) * (1, q.2)) := by
            congr 1
            ext <;> simp
      _ = c (q.1, 1) * c (1, q.2) := map_mul c _ _
      _ = (q.1, 1) * (1, q.2) := by rw [hq₁, hq₂]
      _ = q := by ext <;> simp
  haveI : Finite (Subgroup (Q₁ × Q₂)) := inferInstance
  let Mset : Set (Subgroup (Q₁ × Q₂)) := {J | s16kMinimal ρ J}
  let G : Subgroup (Q₁ × Q₂) :=
    if h : ∃ J : Subgroup (Q₁ × Q₂), s16kMinimal ρ J ∧ J ≠ s16kA₁ ∧ J ≠ s16kA₂
      then Classical.choose h else ⊥
  have hG : ∀ J, s16kMinimal ρ J → J ≠ s16kA₁ → J ≠ s16kA₂ → J = G := by
    intro J hJ hJ₁ hJ₂
    have hex : ∃ K : Subgroup (Q₁ × Q₂), s16kMinimal ρ K ∧ K ≠ s16kA₁ ∧ K ≠ s16kA₂ :=
      ⟨J, hJ, hJ₁, hJ₂⟩
    have hspec := Classical.choose_spec hex
    show J = (if h : ∃ K : Subgroup (Q₁ × Q₂), s16kMinimal ρ K ∧ K ≠ s16kA₁ ∧ K ≠ s16kA₂
      then Classical.choose h else ⊥)
    rw [dif_pos hex]
    exact unique hJ hJ₁ hJ₂ hspec.1 hspec.2.1 hspec.2.2
  have hsub : Mset ⊆ ({s16kA₁, s16kA₂, G} : Set (Subgroup (Q₁ × Q₂))) := by
    intro J hJ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h1 : J = s16kA₁
    · exact Or.inl h1
    by_cases h2 : J = s16kA₂
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (hG J hJ h1 h2))
  have hcard : Mset.ncard ≤ 3 := by
    calc Mset.ncard ≤ ({s16kA₁, s16kA₂, G} : Set (Subgroup (Q₁ × Q₂))).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ 3 := by
          rw [show ({s16kA₁, s16kA₂, G} : Set (Subgroup (Q₁ × Q₂))) =
              insert s16kA₁ (insert s16kA₂ ({G} : Set (Subgroup (Q₁ × Q₂)))) by ext; simp]
          calc (insert s16kA₁ (insert s16kA₂ ({G} : Set (Subgroup (Q₁ × Q₂))))).ncard
              ≤ (insert s16kA₂ ({G} : Set (Subgroup (Q₁ × Q₂)))).ncard + 1 :=
                Set.ncard_insert_le _ _
            _ ≤ (({G} : Set (Subgroup (Q₁ × Q₂))).ncard + 1) + 1 := by
                have h := Set.ncard_insert_le s16kA₂ ({G} : Set (Subgroup (Q₁ × Q₂)))
                omega
            _ ≤ 3 := by simp
  have hM3 : Nat.card Mset ≤ 3 := by
    rw [Nat.card_coe_set_eq]
    exact hcard
  let Φ : ↥C →* Equiv.Perm Mset :=
    { toFun := fun c =>
        { toFun := fun J => ⟨s16kShift (c : MulAut (Q₁ × Q₂)) J.1,
              hshift_min (c : MulAut (Q₁ × Q₂)) c.2 J.1 J.2⟩
          invFun := fun J => ⟨s16kShift (c : MulAut (Q₁ × Q₂))⁻¹ J.1,
              hshift_min (c : MulAut (Q₁ × Q₂))⁻¹ (inv_mem c.2) J.1 J.2⟩
          left_inv := fun J => by
            apply Subtype.ext
            change s16kShift (c : MulAut (Q₁ × Q₂))⁻¹
              (s16kShift (c : MulAut (Q₁ × Q₂)) J.1) = J.1
            rw [s16kShift_shift, inv_mul_cancel, s16kShift_one]
          right_inv := fun J => by
            apply Subtype.ext
            change s16kShift (c : MulAut (Q₁ × Q₂))
              (s16kShift (c : MulAut (Q₁ × Q₂))⁻¹ J.1) = J.1
            rw [s16kShift_shift, mul_inv_cancel, s16kShift_one] }
      map_one' := by
        ext J
        simp [s16kShift_one]
      map_mul' := fun c d => by
        ext J
        simp [s16kShift_shift] }
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    apply Subtype.ext
    apply hfix_triv (c : MulAut (Q₁ × Q₂)) c.2
    intro J hJ
    have h3 := congrArg (fun e : Equiv.Perm Mset => e ⟨J, hJ⟩) hc
    exact Subtype.ext_iff.mp h3
  have hCcard : Nat.card ↥C ∣ 6 := by
    have hdvd : Nat.card ↥C ∣ Nat.card (Equiv.Perm Mset) :=
      Subgroup.card_dvd_of_injective Φ hΦinj
    rw [Nat.card_perm] at hdvd
    have h4 : Nat.factorial (Nat.card Mset) ∣ Nat.factorial 3 :=
      Nat.factorial_dvd_factorial hM3
    have h5 : Nat.factorial 3 = 6 := by norm_num
    rw [h5] at h4
    exact hdvd.trans h4
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hE hEea
  have hdvd : Nat.card E ∣ 6 := (Subgroup.card_dvd_of_le hE).trans hCcard
  have hEpg : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEea.2 g g.2)⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hEpg.exists_card_eq
  by_cases hp3 : p = 3
  · subst p
    rw [if_pos rfl]
    rw [hn]
    have hle6 : 3 ^ n ≤ 6 := by
      rw [← hn]
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hn2 : n < 2 := by
      by_contra h
      have h2 : 2 ≤ n := not_lt.1 h
      have hmono : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      norm_num at hmono
      omega
    have hn1 : n ≤ 1 := Nat.lt_succ_iff.mp hn2
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 3 ^ 1 := rfl
  · rw [if_neg hp3]
    rw [hn]
    have hn0 : n = 0 := by
      by_contra h
      have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hpn : p ^ n ∣ 6 := by rw [← hn]; exact hdvd
      have hpdvd : p ∣ 6 := (dvd_pow_self p h).trans hpn
      have hpge5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      have hple6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpdvd
      have hp56 : p = 5 ∨ p = 6 := by omega
      rcases hp56 with h5 | h6
      · rw [h5] at hpdvd; norm_num at hpdvd
      · rw [h6] at hp; norm_num at hp
    rw [hn0, pow_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
