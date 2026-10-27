module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

@[expose] def qTwoChartHub_spec (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (ψ : Su F0 2 1 m →* G) (ε0 : Fin m ↪ Fin (n + 1)) (blk : Finset (Fin (n + 1)) → Subgroup G) :
    Prop :=
  ∀ {g : G} {π : Equiv.Perm (Fin (n + 1))} {T : Finset (Fin m)},
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π → 2 ≤ T.card → T.card ≤ 4 →
      blk (qTwoFrameSet ε0 π T) = qTwoBlockOf ψ g T

theorem qTwoChartHub_card_frameSet (ε0 : Fin m ↪ Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1)))
    (T : Finset (Fin m)) : (qTwoFrameSet ε0 π T).card = T.card := by
  unfold qTwoFrameSet
  rw [Finset.card_map, Finset.card_map]

theorem qTwoChartHub_frameSet_mul (ε0 : Fin m ↪ Fin (n + 1))
    (π₁ π₂ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin m)) :
    qTwoFrameSet ε0 (π₁ * π₂) T = (qTwoFrameSet ε0 π₂ T).map π₁.toEmbedding := by
  unfold qTwoFrameSet
  calc (T.map ε0).map (π₁ * π₂).toEmbedding
      = (T.map ε0).map (π₂.toEmbedding.trans π₁.toEmbedding) := by
        rw [Equiv.Perm.mul_def, Equiv.trans_toEmbedding]
    _ = ((T.map ε0).map π₂.toEmbedding).map π₁.toEmbedding :=
        (Finset.map_map π₂.toEmbedding π₁.toEmbedding (T.map ε0)).symm

theorem qTwoChartHub_lifts_mul (S : QTwoChartSetting B Bs x L D J 𝒦 m n) {g₁ g₂ : G}
    {π₁ π₂ : Equiv.Perm (Fin (n + 1))} (h₁ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g₁ π₁)
    (h₂ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g₂ π₂) :
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (g₁ * g₂) (π₁ * π₂) := by
  unfold QTwoLiftsPerm at h₁ h₂ ⊢
  refine ⟨Subgroup.mul_mem _ h₁.1 h₂.1, Subgroup.mul_mem _ h₁.2.1 h₂.2.1, ?_⟩
  intro b
  have hρ : ((S.ρA (π₁ * π₂) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((S.ρA π₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      ((S.ρA π₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    rw [map_mul, Subgroup.coe_mul]
  rw [hρ, MulAut.mul_apply, h₁.2.2, h₂.2.2]
  group

theorem qTwoChartHub_lifts_inv (S : QTwoChartSetting B Bs x L D J 𝒦 m n) {g : G}
    {π : Equiv.Perm (Fin (n + 1))} (h : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π) :
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g⁻¹ π⁻¹ := by
  unfold QTwoLiftsPerm at h ⊢
  refine ⟨Subgroup.inv_mem _ h.1, Subgroup.inv_mem _ h.2.1, ?_⟩
  intro b
  have hπ : ((S.ρA π⁻¹ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))⁻¹ := by
    rw [map_inv, Subgroup.coe_inv]
  rw [hπ]
  let b' : ↥Bs := (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))⁻¹ b
  have hb' : (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b' : ↥Bs) = b := by
    dsimp [b']
    exact MulAut.apply_inv_self (↥Bs) _ b
  have hg := h.2.2 b'
  rw [hb'] at hg
  change (b' : G) = g⁻¹ * (b : G) * (g⁻¹)⁻¹
  rw [hg]
  group

theorem qTwoChartHub_blockOf_conj (ψ : Su F0 2 1 m →* G) (s g : G) (T : Finset (Fin m)) :
    (qTwoBlockOf ψ g T).map (MulAut.conj s).toMonoidHom = qTwoBlockOf ψ (s * g) T := by
  unfold qTwoBlockOf
  rw [Subgroup.map_map]
  congr 1
  ext u
  show s * (g * ψ u * g⁻¹) * s⁻¹ = (s * g) * ψ u * (s * g)⁻¹
  group

theorem qTwoChartHub_exists_frameSet (ε0 : Fin m ↪ Fin (n + 1)) {I : Finset (Fin (n + 1))}
    (hI : I.card ≤ m) :
    ∃ (π : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin m)),
      qTwoFrameSet ε0 π T = I ∧ T.card = I.card := by
  obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (n := I.card) (by simpa using hI)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq (T₀.map ε0) I
    (by rw [Finset.card_map, hT₀])
  exact ⟨π, T₀, hπ, hT₀⟩

theorem qTwoChartHub_exists_perm_of_embedding (ε0 ε : Fin m ↪ Fin (n + 1)) :
    ∃ π : Equiv.Perm (Fin (n + 1)), ∀ i : Fin m, π (ε0 i) = ε i := by
  exact Equiv.Perm.exists_extending_pair (ε0 : Fin m → Fin (n + 1))
    (ε : Fin m → Fin (n + 1)) ε0.injective ε.injective

theorem qTwoChartHub_exists_perm_pair {a b i j : Fin (n + 1)} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ π : Equiv.Perm (Fin (n + 1)), π a = i ∧ π b = j := by
  refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (by
      intro h
      exact hab (Eq.symm ((Equiv.swap a i).injective (by rw [← h, Equiv.swap_apply_left])))
      ) hij
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem qTwoChartHub_exists_blk (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (ψ : Su F0 2 1 m →* G) (ε0 : Fin m ↪ Fin (n + 1))
    (hunique : ∀ {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))} {T T' : Finset (Fin m)},
      QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π → QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π' →
      2 ≤ T.card → T.card ≤ 4 → T'.card = T.card →
      qTwoFrameSet ε0 π T = qTwoFrameSet ε0 π' T' → qTwoBlockOf ψ g T = qTwoBlockOf ψ g' T') :
    ∃ blk : Finset (Fin (n + 1)) → Subgroup G, qTwoChartHub_spec S ψ ε0 blk := by
  classical
  let P : Finset (Fin (n + 1)) → Prop := fun I =>
    ∃ (g : G) (π : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin m)),
      QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π ∧ 2 ≤ T.card ∧ T.card ≤ 4 ∧
        qTwoFrameSet ε0 π T = I
  refine ⟨fun I => if h : P I then
    qTwoBlockOf ψ h.choose h.choose_spec.choose_spec.choose else ⊥, ?_⟩
  intro g π T hg h2 h4
  have hP : P (qTwoFrameSet ε0 π T) := ⟨g, π, T, hg, h2, h4, rfl⟩
  show (if h : P (qTwoFrameSet ε0 π T) then
    qTwoBlockOf ψ h.choose h.choose_spec.choose_spec.choose else ⊥) = qTwoBlockOf ψ g T
  rw [dif_pos hP]
  obtain ⟨hg', h2', h4', hframe'⟩ := hP.choose_spec.choose_spec.choose_spec
  have hcard' : (hP.choose_spec.choose_spec.choose).card = T.card := by
    rw [← qTwoChartHub_card_frameSet ε0 hP.choose_spec.choose
        hP.choose_spec.choose_spec.choose,
      hframe', qTwoChartHub_card_frameSet ε0 π T]
  exact (hunique hg hg' h2 h4 hcard' hframe'.symm).symm

theorem qTwoChartHub_blk_le (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {blk : Finset (Fin (n + 1)) → Subgroup G} (hblk : qTwoChartHub_spec S ψ ε0 blk)
    {I : Finset (Fin (n + 1))} (h2 : 2 ≤ I.card) (h4 : I.card ≤ 4) : blk I ≤ QTwoH L 𝒦 := by
  have hIm : I.card ≤ m := by have h5 := S.hm; omega
  obtain ⟨π, T, hframe, hcardT⟩ := qTwoChartHub_exists_frameSet ε0 hIm
  obtain ⟨g, hg⟩ := hlifts π
  have h2' : 2 ≤ T.card := by rw [hcardT]; exact h2
  have h4' : T.card ≤ 4 := by rw [hcardT]; exact h4
  have hblkI : blk I = qTwoBlockOf ψ g T := by
    rw [← hframe]
    exact hblk hg h2' h4'
  rw [hblkI]
  unfold qTwoBlockOf
  rintro x ⟨u, -, rfl⟩
  show g * ψ u * g⁻¹ ∈ QTwoH L 𝒦
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.1
    (Subgroup.mem_sup_left (hψ.1 ▸ (MonoidHom.mem_range.mpr ⟨u, rfl⟩))))
    (Subgroup.inv_mem _ hg.1)

end CFSG.StandardType.QTwo

end
