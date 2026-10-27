module

public import CFSG.Sporadic.Co2M22Inputs
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.TwoGen
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Co2Inv

public section

namespace CFSG.Sporadic.Co2Heavy

open CFSG.Sporadic.Co2Inv CFSG.Blueprint

section M22Helpers

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

theorem m22_rowCheck_wf {pt : Array UInt32} {levels : Array Level} {X : Array ℕ}
    (h : rowCheck levels pt X = true) : wfRows X = true := by
  simp only [rowCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem m22_exists_elt
    {X : Array ℕ}
    (h : rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable X = true) :
    ∃ x : NativeSporadic.Co2, x.val.val = rowsMatrix 22 X := by
  simp only [rowCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, hinv⟩, himg⟩, hsift⟩ := h
  have himg' : ∀ i < 2300, co2PackedVecs[(rowPerm co2PosTable X)[i]!]! =
      vecMulN 22 (transposeRows 22 X) co2PackedVecs[i]! := fun i hi => by
    simpa using allLt_spec himg hi
  have hrep := (rep_permOfArr hinv).1
  have hmem : permOfArr 2300 (rowPerm co2PosTable X) ∈ co2P := by
    rw [← co2Q_originalSubgroup]
    exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
      hrep).1 hsift
  refine ⟨co2PermEquiv.symm ⟨permOfArr 2300 (rowPerm co2PosTable X), hmem⟩, ?_⟩
  apply matrix_eq_of_vecs
  intro i
  have hp := co2Vec_permEquiv (co2PermEquiv.symm ⟨permOfArr 2300 (rowPerm co2PosTable X), hmem⟩) i
  have he : (co2PermEquiv (co2PermEquiv.symm
      ⟨permOfArr 2300 (rowPerm co2PosTable X), hmem⟩) : Equiv.Perm (Fin 2300)) =
      permOfArr 2300 (rowPerm co2PosTable X) := by
    rw [MulEquiv.apply_symm_apply]
  rw [he] at hp
  rw [← hp, co2Vec_eq i.2, rowsMatrix_mulVec, ← himg' i i.2, hrep i,
    ← co2Vec_eq (permOfArr 2300 (rowPerm co2PosTable X) i).2]

theorem m22_val_inv {x : NativeSporadic.Co2} {X Xi : Array ℕ} (hx : x.val.val = rowsMatrix 22 X)
    (h : mulRows 22 X Xi = idRows 22) : (x⁻¹).val.val = rowsMatrix 22 Xi := by
  apply val_val_inv
  rw [hx, ← rowsMatrix_mulRows, h, rowsMatrix_idRows]

section Words

variable {a b : NativeSporadic.Co2} {A B Ai Bi : Array ℕ}

theorem m22_letter_val (ha : a.val.val = rowsMatrix 22 A) (hb : b.val.val = rowsMatrix 22 B)
    (hai : (a⁻¹).val.val = rowsMatrix 22 Ai) (hbi : (b⁻¹).val.val = rowsMatrix 22 Bi)
    (l : ℕ × Bool) :
    (if l.2 then CFSG.Sporadic.Bridge.TwoGen.img2 a b l.1
      else (CFSG.Sporadic.Bridge.TwoGen.img2 a b l.1)⁻¹).val.val =
      rowsMatrix 22 (if l.1 = 0 then (if l.2 then A else Ai) else (if l.2 then B else Bi)) := by
  obtain ⟨i, s⟩ := l
  by_cases hi : i = 0 <;> cases s <;>
    simp [CFSG.Sporadic.Bridge.TwoGen.img2, hi, ha, hb, hai, hbi]

theorem m22_word_val (ha : a.val.val = rowsMatrix 22 A) (hb : b.val.val = rowsMatrix 22 B)
    (hai : (a⁻¹).val.val = rowsMatrix 22 Ai) (hbi : (b⁻¹).val.val = rowsMatrix 22 Bi)
    (w : List (ℕ × Bool)) :
    ∀ (g : NativeSporadic.Co2) (G : Array ℕ), g.val.val = rowsMatrix 22 G →
      (g * CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 a b) w).val.val =
        rowsMatrix 22 (w.foldl (fun acc l => mulRows 22 acc
          (if l.1 = 0 then (if l.2 then A else Ai) else (if l.2 then B else Bi))) G) := by
  induction w with
  | nil =>
    intro g G hg
    simpa [CFSG.Sporadic.Bridge.wordProd] using hg
  | cons l w ih =>
    intro g G hg
    have e : g * CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 a b) (l :: w) =
        (g * (if l.2 then CFSG.Sporadic.Bridge.TwoGen.img2 a b l.1
          else (CFSG.Sporadic.Bridge.TwoGen.img2 a b l.1)⁻¹)) *
          CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 a b) w := by
      simp only [CFSG.Sporadic.Bridge.wordProd, List.map_cons, List.prod_cons, mul_assoc]
    rw [e, List.foldl_cons]
    refine ih _ _ ?_
    rw [val_val_mul, hg, m22_letter_val ha hb hai hbi l, rowsMatrix_mulRows]

theorem m22_wordRows_val (ha : a.val.val = rowsMatrix 22 A) (hb : b.val.val = rowsMatrix 22 B)
    (hai : (a⁻¹).val.val = rowsMatrix 22 Ai) (hbi : (b⁻¹).val.val = rowsMatrix 22 Bi)
    (w : List (ℕ × Bool)) :
    (CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 a b) w).val.val =
      rowsMatrix 22 (wordRows A B Ai Bi w) := by
  have h := m22_word_val ha hb hai hbi w 1 (idRows 22)
    (by rw [val_val_one, rowsMatrix_idRows])
  rw [one_mul] at h
  exact h

end Words

private theorem m22_presentation_eq :
    TauCeti.SporadicName.M22.presentation = TauCeti.Sporadic.m22Presentation := rfl

theorem m22_generatorCount : TauCeti.SporadicName.M22.presentation.generatorCount = 2 := by
  rw [m22_presentation_eq]
  exact CFSG.Sporadic.Bridge.M22.generatorCount_eq

theorem m22_closure_presGen :
    Subgroup.closure ({CFSG.Sporadic.Bridge.presGen TauCeti.SporadicName.M22.presentation 0,
      CFSG.Sporadic.Bridge.presGen TauCeti.SporadicName.M22.presentation 1} :
        Set TauCeti.SporadicName.M22.Group) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of
    TauCeti.SporadicName.M22.presentation.relatorSet, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  apply Subgroup.subset_closure
  have hi : i.val < 2 := m22_generatorCount ▸ i.2
  have hgen : CFSG.Sporadic.Bridge.presGen TauCeti.SporadicName.M22.presentation i.val =
      PresentedGroup.of i := by
    rw [CFSG.Sporadic.Bridge.presGen, dite_eq_left i.2]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
  · left
    rw [← hgen, h]
  · right
    rw [← hgen, h]

theorem m22_mem_normalizer {G : Type*} [Group G] [Finite G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro s hs
    exact Subgroup.subset_closure (h s hs)
  exact Subgroup.eq_of_le_of_card_ge hmap
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem m22_injective_of_ne_one {G P : Type*} [Group G] [Group P] [IsSimpleGroup P]
    (φ : P →* G) {x : P} (hx : φ x ≠ 1) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h0 | h0
  · exact h0
  · exact absurd (MonoidHom.mem_ker.1 (h0 ▸ Subgroup.mem_top x)) hx

theorem m22_range_facts {G P : Type*} [Group G] [Group P] [IsSimpleGroup P] {n : ℕ}
    (hn : Nat.card P = n) (hnp : ¬ n.Prime) {φ : P →* G} (hinj : Function.Injective φ) :
    IsSimpleGroup φ.range ∧ ¬ IsMulCommutative φ.range ∧ Nat.card φ.range = n := by
  have e := MonoidHom.ofInjective hinj
  have hs : IsSimpleGroup φ.range := e.symm.isSimpleGroup
  have hc : Nat.card φ.range = n := by rw [← Nat.card_congr e.toEquiv, hn]
  refine ⟨hs, fun hcomm => ?_, hc⟩
  have hp := Group.is_simple_iff_prime_card.1 hs
  rw [hc] at hp
  exact hnp hp

theorem m22_range_le {G P : Type*} [Group G] [Group P] (φ : P →* G) {T : Set P}
    (hT : Subgroup.closure T = ⊤) {N : Subgroup G} (h : ∀ t ∈ T, φ t ∈ N) : φ.range ≤ N := by
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure T := by
    rw [hT]
    exact Subgroup.mem_top g
  exact (Subgroup.closure_le (N.comap φ)).2 h hg

end M22Helpers

end CFSG.Sporadic.Co2Heavy
