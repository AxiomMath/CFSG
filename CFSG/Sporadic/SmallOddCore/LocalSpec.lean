module

public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

noncomputable abbrev genOf (n : ℕ) (gs : List Table) : Subgroup (Equiv.Perm (Fin n)) :=
  closure (tp n '' {x | x ∈ gs.toArray})

theorem tp_mem_genOf {gs : List Table} {g : Table} (hg : g ∈ gs) : tp n g ∈ genOf n gs :=
  subset_closure ⟨g, by simpa using hg, rfl⟩

theorem rep_wordTbl (hn : n < 2 ^ 32) {gs : List Table} (hg : ∀ g ∈ gs, permOK n g = true)
    (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) :
    ∃ x ∈ genOf n gs, Rep n (wordTbl n gs w) x := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) → ∀ (acc : Table)
      (a : Equiv.Perm (Fin n)), a ∈ genOf n gs → Rep n acc a →
      ∃ x ∈ genOf n gs, Rep n (w.foldl (fun acc l => compT n acc (gs.getD (l - 1) (idT n)))
        acc) x := by
    intro w
    induction w with
    | nil => intro _ acc a ha hrep; exact ⟨a, ha, hrep⟩
    | cons l w ih =>
      intro hw acc a ha hrep
      rw [List.foldl_cons]
      obtain ⟨hl1, hl2⟩ := hw l List.mem_cons_self
      have hmem : gs.getD (l - 1) (idT n) ∈ gs := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) _ _
        (mul_mem ha (tp_mem_genOf hmem)) (Rep.compT hrep (rep_tp (hg _ hmem)))
  exact key w hw (idT n) 1 (one_mem _) (Rep.idT hn)

theorem tp_wordTbl_mem (hn : n < 2 ^ 32) {gs : List Table} (hg : ∀ g ∈ gs, permOK n g = true)
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) (hp : permOK n (wordTbl n gs w) = true) :
    tp n (wordTbl n gs w) ∈ genOf n gs := by
  obtain ⟨x, hx, hrep⟩ := rep_wordTbl hn hg w hw
  rwa [rep_unique (rep_tp hp) hrep]

theorem enumOK_spec (hn : n < 2 ^ 32) {cap m : ℕ} {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (h : enumOK n cap m gs = true) :
    Nat.card (genOf n gs) = m ∧
      (∀ k < (mulClosureH n gs.toArray cap).1.size,
        Rep n (mulClosureH n gs.toArray cap).1[k]!
          (tablePerm n (mulClosureH n gs.toArray cap).1[k]!) ∧
        tablePerm n (mulClosureH n gs.toArray cap).1[k]! ∈ genOf n gs) ∧
      (∀ x ∈ genOf n gs, ∃ k < (mulClosureH n gs.toArray cap).1.size,
        Rep n (mulClosureH n gs.toArray cap).1[k]! x) ∧
      hkeysDistinct n (mulClosureH n gs.toArray cap).1.toList = true := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hinv, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  obtain ⟨hrep, hcov, hcard⟩ :=
    enum_spec hn (A := gs.toArray) (fun x hx => hg x (by simpa using hx))
    (fun x hx => hinv x (by simpa using hx)) htree hclosed hdist
  exact ⟨hcard.trans hsize, hrep, hcov, hdist⟩

theorem normOK_spec (hn : n < 2 ^ 32) {cap m : ℕ} {gs cs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (hK : enumOK n cap m gs = true)
    (hc : ∀ c ∈ cs, permOK n c = true ∧ invOK n c (invT n c) = true)
    (h : normOK n cap gs cs = true) :
    genOf n cs ≤ normalizer (genOf n gs : Set (Equiv.Perm (Fin n))) := by
  obtain ⟨-, hrep, hcov, -⟩ := enumOK_spec hn hg hK
  set E := (mulClosureH n gs.toArray cap).1
  simp only [normOK, List.all_eq_true, Array.all_eq_true] at h
  have hle : ∀ c ∈ cs, (genOf n gs).map (MulAut.conj (tp n c)).toMonoidHom ≤ genOf n gs := by
    rintro c hcm _ ⟨k, hk, rfl⟩
    obtain ⟨j, hj, hjrep⟩ := hcov k hk
    have hc' := rep_tp (hc c hcm).1
    have h1 := h c hcm j hj
    rw [← getElem!_pos E j hj] at h1
    obtain ⟨j', hj', hj'eq⟩ := memT_spec (fun k hk => (hrep k hk).1)
      (rep_conjT hc' (rep_invT hc' (hc c hcm).2) hjrep) h1
    show tp n c * k * (tp n c)⁻¹ ∈ genOf n gs
    rw [hj'eq]
    exact (hrep j' hj').2
  rw [closure_le]
  rintro _ ⟨c, hcm, rfl⟩
  have hcm' : c ∈ cs := by simpa using hcm
  have heq : (genOf n gs).map (MulAut.conj (tp n c)).toMonoidHom = genOf n gs :=
    Subgroup.eq_of_le_of_card_ge (hle c hcm')
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (tp n c)).injective])
  show tp n c ∈ normalizer _
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle c hcm' ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj (tp n c)).injective hyx
    rwa [← this]

theorem centCount_spec (hn : n < 2 ^ 32) {cap mC : ℕ} {cs gs : List Table}
    (hc : ∀ c ∈ cs, permOK n c = true) (hC : enumOK n cap mC cs = true)
    (hg : ∀ g ∈ gs, permOK n g = true) :
    Nat.card ↥(genOf n cs ⊓ centralizer (genOf n gs : Set (Equiv.Perm (Fin n)))) =
      centCount n cap cs gs := by
  classical
  obtain ⟨-, hrep, hcov, hdist⟩ := enumOK_spec hn hc hC
  set E := (mulClosureH n cs.toArray cap).1
  have hrepL := forall₂_tablePerm (fun k hk => (hrep k hk).1)
  have hnodup := nodup_of_hkeysDistinct hrepL hdist
  have hmemL : ∀ g, g ∈ E.toList.map (tablePerm n) ↔ g ∈ genOf n cs := by
    intro g
    constructor
    · intro hg'
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm (fun k hk => (hrep k hk).1) hg'
      exact (hrep k hk).2
    · intro hg'
      obtain ⟨k, hk, hkrep⟩ := hcov g hg'
      refine List.mem_map.mpr ⟨E[k]!, ?_, tablePerm_eq hkrep⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  have hcount := card_subtype_eq_countP (genOf n cs) (E.toList.map (tablePerm n)) hnodup hmemL
    (fun y => ∀ g ∈ gs, y * tp n g = tp n g * y)
  have hcongr : Nat.card {x : genOf n cs // ∀ g ∈ gs, (x : Equiv.Perm (Fin n)) * tp n g =
      tp n g * x} =
        Nat.card ↥(genOf n cs ⊓ centralizer (genOf n gs : Set (Equiv.Perm (Fin n)))) := by
    have hcent : ∀ y : Equiv.Perm (Fin n), y ∈ centralizer (genOf n gs : Set (Equiv.Perm (Fin n))) ↔
        ∀ g ∈ gs, y * tp n g = tp n g * y := by
      intro y
      rw [centralizer_closure, mem_centralizer_iff]
      constructor
      · intro h g hgm
        exact (h _ ⟨g, by simpa using hgm, rfl⟩).symm
      · rintro h _ ⟨g, hgm, rfl⟩
        exact (h g (by simpa using hgm)).symm
    refine Nat.card_congr ⟨fun x => ⟨x.1, mem_inf.mpr ⟨x.1.2, (hcent _).2 x.2⟩⟩,
      fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, (hcent _).1 (mem_inf.mp x.2).2⟩, fun _ => rfl,
      fun _ => rfl⟩
  rw [← hcongr, hcount, centCount, List.countP_map]
  apply List.countP_congr
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have hk' := (hrep k hk).1
  rw [getElem!_pos E k hk] at hk'
  simp only [Function.comp_apply, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro h g hgm
    exact (commTT_iff hk' (rep_tp (hg g hgm))).2 (h g hgm)
  · intro h g hgm
    exact (commTT_iff hk' (rep_tp (hg g hgm))).1 (h g hgm)

theorem isSimpleGroup_of_cover {M : Type*} [Group M] {D : Subgroup M} (hD : D ≠ ⊥)
    (reps : List M)
    (hcover : ∀ x ∈ D, x = 1 ∨ ∃ r ∈ reps, ∃ c ∈ D, x = c * r * c⁻¹)
    (hgen : ∀ r ∈ reps, D ≤ closure (conjClass D r)) : IsSimpleGroup ↥D := by
  have hnt : Nontrivial ↥D := by
    rw [nontrivial_iff_ne_bot]
    exact hD
  refine ⟨fun N hN => ?_⟩
  by_cases hNb : N = ⊥
  · exact Or.inl hNb
  · right
    obtain ⟨⟨x, hxN⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
    rcases hcover x x.2 with h1 | ⟨r, hr, c, hc, hxr⟩
    · exact absurd (Subtype.ext (Subtype.ext h1)) hx1
    ·
      set N' := N.map D.subtype
      have hN'n : ∀ c ∈ D, ∀ y ∈ N', c * y * c⁻¹ ∈ N' := by
        intro c hc y hy
        obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
        exact mem_map.mpr ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, hN.conj_mem _ hy' _, by simp⟩
      have hxN' : (x : M) ∈ N' := mem_map.mpr ⟨x, hxN, rfl⟩
      have hrN' : r ∈ N' := by
        have := hN'n c⁻¹ (D.inv_mem hc) _ hxN'
        rwa [hxr, show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group] at this
      have hcl : conjClass D r ⊆ N' := by
        rintro _ ⟨g, hg, rfl⟩
        exact hN'n g hg r hrN'
      have hDN : D ≤ N' := (hgen r hr).trans ((closure_le N').mpr hcl)
      rw [eq_top_iff]
      intro y _
      obtain ⟨y', hy', hyy'⟩ := mem_map.mp (hDN y.2)
      rwa [show y' = y from Subtype.ext hyy'] at hy'

end CFSG.Sporadic.SmallOddCore
