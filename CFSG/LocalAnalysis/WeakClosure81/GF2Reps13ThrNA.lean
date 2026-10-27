module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Finite X := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 (x : MulAut W) x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn]
  exact Odd.pow (hp.odd_of_ne_two hp2)

private theorem w16g_eq_of_sSup_eq_of_sSupIndep {α : Type*} [CompleteLattice α]
    {s S T : Set α} (hind : sSupIndep s) (hS : S ⊆ s) (hT : T ⊆ s)
    (hne : ∀ a ∈ s, a ≠ ⊥) (h : sSup S = sSup T) : S = T := by
  ext a
  constructor
  · intro haS
    by_contra haT
    have hd := hind.disjoint_sSup (hS haS) hT haT
    have hle : a ≤ sSup T := h ▸ le_sSup haS
    exact hne a (hS haS) (le_bot_iff.mp (disjoint_iff.mp hd ▸ le_inf le_rfl hle))
  · intro haT
    by_contra haS
    have hd := hind.disjoint_sSup (hT haT) hS haS
    have hle : a ≤ sSup S := h.symm ▸ le_sSup haT
    exact hne a (hT haT) (le_bot_iff.mp (disjoint_iff.mp hd ▸ le_inf le_rfl hle))

theorem s13_U1_abelian (h : HAb A X Q t p) {L : Subgroup (MulAut W)} (hLX : L ≤ X) :
    ∀ n ∈ X, ∀ w ∈ commSub ⊤ L, n w ∈ commSub ⊤ L := by
  have hp : p.Prime := by rcases h.hp with rfl | rfl <;> decide
  have hp2 : p ≠ 2 := by rcases h.hp with rfl | rfl <;> decide
  rw [commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe hLX]
  intro n hn
  exact stableUnder_iSup
    (fun U => stableUnder_iSup (fun hU => s13IsoComps_stable hU.1)) n hn

theorem s13_U3_abelian (h : HAb A X Q t p) {L : Subgroup (MulAut W)} (hLX : L ≤ X)
    (hcl : L = s13XSupp X (s13Supp X L)) :
    ∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
      L.map (MulAut.conj g).toMonoidHom = L := by
  intro g hgA hm
  have hp : p.Prime := by rcases h.hp with rfl | rfl <;> decide
  have hp2 : p ≠ 2 := by rcases h.hp with rfl | rfl <;> decide
  have hXodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 h.hXe
  have hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X := h.hXA g hgA
  have hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X := h.hXA g⁻¹ (A.inv_mem hgA)
  have hLgX : L.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro l ⟨l', hl', rfl⟩
    simpa [MulAut.conj_apply] using h.hXA g hgA l' (hLX hl')
  set S : Set (Subgroup W) := s13Supp X L
  set T : Set (Subgroup W) := (fun U : Subgroup W => U.map g.toMonoidHom) '' S
  have hSsub : S ⊆ s13IsoComps X := fun U hU => hU.1
  have hTsub : T ⊆ s13IsoComps X := by
    rintro U ⟨V, hV, rfl⟩
    exact map_mem_s13IsoComps hg hg' (hSsub hV)
  have hcomm : commSub ⊤ L = sSup S := by
    rw [commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe hLX]
    exact (sSup_eq_iSup).symm
  have hmapg : (commSub ⊤ L).map g.toMonoidHom = sSup T := by
    rw [CFSG.RankThree.S4Free.Stell.map_commSub g ⊤ L,
      Subgroup.map_top_of_surjective _ g.surjective,
      commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe hLgX,
      ← sSup_eq_iSup]
    exact congrArg sSup (s13Supp_conj hg hg')
  have hsup : sSup S = sSup T := by
    rw [← hcomm, ← hmapg, hm]
  have hST : S = T := w16g_eq_of_sSup_eq_of_sSupIndep
    (s13IsoComps_sSupIndep h.hW hXodd) hSsub hTsub
    (fun U hU => (s13IsoComps_le_commSub h.hW hXodd hU).1) hsup
  have hsupp : s13Supp X (L.map (MulAut.conj g).toMonoidHom) = s13Supp X L := by
    rw [s13Supp_conj hg hg']
    exact hST.symm
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    have h' := (le_s13XSupp_iff h.hW hp hp2 h.hXe hLgX
      (B := s13Supp X L)).mpr (le_of_eq hsupp)
    rwa [← hcl] at h'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact le_of_eq (Subgroup.card_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm

end CFSG.LocalAnalysis.WeakClosure81
