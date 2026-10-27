module

public import CFSG.RankThree.PartOne.KLR.FrameRoots
public import CFSG.RankThree.PartOne.KLR.Embedding
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] def reeTuple (a : ℕ) (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    Fin ReeTag.F4.tag.rank → Lˣ :=
  fun k => b (ReeTag.F4.perm k) ^ ReeTag.F4.relationExponent a (ReeTag.F4.perm k)

omit [CharP L 2] in
theorem xUnit_inj_F4 {i : Fin ReeTag.F4.tag.rank} {c c' : L}
    (e : xUnit ReeTag.F4.tag L i c = xUnit ReeTag.F4.tag L i c') : c = c' := by
  rw [← pinnedX_single, ← pinnedX_single] at e
  exact pinnedX_injective ReeTag.F4.tag L _ e

theorem IsReeFrob.map_torusGroup (hF : IsReeFrob a F) {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ torusGroup ReeTag.F4.tag L) :
    ∃ hadj : h ∈ adjointGroup ReeTag.F4.tag L,
      ((F ⟨h, hadj⟩ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        torusGroup ReeTag.F4.tag L := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    refine ⟨torusElt_mem_adjointGroup i u, ?_⟩
    have h1 : (⟨torusElt ReeTag.F4.tag L i u, torusElt_mem_adjointGroup i u⟩ :
        adjointGroup ReeTag.F4.tag L) = torusElement ReeTag.F4.tag L i u := rfl
    rw [h1, hF.map_torusElement i u]
    exact Subgroup.subset_closure ⟨(ReeTag.F4.perm i, u ^ ReeTag.F4.relationExponent a i), rfl⟩
  | one =>
    refine ⟨one_mem _, ?_⟩
    have h1 : (⟨1, one_mem _⟩ : adjointGroup ReeTag.F4.tag L) = 1 := rfl
    rw [h1, map_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨hxa, hx⟩ := hx
    obtain ⟨hya, hy⟩ := hy
    refine ⟨mul_mem hxa hya, ?_⟩
    have h1 : (⟨x * y, mul_mem hxa hya⟩ : adjointGroup ReeTag.F4.tag L) = ⟨x, hxa⟩ * ⟨y, hya⟩ :=
      rfl
    rw [h1, map_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    obtain ⟨hxa, hx⟩ := hx
    refine ⟨inv_mem hxa, ?_⟩
    have h1 : (⟨x⁻¹, inv_mem hxa⟩ : adjointGroup ReeTag.F4.tag L) = ⟨x, hxa⟩⁻¹ := rfl
    rw [h1, map_inv]
    exact inv_mem hx

theorem IsReeFrob.fext_rootDiagUnit [IsAlgClosed L] (hF : IsReeFrob a F)
    (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    Fext F (rootDiagUnit ReeTag.F4.tag b) = rootDiagUnit ReeTag.F4.tag (reeTuple a b) := by
  have hbH : rootDiagUnit ReeTag.F4.tag b ∈ torusGroup ReeTag.F4.tag L :=
    rootDiagUnit_mem_torusGroup b
  obtain ⟨hadj, hFH⟩ := hF.map_torusGroup hbH
  rw [Fext_of_mem F hadj]
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hFH
  rw [hb']
  congr 1
  funext k
  set j := ReeTag.F4.perm k with hj
  have hjk : ReeTag.F4.perm j = k := by rw [hj]; exact ReeTag.perm_perm _ _
  have h1 : (⟨rootDiagUnit ReeTag.F4.tag b, hadj⟩ : adjointGroup ReeTag.F4.tag L) *
      xElement j 1 * (⟨rootDiagUnit ReeTag.F4.tag b, hadj⟩ : adjointGroup ReeTag.F4.tag L)⁻¹ =
        xElement j ((b j : Lˣ) : L) := by
    refine Subtype.ext ?_
    have := (root_diagonal_conjugation ReeTag.F4.tag L b).1 j 1
    rw [mul_one] at this
    exact this
  have h2 := congrArg F h1
  rw [map_mul, map_mul, map_inv, (hF j 1).1, (hF j _).1, one_pow, hjk] at h2
  have h3 := congrArg (fun z : adjointGroup ReeTag.F4.tag L => (z : ModGL ReeTag.F4.tag L)) h2
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h3
  rw [hb'] at h3
  have h4 := (root_diagonal_conjugation ReeTag.F4.tag L b').1 k 1
  rw [mul_one] at h4
  have h5 : xUnit ReeTag.F4.tag L k ((b' k : Lˣ) : L) =
      xUnit ReeTag.F4.tag L k (((b j : Lˣ) : L) ^ ReeTag.F4.relationExponent a j) :=
    h4.symm.trans h3
  have h6 := xUnit_inj_F4 h5
  refine Units.ext ?_
  rw [h6, reeTuple, Units.val_pow_eq_pow_val]

theorem rootDiagUnit_mem_twistedFixed_canonicalRep_iff [IsAlgClosed L] (hF : IsReeFrob a F)
    (w : WeylGroup ReeTag.F4.tag) (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    rootDiagUnit ReeTag.F4.tag b ∈
        twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ↔
      ∀ v : Fin ReeTag.F4.tag.rank → ℤ,
        rootChar b (w • v) = rootChar (reeTuple a b) v := by
  have hadj : rootDiagUnit ReeTag.F4.tag b ∈ adjointGroup ReeTag.F4.tag L :=
    torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup b)
  rw [mem_twistedFixed, hF.fext_rootDiagUnit b, ← rootDiagUnit_eq_conj_canonicalRep_iff b
    (reeTuple a b) w]
  constructor
  · exact fun h => h.2.symm
  · exact fun h => ⟨hadj, h.symm⟩

end CFSG.RankThree.PartOne.KLR
