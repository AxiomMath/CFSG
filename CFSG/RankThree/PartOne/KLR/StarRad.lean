module

public import CFSG.RankThree.PartOne.KLR.B2Twist
public import CFSG.RankThree.PartOne.KE.CTMain

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

theorem smul_dualRoot_mem_parabolic {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w u : WeylGroup ReeTag.F4.tag)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    {J : Finset (Fin ReeTag.F4.tag.rank)}
    (hu : (fun α => u • α) '' S =
      parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank))) :
    (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
      parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) := by
  rw [← hu] at hγ ⊢
  obtain ⟨β, hβ, rfl⟩ := hγ
  have hβr := hS β hβ
  refine ⟨w • ReeTag.F4.dualRoot β, (hst β hβr).2 hβ, ?_⟩
  show u • (w • ReeTag.F4.dualRoot β) = _
  rw [ReeTag.dualRoot_smul u hβr, mul_smul, mul_smul, inv_smul_smul]

omit [CharP L 2] in
theorem rootSpan_parabolicRoots_empty :
    rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      ((∅ : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) = ⊥ := by
  have h : parabolicRoots ReeTag.F4.tag
      ((∅ : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)) = ∅ := by
    ext γ
    simp only [parabolicRoots, Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true,
      forall_const, Set.mem_ofPred_eq, iff_false]
    rintro ⟨hγ, hz⟩
    exact IsRoot.ne_zero hγ (funext hz)
  rw [h]
  simp [rootSpan]

theorem noSolvableRadical_parabolic_fixed [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w') {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (J : Set (Fin ReeTag.F4.tag.rank))) :
    NoSolvableRadical (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n') := by
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · rw [rootSpan_parabolicRoots_empty, bot_inf_eq]
    exact noSolvableRadical_bot
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact noSolvableRadical_A1Pair D ha hK a1Pair_zero_two hn' hperm hstab
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact noSolvableRadical_A1Pair D ha hK a1Pair_zero_three hn' hperm hstab
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact noSolvableRadical_A1Pair D ha hK a1Pair_one_three hn' hperm hstab
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hstab ⊢
    rw [← B2Q_eq_rootSpan]
    exact noSolvableRadical_B2 D ha hK hperm hstab

theorem starRadFree [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    NoSolvableRadical (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp (by omega) hbp hw hβ
  have hFN : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hNad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L u
  have hnad : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w
  have hn'ad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹ ∈
      adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hNad hnad) (inv_mem (Fext_mem D.F hNad))
  have hperm : PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹)
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have key := noSolvableRadical_parabolic_fixed D ha hK hn'ad hperm hJ
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ)
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ] at hmap
  refine noSolvableRadical_of_map
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective ?_
  rw [hmap]
  exact key

end CFSG.RankThree.PartOne.KLR
