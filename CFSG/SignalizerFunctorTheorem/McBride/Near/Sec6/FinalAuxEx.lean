module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxR0
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Khat
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAux618

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

section Ex

variable (h : Counterexample p A θ)

include h

theorem NT.mem_FN_self {a : G} (ha : NT A θ a) : a ∈ FN A θ a := by
  rw [mem_FN_iff]
  refine ⟨ha.mem, fun J hJ => ?_⟩
  have : a ∈ Subgroup.centralizer (θ a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (h.hyp.isFunctor.le_centralizer a ha.mem ha.ne_one hx)
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (lcal_le hJ)) this)

theorem NT.exists_FN_eq_sup
    {a : G} (ha : NT A θ a) :
    ∃ g ∈ FN A θ a, Subgroup.zpowers a ⊔ Subgroup.zpowers g = FN A θ a ∧
      Group.IsSolvable (thetaOf θ (FN A θ a)) ∧ FN A θ a ∈ signalizerFunctorEk p 2 A := by
  obtain ⟨J, hJ⟩ := ha.lcal_nonempty h
  have hFN := ha.FN_eq h hJ
  obtain ⟨g, hgN, hgc⟩ := ha.exists_noncentral h hJ
  have hgF : g ∈ FN A θ a := hFN ▸ hgN
  have hgA : g ∈ A := hgN.1
  have hac : a ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (h.hyp.isFunctor.le_centralizer a ha.mem ha.ne_one (lcal_le hJ hx))
  have hgz : g ∉ Subgroup.zpowers a := fun hz =>
    hgc (Subgroup.zpowers_le.mpr hac hz)
  have hg1 : g ≠ 1 := fun h1 => hgc (h1 ▸ one_mem _)
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers g := fun heq =>
    hgz (heq ▸ Subgroup.mem_zpowers g)
  have hline := sup_mem_E2_of_ne h (zpowers_mem_E1 h ha.mem ha.ne_one)
    (zpowers_mem_E1 h hgA hg1) hne
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers g ≤ FN A θ a :=
    sup_le (Subgroup.zpowers_le.mpr (ha.mem_FN_self h)) (Subgroup.zpowers_le.mpr hgF)
  have heq : FN A θ a = Subgroup.zpowers a ⊔ Subgroup.zpowers g :=
    eq_of_le_of_ne_top h hline (FN_le a) hle (ha.FN_ne_top h)
  refine ⟨g, hgF, heq.symm, ?_, heq ▸ hline⟩
  rw [heq]
  exact ha.isSolvable_of_mem_FN h hgF hJ hgc

theorem NT.eq_FN_of_isSolvable
    {a : G} (ha : NT A θ a) {Q : Subgroup G}
    (hQ : Q ∈ signalizerFunctorEk p 2 A) (haQ : a ∈ Q)
    (hsol : Group.IsSolvable (thetaOf θ Q)) : Q = FN A θ a := by
  obtain ⟨x, hxQ, hxa⟩ := exists_mem_not_mem_zpowers h hQ ha.mem
  have hx1 : x ≠ 1 := fun h1 => hxa (h1 ▸ one_mem _)
  have hQeq := sup_zpowers_eq_of_mem h hQ haQ ha.ne_one hxQ hxa
  have hxF : x ∈ FN A θ a := ha.mem_FN_of_isSolvable h (hQ.1 hxQ) hx1 (by rw [hQeq]; exact hsol)
  have hle : Q ≤ FN A θ a := by
    rw [← hQeq]
    exact sup_le (Subgroup.zpowers_le.mpr (ha.mem_FN_self h)) (Subgroup.zpowers_le.mpr hxF)
  obtain ⟨g, -, -, -, hFNE⟩ := ha.exists_FN_eq_sup h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hFNE.2, hQ.2])

theorem exists_not_mem_rSetN :
    ∃ E, E ∈ signalizerFunctorEk p 1 A ∧ E ∉ rSetN p A θ 1 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ x ∈ A, x ≠ 1 → NT A θ x := by
    intro x hx hx1
    have := (h.zpowers_mem_rSetN_one_iff).mp (hcon _ (zpowers_mem_E1 h hx hx1))
    exact ⟨this.1, this.2.1, this.2.2⟩
  obtain ⟨B, hB⟩ := h.rSetN_two_nonempty
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  obtain ⟨f, hfB, hf1⟩ : ∃ f ∈ B, f ≠ 1 := by
    obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
    exact ⟨f, hf, fun h1 => hf1 (Subtype.ext h1)⟩
  obtain ⟨l, hlB, hlf⟩ := exists_mem_not_mem_zpowers h hBE (hBA hfB)
  have hl1 : l ≠ 1 := fun h1 => hlf (h1 ▸ one_mem _)
  have hfn := hall f (hBA hfB) hf1
  have hln := hall l (hBA hlB) hl1
  obtain ⟨gf, -, -, hsolf, hQf⟩ := hfn.exists_FN_eq_sup h
  obtain ⟨gl, -, -, hsoll, hQl⟩ := hln.exists_FN_eq_sup h
  have hne : FN A θ f ≠ FN A θ l := by
    intro heq
    have hlF : l ∈ FN A θ f := heq ▸ hln.mem_FN_self h
    have hBle : B ≤ FN A θ f := by
      rw [← sup_zpowers_eq_of_mem h hBE hfB hf1 hlB hlf]
      exact sup_le (Subgroup.zpowers_le.mpr (hfn.mem_FN_self h)) (Subgroup.zpowers_le.mpr hlF)
    have hBeq : B = FN A θ f := Subgroup.eq_of_le_of_card_ge hBle (by rw [hQf.2, hBcard])
    exact hBns (hBeq ▸ hsolf)
  have hinf := inf_mem_E1_of_ne_E2 h hQf hQl hne
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ FN A θ f ⊓ FN A θ l, g ≠ 1 := by
    have hcard := hinf.2
    by_contra hcon'
    push Not at hcon'
    have : FN A θ f ⊓ FN A θ l = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon' x hx)
    rw [this, Subgroup.card_bot, pow_one] at hcard
    exact h.hyp.prime.one_lt.ne hcard
  have hgA : g ∈ A := FN_le f hg.1
  have hgn := hall g hgA hg1
  have e1 := hgn.eq_FN_of_isSolvable h hQf hg.1 hsolf
  have e2 := hgn.eq_FN_of_isSolvable h hQl hg.2 hsoll
  exact hne (e1.trans e2.symm)

theorem NT.inf_khat_eq_FN
    {a : G} (ha : NT A θ a) : A ⊓ khat (A ⊔ θ a) = FN A θ a := by
  ext x
  rw [Subgroup.mem_inf, mem_FN_iff]
  refine and_congr_right fun hxA => ?_
  rw [sup_comm A (θ a)]
  exact Nonsolv.L69.mem_khat_sup_iff h.hyp.elemAbelian.1
    (h.hyp.isFunctor.normalized a ha.mem ha.ne_one) (ha.sol_eq_bot h) (ha.lcal_nonempty h)
    (Subgroup.mem_sup_right hxA)

theorem eq_inf_khat
    {E : Subgroup G} (hE : E ∈ signalizerFunctorEk p 1 A)
    (hER : E ∉ rSetN p A θ 1) {f : G} (hf : f ∈ A) (hfE : f ∉ E) :
    E ⊔ Subgroup.zpowers f = A ⊓ khat (A ⊔ θ f) := by
  have hθ := h.hyp.nearFunctor
  have hf1 : f ≠ 1 := fun h1 => hfE (h1 ▸ one_mem _)
  have hfn : NT A θ f := by
    refine ⟨hf, hf1, fun hs => ?_⟩
    have hE₂ := zpowers_mem_E1 h hf hf1
    have hn₂ : Subgroup.zpowers f ∉ rSetN p A θ 1 := fun hh =>
      ((h.zpowers_mem_rSetN_one_iff).mp hh).2.2 hs
    have := eq_of_not_mem_rSetN h hE hE₂ hER hn₂
    exact hfE (this ▸ Subgroup.mem_zpowers f)
  rw [hfn.inf_khat_eq_FN h]
  obtain ⟨e, heA, he1, rfl, hes⟩ := exists_zpowers_of_not_mem h hE hER
  obtain ⟨g, -, -, -, hFNE⟩ := hfn.exists_FN_eq_sup h
  have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers f ≤ FN A θ f := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr (hfn.mem_FN_self h))
    rw [Subgroup.zpowers_le]
    refine hfn.mem_FN_of_isSolvable h heA he1 ?_
    have hle : thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e) ≤ θ e := by
      rw [← hθ.isFunctor.thetaOf_zpowers heA he1]
      exact thetaOf_anti le_sup_right
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hne : Subgroup.zpowers e ≠ Subgroup.zpowers f := fun heq =>
    hfE (heq ▸ Subgroup.mem_zpowers f)
  have hline := sup_mem_E2_of_ne h hE (zpowers_mem_E1 h hf hf1) hne
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hFNE.2, hline.2])

end Ex

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
