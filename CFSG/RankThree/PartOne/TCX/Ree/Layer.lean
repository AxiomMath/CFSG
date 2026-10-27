module

public import CFSG.RankThree.PartOne.TCX.Ree.Tail
public import CFSG.RankThree.PartOne.TCX.Ree.LayerFacts
public import CFSG.RankThree.PartOne.TCX.Ree.A1Layer
public import CFSG.RankThree.PartOne.TCX.Ree.B2Layer
public import CFSG.RankThree.PartOne.TCX.Ree.Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.StarRad

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.TCX
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

structure IsReeShintani {C : Type} [Group C] {L : Type} [Field L] (p : ℕ)
    (θ : C →* ModGL ReeTag.F4.tag L) (F₀ F : MulAut (adjointGroup ReeTag.F4.tag L))
    (α₀ : MulAut C) : Prop where
  iter : F = F₀ ^ p
  inj : Function.Injective θ
  mem : ∀ y, θ y ∈ adjointGroup ReeTag.F4.tag L
  actor : ∀ y, θ (α₀ y) = Fext F₀ (θ y)
  ordα : α₀ ^ p = 1
  fix : ∀ y, Fext F (θ y) = θ y
  range : ∀ u ∈ adjointGroup ReeTag.F4.tag L, Fext F u = u → u ∈ θ.range

section Facts

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime]
  [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a₀ a : ℕ} {L : Type} [Field L]
  [Algebra K₀ L] [Algebra K L] [CharP L 2] [IsAlgClosed L]
  (D₀ : ReeFrameData K₀ L a₀) (D : ReeFrameData K L a) {p : ℕ}

theorem ree_layerFacts_A1 (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    {Sg : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hS : ∀ γ ∈ Sg, IsRoot ReeTag.F4.tag γ)
    {u : WeylGroup ReeTag.F4.tag} {i j : Fin ReeTag.F4.tag.rank} (hA : A1Pair i j)
    (hΦ : (fun α => u • α) '' Sg = parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    {n N : ModGL ReeTag.F4.tag L} (hn : n ∈ adjointGroup ReeTag.F4.tag L)
    (hN : N ∈ adjointGroup ReeTag.F4.tag L) {w₀ w₁ : WeylGroup ReeTag.F4.tag}
    (hperm₀ : PermAct (conjTwist D₀.F u n) (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstab₀ : ∀ γ ∈ parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)),
      (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    (hpermK : PermAct (conjTwist D.F u N) (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstabK : ∀ γ ∈ parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)),
      (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    (hPP : twistedFixed D₀.F n ≤ twistedFixed D.F N) :
    LayerFacts p (rootSpan ReeTag.F4.tag L Sg) (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D.F N)
      (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D₀.F n) := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK₀2 : CharP K₀ 2 := ‹CharP K₀ ReeTag.F4.prime›
  have hPP' : rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D₀.F n ≤
      rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D.F N := inf_le_inf_left _ hPP
  have hnK : conjTwist D.F u N ∈ adjointGroup ReeTag.F4.tag L := conjTwist_mem hN u
  have hnK₀ : conjTwist D₀.F u n ∈ adjointGroup ReeTag.F4.tag L := conjTwist_mem hn u
  have hKcard : Nat.card K = 2 ^ (p * (2 * a₀ + 1)) := by rw [hK, hKK]
  have hf₀ : 1 ≤ 2 * a₀ + 1 := by omega
  obtain ⟨⟨e⟩, hc⟩ := a1_level D hA hK hnK hpermK hstabK
  obtain ⟨⟨e₀⟩, -⟩ := a1_level D₀ hA hK₀ hnK₀ hperm₀ hstab₀
  rw [← hΦ] at e e₀ hc
  obtain ⟨eK⟩ := transport_iso u hS N e
  obtain ⟨e₀'⟩ := transport_iso u hS n e₀
  exact LayerFacts.of_sl2 hp5 hf₀ hKcard hK₀ hPP' eK e₀' (transport_cent u hS N hc)

theorem ree_layerFacts_B2 (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    {Sg : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hS : ∀ γ ∈ Sg, IsRoot ReeTag.F4.tag γ)
    {u : WeylGroup ReeTag.F4.tag}
    (hΦ : (fun α => u • α) '' Sg = parabolicRoots ReeTag.F4.tag f4B2Support)
    {n N : ModGL ReeTag.F4.tag L} {w₀ w₁ : WeylGroup ReeTag.F4.tag}
    (hperm₀ : PermAct (conjTwist D₀.F u n) (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstab₀ : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag f4B2Support)
    (hpermK : PermAct (conjTwist D.F u N) (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstabK : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag f4B2Support)
    (hPP : twistedFixed D₀.F n ≤ twistedFixed D.F N) :
    LayerFacts p (rootSpan ReeTag.F4.tag L Sg) (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D.F N)
      (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D₀.F n) := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK₀2 : CharP K₀ 2 := ‹CharP K₀ ReeTag.F4.prime›
  have hPP' : rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D₀.F n ≤
      rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D.F N := inf_le_inf_left _ hPP
  have hlt : Nat.card K₀ < Nat.card K := by
    rw [hK₀, hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  have hf₀ : 1 ≤ 2 * a₀ + 1 := by omega
  have ha : 1 ≤ a := by nlinarith
  obtain ⟨⟨e⟩, hc⟩ := b2_level D hK hpermK hstabK
  obtain ⟨⟨e₀⟩, -⟩ := b2_level D₀ hK₀ hperm₀ hstab₀
  rw [← hΦ] at e e₀ hc
  obtain ⟨eK⟩ := transport_iso u hS N e
  obtain ⟨e₀'⟩ := transport_iso u hS n e₀
  exact LayerFacts.of_sz hf₀ ha hK hK₀ hKK.symm hlt hPP' eK e₀'
    (transport_cent u hS N (hc ha))

theorem ree_layerFacts (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    {Sg : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hS : ∀ γ ∈ Sg, IsRoot ReeTag.F4.tag γ)
    {u : WeylGroup ReeTag.F4.tag} {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hJne : J ≠ ∅)
    (hΦ : (fun α => u • α) '' Sg = parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    {n N : ModGL ReeTag.F4.tag L} (hn : n ∈ adjointGroup ReeTag.F4.tag L)
    (hN : N ∈ adjointGroup ReeTag.F4.tag L) {w₀ w₁ : WeylGroup ReeTag.F4.tag}
    (hperm₀ : PermAct (conjTwist D₀.F u n) (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstab₀ : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      (u * w₀ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    (hpermK : PermAct (conjTwist D.F u N) (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹))
    (hstabK : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      (u * w₁ * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    (hPP : twistedFixed D₀.F n ≤ twistedFixed D.F N) :
    LayerFacts p (rootSpan ReeTag.F4.tag L Sg) (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D.F N)
      (rootSpan ReeTag.F4.tag L Sg ⊓ twistedFixed D₀.F n) := by
  classical
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · exact absurd rfl hJne
  · have hJ' : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ'
    exact ree_layerFacts_A1 D₀ D hp5 hK₀ hK hKK hS a1Pair_zero_two hΦ hn hN hperm₀ hstab₀ hpermK
      hstabK hPP
  · have hJ' : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ'
    exact ree_layerFacts_A1 D₀ D hp5 hK₀ hK hKK hS a1Pair_zero_three hΦ hn hN hperm₀ hstab₀ hpermK
      hstabK hPP
  · have hJ' : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ'
    exact ree_layerFacts_A1 D₀ D hp5 hK₀ hK hKK hS a1Pair_one_three hΦ hn hN hperm₀ hstab₀ hpermK
      hstabK hPP
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
    rw [hJs] at hΦ hstab₀ hstabK
    exact ree_layerFacts_B2 D₀ D hp5 hK₀ hK hKK hS hΦ hperm₀ hstab₀ hpermK hstabK hPP

end Facts

section Main

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime]
  [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a₀ a : ℕ} {L : Type} [Field L]
  [Algebra K₀ L] [Algebra K L] [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L]
  (D₀ : ReeFrameData K₀ L a₀) (D : ReeFrameData K L a)
  {C : Type} [Group C] [Finite C] {θ : C →* ModGL ReeTag.F4.tag L} {α₀ : MulAut C} {p : ℕ}

theorem ree_layer_case (hp : p.Prime) (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    (h : IsReeShintani p θ D₀.F D.F α₀) {w₀ : WeylGroup ReeTag.F4.tag}
    {g₀ : ModGL ReeTag.F4.tag L} (hg₀C : g₀ ∈ adjointGroup ReeTag.F4.tag L)
    (hg₀ : Fext D₀.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)
    {x : C} (hx : orderOf x = p) (hxα : α₀ x = x) (c : C) (hcα : α₀ c = c)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b = g₀⁻¹ * θ (c * x * c⁻¹) * g₀)
    (hne : rootCharKernel b ≠ ∅) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set n₀ := canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ with hn₀
  have hn₀C : n₀ ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w₀
  have hn₀perm : PermAct n₀ w₀ := permAct_canonicalRep w₀
  have hfixy : Fext D₀.F (θ (c * x * c⁻¹)) = θ (c * x * c⁻¹) := by
    rw [← h.actor, show α₀ (c * x * c⁻¹) = c * x * c⁻¹ by
      rw [map_mul, map_mul, map_inv, hcα, hxα]]
  have hbT : rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D₀.F n₀ := by
    rw [hb]
    exact conj_mem_twistedFixed D₀.F hg₀C hg₀ (h.mem _) hfixy
  have hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [hb]
    have e1 : orderOf (g₀⁻¹ * θ (c * x * c⁻¹) * g₀) = orderOf (θ (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective
        (θ (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (θ (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective θ h.inj _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hchar := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D₀.isFrob w₀ b).1 hbT
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a₀) hp hp3 hbp hb1 hchar
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hst₀ : ∀ β, IsRoot ReeTag.F4.tag β →
      (w₀ • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) :=
    fun β hβ => mem_kernel_iff_smul_dualRoot hp hp2 hbp hchar hβ
  have hJne : J ≠ ∅ := by
    rintro rfl
    apply hne
    have h1 : parabolicRoots ReeTag.F4.tag
        (((∅ : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) = ∅ := by
      ext γ
      simp only [parabolicRoots, Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true,
        forall_const, Set.mem_ofPred_eq, iff_false]
      rintro ⟨hγ, hz⟩
      exact IsRoot.ne_zero hγ (funext hz)
    rw [h1] at hΦ
    exact Set.image_eq_empty.1 hΦ
  have hNC : nseqF n₀ D₀.F p ∈ adjointGroup ReeTag.F4.tag L := nseqF_mem hn₀C D₀.F p
  have hFg : Fext D.F g₀ = g₀ * nseqF n₀ D₀.F p := fext_lang_norm h.iter hg₀C hn₀C hg₀
  have hRg : Rg θ g₀ = twistedFixed D.F (nseqF n₀ D₀.F p) :=
    Rg_eq_twistedFixed h.fix h.range h.mem hg₀C hFg
  have hNperm : PermAct (nseqF n₀ D₀.F p) (nseqW w₀ p) :=
    permAct_nseqF D₀.isFrob hn₀C hn₀perm p
  have hstK : ∀ β, IsRoot ReeTag.F4.tag β →
      (nseqW w₀ p • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) :=
    fun β hβ => mem_iff_nseqW_smul_dualRoot hst₀ hpodd hβ
  have hPP : twistedFixed D₀.F n₀ ≤ twistedFixed D.F (nseqF n₀ D₀.F p) := by
    rw [← hRg]
    exact twistedFixed_le_Rg h.iter h.range hg₀C hg₀
  have hLF := ree_layerFacts D₀ D hp5 hK₀ hK hKK hS hJ hJne hΦ hn₀C hNC
    (permAct_conjTwist D₀.isFrob hn₀perm u)
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w₀ u hst₀ hΦ hγ)
    (permAct_conjTwist D.isFrob hNperm u)
    (fun γ hγ => smul_dualRoot_mem_parabolic hS (nseqW w₀ p) u hstK hΦ hγ) hPP
  rw [← hRg] at hLF
  have hPP' : rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D₀.F n₀ ≤
      rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ Rg θ g₀ :=
    inf_le_inf_left _ (twistedFixed_le_Rg h.iter h.range hg₀C hg₀)
  obtain ⟨e₁, e₂, he₁, he₂, ho₁, ho₂, hnc, h2P⟩ := hLF.pair
  have hmoveP : ∃ v ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ Rg θ g₀,
      n₀ * Fext D₀.F v * n₀⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    have hle : rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ Rg θ g₀ ≤
        rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D₀.F n₀ := by
      intro v hv
      refine ⟨(Subgroup.mem_inf.1 hv).1, ?_⟩
      exact ⟨CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ (Subgroup.mem_inf.1 hv).1,
        hcon v hv⟩
    have := hLF.finite
    exact absurd hLF.smaller (not_lt.2 (Subgroup.card_le_of_le hle))
  have hodd : ∀ t ∈ torusGroup ReeTag.F4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1 := by
    have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
    exact fun t ht => exists_odd_pow_eq_one_of_mem_torusGroup_ree K ht
  have hstab : ∀ a : Fin ReeTag.F4.tag.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup ReeTag.F4.tag)) :=
    fun a hap ha1 => rootCharStabilizer_subset_closure hp (not_dvd_card_weylGroup_F4 hp hp3) hap ha1
  have hQS : ∀ v ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b),
      n₀ * Fext D₀.F v * n₀⁻¹ ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b) :=
    fun v hv => phi0_mem_rootSpan D₀.isFrob hS (fun β hβ => (hst₀ β (hS β hβ)).2 hβ) hv
  have hc : g₀⁻¹ * θ (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L ⊓
      Subgroup.centralizer (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) := by
    rw [← hb]
    refine ⟨rootDiagUnit_mem_torusGroup b, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 (fun v hv => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_rootCharKernel_le_centralizer b hv)
  have hkerZ : ∀ a' : Fin ReeTag.F4.tag.rank → Lˣ,
      rootDiagUnit ReeTag.F4.tag a' = g₀⁻¹ * θ (c * x * c⁻¹) * g₀ →
        rootCharKernel a' ⊆ rootCharKernel b := by
    intro a' ha'
    have hab : a' = b := rootDiagUnit_injective (τ := ReeTag.F4.tag) (K := L) (ha'.trans hb.symm)
    rw [hab]
  exact singleLayerData_of_layer θ h.inj h.mem D₀.F α₀ h.actor h.ordα hp hp2 hg₀C hg₀ hodd hstab
    hS hSn hQS hLF.quasisimple hLF.cent hLF.model (hPP' he₁) (hPP' he₂) (Subgroup.mem_inf.1 he₁).2.2 (Subgroup.mem_inf.1 he₂).2.2 ho₁ ho₂ hnc
    h2P hmoveP hx c hcα hc hkerZ

end Main

end CFSG.RankThree.PartOne.TCX.Ree
