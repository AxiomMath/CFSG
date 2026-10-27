module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofCent
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofDiag
public import CFSG.RankThree.PartOne.KLR.TwistClosure
public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.RankThree.PartOne.KLR.TwistPerm

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KLR
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof
open scoped MatrixGroups Pointwise


section Bridge

variable (L : Type) [Field L]

@[expose] noncomputable def xStd : Subgroup (ModGL ReeTag.F4.tag L) := (rhoL L).range

@[expose] noncomputable def yStd : Subgroup (ModGL ReeTag.F4.tag L) := (f4rhoShort L).range

@[expose] noncomputable def dStd (ζ : Lˣ) : ModGL ReeTag.F4.tag L :=
  rootDiagUnit ReeTag.F4.tag (bStd ζ)

@[expose] noncomputable def rhoLR : SL(3, L) →* ModGL ReeTag.F4.tag L := rhoL L

variable {L}

theorem rhoLR_injective : Function.Injective (rhoLR L) :=
  (rhoL_frame (L := L)).injective

theorem rhoLR_diag (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    rhoLR L A ∈ torusGroup ReeTag.F4.tag L :=
  (rhoL_frame (L := L)).diag A hA

theorem mem_xStd_iff {x : ModGL ReeTag.F4.tag L} : x ∈ xStd L ↔ ∃ M, rhoLR L M = x :=
  Iff.rfl

theorem commute_xStd_yStd {x y : ModGL ReeTag.F4.tag L} (hx : x ∈ xStd L) (hy : y ∈ yStd L) :
    x * y = y * x :=
  commute_xS_yS hx hy

variable [IsAlgClosed L] {ζ : Lˣ}

theorem exists_mul_of_commute_dStd (hζ : orderOf ζ = 3) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ adjointGroup ReeTag.F4.tag L) (hcomm : g * dStd L ζ = dStd L ζ * g) :
    ∃ x ∈ xStd L, ∃ y ∈ yStd L, g = x * y :=
  exists_mul_of_mem_sup (mem_sup_of_commute_bStd hζ hg hcomm)

theorem eq_pow_of_mem_xStd_yStd (hζ : orderOf ζ = 3) {g : ModGL ReeTag.F4.tag L}
    (hx : g ∈ xStd L) (hy : g ∈ yStd L) : ∃ k : ℕ, k < 3 ∧ g = dStd L ζ ^ k :=
  mem_inf_xS_yS hζ hx hy

theorem commute_dStd_of_mem (hζ : orderOf ζ = 3) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ xStd L ∨ g ∈ yStd L) : g * dStd L ζ = dStd L ζ * g := by
  rcases hg with hg | hg
  · exact commute_bStd_of_mem_sup hζ (Subgroup.mem_sup_left hg)
  · exact commute_bStd_of_mem_sup hζ (Subgroup.mem_sup_right hg)

end Bridge

section Transport

variable (L : Type) [Field L]

@[expose] noncomputable def xOf (N : ModGL ReeTag.F4.tag L) : Subgroup (ModGL ReeTag.F4.tag L) :=
  (xStd L).map (MulAut.conj N).toMonoidHom

@[expose] noncomputable def yOf (N : ModGL ReeTag.F4.tag L) : Subgroup (ModGL ReeTag.F4.tag L) :=
  (yStd L).map (MulAut.conj N).toMonoidHom

variable {L}

theorem commute_xOf_yOf {N x y : ModGL ReeTag.F4.tag L} (hx : x ∈ xOf L N) (hy : y ∈ yOf L N) :
    x * y = y * x := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc N * x' * N⁻¹ * (N * y' * N⁻¹) = N * (x' * y') * N⁻¹ := by group
    _ = N * (y' * x') * N⁻¹ := by rw [commute_xStd_yStd hx' hy']
    _ = N * y' * N⁻¹ * (N * x' * N⁻¹) := by group

variable [IsAlgClosed L] {ζ : Lˣ}

theorem exists_mul_of_commute_conj (hζ : orderOf ζ = 3) {N g : ModGL ReeTag.F4.tag L}
    (hN : N ∈ adjointGroup ReeTag.F4.tag L) (hg : g ∈ adjointGroup ReeTag.F4.tag L)
    (hcomm : g * (N * dStd L ζ * N⁻¹) = N * dStd L ζ * N⁻¹ * g) :
    ∃ x ∈ xOf L N, ∃ y ∈ yOf L N, g = x * y := by
  have hg' : N⁻¹ * g * N ∈ adjointGroup ReeTag.F4.tag L := mul_mem (mul_mem (inv_mem hN) hg) hN
  have hc' : N⁻¹ * g * N * dStd L ζ = dStd L ζ * (N⁻¹ * g * N) := by
    calc N⁻¹ * g * N * dStd L ζ = N⁻¹ * (g * (N * dStd L ζ * N⁻¹)) * N := by group
      _ = N⁻¹ * (N * dStd L ζ * N⁻¹ * g) * N := by rw [hcomm]
      _ = dStd L ζ * (N⁻¹ * g * N) := by group
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_commute_dStd hζ hg' hc'
  refine ⟨N * x * N⁻¹, ⟨x, hx, rfl⟩, N * y * N⁻¹, ⟨y, hy, rfl⟩, ?_⟩
  calc g = N * (N⁻¹ * g * N) * N⁻¹ := by group
    _ = N * x * N⁻¹ * (N * y * N⁻¹) := by rw [hxy]; group

theorem eq_pow_of_mem_xOf_yOf (hζ : orderOf ζ = 3) {N g : ModGL ReeTag.F4.tag L}
    (hx : g ∈ xOf L N) (hy : g ∈ yOf L N) :
    ∃ k : ℕ, k < 3 ∧ g = (N * dStd L ζ * N⁻¹) ^ k := by
  obtain ⟨x, hx', rfl⟩ := hx
  obtain ⟨y, hy', hyx⟩ := hy
  have hxy : y = x := (MulAut.conj N).injective hyx
  subst hxy
  obtain ⟨k, hk, rfl⟩ := eq_pow_of_mem_xStd_yStd hζ hx' hy'
  refine ⟨k, hk, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow]

theorem commute_conj_of_mem (hζ : orderOf ζ = 3) {N g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ xOf L N ∨ g ∈ yOf L N) :
    g * (N * dStd L ζ * N⁻¹) = N * dStd L ζ * N⁻¹ * g := by
  have key : ∀ g' : ModGL ReeTag.F4.tag L, g' * dStd L ζ = dStd L ζ * g' →
      N * g' * N⁻¹ * (N * dStd L ζ * N⁻¹) = N * dStd L ζ * N⁻¹ * (N * g' * N⁻¹) := by
    intro g' h
    calc N * g' * N⁻¹ * (N * dStd L ζ * N⁻¹) = N * (g' * dStd L ζ) * N⁻¹ := by group
      _ = N * (dStd L ζ * g') * N⁻¹ := by rw [h]
      _ = N * dStd L ζ * N⁻¹ * (N * g' * N⁻¹) := by group
  rcases hg with ⟨g', hg', rfl⟩ | ⟨g', hg', rfl⟩
  · exact key g' (commute_dStd_of_mem hζ (Or.inl hg'))
  · exact key g' (commute_dStd_of_mem hζ (Or.inr hg'))

end Transport

section Roots

variable {L : Type} [Field L]

@[expose] def setLR : Set (Fin ReeTag.F4.tag.rank → ℤ) := setL

@[expose] def setSR : Set (Fin ReeTag.F4.tag.rank → ℤ) := setS

theorem isRoot_of_mem_setLR {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ setLR) :
    IsRoot ReeTag.F4.tag α :=
  isRoot_of_mem_setL hα

theorem isRoot_of_mem_setSR {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ setSR) :
    IsRoot ReeTag.F4.tag α :=
  isRoot_of_mem_setS hα

set_option maxRecDepth 10000 in
theorem quadForm_sigma (i j : Fin 3) (hij : i ≠ j) :
    ReeTag.F4.quadForm (sigmaL i j) = 4 ∧ ReeTag.F4.quadForm (f4ShortSigma i j) = 2 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

theorem mem_longRoots_of_mem_setLR {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ setLR) :
    α ∈ ReeTag.F4.longRoots := by
  obtain ⟨i, j, hij, rfl⟩ := hα
  refine ⟨isRoot_of_mem_setL ⟨i, j, hij, rfl⟩, ?_⟩
  change ((ReeTag.F4.quadForm (sigmaL i j) : ℤ) : ℚ) / 2 = _
  rw [(quadForm_sigma i j hij).1]
  norm_num [ReeTag.prime]

theorem mem_shortRoots_of_mem_setSR {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ setSR) :
    α ∈ ReeTag.F4.shortRoots := by
  obtain ⟨i, j, hij, rfl⟩ := hα
  refine ⟨isRoot_of_mem_setS ⟨i, j, hij, rfl⟩, ?_⟩
  change ((ReeTag.F4.quadForm (f4ShortSigma i j) : ℤ) : ℚ) / 2 = _
  rw [(quadForm_sigma i j hij).2]
  norm_num

theorem not_mem_long_and_short {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hl : α ∈ ReeTag.F4.longRoots) (hs : α ∈ ReeTag.F4.shortRoots) : False := by
  have h := hl.2.symm.trans hs.2
  norm_num [ReeTag.prime] at h

theorem xOf_canonicalRep (v : WeylGroup ReeTag.F4.tag) :
    xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) =
      rootSpan ReeTag.F4.tag L ((fun γ => v • γ) '' setLR) := by
  have h := map_conj_rootSpan (L := L) v (S := setLR) fun γ hγ => isRoot_of_mem_setLR hγ
  rw [← h]
  exact congrArg (fun H : Subgroup (ModGL ReeTag.F4.tag L) =>
    H.map (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)).toMonoidHom) range_rhoL

theorem yOf_canonicalRep (v : WeylGroup ReeTag.F4.tag) :
    yOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) =
      rootSpan ReeTag.F4.tag L ((fun γ => v • γ) '' setSR) := by
  have h := map_conj_rootSpan (L := L) v (S := setSR) fun γ hγ => isRoot_of_mem_setSR hγ
  rw [← h]
  exact congrArg (fun H : Subgroup (ModGL ReeTag.F4.tag L) =>
    H.map (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)).toMonoidHom) range_rhoS

end Roots

section Swap

variable {L : Type} [Field L]

theorem rootSpan_eq_closure (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) :
    rootSpan ReeTag.F4.tag L S =
      Subgroup.closure {g | ∃ α ∈ S, ∃ c : L, pinnedX ReeTag.F4.tag L α c = g} := by
  apply le_antisymm
  · refine iSup₂_le fun α hα => Subgroup.closure_mono ?_
    rintro _ ⟨c, rfl⟩
    exact ⟨α, hα, c, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, c, rfl⟩
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => rootSubgroup ReeTag.F4.tag L γ) α hα le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)

variable {ζ : Lˣ}

theorem rootChar_eq_one_iff_transport (hζ : orderOf ζ = 3) {b : Fin ReeTag.F4.tag.rank → Lˣ}
    {v : WeylGroup ReeTag.F4.tag} (hv : ∀ l, rootChar b (v • l) = rootChar (bStd ζ) l)
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) :
    rootChar b γ = 1 ↔ v⁻¹ • γ ∈ setLR ∨ v⁻¹ • γ ∈ setSR := by
  have h1 : rootChar b γ = rootChar (bStd ζ) (v⁻¹ • γ) := by
    rw [← hv, smul_inv_smul]
  have hk : rootCharKernel (bStd ζ) = setLR ∪ setSR := rootCharKernel_bStd (L := L) hζ
  have hr : IsRoot ReeTag.F4.tag (v⁻¹ • γ) := IsRoot.smul hγ v⁻¹
  constructor
  · intro h
    have hmem : v⁻¹ • γ ∈ rootCharKernel (bStd ζ) := ⟨hr, h1 ▸ h⟩
    rw [hk] at hmem
    exact hmem
  · intro h
    have hmem : v⁻¹ • γ ∈ rootCharKernel (bStd ζ) := by
      rw [hk]
      exact h
    rw [h1]
    exact hmem.2

variable [CharP L 2] [IsAlgClosed L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem twistMap_swap (hF : IsReeFrob a F) (hζ : orderOf ζ = 3)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hb3 : ∀ i, b i ^ 3 = 1)
    (hbR : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2))
    {v : WeylGroup ReeTag.F4.tag} (hv : ∀ l, rootChar b (v • l) = rootChar (bStd ζ) l) :
    (∀ x ∈ xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v),
      twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x ∈
        yOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)) ∧
    (∀ y ∈ yOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v),
      twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) y ∈
        xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)) := by
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 with hn
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF wPhi2 b).1 hbR
  have hstab : ∀ β, IsRoot ReeTag.F4.tag β → rootChar b β = 1 →
      rootChar b (wPhi2 • ReeTag.F4.dualRoot β) = 1 := by
    intro β hβ h1
    exact ((mem_kernel_iff_smul_dualRoot Nat.prime_three (by norm_num) hb3 hw hβ).2
      ⟨hβ, h1⟩).2
  have hgen : ∀ (S T : Set (Fin ReeTag.F4.tag.rank → ℤ)),
      (∀ β ∈ (fun γ => v • γ) '' S, IsRoot ReeTag.F4.tag β ∧
        wPhi2 • ReeTag.F4.dualRoot β ∈ (fun γ => v • γ) '' T) →
      ∀ g ∈ rootSpan ReeTag.F4.tag L ((fun γ => v • γ) '' S),
        twistMap F n g ∈ rootSpan ReeTag.F4.tag L ((fun γ => v • γ) '' T) := by
    intro S T hST g hg
    rw [rootSpan_eq_closure] at hg
    refine (twistMap_mem_of_closure (fun g hg' => ?_) (fun g hg' => ?_) hg).1
    · obtain ⟨α, -, c, rfl⟩ := hg'
      exact pinnedX_mem_adjointGroup α c
    · obtain ⟨β, hβ, c, rfl⟩ := hg'
      obtain ⟨hβr, hβT⟩ := hST β hβ
      rw [twistMap, hF.twist_pinnedX (permAct_canonicalRep wPhi2) hβr c]
      exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ (fun γ => v • γ) '' T) =>
        rootSubgroup ReeTag.F4.tag L γ) _ hβT le_rfl (Subgroup.subset_closure ⟨_, rfl⟩)
  have hdual : ∀ α : Fin ReeTag.F4.tag.rank → ℤ, α ∈ setLR ∨ α ∈ setSR →
      v⁻¹ • (wPhi2 • ReeTag.F4.dualRoot (v • α)) ∈ setLR ∨
        v⁻¹ • (wPhi2 • ReeTag.F4.dualRoot (v • α)) ∈ setSR := by
    intro α hα
    have hαr : IsRoot ReeTag.F4.tag α := by
      rcases hα with hα | hα
      · exact isRoot_of_mem_setLR hα
      · exact isRoot_of_mem_setSR hα
    have hβr : IsRoot ReeTag.F4.tag (v • α) := IsRoot.smul hαr v
    have h1 : rootChar b (v • α) = 1 := by
      rw [rootChar_eq_one_iff_transport hζ hv hβr, inv_smul_smul]
      exact hα
    have hγr : IsRoot ReeTag.F4.tag (wPhi2 • ReeTag.F4.dualRoot (v • α)) :=
      IsRoot.smul (ReeTag.isRoot_dualRoot hβr) wPhi2
    exact (rootChar_eq_one_iff_transport hζ hv hγr).1 (hstab _ hβr h1)
  constructor
  · intro x hx
    rw [xOf_canonicalRep] at hx
    rw [yOf_canonicalRep]
    refine hgen setLR setSR (fun β hβ => ?_) x hx
    obtain ⟨α, hα, rfl⟩ := hβ
    refine ⟨IsRoot.smul (isRoot_of_mem_setLR hα) v, ?_⟩
    have hlong : v • α ∈ ReeTag.F4.longRoots := smul_mem_longRoots v (mem_longRoots_of_mem_setLR hα)
    have hshort : wPhi2 • ReeTag.F4.dualRoot (v • α) ∈ ReeTag.F4.shortRoots :=
      smul_mem_shortRoots wPhi2 ((ReeTag.bijOn_dualRoot ReeTag.F4).mapsTo hlong)
    rcases hdual α (Or.inl hα) with h | h
    · exact absurd (not_mem_long_and_short (by
        have := smul_mem_longRoots v (mem_longRoots_of_mem_setLR h)
        rwa [smul_inv_smul] at this) hshort) id
    · exact ⟨_, h, smul_inv_smul v _⟩
  · intro y hy
    rw [yOf_canonicalRep] at hy
    rw [xOf_canonicalRep]
    refine hgen setSR setLR (fun β hβ => ?_) y hy
    obtain ⟨α, hα, rfl⟩ := hβ
    refine ⟨IsRoot.smul (isRoot_of_mem_setSR hα) v, ?_⟩
    have hshort : v • α ∈ ReeTag.F4.shortRoots :=
      smul_mem_shortRoots v (mem_shortRoots_of_mem_setSR hα)
    have hlong : wPhi2 • ReeTag.F4.dualRoot (v • α) ∈ ReeTag.F4.longRoots :=
      smul_mem_longRoots wPhi2 (dualRoot_mem_longRoots hshort)
    rcases hdual α (Or.inr hα) with h | h
    · exact ⟨_, h, smul_inv_smul v _⟩
    · exact absurd (not_mem_long_and_short hlong (by
        have := smul_mem_shortRoots v (mem_shortRoots_of_mem_setSR h)
        rwa [smul_inv_smul] at this)) id

end Swap

section Lang

open CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.E6 (chainRoot chainRoot_swap)


variable (L : Type) [Field L]

@[expose] noncomputable def negRep : ModGL ReeTag.F4.tag L :=
  canonicalRep (coxeterSystem ReeTag.F4.tag) L qpNeg

@[expose] noncomputable def qJ : Subgroup (ModGL ReeTag.F4.tag L) :=
  subsystemGroup Tag.F4 L f4LongSupport

@[expose] noncomputable def nU : ModGL ReeTag.F4.tag L :=
  canonicalRep (coxeterSystem ReeTag.F4.tag) L trElem

variable {L} [CharP L 2] [IsAlgClosed L] [Fact (Nat.Prime 2)] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem negRep_comm (w : WeylGroup ReeTag.F4.tag) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w * negRep L =
      negRep L * canonicalRep (coxeterSystem ReeTag.F4.tag) L w :=
  qpRep_comm w

theorem nW_mul_fext (hF : IsReeFrob a F) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 *
        Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) = negRep L := by
  rw [hF.fext_canonicalRep, ← qplus_canonicalRep_mul, wPhi2_mul_weylPerm]
  rfl

theorem twistMap_twistMap (hF : IsReeFrob a F)
    (hsq : ∀ y : adjointGroup ReeTag.F4.tag L, ((F (F y) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) y)
    {g : ModGL ReeTag.F4.tag L} (hg : g ∈ adjointGroup ReeTag.F4.tag L) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
        (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) g) =
      negRep L * entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) g * (negRep L)⁻¹ := by
  have hnG : canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L wPhi2
  have hFg : Fext F g ∈ adjointGroup ReeTag.F4.tag L := Fext_mem F hg
  have hFF : Fext F (Fext F g) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) g := by
    rw [Fext_of_mem F hFg]
    have h1 : (⟨Fext F g, hFg⟩ : adjointGroup ReeTag.F4.tag L) = F ⟨g, hg⟩ :=
      Subtype.ext (Fext_of_mem F hg)
    rw [h1]
    exact hsq ⟨g, hg⟩
  unfold twistMap
  rw [Fext_mul F (mul_mem hnG hFg) (inv_mem hnG), Fext_mul F hnG hFg, Fext_inv F hnG, hFF,
    ← nW_mul_fext hF]
  group

theorem entrywiseFrobGL_canonicalRep (e : ℕ) (w : WeylGroup ReeTag.F4.tag) :
    entrywiseFrobGL ReeTag.F4.tag L 2 e (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w :=
  CFSG.LieType.Chevalley.baseChangeGL_canonicalRep (iterateFrobenius L 2 e) w

theorem qpRep_mem_normalizer :
    qpRep L ∈ Subgroup.normalizer
      ((subsystemGroup Tag.F4 L f4LongSupport : Subgroup (ModGL Tag.F4 L)) :
        Set (ModGL Tag.F4 L)) := by
  set C : Set (Fin Tag.F4.rank → ℤ) :=
    {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot (τ := Tag.F4) f4chainLong i j} with hC
  have hQ : subsystemGroup Tag.F4 L f4LongSupport = rootSpan Tag.F4 L C := by
    rw [← f4rhoLong_range]
    exact (f4Long_frame (L := L)).range
  have hCr : ∀ γ ∈ C, IsRoot Tag.F4 γ := by
    rintro γ ⟨i, j, hij, rfl⟩
    exact (f4Long_frame (L := L)).isRoot i j hij
  have hneg : (fun γ => qpNeg • γ) '' C = C := by
    ext r
    constructor
    · rintro ⟨γ, ⟨i, j, hij, rfl⟩, rfl⟩
      refine ⟨j, i, hij.symm, ?_⟩
      show qpNeg • chainRoot (τ := Tag.F4) f4chainLong i j = _
      rw [qpNeg_smul]
      exact (chainRoot_swap _ i j).symm
    · rintro ⟨i, j, hij, rfl⟩
      refine ⟨chainRoot (τ := Tag.F4) f4chainLong j i, ⟨j, i, hij.symm, rfl⟩, ?_⟩
      show qpNeg • chainRoot (τ := Tag.F4) f4chainLong j i = _
      rw [qpNeg_smul]
      exact (chainRoot_swap _ j i).symm
  have hmap : (rootSpan Tag.F4 L C).map (MulAut.conj (qpRep L)).toMonoidHom =
      rootSpan Tag.F4 L C := by
    rw [qpRep, map_conj_rootSpan qpNeg hCr, hneg]
  refine Subgroup.mem_normalizer_iff.2 fun g => ?_
  rw [hQ]
  constructor
  · intro hg
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← hmap] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    have : g' = g := (MulAut.conj (qpRep L)).injective hgg
    rw [← this]
    exact hg'

theorem exists_lang_qJ {y : ModGL ReeTag.F4.tag L} (hy : y ∈ qJ L) :
    ∃ h ∈ qJ L, y = h⁻¹ * (negRep L * entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) h *
      (negRep L)⁻¹) := by
  obtain ⟨-, hlang⟩ := supported_native_affine_realization_and_Lang Tag.F4 L f4LongSupport
  obtain ⟨-, -, hl, -⟩ := hlang 2 (2 * a + 1) (by omega) (qpRep L) qpRep_mem_normalizer
  exact hl y hy

theorem qJ_le_adjointGroup : qJ L ≤ adjointGroup ReeTag.F4.tag L := by
  intro g hg
  have hg' : g ∈ rootSpan ReeTag.F4.tag L {r | ∃ i j : Fin 3, i ≠ j ∧
      r = chainRoot (τ := Tag.F4) f4chainLong i j} := by
    have h := (f4Long_frame (L := L)).range
    rw [f4rhoLong_range] at h
    exact h ▸ hg
  exact rootSpan_le_adjointGroup L _ hg'

theorem exists_of_mem_xOf {v : WeylGroup ReeTag.F4.tag} {x : ModGL ReeTag.F4.tag L}
    (hx : x ∈ xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)) :
    ∃ q ∈ qJ L, x = canonicalRep (coxeterSystem ReeTag.F4.tag) L v * (nU L * q * (nU L)⁻¹) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ := by
  obtain ⟨x', ⟨M, rfl⟩, rfl⟩ := hx
  exact ⟨f4rhoLong L M, f4rhoLong_mem M, rfl⟩

theorem mem_xOf_of {v : WeylGroup ReeTag.F4.tag} {q : ModGL ReeTag.F4.tag L} (hq : q ∈ qJ L) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L v * (nU L * q * (nU L)⁻¹) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ ∈
      xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) := by
  have hq' : q ∈ (f4rhoLong L).range := by
    rw [f4rhoLong_range]
    exact hq
  obtain ⟨M, rfl⟩ := hq'
  exact ⟨_, ⟨M, rfl⟩, rfl⟩

theorem exists_lang_xOf (hF : IsReeFrob a F)
    (hsq : ∀ y : adjointGroup ReeTag.F4.tag L, ((F (F y) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) y)
    (v : WeylGroup ReeTag.F4.tag) {x : ModGL ReeTag.F4.tag L}
    (hx : x ∈ xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)) :
    ∃ x' ∈ xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v),
      x'⁻¹ * twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
        (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x') = x := by
  set Nv := canonicalRep (coxeterSystem ReeTag.F4.tag) L v with hNv
  obtain ⟨q, hq, rfl⟩ := exists_of_mem_xOf hx
  obtain ⟨h, hh, hqh⟩ := exists_lang_qJ (a := a) hq
  refine ⟨Nv * (nU L * h * (nU L)⁻¹) * Nv⁻¹, mem_xOf_of hh, ?_⟩
  have hG : Nv * (nU L * h * (nU L)⁻¹) * Nv⁻¹ ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L v) (mul_mem (mul_mem
      (canonicalRep_mem_adjointGroup _ L trElem) (qJ_le_adjointGroup hh))
      (inv_mem (canonicalRep_mem_adjointGroup _ L trElem))))
      (inv_mem (canonicalRep_mem_adjointGroup _ L v))
  rw [twistMap_twistMap hF hsq hG]
  have hFv : entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) Nv = Nv :=
    entrywiseFrobGL_canonicalRep _ v
  have hFu : entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (nU L) = nU L :=
    entrywiseFrobGL_canonicalRep _ trElem
  have hcv : negRep L * Nv = Nv * negRep L := (negRep_comm v).symm
  have hcu : negRep L * nU L = nU L * negRep L := (negRep_comm trElem).symm
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hFv, hFu, hqh]
  obtain ⟨M, hM⟩ : ∃ M, M = Nv * nU L := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) h := ⟨_, rfl⟩
  rw [← hE]
  have hcM : negRep L * M = M * negRep L := by
    rw [hM, ← mul_assoc, hcv, mul_assoc, hcu, ← mul_assoc]
  have hcMi : M⁻¹ * (negRep L)⁻¹ = (negRep L)⁻¹ * M⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hcM]
  have e1 : Nv * (nU L * h * (nU L)⁻¹) * Nv⁻¹ = M * h * M⁻¹ := by rw [hM]; group
  have e2 : Nv * (nU L * E * (nU L)⁻¹) * Nv⁻¹ = M * E * M⁻¹ := by rw [hM]; group
  have e3 : Nv * (nU L * (h⁻¹ * (negRep L * E * (negRep L)⁻¹)) * (nU L)⁻¹) * Nv⁻¹ =
      M * (h⁻¹ * (negRep L * E * (negRep L)⁻¹)) * M⁻¹ := by rw [hM]; group
  rw [e1, e2, e3]
  calc (M * h * M⁻¹)⁻¹ * (negRep L * (M * E * M⁻¹) * (negRep L)⁻¹) =
      M * h⁻¹ * M⁻¹ * ((negRep L * M) * E * (M⁻¹ * (negRep L)⁻¹)) := by group
    _ = M * h⁻¹ * M⁻¹ * ((M * negRep L) * E * ((negRep L)⁻¹ * M⁻¹)) := by rw [hcM, hcMi]
    _ = M * (h⁻¹ * (negRep L * E * (negRep L)⁻¹)) * M⁻¹ := by group

end Lang

section Exchange

open CFSG.LieType.AlgebraicGroups

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] [Fact (Nat.Prime 2)] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)} {ζ : Lˣ}

theorem xOf_le_adjointGroup (v : WeylGroup ReeTag.F4.tag) :
    xOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) ≤ adjointGroup ReeTag.F4.tag L := by
  rw [xOf_canonicalRep]
  exact rootSpan_le_adjointGroup L _

theorem yOf_le_adjointGroup (v : WeylGroup ReeTag.F4.tag) :
    yOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) ≤ adjointGroup ReeTag.F4.tag L := by
  rw [yOf_canonicalRep]
  exact rootSpan_le_adjointGroup L _

theorem twistMap_pow {n g : ModGL ReeTag.F4.tag L} (hg : g ∈ adjointGroup ReeTag.F4.tag L)
    (k : ℕ) : twistMap F n (g ^ k) = twistMap F n g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, twistMap_one]
  | succ k ih => rw [pow_succ, twistMap_mul n (pow_mem hg k) hg, ih, pow_succ]

theorem twistMap_mem_torusGroup (hF : IsReeFrob a F) {t : ModGL ReeTag.F4.tag L}
    (ht : t ∈ torusGroup ReeTag.F4.tag L) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) t ∈
      torusGroup ReeTag.F4.tag L := by
  obtain ⟨hadj, hFt⟩ := hF.map_torusGroup ht
  have h1 : Fext F t ∈ torusGroup ReeTag.F4.tag L := by
    rw [Fext_of_mem F hadj]
    exact hFt
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer wPhi2) _).1 h1

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem pow_two_pow_odd_of_pow_three {u : Lˣ} (hu : u ^ 3 = 1) (a : ℕ) :
    u ^ (2 ^ (2 * a + 1)) = u⁻¹ := by
  have h := Nat.div_add_mod (2 ^ (2 * a + 1)) 3
  rw [two_pow_odd_mod_three] at h
  rw [← h, pow_add, pow_mul, hu, one_pow, one_mul, eq_inv_iff_mul_eq_one, ← pow_succ, hu]

theorem twistMap_twistMap_of_torsion (hF : IsReeFrob a F)
    (hsq : ∀ y : adjointGroup ReeTag.F4.tag L, ((F (F y) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) y)
    {c : Fin ReeTag.F4.tag.rank → Lˣ} (hc : ∀ i, c i ^ 3 = 1) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
        (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
          (rootDiagUnit ReeTag.F4.tag c)) = rootDiagUnit ReeTag.F4.tag c := by
  have hcG : rootDiagUnit ReeTag.F4.tag c ∈ adjointGroup ReeTag.F4.tag L :=
    torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup c)
  rw [twistMap_twistMap hF hsq hcG]
  have hFr : entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (rootDiagUnit ReeTag.F4.tag c) =
      rootDiagUnit ReeTag.F4.tag c⁻¹ := by
    refine Units.ext ?_
    rw [Units.coe_map]
    change entrywise (iterateFrobenius L 2 (2 * a + 1)) (rootDiag c) = rootDiag c⁻¹
    rw [entrywise_rootDiag]
    congr 1
    funext i
    refine Units.ext ?_
    show (iterateFrobenius L 2 (2 * a + 1)) (c i : L) = ((c⁻¹ i : Lˣ) : L)
    rw [iterateFrobenius_def, ← Units.val_pow_eq_pow_val, pow_two_pow_odd_of_pow_three (hc i)]
    rfl
  rw [hFr]
  have h := qpRep_conj_rootDiagUnit (M := L) c⁻¹
  rw [rootDiagUnit_inv] at h
  have hcc : (c⁻¹)⁻¹ = c := inv_inv c
  exact h.trans (congrArg (rootDiagUnit Tag.F4) hcc)

theorem exists_lang_cent (hF : IsReeFrob a F)
    (hsq : ∀ y : adjointGroup ReeTag.F4.tag L, ((F (F y) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) y)
    (hζ : orderOf ζ = 3) {b : Fin ReeTag.F4.tag.rank → Lˣ} (hb3 : ∀ i, b i ^ 3 = 1)
    (hbR : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2))
    {v : WeylGroup ReeTag.F4.tag} (hv : ∀ l, rootChar b (v • l) = rootChar (bStd ζ) l)
    {c : ModGL ReeTag.F4.tag L} (hc : c ∈ adjointGroup ReeTag.F4.tag L)
    (hcomm : c * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * c) :
    ∃ z ∈ adjointGroup ReeTag.F4.tag L,
      z * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * z ∧
        z⁻¹ * twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) z = c := by
  have hnG : canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L wPhi2
  have hd : rootDiagUnit ReeTag.F4.tag b = canonicalRep (coxeterSystem ReeTag.F4.tag) L v *
      dStd L ζ * (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b (bStd ζ) v).2 hv
  rw [hd] at hcomm ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_commute_conj hζ
    (canonicalRep_mem_adjointGroup _ L v) hc hcomm
  obtain ⟨hXY, hYX⟩ := twistMap_swap hF hζ hb3 hbR hv
  have hxG := xOf_le_adjointGroup v hx
  have hyG := yOf_le_adjointGroup v hy
  have hFy := hYX y hy
  obtain ⟨x', hx', hlang⟩ := exists_lang_xOf hF hsq v (mul_mem hx hFy)
  have hx'G := xOf_le_adjointGroup v hx'
  have hFx' := hXY x' hx'
  have hy'Y : twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' * y⁻¹ ∈
      yOf L (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) := mul_mem hFx' (inv_mem hy)
  have hy'G := yOf_le_adjointGroup v hy'Y
  refine ⟨x' * (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' * y⁻¹),
    mul_mem hx'G hy'G, ?_, ?_⟩
  · have h1 := commute_conj_of_mem hζ (Or.inl hx')
    have h2 := commute_conj_of_mem hζ (Or.inr hy'Y)
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  · rw [twistMap_mul _ hx'G hy'G, twistMap_mul _ (twistMap_mem_adjoint hnG hx'G) (inv_mem hyG),
      twistMap_inv _ hyG]
    have hc1 : (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x')⁻¹ * x'⁻¹ *
        twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' = x'⁻¹ := by
      have h := commute_xOf_yOf hx' hFx'
      calc (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x')⁻¹ * x'⁻¹ *
            twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' =
          (x' * twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x')⁻¹ *
            twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' := by group
        _ = (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' * x')⁻¹ *
            twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' := by rw [h]
        _ = x'⁻¹ := by group
    have hc2 : x * y = y * x := commute_xOf_yOf hx hy
    calc (x' * (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' * y⁻¹))⁻¹ *
          (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x' *
            (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
              (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x') *
              (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) y)⁻¹)) =
        y * ((twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x')⁻¹ * x'⁻¹ *
          twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x') *
          twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
            (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x') *
          (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) y)⁻¹ := by group
      _ = y * (x'⁻¹ * twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)
            (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) x')) *
          (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) y)⁻¹ := by
        rw [hc1]
        group
      _ = x * y := by
        rw [hlang, hc2]
        group

theorem exists_torsion_tuple {t : ModGL ReeTag.F4.tag L} (ht : t ∈ torusGroup ReeTag.F4.tag L)
    (ht3 : t ^ 3 = 1) :
    ∃ c : Fin ReeTag.F4.tag.rank → Lˣ, (∀ i, c i ^ 3 = 1) ∧ t = rootDiagUnit ReeTag.F4.tag c := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine ⟨c, fun i => ?_, rfl⟩
  have h1 : rootDiagUnit ReeTag.F4.tag (c ^ 3) = rootDiagUnit ReeTag.F4.tag 1 := by
    rw [rootDiagUnit_one, ← ht3]
    exact (rootDiagUnit_pow' c 3).symm
  exact congrFun (rootDiagUnit_injective h1) i

theorem torus_comm {s t : ModGL ReeTag.F4.tag L} (hs : s ∈ torusGroup ReeTag.F4.tag L)
    (ht : t ∈ torusGroup ReeTag.F4.tag L) : s * t = t * s := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  obtain ⟨d, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem rootDiagUnit_pow_three {b : Fin ReeTag.F4.tag.rank → Lˣ} (hb3 : ∀ i, b i ^ 3 = 1) :
    rootDiagUnit ReeTag.F4.tag b ^ 3 = 1 := by
  have h : b ^ 3 = 1 := funext hb3
  calc rootDiagUnit ReeTag.F4.tag b ^ 3 = rootDiagUnit ReeTag.F4.tag (b ^ 3) :=
        rootDiagUnit_pow' b 3
    _ = 1 := (congrArg (rootDiagUnit ReeTag.F4.tag) h).trans rootDiagUnit_one

theorem exists_conj_torsion (hF : IsReeFrob a F)
    (hsq : ∀ y : adjointGroup ReeTag.F4.tag L, ((F (F y) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) y)
    (hζ : orderOf ζ = 3) {b : Fin ReeTag.F4.tag.rank → Lˣ} (hb3 : ∀ i, b i ^ 3 = 1)
    (hbR : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2))
    {v : WeylGroup ReeTag.F4.tag} (hv : ∀ l, rootChar b (v • l) = rootChar (bStd ζ) l)
    {s : ModGL ReeTag.F4.tag L}
    (hsR : s ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2))
    (hscomm : s * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * s)
    (hs3 : s ^ 3 = 1) :
    ∃ g ∈ adjointGroup ReeTag.F4.tag L, ∃ c : Fin ReeTag.F4.tag.rank → Lˣ,
      (∀ i, c i ^ 3 = 1) ∧ rootDiagUnit ReeTag.F4.tag c ∈
        twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) ∧
      g⁻¹ * s * g = rootDiagUnit ReeTag.F4.tag c := by
  set Nv := canonicalRep (coxeterSystem ReeTag.F4.tag) L v with hNv
  have hNvG : Nv ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L v
  have hnG : canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L wPhi2
  set db := rootDiagUnit ReeTag.F4.tag b with hdb
  have hd : db = Nv * dStd L ζ * Nv⁻¹ := (rootDiagUnit_eq_conj_canonicalRep_iff b (bStd ζ) v).2 hv
  have hdbG : db ∈ adjointGroup ReeTag.F4.tag L := hbR.1
  have hFdb : twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) db = db := hbR.2
  have hdb3 : db ^ 3 = 1 := rootDiagUnit_pow_three hb3
  have hdbH : db ∈ torusGroup ReeTag.F4.tag L := rootDiagUnit_mem_torusGroup b
  have hsG : s ∈ adjointGroup ReeTag.F4.tag L := hsR.1
  have hFs : twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) s = s := hsR.2
  rw [hd] at hscomm
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_commute_conj hζ hNvG hsG hscomm
  obtain ⟨hXY, hYX⟩ := twistMap_swap hF hζ hb3 hbR hv
  have hxG := xOf_le_adjointGroup v hx
  have hyG := yOf_le_adjointGroup v hy
  set F' := twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) with hF'
  have tpow : ∀ {g : ModGL ReeTag.F4.tag L}, g ∈ adjointGroup ReeTag.F4.tag L →
      ∀ j : ℕ, F' (g ^ j) = F' g ^ j := fun hg j => by rw [hF']; exact twistMap_pow hg j
  have tmul : ∀ {g h : ModGL ReeTag.F4.tag L}, g ∈ adjointGroup ReeTag.F4.tag L →
      h ∈ adjointGroup ReeTag.F4.tag L → F' (g * h) = F' g * F' h :=
    fun hg hh => by rw [hF']; exact twistMap_mul _ hg hh
  have tinv : ∀ {g : ModGL ReeTag.F4.tag L}, g ∈ adjointGroup ReeTag.F4.tag L →
      F' g⁻¹ = (F' g)⁻¹ := fun hg => by rw [hF']; exact twistMap_inv _ hg
  have hFx := hXY x hx
  have hFy := hYX y hy
  have hFxy : F' x * F' y = x * y := by rw [← tmul hxG hyG]; exact hFs
  have hεX : x⁻¹ * F' y ∈ xOf L Nv := mul_mem (inv_mem hx) hFy
  have hεeq : x⁻¹ * F' y = (F' x)⁻¹ * y := by
    have h1 : F' y = (F' x)⁻¹ * (x * y) := by rw [← hFxy]; group
    rw [h1]
    have h2 : x⁻¹ * (F' x)⁻¹ = (F' x)⁻¹ * x⁻¹ :=
      commute_xOf_yOf (inv_mem hx) (inv_mem hFx)
    calc x⁻¹ * ((F' x)⁻¹ * (x * y)) = (x⁻¹ * (F' x)⁻¹) * x * y := by group
      _ = (F' x)⁻¹ * y := by rw [h2]; group
  have hεY : x⁻¹ * F' y ∈ yOf L Nv := by
    rw [hεeq]
    exact mul_mem (inv_mem hFx) hy
  obtain ⟨k, -, hk⟩ := eq_pow_of_mem_xOf_yOf hζ hεX hεY
  rw [← hd] at hk
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = x⁻¹ * F' y := ⟨_, rfl⟩
  rw [← hεdef] at hk hεX hεY hεeq
  have hεH : ε ∈ torusGroup ReeTag.F4.tag L := hk ▸ pow_mem hdbH k
  have hεG : ε ∈ adjointGroup ReeTag.F4.tag L := hk ▸ pow_mem hdbG k
  have hε3 : ε ^ 3 = 1 := by rw [hk, ← pow_mul, mul_comm, pow_mul, hdb3, one_pow]
  have hFε : F' ε = ε := by rw [hk, tpow hdbG, hFdb]
  have hyε : y = F' x * ε := by rw [hεeq]; group
  have cεX : ∀ z ∈ xOf L Nv, ε * z = z * ε := fun z hz => (commute_xOf_yOf hz hεY).symm
  have cεY : ∀ z ∈ yOf L Nv, ε * z = z * ε := fun z hz => commute_xOf_yOf hεX hz
  have hx3F : x ^ 3 * F' (x ^ 3) = 1 := by
    have h1 : (x * (F' x * ε)) ^ 3 = x ^ 3 * F' x ^ 3 * ε ^ 3 := by
      have c1 : Commute x (F' x) := commute_xOf_yOf hx hFx
      have c2 : Commute (x * F' x) ε :=
        Commute.mul_left (cεX x hx).symm (cεY _ hFx).symm
      rw [← mul_assoc, c2.mul_pow, c1.mul_pow]
    rw [← hyε, hs3, hε3, mul_one, ← tpow hxG] at h1
    exact h1.symm
  have hx3X : x ^ 3 ∈ xOf L Nv := pow_mem hx 3
  have hx3Y : x ^ 3 ∈ yOf L Nv := by
    have h1 : F' (x ^ 3) = (x ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hx3F
    have h2 : (x ^ 3)⁻¹ ∈ yOf L Nv := h1 ▸ hXY _ hx3X
    simpa using inv_mem h2
  obtain ⟨m, -, hm⟩ := eq_pow_of_mem_xOf_yOf hζ hx3X hx3Y
  rw [← hd] at hm
  have hFx3 : F' (x ^ 3) = x ^ 3 := by rw [hm, tpow hdbG, hFdb]
  have hx6 : x ^ 3 * x ^ 3 = 1 := by
    calc x ^ 3 * x ^ 3 = x ^ 3 * F' (x ^ 3) := by rw [hFx3]
      _ = 1 := hx3F
  have hx9 : (x ^ 3) ^ 3 = 1 := by rw [hm, ← pow_mul, mul_comm, pow_mul, hdb3, one_pow]
  have hx3 : x ^ 3 = 1 := by
    have : x ^ 3 = (x ^ 3) ^ 3 * (x ^ 3 * x ^ 3)⁻¹ := by group
    rw [this, hx9, hx6, inv_one, mul_one]
  obtain ⟨x₀, hx₀X, hx₀⟩ := hx
  obtain ⟨M, hM⟩ := mem_xStd_iff.1 hx₀X
  have hxM : x = Nv * rhoLR L M * Nv⁻¹ := by rw [hM]; exact hx₀.symm
  have hM3 : M ^ 3 = 1 := by
    apply rhoLR_injective
    rw [map_pow, map_one]
    have h1 : (Nv * rhoLR L M * Nv⁻¹) ^ 3 = 1 := by rw [← hxM]; exact hx3
    rw [conj_pow] at h1
    have h2 : rhoLR L M ^ 3 = Nv⁻¹ * (Nv * rhoLR L M ^ 3 * Nv⁻¹) * Nv := by group
    rw [h2, h1]
    group
  have h3L : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  obtain ⟨P, D, hD, hPD⟩ := exists_conj_diag h3L M hM3
  set p := Nv * rhoLR L P * Nv⁻¹ with hp
  set t := Nv * rhoLR L D * Nv⁻¹ with ht
  have hpX : p ∈ xOf L Nv := ⟨rhoLR L P, mem_xStd_iff.2 ⟨P, rfl⟩, rfl⟩
  have htX : t ∈ xOf L Nv := ⟨rhoLR L D, mem_xStd_iff.2 ⟨D, rfl⟩, rfl⟩
  have hpG := xOf_le_adjointGroup v hpX
  have htG := xOf_le_adjointGroup v htX
  have hxpt : x = p * t * p⁻¹ := by
    rw [hxM, hPD, map_mul, map_mul, map_inv, hp, ht]
    group
  have htH : t ∈ torusGroup ReeTag.F4.tag L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 (rhoLR_diag D hD)
  have ht3 : t ^ 3 = 1 := by
    have : t = p⁻¹ * x * p⁻¹⁻¹ := by rw [hxpt]; group
    rw [this, conj_pow, hx3]
    group
  have hFp := hXY p hpX
  have hFt := hXY t htX
  have hFpG := yOf_le_adjointGroup v hFp
  have hFtG := yOf_le_adjointGroup v hFt
  have hFx' : F' x = F' p * F' t * (F' p)⁻¹ := by
    rw [hxpt, tmul (mul_mem hpG htG) (inv_mem hpG), tmul hpG htG, tinv hpG]
  have hgconj : x * F' x = p * F' p * (t * F' t) * (p * F' p)⁻¹ := by
    have c1 : F' p * t = t * F' p := (commute_xOf_yOf htX hFp).symm
    have c2 : F' p * F' t * (F' p)⁻¹ * p⁻¹ = p⁻¹ * (F' p * F' t * (F' p)⁻¹) :=
      (commute_xOf_yOf (inv_mem hpX) (mul_mem (mul_mem hFp hFt) (inv_mem hFp))).symm
    calc x * F' x = p * t * p⁻¹ * (F' p * F' t * (F' p)⁻¹) := by rw [hxpt, ← hFx', hxpt]
      _ = p * t * (p⁻¹ * (F' p * F' t * (F' p)⁻¹)) := by group
      _ = p * t * (F' p * F' t * (F' p)⁻¹ * p⁻¹) := by rw [c2]
      _ = p * (t * F' p) * F' t * (F' p)⁻¹ * p⁻¹ := by group
      _ = p * (F' p * t) * F' t * (F' p)⁻¹ * p⁻¹ := by rw [c1]
      _ = p * F' p * (t * F' t) * (p * F' p)⁻¹ := by group
  have hεg : ε * (p * F' p) = p * F' p * ε := by
    rw [← mul_assoc, cεX p hpX, mul_assoc, cεY _ hFp, ← mul_assoc]
  refine ⟨p * F' p, mul_mem hpG hFpG, ?_⟩
  have hFtH : F' t ∈ torusGroup ReeTag.F4.tag L := by
    rw [hF']
    exact twistMap_mem_torusGroup hF htH
  have hhH : t * F' t * ε ∈ torusGroup ReeTag.F4.tag L := mul_mem (mul_mem htH hFtH) hεH
  have hh3 : (t * F' t * ε) ^ 3 = 1 := by
    have c1 : Commute t (F' t) := torus_comm htH hFtH
    have c2 : Commute (t * F' t) ε := torus_comm (mul_mem htH hFtH) hεH
    rw [c2.mul_pow, c1.mul_pow, ht3, ← tpow htG, ht3, hε3, hF', twistMap_one]
    group
  obtain ⟨ct, hct3, hct⟩ := exists_torsion_tuple htH ht3
  have hFFt : F' (F' t) = t := by
    rw [hct, hF']
    exact twistMap_twistMap_of_torsion hF hsq hct3
  obtain ⟨c, hc3, hc⟩ := exists_torsion_tuple hhH hh3
  refine ⟨c, hc3, ?_, ?_⟩
  · rw [← hc]
    refine ⟨torusGroup_le_adjointGroup' hhH, ?_⟩
    change F' (t * F' t * ε) = t * F' t * ε
    rw [tmul (mul_mem htG hFtG) hεG, tmul htG hFtG, hFFt, hFε, torus_comm hFtH htH]
  · rw [← hc, hyε]
    calc (p * F' p)⁻¹ * (x * (F' x * ε)) * (p * F' p) =
        (p * F' p)⁻¹ * (x * F' x) * (ε * (p * F' p)) := by group
      _ = t * F' t * ε := by rw [hgconj, hεg]; group

end Exchange

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
