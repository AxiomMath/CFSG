module

public import CFSG.Monster.B.TwoA.Amalgam.Flag2Map

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree
open scoped Pointwise

attribute [local instance] vAction

theorem exists_quotient_equiv {G X : Type*} [Group G] (H : Subgroup G) (f : G → X)
    (hf : ∀ g h, f g = f h ↔ g⁻¹ * h ∈ H) (hs : Function.Surjective f) :
    ∃ e : G ⧸ H ≃ X, ∀ g, e (QuotientGroup.mk g) = f g := by
  refine ⟨Equiv.ofBijective (Quotient.lift f fun a b hab =>
    (hf a b).2 (QuotientGroup.leftRel_apply.1 hab)) ⟨?_, ?_⟩, fun g => rfl⟩
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 ((hf a b).1 hxy)
  · intro x
    obtain ⟨g, rfl⟩ := hs x
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem coset_inter_nonempty_iff {G : Type*} [Group G] (H K : Subgroup G) (g h : G) :
    (g • (H : Set G) ∩ h • (K : Set G)).Nonempty ↔ ∃ x, g⁻¹ * x ∈ H ∧ h⁻¹ * x ∈ K := by
  simp only [Set.Nonempty, Set.mem_inter_iff, mem_leftCoset_iff, SetLike.mem_coe]

theorem fst_eq_iff
    (g h : Pc 1) :
    (piTwo g).1 vX = (piTwo h).1 vX ↔ g⁻¹ * h ∈ (Pc 0).subgroupOf (Pc 1) := by
  rw [Pc_zero_subgroupOf, Subgroup.mem_comap, Subgroup.mem_prod, MulAction.mem_stabilizer_iff,
    map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, mul_smul, inv_smul_eq_iff]
  exact ⟨fun e => ⟨e.symm, Subgroup.mem_top _⟩, fun e => e.1.symm⟩

theorem snd_pt_eq_iff
    (g h : Pc 1) :
    (piTwo g).2 • pPt = (piTwo h).2 • pPt ↔ g⁻¹ * h ∈ (Pc 2).subgroupOf (Pc 1) := by
  rw [Pc_two_subgroupOf_Pc_one, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, mul_smul,
    inv_smul_eq_iff]
  exact ⟨fun e => ⟨Subgroup.mem_top _, e.symm⟩, fun e => e.2.symm⟩

theorem snd_ln_eq_iff
    (g h : Pc 1) :
    (piTwo g).2 • ellLine = (piTwo h).2 • ellLine ↔ g⁻¹ * h ∈ (Pc 3).subgroupOf (Pc 1) := by
  rw [Pc_three_subgroupOf_Pc_one, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, mul_smul,
    inv_smul_eq_iff]
  exact ⟨fun e => ⟨Subgroup.mem_top _, e.symm⟩, fun e => e.2.symm⟩

theorem exists_piTwo
    (σ : Equiv.Perm Vsharp) (s : SigmaL3) : ∃ g : Pc 1, piTwo g = (σ, s) :=
  piTwo_surjective (σ, s)

theorem exists_fst_eq
    (v : Vsharp) : ∃ g : Pc 1, (piTwo g).1 vX = v := by
  classical
  obtain ⟨g, hg⟩ := exists_piTwo (Equiv.swap vX v) 1
  exact ⟨g, by rw [hg]; exact Equiv.swap_apply_left vX v⟩

theorem exists_snd_pt_eq
    (x : PlanePoint) : ∃ g : Pc 1, (piTwo g).2 • pPt = x := by
  obtain ⟨s, hs⟩ := exists_smul_pPt x
  obtain ⟨g, hg⟩ := exists_piTwo 1 s
  exact ⟨g, by rw [hg]; exact hs⟩

theorem exists_snd_ln_eq
    {S : Set PlanePoint} (hS : S ∈ planeLines) :
    ∃ g : Pc 1, (piTwo g).2 • ellLine = S := by
  obtain ⟨s, hs⟩ := exists_smul_ellLine hS
  obtain ⟨g, hg⟩ := exists_piTwo 1 s
  exact ⟨g, by rw [hg]; exact hs⟩

theorem exists_equiv_vsharp :
    ∃ e : Pc 1 ⧸ (Pc 0).subgroupOf (Pc 1) ≃ Vsharp,
    ∀ g, e (QuotientGroup.mk g) = (piTwo g).1 vX :=
  exists_quotient_equiv _ (fun g => (piTwo g).1 vX) fst_eq_iff exists_fst_eq

theorem exists_equiv_points :
    ∃ e : Pc 1 ⧸ (Pc 2).subgroupOf (Pc 1) ≃ PlanePoint,
    ∀ g, e (QuotientGroup.mk g) = (piTwo g).2 • pPt :=
  exists_quotient_equiv _ (fun g => (piTwo g).2 • pPt) snd_pt_eq_iff exists_snd_pt_eq

theorem exists_equiv_lines :
    ∃ e : Pc 1 ⧸ (Pc 3).subgroupOf (Pc 1) ≃ planeLines,
    ∀ g, (e (QuotientGroup.mk g) : Set PlanePoint) = (piTwo g).2 • ellLine := by
  obtain ⟨e, he⟩ := exists_quotient_equiv ((Pc 3).subgroupOf (Pc 1))
    (fun g => (⟨(piTwo g).2 • ellLine, smul_mem_planeLines _ ellLine_mem_planeLines⟩ :
      planeLines))
    (fun g h => Subtype.ext_iff.trans (snd_ln_eq_iff g h))
    (fun S => by
      obtain ⟨g, hg⟩ := exists_snd_ln_eq S.2
      exact ⟨g, Subtype.ext hg⟩)
  exact ⟨e, fun g => congrArg Subtype.val (he g)⟩

theorem inter_vsharp_points
    (g h : Pc 1) :
    (g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty := by
  rw [coset_inter_nonempty_iff]
  obtain ⟨x, hx⟩ := exists_piTwo (piTwo g).1 (piTwo h).2
  refine ⟨x, (fst_eq_iff g x).1 ?_, (snd_pt_eq_iff h x).1 ?_⟩ <;> rw [hx]

theorem inter_vsharp_lines
    (g h : Pc 1) :
    (g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty := by
  rw [coset_inter_nonempty_iff]
  obtain ⟨x, hx⟩ := exists_piTwo (piTwo g).1 (piTwo h).2
  refine ⟨x, (fst_eq_iff g x).1 ?_, (snd_ln_eq_iff h x).1 ?_⟩ <;> rw [hx]

theorem inter_points_lines_iff
    (g h : Pc 1) :
    (g • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty ↔
      (piTwo g).2 • pPt ∈ (piTwo h).2 • ellLine := by
  rw [coset_inter_nonempty_iff]
  constructor
  · rintro ⟨x, h1, h2⟩
    rw [(snd_pt_eq_iff g x).2 h1, (snd_ln_eq_iff h x).2 h2]
    exact Set.smul_mem_smul_set pPt_mem_ellLine
  · intro hmem
    obtain ⟨s, hs1, hs2⟩ :=
      exists_smul_flag (smul_mem_planeLines (piTwo h).2 ellLine_mem_planeLines) hmem
    obtain ⟨x, hx⟩ := exists_piTwo 1 s
    refine ⟨x, (snd_pt_eq_iff g x).1 ?_, (snd_ln_eq_iff h x).1 ?_⟩
    · rw [hx]
      exact hs1.symm
    · rw [hx]
      exact hs2.symm

theorem exists_flag
    (v : Vsharp) {x : PlanePoint} {S : Set PlanePoint} (hS : S ∈ planeLines)
    (hx : x ∈ S) : ∃ g : Pc 1, (piTwo g).1 vX = v ∧ (piTwo g).2 • pPt = x ∧
      (piTwo g).2 • ellLine = S := by
  classical
  obtain ⟨s, hs1, hs2⟩ := exists_smul_flag hS hx
  obtain ⟨g, hg⟩ := exists_piTwo (Equiv.swap vX v) s
  refine ⟨g, ?_, ?_, ?_⟩ <;> rw [hg]
  · exact Equiv.swap_apply_left vX v
  · exact hs1
  · exact hs2

theorem exists_chamber
    (a b c : Pc 1)
    (hbc : (b • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      c • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty) :
    ∃ g : Pc 1, a • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) =
        g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∧
      b • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) = g • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∧
      c • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1)) =
        g • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1)) := by
  obtain ⟨g, h1, h2, h3⟩ := exists_flag ((piTwo a).1 vX)
    (smul_mem_planeLines (piTwo c).2 ellLine_mem_planeLines) ((inter_points_lines_iff b c).1 hbc)
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [leftCoset_eq_iff]
    exact (fst_eq_iff a g).1 h1.symm
  · rw [leftCoset_eq_iff]
    exact (snd_pt_eq_iff b g).1 h2.symm
  · rw [leftCoset_eq_iff]
    exact (snd_ln_eq_iff c g).1 h3.symm

theorem commonKernel_eq :
    (⨅ (k : Fin 4) (_ : k ≠ 1) (g : Pc 1),
    ((Pc k).subgroupOf (Pc 1)).map (MulAut.conj g).toMonoidHom) = (Nc 1).subgroupOf (Pc 1) := by
  apply le_antisymm
  · intro x hx
    simp only [Subgroup.mem_iInf] at hx
    have hmem : ∀ k : Fin 4, k ≠ 1 → ∀ g : Pc 1, g⁻¹ * x * g ∈ (Pc k).subgroupOf (Pc 1) := by
      intro k hk g
      have := hx k hk g
      rwa [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
    rw [← ker_piTwo', MonoidHom.mem_ker]
    refine Prod.ext (Equiv.ext fun v => ?_) (eq_one_of_smul_eq _ fun p => ?_)
    · obtain ⟨g, hg⟩ := exists_fst_eq v
      have h0 := (mem_Pc_zero_iff _).1 (Subgroup.mem_subgroupOf.1 (hmem 0 (by decide) g))
      rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv,
        Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, hg] at h0
      exact h0
    · obtain ⟨g, hg⟩ := exists_snd_pt_eq p
      have h2 := (mem_Pc_two_iff _).1 (Subgroup.mem_subgroupOf.1 (hmem 2 (by decide) g))
      rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, mul_smul,
        mul_smul, inv_smul_eq_iff, hg] at h2
      exact h2
  · intro x hx
    rw [← ker_piTwo', MonoidHom.mem_ker] at hx
    simp only [Subgroup.mem_iInf]
    intro k _ g
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_subgroupOf]
    have h1 : g⁻¹ * x * g ∈ piTwo.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hx, mul_one, map_inv, inv_mul_cancel]
    rw [ker_piTwo', Subgroup.mem_subgroupOf] at h1
    exact Nc_le_Pc 1 k h1

theorem short_second_centralizer_product_flag :
    Nat.card Vsharp = 3 ∧ Function.Surjective piTwo ∧
    piTwo.ker = (Nc 1).subgroupOf (Pc 1) ∧ piTwo.ker = CFSG.pCore 2 (Pc 1) ∧
    (∃ e : Pc 1 ⧸ CFSG.pCore 2 (Pc 1) ≃* Equiv.Perm Vsharp × SigmaL3,
      ∀ g, e (QuotientGroup.mk g) = piTwo g) ∧
    (∀ (h : Pc 1) (v : Vsharp),
      (((piTwo h).1 v : Vsharp) : Dfull) = (h : Dfull) * (v : Dfull) * (h : Dfull)⁻¹) ∧
    (∀ (h : Pc 1) (i : NativeCoord),
      (fun d => (h : Dfull) * d * (h : Dfull)⁻¹) '' {d | ∃ v ∈ Vhat, dhat 0 i * v = d} =
        {d | ∃ v ∈ Vhat,
          dhat 0 (Unitary.LinThree.jEquiv.symm ((piTwo h).2 • j i) : Fin 24) * v = d}) ∧
    (Pc 0).subgroupOf (Pc 1) =
      ((MulAction.stabilizer (Equiv.Perm Vsharp) vX).prod ⊤).comap piTwo ∧
    (Pc 2).subgroupOf (Pc 1) =
      ((⊤ : Subgroup (Equiv.Perm Vsharp)).prod (MulAction.stabilizer SigmaL3 pPt)).comap piTwo ∧
    (Pc 3).subgroupOf (Pc 1) =
      ((⊤ : Subgroup (Equiv.Perm Vsharp)).prod (MulAction.stabilizer SigmaL3 ellLine)).comap
        piTwo ∧
    (⨅ (k : Fin 4) (_ : k ≠ 1) (g : Pc 1),
      ((Pc k).subgroupOf (Pc 1)).map (MulAut.conj g).toMonoidHom) = (Nc 1).subgroupOf (Pc 1) ∧
    (∃ e : Pc 1 ⧸ (Pc 0).subgroupOf (Pc 1) ≃ Vsharp,
      ∀ g, e (QuotientGroup.mk g) = (piTwo g).1 vX) ∧
    (∃ e : Pc 1 ⧸ (Pc 2).subgroupOf (Pc 1) ≃ PlanePoint,
      ∀ g, e (QuotientGroup.mk g) = (piTwo g).2 • pPt) ∧
    (∃ e : Pc 1 ⧸ (Pc 3).subgroupOf (Pc 1) ≃ planeLines,
      ∀ g, (e (QuotientGroup.mk g) : Set PlanePoint) = (piTwo g).2 • ellLine) ∧
    (∀ g h : Pc 1, (piTwo (g * h)).1 vX = (piTwo g).1 ((piTwo h).1 vX) ∧
      (piTwo (g * h)).2 • pPt = (piTwo g).2 • ((piTwo h).2 • pPt) ∧
      (piTwo (g * h)).2 • ellLine = (piTwo g).2 • ((piTwo h).2 • ellLine)) ∧
    pPt ∈ ellLine ∧ ellLine ∈ planeLines ∧
    (∀ g h : Pc 1, (g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty) ∧
    (∀ g h : Pc 1, (g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty) ∧
    (∀ g h : Pc 1, (g • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∩
      h • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty ↔
        (piTwo g).2 • pPt ∈ (piTwo h).2 • ellLine) ∧
    (∀ (v : Vsharp) (x : PlanePoint) (S : Set PlanePoint), S ∈ planeLines → x ∈ S →
      ∃ g : Pc 1, (piTwo g).1 vX = v ∧ (piTwo g).2 • pPt = x ∧ (piTwo g).2 • ellLine = S) ∧
    (∀ a b c : Pc 1,
      (a • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
        b • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty →
      (a • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∩
        c • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty →
      (b • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∩
        c • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))).Nonempty →
      ∃ g : Pc 1, a • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) =
          g • ((Pc 0).subgroupOf (Pc 1) : Set (Pc 1)) ∧
        b • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) =
          g • ((Pc 2).subgroupOf (Pc 1) : Set (Pc 1)) ∧
        c • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1)) =
          g • ((Pc 3).subgroupOf (Pc 1) : Set (Pc 1))) := by
  refine ⟨natCard_vsharp, piTwo_surjective, ker_piTwo', ker_piTwo,
    ⟨(QuotientGroup.quotientMulEquivOfEq ker_piTwo.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective piTwo piTwo_surjective), fun g => rfl⟩,
    coe_piTwo_fst, image_conj_block, Pc_zero_subgroupOf, Pc_two_subgroupOf_Pc_one,
    Pc_three_subgroupOf_Pc_one,
    commonKernel_eq, exists_equiv_vsharp, exists_equiv_points, exists_equiv_lines,
    fun g h => ⟨by rw [map_mul]; rfl, by rw [map_mul, Prod.snd_mul, mul_smul],
      by rw [map_mul, Prod.snd_mul, mul_smul]⟩,
    pPt_mem_ellLine, ellLine_mem_planeLines, inter_vsharp_points, inter_vsharp_lines,
    inter_points_lines_iff, fun v _ _ hS hx => exists_flag v hS hx,
    fun a b c _ _ hbc => exists_chamber a b c hbc⟩

end CFSG.Monster.B.TwoA.Amalgam
