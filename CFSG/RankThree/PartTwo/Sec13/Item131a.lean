module

public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec11.Statements
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Item131a

variable {G : Type} [Group G] [Finite G]

@[expose] def Item131a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      (Sec8.IsZ3LThreePi (lBarA c L A) ∧
          (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
            Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
      (Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
          Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, Sec4.InducesTypeOn L x 3) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
          Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M22) ∧
          Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) ∧
          Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      Sec4.IsSLThreePiTwo (lBarA c L A) ∨
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
          (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
              CFSG.Blueprint.NativeSporadic.M22))

theorem mem_lStarAt_of_sec13Data {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    L ∈ lStarAt A c := by
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  have hle : A ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers c := fun x hx => by
    have : x ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := hx
    rw [hsc] at this
    exact this
  exact ⟨Sec6.mem_lStar_of_inf_le_zpowers hD.isElemAbelian hD.mem_A hD.ne_one
    hD.mem_thetaComponentsAt hD.le_normalizer hle, hD.mem_thetaComponentsAt⟩

theorem card_autThetaQuot_eq_nine {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    Nat.card (Sec4.autThetaQuot A L) = 9 := by
  have h := card_inf_mul_card_autThetaQuot hD.le_normalizer
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  have heq : (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = Subgroup.zpowers c :=
    SetLike.coe_injective hsc
  have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [heq, hD.card_zpowers]
  rw [h3, hD.card_eq] at h
  omega

theorem rank3II_13_1a_of
    (h423 : Sec4.Item4_23) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hK : KS131AlphaInvolutionCentral) (hgap : Gap131Hyp1134)
    (h1134 : Sec11.Item1134E27) : Item131a := by
  intro G _ _ A c L hD
  have hαC := thetaAlpha_autThetaQuot_centralizer_ne_bot_of_central h422 h45 hK hD
  have hst := hD.toPartTwoStanding
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hc1 := hD.ne_one
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz => hD.commute hy hz
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha c hcA)
  have hLC : L ≤ C := hD.le_centralizer
  have hFE := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  have hAF : A ∈ partTwoF G := hD.mem_partTwoF
  have hmax : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'e, fun B hB hAB => ?_⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := x
        obtain ⟨_, y, hy, rfl⟩ := y
        apply Subtype.ext
        change (x : G) * y = y * x
        exact congrArg Subtype.val
          (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hB.2 x hx)
    have hAB' : A ≤ B.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hBA := hAF.2.1 _ hBe hAB'
    intro x hx
    have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨L', hL', hL'L₀⟩ := hD.mem_thetaComponentsAt
  have hL'L : L'.map C.subtype = L := hL'L₀
  have hL'eq : L' = L.subgroupOf C := by
    rw [← hL'L]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective L').symm
  have h9 : Nat.card (Sec4.autThetaQuot A' L') = 9 := by
    have := card_autThetaQuot_eq_nine hD
    rw [← hA'map, ← hL'L, ← map_autThetaQuot_sub C A' L',
      Subgroup.card_map_of_injective (MulAut.congr (thetaQuotEquivSub C L')).injective] at this
    exact this
  have hα' : thetaAlpha 3 ((Sec4.autThetaQuot A' L').subgroupOf (Sec4.autThetaQuot ⊤ L')) ≠ ⊥ := by
    rw [← thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (thetaQuotEquivSub C L'))
      (Sec4.autThetaQuot A' L') (Sec4.autThetaQuot ⊤ L'), map_autThetaQuot_sub,
      map_autThetaQuot_sub, hA'map, hL'L]
    have hC' : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hC']
    exact hαC
  obtain ⟨eImg⟩ := nonempty_thetaImage_equiv_lBarA (c := c) hLC hAC
  have eImg' : Nonempty (Sec4.thetaImage (L' ⊔ A') ≃* lBarA c L A) := by
    rw [hL'eq]
    exact ⟨eImg⟩
  obtain ⟨eI⟩ := eImg'
  obtain ⟨eAut⟩ := nonempty_autIn_subgroupOf_equiv C hLC hAC
  have eAut' : Nonempty (Sec4.autIn L' A' ≃* Sec4.autIn L A) := by
    rw [hL'eq]
    exact ⟨eAut⟩
  obtain ⟨eA⟩ := eAut'
  set eL := thetaQuotEquivSub C L' with heL
  have hLL : L'.map C.subtype = L := hL'L
  rcases h423 C hS4 A' hmax h27' c' hc'A hc'Z hc'1 L' hL' h9 hα' with
    ⟨hZ3, hQ⟩ | ⟨hPGL, ⟨eZ3⟩, a, haA, -, ha3⟩ | ⟨hHeis, hcase, -⟩ | ⟨hSL2, -⟩ |
      ⟨⟨eA7⟩, ⟨eZ4⟩⟩ | ⟨⟨eM22⟩, ⟨eQ⟩⟩ | ⟨hMJ, ⟨eS3⟩⟩ | ⟨a, haA, ha1, hk⟩
  · refine Or.inl ⟨isZ3LThreePi_of_mulEquiv eI hZ3, ?_⟩
    rcases hQ with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨eA.symm.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨eA.symm.trans e⟩
  · refine Or.inr (Or.inl ⟨isZ3PGLThreePi_of_mulEquiv eI hPGL, ⟨eA.symm.trans eZ3⟩,
      (a : G), Subgroup.mem_subgroupOf.mp haA, ?_⟩)
    have := inducesTypeOn_sub C L' ha3
    rwa [hLL] at this
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))))
    · have := isHeisCentral_of_mulEquiv eI eL hHeis
      rwa [hLL] at this
    · rcases hcase with h | h | h
      · exact Or.inr (Or.inl (by
          have := isTripleCover_of_mulEquiv eL h
          rwa [hLL] at this))
      · exact Or.inr (Or.inr (by
          have := isTripleCover_of_mulEquiv eL h
          rwa [hLL] at this))
      · exact Or.inl (by
          have := isSLThreePi_of_mulEquiv eL h
          rwa [hLL] at this)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isSLThreePiTwo_of_mulEquiv eI hSL2)))))))
  · exact Or.inr (Or.inr (Or.inl ⟨⟨eI.symm.trans eA7⟩, ⟨eA.symm.trans eZ4⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨eI.symm.trans eM22⟩, ⟨eA.symm.trans eQ⟩⟩)))
  · rcases hMJ with he | he
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨eI.symm.trans e⟩, ⟨eA.symm.trans eS3⟩⟩))))
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨⟨eI.symm.trans e⟩, ⟨eA.symm.trans eS3⟩⟩)))))
  ·
    exfalso
    have hsc := hD.sectionCentralizer_eq
    have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
    have hk' : KFacts.InducesStdKind L (a : G) .field ∨
        KFacts.InducesStdKind L (a : G) .graphField := by
      rcases hk with hk | hk
      · have := inducesStdKind_sub C L' hk
        rw [hLL] at this
        exact Or.inl this
      · have := inducesStdKind_sub C L' hk
        rw [hLL] at this
        exact Or.inr this
    have hhyp : (∃ E ∈ partTwoE G, E ≤ A ∧ Sec8.InvTwoBarNontrivial E L) ∨
        (Nat.card A = 27 ∧ ∃ A₁ : Subgroup G, A₁ ≤ A ∧ Nat.card A = 3 * Nat.card A₁ ∧ c ∈ A₁ ∧
          ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A₁ : Set G)), A⁆ ≤
            Sec4.thetaQuotCentralizer L) := by
      rcases hgap G A c L hD hαC (a : G) haA' (fun h => ha1 (Subtype.ext h)) hk' with h | h
      · exact Or.inl ⟨A, hD.mem_partTwoE, le_rfl, h⟩
      · exact Or.inr ⟨h27, h⟩
    have h1134' := h1134 G A c L hst hAF hD.not_mem_partTwoT h27 hcA hc1
      (mem_lStarAt_of_sec13Data hD) hsc hhyp (fun _ => hFE.symm) (a : G) haA'
    rcases hk' with hk' | hk'
    · exact h1134'.1 hk'
    · exact h1134'.2 hk'

end Item131a

end CFSG.RankThree.PartTwo.Sec13
