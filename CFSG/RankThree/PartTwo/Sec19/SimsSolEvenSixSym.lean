module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSOne
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSTwo
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiDefs
public import CFSG.GF2Type.Smith1979W3.KProper

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

@[expose] def SixSymResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6) (D : C.PiData),
    Nat.card ↥(Rc X) = 2 → Function.Surjective C.θ →
    ∀ (x : G) (hx : x ∈ CFSG.Open.pCoreOf 2 M) (i j : Fin 6), i ≠ j →
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j} → ¬ CGOf x ≤ M →
      CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x →
      Nonempty (↥M ≃* YamakiHat)

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem inCatalog_of_extraspecial
    (hSmith3 : CFSG.GF2Type.Smith1979W3.Smith1979WidthThreeCharTwoKP) {n : ℕ} (C : Cfg G M X n)
    {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hext : IsExtraspecialPGroup 2 ↥(CFSG.Open.pCoreOf 2 (CGOf x)))
    (hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x)) = 2 ^ (1 + 2 * 3)) :
    CFSG.Assembly.InCatalog G := by
  haveI := C.S.simple
  have hF : inSubgroup generalizedFitting (Subgroup.centralizer ({x} : Set G)) =
      CFSG.Open.pCoreOf 2 (CGOf x) := by
    unfold inSubgroup
    rw [C.S.cent x hx hx1]
    show CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = _
    rw [centralizer_singleton_eq_zpowers]
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  rw [← hF] at hext hcard
  exact inCatalog_of_smithThreeConcl
    (hSmith3 G C.S.nonab C.S.charTwo C.S.kProper x hord hext 3 hcard rfl)

theorem inCatalog_of_yamaki (hYamaki : YamakiSp62CharTwo)
    {C : Cfg G M X 6} (D : C.PiData) (hR2 : Nat.card ↥(Rc X) = 2)
    (hsurj : Function.Surjective C.θ) (e : ↥M ≃* YamakiHat) : CFSG.Assembly.InCatalog G := by
  obtain ⟨S, hSM⟩ := exists_sylow_le_M (C := C) hR2 hsurj
  have hR : Nat.card ↥(Rc X) ≤ 2 := hR2.le
  have hRb : Rc X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hR2
    norm_num at hR2
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hord : orderOf r = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Rc_mul_self hR hr) hr1'
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf] at hr
    exact hr.1
  have hQS : CFSG.Open.pCoreOf 2 M ≤ (S : Subgroup G) := by
    have hN : (S : Subgroup G) ≤
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) := by
      rw [C.S.normalizer_Q_eq]
      exact hSM
    have h2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M ⊔ (S : Subgroup G) : Subgroup G) :=
      (isPGroup_pCoreOf' M).to_sup_of_normal_left' S.isPGroup' hN
    rw [← S.is_maximal' h2 le_sup_right]
    exact le_sup_left
  have hcomm : ∀ s ∈ (S : Subgroup G), s * r = r * s := fun s hs => by
    have := C.R_central hR s (hSM hs) r hr
    calc s * r = (s * r * s⁻¹) * s := by group
      _ = r * s := by rw [this]
  have hC : Subgroup.centralizer ({r} : Set G) = M := by
    refine le_antisymm (C.S.centralizer_le_of_mem_R hr hr1') fun m hm => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := C.R_central hR m hm r hr
    calc m * r = (m * r * m⁻¹) * m := by group
      _ = r * m := by rw [this]
  exact inCatalog_of_yamakiCharTwo hYamaki C.S.simple C.S.nonab C.S.charTwo S hord (hQS hrQ)
    hcomm ⟨(MulEquiv.subgroupCongr hC).trans e⟩

end Cfg.PiData

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem inCatalog_of_sym_of_residual
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (hYamaki : YamakiSp62CharTwo)
    (hSmith3 : CFSG.GF2Type.Smith1979W3.Smith1979WidthThreeCharTwoKP) (hRes : SixSymResidual)
    (C : Cfg G M X 6) (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) :
    CFSG.Assembly.InCatalog G := by
  by_cases hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M
  · exact Cfg.PiData.inCatalog_of_centInM_sym hNode C D hR hH
  push Not at hH
  obtain ⟨x, hx, hx1, hxM⟩ := hH
  have hK : ¬ CGOf x ≤ M := fun h => hxM (by rw [centralizer_singleton_eq_zpowers]; exact h)
  have hl : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 2 := by
    by_contra hl
    have h4 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) ≠ 4 := by
      have := SixS.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨x, hx⟩))
      omega
    exact hxM (D.centralizer_le_of_len hR ⟨x, hx⟩ hx1 ⟨hl, h4⟩).1
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨x, hx⟩))
  rw [hl] at hIc
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hIc
  have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  rcases (show Nat.card ↥(Rc X) = 1 ∨ Nat.card ↥(Rc X) = 2 by omega) with hR1 | hR2
  ·
    have hRb : Rc X = ⊥ := Subgroup.card_eq_one.1 hR1
    rcases D.sup_eq_cases hR hsurj hQ hx hij hI hK with h | h | h
    · exact (D.false_of_sup_eq_T2_of_bot hR hsurj hQ hRb hx hij hI hK h).elim
    · exact (D.false_of_sup_eq_T1 hR hsurj hQ hx hij hI hK h).elim
    · obtain ⟨hext, hcard⟩ := D.extraspecial_of_sup_eq_TOf_of_bot hR hsurj hQ hRb hx hij hI hK h
      have hx2 : x * x = 1 := by
        have h1 : D.piQ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
          apply Multiplicative.toAdd.injective
          rw [map_mul, toAdd_mul, toAdd_one, permBar_add_self]
        have h2 := (D.piQ_eq_one_iff _).1 h1
        rw [hRb] at h2
        exact Subgroup.mem_bot.1 h2
      exact Cfg.PiData.inCatalog_of_extraspecial hSmith3 C hx hx1 hx2 hext hcard
  ·
    by_cases hT : ∃ (y : G) (hy : y ∈ CFSG.Open.pCoreOf 2 M) (a b : Fin 6), a ≠ b ∧
        Multiplicative.toAdd (D.piQ ⟨y, hy⟩) = barInd {a, b} ∧ ¬ CGOf y ≤ M ∧
        CFSG.Open.pCoreOf 2 (CGOf y) ⊔ CFSG.Open.pCoreOf 2 M = TOf M y
    · obtain ⟨y, hy, a, b, hab, hπy, hKy, hPy⟩ := hT
      obtain ⟨e⟩ := hRes G M X C D hR2 hsurj y hy a b hab hπy hKy hPy
      exact D.inCatalog_of_yamaki hYamaki hR2 hsurj e
    · push Not at hT
      exfalso
      refine D.false_of_forall_sup_eq_T2 hR2 hsurj hQ (fun y hy a b hab hπy hKy => ?_) hx hij hI
        hK
      rcases D.sup_eq_cases hR hsurj hQ hy hab hπy hKy with h | h | h
      · exact h
      · exact (D.false_of_sup_eq_T1 hR hsurj hQ hy hab hπy hKy h).elim
      · exact absurd h (hT y hy a b hab hπy hKy)

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
