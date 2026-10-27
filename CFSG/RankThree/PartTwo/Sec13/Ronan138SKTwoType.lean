module

public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree ModNine IsTypeC Type123)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

section Acts

variable {X : Type*} [Group X] {K : Type} [Field K] {M : Subgroup (ProjGenLinGroup (Fin 3) K)}

theorem acts_mul (φ : X ≃* M) {τ₁ τ₂ : MulAut X} {Y₁ Y₂ : ProjGenLinGroup (Fin 3) K}
    (h₁ : ∀ z, (φ (τ₁ z) : ProjGenLinGroup (Fin 3) K) = Y₁ * φ z * Y₁⁻¹)
    (h₂ : ∀ z, (φ (τ₂ z) : ProjGenLinGroup (Fin 3) K) = Y₂ * φ z * Y₂⁻¹) (z : X) :
    (φ ((τ₁ * τ₂) z) : ProjGenLinGroup (Fin 3) K) = (Y₁ * Y₂) * φ z * (Y₁ * Y₂)⁻¹ := by
  rw [MulAut.mul_apply, h₁, h₂]
  group

theorem acts_inv (φ : X ≃* M) {τ : MulAut X} {Y : ProjGenLinGroup (Fin 3) K}
    (h : ∀ z, (φ (τ z) : ProjGenLinGroup (Fin 3) K) = Y * φ z * Y⁻¹) (z : X) :
    (φ (τ⁻¹ z) : ProjGenLinGroup (Fin 3) K) = Y⁻¹ * φ z * Y⁻¹⁻¹ := by
  have h1 := h (τ⁻¹ z)
  rw [MulAut.apply_inv_self] at h1
  rw [h1]
  group

theorem eq_one_of_acts_one (φ : X ≃* M) {τ : MulAut X}
    (h : ∀ z, (φ (τ z) : ProjGenLinGroup (Fin 3) K) = 1 * φ z * 1⁻¹) : τ = 1 := by
  ext z
  apply φ.injective
  apply Subtype.ext
  rw [h z, MulAut.one_apply]
  group

variable {π : Bool} {p f : ℕ}

theorem inv_mul_mem_statedScalars_of_acts (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (φ : X ≃* projImage (slPi π 3 (p ^ f) K)) {τ : MulAut X}
    {y y' : GL (Fin 3) K}
    (h : ∀ z, (φ (τ z) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y * φ z * (ProjGenLinGroup.mk y)⁻¹)
    (h' : ∀ z, (φ (τ z) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y' * φ z * (ProjGenLinGroup.mk y')⁻¹) :
    y⁻¹ * y' ∈ StatedScalars (Fin 3) K := by
  refine Sec13.mem_statedScalars_of_commute_mk hK hq hq2 fun s hs => ?_
  set z := φ.symm ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩ with hz
  have hφz : (φ z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s := by
    rw [hz, MulEquiv.apply_symm_apply]
  have h1 := (h z).symm.trans (h' z)
  rw [hφz] at h1
  rw [map_mul, map_inv]
  calc (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s
      = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk y')⁻¹) * ProjGenLinGroup.mk y' := by group
    _ = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk y' := by rw [← h1]
    _ = ProjGenLinGroup.mk s * ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y') := by group

end Acts

section Types

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_thetaQuotMulAut_eq_one {E L : Subgroup G} {c : G}
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hCE : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G)) {w : G} (hwE : w ∈ E)
    (hw : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hEN hwE⟩) = 1) :
    w ∈ Subgroup.zpowers c := by
  have h1 : w ∈ Sec4.thetaQuotCentralizer L :=
    Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨hEN hwE, hw⟩
  have h2 : w ∈ ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hwE, h1⟩
  rw [← sectionCentralizer_eq_inf hEN, hCE] at h2
  exact h2

theorem not_modNine_of_typeC {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec13Data G A c L) (hcE : c ∈ E) (hE3 : CFSG.Assembly.IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E))
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D)
    (hτD : ∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ¬ ModNine π (p ^ f) := by
  intro h9
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  have hinn : ∀ e' ∈ E, ∀ hN : e' ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e', hN⟩) z = w * z * w⁻¹ := by
    intro e' he' hN
    obtain ⟨y, hy, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨e', hN, he', rfl⟩)
    exact exists_conj_eq_of_isTypeC hK hq h9 φ hD hy hyz
  exact false_of_inner_of_isZ3PGLThreePi h hEN hEH hEc
    (fun x hx => exists_lBar_conj_eq_of_inner h.mem_thetaComponentsAt hEN hEH hinn hx) hPGL

theorem type123_two_of_not_mem {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec13Data G A c L) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hCE : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G))
    {d : G} (hdE : d ∈ E) (hdL : d ∈ L) (hd1 : d ≠ 1)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ ModNine π (p ^ f))
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K))
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D)
    (hτD : ∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    {e : G} (heE : e ∈ E) (he : e ∉ Subgroup.zpowers c ⊔ (E ⊓ L)) {y : GL (Fin 3) K}
    (hyD : y ∈ D)
    (hy : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) z) :
        ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    Type123 π (p ^ f) K y 2 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hL := h.mem_thetaComponentsAt
  have hq2 := Item138Proof.two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL)
    hK hq φ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hZL := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZL
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hEN hdE
  obtain ⟨yd, hydD, hyd⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨d, hdN, hdE, rfl⟩)
  have hy1 : ProjGenLinGroup.mk y ≠ 1 := by
    intro h1
    apply he
    refine Subgroup.mem_sup_left (mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE heE
      (eq_one_of_acts_one φ fun z => ?_))
    rw [hy z, h1]
  have hyd1 : ProjGenLinGroup.mk yd ≠ 1 := by
    intro h1
    have hdc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE hdE
      (eq_one_of_acts_one φ fun z => by rw [hyd z, h1])
    apply hd1
    have hmem : d ∈ Subgroup.zpowers c ⊓ L := Subgroup.mem_inf.mpr ⟨hdc, hdL⟩
    rw [zpowers_inf_eq_bot hc3 hcL] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨N, hN, hNd⟩ := (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩)).2
  have hτd : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) z) :
        ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk N * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk N)⁻¹ := by
    intro z
    rw [show Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) from
      KFacts.thetaQuotMulAut_compAction_of_mem hdL hdN, MulAut.conj_apply, map_mul, map_mul,
      map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hNd]
  have hsc := inv_mul_mem_statedScalars_of_acts hK hq hq2 φ hτd hyd
  have hinner : ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K,
      yd * m * yd⁻¹ = l * m * l⁻¹ := by
    refine ⟨N, hN, fun m _ => ?_⟩
    have hc := Sec4.commute_of_mem_statedScalars hsc m
    calc yd * m * yd⁻¹ = N * ((N⁻¹ * yd) * m) * (N⁻¹ * yd)⁻¹ * N⁻¹ := by group
      _ = N * (m * (N⁻¹ * yd)) * (N⁻¹ * yd)⁻¹ * N⁻¹ := by rw [← hc]
      _ = N * m * N⁻¹ := by group
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hydH : yd ∈ glPi π 3 (p ^ f) K := hD.1 hydD
  have hydsc : yd ∉ StatedScalars (Fin 3) K := fun h =>
    hyd1 (Sec4.mk_eq_one_iff_mem_statedScalars.mpr h)
  have hysc : y ∉ StatedScalars (Fin 3) K := fun h =>
    hy1 (Sec4.mk_eq_one_iff_mem_statedScalars.mpr h)
  have hydZ : yd ∉ zPi π 3 (p ^ f) K := fun hz => by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz
    exact hydsc hz.2
  have hyd3 : yd ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hydH 3, hD.2.1 yd hydD⟩
  have hydT : Type123 π (p ^ f) K yd 1 := by
    rcases (Sec4.rank3II_4_10_two hK hq hτ hτ1 hydH hydZ hyd3).mp hinner with
      ⟨_, ⟨z, hz, rfl⟩, g, hg, hD'⟩ | ⟨-, h9'⟩
    · exact ⟨τ, hτ, hτ1, z, hz, g, hg, hD'⟩
    · exact absurd h9' h9
  obtain ⟨a₁, -, -, htypes⟩ := Sec4.isTypeC_types hK hq hD
  refine (htypes y hyD hysc).2 fun hyT => ?_
  have key : ∀ x : GL (Fin 3) K,
      (x * a₁⁻¹ ∈ StatedScalars (Fin 3) K ∨ x * a₁ ∈ StatedScalars (Fin 3) K) →
      (ProjGenLinGroup.mk x = ProjGenLinGroup.mk a₁ ∨
        ProjGenLinGroup.mk x = (ProjGenLinGroup.mk a₁)⁻¹) := by
    rintro x (hx | hx)
    · left
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, mul_inv_eq_one] at hx
      exact hx
    · right
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, mul_eq_one_iff_eq_inv] at hx
      exact hx
  have hcomb : ProjGenLinGroup.mk y = ProjGenLinGroup.mk yd ∨
      ProjGenLinGroup.mk y = (ProjGenLinGroup.mk yd)⁻¹ := by
    rcases key y ((htypes y hyD hysc).1.mp hyT) with hY | hY <;>
      rcases key yd ((htypes yd hydD hydsc).1.mp hydT) with hYd | hYd
    · exact Or.inl (by rw [hY, hYd])
    · exact Or.inr (by rw [hY, hYd, inv_inv])
    · exact Or.inr (by rw [hY, hYd])
    · exact Or.inl (by rw [hY, hYd])
  apply he
  have hdEL : d ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨hdE, hdL⟩
  rcases hcomb with hc | hc
  ·
    have hw : Sec4.thetaQuotMulAut L
        (L.normalizerMonoidHom ⟨e * d⁻¹, hEN (mul_mem heE (inv_mem hdE))⟩) = 1 := by
      have hsplit : Sec4.thetaQuotMulAut L
          (L.normalizerMonoidHom ⟨e * d⁻¹, hEN (mul_mem heE (inv_mem hdE))⟩) =
          Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) *
            (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩))⁻¹ := by
        have h1 := map_mul ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨e, hEN heE⟩
          (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G))⁻¹
        rw [map_inv] at h1
        exact h1
      rw [hsplit]
      refine eq_one_of_acts_one φ fun z => ?_
      rw [acts_mul φ hy (acts_inv φ hyd) z, hc, mul_inv_cancel]
    have hwc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE (mul_mem heE (inv_mem hdE)) hw
    rw [show e = e * d⁻¹ * d by group]
    exact mul_mem (Subgroup.mem_sup_left hwc) (Subgroup.mem_sup_right hdEL)
  ·
    have hw : Sec4.thetaQuotMulAut L
        (L.normalizerMonoidHom ⟨e * d, hEN (mul_mem heE hdE)⟩) = 1 := by
      have hsplit : Sec4.thetaQuotMulAut L
          (L.normalizerMonoidHom ⟨e * d, hEN (mul_mem heE hdE)⟩) =
          Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hEN heE⟩) *
            Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) := by
        have h1 := map_mul ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨e, hEN heE⟩
          ⟨d, hdN⟩
        exact h1
      rw [hsplit]
      refine eq_one_of_acts_one φ fun z => ?_
      rw [acts_mul φ hy hyd z, hc, inv_mul_cancel]
    have hwc := mem_zpowers_of_thetaQuotMulAut_eq_one hEN hCE (mul_mem heE hdE) hw
    rw [show e = e * d * d⁻¹ by group]
    exact mul_mem (Subgroup.mem_sup_left hwc) (Subgroup.mem_sup_right (inv_mem hdEL))

end Types

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
