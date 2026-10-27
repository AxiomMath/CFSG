module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightQ
public import CFSG.LocalAnalysis.WeakClosure81.W19KNorm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_right_of_le_normalizer {A E : Subgroup G}
    (h : A ≤ normalizer (E : Set G)) : ⁅A, E⁆ ≤ E := by
  refine Subgroup.commutator_le.2 fun a ha e he => ?_
  rw [commutatorElement_def]
  exact E.mul_mem ((Subgroup.mem_normalizer_iff.1 (h ha) e).1 he) (E.inv_mem he)

theorem isElemAbelian_mul_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))

namespace Hyp197

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X E F : Subgroup G} {g : G}

theorem not_le_centralizerQuot (h : Hyp197 D V X E F g) :
    ¬ conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F := by
  intro hA
  apply h.comm_ne
  refine Subgroup.commutator_le.2 fun x hx a ha => ?_
  have hxH : x ∈ X ⊔ D.T := twoResidual_le _ hx
  have h1 : x * a * x⁻¹ ∈ centralizerQuot (X ⊔ D.T) E F :=
    (Subgroup.mem_normalizer_iff.1 (h.normalizer_centralizerQuot hxH) a).1 (hA ha)
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hA ha))

theorem not_comm_le_F (h : Hyp197 D V X E F g) : ¬ ⁅conjSubgroup V g, E⁆ ≤ F := by
  intro hAF
  apply h.not_le_centralizerQuot
  intro a ha
  exact ⟨h.A_le_H ha, h.A_le_normalizer_F ha, fun e he =>
    hAF (Subgroup.commutator_mem_commutator ha he)⟩

theorem comm_ne_bot (h : Hyp197 D V X E F g) : ⁅conjSubgroup V g, E⁆ ≠ ⊥ := fun hb =>
  h.not_comm_le_F (hb ▸ bot_le)

theorem exists_gamma_eB_eq (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g)
    (hidx : ((conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).subgroupOf
      (conjSubgroup V g)).index ≤ 2) :
    ∃ B ∈ E3.gammaSet V 1 (conjSubgroup V g), eB E F B = E := by
  have hA2 : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup c.isPGroup_V g
  have hBA : conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F ≤ conjSubgroup V g := inf_le_left
  have hrel := E3.relIndex_eq_two_pow hA2
    (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F)
  have hm0 : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F) ≠ 0 := by
    intro h0
    have := (E3.mQuot_eq_zero_iff hA2 hBA).1 h0
    exact h.not_le_centralizerQuot (this ▸ inf_le_right)
  have hm1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F)
      = 1 := by
    by_contra hne
    have h2 : 2 ≤ E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F) := by omega
    have h3 : 2 ^ 2 ≤ 2 ^ E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F) := Nat.pow_le_pow_right (by norm_num) h2
    have h4 : (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).relIndex (conjSubgroup V g) ≤ 2 :=
      hidx
    omega
  refine ⟨_, (c.mem_gammaSet_one_iff).2 ⟨hBA, hm1⟩, eB_eq_of_forall fun e he b hb => ?_⟩
  have hbe : ⁅b, e⁆ ∈ F := hb.2.2.2 e he
  rw [← commutatorElement_inv]
  exact F.inv_mem hbe

end Hyp197

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem false_of_eB_eq (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : ∀ (g : G) (K : Subgroup G), Conf196 D V X g K →
      Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) = p)
    {E F : Subgroup G} {g : G} (h : Hyp197 D V X E F g) {B : Subgroup G}
    (hB : B ∈ E3.gammaSet V 1 (conjSubgroup V g)) (hBE : eB E F B = E)
    (hs1 : ⁅conjSubgroup V g, eB E F B⁆ ≤ conjSubgroup V₀ g) : False := by
  obtain ⟨hBA, hmB⟩ := (c.mem_gammaSet_one_iff).1 hB
  have hA2 : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup c.isPGroup_V g
  have hne : E ⊓ conjSubgroup V₀ g ≠ ⊥ := by
    intro hbot
    apply h.comm_ne_bot
    have h1 : ⁅conjSubgroup V g, E⁆ ≤ E ⊓ conjSubgroup V₀ g :=
      le_inf (commutator_le_right_of_le_normalizer h.A_le_normalizer_E) (hBE ▸ hs1)
    rwa [hbot, le_bot_iff] at h1
  have hC := h.centralizerQuot_eq_pCoreOf c h162 hne
  have hBO : B ≤ pCoreOf 2 (X ⊔ D.T) := by
    rw [← hC]
    intro b hb
    refine ⟨h.A_le_H (hBA hb), h.A_le_normalizer_F (hBA hb), fun e he => ?_⟩
    have he' : e ∈ eB E F B := by rw [hBE]; exact he
    have h1 := ((mem_eB_iff h.F_le fun x hx y hy => isElemAbelian_mul_comm h.isElemAbelian hx hy).1
      he').2 b hb
    rw [← commutatorElement_inv]
    exact F.inv_mem h1
  have hAO : ¬ conjSubgroup V g ≤ pCoreOf 2 (X ⊔ D.T) := fun hle =>
    h.not_le_centralizerQuot (hle.trans (h.pCoreOf_le_centralizerQuot c))
  have hBle : B ≤ pCoreOf 2 (X ⊔ D.T) ⊓ conjSubgroup V g := le_inf hBO hBA
  have hrel : B.relIndex (conjSubgroup V g) = 2 := by
    rw [E3.relIndex_eq_two_pow hA2, hmB, pow_one]
  have hmul := Subgroup.relIndex_mul_relIndex B (pCoreOf 2 (X ⊔ D.T) ⊓ conjSubgroup V g)
    (conjSubgroup V g) hBle inf_le_right
  rw [hrel, Subgroup.inf_relIndex_right] at hmul
  have hne1 : (pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) ≠ 1 := fun h1 =>
    hAO (Subgroup.relIndex_eq_one.1 h1)
  have hA2' : (pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) = 2 := by
    have hd : (pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) ∣ 2 := Dvd.intro_left _ hmul
    exact ((Nat.dvd_prime Nat.prime_two).1 hd).resolve_left hne1
  obtain ⟨K, hK, hXJ⟩ := c.exists_conf196_le_J h.le_T hA2' (h.not_comm_le_pCoreOf c)
  have hcard := h4 g K hK
  rw [inf_eq_left.2 hXJ] at hcard
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  exact c.hyp.noncyclic (isCyclic_of_prime_card hcard)

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
