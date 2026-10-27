module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7HighRadicalComm
import CFSG.LocalAnalysis.StandardType.FS81.S7ModuleNontrivial
import CFSG.LocalAnalysis.StandardType.FS81.E7RecogIrr
import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)
local notation "J₇" => EPilot.perpLevi Tag.E7 (ZMod 2)

private abbrev E7G : Type := ↥(adjointGroup Tag.E7 (ZMod 2))

private theorem conj_mem_zpowers_eq_self {G : Type*} [Group G] {a h z : G}
    (hh : h ∈ Subgroup.centralizer ({a} : Set G)) (hz : z ∈ Subgroup.zpowers a) :
    h * z * h⁻¹ = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 hh) k).mul_inv_cancel

section E7Model


private theorem s7_mem_Q7 : s₇ ∈ Q₇ := by
  have hθ : highRoot .E7 ∈ parabolicRadicalRoots .E7 (EPilot.perpNodes .E7) :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).2
      ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)

private theorem not_Q7_le_centralizer_Q7 :
    ¬ Q₇ ≤ Subgroup.centralizer (Q₇ : Set E7G) := by
  intro h
  have hα : IsRoot .E7 (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) := isRoot_single _ _
  have hβ : IsRoot .E7 (highRoot .E7 - (Pi.single 0 1 : Fin Tag.E7.rank → ℤ)) :=
    mem_rootFinset.1 (by decide +kernel)
  have hmemR : ∀ δ : Fin Tag.E7.rank → ℤ, IsRoot .E7 δ →
      0 < CFSG.LieType.Steinberg.Adjoint.iform δ (highRoot .E7) →
      EPilot.pinnedElt .E7 δ (1 : ZMod 2) ∈ Q₇ := fun δ hδ hpos =>
    Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan
      ((EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).2
        ⟨hδ, hpos⟩) 1)
  have hA := hmemR _ hβ (by decide +kernel)
  have hB := hmemR _ hα (by decide +kernel)
  have hcomm := Subgroup.mem_centralizer_iff.1 (h hB) _ hA
  have hcomm' : pinnedX .E7 (ZMod 2)
        (highRoot .E7 - (Pi.single 0 1 : Fin Tag.E7.rank → ℤ)) 1 *
      pinnedX .E7 (ZMod 2) (Pi.single 0 1) 1 =
      pinnedX .E7 (ZMod 2) (Pi.single 0 1) 1 *
        pinnedX .E7 (ZMod 2)
          (highRoot .E7 - (Pi.single 0 1 : Fin Tag.E7.rank → ℤ)) 1 := by
    have := congrArg Subtype.val hcomm
    simpa only [Subgroup.coe_mul] using this
  have hform := commutatorElement_pinnedX_of_oddDerivLaced (R := ZMod 2)
    (CharP.cast_eq_zero (ZMod 2) 2)
    (oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl)))) hβ hα
    (by decide +kernel) (by decide +kernel)
    (by rw [sub_add_cancel]; exact isRoot_highRoot _) (1 : ZMod 2) 1
  rw [sub_add_cancel, one_mul, commutatorElement_def, hcomm', mul_inv_cancel_right,
    mul_inv_cancel] at hform
  have hx : EPilot.pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) = 1 := Subtype.ext hform.symm
  have h2 := orderOf_pinnedElt_one (τ := .E7) (K := ZMod 2) (highRoot .E7)
  rw [hx, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem Q7_inf_centralizer_eq_zpowers :
    Q₇ ⊓ Subgroup.centralizer (Q₇ : Set E7G) = Subgroup.zpowers s₇ := by
  obtain ⟨-, hC, -, hLQ⟩ := EPilot.isTwoRadicalDecomp_highRoot (K := ZMod 2)
    (Or.inr (Or.inl rfl)) (one_ne_zero : (1 : ZMod 2) ≠ 0)
  have htQ : s₇ ∈ Q₇ := s7_mem_Q7
  have hQt : Q₇ ≤ Subgroup.centralizer ({s₇} : Set E7G) := by
    rw [← hC]
    exact le_sup_left
  have htZ : s₇ ∈ Q₇ ⊓ Subgroup.centralizer (Q₇ : Set E7G) :=
    ⟨htQ, Subgroup.mem_centralizer_iff.2 fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.1 (hQt hq)⟩
  rcases e7ModelIrr_holds (Q₇ ⊓ Subgroup.centralizer (Q₇ : Set E7G))
      (Subgroup.zpowers_le.2 htZ) inf_le_left
      (fun d hd => mem_normalizer_inf_centralizer (hLQ hd)) with h | h
  · exact h
  · exact absurd (h.symm.le.trans inf_le_right) not_Q7_le_centralizer_Q7

theorem mem_zpowers_of_centralizes_highRadical_E7 (x : ↥(adjointGroup .E7 (ZMod 2)))
    (hx : ∀ y ∈ Q₇, x * y = y * x) : x ∈ Subgroup.zpowers s₇ := by
  obtain ⟨-, hC, -, hLQ⟩ := EPilot.isTwoRadicalDecomp_highRoot (K := ZMod 2)
    (Or.inr (Or.inl rfl)) (one_ne_zero : (1 : ZMod 2) ≠ 0)
  have hsQ : s₇ ∈ Q₇ := s7_mem_Q7
  have hJcent : J₇ ≤ Subgroup.centralizer ({s₇} : Set E7G) := by
    rw [← hC]
    exact le_sup_right
  have hxZ : x ∈ Subgroup.centralizer ({s₇} : Set E7G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hx s₇ hsQ)
  have hxsup : x ∈ J₇ ⊔ Q₇ := by
    rw [sup_comm, hC]
    exact hxZ
  have hx' : x ∈ ((J₇ ⊔ Q₇ : Subgroup E7G) : Set E7G) := hxsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J₇ Q₇ hLQ] at hx'
  obtain ⟨j, hj, q, hq, rfl⟩ := hx'
  have hjtriv : ∀ y ∈ Q₇, j * y * j⁻¹ * y⁻¹ ∈ Subgroup.zpowers s₇ := by
    intro y hy
    have hqy : q⁻¹ * y * q ∈ Q₇ :=
      Subgroup.mul_mem Q₇ (Subgroup.mul_mem Q₇ (Subgroup.inv_mem Q₇ hq) hy) hq
    have hxC : (j * q) * (q⁻¹ * y * q) * (j * q)⁻¹ = q⁻¹ * y * q := by
      rw [hx (q⁻¹ * y * q) hqy]
      group
    have hconj : j * y * j⁻¹ = q⁻¹ * y * q := by
      calc j * y * j⁻¹ = (j * q) * (q⁻¹ * y * q) * (j * q)⁻¹ := by group
        _ = q⁻¹ * y * q := hxC
    have hcommq : q⁻¹ * y * q * y⁻¹ ∈ Subgroup.zpowers s₇ := by
      have h := commutator_highRadical_le_zpowers (τ := .E7) (Or.inl rfl) (K := ZMod 2)
        (by simp [ZMod.card]) q⁻¹ (Subgroup.inv_mem Q₇ hq) y hy
      simpa using h
    rw [hconj]
    exact hcommq
  let N : Subgroup ↥J₇ :=
    { carrier := {g : ↥J₇ |
        ∀ y ∈ Q₇, (g : E7G) * y * (g : E7G)⁻¹ * y⁻¹ ∈ Subgroup.zpowers s₇}
      mul_mem' := by
        intro g g' hg hg' y hy
        have hZ' : (g' : E7G) * y * (g' : E7G)⁻¹ * y⁻¹ ∈ Subgroup.zpowers s₇ := hg' y hy
        have hZ : (g : E7G) * y * (g : E7G)⁻¹ * y⁻¹ ∈ Subgroup.zpowers s₇ := hg y hy
        have hfix : (g : E7G) * ((g' : E7G) * y * (g' : E7G)⁻¹ * y⁻¹) * (g : E7G)⁻¹ =
            (g' : E7G) * y * (g' : E7G)⁻¹ * y⁻¹ :=
          conj_mem_zpowers_eq_self (hJcent g.2) hZ'
        have heq : ((g * g' : ↥J₇) : E7G) * y * ((g * g' : ↥J₇) : E7G)⁻¹ * y⁻¹ =
            ((g' : E7G) * y * (g' : E7G)⁻¹ * y⁻¹) *
              ((g : E7G) * y * (g : E7G)⁻¹ * y⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          rw [show (g : E7G) * (g' : E7G) * y * ((g' : E7G)⁻¹ * (g : E7G)⁻¹) * y⁻¹ =
              (g : E7G) * ((g' : E7G) * y * (g' : E7G)⁻¹ * y⁻¹) * (g : E7G)⁻¹ *
                ((g : E7G) * y * (g : E7G)⁻¹ * y⁻¹) from by group]
          rw [hfix]
        rw [heq]
        exact (Subgroup.zpowers s₇).mul_mem hZ' hZ
      one_mem' := by
        intro y hy
        simp
      inv_mem' := by
        intro g hg y hy
        have hZ : (g : E7G) * y * (g : E7G)⁻¹ * y⁻¹ ∈ Subgroup.zpowers s₇ := hg y hy
        have hfix : (g : E7G)⁻¹ * ((g : E7G) * y * (g : E7G)⁻¹ * y⁻¹)⁻¹ *
              (g : E7G)⁻¹⁻¹ = ((g : E7G) * y * (g : E7G)⁻¹ * y⁻¹)⁻¹ :=
          conj_mem_zpowers_eq_self (hJcent (Subgroup.inv_mem J₇ g.2)) (Subgroup.inv_mem _ hZ)
        have heq : ((g⁻¹ : ↥J₇) : E7G) * y * ((g⁻¹ : ↥J₇) : E7G)⁻¹ * y⁻¹ =
            (g : E7G)⁻¹ * ((g : E7G) * y * (g : E7G)⁻¹ * y⁻¹)⁻¹ * (g : E7G)⁻¹⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [heq, hfix]
        exact Subgroup.inv_mem (Subgroup.zpowers s₇) hZ }
  have hgjN : (⟨j, hj⟩ : ↥J₇) ∈ N := hjtriv
  have hNnormal : N.Normal :=
    ⟨fun n hn c => by
      intro y hy
      have hcy : (c : E7G)⁻¹ * y * (c : E7G) ∈ Q₇ := by
        have h := (Subgroup.mem_normalizer_iff.1 (hLQ (Subgroup.inv_mem J₇ c.2)) y).1 hy
        simpa using h
      have hZ : (n : E7G) * ((c : E7G)⁻¹ * y * (c : E7G)) * (n : E7G)⁻¹ *
          ((c : E7G)⁻¹ * y * (c : E7G))⁻¹ ∈ Subgroup.zpowers s₇ := hn _ hcy
      have hfix : (c : E7G) * ((n : E7G) * ((c : E7G)⁻¹ * y * (c : E7G)) * (n : E7G)⁻¹ *
            ((c : E7G)⁻¹ * y * (c : E7G))⁻¹) * (c : E7G)⁻¹ =
          (n : E7G) * ((c : E7G)⁻¹ * y * (c : E7G)) * (n : E7G)⁻¹ *
            ((c : E7G)⁻¹ * y * (c : E7G))⁻¹ :=
        conj_mem_zpowers_eq_self (hJcent c.2) hZ
      have heq : ((c * n * c⁻¹ : ↥J₇) : E7G) * y * ((c * n * c⁻¹ : ↥J₇) : E7G)⁻¹ * y⁻¹ =
          (c : E7G) * ((n : E7G) * ((c : E7G)⁻¹ * y * (c : E7G)) * (n : E7G)⁻¹ *
            ((c : E7G)⁻¹ * y * (c : E7G))⁻¹) * (c : E7G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq, hfix]
      exact hZ⟩
  have hNne : N ≠ ⊤ := by
    intro hNtop
    obtain ⟨j₀, hj₀, y₀, hy₀, h₀⟩ := exists_perpLevi_E7_not_trivial_on_highRadical
    have hmem : (⟨j₀, hj₀⟩ : ↥J₇) ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact h₀ (by simpa using hmem y₀ hy₀)
  have hj1 : j = 1 := by
    rcases @Subgroup.Normal.eq_bot_or_eq_top ↥J₇ _
      (E7Pilot.isSimpleGroup_perpLevi_E7 (K := ZMod 2)) N hNnormal with h | h
    · have h1 : (⟨j, hj⟩ : ↥J₇) = 1 := by
        rw [h] at hgjN
        exact Subgroup.mem_bot.1 hgjN
      simpa using congrArg Subtype.val h1
    · exact absurd h hNne
  simp only [hj1, one_mul]
  have hqcent : q ∈ Subgroup.centralizer (Q₇ : Set E7G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hx y hy
    simp only [hj1, one_mul] at this
    exact this.symm
  have hqmem : q ∈ Q₇ ⊓ Subgroup.centralizer (Q₇ : Set E7G) := ⟨hq, hqcent⟩
  rwa [Q7_inf_centralizer_eq_zpowers] at hqmem

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
