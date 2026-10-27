module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7Base
public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.Quasithin.ThreeC CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e7_caseI {Z U TC G2 R V Vp : Subgroup G} {g : G} (h : E7Pair Z U TC G2 R g)
    (hVp : Vp ≤ U)
    (e5c : G2 ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G))
    (e6i : ¬ ⁅conjSub g U, V⁆ ≤ conjSub g Z)
    (hD : centralizerMod Z (conjSub g U) U = conjSub g U) :
    ∃ B : Subgroup G, B ≤ R ∧ ¬ B ≤ TC ∧
      mIdx U (centralizerMod Z U B) ≤ 2 * mIdx (B ⊔ TC) TC := by
  classical
  have hZC : ∀ X : Subgroup G, X ≤ G2 → Z ≤ Subgroup.centralizer (X : Set G) := by
    intro X hX z hz
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (h.G2_cent (hX hx))) z hz).symm
  have hcardA : Nat.card (conjSub g Z) = 2 := (CosetGeom.card_conjSub g Z).trans h.card_Z
  have hcardZ' : Nat.card (conjSub g⁻¹ Z) = 2 := (CosetGeom.card_conjSub g⁻¹ Z).trans h.card_Z
  have hZ'ne : conjSub g⁻¹ Z ≠ Z := by
    intro heq
    apply h.ne_A
    have := congrArg (conjSub g) heq
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hZZ' : Z ⊓ conjSub g⁻¹ Z = ⊥ := by
    by_contra hne
    have hle : Z ≤ conjSub g⁻¹ Z := le_of_card_eq_two_of_inf_ne_bot h.card_Z hne
    exact hZ'ne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ', h.card_Z])).symm
  have hUW : ⁅U, conjSub g U⁆ ≤ Z := by
    refine Subgroup.commutator_le.mpr fun u hu w hw => ?_
    have hw' : w ∈ centralizerMod Z (conjSub g U) U := hD.symm ▸ hw
    have h1 := Z.inv_mem (hw'.2.2 u hu)
    have e : (w * u * w⁻¹ * u⁻¹)⁻¹ = u * w * u⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  have hne : ⁅U, conjSub g U⁆ ≠ ⊥ := by
    intro hbot
    have hWC : conjSub g U ≤ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.commutator_comm] at hbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hWV : conjSub g U ≤ Subgroup.centralizer (V : Set G) :=
      fun w hw => e5c ⟨h.W_le hw, Subgroup.centralizer_le hVp (hWC hw)⟩
    apply e6i
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWV]
    exact bot_le
  have hUWZ : ⁅U, conjSub g U⁆ = Z := by
    rcases HypF98.eq_bot_or_eq_of_card_eq_two h.card_Z hUW with hb | he
    · exact absurd hb hne
    · exact he
  set B := conjSub g⁻¹ U with hBdef
  have hBU : conjSub g B = U := conjSub_inv_conjSub g U
  have hBab : IsElemAbelian 2 B := F7.isElemAbelian_conjSub h.U_ab
  have hUB : ⁅U, B⁆ = conjSub g⁻¹ Z := by
    have e1 : U = conjSub g⁻¹ (conjSub g U) := (conjSub_conjSub_inv g U).symm
    calc ⁅U, B⁆ = ⁅conjSub g⁻¹ (conjSub g U), conjSub g⁻¹ U⁆ := by rw [← e1]
      _ = conjSub g⁻¹ ⁅conjSub g U, U⁆ := conjSub_commutator _ _ _
      _ = conjSub g⁻¹ Z := by rw [Subgroup.commutator_comm, hUWZ]
  have hZ'U : conjSub g⁻¹ Z ≤ Subgroup.centralizer (U : Set G) := by
    have h1 : Z ≤ Subgroup.centralizer (conjSub g U : Set G) := hZC _ h.W_le
    have h2 := conjSub_mono g⁻¹ h1
    rw [← conjSub_centralizer, conjSub_conjSub_inv] at h2
    exact h2
  have hZ'B : conjSub g⁻¹ Z ≤ Subgroup.centralizer (B : Set G) := by
    have h1 : Z ≤ Subgroup.centralizer (U : Set G) := hZC _ h.U_le
    have h2 := conjSub_mono g⁻¹ h1
    rw [← conjSub_centralizer] at h2
    exact h2
  have hpair := relIndex_eq_of_commutator_le (X := U) (Y := B) (C := conjSub g⁻¹ Z) hBab hcardZ'
    hUB.le hZ'U hZ'B
  have hcM : U ⊓ Subgroup.centralizer (B : Set G) ≤ centralizerMod Z U B := by
    intro u hu
    refine ⟨hu.1, Subgroup.centralizer_le_normalizer _ (h.G2_cent (h.U_le hu.1)), fun b hb => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hu.2 b hb
    have e : u * b * u⁻¹ * b⁻¹ = 1 := by rw [← this]; group
    rw [e]
    exact Z.one_mem
  have hBTC : B ⊓ TC ≤ B ⊓ Subgroup.centralizer (U : Set G) := by
    intro b hb
    refine ⟨hb.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have h1 : ⁅b, u⁆ ∈ conjSub g⁻¹ Z := by
      have := Subgroup.commutator_mem_commutator hb.1 hu
      rw [Subgroup.commutator_comm, hUB] at this
      exact this
    have h2 : ⁅b, u⁆ ∈ Z := by
      have := h.e5a (Subgroup.commutator_mem_commutator hu hb.2)
      have e : ⁅b, u⁆ = ⁅u, b⁆⁻¹ := (commutatorElement_inv u b).symm
      rw [e]
      exact Z.inv_mem this
    have h3 : ⁅b, u⁆ ∈ Z ⊓ conjSub g⁻¹ Z := ⟨h2, h1⟩
    rw [hZZ', Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  refine ⟨B, h.B_le, ?_, ?_⟩
  ·
    intro hBle
    apply h.ne_A
    have hUTC : U ≤ conjSub g TC := by
      rw [← hBU]
      exact conjSub_mono g hBle
    have hZA : Z ≤ conjSub g Z := by
      calc Z = ⁅conjSub g U, U⁆ := by rw [Subgroup.commutator_comm]; exact hUWZ.symm
        _ ≤ ⁅conjSub g U, conjSub g TC⁆ := Subgroup.commutator_mono le_rfl hUTC
        _ = conjSub g ⁅U, TC⁆ := conjSub_commutator g U TC
        _ ≤ conjSub g Z := conjSub_mono g h.e5a
    exact (Subgroup.eq_of_le_of_card_ge hZA (by rw [hcardA, h.card_Z])).symm
  ·
    have h1 : mIdx U (centralizerMod Z U B) ≤ mIdx U (U ⊓ Subgroup.centralizer (B : Set G)) :=
      mIdx_anti_of_le hcM
    have h2 : mIdx U (U ⊓ Subgroup.centralizer (B : Set G)) =
        mIdx B (B ⊓ Subgroup.centralizer (U : Set G)) := by
      unfold mIdx
      rw [hpair]
    have h3 : mIdx B (B ⊓ Subgroup.centralizer (U : Set G)) ≤ mIdx B (B ⊓ TC) :=
      mIdx_anti_of_le hBTC
    have hBN : B ≤ Subgroup.normalizer (TC : Set G) :=
      fun b hb => h.G2_normTC (h.R_le (h.B_le hb))
    have h4 : mIdx B (B ⊓ TC) = mIdx (B ⊔ TC) TC := mIdx_inf_eq_mIdx_sup hBN
    omega

end CFSG.Quasithin.H13.NFa2
