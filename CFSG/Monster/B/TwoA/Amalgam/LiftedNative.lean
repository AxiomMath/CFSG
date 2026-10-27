module

public import CFSG.Monster.B.TwoA.Amalgam.LiftedStab
public import CFSG.Monster.B.TwoA.Amalgam.CoverNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

@[expose] def pairOff (a b : ℕ) : Set (Fin Tag.F4.rank) := {j | (j : ℕ) ≠ a ∧ (j : ℕ) ≠ b}

theorem ncard_pairOff {a b : ℕ} (hab : a ≠ b) (ha : a < 4) (hb : b < 4) :
    (pairOff a b).ncard = 2 := by
  rw [pairOff, Set.ncard_eq_toFinset_card']
  interval_cases a <;> interval_cases b <;> simp_all <;> decide

theorem pairOff_comm (a b : ℕ) : pairOff a b = pairOff b a := by
  ext j
  exact and_comm

theorem pairOff_subset_typesOff_left (i j : Fin 4) : pairOff i j ⊆ typesOff i := fun _ hk => hk.1

theorem pairOff_subset_typesOff_right (i j : Fin 4) : pairOff i j ⊆ typesOff j :=
  fun _ hk => hk.2

theorem setOf_decide_pairOff (a b : ℕ) :
    {i : Fin Tag.F4.rank | decide ((i : ℕ) ≠ a ∧ (i : ℕ) ≠ b) = true} = pairOff a b := by
  ext i
  simp [pairOff]

variable {X : ChamberSystem (Fin Tag.F4.rank) Chamber}
  (hX : ∀ i c d, X.adj i c d ↔ chamberAdj i c d)

theorem residueSetStab_chamberRho_eq {J : Set (Fin Tag.F4.rank)} {S : Subgroup Eam}
    (hBS : Bam.subgroupOf Eam ≤ S)
    (hR : X.residue J (chamberOf 1) = chamberOf '' (S : Set Eam)) :
    X.residueSetStab (chamberRho X hX).range J (chamberOf 1) = S.map (chamberRho X hX) := by
  ext h
  rw [mem_residueSetStab, hR]
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, (image_chamberLeft_eq_iff hBS g).mp hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (image_chamberLeft_eq_iff hBS g).mpr hg⟩

omit hX in
theorem natCard_parJ_of_isResidueBuilding
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J)
    (hsize : ∀ (i : Fin Tag.F4.rank) (x : Chamber),
      (X.residue {i} x).encard = if (i : ℕ) < 2 then 3 else 5)
    {J : Set (Fin Tag.F4.rank)} (hJ : X.IsResidueBuilding (coxeterSystem .F4) J (chamberOf 1)) :
    Nat.card (parJ J) =
      Nat.card Bam * ∑ᶠ w ∈ ((coxeterSystem .F4).parabolic J : Set (WeylGroup .F4)),
        weylWeight (coxeterSystem .F4) f4q w := by
  have hR := finite_ncard_residue_of_isResidueBuilding (q := f4q) hJ (fun y _ j _ => by
    rw [hsize, f4q]
    split_ifs <;> rfl)
  rw [← natCard_resGroup, natCard_eq_mul_ncard_image (Bam_le_resGroup J),
    ← residue_chamberOf_one hres J, hR.2]

theorem eq_inf_of_natCard {A P P' : Subgroup Dfull} (hA : A ≤ P ⊓ P') {N s : ℕ} (hN : 0 < N)
    (hAcard : Nat.card A = Nat.card Bam * s) (hPcard : Nat.card P = Nat.card Bam * (N * s))
    (hidx : (P'.subgroupOf P).index = N) : A = P ⊓ P' := by
  have h1 := (P'.subgroupOf P).card_mul_index
  rw [hidx, hPcard, ← Subgroup.inf_subgroupOf_left P' P,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ P' ≤ P)).toEquiv] at h1
  have h2 : Nat.card ↥(P ⊓ P') = Nat.card Bam * s := by
    have h3 : Nat.card ↥(P ⊓ P') * N = Nat.card Bam * s * N := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hN h3
  exact Subgroup.eq_of_le_of_card_ge hA (by rw [h2, hAcard])

include hX in
theorem iInf_map_chamberRho {ι : Type*} [Nonempty ι] (S : ι → Subgroup Eam)
    (hS : ∀ i, (chamberRho X hX).ker ≤ S i) :
    (⨅ i, S i).map (chamberRho X hX) = ⨅ i, (S i).map (chamberRho X hX) := by
  refine le_antisymm (le_iInf fun i => Subgroup.map_mono (iInf_le S i)) fun h hh => ?_
  rw [Subgroup.mem_iInf] at hh
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨g, -, rfl⟩ := hh i₀
  refine ⟨g, Subgroup.mem_iInf.mpr fun i => ?_, rfl⟩
  obtain ⟨g', hg', he⟩ := hh i
  have hk : g'⁻¹ * g ∈ (chamberRho X hX).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have := mul_mem hg' (hS i hk)
  rwa [mul_inv_cancel_left] at this

include hX in
theorem inf_map_chamberRho {S T : Subgroup Eam} (hS : (chamberRho X hX).ker ≤ S)
    (hT : (chamberRho X hX).ker ≤ T) :
    (S ⊓ T).map (chamberRho X hX) = S.map (chamberRho X hX) ⊓ T.map (chamberRho X hX) := by
  have h := iInf_map_chamberRho hX (fun b : Bool => cond b S T) (fun b => by cases b <;> assumption)
  simpa [iInf_bool_eq] using h

end CFSG.Monster.B.TwoA.Amalgam
