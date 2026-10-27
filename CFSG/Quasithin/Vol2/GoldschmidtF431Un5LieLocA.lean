module

public import CFSG.LocalAnalysis.EvenBN.U5.Model

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def vsub (p : Matrix (Fin 2) (Fin 2) K → Prop) (h0 : p 0)
    (hadd : ∀ Y Y', p Y → p Y' → p (Y + Y')) (hneg : ∀ Y, p Y → p (-Y)) :
    Subgroup (hypSU h 2 1) where
  carrier := {g | g ∈ Vsub h ∧ p (Yof g)}
  mul_mem' := by
    rintro g g' ⟨hg, hpg⟩ ⟨hg', hpg'⟩
    refine ⟨mul_mem hg hg', ?_⟩
    obtain ⟨-, Y, hY⟩ := hg
    obtain ⟨-, Y', hY'⟩ := hg'
    have hm : mat (g * g') = oddUni h 0 (Y + Y') := by
      rw [mat_mul, hY, hY', oddUni_mul]
      simp
    rw [Yof_eq hm]
    rw [Yof_eq hY] at hpg
    rw [Yof_eq hY'] at hpg'
    exact hadd _ _ hpg hpg'
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    have : Yof (1 : hypSU h 2 1) = 0 := Yof_eq (by rw [mat_one, oddUni_zero])
    rw [this]
    exact h0
  inv_mem' := by
    rintro g ⟨hg, hpg⟩
    refine ⟨inv_mem hg, ?_⟩
    obtain ⟨-, Y, hY⟩ := hg
    have hm : mat g⁻¹ = oddUni h 0 (-Y) := mat_inv_eq (by
      rw [hY, oddUni_mul]
      simp [oddUni_zero])
    rw [Yof_eq hm]
    rw [Yof_eq hY] at hpg
    exact hneg _ hpg

variable {h}

theorem Yof_vSU {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) : Yof (vSU h Y hY) = Y :=
  Yof_eq (mat_vSU hY)

theorem mem_vsub_iff {p : Matrix (Fin 2) (Fin 2) K → Prop} {h0 : p 0}
    {hadd : ∀ Y Y', p Y → p Y' → p (Y + Y')} {hneg : ∀ Y, p Y → p (-Y)} {g : hypSU h 2 1} :
    g ∈ vsub h p h0 hadd hneg ↔ ∃ (Y : Matrix (Fin 2) (Fin 2) K) (hY : IsHerm h Y),
      p Y ∧ g = vSU h Y hY := by
  constructor
  · rintro ⟨hg, hp⟩
    obtain ⟨-, Y, hY⟩ := hg
    have hH : IsHerm h Y := herm_of_mem_Vsub hY
    refine ⟨Y, hH, by rwa [Yof_eq hY] at hp, mat_injective (hY.trans (mat_vSU hH).symm)⟩
  · rintro ⟨Y, hY, hp, rfl⟩
    exact ⟨vSU_mem_Vsub hY, by rwa [Yof_vSU hY]⟩

theorem vsub_le_Vsub {p : Matrix (Fin 2) (Fin 2) K → Prop} {h0 : p 0}
    {hadd : ∀ Y Y', p Y → p Y' → p (Y + Y')} {hneg : ∀ Y, p Y → p (-Y)} :
    vsub h p h0 hadd hneg ≤ Vsub h := fun _ hg => hg.1

theorem vsub_mono {p q : Matrix (Fin 2) (Fin 2) K → Prop} {hp0 : p 0}
    {hpa : ∀ Y Y', p Y → p Y' → p (Y + Y')} {hpn : ∀ Y, p Y → p (-Y)} {hq0 : q 0}
    {hqa : ∀ Y Y', q Y → q Y' → q (Y + Y')} {hqn : ∀ Y, q Y → q (-Y)}
    (hpq : ∀ Y, p Y → q Y) : vsub h p hp0 hpa hpn ≤ vsub h q hq0 hqa hqn :=
  fun _ hg => ⟨hg.1, hpq _ hg.2⟩

variable (h)

@[expose] def Vt : Subgroup (hypSU h 2 1) :=
  vsub h (fun Y => Y 0 1 = Y 1 0) rfl (fun Y Y' a b => by simp [a, b])
    (fun Y a => by simp [a])

@[expose] def Uct : Subgroup (hypSU h 2 1) :=
  vsub h (fun Y => Y 0 0 = 0 ∧ Y 1 1 = 0 ∧ Y 0 1 = Y 1 0) ⟨rfl, rfl, rfl⟩
    (fun Y Y' a b => ⟨by simp [a.1, b.1], by simp [a.2.1, b.2.1], by simp [a.2.2, b.2.2]⟩)
    (fun Y a => ⟨by simp [a.1], by simp [a.2.1], by simp [a.2.2]⟩)

@[expose] def Rt : Subgroup (hypSU h 2 1) :=
  vsub h (fun Y => Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 1 = 0) ⟨rfl, rfl, rfl⟩
    (fun Y Y' a b => ⟨by simp [a.1, b.1], by simp [a.2.1, b.2.1], by simp [a.2.2, b.2.2]⟩)
    (fun Y a => ⟨by simp [a.1], by simp [a.2.1], by simp [a.2.2]⟩)

theorem Vt_le_Vsub : Vt h ≤ Vsub h := vsub_le_Vsub
theorem Uct_le_Vsub : Uct h ≤ Vsub h := vsub_le_Vsub
theorem Rt_le_Vsub : Rt h ≤ Vsub h := vsub_le_Vsub

theorem Uct_le_Vt : Uct h ≤ Vt h := vsub_mono fun _ a => a.2.2
theorem Rt_le_Vt : Rt h ≤ Vt h := vsub_mono fun _ a => by simp [a.1, a.2.1]

@[expose] def slF : SpecialLinearGroup (Fin 2) h.fixedField →* SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.map (algebraMap h.fixedField K)

@[expose] def levHom : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h 2 1 :=
  (UnitaryHigher.leviSU h 1).comp (slF h)

@[expose] def L0 : Subgroup (hypSU h 2 1) := (levHom h).range

@[expose] def vY : Subgroup (hypPSU h 2 1) := (Vt h).map (hypProj h 2 1)

@[expose] def ucY : Subgroup (hypPSU h 2 1) := (Uct h).map (hypProj h 2 1)

@[expose] def rY : Subgroup (hypPSU h 2 1) := (Rt h).map (hypProj h 2 1)

@[expose] def kY : Subgroup (hypPSU h 2 1) := (Vt h ⊔ L0 h).map (hypProj h 2 1)

@[expose] def lY : Subgroup (hypPSU h 2 1) := (L0 h).map (hypProj h 2 1)

variable {h}

theorem vSU_mem_Vt {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) (hs : Y 0 1 = Y 1 0) :
    vSU h Y hY ∈ Vt h :=
  ⟨vSU_mem_Vsub hY, by rwa [Yof_vSU hY]⟩

theorem vSU_mem_Uct {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hs : Y 0 0 = 0 ∧ Y 1 1 = 0 ∧ Y 0 1 = Y 1 0) : vSU h Y hY ∈ Uct h :=
  ⟨vSU_mem_Vsub hY, by rwa [Yof_vSU hY]⟩

theorem vSU_mem_Rt {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hs : Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 1 = 0) : vSU h Y hY ∈ Rt h :=
  ⟨vSU_mem_Vsub hY, by rwa [Yof_vSU hY]⟩

theorem z₁SU_mem_Rt : z₁SU h ∈ Rt h :=
  vSU_mem_Rt (isHerm_e₁₁ h) ⟨rfl, rfl, rfl⟩

theorem z₂SU_mem_Uct : z₂SU h ∈ Uct h :=
  vSU_mem_Uct (isHerm_swap h) ⟨rfl, rfl, rfl⟩

end CFSG.Quasithin.H13.F431.Un.L5
