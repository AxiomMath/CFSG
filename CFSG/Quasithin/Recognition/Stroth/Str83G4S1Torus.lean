module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Borel
public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Step1
public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Fpf

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Step3

variable {L1 L2 S : Subgroup G} {a : ℕ}

private theorem s1t_sup_eq (hfr : Str83G4Frame L1 L2 S a) :
    S = (S ⊓ L2) ⊔ Q2 L1 L2 S ∧ L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  refine ⟨hS2, ?_⟩
  have h : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
  rw [h, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]

theorem str83G4_pCoreOf_sup_right (hfr : Str83G4Frame L1 L2 S a) :
    pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
  have hsup2 := (s1t_sup_eq hfr).2
  obtain ⟨hF, -, -, -, -, -⟩ := hfr
  rw [hsup2]
  have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

theorem str83G4_isSylowTwoOf_sup_right
    (hfr : Str83G4Frame L1 L2 S a) : IsSylowTwoOf S (L2 ⊔ S) := by
  obtain ⟨hS2, hsup2⟩ := s1t_sup_eq hfr
  obtain ⟨hF, -, -, -, -, -⟩ := hfr
  have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
  have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
  rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
  exact h

private theorem s1t_card_natural {V : Subgroup G} (hnat : Str83G4VNat L1 L2 S V a) :
    Nat.card V = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨hstep, hVH, hV, hdata⟩ := hnat
  obtain ⟨e, ρ, φ, -, -⟩ := hdata
  rw [Nat.card_congr (chiefModBotMulEquiv V).toEquiv,
    show Nat.card ↥(Ch3z.chiefMod ⊥ V) = Nat.card (Additive ↥(Ch3z.chiefMod ⊥ V)) from rfl,
    Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin, GaloisField.card 2 (2 * a + 1) (by omega)]

theorem str83G4_s1_eq_one_of_trivial
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G))
    {x : G} (hx : x ∈ d.D2) (hxL : ∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) : x = 1 := by
  classical
  have hfr' := hfr
  have hpc := str83G4_pCoreOf_sup_right hfr
  have hsyl := str83G4_isSylowTwoOf_sup_right hfr
  have hsupq := str83G4_s1_sup_q2 hfr hg hc
  have hinfq := str83G4_s1_inf_q2 hfr hg hc
  have hcard := str83G4_s1_card_z2 hfr hg hc
  have hXQ1 := str83G4_commutator_x_q1_le hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, hZ2CS⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := Setup.omegaOneCenterOf_le _
  have hxB : x ∈ bigB L1 L2 S := by
    rw [d.hBsplit]
    exact (le_sup_right : d.D2 ≤ S ⊔ d.D1 ⊔ d.D2) hx
  have hxH : x ∈ L2 ⊔ S :=
    (le_sup_left : L2 ≤ L2 ⊔ S) (Subgroup.mem_inf.mp (d.hD2hall.1 hx)).1
  have hxN : x ∈ Subgroup.normalizer (S : Set G) := hB hxB
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hx)
  obtain ⟨V, hVZ, -, hnat⟩ := str83G4_exists_natural_bottom hfr'
  have hVeq : V = Z2 L1 L2 S :=
    Subgroup.eq_of_le_of_card_ge hVZ (by rw [hcard, s1t_card_natural hnat])
  subst hVeq
  obtain ⟨hstep, hVH, hVea, hdata⟩ := hnat
  obtain ⟨e, ρ, φ, hcompat, hφnat⟩ := hdata
  have hmemZg : ∀ y ∈ Z2 L1 L2 S, g⁻¹ * y * g⁻¹⁻¹ ∈ CFSG.conjugate (Z2 L1 L2 S) g := by
    intro y hy
    rw [CFSG.mem_conjugate_iff]
    have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    rw [e]
    exact hy
  have hZgS : CFSG.conjugate (Z2 L1 L2 S) g ≤ S :=
    (le_sup_left : CFSG.conjugate (Z2 L1 L2 S) g ≤ CFSG.conjugate (Z2 L1 L2 S) g ⊔ Q2 L1 L2 S).trans
      hsupq.le
  have hgZ1 : g ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)) hg
  have hgX : g⁻¹ ∈ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    le_normalizer_str83X L1 L2 S (sup_left_le_p1 L1 L2 S ((L1 ⊔ S).inv_mem hg))
  refine l2_chiefStep_eq_one_of_conj_equivariant (H := L2 ⊔ S) (Y := Z2 L1 L2 S) (S := S)
    (n := 2 * a + 1) ⟨a, rfl⟩ hsyl hVH hVea hstep e ρ φ hcompat hφnat x g⁻¹ hxH hxN hxodd
    (fun y hy => hZgS (hmemZg y hy)) (fun y hy => ?_) (fun y hy => ?_)
  ·
    rw [hpc]
    constructor
    · intro h
      have h1 : g⁻¹ * y * g⁻¹⁻¹ ∈ Z1 L1 L2 S := by
        rw [← hinfq]
        exact Subgroup.mem_inf.mpr ⟨hmemZg y hy, h⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hgZ1 _).mp h1
      have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rw [e, ← hZ2CS] at h2
      exact (Subgroup.mem_inf.mp h2).2
    · intro h
      have h1 : y ∈ Z1 L1 L2 S := by
        rw [← hZ2CS]
        exact Subgroup.mem_inf.mpr ⟨hy, h⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Z1 L1 L2 S : Set G)).inv_mem hgZ1) y).mp h1
      exact hZ2Q2 (hZ1Z2 h2)
  ·
    rw [hpc]
    have hc' : x * g⁻¹ * x⁻¹ * g⁻¹⁻¹ ∈ Q1 L1 L2 S :=
      str83G4_trivial_on_sup hfr' hxB hxL g⁻¹ ((L1 ⊔ S).inv_mem hg)
    have hxy : x * y * x⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (bigB_le_normalizer_z2 L1 L2 S hxB) y).mp hy
    have hw : g⁻¹ * (x * y * x⁻¹) * g⁻¹⁻¹ ∈ str83X L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp hgX _).mp (z2_le_str83X L1 L2 S hxy)
    have hcomm : ⁅x * g⁻¹ * x⁻¹ * g⁻¹⁻¹, g⁻¹ * (x * y * x⁻¹) * g⁻¹⁻¹⁆ ∈ Z1 L1 L2 S := by
      refine hXQ1 ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hc' hw
    have e : x * (g⁻¹ * y * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * (x * y * x⁻¹) * g⁻¹⁻¹)⁻¹ =
        ⁅x * g⁻¹ * x⁻¹ * g⁻¹⁻¹, g⁻¹ * (x * y * x⁻¹) * g⁻¹⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hZ2Q2 (hZ1Z2 hcomm)

theorem str83G4_s1_fpf
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G))
    {x y : G} (hx : x ∈ d.D2) (hx1 : x ≠ 1) (hy : y ∈ Q2 L1 L2 S)
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S) : y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
  str83G4_mem_q1_inf_q2_of_fix hfr d
    (fun _ hx' hxL => str83G4_s1_eq_one_of_trivial hfr d hg hc hx' hxL) hx hx1 hy hxy

theorem str83G4_s1_fpf_r0
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G))
    {x y : G} (hx : x ∈ d.D2) (hx1 : x ≠ 1) (hy : y ∈ Q2 L1 L2 S)
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓
      CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w) :
    y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w :=
  str83G4_mem_r0_of_fpf d
    (fun _ hx' hx1' _ hy' hxy' => str83G4_s1_fpf hfr d hg hc hx' hx1' hy' hxy') hx hx1 hy hxy

end Step3

end CFSG.Quasithin.Stroth

end
