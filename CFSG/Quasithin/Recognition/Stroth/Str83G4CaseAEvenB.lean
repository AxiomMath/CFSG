module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEvenA

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

open scoped commutatorElement

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

@[expose] noncomputable def caseAEvenXInf (b : ℕ) (x : GPath (f112Amalgam L1 L2 S).graphHat b) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAX (x (b - 1)) ⊓ CosetGeom.Qy (x 0)

@[expose] noncomputable def caseAEvenF (b : ℕ) (x : GPath (f112Amalgam L1 L2 S).graphHat b)
    (l : f112Gamma L1 L2 S) : Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAEvenXInf b x ⊓ CosetGeom.Qy l

variable [Finite G]

theorem caseA_even_mem_caseAS
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b)
    {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) {u : (f112Amalgam L1 L2 S).Ghat}
    (hu : u ∈ caseAX l) : u ∈ caseAS (x (b - 1)) (x (b - 2)) ∧ u * u = 1 := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hlA : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hlf : CosetGeom.vtype l = false := by
    have hne := CosetGeom.vtype_ne_of_adj hlA
    rw [hx.type_two] at hne
    cases h : CosetGeom.vtype l <;> simp_all
  have hXel : IsElemAbelian 2 (caseAX l) := caseA_isElemAbelian_X hfr hlf
  have hu2 : u * u = 1 := IsElemAbelian.mul_self_eq_one hXel hu
  have hXlR : caseAX l ≤ caseAR (x 0) :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (x 0)) => caseAX w) l hl
  have huQb2 : u ∈ CosetGeom.Qy (x (b - 2)) :=
    (caseA_even_R_le_Qy hfr hx hbe hb) (hXlR hu)
  have hstab2 : u ∈ CosetGeom.stab (x (b - 2)) := caseA_Qy_le_stab _ huQb2
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
    simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega)
  have hstab1 : u ∈ CosetGeom.stab (x (b - 1)) :=
    (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := x (b - 2)) (δ := x (b - 1))
      (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le)
      ((caseA_Qy_le_ballStab_one hfr (x (b - 2))) huQb2)
  have h2 : ∃ k, orderOf u = 2 ^ k := by
    have hdvd : orderOf u ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hu2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have hw : x (b - 1) ∈ CosetGeom.nbrs (x (b - 2)) := by
    simpa [CosetGeom.nbrs] using hadj
  refine ⟨?_, hu2⟩
  rw [caseAS_comm (x (b - 1)) (x (b - 2))]
  exact caseA_mem_caseAS_of_two_elem hfr hw hstab2 hstab1 h2

theorem caseA_even_commutator_X_le
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) :
    ⁅caseAX l, caseAEvenXInf b x⁆ ≤ caseAEvenXInf b x := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hlA : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hlf : CosetGeom.vtype l = false := by
    have hne := CosetGeom.vtype_ne_of_adj hlA
    rw [hx.type_two] at hne
    cases h : CosetGeom.vtype l <;> simp_all
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
    simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega)
  have hXlQy : caseAX l ≤ CosetGeom.Qy l :=
    caseA_X_le_Qy hx.ball hlf (by rw [CosetGeom.dist_self]; omega)
  have hXlR : caseAX l ≤ caseAR (x 0) :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (x 0)) => caseAX w) l hl
  have hXlQb2 : caseAX l ≤ CosetGeom.Qy (x (b - 2)) :=
    hXlR.trans (caseA_even_R_le_Qy hfr hx hbe hb)
  have hXl_stab0 : caseAX l ≤ CosetGeom.stab (x 0) :=
    hXlQy.trans ((caseA_Qy_le_ballStab_one hfr l).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := l) (δ := x 0)
        (CosetGeom.dist_eq_one_iff_adj.mpr hlA.symm).le))
  have hXl_stab_b1 : caseAX l ≤ CosetGeom.stab (x (b - 1)) :=
    hXlQb2.trans ((caseA_Qy_le_ballStab_one hfr (x (b - 2))).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := x (b - 2)) (δ := x (b - 1))
        (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le))
  have hnorm : caseAX l ≤
      Subgroup.normalizer ((caseAX (x (b - 1)) ⊓ CosetGeom.Qy (x 0) :
        Subgroup (f112Amalgam L1 L2 S).Ghat) : Set (f112Amalgam L1 L2 S).Ghat) :=
    (le_inf (hXl_stab_b1.trans (caseA_stab_le_normalizer_X (x (b - 1))))
      (hXl_stab0.trans (caseA_stab_le_normalizer_Qy (x 0)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  simpa [caseAEvenXInf] using
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hnorm

private lemma caseA_even_F_le_centralizer
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x)
    (hbe : Even b) (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0))
    (hl1 : l ≠ x 1) {u : (f112Amalgam L1 L2 S).Ghat} (hu : u ∈ caseAX l)
    (huQ : u ∉ CosetGeom.Qy (x (b - 1))) :
    caseAEvenF b x l ≤ caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat) := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hlA : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hlf : CosetGeom.vtype l = false := by
    have hne := CosetGeom.vtype_ne_of_adj hlA
    rw [hx.type_two] at hne
    cases h : CosetGeom.vtype l <;> simp_all
  have hxbf : CosetGeom.vtype (x (b - 1)) = false := by
    refine (hx.vtype_eq_false_iff_odd (i := b - 1) (show b - 1 ≤ b by omega)).mpr ?_
    rw [← Nat.not_even_iff_odd]
    intro he
    obtain ⟨k, hk⟩ := hbe
    obtain ⟨m, hm⟩ := he
    omega
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
    simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega)
  have hXQb : caseAX (x (b - 1)) ≤ CosetGeom.Qy (x b) := by
    refine caseA_X_le_Qy hx.ball hxbf ?_
    have hd := hx.dist_eq (i := b - 1) (j := b) (by omega) le_rfl
    rw [hd]
    omega
  have hXlR : caseAX l ≤ caseAR (x 0) :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (x 0)) => caseAX w) l hl
  have huQb2 : u ∈ CosetGeom.Qy (x (b - 2)) :=
    (hXlR.trans (caseA_even_R_le_Qy hfr hx hbe hb)) hu
  have hXu_stab : u ∈ CosetGeom.stab (x (b - 1)) :=
    (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := x (b - 2)) (δ := x (b - 1))
      (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le)
      ((caseA_Qy_le_ballStab_one hfr (x (b - 2))) huQb2)
  have hXnorm : u ∈ Subgroup.normalizer (caseAX (x (b - 1)) :
      Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_X (x (b - 1)) hXu_stab
  have hbot := caseA_even_Z_inf_Qy_end hfr hx hbe hb hl hl1
  intro y hy
  have hyX : y ∈ caseAX (x (b - 1)) := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1
  refine ⟨hyX, ?_⟩
  change y ∈ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hyQl : y ∈ CosetGeom.Qy l := (Subgroup.mem_inf.mp hy).2
  have hmemZ : ⁅y, u⁆ ∈ caseAZ l := by
    have hmem : ⁅y, u⁆ ∈ ⁅CosetGeom.Qy l, caseAX l⁆ :=
      Subgroup.commutator_mem_commutator hyQl hu
    have hmem' : ⁅y, u⁆ ∈ ⁅caseAX l, CosetGeom.Qy l⁆ := by
      rwa [Subgroup.commutator_comm] at hmem
    exact caseA_commutator_X_Qy_le_Z hfr hlf hmem'
  have hmemX : ⁅y, u⁆ ∈ caseAX (x (b - 1)) := by
    have hconj : u * y⁻¹ * u⁻¹ ∈ caseAX (x (b - 1)) :=
      (Subgroup.mem_normalizer_iff.mp hXnorm y⁻¹).mp ((caseAX (x (b - 1))).inv_mem hyX)
    have heq : ⁅y, u⁆ = y * (u * y⁻¹ * u⁻¹) := by group
    rw [heq]
    exact (caseAX (x (b - 1))).mul_mem hyX hconj
  have hone : ⁅y, u⁆ = 1 := by
    have hmem : ⁅y, u⁆ ∈ caseAZ l ⊓ CosetGeom.Qy (x b) :=
      Subgroup.mem_inf.mpr ⟨hmemZ, hXQb hmemX⟩
    rw [hbot] at hmem
    simpa using hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hone

private lemma caseA_even_E5_count
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1)
    {u : (f112Amalgam L1 L2 S).Ghat} (hu : u ∈ caseAX l)
    (huQ : u ∉ CosetGeom.Qy (x (b - 1))) :
    (caseAX (x (b - 1)) ⊓ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat) =
        caseAEvenF b x l) ∧
      (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) = (2 ^ (2 * a + 1)) ^ 2 ∧
      (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) = 2 ^ (2 * a + 1) ∧
      (caseAEvenF b x l).relIndex (caseAEvenXInf b x) = 2 ^ (2 * a + 1) := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hxbf : CosetGeom.vtype (x (b - 1)) = false := by
    refine (hx.vtype_eq_false_iff_odd (i := b - 1) (show b - 1 ≤ b by omega)).mpr ?_
    rw [← Nat.not_even_iff_odd]
    intro he
    obtain ⟨k, hk⟩ := hbe
    obtain ⟨m, hm⟩ := he
    omega
  have hlf : CosetGeom.vtype l = false := by
    have hlA : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
      simpa [CosetGeom.nbrs] using hl
    have hne := CosetGeom.vtype_ne_of_adj hlA
    rw [hx.type_two] at hne
    cases h : CosetGeom.vtype l <;> simp_all
  haveI hstabfin : Finite ↥(CosetGeom.stab (x (b - 1))) :=
    caseA_finite_stab L1 L2 S (x (b - 1))
  haveI hXfin : Finite ↥(caseAX (x (b - 1))) :=
    Finite.of_injective (Subgroup.inclusion (caseA_X_le_stab hfr (x (b - 1))))
      (Subgroup.inclusion_injective (caseA_X_le_stab hfr (x (b - 1))))
  have hF_le_C := caseA_even_F_le_centralizer hfr hx hbe hb hl hl1 hu huQ
  have hC_le_X : (caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)) ≤ caseAX (x (b - 1)) :=
    inf_le_left
  have hFX' : caseAEvenF b x l ≤ caseAEvenXInf b x := inf_le_left
  have hX'X : caseAEvenXInf b x ≤ caseAX (x (b - 1)) := inf_le_left
  have hFX : caseAEvenF b x l ≤ caseAX (x (b - 1)) := hFX'.trans hX'X
  have hX1 : x 1 ∈ CosetGeom.nbrs (x 0) := by
    simpa [CosetGeom.nbrs] using x.adj 0 (by omega)
  have hM5X : (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) ≤ 2 ^ (2 * a + 1) := by
    have hS : caseAX (x (b - 1)) ≤ caseAS (x 0) (x 1) := by
      have hd : CosetGeom.dist (x (b - 1)) (x 1) + 1 ≤ b - 1 := by
        have hdist := hx.dist_eq (i := 1) (j := b - 1)
          (by omega) (by omega)
        rw [CosetGeom.dist_comm, hdist]
        omega
      have hQ1 : caseAX (x (b - 1)) ≤ CosetGeom.Qy (x 1) :=
        caseA_X_le_Qy hx.ball hxbf hd
      have hw10 : x 0 ∈ CosetGeom.nbrs (x 1) := by
        simpa [CosetGeom.nbrs] using (x.adj 0 (by omega)).symm
      have h := caseA_Qy_le_caseAS hfr (v := x 1) (w := x 0) hw10
      rw [caseAS_comm (x 1) (x 0)] at h
      exact hQ1.trans h
    simpa [caseAEvenXInf] using
      caseA_relIndex_inf_Qy_le_type2 hfr hx.type_two hX1 hS
  have hM5F : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) ≤ 2 ^ (2 * a + 1) := by
    have hS : caseAEvenXInf b x ≤ caseAS l (x 0) := by
      have h := caseA_Qy_le_caseAS hfr (v := x 0) (w := l) hl
      rw [caseAS_comm (x 0) l] at h
      exact inf_le_right.trans h
    have hsq : ∀ y ∈ caseAEvenXInf b x, y * y ∈ CosetGeom.Qy l := by
      intro y hy
      have hyX : y ∈ caseAX (x (b - 1)) := (Subgroup.mem_inf.mp hy).1
      have hXel := caseA_isElemAbelian_X hfr hxbf
      rw [IsElemAbelian.mul_self_eq_one hXel hyX]
      exact (CosetGeom.Qy l).one_mem
    have hτ : x 0 ∈ CosetGeom.nbrs l := by
      have hlA : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
        simpa [CosetGeom.nbrs] using hl
      simpa [CosetGeom.nbrs] using hlA.symm
    simpa [caseAEvenF, caseAEvenXInf] using
      caseA_relIndex_inf_Qy_le_type1 hfr hlf hτ hS hsq
  have hM7 : (2 ^ (2 * a + 1)) ^ 2 ≤
      (centralizerMod (caseAZ (x (b - 1))) (caseAX (x (b - 1)))
        (Subgroup.zpowers u)).relIndex (caseAX (x (b - 1))) := by
    have hmemAS := (caseA_even_mem_caseAS hfr hx hbe hb hl hu).1
    have hu2 := (caseA_even_mem_caseAS hfr hx hbe hb hl hu).2
    have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
      simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega)
    have hτ : x (b - 2) ∈ CosetGeom.nbrs (x (b - 1)) := by
      simpa [CosetGeom.nbrs] using hadj.symm
    exact caseA_sq_le_relIndex_centralizerMod_X hfr hxbf hτ hmemAS hu2 huQ
  have hmodle :
      (centralizerMod (caseAZ (x (b - 1))) (caseAX (x (b - 1)))
        (Subgroup.zpowers u)).relIndex (caseAX (x (b - 1))) ≤
      (caseAX (x (b - 1)) ⊓
        Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
        (caseAX (x (b - 1))) :=
    caseA_relIndex_centralizerMod_le_relIndex_centralizer
      ((caseA_X_le_stab hfr (x (b - 1))).trans (caseA_stab_le_normalizer_Z (x (b - 1))))
  have hlow : (2 ^ (2 * a + 1)) ^ 2 ≤
      (caseAX (x (b - 1)) ⊓
        Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
        (caseAX (x (b - 1))) := hM7.trans hmodle
  have hFrelX_ne : (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) ≠ 0 := by
    haveI : ((caseAEvenF b x l).subgroupOf (caseAX (x (b - 1)))).FiniteIndex := inferInstance
    haveI : (caseAEvenF b x l).IsFiniteRelIndex (caseAX (x (b - 1))) :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
    exact Subgroup.relIndex_ne_zero
  have hCleF : (caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
      (caseAX (x (b - 1))) ≤ (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) :=
    Subgroup.relIndex_le_of_le_left hF_le_C hFrelX_ne
  have hprod : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) *
      (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) =
      (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) :=
    Subgroup.relIndex_mul_relIndex (caseAEvenF b x l) (caseAEvenXInf b x)
      (caseAX (x (b - 1))) hFX' hX'X
  have hupper : (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
    have h1 : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) *
        (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) ≤
        (2 ^ (2 * a + 1)) * (2 ^ (2 * a + 1)) :=
      Nat.mul_le_mul hM5F hM5X
    rw [hprod] at h1
    calc (caseAEvenF b x l).relIndex (caseAX (x (b - 1)))
        ≤ (2 ^ (2 * a + 1)) * (2 ^ (2 * a + 1)) := h1
      _ = (2 ^ (2 * a + 1)) ^ 2 := by ring
  have hFrel : (caseAEvenF b x l).relIndex (caseAX (x (b - 1))) =
      (2 ^ (2 * a + 1)) ^ 2 := le_antisymm hupper (hlow.trans hCleF)
  have hCrel : (caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
      (caseAX (x (b - 1))) = (2 ^ (2 * a + 1)) ^ 2 :=
    le_antisymm (hCleF.trans hFrel.le) hlow
  have hprodC := Subgroup.relIndex_mul_relIndex (caseAEvenF b x l)
    (caseAX (x (b - 1)) ⊓ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat))
    (caseAX (x (b - 1))) hF_le_C hC_le_X
  have hRelFC : (caseAEvenF b x l).relIndex (caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)) = 1 := by
    have h2 : (caseAEvenF b x l).relIndex (caseAX (x (b - 1)) ⊓
        Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)) *
        (2 ^ (2 * a + 1)) ^ 2 = 1 * (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← hCrel, hprodC, hFrel, hCrel, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have hC_le_F : (caseAX (x (b - 1)) ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)) ≤ caseAEvenF b x l :=
    Subgroup.relIndex_eq_one.mp hRelFC
  have hqpos : 0 < 2 ^ (2 * a + 1) := by positivity
  have hX'rel : (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) = 2 ^ (2 * a + 1) := by
    have h1 : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) *
        (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) ≤
        2 ^ (2 * a + 1) * (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) :=
      Nat.mul_le_mul_right _ hM5F
    rw [hprod, hFrel, pow_two] at h1
    exact le_antisymm hM5X (Nat.le_of_mul_le_mul_left h1 hqpos)
  have hFrel' : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) = 2 ^ (2 * a + 1) := by
    have h1 : (caseAEvenF b x l).relIndex (caseAEvenXInf b x) *
        (caseAEvenXInf b x).relIndex (caseAX (x (b - 1))) ≤
        (caseAEvenF b x l).relIndex (caseAEvenXInf b x) * 2 ^ (2 * a + 1) :=
      Nat.mul_le_mul_left _ hM5X
    rw [hprod, hFrel, pow_two] at h1
    exact le_antisymm hM5F (Nat.le_of_mul_le_mul_right h1 hqpos)
  exact ⟨le_antisymm hC_le_F hF_le_C, hFrel, hX'rel, hFrel'⟩

theorem caseA_even_relIndex_F
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    (caseAEvenF b x l).relIndex (caseAEvenXInf b x) = 2 ^ (2 * a + 1) := by
  obtain ⟨u, hu, huQ⟩ := SetLike.not_le_iff_exists.mp
    (caseA_even_not_X_le_Qy_pred hfr hx hbe hb hl hl1)
  exact (caseA_even_E5_count hfr hA hx hbe hb hl hl1 hu huQ).2.2.2

end CFSG.Quasithin.Stroth

end
