module

public import Certificates.Kernel.A45Cls.CheckInv
public import Certificates.Kernel.A45Cls.Checks8

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb Certificates.OmegaInv
  Certificates.OmegaT11 CFSG.ComponentClassification.RankTwoHypIICover.U42

local notation "P45" => Equiv.Perm (Fin 45)

theorem cubeK_iff {P : ℕ} {g : P45} (hP : PRep 45 6 P g) :
    cubeK P = true ↔ g ^ 3 = 1 ∧ g ≠ 1 := by
  unfold cubeK
  rw [Bool.and_eq_true, isIdK_iff (prep_pcomp hn45 hP (prep_pcomp hn45 hP hP)), Bool.not_eq_true',
    Bool.eq_false_iff, Ne, isIdK_iff hP, CFSG.KC.OrbFind.pow_three']

theorem tauFix_1152 {m : ℕ} (h : tauFix m = 1152) : m = 13 := by
  unfold tauFix at h
  split_ifs at h <;> first | assumption | omega

theorem notb_or_dec {b : Bool} {q : Prop} [Decidable q] (h : b = true → q) :
    (!b || decide q) = true := by
  cases b <;> simp_all

theorem notb_or {b c : Bool} (h : b = true → c = true) : (!b || c) = true := by
  cases b <;> simp_all

theorem prep_t11r : PRep 45 6 (i7rP 2) (r3 ()) := prep_i7r 2

theorem prep_t11y : PRep 45 6 (i7rP 1) (Certificates.OmegaT0.yB ()) := prep_i7r 1

theorem prep_t11z : PRep 45 6 t11zP (zeta0 ()) := prep_cOf _

theorem prep_t11g1 : PRep 45 6 t11g1P (g1 ()) := prep_cOf _

theorem prep_t11g2 : PRep 45 6 t11g2P (g2 ()) := prep_cOf _

@[expose] def t11g (k : ℕ) : P45 := wvA (t11W.getD k [])

theorem prep_t11g : ∀ k < 5, PRep 45 6 (T11Z.G k) (t11g k) ∧ t11g k ∈ A :=
  fun _ hk => prep_word t11binds.1 hk

theorem card_t11C :
    Nat.card ↥(A ⊓ centralizer ({r3 ()} : Set P45)) = 96 := by
  have h := i7_card (k := 2) (by norm_num)
  rw [i7reps.2.2.2.2.2.2.2.2.2.2.2.1] at h
  rw [show r3 () = i7r 2 from rfl, h]
  rfl

theorem t11_enum {y : P45}
    (hy : y ∈ QA45.originalSubgroup ∧ y * r3 () = r3 () * y) :
    ∃ i < 96, PRep 45 6 (T11Z.T i) y := by
  obtain ⟨-, hN, hng, h0, hc⟩ := t11binds
  obtain ⟨hcard, hall⟩ := group_A (g := t11g) (fun k hk => (prep_t11g k hk).1) T11Z.cl T11Z.tr
    (by norm_num) h0 T11Z.k
  have hle : closure (t11g '' {k | k < 5}) ≤ A ⊓ centralizer ({r3 ()} : Set P45) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk5 : k < 5 := hk
    refine mem_inf.2 ⟨(prep_t11g k hk5).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_eq22 (prep_t11g k hk5).1 prep_t11r (allN_spec hc k hk5)
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_t11C, hcard]))
  have hy' : y ∈ closure (t11g '' {k | k < 5}) := by
    rw [heq]
    exact mem_inf.2 ⟨hy.1, mem_centralizer_singleton_iff.2 hy.2⟩
  obtain ⟨i, hi, hp⟩ := hall y hy'
  exact ⟨i, by omega, hp⟩

theorem mem_t11C {g : P45} :
    g ∈ centL (elemsT QA45) (r3 ()) ↔ g ∈ QA45.originalSubgroup ∧ g * r3 () = r3 () * g := by
  simp only [centL, List.mem_filter, decide_eq_true_eq, mem_elemsT QA45 QA45_ok]

theorem mem_t11C3 {g : P45} :
    g ∈ cubeL (centL (elemsT QA45) (r3 ())) ↔
      (g ∈ QA45.originalSubgroup ∧ g * r3 () = r3 () * g) ∧ g ^ 3 = 1 ∧ g ≠ 1 := by
  simp only [cubeL, List.mem_filter, decide_eq_true_eq, mem_t11C]

theorem t11_zeta :
    zeta0 () ∈ QP45.originalSubgroup ∧ (zeta0 () * zeta0 () = 1 ∧ zeta0 () ≠ 1) ∧
      Nat.card ↥(A ⊓ centralizer ({zeta0 ()} : Set P45)) = 1152 ∧
      zeta0 () * r3 () = r3 () * zeta0 () := by
  obtain ⟨hl, hz, -, -, hzi, hzf, hzr, -⟩ := t11elts
  have hw := prep_xy (allN_spec hl 0 (by norm_num))
  have hP : zeta0 () ∈ QP45.originalSubgroup := by
    rw [← eqP_sound hz hw.1 prep_t11z]
    exact hw.2
  have hinv := inv_of_isInvK prep_t11z hzi
  refine ⟨hP, hinv, ?_, comm_of_eq22 prep_t11z prep_t11r hzr⟩
  rw [card_cent_eq (QP45_le_QA45 hP) hinv.1 hinv.2, ← fixK_eq prep_t11z, hzf]
  rfl

theorem t11_g :
    (g1 () ∈ QP45.originalSubgroup ∧ (g1 () ∈ QA45.originalSubgroup ∧ g1 () * r3 () = r3 () * g1 ()) ∧
      g1 () ^ 3 = 1 ∧ g1 () ≠ 1) ∧
    (g2 () ∈ QP45.originalSubgroup ∧ (g2 () ∈ QA45.originalSubgroup ∧ g2 () * r3 () = r3 () * g2 ()) ∧
      g2 () ^ 3 = 1 ∧ g2 () ≠ 1) := by
  obtain ⟨hl, -, h1, h2, -, -, -, hc1, hc2, hr1, hr2, -⟩ := t11elts
  have hw1 := prep_xy (allN_spec hl 1 (by norm_num))
  have hw2 := prep_xy (allN_spec hl 2 (by norm_num))
  have hP1 : g1 () ∈ QP45.originalSubgroup := by
    rw [← eqP_sound h1 hw1.1 prep_t11g1]
    exact hw1.2
  have hP2 : g2 () ∈ QP45.originalSubgroup := by
    rw [← eqP_sound h2 hw2.1 prep_t11g2]
    exact hw2.2
  exact ⟨⟨hP1, ⟨QP45_le_QA45 hP1, comm_of_eq22 prep_t11g1 prep_t11r hr1⟩,
      (cubeK_iff prep_t11g1).1 hc1⟩,
    ⟨hP2, ⟨QP45_le_QA45 hP2, comm_of_eq22 prep_t11g2 prep_t11r hr2⟩, (cubeK_iff prep_t11g2).1 hc2⟩⟩

theorem t11_k1 :
    k1Chk (elemsT QA45) (elemsT QP45) (centL (elemsT QA45) (r3 ()))
      (cubeL (centL (elemsT QA45) (r3 ()))) (r3 ()) (zeta0 ()) = true := by
  obtain ⟨hP, hinv, hcard, hr⟩ := t11_zeta
  unfold k1Chk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, mem_elemsT QP45 QP45_ok,
    cntL_eq]
  refine ⟨⟨⟨⟨⟨hP, hinv⟩, hcard⟩, hr⟩, fun g hg => ?_⟩, fun g hg => ?_⟩
  · rw [mem_t11C3] at hg
    obtain ⟨i, hi, hp⟩ := t11_enum hg.1
    have hc := t11c3
    unfold t11c3K at hc
    have h := allN_spec hc i hi
    beta_reduce at h
    rw [(cubeK_iff hp).2 hg.2, Bool.not_true, Bool.false_or] at h
    exact comm_of_eq22 hp prep_t11z h
  · rw [mem_t11C] at hg
    have h := pow_card_eq_one' (G := ↥(A ⊓ centralizer ({r3 ()} : Set P45)))
      (x := ⟨g, mem_inf.2 ⟨hg.1, mem_centralizer_singleton_iff.2 hg.2⟩⟩)
    rw [card_t11C] at h
    have h' := congrArg Subtype.val h
    simpa using h'

theorem t11_k2 :
    k2Chk (elemsT QP45) (cubeL (centL (elemsT QA45) (r3 ()))) (r3 ()) (zeta0 ()) (lam0 ())
      (g1 ()) (g2 ()) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgi, hcomm⟩ := t11elts
  obtain ⟨⟨hP1, hC1, hc1⟩, ⟨hP2, hC2, hc2⟩⟩ := t11_g
  have hb := inv_of_isInvK (prep_pcomp hn45 prep_t11g1 prep_t11g2) hgi
  have e := eqP_sound hcomm (prep_pcomp hn45 (prep_pcomp hn45 (prep_pcomp hn45 prep_t11r prep_t11y)
    prep_t11r) prep_t11y) (prep_pcomp hn45 (prep_pcomp hn45 prep_t11g1 prep_t11g2) prep_t11z)
  have hr := i7_inv (k := 2) (by norm_num)
  have hy := i7_inv (k := 1) (by norm_num)
  have er : (r3 ())⁻¹ = r3 () := inv_eq_of_mul_eq_one_right hr.1
  have ey : (Certificates.OmegaT0.yB ())⁻¹ = Certificates.OmegaT0.yB () :=
    inv_eq_of_mul_eq_one_right hy.1
  unfold k2Chk lam0
  simp only [Bool.and_eq_true, decide_eq_true_eq, mem_elemsT QP45 QP45_ok, mem_t11C3]
  refine ⟨⟨⟨⟨⟨⟨i7_mem01 (k := 1) (by norm_num), hP1⟩, hP2⟩, ⟨hC1, hc1⟩⟩, ⟨hC2, hc2⟩⟩, hb⟩, ?_⟩
  rw [er, ey]
  exact e

theorem t11_k3 :
    k3Chk (elemsT QA45) (elemsT QP45) (centL (elemsT QA45) (r3 ()))
      (cubeL (centL (elemsT QA45) (r3 ()))) (zeta0 ()) = true := by
  obtain ⟨⟨-, hC1, hc1⟩, -⟩ := t11_g
  unfold k3Chk
  rw [List.all_eq_true]
  intro x hx
  rw [mem_t11C] at hx
  apply notb_or_dec
  intro hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cntL_eq] at hb
  obtain ⟨⟨⟨hall, hinv⟩, -⟩, hcard⟩ := hb
  have hg1 := hall (g1 ()) (mem_t11C3.2 ⟨hC1, hc1⟩)
  obtain ⟨i, hi, hp⟩ := t11_enum hx
  have hk := t11k3
  unfold t11k3K at hk
  have h := allN_spec hk i hi
  beta_reduce at h
  have e1 : isInvK 45 6 (T11Z.T i) = true :=
    (isInvK_iff hn45 hp).2 (orderOf_eq_prime (by rw [sq]; exact hinv.1) hinv.2)
  have e2 : Nat.beq (fixK 45 6 (T11Z.T i)) 13 = true := by
    have h13 := tauFix_1152 ((card_cent_eq hx.1 hinv.1 hinv.2).symm.trans hcard)
    rw [fixK_eq hp, h13]
    rfl
  have e3 : eq22 45 6 (mask 6) t11g1P (T11Z.T i) (T11Z.T i) t11g1P = true :=
    eq22_of_eq prep_t11g1 hp hp prep_t11g1 hg1
  rw [e1, e2, e3, Bool.not_true, Bool.false_or, Bool.false_or, Bool.false_or] at h
  exact eqP_sound h hp prep_t11z

theorem t11_k4 :
    k4Chk (elemsT QA45) (cubeL (centL (elemsT QA45) (r3 ()))) (zeta0 ()) = true := by
  obtain ⟨hP, -, -, -⟩ := t11_zeta
  unfold k4Chk
  rw [List.all_eq_true]
  intro a1 ha1
  rw [List.all_eq_true]
  intro a2 ha2
  apply notb_or
  intro hb
  rw [decide_eq_true_eq] at hb
  rw [mem_t11C3] at ha1 ha2
  obtain ⟨i, hi, hpi⟩ := t11_enum ha1.1
  obtain ⟨j, hj, hpj⟩ := t11_enum ha2.1
  have hk := t11k4
  unfold t11k4K at hk
  have h := allN_spec hk i hi
  beta_reduce at h
  rw [(cubeK_iff hpi).2 ha1.2, Bool.not_true, Bool.false_or] at h
  have h2 := allN_spec h j hj
  beta_reduce at h2
  have e2 : isInvK 45 6 (pcomp 45 6 (mask 6) (T11Z.T i) (T11Z.T j)) = true :=
    (isInvK_iff hn45 (prep_pcomp hn45 hpi hpj)).2 (orderOf_eq_prime (by rw [sq]; exact hb.1) hb.2)
  rw [(cubeK_iff hpj).2 ha2.2, e2, Bool.not_true, Bool.false_or, Bool.false_or,
    Bool.and_eq_true] at h2
  have hpp := prep_pcomp hn45 (prep_pcomp hn45 hpi hpj) prep_t11z
  have hv := inv_of_isInvK hpp h2.1
  have hA : a1 * a2 * zeta0 () ∈ A := mul_mem (mul_mem ha1.1.1 ha2.1.1) (QP45_le_QA45 hP)
  simp only [Bool.and_eq_true, decide_eq_true_eq, cntL_eq]
  refine ⟨hv, ?_⟩
  rw [card_cent_eq hA hv.1 hv.2, ← fixK_eq hpp, Nat.eq_of_beq_eq_true h2.2]
  rfl

theorem omegaT11_check : Certificates.OmegaT11.check () = true := by
  unfold Certificates.OmegaT11.check
  simp only [t11_k1, t11_k2, t11_k3, t11_k4, Bool.and_self]

end CertificateChecks.KernelA45

end
