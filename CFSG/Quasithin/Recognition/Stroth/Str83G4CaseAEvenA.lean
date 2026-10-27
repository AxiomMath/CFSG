module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAA2
public import CFSG.GH74.Uniqueness.Bender.FrameTorus
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABall

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_even_Z_sup_Qy
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAZ (x b) ⊔ CosetGeom.Qy (x 0) = caseAS (x 0) (x 1) := by
  classical
  let A : Subgroup (f112Amalgam L1 L2 S).Ghat := caseAZ (x b)
  let B : Subgroup (f112Amalgam L1 L2 S).Ghat := CosetGeom.Qy (x 0)
  let T : Subgroup (f112Amalgam L1 L2 S).Ghat := caseAS (x 0) (x 1)
  have hb1 : 1 ≤ b := by omega
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have h01 : x 1 ∈ CosetGeom.nbrs (x 0) := by simpa [CosetGeom.nbrs] using x.adj 0 hb1
  have hx0nbrs1 : x 0 ∈ CosetGeom.nbrs (x 1) := by
    simpa [CosetGeom.nbrs] using (x.adj 0 hb1).symm
  have hbm1_b : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x b) := by
    simpa [Nat.sub_add_cancel hb1] using x.adj (b - 1) (by omega)
  have hbm1_nbrs : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    simpa [CosetGeom.nbrs] using hbm1_b
  have hbm1_nbrs' : x (b - 1) ∈ CosetGeom.nbrs (x b) := by
    simpa [CosetGeom.nbrs] using hbm1_b.symm
  have hdx0b : CosetGeom.dist (x 0) (x b) = b :=
    hx.geodesic.dist_eq hconn (j := b) le_rfl
  have hvb : CosetGeom.vtype (x b) = true := by
    have hd : CosetGeom.dist (x b) (x 0) = b := by
      rw [CosetGeom.dist_comm]; exact hdx0b
    have h := (CosetGeom.vtype_eq_iff_even_dist rfl (x b) (x 0)).mpr (by rw [hd]; exact hbe)
    rwa [hx.type_two] at h
  have hvbm1 : CosetGeom.vtype (x (b - 1)) = false := by
    have hne := CosetGeom.vtype_ne_of_adj hbm1_b
    rw [hvb] at hne
    cases h : CosetGeom.vtype (x (b - 1)) <;> simp_all
  have hdist_b1 : CosetGeom.dist (x b) (x 1) = b - 1 := by
    rw [CosetGeom.dist_comm]
    have h : (f112Amalgam L1 L2 S).graphHat.dist (x 1) (x b) = b - 1 := by
      have h0 := (hx.geodesic.drop hconn 1 hb1).dist_eq hconn (j := b - 1) le_rfl
      have h' : 1 + (b - 1) = b := by omega
      simpa [h'] using h0
    exact h
  have hdist_0_bm1 : CosetGeom.dist (x 0) (x (b - 1)) = b - 1 :=
    hx.geodesic.dist_eq hconn (j := b - 1) (by omega)
  have hA_S : A ≤ T := by
    have h1 : A ≤ CosetGeom.Qy (x 1) :=
      hx.ball (x b) (x 1) hvb (le_of_eq hdist_b1)
    have h2 : CosetGeom.Qy (x 1) ≤ caseAS (x 0) (x 1) := by
      rw [caseAS_comm]
      exact caseA_Qy_le_caseAS hfr hx0nbrs1
    exact h1.trans h2
  have hB_S : B ≤ T := caseA_Qy_le_caseAS hfr h01
  have hAB_S : A ⊔ B ≤ T := sup_le hA_S hB_S
  have hN : T ≤ Subgroup.normalizer (B : Set (f112Amalgam L1 L2 S).Ghat) :=
    (caseAS_le_stab_left (x 0) (x 1)).trans (caseA_stab_le_normalizer_Qy (x 0))
  have hBS : B.relIndex T = 2 ^ (2 * a + 1) :=
    caseA_relIndex_Qy_caseAS_type2 hfr hx.type_two h01
  have hdiamond : (A ⊓ B).relIndex A = B.relIndex (A ⊔ B) := by
    rw [Subgroup.inf_relIndex_left]
    exact (CFSG.ABGTheoremB.relIndex_sup_right_of_le_normalizer (hA_S.trans hN)).symm
  obtain ⟨y, hyA0, hynotQ⟩ := SetLike.not_le_iff_exists.mp hx.not_le
  have hyS : y ∈ caseAS (x b) (x (b - 1)) := by
    have hyQbm1 : y ∈ CosetGeom.Qy (x (b - 1)) :=
      hx.ball (x 0) (x (b - 1)) hx.type_two (le_of_eq hdist_0_bm1) hyA0
    rw [caseAS_comm]
    exact caseA_Qy_le_caseAS hfr hbm1_nbrs hyQbm1
  have hcomm_zpow : ⁅A, Subgroup.zpowers y⁆ = caseAZ (x (b - 1)) :=
    caseA_commutator_Z_zpowers hfr hvb hbm1_nbrs' hyS hynotQ
  let C : Subgroup (f112Amalgam L1 L2 S).Ghat :=
    Subgroup.centralizer ({y} : Set (f112Amalgam L1 L2 S).Ghat)
  have hA_le_stab : A ≤ CosetGeom.stab (x b) :=
    (caseA_Z_le_Qy (x b)).trans (caseA_Qy_le_stab (x b))
  haveI : Finite ↥A := by
    haveI : Finite ↥(CosetGeom.stab (x b)) := caseA_finite_stab L1 L2 S (x b)
    exact Finite.of_injective (Subgroup.inclusion hA_le_stab)
      (Subgroup.inclusion_injective hA_le_stab)
  haveI : Finite ↥(A ⊓ C) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : A ⊓ C ≤ A))
      (Subgroup.inclusion_injective (inf_le_left : A ⊓ C ≤ A))
  haveI : Nonempty ↥(A ⊓ C) := ⟨1⟩
  have ht2 : y * y = 1 := by
    rw [← pow_two]
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hyA0
  have hcomm : ∀ z ∈ A, ∀ w ∈ A, z * w = w * z :=
    fun z hz w hw => A4.mul_comm_of_mem_omegaOneCenterOf hz hw
  have hyNorm : y ∈ Subgroup.normalizer (A : Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_Z (x b) (caseAS_le_stab_left (x b) (x (b - 1)) hyS)
  have hnorm : ∀ z ∈ A, y * z * y⁻¹ ∈ A :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp hyNorm z).mp hz
  have hcard1 : Nat.card ↥(A ⊓ C) * Nat.card ↥⁅A, Subgroup.zpowers y⁆ = Nat.card ↥A :=
    CFSG.GH74.Uniqueness.Bender.Frame.card_inf_centralizer_mul_card_commutator
      (F := A) (t := y) ht2 hcomm hnorm
  have hcard1' : Nat.card ↥(A ⊓ C) * Nat.card ↥(caseAZ (x (b - 1))) = Nat.card ↥A := by
    rw [hcomm_zpow] at hcard1
    exact hcard1
  have hZcard : Nat.card ↥(caseAZ (x (b - 1))) = 2 ^ (2 * a + 1) :=
    caseA_card_Z_type1 hfr hvbm1
  have hrelcard : Nat.card ↥(A ⊓ C) * (A ⊓ C).relIndex A = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ C) (K := A)
    rw [inf_of_le_left inf_le_left, mul_comm] at h
    exact h
  have hcancel : Nat.card ↥(A ⊓ C) * (A ⊓ C).relIndex A =
      Nat.card ↥(A ⊓ C) * Nat.card ↥(caseAZ (x (b - 1))) := by
    rw [hrelcard, hcard1']
  have hrelAq : (A ⊓ C).relIndex A = 2 ^ (2 * a + 1) := by
    have hposC : (0 : ℕ) < Nat.card ↥(A ⊓ C) := Nat.card_pos
    exact (mul_left_cancel₀ hposC.ne' hcancel).trans hZcard
  have hBC : B ≤ C :=
    fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
      (caseA_Z_commute_Qy (x 0) hyA0 hz).symm
  have hle : A ⊓ B ≤ A ⊓ C := le_inf inf_le_left (inf_le_right.trans hBC)
  have hdvd : (A ⊓ C).relIndex A ∣ (A ⊓ B).relIndex A :=
    Subgroup.relIndex_dvd_of_le_left (H := A ⊓ B) (K := A ⊓ C) (L := A) hle
  have hnonzero : (A ⊓ B).relIndex A ≠ 0 := by
    rw [hdiamond]
    intro hzero
    have h0 := Subgroup.relIndex_eq_zero_of_le_right (H := B) (K := A ⊔ B) (L := T) hAB_S hzero
    rw [hBS] at h0
    exact (pow_ne_zero (2 * a + 1) (by norm_num : (2 : ℕ) ≠ 0)) h0
  have hlower : 2 ^ (2 * a + 1) ≤ (A ⊓ B).relIndex A := by
    have hdvd' : 2 ^ (2 * a + 1) ∣ (A ⊓ B).relIndex A := by
      rw [← hrelAq]; exact hdvd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hnonzero) hdvd'
  have hprod : B.relIndex (A ⊔ B) * (A ⊔ B).relIndex T = 2 ^ (2 * a + 1) := by
    rw [← hBS]
    exact Subgroup.relIndex_mul_relIndex (H := B) (K := A ⊔ B) (L := T) le_sup_right hAB_S
  have hprodA : (A ⊓ B).relIndex A * (A ⊔ B).relIndex T = 2 ^ (2 * a + 1) := by
    rw [hdiamond]; exact hprod
  have hdiv : (A ⊓ B).relIndex A ∣ 2 ^ (2 * a + 1) := ⟨_, hprodA.symm⟩
  have hle2 : (A ⊓ B).relIndex A ≤ 2 ^ (2 * a + 1) :=
    Nat.le_of_dvd (pow_pos (by norm_num) _) hdiv
  have hABrel : (A ⊓ B).relIndex A = 2 ^ (2 * a + 1) := le_antisymm hle2 hlower
  have hrelS : (A ⊔ B).relIndex T = 1 := by
    have h := hprodA
    rw [hABrel] at h
    exact mul_left_cancel₀ (pow_ne_zero (2 * a + 1) (by norm_num : (2 : ℕ) ≠ 0))
      (by simpa using h)
  exact le_antisymm hAB_S (Subgroup.relIndex_eq_one.mp hrelS)

theorem caseA_even_exists_Z_smul
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b)
    {l m : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hm : m ∈ CosetGeom.nbrs (x 0))
    (hl1 : l ≠ x 1) (hm1 : m ≠ x 1) :
    ∃ g : f112Acting L1 L2 S, (g : (f112Amalgam L1 L2 S).Ghat) ∈ caseAZ (x b) ∧ g • l = m := by
  have hb1 : 1 ≤ b := by omega
  have h01 : x 1 ∈ CosetGeom.nbrs (x 0) := by simpa [CosetGeom.nbrs] using x.adj 0 hb1
  obtain ⟨s, hsS, hsm⟩ :=
    caseA_exists_caseAS_smul_eq hfr hx.type_two h01 hl hm hl1 hm1
  have hE1 := caseA_even_Z_sup_Qy hfr hx hbe hb
  have hA_T : caseAZ (x b) ≤ caseAS (x 0) (x 1) :=
    le_sup_left.trans (le_of_eq hE1)
  have hN : caseAS (x 0) (x 1) ≤
      Subgroup.normalizer (CosetGeom.Qy (x 0) : Set (f112Amalgam L1 L2 S).Ghat) :=
    (caseAS_le_stab_left (x 0) (x 1)).trans (caseA_stab_le_normalizer_Qy (x 0))
  have hA_normB : caseAZ (x b) ≤
      Subgroup.normalizer (CosetGeom.Qy (x 0) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hA_T.trans hN
  have hsmem : (s : (f112Amalgam L1 L2 S).Ghat) ∈
      (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) *
        (CosetGeom.Qy (x 0) : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (caseAZ (x b)) (CosetGeom.Qy (x 0))
      hA_normB]
    rw [hE1]; exact hsS
  rw [Set.mem_mul] at hsmem
  obtain ⟨z0, hz0A, q0, hq0B, hz0q0⟩ := hsmem
  have hS_G0 : caseAS (x 0) (x 1) ≤
      (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2 :=
    (caseAS_le_stab_left (x 0) (x 1)).trans (CosetGeom.stab_le (x 0))
  have hB_G0 : CosetGeom.Qy (x 0) ≤
      (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2 :=
    (caseA_Qy_le_caseAS hfr h01).trans hS_G0
  let z : f112Acting L1 L2 S := ⟨z0, hS_G0 (hA_T hz0A)⟩
  let q : f112Acting L1 L2 S := ⟨q0, hB_G0 hq0B⟩
  have hzA : (z : (f112Amalgam L1 L2 S).Ghat) ∈ caseAZ (x b) := hz0A
  have hqB : (q : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy (x 0) := hq0B
  have hzq : z * q = s := by
    apply Subtype.ext
    show (z : (f112Amalgam L1 L2 S).Ghat) * (q : (f112Amalgam L1 L2 S).Ghat) =
      (s : (f112Amalgam L1 L2 S).Ghat)
    exact hz0q0
  have hldist : CosetGeom.dist (x 0) l ≤ 1 :=
    (CosetGeom.dist_eq_one_iff_adj.mpr (by simpa [CosetGeom.nbrs] using hl)).le
  have hqfix : q • l = l :=
    CosetGeom.smul_eq_of_mem_stab
      ((CosetGeom.mem_ballStab.mp (caseA_Qy_le_ballStab_one hfr (x 0) hqB)) l hldist)
  refine ⟨z, hzA, ?_⟩
  calc z • l = (z * q) • l := (by rw [mul_smul, hqfix])
    _ = s • l := by rw [hzq]
    _ = m := hsm

theorem caseA_even_centralizer_Z_le
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAZ (x 0) ⊓ Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) ≤
      caseAZ (x 1) := by
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyA0, hyC⟩ := hy
  have hb1 : 1 ≤ b := by omega
  have h01 : x 1 ∈ CosetGeom.nbrs (x 0) := by simpa [CosetGeom.nbrs] using x.adj 0 hb1
  have hE1 := caseA_even_Z_sup_Qy hfr hx hbe hb
  have hycentS : y ∈ Subgroup.centralizer
      (caseAS (x 0) (x 1) : Set (f112Amalgam L1 L2 S).Ghat) := by
    have h1 : caseAZ (x b) ≤
        Subgroup.centralizer ({y} : Set (f112Amalgam L1 L2 S).Ghat) :=
      fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hyC) a ha)
    have h2 : CosetGeom.Qy (x 0) ≤
        Subgroup.centralizer ({y} : Set (f112Amalgam L1 L2 S).Ghat) :=
      fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
        (caseA_Z_commute_Qy (x 0) hyA0 hw).symm
    have hle : caseAZ (x b) ⊔ CosetGeom.Qy (x 0) ≤
        Subgroup.centralizer ({y} : Set (f112Amalgam L1 L2 S).Ghat) := sup_le h1 h2
    rw [hE1] at hle
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
  have hS : caseAZ (x 0) ⊓ Subgroup.centralizer
      (caseAS (x 0) (x 1) : Set (f112Amalgam L1 L2 S).Ghat) = caseAZ (x 1) :=
    caseA_Z_inf_centralizer_caseAS hfr hx.type_two h01
  rw [← hS]
  exact ⟨hyA0, hycentS⟩

theorem caseA_even_Z_inf_Qy_end
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b)
    {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    caseAZ l ⊓ CosetGeom.Qy (x b) = ⊥ := by
  have hb1 : 1 ≤ b := by omega
  have h01 : x 1 ∈ CosetGeom.nbrs (x 0) := by simpa [CosetGeom.nbrs] using x.adj 0 hb1
  refine le_antisymm ?_ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzZl, hzQb⟩ := hz
  have hl_adj : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hl_type : CosetGeom.vtype l = false := by
    have hne := CosetGeom.vtype_ne_of_adj hl_adj
    rw [hx.type_two] at hne
    cases h : CosetGeom.vtype l <;> simp_all
  have hzZ0 : z ∈ caseAZ (x 0) :=
    caseA_Z_le_Z_of_adj hfr hl_type hl_adj.symm hzZl
  have hzC : z ∈ Subgroup.centralizer
      (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact caseA_Z_commute_Qy (x b) hw hzQb
  have hzZ1 : z ∈ caseAZ (x 1) :=
    caseA_even_centralizer_Z_le hfr hx hbe hb ⟨hzZ0, hzC⟩
  have hbot : caseAZ l ⊓ caseAZ (x 1) = ⊥ :=
    caseA_Z_inf_Z_eq_bot hfr hx.type_two hl h01 hl1
  have hmem : z ∈ (⊥ : Subgroup (f112Amalgam L1 L2 S).Ghat) := by
    rw [← hbot]; exact ⟨hzZl, hzZ1⟩
  exact Subgroup.mem_bot.mp hmem

private theorem evenab_bad_contra
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {c : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat (c + 2)}
    (hx : caseACritPath L1 L2 S (c + 2) x) (hbe : Even (c + 2)) (hb : 5 ≤ c + 2)
    {w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs (x 0)) (hw1 : w ≠ x 1)
    {ε : f112Gamma L1 L2 S} (hε : ε ∈ CosetGeom.nbrs w)
    (hbad : ¬ caseAZ ε ≤ CosetGeom.Qy (x c)) : False := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hcx : c ≤ c + 2 := by omega
  have hεv : CosetGeom.vtype ε = true := by
    have hwv : CosetGeom.vtype w = false := by
      have hne := CosetGeom.vtype_ne_of_adj hw
      rw [hx.type_two] at hne
      cases h : CosetGeom.vtype w <;> simp_all
    have hne := CosetGeom.vtype_ne_of_adj hε
    rw [hwv] at hne
    cases h : CosetGeom.vtype ε <;> simp_all
  have hcv : CosetGeom.vtype (x c) = true := by
    have hcd : CosetGeom.dist (x 0) (x c) = c := hx.geodesic.dist_eq hconn (by omega)
    have hce : Even c := by obtain ⟨k, hk⟩ := hbe; exact ⟨k - 1, by omega⟩
    have h := (CosetGeom.vtype_eq_iff_even_dist rfl (x 0) (x c)).mpr (by rw [hcd]; exact hce)
    rw [hx.type_two] at h
    exact h.symm
  have hdist_le : CosetGeom.dist ε (x c) ≤ c + 2 := by
    have h1 : CosetGeom.dist ε (x 0) ≤ 2 := by
      have h2 : CosetGeom.dist ε w = 1 :=
        CosetGeom.dist_eq_one_iff_adj.mpr hε.symm
      have h3 : CosetGeom.dist w (x 0) = 1 :=
        CosetGeom.dist_eq_one_iff_adj.mpr hw.symm
      have h4 : CosetGeom.dist ε (x 0) ≤
          CosetGeom.dist ε w + CosetGeom.dist w (x 0) :=
        CosetGeom.dist_triangle_of_adj hε.symm (x 0)
      omega
    have h5 : CosetGeom.dist (x 0) (x c) = c := hx.geodesic.dist_eq hconn (by omega)
    have h6 : CosetGeom.dist ε (x c) ≤
        CosetGeom.dist ε (x 0) + CosetGeom.dist (x 0) (x c) :=
      hconn.dist_triangle (u := ε) (v := x 0) (w := x c)
    omega
  have hdist_ge : c + 2 ≤ CosetGeom.dist ε (x c) := by
    by_contra hlt
    exact hbad (hx.ball ε (x c) hεv (by omega))
  have hdist : CosetGeom.dist ε (x c) = c + 2 := le_antisymm hdist_le hdist_ge
  let p : GPath (f112Amalgam L1 L2 S).graphHat c := x.take c hcx
  have hp0 : p 0 = x 0 := GPath.take_apply_of_le x c hcx (by omega)
  have h1 : (f112Amalgam L1 L2 S).graphHat.Adj w (p 0) := by rw [hp0]; exact hw.symm
  have h2 : (f112Amalgam L1 L2 S).graphHat.Adj ε (GPath.cons w p h1 0) := by
    rw [GPath.cons_zero]; exact hε.symm
  let z : GPath (f112Amalgam L1 L2 S).graphHat (c + 2) :=
    GPath.cons ε (GPath.cons w p h1) h2
  have hz0 : z 0 = ε := by
    show GPath.cons ε (GPath.cons w p h1) h2 0 = ε
    rw [GPath.cons_zero]
  have hzlast : z (c + 2) = x c := by
    show GPath.cons ε (GPath.cons w p h1) h2 ((c + 1) + 1) = x c
    rw [GPath.cons_succ, GPath.cons_succ]
    exact GPath.take_apply_of_le x c hcx (le_refl c)
  have hzc1 : z (c + 1) = x (c - 1) := by
    show GPath.cons ε (GPath.cons w p h1) h2 (c + 1) = x (c - 1)
    rw [GPath.cons_succ]
    show (if c = 0 then w else p (c - 1)) = x (c - 1)
    rw [if_neg (by omega : c ≠ 0)]
    exact GPath.take_apply_of_le x c hcx (by omega)
  have hz1 : z 1 = w := by
    show GPath.cons ε (GPath.cons w p h1) h2 1 = w
    rw [GPath.cons_succ, GPath.cons_zero]
  have hzcrit : caseACritPath L1 L2 S (c + 2) z :=
    { geodesic := by
        show CosetGeom.dist (z 0) (z (c + 2)) = c + 2
        rw [hz0, hzlast]; exact hdist
      type_two := hεv
      ball := hx.ball
      not_le := by rw [hz0, hzlast]; exact hbad }
  have hZw : caseAZ w = caseAZ (x (c - 1)) := by
    have hA2 := caseA_Z_one_eq_Z_pred hfr hzcrit hbe hb
    have hzl : z ((c + 2) - 1) = x (c - 1) := hzc1
    rw [hz1, hzl] at hA2
    exact hA2
  have hc1adj : (f112Amalgam L1 L2 S).graphHat.Adj (x (c - 1)) (x c) := by
    have h := x.adj (c - 1) (by omega)
    rwa [show c - 1 + 1 = c by omega] at h
  have hc1v : CosetGeom.vtype (x (c - 1)) = false := by
    have hne := CosetGeom.vtype_ne_of_adj hc1adj
    rw [hcv] at hne
    cases h : CosetGeom.vtype (x (c - 1)) <;> simp_all
  have hcd2 : CosetGeom.dist (x c) (x (c + 2)) ≤ (c + 2) - 1 := by
    have h : CosetGeom.dist (x c) (x (c + 2)) ≤ (c + 2) - c :=
      GPath.dist_le_sub hconn x (i := c) (j := c + 2) (by omega) (by omega)
    omega
  have hZwQ : caseAZ w ≤ CosetGeom.Qy (x (c + 2)) := by
    rw [hZw]
    exact (caseA_Z_le_Z_of_adj hfr hc1v hc1adj).trans (hx.ball (x c) (x (c + 2)) hcv hcd2)
  obtain ⟨t, htZ, htQ⟩ :=
    SetLike.not_le_iff_exists.mp (caseA_not_Z_le_Qy_start hfr hx hbe hb)
  have hE1 := caseA_even_Z_sup_Qy hfr hx hbe hb
  have htS : t ∈ caseAS (x 0) (x 1) := by
    rw [← hE1]
    exact (le_sup_left : caseAZ (x (c + 2)) ≤
      caseAZ (x (c + 2)) ⊔ CosetGeom.Qy (x 0)) htZ
  have htstab0 : t ∈ CosetGeom.stab (x 0) := caseAS_le_stab_left (x 0) (x 1) htS
  have htstab1 : t ∈ CosetGeom.stab (x 1) := caseAS_le_stab_right (x 0) (x 1) htS
  have ht2 : ∃ k, orderOf t = 2 ^ k := by
    have hsq : t ^ 2 = 1 := CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf htZ
    have hne : t ≠ 1 := by
      intro h1
      exact htQ (by rw [h1]; exact (CosetGeom.Qy (x 0)).one_mem)
    exact ⟨1, by rw [orderOf_eq_prime hsq hne]; norm_num⟩
  obtain ⟨htmem, htfix0⟩ := CosetGeom.mem_stab.mp htstab0
  let hA : f112Acting L1 L2 S := ⟨t, htmem⟩
  have hAfix0 : hA • (x 0) = x 0 := htfix0
  have hw1nbr : x 1 ∈ CosetGeom.nbrs (x 0) := x.adj 0 (by omega)
  have hmove : hA • w ≠ w := by
    intro hfix
    apply htQ
    refine caseA_mem_Qy_of_fixes_two_nbrs hfr hw hw1nbr hw1 htstab0 ?_ htstab1 ht2
    exact CosetGeom.mem_stab_of_smul_eq hfix
  have hw' : hA • w ∈ CosetGeom.nbrs (x 0) := by
    have h := (CosetGeom.smul_adj hA).mpr hw
    rwa [hAfix0] at h
  have hle : caseAZ w ≤ caseAZ (hA • w) := by
    rw [caseA_Z_smul hA w]
    intro z hz
    rw [mem_conjSub]
    have hcomm : (hA : (f112Amalgam L1 L2 S).Ghat) * z
        = z * (hA : (f112Amalgam L1 L2 S).Ghat) :=
      caseA_Z_commute_Qy (x (c + 2)) htZ (hZwQ hz)
    have hzy : (hA : (f112Amalgam L1 L2 S).Ghat)⁻¹ * z *
        (hA : (f112Amalgam L1 L2 S).Ghat) = z := by
      calc (hA : (f112Amalgam L1 L2 S).Ghat)⁻¹ * z *
            (hA : (f112Amalgam L1 L2 S).Ghat)
          = (hA : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
              (z * (hA : (f112Amalgam L1 L2 S).Ghat)) := by group
        _ = (hA : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
              ((hA : (f112Amalgam L1 L2 S).Ghat) * z) := by rw [← hcomm]
        _ = z := by group
    rw [hzy]; exact hz
  have hbot : caseAZ w = ⊥ := by
    have h := caseA_Z_inf_Z_eq_bot hfr hx.type_two hw hw' (Ne.symm hmove)
    rwa [inf_eq_left.mpr hle] at h
  exact caseA_Z_ne_bot hfr w hbot

private theorem evenab_Z_le_of_nbr
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {c : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat (c + 2)}
    (hx : caseACritPath L1 L2 S (c + 2) x) (hbe : Even (c + 2)) (hb : 5 ≤ c + 2)
    {w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs (x 0))
    {ε : f112Gamma L1 L2 S} (hε : ε ∈ CosetGeom.nbrs w) :
    caseAZ ε ≤ CosetGeom.Qy (x c) := by
  by_cases hw1 : w = x 1
  · subst hw1
    have hx1v : CosetGeom.vtype (x 1) = false := by
      have hne := CosetGeom.vtype_ne_of_adj (x.adj 0 (by omega))
      rw [hx.type_two] at hne
      cases h : CosetGeom.vtype (x 1) <;> simp_all
    have hεv : CosetGeom.vtype ε = true := by
      have hne := CosetGeom.vtype_ne_of_adj hε
      rw [hx1v] at hne
      cases h : CosetGeom.vtype ε <;> simp_all
    have hdist : CosetGeom.dist ε (x c) ≤ (c + 2) - 1 := by
      have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
      have h1 : CosetGeom.dist ε (x 1) = 1 := by
        rw [CosetGeom.dist_comm]
        exact CosetGeom.dist_eq_one_iff_adj.mpr hε
      have h2 : CosetGeom.dist (x 1) (x c) ≤ c - 1 :=
        GPath.dist_le_sub hconn x (i := 1) (j := c) (by omega) (by omega)
      have h3 : CosetGeom.dist ε (x c) ≤
          CosetGeom.dist ε (x 1) + CosetGeom.dist (x 1) (x c) :=
        hconn.dist_triangle (u := ε) (v := x 1) (w := x c)
      omega
    exact hx.ball ε (x c) hεv hdist
  · by_contra hbad
    exact evenab_bad_contra hfr hx hbe hb hw hw1 hε hbad

theorem caseA_even_R_le_Qy
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAR (x 0) ≤ CosetGeom.Qy (x (b - 2)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  unfold caseAR
  refine iSup₂_le fun w hw => ?_
  unfold caseAX
  refine iSup₂_le fun ε hε => ?_
  exact evenab_Z_le_of_nbr hfr hx hbe hb hw hε

theorem caseA_even_not_X_le_Qy_pred
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b)
    {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    ¬ caseAX l ≤ CosetGeom.Qy (x (b - 1)) := by
  intro h
  let Y : Subgroup (f112Amalgam L1 L2 S).Ghat := caseAX l
  have hb1 : 1 ≤ b := by omega
  have hl_adj : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hx0l : x 0 ∈ CosetGeom.nbrs l := by
    simpa [CosetGeom.nbrs] using hl_adj.symm
  have hx1nbr : x 1 ∈ CosetGeom.nbrs (x 0) := by
    simpa [CosetGeom.nbrs] using x.adj 0 hb1
  have hbm1_b : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x b) := by
    simpa [Nat.sub_add_cancel hb1] using x.adj (b - 1) (by omega)
  have hbm1_nbrs : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    simpa [CosetGeom.nbrs] using hbm1_b
  have hbm1_nbrs' : x (b - 1) ∈ CosetGeom.nbrs (x b) := by
    simpa [CosetGeom.nbrs] using hbm1_b.symm
  have hxb_type : CosetGeom.vtype (x b) = true :=
    (hx.vtype_eq_true_iff_even le_rfl).mpr hbe
  have hx1v : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd hb1).mpr (by norm_num)
  have hl_false : CosetGeom.vtype l = false :=
    CosetGeom.vtype_eq_false_of_adj hl_adj hx.type_two
  have hZ_le_Y : caseAZ (x 0) ≤ Y := by
    show caseAZ (x 0) ≤ caseAX l
    exact le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs l) => caseAZ w) (x 0) hx0l
  have hZ_le_normalizer : caseAZ (x b) ≤
      Subgroup.normalizer (Y : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    calc ⁅caseAZ (x b), Y⁆
        ≤ ⁅caseAZ (x b), CosetGeom.Qy (x (b - 1))⁆ :=
          Subgroup.commutator_mono le_rfl h
      _ ≤ ⁅caseAZ (x b), caseAS (x (b - 1)) (x b)⁆ :=
          Subgroup.commutator_mono le_rfl (caseA_Qy_le_caseAS hfr hbm1_nbrs)
      _ = ⁅caseAZ (x b), caseAS (x b) (x (b - 1))⁆ := by rw [caseAS_comm]
      _ = caseAZ (x (b - 1)) := caseA_commutator_Z_caseAS hfr hxb_type hbm1_nbrs'
      _ = caseAZ (x 1) := (caseA_Z_one_eq_Z_pred hfr hx hbe hb).symm
      _ ≤ caseAZ (x 0) := caseA_Z_le_Z_of_adj hfr hx1v (x.adj 0 hb1).symm
      _ ≤ Y := hZ_le_Y
  have hX_eq_Y : ∀ m ∈ CosetGeom.nbrs (x 0), m ≠ x 1 → caseAX m = Y := by
    intro m hm hm1
    obtain ⟨g, hgZ, hgl⟩ := caseA_even_exists_Z_smul hfr hx hbe hb hl hm hl1 hm1
    have hnorm : (g : (f112Amalgam L1 L2 S).Ghat) ∈
        Subgroup.normalizer (Y : Set (f112Amalgam L1 L2 S).Ghat) := hZ_le_normalizer hgZ
    have hconj : conjSub (g : (f112Amalgam L1 L2 S).Ghat) Y = Y := by
      simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm)
    calc caseAX m = caseAX (g • l) := by rw [hgl]
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX l) := caseA_X_smul g l
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) Y := by rfl
      _ = Y := hconj
  have hX1_eq_Y : caseAX (x 1) = Y := by
    obtain ⟨m, hm, hm1, hml⟩ := caseA_exists_nbr_ne hfr hx.type_two (x 1) l
    obtain ⟨g, _, hgm, hgl⟩ :=
      caseA_exists_smul_two hfr hx.type_two hm hl hl hx1nbr hml hl1
    calc caseAX (x 1) = caseAX (g • l) := by rw [hgl]
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX l) := caseA_X_smul g l
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) Y := by rfl
      _ = caseAX (g • m) := by rw [caseA_X_smul g m, hX_eq_Y m hm hm1]
      _ = caseAX l := by rw [hgm]
      _ = Y := by rfl
  have hR_eq : caseAR (x 0) = Y := by
    unfold caseAR
    apply le_antisymm
    · apply iSup₂_le
      intro w hw
      by_cases hw1 : w = x 1
      · rw [hw1, hX1_eq_Y]
      · rw [hX_eq_Y w hw hw1]
    · calc Y = caseAX (x 1) := hX1_eq_Y.symm
        _ ≤ ⨆ (w) (_ : w ∈ CosetGeom.nbrs (x 0)), caseAX w :=
              le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (x 0)) => caseAX w)
                (x 1) hx1nbr
  have hN0 : CosetGeom.stab (x 0) ≤
      Subgroup.normalizer (Y : Set (f112Amalgam L1 L2 S).Ghat) := by
    simpa [hR_eq] using caseA_stab_le_normalizer_R (x 0)
  have hNl : CosetGeom.stab l ≤
      Subgroup.normalizer (Y : Set (f112Amalgam L1 L2 S).Ghat) := by
    simpa [Y] using caseA_stab_le_normalizer_X l
  have hX_le_Qy0 : caseAX l ≤ CosetGeom.Qy (x 0) := by
    refine caseA_X_le_Qy hx.ball hl_false ?_
    have hd : CosetGeom.dist l (x 0) = 1 := by
      rw [CosetGeom.dist_comm]
      exact CosetGeom.dist_eq_one_iff_adj.mpr hl_adj
    omega
  have hX_le_Qyl : caseAX l ≤ CosetGeom.Qy l := by
    refine caseA_X_le_Qy hx.ball hl_false ?_
    have hd : CosetGeom.dist l l = 0 := (CosetGeom.dist_eq_zero_iff rfl).mpr rfl
    omega
  have hY0 : Y ≤ CosetGeom.stab (x 0) := by
    simpa [Y] using hX_le_Qy0.trans (caseA_Qy_le_stab (x 0))
  have hYl : Y ≤ CosetGeom.stab l := by
    simpa [Y] using hX_le_Qyl.trans (caseA_Qy_le_stab l)
  have hYbot : Y = ⊥ := caseA_eq_bot_of_le_normalizer hfr hl hY0 hYl hN0 hNl
  have hZ0bot : caseAZ (x 0) = ⊥ := by
    rw [hYbot] at hZ_le_Y
    exact le_bot_iff.mp hZ_le_Y
  exact caseA_Z_ne_bot hfr (x 0) hZ0bot

end CFSG.Quasithin.Stroth

end
