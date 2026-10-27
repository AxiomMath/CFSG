module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.Quasithin.Background.F1Amalgam
public import Certificates.Certificate40702
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin.F112R.AJ2L

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.ComponentClassification.J2Cover
  CFSG.Quasithin.E2P.SporB

@[expose] noncomputable def rCtx : LatCtx R 315 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful rDelta_valid rfl rfl Certificates.certificate40702.1 rfl
    card_closure_rSg 4725 (by rw [card_R]; norm_num) Certificates.certificate40702.2.1

theorem rCtx_hL : rCtx.D.Om.map (fun o => o.lbl.size) = #[1, 9, 15, 3, 3] :=
  Certificates.certificate40702.2.2.1

theorem rCtx_S_card : Nat.card rCtx.S = 2 ^ 8 := rCtx.S_card

theorem rCtx_J : rCtx.J = 5 := lat_J_eq rCtx rCtx_hL

theorem rCtx_S : rCtx.S = sylowS.subgroupOf R := rCtx.hSeq.symm.trans closure_rSg

theorem rCtx_sylow : IsSylowTwoOf rCtx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨rCtx.S_isPGroup, ?_⟩
  rw [rCtx_S, index_sylowS]
  norm_num

theorem rCtx_card {j : ℕ} (hj : j < 5) :
    Nat.card (rCtx.Y j) = (#[1, 9, 15, 3, 3] : Array ℕ)[j]! * 2 ^ 8 :=
  lat_card rCtx rCtx_hL j (by simpa using hj)

theorem row_eq {j : ℕ} (hj : j < 5) :
    defaultRow 8 rLatD rOtD j = mems.getD j ⟨0, 0, 0⟩ := by
  have hm := Certificates.certificate40702.2.2.2.2.1
  calc defaultRow 8 rLatD rOtD j
      = ((List.range 5).map (defaultRow 8 rLatD rOtD)).getD j ⟨0, 0, 0⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rfl
    _ = mems.getD j ⟨0, 0, 0⟩ := by rw [hm]

theorem memStmt_Y {j : ℕ} (hj : j < 5) : MemStmt (rCtx.Y j) (mems.getD j ⟨0, 0, 0⟩) := by
  have hJ : rCtx.J = 5 := rCtx_J
  have h := rCtx.memStmt_default (Ot := rOtD) Certificates.certificate40702.2.2.2.1
    (j := j) (by omega)
  have hrow : defaultRow rCtx.k rCtx.D rOtD j = mems.getD j ⟨0, 0, 0⟩ := row_eq hj
  rwa [hrow] at h

theorem card_Y1 : Nat.card (rCtx.Y 1) = 2304 := (memStmt_Y (j := 1) (by norm_num)).1

theorem card_Y2 : Nat.card (rCtx.Y 2) = 3840 := (memStmt_Y (j := 2) (by norm_num)).1

theorem card_pCoreOf_Y1 : Nat.card (pCoreOf 2 (rCtx.Y 1)) = 2 ^ 6 :=
  (memStmt_Y (j := 1) (by norm_num)).2.1

theorem card_pCoreOf_Y2 : Nat.card (pCoreOf 2 (rCtx.Y 2)) = 2 ^ 5 :=
  (memStmt_Y (j := 2) (by norm_num)).2.1

theorem Y3_le_Y1 : rCtx.Y 3 ≤ rCtx.Y 1 := by
  have hJ : rCtx.J = 5 := rCtx_J
  exact rCtx.gensIn_le (by omega) (by omega) Certificates.certificate40702.2.2.2.2.2.1

theorem Y4_le_Y1 : rCtx.Y 4 ≤ rCtx.Y 1 := by
  have hJ : rCtx.J = 5 := rCtx_J
  exact rCtx.gensIn_le (by omega) (by omega) Certificates.certificate40702.2.2.2.2.2.2.1

theorem Y4_le_Y2 : rCtx.Y 4 ≤ rCtx.Y 2 := by
  have hJ : rCtx.J = 5 := rCtx_J
  exact rCtx.gensIn_le (by omega) (by omega) Certificates.certificate40702.2.2.2.2.2.2.2

theorem overgroup {Z : Subgroup R} (hSZ : rCtx.S ≤ Z) :
    Z = ⊤ ∨ ∃ j < 5, Z = rCtx.Y j ∧ Nat.card Z = (#[1, 9, 15, 3, 3] : Array ℕ)[j]! * 2 ^ 8 := by
  obtain ⟨j, hj, hZ⟩ := lat_all rCtx rCtx_hL Z hSZ
  by_cases hj5 : j < 5
  · have hm : memberOrTop 5 rCtx.Y j = rCtx.Y j := by simp [memberOrTop, hj5]
    have hm' : memberOrTop (#[1, 9, 15, 3, 3] : Array ℕ).size rCtx.Y j = rCtx.Y j := hm
    rw [hm'] at hZ
    exact Or.inr ⟨j, hj5, hZ, by rw [hZ]; exact rCtx_card hj5⟩
  · left
    have hm : memberOrTop 5 rCtx.Y j = ⊤ := by simp [memberOrTop, hj5]
    exact hZ.trans hm

theorem normalizer_ne_top {Q : Subgroup R} (hQ : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) : Subgroup.normalizer (Q : Set R) ≠ ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hn : Q.Normal := Subgroup.normalizer_eq_top_iff.mp h
  set N := Q.map R.subtype with hN
  have hNR : N ≤ R := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hNconj : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    rintro r hr _ ⟨q, hq, rfl⟩
    exact ⟨⟨r, hr⟩ * q * ⟨r, hr⟩⁻¹, hn.conj_mem q hq _, rfl⟩
  have hN2 : IsPGroup 2 N := h2.map _
  haveI := isSimpleGroup_P
  have hnorm : ((N ⊓ P).subgroupOf P).Normal := by
    constructor
    intro x hx p
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hNconj _ (P_le_R p.2) _ hx.1, P.mul_mem (P.mul_mem p.2 hx.2) (P.inv_mem p.2)⟩
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  ·
    have hcen : N ≤ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) := by
      intro n hnN
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hc1 : n * p * n⁻¹ * p⁻¹ ∈ N := by
        have h := N.mul_mem hnN (hNconj p (P_le_R hp) n⁻¹ (N.inv_mem hnN))
        simpa [mul_assoc] using h
      have hc2 : n * p * n⁻¹ * p⁻¹ ∈ P :=
        P.mul_mem (by
          have := (Subgroup.mem_normalizer_iff.mp (R_le_normalizer (hNR hnN)) p).mp hp
          exact this) (P.inv_mem hp)
      have hc : (⟨_, hc2⟩ : P) ∈ (N ⊓ P).subgroupOf P := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hc1, hc2⟩
      rw [hb, Subgroup.mem_bot] at hc
      have hc' : n * p * n⁻¹ * p⁻¹ = 1 := congrArg Subtype.val hc
      have : n * p = p * n := by
        calc n * p = n * p * n⁻¹ * p⁻¹ * (p * n) := by group
          _ = p * n := by rw [hc', one_mul]
      exact this.symm
    rw [centralizer_P] at hcen
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have : (q : Equiv.Perm (Fin 315)) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 315))) := hcen ⟨q, hq, rfl⟩
    rw [Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  · have hPN : P ≤ N := by
      intro p hp
      have : (⟨p, hp⟩ : P) ∈ (N ⊓ P).subgroupOf P := by rw [ht]; exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at this
      exact this.1
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hN2
    have hd : Nat.card P ∣ Nat.card N := Subgroup.card_dvd_of_le hPN
    rw [card_P, hm] at hd
    have h3 : 3 ∣ 2 ^ m := (by norm_num : 3 ∣ 604800).trans hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem not_isTwoLocal_top : ¬ IsTwoLocal (⊤ : Subgroup R) := by
  rintro ⟨Q, hQ, h2, h⟩
  exact normalizer_ne_top hQ h2 h.symm

theorem eq_normalizer_of_card {j : ℕ} (hj : j < 5)
    (hc : ∀ i < 5, Nat.card (rCtx.Y j) ∣ (#[1, 9, 15, 3, 3] : Array ℕ)[i]! * 2 ^ 8 → i = j)
    (hO : pCoreOf 2 (rCtx.Y j) ≠ ⊥) :
    rCtx.Y j = Subgroup.normalizer (pCoreOf 2 (rCtx.Y j) : Set R) := by
  have hle : rCtx.Y j ≤ Subgroup.normalizer (pCoreOf 2 (rCtx.Y j) : Set R) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  rcases overgroup ((rCtx.S_le_Y j).trans hle) with h | ⟨i, hi, hN, hcard⟩
  · exact absurd h (normalizer_ne_top hO (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
  · have hdvd : Nat.card (rCtx.Y j) ∣ Nat.card (Subgroup.normalizer
        (pCoreOf 2 (rCtx.Y j) : Set R)) := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    have := hc i hi hdvd
    subst this
    exact hN.symm

theorem isTwoLocal_Y1 : IsTwoLocal (rCtx.Y 1) := by
  have hO : pCoreOf 2 (rCtx.Y 1) ≠ ⊥ := fun h => by
    have := card_pCoreOf_Y1
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  refine ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, eq_normalizer_of_card (by norm_num)
    (fun i hi h => ?_) hO⟩
  rw [card_Y1] at h
  interval_cases i <;> simp_all

theorem isTwoLocal_Y2 : IsTwoLocal (rCtx.Y 2) := by
  have hO : pCoreOf 2 (rCtx.Y 2) ≠ ⊥ := fun h => by
    have := card_pCoreOf_Y2
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  refine ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, eq_normalizer_of_card (by norm_num)
    (fun i hi h => ?_) hO⟩
  rw [card_Y2] at h
  interval_cases i <;> simp_all

theorem eq_Y1_or_Y2 {M : Subgroup R} (hM : IsMaximalTwoLocal M)
    (hSM : rCtx.S ≤ M) : M = rCtx.Y 1 ∨ M = rCtx.Y 2 := by
  obtain ⟨hloc, hmax⟩ := hM
  rcases overgroup hSM with h | ⟨j, hj, rfl, hcard⟩
  · exact absurd (h ▸ hloc) not_isTwoLocal_top
  · have h1 := card_Y1
    interval_cases j
    · exfalso
      have := hmax _ isTwoLocal_Y1 (by rw [rCtx.Y_zero]; exact rCtx.S_le_Y 1)
      rw [this] at h1
      simp at hcard
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have := hmax _ isTwoLocal_Y1 Y3_le_Y1
      rw [this] at h1
      simp at hcard
      omega
    · exfalso
      have := hmax _ isTwoLocal_Y1 Y4_le_Y1
      rw [this] at h1
      simp at hcard
      omega

theorem yPair_eq {M₁ M₂ : Subgroup R}
    (hp : IsYAmalgamPair rCtx.S M₁ M₂) :
    (M₁ = rCtx.Y 2 ∧ M₂ = rCtx.Y 1) ∨ (M₁ = rCtx.Y 1 ∧ M₂ = rCtx.Y 2) := by
  obtain ⟨-, hne, hiff⟩ := hp
  have h1 := (hiff M₁).2 (Or.inl rfl)
  have h2 := (hiff M₂).2 (Or.inr rfl)
  have hS1 : rCtx.S ≤ M₁ := Subgroup.le_normalizer.trans h1.2
  have hS2 : rCtx.S ≤ M₂ := Subgroup.le_normalizer.trans h2.2
  rcases eq_Y1_or_Y2 h1.1 hS1 with e1 | e1 <;> rcases eq_Y1_or_Y2 h2.1 hS2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact Or.inr ⟨e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hne

end CFSG.Quasithin.F112R.AJ2L
