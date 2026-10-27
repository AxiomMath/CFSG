module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Steps
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Pre
public import CFSG.RankThree.GF2n.Stroth80.Sec78VtIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec7TypeSec
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step6

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement


@[expose] def Step713XActsPlus6Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (t : G), Sec7Hyp hc 10 t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, InO2NormPre M Q Z Z0 x →
      (∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem sec713_Q_le_NormH0 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Q ≤ NormH0 M Z Z0 :=
  fun _ hx => sec8_Rt_le_NormH0 hc hZ0 (hc.Q_le_Rt ht hx)

theorem sec713_O2NormPre_facts (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    IsPGroup 2 ↥(O2NormPre M Q Z Z0) ∧ O2NormPre M Q Z Z0 ≤ NormH0 M Z Z0 ∧
      Q ≤ O2NormPre M Q Z Z0 :=
  ⟨isPGroup_O2NormPre (by rw [hc.hyp.hQ]; exact (inSubgroup_pCore_two M).1),
    O2NormPre_le_NormH0 (sec713_Q_le_NormH0 hc ht hZ0), Q_le_O2NormPre hc.hyp.Q_normal.1⟩

theorem sec713_comm_Vt_of_O2 (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ d ∈ O2NormPre M Q Z Z0, ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hD2, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hMZ : ∀ g ∈ M, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) z).mp hz
  have hNV : ∀ g ∈ NormH0 M Z Z0, ∀ v ∈ Vt M (LB M Q B) B Z t,
      g * v * g⁻¹ ∈ Vt M (LB M Q B) B Z t := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hg).2) v).mp hv
  have hVZ : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ z ∈ Z, v * z * v⁻¹ ∈ Z := fun v hv z hz =>
    hMZ v (hc.hyp.Q_normal.1 (hVQ hv)) z hz
  have hsec : SecHyp (O2NormPre M Q Z Z0) (Vt M (LB M Q B) B Z t) Z :=
    ⟨hZV, fun a ha b hb => hc.hyp.toHyp79.comm_mem_V (hVQ ha) (hVQ hb),
      fun a ha => hc.hyp.toHyp79.sq_mem_V (hVQ ha),
      fun d hd v hv => hNV d (hDN hd) v hv, fun d hd z hz => hMZ d (hDN hd).1.1 z hz⟩
  have hZltV : Z < Vt M (LB M Q B) B Z t := by
    refine lt_of_le_of_ne hZV fun h => ?_
    obtain ⟨m, hm2, hmO⟩ := hs.orth
    have hcard := n12N_card_V hc t m hm2 hmO
    rw [← h] at hcard
    have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
    have h1 : 1 < Nat.card Z ^ (2 * m) := Nat.one_lt_pow (by omega) hq
    have h2 : Nat.card Z * 1 < Nat.card Z * Nat.card Z ^ (2 * m) :=
      Nat.mul_lt_mul_of_pos_left h1 (by omega)
    omega
  obtain ⟨y, hyV, hyZ, hyD⟩ := exists_fixed_sec_of_isPGroup hD2 hsec hZltV
  have hCR : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ secCentPre (O2NormPre M Q Z Z0)
      (Vt M (LB M Q B) B Z t) Z hVZ,
      r * u * r⁻¹ ∈ secCentPre (O2NormPre M Q Z Z0) (Vt M (LB M Q B) B Z t) Z hVZ := by
    intro r hr u hu
    have hrN : r ∈ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0 hr
    refine secCentPre_conj_mem (fun d hd => ?_) (fun v hv => hNV r hrN v hv)
      (fun z hz => hMZ r hrN.1.1 z hz) hu
    simpa using conj_mem_O2NormPre ((NormH0 M Z Z0).inv_mem hrN) hd
  have hZC : Z ≤ secCentPre (O2NormPre M Q Z Z0) (Vt M (LB M Q B) B Z t) Z hVZ := by
    intro z hz
    refine ⟨hZV hz, fun d hd => ?_⟩
    rw [commutatorElement_def]
    exact Z.mul_mem (hMZ d (hDN hd).1.1 z hz) (Z.inv_mem hz)
  rcases sec7VtIrred_holds G M Q Z B hc n t hs _ hZC (fun u hu => hu.1) hCR with h | h
  · have hyC : y ∈ secCentPre (O2NormPre M Q Z Z0) (Vt M (LB M Q B) B Z t) Z hVZ := ⟨hyV, hyD⟩
    rw [h] at hyC
    exact absurd hyC hyZ
  · intro d hd v hv
    have hvC : v ∈ secCentPre (O2NormPre M Q Z Z0) (Vt M (LB M Q B) B Z t) Z hVZ := by
      rw [h]
      exact hv
    exact hvC.2 d hd

theorem sec713_comm_Rt_of_O2 (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ x ∈ O2NormPre M Q Z Z0, ∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t := by
  intro x hx r hr
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨-, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hRx : x * r * x⁻¹ ∈ Rt M (LB M Q B) t :=
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp
      (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 (hDN hx)).1) r).mp hr
  have hmemR : ⁅x, r⁆ ∈ Rt M (LB M Q B) t := by
    rw [commutatorElement_def]
    exact (Rt M (LB M Q B) t).mul_mem hRx ((Rt M (LB M Q B) t).inv_mem hr)
  have hmemD : ⁅x, r⁆ ∈ O2NormPre M Q Z Z0 := by
    have h1 : r * x⁻¹ * r⁻¹ ∈ O2NormPre M Q Z Z0 :=
      conj_mem_O2NormPre (sec8_Rt_le_NormH0 hc hZ0 hr) ((O2NormPre M Q Z Z0).inv_mem hx)
    have e : ⁅x, r⁆ = x * (r * x⁻¹ * r⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (O2NormPre M Q Z Z0).mul_mem hx h1
  exact Ctx.mem_CN.mpr ⟨hmemR, fun v hv => sec713_comm_Vt_of_O2 hZt hZcard hc hs hZ0 _ hmemD v hv⟩

theorem sec713_card_W_eq {q W V Qc n m k : ℕ} (hq : 0 < q) (hchi : Qc * q = W * V)
    (hQ : Qc = q ^ (2 * n + 1)) (hV : V = q * q ^ (2 * m)) (hk : 2 * n = 4 * m + k) :
    W = V * q ^ k := by
  have hVpos : 0 < V := by rw [hV]; positivity
  apply Nat.eq_of_mul_eq_mul_right hVpos
  rw [← hchi, hQ, hV, show 2 * n + 1 = 4 * m + k + 1 by omega]
  ring

theorem sec713_comm_Wt_of_O2 (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (h52c : Stroth52cStatement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h310chi : Stroth310ChiStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hWVo : Sec7WVSecOrderStatement) (h78 : Stroth78Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hn4 : ¬ OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (OmegaPlusNat hc t 3 ∧ n = 10) ∨
      ∀ d ∈ O2NormPre M Q Z Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        ⁅d, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  obtain ⟨hD2, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hqpos : 0 < Nat.card Z := by omega
  obtain ⟨m, hm2, hmO⟩ := hs.orth
  have hVc : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * m) :=
    n12N_card_V hc t m hm2 hmO
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := h5.width
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc n t h5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl) hWQ hZV
  have hsecP : ∀ P : Subgroup G, Vt M (LB M Q B) B Z t < P → P ≤ Wt Q (Vt M (LB M Q B) B Z t) →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) →
      (Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ m) ≤ Nat.card P ∨
        ¬ OmegaMinusNat hc t m) ∧
      (Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ (m - 1)) ≤ Nat.card P ∨
        ¬ (OmegaPlusNat hc t m ∧ 3 ≤ m)) := by
    intro P hVP hPW hPR
    obtain ⟨r, hr, hdec⟩ := oppDecomp_of_invariant_section hA hPts h52a h52b hc hs hVP.le hPW hPR
    have hNP : ∀ k ∈ hc.CN t, ∀ y ∈ P, ⁅k, y⁆ ∈ Vt M (LB M Q B) B Z t := fun k hk y hy =>
      sec7_N_comm_W_le_V h52a hA hc hs k hk y (hPW hy)
    obtain ⟨hmin, hplus⟩ := hWVo G M Q Z B hc n t hs P hVP hPW hPR hNP ⟨r, hr, _, _, hdec⟩ m hm2
    refine ⟨?_, ?_⟩
    · by_cases h : OmegaMinusNat hc t m
      · exact Or.inl (hmin h)
      · exact Or.inr h
    · by_cases h : OmegaPlusNat hc t m ∧ 3 ≤ m
      · exact Or.inl (hplus h.1 h.2)
      · exact Or.inr h
  have hmin : (OmegaPlusNat hc t 3 ∧ n = 10) ∨ ∃ k : ℕ, 0 < k ∧
      Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card ↥(Vt M (LB M Q B) B Z t) *
        Nat.card Z ^ k ∧
      ∀ P : Subgroup G, Vt M (LB M Q B) B Z t < P → P ≤ Wt Q (Vt M (LB M Q B) B Z t) →
        (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) →
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ k ≤ Nat.card P := by
    have h78c := h78 G M Q Z B hc n t h5 hs.large hs.notPlus4 m hm2 hmO
    rcases h78c with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, hp4, -, -⟩ | ⟨rfl, hp5, rfl, -⟩ |
      ⟨rfl, hp6, rfl, -⟩
    · rcases hmO with hp3 | hm3
      · exact Or.inl ⟨hp3, rfl⟩
      · refine Or.inr ⟨8, by norm_num,
          sec713_card_W_eq hqpos hchi hQc hVc (by norm_num), fun P hVP hPW hPR => ?_⟩
        rcases (hsecP P hVP hPW hPR).1 with h | h
        · simpa using h
        · exact absurd hm3 h
    · rcases hmO with hp4 | hm4
      · exact absurd hp4 hn4
      · refine Or.inr ⟨16, by norm_num,
          sec713_card_W_eq hqpos hchi hQc hVc (by norm_num), fun P hVP hPW hPR => ?_⟩
        rcases (hsecP P hVP hPW hPR).1 with h | h
        · simpa using h
        · exact absurd hm4 h
    · exact absurd hp4 hn4
    · refine Or.inr ⟨16, by norm_num,
        sec713_card_W_eq hqpos hchi hQc hVc (by norm_num), fun P hVP hPW hPR => ?_⟩
      rcases (hsecP P hVP hPW hPR).2 with h | h
      · simpa using h
      · exact absurd ⟨hp5, by norm_num⟩ h
    · refine Or.inr ⟨32, by norm_num,
        sec713_card_W_eq hqpos hchi hQc hVc (by norm_num), fun P hVP hPW hPR => ?_⟩
      rcases (hsecP P hVP hPW hPR).2 with h | h
      · simpa using h
      · exact absurd ⟨hp6, by norm_num⟩ h
  rcases hmin with h6 | ⟨k, hk, hWc, hbound⟩
  · exact Or.inl h6
  right
  have hNV : ∀ g ∈ NormH0 M Z Z0, g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    fun g hg => conjSubgroup_eq_self_iff.mp (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hg).2
  have hNW : ∀ g ∈ NormH0 M Z Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      g * w * g⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun g hg w hw =>
    conj_mem_Wt (hc.hyp.Q_normal.2 hg.1.1) (hNV g hg) hw
  have hNV' : ∀ g ∈ NormH0 M Z Z0, ∀ v ∈ Vt M (LB M Q B) B Z t,
      g * v * g⁻¹ ∈ Vt M (LB M Q B) B Z t := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hNV g hg) v).mp hv
  have hWV : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t,
      w * v * w⁻¹ ∈ Vt M (LB M Q B) B Z t := fun w hw v hv => by
    have e := Subgroup.mem_centralizer_iff.mp hw.2 v hv
    rw [← e, mul_inv_cancel_right]
    exact hv
  have hsec : SecHyp (O2NormPre M Q Z Z0) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t) :=
    ⟨hVW, fun a ha b hb => hZV (hc.hyp.toHyp79.comm_mem_V (hWQ ha) (hWQ hb)),
      fun a ha => hZV (hc.hyp.toHyp79.sq_mem_V (hWQ ha)),
      fun d hd w hw => hNW d (hDN hd) w hw, fun d hd v hv => hNV' d (hDN hd) v hv⟩
  have hVltW : Vt M (LB M Q B) B Z t < Wt Q (Vt M (LB M Q B) B Z t) := by
    refine lt_of_le_of_ne hVW fun h => ?_
    have hq1 : 1 < Nat.card Z ^ k := Nat.one_lt_pow hk.ne' (by omega)
    have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
    rw [← h] at hWc
    have h2 : Nat.card ↥(Vt M (LB M Q B) B Z t) * 1 <
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ k :=
      Nat.mul_lt_mul_of_pos_left hq1 hVpos
    omega
  obtain ⟨y, hyW, hyV, hyD⟩ := exists_fixed_sec_of_isPGroup hD2 hsec hVltW
  set C := secCentPre (O2NormPre M Q Z Z0) (Wt Q (Vt M (LB M Q B) B Z t))
    (Vt M (LB M Q B) B Z t) hWV with hCdef
  have hCR : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ C, r * u * r⁻¹ ∈ C := by
    intro r hr u hu
    have hrN : r ∈ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0 hr
    refine secCentPre_conj_mem (fun d hd => ?_) (fun w hw => hNW r hrN w hw)
      (fun v hv => hNV' r hrN v hv) hu
    simpa using conj_mem_O2NormPre ((NormH0 M Z Z0).inv_mem hrN) hd
  have hCR' : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r C = C := fun r hr =>
    conjSubgroup_eq_of_le fun u hu => by
      have := hCR r hr _ (mem_conjSubgroup.mp hu)
      simpa [mul_assoc] using this
  have hVC : Vt M (LB M Q B) B Z t ≤ C := by
    intro v hv
    refine ⟨hVW hv, fun d hd => ?_⟩
    rw [commutatorElement_def]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hNV' d (hDN hd) v hv)
      ((Vt M (LB M Q B) B Z t).inv_mem hv)
  have hVltC : Vt M (LB M Q B) B Z t < C :=
    lt_of_le_of_ne hVC fun h => hyV (h ▸ (⟨hyW, hyD⟩ : y ∈ C))
  have hCW : C ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun u hu => hu.1
  have hcard := hbound C hVltC hCW hCR'
  rw [← hWc] at hcard
  have hCeq : C = Wt Q (Vt M (LB M Q B) B Z t) := Subgroup.eq_of_le_of_card_ge hCW hcard
  intro d hd w hw
  have hwC : w ∈ C := by
    rw [hCeq]
    exact hw
  exact hwC.2 d hd

theorem step713XActs_of (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (h52c : Stroth52cStatement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h310chi : Stroth310ChiStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hWVo : Sec7WVSecOrderStatement) (h78 : Stroth78Statement)
    (hP6 : Step713XActsPlus6Statement) : Step713XActsStatement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0 x hx
  have hxD : x ∈ O2NormPre M Q Z Z0 := mem_O2NormPre.mpr hx
  have hR := sec713_comm_Rt_of_O2 hZt hZcard hc hs hZ0 x hxD
  have hV := sec713_comm_Vt_of_O2 hZt hZcard hc hs hZ0 x hxD
  refine ⟨hR, hV, ?_⟩
  rcases sec713_comm_Wt_of_O2 h52a h52b h52c hA hPts h310chi hZt hZcard hWVo h78 hc hs hn4 hZ0
    with ⟨hp3, rfl⟩ | hW
  · exact hP6 G M Q Z B hc t hs hp3 Z0 hZ0 x hx hR hV
  · exact hW x hxD

end CFSG.RankThree.GF2n.Stroth80
