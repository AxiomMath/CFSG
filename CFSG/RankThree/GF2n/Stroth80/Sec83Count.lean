module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Pts

variable {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
  {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}

theorem Sec8Pts.spNat (h : Sec8Pts hc t r m K φ u u') : SpNat hc t :=
  ⟨K, inferInstance, inferInstance, h.card, m, h.two_le, φ, h.range, h.ker, h.act⟩

theorem Sec8Pts.u_ne_zero (h : Sec8Pts hc t r m K φ u u') : u ≠ 0 := fun h0 =>
  h.uu' (by simp [h0])

theorem Sec8Pts.charP (h : Sec8Pts hc t r m K φ u u') : CharP K 2 := by
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  exact charP_two_of_card_eq_two_pow (h.card.trans he)

theorem Sec8Pts.naturalRep (h : Sec8Pts hc t r m K φ u u') :
    NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t) :=
  ⟨φ, h.range, h.ker, h.act⟩

theorem Sec8Pts.card_V (h : Sec8Pts hc t r m K φ u u') :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  have := card_of_naturalRep h.naturalRep sec39_Z_le_Vt h.card
  rw [this]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

end Pts

theorem Ctx.mem_conjSubgroup_LB_of_mem_Rt (hc : Ctx M Q Z B) {t h : G} (ht : t ∈ LB M Q B)
    (hh : h ∈ Rt M (LB M Q B) t) : t ∈ conjSubgroup h (LB M Q B) := by
  rw [mem_conjSubgroup]
  have e : h⁻¹ * t * h = ⁅h⁻¹, t⁆ * t := by simp only [commutatorElement_def]; group
  rw [e]
  exact (LB M Q B).mul_mem
    (sec39_Q_le_LB (hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hh))) ht

theorem Ctx.LB_conj_le_Rt_of_mem (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
  hc.LB_conj_le_Rt (hc.Rt_le_M t hr) (hc.mem_conjSubgroup_LB_of_mem_Rt ht hr)

omit [Finite G] in
theorem conj_mem_of_conjSubgroup_eq {S : Subgroup G} {ρ x : G} (h : conjSubgroup ρ S = S)
    (hx : x ∈ S) : ρ * x * ρ⁻¹ ∈ S := by
  have h1 : ρ * x * ρ⁻¹ ∈ conjSubgroup ρ S := by
    refine mem_conjSubgroup.mpr ?_
    have e : ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x := by group
    rw [e]
    exact hx
  rwa [h] at h1

theorem sec83_count_A (h53 : Stroth53Statement) (hInv : Sec8InvStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u') :
    ∃ a : ℕ, 2 * n = a * 2 ^ m + 4 * m + 2 ∧
      Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ (2 * m + 2) ∧
      Nat.card ↥(Sec8W1 M Q Z B t r) =
        Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (a * 2 ^ m) := by
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨hV1c, hWc, -⟩ := h53.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have he := h53.2.2.2.2 G M Q Z B hc n t hs hpts.spNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hinv := hInv G M Q Z B hc n t h8 r hr
  have hV := hpts.card_V
  obtain ⟨-, hN, -⟩ := hpts.act
  haveI := hN
  have hchi := card_mul_card_of_isChiIso he (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q)
    (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t)
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  obtain ⟨a, ha⟩ := stroth_2_1_ii_secSp (m := m) (by have := hpts.two_le; omega) φ hpts.range
    hpts.ker (fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx)
    (fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx) hb.2 hcd hLeR hL'eR hpts.uu'
    hpts.hL hL2
  have g2 : Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ (2 * m + 2) := by
    rw [hV1c, hV]
    ring
  have g3 : Nat.card ↥(Sec8W1 M Q Z B t r) =
      Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (a * 2 ^ m) := by
    rw [ha, hpts.card, mul_comm (2 ^ m) a]
  refine ⟨a, ?_, g2, g3⟩
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have h1 : Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (4 * m + 4 + a * 2 ^ m) := by
    calc Nat.card Z ^ (2 * n + 2) = Nat.card Q * Nat.card Z := by rw [hw]; ring
      _ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card (Vt M (LB M Q B) B Z t) := hchi
      _ = (Nat.card ↥(Sec8W1 M Q Z B t r) * Nat.card Z) * Nat.card Z ^ (2 * m + 1) := by
          rw [hWc, hV]
      _ = Nat.card Z ^ (4 * m + 4 + a * 2 ^ m) := by rw [g3, g2]; ring
  have h2 := Nat.pow_right_injective hq2 h1
  omega

theorem sec83_count_B (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u') {e : ℕ}
    (hn : 2 * n = e + 4 * m + 2) :
    Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (e + 1) := by
  classical
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hm2 := hpts.two_le
  have hn3 := hs.n_gt
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨-, hLL', -, hdec⟩ := h51 G M Q Z B hc n t hs (Or.inl hpts.spNat) r hrR hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
    rfl rfl rfl rfl rfl
  have hcard1 := card_mul_card_isOppDecomp hdec
  rw [hLL'] at hcard1
  have hNnorm : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem hs.mem hrR hx
  have hconj : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr hNnorm]
  have hcard2 : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hconj]
    exact card_conjSubgroup r _
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hcard3 := card_inf_mul_card_map hLR φ hpts.ker
  rw [hpts.hL, card_LspGL hpts.u_ne_zero, hpts.card] at hcard3
  have hL35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.2.1
  rw [hL35] at hcard3
  set y := Nat.card ↥(LB M Q B ⊓ hc.CN t) with hy
  set q := Nat.card Z with hq
  set P := Nat.card Q with hP
  have hPpos : 0 < P := Nat.card_pos
  have hqpos : 0 < q := by omega
  rw [hcard2] at hcard1
  have hn1 : 2 * (n - 1) = e + 4 * m := by omega
  have hm1 : 2 * (2 * m - 1) + 2 = 4 * m := by omega
  have h5 : Nat.card ↥(hc.CN t) * (P * q * q ^ (2 * (2 * m - 1))) =
      P ^ 2 * q ^ (2 * (n - 1)) := by
    calc Nat.card ↥(hc.CN t) * (P * q * q ^ (2 * (2 * m - 1)))
        = (Nat.card ↥(hc.CN t) * (P * q)) * q ^ (2 * (2 * m - 1)) := by ring
      _ = (y * y) * q ^ (2 * (2 * m - 1)) := by rw [hcard1]
      _ = (y * q ^ (2 * m - 1)) ^ 2 := by ring
      _ = (P * q ^ (n - 1)) ^ 2 := by rw [hcard3]
      _ = P ^ 2 * q ^ (2 * (n - 1)) := by ring
  have h6 : (P * q ^ (e + 1)) * (P * q * q ^ (2 * (2 * m - 1))) =
      P ^ 2 * q ^ (2 * (n - 1)) := by
    have h7 : (e + 1) + 1 + 2 * (2 * m - 1) = 2 * (n - 1) := by omega
    calc (P * q ^ (e + 1)) * (P * q * q ^ (2 * (2 * m - 1)))
        = P ^ 2 * q ^ ((e + 1) + 1 + 2 * (2 * m - 1)) := by ring
      _ = P ^ 2 * q ^ (2 * (n - 1)) := by rw [h7]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (h5.trans h6.symm)

end CFSG.RankThree.GF2n.Stroth80
