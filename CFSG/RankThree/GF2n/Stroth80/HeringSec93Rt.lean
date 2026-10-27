module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA
public import CFSG.RankThree.GF2n.Stroth80.Sec312Stmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conj_not_le_QB91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G}
    (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r) : ¬ conjSubgroup r B ≤ QB B := by
  intro hle
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := exists_pts91 h34 hs
  haveI := hn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  let r' : ↥(Rt M (LB M Q B) t) := ⟨r, hr.mem⟩
  have hne := (hypPlane_iff_polar91 h34 hs P r').mp hr.plane
  obtain ⟨b₀, hb₀B, hb₀⟩ := (P.point u).mpr ⟨1, (one_smul K u).symm⟩
  have hVn := hc.Rt_normalizes_Vt ht hr.mem
  have hbV : (b₀ : G) ∈ Vt M (LB M Q B) B Z t := b₀.2
  have haV : r * (b₀ : G) * r⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp hVn (b₀ : G)).mp hbV
  let a₀ : ↥(Vt M (LB M Q B) B Z t) := ⟨r * (b₀ : G) * r⁻¹, haV⟩
  have hvec : secVec ψ a₀ = (φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u := by
    have := P.act r' b₀ a₀ rfl
    rw [← hb₀]
    exact this
  have haA : r * (b₀ : G) * r⁻¹ ∈ conjSubgroup r B :=
    mem_conjSubgroup.mpr (by
      have e : r⁻¹ * (r * (b₀ : G) * r⁻¹) * r = (b₀ : G) := by group
      rw [e]; exact hb₀B)
  have hmem : (a₀ : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B := ⟨a₀.2, hle haA⟩
  have h0 := (P.perp (secVec ψ a₀)).mp ⟨a₀, hmem, rfl⟩
  rw [hvec] at h0
  exact hne h0

theorem Rt_eq_of_mem_Z091 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    (hsQ : s ∉ Q) : Rt M (LB M Q B) s = Rt M (LB M Q B) t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
  have heq := isCentrePre_eq_inf91 hs hr hprod hcomm hZ0
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hsL : s ∈ LB M Q B := by
    have h := hsZ
    rw [heq] at h
    exact h.1
  have hsLA : s ∈ conjSubgroup r (LB M Q B) := by
    have h := hsZ
    rw [heq, hLA] at h
    exact h.2
  have hsS : Sec5Hyp hc n s := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hsL, hsQ⟩
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hnotSL : ¬ SLNat hc s := by
    intro hSL
    have hVle := hc.Vt_le_inf_QB_of_SLNat hsS h35 hSL
    apply conj_not_le_QB91 h34 hs hr
    have hAV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z s := by
      refine le_sup_of_le_right ?_
      exact le_iSup₂_of_le r hrM (le_iSup_of_le hsLA le_rfl)
    exact (hAV.trans hVle).trans inf_le_right
  have hne : LB M Q B ≠ conjSubgroup r (LB M Q B) := by
    intro h
    apply sec9_Rt_ne_LB h34 hs
    rw [hr.gen, hLA, ← h, sup_idem]
  have h312 := h312b G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen s hsL hsQ (LB M Q B)
    (conjSubgroup r (LB M Q B)) ⟨1, M.one_mem, (conjSubgroup_one _).symm⟩ ⟨r, hrM, rfl⟩ hsL hsLA
    hne hnotSL
  have hR : LB M Q B ⊔ conjSubgroup r (LB M Q B) = Rt M (LB M Q B) t := by
    rw [hr.gen, hLA]
  rw [hR] at h312
  rcases h312 with hq | hRs
  · exfalso
    obtain ⟨hnorm, hmod⟩ := hq
    haveI := hnorm
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hq2 : ∃ e : ℕ, Nat.card Z = 2 ^ e := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact ⟨e, he⟩
    obtain ⟨hcard, -⟩ := isSLModel_two_data hq4 hq2 hmod
    have hRne : Rt M (LB M Q B) t ≠ LB M Q B := sec9_Rt_ne_LB h34 hs
    have hN311 := h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht hs5.notQ hRne
    have hN2 : IsPGroup 2 ↥(hc.CN t) := hc.isPGroup_CN_of_311 h34 hs5 hN311
    have hNt : inSubgroup (pCore 2) (Rt M (LB M Q B) t) = hc.CN t :=
      le_antisymm (hc.Nt_le_CN h34 hs5) (hc.CN_le_Nt ht hN2)
    obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk⟩ := exists_psi91 hs
    haveI : CharP K 2 := hch
    have hidx : Nat.card (↥(Rt M (LB M Q B) t) ⧸
        (inSubgroup (pCore 2) (Rt M (LB M Q B) t)).subgroupOf (Rt M (LB M Q B) t)) =
        Nat.card (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
      rw [hNt, ← hψk]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv
    rw [hcard, Nat.card_prod, card_statedSL_two, hK] at hidx
    have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
    have hpos : 0 < Nat.card Z * (Nat.card Z ^ 2 - 1) :=
      Nat.mul_pos (by omega) (by omega)
    have h1 : Nat.card Z * (Nat.card Z ^ 2 - 1) = 1 := by
      have h2 : Nat.card Z * (Nat.card Z ^ 2 - 1) * 1 =
          Nat.card Z * (Nat.card Z ^ 2 - 1) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) := by
        rw [mul_one]
        nlinarith [hidx]
      exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
    have h3 : 15 ≤ Nat.card Z ^ 2 - 1 := by omega
    have h4 : Nat.card Z * (Nat.card Z ^ 2 - 1) ≥ 4 * 15 := Nat.mul_le_mul hq4 h3
    omega
  · exact hRs.symm

end HS9

end CFSG.RankThree.GF2n.Stroth80
