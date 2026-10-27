module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeStmt
import CFSG.RankThree.GF2n.Stroth80.HeringSec93Fix
import CFSG.RankThree.GF2n.Stroth80.HeringSec93Rt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

theorem step94Point_holds (h34 : Stroth34Statement) : Step94PointStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs m hm hLR
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have hq4 : 4 ≤ Nat.card K := by
    rw [P.card]
    exact hc.hyp.q4
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hcC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hnoC := hc.noA2_conj hs5.noA2 hm
  have hgenC := hs5.gen.conj_of_mem hm
  have hVn := hc.Rt_normalizes_Vt ht
  let U₀ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    ((LB M Q (conjSubgroup m B)).subgroupOf (Rt M (LB M Q B) t)).map φ
  have hU₀X : U₀ ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rintro _ ⟨x, -, rfl⟩
    rw [← P.range]
    exact ⟨x, rfl⟩
  have hU₀p : IsPGroup 2 U₀ := by
    have hLp : IsPGroup 2 ↥(LB M Q (conjSubgroup m B)) :=
      hcC.isPGroup_LB h34 hs5.width hs5.n_gt hnoC hgenC
    have h1 : IsPGroup 2 ↥((LB M Q (conjSubgroup m B)).subgroupOf (Rt M (LB M Q B) t)) :=
      hLp.of_injective (Subgroup.subgroupOfEquivOfLe hLR).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hLR).injective
    exact h1.of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)
  obtain ⟨p, hp0, hpsing, hpfix⟩ :=
    HS9.exists_singular_fixed91 hq4 E P.sing P.ne_zero hU₀X hU₀p
  obtain ⟨w, hwp⟩ := exists_secVec_eq ψ p
  have hwC : (w : G) ∈ CQt Q Z (LB M Q (conjSubgroup m B)) := by
    refine ⟨hc.Vt_le_Q t w.2, fun x hx => ?_⟩
    have hxR : x ∈ Rt M (LB M Q B) t := hLR hx
    let x' : ↥(Rt M (LB M Q B) t) := ⟨x, hxR⟩
    have hxU : φ x' ∈ U₀ := ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hxw : x * (w : G) * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVn hxR) (w : G)).mp w.2
    let w' : ↥(Vt M (LB M Q B) B Z t) := ⟨x * (w : G) * x⁻¹, hxw⟩
    have hv : secVec ψ w' =
        (φ x' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ w := P.act x' w w' rfl
    have hv' : secVec ψ w' = secVec ψ w := by rw [hv, hwp, hpfix _ hxU]
    rw [commutatorElement_def]
    exact (secVec_eq_iff ψ w' w).mp hv'
  have hwCZ : (w : G) ∈ conjSubgroup m B ⊔ Z := by
    have h := hwC
    rw [(stroth_3_5 h34 hcC hs5.width hs5.n_gt hnoC hgenC).2.1] at h
    exact h
  have hwZ : (w : G) ∉ Z := fun hz =>
    hp0 (by rw [← hwp]; exact (secVec_eq_zero_iff ψ w).mpr hz)
  obtain ⟨A, hA, hAu⟩ := E.exists_mulVec_eq hQ (P := plusPair K 0) (P' := plusPair K 1)
    (plusPair_orth (by decide)) P.ne_zero hp0 (by rw [P.sing, hpsing])
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(Rt M (LB M Q B) t), φ ρ = A := by
    rw [← P.range] at hA
    exact MonoidHom.mem_range.mp hA
  have hρM : (ρ : G) ∈ M := hc.Rt_le_M t ρ.2
  obtain ⟨b₀, hb₀B, hb₀⟩ := (P.point u).mpr ⟨1, (one_smul K u).symm⟩
  have hb₁V : (ρ : G) * (b₀ : G) * (ρ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hVn ρ.2) (b₀ : G)).mp b₀.2
  let b₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨(ρ : G) * (b₀ : G) * (ρ : G)⁻¹, hb₁V⟩
  have hb₁ : secVec ψ b₁ = p := by
    have h1 : secVec ψ b₁ = (φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ b₀ :=
      P.act ρ b₀ b₁ rfl
    rw [h1, hb₀, hρ, hAu]
  have hwρ : (w : G) ∈ conjSubgroup (ρ : G) B ⊔ Z := by
    have hz : (w : G) * (b₁ : G)⁻¹ ∈ Z := (secVec_eq_iff ψ w b₁).mp (by rw [hwp, hb₁])
    have hb₁C : (b₁ : G) ∈ conjSubgroup (ρ : G) B := mem_conjSubgroup.mpr (by
      show (ρ : G)⁻¹ * ((ρ : G) * (b₀ : G) * (ρ : G)⁻¹) * (ρ : G) ∈ B
      rw [show (ρ : G)⁻¹ * ((ρ : G) * (b₀ : G) * (ρ : G)⁻¹) * (ρ : G) = (b₀ : G) by group]
      exact hb₀B)
    have e : (w : G) = ((w : G) * (b₁ : G)⁻¹) * (b₁ : G) := by group
    rw [sup_comm, e]
    exact Subgroup.mul_mem_sup hz hb₁C
  have hLC := sec8_LB_eq_of_sup_eq hcC (hc.conj_of_mem hρM)
    (sec8_point_eq (hc := hc) hm hρM hwCZ hwρ hwZ)
  refine ⟨ρ, ρ.2, ?_⟩
  rw [← hc.LB_conj hm, hLC, hc.LB_conj hρM]

theorem step94ZExists_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
        ∃ h ∈ M, conjSubgroup h Z0 ≤ LB M Q B ∧ x ∈ conjSubgroup h Z0 ∧ conjSubgroup h Z0 ≠ Z0 := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hxN hconj
  obtain ⟨-, g, hgM, hgq⟩ := hconj
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  have hq' : g⁻¹ * x * g * s⁻¹ ∈ Q := by
    have h := HS9.conj_mem_Q91 hc hgi hgq
    rwa [inv_inv, show g⁻¹ * (x * (g * s * g⁻¹)⁻¹) * g = g⁻¹ * x * g * s⁻¹ by group] at h
  have hsQ : s ∉ Q := by
    intro hsQ
    apply hxN
    refine sec9_Q_le_CN hc ht ?_
    have h := HS9.conj_mem_Q91 hc hgM (Q.mul_mem hq' hsQ)
    rwa [show g * (g⁻¹ * x * g * s⁻¹ * s) * g⁻¹ = x by group] at h
  have hxZ : g⁻¹ * x * g ∈ Z0 := by
    rw [show g⁻¹ * x * g = (g⁻¹ * x * g * s⁻¹) * s by group]
    exact Z0.mul_mem (hQZ0 hq') hs0
  have hsLD : s ∈ conjSubgroup g⁻¹ (LB M Q B) := by
    rw [mem_conjSubgroup, inv_inv,
      show g * s * g⁻¹ = (x * (g * s * g⁻¹)⁻¹)⁻¹ * x by group]
    exact (LB M Q B).mul_mem (sec39_Q_le_LB (Q.inv_mem hgq)) hxL
  have hLD : LB M Q (conjSubgroup g⁻¹ B) ≤ Rt M (LB M Q B) t := by
    rw [hc.LB_conj hgi, ← HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs0 hsQ]
    exact conjSubgroup_le_Rt hgi hsLD
  obtain ⟨ρ, hρR, hρ⟩ := step94Point_holds h34 G M Q Z B hc n t hs g⁻¹ hgi hLD
  have hZL : Z0 ≤ LB M Q B := by
    obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
    rw [HS9.isCentrePre_eq_inf91 hs hr hprod hcomm hZ0]
    exact inf_le_left
  have hZρ : conjSubgroup ρ Z0 = Z0 := conjSubgroup_eq_self_iff.mpr
    (hZ0.mem_normalizer (fun σ hσ y hy => HS9.conj_mem_Q91 hc (hc.Rt_le_M t hσ) hy) hρR)
  have hZD : Z0 ≤ conjSubgroup g⁻¹ (LB M Q B) := by
    rw [hρ, ← hZρ]
    exact Subgroup.map_mono hZL
  refine ⟨g, hgM, fun y hy => ?_, mem_conjSubgroup.mpr hxZ, fun heq => ?_⟩
  · have h1 := mem_conjSubgroup.mp (hZD (mem_conjSubgroup.mp hy))
    rwa [inv_inv, show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
  · apply hxN
    have hx : x ∈ Z0 := by
      rw [← heq]
      exact mem_conjSubgroup.mpr hxZ
    exact HS9.isCentrePre_le_CN91 hs hZ0 hx

theorem step94ZInR0_of (hCYW : Step94CYWStatement) (h92 : Stroth92Statement)
    (hB : Step94ConjVStatement) : Step94ZInR0Statement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hxN hconj Y hdp hYsl hn5 z hzM hZL y hy
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  by_cases hyN : y ∈ hc.CN t
  · exact (le_sup_left : hc.CN t ≤ Sec9R0 hc t x) hyN
  have hyL : y ∈ LB M Q B := hZL hy
  have hyconj : ConjMod M Q (z⁻¹ * y * z) y := ⟨hc.LB_le_M hyL, z, hzM, by
    rw [show y * (z * (z⁻¹ * y * z) * z⁻¹)⁻¹ = 1 by group]
    exact Q.one_mem⟩
  have hyW := hB G M Q Z B hc n t hs _ _ rfl rfl Z0 hZ0 _ (mem_conjSubgroup.mp hy) y hyL hyN
    hyconj
  obtain ⟨hQX, hXR, -, -, hXY, -, hcomm⟩ := hdp
  have hYnX : Y ≤ Subgroup.normalizer (Sec9R0 hc t x : Set G) :=
    HS9.normalizer_of_commutator_le hQX hcomm
  have hmem : y ∈ ((Sec9R0 hc t x ⊔ Y : Subgroup G) : Set G) := by
    rw [hXY]
    exact le_Rt (M := M) (LB M Q B) ht hyL
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hYnX] at hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem
  have hai : a⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem (hXR ha)
  have hbW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅b, w⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro w hw
    have e : ⁅b, w⁆ = a⁻¹ * ⁅a * b, w⁆ * a⁻¹⁻¹ * ⁅a⁻¹, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hai) _).mp (hyW w hw))
      (hsplit.2.2 _ ((Sec9R0 hc t x).inv_mem ha) w hw)
  exact (Sec9R0 hc t x).mul_mem ha (hQX (hCYW G M Q Z B hc n t hs _ Y hsplit hn5 b hb hbW))

end CFSG.RankThree.GF2n.Stroth80
