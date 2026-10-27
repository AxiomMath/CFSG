module

public import CFSG.RankThree.GF2n.Stroth80.OppDecompSplit
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec79Split
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSecOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}


theorem sec715Spl_CN_conj (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, g * y * g⁻¹ ∈ hc.CN t := by
  intro g hg y hy
  refine mem_CN_conj_of_normalizes hc (hc.Rt_le_M t hg) ?_ ?_ hy
  · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
  · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)

theorem sec715Spl_Z0_conj (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
  (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer (fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy) hg) y).mp hy

theorem sec715Spl_plus_data (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {m : ℕ} (hm3 : 3 ≤ m) (hPlus : OmegaPlusNat hc t m) :
    ∃ (r : G) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
      Sec7A hc t r ∧ Nat.card K = Nat.card Z ∧
      φ.range = StatedOmega (StatedQuadPlus m K) ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      quadPlus m K u = 0 ∧ quadPlus m K u' = 0 ∧ polar (quadPlus m K) u u' ≠ 0 ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.plus hm3).LomGL u ∧
      ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.plus hm3).LomGL u' ∧
      IsOppDecomp (hc.CN t) Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
        (LB M Q B ⊓ hc.CN t) (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  have hPlus' := hPlus
  obtain ⟨K₀, _, _, hK₀, hrep₀⟩ := hPlus
  have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
  have hι₀ : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hι₀] at hcard₀
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    refine ⟨r, K, hKf, hKfin, hchar, φ, u, u', hr, hKZ, hrange, hker, hu, hu', huu', ?_, ?_, hopp⟩
    · rw [ElemMatrixIso.LomGL_plus hm3]
      exact hLu
    · rw [hLA, ElemMatrixIso.LomGL_plus hm3]
      exact hLu'
  · exfalso
    have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    exact omegaSignStatement_holds G M Q Z B hc t m' (by omega) hPlus'
      ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩

theorem sec715Spl_Zn_facts (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q) :
    Z0 ≤ Zn ∧ Zn ≤ hc.CN t ∧ ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Zn, r * y * r⁻¹ ∈ Zn := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hNnorm := sec715Spl_CN_conj hc ht
  refine ⟨fun z hz => (hZn z).mpr ⟨hZN hz, fun y hy => ((hZ0 z).mp hz).2 y (hCNR hy)⟩,
    fun x hx => ((hZn x).mp hx).1, fun r hr y hy => ?_⟩
  obtain ⟨hyN, hyc⟩ := (hZn y).mp hy
  refine (hZn _).mpr ⟨hNnorm r hr y hyN, fun x hx => ?_⟩
  have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ hc.CN t := hNnorm _ ((Rt M (LB M Q B) t).inv_mem hr) x hx
  rw [inv_inv] at hx'
  have e : ⁅r * y * r⁻¹, x⁆ = r * ⁅y, r⁻¹ * x * r⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) _).mp
    (hyc _ hx')


theorem sec715Spl_data (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hp4 : OmegaPlusNat hc t 4) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q) :
    ∃ r : G, Sec7A hc t r ∧
      IsOppDecomp Zn Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
        (Zn ⊓ LB M Q B) (Zn ⊓ LB M Q (conjSubgroup r B)) ∧
      Nat.card ↥(Zn ⊓ LB M Q B) ^ 2 = Nat.card ↥Z0 * Nat.card ↥Zn ∧
      Nat.card ↥(Zn ⊓ LB M Q (conjSubgroup r B)) ^ 2 = Nat.card ↥Z0 * Nat.card ↥Zn ∧
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  have hm3 : 3 ≤ 4 := by norm_num
  obtain ⟨r, K, hKf, hKfin, hchar, φ, u, u', hr, hKZ, hrange, hker, hu, hu', huu', hLu₁, hLu₂,
    hopp⟩ := sec715Spl_plus_data h51 hA hPts hc hs hZ0 hm3 hp4
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hNnorm := sec715Spl_CN_conj hc ht
  have hZ0n := sec715Spl_Z0_conj hc hZ0
  have hZnR' : ∀ x ∈ Rt M (LB M Q B) t, conjSubgroup x Zn = Zn := fun x hx =>
    conjSubgroup_eq_of_le fun y hy => by
      have h1 := hZnn x hx _ (mem_conjSubgroup.mp hy)
      simpa [mul_assoc] using h1
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hι : 4 ≤ Fintype.card (Fin 4 ⊕ Fin 4) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm3) hQ hι φ hrange hker hNnorm hZ0n
    hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂ hZ0Zn hZnN hZnR'
  have hdA := isOppDecomp_of_split hopp hZ0Zn hZnN hsplit
  have eA₁ : Zn ⊓ (LB M Q B ⊓ hc.CN t) = Zn ⊓ LB M Q B := by
    rw [inf_comm (LB M Q B) (hc.CN t), ← inf_assoc, inf_of_le_left hZnN]
  have eA₂ : Zn ⊓ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = Zn ⊓ LB M Q (conjSubgroup r B) := by
    rw [inf_comm (LB M Q (conjSubgroup r B)) (hc.CN t), ← inf_assoc, inf_of_le_left hZnN]
  rw [eA₁, eA₂] at hdA
  have hsec := SecHyp.of_isOppDecomp hdA hZnn hZ0n
  obtain ⟨Mm, iM, iA, κ, hκ, hkerκ⟩ := exists_sectionModule_ker hker hsec
    (fun k hk y hy => hNcomm k hk y (hZnN hy))
  haveI : Finite Mm := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hZnn hκ hdA hLR hL2R
  have huu'' : polar (quadPlus 4 K) u' u ≠ 0 := by rwa [polar_comm]
  obtain ⟨y₂, hy₂, hny₂⟩ := exists_nonA2_of_map_Lom (ElemMatrixIso.plus hm3) hQ hι φ hu' huu'
    hLu₂
  obtain ⟨y₁, hy₁, hny₁⟩ := exists_nonA2_of_map_Lom (ElemMatrixIso.plus hm3) hQ hι φ hu huu''
    hLu₁
  obtain ⟨-, -, hc₂⟩ := stroth_2_1_ii_omega_fixed_of_hom (ElemMatrixIso.plus hm3) φ hrange hQ
    hκ.two hkerκ hu hu' huu' hLu₁ hLu₂ hdec hι hy₂ hny₂
  obtain ⟨-, -, hc₁⟩ := stroth_2_1_ii_omega_fixed_of_hom (ElemMatrixIso.plus hm3) φ hrange hQ
    hκ.two hkerκ hu' hu huu'' hLu₂ hLu₁ hdec.symm hι hy₁ hny₁
  obtain ⟨e₁, e₂⟩ := fixedSub_eq_secSub_of_isOppDecomp hZnn hκ hdA hLR hL2R
  rw [e₂] at hc₂
  rw [e₁] at hc₁
  have hI₁ := hdA.1
  have hA₁P := hdA.2.1
  have hI₂ := hdA.2.2.1
  have hA₂P := hdA.2.2.2.1
  have hAA := natCard_eq_of_isSecMod hZ0Zn hκ
  have hA₁ := natCard_secSub_mul hZ0Zn hκ hI₁ hA₁P
  have hA₂ := natCard_secSub_mul hZ0Zn hκ hI₂ hA₂P
  refine ⟨r, hr, hdA, ?_, ?_, ?_⟩
  · rw [← hA₁, hAA, hc₁]
    ring
  · rw [← hA₂, hAA, hc₂]
    ring
  · exact le_sup_secOmega (ElemMatrixIso.plus hm3) hQ φ hrange hker hu hu' huu' hLu₁ hLu₂

end CFSG.RankThree.GF2n.Stroth80
