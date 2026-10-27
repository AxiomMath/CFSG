module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndClassical
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

section Kernel

variable {G : Type} [Group G]

theorem comm_mem_iff_mem_of_isSimpleGroup {R N P J : Subgroup G} {X : Type} [Group X]
    (φ : ↥R →* X) (hker : φ.ker = N.subgroupOf R) (hsimple : IsSimpleGroup ↥φ.range)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hJ : ∀ r ∈ R, ∀ x ∈ J, r * x * r⁻¹ ∈ J)
    (hN : ∀ k ∈ N, ∀ x ∈ P, ⁅k, x⁆ ∈ J) (hnt : ∃ r ∈ R, ∃ x ∈ P, ⁅r, x⁆ ∉ J) :
    ∀ r ∈ R, (∀ x ∈ P, ⁅r, x⁆ ∈ J) ↔ r ∈ N := by
  let K₀ : Subgroup ↥R :=
    { carrier := {a | ∀ x ∈ P, ⁅(a : G), x⁆ ∈ J}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        intro x hx
        have e : ⁅((a * b : ↥R) : G), x⁆ =
            (a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹ * ⁅(a : G), x⁆ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        rw [e]
        exact J.mul_mem (hJ _ a.2 _ (hb x hx)) (ha x hx)
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        intro x _
        rw [Subgroup.coe_one, commutatorElement_one_left]
        exact J.one_mem
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        intro x hx
        have e : ⁅((a⁻¹ : ↥R) : G), x⁆ = (a : G)⁻¹ * ⁅(a : G), x⁆⁻¹ * ((a : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact hJ _ (R.inv_mem a.2) _ (J.inv_mem (ha x hx)) }
  have hmem : ∀ a : ↥R, a ∈ K₀ ↔ ∀ x ∈ P, ⁅(a : G), x⁆ ∈ J := fun a => Iff.rfl
  have hK₀n : K₀.Normal := by
    refine ⟨fun a ha g => (hmem _).mpr fun x hx => ?_⟩
    have hx' : (g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹ ∈ P := hP _ (R.inv_mem g.2) x hx
    rw [inv_inv] at hx'
    have e : ⁅((g * a * g⁻¹ : ↥R) : G), x⁆ =
        (g : G) * ⁅(a : G), (g : G)⁻¹ * x * (g : G)⁆ * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hJ _ g.2 _ ((hmem a).mp ha _ hx')
  have hNK : φ.ker ≤ K₀ := by
    intro a ha
    rw [hker, Subgroup.mem_subgroupOf] at ha
    exact (hmem a).mpr (hN _ ha)
  haveI := hsimple
  haveI : (K₀.map φ.rangeRestrict).Normal := hK₀n.map _ φ.rangeRestrict_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.map φ.rangeRestrict) with hbot | htop
  · intro r hr
    refine ⟨fun h => ?_, fun h x hx => hN r h x hx⟩
    have h1 : φ.rangeRestrict ⟨r, hr⟩ ∈ K₀.map φ.rangeRestrict :=
      Subgroup.mem_map_of_mem _ ((hmem _).mpr h)
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, hker,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  · exfalso
    obtain ⟨r, hr, x, hx, hrx⟩ := hnt
    have h1 : φ.rangeRestrict ⟨r, hr⟩ ∈ K₀.map φ.rangeRestrict := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkr⟩ := Subgroup.mem_map.mp h1
    have h2 : k⁻¹ * ⟨r, hr⟩ ∈ K₀ := by
      refine hNK ?_
      rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_mul, map_inv, hkr,
        inv_mul_cancel]
    have h3 : (⟨r, hr⟩ : ↥R) ∈ K₀ := by
      have := K₀.mul_mem hk h2
      rwa [mul_inv_cancel_left] at this
    exact hrx ((hmem _).mp h3 x hx)

end Kernel

section Split

variable {G : Type} [Group G] [Finite G] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
  {R N P I L₁ L₂ A₁ A₂ J : Subgroup G}

theorem exists_comm_not_mem_of_hom (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    (hIJ : I ≤ J) (hJP : J ≤ P) (hJne : J ≠ P) :
    ∃ r ∈ R, ∃ x ∈ P, ⁅r, x⁆ ∉ J := by
  classical
  by_contra hcon
  push Not at hcon
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  have huu'' : polar Q u' u ≠ 0 := by rwa [polar_comm]
  obtain ⟨y, hy, hny⟩ := exists_nonA2_of_map_Lom E hQ h4 φ hu' huu' hL₂
  obtain ⟨x, hx, hnx⟩ := exists_nonA2_of_map_Lom E hQ h4 φ hu huu'' hL₁
  obtain ⟨-, hy2, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu hu' huu' hL₁
    hL₂ hdec h4 hy hny
  obtain ⟨-, hx2, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu' hu huu'' hL₂
    hL₁ hdec.symm h4 hx hnx
  have hcommJ : ∀ (g : ↥R) (a : M), comm M g a ∈ secSub κ J := by
    intro g a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hgw : (g : G) * w * (g : G)⁻¹ ∈ P := hP _ g.2 _ w.2
    have h1 := hκ.act g w ⟨_, hgw⟩ rfl
    refine mem_secSub.mpr ⟨⟨(g : G) * w * (g : G)⁻¹, hgw⟩ * w⁻¹, ?_, ?_⟩
    · have e : (((⟨(g : G) * w * (g : G)⁻¹, hgw⟩ : ↥P) * w⁻¹ : ↥P) : G) =
          ⁅(g : G), (w : G)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, commutatorElement_def]
      rw [e]
      exact hcon _ g.2 _ w.2
    · rw [map_mul, map_inv, h1, hw, toAdd_ofAdd, comm_apply, ofAdd_sub, div_eq_mul_inv]
  have hrange_le : ∀ g : ↥R, (comm M g).range ≤ secSub κ J := by
    intro g b hb
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hb
    exact hcommJ g a
  have hC : fixedSub M ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R) ⊔
      fixedSub M ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R) ≤ secSub κ J := by
    refine sup_le ?_ ?_
    · rw [← hx2]
      exact hrange_le x
    · rw [← hy2]
      exact hrange_le y
  rw [hdec.sup_eq_top] at hC
  have htop : secSub κ J = secSub κ P := by
    rw [secSub_eq_top hκ]
    exact top_le_iff.mp hC
  exact hJne ((secSub_inj hκ hIJ hJP hsec.le le_rfl).mp htop)

end Split

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem sec715_CN_conj (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, g * y * g⁻¹ ∈ hc.CN t := by
  intro g hg y hy
  refine mem_CN_conj_of_normalizes hc (hc.Rt_le_M t hg) ?_ ?_ hy
  · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
  · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)

private theorem sec715_Z0_conj (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
  (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer (fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy) hg) y).mp hy

private theorem sec715_plus_data (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
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

theorem sec79_card_eq_omegaPlus (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {A : Subgroup G} (hZA : Z0 ≤ A) (hAN : A ≤ hc.CN t)
    (hAR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) {m : ℕ} (hm3 : 3 ≤ m)
    (hPlus : OmegaPlusNat hc t m) :
    ∃ k : ℕ, Nat.card A = Nat.card Z0 * Nat.card Z ^ (2 ^ (m - 1) * k) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, K, hKf, hKfin, hchar, φ, u, u', hr, hKZ, hrange, hker, hu, hu', huu', hLu₁, hLu₂,
    hopp⟩ := sec715_plus_data h51 hA hPts hc hs hZ0 hm3 hPlus
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hNnorm := sec715_CN_conj hc ht
  have hZ0n := sec715_Z0_conj hc hZ0
  have hAn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ A, x * y * x⁻¹ ∈ A := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x A := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    rwa [hAR x hx] at h1
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hcomm : ∀ x ∈ hc.CN t, ∀ y ∈ A, ⁅x, y⁆ ∈ Z0 := fun x hx y hy => hNcomm x hx y (hAN hy)
  have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm3)
    (nondegenerate_polarBilin_quadPlus m K) (by omega) φ hrange hker
    hNnorm hZ0n hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂ hZA hAN hAR
  have hdA := isOppDecomp_of_split hopp hZA hAN hsplit
  obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm3) hm3
    (isPlus_quadPlus m) φ hrange hker hAn hZ0n hcomm hdA hLR hL2R hu hu' huu' hLu₁ hLu₂
  rw [hKZ] at hk
  exact ⟨k, hk⟩

theorem sec7_comm_mem_iff_mem_omegaPlus (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {J : Subgroup G} (hZJ : Z0 ≤ J) (hJN : J ≤ hc.CN t) (hJne : J ≠ hc.CN t)
    (hJR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ J, r * y * r⁻¹ ∈ J) {m : ℕ} (hm3 : 3 ≤ m)
    (hPlus : OmegaPlusNat hc t m) :
    ∀ r ∈ Rt M (LB M Q B) t, (∀ x ∈ hc.CN t, ⁅r, x⁆ ∈ J) ↔ r ∈ hc.CN t := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, K, hKf, hKfin, hchar, φ, u, u', hr, hKZ, hrange, hker, hu, hu', huu', hLu₁, hLu₂,
    hopp⟩ := sec715_plus_data h51 hA hPts hc hs hZ0 hm3 hPlus
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hNnorm := sec715_CN_conj hc ht
  have hZ0n := sec715_Z0_conj hc hZ0
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hnt := exists_comm_not_mem_of_hom (ElemMatrixIso.plus hm3)
    (nondegenerate_polarBilin_quadPlus m K) (by omega) φ hrange hker hNnorm hZ0n hNcomm hopp hLR
    hL2R hu hu' huu' hLu₁ hLu₂ hZJ hJN hJne
  have hsimple : IsSimpleGroup ↥φ.range := by
    rw [hrange]
    exact (endg_omegaPlus_facts (by rw [hKZ]; exact hc.hyp.q4) hm3).1
  exact comm_mem_iff_mem_of_isSimpleGroup φ hker hsimple hNnorm hJR
    (fun k hk x hx => hZJ (hNcomm k hk x hx)) hnt

private theorem sec715_Zn_facts (h711 : Stroth711StrongStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q) :
    Z0 ≤ Zn ∧ Zn ≤ hc.CN t ∧ Zn ≠ hc.CN t ∧
      ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Zn, r * y * r⁻¹ ∈ Zn := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hNnorm := sec715_CN_conj hc ht
  refine ⟨fun z hz => (hZn z).mpr ⟨hZN hz, fun y hy => ((hZ0 z).mp hz).2 y (hCNR hy)⟩,
    fun x hx => ((hZn x).mp hx).1, fun h => ?_, fun r hr y hy => ?_⟩
  · refine h711 G M Q Z B hc n t hs ((Subgroup.commutator_le).mpr fun x hx y hy => ?_)
    rw [← h] at hx
    exact ((hZn x).mp hx).2 y hy
  · obtain ⟨hyN, hyc⟩ := (hZn y).mp hy
    refine (hZn _).mpr ⟨hNnorm r hr y hyN, fun x hx => ?_⟩
    have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ hc.CN t := hNnorm _ ((Rt M (LB M Q B) t).inv_mem hr) x hx
    rw [inv_inv] at hx'
    have e : ⁅r * y * r⁻¹, x⁆ = r * ⁅y, r⁻¹ * x * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) _).mp
      (hyc _ hx')

theorem sec715_comm_mem_Zn_iff (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h711 : Stroth711StrongStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp4 : OmegaPlusNat hc t 4) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q) :
    ∀ r ∈ Rt M (LB M Q B) t, (∀ x ∈ hc.CN t, ⁅r, x⁆ ∈ Zn) ↔ r ∈ hc.CN t := by
  obtain ⟨hZ0Zn, hZnN, hZnne, hZnR⟩ := sec715_Zn_facts h711 hc hs hZ0 hZn
  exact sec7_comm_mem_iff_mem_omegaPlus h51 hA hPts hc hs hZ0 hZ0Zn hZnN hZnne hZnR
    (by norm_num) hp4

theorem sec715_card_Zn (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hNO : Sec7NOrderStatement)
    (h711 : Stroth711StrongStatement) (hc : Ctx M Q Z B) {t : G} (hs : Sec7Hyp hc 16 t)
    (hp4 : OmegaPlusNat hc t 4) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q)
    (hne : Zn ≠ Z0) :
    Nat.card Zn = Nat.card Z0 * Nat.card Z ^ 8 ∧
      Nat.card ↥(hc.CN t) = Nat.card Zn * Nat.card Z ^ 8 := by
  classical
  obtain ⟨hZ0Zn, hZnN, hZnne, hZnR⟩ := sec715_Zn_facts h711 hc hs hZ0 hZn
  have hZnR' : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r Zn = Zn := fun r hr =>
    conjSubgroup_eq_of_le fun x hx => by
      have h1 := hZnR r hr _ (mem_conjSubgroup.mp hx)
      simpa [mul_assoc] using h1
  obtain ⟨k, hk⟩ := sec79_card_eq_omegaPlus h51 hA hPts hc hs hZ0 hZ0Zn hZnN hZnR'
    (by norm_num) hp4
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 16 t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨hcardI, -, hIZ⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  rw [hIZ] at hcardI
  have hQc : Nat.card Q = Nat.card Z ^ (2 * 16 + 1) := hs.toSec5.width
  have hNc := hNO G M Q Z B hc 16 t hs 4 (by norm_num) (Or.inl hp4)
  set q := Nat.card ↥Z with hq
  have hq1 : 1 < q := by
    have := hc.hyp.q4
    omega
  have hqpos : 0 < q := by omega
  have hN50 : Nat.card ↥(hc.CN t) = q ^ 50 := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hqpos (4 * 4))
    rw [hNc, hQc]
    ring
  have hZ034 : Nat.card ↥Z0 = q ^ 34 := by
    rw [hcardI, hQc]
    ring
  rw [hZ034, show (2 : ℕ) ^ (4 - 1) = 8 by norm_num] at hk
  have hkle : k ≤ 2 := by
    have h1 : Nat.card ↥Zn ≤ Nat.card ↥(hc.CN t) := Subgroup.card_le_of_le hZnN
    rw [hk, hN50, ← pow_add] at h1
    have h2 := (Nat.pow_le_pow_iff_right hq1).mp h1
    omega
  have hk1 : k = 1 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h0 | h1 | h2
    · exfalso
      subst h0
      refine hne (Subgroup.eq_of_le_of_card_ge hZ0Zn ?_).symm
      rw [hk, hZ034]
      simp
    · exact h1
    · exfalso
      subst h2
      refine hZnne (Subgroup.eq_of_le_of_card_ge hZnN ?_)
      rw [hk, hN50]
      exact le_of_eq (by ring)
  subst hk1
  refine ⟨?_, ?_⟩
  · simp only [hk, hZ034, mul_one]
  · rw [hN50, hk]
    ring

end CFSG.RankThree.GF2n.Stroth80
