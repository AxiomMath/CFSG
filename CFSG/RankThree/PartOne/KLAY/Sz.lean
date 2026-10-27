module

public import CFSG.RankThree.PartOne.KLAY.F4
public import CFSG.LieType.Ree.LargeReeSimplePairGeneration
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.KFU
  CFSG.LieType.Ree.LargeReeCover CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (rootList mem_rootList)

open scoped Pointwise

theorem rootLevi_le_parabolicLevi {τ : Tag} {K : Type} [Field K]
    (J : Set (Fin τ.rank)) : rootLevi τ K J ≤ parabolicLevi τ K J := by
  refine iSup₂_le fun α hα => ?_
  rcases IsRoot.height_pos_or_neg hα.1 with hpos | hneg
  · exact (le_iSup₂_of_le α ⟨hα, hα.1, hpos⟩ le_rfl).trans
      (parabolicLeviUnipotent_le_parabolicLevi J)
  · have hmem : -α ∈ parabolicPosRoots τ J :=
      ⟨⟨IsRoot.neg hα.1, fun i hi => by rw [Pi.neg_apply, hα.2 i hi, neg_zero]⟩, IsRoot.neg hα.1,
        by rw [height_neg]; omega⟩
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-α) rfl hmem
    have hα' : α = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by
      rw [smul_neg, hwj, neg_neg]
    rw [hα', ← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ j)]
    rintro _ ⟨u, hu, rfl⟩
    have huM : u ∈ parabolicLevi τ K J := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hj c
    have hn := canonicalRep_mem_parabolicLevi (K := K) hw
    exact mul_mem (mul_mem hn huM) (inv_mem hn)

section Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem mem_reeFixed_of_mul_mem_reeGamma {j : Fin F4.fixedOrbitCount} {h v : ModGL F4.tag K}
    (hh : h ∈ torusGroup F4.tag K) (hv : v ∈ rootSpan F4.tag K (F4.fixedOrbitRoots j))
    (hgΓ : h * v ∈ F4.reeGamma K a) :
    h ∈ F4.reeFixedTorus K a ∧ v ∈ F4.reeFixedOrbitUnipotent K a j := by
  have hvU : v ∈ posUnipotent F4.tag K := rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hv
  have hha := torusGroup_le_adjointGroup F4 K hh
  have hva := rootSpan_le_adjointGroup _ hv
  have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (mul_mem hha hva)
  have e : (⟨h * v, mul_mem hha hva⟩ : adjointGroup F4.tag K) = ⟨h, hha⟩ * ⟨v, hva⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul] at hF
  have hFh := finiteReeAut_mem_torusGroup (a := a) hh hha
  have hFv := finiteReeAut_mem_of_map_le (a := a) (map_finiteReeAut_rootSpan_le fun α hα =>
    ⟨(mem_fixedOrbitRoots_iff.1 hα).1, dualRoot_mem_fixedOrbitRoots hα⟩) hv hva
  obtain ⟨h1, h2⟩ := (triangular_borel_structure.{0, 0} F4.tag K).2.2.2.2.2.2.1 _ hFh _ hh _
    (rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hFv) _ hvU hF
  exact ⟨Subgroup.mem_inf.2 ⟨hh, mem_reeGamma_of_fixed hha h1⟩,
    Subgroup.mem_inf.2 ⟨hv, mem_reeGamma_of_fixed hva h2⟩⟩

theorem exists_mul_of_eq_torus_mul_rootLevi {j : Fin F4.fixedOrbitCount}
    {t q g : ModGL F4.tag K} (ht : t ∈ torusGroup F4.tag K)
    (hq : q ∈ rootLevi F4.tag K (F4.fixedOrbitSet j)) (hg : g = t * q)
    (hgB : g ∈ F4.reeFixedBorel K a) :
    ∃ h ∈ F4.reeFixedTorus K a, ∃ x ∈ F4.reeFixedOrbitUnipotent K a j, g = h * x := by
  obtain ⟨hgB', hgΓ⟩ := Subgroup.mem_inf.1 hgB
  have hqB : q ∈ borelGroup F4.tag K := by
    have h1 : q = t⁻¹ * g := by rw [hg]; group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left ht)) hgB'
  obtain ⟨h', hh', v, hv, hqv⟩ :=
    (large_Ree_parabolic_degree_intersection F4.tag K (F4.fixedOrbitSet j)).2.1 q
      (Subgroup.mem_inf.2 ⟨hq, hqB⟩)
  have hv' : v ∈ rootSpan F4.tag K (F4.fixedOrbitRoots j) := hv
  have hgv : g = (t * h') * v := by rw [hg, ← hqv, mul_assoc]
  have hΓ : (t * h') * v ∈ F4.reeGamma K a := hgv ▸ hgΓ
  obtain ⟨h1, h2⟩ := mem_reeFixed_of_mul_mem_reeGamma (mul_mem ht hh') hv' hΓ
  exact ⟨t * h', h1, v, h2, hgv⟩

theorem mem_torus_mul_block {j : Fin F4.fixedOrbitCount} {y t q : ModGL F4.tag K}
    (hyΓ : y ∈ F4.reeGamma K a) (ht : t ∈ torusGroup F4.tag K)
    (hq : q ∈ rootLevi F4.tag K (F4.fixedOrbitSet j)) (hy : y = t * q) :
    y ∈ (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) *
      (F4.reeLocalBlock K a j : Set (ModGL F4.tag K)) := by
  have hJ : y ∈ parabolicSubgroup F4.tag K (F4.fixedOrbitSet j) := by
    rw [hy]
    exact parabolicLevi_le_parabolicSubgroup _ (mul_mem (torusGroup_le_parabolicLevi _ ht)
      (rootLevi_le_parabolicLevi _ hq))
  have hω : (y : ModGL F4.tag K ⧸ F4.reeFixedBorel K a) ∈ F4.reeLocalCosets K a j :=
    ⟨y, Subgroup.mem_inf.2 ⟨hyΓ, hJ⟩, rfl⟩
  obtain ⟨m, hm, hmω⟩ := exists_mem_reeLocalBlock_smul_one_eq hω
  rw [smul_mk, mul_one, QuotientGroup.eq] at hmω
  have hmL : m ∈ rootLevi F4.tag K (F4.fixedOrbitSet j) := reeLocalBlock_le_rootLevi j hm
  have hTn : torusGroup F4.tag K ≤
      Subgroup.normalizer (rootLevi F4.tag K (F4.fixedOrbitSet j) : Set (ModGL F4.tag K)) :=
    torusGroup_le_normalizer_rootSpan (fun α hα => hα.1)
  have hc : t⁻¹ * m⁻¹ * t ∈ rootLevi F4.tag K (F4.fixedOrbitSet j) := by
    have h1 := Subgroup.mem_normalizer_iff.1 (hTn (inv_mem ht)) m⁻¹
    rw [inv_inv] at h1
    exact h1.1 (inv_mem hmL)
  obtain ⟨h, hh, x, hx, hhx⟩ := exists_mul_of_eq_torus_mul_rootLevi ht (mul_mem hc hq)
    (g := m⁻¹ * y) (by rw [hy]; group) hmω
  have hy' : y = m * (h * x) := by
    calc y = m * (m⁻¹ * y) := by group
      _ = m * (h * x) := by rw [hhx]
  refine ⟨h, hh, h⁻¹ * m * h * x, ?_, ?_⟩
  · have h1 : h⁻¹ * m * h ∈ F4.reeLocalBlock K a j := by
      have h2 := Subgroup.mem_normalizer_iff.1
        (reeFixedTorus_le_normalizer_reeLocalBlock j (inv_mem hh)) m
      rw [inv_inv] at h2
      exact h2.1 hm
    exact mul_mem h1 (reeFixedOrbitUnipotent_le_reeLocalBlock j hx)
  · rw [hy']
    group

@[expose] def blk2 : Fin F4.fixedOrbitCount := ⟨1, by decide⟩

theorem rankOneTorusTwo_le_reeFixedTorus (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusTwo K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨u, rfl⟩
  have h1 : torusPair (K := K) a (1, u) = pairedTorusHom (K := K) a (f4i 1) (f4i 2) u := by
    rw [torusPair_apply, pairedTorusHom_apply]
    simp [torusElt_one]
  have h2 : pairedTorusHom (K := K) a (f4i 1) (f4i 2) u ∈ torusGroup F4.tag K := by
    rw [pairedTorusHom_apply]
    exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  refine Subgroup.mem_inf.2 ⟨h2, ?_⟩
  rw [← h1]
  exact torusPair_mem_reeGamma a hK (1, u)

theorem reeLocalBlock_eq_rankOneGroupTwo (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalBlock K a blk2 = rankOneGroupTwo K a := by
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement blk2) ∈
      rankOneGroupTwo K a := Subgroup.subset_closure (Or.inr rfl)
  have hX : F4.reeFixedOrbitUnipotent K a blk2 ≤ rankOneGroupTwo K a := fun x hx =>
    Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hle : F4.reeLocalBlock K a blk2 ≤ rankOneGroupTwo K a := by
    refine sup_le hX ?_
    rw [← map_conj_reeFixedOrbitUnipotent]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hn (hX hx)) (inv_mem hn)
  refine le_antisymm hle ?_
  have hnorm : ((F4.reeLocalBlock K a blk2).subgroupOf (rankOneGroupTwo K a)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ((hx | hx) | hx)
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_left hx)
    · exact reeFixedTorus_le_normalizer_reeLocalBlock blk2 (rankOneTorusTwo_le_reeFixedTorus hK hx)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have hmap : (F4.reeLocalBlock K a blk2).map
          (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K
            (F4.fixedOrbitElement blk2))).toMonoidHom = F4.reeLocalBlock K a blk2 := by
        unfold reeLocalBlock
        rw [Subgroup.map_sup, map_conj_reeFixedOrbitUnipotent, map_conj_reeFixedOrbitNegUnipotent,
          sup_comm]
      exact mem_normalizer_of_map_eq hmap
  have := (isSimpleGroup_rankOneGroupTwo ha hK).1
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((F4.reeLocalBlock K a blk2).subgroupOf (rankOneGroupTwo K a)) with hbot | htop
  · exfalso
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) blk2
    have hmem : (⟨u, hX hu⟩ : ↥(rankOneGroupTwo K a)) ∈
        (F4.reeLocalBlock K a blk2).subgroupOf (rankOneGroupTwo K a) :=
      Subgroup.mem_subgroupOf.2 (reeFixedOrbitUnipotent_le_reeLocalBlock blk2 hu)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)
  · intro g hg
    have hmem : (⟨g, hg⟩ : ↥(rankOneGroupTwo K a)) ∈
        (F4.reeLocalBlock K a blk2).subgroupOf (rankOneGroupTwo K a) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

end Ree

section Kernel

theorem torusExp_combo_sz (θ : ℤ) (β : Fin F4.tag.rank → ℤ) :
    torusExp0 θ β + (1 + θ) * torusExp1 θ β =
      (β (f4i 0) + β (f4i 1) - β (f4i 2)) + θ * (β (f4i 3) - β (f4i 0)) +
        θ ^ 2 * (-2 * β (f4i 1) + 2 * β (f4i 2) - β (f4i 3)) := by
  simp only [torusExp0, torusExp1, ReeTag.cartanPair, sum_f4, cartan_f4]
  simp
  ring

set_option maxRecDepth 100000 in
theorem f4_root_check_sz :
    ∀ β ∈ rootList F4.tag, (β (f4i 0) ≠ 0 ∨ β (f4i 3) ≠ 0) →
      2 * β (f4i 0) ^ 2 - β (f4i 3) ^ 2 ∣ 4 := by
  decide +kernel

theorem f4_kernel_sub_sz {p : ℕ} {θ : ℤ} (h5 : 5 ≤ p)
    (hθ : (p : ℤ) ∣ 2 * θ ^ 2 - 1) {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (A : Fin F4.tag.rank → Kˣ)
    (hA : ∀ β, IsRoot F4.tag β → rootChar A β = ζ ^ ((β (f4i 0) + β (f4i 1) - β (f4i 2)) +
      θ * (β (f4i 3) - β (f4i 0)) + θ ^ 2 * (-2 * β (f4i 1) + 2 * β (f4i 2) - β (f4i 3)))) :
    rootCharKernel A ⊆ parabolicRoots F4.tag (F4.fixedOrbitSet blk2) := by
  rintro β ⟨hβ, hχ⟩
  rw [hA β hβ] at hχ
  have hdvd := (hζ.zpow_eq_one_iff_dvd _).1 hχ
  by_cases hz : β (f4i 0) = 0 ∧ β (f4i 3) = 0
  · refine ⟨hβ, fun i hi => ?_⟩
    have hJ : F4.fixedOrbitSet blk2 = ({f4i 1, f4i 2} : Set (Fin F4.tag.rank)) := rfl
    rw [hJ] at hi
    fin_cases i
    · exact hz.1
    · exact absurd (Or.inl rfl) hi
    · exact absurd (Or.inr rfl) hi
    · exact hz.2
  · exfalso
    have hne : β (f4i 0) ≠ 0 ∨ β (f4i 3) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz hcon
    have h4 := f4_root_check_sz β ((mem_rootList).2 hβ) hne
    set N : ℤ := (β (f4i 0) + β (f4i 1) - β (f4i 2)) + θ * (β (f4i 3) - β (f4i 0)) +
      θ ^ 2 * (-2 * β (f4i 1) + 2 * β (f4i 2) - β (f4i 3)) with hN
    have hid : 2 * β (f4i 0) ^ 2 - β (f4i 3) ^ 2 =
        (2 * N - (2 * θ ^ 2 - 1) * (-2 * β (f4i 1) + 2 * β (f4i 2) - β (f4i 3))) *
          ((2 * β (f4i 0) - β (f4i 3)) - 2 * θ * (β (f4i 3) - β (f4i 0))) +
        2 * (2 * θ ^ 2 - 1) * (β (f4i 3) - β (f4i 0)) ^ 2 := by
      rw [hN]
      ring
    have hpN : (p : ℤ) ∣ 2 * β (f4i 0) ^ 2 - β (f4i 3) ^ 2 := by
      rw [hid]
      exact dvd_add (Dvd.dvd.mul_right (dvd_sub (Dvd.dvd.mul_left hdvd 2)
        (Dvd.dvd.mul_right hθ _)) _) (Dvd.dvd.mul_right (Dvd.dvd.mul_left hθ 2) _)
    have hp4 : (p : ℤ) ∣ 4 := hpN.trans h4
    have hp4' : p ∣ 4 := by exact_mod_cast hp4
    have := Nat.le_of_dvd (by norm_num) hp4'
    omega

end Kernel

section Layer

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeLocalBlock_subgroupOf_facts (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup ↥((F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)) ∧
      Group.IsPerfect ↥((F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)) ∧
      Nat.card ↥((F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)) =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hMR := reeLocalBlock_eq_rankOneGroupTwo ha hK
  have hMΓ : F4.reeLocalBlock K a blk2 ≤ F4.reeGamma K a := reeLocalBlock_le_reeGamma blk2
  let e : ↥((F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a)) ≃*
      ↥(rankOneGroupTwo K a) :=
    (Subgroup.subgroupOfEquivOfLe hMΓ).trans (MulEquiv.subgroupCongr hMR)
  have hs := (isSimpleGroup_rankOneGroupTwo ha hK).1
  have hperf := (suzuki_perfect ha hK).2
  have hperfR : Group.IsPerfect ↥(rankOneGroupTwo K a) :=
    Group.IsPerfect.ofSurjective (f := (rankOneEquivSuzuki K a ha hK).symm.toMonoidHom)
      (rankOneEquivSuzuki K a ha hK).symm.surjective
  refine ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv, card_rankOneGroupTwo ha hK]

theorem f4_layerD_sz (hP : F4Param p a K) {z z2 : rootsOfUnity p K}
    (hz : IsPrimitiveRoot (z : Kˣ) p) (hz2 : (z2 : Kˣ) = (z : Kˣ) ^ (1 + 2 ^ a)) :
    layerD (tp4M hP ![z, z2]) =
      (F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a) := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have h5 := hP.five_le
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hζ1 : (z : Kˣ) ≠ 1 := hz.ne_one (by omega)
  set bM : ↥(F4.reeGamma K a) := tp4M hP ![z, z2] with hbM
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) ![z, z2])
  have hA : torusPair (K := K) a ((z : Kˣ), (z : Kˣ) ^ (1 + 2 ^ a)) =
      rootDiagUnit F4.tag l := by
    rw [← hl, tp4Hom_apply, ← hz2]
    rfl
  have hA' : ∀ β : Fin F4.tag.rank → ℤ, IsRoot F4.tag β → rootChar l β =
      (z : Kˣ) ^ ((β (f4i 0) + β (f4i 1) - β (f4i 2)) + (2 : ℤ) ^ a * (β (f4i 3) - β (f4i 0)) +
        ((2 : ℤ) ^ a) ^ 2 * (-2 * β (f4i 1) + 2 * β (f4i 2) - β (f4i 3))) := by
    intro β hβ
    have hv : (z : Kˣ) ^ (1 + 2 ^ a) = (z : Kˣ) ^ ((1 : ℤ) + 2 ^ a) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [rootChar_eq_torusWeight hA hβ, torusWeight_apply, hv,
      ← torusExp_combo_sz ((2 : ℤ) ^ a) β, zpow_add (z : Kˣ) (torusExp0 ((2 : ℤ) ^ a) β),
      zpow_mul (z : Kˣ)]
  have hap : ∀ i, l i ^ p = 1 := fun i => by
    have h := hA' (Pi.single i 1) (IsRoot.basis i)
    rw [rootChar_single] at h
    rw [h, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have hθ : (p : ℤ) ∣ 2 * ((2 : ℤ) ^ a) ^ 2 - 1 := by
    have := hP.theta_dvd
    push_cast at this
    exact this
  have hker : rootCharKernel l ⊆ parabolicRoots F4.tag (F4.fixedOrbitSet blk2) :=
    f4_kernel_sub_sz h5 hθ hz l hA'
  have hJ : F4.fixedOrbitSet blk2 = ({f4i 1, f4i 2} : Set (Fin F4.tag.rank)) := rfl
  have hnot0 : f4i 0 ∉ F4.fixedOrbitSet blk2 := by
    rw [hJ]
    rintro (h | h) <;> exact absurd h (by decide)
  have hnot3 : f4i 3 ∉ F4.fixedOrbitSet blk2 := by
    rw [hJ]
    rintro (h | h) <;> exact absurd h (by decide)
  have hSker : ∀ α ∈ parabolicRoots F4.tag (F4.fixedOrbitSet blk2),
      IsRoot F4.tag α ∧ rootChar l α = 1 := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    rw [hA' α hα.1, hα.2 _ hnot0, hα.2 _ hnot3]
    refine (hz.zpow_eq_one_iff_dvd _).2 ?_
    have h1 : (0 + α (f4i 1) - α (f4i 2)) + (2 : ℤ) ^ a * (0 - 0) +
        ((2 : ℤ) ^ a) ^ 2 * (-2 * α (f4i 1) + 2 * α (f4i 2) - 0) =
        (α (f4i 2) - α (f4i 1)) * (2 * ((2 : ℤ) ^ a) ^ 2 - 1) := by ring
    rw [h1]
    exact Dvd.dvd.mul_left hθ _
  have hbMd : ((bM : ↥(F4.reeGamma K a)) : ModGL F4.tag K) = rootDiagUnit F4.tag l := by
    rw [hbM, coe_tp4M]
    exact hl
  have hbM1 : bM ≠ 1 := fun h => hζ1 (by
    have h1 : (![z, z2] : Fin 2 → rootsOfUnity p K) = 1 :=
      tp4M_injective hP (h.trans (map_one _).symm)
    have := congrFun h1 0
    exact congrArg (fun x : rootsOfUnity p K => ((x : Kˣ))) this)
  have ha1 : l ≠ 1 := fun h => hbM1 (Subtype.ext (by rw [hbMd, h, rootDiagUnit_one]; rfl))
  have hSn : ∀ α ∈ parabolicRoots F4.tag (F4.fixedOrbitSet blk2),
      -α ∈ parabolicRoots F4.tag (F4.fixedOrbitSet blk2) := fun α hα =>
    ⟨IsRoot.neg hα.1, fun i hi => by
      have h := hα.2 i hi
      show -(α i) = 0
      rw [h, neg_zero]⟩
  have hfacts := reeLocalBlock_subgroupOf_facts (K := K) (a := a) hP.one_le hK
  refine inSubgroup_perfectResidual_centralizer_eq (F4.reeGamma K a) bM (F4.reeFixedTorus K a)
    (F4.reeLocalBlock K a blk2)
    (fun s hs t ht => (triangular_borel_structure.{0, 0} F4.tag K).1 s
      (Subgroup.mem_inf.1 hs).1 t (Subgroup.mem_inf.1 ht).1)
    (reeFixedTorus_le_normalizer_reeLocalBlock blk2) ?_ ?_
    ((F4.reeLocalBlock K a blk2).subgroupOf (F4.reeGamma K a))
    ((Subgroup.subgroupOf_map_subtype _ _).trans (inf_comm _ _)) hfacts.2.1
  · intro x hx
    rw [hbMd]
    exact rootSpan_le_centralizer_of_char_one (fun α hα => hSker α hα)
      (reeLocalBlock_le_rootLevi blk2 hx)
  · intro y hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
    have hc' : (y : ModGL F4.tag K) * rootDiagUnit F4.tag l =
        rootDiagUnit F4.tag l * (y : ModGL F4.tag K) := by
      rw [← hbMd]
      exact hc
    obtain ⟨t, ht, q, hq, hyt⟩ := KE.mem_torus_mul_rootSpan_of_commute hp
      (KE.not_dvd_card_weylGroup_F4 hp (by omega)) hap ha1
      (S := parabolicRoots F4.tag (F4.fixedOrbitSet blk2)) (fun α hα => hα.1)
      hSn hker
      (ReeTag.mem_reeGamma.1 y.2).1 hc'
    exact mem_torus_mul_block y.2 ht hq hyt.symm

end Layer

end CFSG.RankThree.PartOne.KLAY
