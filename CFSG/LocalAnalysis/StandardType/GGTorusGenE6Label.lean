module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Model
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkLabel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCent
public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow5Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkNarrow11Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private def pTorsionSubgroup (p : ℕ) {H : Type} [Group H] (A : Subgroup H)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Subgroup H where
  carrier := {x | x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1}
  one_mem' := ⟨A.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxA, k, hxk⟩ ⟨hyA, l, hyl⟩
    have hxy : Commute x y := hcomm x hxA y hyA
    refine ⟨A.mul_mem hxA hyA, max k l, ?_⟩
    have hxk' : x ^ p ^ max k l = 1 := by
      have hd : orderOf x ∣ p ^ max k l :=
        (orderOf_dvd_iff_pow_eq_one.mpr hxk).trans (Nat.pow_dvd_pow p (le_max_left k l))
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hyl' : y ^ p ^ max k l = 1 := by
      have hd : orderOf y ∣ p ^ max k l :=
        (orderOf_dvd_iff_pow_eq_one.mpr hyl).trans (Nat.pow_dvd_pow p (le_max_right k l))
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    rw [hxy.mul_pow, hxk', hyl', mul_one]
  inv_mem' := by
    rintro x ⟨hxA, k, hxk⟩
    exact ⟨A.inv_mem hxA, k, by rw [inv_pow, hxk, inv_one]⟩

private theorem mem_pTorsionSubgroup (p : ℕ) {H : Type} [Group H] (A : Subgroup H)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : H} :
    x ∈ pTorsionSubgroup p A hcomm ↔ x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1 :=
  Iff.rfl

private theorem isPGroup_pTorsionSubgroup (p : ℕ) {H : Type} [Group H] (A : Subgroup H)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    IsPGroup p (pTorsionSubgroup p A hcomm) := fun x => by
  obtain ⟨k, hk⟩ := ((mem_pTorsionSubgroup p A hcomm).mp x.2).2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem torus_map_le_centralizer_twE6
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {T : Subgroup L'} {w : Fin 6 → L'}
    (hT : GGE6ThreeStrongWitness (ggQuotHom θ).ker (ggGamma L' hE).range T w) :
    T.map L'.subtype ≤ Subgroup.centralizer (E : Set M) := by
  rintro x ⟨t, ht, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hfix := hT.2.2.1 (ggGamma L' hE ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩ t ht
  have hval : (e : M) * ((t : L') : M) * (e : M)⁻¹ = ((t : L') : M) := by
    have h1 := congrArg (fun y : L' => (y : M)) hfix
    rw [ggGamma_coe] at h1
    simpa using h1
  calc (e : M) * ((t : L') : M)
      = ((e : M) * ((t : L') : M) * (e : M)⁻¹) * (e : M) := by group
    _ = ((t : L') : M) * (e : M) := by rw [hval]

private theorem weyl_map_le_normalizer_twE6
    {M : Type} [Group M] [Finite M] {L' E E₁ : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition 3 L' E I θ hE)
    (hN : Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (E₁ : Set M))
    {T : Subgroup L'} {w : Fin 6 → L'}
    (hT : GGE6ThreeStrongWitness (ggQuotHom θ).ker (ggGamma L' hE).range T w) :
    L'.subtype '' (Subgroup.closure (Set.range w) : Set L') ⊆
      Subgroup.normalizer (E₁ : Set M) := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hsub : Subgroup.closure (Set.range w) ≤
      Subgroup.comap L'.subtype (Subgroup.normalizer (E₁ : Set M)) := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact hN (weylLift_mem_normalizer_twE6 hpos hT i)
  exact hsub hn

theorem ggTorusGenTableBRk_of_e6StrongSCr
    {R : Type} [Group R] {I : Set (MulAut R)} (hstrong : GGE6ThreeStrongSCr R I) :
    GGTorusGenTableBRk 3 R I 6 := by
  intro M _ _ L' E E₁ D' J' d θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd hJ
  classical
  obtain ⟨T, w, hT⟩ := exists_e6StrongData_of_position hstrong hpos hr
  refine ⟨center_pElts_centralize_twE6 hT, ?_⟩
  intro c hc hcp hdisj
  obtain ⟨hdec, hcent⟩ :=
    exists_mul_of_complement_position (p := 3) (by norm_num) hpos hC hE₁E hE₁C hcard
  have hcE : c ∈ Subgroup.centralizer (E : Set M) := hcent hc
  let cL : L' := ⟨c, hc.1⟩
  have hcpL : ∃ k : ℕ, cL ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hodd : Odd (orderOf cL) := by
    obtain ⟨k, hk⟩ := hcpL
    have hdvd : orderOf cL ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    exact (Odd.pow (n := k) (by decide : Odd (3 : ℕ))).of_dvd_nat hdvd
  have hfix : ∀ a ∈ (ggGamma L' hE).range, a cL = cL := by
    rintro a ⟨e, rfl⟩
    apply Subtype.ext
    have hcomm : (e : M) * (cL : M) = (cL : M) * (e : M) :=
      Subgroup.mem_centralizer_iff.mp hcE e e.2
    have hcoe := ggGamma_coe L' hE e cL
    rw [hcoe]
    rw [hcomm]
    group
  have hcLT : cL ∈ T := hT.2.2.2.2.1 cL hfix hodd
  have hdD'E₁ : d ∈ D' ⊓ E₁ := hD'E₁ ▸ Subgroup.mem_zpowers d
  have hdE : d ∈ E := hD'E hdD'E₁.1
  have ha_mem : ggGamma L' hE ⟨d, hdE⟩ ∈ (ggGamma L' hE).range :=
    ⟨⟨d, hdE⟩, rfl⟩
  have ha_ne : ggGamma L' hE ⟨d, hdE⟩ ≠ 1 := by
    intro h1
    have hdC : d ∈ Subgroup.centralizer (L' : Set M) :=
      (ggGamma_eq_one_iff L' hE ⟨d, hdE⟩).mp h1
    have hbot : d ∈ E₁ ⊓ Subgroup.centralizer (L' : Set M) := ⟨hdD'E₁.2, hdC⟩
    rw [hE₁C] at hbot
    exact hd (Subgroup.mem_bot.mp hbot)
  have hcomp : IsComponentOf (J'.subgroupOf L') (ggFix (ggGamma L' hE ⟨d, hdE⟩)) := by
    have hcomp' : IsComponentOf (J'.subgroupOf L')
        (ggFix (L'.normalizerMonoidHom ⟨d, hE hdE⟩)) :=
      isComponentOf_subgroupOf_ggFix_of_decomp hE hdE hdec hD'E hCD' hD'E₁ hJ
    have hga : ggGamma L' hE ⟨d, hdE⟩ = L'.normalizerMonoidHom ⟨d, hE hdE⟩ := by
      show L'.normalizerMonoidHom (Subgroup.inclusion hE ⟨d, hdE⟩) =
        L'.normalizerMonoidHom ⟨d, hE hdE⟩
      congr 1
    rwa [hga]
  have hgen := hT.2.2.2.2.2 (ggGamma L' hE ⟨d, hdE⟩) ha_mem ha_ne
    (J'.subgroupOf L') hcomp cL hcLT hcpL
  let GenSet : Set L' := ⋃ n ∈ (Subgroup.closure (Set.range w) : Set L'),
    (fun s : L' => n * s * n⁻¹) ''
      {s : L' | s ∈ J'.subgroupOf L' ∧ s ∈ T ∧ ∃ k : ℕ, s ^ 3 ^ k = 1}
  have hgen' : cL ∈ Subgroup.closure GenSet := hgen
  let A0 : Subgroup L' := J'.subgroupOf L' ⊓ T
  have hcommA : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x :=
    fun x hx y hy => hT.1 x hx.2 y hy.2
  let S0 : Subgroup L' := pTorsionSubgroup 3 A0 hcommA
  let S : Subgroup M := S0.map L'.subtype
  let W : Set M := L'.subtype '' (Subgroup.closure (Set.range w) : Set L')
  have hS0_pg : IsPGroup 3 S0 := isPGroup_pTorsionSubgroup 3 A0 hcommA
  have hS_pg : IsPGroup 3 S := IsPGroup.map hS0_pg L'.subtype
  have hS0T : S0 ≤ T := fun x hx => ((mem_pTorsionSubgroup 3 A0 hcommA).mp hx).1.2
  have hScent : S ≤ Subgroup.centralizer (E₁ : Set M) :=
    (Subgroup.map_mono hS0T).trans ((torus_map_le_centralizer_twE6 hT).trans
      (Subgroup.centralizer_le hE₁E))
  have hSJ : S ≤ J' := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hsJ : s ∈ J'.subgroupOf L' := ((mem_pTorsionSubgroup 3 A0 hcommA).mp hs).1.1
    simpa using Subgroup.mem_subgroupOf.mp hsJ
  have hWN : W ⊆ Subgroup.normalizer (E₁ : Set M) :=
    weyl_map_le_normalizer_twE6 hpos hN hT
  refine ⟨S, W, hS_pg, hScent, hSJ, hWN, ?_⟩
  have hsubset : L'.subtype '' GenSet ⊆
      ⋃ n ∈ W, (fun s : M => n * s * n⁻¹) '' (S : Set M) := by
    rintro y ⟨z, hz, rfl⟩
    simp only [GenSet, Set.mem_iUnion, Set.mem_image] at hz ⊢
    obtain ⟨n, hn, s, hs, rfl⟩ := hz
    refine ⟨L'.subtype n, ⟨n, hn, rfl⟩, L'.subtype s, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨s, (mem_pTorsionSubgroup 3 A0 hcommA).mpr ⟨⟨hs.1, hs.2.1⟩, hs.2.2⟩, rfl⟩
    · rw [map_mul, map_mul, map_inv]
  have hmapmem : ((cL : L') : M) ∈ Subgroup.map L'.subtype (Subgroup.closure GenSet) :=
    Subgroup.mem_map.mpr ⟨cL, hgen', rfl⟩
  rw [MonoidHom.map_closure] at hmapmem
  exact Subgroup.closure_mono hsubset (by simpa using hmapmem)

theorem ggTorusGenTableBRk_twE6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusGenTableBRk 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) 6 := by
  exact ggTorusGenTableBRk_of_e6StrongSCr (e6ThreeStrong_holds_T hn hK h3)

theorem largeEvenLabelAll_torusGenRk_twE6_three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6)
    (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk 3 R I 6 := by
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn h3 ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusGenTableBRk_twE6_three n hn hK h3⟩⟩

theorem ggL48TBForm5RowE_holds
    : GGL48TBForm5RowE := by
  intro p lab _ hlab _ _ hrow
  obtain ⟨ht, hp, h3⟩ := hrow
  subst hp
  simpa only [GGL48TB0Rank, ht, if_true] using
    largeEvenLabelAll_torusGenRk_twE6_three hlab ht h3

end CFSG.StandardType
