module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeOuterSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeOuterJT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeOuterFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeOuterTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement

private lemma conjNormal_not_mem_inner {A : Type} [Group A] {L : Subgroup A} [L.Normal]
    (hCL : centralizer (L : Set A) = ⊥) {d : A} (hdL : d ∉ L) :
    (MulAut.conjNormal d : MulAut ↥L) ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
  rintro ⟨y, hy⟩
  have hcomm : ∀ x : ↥L, (x : A) * ((y : A)⁻¹ * d) = ((y : A)⁻¹ * d) * (x : A) := by
    intro x
    have h := congrArg (fun (f : MulAut ↥L) => ((f x : ↥L) : A)) hy
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc (x : A) * ((y : A)⁻¹ * d)
        = (y : A)⁻¹ * ((y : A) * (x : A) * (y : A)⁻¹) * d := by group
      _ = (y : A)⁻¹ * (d * (x : A) * d⁻¹) * d := by rw [h]
      _ = ((y : A)⁻¹ * d) * (x : A) := by group
  have hz : ((y : A)⁻¹ * d) ∈ centralizer (L : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hcomm ⟨w, hw⟩
  rw [hCL, Subgroup.mem_bot] at hz
  apply hdL
  have hd : d = (y : A) := by
    calc d = (y : A) * ((y : A)⁻¹ * d) := by group
      _ = (y : A) * 1 := by rw [hz]
      _ = (y : A) := mul_one _
  rw [hd]
  exact y.2

private lemma eq_or_eq_seven_mul {d e f : ℕ} (hd : 3 ≤ d) (hf : f = 7 * d)
    (hde : d ∣ e) (hef : e ∣ f) : e = d ∨ e = 7 * d := by
  obtain ⟨c, rfl⟩ := hde
  have hc7 : c ∣ 7 := by
    have h : d * c ∣ d * 7 := by
      rw [hf, mul_comm 7 d] at hef
      exact hef
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h
  rcases (Nat.dvd_prime Nat.prime_seven).mp hc7 with h | h
  · left
    rw [h, mul_one]
  · right
    rw [h, mul_comm d 7]

theorem uc2_10_7OddReeSevenOuter_holds :
    UC2_10_7OddReeSevenOuter := by
  intro A _ _ L hLn hLs hCL f hmod T B M hT hBT hB7 hBL hsup hTM hBM hstar
  classical
  have hTL : T ≤ L := le_of_isSylowOf_two_of_ree hLn hCL hmod hT
  have hLB : L ⊔ B = ⊤ := by
    have h := hsup
    rw [sup_eq_left.mpr hTL] at h
    exact h
  set T' : Subgroup ↥L := T.subgroupOf L with hT'def
  set K : Subgroup ↥L := M.subgroupOf L with hKdef
  have hT'rel : T'.index = T.relIndex L := by
    rw [hT'def]
    rfl
  have hT'pg : IsPGroup 2 T' := by
    rw [hT'def]
    exact hT.isPGroup.comap_subtype
  have hT'idx : ¬ 2 ∣ T'.index := by
    have h2 : ¬ 2 ∣ T.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
      rwa [Subgroup.relIndex_top_right] at h
    rw [hT'rel]
    intro hd
    refine h2 ?_
    rw [← Subgroup.relIndex_mul_index hTL]
    exact dvd_mul_of_dvd_left hd L.index
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hT'pg, ?_⟩
    rwa [Subgroup.relIndex_top_right]
  obtain ⟨hT8', hCT', h21⟩ := ree_sylow_two_facts hLs hmod hT'
  have hT8 : Nat.card T = 8 := by
    rw [← hT8', hT'def]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (K := L) hTL).toEquiv).symm
  have hidx147 : (T.subgroupOf (normalizer (T : Set A))).index = 147 := by
    rw [index_normalizer_eq_mul_seven hTL hLB hB7 hBL hBT, ← hT'def, h21]
  have hNA : normalizer (T : Set A) ≤ M :=
    normalizer_le_of_index_eq_147 hT8 hidx147 hBT hB7 hTM hBM hstar
  have hTK : T' ≤ K := by
    intro x hx
    rw [hKdef, Subgroup.mem_subgroupOf]
    exact hTM (Subgroup.mem_subgroupOf.mp hx)
  have hstep : ∀ (y : ↥L), y ∈ normalizer (T' : Set ↥L) → ∀ s ∈ T,
      (y : A) * s * (y : A)⁻¹ ∈ T := by
    intro y hy s hs
    have hs' : (⟨s, hTL hs⟩ : ↥L) ∈ T' := Subgroup.mem_subgroupOf.mpr hs
    have h1 : y * ⟨s, hTL hs⟩ * y⁻¹ ∈ T' :=
      (Subgroup.mem_normalizer_iff.mp hy ⟨s, hTL hs⟩).mp hs'
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2
  have hNK : normalizer (T' : Set ↥L) ≤ K := by
    intro y hy
    rw [hKdef, Subgroup.mem_subgroupOf]
    refine hNA ?_
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact hstep y hy s hs
    · intro hs
      have hy' : y⁻¹ ∈ normalizer (T' : Set ↥L) := Subgroup.inv_mem _ hy
      have h := hstep y⁻¹ hy' ((y : A) * s * (y : A)⁻¹) hs
      have heq : ((y⁻¹ : ↥L) : A) = (y : A)⁻¹ := rfl
      rw [heq] at h
      have h' : (y : A)⁻¹ * ((y : A) * s * (y : A)⁻¹) * (y : A) = s := by group
      simpa [h'] using h
  have hN168 : Nat.card ↥(normalizer (T' : Set ↥L)) = 168 := by
    have h := Subgroup.index_mul_card (H := T'.subgroupOf (normalizer (T' : Set ↥L)))
    have hcard : Nat.card ↥(T'.subgroupOf (normalizer (T' : Set ↥L))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (K := normalizer (T' : Set ↥L)) Subgroup.le_normalizer).toEquiv, hT8']
    rw [h21, hcard] at h
    omega
  obtain ⟨x, hx7⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hN168]; norm_num)
  let X₇ : Subgroup ↥L := Subgroup.zpowers (x : ↥L)
  have hX₇7 : Nat.card X₇ = 7 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx7]
  have hX₇T : X₇ ≤ normalizer (T' : Set ↥L) := Subgroup.zpowers_le.mpr x.2
  have hX₇C : ¬ X₇ ≤ centralizer (T' : Set ↥L) := by
    intro h
    have hd := Subgroup.card_dvd_of_le h
    rw [hX₇7, hCT', hT8'] at hd
    norm_num at hd
  have hX₇K : X₇ ≤ K := hX₇T.trans hNK
  have hidxK : ∀ N : Subgroup ↥K, N.index ≠ 2 :=
    index_ne_two_of_fpf hT' hT8' hX₇T hX₇7 hX₇C hTK hX₇K
  have hLM : L ⊔ M = ⊤ := eq_top_iff.mpr (hLB ▸ sup_le_sup_left hBM L)
  have hKidx : K.index = M.index := by
    rw [hKdef]
    show (M.subgroupOf L).index = M.index
    rw [show (M.subgroupOf L).index = M.relIndex L from rfl,
      ← CFSG.AGLEmbedding.relIndex_sup_left_eq_of_normal L M, hLM,
      Subgroup.relIndex_top_right]
  have hM7 : ¬ 7 ∣ M.index := by
    have hBpg : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by simpa using hB7)
    have h := index_modEq_one_of_star (p := 7) hBpg hBM hstar
    rw [Nat.ModEq] at h
    intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    omega
  have hK7 : ¬ 7 ∣ K.index := by
    rw [hKidx]
    exact hM7
  have hBcyc : IsCyclic ↥B := isCyclic_of_prime_card (by simpa using hB7)
  obtain ⟨b, hb7⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥B)
  have hb7' : orderOf b = 7 := by
    rw [hb7]
    exact hB7
  let b₀ : A := (b : A)
  have hb₀B : b₀ ∈ B := b.2
  have horder : orderOf b₀ = 7 := by
    show orderOf ((b : ↥B) : A) = 7
    rw [Subgroup.orderOf_coe, hb7']
  have hzB : Subgroup.zpowers b₀ = B := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb₀B) ?_
    rw [hB7, Nat.card_zpowers, horder]
  have hb₀L : b₀ ∉ L := by
    intro h
    apply hBL
    rw [← hzB]
    exact Subgroup.zpowers_le.mpr h
  let α : MulAut ↥L := MulAut.conjNormal b₀
  have hα : α ^ 7 = 1 := by
    have hmap : (MulAut.conjNormal (b₀ ^ 7) : MulAut ↥L) = MulAut.conjNormal b₀ ^ 7 :=
      map_pow (MulAut.conjNormal (H := L)) b₀ 7
    have hαeq : α = MulAut.conjNormal b₀ := rfl
    rw [hαeq, ← hmap, ← horder, pow_orderOf_eq_one, map_one]
  have hαout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    conjNormal_not_mem_inner hCL hb₀L
  have hfix_comm : ∀ x ∈ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α,
      b₀ * (x : A) = (x : A) * b₀ := by
    intro x hx
    have hx' : α x = x := hx
    have h2 : ((α x : ↥L) : A) = b₀ * (x : A) * b₀⁻¹ := by
      show ((MulAut.conjNormal b₀ x : ↥L) : A) = b₀ * (x : A) * b₀⁻¹
      exact MulAut.conjNormal_apply b₀ x
    have h3 : b₀ * (x : A) * b₀⁻¹ = (x : A) := by rw [← h2, hx']
    calc b₀ * ↑x = b₀ * ↑x * b₀⁻¹ * b₀ := by group
      _ = ↑x * b₀ := by rw [h3]
  have hFixK : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α ≤ K := by
    intro x hx
    rw [hKdef, Subgroup.mem_subgroupOf]
    apply hstar (x : A)
    intro c hc
    have hc0 : b₀ ∈ Subgroup.centralizer ({(x : A)} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hfix_comm x hx
    have hBcent : B ≤ Subgroup.centralizer ({(x : A)} : Set A) :=
      hzB ▸ Subgroup.zpowers_le.mpr hc0
    have hcx : c * (x : A) = (x : A) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (hBcent hc)
    have h1 : (x : A)⁻¹ * c * (x : A) = c := by
      calc (x : A)⁻¹ * c * (x : A) = (x : A)⁻¹ * (c * (x : A)) := by rw [mul_assoc]
        _ = (x : A)⁻¹ * ((x : A) * c) := by rw [hcx]
        _ = c := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1]
    exact hBM hc
  have hLcard : Nat.card ↥L = (3 ^ f) ^ 3 * ((3 ^ f) ^ 3 + 1) * (3 ^ f - 1) := by
    have hree : CFSG.Blueprint.ReeTitsModel ↥L .twistedG2 3 f :=
      (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
    obtain ⟨-, -, -, -, hcard⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hree
    rw [hcard]
    simp [CFSG.Open.ordRee]
  obtain ⟨d, hfd, hdodd, hFixcard, hbig⟩ := ree_outer_seven_fixed hmod α hα hαout
  by_cases hd1 : d = 1
  ·
    have hf7 : f = 7 := by rw [hfd, hd1]
    have h49L : 49 ∣ Nat.card ↥L := by
      rw [hLcard, hf7]
      norm_num
    have hcop : Nat.Coprime 49 K.index := by
      have h7 : Nat.Coprime 7 K.index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr hK7
      exact h7.pow_left 2
    have h49K : 49 ∣ Nat.card ↥K := by
      have hmul := Subgroup.index_mul_card (H := K)
      rw [← hmul] at h49L
      exact hcop.dvd_of_dvd_mul_left h49L
    have hKtop : K = ⊤ :=
      ree_seven_eq_top_of_sq_dvd hLs (hf7 ▸ hmod) hT' hTK hNK hidxK h49K
    left
    exact Subgroup.subgroupOf_eq_top.mp (by rw [← hKdef]; exact hKtop)
  ·
    have hd3 : 3 ≤ d := by
      obtain ⟨m, hm⟩ := hdodd
      omega
    obtain ⟨v, hvFix, hv2, F, hFFix, hFv, ⟨eF⟩⟩ := hbig hd3
    obtain ⟨e, hde, hef, hKcard⟩ :=
      ree_card_eq_of_psl2_le hLs hmod hidxK (hFixK hvFix) hv2 hd3
        (hFFix.trans hFixK) hFv eF
    rcases eq_or_eq_seven_mul hd3 hfd hde hef with he | he
    ·
      right
      have hKcardFix : Nat.card ↥K =
          Nat.card ↥(CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α) := by
        rw [hKcard, hFixcard, he]
      have hKfix : K = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α :=
        (Subgroup.eq_of_le_of_card_ge hFixK (by rw [hKcardFix])).symm
      have hTfix : T' ≤ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α := by
        rw [← hKfix]
        exact hTK
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have htfix : (⟨t, hTL ht⟩ : ↥L) ∈
          CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α :=
        hTfix (Subgroup.mem_subgroupOf.mpr ht)
      have hc0 : b₀ ∈ Subgroup.centralizer ({t} : Set A) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hfix_comm ⟨t, hTL ht⟩ htfix
      have hBcent : B ≤ Subgroup.centralizer ({t} : Set A) :=
        hzB ▸ Subgroup.zpowers_le.mpr hc0
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBcent hc)
    ·
      left
      have hcardKeq : Nat.card ↥K = Nat.card ↥L := by
        rw [hKcard, hLcard, hfd, he]
      have hKtop : K = ⊤ := (Subgroup.card_eq_iff_eq_top (H := K)).mp hcardKeq
      exact Subgroup.subgroupOf_eq_top.mp (by rw [← hKdef]; exact hKtop)

theorem uc2_10_7OddReeSeven_holds :
    UC2_10_7OddReeSeven :=
  uc2_10_7OddReeSeven_of_phi6_outer uc2_10_7OddReeSevenInnerPhi6_holds
    uc2_10_7OddReeSevenOuter_holds

theorem uc2_10_7OddRee_holds :
    UC2_10_7OddRee :=
  uc2_10_7OddRee_of_seven uc2_10_7OddReeSeven_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
