module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotO6p
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23Lines
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.CardNineCentralizer
public import CFSG.GroupTheory.OmegaOneE9
public import CFSG.GroupTheory.PGroupProdCommutative
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898f
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.GroupTheory.PGroup.OmegaComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Ctx23L
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem three_dvd_four_pow_sub_one (n : ℕ) : 3 ∣ 4 ^ n - 1 := by
  have h : (1 : ℕ) ≡ 4 ^ n [MOD 3] := by
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    simpa using (h4.pow n).symm
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow n 4 (by norm_num))).mp h

private theorem three_dvd_two_pow_two_mul_sub_one (n : ℕ) : 3 ∣ 2 ^ (2 * n) - 1 := by
  have h : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  rw [h]
  exact three_dvd_four_pow_sub_one n

theorem isL2Square_bar2_K (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch)
    (hK : KOrdNatural) (hSO : KSchurO6p) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    IsL2Square (Bar2 (K c)) (CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV hA h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, -, -, -, -, hΩ6, -, -⟩
  have hKstar : IsL2Square (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) :=
    bar2_congr (P := fun T _ => IsL2Square T (CFSG.Open.pRank 2 D.Z)) hEq (hΩ6 hline)
  have hkerφ : IsPGroup 2 (c.phiL hV).ker := by
    rw [(phiL_ker_eq_pCore_and_map_Hinf_eq c hV hA h4 hK hSO h1930 h3 hnat hline).1]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hker : IsPGroup 2 (phiK c hV).ker := by
    rw [phiK, MonoidHom.ker_rangeRestrict, ← MonoidHom.comap_ker]
    exact hkerφ.comap_of_injective (Subgroup.inclusion (K_le_L c))
      (Subgroup.inclusion_injective (K_le_L c))
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
    (p := 2) (phiK c hV) (MonoidHom.rangeRestrict_surjective _) hker
  exact IsL2Square.of_mulEquiv e.symm hKstar

theorem three_dvd_card_K (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hA : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch)
    (hK : KOrdNatural) (hSO : KSchurO6p) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    3 ∣ Nat.card ↥(K c) := by
  have hsq := isL2Square_bar2_K D Ch c hV hA hd h4 hK hSO h1930 h3 hnat hline
  have hcardBar := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2Square_eq hsq
  have h3bar : 3 ∣ Nat.card (Bar2 (K c)) := by
    rw [hcardBar]
    have h3 := three_dvd_two_pow_two_mul_sub_one (CFSG.Open.pRank 2 D.Z)
    have h9 : 3 ∣ (2 ^ (2 * CFSG.Open.pRank 2 D.Z) - 1) ^ 2 := by
      obtain ⟨k, hk⟩ := h3
      exact ⟨3 * k ^ 2, by rw [hk]; ring⟩
    exact dvd_mul_of_dvd_right h9 _
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pCore 2 ↥(K c))
  rw [hcard]
  exact dvd_mul_of_dvd_left h3bar _

private theorem pCoreOf_le_normalizer_K {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.normalizer (K c : Set G) := by
  have hO2_le_T : CFSG.Open.pCoreOf 2 D.M ≤ D.T := by
    obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
    have hpcS : CFSG.pCore 2 ↥D.M ≤ (S : Subgroup ↥D.M) :=
      CFSG.pCore_isPGroup.le_sylow_of_normal S
    rw [hS] at hpcS
    exact Subgroup.map_le_iff_le_comap.2 hpcS
  have hO2_le_NL : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer (c.L : Set G) := hO2_le_T.trans c.hL.1.1
  have hO2_le_M : CFSG.Open.pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hQ_le_NM : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer (D.M : Set G) := fun x hx => Subgroup.le_normalizer (hO2_le_M hx)
  have hQ_le_NML : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer ((D.M ⊓ c.L : Subgroup G) : Set G) :=
    (le_inf hQ_le_NM hO2_le_NL).trans Subgroup.inf_normalizer_le_normalizer_inf
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hMLmap : (D.M ⊓ c.L).map (MulAut.conj q).toMonoidHom = D.M ⊓ c.L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ_le_NML hq)
  calc (Hinf (D.M ⊓ c.L)).map (MulAut.conj q).toMonoidHom
      = Hinf ((D.M ⊓ c.L).map (MulAut.conj q).toMonoidHom) := Hinf_map _ _
    _ = Hinf (D.M ⊓ c.L) := by rw [hMLmap]

private theorem one_le_pRank_three_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2 X n) : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have h3 : 3 ∣ Nat.card X := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2 h]
    exact dvd_mul_of_dvd_right (three_dvd_two_pow_two_mul_sub_one n) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  exact CFSG.Quasithin.A3Facts.one_le_pRank_of_orderOf Nat.prime_three hx

private theorem pRank_three_K_eq_two (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hsq : IsL2Square (Bar2 (K c)) n) :
    CFSG.pRank 3 ↥(K c) = 2 := by
  classical
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hsq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (A × B) := Finite.of_equiv (Bar2 (K c)) e.toEquiv
  haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
    (fun a b h => by simpa using h)
  haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
    (fun a b h => by simpa using h)
  have hA1 : CFSG.Open.pRank 3 (⊤ : Subgroup A) = 1 :=
    le_antisymm (pRank_le_one_of_isL2_or_isSz (Or.inl hA) Nat.prime_three (by norm_num))
      (one_le_pRank_three_of_isL2 hA)
  have hB1 : CFSG.Open.pRank 3 (⊤ : Subgroup B) = 1 :=
    le_antisymm (pRank_le_one_of_isL2_or_isSz (Or.inl hB) Nat.prime_three (by norm_num))
      (one_le_pRank_three_of_isL2 hB)
  have hAB : CFSG.Open.pRank 3 (⊤ : Subgroup (A × B)) = 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (A × B)]
    rw [CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_three,
      CFSG.SectionRank.pRank_eq_open_pRank_top 3 A,
      CFSG.SectionRank.pRank_eq_open_pRank_top 3 B, hA1, hB1]
  have hbar : CFSG.pRank 3 (Bar2 (K c)) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Bar2 (K c))]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact hAB
  have hpc : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥(K c)) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(K c))) Nat.prime_three (by norm_num)
  calc CFSG.pRank 3 ↥(K c) = CFSG.pRank 3 (Bar2 (K c)) :=
        (CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
          Nat.prime_three (CFSG.pCore 2 ↥(K c)) hpc).symm
    _ = 2 := hbar

private theorem isMulCommutative_of_le_K (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {n : ℕ} (hsq : IsL2Square (Bar2 (K c)) n)
    {R : Subgroup G} (hRK : R ≤ K c) (hRp : IsPGroup 3 ↥R) :
    IsMulCommutative ↥R := by
  classical
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hsq
  haveI : Finite (A × B) := Finite.of_equiv (Bar2 (K c)) e.toEquiv
  haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
    (fun a b h => by simpa using h)
  haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
    (fun a b h => by simpa using h)
  let q : ↥(K c) →* Bar2 (K c) := QuotientGroup.mk' (CFSG.pCore 2 ↥(K c))
  let φ : ↥(K c) →* A × B := e.toMonoidHom.comp q
  have hφker : φ.ker = CFSG.pCore 2 ↥(K c) := by
    ext x
    constructor
    · intro hx
      have hx' : q x = 1 := e.injective (by simpa [φ, MonoidHom.mem_ker] using hx)
      simpa [q] using (QuotientGroup.eq_one_iff x).mp hx'
    · intro hx
      simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply]
      rw [show q x = 1 by simpa [q] using (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  let Rk : Subgroup ↥(K c) := R.subgroupOf (K c)
  have hRkp : IsPGroup 3 ↥Rk := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  have hdisj : Disjoint Rk φ.ker := by
    rw [hφker]
    exact IsPGroup.disjoint_of_ne 3 2 (by norm_num) Rk (CFSG.pCore 2 ↥(K c)) hRkp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(K c)))
  have hcomm : IsMulCommutative ↥Rk :=
    CFSG.GroupTheory.isMulCommutative_of_isPGroup_of_le_prod Nat.prime_three (by norm_num)
      (pRank_le_one_of_isL2_or_isSz (Or.inl hA) Nat.prime_three (by norm_num))
      (pRank_le_one_of_isL2_or_isSz (Or.inl hB) Nat.prime_three (by norm_num))
      φ hRkp hdisj
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hRK) hcomm

private theorem pRank_three_sylow_eq_two (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {n : ℕ} (hsq : IsL2Square (Bar2 (K c)) n)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (K c)) :
    CFSG.pRank 3 ↥R = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK2 := pRank_three_K_eq_two D Ch c hV hsq
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  have h1 : CFSG.pRank 3 (R.subgroupOf (K c)) = CFSG.pRank 3 ↥(K c) := by
    rw [← hQ]
    exact (CFSG.SectionRank.pRank_sylow Q).2
  have h2 : CFSG.pRank 3 (R.subgroupOf (K c)) = CFSG.pRank 3 ↥R := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
      (Subgroup.subgroupOfEquivOfLe hR.le)
  rw [← h2, h1, hK2]

private theorem card_omega_one_sylow_eq_nine (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {n : ℕ} (hsq : IsL2Square (Bar2 (K c)) n)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (K c)) (hRcomm : IsMulCommutative ↥R) :
    Nat.card (omega₁ ↥R (p := 3)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.GroupTheory.card_omega₁_eq_pow_pRank_of_isMulCommutative (X := ↥R) (p := 3),
    pRank_three_sylow_eq_two D Ch c hV hsq hR]
  norm_num

private theorem le_normalizer_omega_one_sylow {R B : Subgroup G}
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    B ≤ Subgroup.normalizer
      (((omega₁ ↥R (p := 3)).map R.subtype : Subgroup G) : Set G) := by
  set S : Set G := {x : G | x ∈ R ∧ x ^ 3 = 1} with hS
  let E : Subgroup G := (omega₁ ↥R (p := 3)).map R.subtype
  have hEeq : E = Subgroup.closure S := by
    change (omega₁ ↥R (p := 3)).map R.subtype = Subgroup.closure S
    rw [CFSG.omega₁, CFSG.omega, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg (Subtype.val) hy⟩
    · rintro ⟨hxR, hx3⟩
      exact ⟨⟨x, hxR⟩, by simpa using hx3, rfl⟩
  have hmem : ∀ {c : G}, c ∈ Subgroup.normalizer (R : Set G) → ∀ {x : G}, x ∈ S →
      c * x * c⁻¹ ∈ S := by
    intro c hc x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hc x).mp hx.1, ?_⟩
    calc (c * x * c⁻¹) ^ 3 = c * x ^ 3 * c⁻¹ := by rw [← conj_pow]
      _ = 1 := by rw [hx.2]; group
  intro b hb
  change b ∈ Subgroup.normalizer (E : Set G)
  rw [hEeq, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  have hset : (fun x : G => b * x * b⁻¹) '' S = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmem (hBR hb) hx
    · intro hy
      refine ⟨b⁻¹ * y * b, ?_, by group⟩
      simpa [inv_inv] using
        hmem ((Subgroup.normalizer (R : Set G)).inv_mem (hBR hb)) hy
  change Subgroup.closure ((fun x : G => b * x * b⁻¹) '' S) = Subgroup.closure S
  rw [hset]

theorem exists_elemAbelian_nine_normalized_of_isSylowOf (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hsq : IsL2Square (Bar2 (K c)) n) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (K c)) (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    ∃ E : Subgroup G, E = (omega₁ ↥R (p := 3)).map R.subtype ∧ E ≤ R ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      B ≤ Subgroup.normalizer (E : Set G) := by
  have hRle : R ≤ K c := hR.le
  have hcomm := isMulCommutative_of_le_K D Ch c hV hsq hRle hR.isPGroup
  refine ⟨(omega₁ ↥R (p := 3)).map R.subtype, rfl, Subgroup.map_subtype_le _,
    ?_, ?_, le_normalizer_omega_one_sylow hBR⟩
  · have hEl : IsElementaryAbelian 3 (omega₁ ↥R (p := 3)) :=
      CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative ↥R
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.subgroup_map hEl R.subtype)
  · rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact card_omega_one_sylow_eq_nine D Ch c hV hsq hR hcomm

private theorem mem_omega_one_of_order_three {R : Subgroup G} (hRcomm : IsMulCommutative ↥R)
    {x : G} (hxR : x ∈ R) (hxord : orderOf x = 3) :
    x ∈ (omega₁ ↥R (p := 3)).map R.subtype := by
  have hcomm : ∀ a b : ↥R, a * b = b * a := fun a b => hRcomm.is_comm.comm a b
  have h3 : (⟨x, hxR⟩ : ↥R) ^ 3 = 1 := by
    apply Subtype.ext
    show x ^ 3 = 1
    rw [← hxord, pow_orderOf_eq_one]
  exact Subgroup.mem_map_of_mem R.subtype ((CFSG.mem_omega₁_iff_of_comm hcomm).2 h3)

private theorem normalizer_sup_of_mem_calC (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h8 : S23_8 D Ch) (h1930 : H1930 D)
    {X₁ X₂ : Subgroup G} (hX₁ : X₁ ∈ calC D.M) (hX₂ : X₂ ∈ calC D.M) :
    D.M ≤ Subgroup.normalizer (X₁ ⊔ X₂ : Subgroup G) := by
  have hX₁M : X₁ ≤ D.M := hX₁.1.le
  have hX₂M : X₂ ≤ D.M := hX₂.1.le
  have hJM : X₁ ⊔ X₂ ≤ D.M := sup_le hX₁M hX₂M
  have hJN : ((X₁ ⊔ X₂).subgroupOf D.M).Normal := by
    haveI h1 : (X₁.subgroupOf D.M).Normal := (h8 h1930 c X₁ hX₁).1
    haveI h2 : (X₂.subgroupOf D.M).Normal := (h8 h1930 c X₂ hX₂).1
    rw [Subgroup.subgroupOf_sup hX₁M hX₂M]
    exact Subgroup.sup_normal (X₁.subgroupOf D.M) (X₂.subgroupOf D.M)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hJN

private theorem commutator_sup_eq_self_of_mem_calC {D : Data G} {X₁ X₂ : Subgroup G}
    (hX₁ : X₁ ∈ calC D.M) (hX₂ : X₂ ∈ calC D.M) :
    ⁅X₁ ⊔ X₂, X₁ ⊔ X₂⁆ = X₁ ⊔ X₂ := by
  apply le_antisymm
  · simpa using Subgroup.commutator_le_sup (X₁ ⊔ X₂) (X₁ ⊔ X₂)
  · refine sup_le ?_ ?_
    · have h := Subgroup.commutator_mono (le_sup_left : X₁ ≤ X₁ ⊔ X₂)
        (le_sup_left : X₁ ≤ X₁ ⊔ X₂)
      rwa [hX₁.2.1] at h
    · have h := Subgroup.commutator_mono (le_sup_right : X₂ ≤ X₁ ⊔ X₂)
        (le_sup_right : X₂ ≤ X₁ ⊔ X₂)
      rwa [hX₂.2.1] at h

private theorem K_eq_sup_of_barImage_eq_sup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {X₁ X₂ : Subgroup G}
    (hX₁ : X₁ ∈ calC D.M) (hX₂ : X₂ ∈ calC D.M)
    (hJnorm : D.M ≤ Subgroup.normalizer (X₁ ⊔ X₂ : Subgroup G))
    (hprod : barImage D.M (K c) = barImage D.M X₁ ⊔ barImage D.M X₂) :
    K c = X₁ ⊔ X₂ := by
  let J : Subgroup G := X₁ ⊔ X₂
  have hX₁M : X₁ ≤ D.M := hX₁.1.le
  have hX₂M : X₂ ≤ D.M := hX₂.1.le
  have hJM : J ≤ D.M := sup_le hX₁M hX₂M
  have hSJ : CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.map_subtype_le _).trans hJnorm
  have hbarJ : barImage D.M J = barImage D.M X₁ ⊔ barImage D.M X₂ := by
    rw [show J = X₁ ⊔ X₂ from rfl, barImage, barImage, barImage,
      Subgroup.subgroupOf_sup hX₁M hX₂M, Subgroup.map_sup]
  have hJperf : ⁅J, J⁆ = J := commutator_sup_eq_self_of_mem_calC hX₁ hX₂
  have hKle : K c ≤ J := by
    have hKS : K c ≤ J ⊔ CFSG.Open.pCoreOf 2 D.M :=
      CFSG.Quasithin.C1Pack.le_sup_pCoreOf_of_barImage_le (K_le_M c)
        (le_of_eq (hprod.trans hbarJ.symm))
    have hpc := CFSG.Quasithin.RonanE111.perfectCore_le_of_le_sup_two
      (J := J) (S := CFSG.Open.pCoreOf 2 D.M) (P := K c) hSJ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D.M) hKS
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect (H := K c)
      c.Hinf_inf_L_perfect] at hpc
    exact hpc
  have hJle : J ≤ K c := by
    have hJK : J ≤ K c ⊔ CFSG.Open.pCoreOf 2 D.M :=
      CFSG.Quasithin.C1Pack.le_sup_pCoreOf_of_barImage_le hJM
        (le_of_eq (hbarJ.trans hprod.symm))
    have hpc := CFSG.Quasithin.RonanE111.perfectCore_le_of_le_sup_two
      (J := K c) (S := CFSG.Open.pCoreOf 2 D.M) (P := J) (pCoreOf_le_normalizer_K c)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D.M) hJK
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect (H := J) hJperf] at hpc
    exact hpc
  exact le_antisymm hKle hJle

private theorem M_le_normalizer_K_of_barImage_sup (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (h8 : S23_8 D Ch) (h1930 : H1930 D)
    {X₁ X₂ : Subgroup G} (hX₁ : X₁ ∈ calC D.M) (hX₂ : X₂ ∈ calC D.M)
    (hprod : barImage D.M (K c) = barImage D.M X₁ ⊔ barImage D.M X₂) :
    D.M ≤ Subgroup.normalizer (K c : Set G) := by
  have hJnorm := normalizer_sup_of_mem_calC D Ch c h8 h1930 hX₁ hX₂
  have hKJ := K_eq_sup_of_barImage_eq_sup c hX₁ hX₂ hJnorm hprod
  simpa only [hKJ] using hJnorm

private theorem M_le_normalizer_K_of_mem_calC (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (h8 : S23_8 D Ch) (h1930 : H1930 D)
    (hcal : K c ∈ calC D.M) : D.M ≤ Subgroup.normalizer (K c : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (K_le_M c)).mp (h8 h1930 c (K c) hcal).1

theorem M_le_normalizer_K_of_B23Omega (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h8 : S23_8 D Ch) (hΩ : S23_9_B23Omega D Ch)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    K c ≠ ⊥ → D.M ≤ Subgroup.normalizer (K c : Set G) := by
  intro hne
  have hOmega := hΩ h1930 c h3 hV (by simpa only [Ctx23L.H] using hline.1)
    (by simpa only [Ctx23L.H] using hline.2)
  rcases hOmega with hbot | hcal | ⟨X₁, X₂, hX₁, hX₂, hne12, hprod⟩
  · exact absurd hbot hne
  · exact M_le_normalizer_K_of_mem_calC D Ch c h8 h1930 hcal
  · exact M_le_normalizer_K_of_barImage_sup D Ch c h8 h1930 hX₁ hX₂ hprod

private theorem exists_prime_normalizer_le_M_of_dvd_card_K
    (D : Data G) (Ch : Choice2011 G) (h6 : S23_6 D Ch) (hσ : UC6S846.SigmaStd D)
    {c : Ctx23L D Ch} (h1930 : H1930 D)
    (hcase : ∃ p ∈ D.sig, p ∣ Nat.card ↥(K c)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(K c) ∧
      ∀ x ∈ K c, orderOf x = p →
        Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := by
  obtain ⟨p, hpσ, hpdvd⟩ := hcase
  have hp := (D.sig_prime p hpσ).1
  have hp2 := (D.sig_prime p hpσ).2
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hsp : IsStronglyPEmbedded p D.M :=
    hσ.sig1_sp p (by rw [← h6 h1930 c]; exact hpσ)
  refine ⟨p, hp, hp2, hpdvd, ?_⟩
  intro x hxK hxord
  have hxne : x ≠ 1 := by
    intro hx1
    rw [hx1, orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  have hxp : x ^ p = 1 := by rw [← hxord, pow_orderOf_eq_one]
  have hUp : IsPGroup p (Subgroup.zpowers x) :=
    CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one hxp
  refine hsp.normalizer_le (Subgroup.zpowers_ne_bot.mpr hxne) hUp ?_
  exact (Subgroup.zpowers_le.mpr hxK).trans (K_le_M c)

private theorem exists_isSylowOf_three_normalized_of_not_dvd_card_K
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hΩ : S23_9_B23Omega D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))
    {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig) (hpdvd : ¬ p ∣ Nat.card ↥(K c))
    (hKne : K c ≠ ⊥) :
    ∃ (B R : Subgroup G), B ≤ D.M ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 3 R (K c) ∧ B ≤ Subgroup.normalizer (R : Set G) := by
  have hNK : D.M ≤ Subgroup.normalizer (K c : Set G) :=
    M_le_normalizer_K_of_B23Omega D Ch c hV h8 hΩ h1930 h3 hline hKne
  obtain ⟨B, hBM, hBel, hBcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hp
      (H := D.M) (k := 2) (D.sig_rank p hpσ)
  have hBp : IsPGroup p B := CFSG.Open.IsElemAbelian.isPGroup hBel
  have hBNK : B ≤ Subgroup.normalizer (K c : Set G) := fun b hb => hNK (hBM hb)
  obtain ⟨R, hRsyl, hBR⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime hp Nat.prime_three hBp hBNK hpdvd
  exact ⟨B, R, hBM, hBel, hBcard, hRsyl, hBR⟩

private theorem pRank_eq_two_of_isElemAbelian {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2) :
    CFSG.Open.pRank p B = 2 := by
  have hc := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hBel
  exact Nat.pow_right_injective hp.one_lt (hc.symm.trans hBcard)

private theorem le_centralizer_of_card_nine_of_isPGroup_sig {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {B E : Subgroup G} (hBp : IsPGroup p B)
    (hEcard : Nat.card E = 9) (hBNE : B ≤ Subgroup.normalizer (E : Set G)) :
    B ≤ Subgroup.centralizer (E : Set G) := by
  have hp6 : Nat.Coprime p 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hdvd' : p ∣ 2 * 3 := by simpa using hdvd
    rcases ((Nat.Prime.dvd_mul hp).mp hdvd') with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  exact CFSG.GroupTheory.le_centralizer_of_card_nine_of_isPGroup hp hp6 hBp hEcard hBNE

private theorem pos_pRank_inf_centralizer_of_isElemAbelian (D : Data G) {p : ℕ} (hp : p.Prime)
    {B E : Subgroup G} (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBM : B ≤ D.M) (hBCE : B ≤ Subgroup.centralizer (E : Set G)) :
    0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
  have hle : B ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := le_inf hBM hBCE
  have h2 := CFSG.SectionRank.pRank_mono hp.one_lt hle
  rw [pRank_eq_two_of_isElemAbelian hp hBel hBcard] at h2
  omega

private theorem one_lt_pRank_inf_normalizer_of_isElemAbelian (D : Data G) {p : ℕ} (hp : p.Prime)
    {B E X : Subgroup G} (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBM : B ≤ D.M) (hBCE : B ≤ Subgroup.centralizer (E : Set G)) (hXE : X ≤ E) :
    1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
  have hBX : B ≤ Subgroup.normalizer (X : Set G) :=
    hBCE.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXE)).trans
      (Subgroup.centralizer_le_normalizer (X : Set G)))
  have hle : B ≤ D.M ⊓ Subgroup.normalizer (X : Set G) := le_inf hBM hBX
  have h2 := CFSG.SectionRank.pRank_mono hp.one_lt hle
  rw [pRank_eq_two_of_isElemAbelian hp hBel hBcard] at h2
  omega

private theorem exists_conj_normalizer_le_gamma_of_mem_K
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {n : ℕ} (hsq : IsL2Square (Bar2 (K c)) n) {R E : Subgroup G}
    (hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 R (K c))
    (hEeq : E = (omega₁ ↥R (p := 3)).map R.subtype)
    {x : G} (hxK : x ∈ K c) (hxord : orderOf x = 3) :
    ∃ (k e : G), k ∈ K c ∧ k⁻¹ * x * k = e ∧
      Subgroup.normalizer (Subgroup.zpowers e : Set G) ≤ rankThreeGamma 1 3 E := by
  have hRcomm := isMulCommutative_of_le_K D Ch c hV hsq hRsyl.le hRsyl.isPGroup
  have hQp : IsPGroup 3 (Subgroup.zpowers x) :=
    CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one
      (by rw [← hxord, pow_orderOf_eq_one])
  obtain ⟨k, hkK, hkQ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf hRsyl
      (Subgroup.zpowers_le.mpr hxK) hQp
  let e : G := k⁻¹ * x * k
  have heR : e ∈ R := hkQ x (Subgroup.mem_zpowers x)
  have heord : orderOf e = 3 := by
    have hconj : e = MulAut.conj k⁻¹ x := by simp [e, MulAut.conj_apply]
    rw [hconj, MulEquiv.orderOf_eq, hxord]
  have heE : e ∈ E := by
    rw [hEeq]
    exact mem_omega_one_of_order_three hRcomm heR heord
  have hAel : IsElemAbelian 3 (Subgroup.zpowers e) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← heord, pow_orderOf_eq_one])
  have hAcard : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, heord]
  exact ⟨k, e, hkK, rfl,
    CFSG.LocalAnalysis.UniquenessCase.UC6S898.normalizer_le_gamma
      (Subgroup.zpowers_le.mpr heE) Nat.prime_three hAel hAcard⟩

private theorem normalizer_zpowers_le_of_mem_K_of_orderOf_eq_three
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {n : ℕ} (hsq : IsL2Square (Bar2 (K c)) n) {R E : Subgroup G}
    (hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 R (K c))
    (hEeq : E = (omega₁ ↥R (p := 3)).map R.subtype)
    (hGamma : rankThreeGamma 1 3 E ≤ D.M)
    {x : G} (hxK : x ∈ K c) (hxord : orderOf x = 3) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := by
  obtain ⟨k, e, hkK, hkeq, hAgamma⟩ :=
    exists_conj_normalizer_le_gamma_of_mem_K D Ch c hV hsq hRsyl hEeq hxK hxord
  have hke : (MulAut.conj k⁻¹).toMonoidHom x = e := by
    simpa [MulAut.conj_apply, inv_inv] using hkeq
  have hNmap : (Subgroup.normalizer (Subgroup.zpowers x : Set G)).map
        (MulAut.conj k⁻¹).toMonoidHom =
      Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq _ (MulAut.conj k⁻¹), MonoidHom.map_zpowers, hke]
  intro g hg
  have hg' : (MulAut.conj k⁻¹) g ∈
      Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    have hmem : (MulAut.conj k⁻¹) g ∈
        (Subgroup.normalizer (Subgroup.zpowers x : Set G)).map
          (MulAut.conj k⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hg
    rwa [hNmap] at hmem
  have hgM : k⁻¹ * g * k ∈ D.M := by
    simpa [MulAut.conj_apply, inv_inv] using hGamma (hAgamma hg')
  have hkM : k ∈ D.M := K_le_M c hkK
  have hmem : k * (k⁻¹ * g * k) * k⁻¹ ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem hkM hgM) (D.M.inv_mem hkM)
  simpa [mul_assoc] using hmem

private theorem exists_prime_normalizer_data_of_not_dvd_card_K
    (D : Data G) (Ch : Choice2011 G) (h8 : S23_8 D Ch)
    (hΩ : S23_9_B23Omega D Ch) (hσ : UC6S846.SigmaStd D)
    {c : Ctx23L D Ch} (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hV : IsElemAbelian 2 c.V)
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))
    (hcase : ¬ ∃ p ∈ D.sig, p ∣ Nat.card ↥(K c))
    (hsq : IsL2Square (Bar2 (K c)) (CFSG.Open.pRank 2 D.Z))
    (h3K : 3 ∣ Nat.card ↥(K c)) :
    ∃ (p : ℕ) (B R E : Subgroup G), p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ∈ D.sig ∧
      B ≤ D.M ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 3 R (K c) ∧
      E = (omega₁ ↥R (p := 3)).map R.subtype ∧
      E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      B ≤ Subgroup.centralizer (E : Set G) := by
  obtain ⟨p, hpσ⟩ := hσ.nonempty
  have hp := (D.sig_prime p hpσ).1
  have hp2 := (D.sig_prime p hpσ).2
  have hpdvd : ¬ p ∣ Nat.card ↥(K c) := fun hdvd => hcase ⟨p, hpσ, hdvd⟩
  have hp3 : p ≠ 3 := fun hp3' => hpdvd (hp3' ▸ h3K)
  have hKne : K c ≠ ⊥ := by
    intro hbot
    rw [hbot] at h3K
    simpa using h3K
  obtain ⟨B, R, hBM, hBel, hBcard, hRsyl, hBR⟩ :=
    exists_isSylowOf_three_normalized_of_not_dvd_card_K D Ch c hV h8 hΩ h1930 h3 hline
      hp hpσ hpdvd hKne
  obtain ⟨E, hEeq, hER, hEel, hEcard, hBNE⟩ :=
    exists_elemAbelian_nine_normalized_of_isSylowOf D Ch c hV hsq hRsyl hBR
  have hBCE : B ≤ Subgroup.centralizer (E : Set G) :=
    le_centralizer_of_card_nine_of_isPGroup_sig hp hp2 hp3
      (CFSG.Open.IsElemAbelian.isPGroup hBel) hEcard hBNE
  exact ⟨p, B, R, E, hp, hp2, hp3, hpσ, hBM, hBel, hBcard, hRsyl, hEeq, hER, hEel,
    hEcard, hBCE⟩

private theorem exists_three_normalizer_le_M_of_not_dvd_card_K
    (D : Data G) (Ch : Choice2011 G) (h6 : S23_6 D Ch) (h8 : S23_8 D Ch)
    (hΩ : S23_9_B23Omega D Ch) (hσ : UC6S846.SigmaStd D) (h76 : F07.R76Sig D)
    {c : Ctx23L D Ch} (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hV : IsElemAbelian 2 c.V)
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))
    (hcase : ¬ ∃ p ∈ D.sig, p ∣ Nat.card ↥(K c))
    (hsq : IsL2Square (Bar2 (K c)) (CFSG.Open.pRank 2 D.Z))
    (h3K : 3 ∣ Nat.card ↥(K c)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(K c) ∧
      ∀ x ∈ K c, orderOf x = p →
        Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := by
  obtain ⟨p, B, R, E, hp, hp2, hp3, hpσ, hBM, hBel, hBcard, hRsyl, hEeq, hER, hEel,
    hEcard, hBCE⟩ :=
    exists_prime_normalizer_data_of_not_dvd_card_K D Ch h8 hΩ hσ h1930 h3 hV hline
      hcase hsq h3K
  have hsp : IsStronglyPEmbedded p D.M :=
    hσ.sig1_sp p (by rw [← h6 h1930 c]; exact hpσ)
  have hGamma : rankThreeGamma 1 3 E ≤ D.M :=
    h76 p hpσ hp2 hsp 3 Nat.prime_three E (hER.trans (hRsyl.le.trans (K_le_M c)))
      hEel (by simpa using hEcard)
      (pos_pRank_inf_centralizer_of_isElemAbelian D hp hBel hBcard hBM hBCE)
      (fun X hXE _ =>
        one_lt_pRank_inf_normalizer_of_isElemAbelian D hp hBel hBcard hBM hBCE hXE)
  exact ⟨3, Nat.prime_three, by norm_num, by simpa only [K] using h3K,
    fun x hxK hxord =>
      normalizer_zpowers_le_of_mem_K_of_orderOf_eq_three D Ch c hV hsq hRsyl hEeq hGamma
        hxK hxord⟩

theorem s23_9_C2Emb_of (D : Data G) (Ch : Choice2011 G)
    (hA : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (hK : KOrdNatural)
    (hSO : KSchurO6p) (h6 : S23_6 D Ch) (h8 : S23_8 D Ch)
    (hΩ : S23_9_B23Omega D Ch) (hσ : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) :
    S23_9_C2Emb D Ch := by
  intro h1930 c h3 hV
  dsimp only
  intro hline
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) := by
    rcases hline with ⟨hPlus, hNatPlus⟩
    exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inl ⟨hPlus, hNatPlus⟩
  have hlineH : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z) := by
    simpa only [Ctx23L.H] using hline
  have hsq : IsL2Square (Bar2 (K c)) (CFSG.Open.pRank 2 D.Z) :=
    isL2Square_bar2_K D Ch c hV hA hd h4 hK hSO h1930 h3 hnat hlineH
  have h3K : 3 ∣ Nat.card ↥(K c) :=
    three_dvd_card_K D Ch c hV hA hd h4 hK hSO h1930 h3 hnat hlineH
  by_cases hcase : ∃ p ∈ D.sig, p ∣ Nat.card ↥(K c)
  · obtain ⟨p, hp, hp2, hpdvd, hx⟩ :=
      exists_prime_normalizer_le_M_of_dvd_card_K D Ch h6 hσ h1930 hcase
    exact ⟨p, hp, hp2, by simpa only [K] using hpdvd,
      fun x hxK hxord => hx x (by simpa only [K] using hxK) hxord⟩
  · obtain ⟨p, hp, hp2, hpdvd, hx⟩ :=
      exists_three_normalizer_le_M_of_not_dvd_card_K D Ch h6 h8 hΩ hσ h76 h1930 h3 hV
        hlineH hcase hsq h3K
    exact ⟨p, hp, hp2, by simpa only [K] using hpdvd,
      fun x hxK hxord => hx x (by simpa only [K] using hxK) hxord⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end