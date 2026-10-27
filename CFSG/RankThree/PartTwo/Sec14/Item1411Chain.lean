module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.FusionDefs
public import CFSG.RankThree.PartTwo.Sec14.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Statements

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G)

abbrev xA : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))

@[expose] def TransOn (V Y : Subgroup G) : Prop :=
  ∀ S ∈ scriptQPiStar A LB Y (piOf 2), ∀ T ∈ scriptQPiStar A LB Y (piOf 2),
    IsConjIn (V ⊓ Y) S T

@[expose] def Item1411_1 : Prop :=
  TransOn A LB (Subgroup.normalizer (A : Set G)) ⊤

@[expose] def Item1411_2 : Prop :=
  (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
      TransOn A LB (xA A) (Subgroup.centralizer ({a} : Set G))) →
    TransOn A LB (xA A) ⊤

@[expose] def Item1411_3 : Prop :=
  ¬ TransOn A LB (xA A) ⊤ →
    ∃ Y : Subgroup G, Y = delta A LB Y ∧ Y ∈ scriptY A ∧ CFSG.Open.pCoreOf 2 Y ≠ ⊥ ∧
      inSubgroup perfectResidual Y ≠ ⊥ ∧ ¬ TransOn A LB (xA A) Y

@[expose] def Fail1411 : Prop :=
  ¬ TransOn A LB (xA A) ⊤ ∧
    ∀ Y : Subgroup G, Y = delta A LB Y → Y ∈ scriptY A → CFSG.Open.pCoreOf 2 Y ≠ ⊥ →
      inSubgroup perfectResidual Y ≠ ⊥ → TransOn A LB (xA A) Y

@[expose] def gammaA : Set (Subgroup G) :=
  {F | F ∈ omegaA A ∧ ¬ TransOn A LB (xA A) (Subgroup.normalizer (F : Set G))}

@[expose] def Claim1411Local : Prop :=
  (∀ Y ∈ scriptY A, TransOn A LB (Subgroup.normalizer (A : Set G)) Y) ∧
    ((∀ a : G, Subgroup.zpowers a ∈ omegaA A →
        TransOn A LB (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y ∈ scriptY A, TransOn A LB (xA A) Y)

@[expose] def Item148Solvable : Prop :=
  ∀ Y ∈ scriptY A, Group.IsSolvable ↥Y → deltaZero A LB Y ≤ pPrimeCoreOf 3 Y

end Statements

section Local

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem le_centralizer_of_le_normalizer_zpowers (hA : IsE27 A) {c : G} (hcA : c ∈ A)
    {Q : Subgroup G} (hQ : Q ∈ scriptQ A LB)
    (hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.2.1
  set y := x * c * x⁻¹ * c⁻¹ with hy
  have hyQ : y ∈ Q := by
    have h1 : c * x⁻¹ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQ.1.2.2 hcA) x⁻¹).mp (inv_mem hx)
    have : y = x * (c * x⁻¹ * c⁻¹) := by rw [hy]; group
    rw [this]
    exact mul_mem hx h1
  have hyc : y ∈ Subgroup.zpowers c := by
    have h1 : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hQN hx) c).mp (Subgroup.mem_zpowers c)
    exact mul_mem h1 (inv_mem (Subgroup.mem_zpowers c))
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyc
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA.1.2 c hcA,
      one_zpow]
  have hy1 : y = 1 := by
    have hdvd : orderOf (⟨y, hyQ⟩ : Q) ∣ Nat.gcd 3 (Nat.card Q) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy3)))
        (orderOf_dvd_natCard _)
    rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3),
      Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact congrArg Subtype.val hdvd
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : x * c * x⁻¹ = c := by
    have h := hy1
    rw [hy, mul_inv_eq_one] at h
    exact h
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [this]

omit [Finite G] in
theorem scriptQPiStar_normalizer_eq (hA : IsE27 A) {c : G} (hcA : c ∈ A)
    (π : Set Nat.Primes) :
    scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) π =
      scriptQPiStar A LB (Subgroup.centralizer ({c} : Set G)) π := by
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
  have h : scriptQPi A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) π =
      scriptQPi A LB (Subgroup.centralizer ({c} : Set G)) π := by
    ext Q
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, le_centralizer_of_le_normalizer_zpowers hA hcA h1 h2⟩, h3⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2.trans hCN⟩, h3⟩⟩
  simp only [scriptQPiStar, h]

omit [Finite G] in
theorem transOn_normalizer_iff (hA : IsE27 A) {c : G} (hcA : c ∈ A) :
    TransOn A LB (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ↔
      TransOn A LB (xA A) (Subgroup.centralizer ({c} : Set G)) := by
  have hXC : xA A ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
  unfold TransOn
  rw [scriptQPiStar_normalizer_eq hA hcA, inf_eq_left.mpr (hXC.trans hCN), inf_eq_left.mpr hXC]

end Local

section Steps

variable {A L : Subgroup G} {c : G}

theorem rank3II_14_11_1_of (h : Sec14Std G A c L) (hC : Claim1411Local A (lB A)) :
    Item1411_1 A (lB A) := by
  intro S hS T hT
  rw [inf_top_eq]
  exact rank3II_14_11_1_lB h (fun Y hY => hC.1 Y hY) hS hT

theorem rank3II_14_11_2_of (h : Sec14Std G A c L) (hC : Claim1411Local A (lB A)) :
    Item1411_2 A (lB A) := by
  intro hloc S hS T hT
  rw [inf_top_eq]
  exact rank3II_14_11_2_lB h (fun Y hY => hC.2 hloc Y hY) hS hT

omit [Finite G] in
theorem rank3II_14_12_nonempty {LB : Subgroup G → Subgroup G} (hA : IsE27 A)
    (h2 : Item1411_2 A LB) (hX : ¬ TransOn A LB (xA A) ⊤) : (gammaA A LB).Nonempty := by
  by_contra hne
  apply hX
  refine h2 fun a ha => ?_
  have haA : a ∈ A := (zpowers_mem_omegaA_iff.mp ha).1
  rw [← transOn_normalizer_iff hA haA]
  by_contra hT
  exact hne ⟨_, ha, hT⟩

omit [Finite G] in
theorem delta_delta {LB : Subgroup G → Subgroup G} (Z : Subgroup G) :
    delta A LB (delta A LB Z) = delta A LB Z :=
  le_antisymm (delta_le _) (sSup_le fun _ hQ => le_delta hQ.1 (le_delta hQ.1 hQ.2))

omit [Finite G] in
theorem scriptQPiStar_delta {LB : Subgroup G → Subgroup G} (Z : Subgroup G)
    (π : Set Nat.Primes) :
    scriptQPiStar A LB (delta A LB Z) π = scriptQPiStar A LB Z π := by
  have h : scriptQPi A LB (delta A LB Z) π = scriptQPi A LB Z π := by
    ext Q
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2.trans (delta_le Z)⟩, h3⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, le_delta h1 h2⟩, h3⟩⟩
  simp only [scriptQPiStar, h]

theorem transOn_of_isSolvable (h : Sec14Std G A c L) (h148s : Item148Solvable A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hYΔ : Y = delta A (lB A) Y) (hY : Y ∈ scriptY A) (hYs : Group.IsSolvable ↥Y) :
    TransOn A (lB A) (xA A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨hdelta, -, -⟩ := rank3II_14_5_lB hA hbot hY.2
  set R := pPrimeCoreOf 3 Y with hR
  set C' := xA A ⊓ Y with hC'
  have hDR : deltaZero A (lB A) Y ≤ R := h148s Y hY hYs
  have hYRC : Y ≤ C' ⊔ R := by
    calc Y = delta A (lB A) Y := hYΔ
      _ = deltaZero A (lB A) Y ⊔ C' := hdelta
      _ ≤ R ⊔ C' := sup_le_sup_right hDR _
      _ = C' ⊔ R := sup_comm _ _
  have hC'R : C' ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    have hdvd := h3.trans ((Subgroup.card_dvd_of_le hYRC).trans (card_sup_dvd_card_mul hC'R))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
        (h1.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y) h1
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3, hY.2⟩
  have hYQ : Y ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hsyl : ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), CFSG.Open.fusionIsSylowIn 2 S Y ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hY3 hY.2 hS.prop.1.2 hS2 hAS
    have hS'mem : S' ∈ scriptQPi A (lB A) Y (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hYQ hS'.1 hAS', hS'.1⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'mem hSS'
    exact ⟨this ▸ hS', hAS⟩
  intro S hS T hT
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hY3 hY.2 hSs hTs hAS hAT
  have hCYA : Y ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hYQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hY.2 (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCYA hx, (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

theorem rank3II_14_15_of (h : Sec14Std G A c L)
    (hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y)
    (hsol : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      Group.IsSolvable ↥Y → TransOn A (lB A) (xA A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T) : S ⊓ T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  refine rank3II_14_15_lB hXA ?_ hS hT hST
  intro U hU hU1 S' hS' T' hT'
  set N := Subgroup.normalizer (U : Set G) with hN
  set Y := delta A (lB A) N with hY
  have hYN : Y ≤ N := delta_le N
  have hYΔ : Y = delta A (lB A) Y := (delta_delta N).symm
  have hYne : Y ≠ ⊤ := fun htop => normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hU1
    (isPGroup_of_mem_scriptQPi Nat.prime_two hU) (top_le_iff.mp (htop ▸ hYN))
  have hYsc : Y ∈ scriptY A := ⟨hYne, le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
  have htrans : TransOn A (lB A) (xA A) Y := by
    by_cases hres : inSubgroup perfectResidual Y = ⊥
    · refine hsol Y hYΔ hYsc ?_
      have h0 : perfectResidual ↥Y = ⊥ := by
        rw [inSubgroup] at hres
        exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hres
      exact (perfect_residual_characterization (G := ↥Y)).2.2.2.2.2.mp h0
    · refine hfail Y hYΔ hYsc ?_ hres
      have hUY : U ≤ Y := le_delta hU.1.1 Subgroup.le_normalizer
      have hUO : U ≤ CFSG.Open.pCoreOf 2 Y :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUY hYN
          (isPGroup_of_mem_scriptQPi Nat.prime_two hU)
      intro hbot
      rw [hbot] at hUO
      exact hU1 (le_bot_iff.mp hUO)
  rw [← scriptQPiStar_delta (A := A) (LB := lB A) N] at hS' hT'
  exact (htrans S' hS' T' hT').mono (inf_le_inf_left _ hYN)

theorem rank3II_14_14_not_isConjIn {LB : Subgroup G → Subgroup G} {Y U₁ U₂ T₁ T₂ : Subgroup G}
    (hU₁ : U₁ ∈ scriptQPiStar A LB Y (piOf 2)) (hU₂ : U₂ ∈ scriptQPiStar A LB Y (piOf 2))
    (hne : U₁ ≠ U₂) (hT₁ : T₁ ∈ scriptQPiStar A LB ⊤ (piOf 2)) (hUT₁ : U₁ ≤ T₁)
    (hUT₂ : U₂ ≤ T₂) (hXU : xA A ≤ Subgroup.normalizer (U₂ : Set G)) :
    ¬ IsConjIn (xA A) T₂ T₁ := by
  rintro ⟨x, hx, rfl⟩
  have hU₂T₁ : U₂ ≤ T₂.map (MulAut.conj x).toMonoidHom := by
    rw [← Late.map_conj_eq_of_mem_normalizer (hXU hx)]
    exact Subgroup.map_mono hUT₂
  have hle : U₁ ⊔ U₂ ≤ T₂.map (MulAut.conj x).toMonoidHom := sup_le hUT₁ hU₂T₁
  have hsup : U₁ ⊔ U₂ ∈ scriptQPi A LB Y (piOf 2) := by
    refine ⟨⟨mem_scriptQ_of_le hT₁.prop.1.1 hle
      (le_normalizer_sup hU₁.prop.1.1.1.2.2 hU₂.prop.1.1.1.2.2),
      sup_le hU₁.prop.1.2 hU₂.prop.1.2⟩, ?_⟩
    exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      ((isPGroup_of_mem_scriptQPi Nat.prime_two hT₁.prop).to_le hle)
  have h1 : U₁ = U₁ ⊔ U₂ := hU₁.eq_of_le hsup le_sup_left
  have h2 : U₂ ≤ U₁ := h1 ▸ le_sup_right
  exact hne (hU₂.eq_of_le hU₁.prop h2).symm

theorem rank3II_14_16_false (h : Sec14Std G A c L)
    (hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y)
    (hsol : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      Group.IsSolvable ↥Y → TransOn A (lB A) (xA A) Y)
    {Y U₁ U₂ : Subgroup G} (hU₁ : U₁ ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hU₂ : U₂ ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hne : U₁ ≠ U₂) (hmeet : U₁ ⊓ U₂ ≠ ⊥)
    (hXU : xA A ≤ Subgroup.normalizer (U₂ : Set G)) : False := by
  have ext : ∀ U ∈ scriptQPiStar A (lB A) Y (piOf 2),
      ∃ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), U ≤ T := by
    intro U hU
    obtain ⟨T, hUT, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)))
      (a := U) ⟨⟨hU.prop.1.1, le_top⟩, hU.prop.2⟩
    exact ⟨T, hT, hUT⟩
  obtain ⟨T₁, hT₁, hUT₁⟩ := ext U₁ hU₁
  obtain ⟨T₂, hT₂, hUT₂⟩ := ext U₂ hU₂
  have hnc := rank3II_14_14_not_isConjIn hU₁ hU₂ hne hT₁ hUT₁ hUT₂ hXU
  have hbot := rank3II_14_15_of h hfail hsol hT₂ hT₁ hnc
  apply hmeet
  rw [eq_bot_iff, ← hbot]
  exact (inf_le_inf hUT₁ hUT₂).trans (inf_comm T₁ T₂).le

theorem rank3II_14_11_3_of_steps {LB : Subgroup G → Subgroup G} (hA : IsE27 A)
    (h2 : Item1411_2 A LB)
    (hset : ∀ c : G, Subgroup.zpowers c ∈ omegaA A → ∃ L' : Subgroup G, L' ∈ lA A c)
    (h1421 : Fail1411 A LB → ∀ c : G, Subgroup.zpowers c ∈ gammaA A LB → ∀ L' ∈ lA A c,
      Nonempty (↥L' ⧸ LocalRank.aschbacherSolvableCore 3 ↥L' ≃*
        CFSG.Blueprint.NativeSporadic.M22))
    (h1422 : Fail1411 A LB → ∀ c : G, Subgroup.zpowers c ∈ gammaA A LB → ∀ L' ∈ lA A c,
      IsEmpty (↥L' ⧸ LocalRank.aschbacherSolvableCore 3 ↥L' ≃*
        CFSG.Blueprint.NativeSporadic.M22)) :
    Item1411_3 A LB := by
  intro hX
  by_contra hno
  have hfail : Fail1411 A LB := ⟨hX, fun Y hYΔ hY hO hres => by
    by_contra hT
    exact hno ⟨Y, hYΔ, hY, hO, hres, hT⟩⟩
  obtain ⟨F, hFΓ⟩ := rank3II_14_12_nonempty hA h2 hX
  obtain ⟨-, -, c, rfl, -⟩ := hFΓ.1
  obtain ⟨L', hL'⟩ := hset c hFΓ.1
  obtain ⟨e⟩ := h1421 hfail c hFΓ L' hL'
  exact (h1422 hfail c hFΓ L' hL').false e

end Steps

end CFSG.RankThree.PartTwo.Sec14
