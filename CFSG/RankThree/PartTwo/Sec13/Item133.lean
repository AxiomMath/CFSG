module

public import CFSG.RankThree.PartTwo.Sec13.Item133Mono
public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.Milestones.AT_alternating_automorphism_permutation
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import Certificates.Certificate8171
public import Certificates.Certificate8172
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
  CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

section Orders

variable {G : Type} [Group G] [Finite G]

theorem exists_order_four_of_equiv {X M : Type*} [Group X] [Group M] {T : Subgroup X}
    (e : T ≃* M) {m : M} (h4 : m ^ 4 = 1) (h2 : m ^ 2 ≠ 1) :
    ∃ τ ∈ T, τ ^ 4 = 1 ∧ τ ^ 2 ≠ 1 := by
  refine ⟨e.symm m, (e.symm m).2, ?_, fun h => h2 ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, h4, map_one, Subgroup.coe_one]
  · have : (e.symm m) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
    rw [← map_pow, MulEquiv.map_eq_one_iff] at this
    exact this

theorem exists_order_three_of_equiv {X M : Type*} [Group X] [Group M] {T : Subgroup X}
    (e : T ≃* M) {m : M} (h3 : m ^ 3 = 1) (h1 : m ≠ 1) :
    ∃ τ ∈ T, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  refine ⟨e.symm m, (e.symm m).2, ?_, fun h => h1 ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
  · have : e.symm m = 1 := Subtype.ext (by rw [h, Subgroup.coe_one])
    rwa [MulEquiv.map_eq_one_iff] at this

theorem exists_order_four_of_cases {X : Type*} [Group X] {T : Subgroup X} {P Q R : Prop}
    (h : (P ∧ (Nonempty (T ≃* QuaternionGroup 2) ∨
        Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
      (Q ∧ Nonempty (T ≃* Multiplicative (ZMod 4))) ∨
      (R ∧ Nonempty (T ≃* QuaternionGroup 2))) :
    ∃ τ ∈ T, τ ^ 4 = 1 ∧ τ ^ 2 ≠ 1 := by
  rcases h with ⟨-, he | he⟩ | ⟨-, he⟩ | ⟨-, he⟩
  · obtain ⟨e⟩ := he
    exact exists_order_four_of_equiv e (m := QuaternionGroup.a 1) (by decide) (by decide)
  · obtain ⟨e⟩ := he
    exact exists_order_four_of_equiv e (m := slI) slI_rel.1 slI_rel.2.2.2
  · obtain ⟨e⟩ := he
    exact exists_order_four_of_equiv e (m := Multiplicative.ofAdd (1 : ZMod 4)) (by decide)
      (by decide)
  · obtain ⟨e⟩ := he
    exact exists_order_four_of_equiv e (m := QuaternionGroup.a 1) (by decide) (by decide)

omit [Finite G] in
theorem normalizerMonoidHom_pow_apply_val {A : Subgroup G} (w : G)
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (n : ℕ) (x : A) :
    (((A.normalizerMonoidHom ⟨w, hw⟩) ^ n) x : G) = w ^ n * x * (w ^ n)⁻¹ := by
  rw [← map_pow]
  have : (⟨w, hw⟩ : Subgroup.normalizer (A : Set G)) ^ n =
      ⟨w ^ n, Subgroup.pow_mem _ hw n⟩ := Subtype.ext (by simp)
  rw [this, normalizerMonoidHom_apply_val]

theorem exists_order_four_restrict {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) {τ : MulAut A} (hτ : τ ∈ Sec4.autIn L A)
    (h4 : τ ^ 4 = 1) (h2 : τ ^ 2 ≠ 1) :
    ∃ ρ ∈ Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L), ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1 := by
  obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  have hlB : l ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf A L ⟨hlL, hlN⟩
  have hfix : ∀ n : ℕ, (A.normalizerMonoidHom ⟨l, hlN⟩) ^ n = 1 →
      ∀ y ∈ A, l ^ n * y * (l ^ n)⁻¹ = y := by
    intro n hn y hy
    have := congrArg (fun σ : MulAut A => ((σ ⟨y, hy⟩ : A) : G)) hn
    simpa [normalizerMonoidHom_pow_apply_val] using this
  refine ⟨(A ⊓ L).normalizerMonoidHom ⟨l, hlB⟩,
    Sec4.mem_autIn_iff.mpr ⟨l, hlB, ⟨hlL, hlN⟩, rfl⟩, ?_, fun h => h2 ?_⟩
  · ext x
    rw [normalizerMonoidHom_pow_apply_val, hfix 4 h4 x x.2.1]
    rfl
  · ext ⟨y, hy⟩
    rw [normalizerMonoidHom_pow_apply_val]
    have hB : ∀ x ∈ A ⊓ L, l ^ 2 * x * (l ^ 2)⁻¹ = x := by
      intro x hx
      have := congrArg (fun σ : MulAut (A ⊓ L : Subgroup G) => ((σ ⟨x, hx⟩ : _) : G)) h
      simp only [MulAut.one_apply] at this
      rw [normalizerMonoidHom_pow_apply_val] at this
      exact this
    have hc : l ^ 2 * c * (l ^ 2)⁻¹ = c := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp
        (hD.le_centralizer (L.pow_mem hlL 2))
      rw [h1, mul_inv_cancel_right]
    obtain ⟨i, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hD.isElemAbelian hD.mem_A hAa hy
    change l ^ 2 * (c ^ i * b) * (l ^ 2)⁻¹ = c ^ i * b
    calc l ^ 2 * (c ^ i * b) * (l ^ 2)⁻¹ =
        (l ^ 2 * c * (l ^ 2)⁻¹) ^ i * (l ^ 2 * b * (l ^ 2)⁻¹) := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow]
      _ = c ^ i * b := by rw [hc, hB b hb]

omit [Finite G] in
theorem autIn_fix {A X : Subgroup G} {a : G} (hX : X ≤ Subgroup.centralizer ({a} : Set G))
    (haA : a ∈ A) {τ : MulAut A} (hτ : τ ∈ Sec4.autIn X A) : τ ⟨a, haA⟩ = ⟨a, haA⟩ := by
  obtain ⟨l, hlN, hlX, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_val]
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hX hlX)
  change l * a * l⁻¹ = a
  rw [h1, mul_inv_cancel_right]

omit [Finite G] in
theorem autIn_mem_inf {A X : Subgroup G} {τ : MulAut A} (hτ : τ ∈ Sec4.autIn X A) {x : A}
    (hx : (x : G) ∈ X) : ((τ x : A) : G) ∈ X := by
  obtain ⟨l, hlN, hlX, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  rw [normalizerMonoidHom_apply_val]
  exact X.mul_mem (X.mul_mem hlX hx) (X.inv_mem hlX)

omit [Finite G] in
theorem not_le_normalizer_of_irreducible {A : Subgroup G}
    (hirrW : Sec21.IsIrreducibleOn (wStar A)) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A)
    (h3 : Nat.card (Subgroup.zpowers a) = 3) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  intro hle
  have hirr' : Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) A) := by
    rw [autIn_normalizer_eq]
    exact hirrW
  rcases eq_bot_or_eq_of_isIrreducibleOn hirr' (Subgroup.zpowers_le.mpr haA) hle with h | h
  · rw [h, Subgroup.card_bot] at h3
    norm_num at h3
  · rw [h, h27] at h3
    norm_num at h3

end Orders

section Omega

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_mem_zpowers {a y : G} (h3 : Nat.card (Subgroup.zpowers a) = 3)
    (hy : y ∈ Subgroup.zpowers a) (hy1 : y ≠ 1) : a ∈ Subgroup.zpowers y := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hy
  have hdvd : Nat.card (Subgroup.zpowers y) ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    apply hy1
    have : Subgroup.zpowers y = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    exact Subgroup.zpowers_eq_bot.mp this
  · have heq : Subgroup.zpowers y = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h, h3])
    rw [heq]
    exact Subgroup.mem_zpowers a

theorem false_of_order_three_mono {A X : Subgroup G} {a : G} (hDa : Sec13Data G A a X)
    (haX : a ∉ X) {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hle : (wStar A).map (KFacts.glHom f) ≤ linePermuting Lstd) {τ : MulAut A}
    (hτ : τ ∈ Sec4.autIn X A) (h3 : τ ^ 3 = 1) (h1 : τ ≠ 1) : False := by
  have hne : Sec4.autIn X A ≠ ⊥ := fun h => h1 (by rw [h] at hτ; exact Subgroup.mem_bot.mp hτ)
  obtain ⟨d, hdA, hdX, hd1⟩ := exists_mem_inf_of_autIn_ne_bot hDa.le_normalizer hne
  set g := KFacts.glHom f τ with hgdef
  have hg : g ∈ linePermuting Lstd := hle ⟨τ, autIn_mono le_top hτ, rfl⟩
  have hg3 : g ^ 3 = 1 := by rw [hgdef, ← map_pow, h3, map_one]
  have hg1 : g ≠ 1 := fun h => h1 (KFacts.glHom_injective f (by rw [← hgdef, h, map_one]))
  have hcv : ∀ y : A, Sec12.coordVec f y = Multiplicative.toAdd (f.symm y) := fun y => rfl
  have hfv : ∀ v : Fin 3 → ZMod 3, Sec12.coordVec f (f (Multiplicative.ofAdd v)) = v := by
    intro v
    simp [Sec12.coordVec]
  set U := KFacts.coordSubspace f ((A ⊓ X).subgroupOf A) with hUdef
  have hU : ∀ u ∈ U, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u ∈ U := by
    intro u hu
    have hu' : (f (Multiplicative.ofAdd u) : G) ∈ A ⊓ X := Subgroup.mem_subgroupOf.mp hu
    have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u =
        Sec12.coordVec f (τ (f (Multiplicative.ofAdd u))) := by
      rw [← hfv u, hgdef, glHom_mulVec_coordVec, hfv]
    change f (Multiplicative.ofAdd _) ∈ (A ⊓ X).subgroupOf A
    rw [h1, hcv, ofAdd_toAdd, MulEquiv.apply_symm_apply, Subgroup.mem_subgroupOf]
    exact ⟨(τ _).2, autIn_mem_inf hτ hu'.2⟩
  have hw : Sec12.coordVec f ⟨d, hdA⟩ ∈ U := by
    change f (Multiplicative.ofAdd _) ∈ (A ⊓ X).subgroupOf A
    rw [hcv, ofAdd_toAdd, MulEquiv.apply_symm_apply, Subgroup.mem_subgroupOf]
    exact ⟨hdA, hdX⟩
  have hw0 : Sec12.coordVec f ⟨d, hdA⟩ ≠ 0 :=
    Sec12.coordVec_ne_zero f (fun h => hd1 (congrArg Subtype.val h))
  obtain ⟨w', hw'U, hw'0, hgw'⟩ := exists_fixed_of_cube hg hg3 hU hw hw0
  set u := Sec12.coordVec f ⟨a, hDa.mem_A⟩ with hudef
  have hu0 : u ≠ 0 := Sec12.coordVec_ne_zero f (fun h => hDa.ne_one (congrArg Subtype.val h))
  have hgu : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u = u := by
    rw [hudef, hgdef, glHom_mulVec_coordVec, autIn_fix hDa.le_centralizer hDa.mem_A hτ]
  have hspan := mem_span_of_order_three hg hg3 hg1 hu0 hgu hgw'
  set y := f (Multiplicative.ofAdd w') with hydef
  have hya : y ∈ Subgroup.zpowers (⟨a, hDa.mem_A⟩ : A) := by
    rw [← KFacts.coordVec_mem_span_iff f, hydef, hfv]
    exact hspan
  have hyX : (y : G) ∈ X :=
    (Subgroup.mem_subgroupOf.mp (show f (Multiplicative.ofAdd w') ∈ (A ⊓ X).subgroupOf A from
      hw'U)).2
  have hy1 : (y : G) ≠ 1 := by
    intro h
    apply hw'0
    have : y = 1 := Subtype.ext h
    rw [← hfv w', ← hydef, this]
    simp [Sec12.coordVec]
  have hyaG : (y : G) ∈ Subgroup.zpowers a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hya
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk]; simp⟩
  exact haX ((Subgroup.zpowers_le.mpr hyX)
    (mem_zpowers_of_mem_zpowers hDa.card_zpowers hyaG hy1))

theorem coord_line_of_mem_omegaA (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hset : Item13SetupAt) (hSLT : NotSLTwoOfHypT) {A L : Subgroup G}
    {c : G} (hD : Sec13Data G A c L) (hST : HypS A ∨ HypT A)
    (hirrW : Sec21.IsIrreducibleOn (wStar A)) {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hle : (wStar A).map (KFacts.glHom f) ≤ linePermuting Lstd) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) (haA : a ∈ A) :
    ∃ j, Sec12.coordVec f ⟨a, haA⟩ ∈ Lstd j := by
  obtain ⟨X, hX⟩ := hset G hD.toPartTwoStanding hD.partTwoS_eq A hD.mem_partTwoF
    hD.not_mem_partTwoT a ha
  have hDa : Sec13Data G A a X :=
    ⟨hD.toPartTwoStanding, hD.partTwoS_eq, hD.mem_partTwoF, hD.not_mem_partTwoT, ha, hX⟩
  have hWa := not_le_normalizer_of_irreducible hirrW hD.card_eq haA hDa.card_zpowers
  have haX : a ∉ X := not_mem_of_hyp h131 hspor hSLC hSLT hDa hST hWa
  have hu0 : Sec12.coordVec f ⟨a, haA⟩ ≠ 0 :=
    Sec12.coordVec_ne_zero f (fun h => hDa.ne_one (congrArg Subtype.val h))
  rcases cases131 h131 hspor hSLC hDa with ⟨-, -, -, hcase⟩ | ⟨-, -, -, ⟨eS3⟩⟩ |
      ⟨-, -, ⟨eZ3⟩, -⟩ | ⟨haX', -⟩
  · obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
    refine mem_Lstd_of_order_four (hle ⟨τ, autIn_mono le_top hτ, rfl⟩)
      (by rw [← map_pow, h4, map_one])
      (fun h => h2 (KFacts.glHom_injective f (by rw [map_pow, h, map_one]))) hu0 ?_
    rw [glHom_mulVec_coordVec, autIn_fix hDa.le_centralizer haA hτ]
    exact Submodule.mem_span_singleton_self _
  · exfalso
    obtain ⟨τ, hτ, h3, h1⟩ := exists_order_three_of_equiv eS3
      (m := Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) (by decide) (by decide)
    exact false_of_order_three_mono hDa haX hle hτ h3 h1
  · exfalso
    obtain ⟨τ, hτ, h3, h1⟩ := exists_order_three_of_equiv eZ3
      (m := Multiplicative.ofAdd (1 : ZMod 3)) (by decide) (by decide)
    exact false_of_order_three_mono hDa haX hle hτ h3 h1
  · exact absurd haX' haX

end Omega

section ASeven

theorem card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem exists_conj_eq_eStd {E : Subgroup (alternatingGroup (Fin 7))} (hE : Nat.card E = 9) :
    ∃ ρ : alternatingGroup (Fin 7), E.map (MulAut.conj ρ).toMonoidHom = eStd := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ∀ {H : Subgroup (alternatingGroup (Fin 7))}, Nat.card H = 9 → ¬ 3 ∣ H.index := by
    intro H hH h3
    have := H.card_mul_index
    rw [hH, card_alternating_seven] at this
    omega
  have hP : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hQ : IsPGroup 3 eStd := IsPGroup.of_card (n := 2) (by rw [card_eStd]; norm_num)
  obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hP.toSylow (hidx hE))
    (hQ.toSylow (hidx card_eStd))
  refine ⟨ρ, ?_⟩
  have h := congrArg (fun S : Sylow 3 (alternatingGroup (Fin 7)) =>
    (S : Subgroup (alternatingGroup (Fin 7)))) hρ
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
  rw [← h]
  rfl

end ASeven

section Swap

open CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coordVec_mul' {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (x y : A) :
    Sec12.coordVec f (x * y) = Sec12.coordVec f x + Sec12.coordVec f y := by
  simp [Sec12.coordVec]

omit [Finite G] in
theorem coordVec_inv' {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (x : A) :
    Sec12.coordVec f x⁻¹ = -Sec12.coordVec f x := by
  simp [Sec12.coordVec]

theorem eq_one_of_mem_theta {L : Subgroup G} {b : L} (hb3 : b ^ 3 = 1)
    (hb : b ∈ aschbacherSolvableCore 3 L) : b = 1 := by
  have hnd := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hdvd : orderOf b ∣ Nat.card (aschbacherSolvableCore 3 L) := by
    have := Subgroup.orderOf_dvd_natCard (aschbacherSolvableCore 3 L) hb
    exact this
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb3) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hdvd) hnd

theorem exists_swap_of_conj {L B : Subgroup G}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
    (hB : ∀ l : B.subgroupOf L, e (l : L) ∈ eStd)
    (hBE : ∀ g ∈ eStd, ∃ l : B.subgroupOf L, e (l : L) = g)
    {t : G} (htL : t ∈ Subgroup.normalizer (L : Set G))
    (htB : ∀ b ∈ B, t * b * t⁻¹ ∈ B) {b : L}
    (hby : e (b : L ⧸ aschbacherSolvableCore 3 L) = y7A) (htb : t * b * t⁻¹ = b)
    {x : L} (hxB : (x : G) ∈ B) (htx : t * x * t⁻¹ = (x : G)⁻¹)
    (hx1 : e (x : L ⧸ aschbacherSolvableCore 3 L) ≠ 1) :
    ∃ τ : Equiv.Perm (Fin 7), τ.IsSwap ∧ ∀ y : L ⧸ aschbacherSolvableCore 3 L,
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t ^ 3, Subgroup.pow_mem _ htL 3⟩) y) :
          Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹ := by
  set α := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, htL⟩) with hαdef
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 7) (Or.inr le_rfl)
    (e.symm.trans (α.trans e))
  have hσ' : ∀ y, ((e (α y) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      σ * (e y : Equiv.Perm (Fin 7)) * σ⁻¹ := by
    intro y
    have := hσ (e y)
    simpa using this
  have hαmk : ∀ l : L, α (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL l).mp l.2⟩ : L) :
        L ⧸ aschbacherSolvableCore 3 L) := fun l => rfl
  have hy : σ * y7 = y7 * σ := by
    have h1 := hσ' (b : L ⧸ aschbacherSolvableCore 3 L)
    have hb' : (⟨t * b * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL b).mp b.2⟩ : L) = b :=
      Subtype.ext htb
    rw [hαmk, hb', hby] at h1
    have h2 : σ * y7 * σ⁻¹ = y7 := h1.symm
    calc σ * y7 = σ * y7 * σ⁻¹ * σ := by group
      _ = y7 * σ := by rw [h2]
  have hN : ∀ g ∈ eStd, ∃ g' ∈ eStd,
      σ * (g : Equiv.Perm (Fin 7)) * σ⁻¹ = (g' : Equiv.Perm (Fin 7)) := by
    intro g hg
    obtain ⟨l, rfl⟩ := hBE g hg
    have hl : ((l : L) : G) ∈ B := Subgroup.mem_subgroupOf.mp l.2
    refine ⟨_, hB ⟨⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL l).mp (l : L).2⟩,
      Subgroup.mem_subgroupOf.mpr (htB _ hl)⟩, ?_⟩
    rw [← hσ', hαmk]
  have hne : ∃ g ∈ eStd, σ * (g : Equiv.Perm (Fin 7)) * σ⁻¹ ≠ g := by
    refine ⟨_, hB ⟨x, Subgroup.mem_subgroupOf.mpr hxB⟩, ?_⟩
    rw [← hσ', hαmk]
    have hx' : (⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL x).mp x.2⟩ : L) = x⁻¹ :=
      Subtype.ext htx
    rw [hx', QuotientGroup.mk_inv, map_inv]
    intro h
    apply hx1
    set g := e (x : L ⧸ aschbacherSolvableCore 3 L) with hgdef
    have h3 := pow_three_of_mem_eStd (hB ⟨x, Subgroup.mem_subgroupOf.mpr hxB⟩)
    have h2 : g ^ 2 = 1 := by
      have h' : g⁻¹ = g := Subtype.ext h
      rw [sq]
      nth_rewrite 1 [← h']
      exact inv_mul_cancel _
    have : g = g ^ 3 * (g ^ 2)⁻¹ := by group
    rw [this, h3, h2, inv_one, one_mul]
  have hz := conj_z7_eq_inv hy hN hne
  refine ⟨σ ^ 3, isSwap_pow_three hy hz, fun y => ?_⟩
  have hpow : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t ^ 3, Subgroup.pow_mem _ htL 3⟩) =
      α ^ 3 := by
    rw [hαdef, ← map_pow, ← map_pow]
    congr 2
  rw [hpow, pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hσ', hσ', hσ']
  simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]

end Swap

section Main

open CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem case_two_133 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hset : Item13SetupAt) (hSLT : NotSLTwoOfHypT) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hST : HypS A ∨ HypT A) (hcL : c ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hirrW : Sec21.IsIrreducibleOn (wStar A))
    {φ : wStar A →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)} (hφ : Function.Injective φ)
    (eA7 : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
    (ψ : Sec4.autIn L A ≃* Multiplicative (ZMod 4)) :
    (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
      (omegaA A).ncard = 3 ∧
      (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
        F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) ∧
      ∃ t ∈ Subgroup.normalizer (A : Set G), t * c * t⁻¹ = c⁻¹ ∧
        ∃ (ht : t ∈ Subgroup.normalizer (L : Set G))
          (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
          (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L ⧸ aschbacherSolvableCore 3 L,
            ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, ht⟩) y) :
                Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹ := by
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  set B := A ⊓ L with hBdef
  obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_equiv ψ
    (m := Multiplicative.ofAdd (1 : ZMod 4)) (by decide) (by decide)
  have hτW : τ ∈ wStar A := autIn_mono le_top hτ
  have hW48 : Nat.card (wStar A) ∣ 48 := by
    have h1 := Subgroup.card_subgroup_dvd_card φ.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_prod,
      card_multiplicative_zmod, Nat.card_perm, Nat.card_fin] at h1
    exact h1
  have hord : orderOf (⟨τ, hτW⟩ : wStar A) = 4 := by
    have h4' : (⟨τ, hτW⟩ : wStar A) ^ 4 = 1 := Subtype.ext h4
    have h2' : (⟨τ, hτW⟩ : wStar A) ^ 2 ≠ 1 := fun h => h2 (congrArg Subtype.val h)
    have hdvd := orderOf_dvd_of_pow_eq_one h4'
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf (⟨τ, hτW⟩ : wStar A)
    · exact absurd (orderOf_eq_zero_iff'.mp h 4 (by norm_num)) (by simpa using h4')
    · exact absurd (by rw [← orderOf_dvd_iff_pow_eq_one, h]; norm_num) h2'
    · exact absurd (by rw [← orderOf_dvd_iff_pow_eq_one, h]) h2'
    · norm_num at hdvd
    · rfl
  have hW4 : 4 ∣ Nat.card (wStar A) := hord ▸ orderOf_dvd_natCard _
  have hW13 : ¬ 13 ∣ Nat.card (wStar A) := fun h => absurd (h.trans hW48) (by norm_num)
  obtain ⟨f, hle, hG0⟩ := exists_std_coords hAe h27 hirrW hW4 hW13
  set G' := (wStar A).map (KFacts.glHom f) with hG'def
  set M := KFacts.glHom f τ with hMdef
  have hMG : M ∈ G' := ⟨τ, hτW, rfl⟩
  have hM4 : M ^ 4 = 1 := by rw [hMdef, ← map_pow, h4, map_one]
  have hM2 : M ^ 2 ≠ 1 := fun h =>
    h2 (KFacts.glHom_injective f (by rw [map_pow, ← hMdef, h, map_one]))
  set vc := Sec12.coordVec f ⟨c, hcA⟩ with hvcdef
  have hvc0 : vc ≠ 0 := Sec12.coordVec_ne_zero f (fun h => hD.ne_one (congrArg Subtype.val h))
  have hMvc : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vc = vc := by
    rw [hMdef, hvcdef, glHom_mulVec_coordVec, autIn_fix hD.le_centralizer hcA hτ]
  obtain ⟨i, hi⟩ := mem_Lstd_of_order_four (hle hMG) hM4 hM2 hvc0
    (by rw [hMvc]; exact Submodule.mem_span_singleton_self _)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact hvc0 hμ.symm
  have hMi : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single i 1 := by
    have h := hMvc
    rw [← hμ, Matrix.mulVec_smul] at h
    exact smul_right_injective _ hμ0 h
  have hN0 : monomialDetOne Lstd ≤ G' := N0std_le_of hle hG0 hMG hM4 hM2 hMi
  have hWiso : Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
    have e0 : wStar A ≃* G' := (wStar A).equivMapOfInjective _ (KFacts.glHom_injective f)
    rcases nonempty_equiv_of_N0std_le hle hN0 with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨e0.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨e0.trans e⟩
  have hfromW : ∀ r ∈ monomialDetOne Lstd, ∃ (w : G) (hw : w ∈ Subgroup.normalizer (A : Set G)),
      KFacts.glHom f (A.normalizerMonoidHom ⟨w, hw⟩) = r := by
    intro r hr
    obtain ⟨σ, hσ, rfl⟩ := hN0 hr
    obtain ⟨w, hw, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact ⟨w, hw, rfl⟩
  have hPj : ∀ j, ∃ w ∈ Subgroup.normalizer (A : Set G),
      Subgroup.zpowers (coordPt f j) = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
    intro j
    obtain ⟨r, hr, hrij⟩ := exists_mem_N0std_mulVec i j
    obtain ⟨w, hw, hwr⟩ := hfromW r hr
    refine ⟨w, hw, ?_⟩
    rw [MonoidHom.map_zpowers]
    have hne : A.normalizerMonoidHom ⟨w, hw⟩ ⟨c, hcA⟩ ≠ 1 := by
      intro h
      apply hD.ne_one
      have := congrArg Subtype.val h
      rw [normalizerMonoidHom_apply_val] at this
      have h1 : c = w⁻¹ * (w * c * w⁻¹) * w := by group
      rw [h1]
      change w⁻¹ * (w * c * w⁻¹) * w = 1
      rw [show w * c * w⁻¹ = 1 from this]
      group
    have hx := zpowers_eq_coordPt f hne (j := j) (by
      rw [← glHom_mulVec_coordVec, hwr, ← hvcdef, ← hμ, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ hrij)
    rw [← hx]
    rfl
  have hc3 : ∀ (a : G) (haA : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
      (⟨a, haA⟩ : A) ≠ 1 := by
    intro a haA h h1
    have := (zpowers_mem_omegaA_iff.mp h).2.1
    rw [show a = 1 from congrArg Subtype.val h1, Subgroup.zpowers_one_eq_bot,
      Subgroup.card_bot] at this
    norm_num at this
  have hΩsub : ∀ F ∈ omegaA A, ∃ j, F = Subgroup.zpowers (coordPt f j) := by
    intro F hF
    obtain ⟨hFA, hF3, a, rfl, hstar⟩ := hF
    have haA : a ∈ A := hFA (Subgroup.mem_zpowers a)
    obtain ⟨j, hj⟩ := coord_line_of_mem_omegaA h131 hspor hSLC hset hSLT hD hST hirrW hle
      ⟨hFA, hF3, a, rfl, hstar⟩ haA
    exact ⟨j, zpowers_eq_coordPt f (hc3 a haA ⟨hFA, hF3, a, rfl, hstar⟩) hj⟩
  have hPmem : ∀ j, Subgroup.zpowers (coordPt f j) ∈ omegaA A := by
    intro j
    obtain ⟨w, hw, hwj⟩ := hPj j
    rw [hwj]
    exact (map_conj_mem_omegaA_iff hw).mpr hD.zpowers_mem_omegaA
  have hΩeq : omegaA A = {Subgroup.zpowers (coordPt f 0), Subgroup.zpowers (coordPt f 1),
      Subgroup.zpowers (coordPt f 2)} := by
    ext F
    constructor
    · intro hF
      obtain ⟨j, rfl⟩ := hΩsub F hF
      fin_cases j <;> simp
    · rintro (rfl | rfl | rfl) <;> exact hPmem _
  have hncard : (omegaA A).ncard = 3 := by
    rw [hΩeq]
    refine Set.ncard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> intro h <;>
      exact absurd (coordPt_injective f h) (by decide)
  have htrans : ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
      F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
    intro F hF
    obtain ⟨j, rfl⟩ := hΩsub F hF
    exact hPj j
  refine ⟨hWiso, hncard, htrans, ?_⟩
  have hτB : ∀ y : A, (y : G) ∈ B → ((τ y : A) : G) ∈ B := fun y hy =>
    ⟨(τ y).2, autIn_mem_inf hτ hy.2⟩
  have hBcoord : ∀ x : A, (x : G) ∈ B → Sec12.coordVec f x i = 0 := by
    intro x hx
    by_contra hne
    set v := Sec12.coordVec f x with hvdef
    have hy2 : (((τ ^ 2) x : A) : G) ∈ B := by
      rw [pow_two, MulAut.mul_apply]
      exact hτB _ (hτB _ hx)
    have hxy : ((x * (τ ^ 2) x : A) : G) ∈ B := B.mul_mem hx hy2
    have hcoord : Sec12.coordVec f (x * (τ ^ 2) x) = (2 * v i) • Pi.single i 1 := by
      rw [coordVec_mul', ← glHom_mulVec_coordVec, map_pow, ← hMdef]
      exact add_sq_mulVec (hle hMG) hM4 hM2 hMi v
    have hk : (2 * v i : ZMod 3) ≠ 0 := mul_ne_zero (by decide) hne
    set z := (x * (τ ^ 2) x) ^ ((2 * v i)⁻¹ : ZMod 3).val with hzdef
    have hz : Sec12.coordVec f z = Pi.single i 1 := by
      rw [hzdef, KFacts.coordVec_pow, hcoord, ← Nat.cast_smul_eq_nsmul (ZMod 3),
        ZMod.natCast_zmod_val, smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hzB : (z : G) ∈ B := by
      rw [hzdef, Subgroup.coe_pow]
      exact B.pow_mem hxy _
    have hcz : (⟨c, hcA⟩ : A) ∈ Subgroup.zpowers z := by
      rw [← KFacts.coordVec_mem_span_iff f, hz, ← hvcdef]
      exact hi
    apply hcL
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcz
    have hc : c = (z : G) ^ n := by
      have := congrArg Subtype.val hn
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    rw [hc]
    exact L.zpow_mem hzB.2 n
  have hBfull : ∀ v : Fin 3 → ZMod 3, v i = 0 →
      ((f (Multiplicative.ofAdd v) : A) : G) ∈ B := by
    intro v hv
    let φB : {x : A // (x : G) ∈ B} → {v : Fin 3 → ZMod 3 // v i = 0} :=
      fun x => ⟨Sec12.coordVec f x.1, hBcoord x.1 x.2⟩
    have hinj : Function.Injective φB := fun x y h =>
      Subtype.ext (KFacts.coordVec_injective f (congrArg Subtype.val h))
    have hcardB : Nat.card {x : A // (x : G) ∈ B} = 9 := by
      rw [← h9]
      exact Nat.card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    have hbij : Function.Bijective φB := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨hinj, by rw [hcardB, card_coord_zero]⟩
    obtain ⟨x, hx⟩ := hbij.2 ⟨v, hv⟩
    have h1 : Sec12.coordVec f x.1 = v := congrArg Subtype.val hx
    have : f (Multiplicative.ofAdd v) = x.1 := by
      rw [← h1]
      simp [Sec12.coordVec]
    rw [this]
    exact x.2
  set ιB : B.subgroupOf L →* alternatingGroup (Fin 7) :=
    eA7.toMonoidHom.comp ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp
      (B.subgroupOf L).subtype) with hιdef
  have hιinj : Function.Injective ιB := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (b : L) = 1 := by
      have : eA7 (QuotientGroup.mk' _ (b : L)) = 1 := hb
      rwa [MulEquiv.map_eq_one_iff] at this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hb3 : (b : L) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hAe.2 _ (Subgroup.mem_subgroupOf.mp b.2).1)
    exact Subtype.ext (eq_one_of_mem_theta hb3 h1)
  have hE9 : Nat.card ιB.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  obtain ⟨ρ, hρ⟩ := exists_conj_eq_eStd hE9
  set e' := eA7.trans (MulAut.conj ρ) with he'def
  have he'mk : ∀ l : B.subgroupOf L,
      e' ((l : L) : L ⧸ aschbacherSolvableCore 3 L) = MulAut.conj ρ (ιB l) := fun l => rfl
  have hB' : ∀ l : B.subgroupOf L, e' ((l : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ eStd := by
    intro l
    rw [he'mk, ← hρ]
    exact ⟨ιB l, ⟨l, rfl⟩, rfl⟩
  have hBE' : ∀ g ∈ eStd, ∃ l : B.subgroupOf L,
      e' ((l : L) : L ⧸ aschbacherSolvableCore 3 L) = g := by
    intro g hg
    rw [← hρ] at hg
    obtain ⟨_, ⟨l, rfl⟩, rfl⟩ := hg
    exact ⟨l, rfl⟩
  obtain ⟨by_, hby⟩ := hBE' y7A y7A_mem
  have hbyB : ((by_ : L) : G) ∈ B := Subgroup.mem_subgroupOf.mp by_.2
  set bA : A := ⟨((by_ : L) : G), hbyB.1⟩ with hbAdef
  have hb1 : ((by_ : L) : G) ≠ 1 := by
    intro h
    have : (by_ : L) = 1 := Subtype.ext h
    rw [this, QuotientGroup.mk_one, map_one] at hby
    exact y7A_ne_one hby.symm
  set v := Sec12.coordVec f bA with hvdef
  have hvi : v i = 0 := hBcoord bA hbyB
  have hv0 : v ≠ 0 := Sec12.coordVec_ne_zero f (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨r, hr, hri, hrv, -, w, hwi, hwv, hrw⟩ := exists_reflection i hvi hv0
  obtain ⟨t, htA, htr⟩ := hfromW r hr
  have hconj : ∀ y : A, Sec12.coordVec f (A.normalizerMonoidHom ⟨t, htA⟩ y) =
      (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Sec12.coordVec f y := by
    intro y
    rw [← glHom_mulVec_coordVec, htr]
  have hval : ∀ y : A, ((A.normalizerMonoidHom ⟨t, htA⟩ y : A) : G) = t * y * t⁻¹ :=
    fun y => normalizerMonoidHom_apply_val t htA y
  have htc : t * c * t⁻¹ = c⁻¹ := by
    have h1 : A.normalizerMonoidHom ⟨t, htA⟩ ⟨c, hcA⟩ = (⟨c, hcA⟩ : A)⁻¹ := by
      apply KFacts.coordVec_injective f
      rw [hconj, coordVec_inv', ← hvcdef, ← hμ, Matrix.mulVec_smul, hri, smul_neg]
    have := congrArg Subtype.val h1
    rw [hval] at this
    simpa using this
  have htb : t * ((by_ : L) : G) * t⁻¹ = ((by_ : L) : G) := by
    have h1 : A.normalizerMonoidHom ⟨t, htA⟩ bA = bA := by
      apply KFacts.coordVec_injective f
      rw [hconj, ← hvdef, hrv]
    have := congrArg Subtype.val h1
    rwa [hval] at this
  set xA := f (Multiplicative.ofAdd w) with hxAdef
  have hxB : (xA : G) ∈ B := hBfull w hwi
  have hxv : Sec12.coordVec f xA = w := by simp [hxAdef, Sec12.coordVec]
  have htx : t * (xA : G) * t⁻¹ = (xA : G)⁻¹ := by
    have h1 : A.normalizerMonoidHom ⟨t, htA⟩ xA = xA⁻¹ := by
      apply KFacts.coordVec_injective f
      rw [hconj, coordVec_inv', hxv, hrw]
    have := congrArg Subtype.val h1
    rw [hval] at this
    simpa using this
  have htH : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * c * t⁻¹) = _
    rw [htc, Subgroup.zpowers_inv]
  have hbc : ((by_ : L) : G) ∉ Subgroup.zpowers c := by
    intro h
    apply hcL
    exact (Subgroup.zpowers_le.mpr (by_ : L).2) (mem_zpowers_of_mem_zpowers hD.card_zpowers h hb1)
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer hD.sectionCentralizer_eq
      hbyB.1 (by_ : L).2 hbc ⟨htH, htA⟩
  have htBn : ∀ b ∈ B, t * b * t⁻¹ ∈ B := fun b hb =>
    ⟨(Subgroup.mem_normalizer_iff.mp htA b).mp hb.1, (Subgroup.mem_normalizer_iff.mp htL b).mp hb.2⟩
  have hx1 : e' (((⟨(xA : G), hxB.2⟩ : L)) : L ⧸ aschbacherSolvableCore 3 L) ≠ 1 := by
    intro h
    have h1 : ιB ⟨⟨(xA : G), hxB.2⟩, Subgroup.mem_subgroupOf.mpr hxB⟩ = 1 := by
      have : MulAut.conj ρ (ιB ⟨⟨(xA : G), hxB.2⟩, Subgroup.mem_subgroupOf.mpr hxB⟩) = 1 := h
      rwa [MulEquiv.map_eq_one_iff] at this
    have h2 := hιinj (h1.trans (map_one ιB).symm)
    apply hwv
    have hx0 : (xA : G) = 1 := congrArg (fun y : B.subgroupOf L => ((y : L) : G)) h2
    have : w = 0 := by
      rw [← hxv, show xA = 1 from Subtype.ext hx0]
      simp [Sec12.coordVec]
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨τ7, hτ7, hτ7y⟩ := exists_swap_of_conj e' hB' hBE' htL htBn hby htb
    (x := ⟨(xA : G), hxB.2⟩) hxB htx hx1
  have h1 : t * c⁻¹ * t⁻¹ = c := by
    rw [show t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ by group, htc, inv_inv]
  refine ⟨t ^ 3, Subgroup.pow_mem _ htA 3, ?_, Subgroup.pow_mem _ htL 3, e', τ7, hτ7, hτ7y⟩
  calc t ^ 3 * c * (t ^ 3)⁻¹ = t * (t * (t * c * t⁻¹) * t⁻¹) * t⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    _ = c⁻¹ := by rw [htc, h1, htc]


theorem eq_sup_of_card_nine {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcB : c ∉ A ⊓ L) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  set S := Subgroup.zpowers c ⊔ (A ⊓ L) with hSdef
  have hSA : S ≤ A := sup_le (Subgroup.zpowers_le.mpr hD.mem_A) inf_le_left
  have hBS : A ⊓ L ≤ S := le_sup_right
  have h1 : 9 ∣ Nat.card S := h9 ▸ Subgroup.card_dvd_of_le hBS
  have h2 : Nat.card S ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← hD.card_eq]
    exact Subgroup.card_dvd_of_le hSA
  have h3 : Nat.card S ≠ 9 := by
    intro h
    have : A ⊓ L = S := Subgroup.eq_of_le_of_card_ge hBS (by rw [h, h9])
    exact hcB (this ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  have h27 : Nat.card S = 27 := by
    interval_cases k <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hSA (by rw [h27, hD.card_eq])).symm

theorem rank3II_13_3_of_inputs (h131 : Item131) (h132 : Item132) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hset : Item13SetupAt) (hSLT : NotSLTwoOfHypT) : Item133 := by
  intro G _ _ A c L hD hST
  by_cases hW : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact Or.inl hW
  have hcL := not_mem_of_hyp h131 hspor hSLC hSLT hD hST hW
  rcases cases131 h131 hspor hSLC hD with ⟨-, h9, -, hcase⟩ | ⟨-, -, hMJ, -⟩ |
      ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · have hAe := hD.isElemAbelian
    have hcB : c ∉ A ⊓ L := fun h => hcL h.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
    have hirrL := isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2
    rcases h132 G A c L hD hST c hD.mem_A hD.ne_one L hD.mem_thetaComponentsAt hAa hcB hirrL with
      ⟨hWB, hO3e, hO3, hWsup, hΩc, -, hΩ9, hprod', hL⟩ | hWc | ⟨hirrW, -, φ, hφ⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hirrL, hWB, hO3e, hO3, hWsup, hΩc, hΩ9, hprod', hL⟩))
    · exact absurd hWc hW
    · have hLW : Sec4.autIn L A ≤ wStar A := autIn_mono le_top
      rcases h131 G A c L hD with ⟨-, he | he⟩ | ⟨hPGL, -, -⟩ | ⟨hφA, hψ⟩ | ⟨-, he⟩ |
          ⟨hM, -⟩ | ⟨hJ, -⟩ | ⟨h7, -, -⟩
      · obtain ⟨e⟩ := he
        exact (false_of_quaternion hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · obtain ⟨e⟩ := he
        exact (false_of_SL23 hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl hPGL)))
      · obtain ⟨φA⟩ := hφA
        obtain ⟨ψ⟩ := hψ
        obtain ⟨-, -, -, ⟨eA7⟩⟩ :=
          facts_of_prod hD isPerfect_center_alt7.1 isPerfect_center_alt7.2 φA
        obtain ⟨hWiso, hncard, htrans, ht⟩ :=
          case_two_133 h131 hspor hSLC hset hSLT hD hST hcL h9 hirrW hφ eA7 ψ
        exact Or.inr (Or.inl ⟨hWiso, ⟨φA⟩, hncard, htrans, ht⟩)
      · obtain ⟨e⟩ := he
        exact (false_of_quaternion hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
      · exfalso
        rcases h7 with hSL | ⟨hHeis, -⟩
        · exact hcL (mem_of_isSLThreePiTwo hSLC hD hSL)
        · exact hcL (mem_of_isHeisCentral hD hHeis)
  · rcases hMJ with hM | hJ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hPGL)))
  · exact absurd hcL' hcL

end Main

end CFSG.RankThree.PartTwo.Sec13
