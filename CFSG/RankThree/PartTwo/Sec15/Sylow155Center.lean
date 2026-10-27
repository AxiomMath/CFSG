module

import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Sylow155T

theorem subsingleton_quotient_of_eq_top {Q : Type*} [Group Q] {N : Subgroup Q} [N.Normal]
    (h : N = ⊤) : Subsingleton (Q ⧸ N) := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  rw [QuotientGroup.eq, h]
  exact Subgroup.mem_top _

theorem center_eq_bot_of_isQuasisimple {W : Type*} [Group W] [IsSimpleGroup W]
    (hq : IsQuasisimple W) : Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with h | h
  · exact h
  · exfalso
    have hs : IsSimpleGroup (W ⧸ Subgroup.center W) := hq.2.1
    have : Subsingleton (W ⧸ Subgroup.center W) := subsingleton_quotient_of_eq_top h
    exact not_nontrivial_iff_subsingleton.mpr this hs.toNontrivial

theorem center_eq_bot_of_mulEquiv {W S : Type*} [Group W] [Group S] (e : W ≃* S)
    (hS : Subgroup.center S = ⊥) : Subgroup.center W = ⊥ := by
  have hmap := Subgroup.map_center_eq e
  rw [hS] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem nontrivial_of_isTripleCover {U S : Type*} [Group U] [Group S] (hS : Nontrivial S)
    (h : Sec4.IsTripleCover U S) : Nontrivial (U ⧸ Subgroup.center U) := by
  obtain ⟨-, ⟨ψ⟩⟩ := h
  exact ψ.surjective.nontrivial

theorem eq_top_of_isQuasisimple_of_nontrivial {W : Type*} [Group W] (hq : IsQuasisimple W)
    {U : Subgroup W} (hU : U.Normal) (hnt : Nontrivial (↥U ⧸ Subgroup.center ↥U)) : U = ⊤ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hU with h | h
  · exact h
  · exfalso
    have hc : Subgroup.center ↥U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rw [Subgroup.mem_center_iff]
      intro v
      exact Subtype.ext (Subgroup.mem_center_iff.mp (h u.2) v)
    exact not_nontrivial_iff_subsingleton.mpr (subsingleton_quotient_of_eq_top hc) hnt

theorem not_isQuasisimple_prod {S₁ S₂ : Type*} [Group S₁] [Group S₂] [Nontrivial S₁]
    [Nontrivial S₂] : ¬ IsQuasisimple (S₁ × S₂) := by
  intro hq
  have hsup : (⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂) ⊔ (⊥ : Subgroup S₁).prod ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h1 : ((a, 1) : S₁ × S₂) ∈ (⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.one_mem _⟩
    have h2 : ((1, b) : S₁ × S₂) ∈ (⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top b⟩
    have hab : ((a, b) : S₁ × S₂) = (a, 1) * (1, b) := by
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hinf : (⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂) ⊓ (⊥ : Subgroup S₁).prod ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_prod] at hx
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subgroup.mem_bot.mp hx.2.1) (Subgroup.mem_bot.mp hx.1.2)
  rcases eq_bot_or_eq_bot_of_isQuasisimple hq (Subgroup.prod_normal _ _)
      (Subgroup.prod_normal _ _) hsup hinf with h | h
  · obtain ⟨x, hx⟩ := exists_ne (1 : S₁)
    exact hx (Subgroup.mem_bot.mp ((Subgroup.prod_eq_bot_iff.mp h).1 ▸ Subgroup.mem_top x))
  · obtain ⟨x, hx⟩ := exists_ne (1 : S₂)
    exact hx (Subgroup.mem_bot.mp ((Subgroup.prod_eq_bot_iff.mp h).2 ▸ Subgroup.mem_top x))

theorem aschbacherSolvableCore_eq_pPrimeCore {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (h3 : 3 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X)) :
    aschbacherSolvableCore 3 X = CFSG.pPrimeCore 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, hθmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have : (aschbacherSolvableCore 3 X).Characteristic := hθc
  refine le_antisymm
    (le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩) ?_
  have hNn : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal (p := 3) (G := X)
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  have hNb : ((CFSG.pPrimeCore 3 X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNb with htop | hcen
  · exfalso
    apply hN3
    have h1 : Nat.card ((CFSG.pPrimeCore 3 X).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 X))) ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
      Subgroup.card_map_dvd _ _
    rw [htop, Subgroup.card_top] at h1
    exact h3.trans h1
  · have hKs : Group.IsSolvable ((Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)).comap
        (QuotientGroup.mk' (aschbacherSolvableCore 3 X))) :=
      isSolvable_comap_center _ hθs
    have hNK : CFSG.pPrimeCore 3 X ≤ (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)).comap
        (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) := fun x hx =>
      hcen (Subgroup.mem_map_of_mem _ hx)
    have hNs : Group.IsSolvable (CFSG.pPrimeCore 3 X) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNK)
    exact hθmax _ hNn hNs hN3

theorem card_center_le_three_of_isSimpleGroup {W : Type*} [Group W] (hq : IsQuasisimple W)
    (hS : IsSimpleGroup W) : Nat.card (Subgroup.center W) ≤ 3 := by
  rw [center_eq_bot_of_isQuasisimple hq, Subgroup.card_bot]
  norm_num

theorem card_center_le_three_of_mulEquiv_simple {W S : Type*} [Group W] [Group S]
    (hq : IsQuasisimple W) (hS : IsSimpleGroup S) (e : W ≃* S) :
    Nat.card (Subgroup.center W) ≤ 3 :=
  card_center_le_three_of_isSimpleGroup hq e.isSimpleGroup

theorem card_center_le_three_of_mulEquiv_bot {W S : Type*} [Group W] [Group S] (e : W ≃* S)
    (hS : Subgroup.center S = ⊥) : Nat.card (Subgroup.center W) ≤ 3 := by
  rw [center_eq_bot_of_mulEquiv e hS, Subgroup.card_bot]
  norm_num

theorem card_center_le_three_of_isTripleCover {W S : Type*} [Group W] [Group S]
    (h : Sec4.IsTripleCover W S) : Nat.card (Subgroup.center W) ≤ 3 :=
  h.1.le

theorem false_of_mulEquiv_prod {W S₁ S₂ : Type*} [Group W] [Group S₁] [Group S₂]
    (hq : IsQuasisimple W) (h₁ : Nontrivial S₁) (h₂ : Nontrivial S₂) (e : W ≃* S₁ × S₂) :
    False :=
  not_isQuasisimple_prod (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

theorem false_of_isCentralProductA6Covers {W : Type*} [Group W] (hq : IsQuasisimple W)
    (h : IsCentralProductA6Covers W) : False := by
  obtain ⟨U, V, hU, hV, -, hcomm, -, hU6, hV6⟩ := h
  have h6 := (Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)).toNontrivial
  have hUt := eq_top_of_isQuasisimple_of_nontrivial hq hU (nontrivial_of_isTripleCover h6 hU6)
  have hVt := eq_top_of_isQuasisimple_of_nontrivial hq hV (nontrivial_of_isTripleCover h6 hV6)
  rw [hUt, hVt] at hcomm
  have hc : commutator W = ⊥ := hcomm
  rw [Group.isPerfect_def.mp hq.1] at hc
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨x, hx⟩ := exists_ne (1 : W)
  exact hx (Subgroup.mem_bot.mp (hc ▸ Subgroup.mem_top x))

theorem false_of_isA6CoverTimesA5 {W : Type*} [Group W] (hq : IsQuasisimple W)
    (h : IsA6CoverTimesA5 W) : False := by
  obtain ⟨U, V, hU, -, hUV, -, hU6, heV⟩ := h
  obtain ⟨eV⟩ := heV
  have h6 := (Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)).toNontrivial
  have h5 := (Y4Core.isSimpleGroup_alternatingGroup 5 le_rfl).toNontrivial
  have hUt := eq_top_of_isQuasisimple_of_nontrivial hq hU (nontrivial_of_isTripleCover h6 hU6)
  rw [hUt, top_inf_eq] at hUV
  obtain ⟨v, hv⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  apply hv
  have h1 : eV.symm v = 1 := Subtype.ext (Subgroup.mem_bot.mp (hUV ▸ (eV.symm v).2))
  rw [← eV.apply_symm_apply v, h1, map_one]

theorem card_center_le_three_of_types
    {W Lb : Type} [Group W]
    [Group Lb] [Finite Lb] (hq : IsQuasisimple W) (φ : W ≃* Lb)
    (htypes : Nonempty (Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi Lb ∨
      Nonempty (Lb ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (Lb ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (Lb ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Nat.card (Subgroup.center W) ≤ 3 := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, -, hJ2z⟩ := Sec13.sporadicModels131
  rcases htypes with hψ | ⟨p, e, hp, he, hiso⟩ | hψ | hψ | hψ
  · obtain ⟨ψ⟩ := hψ
    exact card_center_le_three_of_mulEquiv_bot (φ.trans ψ) hJ2z
  · have : Group.IsPerfect W := hq.1
    have : Group.IsPerfect Lb := Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    exact card_center_le_three_of_mulEquiv_simple hq
      (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso).1 φ
  · obtain ⟨ψ⟩ := hψ
    exact card_center_le_three_of_mulEquiv_simple hq
      (Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)) (φ.trans ψ)
  · obtain ⟨ψ⟩ := hψ
    exact card_center_le_three_of_mulEquiv_bot (φ.trans ψ) hM22z
  · obtain ⟨ψ⟩ := hψ
    exact card_center_le_three_of_mulEquiv_bot (φ.trans ψ) hM12z

section Case148

variable {G : Type} [Group G] [Finite G]

theorem false_of_case7 {A Y : Subgroup G} [(ker148 A Y).Normal] (hAab : IsMulCommutative A)
    {D J₁ J₂ : Subgroup G} (hJ₁ : J₁ ≤ Y) (hJ₂ : J₂ ≤ Y) (hq : IsQuasisimple ↥(img148 A Y D))
    (hsup : img148 A Y J₁ ⊔ img148 A Y J₂ = img148 A Y D)
    (hinf : img148 A Y J₁ ⊓ img148 A Y J₂ = ⊥) (hcomm : ⁅img148 A Y J₁, img148 A Y J₂⁆ = ⊥)
    {p₁ f₁ p₂ f₂ : ℕ} (hZ₁ : IsZ3PGLThreeAt ↥(img148 A Y (J₁ ⊔ A)) p₁ f₁)
    (hZ₂ : IsZ3PGLThreeAt ↥(img148 A Y (J₂ ⊔ A)) p₂ f₂) : False := by
  have hJ₁le : img148 A Y J₁ ≤ img148 A Y D := hsup ▸ le_sup_left
  have hJ₂le : img148 A Y J₂ ≤ img148 A Y D := hsup ▸ le_sup_right
  have hC₁ : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hC₂ : img148 A Y J₁ ≤ Subgroup.centralizer (img148 A Y J₂ : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hN₁ : ((img148 A Y J₁).subgroupOf (img148 A Y D)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : ((img148 A Y J₂).subgroupOf (img148 A Y D)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
    rw [← hsup]
    exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hsup' : (img148 A Y J₁).subgroupOf (img148 A Y D) ⊔
      (img148 A Y J₂).subgroupOf (img148 A Y D) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
  have hinf' : (img148 A Y J₁).subgroupOf (img148 A Y D) ⊓
      (img148 A Y J₂).subgroupOf (img148 A Y D) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J₁ ⊓ img148 A Y J₂ := ⟨hx.1, hx.2⟩
    rw [hinf] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
  have hAle : A ≤ Y ⊔ A := le_sup_right
  have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
      ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
    intro J hJY hJ p f hZ
    rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
    obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
    exact hab (img148_comm hAab a b)
  rcases eq_bot_or_eq_bot_of_isQuasisimple hq hN₁ hN₂ hsup' hinf' with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact key J₁ hJ₁ (disjoint_self.mp (h.mono_right hJ₁le)) p₁ f₁ hZ₁
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact key J₂ hJ₂ (disjoint_self.mp (h.mono_right hJ₂le)) p₂ f₂ hZ₂

theorem card_center_img148_le_three
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hq : letI := ker148_normal hY.2
      IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y))) :
    letI := ker148_normal hY.2
    Nat.card (Subgroup.center ↥(img148 A Y (deltaZero A (lB A) Y))) ≤ 3 := by
  let := ker148_normal hY.2
  have h148Y := (h148 Y hY).2
  have hq' : IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) := hq
  have hS5 := Y4Core.isSimpleGroup_alternatingGroup 5 le_rfl
  have hS7 := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
  rcases h148Y with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq'
    have hX1 : img148 A Y (deltaZero A (lB A) Y) = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(img148 A Y (deltaZero A (lB A) Y)))
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hX1 ▸ x.2)))
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e, hp, hf, he, -, hε⟩ | ⟨-, h6' | hφ⟩
    ·
      obtain ⟨φ⟩ := hφ
      exact card_center_le_three_of_types hq' φ (h.chosen136.2 c' hc' L' hL').1
    ·
      obtain ⟨φ⟩ := hφ
      exact card_center_le_three_of_mulEquiv_simple hq' hS7 φ
    ·
      exact card_center_le_three_of_isSimpleGroup hq'
        (Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε)
    ·
      exact card_center_le_three_of_isTripleCover h6'
    ·
      obtain ⟨φ⟩ := hφ
      exact card_center_le_three_of_mulEquiv_simple hq' hS5 φ
  ·
    obtain ⟨c', d, L', -, -, -, -, -, -, -, hcases⟩ := h3
    rcases hcases with hON | hcp | hA6A5 | hφ | hφ | ⟨_, hφ⟩
    ·
      exact card_center_le_three_of_isTripleCover hON
    · exact (false_of_isCentralProductA6Covers hq' hcp).elim
    · exact (false_of_isA6CoverTimesA5 hq' hA6A5).elim
    ·
      obtain ⟨φ⟩ := hφ
      exact (false_of_mulEquiv_prod hq' hS5.toNontrivial hS5.toNontrivial φ).elim
    ·
      obtain ⟨φ⟩ := hφ
      exact card_center_le_three_of_mulEquiv_simple hq' hS7 φ
    ·
      obtain ⟨φ⟩ := hφ
      exact card_center_le_three_of_mulEquiv_simple hq'
        (Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)) φ
  ·
    obtain ⟨hφ, -, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact card_center_le_three_of_mulEquiv_simple hq'
      (Y4Core.isSimpleGroup_alternatingGroup 10 (by norm_num)) φ
  ·
    obtain ⟨c', -, L', n, m, -, -, hn, -, hiso, -⟩ := h5
    have : Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)) := hq'.1
    exact card_center_le_three_of_isSimpleGroup hq'
      (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega : 1 ≤ 3 * n) hiso).1
  ·
    obtain ⟨hφ, -, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact (false_of_mulEquiv_prod hq' hS5.toNontrivial
      CFSG.Sporadic.J2.isSimpleGroup_J2.toNontrivial φ).elim
  ·
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    exact (false_of_case7 h.isElemAbelian.1 (hJ₁.trans inf_le_right) (hJ₂.trans inf_le_right)
      hq' hsup hinf hcomm hZ₁ hZ₂).elim

theorem card_center_le_three_of_mem_scriptY4
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) {X : Subgroup G}
    (hX : X ∈ scriptY4 A (lB A)) (hΔ : X = deltaZero A (lB A) X) :
    Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXY : X ∈ scriptY A := hX.1
  obtain ⟨-, -, -, -, -, -, hθ2⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hqθ : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    Sec12.Hering129HLift.isQuasisimple_quot_theta (isPerfect_of_mem_scriptY4 hX)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _) hX.2.2.2
      (by
        rw [QuotientGroup.ker_mk']
        exact hθ2 2 Nat.prime_two (by norm_num))
  have hθne : aschbacherSolvableCore 3 ↥X ≠ ⊤ := fun htop => by
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hqθ
    exact not_nontrivial_iff_subsingleton.mpr (subsingleton_quotient_of_eq_top htop) hnt
  have h3 : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    three_dvd_card_quotient_of_eq_oPrimeResidualOf hX.2.1 _ hθne
  have hθO := aschbacherSolvableCore_eq_pPrimeCore hqθ h3
  let := ker148_normal hXY.2
  obtain ⟨ψ⟩ := nonempty_img148_equiv hXY.2
  have he : Nonempty (↥(img148 A X (deltaZero A (lB A) X)) ≃*
      ↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [← hΔ]
    exact ⟨ψ.trans (QuotientGroup.quotientMulEquivOfEq hθO.symm)⟩
  obtain ⟨e⟩ := he
  have hqW : IsQuasisimple ↥(img148 A X (deltaZero A (lB A) X)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqθ
  have hW := card_center_img148_le_three h h148 hXY hqW
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact hW

theorem card_center_le_three_of_mem_scriptY4'
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8)
    {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A)) :
    Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3 := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  exact card_center_le_three_of_mem_scriptY4 h h148 hX
    (rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
      (KFacts.KS14.center_nativeJ2_eq_bot h415) h hX)

theorem card_center_le_three_of_ctx155
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8)
    {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3 :=
  card_center_le_three_of_mem_scriptY4' h h148 h134 h48 (hC.res ▸ hC.isY.2.1)

end Case148

end Sylow155T

end CFSG.RankThree.PartTwo.Sec15
