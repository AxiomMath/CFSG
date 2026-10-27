module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix
import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

open CFSG Equiv CFSG.ComponentClassification

theorem card_le_of_isPGroup_of_dvd {X : Type*} [Group X] {p : ℕ} [hp : Fact p.Prime]
    {F : Subgroup X} [Finite F] (hF : IsPGroup p F) {m n : ℕ} (hdvd : Nat.card F ∣ m)
    (h : ¬ p ^ (n + 1) ∣ m) : Nat.card F ≤ p ^ n := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF
  have hkn : k ≤ n := by
    by_contra hlt
    push Not at hlt
    exact h ((Nat.pow_dvd_pow p hlt).trans (hk ▸ hdvd))
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos hkn

theorem card_le_of_isPGroup_of_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {F : Subgroup X} (hF : IsPGroup p F) {n : ℕ} (h : ¬ p ^ (n + 1) ∣ Nat.card X) :
    Nat.card F ≤ p ^ n :=
  card_le_of_isPGroup_of_dvd hF (Subgroup.card_subgroup_dvd_card F) h

theorem card_le_mul_card_inf_centralizer {Γ : Type*} [Group Γ] [Finite Γ] {U E : Subgroup Γ}
    (hEU : E ≤ Subgroup.normalizer (U : Set Γ)) (hE : CFSG.Assembly.IsElemAbelian 3 E) {b : ℕ}
    (hb : ∀ F : Subgroup (MulAut U), CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ b) :
    Nat.card E ≤ b * Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) := by
  set ρ : E →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hEU) with hρ
  have hcard : Nat.card E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have hEtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup E) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext (hE.2 a a.2)⟩
    exact congrArg Subtype.val (hE.1.is_comm.comm (a : E) (b : E))
  have hrange : Nat.card ρ.range ≤ b := by
    rw [MonoidHom.range_eq_map]
    exact hb _ (CFSG.SectionRank.isElemAbelian_map hEtop ρ)
  have hker : ρ.ker.map E.subtype = E ⊓ Subgroup.centralizer (U : Set Γ) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 := congrArg (fun σ : MulAut U => ((σ ⟨u, hu⟩ : U) : Γ)) (MonoidHom.mem_ker.mp hx)
      simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
      rw [U.normalizerMonoidHom_apply_apply_coe] at h1
      simp only [Subgroup.coe_inclusion] at h1
      calc u * (x : Γ) = (x : Γ) * u * (x : Γ)⁻¹ * (x : Γ) := by rw [h1]
        _ = (x : Γ) * u := by group
    · rintro ⟨hgE, hgC⟩
      refine ⟨⟨g, hgE⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply]
      rw [U.normalizerMonoidHom_apply_apply_coe]
      simp only [Subgroup.coe_inclusion]
      have h1 := Subgroup.mem_centralizer_iff.mp hgC u u.2
      calc g * (u : Γ) * g⁻¹ = (u : Γ) * g * g⁻¹ := by rw [h1]
        _ = u := by group
  have hker' : Nat.card ρ.ker = Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) := by
    rw [← hker, Subgroup.card_map_of_injective E.subtype_injective]
  rw [hcard, hker']
  exact Nat.mul_le_mul_right _ hrange

theorem isPGroup_of_isElemAbelian {X : Type*} [Group X] {F : Subgroup X}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : IsPGroup 3 F := CFSG.Open.IsElemAbelian.isPGroup hF

theorem card_mulAut_five : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))), Nat.card_perm, Nat.card_fin]
  rfl

theorem card_le_three_of_mulAut_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    (F : Subgroup (MulAut X)) (hF : IsPGroup 3 F) : Nat.card F ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (MulAut X) = 120 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans card_mulAut_five
  have : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h := card_le_of_isPGroup_of_not_dvd (n := 1) hF (by rw [hcard]; norm_num)
  simpa using h

theorem eq_top_of_isPerfect_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    {T : Subgroup X} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥) : T = ⊤ := by
  have : Finite X := Finite.of_equiv _ e.toEquiv.symm
  set f : X →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom with hf
  have hfi : Function.Injective f := (alternatingGroup (Fin 5)).subtype_injective.comp e.injective
  have hT' : Group.IsPerfect (T.map f) :=
    Group.IsPerfect.ofSurjective (f := (T.equivMapOfInjective f hfi).toMonoidHom)
      (MulEquiv.surjective _)
  have hne : T.map f ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hfi).mp h)
  have h5 := Sec4.Census.perfect_perm_five hT' hne
  have hcard : Nat.card T = Nat.card X := by
    rw [← Subgroup.card_map_of_injective hfi, h5, Nat.card_congr e.toEquiv]
  exact Subgroup.eq_top_of_card_eq T hcard

theorem exists_orderOf_three_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    ∃ x : X, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : swap (0 : Fin 5) 1 * swap 1 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h3 : (swap (0 : Fin 5) 1 * swap 1 2) ^ 3 = 1 := by decide
  have h1 : swap (0 : Fin 5) 1 * swap 1 2 ≠ 1 := by decide
  set c : alternatingGroup (Fin 5) := ⟨_, hmem⟩ with hc
  refine ⟨e.symm c, ?_⟩
  rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact orderOf_eq_prime h3 h1

theorem card_mulAut_six : Nat.card (MulAut (alternatingGroup (Fin 6))) = 720 ∨
    Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
  have hle := CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective (fun f : MulAut (alternatingGroup (Fin 6)) => (f : _ → _))
      DFunLike.coe_injective
  have hdvd := Subgroup.card_dvd_of_injective _
    (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num))
  rw [Nat.card_perm, Nat.card_fin] at hdvd
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have h6 : Nat.factorial 6 = 720 := rfl
  rw [h6] at hk
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> omega

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 :=
  KFacts.K412.card_alternating_six_seven.1

theorem finite_mulAut_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Finite (MulAut X) := by
  have : Finite X := Finite.of_equiv _ e.toEquiv.symm
  exact Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective

theorem card_le_nine_of_mulAut_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6))
    (F : Subgroup (MulAut X)) (hF : IsPGroup 3 F) : Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_mulAut_six e
  have hcard := card_mulAut_six
  rw [← Nat.card_congr (MulAut.congr e).toEquiv] at hcard
  have h := card_le_of_isPGroup_of_not_dvd (n := 2) hF (by rcases hcard with h | h <;> rw [h] <;>
    norm_num)
  simpa using h

theorem center_eq_bot_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Subgroup.center X = ⊥ := by
  have h := OuterAutomorphisms.center_map_equiv e
  rw [Sec15.Y4Core.good3_alternatingGroup_six.2.1] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem card_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) : Nat.card X = 360 :=
  (Nat.card_congr e.toEquiv).trans card_alternatingGroup_six

theorem mem_inner_of_pow_eq_one_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6))
    {σ : MulAut X} {k : ℕ} (hσ : σ ^ (3 ^ k) = 1) : σ ∈ OuterAutomorphisms.inner X := by
  have : Finite X := Finite.of_equiv _ e.toEquiv.symm
  have := finite_mulAut_six e
  have hA := card_mulAut_six
  rw [← Nat.card_congr (MulAut.congr e).toEquiv] at hA
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut X => φ g) hab
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [center_eq_bot_six e, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  have hI : Nat.card (OuterAutomorphisms.inner X) = 360 := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
      Subgroup.card_top, card_six e]
  have hO : Nat.card (OuterAutomorphisms.Outer X) * 360 = Nat.card (MulAut X) := by
    rw [← hI]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (OuterAutomorphisms.inner X)).symm
  have h3 : ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer X) := by
    intro h3
    obtain ⟨m, hm⟩ := h3
    rcases hA with h | h <;> omega
  set s : OuterAutomorphisms.Outer X := QuotientGroup.mk' (OuterAutomorphisms.inner X) σ with hs
  have hs3 : s ^ (3 ^ k) = 1 := by rw [hs, ← map_pow, hσ, map_one]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (OuterAutomorphisms.Outer X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have hord : orderOf s = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hs3) (orderOf_dvd_natCard s)
  rw [orderOf_eq_one_iff, hs, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
  exact hord

theorem six_le_index_of_six {X : Type*} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 6))
    {H : Subgroup X} (hH : H ≠ ⊤) : 6 ≤ H.index := by
  have := Sec15.Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
  have hsimp : IsSimpleGroup X := e.isSimpleGroup
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have hdvd := H.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, card_six e] at hdvd
  by_contra hlt
  push Not at hlt
  interval_cases h : H.index <;> revert hdvd <;> decide

theorem eq_top_or_card_eq_sixty_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6))
    {T : Subgroup X} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥) :
    T = ⊤ ∨ (Nonempty (T ≃* alternatingGroup (Fin 5)) ∧ Nat.card T = 60) := by
  have : Finite X := Finite.of_equiv _ e.toEquiv.symm
  set f : X →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom with hf
  have hfi : Function.Injective f := (alternatingGroup (Fin 6)).subtype_injective.comp e.injective
  have hT' : Group.IsPerfect (T.map f) :=
    Group.IsPerfect.ofSurjective (f := (T.equivMapOfInjective f hfi).toMonoidHom)
      (MulEquiv.surjective _)
  have hne : T.map f ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hfi).mp h)
  rcases Sec4.Census.perfect_perm_six hT' hne with h6 | hφ
  · left
    have hcard : Nat.card T = Nat.card X := by
      rw [← Subgroup.card_map_of_injective hfi, h6, card_six e, card_alternatingGroup_six]
    exact Subgroup.eq_top_of_card_eq T hcard
  · right
    obtain ⟨φ⟩ := hφ
    have φ' : T ≃* alternatingGroup (Fin 5) := (T.equivMapOfInjective f hfi).trans φ
    refine ⟨⟨φ'⟩, ?_⟩
    rw [Nat.card_congr φ'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl

theorem centralizer_eq_bot_six {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) {T : Subgroup X} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥) :
    Subgroup.centralizer (T : Set X) = ⊥ := by
  rcases eq_top_or_card_eq_sixty_six e hT hT1 with rfl | ⟨⟨φ⟩, h60⟩
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ, center_eq_bot_six e]
  · set C := Subgroup.centralizer (T : Set X) with hC
    have hcomm : ∀ x ∈ T, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp hy x hx
    have hinf : T ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : (⟨x, hx.1⟩ : T) ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
      have hZ : Subgroup.center T = ⊥ := by
        have h := OuterAutomorphisms.center_map_equiv φ
        rw [Sec15.Y4Core.good3_alternatingGroup_five.2.1] at h
        exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
      rw [hZ, Subgroup.mem_bot] at hxZ
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxZ
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T C hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, h60] at hcard
    by_contra hne
    have hC1 : 2 ≤ Nat.card C := by
      have : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hne
      exact Finite.one_lt_card
    have htop : T ⊔ C = ⊤ := by
      by_contra hne'
      have h6 := six_le_index_of_six e hne'
      have hmul := (T ⊔ C).card_mul_index
      rw [card_six e, hcard] at hmul
      have : 60 * Nat.card C * (T ⊔ C).index ≥ 60 * 2 * 6 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 60 hC1) h6
      omega
    have hC6 : Nat.card C = 6 := by
      have h := card_six e
      rw [← Subgroup.card_top (G := X), ← htop, hcard] at h
      omega
    have hCn : C.Normal := by
      have hN : (⊤ : Subgroup X) ≤ Subgroup.normalizer (C : Set X) := by
        rw [← htop]
        refine sup_le ?_ Subgroup.le_normalizer
        intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro c
        constructor
        · intro hc
          rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
          intro s hs
          have h1 := hc (t⁻¹ * s * t) (T.mul_mem (T.mul_mem (T.inv_mem ht) hs) ht)
          calc s * (t * c * t⁻¹) = t * ((t⁻¹ * s * t) * c) * t⁻¹ := by group
            _ = t * (c * (t⁻¹ * s * t)) * t⁻¹ := by rw [h1]
            _ = t * c * t⁻¹ * s := by group
        · intro hc
          rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
          intro s hs
          have h1 := hc (t * s * t⁻¹) (T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht))
          calc s * c = t⁻¹ * ((t * s * t⁻¹) * (t * c * t⁻¹)) * t := by group
            _ = t⁻¹ * ((t * c * t⁻¹) * (t * s * t⁻¹)) * t := by rw [h1]
            _ = c * s := by group
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
    have := Sec15.Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
    have hsimp : IsSimpleGroup X := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C with h | h
    · exact hne h
    · rw [h, Subgroup.card_top, card_six e] at hC6
      omega

theorem eq_bot_of_isSolvable_six {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) {T S : Subgroup X} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥)
    (hS : Group.IsSolvable S) (hTS : T ≤ Subgroup.normalizer (S : Set X)) : S = ⊥ := by
  have := Sec15.Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
  have hsimp : IsSimpleGroup X := e.isSimpleGroup
  have hXns : ¬ Group.IsSolvable X := by
    have : Group.IsPerfect (alternatingGroup (Fin 6)) := Sec15.Y4Core.good3_alternatingGroup_six.1.1
    have : Nontrivial (alternatingGroup (Fin 6)) := IsSimpleGroup.toNontrivial
    intro hX
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hnorm : S.Normal → S = ⊥ := by
    intro hSn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · exact h
    · exfalso
      subst h
      exact hXns (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X)).toMonoidHom)
        (MulEquiv.surjective _))
  rcases eq_top_or_card_eq_sixty_six e hT hT1 with rfl | ⟨⟨φ⟩, h60⟩
  · exact hnorm (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hTS))
  · by_cases hST : S ≤ T
    ·
      have := Sec15.Y4Core.isSimpleGroup_alternatingGroup 5 le_rfl
      have hTs : IsSimpleGroup T := φ.isSimpleGroup
      have hSn : (S.subgroupOf T).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mpr hTS
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf T) with h | h
      · rw [← Subgroup.map_subgroupOf_eq_of_le hST, h, Subgroup.map_bot]
      · exfalso
        rw [Subgroup.subgroupOf_eq_top] at h
        have := hS
        have hTsol : Group.IsSolvable T :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
        have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
        have := hT
        exact Group.IsPerfect.not_isSolvable T hTsol
    ·
      have hlt : T < T ⊔ S := lt_of_le_of_ne le_sup_left fun h => hST (h ▸ le_sup_right)
      have hcardlt : Nat.card T < Nat.card (T ⊔ S : Subgroup X) := Subgroup.card_lt_of_lt hlt
      have hdvd : Nat.card T ∣ Nat.card (T ⊔ S : Subgroup X) :=
        Subgroup.card_dvd_of_le le_sup_left
      have htop : T ⊔ S = ⊤ := by
        by_contra hne
        have h6 := six_le_index_of_six e hne
        have hmul := (T ⊔ S).card_mul_index
        rw [card_six e] at hmul
        rw [h60] at hcardlt hdvd
        obtain ⟨m, hm⟩ := hdvd
        rw [hm] at hmul hcardlt
        have hm2 : 2 ≤ m := by
          by_contra h
          push Not at h
          interval_cases m <;> omega
        have : 60 * m * (T ⊔ S).index ≥ 60 * 2 * 6 := Nat.mul_le_mul (Nat.mul_le_mul_left 60 hm2) h6
        omega
      have hN : (⊤ : Subgroup X) ≤ Subgroup.normalizer (S : Set X) := by
        rw [← htop]
        exact sup_le hTS Subgroup.le_normalizer
      exact hnorm (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN))

theorem eq_bot_of_le_normalizer_six {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) {P Q : Subgroup X} (hP : Nat.card P = 9)
    (hQ : ¬ 3 ∣ Nat.card Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set X)) : Q = ⊥ := by
  set f : X →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom with hf
  have hfi : Function.Injective f := (alternatingGroup (Fin 6)).subtype_injective.comp e.injective
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eSix (E := P.map f)
    (by rw [Subgroup.card_map_of_injective hfi, hP])
  set c := (MulAut.conj g).toMonoidHom with hc
  have hci : Function.Injective c := (MulAut.conj g).injective
  have hQ' : ¬ 3 ∣ Nat.card ((Q.map f).map c) := by
    rwa [Subgroup.card_map_of_injective hci, Subgroup.card_map_of_injective hfi]
  have hE : KFacts.K412.eSix ≤ Subgroup.normalizer (((Q.map f).map c : Subgroup (Perm (Fin 6))) :
      Set (Perm (Fin 6))) := by
    rw [← hg]
    exact (Subgroup.map_mono ((Subgroup.map_mono hPQ).trans (Subgroup.le_normalizer_map f))).trans
      (Subgroup.le_normalizer_map c)
  have h := KFacts.K412.eq_bot_of_le_normalizer hQ' hE
  rw [Subgroup.map_eq_bot_iff_of_injective _ hci, Subgroup.map_eq_bot_iff_of_injective _ hfi] at h
  exact h

theorem mul_pow_three_of_central {G : Type*} [Group G] {x y c : G}
    (hc : ∀ g : G, g * c = c * g) (hyx : y * x = c * x * y) :
    (x * y) ^ 3 = c ^ 3 * (x ^ 3 * y ^ 3) := by
  have h1 : y * x * y⁻¹ = c * x := by rw [hyx]; group
  have h2 : y * (c * x) * y⁻¹ = c * (c * x) := by
    calc y * (c * x) * y⁻¹ = (y * c) * x * y⁻¹ := by group
      _ = (c * y) * x * y⁻¹ := by rw [hc y]
      _ = c * (y * x * y⁻¹) := by group
      _ = c * (c * x) := by rw [h1]
  have hxc : x * c = c * x := hc x
  calc (x * y) ^ 3 = x * (y * x * y⁻¹) * (y * (y * x * y⁻¹) * y⁻¹) * y ^ 3 := by
        rw [pow_three]; group
    _ = x * (c * x) * (c * (c * x)) * y ^ 3 := by rw [h1, h2]
    _ = (x * c) * x * c * c * x * y ^ 3 := by group
    _ = (c * x) * x * c * c * x * y ^ 3 := by rw [hxc]
    _ = c * ((x * x) * c) * c * x * y ^ 3 := by group
    _ = c * (c * (x * x)) * c * x * y ^ 3 := by rw [hc (x * x)]
    _ = c * c * ((x * x) * c) * x * y ^ 3 := by group
    _ = c * c * (c * (x * x)) * x * y ^ 3 := by rw [hc (x * x)]
    _ = c ^ 3 * (x ^ 3 * y ^ 3) := by rw [pow_three c, pow_three x]; group

theorem exists_elemAbelian_nine_of_card_eq {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 27) (hnc : ¬ IsMulCommutative P) :
    ∃ E : Subgroup P, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  set Z := Subgroup.center P with hZ
  have hZdvd : Nat.card Z ∣ 27 := hP ▸ Subgroup.card_subgroup_dvd_card Z
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP]
    norm_num
  have hZnt : Nontrivial Z := hP3.center_nontrivial
  have hZ1 : 1 < Nat.card Z := Finite.one_lt_card
  have hquot : Nat.card (P ⧸ Z) * Nat.card Z = 27 := by
    rw [← hP]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  have hZ3 : Nat.card Z = 3 := by
    have hcases : Nat.card Z = 3 ∨ Nat.card Z = 9 ∨ Nat.card Z = 27 := by
      have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
      rw [h27] at hZdvd
      obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hZdvd
      interval_cases k <;> simp_all
    rcases hcases with h | h | h
    · exact h
    · exfalso
      rw [h] at hquot
      have hq3 : Nat.card (P ⧸ Z) = 3 := by omega
      have : IsCyclic (P ⧸ Z) := isCyclic_of_prime_card hq3
      exact hnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
        (by rw [QuotientGroup.ker_mk']))
    · exfalso
      apply hnc
      have htop : Z = ⊤ := Subgroup.eq_top_of_card_eq Z (h.trans hP.symm)
      refine ⟨⟨fun a b => ?_⟩⟩
      have hb : b ∈ Z := by rw [htop]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  have hq9 : Nat.card (P ⧸ Z) = 9 := by rw [hZ3] at hquot; omega
  have hqab : IsMulCommutative (P ⧸ Z) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hq9]; norm_num)
  have hqnc : ¬ IsCyclic (P ⧸ Z) := fun hc =>
    hnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']))
  have hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hqab.is_comm.comm (x : P ⧸ Z) y]
    group
  have hcube : ∀ x : P, x ^ 3 ∈ Z := by
    intro x
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    by_contra hne
    apply hqnc
    have hx9 : (x : P ⧸ Z) ^ 9 = 1 := by
      rw [← hq9]
      exact pow_card_eq_one'
    have hord : orderOf (x : P ⧸ Z) = 9 := by
      have hdvd : orderOf (x : P ⧸ Z) ∣ 3 ^ 2 := by
        norm_num
        exact orderOf_dvd_of_pow_eq_one hx9
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases k
      · rw [pow_zero, orderOf_eq_one_iff] at hk'
        rw [hk', one_pow] at hne
        exact absurd rfl hne
      · rw [pow_one] at hk'
        rw [← hk', pow_orderOf_eq_one] at hne
        exact absurd rfl hne
      · rw [hk']
        norm_num
    exact isCyclic_of_orderOf_eq_card (x : P ⧸ Z) (hord.trans hq9.symm)
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hmul : ∀ x y : P, (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
    intro x y
    have hcZ : y * x * y⁻¹ * x⁻¹ ∈ Z := hcomm y x
    rw [mul_pow_three_of_central (fun g => Subgroup.mem_center_iff.mp hcZ g)
      (by group), hZexp _ hcZ, one_mul]
  set f : P →* P :=
    { toFun := fun x => x ^ 3
      map_one' := one_pow 3
      map_mul' := hmul } with hf
  have hrange : f.range ≤ Z := by
    rintro _ ⟨x, rfl⟩
    exact hcube x
  have hker : 9 ≤ Nat.card f.ker := by
    have h1 : Nat.card P = Nat.card f.range * Nat.card f.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card f.range ≤ 3 := hZ3 ▸ Subgroup.card_le_of_le hrange
    rw [hP] at h1
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    by_contra h
    push Not at h
    have : Nat.card f.range * Nat.card f.ker ≤ 3 * 8 :=
      Nat.mul_le_mul h2 (by omega)
    omega
  have hkdvd : 3 ^ 2 ∣ Nat.card f.ker := by
    have hk3 : IsPGroup 3 f.ker := hP3.to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hk3
    rw [hn] at hker ⊢
    have hn2 : 2 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> norm_num at hker
    exact Nat.pow_dvd_pow 3 hn2
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.ker) 3 hkdvd
  have hEab : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hE
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨hEab, fun a _ => Subtype.ext (MonoidHom.mem_ker.mp a.2)⟩
  refine ⟨E.map f.ker.subtype, CFSG.SectionRank.isElemAbelian_map hE3 _, ?_⟩
  rw [Subgroup.card_map_of_injective f.ker.subtype_injective, hE]
  norm_num

theorem card_tripleCover {U : Type*} [Group U]
    (htc : Sec4.IsTripleCover U (alternatingGroup (Fin 6))) : Nat.card U = 1080 := by
  obtain ⟨h3, ⟨φ⟩⟩ := htc
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center U)
  rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_six, h3] at h
  exact h

theorem exists_elemAbelian_nine_tripleCover {U : Type*} [Group U] [Finite U]
    (hU : Group.IsPerfect U) (htc : Sec4.IsTripleCover U (alternatingGroup (Fin 6))) :
    ∃ E : Subgroup U, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU1080 := card_tripleCover htc
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := U) 3 (n := 3)
    (by rw [hU1080]; norm_num)
  have hH27 : Nat.card H = 27 := by rw [hH]; norm_num
  have hHp : IsPGroup 3 H := IsPGroup.of_card hH
  have hidx : ¬ 3 ∣ H.index := by
    have h := H.card_mul_index
    rw [hU1080, hH27] at h
    omega
  obtain ⟨z, hzZ, hz1, hz3⟩ := KFacts.K412.exists_ne_one_of_card_eq_three htc.1
  have hnc := KFacts.K412.not_isMulCommutative_sylow hU.commutator_eq_top hzZ hz1 hz3
    (hHp.toSylow hidx)
  rw [IsPGroup.toSylow_coe] at hnc
  obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine_of_card_eq (P := H) hH27 hnc
  exact ⟨E.map H.subtype, CFSG.SectionRank.isElemAbelian_map hE _,
    by rw [Subgroup.card_map_of_injective H.subtype_injective, hE9]⟩

theorem card_le_nine_of_mulAut_tripleCover {U : Type*} [Group U] [Finite U]
    (hU : Group.IsPerfect U) (htc : Sec4.IsTripleCover U (alternatingGroup (Fin 6)))
    (F : Subgroup (MulAut U)) (hF : IsPGroup 3 F) : Nat.card F ≤ 9 := by
  obtain ⟨-, ⟨φ⟩⟩ := htc
  have := hU
  have hinj := PerfectAutomorphisms.centerQuotientHom_injective U
  have h := card_le_nine_of_mulAut_six φ (F.map (PerfectAutomorphisms.centerQuotientHom U))
    (hF.map _)
  rwa [Subgroup.card_map_of_injective hinj] at h

section J2

theorem card_le_nine_of_j2 {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) {F : Subgroup X}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card X = 604800 := (Nat.card_congr e.toEquiv).trans KFacts.KS14.card_nativeJ2
  have hF3 : IsPGroup 3 F := isPGroup_of_isElemAbelian hF
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF3
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have hdvd : 3 ^ 4 ∣ Nat.card X :=
      (Nat.pow_dvd_pow 3 h).trans (hk ▸ Subgroup.card_subgroup_dvd_card F)
    rw [hX] at hdvd
    norm_num at hdvd
  by_contra hlt
  push Not at hlt
  have hk' : k = 3 := by
    rw [hk] at hlt
    interval_cases k <;> first | rfl | (exfalso; norm_num at hlt)
  have hF27 : Nat.card F = 27 := by rw [hk, hk']; norm_num
  have hidx : ¬ 3 ∣ F.index := by
    have h := F.card_mul_index
    rw [hX, hF27] at h
    omega
  have h415 := (Sec4.Sporadic.rank3II_4_15 X ⟨e⟩ (hF3.toSylow hidx) _ rfl _ rfl).1.1
  rw [IsPGroup.toSylow_coe] at h415
  obtain ⟨⟨-, hcomm, -, hZ⟩, -, -⟩ := h415
  have hc : commutator F = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hF.1.is_comm.comm y x
  rw [hc] at hcomm
  rw [← hcomm, Subgroup.card_bot] at hZ
  omega

theorem card_le_nine_of_mulAut_j2 {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) (F : Subgroup (MulAut X))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  have hZ : Subgroup.center X = ⊥ := by
    have h := OuterAutomorphisms.center_map_equiv e
    rw [KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut X => φ g) hab
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  have hFle : F ≤ (MulAut.conj : X →* MulAut X).range := fun σ hσ =>
    Sec17.j2_mem_range_conj_of_pow_eq_one ⟨e⟩ (k := 1) (by rw [pow_one]; exact hF.2 σ hσ)
  set F' := F.comap (MulAut.conj : X →* MulAut X) with hF'
  have hmap : F'.map (MulAut.conj : X →* MulAut X) = F := Subgroup.map_comap_eq_self hFle
  have hF'ab : CFSG.Assembly.IsElemAbelian 3 F' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have := hF.1.is_comm.comm ⟨MulAut.conj (a : X), a.2⟩ ⟨MulAut.conj (b : X), b.2⟩
      have h := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h
    · rw [map_pow, map_one]
      exact hF.2 _ hx
  rw [← hmap, Subgroup.card_map_of_injective hinj]
  exact card_le_nine_of_j2 e hF'ab

theorem exists_elemAbelian_nine_j2 {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) :
    ∃ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨⟨-, -, -, -⟩, hS27, hexp⟩ := (Sec4.Sporadic.rank3II_4_15 X ⟨e⟩ S _ rfl _ rfl).1.1
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := (S : Subgroup X)) 3 (n := 2)
    (by rw [hS27]; norm_num)
  have hEab : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hE
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨hEab, fun x _ => ?_⟩
    have h := Monoid.pow_exponent_eq_one x
    rw [hexp] at h
    exact h
  exact ⟨E.map (S : Subgroup X).subtype, CFSG.SectionRank.isElemAbelian_map hE3 _,
    by rw [Subgroup.card_map_of_injective (S : Subgroup X).subtype_injective, hE]; norm_num⟩

end J2

theorem card_le_three_of_mulAut_five' {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    (F : Subgroup (MulAut X)) (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 3 :=
  card_le_three_of_mulAut_five e F (isPGroup_of_isElemAbelian hF)

theorem card_le_nine_of_mulAut_tripleCover' {U : Type*} [Group U] [Finite U]
    (hU : Group.IsPerfect U) (htc : Sec4.IsTripleCover U (alternatingGroup (Fin 6)))
    (F : Subgroup (MulAut U)) (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 :=
  card_le_nine_of_mulAut_tripleCover hU htc F (isPGroup_of_isElemAbelian hF)

end CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag
