module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterBase
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Cover
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model
public import Certificates.Certificate185002

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.AGLEmbedding.ChevOuter (Pr Rep mulP oneP wordP wordAut phiT)
open CFSG.AGLEmbedding.ChevOuter (rep_wordP rep_ext)
open CFSG.RankThree.PartTwo.Sec4.Item434D42 (lineGroup)
open CFSG.RankThree.PartTwo.Sec19.TrialityTwo (sGrp card_sGrp exists_rep_of_mem_sGrp rep_commP
  exists_conj_le_sylow factorization_three_aut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem centerCheck_parts (h : HuppertD4Q2.centerCheck () = true) :
    HuppertD4Q2.sylowCheck () = true ∧ (HuppertD4Q2.centralP ()).length = 3 ∧
      ∀ z ∈ HuppertD4Q2.centralP (), z.2 = 0 := by
  simp only [HuppertD4Q2.centerCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem mem_centralP {p : Pr} :
    p ∈ HuppertD4Q2.centralP () ↔ p ∈ HuppertD4Q2.sElems () ∧
      ∀ g ∈ HuppertD4Q2.sGenP (), HuppertD4Q2.commP p g = true := by
  simp only [HuppertD4Q2.centralP, List.mem_filter, List.all_eq_true]

private theorem wordAut_sWordA_mem : wordAut HuppertD4Q2.sWordA ∈ sGrp :=
  Subgroup.subset_closure (by simp)

private theorem wordAut_sWordB_mem : wordAut HuppertD4Q2.sWordB ∈ sGrp :=
  Subgroup.subset_closure (by simp)

private theorem wordAut_sWordC_mem : wordAut HuppertD4Q2.sWordC ∈ sGrp :=
  Subgroup.subset_closure (by simp)

private theorem exists_centralP_of_central (hZ : Subgroup.center lineGroup = ⊥)
    (hsyl : HuppertD4Q2.sylowCheck () = true) {x : MulAut lineGroup} (hx : x ∈ sGrp)
    (hc : ∀ y ∈ sGrp, x * y = y * x) : ∃ p ∈ HuppertD4Q2.centralP (), Rep p x := by
  obtain ⟨p, hp, hpx⟩ := exists_rep_of_mem_sGrp hsyl hx
  refine ⟨p, mem_centralP.mpr ⟨hp, fun g hg => ?_⟩, hpx⟩
  simp only [HuppertD4Q2.sGenP, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact (rep_commP hZ hpx (rep_wordP HuppertD4Q2.sWordA)).mpr (hc _ wordAut_sWordA_mem)
  · exact (rep_commP hZ hpx (rep_wordP HuppertD4Q2.sWordB)).mpr (hc _ wordAut_sWordB_mem)
  · exact (rep_commP hZ hpx (rep_wordP HuppertD4Q2.sWordC)).mpr (hc _ wordAut_sWordC_mem)

theorem center_sGrp (hZ : Subgroup.center lineGroup = ⊥) (h : HuppertD4Q2.centerCheck () = true) :
    (∀ x ∈ sGrp, (∀ y ∈ sGrp, x * y = y * x) → x ∈ innerAut lineGroup) ∧
    (∀ E : Subgroup (MulAut lineGroup), E ≤ sGrp → (∀ x ∈ E, ∀ y ∈ sGrp, x * y = y * x) →
      Nat.card E ≤ 3) := by
  obtain ⟨hsyl, hlen, hexp⟩ := centerCheck_parts h
  refine ⟨fun x hx hc => ?_, fun E hE hEc => ?_⟩
  · obtain ⟨p, hp, hpx⟩ := exists_centralP_of_central hZ hsyl hx hc
    obtain ⟨-, -, g, -, hα⟩ := hpx
    rw [hexp p hp, pow_zero, mul_one] at hα
    exact MonoidHom.mem_range.mpr ⟨g, hα.symm⟩
  · have hex : ∀ x ∈ E, ∃ p ∈ HuppertD4Q2.centralP (), Rep p x := fun x hx =>
      exists_centralP_of_central hZ hsyl (hE hx) (hEc x hx)
    choose! ρ hρL hρ using hex
    have hinj : Function.Injective fun x : E =>
        (⟨ρ x.1, List.mem_toFinset.mpr (hρL x.1 x.2)⟩ :
          {p // p ∈ (HuppertD4Q2.centralP ()).toFinset}) := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hp : ρ x = ρ y := congrArg Subtype.val hxy
      exact Subtype.ext (rep_ext (hρ x hx) (hρ y hy) hp)
    calc Nat.card E ≤ Nat.card {p // p ∈ (HuppertD4Q2.centralP ()).toFinset} :=
          Nat.card_le_card_of_injective _ hinj
      _ = (HuppertD4Q2.centralP ()).toFinset.card := Nat.card_eq_finsetCard _
      _ ≤ (HuppertD4Q2.centralP ()).length := List.toFinset_card_le _
      _ = 3 := hlen

theorem OuterData.card_eq_of_outer (hOut : Nat.card (Outer lineGroup) = 3)
    (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312)
    {P A B : Subgroup (MulAut lineGroup)} {c : MulAut lineGroup}
    (h : OuterData lineGroup P A B c) : Nat.card P = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut lineGroup) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have hcA : c ∈ A := by
    rw [h.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcK : c ∈ P ⊔ innerAut lineGroup := Subgroup.mem_sup_left (h.le_P hcA)
  have hindex : (innerAut lineGroup).index = 3 := hOut
  have hrel := Subgroup.relIndex_mul_index
    (le_sup_right : innerAut lineGroup ≤ P ⊔ innerAut lineGroup)
  rw [hindex] at hrel
  have hKtop : P ⊔ innerAut lineGroup = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hrel) with h1 | h1
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      rw [h1] at hrel
      have hrel1 : (innerAut lineGroup).relIndex (P ⊔ innerAut lineGroup) = 1 := by omega
      exact h.outer (Subgroup.relIndex_eq_one.mp hrel1 hcK)
  have hcard := h.sylow.card_eq
  rw [hKtop, Subgroup.card_top, hAut, factorization_three_aut] at hcard
  exact hcard

theorem central_of_dichotomy {G : Type} [Group G] {P A B : Subgroup G} {c : G}
    (hP : Nat.card P = 3 ^ 5) (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hAP : A ≤ P)
    (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hsup : A = Subgroup.zpowers c ⊔ B) (hc : c ∉ B)
    (hd : (∀ x ∈ P, x * c = c * x) ∨
      ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
        ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set G), x * c * x⁻¹ = b * c)) :
    (∀ x ∈ P, x * c = c * x) ∨ (∀ x ∈ P, ∀ b ∈ B, x * b = b * x) := by
  rcases hd with h1 | ⟨-, h3⟩
  · exact Or.inl h1
  refine Or.inr ?_
  haveI : Inhabited G := ⟨1⟩
  have hcA : c ∈ A := by
    rw [hsup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAQ : A ≤ P ⊓ Subgroup.centralizer (B : Set G) := by
    intro a ha
    exact Subgroup.mem_inf.mpr
      ⟨hAP ha, Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b (hBA hb) a ha⟩
  choose! σ hσQ hσc using h3
  let ψ : ↥B × ↥A → ↥(P ⊓ Subgroup.centralizer (B : Set G)) := fun p =>
    ⟨σ p.1.1 * p.2.1, mul_mem (hσQ p.1.1 p.1.2) (hAQ p.2.2)⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ ⟨⟨b', hb'⟩, ⟨a', ha'⟩⟩ hEq
    have hEq' : σ b * a = σ b' * a' := congrArg Subtype.val hEq
    obtain ⟨k, hk_def⟩ : ∃ k, k = a' * a⁻¹ := ⟨_, rfl⟩
    have hk : k ∈ A := by
      rw [hk_def]
      exact mul_mem ha' (inv_mem ha)
    have hkc : k * c = c * k := hcomm k hk c hcA
    have hsb : σ b = σ b' * k := by
      rw [hk_def]
      calc σ b = σ b * a * a⁻¹ := by group
        _ = σ b' * a' * a⁻¹ := by rw [hEq']
        _ = σ b' * (a' * a⁻¹) := by group
    have hbc : b * c = b' * c := by
      rw [← hσc b hb, ← hσc b' hb', hsb]
      calc σ b' * k * c * (σ b' * k)⁻¹ = σ b' * (k * c) * k⁻¹ * (σ b')⁻¹ := by group
        _ = σ b' * (c * k) * k⁻¹ * (σ b')⁻¹ := by rw [hkc]
        _ = σ b' * c * (σ b')⁻¹ := by group
    have hbb : b = b' := mul_right_cancel hbc
    subst hbb
    have haa : a = a' := mul_left_cancel hEq'
    subst haa
    rfl
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hQle : P ⊓ Subgroup.centralizer (B : Set G) ≤ P := inf_le_left
  haveI : Finite ↥(P ⊓ Subgroup.centralizer (B : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hQle)
  have hcardQ : Nat.card (↥B × ↥A) ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (B : Set G)) :=
    Nat.card_le_card_of_injective ψ hψ
  rw [Nat.card_prod, hB9, hA27] at hcardQ
  have hQP : P ⊓ Subgroup.centralizer (B : Set G) = P :=
    Subgroup.eq_of_le_of_card_ge hQle (by rw [hP]; exact le_trans (by norm_num) hcardQ)
  intro x hx b hb
  have hxQ : x ∈ P ⊓ Subgroup.centralizer (B : Set G) := by
    rw [hQP]
    exact hx
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxQ).2 b hb).symm

theorem center_props_of_card (hZ : Subgroup.center lineGroup = ⊥)
    (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312) (h : HuppertD4Q2.centerCheck () = true)
    {P : Subgroup (MulAut lineGroup)} (hP3 : IsPGroup 3 P) (hP : Nat.card P = 3 ^ 5) :
    (∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ innerAut lineGroup) ∧
    (∀ E : Subgroup (MulAut lineGroup), E ≤ P → (∀ x ∈ E, ∀ y ∈ P, x * y = y * x) →
      Nat.card E ≤ 3) := by
  haveI : Finite (MulAut lineGroup) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have hsyl : HuppertD4Q2.sylowCheck () = true := (centerCheck_parts h).1
  have hS : Nat.card sGrp = 3 ^ (Nat.card (MulAut lineGroup)).factorization 3 := by
    rw [card_sGrp hZ hsyl, hAut, factorization_three_aut]
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hS hP3
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ sGrp := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  have hcard : Nat.card sGrp = Nat.card (P.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective hinj, hP, card_sGrp hZ hsyl]
  have heq : P.map (MulAut.conj g).toMonoidHom = sGrp :=
    Subgroup.eq_of_le_of_card_ge hle hcard.le
  have hsurj : ∀ w ∈ sGrp, ∃ z ∈ P, MulAut.conj g z = w := by
    intro w hw
    rw [← heq] at hw
    obtain ⟨z, hz, hzw⟩ := Subgroup.mem_map.mp hw
    exact ⟨z, hz, hzw⟩
  constructor
  · intro x hx hcx
    have hy : MulAut.conj g x ∈ sGrp := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ hx
    have hyc : ∀ w ∈ sGrp, MulAut.conj g x * w = w * MulAut.conj g x := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsurj w hw
      rw [← map_mul, ← map_mul, hcx z hz]
    have hyin := (center_sGrp hZ h).1 _ hy hyc
    have hconj := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal lineGroup).conj_mem
      _ hyin g⁻¹
    rw [inv_inv, MulAut.conj_apply] at hconj
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at hconj
    exact hconj
  · intro E hE hEc
    have hE' : E.map (MulAut.conj g).toMonoidHom ≤ sGrp := by
      rw [← heq]
      exact Subgroup.map_mono hE
    have hEc' : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ sGrp, x * y = y * x := by
      rintro _ ⟨u, hu, rfl⟩ w hw
      obtain ⟨z, hz, rfl⟩ := hsurj w hw
      show MulAut.conj g u * MulAut.conj g z = MulAut.conj g z * MulAut.conj g u
      rw [← map_mul, ← map_mul, hEc u hu z hz]
    have key := (center_sGrp hZ h).2 _ hE' hEc'
    rwa [Subgroup.card_map_of_injective hinj] at key

theorem noOuterData_lineGroup (hZ : Subgroup.center lineGroup = ⊥)
    (hOut : Nat.card (Outer lineGroup) = 3) (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312)
    (h : HuppertD4Q2.centerCheck () = true) : NoOuterData lineGroup := by
  intro P A B c hd
  have hP := hd.card_eq_of_outer hOut hAut
  obtain ⟨hin, hE⟩ := center_props_of_card hZ hAut h hd.isPGroup hP
  have hcA : c ∈ A := by
    rw [hd.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  rcases central_of_dichotomy hP hd.isElemAbelian hd.card_A hd.le_P hd.le_B hd.card_B hd.eq_sup
    hd.not_mem hd.dichotomy with hc | hB
  · exact hd.outer (hin c (hd.le_P hcA) fun y hy => (hc y hy).symm)
  · have h3 := hE B (hd.le_B.trans hd.le_P) (fun x hx y hy => (hB y hy x hx).symm)
    rw [hd.card_B] at h3
    omega

section Final

theorem noOuterData_d42 :
    ∀ (X : Type) [Group X] [Finite X], Sec4.IsSmallTwoD42 X → NoOuterData X := by
  intro X _ _ hX
  have hmod := Sec4.Item434SmallTwoIII.chevalleyExceptionalModel_of_d42 hX
  haveI : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 1 hmod).2
  obtain ⟨q, hq, hq2, hq1, ⟨e⟩⟩ := hX
  obtain ⟨⟨e'⟩, hZ, hAut⟩ :=
    Sec19.lineGroup_facts_of_isoLie q hq2 hq1 (K := X) ⟨hq, ⟨e⟩⟩
  have hOut : Nat.card (Outer lineGroup) = 3 :=
    Sec4.Item434SmallTwoIII.card_outer_d42
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e'.symm hmod)
  exact NoOuterData.of_mulEquiv e'
    (noOuterData_lineGroup hZ hOut hAut Certificates.certificate185002)

end Final

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
