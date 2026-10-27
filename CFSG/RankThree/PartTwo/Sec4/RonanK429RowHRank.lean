module

public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsKS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429

@[expose] def Rank3LeOne (H : Type*) [Group H] : Prop :=
  ∀ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 3

theorem isElemAbelian_of_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    {E : Subgroup A} (hf : Function.Injective (f.comp E.subtype))
    (hE : CFSG.Assembly.IsElemAbelian 3 (E.map f)) : CFSG.Assembly.IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply hf
    have hc := hE.1.is_comm.comm (⟨f x, x, x.2, rfl⟩ : E.map f) ⟨f y, y, y.2, rfl⟩
    have h' := congrArg Subtype.val hc
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      map_mul] at h' ⊢
    exact h'
  · have h3 := hE.2 (f x) ⟨x, hx, rfl⟩
    have : (f.comp E.subtype) (⟨x, hx⟩ ^ 3) = (f.comp E.subtype) 1 := by
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        SubmonoidClass.coe_pow, map_pow, map_one]
      exact h3
    have := congrArg Subtype.val (hf this)
    simpa using this

theorem isElemAbelian_of_le {B : Type*} [Group B] {E F : Subgroup B} (hFE : F ≤ E)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 F := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  have hc := congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hFE x.2⟩ : E) ⟨y, hFE y.2⟩)
  exact Subtype.ext hc

theorem isElemAbelian_map {A B : Type*} [Group A] [Group B] (f : A →* B) {E : Subgroup A}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x, a, ha, rfl⟩ := x
    obtain ⟨y, b, hb, rfl⟩ := y
    have hc := hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : E => f z.1) hc
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem natCard_map_of_injective_comp {A B : Type*} [Group A] [Group B] (f : A →* B)
    {E : Subgroup A} (hf : Function.Injective (f.comp E.subtype)) :
    Nat.card (E.map f) = Nat.card E := by
  have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup E)) hf
  rwa [← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype,
    Subgroup.card_top] at h

theorem eq_one_of_mem_isPGroup_two {A : Type*} [Group A] {T : Subgroup A} (hT : IsPGroup 2 T)
    {z : A} (hz : z ∈ T) (h9 : orderOf z ∣ 9) : z = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf z) 9 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by norm_num))
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h9)

theorem injective_comp_subtype_of_ker_le {A B : Type*} [Group A] [Group B] (f : A →* B)
    {E T : Subgroup A} (hE : Nat.card E = 9) (hT : IsPGroup 2 T) (hk : f.ker ≤ T) :
    Function.Injective (f.comp E.subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have ha' : (a : A) ∈ f.ker := ha
  have hord : orderOf (a : A) ∣ 9 := by
    rw [Subgroup.orderOf_coe, ← hE]
    exact orderOf_dvd_natCard a
  exact Subtype.ext (eq_one_of_mem_isPGroup_two hT (hk ha') hord)

theorem exists_e9_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) {E : Subgroup B}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    ∃ E' : Subgroup A, CFSG.Assembly.IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup A := E.comap f with hM
  set g : M →* B := f.comp M.subtype with hg
  have hrange : g.range = E := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype, hM]
    exact Subgroup.map_comap_eq_self_of_surjective hf E
  have hcard : Nat.card M = Nat.card g.range * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hdvd : 3 ^ 2 ∣ Nat.card M := by
    rw [hcard, hrange, h9]
    exact ⟨Nat.card g.ker, by norm_num⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  have hcardE' : Nat.card (P.map M.subtype) = 9 := by
    rw [Subgroup.card_subtype, hP]
    norm_num
  have hinj : Function.Injective (f.comp (P.map M.subtype).subtype) :=
    injective_comp_subtype_of_ker_le f hcardE' hker le_rfl
  have hle : (P.map M.subtype).map f ≤ E := by
    rintro _ ⟨_, ⟨p, _, rfl⟩, rfl⟩
    exact p.2
  exact ⟨P.map M.subtype, isElemAbelian_of_injective f hinj (isElemAbelian_of_le hle hE),
    hcardE'⟩

theorem exists_e9_of_isType429 {X : Type} [Group X] [Finite X]
    (h : IsType429 X) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine CFSG.RankThree.PartTwo.Sec15.ks153ThreeRank X ?_
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl h

theorem ker_le_pCore_two_or_eq_top
    {K H : Type} [Group K] [Finite K] [Group.IsPerfect K] [Group H]
    (hT : IsType429 (K ⧸ CFSG.pCore 2 K)) (f : K →* H) :
    f.ker ≤ CFSG.pCore 2 K ∨ f.ker = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isSimpleGroup_of_isType429 hT
  have hπs : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
    QuotientGroup.mk'_surjective _
  haveI : (f.ker.map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    Subgroup.Normal.map inferInstance _ hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (f.ker.map (QuotientGroup.mk' (CFSG.pCore 2 K))) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hsup : f.ker ⊔ CFSG.pCore 2 K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 K)) f.ker
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    by_contra hne
    have hrange : f.range = (CFSG.pCore 2 K).map f := by
      rw [MonoidHom.range_eq_map, ← hsup, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff f.ker).2 (le_refl f.ker), bot_sup_eq]
    have h2 : IsPGroup 2 f.range := by
      rw [hrange]
      exact (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).map f
    haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
    haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
    haveI : Nontrivial f.range := by
      obtain ⟨x, hx⟩ : ∃ x, x ∉ f.ker := by
        by_contra hcon
        exact hne (eq_top_iff.2 fun x _ => not_not.1 (not_exists.1 hcon x))
      refine nontrivial_of_ne (⟨f x, x, rfl⟩ : f.range) 1 fun hx1 => hx ?_
      simpa using congrArg Subtype.val hx1
    exact not_isPGroup_of_isPerfect h2

theorem false_of_ker_le_pCore_two {K H : Type} [Group K] [Finite K]
    [Group H] (hT : IsType429 (K ⧸ CFSG.pCore 2 K)) (hH : Rank3LeOne H) (f : K →* H)
    (hk : f.ker ≤ CFSG.pCore 2 K) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, h9⟩ := exists_e9_of_isType429 hT
  obtain ⟨E', hE', h9'⟩ := exists_e9_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 K))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) hE h9
  have hinj : Function.Injective (f.comp E'.subtype) :=
    injective_comp_subtype_of_ker_le f h9' CFSG.pCore_isPGroup hk
  have h3 := hH _ (isElemAbelian_map f hE')
  rw [natCard_map_of_injective_comp f hinj, h9'] at h3
  omega

theorem not_isType429_of_two_homs
    {K H₁ H₂ : Type} [Group K] [Finite K] [Group.IsPerfect K] [Group H₁] [Group H₂]
    (h₁ : Rank3LeOne H₁) (h₂ : Rank3LeOne H₂) (f₁ : K →* H₁) (f₂ : K →* H₂)
    (hinj : f₁.ker ⊓ f₂.ker = ⊥) : ¬ IsType429 (K ⧸ CFSG.pCore 2 K) := by
  intro hT
  rcases ker_le_pCore_two_or_eq_top hT f₁ with h1 | h1
  · exact false_of_ker_le_pCore_two hT h₁ f₁ h1
  · refine false_of_ker_le_pCore_two hT h₂ f₂ ?_
    rw [h1, top_inf_eq] at hinj
    rw [hinj]
    exact bot_le

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
