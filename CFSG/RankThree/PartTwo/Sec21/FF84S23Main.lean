module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23Comp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.RankThree.PartTwo.Sec21.FF84S23KFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H]

theorem normal_centralizer_of_normal' (C : Subgroup H) [hC : C.Normal] :
    (Subgroup.centralizer (C : Set H)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have hc : g⁻¹ * y * g ∈ C := by
    have := hC.conj_mem y hy g⁻¹
    simpa using this
  have := hx _ hc
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = (g * x * g⁻¹) * y := by group

theorem comp_inCatalog (hK : KCore.KGroupNonab InCatalog H) {C : Subgroup H}
    (hCs : IsSimpleGroup C) (hnab : ∃ a b : C, a * b ≠ b * a) : InCatalog C := by
  have hN : ((⊥ : Subgroup H).subgroupOf C).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  let e : C ≃* C ⧸ (⊥ : Subgroup H).subgroupOf C :=
    mulEquivQuotientOfEqBot _ (Subgroup.bot_subgroupOf C)
  haveI : IsSimpleGroup (C ⧸ (⊥ : Subgroup H).subgroupOf C) := e.symm.isSimpleGroup
  have hnab' : ∃ a b : C ⧸ (⊥ : Subgroup H).subgroupOf C, a * b ≠ b * a :=
    KCore.nonabelian_of_mulEquiv e.symm hnab
  exact CFSG.Assembly.inCatalog_isoInvariant e (hK C ⊥ bot_le inferInstance hnab')

namespace Red3

variable {P P₁ P₂ : Subgroup H} (h : Red3 P P₁ P₂)
include h

theorem le_pPrimeCore_of_inf_bot {X : Subgroup H} [X.Normal] (hX : P ⊓ X = ⊥) :
    X ≤ pPrimeCore 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal h.toSylow X
  have hS' : Subgroup.map X.subtype (S : Subgroup X) = P ⊓ X := hS
  rw [hX] at hS'
  have hSbot : (S : Subgroup X) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hS'
  have hnd : ¬ 3 ∣ Nat.card X := fun hd => Sylow.ne_bot_of_dvd_card S hd hSbot
  exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd⟩

theorem card_comp_sylow {C : Subgroup H} (S : Sylow 3 C)
    (hS : (S : Subgroup C).map C.subtype = P ⊓ C) : Nat.card (S : Subgroup C) = Nat.card ↥(P ⊓ C) := by
  have := Nat.card_congr
    (Subgroup.equivMapOfInjective (S : Subgroup C) C.subtype C.subtype_injective).toEquiv
  rw [this, hS]

theorem comp_not_dvd_nine {C : Subgroup H} (hC : IsComponent C) (h3 : Nat.card ↥(P ⊓ C) = 3) :
    ¬ 9 ∣ Nat.card C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := h.comp_sylow hC
  have hcard : Nat.card S = 3 := (h.card_comp_sylow S hS).trans h3
  intro hd
  have := Sylow.pow_dvd_card_of_pow_dvd_card S (n := 2) (by simpa using hd)
  rw [hcard] at this
  omega

theorem comp_card_nine_false (hKF1 : FF84KF1) (hK : KCore.KGroupNonab InCatalog H)
    (hO : pPrimeCore 3 H = ⊥) {C : Subgroup H} (hC : IsComponent C)
    (h9 : Nat.card ↥(P ⊓ C) = 9) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen := h.comp_center_bot hO hC
  obtain ⟨hCs, hnab⟩ := comp_simple hC hcen
  have hcat := comp_inCatalog hK hCs hnab
  have hPC : P ≤ C := by
    have : P ⊓ C = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, h.card])
    exact inf_eq_left.1 this
  obtain ⟨S, hS⟩ := h.comp_sylow hC
  have hSeq : (S : Subgroup C) = (P ⊓ C).subgroupOf C := by
    rw [← hS]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective S).symm
  have hcardS : Nat.card S = 9 := (h.card_comp_sylow S hS).trans h9
  have hmemS : ∀ x : C, x ∈ (S : Subgroup C) ↔ (x : H) ∈ P := by
    intro x
    rw [hSeq, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hnc : ¬ IsCyclic (S : Subgroup C) := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hg3 : g ^ 3 = 1 := by
      have := h.pow_three ((hmemS g.1).1 g.2)
      exact Subtype.ext (Subtype.ext (by simpa using this))
    have hord : orderOf g = 9 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardS]
    have : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rw [hord] at this
    omega
  set P₁' : Subgroup C := P₁.subgroupOf C with hP₁'
  have hP₁'card : Nat.card P₁' = 3 := by
    rw [← h.c₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le₁.trans hPC)).toEquiv
  have hP₁'le : P₁' ≤ (S : Subgroup C) := fun x hx =>
    (hmemS x).2 (h.le₁ (Subgroup.mem_subgroupOf.1 hx))
  refine hKF1 C hCs hnab hcat S hcardS hnc P₁' hP₁'le hP₁'card ?_
  have key : ∀ m : C, m ∈ Subgroup.normalizer ((S : Subgroup C) : Set C) →
      ∀ a ∈ P₁, (m : H) * a * (m : H)⁻¹ ∈ P₁ := by
    intro m hm a ha
    have haC : a ∈ C := hPC (h.le₁ ha)
    have haS : (⟨a, haC⟩ : C) ∈ (S : Subgroup C) := (hmemS _).2 (h.le₁ ha)
    have h1 := ((Subgroup.mem_normalizer_iff.1 hm) ⟨a, haC⟩).1 haS
    have h2 : (m : H) * a * (m : H)⁻¹ ∈ P := (hmemS _).1 h1
    have := h.sc₁.2 a ha ((m : H)⁻¹) (by simpa using h2)
    simpa using this
  intro n hn
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (key n hn x.1 (Subgroup.mem_subgroupOf.1 hx))
  · have hn' : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup C) : Set C) := inv_mem hn
    have := key n⁻¹ hn' _ (Subgroup.mem_subgroupOf.1 hx)
    apply Subgroup.mem_subgroupOf.2
    simpa [mul_assoc] using this

theorem comp_card_three (hKS : FF84KSOut) (hK : KCore.KGroupNonab InCatalog H)
    (hO : pPrimeCore 3 H = ⊥) {C : Subgroup H} (hC : IsComponent C)
    (h3 : Nat.card ↥(P ⊓ C) = 3) :
    Subgroup.normalClosure (P₁ : Set H) ⊓ Subgroup.normalClosure (P₂ : Set H) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen := h.comp_center_bot hO hC
  haveI hCn : C.Normal := h.comp_normal hO hC
  obtain ⟨hCs, hnab⟩ := comp_simple hC hcen
  have hcat := comp_inCatalog hK hCs hnab
  set X : Subgroup H := Subgroup.centralizer (C : Set H) with hXdef
  haveI hXn : X.Normal := normal_centralizer_of_normal' C
  have hCX : ⁅C, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp hx) c hc).symm
  have hCXbot : C ⊓ X = ⊥ := h.comp_inf_eq_bot hcen hCX
  by_cases hR : P ⊓ X = ⊥
  · exfalso
    have hXle := h.le_pPrimeCore_of_inf_bot hR
    rw [hO, le_bot_iff] at hXle
    obtain ⟨x, hxP, hxC⟩ : ∃ x ∈ P, x ∉ C := by
      by_contra hcon
      have hcon' : ∀ x ∈ P, x ∈ C := fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩
      have : P ⊓ C = P := inf_eq_left.2 (fun x hx => hcon' x hx)
      rw [this, h.card] at h3
      omega
    let α : MulAut C := MulAut.conjNormal x
    have hα : α ^ 3 = 1 := by
      show (MulAut.conjNormal x) ^ 3 = 1
      rw [← map_pow, h.pow_three hxP, map_one]
    have h3dvd : 3 ∣ Nat.card C := by
      obtain ⟨S, hS⟩ := h.comp_sylow hC
      have := Subgroup.card_subgroup_dvd_card (S : Subgroup C)
      rwa [(h.card_comp_sylow S hS).trans h3] at this
    obtain ⟨c, hc⟩ := hKS C hCs hnab hcat h3dvd (h.comp_not_dvd_nine hC h3) α hα
    have hcx : ∀ y : C, x * (y : H) * x⁻¹ = (c : H) * y * (c : H)⁻¹ := fun y => by
      have := congrArg (fun β : MulAut C => ((β y : C) : H)) hc
      simpa [α, MulAut.conjNormal_apply, MulAut.conj_apply] using this
    have hmemX : (c : H)⁻¹ * x ∈ X := by
      rw [hXdef, Subgroup.mem_centralizer_iff]
      intro y hy
      have := hcx ⟨y, hy⟩
      calc y * ((c : H)⁻¹ * x) = (c : H)⁻¹ * ((c : H) * y * (c : H)⁻¹) * x := by group
        _ = (c : H)⁻¹ * (x * y * x⁻¹) * x := by rw [this]
        _ = ((c : H)⁻¹ * x) * y := by group
    rw [hXle, Subgroup.mem_bot, inv_mul_eq_one] at hmemX
    exact hxC (hmemX ▸ c.2)
  · have hRP : P ⊓ X ≤ P := inf_le_left
    have hQR : (P ⊓ C) ⊓ (P ⊓ X) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ C ⊓ X := ⟨hy.1.2, hy.2.2⟩
      rwa [hCXbot] at this
    have hRQ : (P ⊓ X) ⊓ (P ⊓ C) = ⊥ := by rw [inf_comm]; exact hQR
    have hRcard : Nat.card ↥(P ⊓ X) = 3 ∨ Nat.card ↥(P ⊓ X) = 9 := by
      have hd : Nat.card ↥(P ⊓ X) ∣ 9 := by
        rw [← h.card]; exact Subgroup.card_dvd_of_le hRP
      have hm : Nat.card ↥(P ⊓ X) ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h1 | h3' | h9
      · exact absurd (Subgroup.card_eq_one.1 h1) hR
      · exact Or.inl h3'
      · exact Or.inr h9
    have hR3 : Nat.card ↥(P ⊓ X) = 3 :=
      h.card_three_of_inf_bot inf_le_left inf_le_left hRQ hRcard (Or.inl h3)
    have hsup := h.sup_eq_P inf_le_left hRP h3 hR3 hQR
    obtain ⟨n, hnC, hnv⟩ := exists_inverting_of_simple C (P ⊓ C) hCs hnab inf_le_right h3
      (h.comp_relIndex hC)
    have hncen : ∀ r ∈ P ⊓ X, n * r * n⁻¹ = r := by
      intro r hr
      have := (Subgroup.mem_centralizer_iff.mp hr.2) n hnC
      rw [this]; group
    have hrefl := h.reflection h3 hR3 inf_le_left hRP hsup hnv hncen
    have hNQ : Subgroup.normalClosure ((P ⊓ C : Subgroup H) : Set H) ≤ C :=
      Subgroup.normalClosure_le_normal (fun x hx => hx.2)
    have hNR : Subgroup.normalClosure ((P ⊓ X : Subgroup H) : Set H) ≤ X :=
      Subgroup.normalClosure_le_normal (fun x hx => hx.2)
    have hbot : Subgroup.normalClosure ((P ⊓ C : Subgroup H) : Set H) ⊓
        Subgroup.normalClosure ((P ⊓ X : Subgroup H) : Set H) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ C ⊓ X := ⟨hNQ hy.1, hNR hy.2⟩
      rwa [hCXbot] at this
    rcases hrefl with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hbot
    · rw [e1, e2, inf_comm]; exact hbot

theorem no_comp_case (hO : pPrimeCore 3 H = ⊥) (hno : ∀ C : Subgroup H, ¬ IsComponent C) :
    Subgroup.normalClosure (P₁ : Set H) ⊓ Subgroup.normalClosure (P₂ : Set H) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlayer : layer H = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hno
  have hgf : generalizedFitting H = fittingSubgroup H := by
    rw [generalizedFitting.eq_sup, hlayer, sup_bot_eq]
  have hF3 : IsPGroup 3 (fittingSubgroup H) :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO
  have hFP : fittingSubgroup H ≤ P := hF3.le_sylow_of_normal h.toSylow
  have hPF : P ≤ fittingSubgroup H := by
    have hc : P ≤ Subgroup.centralizer ((fittingSubgroup H : Subgroup H) : Set H) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact h.comm (hFP hy) hx
    have := CFSG.centralizer_generalizedFitting_le H
    rw [hgf] at this
    exact hc.trans this
  have hPeq : P = fittingSubgroup H := le_antisymm hPF hFP
  haveI hPn : P.Normal := hPeq ▸ inferInstance
  have hnorm : ∀ {Q : Subgroup H}, Q ≤ P → IsStronglyClosedIn P (Q : Set H) → Q.Normal := by
    intro Q hQP hsc
    refine ⟨fun a ha g => ?_⟩
    have hmem : g * a * g⁻¹ ∈ P := hPn.conj_mem a (hQP ha) g
    have := hsc.2 a ha g⁻¹ (by simpa using hmem)
    simpa using this
  haveI h1 : P₁.Normal := hnorm h.le₁ h.sc₁
  haveI h2 : P₂.Normal := hnorm h.le₂ h.sc₂
  rw [Subgroup.normalClosure_eq_self, Subgroup.normalClosure_eq_self]
  exact h.inf

end Red3

end CFSG.RankThree.PartTwo.Sec21.FF84
