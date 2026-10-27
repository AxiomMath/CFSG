module

public import CFSG.Sporadic.Th.Recog.NormTBasic
public import CFSG.Sporadic.Th.Recog.CentT
public import CFSG.Sporadic.Th.Recog.DModel
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2Facts

public section

namespace CFSG.Sporadic.Th.Recog

open Subgroup CFSG.GH74.QTGen4.Recog.G23 CFSG.Sporadic.Th Native Max3 CFSG.LieType.Ree
open CFSG.Sporadic.Recognition.PresentedWords

private theorem short_rels : ∀ w ∈ ([[(0, true), (0, true)], [(2, true), (2, true)],
    [(3, true), (3, true)], [(4, true), (4, true)], [(6, true), (6, true), (6, true)],
    [(6, false), (0, false), (6, true), (0, true)], [(6, false), (2, false), (6, true), (2, true)],
    [(6, false), (3, false), (6, true), (3, true)], [(6, false), (4, false), (6, true), (4, true)],
    [(7, false), (6, true), (7, true), (6, true)]] : List (List (Fin 8 × Bool))), w ∈ R0' := by
  simp only [R0', TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
    TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.relatorsTwo,
    TauCeti.Sporadic.Thompson.relatorsThree, TauCeti.Sporadic.Thompson.relatorsFour,
    TauCeti.Sporadic.Thompson.relatorsFive, TauCeti.Sporadic.Thompson.relatorsSix,
    TauCeti.Sporadic.Thompson.genA, TauCeti.Sporadic.Thompson.genB,
    TauCeti.Sporadic.Thompson.genC, TauCeti.Sporadic.Thompson.genD,
    TauCeti.Sporadic.Thompson.genE, TauCeti.Sporadic.Thompson.genS,
    TauCeti.Sporadic.Thompson.genT, TauCeti.Sporadic.Thompson.genU,
    TauCeti.Relator.toWord_gen, TauCeti.Relator.toWord_pow, TauCeti.Relator.toWord_mul,
    TauCeti.Relator.toWord_inv, TauCeti.Relator.toWord_div, TauCeti.Relator.toWord_conj,
    TauCeti.Relator.toWord_commInvInv, List.map_cons, List.map_append, List.map_nil]
  decide

section GhatCenter


theorem eq_one_of_forall_commute {X : Type*} [Group X] {K : Subgroup X} (β : ↥K ≃* Ghat) :
    ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1 := by
  intro k hk hcomm
  have hc : β ⟨k, hk⟩ ∈ Subgroup.center Ghat := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := β.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg β (Subtype.ext (hcomm x x.2).symm)
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := ZMod 3)] at hc
  have h1 : (⟨k, hk⟩ : ↥K) = 1 := β.injective (by rw [Subgroup.mem_bot.mp hc, map_one])
  exact congrArg Subtype.val h1

end GhatCenter

section Ghat


theorem exists_conj_mul_of_not_inner {K : Type*} [Group K] (β : K ≃* Ghat) (σ₁ σ₂ : MulAut K)
    (h₁ : ∀ g : K, σ₁ ≠ MulAut.conj g) (h₂ : ∀ g : K, σ₂ ≠ MulAut.conj g) :
    ∃ g : K, σ₁ = MulAut.conj g * σ₂ := by
  let β' : K ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup ReeTag.G2.tag (ZMod 3)) := β
  have key : ∀ σ : MulAut K, (∀ g : K, σ ≠ MulAut.conj g) →
      ∃ g, ∀ x : K, β' (σ x) = g * ReeTag.G2.finiteExceptionalAut (ZMod 3) (β' x) * g⁻¹ := by
    intro σ hσ
    have hτ : ∀ y, (β'.symm.trans (σ.trans β')) y = β' (σ (β'.symm y)) := fun y => rfl
    rcases CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.aut_cases (K := ZMod 3)
      (by rw [Nat.card_zmod]) (β'.symm.trans (σ.trans β')) with ⟨g, hg⟩ | ⟨g, hg⟩
    · exfalso
      apply hσ (β'.symm g)
      ext x
      have h1 := congrArg (fun α => α (β' x)) hg
      simp only [hτ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
      rw [MulAut.conj_apply]
      apply β'.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · refine ⟨g, fun x => ?_⟩
      have h1 := congrArg (fun α => α (β' x)) hg
      simp only [hτ, MulEquiv.symm_apply_apply, MulAut.mul_apply, MulAut.conj_apply] at h1
      exact h1
  obtain ⟨g₁, hg₁⟩ := key σ₁ h₁
  obtain ⟨g₂, hg₂⟩ := key σ₂ h₂
  refine ⟨β'.symm (g₁ * g₂⁻¹), ?_⟩
  ext x
  apply β'.injective
  rw [hg₁, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hg₂,
    MulEquiv.apply_symm_apply]
  group

theorem exists_mul_conj_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K₁ : Subgroup G₁}
    {K₂ : Subgroup G₂} (β : ↥K₂ ≃* Ghat) (α : ↥K₁ ≃* ↥K₂) {u₁ : G₁} {u₂ : G₂}
    (hn₁ : u₁ ∈ normalizer (K₁ : Set G₁)) (hn₂ : u₂ ∈ normalizer (K₂ : Set G₂))
    (h₁ : ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, u₁ * x * u₁⁻¹ = k * x * k⁻¹)
    (h₂ : ¬ ∃ k ∈ K₂, ∀ x ∈ K₂, u₂ * x * u₂⁻¹ = k * x * k⁻¹) :
    ∃ g ∈ K₂, ∀ x y : ↥K₁, (y : G₁) = u₁ * x * u₁⁻¹ →
      (α y : G₂) = (g * u₂) * (α x : G₂) * (g * u₂)⁻¹ := by
  let σ₂ : MulAut ↥K₂ := K₂.normalizerMonoidHom ⟨u₂, hn₂⟩
  let c₁ : MulAut ↥K₁ := K₁.normalizerMonoidHom ⟨u₁, hn₁⟩
  let σ₁ : MulAut ↥K₂ := α.symm.trans (c₁.trans α)
  have hσ₂ : ∀ x : ↥K₂, (σ₂ x : G₂) = u₂ * x * u₂⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K₂ ⟨u₂, hn₂⟩ x
  have hc₁ : ∀ x : ↥K₁, (c₁ x : G₁) = u₁ * x * u₁⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K₁ ⟨u₁, hn₁⟩ x
  have h₂' : ∀ g : ↥K₂, σ₂ ≠ MulAut.conj g := by
    intro g hg
    apply h₂
    refine ⟨g, g.2, fun x hx => ?_⟩
    have h := congrArg (fun σ : MulAut ↥K₂ => ((σ ⟨x, hx⟩ : ↥K₂) : G₂)) hg
    simp only [hσ₂, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have h₁' : ∀ g : ↥K₂, σ₁ ≠ MulAut.conj g := by
    intro g hg
    apply h₁
    refine ⟨(α.symm g : G₁), (α.symm g).2, fun x hx => ?_⟩
    have h := congrArg (fun σ : MulAut ↥K₂ => α.symm (σ (α ⟨x, hx⟩))) hg
    simp only [σ₁, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv] at h
    have h' := congrArg Subtype.val h
    simp only [hc₁, Subgroup.coe_mul, Subgroup.coe_inv] at h'
    exact h'
  obtain ⟨g, hg⟩ := exists_conj_mul_of_not_inner β σ₁ σ₂ h₁' h₂'
  refine ⟨g, g.2, fun x y hy => ?_⟩
  have hy' : y = c₁ x := Subtype.ext (by rw [hc₁]; exact hy)
  have h := congrArg (fun σ : MulAut ↥K₂ => ((σ (α x) : ↥K₂) : G₂)) hg
  simp only [σ₁, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply,
    MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hσ₂] at h
  rw [hy', h]
  group

end Ghat

variable {G : Type} [Group G] [Finite G]

section Core


theorem ThCore.u_not_inner (C : ThCore G) {tM uM : ↥Max3.M} (htM : orderOf tM = 3)
    (huM : uM * tM * uM⁻¹ = tM⁻¹)
    (hcount : ¬ 8 ∣ Nat.card {x : ↥(Subgroup.normalizer (Subgroup.zpowers tM : Set ↥Max3.M)) //
      x ^ 2 = 1})
    {K : Subgroup G} (hinf : K ⊓ Subgroup.zpowers (C.ψ tM : G) = ⊥)
    (hsup : K ⊔ Subgroup.zpowers (C.ψ tM : G) = Subgroup.centralizer ({(C.ψ tM : G)} : Set G))
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1) :
    ¬ ∃ k ∈ K, ∀ x ∈ K, (C.ψ uM : G) * x * (C.ψ uM : G)⁻¹ = k * x * k⁻¹ :=
  not_inner_of_not_dvd C.psiG_injective C.psiG_range C.orderOf_z htM huM hcount hinf hsup hZ

end Core

section TwoCores


theorem exists_normT_mulEquiv {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (C₁ : ThCore G₁) (C₂ : ThCore G₂) {tM uM : ↥Max3.M} (htM : orderOf tM = 3)
    (huM : uM * tM * uM⁻¹ = tM⁻¹)
    (hcount : ¬ 8 ∣ Nat.card {x : ↥(Subgroup.normalizer (Subgroup.zpowers tM : Set ↥Max3.M)) //
      x ^ 2 = 1})
    {K₁ : Subgroup G₁} (hinf₁ : K₁ ⊓ Subgroup.zpowers (C₁.ψ tM : G₁) = ⊥)
    (hsup₁ : K₁ ⊔ Subgroup.zpowers (C₁.ψ tM : G₁) =
      Subgroup.centralizer ({(C₁.ψ tM : G₁)} : Set G₁))
    (hK₁ : K₁ = ⁅Subgroup.centralizer ({(C₁.ψ tM : G₁)} : Set G₁),
      Subgroup.centralizer ({(C₁.ψ tM : G₁)} : Set G₁)⁆)
    (he₁ : Nonempty (↥K₁ ≃* Ghat))
    {K₂ : Subgroup G₂} (hinf₂ : K₂ ⊓ Subgroup.zpowers (C₂.ψ tM : G₂) = ⊥)
    (hsup₂ : K₂ ⊔ Subgroup.zpowers (C₂.ψ tM : G₂) =
      Subgroup.centralizer ({(C₂.ψ tM : G₂)} : Set G₂))
    (hK₂ : K₂ = ⁅Subgroup.centralizer ({(C₂.ψ tM : G₂)} : Set G₂),
      Subgroup.centralizer ({(C₂.ψ tM : G₂)} : Set G₂)⁆)
    (he₂ : Nonempty (↥K₂ ≃* Ghat)) :
    ∃ ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (C₁.ψ tM : G₁) : Set G₁)) ≃*
        ↥(Subgroup.normalizer (Subgroup.zpowers (C₂.ψ tM : G₂) : Set G₂)),
      (∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (C₁.ψ tM : G₁) : Set G₁)),
        (y : G₁) = C₁.ψ tM → (ψ' y : G₂) = C₂.ψ tM) ∧
      ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (C₁.ψ tM : G₁) : Set G₁)),
        (y : G₁) ∈ K₁ ↔ (ψ' y : G₂) ∈ K₂ := by
  obtain ⟨β₁⟩ := he₁
  obtain ⟨β₂⟩ := he₂
  have ht₁ : orderOf (C₁.ψ tM : G₁) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have ht₂ : orderOf (C₂.ψ tM : G₂) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hu₁ : (C₁.ψ uM : G₁) * (C₁.ψ tM : G₁) * (C₁.ψ uM : G₁)⁻¹ = (C₁.ψ tM : G₁)⁻¹ := by
    have h := congrArg (fun m => (C₁.ψ m : G₁)) huM
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hu₂ : (C₂.ψ uM : G₂) * (C₂.ψ tM : G₂) * (C₂.ψ uM : G₂)⁻¹ = (C₂.ψ tM : G₂)⁻¹ := by
    have h := congrArg (fun m => (C₂.ψ m : G₂)) huM
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hn₁ : (C₁.ψ uM : G₁) ∈ normalizer (K₁ : Set G₁) := by
    rw [hK₁]
    exact mem_normalizer_commutator_centralizer ht₁
      ((mem_normalizer_zpowers_iff ht₁).2 (Or.inr hu₁))
  have hn₂ : (C₂.ψ uM : G₂) ∈ normalizer (K₂ : Set G₂) := by
    rw [hK₂]
    exact mem_normalizer_commutator_centralizer ht₂
      ((mem_normalizer_zpowers_iff ht₂).2 (Or.inr hu₂))
  have hZ₂ := eq_one_of_forall_commute β₂
  obtain ⟨g, hgK, hg⟩ := exists_mul_conj_eq β₂ (β₁.trans β₂.symm) hn₁ hn₂
    (C₁.u_not_inner htM huM hcount hinf₁ hsup₁ (eq_one_of_forall_commute β₁))
    (C₂.u_not_inner htM huM hcount hinf₂ hsup₂ hZ₂)
  have hgt : g * (C₂.ψ tM : G₂) = (C₂.ψ tM : G₂) * g :=
    (Subgroup.mem_centralizer_singleton_iff.mp ((hsup₂ ▸ le_sup_left : K₂ ≤ _) hgK))
  have hs : (g * (C₂.ψ uM : G₂)) * (C₂.ψ tM : G₂) * (g * (C₂.ψ uM : G₂))⁻¹ =
      (C₂.ψ tM : G₂)⁻¹ := by
    have hgt' : g * (C₂.ψ tM : G₂)⁻¹ * g⁻¹ = (C₂.ψ tM : G₂)⁻¹ := by
      rw [(Commute.inv_right hgt).eq, mul_inv_cancel_right]
    calc (g * (C₂.ψ uM : G₂)) * (C₂.ψ tM : G₂) * (g * (C₂.ψ uM : G₂))⁻¹
        = g * ((C₂.ψ uM : G₂) * (C₂.ψ tM : G₂) * (C₂.ψ uM : G₂)⁻¹) * g⁻¹ := by group
      _ = (C₂.ψ tM : G₂)⁻¹ := by rw [hu₂, hgt']
  have hsn : g * (C₂.ψ uM : G₂) ∈ normalizer (K₂ : Set G₂) :=
    (normalizer (K₂ : Set G₂)).mul_mem (Subgroup.le_normalizer hgK) hn₂
  obtain ⟨φ, hφt, -, hφK⟩ := exists_normalizer_mulEquiv ht₁ ht₂ hu₁ hs hinf₁ hsup₁ hinf₂ hsup₂
    hn₁ hsn hZ₂ (β₁.trans β₂.symm) hg
  refine ⟨φ, hφt, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hφK y ⟨y, hy⟩ rfl]
    exact ((β₁.trans β₂.symm) ⟨y, hy⟩).2
  · rw [hK₂] at hy
    rw [hK₁]
    exact (mem_commutator_iff_of_mulEquiv φ hφt y).2 hy

end TwoCores

section J


theorem orderOf_hswJ_six : orderOf (hswJ 6) = 3 := by
  have h := hswJ_rel _ (short_rels [(6, true), (6, true), (6, true)] (by decide))
  simp only [wprod_cons, wprod_nil, ↓reduceIte, mul_one] at h
  have h3 : hswJ 6 ^ 3 = 1 := by rw [pow_three]; exact h
  exact orderOf_eq_prime h3 (by rw [← dJ_five]; exact dJ_five_ne_one)

theorem hswJ_seven_conj_six : hswJ 7 * hswJ 6 * (hswJ 7)⁻¹ = (hswJ 6)⁻¹ := by
  have h := hswJ_rel _ (short_rels [(7, false), (6, true), (7, true), (6, true)] (by decide))
  simp only [wprod_cons, wprod_nil, Bool.false_eq_true, ↓reduceIte, mul_one] at h
  have h' : hswJ 6 * hswJ 7 * hswJ 6 = hswJ 7 := by
    calc hswJ 6 * hswJ 7 * hswJ 6 = hswJ 7 * ((hswJ 7)⁻¹ * (hswJ 6 * (hswJ 7 * hswJ 6))) := by
          group
      _ = hswJ 7 := by rw [h, mul_one]
  calc hswJ 7 * hswJ 6 * (hswJ 7)⁻¹
      = (hswJ 6)⁻¹ * (hswJ 6 * hswJ 7 * hswJ 6) * (hswJ 7)⁻¹ := by group
    _ = (hswJ 6)⁻¹ := by rw [h']; group

theorem splitJ_of_core {tM : ↥Max3.M} (htJ : (tM : ↥J) = hswJ 6)
    (h : ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({(thCoreJ.ψ tM : ↥J)} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (thCoreJ.ψ tM : ↥J) = ⊥ ∧
      K ⊔ Subgroup.zpowers (thCoreJ.ψ tM : ↥J) =
        Subgroup.centralizer ({(thCoreJ.ψ tM : ↥J)} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({(thCoreJ.ψ tM : ↥J)} : Set ↥J),
        Subgroup.centralizer ({(thCoreJ.ψ tM : ↥J)} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat)) :
    ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
      K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
        Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat) := by
  have e : ((thCoreJ.ψ tM : ↥(Subgroup.centralizer ({thCoreJ.z} : Set ↥J))) : ↥J) = hswJ 6 :=
    htJ
  rw [e] at h
  exact h

theorem closure_lJ_eq_commutator (hsimp : IsSimpleGroup Ghat)
    (hcard : Nat.card Ghat = 7371 * 576)
    (hK₀ : Nonempty (↥(Subgroup.closure (Set.range lJ)) ≃* Ghat))
    (hJ : ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
      K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
        Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat)) :
    Subgroup.closure (Set.range lJ) = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
      Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ := by
  obtain ⟨K, -, -, -, hKc, ⟨eK⟩⟩ := hJ
  obtain ⟨e₀⟩ := hK₀
  have hK₀C : Subgroup.closure (Set.range lJ) ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (lJ_comm_t i).eq
  haveI : IsSimpleGroup ↥(Subgroup.closure (Set.range lJ)) := MulEquiv.isSimpleGroup e₀
  have hnab : ¬ IsMulCommutative ↥(Subgroup.closure (Set.range lJ)) := by
    intro h
    haveI := h
    have hp := (Group.is_simple_iff_prime_card
      (α := ↥(Subgroup.closure (Set.range lJ)))).mp inferInstance
    rw [Nat.card_congr e₀.toEquiv, hcard] at hp
    norm_num at hp
  haveI : Group.IsPerfect ↥(Subgroup.closure (Set.range lJ)) := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (commutator ↥(Subgroup.closure (Set.range lJ))) with h | h
    · exact absurd ((commutator_eq_bot_iff _).mp h) hnab
    · exact h
  have hle : Subgroup.closure (Set.range lJ) ≤ ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
      Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ := by
    rw [← Subgroup.commutator_eq_self (H := Subgroup.closure (Set.range lJ))]
    exact Subgroup.commutator_mono hK₀C hK₀C
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [← hKc, Nat.card_congr eK.toEquiv, Nat.card_congr e₀.toEquiv]

theorem dJ_mem_closure_lJ (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hK₀ : Nonempty (↥(Subgroup.closure (Set.range lJ)) ≃* Ghat))
    (hJ : ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
      K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
        Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat))
    (j : Fin 6) (h4 : j ≠ 4) (h5 : j ≠ 5) : dJ j ∈ Subgroup.closure (Set.range lJ) := by
  have hK₀eq := closure_lJ_eq_commutator hsimp hcard hK₀ hJ
  obtain ⟨K, -, hinf, hsup, hK, -⟩ := hJ
  rw [hK₀eq, ← hK]
  have key : ∀ i : Fin 8, [(i, true), (i, true)] ∈ R0' →
      [(6, false), (i, false), (6, true), (i, true)] ∈ R0' → hswJ i ∈ K := by
    intro i h2 hc
    have hsq := hswJ_rel _ h2
    have hcm := hswJ_rel _ hc
    simp only [wprod_cons, wprod_nil, Bool.false_eq_true, ↓reduceIte, mul_one] at hsq hcm
    refine mem_of_mem_centralizer_of_pow_eq_one (n := 2) orderOf_hswJ_six hinf hsup ?_
      (by rw [pow_two]; exact hsq) (by norm_num)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc hswJ i * hswJ 6
        = hswJ i * hswJ 6 * ((hswJ 6)⁻¹ * ((hswJ i)⁻¹ * (hswJ 6 * hswJ i))) := by
          rw [hcm, mul_one]
      _ = hswJ 6 * hswJ i := by group
  fin_cases j
  · exact key 0 (short_rels _ (by decide)) (short_rels _ (by decide))
  · exact key 2 (short_rels _ (by decide)) (short_rels _ (by decide))
  · exact key 3 (short_rels _ (by decide)) (short_rels _ (by decide))
  · exact key 4 (short_rels _ (by decide)) (short_rels _ (by decide))
  · exact (h4 rfl).elim
  · exact (h5 rfl).elim

end J

section JD


theorem M_inf_normalizer_eq_DJ {tM : ↥Max3.M} (htJ : (tM : ↥J) = hswJ 6)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728) :
    Max3.M ⊓ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J) = DJ := by
  have htM : orderOf tM = 3 := by rw [← Subgroup.orderOf_coe, htJ, orderOf_hswJ_six]
  have huM : (⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩ : ↥Max3.M) * tM *
      (⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩ : ↥Max3.M)⁻¹ = tM⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, htJ, hswJ_seven_conj_six])
  have hmap := map_normalizer_zpowers_of_injective (f := Max3.M.subtype)
    Max3.M.subtype_injective htM
  rw [Subgroup.range_subtype, Subgroup.coe_subtype, htJ] at hmap
  have hcard : Nat.card ↥(Max3.M ⊓ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) =
      3456 := by
    rw [← hmap, Subgroup.card_map_of_injective Max3.M.subtype_injective,
      card_normalizer_zpowers_eq_two_mul htM huM, hCt]
  symm
  apply Subgroup.eq_of_le_of_card_ge (le_inf DJ_le_M DJ_le_normalizer)
  rw [hcard, card_DJ]

theorem card_sq_eq_one_normalizer_tM {tM : ↥Max3.M} (htJ : (tM : ↥J) = hswJ 6)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728) :
    Nat.card {x : ↥(Subgroup.normalizer (Subgroup.zpowers tM : Set ↥Max3.M)) // x ^ 2 = 1} =
      164 := by
  have htM : orderOf tM = 3 := by rw [← Subgroup.orderOf_coe, htJ, orderOf_hswJ_six]
  have hmap := map_normalizer_zpowers_of_injective (f := Max3.M.subtype)
    Max3.M.subtype_injective htM
  rw [Subgroup.range_subtype, Subgroup.coe_subtype, htJ, M_inf_normalizer_eq_DJ htJ hCt] at hmap
  have e : ↥(Subgroup.normalizer (Subgroup.zpowers tM : Set ↥Max3.M)) ≃* ↥DJ :=
    (Subgroup.equivMapOfInjective _ Max3.M.subtype Max3.M.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have h1 : Nat.card {x : ↥(Subgroup.normalizer (Subgroup.zpowers tM : Set ↥Max3.M)) //
      x ^ 2 = 1} = Nat.card {x : ↥DJ // x ^ 2 = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ e x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [h1]
  exact card_sq_eq_one_DJ

end JD

section JGhat


theorem exists_normT_iso (C : ThCore G) {tM : ↥Max3.M} (htJ : (tM : ↥J) = hswJ 6)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hK₀ : Nonempty (↥(Subgroup.closure (Set.range lJ)) ≃* Ghat))
    (hJ : ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
      K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
        Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat))
    (hG : ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K ⊓ Subgroup.zpowers (C.ψ tM : G) = ⊥ ∧
      K ⊔ Subgroup.zpowers (C.ψ tM : G) = Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K = ⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
        Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ ∧
      Nonempty (↥K ≃* Ghat)) :
    ∃ ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
        ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tM : G) : Set G)),
      (∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) = hswJ 6 → (ψ' y : G) = C.ψ tM) ∧
      ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) ∈ Subgroup.closure (Set.range lJ) ↔
          (ψ' y : G) ∈ ⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
            Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ := by
  have htM : orderOf tM = 3 := by rw [← Subgroup.orderOf_coe, htJ, orderOf_hswJ_six]
  have hK₀eq := closure_lJ_eq_commutator hsimp hcard hK₀ hJ
  have hcount : ¬ 8 ∣ Nat.card {x : ↥(Subgroup.normalizer (Subgroup.zpowers tM :
      Set ↥Max3.M)) // x ^ 2 = 1} := by
    rw [card_sq_eq_one_normalizer_tM htJ hCt]
    decide
  have huM : (⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩ : ↥Max3.M) * tM *
      (⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩ : ↥Max3.M)⁻¹ = tM⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, htJ, hswJ_seven_conj_six])
  obtain ⟨KJ, -, hinfJ, hsupJ, hKJ, heJ⟩ := hJ
  obtain ⟨KG, -, hinfG, hsupG, hKG, heG⟩ := hG
  have e : ((thCoreJ.ψ tM : ↥(Subgroup.centralizer ({thCoreJ.z} : Set ↥J))) : ↥J) = hswJ 6 :=
    htJ
  rw [← e] at hinfJ hsupJ hKJ hK₀eq ⊢
  obtain ⟨ψ', h1, h2⟩ := exists_normT_mulEquiv thCoreJ C htM huM hcount hinfJ hsupJ hKJ heJ
    hinfG hsupG hKG heG
  refine ⟨ψ', h1, fun y => ?_⟩
  rw [hK₀eq, ← hKJ, ← hKG]
  exact h2 y

end JGhat

section JIota


theorem exists_iota (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hK₀ : Nonempty (↥(Subgroup.closure (Set.range lJ)) ≃* Ghat))
    (hJ : ∃ K : Subgroup ↥J, K ≤ Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
      K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set ↥J) ∧
      K = ⁅Subgroup.centralizer ({hswJ 6} : Set ↥J),
        Subgroup.centralizer ({hswJ 6} : Set ↥J)⁆ ∧
      Nonempty (↥K ≃* Ghat)) :
    ∃ ι : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
        ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) ∈ Subgroup.closure (Set.range lJ) → ι y = y) ∧
      (∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) = hswJ 6 → (ι y : ↥J) = (hswJ 6)⁻¹) ∧
      ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
        (y : ↥J) = hswJ 7 → ι y = y := by
  have ht := orderOf_hswJ_six
  have hK₀eq := closure_lJ_eq_commutator hsimp hcard hK₀ hJ
  obtain ⟨K, -, hinf, hsup, hK, -⟩ := hJ
  obtain ⟨e₀⟩ := hK₀
  rw [← hK₀eq] at hK
  subst hK
  have hn : hswJ 7 ∈ normalizer ((Subgroup.closure (Set.range lJ) : Subgroup ↥J) : Set ↥J) := by
    rw [hK₀eq]
    exact mem_normalizer_commutator_centralizer ht
      ((mem_normalizer_zpowers_iff ht).2 (Or.inr hswJ_seven_conj_six))
  exact exists_inv_mulEquiv ht hswJ_seven_conj_six hinf hsup hn (eq_one_of_forall_commute e₀)

end JIota

end CFSG.Sporadic.Th.Recog
