module

public import CFSG.Quasithin.Background.G2A5Six

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
  CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

theorem card_inf_eq_card_mul_relIndex {U V VL A S₂ : Subgroup G} (hS₂ : S₂ = VL ⊔ A) (hAU : A ≤ U)
    (hVVL : V ≤ VL) (hVU : V ≤ U) (hVLU : ∀ x ∈ VL, x ∈ U → x ∈ V)
    (hSnorm : S₂ ≤ Subgroup.normalizer (VL : Set G)) :
    Nat.card ↥(U ⊓ S₂) = Nat.card ↥V * VL.relIndex S₂ := by
  have hVLS₂ : VL ≤ S₂ := by rw [hS₂]; exact le_sup_left
  have hAS₂ : A ≤ S₂ := by rw [hS₂]; exact le_sup_right
  have hnorm : (VL.subgroupOf S₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVLS₂).2 hSnorm
  let f : ↥(U ⊓ S₂) →* ↥S₂ ⧸ VL.subgroupOf S₂ :=
    (QuotientGroup.mk' (VL.subgroupOf S₂)).comp (Subgroup.inclusion (inf_le_right : U ⊓ S₂ ≤ S₂))
  have hker : f.ker = V.subgroupOf (U ⊓ S₂) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (VL.subgroupOf S₂) (Subgroup.inclusion (inf_le_right : U ⊓ S₂ ≤ S₂) x)
      = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hVLU _ h (Subgroup.mem_inf.1 x.2).1
    · intro h
      exact hVVL h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hAnorm : A ≤ Subgroup.normalizer (VL : Set G) := fun a ha => hSnorm (hAS₂ ha)
    have hmulA := Subgroup.coe_mul_of_left_le_normalizer_right A VL hAnorm
    have hs : (s : G) ∈ (↑(A ⊔ VL) : Set G) := by
      rw [sup_comm, ← hS₂]
      exact s.2
    rw [hmulA] at hs
    obtain ⟨a, ha, v, hv, hav⟩ := Set.mem_mul.1 hs
    have hmem : a ∈ U ⊓ S₂ := Subgroup.mem_inf.2 ⟨hAU ha, hAS₂ ha⟩
    refine ⟨⟨a, hmem⟩, ?_⟩
    show QuotientGroup.mk' (VL.subgroupOf S₂)
      (Subgroup.inclusion (inf_le_right : U ⊓ S₂ ≤ S₂) ⟨a, hmem⟩) = QuotientGroup.mk s
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (a : G)⁻¹ * (s : G) = v := by rw [← hav]; group
    show (a : G)⁻¹ * (s : G) ∈ VL
    rw [e]
    exact hv
  have h1 := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = VL.relIndex S₂ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    rfl
  rw [h2, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_inf hVU (hVVL.trans hVLS₂))).toEquiv] at h1
  exact h1.symm

namespace NatData5

variable {L K V V₁ : Subgroup G} (D : NatData5 L K (conjClosure V₁ L) V V₁)

include D

theorem card_V (hV : V = ⁅conjClosure V₁ L, lOne L V₁⁆) : Nat.card ↥V = 8 := by
  have hVVL := D.V_le_VL hV
  let f : ↥V → {x : ↥Ev // (x : Fin 5 → ZMod 2) 4 = 0} := fun v =>
    ⟨Multiplicative.toAdd (D.ψ ⟨v, hVVL v.2⟩), (D.hV ⟨v, hVVL v.2⟩).1 v.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v v' h
      have h1 := congrArg Subtype.val h
      have h2 := Multiplicative.toAdd.injective h1
      have h3 := D.ψ.injective h2
      have h4 : (v : G) = (v' : G) := congrArg (fun z : ↥(conjClosure V₁ L) => (z : G)) h3
      exact Subtype.ext h4
    · rintro ⟨x, hx⟩
      obtain ⟨v, hv⟩ := D.ψ.surjective (Multiplicative.ofAdd x)
      have hvV : (v : G) ∈ V := (D.hV v).2 (by rw [hv]; exact hx)
      refine ⟨⟨v, hvV⟩, ?_⟩
      apply Subtype.ext
      show Multiplicative.toAdd (D.ψ ⟨(v : G), hVVL hvV⟩) = x
      have : (⟨(v : G), hVVL hvV⟩ : conjClosure V₁ L) = v := Subtype.ext rfl
      rw [this, hv]
      rfl
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide

end NatData5

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem card_V : Nat.card ↥V = 8 := S.D.card_V S.hyp.V_eq

theorem card_U_eq {U I Sx W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : Sx = pCoreOf 2 I) (hW : W = U ⊓ Sx) : Nat.card ↥U = Nat.card ↥W * 4 := by
  have hI'' : I = L ⊔ conjClosure V H := by
    rw [hI, hU]
    exact S.G24_two_aux hg hgN
  obtain ⟨hIle, hSxO, -, -, -⟩ := sx_facts_gen hI'' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  rw [← hS] at hSxO
  have hWU : W ≤ U := by rw [hW]; exact inf_le_left
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left
  subst hU
  have hker : S.betaU.ker = W.subgroupOf (conjClosure V H) := by
    ext u
    rw [MonoidHom.mem_ker, S.betaU_eq_one_iff, Subgroup.mem_subgroupOf, hW, Subgroup.mem_inf]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      rw [hS]
      exact mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hUI u.2) hu
    · rintro ⟨-, hu⟩
      exact hSxO hu
  have h1 := Subgroup.card_ker_mul_card_range S.betaU
  rw [hker, show S.betaU.range = K4 from S.Ubar_eq_K4, card_K4,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv] at h1
  exact h1.symm

theorem card_formula {U I Sx W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : Sx = pCoreOf 2 I) (hW : W = U ⊓ Sx)
    (hG13 : Theorem_G_1_3 (GaloisField 2 2) 2 (le_refl 2)) :
    ∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I Sx Sx
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ∧
      Nat.card ↥U = 2 ^ (2 * s + 5) *
        (conjClosure V₁ L).relIndex (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) := by
  obtain ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, -, hWcard, -, -, -⟩ :=
    S.sum_natural hU hg hgN hI hS hW rfl rfl hG13
  refine ⟨s, ⟨β, φ, hβs, hβk, hφs, hφk, hφe⟩, ?_⟩
  have h1 := S.card_U_eq hU hg hgN hI hS hW
  have hV := S.card_V
  have hVU : V ≤ U := by rw [hU]; exact le_conjClosure V H
  have hVLU : ∀ x ∈ conjClosure V₁ L, x ∈ U → x ∈ V := fun x hx hxU =>
    S.inf_le_V hx (hU ▸ hxU)
  have hSnorm : conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤
      Subgroup.normalizer (conjClosure V₁ L : Set G) := by
    have four := S.series_facts hg hgN
    rw [← hU] at four
    obtain ⟨-, h2, -, h4, -, -, -⟩ := four
    exact (h2.trans (pCoreOf_le 2 _)).trans h4
  have h3 := card_inf_eq_card_mul_relIndex (V := V) (VL := conjClosure V₁ L)
    (A := U ⊓ rconj U g) (S₂ := conjClosure V₁ L ⊔ (U ⊓ rconj U g)) rfl inf_le_left
    S.V_le_VL hVU hVLU hSnorm
  have hF : Nat.card (GaloisField 2 2) = 4 := card_gf4
  rw [h1, hWcard, h3, hV, hF]
  have h4 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by
    rw [pow_mul]
    norm_num
  rw [h4]
  ring

end A5SettingCore

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_seven {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S)
    (hG13 : Theorem_G_1_3 (GaloisField 2 2) 2 (le_refl 2)) :
    ∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ∧
      Nat.card ↥U = 2 ^ (2 * s + 5) *
        (conjClosure V₁ L).relIndex (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let St : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  exact St.card_formula hU hg hgN hI hS hW hG13

end AlmostSpecialA5Core

end CFSG.Quasithin
