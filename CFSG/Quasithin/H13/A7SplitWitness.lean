module

public import CFSG.Quasithin.H13.A7S5S3Split
public import CFSG.Quasithin.H13.A7InvolutionSeed
public import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup Module CFSG.Quasithin.BlueprintB2
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

section ConjLin

variable (U : Subgroup G)

@[expose] def conjAddHom (n : normalizer (U : Set G)) : Additive U →+ Additive U where
  toFun w := Additive.ofMul ⟨n * (Additive.toMul w : U) * (n : G)⁻¹,
    (mem_normalizer_iff.1 n.2 _).1 (Additive.toMul w).2⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, toMul_add, Subgroup.coe_mul]
    group

theorem coe_toMul_conjAddHom (n : normalizer (U : Set G)) (w : Additive U) :
    ((Additive.toMul (conjAddHom U n w) : U) : G) = n * (Additive.toMul w : U) * (n : G)⁻¹ :=
  rfl

theorem conjAddHom_one (w : Additive U) : conjAddHom U 1 w = w := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_toMul_conjAddHom]
  simp

theorem conjAddHom_mul (n m : normalizer (U : Set G)) (w : Additive U) :
    conjAddHom U (n * m) w = conjAddHom U n (conjAddHom U m w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_toMul_conjAddHom, coe_toMul_conjAddHom, coe_toMul_conjAddHom]
  simp only [Subgroup.coe_mul, mul_inv_rev]
  group

variable [IsElementaryAbelian 2 U]

@[expose] noncomputable def conjLin :
    normalizer (U : Set G) →* (Additive U ≃ₗ[ZMod 2] Additive U) where
  toFun n := LinearEquiv.ofLinearMap ((conjAddHom U n).toZModLinearMap 2)
    ((conjAddHom U n⁻¹).toZModLinearMap 2)
    (LinearMap.ext fun w => by
      show conjAddHom U n (conjAddHom U n⁻¹ w) = w
      rw [← conjAddHom_mul, mul_inv_cancel, conjAddHom_one])
    (LinearMap.ext fun w => by
      show conjAddHom U n⁻¹ (conjAddHom U n w) = w
      rw [← conjAddHom_mul, inv_mul_cancel, conjAddHom_one])
  map_one' := LinearEquiv.ext fun w => conjAddHom_one U w
  map_mul' n m := LinearEquiv.ext fun w => conjAddHom_mul U n m w

theorem conjLin_apply (n : normalizer (U : Set G)) (w : Additive U) :
    conjLin U n w = conjAddHom U n w :=
  rfl

end ConjLin

def toMulImage (U : Subgroup G) (S : AddSubgroup (Additive U)) : Subgroup G where
  carrier := {g | ∃ w ∈ S, ((Additive.toMul w : U) : G) = g}
  mul_mem' := by
    rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ + w₂, S.add_mem hw₁ hw₂, by simp⟩
  one_mem' := ⟨0, S.zero_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, S.neg_mem hw, by simp⟩

theorem centralizer_subgroupOf_eq {X L : Subgroup G} (hXL : X ≤ L) :
    centralizer ((X.subgroupOf L : Subgroup L) : Set L) =
      (centralizer (X : Set G)).subgroupOf L := by
  ext t
  rw [mem_centralizer_iff, mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hXL hx⟩ (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hx))
  · intro h s hs
    rw [SetLike.mem_coe, mem_subgroupOf] at hs
    exact Subtype.ext (h s hs)

theorem inf_subgroupOf_eq (H K L : Subgroup G) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L := by
  ext x
  simp [mem_subgroupOf]

theorem A7_involution_local_action_data_gives_split_witness [Finite G]
    (hG : CFSG.IsEvenCharacteristic G) (T : Sylow 2 G) {e : G} (heT : e ∈ (T : Subgroup G))
    (heZ : ∀ t ∈ (T : Subgroup G), t * e = e * t) (he2 : orderOf e = 2)
    {Y M K D J Z U : Subgroup G} (hTY : (T : Subgroup G) ≤ Y)
    (hYe : Y ≤ centralizer ({e} : Set G)) (hKY : K ≤ Y) (hDY : D ≤ Y)
    (hJ : J = ⨆ (A : Subgroup G) (_ : A ≤ (T : Subgroup G) ∧ IsElementaryAbelian 2 A ∧
      ∀ B : Subgroup G, B ≤ (T : Subgroup G) → IsElementaryAbelian 2 B →
        Nat.card B ≤ Nat.card A), A)
    (hZ : Z = centerTorsion 2 (T : Subgroup G))
    (hU : U = closure {x | ∃ y ∈ Y, ∃ z ∈ Z, x = y * z * y⁻¹})
    (_hKM : ¬ K ≤ M) (hDJ : D = ⁅D, J⁆)
    (hρ : ∃ ρ : Y →* Perm (Fin 5) × Perm (Fin 3), Function.Surjective ρ ∧
      ρ.ker = (centralizer (U : Set G)).subgroupOf Y ∧
      (K.subgroupOf Y).map ρ = (alternatingGroup (Fin 5)).prod ⊥ ∧
      (D.subgroupOf Y).map ρ = (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3)))
    {v : G} (_hv1 : v ≠ 1) (hvZD : v ∈ ⁅Z, D⁆) (_hvM : centralizer ({v} : Set G) ≤ M) :
    CFSG.Open.IsElemAbelian 2 U ∧ K ≤ normalizer (U : Set G) ∧ D ≤ normalizer (U : Set G) ∧
      v ∈ ⁅U, D⁆ ∧ ⁅K, D⁆ ≤ centralizer (U : Set G) ∧ ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hseed : U ≤ Y ∧ Y ≤ normalizer (U : Set G) ∧ CFSG.Open.IsElemAbelian 2 U ∧
      U ≤ (T : Subgroup G) := by
    have h := A7_involution_local_central_seed_construction hG T heT heZ he2 hTY hYe
    rw [hU, hZ]
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  obtain ⟨hUY, hYN, hUel, hUT⟩ := hseed
  have hZU : Z ≤ U := by
    intro z hz
    rw [hU]
    exact subset_closure ⟨1, one_mem _, z, hz, by group⟩
  obtain ⟨ρ, hρs, hρker, hρK, hρD⟩ := hρ
  have hρK' : ∀ k (hk : k ∈ K), (ρ ⟨k, hKY hk⟩).2 = 1 := by
    intro k hk
    have h : ρ ⟨k, hKY hk⟩ ∈ (K.subgroupOf Y).map ρ :=
      ⟨⟨k, hKY hk⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hk, rfl⟩
    rw [hρK] at h
    exact Subgroup.mem_bot.1 (Subgroup.mem_prod.1 h).2
  have hρD' : ∀ d (hd : d ∈ D), (ρ ⟨d, hDY hd⟩).1 = 1 := by
    intro d hd
    have h : ρ ⟨d, hDY hd⟩ ∈ (D.subgroupOf Y).map ρ :=
      ⟨⟨d, hDY hd⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hd, rfl⟩
    rw [hρD] at h
    exact Subgroup.mem_bot.1 (Subgroup.mem_prod.1 h).1
  have hKD : ⁅K, D⁆ ≤ centralizer (U : Set G) := by
    rw [Subgroup.commutator_le]
    intro k hk d hd
    have h1 : ρ ⁅(⟨k, hKY hk⟩ : Y), ⟨d, hDY hd⟩⁆ = 1 := by
      rw [map_commutatorElement]
      refine Prod.ext ?_ ?_
      · simp [commutatorElement_def, hρD' d hd]
      · simp [commutatorElement_def, hρK' k hk]
    have h2 : ⁅(⟨k, hKY hk⟩ : Y), ⟨d, hDY hd⟩⁆ ∈ (centralizer (U : Set G)).subgroupOf Y := by
      rw [← hρker]
      exact h1
    rw [mem_subgroupOf] at h2
    simpa [commutatorElement_def] using h2
  have hsplit : ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ := by
    have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hUel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have instU : IsElementaryAbelian 2 U := isElementaryAbelian_iff.2 ⟨hUcomm, hUel.2⟩
    set φ : Y →* (Additive U ≃ₗ[ZMod 2] Additive U) := (conjLin U).comp (inclusion hYN)
      with hφdef
    have hφ : ∀ (y : Y) (w : Additive U), ((Additive.toMul (φ y w) : U) : G) =
        y * (Additive.toMul w : U) * (y : G)⁻¹ := fun _ _ => rfl
    have hker : ρ.ker ≤ φ.ker := by
      intro y hy
      rw [hρker, mem_subgroupOf] at hy
      rw [MonoidHom.mem_ker]
      refine LinearEquiv.ext fun w => Additive.toMul.injective (Subtype.ext ?_)
      rw [hφ]
      show (y : G) * (Additive.toMul w : U) * (y : G)⁻¹ = (Additive.toMul w : U)
      rw [← mem_centralizer_iff.1 hy _ (Additive.toMul w).2, mul_inv_cancel_right]
    set ρlin : Perm (Fin 5) × Perm (Fin 3) →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
      (QuotientGroup.lift ρ.ker φ hker).comp
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.toMonoidHom with hρlindef
    have hρlin : ∀ y : Y, ρlin (ρ y) = φ y := by
      intro y
      have h : (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm (ρ y) =
          (y : Y ⧸ ρ.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      show QuotientGroup.lift ρ.ker φ hker
        ((QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm (ρ y)) = φ y
      rw [h]
      rfl
    obtain ⟨A, ⟨hAT, hAel, hAmax⟩, a, haA, haY, ha2⟩ : ∃ A : Subgroup G,
        (A ≤ (T : Subgroup G) ∧ IsElementaryAbelian 2 A ∧ ∀ B : Subgroup G,
          B ≤ (T : Subgroup G) → IsElementaryAbelian 2 B → Nat.card B ≤ Nat.card A) ∧
        ∃ a ∈ A, ∃ ha : a ∈ Y, (ρ ⟨a, ha⟩).2 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      set L : Subgroup G := (((MonoidHom.snd _ _).comp ρ).ker).map Y.subtype with hL
      have hJL : J ≤ L := by
        rw [hJ]
        refine iSup₂_le fun A hA' => ?_
        intro x hxA
        exact ⟨⟨x, hTY (hA'.1 hxA)⟩, hcon A hA' x hxA (hTY (hA'.1 hxA)), rfl⟩
      have hle : ⁅D, J⁆ ≤ (ρ.ker).map Y.subtype := by
        rw [Subgroup.commutator_le]
        intro d hd j hj
        obtain ⟨j', hj'1, rfl⟩ := hJL hj
        refine ⟨⁅(⟨d, hDY hd⟩ : Y), j'⁆, ?_, by simp⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
        have hj2 : (ρ j').2 = 1 := hj'1
        refine Prod.ext ?_ ?_
        · simp [commutatorElement_def, hρD' d hd]
        · simp [commutatorElement_def, hj2]
      have hc : ((1 : Perm (Fin 5)), finRotate 3) ∈ (D.subgroupOf Y).map ρ := by
        rw [hρD]
        exact Subgroup.mem_prod.2 ⟨Subgroup.mem_bot.2 rfl, mem_alternatingGroup.2 (by decide)⟩
      obtain ⟨y, hyD, hy⟩ := hc
      rw [SetLike.mem_coe, mem_subgroupOf, hDJ] at hyD
      obtain ⟨y', hy'1, hy'y⟩ := hle hyD
      have hyy : y' = y := Subtype.ext hy'y
      rw [hyy, SetLike.mem_coe, MonoidHom.mem_ker] at hy'1
      rw [hy'1] at hy
      have h3 := congrArg Prod.snd hy
      exact absurd h3 (by decide)
    have hAY : A ≤ Y := hAT.trans hTY
    set B := (A.subgroupOf Y).map ρ with hBdef
    have hBel : IsElementaryAbelian 2 B :=
      isElementaryAbelian_map (isElementaryAbelian_subgroupOf hAel) ρ
    obtain ⟨r, hr⟩ := exists_card_eq_pow_of_isElementaryAbelian hBel
    have haB : ρ ⟨a, haY⟩ ∈ B :=
      ⟨⟨a, haY⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact haA, rfl⟩
    have hidx : (U ⊓ centralizer (A : Set G)).relIndex U ≤
        (A ⊓ centralizer (U : Set G)).relIndex A := by
      have : (U.subgroupOf T).Normal :=
        (normal_subgroupOf_iff_le_normalizer hUT).2 (hTY.trans hYN)
      have h := relIndex_inf_centralizer_le (p := 2) (V := U.subgroupOf T)
        (A := A.subgroupOf T) (isElementaryAbelian_subgroupOf instU)
        (isElementaryAbelian_subgroupOf hAel) (fun E hE => by
          have h1 := hAmax (E.map (T : Subgroup G).subtype) (map_subtype_le E)
            (isElementaryAbelian_map hE _)
          rwa [card_map_of_injective (subtype_injective _), ← card_subgroupOf_eq hAT] at h1)
      rw [centralizer_subgroupOf_eq hAT, centralizer_subgroupOf_eq hUT, ← inf_subgroupOf_eq,
        ← inf_subgroupOf_eq, relIndex_subgroupOf hUT, relIndex_subgroupOf hAT] at h
      exact h
    have hidxA : (A ⊓ centralizer (U : Set G)).relIndex A = Nat.card B := by
      rw [← relIndex_subgroupOf hAY, inf_subgroupOf_eq, ← hρker, inf_relIndex_left,
        relIndex_ker]
    have hfixmem : ∀ w : Additive U, w ∈ fixSpace ρlin B ↔
        ((Additive.toMul w : U) : G) ∈ centralizer (A : Set G) := by
      intro w
      rw [mem_fixSpace, mem_centralizer_iff]
      constructor
      · intro h x hx
        have h1 := h (ρ ⟨x, hAY hx⟩)
          ⟨⟨x, hAY hx⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hx, rfl⟩
        rw [hρlin] at h1
        have h2 := congrArg (fun w => ((Additive.toMul w : U) : G)) h1
        simp only [hφ] at h2
        calc x * ((Additive.toMul w : U) : G)
            = x * ((Additive.toMul w : U) : G) * x⁻¹ * x := by group
          _ = ((Additive.toMul w : U) : G) * x := by rw [h2]
      · rintro h _ ⟨y, hyA, rfl⟩
        rw [SetLike.mem_coe, mem_subgroupOf] at hyA
        rw [hρlin]
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hφ, h y hyA, mul_inv_cancel_right]
    have hn : 2 ^ finrank (ZMod 2) (Additive U) = Nat.card U := by
      rw [FiniteField.pow_finrank_eq_natCard 2 (Additive U)]
      exact Nat.card_congr Additive.toMul
    have hc : 2 ^ finrank (ZMod 2) (fixSpace ρlin B) =
        Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) := by
      rw [FiniteField.pow_finrank_eq_natCard 2 (fixSpace ρlin B)]
      let f : fixSpace ρlin B → (U ⊓ centralizer (A : Set G) : Subgroup G) := fun w =>
        ⟨((Additive.toMul (w : Additive U) : U) : G),
          (Additive.toMul (w : Additive U)).2, (hfixmem w).1 w.2⟩
      refine Nat.card_congr (Equiv.ofBijective f ⟨fun w₁ w₂ h => ?_, fun g => ?_⟩)
      · have h' := congrArg (fun z : (U ⊓ centralizer (A : Set G) : Subgroup G) => (z : G)) h
        exact Subtype.ext (Additive.toMul.injective (Subtype.ext h'))
      · obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.1 g.2
        exact ⟨⟨Additive.ofMul ⟨g, hgU⟩, (hfixmem _).2 hgC⟩, rfl⟩
    have hcardU := Subgroup.relIndex_mul_card (U ⊓ centralizer (A : Set G)) U
    rw [inf_of_le_left inf_le_left] at hcardU
    have hineq : finrank (ZMod 2) (Additive U) - finrank (ZMod 2) (fixSpace ρlin B) ≤ r := by
      have h1 : 2 ^ finrank (ZMod 2) (Additive U) ≤
          2 ^ (r + finrank (ZMod 2) (fixSpace ρlin B)) := by
        rw [hn, pow_add, hc, ← hcardU, ← hr, ← hidxA]
        exact Nat.mul_le_mul_right _ hidx
      have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
      omega
    obtain ⟨-, -, -, -, hinf⟩ := A7_S5_S3_action_inequality_commutator_split ρlin
      ⟨B, hBel, r, hr, hineq, ρ ⟨a, haY⟩, haB, ha2⟩
    have hgen : ∀ (X : Subgroup G) (hXY : X ≤ Y), ⁅U, X⁆ ≤
        toMulImage U (commSpace ρlin ((X.subgroupOf Y).map ρ)).toAddSubgroup := by
      intro X hXY
      rw [Subgroup.commutator_le]
      intro u hu x hx
      refine ⟨-(ρlin (ρ ⟨x, hXY hx⟩) (Additive.ofMul ⟨u, hu⟩) - Additive.ofMul ⟨u, hu⟩), ?_, ?_⟩
      · refine Submodule.neg_mem _ (Submodule.subset_span ⟨ρ ⟨x, hXY hx⟩, ?_, _, rfl⟩)
        exact ⟨⟨x, hXY hx⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hx, rfl⟩
      · rw [hρlin, neg_sub, toMul_sub, Subgroup.coe_div, hφ, commutatorElement_def]
        simp only [toMul_ofMul]
        change u / (x * u * x⁻¹) = u * x * u⁻¹ * x⁻¹
        rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev, inv_inv]
        simp only [mul_assoc]
    have hK' := hgen K hKY
    have hD' := hgen D hDY
    rw [hρK] at hK'
    rw [hρD] at hD'
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgK, hgD⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨w₁, hw₁, rfl⟩ := hK' hgK
    obtain ⟨w₂, hw₂, hw₂e⟩ := hD' hgD
    have h12 : w₂ = w₁ := Additive.toMul.injective (Subtype.ext hw₂e)
    subst h12
    have hmem : w₂ ∈ commSpace ρlin ((alternatingGroup (Fin 5)).prod ⊥) ⊓
        commSpace ρlin ((⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3))) :=
      ⟨hw₁, hw₂⟩
    rw [hinf, Submodule.mem_bot] at hmem
    rw [hmem, Subgroup.mem_bot]
    rfl
  exact ⟨hUel, hKY.trans hYN, hDY.trans hYN, commutator_mono hZU le_rfl hvZD, hKD, hsplit⟩

end CFSG.Quasithin.H13.A7
