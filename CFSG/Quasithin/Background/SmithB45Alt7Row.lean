module

public import CFSG.Quasithin.Background.SmithB45HatA6Mono
public import CFSG.Quasithin.Background.SmithB45Alt7Sym
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourTypes
public import CFSG.Quasithin.Background.SmithB45HatA6Six

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.SL2Modules Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem k7_facts :
    (swap (0 : Fin 7) 1 * swap 2 3) * (swap 0 1 * swap 2 3) = 1 ∧
    (swap (0 : Fin 7) 1 * swap 4 5) * (swap 0 1 * swap 4 5) = 1 ∧
    (swap (0 : Fin 7) 1 * swap 2 3) * (swap 0 1 * swap 4 5) =
      (swap 0 1 * swap 4 5) * (swap 0 1 * swap 2 3) ∧
    swap (0 : Fin 7) 1 * swap 2 3 ≠ 1 ∧ swap (0 : Fin 7) 1 * swap 4 5 ≠ 1 ∧
    swap (0 : Fin 7) 1 * swap 2 3 ≠ swap 0 1 * swap 4 5 ∧
    sign (swap (0 : Fin 7) 1 * swap 2 3) = 1 ∧ sign (swap (0 : Fin 7) 1 * swap 4 5) = 1 := by
  decide

theorem card_fixK7 :
    Nat.card {y : G6.PermMod 7 // y ∈ G6.coreMod 7 ∧
      G6.permAct 7 (swap 0 1 * swap 2 3) y = y ∧ G6.permAct 7 (swap 0 1 * swap 4 5) y = y} =
      8 := by
  have h : {y : G6.PermMod 7 | y ∈ G6.coreMod 7 ∧
      G6.permAct 7 (swap 0 1 * swap 2 3) y = y ∧ G6.permAct 7 (swap 0 1 * swap 4 5) y = y} =
      ↑(Finset.univ.filter fun x : G6.PermMod 7 =>
        ∑ i, Multiplicative.toAdd x i = 0 ∧ G6.permAct 7 (swap 0 1 * swap 2 3) x = x ∧
          G6.permAct 7 (swap 0 1 * swap 4 5) x = x) := by
    ext x
    simp [G6.mem_coreMod]
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide +kernel

theorem quad_K7 : ∀ y : G6.PermMod 7, y ∈ G6.coreMod 7 →
    G6.permAct 7 (swap 0 1 * swap 2 3) (G6.permAct 7 (swap 0 1 * swap 4 5) y * y⁻¹) =
      G6.permAct 7 (swap 0 1 * swap 4 5) y * y⁻¹ ∧
    G6.permAct 7 (swap 0 1 * swap 4 5) (G6.permAct 7 (swap 0 1 * swap 2 3) y * y⁻¹) =
      G6.permAct 7 (swap 0 1 * swap 2 3) y * y⁻¹ ∧
    G6.permAct 7 (swap 0 1 * swap 2 3) (G6.permAct 7 (swap 0 1 * swap 2 3) y * y⁻¹) =
      G6.permAct 7 (swap 0 1 * swap 2 3) y * y⁻¹ ∧
    G6.permAct 7 (swap 0 1 * swap 4 5) (G6.permAct 7 (swap 0 1 * swap 4 5) y * y⁻¹) =
      G6.permAct 7 (swap 0 1 * swap 4 5) y * y⁻¹ := by
  intro y
  rw [G6.mem_coreMod]
  revert y
  decide +kernel

section Pair

variable {V : Type} [CommGroup V]

theorem mem_fixV_pair {a b : MulAut V} {x : V} :
    x ∈ fixV (Subgroup.closure ({a, b} : Set (MulAut V))) ↔ a x = x ∧ b x = x :=
  CFSG.Quasithin.B45HatA6.mem_fixV_closure_pair

theorem mem_closure_pair_cases [Finite V] {a b : MulAut V} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) {g : MulAut V}
    (hg : g ∈ Subgroup.closure ({a, b} : Set (MulAut V))) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  classical
  set E := Subgroup.closure ({a, b} : Set (MulAut V)) with hE
  have h4 := B45HatA6.card_closure_pair_eq_four ha hb hab ha1 hb1 hne
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = a * b * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have hane : a ≠ a * b := fun h => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [← h, inv_mul_cancel])
  have hbne : b ≠ a * b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel])
  let S : Finset E := {1, ⟨a, haE⟩, ⟨b, hbE⟩, ⟨a * b, mul_mem haE hbE⟩}
  have hS : S.card = 4 := by
    have h1 : (⟨a, haE⟩ : E) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have h2 : (⟨b, hbE⟩ : E) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    have h3 : (⟨a * b, mul_mem haE hbE⟩ : E) ≠ 1 := fun h => hab1 (congrArg Subtype.val h)
    have h4 : (⟨a, haE⟩ : E) ≠ ⟨b, hbE⟩ := fun h => hne (congrArg Subtype.val h)
    have h5 : (⟨a, haE⟩ : E) ≠ ⟨a * b, mul_mem haE hbE⟩ :=
      fun h => hane (congrArg Subtype.val h)
    have h6 : (⟨b, hbE⟩ : E) ≠ ⟨a * b, mul_mem haE hbE⟩ :=
      fun h => hbne (congrArg Subtype.val h)
    rw [Finset.card_insert_of_notMem (by simp [h1.symm, h2.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
  have : Fintype E := Fintype.ofFinite E
  have hSu : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hS, ← Nat.card_eq_fintype_card, h4]
  have hmem : (⟨g, hg⟩ : E) ∈ S := by rw [hSu]; exact Finset.mem_univ _
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end Pair

section Row

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}

omit [Finite V] in
theorem card_V_of_coreEquiv (β : V ≃* ↥(G6.coreMod 7)) : Nat.card V = 64 := by
  rw [← card_coreMod7]
  exact Nat.card_congr β.toEquiv

variable {ι : ↥L ≃* A7} {β : V ≃* ↥(G6.coreMod 7)}
variable (hβ : ∀ (γ : A7) (s : V), (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) =
  G6.permAct 7 (γ : Perm (Fin 7)) (β s))
include hβ

omit [Finite V] in
theorem β_apply_l (l : ↥L) (s : V) :
    (β ((l : MulAut V) s) : G6.PermMod 7) = G6.permAct 7 (ι l : Perm (Fin 7)) (β s) := by
  have := hβ (ι l) s
  rwa [MulEquiv.symm_apply_apply] at this

omit hβ in
@[expose] noncomputable def imgB (ι : ↥L ≃* A7) (A : Subgroup (MulAut V)) :
    Subgroup (Perm (Fin 7)) :=
  ((A.subgroupOf L).map ι.toMonoidHom).map (alternatingGroup (Fin 7)).subtype

omit [Finite V] hβ in
theorem mem_imgB {A : Subgroup (MulAut V)} {σ : Perm (Fin 7)} :
    σ ∈ imgB ι A ↔ ∃ a : ↥L, (a : MulAut V) ∈ A ∧ (ι a : Perm (Fin 7)) = σ := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

omit [Finite V] in
theorem card_fixV_eq {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    Nat.card (fixV A) = Nat.card ↥(evenWeight (Fin 7) ⊓ fixedVectors (imgB ι A)) := by
  classical
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (β v : G6.PermMod 7), (β v).2, ?_⟩
      invFun := fun x => ⟨β.symm ⟨Multiplicative.ofAdd x.1, x.2.1⟩, ?_⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  · intro σ hσ
    obtain ⟨a, ha, rfl⟩ := mem_imgB.1 hσ
    have h1 := β_apply_l hβ a v
    rw [v.2 _ ha] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    funext i
    exact (congrFun h2 i).symm
  · intro a ha
    have h1 := β_apply_l hβ ⟨a, hAL ha⟩ (β.symm ⟨Multiplicative.ofAdd x.1, x.2.1⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have hfix := x.2.2 _ (mem_imgB.2 ⟨⟨a, hAL ha⟩, ha, rfl⟩)
    apply β.injective
    apply Subtype.ext
    rw [h1, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    funext i
    exact congrFun hfix i

theorem le_rAV (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} (hA : IsA2 L A) :
    (3 / 2 : ℚ) ≤ rAV A := by
  classical
  obtain ⟨hAL, hA1, hAe⟩ := hA
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := imgB ι A with hBdef
  have hBA : B ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_imgB.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_imgB.1 hy
    have hab : a * b = b * a := Subtype.ext (hAe.1 _ ha _ hb)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_imgB.1 hx
    have ha2 : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hAe.2 _ ha)
    rw [← Subgroup.coe_mul, ← map_mul, ha2, map_one]
    rfl
  have hBcard : Nat.card B = Nat.card A := by
    rw [hBdef, imgB, Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective,
      Subgroup.card_map_of_injective ι.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hrk := B1.card_elemAbelian hAe
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    apply hA1
    exact (Subgroup.card_eq_one).1 hBcard.symm
  have h24 : Nat.card B = 2 ∨ Nat.card B = 4 := by
    rcases B42A57.classify7A hB1 hBA hBc hB2 with ⟨h2, -⟩ | h
    · exact Or.inl h2
    · right
      rcases h with ⟨h4, -⟩ | ⟨h4, -⟩ <;> exact h4
  have hr12 : rk A = 1 ∨ rk A = 2 := by
    rw [hBcard, hrk] at h24
    rcases h24 with h | h
    · left
      exact Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm)
    · right
      exact Nat.pow_right_injective le_rfl (h.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
  have i1 : CFSG.IsElementaryAbelian 2 ↥A := B1.isElementaryAbelian_of_isElemAbelian2 hAe
  have i2 : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf L) := CFSG.IsElementaryAbelian.subgroupOf hAL
  have i3 : CFSG.IsElementaryAbelian 2 ↥((A.subgroupOf L).map ι.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map ι.toMonoidHom
  have i4 : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.map _
  set f := finrank (ZMod 2) ↥(evenWeight (Fin 7) ⊓ fixedVectors B) with hf
  have hfcard : Nat.card (fixV A) = 2 ^ f := by
    rw [card_fixV_eq hβ hAL, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hmul := (fixV A).card_mul_index
  rw [hfcard, B1.index_eq_two_pow hV (fixV A), card_V_of_coreEquiv β, ← pow_add] at hmul
  have hfk : f + rkIdx (fixV A) = 6 :=
    Nat.pow_right_injective le_rfl (hmul.trans (by norm_num : (64 : ℕ) = 2 ^ 6))
  have hk : rk A + 1 ≤ rkIdx (fixV A) := by
    by_contra hcon
    push Not at hcon
    have hE6 : finrank (ZMod 2) (evenWeight (Fin 7)) = 6 := by
      rw [finrank_evenWeight]
      rfl
    obtain ⟨s, hs2, -, hscard, hBs, -, -⟩ := even_weight_action_inequality_transpositions
      (Ω := Fin 7) (by decide) B (r := rk A) (by rw [hBcard, hrk]) (by rw [hE6]; omega)
    obtain ⟨Δ, hΔ⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hs2 _ hΔ)
    have hsw : swap a b ∈ B := by
      rw [hBs]
      exact Subgroup.subset_closure ⟨_, hΔ, a, by simp, b, by simp, hab, rfl⟩
    have hsign := hBA hsw
    rw [mem_alternatingGroup, sign_swap hab] at hsign
    exact absurd hsign (by decide)
  unfold rAV
  have hr0 : (0 : ℚ) < (rk A : ℚ) := by
    have : 0 < rk A := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hr0]
  have h1 : (rk A : ℚ) + 1 ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast hk
  have h2 : (rk A : ℚ) ≤ 2 := by
    have : rk A ≤ 2 := by omega
    exact_mod_cast this
  linarith

omit hβ in
@[expose] noncomputable def ιs (ι : ↥L ≃* A7) (σ : Perm (Fin 7))
    (hσ : σ ∈ alternatingGroup (Fin 7)) : MulAut V :=
  ((ι.symm ⟨σ, hσ⟩ : ↥L) : MulAut V)

omit [Finite V] hβ in
theorem ιs_mul {σ τ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (hτ : τ ∈ alternatingGroup (Fin 7)) :
    ιs ι σ hσ * ιs ι τ hτ = ιs ι (σ * τ) (mul_mem hσ hτ) := by
  unfold ιs
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

omit [Finite V] hβ in
theorem ιs_inj {σ τ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (hτ : τ ∈ alternatingGroup (Fin 7)) (h : ιs ι σ hσ = ιs ι τ hτ) : σ = τ := by
  have h1 := ι.symm.injective (Subtype.ext h)
  exact congrArg Subtype.val h1

omit [Finite V] hβ in
theorem ιs_one : ιs ι 1 (one_mem _) = (1 : MulAut V) := by
  unfold ιs
  have : (⟨1, one_mem _⟩ : A7) = 1 := rfl
  rw [this, map_one]
  rfl

omit [Finite V] in
theorem β_ιs {σ : Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7)) (s : V) :
    (β (ιs ι σ hσ s) : G6.PermMod 7) = G6.permAct 7 σ (β s) := hβ ⟨σ, hσ⟩ s

theorem exists_A0 :
    ∃ A : Subgroup (MulAut V), IsA2 L A ∧ commSeries A 2 = ⊥ ∧ rAV A = 3 / 2 := by
  classical
  obtain ⟨h1, h2, h12, h1n, h2n, hne, hs1, hs2⟩ := k7_facts
  have hm1 : swap (0 : Fin 7) 1 * swap 2 3 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.2 hs1
  have hm2 : swap (0 : Fin 7) 1 * swap 4 5 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.2 hs2
  set u1 := ιs ι _ hm1 with hu1
  set u2 := ιs ι _ hm2 with hu2
  have hu11 : u1 * u1 = 1 := by
    rw [hu1, ιs_mul]
    simp only [h1]
    exact ιs_one
  have hu22 : u2 * u2 = 1 := by
    rw [hu2, ιs_mul]
    simp only [h2]
    exact ιs_one
  have hu12 : u1 * u2 = u2 * u1 := by
    rw [hu1, hu2, ιs_mul, ιs_mul]
    simp only [h12]
  have hu1n : u1 ≠ 1 := fun h => h1n (ιs_inj (ι := ι) hm1 (one_mem _) (h.trans ιs_one.symm))
  have hu2n : u2 ≠ 1 := fun h => h2n (ιs_inj (ι := ι) hm2 (one_mem _) (h.trans ιs_one.symm))
  have hu12n : u1 ≠ u2 := fun h => hne (ιs_inj (ι := ι) hm1 hm2 h)
  set A := Subgroup.closure ({u1, u2} : Set (MulAut V)) with hA
  have hAL : A ≤ L := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (ι.symm _).2
    · exact (ι.symm _).2
  have hAe : IsElemAbelian2 A := B45HatA6.isElemAbelian2_closure_pair hu11 hu22 hu12
  have hA4 : Nat.card A = 4 := B45HatA6.card_closure_pair_eq_four hu11 hu22 hu12 hu1n hu2n hu12n
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA4
    omega
  have hfix : ∀ v : V, v ∈ fixV A ↔ (β v : G6.PermMod 7) ∈ G6.coreMod 7 ∧
      G6.permAct 7 (swap 0 1 * swap 2 3) (β v) = β v ∧
        G6.permAct 7 (swap 0 1 * swap 4 5) (β v) = β v := by
    intro v
    rw [hA, mem_fixV_pair]
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨(β v).2, ?_, ?_⟩
      · rw [← β_ιs hβ hm1, ← hu1, ha]
      · rw [← β_ιs hβ hm2, ← hu2, hb]
    · rintro ⟨-, ha, hb⟩
      refine ⟨β.injective (Subtype.ext ?_), β.injective (Subtype.ext ?_)⟩
      · rw [hu1, β_ιs hβ hm1, ha]
      · rw [hu2, β_ιs hβ hm2, hb]
  have hfcard : Nat.card (fixV A) = 8 := by
    rw [← card_fixK7]
    refine Nat.card_congr
      { toFun := fun v => ⟨β v, (hfix v).1 v.2⟩
        invFun := fun y => ⟨β.symm ⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
    rw [hfix, MulEquiv.apply_symm_apply]
    exact y.2
  have hquad : IsQuadratic A := by
    unfold IsQuadratic commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have hgen : ∀ y ∈ [u1, u2], ∀ w : V, y w * w⁻¹ ∈ fixV A := by
      intro y hy w
      rw [hfix]
      have hq := quad_K7 (β w) (β w).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · have e : (β (u1 w * w⁻¹) : G6.PermMod 7) =
            G6.permAct 7 (swap 0 1 * swap 2 3) (β w) * (β w : G6.PermMod 7)⁻¹ := by
          rw [map_mul β, map_inv β, Subgroup.coe_mul, Subgroup.coe_inv, β_ιs hβ hm1]
        refine ⟨(β _).2, ?_, ?_⟩
        · rw [e]
          exact hq.2.2.1
        · rw [e]
          exact hq.2.1
      · have e : (β (u2 w * w⁻¹) : G6.PermMod 7) =
            G6.permAct 7 (swap 0 1 * swap 4 5) (β w) * (β w : G6.PermMod 7)⁻¹ := by
          rw [map_mul β, map_inv β, Subgroup.coe_mul, Subgroup.coe_inv, β_ιs hβ hm2]
        refine ⟨(β _).2, ?_, ?_⟩
        · rw [e]
          exact hq.1
        · rw [e]
          exact hq.2.2.2
    rcases mem_closure_pair_cases hu11 hu22 hu12 hu1n hu2n hu12n hx with rfl | rfl | rfl | rfl
    · simp only [MulAut.one_apply, mul_inv_cancel]
      exact (fixV A).one_mem
    · exact hgen _ (by simp) v
    · exact hgen _ (by simp) v
    · have : (u1 * u2) v * v⁻¹ = (u1 (u2 v) * (u2 v)⁻¹) * (u2 v * v⁻¹) := by
        simp only [MulAut.mul_apply]
        group
      rw [this]
      exact (fixV A).mul_mem (hgen _ (by simp) _) (hgen _ (by simp) _)
  refine ⟨A, ⟨hAL, hA1, hAe⟩, (isQuadratic_iff_commSeries_two A).1 hquad, ?_⟩
  have hmul := (fixV A).card_mul_index
  rw [hfcard, card_V_of_coreEquiv β] at hmul
  have hidx : (fixV A).index = 2 ^ 3 := by omega
  have hrk : rk A = 2 := by
    unfold rk
    rw [hA4, show (4 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]
  have hrkI : rkIdx (fixV A) = 3 := by
    unfold rkIdx
    rw [hidx, padicValNat.prime_pow]
  unfold rAV
  rw [hrk, hrkI]
  norm_num

theorem kq_eq_of_coreEquiv (hV : ∀ v : V, v ^ 2 = 1) :
    qOf L = ((3 / 2 : ℚ) : WithTop ℚ) ∧ qhatOf L = ((3 / 2 : ℚ) : WithTop ℚ) := by
  obtain ⟨A, hA, h2, hr⟩ := exists_A0 hβ
  have h3 : commSeries A 3 = ⊥ := by
    change commSub (commSeries A 2) A = ⊥
    rw [h2]
    exact commSub_bot_left A
  have hlow : ∀ B, IsA2 L B → (3 / 2 : ℚ) ≤ rAV B := fun B hB => le_rAV hβ hV hB
  exact ⟨kq_eq_coe_iff.2 ⟨⟨A, hA, h2, hr⟩, fun B hB _ => hlow B hB⟩,
    kq_eq_coe_iff.2 ⟨⟨A, hA, h3, hr⟩, fun B hB _ => hlow B hB⟩⟩

end Row

end CFSG.Quasithin.B45Alt7
