module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Main
public import CFSG.RankThree.GF2n.Stroth80.Sec311SLTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLDirect

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem det_one_add_vecMulVec_eq {m : ℕ} {K : Type} [Field K] (u f : Fin m → K) :
    (1 + Matrix.vecMulVec u f).det = 1 + f ⬝ᵥ u := by
  have h : Matrix.vecMulVec u f = Matrix.replicateCol Unit u * Matrix.replicateRow Unit f := by
    ext a b
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]

theorem elation_mulVec_centre {m : ℕ} {K : Type} [Field K] {u : Fin m → K}
    {g : GL (Fin m) K} (hg : g ∈ StatedSL m K)
    (hge : ∀ x : Fin m → K, ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u) :
    (g : Matrix (Fin m) (Fin m) K) *ᵥ u = u := by
  obtain ⟨f, hf⟩ := exists_vecMulVec_of_sub_smul hge
  have hdet := StatedAPI.det_of_mem_statedSL hg
  rw [hf, det_one_add_vecMulVec_eq] at hdet
  have hfu : f ⬝ᵥ u = 0 := by linear_combination hdet
  rw [hf, mulVec_one_add_vecMulVec, hfu, zero_smul, add_zero]

theorem mem_of_elation_of_card {K : Type} [Field K] [Finite K] {m : ℕ} {u : Fin m → K}
    (hu : u ≠ 0) (Λ : Subgroup (GL (Fin m) K)) (hΛS : Λ ≤ StatedSL m K)
    (hΛ : ∀ g ∈ Λ, ∀ x : Fin m → K,
      ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u)
    (hcard : Nat.card K ^ (m - 1) ≤ Nat.card Λ) {g : GL (Fin m) K} (hg : g ∈ StatedSL m K)
    (hge : ∀ x : Fin m → K, ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u) :
    g ∈ Λ := by
  classical
  have hex : ∀ g' : Λ, ∃ f : Fin m → K,
      ((g' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f :=
    fun g' => exists_vecMulVec_of_sub_smul (fun x => hΛ (g' : GL (Fin m) K) g'.2 x)
  choose F hF using hex
  have hFdot : ∀ g' : Λ, F g' ⬝ᵥ u = 0 := by
    intro g'
    have h1 := StatedAPI.det_of_mem_statedSL (hΛS g'.2)
    rw [hF g', det_one_add_vecMulVec_eq] at h1
    linear_combination h1
  let Φ : Λ → {f : Fin m → K // f ⬝ᵥ u = 0} := fun g' => ⟨F g', hFdot g'⟩
  have hΦinj : Function.Injective Φ := by
    intro g₁ g₂ h12
    have hF' : F g₁ = F g₂ := congrArg Subtype.val h12
    apply Subtype.ext
    apply Units.ext
    rw [hF g₁, hF g₂, hF']
  have hcardΛ : Nat.card {f : Fin m → K // f ⬝ᵥ u = 0} = Nat.card Λ :=
    le_antisymm (by rw [card_dotProduct_ker hu]; exact hcard)
      (Nat.card_le_card_of_injective Φ hΦinj)
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, hcardΛ.symm⟩
  obtain ⟨f, hf⟩ := exists_vecMulVec_of_sub_smul hge
  have hfu : f ⬝ᵥ u = 0 := by
    have h1 := StatedAPI.det_of_mem_statedSL hg
    rw [hf, det_one_add_vecMulVec_eq] at h1
    linear_combination h1
  obtain ⟨g', hg'⟩ := hbij.2 ⟨f, hfu⟩
  have hFg : F g' = f := congrArg Subtype.val hg'
  have hgg : g = (g' : GL (Fin m) K) := by
    apply Units.ext
    rw [hf, hF g', hFg]
  rw [hgg]
  exact g'.2

theorem exists_ne_zero_one_of_four_le_card {K : Type} [Field K] [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ a : K, a ≠ 0 → a = 1 := fun a ha => by
    by_contra h1
    exact hcon ⟨a, ha, h1⟩
  have hinj : Function.Injective (fun a : K => decide (a = 0)) := by
    intro a b hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · rw [hcon' a ha, hcon' b hb]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth311a_of_SL (h34 : Stroth34Statement) (hGr : GriessCoverStatement)
    (hConj : Stroth311ConjStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hR : Rt M (LB M Q B) t ≠ LB M Q B) (hV : Vt M (LB M Q B) B Z t ≤ QB B) :
    hc.CN t ≤ N0t M Q Z B hc t := by
  classical
  obtain ⟨K, fK, finK, chK, hK, m, hm, φ, hker, -, hirr, hgenT, ⟨u, hu, hel⟩, hcount⟩ :=
    stroth310SLTransv_of_34 h34 G M Q Z B hc n t hs hR hV
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  set Λ : Subgroup (GL (Fin m) K) := ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ with hΛdef
  have hΛX : Λ ≤ φ.range := Subgroup.map_le_range _ _
  have hΛ : ∀ g ∈ Λ, ∀ x : Fin m → K,
      ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u := by
    rintro g ⟨l, hl, rfl⟩ x
    exact hel l (Subgroup.mem_subgroupOf.mp hl) x
  have hrange : φ.range = StatedSL m K :=
    eq_statedSL_of_full_centre hm φ.range hirr hgenT Λ hΛX hu hΛ hcount
  have hΛS : Λ ≤ StatedSL m K := hΛX.trans hrange.le
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_one_of_four_le_card hq4
  obtain ⟨T, hTS, hTu, hTfree⟩ := exists_torus_statedSL hm hu ha0 ha1
  have hTr : T ∈ φ.range := by
    rw [hrange]
    exact hTS
  obtain ⟨τ', hτ'⟩ := hTr
  have hTinv : ∀ g : GL (Fin m) K, g ∈ Λ → T * g * T⁻¹ ∈ Λ := by
    intro g hg
    have hgS : g ∈ StatedSL m K := hΛS hg
    refine mem_of_elation_of_card hu Λ hΛS hΛ hcount
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hTS hgS) (Subgroup.inv_mem _ hTS)) ?_
    intro x
    obtain ⟨c, hc'⟩ := hΛ g hg
      (((T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x)
    refine ⟨c * a, ?_⟩
    have hTy : (T : Matrix (Fin m) (Fin m) K) *ᵥ
        (((T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e1 : ((T * g * T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
        (T : Matrix (Fin m) (Fin m) K) *ᵥ ((g : Matrix (Fin m) (Fin m) K) *ᵥ
          (((T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x)) := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    calc ((T * g * T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x - x
        = (T : Matrix (Fin m) (Fin m) K) *ᵥ ((g : Matrix (Fin m) (Fin m) K) *ᵥ
            (((T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) -
            ((T⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) := by
          rw [Matrix.mulVec_sub, hTy, e1]
      _ = (c * a) • u := by rw [hc', Matrix.mulVec_smul, hTu, smul_smul]
  have hLN : LB M Q B ≤ Subgroup.normalizer (hc.CN t : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hc.CN_conj_mem hs.mem (hLR hl) hy, fun hy => ?_⟩
    have h2 := hc.CN_conj_mem hs.mem ((Rt M (LB M Q B) t).inv_mem (hLR hl)) hy
    have e : l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y := by group
    rwa [e] at h2
  have hconjL : ∀ l ∈ LB M Q B, (τ' : G) * l * (τ' : G)⁻¹ ∈ LB M Q B ⊔ hc.CN t := by
    intro l hl
    have hlΛ : φ ⟨l, hLR hl⟩ ∈ Λ := ⟨⟨l, hLR hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨l₁, hl₁, hφl₁⟩ := hTinv _ hlΛ
    have hφy : φ (τ' * ⟨l, hLR hl⟩ * τ'⁻¹) = φ l₁ := by
      rw [map_mul, map_mul, map_inv, hτ', hφl₁]
    have hker1 : l₁⁻¹ * (τ' * ⟨l, hLR hl⟩ * τ'⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφy, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hker1
    have h1 : ((l₁ : ↥(Rt M (LB M Q B) t)) : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl₁
    have e : (τ' : G) * l * (τ' : G)⁻¹ =
        ((l₁ : ↥(Rt M (LB M Q B) t)) : G) *
          ((l₁⁻¹ * (τ' * ⟨l, hLR hl⟩ * τ'⁻¹) : ↥(Rt M (LB M Q B) t)) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem_sup h1 hker1
  have hτn : (τ' : G) ∈ Subgroup.normalizer ((LB M Q B ⊔ hc.CN t : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨l, hl, n₁, hn₁, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN hx
    have e : (τ' : G) * (l * n₁) * (τ' : G)⁻¹ =
        ((τ' : G) * l * (τ' : G)⁻¹) * ((τ' : G) * n₁ * (τ' : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hconjL l hl)
      (Subgroup.mem_sup_right (hc.CN_conj_mem hs.mem τ'.2 hn₁))
  have hτL : (τ' : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    hc.mem_normalizer_LB_of_normalizer_LN h34 hs τ'.2 hτn
  have hτ : ∀ l ∈ LB M Q B, ⁅(τ' : G), l⁆ ∈ hc.CN t → l ∈ hc.CN t := by
    intro l hl hcomm
    have hlΛ : φ ⟨l, hLR hl⟩ ∈ Λ := ⟨⟨l, hLR hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hc1 : ⁅τ', (⟨l, hLR hl⟩ : ↥(Rt M (LB M Q B) t))⁆ ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hcomm
    have hc2 : ⁅T, φ ⟨l, hLR hl⟩⁆ = 1 := by
      rw [← hτ', ← map_commutatorElement]
      exact hc1
    have hc3 : T * φ ⟨l, hLR hl⟩ = φ ⟨l, hLR hl⟩ * T :=
      commutatorElement_eq_one_iff_mul_comm.mp hc2
    have hge : ∀ x : Fin m → K, ∃ c : K,
        ((φ ⟨l, hLR hl⟩ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u :=
      hel ⟨l, hLR hl⟩ hl
    have hgu := elation_mulVec_centre (hΛS hlΛ) hge
    have h1 : φ ⟨l, hLR hl⟩ = 1 := hTfree _ hgu hge hc3
    have h2 : (⟨l, hLR hl⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hrel : Nat.card Λ = (hc.CN t).relIndex (LB M Q B) := by
    rw [hΛdef, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hLR]
  have hb : (if Nat.card K = 4 then (if m = 2 then 4 else if m = 3 then 16 else 0) else 0) ≤
      (hc.CN t).relIndex (LB M Q B) := by
    rw [← hrel]
    refine le_trans ?_ hcount
    split_ifs with h4 h2 h3
    · subst h2
      rw [h4]
      norm_num
    · subst h3
      rw [h4]
      norm_num
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hAb := stroth311ElAb G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hR
  have hConj' := hConj G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hR
  refine Ctx.CN_le_N0t h34 hc hs hConj' hAb τ'.2 hτL hτ φ hker
    (if Nat.card K = 4 then (if m = 2 then 4 else if m = 3 then 16 else 0) else 0) ?_ hb
  intro E _ _ Y π hrange' hkerπ hcen hperf A hAY hAel hAnorm hbA
  rcases (hGr K hq4 E Y hcen hperf).1 m hm π (hrange'.trans hrange) hkerπ with hY | hlt
  · exact hY
  · exact absurd (hlt A hAY hAel hAnorm) (not_lt.mpr hbA)

end CFSG.RankThree.GF2n.Stroth80
