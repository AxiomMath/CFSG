module

public import CFSG.Quasithin.Vol2.Ch12Sec9Statements
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem exists_linearEquiv_extend {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) (e : U ≃ₗ[K] U) : ∃ β : E ≃ₗ[K] E, ∀ u : U, β u = e u := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  let β : E ≃ₗ[K] E := ((Submodule.prodEquivOfIsCompl U C hC).symm.trans
    (e.prodCongr (LinearEquiv.refl K C))).trans (Submodule.prodEquivOfIsCompl U C hC)
  exact ⟨β, fun u => by simp [β]⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_conj_eq_of_le {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {W : Subgroup G} (hWV : W ≤ V) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    ∃ l ∈ L, ∀ x ∈ W, l * x * l⁻¹ = g * x * g⁻¹ := by
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  let _ := zmodModuleOf hsq
  have hgW : ∀ a ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ W, a * x * a⁻¹ ∈ W :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.1 ha x).1 hx
  let cj : ∀ a ∈ Subgroup.normalizer (W : Set G), subOf (V := V) W →+ subOf (V := V) W :=
    fun a ha =>
      { toFun := fun x => ⟨Additive.ofMul
          ⟨a * ((Additive.toMul (x : Additive ↥V) : ↥V) : G) * a⁻¹,
            hWV (hgW a ha _ (mem_subOf.1 x.2))⟩, mem_subOf.2 (hgW a ha _ (mem_subOf.1 x.2))⟩
        map_zero' := by
          apply Subtype.ext
          apply Additive.toMul.injective
          apply Subtype.ext
          simp
        map_add' := fun x y => by
          apply Subtype.ext
          apply Additive.toMul.injective
          apply Subtype.ext
          simp only [Submodule.coe_add, toMul_add, Subgroup.coe_mul, toMul_ofMul]
          group }
  have hcj : ∀ a (ha : a ∈ Subgroup.normalizer (W : Set G)) (x : subOf (V := V) W),
      ((Additive.toMul ((cj a ha x : subOf (V := V) W) : Additive ↥V) : ↥V) : G) =
        a * ((Additive.toMul (x : Additive ↥V) : ↥V) : G) * a⁻¹ := fun _ _ _ => rfl
  let e : subOf (V := V) W ≃ₗ[ZMod 2] subOf (V := V) W :=
    LinearEquiv.ofLinearMap ((cj g hg).toZModLinearMap 2)
      ((cj g⁻¹ (inv_mem hg)).toZModLinearMap 2)
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toZModLinearMap,
          LinearMap.id_coe, id_eq]
        rw [hcj g hg, hcj g⁻¹ (inv_mem hg)]
        group)
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toZModLinearMap,
          LinearMap.id_coe, id_eq]
        rw [hcj g⁻¹ (inv_mem hg), hcj g hg]
        group)
  obtain ⟨β, hβ⟩ := exists_linearEquiv_extend (subOf (V := V) W) e
  have hαL : mulAutOfLin β ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, fun x hx => ?_⟩
  have e1 : l * x * l⁻¹ = ((mulAutOfLin β ⟨x, hWV hx⟩ : ↥V) : G) := by
    rw [← hlα]
    rfl
  rw [e1, mulAutOfLin_apply, hβ ⟨Additive.ofMul ⟨x, hWV hx⟩, mem_subOf.2 hx⟩]
  exact hcj g hg _

theorem Hyp1223.ti_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1223 G T L V)
    {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥ := by
  rcases h1222 G T h.simple h.nonabelian h.qtke h.sylow with hAlt | h3
  · exact absurd hAlt h.notAlt
  obtain ⟨-, -, hall⟩ := h3 L h.maximal h.faithful h.quasisimple
  exact (hall V h.irrPlus).2.1 m hm

@[expose] def Claim12_9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₂ : Subgroup G, IsTSub T V V₂ 2 →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)

theorem lemma12_9_7_of_claim (h1222 : Stmt12_2_2) (hcl : Claim12_9_7) : Lemma12_9_7 := by
  intro G _ _ T L V n hcx i Vi hi1 hin hVi
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  obtain ⟨V₂, hV₂⟩ := exists_tsub hyp.sylow.1 hsq hab hTV hcard 2 (by omega)
  have hV₂i : V₂ ≤ Vi := by
    rcases tinv_comparable_of_hyp1281One h1222 hcx.hyp hV₂.1 hVi.1 hV₂.2.2 hVi.2.2 with h | h
    · exact h
    · have h1 := Subgroup.card_le_of_le h
      rw [hVi.2.1, hV₂.2.1] at h1
      have hi : i = 2 := by
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
        omega
      exact (Subgroup.eq_of_le_of_card_ge h (by rw [hVi.2.1, hV₂.2.1, hi])).ge
  intro g hg
  obtain ⟨l, hl, hlg⟩ := exists_mem_conj_eq_of_le hcx.hyp hVi.1 hg
  have hc : l⁻¹ * g ∈ Subgroup.centralizer (Vi : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * (l⁻¹ * g) = l⁻¹ * (l * x * l⁻¹) * g := by group
      _ = l⁻¹ * (g * x * g⁻¹) * g := by rw [hlg x hx]
      _ = l⁻¹ * g * x := by group
  have hcM : l⁻¹ * g ∈ Subgroup.normalizer (L : Set G) :=
    hcl G T L V n hcx V₂ hV₂ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hV₂i) hc)
  have hgM : g ∈ Subgroup.normalizer (L : Set G) := by
    have h1 := mul_mem (Subgroup.le_normalizer hl) hcM
    rwa [mul_inv_cancel_left] at h1
  refine ⟨hgM, ?_⟩
  rcases hyp.ti_of_1222 h1222 hgM with h | h
  · exact SteinbergBS.mem_normalizer_of_conjugate_eq h
  · exfalso
    have hViV : Vi ≤ V ⊓ CFSG.conjugate V g := le_inf hVi.1 fun x hx => by
      rw [SteinbergBS.mem_conjugate_iff]
      exact hVi.1 ((Subgroup.mem_normalizer_iff.1 hg x).1 hx)
    rw [h, le_bot_iff] at hViV
    have h1 := hVi.2.1
    rw [hViV, Subgroup.card_bot] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CFSG.Quasithin.H13
