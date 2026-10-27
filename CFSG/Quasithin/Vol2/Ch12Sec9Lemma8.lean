module

public import CFSG.Quasithin.Vol2.Ch12Sec9Statements
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizer_conjugate_of_le_inf {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {i : ℕ} {Vi W : Subgroup G} (hVi : IsTSub T V Vi i)
    (hWV : W ≤ V) (hWc : Nat.card W = 2 ^ i) {g : G} (hWg : W ≤ CFSG.conjugate V g) :
    ∃ l ∈ L, ∃ k ∈ Subgroup.normalizer (Vi : Set G),
      CFSG.conjugate V k = CFSG.conjugate V (g * l⁻¹) := by
  obtain ⟨l, hl, hlW⟩ := lemma12_8_3_two h hVi.1 hWV hVi.2.1 hWc
  refine ⟨l, hl, lemma12_8_3_three h hVi fun x hx => ?_⟩
  have h1 : l⁻¹ * x * l ∈ W := by
    rw [← hlW, SteinbergBS.mem_conjugate_iff, show l * (l⁻¹ * x * l) * l⁻¹ = x by group]
    exact hx
  have h2 := SteinbergBS.mem_conjugate_iff.1 (hWg h1)
  rw [SteinbergBS.mem_conjugate_iff,
    show g * l⁻¹ * x * (g * l⁻¹)⁻¹ = g * (l⁻¹ * x * l) * g⁻¹ by group]
  exact h2

theorem lemma12_9_8 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1294 : Lemma12_9_4) (h1297 : Lemma12_9_7) : Lemma12_9_8 := by
  intro G _ _ T L V n hcx
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2)⟩
  have hNV : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_le_of_hyp1223 h37 h38 h39 hyp hTV hVp
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  ·
    by_contra hlt
    push Not at hlt
    have hWV : V ⊓ CFSG.conjugate V g ≤ V := inf_le_left
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 (hVp.to_le hWV)
    have hi2 : 2 ≤ i := by
      by_contra hi2
      have h1 : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hi] at h1
      omega
    have hin : i ≤ n := by
      have h1 := Subgroup.card_le_of_le hWV
      rw [hi, hcard] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    obtain ⟨Vi, hVi⟩ := exists_tsub hT2 hsq hab hTV hcard i hin
    obtain ⟨l, hl, k, hk, hkg⟩ :=
      exists_normalizer_conjugate_of_le_inf hcx.hyp hVi hWV hi inf_le_right
    have hkV : k ∈ Subgroup.normalizer (V : Set G) := by
      rcases eq_or_lt_of_le hin with rfl | hlt'
      · have hViV : Vi = V := Subgroup.eq_of_le_of_card_ge hVi.1 (by rw [hVi.2.1, hcard])
        rw [hViV] at hk
        exact hk
      · exact (h1297 G T L V _ hcx i Vi (by omega) hlt' hVi hk).2
    have hgl : g * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      SteinbergBS.mem_normalizer_of_conjugate_eq
        (hkg.symm.trans (SteinbergBS.conjugate_of_mem_normalizer hkV))
    apply hg
    have h1 := mul_mem (hNV hgl) (Subgroup.le_normalizer hl)
    rwa [inv_mul_cancel_right] at h1
  ·
    obtain ⟨⟨v, hvW⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hg
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hZc : Nat.card (Subgroup.zpowers v) = 2 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (hsq v hvW.1) hv1'
    have hZW : Subgroup.zpowers v ≤ V ⊓ CFSG.conjugate V g := Subgroup.zpowers_le.2 hvW
    obtain ⟨V₁, hV₁⟩ := exists_tsub hT2 hsq hab hTV hcard 1 (by
      rcases hcx.n45 with h | h <;> omega)
    obtain ⟨l, hl, k, hk, hkg⟩ := exists_normalizer_conjugate_of_le_inf hcx.hyp hV₁
      (hZW.trans inf_le_left) hZc (hZW.trans inf_le_right)
    have hU := h1294 G T L V n hcx V₁ hV₁
    have hkU : CFSG.conjugate V k ≤ u128 V V₁ := by
      intro y hy
      have h1 := mem_conjClosure (Z := V) (H := Subgroup.normalizer (V₁ : Set G)) (inv_mem hk)
        (SteinbergBS.mem_conjugate_iff.1 hy)
      rwa [inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h1
    have hlV := hLV hl
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : l * x * l⁻¹ ∈ u128 V V₁ :=
      le_conjClosure V _ ((Subgroup.mem_normalizer_iff.1 hlV x).1 hx)
    have hy' : l * y * l⁻¹ ∈ u128 V V₁ := by
      apply hkU
      rw [hkg, SteinbergBS.mem_conjugate_iff,
        show g * l⁻¹ * (l * y * l⁻¹) * (g * l⁻¹)⁻¹ = g * y * g⁻¹ by group]
      exact SteinbergBS.mem_conjugate_iff.1 hy
    have h1 := congrArg Subtype.val
      (mul_comm' (⟨_, hy'⟩ : ↥(u128 V V₁)) (⟨_, hx'⟩ : ↥(u128 V V₁)))
    simp only [Subgroup.coe_mul] at h1
    calc y * x = l⁻¹ * ((l * y * l⁻¹) * (l * x * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * x * l⁻¹) * (l * y * l⁻¹)) * l := by rw [h1]
      _ = x * y := by group

end CFSG.Quasithin.H13
