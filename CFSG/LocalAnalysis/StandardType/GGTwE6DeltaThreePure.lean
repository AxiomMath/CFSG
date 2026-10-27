module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Pure

variable {L' : Type} [Group L'] [Finite L']

theorem mem_center_of_conj_eq_one {x : L'} (h : (MulAut.conj x : MulAut L') = 1) :
    x ∈ Subgroup.center L' := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun f : MulAut L' => f g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * x = x * g * x⁻¹ * x := by rw [h1]
    _ = x * g := by group

theorem conj_apply_aut (a : MulAut L') (e : L') :
    (MulAut.conj (a e) : MulAut L') = a * MulAut.conj e * a⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem card_le_center_mul_card_map_conj (E : Subgroup L') :
    Nat.card E ≤ Nat.card (Subgroup.center L') *
      Nat.card (E.map (MulAut.conj : L' →* MulAut L')) := by
  set f : E →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp E.subtype with hf
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card E := Subgroup.card_ker_mul_card_range f
  have h2 : f.range = E.map (MulAut.conj : L' →* MulAut L') := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : Nat.card f.ker ≤ Nat.card (Subgroup.center L') := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨((k : E) : L'), mem_center_of_conj_eq_one k.2⟩ : Subgroup.center L')) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem false_of_fixed {A : Subgroup (MulAut L')} (hadm : GGDeltaAdm 3 L' A) {E : Subgroup L'}
    (hE : IsElemAbelian 3 E) (hfix : ∀ a ∈ A, ∀ e ∈ E, a e = e)
    (hcard : Nat.card (Subgroup.center L') * Nat.card A ≤ Nat.card E) : False := by
  obtain ⟨hF1, hcase⟩ := hadm
  have hle : E.map (MulAut.conj : L' →* MulAut L') ≤ A := by
    rintro _ ⟨e, he, rfl⟩
    exact hF1 e (hE.2 e he) (fun a ha => hfix a ha e he)
  have hc0 : 0 < Nat.card (Subgroup.center L') := Nat.card_pos
  have hcardA : Nat.card A ≤ Nat.card (E.map (MulAut.conj : L' →* MulAut L')) :=
    Nat.le_of_mul_le_mul_left (hcard.trans (card_le_center_mul_card_map_conj E)) hc0
  have heq : E.map (MulAut.conj : L' →* MulAut L') = A :=
    Subgroup.eq_of_le_of_card_ge hle hcardA
  have hAinn : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range := by
    intro a ha
    rw [← heq] at ha
    obtain ⟨e, -, rfl⟩ := ha
    exact ⟨e, rfl⟩
  rcases hcase with ⟨⟨a, ha, hna⟩, -⟩ | ⟨-, -, a, ha, hna⟩
  · exact hna (hAinn a ha)
  · rcases hna with hna | hord
    · exact hna (hAinn a ha)
    · rw [← heq] at ha
      obtain ⟨e, he, hea⟩ := ha
      have h3 := hord e hea
      rw [hE.2 e he, orderOf_one] at h3
      exact absurd h3 (by norm_num)

theorem isElemAbelian_comap_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {S : Subgroup H} (hS : IsElemAbelian p S) :
    IsElemAbelian p (S.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun y hy => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hS a.2 b.2
  · rw [map_pow, hS.2 _ hy, map_one]

theorem conj_injective_of_center_card_eq_one (h : Nat.card (Subgroup.center L') = 1) :
    Function.Injective (MulAut.conj : L' →* MulAut L') := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem := mem_center_of_conj_eq_one hx
  have hbot : Subgroup.center L' = ⊥ := Subgroup.card_eq_one.1 h
  rw [hbot] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem fixes_of_mem_zpowers {P : L' → Prop} {t a : MulAut L'} (ht : ∀ j, P j → t j = j)
    (ha : a ∈ Subgroup.zpowers t) : ∀ j, P j → a j = j := by
  let F : Subgroup (MulAut L') :=
    { carrier := {x | ∀ j, P j → x j = j}
      mul_mem' := fun {x y} hx hy j hj => by rw [MulAut.mul_apply, hy j hj, hx j hj]
      one_mem' := fun j _ => rfl
      inv_mem' := fun {x} hx j hj => by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact (hx j hj).symm }
  exact (Subgroup.zpowers_le.2 (show t ∈ F from ht)) ha

end Pure

section Induced

variable {K : Type} [Field K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n}

theorem mem_range_conj_of_inner (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {a : MulAut L'}
    (h : ∃ r : TwE6Delta.RecipeR K n, ∀ l, ψ (a l) = r * ψ l * r⁻¹) :
    a ∈ (MulAut.conj : L' →* MulAut L').range := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨l₀, rfl⟩ := hψ r
  refine ⟨l₀, ?_⟩
  apply ggIE_indAutHom_injective hψ hZ hker hperf
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  change ggIE_indAut hψ hZ hker (MulAut.conj l₀) (ψ l) = ggIE_indAut hψ hZ hker a (ψ l)
  rw [ggIE_indAut_apply, ggIE_indAut_apply, hr, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem rho_mem_range_conj_iff (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (a : MulAut L') :
    ggIE_indAutHom hψ hZ hker a ∈
        (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range ↔
      a ∈ (MulAut.conj : L' →* MulAut L').range := by
  constructor
  · rintro ⟨r, hr⟩
    refine mem_range_conj_of_inner hψ hZ hker hperf ⟨r, fun l => ?_⟩
    have h1 := ggIE_indAut_apply hψ hZ hker a l
    have h2 := congrArg (fun f : MulAut (TwE6Delta.RecipeR K n) => f (ψ l)) hr
    simp only [MulAut.conj_apply] at h2
    exact h1.symm.trans h2.symm
  · rintro ⟨l₀, rfl⟩
    refine ⟨ψ l₀, ?_⟩
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    change MulAut.conj (ψ l₀) (ψ l) = ggIE_indAut hψ hZ hker (MulAut.conj l₀) (ψ l)
    rw [ggIE_indAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem rho_mem_recipeI (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} (ha : Induces ψ a) :
    ggIE_indAutHom hψ hZ hker a ∈ TwE6Delta.RecipeI K n := by
  obtain ⟨φ, hφ, hφa⟩ := ha
  have h1 := ggIE_eq_indAut_of_forall hψ hZ hker hφa
  show ggIE_indAut hψ hZ hker a ∈ TwE6Delta.RecipeI K n
  rw [← h1]
  exact hφ

end Induced

theorem nine_dvd_of_three_dvd {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) (hn : 3 ∣ n) : 9 ∣ 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ := hn
  have e8 : 2 ^ (3 * m) = 8 ^ m := by rw [pow_mul]; norm_num
  rw [e8] at h3 ⊢
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
  · exfalso
    have h1 : 8 ^ m % 3 = 1 := by
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · simpa using Odd.nat_add_dvd_pow_add_pow 8 1 hodd

end CFSG.StandardType.TwE6D3
