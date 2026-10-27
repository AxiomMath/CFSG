module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount

public section

namespace CFSG.StandardType.TwE6EltSmall

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6RootKill Module

theorem exists_mem_closure_iform_eq_zero
    {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) {Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hβΨ : β ∈ Ψ ∨ ∀ α ∈ Ψ, iform α β = 0) :
    ∃ α₁, ∀ α ∈ Ψ, α ∈ AddSubgroup.closure ({γ | γ ∈ Ψ ∧ iform γ β = 0} ∪ {β, α₁}) := by
  have hτ : ∀ i, TwistTag.E6.tag.symmetrizer i i = 1 := fun i => Matrix.one_apply_eq i
  have h2 : ∀ {α}, IsRoot TwistTag.E6.tag α → iform α α = 2 :=
    fun hα => SimplyLacedCover.iform_self_eq_two hτ hα
  have hcases : ∀ {α γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag α →
      IsRoot TwistTag.E6.tag γ →
        α = γ ∨ α = -γ ∨ iform α γ = -1 ∨ iform α γ = 0 ∨ iform α γ = 1 := fun hα hγ =>
    (em _).imp_right fun e1 => (em _).imp_right (SimplyLacedCover.iform_mem hτ hα hγ e1)
  have hsub : ∀ {α γ}, α ∈ Ψ → γ ∈ Ψ → IsRoot TwistTag.E6.tag (α - γ) → α - γ ∈ Ψ :=
    fun hα hγ hr => by
      rw [sub_eq_add_neg] at hr ⊢; exact hΨ.add_mem _ hα _ (hΨ.neg_mem _ hγ) hr
  have hneg : ∀ α, iform (-α) β = -iform α β := fun α => SimplyLacedCover.iform_neg_left α β
  by_cases h1 : ∃ α₁ ∈ Ψ, iform α₁ β = 1
  swap
  · push Not at h1
    refine ⟨β, fun α hαΨ => ?_⟩
    rcases hcases (hΨ.isRoot α hαΨ) hβ with e | e | h | h | h
    · exact e ▸ AddSubgroup.subset_closure (Or.inr (Or.inl rfl))
    · exact e ▸ neg_mem (AddSubgroup.subset_closure (Or.inr (Or.inl rfl)))
    · exact absurd (by rw [hneg, h, neg_neg]) (h1 (-α) (hΨ.neg_mem α hαΨ))
    · exact AddSubgroup.subset_closure (Or.inl ⟨hαΨ, h⟩)
    · exact absurd h (h1 α hαΨ)
  obtain ⟨α₁, hα₁Ψ, hα₁β⟩ := h1
  have hβΨ' : β ∈ Ψ :=
    hβΨ.resolve_right fun h => absurd ((h α₁ hα₁Ψ).symm.trans hα₁β) (by decide)
  have hα₁ := hΨ.isRoot α₁ hα₁Ψ
  refine ⟨α₁, ?_⟩
  set C := AddSubgroup.closure ({γ | γ ∈ Ψ ∧ iform γ β = 0} ∪ {β, α₁})
  have hS : ∀ γ ∈ Ψ, iform γ β = 0 → γ ∈ C := fun γ hγ h0 =>
    AddSubgroup.subset_closure (Or.inl ⟨hγ, h0⟩)
  have hβC : β ∈ C := AddSubgroup.subset_closure (Or.inr (Or.inl rfl))
  have hα₁C : α₁ ∈ C := AddSubgroup.subset_closure (Or.inr (Or.inr rfl))
  have hone : ∀ α ∈ Ψ, iform α β = 1 → α ∈ C := by
    intro α hαΨ hαβ
    have hα := hΨ.isRoot α hαΨ
    rcases hcases hα hα₁ with e | e | h | h | h
    · exact e ▸ hα₁C
    · rw [e, hneg, hα₁β] at hαβ
      exact absurd hαβ (by decide)
    ·
      have hr := isRoot_add_of_iform_neg hα hα₁ (fun e => by
        rw [e, SimplyLacedCover.iform_neg_left, h2 hα₁] at h
        exact absurd h (by decide)) (by omega)
      have hval : iform (α + α₁) β = 2 := by rw [iform_add_left, hαβ, hα₁β]; norm_num
      have hsum : α + α₁ = β := by
        rcases hcases hr hβ with e | e | e | e | e
        · exact e
        · rw [e, hneg, h2 hβ] at hval
          exact absurd hval (by decide)
        all_goals omega
      rw [show α = β - α₁ by rw [← hsum]; abel]
      exact sub_mem hβC hα₁C
    ·
      have hβα₁ : 0 < iform β α₁ := by rw [iform_comm, hα₁β]; norm_num
      have hr1 := isRoot_sub_of_iform_pos hβ hα₁ (fun e => by
        rw [e, h2 hα₁] at hα₁β
        exact absurd hα₁β (by decide)) hβα₁
      have hpos : iform α (β - α₁) = 1 := by rw [iform_sub_right, hαβ, h]; norm_num
      have hr2 := isRoot_sub_of_iform_pos hα hr1 (fun e => by
        rw [e, h2 hr1] at hpos
        exact absurd hpos (by decide)) (by omega)
      have h0 : iform (α - (β - α₁)) β = 0 := by
        rw [iform_sub_left, iform_sub_left, hαβ, h2 hβ, hα₁β]; norm_num
      rw [show α = (α - (β - α₁)) + (β - α₁) by abel]
      exact add_mem (hS _ (hsub hαΨ (hsub hβΨ' hα₁Ψ hr1) hr2) h0) (sub_mem hβC hα₁C)
    ·
      have hr := isRoot_sub_of_iform_pos hα hα₁ (fun e => by
        rw [e, h2 hα₁] at h
        exact absurd h (by decide)) (by omega)
      have h0 : iform (α - α₁) β = 0 := by rw [iform_sub_left, hαβ, hα₁β]; norm_num
      rw [show α = (α - α₁) + α₁ by abel]
      exact add_mem (hS _ (hsub hαΨ hα₁Ψ hr) h0) hα₁C
  intro α hαΨ
  rcases hcases (hΨ.isRoot α hαΨ) hβ with e | e | h | h | h
  · exact e ▸ hβC
  · exact e ▸ neg_mem hβC
  · simpa using neg_mem (hone (-α) (hΨ.neg_mem α hαΨ) (by rw [hneg, h, neg_neg]))
  · exact hS α hαΨ h
  · exact hone α hαΨ h

theorem mulVec_injective_cartan_twE6 {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    Function.Injective (TwistTag.E6.tag.cartan.map (Int.cast : ℤ → ZMod p)).mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  have hdet : (TwistTag.E6.tag.cartan.map (Int.cast : ℤ → ZMod p)).det =
      ((TwistTag.E6.tag.cartan.det : ℤ) : ZMod p) := by
    rw [← eq_intCast (Int.castRingHom (ZMod p)), RingHom.map_det]; rfl
  rw [hdet, show TwistTag.E6.tag.cartan.det = 3 from CFSG.LieType.Chevalley.det_cartan_E6,
    isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 (by exact_mod_cast h))

theorem false_of_rank_count
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {G : Type*} [Group G] {f : G →* ModGL TwistTag.E6.tag L}
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    {Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hβΨ : β ∈ Ψ ∨ ∀ α ∈ Ψ, iform α β = 0) {Z Y : Subgroup G} [Finite Z] [Finite Y]
    (hZ : ∀ c : Fin TwistTag.E6.tag.rank → Lˣ, (∀ k, c k ^ p = 1) → rootChar c β = 1 →
      (∀ α ∈ Ψ, rootChar c α = 1) → ∃ x ∈ Z, rootDiagUnit TwistTag.E6.tag c = f x)
    (hY : ∀ γ ∈ Ψ, iform γ β = 0 →
      ∃ x ∈ Y, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) = f x)
    (hZc : Nat.card Z ≤ p) (hYc : Nat.card Y < p ^ 3) : False := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h6 : TwistTag.E6.tag.rank = 6 := rfl
  have hz : ∀ {y : ZMod p} {m : ℤ}, (m : ZMod p) = y → ζ ^ ((y.val : ℕ) : ℤ) = ζ ^ m :=
    fun h => by rw [zpow_eq_zpow_iff_wk hζ, Int.cast_natCast, ZMod.natCast_zmod_val, h]
  obtain ⟨e, he⟩ : ∃ e : (Fin TwistTag.E6.tag.rank → ZMod p) → Fin TwistTag.E6.tag.rank → Lˣ,
      ∀ y k, e y k = ζ ^ ((y k).val : ℤ) := ⟨fun y k => ζ ^ ((y k).val : ℤ), fun _ _ => rfl⟩
  have he_inj : ∀ {y y'}, rootDiagUnit TwistTag.E6.tag (e y) =
      rootDiagUnit TwistTag.E6.tag (e y') → y = y' := by
    intro y y' h
    funext k
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) k
    rwa [he, he, zpow_eq_zpow_iff_wk hζ, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have hcard : ∀ (S : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p)) {H : Subgroup G}
      [Finite H], (∀ y ∈ S, ∃ x ∈ H, rootDiagUnit TwistTag.E6.tag (e y) = f x) →
        p ^ finrank (ZMod p) S ≤ Nat.card H := by
    intro S H _ hS
    choose x hx hxe using fun y : S => hS y.1 y.2
    have hS' : Nat.card S = p ^ finrank (ZMod p) S := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    rw [← hS']
    refine Nat.card_le_card_of_injective (fun y => (⟨x y, hx y⟩ : H)) fun y y' h => ?_
    have h' : x y = x y' := congrArg Subtype.val h
    exact Subtype.ext (he_inj (by rw [hxe y, h', ← hxe y']))
  set v : (Fin TwistTag.E6.tag.rank → ℤ) →+ (Fin TwistTag.E6.tag.rank → ZMod p) :=
    (Int.castAddHom (ZMod p)).compLeft _ with hv
  set U := Submodule.span (ZMod p) (v '' insert β Ψ) with hU
  have hP := hcard (LinearFlag.dotOrth U) (H := Z) fun y hy => by
    have hk : ∀ α ∈ insert β Ψ, rootChar (e y) α = 1 := fun α hα => by
      rw [show e y = _ from funext (he y)]
      exact (rootChar_val_eq_one_iff_wk hζ y α).2
        (LinearFlag.mem_dotOrth.1 hy (v α) (Submodule.subset_span ⟨α, hα, rfl⟩))
    exact hZ _ (fun k => by rw [he]; exact zpow_pow_eq_one_rk hζ.pow_eq_one _)
      (hk β (Set.mem_insert _ _)) fun α hα => hk α (Set.mem_insert_of_mem _ hα)
  have hP1 : finrank (ZMod p) (LinearFlag.dotOrth U) ≤ 1 :=
    (pow_le_pow_iff_right₀ hp1).1 (by rw [pow_one]; exact hP.trans hZc)
  rw [LinearFlag.finrank_dotOrth] at hP1
  obtain ⟨α₁, hα₁⟩ := exists_mem_closure_iform_eq_zero hβ hΨ hβΨ
  set V₀ := Submodule.span (ZMod p) (v '' {γ | γ ∈ Ψ ∧ iform γ β = 0}) with hV₀
  set W := Submodule.span (ZMod p) (v '' {β, α₁}) with hW
  have hcl : AddSubgroup.closure ({γ | γ ∈ Ψ ∧ iform γ β = 0} ∪ {β, α₁}) ≤
      (V₀ ⊔ W).toAddSubgroup.comap v := by
    rw [AddSubgroup.closure_le]
    rintro γ (hγ | hγ)
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨γ, hγ, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  have hUle : U ≤ V₀ ⊔ W := by
    rw [hU, Submodule.span_le]
    rintro _ ⟨α, hα | hα, rfl⟩
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨α, Or.inl hα, rfl⟩)
    · exact hcl (hα₁ α hα)
  have hW2 : finrank (ZMod p) W ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ZMod p) ({v β, v α₁} : Finset _)
    rw [Finset.coe_pair] at h
    rw [hW, Set.image_pair]
    exact h.trans Finset.card_le_two
  have hUV := (Submodule.finrank_mono hUle).trans
    (Submodule.finrank_add_le_finrank_add_finrank V₀ W)
  set Cm := TwistTag.E6.tag.cartan.map (Int.cast : ℤ → ZMod p) with hCm
  let T : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) :=
    { carrier := {y | ∃ x ∈ Y, rootDiagUnit TwistTag.E6.tag (e y) = f x}
      add_mem' := by
        rintro y y' ⟨x, hx, hxy⟩ ⟨x', hx', hxy'⟩
        refine ⟨x * x', Y.mul_mem hx hx', ?_⟩
        rw [map_mul, ← hxy, ← hxy', ← CFSG.LieType.Chevalley.rootDiagUnit_mul]
        congr 1
        funext k
        simp only [he, Pi.mul_apply, ← zpow_add]
        exact hz (by simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val,
          Pi.add_apply])
      zero_mem' := ⟨1, Y.one_mem, by rw [show e 0 = 1 from funext fun k => by simp [he],
        CFSG.LieType.Chevalley.rootDiagUnit_one, map_one]⟩
      smul_mem' := by
        rintro c y ⟨x, hx, hxy⟩
        refine ⟨x ^ c.val, Y.pow_mem hx _, ?_⟩
        rw [map_pow, ← hxy, CFSG.LieType.Chevalley.rootDiagUnit_pow]
        congr 1
        funext k
        simp only [he, Pi.pow_apply, ← zpow_natCast, ← zpow_mul]
        exact hz (by simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
          Pi.smul_apply, smul_eq_mul, mul_comm]) }
  have hVT : V₀.map (Matrix.mulVecLin Cm) ≤ T := by
    rw [hV₀, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨γ, ⟨hγΨ, hγβ⟩, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hY γ hγΨ hγβ
    refine ⟨x, hx, ?_⟩
    rw [← hxe]
    congr 1
    funext k
    rw [he]
    exact hz (by simp [hCm, hv, Matrix.mulVec, dotProduct])
  have hV₀T : finrank (ZMod p) V₀ ≤ finrank (ZMod p) T := by
    rw [(Submodule.equivMapOfInjective (Matrix.mulVecLin Cm) (mulVec_injective_cartan_twE6 hp3)
      V₀).finrank_eq]
    exact Submodule.finrank_mono hVT
  have hT2 : finrank (ZMod p) T < 3 :=
    (pow_lt_pow_iff_right₀ hp1).1 ((hcard T fun _ hy => hy).trans_lt hYc)
  omega

end CFSG.StandardType.TwE6EltSmall

end
