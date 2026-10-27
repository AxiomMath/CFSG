module

public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FFC4Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank

theorem card_mulAut_le_six {U : Type*} [Group U] [Finite U] (h4 : Nat.card U = 4) :
    Nat.card (MulAut U) ≤ 6 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hthree : Fintype.card {v : U // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {v : U // v = 1} = 1 := by simp
    rw [hone, ← Nat.card_eq_fintype_card, h4]
  let f : MulAut U →* Equiv.Perm {v : U // v ≠ 1} :=
    { toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rfl }
  have hf : Function.Injective f := by
    intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Equiv.Perm {v : U // v ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hthree]
    decide
  omega

theorem card_statedSL_two_two : Nat.card ↥(StatedSL 2 (ZMod 2)) = 6 :=
  (Nat.card_congr (specialLinearGroupEquivStatedSL 2 (ZMod 2)).toEquiv).symm.trans card_sl2_two

theorem isKleinFour_of_card_four {U : Type*} [Group U] (h4 : Nat.card U = 4) (hsq : ∀ u : U, u ^ 2 = 1) :
    IsKleinFour U := by
  refine ⟨h4, ?_⟩
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  exact (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => orderOf_eq_prime (hsq g) hg


theorem le_stabSub_of_invariant {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) : H ≤ stabSub U := by
  intro h hh u
  refine ⟨fun hu => ?_, fun hu => hinv h hh u hu⟩
  have := hinv h⁻¹ (H.inv_mem hh) _ hu
  simpa using this

theorem exists_natural_s3 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {U : Subgroup V} (hH6 : Nat.card ↥H = 6) (hU4 : Nat.card U = 4)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1) :
    ∃ π : ↥(StatedSL 2 (ZMod 2)) →* ↥H, Function.Bijective π ∧
      (FFModel.nat (StatedSL 2 (ZMod 2))).RealizesVia H U ⊥ π := by
  classical
  have hUsq : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  have hUK : IsKleinFour ↥U := isKleinFour_of_card_four hU4 hUsq
  have hM4 : Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2))]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hMsq : ∀ x : Multiplicative (Fin 2 → ZMod 2), x ^ 2 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    funext i
    have h20 : (2 : ZMod 2) = 0 := by decide
    simp [h20]
  have hMK : IsKleinFour (Multiplicative (Fin 2 → ZMod 2)) := isKleinFour_of_card_four hM4 hMsq
  obtain ⟨θ⟩ : Nonempty (↥U ≃* Multiplicative (Fin 2 → ZMod 2)) := IsKleinFour.nonempty_mulEquiv
  have hstab : H ≤ stabSub U := le_stabSub_of_invariant hUinv
  have hρinj : Function.Injective (resG hstab) := resG_injective hstab hfaith
  have hMA : Nat.card (MulAut ↥U) ≤ 6 := card_mulAut_le_six hU4
  have hρbij : Function.Bijective (resG hstab) :=
    hρinj.bijective_of_nat_card_le (by rw [hH6]; exact hMA)
  let eρ : ↥H ≃* MulAut ↥U := MulEquiv.ofBijective (resG hstab) hρbij
  set Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := StatedSL 2 (ZMod 2) with hΓ
  have hD : (FFModel.nat Γ).IsActionModel := FFModel.nat_isActionModel Γ
  have hid : ∀ x, natAct Γ 1 x = x := hD.act_one
  have hmulact : ∀ γ δ x, natAct Γ (γ * δ) x = natAct Γ γ (natAct Γ δ x) := hD.act_mul_act
  have hmulx : ∀ γ x y, natAct Γ γ (x * y) = natAct Γ γ x * natAct Γ γ y := hD.act_mul
  have hinvact : ∀ γ x, natAct Γ γ⁻¹ (natAct Γ γ x) = x := hD.act_inv_act
  have hactinv : ∀ γ x, natAct Γ γ (natAct Γ γ⁻¹ x) = x := hD.act_act_inv
  let τ : ↥Γ →* MulAut ↥U :=
    { toFun := fun γ =>
        { toFun := fun u => θ.symm (natAct Γ γ (θ u))
          invFun := fun u => θ.symm (natAct Γ γ⁻¹ (θ u))
          left_inv := fun u => by
            simp only [MulEquiv.apply_symm_apply, hinvact, MulEquiv.symm_apply_apply]
          right_inv := fun u => by
            simp only [MulEquiv.apply_symm_apply, hactinv, MulEquiv.symm_apply_apply]
          map_mul' := fun a b => by
            simp only [map_mul, hmulx] }
      map_one' := by
        refine MulEquiv.ext fun u => ?_
        show θ.symm (natAct Γ 1 (θ u)) = u
        rw [hid]; simp
      map_mul' := fun γ δ => by
        refine MulEquiv.ext fun u => ?_
        show θ.symm (natAct Γ (γ * δ) (θ u)) = θ.symm (natAct Γ γ (θ (θ.symm (natAct Γ δ (θ u)))))
        rw [hmulact]; simp }
  have hτ : ∀ γ u, θ (τ γ u) = natAct Γ γ (θ u) := fun γ u => by
    show θ (θ.symm (natAct Γ γ (θ u))) = _
    simp
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine natAct_faithful Γ γ fun m => ?_
    have h1 := hτ γ (θ.symm m)
    rw [hγ, MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    simp
  have hτbij : Function.Bijective τ :=
    hτinj.bijective_of_nat_card_le (by rw [card_statedSL_two_two]; exact hMA)
  let π : ↥Γ →* ↥H := eρ.symm.toMonoidHom.comp τ
  have hπs : Function.Surjective π := eρ.symm.surjective.comp hτbij.2
  have hπact : ∀ γ (u : ↥U), ((π γ : ↥H) : MulAut V) (u : V) = ((τ γ u : ↥U) : V) := by
    intro γ u
    have h1 : resG hstab (π γ) = τ γ := by
      show eρ (eρ.symm (τ γ)) = τ γ
      exact eρ.apply_symm_apply _
    have h2 := congrArg (fun φ : MulAut ↥U => ((φ u : ↥U) : V)) h1
    simpa [resG_apply] using h2.symm.symm
  have hone : ∀ γ, natAct Γ γ 1 = 1 := fun γ => by
    have h11 := hmulx γ 1 1
    rw [mul_one] at h11
    exact (mul_left_cancel (a := natAct Γ γ 1) (by rw [mul_one]; exact h11)).symm
  have hreal : (FFModel.nat Γ).RealizesVia H U ⊥ π := by
    refine ⟨hπs, bot_le, bot_le, fun h u hu => hUinv h h.2 u hu, fun h z hz => ?_,
      fun _ m _ => Subgroup.mem_top _, fun (γ : ↥Γ) m hm => ?_, ?_⟩
    · rw [Subgroup.mem_bot.1 hz, map_one]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_bot.1 hm]
      show natAct Γ γ 1 ∈ (⊥ : Subgroup _)
      rw [hone]
      exact Subgroup.one_mem _
    ·
      let β : ↥U →* ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec :=
        (QuotientGroup.mk' ((FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec)).comp
          (MonoidHom.codRestrict θ.toMonoidHom (FFModel.nat Γ).sec (fun u => Subgroup.mem_top _))
      have hβmk : ∀ u : ↥U, β u = QuotientGroup.mk ⟨θ u, Subgroup.mem_top _⟩ := fun u => rfl
      refine ⟨β, ?_, ?_, ?_⟩
      · intro q
        obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨θ.symm m.1, by rw [hβmk]; congr 1; apply Subtype.ext; exact θ.apply_symm_apply _⟩
      · intro u
        rw [hβmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          have h1 : θ u = 1 := h
          have : u = 1 := θ.injective (h1.trans (map_one θ).symm)
          rw [Subgroup.mem_bot, this]
          rfl
        · intro h
          have h1 : (u : V) = 1 := Subgroup.mem_bot.1 h
          have : u = 1 := Subtype.ext h1
          show θ u = 1
          rw [this, map_one]
      · intro (γ : ↥Γ) u m hu hm hbu
        have hbu' : (⟨θ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat Γ).sec) = m := by
          rw [hβmk] at hbu
          have := QuotientGroup.eq.1 hbu
          rw [Subgroup.mem_subgroupOf] at this
          have h1 : ((⟨θ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat Γ).sec)⁻¹ * m :
              ↥(FFModel.nat Γ).sec).1 = 1 := Subgroup.mem_bot.1 this
          have h2 : (⟨θ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat Γ).sec)⁻¹ * m = 1 := Subtype.ext h1
          exact inv_mul_eq_one.1 h2
        rw [hβmk]
        congr 1
        apply Subtype.ext
        show θ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = natAct Γ γ (m : (FFModel.nat Γ).Amb)
        have h3 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥U) = τ γ u := Subtype.ext (hπact γ u)
        rw [h3, hτ, ← hbu']
  have hπinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful Γ) hreal
  exact ⟨π, ⟨hπinj, hπs⟩, hreal⟩

theorem binaryNaturalSL_two_of_s3 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {U C : Subgroup V} (hH6 : Nat.card ↥H = 6) (hU4 : Nat.card U = 4)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1)
    (hCinv : ∀ h ∈ H, ∀ c ∈ C, h c ∈ C) (hUC : U ⊓ C = ⊥) : BinaryNaturalSL H (U ⊔ C) C 2 1 := by
  obtain ⟨π, -, hreal⟩ := exists_natural_s3 hV hH6 hU4 hUinv hfaith
  have hCfix : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C := fun h c hc => hCinv h h.2 c hc
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, π, RealizesVia.extend hreal hCfix hUC⟩

theorem nonempty_mulEquiv_statedSL_two_of_s3 {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {U : Subgroup V} (hH6 : Nat.card ↥H = 6)
    (hU4 : Nat.card U = 4) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1) :
    Nonempty (↥(StatedSL 2 (ZMod 2)) ≃* ↥H) := by
  obtain ⟨π, hπ, -⟩ := exists_natural_s3 hV hH6 hU4 hUinv hfaith
  exact ⟨MulEquiv.ofBijective π hπ⟩

end FFC

end CFSG.Quasithin
