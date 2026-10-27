module

public import CFSG.Quasithin.Background.JonesParshallG2H1

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {F : Type} [Field F] [CharP F 2]

@[expose] def zornPHom : ↥(zornO0 F) →* Multiplicative (Ix3 → F) where
  toFun x := Multiplicative.ofAdd (zP (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))))
  map_one' := by
    change Multiplicative.ofAdd (zP (0 : quasithinZorn F)) = 1
    rw [← zmk_zero, zP_zmk, q6_zero]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (zP (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F)) +
      Multiplicative.toAdd (y : Multiplicative (quasithinZorn F)))) = _
    rw [zP_add]
    rfl

omit [CharP F 2] in
theorem mem_zornO0 {x : Multiplicative (quasithinZorn F)} :
    x ∈ zornO0 F ↔ cayleyTr (Multiplicative.toAdd x) = 0 := Iff.rfl

omit [CharP F 2] in
@[expose] noncomputable def secEquivOfHom (D : FFModel) {M : Type*} [CommGroup M]
    (φ : ↥D.sec →* M) (hker : ∀ x, φ x = 1 → x ∈ D.ker.subgroupOf D.sec)
    (hker' : ∀ x ∈ D.ker.subgroupOf D.sec, φ x = 1) (hsurj : Function.Surjective φ) :
    D.Sec ≃* M :=
  MulEquiv.ofBijective (QuotientGroup.lift _ φ fun x hx => hker' x hx)
    ⟨fun x y hxy => by
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      change φ x = φ y at hxy
      rw [QuotientGroup.eq]
      refine hker _ ?_
      rw [map_mul, map_inv, hxy, inv_mul_cancel],
    fun m => by
      obtain ⟨x, hx⟩ := hsurj m
      exact ⟨QuotientGroup.mk x, hx⟩⟩

omit [CharP F 2] in
theorem secEquivOfHom_mk (D : FFModel) {M : Type*} [CommGroup M] (φ : ↥D.sec →* M) (hker)
    (hker') (hsurj) (y : ↥D.sec) :
    secEquivOfHom D φ hker hker' hsurj (QuotientGroup.mk y) = φ y := rfl

theorem zornPHom_eq_one {x : ↥(zornO0 F)} (hx : zornPHom x = 1) :
    (x : Multiplicative (quasithinZorn F)) ∈ zornR F := by
  have hz : zP (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))) = 0 :=
    Multiplicative.ofAdd.injective hx
  have htr : cayleyTr (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))) = 0 := x.2
  refine ⟨(Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))).1, ?_⟩
  have := trace_zero_eq htr
  rw [hz, ← q6_zero, zI_q6, cayleyOne_eq, zmk_smul, zmk_add] at this
  rw [this]
  simp [zmk]

omit [CharP F 2] in
theorem zornPHom_of_mem {x : ↥(zornO0 F)} (hx : (x : Multiplicative (quasithinZorn F)) ∈ zornR F) :
    zornPHom x = 1 := by
  obtain ⟨c, hc⟩ := hx
  change Multiplicative.ofAdd (zP (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))))
    = 1
  rw [hc]
  change Multiplicative.ofAdd (zP (zmk c 0 0 0 0 0 0 c)) = 1
  rw [zP_zmk, q6_zero]
  rfl

omit [CharP F 2] in
theorem zornPHom_surjective : Function.Surjective (zornPHom (F := F)) := fun w =>
  ⟨⟨Multiplicative.ofAdd (zI (Multiplicative.toAdd w)), cayleyTr_zI _⟩, by
    change Multiplicative.ofAdd (zP (zI (Multiplicative.toAdd w))) = w
    rw [zP_zI]
    rfl⟩

@[expose] noncomputable def zornSecEquiv (Γ₀ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) :
    (FFModel.zornQ Γ₀).Sec ≃* Multiplicative (Ix3 → F) :=
  secEquivOfHom (FFModel.zornQ Γ₀) zornPHom
    (fun _ hx => (Subgroup.mem_subgroupOf).mpr (zornPHom_eq_one hx))
    (fun _ hx => zornPHom_of_mem ((Subgroup.mem_subgroupOf).mp hx)) zornPHom_surjective

@[expose] def additiveIx3 (F : Type) [Field F] :
    Additive (Multiplicative (Ix3 → F)) ≃+ (Ix3 → F) where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem cayleyActor_le (F : Type) [Field F] (ε : FullDerived) :
    cayleyActor F ε ≤ cayleyGroup F := by
  cases ε with
  | full => exact le_rfl
  | derived =>
    refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)

theorem G2Natural.intertwiner {ρ : Representation (ZMod 2) Γ W} {ε : FullDerived}
    (h : Explicit.G2Natural ρ F ε) :
    ∃ (θ : Γ ≃* ↥(cayleyActor F ε)) (β : W ≃+ (Ix3 → F)),
      ∀ γ w, β (ρ γ w) = g2Act (Subgroup.inclusion (cayleyActor_le F ε) (θ γ)) (β w) := by
  obtain ⟨θ₀, β₀, hw⟩ := h
  obtain ⟨-, hsec, -, hint⟩ := hw
  let θ₁ : Γ ≃* ↥(cayleyActor F ε) := θ₀
  set e := zornSecEquiv (F := F) (cayleyActor F ε)
  refine ⟨θ₁, (β₀.trans e.toAdditive).trans (additiveIx3 F), fun γ w => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (Additive.toMul (β₀ w))
  have hw' : β₀ w =
      Additive.ofMul (QuotientGroup.mk m : (FFModel.zornQ (cayleyActor F ε)).Sec) := by
    rw [hm]
    rfl
  have h1 := hint γ w m (hsec _ _ m.2) hw'
  change Multiplicative.toAdd (e (Additive.toMul (β₀ (ρ γ w)))) =
    g2Act _ (Multiplicative.toAdd (e (Additive.toMul (β₀ w))))
  rw [h1, hw']
  change zP (((θ₁ γ : ↥(cayleyActor F ε)) : quasithinZorn F ≃ₗ[F] quasithinZorn F)
      (Multiplicative.toAdd (m.1 : Multiplicative (quasithinZorn F)))) =
    zP (((θ₁ γ : ↥(cayleyActor F ε)) : quasithinZorn F ≃ₗ[F] quasithinZorn F)
      (zI (zP (Multiplicative.toAdd (m.1 : Multiplicative (quasithinZorn F))))))
  exact g2_zP_apply (Subgroup.inclusion (cayleyActor_le F ε) (θ₁ γ)) _ m.2

instance finite_zornAut [Finite F] : Finite (quasithinZorn F ≃ₗ[F] quasithinZorn F) :=
  Finite.of_injective (fun g : quasithinZorn F ≃ₗ[F] quasithinZorn F =>
    (g : quasithinZorn F → quasithinZorn F)) (fun _ _ hgh => LinearEquiv.ext (congrFun hgh))

theorem finrank_H1_G2Derived_of_one_lt [Fintype F] {a : ℕ} (hF : Fintype.card F = 2 ^ a)
    (ha : 1 < a) {ρ : Representation (ZMod 2) Γ W} (h : Explicit.G2Natural ρ F .derived) :
    Module.finrank (ZMod 2) (H1 ρ) = a := by
  obtain ⟨θ, β, hβ⟩ := G2Natural.intertwiner h
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hF ha
  let θ' : Γ ≃* ↥(cayleyGroup F) := θ.trans (MulEquiv.subgroupCongr (cayley_commutator_eq hc0 hc1))
  have : Finite Γ := Finite.of_equiv _ θ'.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = g2Act (θ' γ) (β w) := hβ
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (card_Z1A_g2Act hF ha), hF]

end CFSG.Quasithin.JonesParshall
