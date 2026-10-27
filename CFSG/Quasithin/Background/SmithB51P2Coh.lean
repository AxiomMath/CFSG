module

public import CFSG.Quasithin.Background.FFC5Coh3
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.SteinbergCBI16A7
public import CFSG.Quasithin.Background.JonesParshallWedgeH1
public import CFSG.Quasithin.SteinbergCBI16Dn

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.P2

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix

variable {V : Type} [CommGroup V]

@[expose] noncomputable def addEquivOf {W : Subgroup V} {M : Type*} [AddCommGroup M]
    (β : ↥W →* Multiplicative M) (hβ : Function.Bijective β) : Additive ↥W ≃+ M :=
  (MulEquiv.toAdditive (MulEquiv.ofBijective β hβ)).trans (AddEquiv.additiveMultiplicative M)

theorem h1_of_model {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {Γ : Type*} [Group Γ] (ρ : Γ →* ↥L) (hρ : Function.Surjective ρ) {M : Type*}
    [AddCommGroup M] (μ : Γ →* AddMonoid.End M) (θ : Additive ↥W ≃+ M)
    (hθ : ∀ γ w, θ (FFC.muW hLW (ρ γ) w) = μ γ (θ w)) (hZ : Z1A μ ≤ B1A μ) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := fun _ hf =>
  FFC.mem_B1A_of_pullback hLW ρ hρ μ θ hθ (hZ (FFC.pullback_mem_Z1A hLW ρ μ θ hθ hf))

theorem Z1A_comp_le {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] {μ : Γ →* AddMonoid.End M}
    (hZ : Z1A μ ≤ B1A μ) (τ : Γ ≃* Γ) :
    Z1A (μ.comp τ.toMonoidHom) ≤ B1A (μ.comp τ.toMonoidHom) := by
  intro f hf
  have hf' : (fun g => f (τ.symm g)) ∈ Z1A μ := by
    intro g h
    show f (τ.symm (g * h)) = f (τ.symm g) + μ g (f (τ.symm h))
    rw [map_mul, hf]
    show f (τ.symm g) + μ (τ (τ.symm g)) (f (τ.symm h)) = _
    rw [MulEquiv.apply_symm_apply]
  obtain ⟨m, hm⟩ := hZ hf'
  refine ⟨m, funext fun g => ?_⟩
  have h1 := congrFun hm (τ g)
  rw [coboundaryA_apply] at h1 ⊢
  rw [MulEquiv.symm_apply_apply] at h1
  exact h1

theorem injective_of_ker_bot {W : Subgroup V} {M : Type*} [Group M] {β : ↥W →* M}
    (hβk : ∀ u : ↥W, β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V)) : Function.Injective β := by
  rw [injective_iff_map_eq_one]
  intro u hu
  exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))

theorem h1_nat {n : ℕ} (hn : n = 4 ∨ n = 5)
    {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L W ⊥ π) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFC.exists_natMap h
  set ψ := specialLinearGroupEquivStatedSL n (ZMod 2)
  refine h1_of_model hLW (π.comp ψ.toMonoidHom) (h.1.comp ψ.surjective) (muF2 n)
    (addEquivOf β ⟨injective_of_ker_bot hβk, hβs⟩) (fun g w => ?_) ?_
  · have h1 := hβe (ψ g) (Additive.toMul w) (hLW _ (π (ψ g)).2 _ (Additive.toMul w).2)
    exact congrArg Multiplicative.toAdd h1
  · rcases hn with rfl | rfl
    · exact Z1A_eq_B1A_four.le
    · exact Z1A_eq_B1A_five.le

theorem h1_dualNat {n : ℕ} (hn : n = 4 ∨ n = 5)
    {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (h : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia L W ⊥ π) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  set ψ := specialLinearGroupEquivStatedSL n (ZMod 2)
  refine h1_of_model hLW (π.comp ψ.toMonoidHom) (h.1.comp ψ.surjective)
    ((muF2 n).comp (invTransposeSL n (ZMod 2)).toMonoidHom)
    (addEquivOf β ⟨injective_of_ker_bot hβk, hβs⟩) (fun g w => ?_) ?_
  · have h1 := hβe (ψ g) (Additive.toMul w) (hLW _ (π (ψ g)).2 _ (Additive.toMul w).2)
    exact congrArg Multiplicative.toAdd h1
  · rcases hn with rfl | rfl
    · exact Z1A_comp_le Z1A_eq_B1A_four.le _
    · exact Z1A_comp_le Z1A_eq_B1A_five.le _

theorem h1_wedge {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) {π : ↥(StatedSL 5 (ZMod 2)) →* ↥L}
    (h : (FFModel.extSq (ZMod 2) 5).RealizesVia L W ⊥ π) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  set ψ := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  let β' : ↥W →* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := β
  refine h1_of_model hLW (π.comp ψ.toMonoidHom) (h.1.comp ψ.surjective) (muW (ZMod 2))
    ((addEquivOf β' ⟨injective_of_ker_bot hβk, hβs⟩).trans (wedgeEquiv (ZMod 2)).toAddEquiv)
    (fun g w => ?_) Z1A_eq_B1A_wedge.le
  have h1 := congrArg Multiplicative.toAdd
    (hβe (ψ g) (Additive.toMul w) (hLW _ (π (ψ g)).2 _ (Additive.toMul w).2))
  show wedgeEquiv (ZMod 2) (Multiplicative.toAdd (β _)) =
    muW (ZMod 2) g (wedgeEquiv (ZMod 2) (Multiplicative.toAdd (β (Additive.toMul w))))
  rw [muW_apply, wedgeEquiv_apply, wedgeEquiv_apply, ← wedgeCoord_map]
  exact congrArg wedgeCoord h1

theorem h1_altDn {n k : ℕ} (C : SteinbergCB.I16.DnCoords n k) (hZ : Z1A C.actA ≤ B1A C.actA)
    {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {π : ↥(alternatingGroup (Fin n)) →* ↥L} (h : (FFModel.altDn n).RealizesVia L W ⊥ π) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := injective_of_ker_bot hβk
  refine h1_of_model hLW π hπs C.actA
    ((MulEquiv.toAdditive (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans C.coordEquiv)
    (fun γ w => ?_) hZ
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β (Additive.toMul w))
  have hm' : (FFModel.altDn n).act γ m ∈ (FFModel.altDn n).sec := hsec _ _ m.2
  have h1 := hβe γ (Additive.toMul w) m (hLW _ (π γ).2 _ (Additive.toMul w).2) hm' hm.symm
  have h2 := congrArg (fun q => C.coordEquiv (Additive.ofMul q)) h1
  refine h2.trans ?_
  show C.coordEquiv (Additive.ofMul (QuotientGroup.mk _)) =
    C.actA γ (C.coordEquiv (Additive.ofMul (β (Additive.toMul w))))
  rw [← hm, SteinbergCB.I16.DnCoords.coordEquiv_mk, SteinbergCB.I16.DnCoords.coordEquiv_mk]
  exact (C.act_proj (γ : Equiv.Perm (Fin n)) (SteinbergCB.I16.DnCoords.sum_secVec m)).symm

theorem altLift7_injective : Function.Injective altLift7 := fun _ _ h =>
  Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective _ (congrArg Subtype.val h))

theorem h1_a7Four {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}
    {π : ↥(alternatingGroup (Fin 7)) →* ↥L} (h : (FFModel.a7Four α).RealizesVia L W ⊥ π) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  let β' : ↥W →* Multiplicative (Fin 4 → ZMod 2) := β
  let M : SteinbergCB.I16.A7 →* GL (Fin 4) (ZMod 2) := α.toMonoidHom.comp altLift7
  have hM : Function.Injective M := α.injective.comp altLift7_injective
  refine h1_of_model hLW π h.1 (SteinbergCB.I16.matAct M)
    (addEquivOf β' ⟨injective_of_ker_bot hβk, hβs⟩) (fun γ w => ?_)
    (SteinbergCB.I16.Z1A_le_B1A_A7 M hM)
  have h1 := hβe γ (Additive.toMul w) (hLW _ (π γ).2 _ (Additive.toMul w).2)
  exact congrArg Multiplicative.toAdd h1

theorem h1_of_central [Finite V] {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (z : ↥L) (hz : ∀ g : ↥L, z * g = g * z)
    (hfix : ∀ w ∈ W, (z : MulAut V) w = w → w = 1) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  intro f hf
  set μ := FFC.muW hLW
  let φ : Additive ↥W → Additive ↥W := fun x => μ z x - x
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : μ z (x - y) = x - y := by
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hxy
    have h2 : ((Additive.toMul (x - y) : ↥W) : V) = 1 :=
      hfix _ (Additive.toMul (x - y)).2 (congrArg Subtype.val (congrArg Additive.toMul h1))
    have h4 : x - y = 0 := by
      apply Additive.toMul.injective
      exact Subtype.ext h2
    exact sub_eq_zero.1 h4
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.1 hφ
  obtain ⟨m, hm⟩ := hφs (f z)
  refine ⟨m, funext fun g => ?_⟩
  rw [coboundaryA_apply]
  apply hφ
  have hzg : f (z * g) = f (g * z) := by rw [hz g]
  rw [hf, hf] at hzg
  have hcomm : μ z (μ g m) = μ g (μ z m) := by
    have h := congrArg (fun k : ↥L => μ k m) (hz g)
    simp only [map_mul] at h
    exact h
  have key : μ z (f g) - f g = μ g (f z) - f z := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm, hzg, add_comm]
  have hfz : f z = μ z m - m := hm.symm
  show μ z (μ g m - m) - (μ g m - m) = μ z (f g) - f g
  rw [key, hfz, map_sub, map_sub, hcomm]
  abel

theorem h1_tripleA6Six [Finite V] {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (h : TripleA6Six L W ⊥) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  obtain ⟨K, _, _, Γ₀, -, -, hhat, hsc, π, hπ⟩ := h
  have hc3 : Nat.card (Subgroup.center ↥Γ₀) = 3 := hhat.2.1
  have hne : Subgroup.center ↥Γ₀ ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hc3
    omega
  obtain ⟨⟨g₀, hg₀c⟩, hg₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨c, hc⟩ := hsc g₀ hg₀c
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hg₀1
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hc, one_smul]
    rfl
  obtain ⟨β, -, hβk, hβe⟩ := FFC.exists_natMap hπ
  let π' : ↥Γ₀ →* ↥L := π
  refine h1_of_central hLW (π' g₀) (fun g => ?_) (fun w hw hzw => ?_)
  · obtain ⟨γ₀, rfl⟩ := hπ.1 g
    let γ : ↥Γ₀ := γ₀
    have h1 : π' (g₀ * γ) = π' (γ * g₀) := by rw [Subgroup.mem_center_iff.1 hg₀c γ]
    rw [map_mul, map_mul] at h1
    exact h1
  · have h2 : (⟨((π' g₀ : ↥L) : MulAut V) w, hLW _ (π' g₀).2 _ hw⟩ : ↥W) = ⟨w, hw⟩ :=
      Subtype.ext hzw
    have h1 : β ⟨w, hw⟩ = natAct Γ₀ g₀ (β ⟨w, hw⟩) :=
      (congrArg β h2).symm.trans (hβe g₀ ⟨w, hw⟩ (hLW _ (π' g₀).2 _ hw))
    have h3 : Multiplicative.toAdd (β ⟨w, hw⟩) = c • Multiplicative.toAdd (β ⟨w, hw⟩) := by
      have h4 := congrArg Multiplicative.toAdd h1
      refine h4.trans ?_
      show ((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
      rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h5 : Multiplicative.toAdd (β ⟨w, hw⟩) = 0 := by
      have h6 : (c - 1) • Multiplicative.toAdd (β ⟨w, hw⟩) = 0 := by
        rw [sub_smul, one_smul, ← h3, sub_self]
      exact (smul_eq_zero.1 h6).resolve_left (sub_ne_zero.2 hc1)
    have h7 : β ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective h5
    exact Subgroup.mem_bot.1 ((hβk _).1 h7)

theorem sup_inv {L : Subgroup (MulAut V)} {X Y : Subgroup V} (hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X)
    (hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y) : ∀ g ∈ L, ∀ w ∈ X ⊔ Y, g w ∈ X ⊔ Y := by
  intro g hg w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hLX g hg x hx) (hLY g hg y hy)

theorem h1_congr {L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V} (hW : W₁ = W₂)
    (hL₁ : ∀ g ∈ L, ∀ w ∈ W₁, g w ∈ W₁) (hL₂ : ∀ g ∈ L, ∀ w ∈ W₂, g w ∈ W₂)
    (h : ∀ f ∈ Z1A (FFC.muW hL₁), f ∈ B1A (FFC.muW hL₁)) :
    ∀ f ∈ Z1A (FFC.muW hL₂), f ∈ B1A (FFC.muW hL₂) := by
  subst hW
  exact h

theorem h1_sup {L : Subgroup (MulAut V)} {X Y W : Subgroup V} (hXY : X ⊓ Y = ⊥)
    (hsup : X ⊔ Y = W) (hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X) (hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y)
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hX : ∀ f ∈ Z1A (FFC.muW hLX), f ∈ B1A (FFC.muW hLX))
    (hY : ∀ f ∈ Z1A (FFC.muW hLY), f ∈ B1A (FFC.muW hLY)) :
    ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW) := by
  intro f hf
  refine FFC.hR_of_directSum (A := ⊥) hsup hXY hLX hLY hLW (fun f hf _ => hX f hf)
    (fun f hf _ => hY f hf) f hf ⟨0, fun a ha => ?_⟩
  have ha1 : a = 1 := Subtype.ext (Subgroup.mem_bot.1 ha)
  rw [ha1, Z1A_one hf, map_zero, sub_zero]

theorem fixV_inf_sup {L : Subgroup (MulAut V)} {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥)
    (hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X) (hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y)
    (hX : fixV L ⊓ X = ⊥) (hY : fixV L ⊓ Y = ⊥) : fixV L ⊓ (X ⊔ Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hvXY⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hvXY
  have hfix : ∀ g ∈ L, g x = x ∧ g y = y := by
    intro g hg
    have h1 : g x * g y = x * y := by rw [← map_mul]; exact hv g hg
    have h2 : g x * x⁻¹ ∈ X ⊓ Y := by
      refine ⟨X.mul_mem (hLX g hg x hx) (X.inv_mem hx), ?_⟩
      have : g x / x = y / g y := by rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      rw [← div_eq_mul_inv, this, div_eq_mul_inv]
      exact Y.mul_mem hy (Y.inv_mem (hLY g hg y hy))
    rw [hXY, Subgroup.mem_bot, mul_inv_eq_one] at h2
    refine ⟨h2, ?_⟩
    rw [h2] at h1
    exact mul_left_cancel h1
  have hx1 : x ∈ fixV L ⊓ X := ⟨fun g hg => (hfix g hg).1, hx⟩
  have hy1 : y ∈ fixV L ⊓ Y := ⟨fun g hg => (hfix g hg).2, hy⟩
  rw [hX, Subgroup.mem_bot] at hx1
  rw [hY, Subgroup.mem_bot] at hy1
  rw [hx1, hy1, mul_one]
  exact Subgroup.one_mem _

theorem h1_fixV_biSup {ι : Type*} [DecidableEq ι] {L : Subgroup (MulAut V)} (I : ι → Subgroup V)
    (hind : ∀ i, I i ⊓ (⨆ (j) (_ : j ≠ i), I j) = ⊥) (hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i)
    (hH1 : ∀ i, ∀ f ∈ Z1A (FFC.muW (hLI i)), f ∈ B1A (FFC.muW (hLI i)))
    (hfix : ∀ i, fixV L ⊓ I i = ⊥) (s : Finset ι) :
    ∃ hLW : ∀ g ∈ L, ∀ w ∈ ⨆ i ∈ s, I i, g w ∈ ⨆ i ∈ s, I i,
      (∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW)) ∧ fixV L ⊓ ⨆ i ∈ s, I i = ⊥ := by
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ι), I i) = ⊥ := by simp
    have hLW : ∀ g ∈ L, ∀ w ∈ ⨆ i ∈ (∅ : Finset ι), I i, g w ∈ ⨆ i ∈ (∅ : Finset ι), I i := by
      intro g _ w hw
      rw [hbot, Subgroup.mem_bot] at hw ⊢
      rw [hw, map_one]
    refine ⟨hLW, fun f hf => ⟨0, funext fun a => ?_⟩, by rw [hbot, inf_bot_eq]⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    have h1 : ((Additive.toMul (f a) : ↥(⨆ i ∈ (∅ : Finset ι), I i)) : V) = 1 :=
      Subgroup.mem_bot.1 (hbot.le (Additive.toMul (f a)).2)
    have h3 : ((Additive.toMul ((coboundaryA (FFC.muW hLW) 0) a) :
        ↥(⨆ i ∈ (∅ : Finset ι), I i)) : V) = 1 :=
      Subgroup.mem_bot.1 (hbot.le (Additive.toMul ((coboundaryA (FFC.muW hLW) 0) a)).2)
    rw [h1, h3]
  | insert a s has ih =>
    obtain ⟨hLs, hH1s, hfixs⟩ := ih
    have heq : (⨆ i ∈ insert a s, I i) = I a ⊔ ⨆ i ∈ s, I i := Finset.iSup_insert a s I
    have hdisj : I a ⊓ ⨆ i ∈ s, I i = ⊥ := by
      rw [eq_bot_iff, ← hind a]
      refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
      exact le_iSup₂_of_le j (fun h => has (h ▸ hj)) le_rfl
    have hLsup := sup_inv (hLI a) hLs
    have hH1sup := h1_sup hdisj rfl (hLI a) hLs hLsup (hH1 a) hH1s
    have hfixsup := fixV_inf_sup hdisj (hLI a) hLs (hfix a) hfixs
    rw [heq]
    exact ⟨hLsup, hH1sup, hfixsup⟩

theorem fixV_inf_nat {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] {L : Subgroup (MulAut V)}
    {W : Subgroup V} {π : ↥(StatedSL n K) →* ↥L}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia L W ⊥ π) : fixV L ⊓ W = ⊥ :=
  CFSG.Quasithin.FFC.fixV_inf_eq_bot_of_nat hn h

theorem fixV_inf_dualNat {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] {L : Subgroup (MulAut V)}
    {W : Subgroup V} {π : ↥(StatedSL n K) →* ↥L}
    (h : (FFModel.dualNat (StatedSL n K)).RealizesVia L W ⊥ π) : fixV L ⊓ W = ⊥ := by
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  let β' : ↥W →* Multiplicative (Fin n → K) := β
  set ψ := specialLinearGroupEquivStatedSL n K
  rw [eq_bot_iff]
  rintro v ⟨hv, hvW⟩
  have h1 : β' ⟨v, hvW⟩ = 1 := by
    apply FFC.eq_one_of_fixed_nat hn
    intro γ
    obtain ⟨g, rfl⟩ := ψ.surjective γ
    set γ' := ψ (invTransposeSL n K g)
    have h3 : (⟨((π γ' : ↥L) : MulAut V) v, by rw [hv _ (π γ').2]; exact hvW⟩ : ↥W) =
        ⟨v, hvW⟩ := Subtype.ext (hv _ (π γ').2)
    have h4 : β' ⟨v, hvW⟩ = (FFModel.dualNat (StatedSL n K)).act γ' (β' ⟨v, hvW⟩) :=
      (congrArg β h3).symm.trans (hβe γ' ⟨v, hvW⟩ _)
    refine Eq.trans ?_ h4.symm
    have hM : (((γ'⁻¹ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
        ((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      show ((invTransposeSL n K (invTransposeSL n K g) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)
      rw [show invTransposeSL n K (invTransposeSL n K g) = g from
        invTransposeFun_invTransposeFun g]
    show Multiplicative.ofAdd (((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd (β' ⟨v, hvW⟩)) =
      Multiplicative.ofAdd ((((γ'⁻¹ : ↥(StatedSL n K)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Multiplicative.toAdd (β' ⟨v, hvW⟩))
    rw [hM]
  exact (hβk _).1 h1

end CFSG.Quasithin.B5.P2
