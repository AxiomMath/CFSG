module

public import CFSG.Quasithin.Background.FFC5S5

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank

section T5

variable {V : Type} [CommGroup V]

theorem coboundary_mod_of_image {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {Γ : Type*} [Group Γ] (ρ : Γ →* ↥L) (hρ : Function.Surjective ρ)
    {X : Type*} [AddCommGroup X] (μ : Γ →* AddMonoid.End X) (θ : Additive ↥W →+ X)
    (hθs : Function.Surjective θ) (hθ : ∀ γ w, θ (muW hLW (ρ γ) w) = μ γ (θ w))
    {z : ↥L → Additive ↥W} (hF : (fun γ => θ (z (ρ γ))) ∈ B1A μ) :
    ∃ m : Additive ↥W, ∀ g : ↥L, θ (z g - (muW hLW g m - m)) = 0 := by
  obtain ⟨x, hx⟩ := hF
  obtain ⟨m, rfl⟩ := hθs x
  refine ⟨m, fun g => ?_⟩
  obtain ⟨γ, rfl⟩ := hρ g
  have h1 : μ γ (θ m) - θ m = θ (z (ρ γ)) := congrFun hx γ
  rw [map_sub, map_sub, hθ, ← h1]
  abel

theorem coboundary_mod_C {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {Γ : Type*} [Group Γ] (ρ : Γ →* ↥L) (hρ : Function.Surjective ρ)
    {X : Type*} [AddCommGroup X] (μ : Γ →* AddMonoid.End X) (θ : Additive ↥W →+ X)
    (hθs : Function.Surjective θ) (hθ : ∀ γ w, θ (muW hLW (ρ γ) w) = μ γ (θ w))
    (hH1 : ∀ F ∈ Z1A μ, F ∈ B1A μ) {z : ↥L → Additive ↥W} (hz : z ∈ Z1A (muW hLW)) :
    ∃ m : Additive ↥W, ∀ g : ↥L, θ (z g - (muW hLW g m - m)) = 0 := by
  refine coboundary_mod_of_image hLW ρ hρ μ θ hθs hθ (hH1 _ ?_)
  intro γ δ
  show θ (z (ρ (γ * δ))) = θ (z (ρ γ)) + μ γ (θ (z (ρ δ)))
  rw [map_mul, hz, map_add, hθ]

theorem sym5_theta {L : Subgroup (MulAut V)} {W Z : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {π : Equiv.Perm (Fin 5) →* ↥L} (h : (FFModel.symDn 5).RealizesVia L W Z π) :
    ∃ θ : Additive ↥W →+ E5, Function.Surjective θ ∧ (∀ w, θ w = 0 ↔ ((Additive.toMul w : ↥W) : V) ∈ Z) ∧
      ∀ σ w, θ (muW hLW (π σ) w) = muE σ (θ w) := by
  obtain ⟨f₀, hfs, hfk, hfe⟩ := RealizesVia.secMap symDn_ker_five h
  let val : ↥W → (Fin 5 → ZMod 2) := fun u =>
    fun i => Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ u : ↥(FFModel.symDn 5).sec) :
      (FFModel.symDn 5).Amb)) i
  have hsec : ∀ u : ↥W, ∑ i, val u i = 0 := fun u => (f₀ u).2
  let θ₀ : Additive ↥W →+ E5 :=
    { toFun := fun w => ⟨val (Additive.toMul w), mem_E5sub.2 (hsec _)⟩
      map_zero' := by
        apply Subtype.ext
        funext i
        show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ 1 : ↥(FFModel.symDn 5).sec) :
          (FFModel.symDn 5).Amb)) i = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        apply Subtype.ext
        funext i
        show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ (Additive.toMul x * Additive.toMul y) :
          ↥(FFModel.symDn 5).sec) : (FFModel.symDn 5).Amb)) i = _
        rw [map_mul]
        rfl }
  refine ⟨θ₀, ?_, ?_, ?_⟩
  · intro e
    have hm : (show G6.PermMod 5 from Multiplicative.ofAdd e.1) ∈ (FFModel.symDn 5).sec :=
      mem_E5sub.1 e.2
    obtain ⟨u, hu⟩ := hfs ⟨_, hm⟩
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    funext i
    show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ u : ↥(FFModel.symDn 5).sec) :
      (FFModel.symDn 5).Amb)) i = e.1 i
    rw [hu]
    rfl
  · intro w
    rw [← hfk]
    constructor
    · intro h0
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      exact congrFun (congrArg Subtype.val h0) i
    · intro h1
      apply Subtype.ext
      funext i
      show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ (Additive.toMul w) :
        ↥(FFModel.symDn 5).sec) : (FFModel.symDn 5).Amb)) i = 0
      rw [h1]
      rfl
  · intro σ w
    apply Subtype.ext
    funext i
    have hu : ((π σ : ↥L) : MulAut V) ((Additive.toMul w : ↥W) : V) ∈ W :=
      hLW _ (π σ).2 _ (Additive.toMul w).2
    have h1 := hfe σ (Additive.toMul w) hu
    have h2 := congrArg (fun x : (FFModel.symDn 5).Amb =>
      Multiplicative.toAdd (show G6.PermMod 5 from x) i) h1
    exact h2

theorem natK_theta {K : Type} [Field K] {L : Subgroup (MulAut V)} {W Z : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) {π : ↥(StatedSL 3 K) →* ↥L}
    (h : (FFModel.nat (StatedSL 3 K)).RealizesVia L W Z π) :
    ∃ θ : Additive ↥W →+ (Fin 3 → K), Function.Surjective θ ∧
      (∀ w, θ w = 0 ↔ ((Additive.toMul w : ↥W) : V) ∈ Z) ∧
      ∀ (γ : SL3 K) w, θ (muW hLW (π (specialLinearGroupEquivStatedSL 3 K γ)) w) = mu3 γ (θ w) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap h
  let θ : Additive ↥W →+ (Fin 3 → K) :=
    { toFun := fun w => Multiplicative.toAdd (f (Additive.toMul w))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul u, by
      show Multiplicative.toAdd (f u) = v
      rw [hu]; rfl⟩
  · intro w
    rw [← hfk]
    constructor
    · intro h0
      exact Multiplicative.toAdd.injective h0
    · intro h1
      show Multiplicative.toAdd (f (Additive.toMul w)) = 0
      rw [h1]; rfl
  · intro γ w
    have h1 := hfe (specialLinearGroupEquivStatedSL 3 K γ) (Additive.toMul w)
      (hLW _ (π _).2 _ (Additive.toMul w).2)
    show Multiplicative.toAdd (f (Additive.toMul (muW hLW (π (specialLinearGroupEquivStatedSL 3 K γ)) w))) =
      mu3 γ (Multiplicative.toAdd (f (Additive.toMul w)))
    rw [muW_apply]
    exact congrArg Multiplicative.toAdd h1

theorem exists_sumHom {W I₀ I₁ Z : Subgroup V} (hsup : I₀ ⊔ I₁ = W) (hinf : I₀ ⊓ I₁ ≤ Z)
    {X₀ X₁ : Type*} [AddCommGroup X₀] [AddCommGroup X₁] (θ₀ : Additive ↥I₀ →+ X₀) (θ₁ : Additive ↥I₁ →+ X₁)
    (hk₀ : ∀ x : Additive ↥I₀, θ₀ x = 0 ↔ ((Additive.toMul x : ↥I₀) : V) ∈ Z)
    (hk₁ : ∀ y : Additive ↥I₁, θ₁ y = 0 ↔ ((Additive.toMul y : ↥I₁) : V) ∈ Z) :
    ∃ θ : Additive ↥W →+ X₀ × X₁, ∀ (x : V) (hx : x ∈ I₀) (y : V) (hy : y ∈ I₁)
      (hw : x * y ∈ W), θ (Additive.ofMul ⟨x * y, hw⟩) =
        (θ₀ (Additive.ofMul ⟨x, hx⟩), θ₁ (Additive.ofMul ⟨y, hy⟩)) := by
  classical
  have hdec : ∀ w : ↥W, ∃ x ∈ I₀, ∃ y ∈ I₁, x * y = (w : V) := fun w => by
    have h : (w : V) ∈ I₀ ⊔ I₁ := by rw [hsup]; exact w.2
    exact Subgroup.mem_sup.1 h
  have huniq : ∀ x ∈ I₀, ∀ x' ∈ I₀, ∀ y ∈ I₁, ∀ y' ∈ I₁, x * y = x' * y' →
      x⁻¹ * x' ∈ Z ∧ y * y'⁻¹ ∈ Z := by
    intro x hx x' hx' y hy y' hy' h
    have h1 : x⁻¹ * x' = y * y'⁻¹ := by
      have : x' = x * y * y'⁻¹ := by rw [h]; simp
      rw [this, mul_assoc x y y'⁻¹, inv_mul_cancel_left]
    have h2 : x⁻¹ * x' ∈ I₀ ⊓ I₁ := ⟨I₀.mul_mem (I₀.inv_mem hx) hx', by
      rw [h1]; exact I₁.mul_mem hy (I₁.inv_mem hy')⟩
    have h3 := hinf h2
    exact ⟨h3, by rw [← h1]; exact h3⟩
  let F : Additive ↥W → X₀ × X₁ := fun w =>
    (θ₀ (Additive.ofMul ⟨(hdec (Additive.toMul w)).choose, (hdec (Additive.toMul w)).choose_spec.1⟩),
      θ₁ (Additive.ofMul ⟨(hdec (Additive.toMul w)).choose_spec.2.choose,
        (hdec (Additive.toMul w)).choose_spec.2.choose_spec.1⟩))
  have hF : ∀ (x : V) (hx : x ∈ I₀) (y : V) (hy : y ∈ I₁) (hw : x * y ∈ W),
      F (Additive.ofMul ⟨x * y, hw⟩) = (θ₀ (Additive.ofMul ⟨x, hx⟩), θ₁ (Additive.ofMul ⟨y, hy⟩)) := by
    intro x hx y hy hw
    have hx' : (hdec ⟨x * y, hw⟩).choose ∈ I₀ := (hdec ⟨x * y, hw⟩).choose_spec.1
    have hy' : (hdec ⟨x * y, hw⟩).choose_spec.2.choose ∈ I₁ :=
      (hdec ⟨x * y, hw⟩).choose_spec.2.choose_spec.1
    have hxy' : (hdec ⟨x * y, hw⟩).choose * (hdec ⟨x * y, hw⟩).choose_spec.2.choose = x * y :=
      (hdec ⟨x * y, hw⟩).choose_spec.2.choose_spec.2
    obtain ⟨h1, h2⟩ := huniq _ hx' x hx _ hy' y hy hxy'
    have hz₀ : θ₀ (Additive.ofMul ⟨((hdec ⟨x * y, hw⟩).choose)⁻¹ * x,
        I₀.mul_mem (I₀.inv_mem hx') hx⟩) = 0 := (hk₀ _).2 h1
    have hz₁ : θ₁ (Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose_spec.2.choose * y⁻¹,
        I₁.mul_mem hy' (I₁.inv_mem hy)⟩) = 0 := (hk₁ _).2 h2
    refine Prod.ext ?_ ?_
    · show θ₀ (Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose, hx'⟩) = θ₀ (Additive.ofMul ⟨x, hx⟩)
      have : (Additive.ofMul ⟨x, hx⟩ : Additive ↥I₀) =
          Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose, hx'⟩ +
            Additive.ofMul ⟨((hdec ⟨x * y, hw⟩).choose)⁻¹ * x, I₀.mul_mem (I₀.inv_mem hx') hx⟩ := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      rw [this, map_add, hz₀, add_zero]
    · show θ₁ (Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose_spec.2.choose, hy'⟩) =
        θ₁ (Additive.ofMul ⟨y, hy⟩)
      have : (Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose_spec.2.choose, hy'⟩ : Additive ↥I₁) =
          Additive.ofMul ⟨y, hy⟩ +
            Additive.ofMul ⟨(hdec ⟨x * y, hw⟩).choose_spec.2.choose * y⁻¹,
              I₁.mul_mem hy' (I₁.inv_mem hy)⟩ := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      rw [this, map_add, hz₁, add_zero]
  have hrep : ∀ w : Additive ↥W, ∃ (x : V) (hx : x ∈ I₀) (y : V) (hy : y ∈ I₁) (hw : x * y ∈ W),
      w = Additive.ofMul ⟨x * y, hw⟩ := by
    intro w
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec (Additive.toMul w)
    refine ⟨x, hx, y, hy, hxy ▸ (Additive.toMul w).2, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hxy.symm
  refine ⟨{ toFun := F
            map_zero' := ?_
            map_add' := ?_ }, hF⟩
  · have h := hF 1 I₀.one_mem 1 I₁.one_mem (by simp)
    have h0 : (Additive.ofMul ⟨(1 : V) * 1, by simp⟩ : Additive ↥W) = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp
    have a0 : (Additive.ofMul ⟨(1 : V), I₀.one_mem⟩ : Additive ↥I₀) = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl
    have a1 : (Additive.ofMul ⟨(1 : V), I₁.one_mem⟩ : Additive ↥I₁) = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl
    rw [h0, a0, a1, map_zero, map_zero] at h
    exact h
  · intro w w'
    obtain ⟨x, hx, y, hy, hw, rfl⟩ := hrep w
    obtain ⟨x', hx', y', hy', hw', rfl⟩ := hrep w'
    have hww : Additive.ofMul (⟨x * y, hw⟩ : ↥W) + Additive.ofMul (⟨x' * y', hw'⟩ : ↥W) =
        Additive.ofMul (⟨(x * x') * (y * y'), by
          have := W.mul_mem hw hw'
          rwa [show (x * x') * (y * y') = (x * y) * (x' * y') by simp [mul_comm, mul_left_comm]]⟩ : ↥W) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      show (x * y) * (x' * y') = (x * x') * (y * y')
      simp [mul_comm, mul_left_comm]
    show F _ = F _ + F _
    rw [hww, hF (x * x') (I₀.mul_mem hx hx') (y * y') (I₁.mul_mem hy hy') _, hF x hx y hy hw,
      hF x' hx' y' hy' hw']
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, ← map_add]
      rfl
    · rw [Prod.snd_add, ← map_add]
      rfl

@[expose] def muProd (K : Type) [Field K] :
    SL3 K →* AddMonoid.End ((Fin 3 → K) × (Fin 3 → K)) where
  toFun γ := (mu3 γ).prodMap (mu3 γ)
  map_one' := AddMonoidHom.ext fun x => Prod.ext
    (by show mu3 1 x.1 = x.1; rw [map_one]; rfl) (by show mu3 1 x.2 = x.2; rw [map_one]; rfl)
  map_mul' γ δ := AddMonoidHom.ext fun x => Prod.ext
    (by show mu3 (γ * δ) x.1 = mu3 γ (mu3 δ x.1); rw [map_mul]; rfl)
    (by show mu3 (γ * δ) x.2 = mu3 γ (mu3 δ x.2); rw [map_mul]; rfl)

theorem muProd_h1 {K : Type} [Field K] [Fintype K] [CharP K 2] {a : ℕ} (hF : Fintype.card K = 2 ^ a)
    (ha : 1 < a) : ∀ F ∈ Z1A (muProd K), F ∈ B1A (muProd K) := by
  intro F hF'
  have h1 : (fun γ => (F γ).1) ∈ Z1A (mu3 (F := K)) := by
    intro γ δ
    have := hF' γ δ
    exact congrArg Prod.fst this
  have h2 : (fun γ => (F γ).2) ∈ Z1A (mu3 (F := K)) := by
    intro γ δ
    have := hF' γ δ
    exact congrArg Prod.snd this
  obtain ⟨n₁, hn₁⟩ := mem_B1A_mu3 hF ha h1
  obtain ⟨n₂, hn₂⟩ := mem_B1A_mu3 hF ha h2
  refine ⟨(n₁, n₂), funext fun γ => Prod.ext ?_ ?_⟩
  · exact congrFun hn₁ γ
  · exact congrFun hn₂ γ

theorem natK2_theta {K : Type} [Field K] {L : Subgroup (MulAut V)} {W Z : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) {π : ↥(StatedSL 3 K) →* ↥L}
    (hd : ∃ I : Fin 2 → Subgroup V, (∀ i, Z ≤ I i) ∧ (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = Z) ∧
      (Z ⊔ ⨆ i, I i) = W ∧ ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) Z π) :
    ∃ θ : Additive ↥W →+ (Fin 3 → K) × (Fin 3 → K), Function.Surjective θ ∧
      (∀ w, θ w = 0 ↔ ((Additive.toMul w : ↥W) : V) ∈ Z) ∧
      ∀ (γ : SL3 K) w, θ (muW hLW (π (specialLinearGroupEquivStatedSL 3 K γ)) w) = muProd K γ (θ w) := by
  obtain ⟨I, hZI, hind, hsup, hreal⟩ := hd
  have hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i :=
    fun i g hg w hw => (hreal i).2.2.2.1 ⟨g, hg⟩ w hw
  have h12 : (⨆ j : Fin 2, ⨆ _ : j ≠ 0, I j) = I 1 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂ (f := fun j _ => I j) 1 (by decide))
    fin_cases j
    · exact absurd rfl hj
    · exact le_rfl
  have hiSup : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hsup2 : I 0 ⊔ I 1 = W := by
    rw [← hsup, hiSup]
    exact (sup_eq_right.2 ((hZI 0).trans le_sup_left)).symm
  have hinf2 : I 0 ⊓ I 1 ≤ Z := by
    have := hind 0
    rw [h12] at this
    exact le_trans (inf_le_inf_left _ le_sup_right) this.le
  obtain ⟨θ₀, hθ₀s, hθ₀k, hθ₀e⟩ := natK_theta (hLI 0 |> fun h => fun g hg w hw => h g hg w hw) (hreal 0)
  obtain ⟨θ₁, hθ₁s, hθ₁k, hθ₁e⟩ := natK_theta (fun g hg w hw => hLI 1 g hg w hw) (hreal 1)
  obtain ⟨θ, hθ⟩ := exists_sumHom hsup2 hinf2 θ₀ θ₁ hθ₀k hθ₁k
  refine ⟨θ, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hθ₀s a
    obtain ⟨y, hy⟩ := hθ₁s b
    have hw : ((Additive.toMul x : ↥(I 0)) : V) * ((Additive.toMul y : ↥(I 1)) : V) ∈ W := by
      rw [← hsup2]
      exact Subgroup.mul_mem_sup (Additive.toMul x).2 (Additive.toMul y).2
    refine ⟨Additive.ofMul ⟨_, hw⟩, ?_⟩
    rw [hθ _ (Additive.toMul x).2 _ (Additive.toMul y).2 hw]
    exact Prod.ext hx hy
  · intro w
    have hdec : ∃ x ∈ I 0, ∃ y ∈ I 1, x * y = ((Additive.toMul w : ↥W) : V) := by
      have h : ((Additive.toMul w : ↥W) : V) ∈ I 0 ⊔ I 1 := by rw [hsup2]; exact (Additive.toMul w).2
      exact Subgroup.mem_sup.1 h
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec
    have hw : x * y ∈ W := hxy ▸ (Additive.toMul w).2
    have hwe : w = Additive.ofMul ⟨x * y, hw⟩ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hxy.symm
    rw [hwe, hθ x hx y hy hw]
    show (θ₀ (Additive.ofMul ⟨x, hx⟩), θ₁ (Additive.ofMul ⟨y, hy⟩)) = 0 ↔ x * y ∈ Z
    rw [Prod.mk_eq_zero, hθ₀k, hθ₁k]
    constructor
    · rintro ⟨h0, h1⟩
      exact Z.mul_mem h0 h1
    · intro hz
      have hy0 : y ∈ I 0 := by
        have : y = x⁻¹ * (x * y) := by simp
        rw [this]
        exact (I 0).mul_mem ((I 0).inv_mem hx) (hZI 0 hz)
      have hyZ : y ∈ Z := hinf2 ⟨hy0, hy⟩
      have hxZ : x ∈ Z := by
        have := Z.mul_mem hz (Z.inv_mem hyZ)
        simpa using this
      exact ⟨hxZ, hyZ⟩
  · intro γ w
    have hdec : ∃ x ∈ I 0, ∃ y ∈ I 1, x * y = ((Additive.toMul w : ↥W) : V) := by
      have h : ((Additive.toMul w : ↥W) : V) ∈ I 0 ⊔ I 1 := by rw [hsup2]; exact (Additive.toMul w).2
      exact Subgroup.mem_sup.1 h
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec
    have hw : x * y ∈ W := hxy ▸ (Additive.toMul w).2
    have hwe : w = Additive.ofMul ⟨x * y, hw⟩ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hxy.symm
    set g : MulAut V := ((π (specialLinearGroupEquivStatedSL 3 K γ) : ↥L) : MulAut V) with hg
    have hgL : g ∈ L := (π (specialLinearGroupEquivStatedSL 3 K γ)).2
    have hgx : g x ∈ I 0 := hLI 0 g hgL x hx
    have hgy : g y ∈ I 1 := hLI 1 g hgL y hy
    have hgw : g x * g y ∈ W := by rw [← map_mul]; exact hLW g hgL _ hw
    have h1 : muW hLW (π (specialLinearGroupEquivStatedSL 3 K γ)) w = Additive.ofMul ⟨g x * g y, hgw⟩ := by
      rw [hwe]
      apply Additive.toMul.injective
      apply Subtype.ext
      show g (x * y) = g x * g y
      rw [map_mul]
    rw [h1, hθ _ hgx _ hgy hgw, hwe, hθ x hx y hy hw]
    refine Prod.ext ?_ ?_
    · exact hθ₀e γ (Additive.ofMul ⟨x, hx⟩)
    · exact hθ₁e γ (Additive.ofMul ⟨y, hy⟩)

end T5

end FFC

end CFSG.Quasithin
