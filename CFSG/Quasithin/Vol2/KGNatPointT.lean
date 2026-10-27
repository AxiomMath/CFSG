module

public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.Quasithin.Vol2.Ch11SecBFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin

theorem isCyclic_ringAut (K : Type) [Field K] [Finite K] [CharP K 2] : IsCyclic (K ≃+* K) := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let e : (K ≃ₐ[ZMod 2] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine isCyclic_of_surjective e fun σ => ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), rfl⟩
  exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod
    ((σ : K →+* K).comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))) x

theorem eq_one_of_pow_two_pow {K : Type} [Field K] [Finite K] [CharP K 2] {a : K} {m : ℕ}
    (ha : a ^ 2 ^ m = 1) : a = 1 := by
  classical
  have := Fintype.ofFinite K
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at ha
    exact zero_ne_one ha
  set u : Kˣ := Units.mk0 a h0
  have hu : u ^ 2 ^ m = 1 := Units.ext (by simp [u, ha])
  have hd1 : orderOf u ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf u ∣ Fintype.card K - 1 := by
    rw [← Fintype.card_units]
    exact orderOf_dvd_card
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hodd : Odd (Fintype.card K - 1) := by
    rw [hk]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      (Nat.even_pow.mpr ⟨even_two, k.ne_zero⟩) odd_one
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hj0 : j = 0 := by
    by_contra hj0
    have h2 : 2 ∣ orderOf u := by
      rw [hj]
      exact dvd_pow_self 2 hj0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hd2))
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have := congrArg Units.val hj
  simpa [u] using this

section Cyclic

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {LM : LinModel D K M} {H : Subgroup (MulAut W)}
  {π : D.Gam →* ↥H} {f : W → M}

theorem bot_maps (τ : MulAut W) : ∀ z ∈ (⊥ : Subgroup W), τ z ∈ (⊥ : Subgroup W) := fun z hz => by
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz, map_one]

theorem autMap_mul (hf : IsCoord LM H ⊥ π f) (s t : MulAut W) (x : M) :
    hf.autMap (s * t) (bot_maps _) x = hf.autMap s (bot_maps s) (hf.autMap t (bot_maps t) x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [hf.autMap_apply, hf.autMap_apply, hf.autMap_apply]
  rfl

theorem autMap_one (hf : IsCoord LM H ⊥ π f) (x : M) : hf.autMap 1 (bot_maps 1) x = x := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [hf.autMap_apply]
  rfl

theorem autMap_ne_zero (hf : IsCoord LM H ⊥ π f) (s : MulAut W) {x : M} (hx : x ≠ 0) :
    hf.autMap s (bot_maps s) x ≠ 0 := by
  intro h0
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [hf.autMap_apply, hf.ker, Subgroup.mem_bot] at h0
  apply hx
  rw [show w = 1 from s.injective (h0.trans (map_one s).symm), hf.map_one]

variable [Finite K] [CharP K 2]

theorem actsCyclicallyOn_point (hf : IsCoord LM H ⊥ π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {v₀ : M} (hv₀ : v₀ ≠ 0) {U : Subgroup W} (hU : ∀ w, w ∈ U ↔ ∃ t : K, f w = t • v₀)
    {S : Subgroup (MulAut W)} (hS2 : IsPGroup 2 S) (hSH : ∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H)
    (hSU : S ≤ Ch11.SecA.stabW U) : Ch11.SecB.ActsCyclicallyOn S U := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hSH' : ∀ s ∈ S, ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun s hs h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have hsl : ∀ s : ↥S, ∃ σ : K →+* K, ∀ c x,
      hf.autMap s (bot_maps (s : MulAut W)) (c • x) =
        σ c • hf.autMap s (bot_maps (s : MulAut W)) x := fun s =>
    hf.exists_semilinear hcomm hv₀ s (bot_maps (s : MulAut W)) (bot_maps ((s : MulAut W)⁻¹))
      (hSH' s s.2)
  choose σ hσ using hsl
  have huniq : ∀ (s : ↥S) (τ : K →+* K), (∀ c x, hf.autMap s (bot_maps (s : MulAut W)) (c • x) =
      τ c • hf.autMap s (bot_maps (s : MulAut W)) x) → τ = σ s := by
    intro s τ hτ
    ext c
    exact smul_left_injective K (autMap_ne_zero hf s hv₀) ((hτ c v₀).symm.trans (hσ s c v₀))
  have hσmul : ∀ s t : ↥S, σ (s * t) = (σ s).comp (σ t) := by
    intro s t
    refine (huniq (s * t) _ fun c x => ?_).symm
    rw [Subgroup.coe_mul, autMap_mul, autMap_mul, hσ t, hσ s]
    rfl
  have hσone : σ 1 = RingHom.id K := (huniq 1 _ fun c x => by
    simp only [OneMemClass.coe_one, autMap_one, RingHom.id_apply]).symm
  have hbij : ∀ s, Function.Bijective (σ s) := fun s =>
    ⟨(σ s).injective, Finite.surjective_of_injective (σ s).injective⟩
  let ψ : ↥S →* (K ≃+* K) :=
    { toFun := fun s => RingEquiv.ofBijective (σ s) (hbij s)
      map_one' := RingEquiv.ext fun c => by
        change σ 1 c = c
        rw [hσone, RingHom.id_apply]
      map_mul' := fun s t => RingEquiv.ext fun c => by
        change σ (s * t) c = σ s (σ t c)
        rw [hσmul]
        rfl }
  have hcyc : IsCyclic ψ.range := @Subgroup.isCyclic _ _ (isCyclic_ringAut K) ψ.range
  obtain ⟨⟨_, s₀, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := ψ.range)
  refine ⟨s₀, s₀.2, fun s hs => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨ψ ⟨s, hs⟩, ⟨s, hs⟩, rfl⟩)
  have hk' : ψ (s₀ ^ k) = ψ ⟨s, hs⟩ := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  set r : ↥S := (s₀ ^ k)⁻¹ * ⟨s, hs⟩ with hrdef
  have hr : ∀ c, σ r c = c := by
    have h1 : ψ r = 1 := by rw [hrdef, map_mul, map_inv, hk', inv_mul_cancel]
    intro c
    exact congrArg (fun e : K ≃+* K => e c) h1
  obtain ⟨w₀, hw₀⟩ := hf.surj v₀
  have hw₀U : w₀ ∈ U := (hU w₀).mpr ⟨1, by rw [hw₀, one_smul]⟩
  obtain ⟨l, hl⟩ := (hU _).mp ((Ch11.SecA.mem_stabW.mp (hSU r.2) w₀).mp hw₀U)
  have hTr0 : hf.autMap r (bot_maps (r : MulAut W)) v₀ = l • v₀ := by
    conv_lhs => rw [← hw₀]
    rw [hf.autMap_apply, hl]
  have hTr : ∀ t : K, hf.autMap r (bot_maps (r : MulAut W)) (t • v₀) = (t * l) • v₀ := by
    intro t
    rw [hσ r, hr, hTr0, smul_smul]
  obtain ⟨m, hm⟩ := hS2 r
  have hpow : ∀ j : ℕ, ∀ t : K,
      hf.autMap ((r ^ j : ↥S) : MulAut W) (bot_maps _) (t • v₀) = (t * l ^ j) • v₀ := by
    intro j
    induction j with
    | zero => intro t; rw [pow_zero, OneMemClass.coe_one, autMap_one, pow_zero, mul_one]
    | succ j ih =>
      intro t
      rw [pow_succ, Subgroup.coe_mul, autMap_mul, hTr, ih]
      congr 1
      ring
  have hl1 : l = 1 := by
    have h1 := hpow (2 ^ m) 1
    rw [hm, OneMemClass.coe_one, autMap_one, one_mul] at h1
    have h2 : (1 : K) • v₀ = l ^ 2 ^ m • v₀ := h1
    exact eq_one_of_pow_two_pow (smul_left_injective K hv₀ h2).symm
  refine ⟨k, fun u hu => ?_⟩
  have hs_eq : s = ((s₀ ^ k : ↥S) : MulAut W) * (r : MulAut W) := by
    rw [hrdef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hs_eq, ← Subgroup.coe_zpow, MulAut.mul_apply]
  congr 1
  apply hinj
  obtain ⟨t, ht⟩ := (hU u).mp hu
  rw [← hf.autMap_apply r (bot_maps (r : MulAut W)), ht, hTr, hl1, mul_one]

end Cyclic

end CFSG.Quasithin.Vol2.KGNat
