module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Vol2.KGNatSL3Par

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix

namespace BK2

@[expose] def IsSemiF {K M W : Type*} [Field K] [AddCommGroup M] [Module K M] [Group W]
    (f : W → M) (σ : K →+* K) (a : MulAut W) : Prop :=
  ∀ (c : K) (w w' : W), f w' = c • f w → f (a w') = σ c • f (a w)

section Field

variable {K : Type} [Field K] [Finite K]

theorem ringHom_eq_of_involutive {n : ℕ} (hK : Nat.card K = 2 ^ n) {σ τ : K →+* K}
    (hσ : ∀ c, σ (σ c) = c) (hτ : ∀ c, τ (τ c) = c) (hσ1 : ∃ c, σ c ≠ c)
    (hτ1 : ∃ c, τ c ≠ c) : ∀ c, σ c = τ c := by
  classical
  have hcyc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    hK).2
  have : Finite (RingAut K) := Finite.of_injective (fun e : RingAut K => (e : K → K))
    fun a b h => RingEquiv.ext (congrFun h)
  have : Fintype (RingAut K) := Fintype.ofFinite _
  let σ' : RingAut K := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let τ' : RingAut K := RingEquiv.ofBijective τ
    ⟨τ.injective, Finite.surjective_of_injective τ.injective⟩
  have hσ2 : σ' ^ 2 = 1 := RingEquiv.ext fun c => by
    rw [sq]
    exact hσ c
  have hτ2 : τ' ^ 2 = 1 := RingEquiv.ext fun c => by
    rw [sq]
    exact hτ c
  have hσne : σ' ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := hσ1
    exact hc (congrArg (fun e : RingAut K => e c) h)
  have hτne : τ' ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := hτ1
    exact hc (congrArg (fun e : RingAut K => e c) h)
  by_contra hne
  push Not at hne
  obtain ⟨c, hc⟩ := hne
  have hστ : σ' ≠ τ' := fun h => hc (congrArg (fun e : RingAut K => e c) h)
  have hle := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
  have hsub : ({1, σ', τ'} : Finset (RingAut K)) ⊆
      Finset.univ.filter fun a : RingAut K => a ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl | rfl
    · exact ⟨Finset.mem_univ _, one_pow 2⟩
    · exact ⟨Finset.mem_univ _, hσ2⟩
    · exact ⟨Finset.mem_univ _, hτ2⟩
  have h3 : ({1, σ', τ'} : Finset (RingAut K)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, σ', τ', hσne.symm, hτne.symm, hστ, rfl⟩
  have := Finset.card_le_card hsub
  omega

end Field

section Rigid

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {W : Type} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥Γ →* ↥H} {f : W → (ι → K)}

theorem eq_of_f_eq_nat (hf : KGNat.IsCoord (KGNat.linModelNat Γ) H Z π f) {a b : MulAut W}
    (ha : a ∈ H) (hb : b ∈ H) (h : ∀ w, f (a w) = f (b w)) : a = b := by
  obtain ⟨α, hα⟩ : ∃ α : ↥Γ, π α = ⟨a, ha⟩ := hf.onto ⟨a, ha⟩
  obtain ⟨β, hβ⟩ : ∃ β : ↥Γ, π β = ⟨b, hb⟩ := hf.onto ⟨b, hb⟩
  have ha' : ((π α : ↥H) : MulAut W) = a := congrArg Subtype.val hα
  have hb' : ((π β : ↥H) : MulAut W) = b := congrArg Subtype.val hβ
  have hlin : ∀ x, ((α : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x =
      ((β : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    have e1 : f (a w) = ((α : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f w := by
      rw [← ha']
      exact (hf.act α w).trans (KGNat.linModelNat_lin Γ α (f w))
    have e2 : f (b w) = ((β : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f w := by
      rw [← hb']
      exact (hf.act β w).trans (KGNat.linModelNat_lin Γ β (f w))
    rw [← e1, ← e2]
    exact h w
  have hαβ : α = β := Subtype.ext (Units.ext (Matrix.toLin'.injective
    (LinearMap.ext fun x => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hlin x)))
  rw [← ha', ← hb', hαβ]

theorem eq_pi_of_modZ_nat (hf : KGNat.IsCoord (KGNat.linModelNat Γ) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) {τ : MulAut W}
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {γ : ↥Γ}
    (hτ : ∀ w, f (τ w) = ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f w) :
    τ = ((π γ : ↥H) : MulAut W) := by
  set g : MulAut W := ((π γ : ↥H) : MulAut W) with hg
  have hgH : g ∈ H := (π γ).2
  have hgf : ∀ w, f (g w) = ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f w :=
    fun w => (hf.act γ w).trans (KGNat.linModelNat_lin Γ γ (f w))
  have hZst : ∀ h ∈ H, ∀ z ∈ Z, (h : MulAut W).toMonoidHom z ∈ Z := fun h hh z hz => by
    rw [MulEquiv.coe_toMonoidHom, hZ h hh z hz]
    exact hz
  have hρf : ∀ w, f ((g⁻¹ * τ) w) = f w := by
    intro w
    have h2 : f (g (g⁻¹ (τ w))) = f (g w) := by rw [MulAut.apply_inv_self, hτ, hgf]
    have h3 := hf.map_eq_of_eq (hZst _ (H.inv_mem hgH)) h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self] at h3
    rw [MulAut.mul_apply]
    exact h3
  have hρi : ∀ w, f ((g⁻¹ * τ)⁻¹ w) = f w := fun w => by
    rw [← hρf ((g⁻¹ * τ)⁻¹ w), MulAut.apply_inv_self]
  have hρH : ∀ h ∈ H, (g⁻¹ * τ) * h * (g⁻¹ * τ)⁻¹ ∈ H := fun h hh => by
    have e : (g⁻¹ * τ) * h * (g⁻¹ * τ)⁻¹ = g⁻¹ * (τ * h * τ⁻¹) * g := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hgH) (hτH h hh)) hgH
  have hcomm' : ∀ h ∈ H, (g⁻¹ * τ) * h = h * (g⁻¹ * τ) := by
    intro h hh
    have h1 := eq_of_f_eq_nat hf (hρH h hh) hh fun w => by
      rw [MulAut.mul_apply, MulAut.mul_apply, hρf]
      exact hf.map_eq_of_eq (hZst h hh) (hρi w)
    calc g⁻¹ * τ * h = (g⁻¹ * τ * h * (g⁻¹ * τ)⁻¹) * (g⁻¹ * τ) := by group
      _ = h * (g⁻¹ * τ) := by rw [h1]
  have h1 : g⁻¹ * τ = 1 := KGNat.eq_one_of_commV hcomm hcomm' fun w h hh =>
    hZ h hh _ ((hf.eq_iff _ _).mp (hρf w))
  rw [← mul_inv_cancel_left g τ, h1, mul_one]

end Rigid

section Line

variable {D : FFModel} {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]
  {W : Type} [CommGroup W] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : D.Gam →* ↥H} {f : W → M}

theorem exists_line_W (hf : KGNat.IsCoord LM H Z π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    (hsq : ∀ w : W, w ^ 2 = 1) {U : Subgroup W} (hZU : Z ≤ U)
    (hst : Ch11.SecA.EndStableW H Z U) (hidx : Z.relIndex U = Nat.card K) :
    ∃ u₀ : M, u₀ ≠ 0 ∧ ∀ w, w ∈ U ↔ ∃ c : K, f w = c • u₀ := by
  have hsc := (hf.endStableW_iff hsq hcomm hZU).mp hst
  have hcard : Nat.card (hf.img U) = Nat.card K := by rw [hf.card_img, hidx]
  have h1K : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨u₀, hu₀, hne⟩ : ∃ u₀ ∈ hf.img U, u₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : hf.img U = ⊥ := (AddSubgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, AddSubgroup.card_bot] at hcard
    omega
  let φ : K → ↥(hf.img U) := fun c => ⟨c • u₀, hsc c u₀ hu₀⟩
  have hφ : Function.Injective φ := by
    intro c c' h
    have h1 : (c - c') • u₀ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact congrArg Subtype.val h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hne)
  have : Finite ↥(hf.img U) := Nat.finite_of_card_ne_zero (by omega)
  have hφs : Function.Surjective φ := (hφ.bijective_of_nat_card_le hcard.le).2
  refine ⟨u₀, hne, fun w => ?_⟩
  rw [hf.mem_iff hZU]
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hφs ⟨f w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, hc⟩
    rw [hc]
    exact hsc c u₀ hu₀

theorem exists_fixed_line [Finite W] (hf : KGNat.IsCoord LM H Z π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    (hsq : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hflag : ∀ P, QuasithinUnique.IsSylowTwoOf P H →
      ∃ U, Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U)
    (hlevi : ∀ P U, QuasithinUnique.IsSylowTwoOf P H → Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U →
      P ≤ perfectCore (H ⊓ Ch11.SecA.stabW U))
    (hpoint : ∀ P U, QuasithinUnique.IsSylowTwoOf P H →
      Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U →
      ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z)
    {B : Subgroup (MulAut W)} (hBH : B ≤ H) (hB2 : IsPGroup 2 ↥B) :
    ∃ u₀ : M, u₀ ≠ 0 ∧ ∀ c : K, ∃ w, f w = c • u₀ ∧ ∀ b ∈ B, b w = w := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨P, hBP, hP⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hBH hB2
  obtain ⟨U, hU⟩ := hflag P hP
  have hfix := KGNat.fix_of_perfect (perfectCore_perfect (H ⊓ Ch11.SecA.stabW U))
    (fun h hh z hz => hZ h (Subgroup.mem_inf.mp (perfectCore_le _ hh)).1 z hz)
    (hpoint P U hP hU)
  obtain ⟨u₀, hu₀, hline⟩ := exists_line_W hf hcomm hsq hU.1 hU.2.1 (by rw [hU.2.2.1, pow_one])
  refine ⟨u₀, hu₀, fun c => ?_⟩
  obtain ⟨w, hw⟩ := hf.surj (c • u₀)
  exact ⟨w, hw, fun b hb => hfix b (hlevi P U hP hU (hBP hb)) w ((hline w).mpr ⟨c, hw⟩)⟩

end Line

end BK2

end CFSG.Quasithin.Vol2.Ch11.SecB
