module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinPairing

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

namespace LinSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem implements_inj (S : LinSetting p q₀ d k K ψ E) {e e' : MulAut K} {x : GL (Fin d) k}
    (h : Implements S.π e x) (h' : Implements S.π e' x) : e = e' := by
  ext y
  obtain ⟨h0, rfl⟩ := S.surj y
  let m : LargeEvenSLGroup (Fin d) k := ⟨x * h0 * x⁻¹, conj_mem_sl x h0.2⟩
  rw [h h0 m rfl, h' h0 m rfl]

theorem exists_primitive (S : LinSetting p q₀ d k K ψ E) : ∃ ζ : kˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨ω, hω⟩ := TypeA.exists_isPrimitiveRoot S.hp S.dvd_card_sub_one
  refine ⟨Units.mk0 ω (hω.ne_zero S.hp.ne_zero), IsPrimitiveRoot.coe_units_iff.mp ?_⟩
  simpa using hω

theorem isLift_scalar (S : LinSetting p q₀ d k K ψ E) {c : kˣ} (hc : c ^ p = 1) :
    S.IsLift (Matrix.GeneralLinearGroup.scalar (Fin d) c) :=
  ⟨by rw [← map_pow, hc, map_one], 1, E.one_mem, implements_one_of_scalar ⟨c, rfl⟩⟩

theorem IsLift.mul (S : LinSetting p q₀ d k K ψ E) {x y : GL (Fin d) k} (hx : S.IsLift x)
    (hy : S.IsLift y) : S.IsLift (x * y) := by
  obtain ⟨hxp, e, he, hxe⟩ := hx
  obtain ⟨hyp, f, hf, hyf⟩ := hy
  refine ⟨?_, e * f, E.mul_mem he hf, hxe.mul hyf⟩
  have hc : Commute x y := S.isLift_comm ⟨hxp, e, he, hxe⟩ ⟨hyp, f, hf, hyf⟩
  rw [hc.mul_pow, hxp, hyp, one_mul]

theorem IsLift.inv (S : LinSetting p q₀ d k K ψ E) {x : GL (Fin d) k} (hx : S.IsLift x) :
    S.IsLift x⁻¹ := by
  obtain ⟨hxp, e, he, hxe⟩ := hx
  exact ⟨by rw [inv_pow, hxp, inv_one], e⁻¹, E.inv_mem he, hxe.inv⟩

theorem IsLift.pow (S : LinSetting p q₀ d k K ψ E) {x : GL (Fin d) k} (hx : S.IsLift x)
    (n : ℕ) : S.IsLift (x ^ n) := by
  obtain ⟨hxp, e, he, hxe⟩ := hx
  exact ⟨by rw [← pow_mul, mul_comm, pow_mul, hxp, one_pow], e ^ n, E.pow_mem he n, hxe.pow n⟩

theorem exists_map_tau_of_isLift (S : LinSetting p q₀ d k K ψ E) {x : GL (Fin d) k}
    (hx : S.IsLift x) : ∃ c : kˣ, c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.map S.τ.toRingHom x = Matrix.GeneralLinearGroup.scalar (Fin d) c * x := by
  obtain ⟨hxp, e, he, hxe⟩ := hx
  obtain ⟨c, hcp, hc⟩ := S.exists_semi_eq S.ψ_impl (S.conj_ψ he) hxp hxe
  refine ⟨c, hcp, ?_⟩
  rw [← hc, semi_apply, one_mul, inv_one, mul_one]

theorem card_E_mul_le (S : LinSetting p q₀ d k K ψ E) :
    Nat.card E * p ≤ Nat.card {x : GL (Fin d) k // S.IsLift x} := by
  obtain ⟨ζ, hζ⟩ := S.exists_primitive
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  choose L hLp hLi using fun e : E => S.exists_lift e.2
  let f : E × Fin p → {x : GL (Fin d) k // S.IsLift x} := fun ei =>
    ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (ei.2 : ℕ)) * L ei.1,
      IsLift.mul S (S.isLift_scalar (by rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]))
        ⟨hLp ei.1, ei.1, ei.1.2, hLi ei.1⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨e, i⟩ ⟨e', i'⟩ h
    have hval : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i : ℕ)) * L e =
        Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i' : ℕ)) * L e' := congrArg Subtype.val h
    have h1 : Implements S.π e (Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i' : ℕ)) * L e') := by
      rw [← hval]; exact (hLi e).scalar_mul ⟨_, rfl⟩
    have hee : e = e' := Subtype.ext (S.implements_inj h1 ((hLi e').scalar_mul ⟨_, rfl⟩))
    subst hee
    have hsc : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i : ℕ)) =
        Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i' : ℕ)) := mul_right_cancel hval
    have hd1 : 1 ≤ d := le_trans (by norm_num) S.three_le
    have hii : ζ ^ (i : ℕ) = ζ ^ (i' : ℕ) := scalar_injective hd1 hsc
    have := hζ.pow_inj i.2 i'.2 hii
    exact Prod.ext rfl (Fin.ext this)
  calc Nat.card E * p = Nat.card (E × Fin p) := by rw [Nat.card_prod, Nat.card_fin]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

theorem card_lifts_le (S : LinSetting p q₀ d k K ψ E) {x₀ : GL (Fin d) k} (hx₀ : S.IsLift x₀)
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ p)
    (hτx₀ : Matrix.GeneralLinearGroup.map S.τ.toRingHom x₀ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ * x₀) :
    Nat.card {x : GL (Fin d) k // S.IsLift x} ≤
      p * Nat.card {x : GL (Fin d) k //
        S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x} := by
  haveI : NeZero p := ⟨S.hp.ne_zero⟩
  have hlog : ∀ x : {x : GL (Fin d) k // S.IsLift x}, ∃ i : Fin p,
      Matrix.GeneralLinearGroup.map S.τ.toRingHom x.1 =
        Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ (i : ℕ)) * x.1 := by
    intro x
    obtain ⟨c, hcp, hc⟩ := S.exists_map_tau_of_isLift x.2
    obtain ⟨i, hi, hic⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p c).mpr hcp)
    exact ⟨⟨i, hi⟩, by rw [hc, ← hic]⟩
  choose ι hι using hlog
  have hcen : ∀ (c : kˣ) (z : GL (Fin d) k),
      Matrix.GeneralLinearGroup.scalar (Fin d) c * z = z * Matrix.GeneralLinearGroup.scalar (Fin d) c :=
    fun c z => (Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩) z).symm
  have hpow : ∀ n : ℕ, (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * x₀) ^ n =
      Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ n) * x₀ ^ n := fun n => by
    have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) x₀ := hcen ζ x₀
    rw [hc.mul_pow, map_pow]
  have hfix : ∀ x : {x : GL (Fin d) k // S.IsLift x},
      Matrix.GeneralLinearGroup.map S.τ.toRingHom (x.1 * (x₀ ^ (ι x : ℕ))⁻¹) =
        x.1 * (x₀ ^ (ι x : ℕ))⁻¹ := by
    intro x
    have key : ∀ (c : kˣ) (y z : GL (Fin d) k),
        Matrix.GeneralLinearGroup.scalar (Fin d) c * y *
          (z * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹) = y * z := by
      intro c y z
      rw [hcen c y, mul_assoc, ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin d) c), hcen c z]
      group
    rw [map_mul, map_inv, map_pow, hι x, hτx₀, hpow, mul_inv_rev]
    exact key _ _ _
  let g : {x : GL (Fin d) k // S.IsLift x} → Fin p × {x : GL (Fin d) k //
      S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x} := fun x =>
    (ι x, ⟨x.1 * (x₀ ^ (ι x : ℕ))⁻¹,
      IsLift.mul S x.2 (IsLift.inv S (IsLift.pow S hx₀ _)), hfix x⟩)
  have hg : Function.Injective g := by
    intro x y h
    have h1 : ι x = ι y := congrArg Prod.fst h
    have h2 : x.1 * (x₀ ^ (ι x : ℕ))⁻¹ = y.1 * (x₀ ^ (ι y : ℕ))⁻¹ :=
      congrArg (fun z => (z.2 : {x : GL (Fin d) k //
        S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x}).1) h
    rw [h1] at h2
    exact Subtype.ext (mul_right_cancel h2)
  calc Nat.card {x : GL (Fin d) k // S.IsLift x}
      ≤ Nat.card (Fin p × {x : GL (Fin d) k //
          S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x}) :=
        Nat.card_le_card_of_injective g hg
    _ = p * Nat.card {x : GL (Fin d) k //
          S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x} := by
        rw [Nat.card_prod, Nat.card_fin]

end LinSetting

end CFSG.StandardType.GGL45TA
