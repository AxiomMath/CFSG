module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2 CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem exists_two_mul_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ t : ZMod p, 2 * t = 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  refine ⟨((ZMod.unitOfCoprime 2 hcop)⁻¹ : (ZMod p)ˣ), ?_⟩
  have h := Units.mul_inv (ZMod.unitOfCoprime 2 hcop)
  rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at h

theorem reflection_comap_comm {Y H : Type*} [Group Y] [Group H] {φ : Y →* H}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {p d : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (e : Multiplicative (Fin d → ZMod p) →* H)
    (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (hc : ∀ i, c i (Pi.single i 1) = 2)
    (n : Fin d → H)
    (hn : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd (v - c i v • Pi.single i 1))) :
    ∀ x ∈ e.range.comap φ, ∀ y ∈ e.range.comap φ, x * y = y * x := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨t, ht⟩ := exists_two_mul_eq_one hp hp2
  have hcomm : ∀ a b, Commute (e a) (e b) := fun a b => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hpow : ∀ a, e a ^ p = 1 := fun a => by
    rw [← map_pow]
    convert map_one e
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      Pi.zero_apply]
  have hbasis : ∀ i j, liftComm φ hφ (e (.ofAdd (Pi.single i 1))) (e (.ofAdd (Pi.single j 1))) =
      1 := by
    intro i j
    set ei : Fin d → ZMod p := Pi.single i 1
    set τ : ZMod p := c i (Pi.single j 1) * t
    set k : Fin d → ZMod p := Pi.single j 1 - τ • ei
    have hk : c i k = 0 := by
      simp only [k, τ, ei]
      rw [map_sub, LinearMap.map_smul, hc, smul_eq_mul, mul_assoc, mul_comm t, ht, mul_one,
        sub_self]
    have hsplit : (Multiplicative.ofAdd (Pi.single j 1) : Multiplicative (Fin d → ZMod p)) =
        Multiplicative.ofAdd k * Multiplicative.ofAdd (τ • ei) := by
      rw [← ofAdd_add, sub_add_cancel]
    rw [hsplit, map_mul, liftComm_mul_right hφ hker (hcomm _ _)]
    have hfirst : liftComm φ hφ (e (.ofAdd ei)) (e (.ofAdd k)) = 1 := by
      refine liftComm_eq_one_of_conj_inv hφ hker hodd (hcomm _ _) (hpow _) (n i) ?_ ?_
      · rw [hn, hc, ← map_inv]
        congr 1
        rw [← ofAdd_neg]
        congr 1
        simp only [ei]
        rw [two_smul]
        abel
      · rw [hn, hk, zero_smul, sub_zero]
    have hsecond : liftComm φ hφ (e (.ofAdd ei)) (e (.ofAdd (τ • ei))) = 1 := by
      have hτ : (Multiplicative.ofAdd (τ • ei) : Multiplicative (Fin d → ZMod p)) =
          Multiplicative.ofAdd ei ^ τ.val := by
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
      rw [hτ, map_pow, liftComm_swap, liftComm_pow_left hφ hker (hcomm _ _), liftComm_self,
        one_pow, inv_one]
    rw [hfirst, hsecond, one_mul]
  have hall : ∀ a b, liftComm φ hφ (e a) (e b) = 1 :=
    liftComm_eq_one_of_closure hφ hker e closure_range_single_eq_top (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hbasis i j)
  exact fun x hx y hy => mul_comm_of_liftComm_eq_one hφ hker (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hall a b) hx hy

theorem reflection_normalizers_actual_central_cover_fixed_hyperplane_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {H : Type*} [Group H] (φ : Y →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 2 ≤ d)
    (e : Multiplicative (Fin d → ZMod p) →* H) (he : Function.Injective e)
    (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (hc : ∀ i, c i (Pi.single i 1) = 2)
    (n : Fin d → H)
    (hn : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd (v - c i v • Pi.single i 1)))
    (hn1 : orderOf (n ⟨0, by omega⟩) = 2) :
    (∀ x ∈ e.range.comap φ, ∀ y ∈ e.range.comap φ, x * y = y * x) ∧
      ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
        IsElemAbelian p A ∧ Nat.card A = p ^ (d - 1) ∧ d - 1 ≤ localRank p G := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpow : ∀ a, e a ^ p = 1 := fun a => by
    rw [← map_pow]
    convert map_one e
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      Pi.zero_apply]
  obtain ⟨t, ht⟩ := exists_two_mul_eq_one hp hp2
  have hF := reflection_comap_comm hφ hker hp hp2 e c hc n hn
  refine ⟨hF, ?_⟩
  set i₀ : Fin d := ⟨0, by omega⟩
  set ψ : Multiplicative (Fin d → ZMod p) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicative (c i₀).toAddMonoidHom with hψ
  have hψs : Function.Surjective ψ := by
    intro s
    refine ⟨.ofAdd ((Multiplicative.toAdd s * t) • Pi.single i₀ 1), ?_⟩
    apply Multiplicative.toAdd.injective
    change c i₀ ((Multiplicative.toAdd s * t) • Pi.single i₀ 1) = Multiplicative.toAdd s
    rw [LinearMap.map_smul, hc, smul_eq_mul, mul_assoc, mul_comm t, ht, mul_one]
  have hD₀D : ψ.ker.map e ≤ e.range := Subgroup.map_le_range e _
  have hcard : Nat.card (ψ.ker.map e) = p ^ (d - 1) := by
    rw [Subgroup.card_map_of_injective he]
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hψs, Subgroup.card_top] at h1
    have h2 : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
    have h3 : Nat.card (Multiplicative (Fin d → ZMod p)) = p ^ d := by
      change Nat.card (Fin d → ZMod p) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [h2, h3] at h1
    have h4 : p ^ d = p ^ (d - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hzD : ∀ x ∈ ψ.ker.map e, Commute (n i₀) x := by
    rintro _ ⟨a, ha, rfl⟩
    have hv : c i₀ (Multiplicative.toAdd a) = 0 := congrArg Multiplicative.toAdd ha
    have := hn i₀ (Multiplicative.toAdd a)
    rw [hv, zero_smul, sub_zero, ofAdd_toAdd] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hφ hker hp hp2
      (fun x hx => by obtain ⟨a, -, rfl⟩ := hx; exact hpow a)
      (fun x hx y hy => hF x (Subgroup.comap_mono hD₀D hx) y (Subgroup.comap_mono hD₀D hy))
      hcard.ge hn1 hzD
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank⟩

end CFSG.RankThree.CentralCover
