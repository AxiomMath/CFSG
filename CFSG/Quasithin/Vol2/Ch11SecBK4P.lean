module

public import CFSG.Quasithin.Vol2.Ch11SecBK4A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin

namespace BK4

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem exists_pow_of_ringHom [Finite K] (σ : K →+* K) {p : ℕ} (hp : 0 < p) :
    ∃ r : ℕ, ∀ c : K, c ^ p = 1 → σ c = c ^ r := by
  have : NeZero p := ⟨hp.ne'⟩
  let σ' : rootsOfUnity p K →* rootsOfUnity p K :=
    { toFun := fun u => ⟨Units.map σ.toMonoidHom u, by
        rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity p (u : Kˣ)).mp u.2, map_one]⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp }
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic σ'
  refine ⟨(k % p).toNat, fun c hc => ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hc
    exact zero_ne_one hc
  set u : rootsOfUnity p K := ⟨Units.mk0 c hc0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hc)⟩ with hu
  have h1 := congrArg (fun x : rootsOfUnity p K => ((x : Kˣ) : K)) (hk u)
  simp only [σ', MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, hu, Units.val_mk0] at h1
  rw [h1]
  have hup : u ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]
    exact Subtype.ext (Units.ext (by simpa [hu] using hc))
  have h2 : u ^ k = u ^ ((k % p).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg k (by exact_mod_cast hp.ne'))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k p, zpow_add, zpow_mul, hup, one_zpow, mul_one]
  rw [h2, zpow_natCast]
  simp [hu]

variable {D : Type*} [CommGroup D] (ρ : D → M →+ M)

theorem rho_pow (hρ1 : ∀ y, ρ 1 y = y) (hρmul : ∀ d₁ d₂ y, ρ (d₁ * d₂) y = ρ d₁ (ρ d₂ y))
    (a : D) (k : ℕ) (y : M) : ρ (a ^ k) y = (⇑(ρ a))^[k] y := by
  induction k generalizing y with
  | zero => rw [pow_zero, hρ1]; rfl
  | succ k ih => rw [pow_succ, hρmul, Function.iterate_succ_apply, ih]

theorem rho_eq_of_unipotent [CharP K 2] {m : ℕ} (F : ℕ → Submodule K M) (hF0 : F 0 = ⊥)
    (hFm : F m = ⊤) (hρ1 : ∀ y, ρ 1 y = y)
    (hρmul : ∀ d₁ d₂ y, ρ (d₁ * d₂) y = ρ d₁ (ρ d₂ y)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {b : D} (hbp : b ^ p = 1) (hb : ∀ i < m, ∀ y ∈ F (i + 1), ρ b y - y ∈ F i) (y : M) :
    ρ b y = y := by
  set N : M →+ M := ρ b - AddMonoidHom.id M with hN
  have hNy : ∀ y, N y = ρ b y - y := fun y => rfl
  have hNj : ∀ j i, ∀ y ∈ F (i + j), i + j ≤ m → (⇑N)^[j] y ∈ F i := by
    intro j
    induction j with
    | zero => intro i y hy _; exact hy
    | succ j ih =>
      intro i y hy hle
      rw [Function.iterate_succ_apply]
      refine ih i (N y) ?_ (by omega)
      rw [hNy]
      exact hb (i + j) (by omega) y (by rwa [show i + j + 1 = i + (j + 1) by ring])
  have hNm : ∀ y, (⇑N)^[m] y = 0 := by
    intro y
    have h1 := hNj m 0 y (by rw [zero_add, hFm]; exact Submodule.mem_top) (by omega)
    rwa [hF0, Submodule.mem_bot] at h1
  have h2M : ∀ x : M, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have hsq : ∀ k : ℕ, ∀ y, ρ (b ^ 2 ^ k) y = y + (⇑N)^[2 ^ k] y := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [pow_zero, pow_one, Function.iterate_one, hNy]
      abel
    | succ k ih =>
      intro y
      have hadd : ∀ j a c, (⇑N)^[j] (a + c) = (⇑N)^[j] a + (⇑N)^[j] c :=
        fun j a c => iterate_map_add N j a c
      rw [pow_succ, pow_mul, sq, hρmul, ih, ih, hadd, add_assoc, ← add_assoc ((⇑N)^[2 ^ k] y),
        h2M, zero_add, ← Function.iterate_add_apply, ← two_mul, mul_comm]
  have hb2 : ∀ y, ρ (b ^ 2 ^ m) y = y := by
    intro y
    rw [hsq, show 2 ^ m = (2 ^ m - m) + m from (Nat.sub_add_cancel
      (Nat.lt_two_pow_self).le).symm, Function.iterate_add_apply, hNm, iterate_map_zero, add_zero]
  have hcop : Nat.Coprime (2 ^ m) p :=
    Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hbu : b = (b ^ 2 ^ m) ^ u := by
    rw [← pow_mul, ← Nat.mod_add_div (2 ^ m * u) p, hu, pow_add, pow_mul, hbp, one_pow,
      mul_one, pow_one]
  rw [hbu, rho_pow ρ hρ1 hρmul]
  exact Function.iterate_fixed (hb2 y) u

theorem conj_eq_pow_of_flag [Finite K] [CharP K 2] [Finite M] {m : ℕ} (F : ℕ → Submodule K M)
    (hF0 : F 0 = ⊥) (hFm : F m = ⊤)
    (hstep : ∀ i < m, ∃ e ∈ F (i + 1), e ∉ F i ∧ ∀ y ∈ F (i + 1), ∃ c : K, y - c • e ∈ F i)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hDp : ∀ d : D, d ^ p = 1) (hρ1 : ∀ y, ρ 1 y = y)
    (hρmul : ∀ d₁ d₂ y, ρ (d₁ * d₂) y = ρ d₁ (ρ d₂ y))
    (hρlin : ∀ d (c : K) y, ρ d (c • y) = c • ρ d y) (hρF : ∀ d i, ∀ y ∈ F i, ρ d y ∈ F i)
    (T : M →+ M) (σ : K →+* K) (hT : ∀ (c : K) y, T (c • y) = σ c • T y)
    (hTinj : Function.Injective T) (hTF : ∀ i, ∀ y ∈ F i, T y ∈ F i) (τ : D → D)
    (hτ : ∀ d y, T (ρ d y) = ρ (τ d) (T y)) :
    ∃ r : ℕ, ∀ d y, ρ (τ d) y = ρ (d ^ r) y := by
  obtain ⟨r, hr⟩ := exists_pow_of_ringHom σ hp.pos
  refine ⟨r, fun d y => ?_⟩
  set b := τ d * d ^ (r * (p - 1)) with hb
  have hstepb : ∀ i < m, ∀ y ∈ F (i + 1), ρ b y - y ∈ F i := by
    intro i hi
    obtain ⟨e, he, he', hdec⟩ := hstep i hi
    have hscal : ∀ a : D, ∃ c : K, ∀ y ∈ F (i + 1), ρ a y - c • y ∈ F i := by
      intro a
      obtain ⟨c, hc⟩ := hdec _ (hρF a (i + 1) e he)
      refine ⟨c, fun y hy => ?_⟩
      obtain ⟨c', hc'⟩ := hdec y hy
      have e1 : ρ a y - c • y = c' • (ρ a e - c • e) + (ρ a (y - c' • e) - c • (y - c' • e)) := by
        rw [map_sub, hρlin, smul_sub, smul_sub, smul_smul, smul_smul, mul_comm c c']
        abel
      rw [e1]
      exact (F i).add_mem ((F i).smul_mem _ hc) ((F i).sub_mem (hρF a i _ hc')
        ((F i).smul_mem _ hc'))
    have huniq : ∀ c c' : K, c • e - c' • e ∈ F i → c = c' := by
      intro c c' h
      by_contra hne
      rw [← sub_smul] at h
      exact he' ((Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h)
    have hmul : ∀ a₁ a₂ : D, ∀ c₁ c₂ : K, (∀ y ∈ F (i + 1), ρ a₁ y - c₁ • y ∈ F i) →
        (∀ y ∈ F (i + 1), ρ a₂ y - c₂ • y ∈ F i) →
        ∀ y ∈ F (i + 1), ρ (a₁ * a₂) y - (c₁ * c₂) • y ∈ F i := by
      intro a₁ a₂ c₁ c₂ h₁ h₂ y hy
      have e1 : ρ (a₁ * a₂) y - (c₁ * c₂) • y =
          ρ a₁ (ρ a₂ y - c₂ • y) + c₂ • (ρ a₁ y - c₁ • y) := by
        rw [hρmul, map_sub, hρlin, smul_sub, smul_smul, mul_comm c₂ c₁]
        abel
      rw [e1]
      exact (F i).add_mem (hρF a₁ i _ (h₂ y hy)) ((F i).smul_mem _ (h₁ y hy))
    have hpow : ∀ a : D, ∀ c : K, (∀ y ∈ F (i + 1), ρ a y - c • y ∈ F i) →
        ∀ k : ℕ, ∀ y ∈ F (i + 1), ρ (a ^ k) y - c ^ k • y ∈ F i := by
      intro a c h k
      induction k with
      | zero =>
        intro y _
        rw [pow_zero, pow_zero, hρ1, one_smul, sub_self]
        exact (F i).zero_mem
      | succ k ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
    obtain ⟨c, hc⟩ := hscal d
    obtain ⟨c', hc'⟩ := hscal (τ d)
    have hcp : c ^ p = 1 := by
      have h1 := hpow d c hc p e he
      rw [hDp, hρ1] at h1
      exact (huniq _ _ (by rw [one_smul]; exact h1)).symm
    have hTe : T e ∈ F (i + 1) := hTF _ e he
    have hTe' : T e ∉ F i := by
      intro h
      have hinj : Function.Injective (fun z : F i => (⟨T z, hTF i z z.2⟩ : F i)) :=
        fun a b hab => Subtype.ext (hTinj (congrArg Subtype.val hab))
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨T e, h⟩
      have : (z : M) = e := hTinj (congrArg Subtype.val hz)
      exact he' (this ▸ z.2)
    have hcc : c' = σ c := by
      have h1 := hc' (T e) hTe
      rw [← hτ] at h1
      have h2 : T (ρ d e) - σ c • T e ∈ F i := by
        have := hTF i _ (hc e he)
        rwa [map_sub, hT] at this
      have h3 : (σ c - c') • T e ∈ F i := by
        have h4 := (F i).sub_mem h1 h2
        rwa [show T (ρ d e) - c' • T e - (T (ρ d e) - σ c • T e) = (σ c - c') • T e by
          rw [sub_smul]; abel] at h4
      by_contra hne
      exact hTe' ((Submodule.smul_mem_iff _ (sub_ne_zero.mpr (Ne.symm hne))).mp h3)
    have h1 := hmul _ _ _ _ hc' (hpow d c hc (r * (p - 1)))
    have hsc : c' * c ^ (r * (p - 1)) = 1 := by
      rw [hcc, hr c hcp, ← pow_add, show r + r * (p - 1) = p * r by
        rcases Nat.exists_eq_add_of_le hp.one_lt.le with ⟨k, hk⟩
        subst hk
        simp only [Nat.add_sub_cancel_left]
        ring, pow_mul, hcp, one_pow]
    intro y hy
    have := h1 y hy
    rwa [hsc, one_smul] at this
  have hbp : b ^ p = 1 := hDp b
  have hρb := rho_eq_of_unipotent ρ F hF0 hFm hρ1 hρmul hp hp2 hbp hstepb
  have hd : d ^ (r * (p - 1)) * d ^ r = 1 := by
    rw [← pow_add, show r * (p - 1) + r = p * r by
      rcases Nat.exists_eq_add_of_le hp.one_lt.le with ⟨k, hk⟩
      subst hk
      simp only [Nat.add_sub_cancel_left]
      ring, pow_mul, hDp, one_pow]
  calc ρ (τ d) y = ρ (τ d) (ρ (d ^ (r * (p - 1)) * d ^ r) y) := by rw [hd, hρ1]
    _ = ρ b (ρ (d ^ r) y) := by rw [hρmul, hb, hρmul]
    _ = ρ (d ^ r) y := hρb _

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
