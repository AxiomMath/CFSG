module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFf
public import CFSG.Quasithin.Vol2.Ch10SecKGCFb
public import CFSG.Quasithin.Vol2.Ch10SecKGCFe
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ) {V : Type} [CommGroup V] [Finite V]

theorem eq_one_orth [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    {H : Subgroup (MulAut V)} {π : ↥(StatedSL 2 K) →* ↥H} (hπ : Function.Bijective π)
    {BE : V ≃* ↥(hermSub a (Fin 2) K)}
    (hBE : ∀ γ v, hmat a (BE (((π γ : ↥H) : MulAut V) v)) =
      smat γ * hmat a (BE v) * (frobPow a (smat γ))ᵀ)
    (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c)
    (hSfix : ∀ c, (∀ τ ∈ Subgroup.zpowers (frobAut (K := K) a), τ c = c) ↔ c ^ 2 ^ a = c)
    (hScard : Nat.card S = 2 ^ a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrH : ¬ r ∣ Nat.card H) {x : MulAut V} (hx : IsSemi (smH a BE S hS) x 1)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hxr : x ^ r = 1) : x = 1 := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxH' := inv_conj_mem hxH
  have hs := isScalarAct_smH a BE S hS
  let eρ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H :=
    (specialLinearGroupEquivStatedSL 2 K).trans (MulEquiv.ofBijective π hπ)
  let E : Matrix.SpecialLinearGroup (Fin 2) K →* MulAut V := H.subtype.comp eρ.toMonoidHom
  have hEinj : Function.Injective E := Subtype.val_injective.comp eρ.injective
  have hEH : ∀ g, E g ∈ H := fun g => (eρ g).2
  have hEsurj : ∀ h ∈ H, ∃ g, E g = h := fun h hh =>
    ⟨eρ.symm ⟨h, hh⟩, by simp [E]⟩
  have hBE' : ∀ g v, hmat a (BE (E g v)) = (g : Matrix (Fin 2) (Fin 2) K) * hmat a (BE v) *
      (frobPow a (g : Matrix (Fin 2) (Fin 2) K))ᵀ := fun g v => hBE _ v
  have hcardH : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card H :=
    Nat.card_congr eρ.toEquiv
  let cx : ↥H ≃* ↥H :=
    { toFun := fun h => ⟨x * h * x⁻¹, hxH h h.2⟩
      invFun := fun h => ⟨x⁻¹ * h * x, hxH' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h k => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨M, τ, hα⟩ := exists_conj_mul_slFieldAut ((eρ.trans cx).trans eρ.symm)
  have key1 : ∀ g, x * E g * x⁻¹ = E (M * slFieldAut K τ g * M⁻¹) := by
    intro g
    have h1 : ((eρ.trans cx).trans eρ.symm) g = M * slFieldAut K τ g * M⁻¹ := by
      rw [hα, MulAut.mul_apply, MulAut.conj_apply]
    rw [← h1]
    change x * E g * x⁻¹ = ((eρ (eρ.symm (cx (eρ g))) : ↥H) : MulAut V)
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hΦE : ∀ g, phiMap a BE τ * E g * (phiMap a BE τ)⁻¹ = E (slFieldAut K τ g) := by
    intro g
    ext v
    apply BE.injective
    apply hmat_injective a
    have h2 : (hmat a (BE ((phiMap a BE τ)⁻¹ v))).map τ = hmat a (BE v) := by
      rw [← hmat_phiMap, MulAut.apply_inv_self]
    rw [MulAut.mul_apply, MulAut.mul_apply, hmat_phiMap, hBE', hBE', map_twist, h2]
    rfl
  obtain ⟨f, hf⟩ : ∃ f : MulAut V, f = (phiMap a BE τ)⁻¹ * (E M)⁻¹ * x := ⟨_, rfl⟩
  have hfE : ∀ g, f * E g = E g * f := by
    intro g
    have h1 : x * E g = E (M * slFieldAut K τ g * M⁻¹) * x := by
      rw [← key1 g]
      group
    have h2 : (phiMap a BE τ)⁻¹ * E (slFieldAut K τ g) = E g * (phiMap a BE τ)⁻¹ := by
      rw [← hΦE g]
      group
    calc f * E g = (phiMap a BE τ)⁻¹ * (E M)⁻¹ * (x * E g) := by rw [hf]; group
      _ = (phiMap a BE τ)⁻¹ * E (slFieldAut K τ g) * (E M)⁻¹ * x := by
          rw [h1, map_mul, map_mul, map_inv]
          group
      _ = E g * f := by rw [h2, hf]; group
  obtain ⟨μ, hμ⟩ := smH_commutant a ha hK hBE S hS f.toMonoidHom fun h hh v => by
    obtain ⟨g, rfl⟩ := hEsurj h hh
    have := congrArg (fun φ : MulAut V => φ v) (hfE g)
    simpa [MulAut.mul_apply] using this
  have hμ' : ∀ v, f v = smH a BE S hS μ v := hμ
  have hsmc : ∀ c v, smH a BE S hS c (E M v) = E M (smH a BE S hS c v) := fun c v =>
    smH_comm a hπ.2 hBE S hS _ (hEH M) c v
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V, hmat a (BE w₀) = C10P34.e11 1 :=
    ⟨BE.symm ⟨Multiplicative.ofAdd (C10P34.e11 1), C10P34.isHerm_e11_one a⟩, by
      rw [MulEquiv.apply_symm_apply]
      rfl⟩
  have hw₀1 : w₀ ≠ 1 := fun h => by
    rw [h, map_one, hmat_one] at hw₀
    have := congrFun (congrFun hw₀ 0) 0
    simp [C10P34.e11] at this
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 := hμ' (f⁻¹ w₀)
    rw [MulAut.apply_inv_self, h0, hs.zero] at h1
    exact hw₀1 h1
  have hxe : x = E M * phiMap a BE τ * f := by rw [hf]; group
  have hτS : ∀ c : K, c ^ 2 ^ a = c → τ c = c := by
    intro c hc
    let c' : S := ⟨c, (hS c).mpr hc⟩
    have hv₀ : smH a BE S hS μ (smH a BE S hS μ⁻¹ w₀) = w₀ := by
      rw [← hs.mul, mul_inv_cancel₀ hμ0, hs.one]
    have h1 := hx c' (smH a BE S hS μ⁻¹ w₀)
    rw [hxe, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hμ', hμ',
      hsmc] at h1
    have h2 := (E M).injective h1
    rw [← hs.mul, mul_comm, hs.mul, hv₀] at h2
    have h3 := congrArg (fun v => hmat a (BE v) 0 0) h2
    simp only [hmat_phiMap, hmat_smH, hw₀] at h3
    simpa [C10P34.e11, c'] using h3
  have hτP : τ ∈ Subgroup.zpowers (frobAut (K := K) a) :=
    mem_of_fix Nat.prime_two (by omega : 1 ≤ 2 * a) hK fun c hc => hτS c ((hSfix c).mp hc)
  have hτ2 : ∀ y : K, τ (τ y) = y := by
    have hcard : Nat.card (Subgroup.zpowers (frobAut (K := K) a)) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (frobAut_sq a hK) (frobAut_ne_one a ha hK)
    have h1 := pow_card_eq_one' (x := (⟨τ, hτP⟩ : Subgroup.zpowers (frobAut (K := K) a)))
    rw [hcard] at h1
    have h2 : τ ^ 2 = 1 := congrArg Subtype.val h1
    intro y
    have h3 := congrArg (fun ρ : K ≃+* K => ρ y) h2
    rw [pow_two] at h3
    exact h3
  have hΦf : phiMap a BE τ * f = f * phiMap a BE τ := by
    ext v
    apply BE.injective
    apply hmat_injective a
    rw [MulAut.mul_apply, MulAut.mul_apply, hμ', hμ', hmat_phiMap, hmat_smH, hmat_smH,
      hmat_phiMap]
    ext i j
    simp [hτS μ ((hS μ).mp μ.2)]
  have hΦΦ : phiMap a BE τ * phiMap a BE τ = 1 := by
    ext v
    apply BE.injective
    apply hmat_injective a
    rw [MulAut.mul_apply, hmat_phiMap, hmat_phiMap, MulAut.one_apply]
    ext i j
    simp [hτ2]
  have h1 : phiMap a BE τ * E M = E (slFieldAut K τ M) * phiMap a BE τ := by
    rw [← hΦE M]
    group
  have hx2 : x * x = E (M * slFieldAut K τ M) * (f * f) := by
    rw [hxe]
    calc E M * phiMap a BE τ * f * (E M * phiMap a BE τ * f)
        = E M * phiMap a BE τ * (f * E M) * phiMap a BE τ * f := by group
      _ = E M * (phiMap a BE τ * E M) * (f * phiMap a BE τ) * f := by rw [hfE M]; group
      _ = E M * E (slFieldAut K τ M) * (phiMap a BE τ * phiMap a BE τ) * (f * f) := by
          rw [h1, ← hΦf]
          group
      _ = E (M * slFieldAut K τ M) * (f * f) := by rw [hΦΦ, map_mul]; group
  set N := M * slFieldAut K τ M with hN
  have hw : (x * x) ^ r = 1 := by rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hxr, one_pow]
  have hcN : Commute (E N) (f * f) := Commute.mul_right (hfE N).symm (hfE N).symm
  rw [hx2, hcN.mul_pow] at hw
  have hNr : N ^ r = 1 := by
    apply eq_one_of_mem_center_sl2
    rw [Subgroup.mem_center_iff]
    intro g
    apply hEinj
    rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_left hw]
    exact ((Commute.mul_right (hfE g).symm (hfE g).symm).pow_right r).inv_right.eq
  have hN1 : N = 1 := eq_one_of_pow_prime hr (by rwa [hcardH]) hNr
  rw [hN1, map_one, one_pow, one_mul] at hw
  have hpow : ∀ (k : ℕ) v, ((f * f) ^ k) v = smH a BE S hS ((μ * μ) ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, pow_zero, MulAut.one_apply, hs.one]
    | succ k ih =>
      intro v
      rw [pow_succ (f * f) k, MulAut.mul_apply, ih, MulAut.mul_apply, hμ' (f v), hμ' v,
        ← hs.mul, ← hs.mul, mul_assoc, pow_succ (μ * μ) k]
  have hμr : (μ * μ) ^ r = 1 := by
    have h2 := hpow r w₀
    rw [hw, MulAut.one_apply] at h2
    exact hs.eq_of_eq hw₀1 (h2.symm.trans (hs.one w₀).symm)
  have hμμ : μ * μ = 1 := by
    refine eq_one_of_pow_prime_of_dvd hr (N := Nat.card H) ?_ hrH hμr
    rw [hScard, ← hcardH, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    have e1 : (2 ^ (2 * a)) ^ 2 - 1 = (2 ^ a) ^ 4 - 1 ^ 4 := by
      rw [one_pow, ← pow_mul, ← pow_mul]
      ring_nf
    rw [e1]
    exact Dvd.dvd.mul_left (Nat.sub_dvd_pow_sub_pow _ _ _) _
  have hff : f * f = 1 := by
    ext v
    rw [MulAut.mul_apply, hμ' (f v), hμ' v, ← hs.mul, hμμ, hs.one, MulAut.one_apply]
  have hxx : x ^ 2 = 1 := by rw [pow_two, hx2, hN1, hff, map_one, mul_one]
  have hco : Nat.Coprime 2 r := Nat.coprime_two_left.mpr (hr.odd_of_ne_two hr2)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_of_pow_eq_one hxx)
    (orderOf_dvd_of_pow_eq_one hxr))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
