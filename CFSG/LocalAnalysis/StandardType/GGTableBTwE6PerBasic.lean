module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.StandardType

open CFSG.RankThree.CentralCover CFSG.RankThree.Classical2

namespace TwE6Per

theorem ggTorusLift_of_inverters {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (τ : (Fin d → Multiplicative (ZMod p)) →* R) (hτ : Function.Injective τ) (S : Set R)
    (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) (hSp : ∀ s ∈ S, s ^ p = 1)
    (hSinv : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ g : R,
      (g * s * g⁻¹ = s⁻¹ ∧ g * t * g⁻¹ = t) ∨ (g * t * g⁻¹ = t⁻¹ ∧ g * s * g⁻¹ = s))
    (hrange : τ.range ≤ Subgroup.closure S)
    (hinv : ∀ i, ∃ w : R,
      w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹)
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hTU : ∀ f, ∀ u ∈ U, τ f * u * (τ f)⁻¹ ∈ U) : GGTorusLift p d R := by
  intro L' _ _ ψ hψ hker _
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hlc : ∀ s ∈ S, ∀ t ∈ S, liftComm ψ hψ s t = 1 := by
    intro s hs t ht
    by_cases hst : s = t
    · subst hst
      exact liftComm_self hψ s
    obtain ⟨g, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hSinv s hs t ht hst
    · exact liftComm_eq_one_of_conj_inv hψ hker hodd (hS s hs t ht) (hSp s hs) g h1 h2
    · rw [liftComm_swap,
        liftComm_eq_one_of_conj_inv hψ hker hodd (hS t ht s hs) (hSp t ht) g h1 h2, inv_one]
  have hcommS := comap_closure_comm hψ hker hS hlc
  have hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x :=
    fun x hx y hy => hcommS x (hrange hx) y (hrange hy)
  obtain ⟨σ, hσ⟩ := TableBF4.exists_torus_section_of_comm hψ hker hodd τ hcomm hinv
  have hσi : Function.Injective σ := by
    intro a b hab
    apply hτ
    rw [← hσ, MonoidHom.comp_apply, MonoidHom.comp_apply, hab]
  obtain ⟨T, hT, hT2, hET⟩ := TableBSymp.exists_twoSubgroup_lift (E := σ.range) hψ hker hU hU2
    (by
      rintro _ ⟨f, rfl⟩ u hu
      have := hTU f u hu
      rwa [← hσ] at this)
  refine ⟨T, σ.range, hT, hT2, hET, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show σ a * σ b = σ b * σ a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul, ofAdd_zero]
      rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hσi).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
      Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨f, rfl⟩, hf⟩
    have hf' : ψ (σ f) = 1 := hf
    rw [← MonoidHom.comp_apply, hσ] at hf'
    rw [Subgroup.mem_bot, hτ (hf'.trans (map_one τ).symm), map_one]


section Inj

variable {R : Type*} [Group R]

theorem eq_one_of_inv_eq {p : ℕ} (hp : Odd p) {x : R} (hx : x ^ p = 1) (h : x⁻¹ = x) : x = 1 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel x
  obtain ⟨m, rfl⟩ := hp
  have : x ^ (2 * m + 1) = (x ^ 2) ^ m * x := by rw [pow_succ, pow_mul]
  rw [this, h2, one_pow, one_mul] at hx
  exact hx

theorem basisTorus_comm {p d : ℕ} (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) :
    Pairwise fun i j => ∀ x y : Multiplicative (ZMod p),
      Commute (TableBSymp.zmodPowHom (hb i) x) (TableBSymp.zmodPowHom (hb j) y) := by
  intro i j _ x y
  rw [TableBSymp.zmodPowHom, TableBSymp.zmodPowHom]
  simp only [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply]
  exact (hc i j).zpow_zpow _ _

@[expose] noncomputable def basisTorus {p d : ℕ} (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) : (Fin d → Multiplicative (ZMod p)) →* R :=
  MonoidHom.noncommPiCoprod (fun i => TableBSymp.zmodPowHom (hb i)) (basisTorus_comm b hb hc)

theorem basisTorus_mulSingle {p d : ℕ} [NeZero p] (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) (i : Fin d) (a : Multiplicative (ZMod p)) :
    basisTorus b hb hc (Pi.mulSingle i a) = b i ^ (Multiplicative.toAdd a).val := by
  rw [basisTorus, MonoidHom.noncommPiCoprod_mulSingle, TableBSymp.zmodPowHom_apply]

theorem torusBasis_basisTorus {p d : ℕ} [Fact p.Prime] (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) (i : Fin d) :
    TableBSymp.torusBasis (basisTorus b hb hc) i = b i := by
  rw [TableBSymp.torusBasis, basisTorus_mulSingle, toAdd_ofAdd, ZMod.val_one, pow_one]

theorem basisTorus_mem_of {p d : ℕ} [NeZero p] (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) {H : Subgroup R} {i : Fin d}
    (hH : ∀ j, j ≠ i → b j ∈ H) {f : Fin d → Multiplicative (ZMod p)} (hf : f i = 1) :
    basisTorus b hb hc f ∈ H := by
  have hmem : f ∈ H.comap (basisTorus b hb hc) := by
    rw [← Finset.univ_prod_mulSingle f]
    refine Subgroup.prod_mem _ fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      rw [hf, Pi.mulSingle_one]
      exact one_mem _
    · show basisTorus b hb hc (Pi.mulSingle j (f j)) ∈ H
      rw [basisTorus_mulSingle]
      exact Subgroup.pow_mem _ (hH j hj) _
  exact hmem

theorem basisTorus_mem {p d : ℕ} [NeZero p] (b : Fin d → R) (hb : ∀ i, b i ^ p = 1)
    (hc : ∀ i j, Commute (b i) (b j)) {H : Subgroup R} (hH : ∀ i, b i ∈ H)
    (f : Fin d → Multiplicative (ZMod p)) : basisTorus b hb hc f ∈ H := by
  have hmem : f ∈ H.comap (basisTorus b hb hc) := by
    rw [← Finset.univ_prod_mulSingle f]
    refine Subgroup.prod_mem _ fun j _ => ?_
    show basisTorus b hb hc (Pi.mulSingle j (f j)) ∈ H
    rw [basisTorus_mulSingle]
    exact Subgroup.pow_mem _ (hH j) _
  exact hmem

theorem eq_one_of_inverter {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : Fin d → R)
    (hb : ∀ i, b i ^ p = 1) (hc : ∀ i j, Commute (b i) (b j)) {i : Fin d} (hbi : b i ≠ 1)
    {g : R} (hgi : g * b i * g⁻¹ = (b i)⁻¹) (hg : ∀ j, j ≠ i → g * b j * g⁻¹ = b j)
    {f : Fin d → Multiplicative (ZMod p)} (hf : basisTorus b hb hc f = 1) : f i = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set τ := basisTorus b hb hc
  set a := f i
  set f' := f * (Pi.mulSingle i a)⁻¹ with hf'
  have hfi : f' i = 1 := by
    rw [hf', Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
    exact mul_inv_cancel _
  have hsplit : f = f' * Pi.mulSingle i a := by rw [hf']; exact (inv_mul_cancel_right f _).symm
  have hC : ∀ h : Fin d → Multiplicative (ZMod p), h i = 1 → g * τ h * g⁻¹ = τ h := by
    intro h hh
    have hmem : τ h ∈ Subgroup.centralizer {g} :=
      basisTorus_mem_of b hb hc (fun j hj => Subgroup.mem_centralizer_singleton_iff.2
        (mul_inv_eq_iff_eq_mul.1 (hg j hj)).symm) hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    rw [← hmem, mul_inv_cancel_right]
  set v := (Multiplicative.toAdd a).val
  have hτa : τ (Pi.mulSingle i a) = b i ^ v := basisTorus_mulSingle b hb hc i a
  have h1 : τ f' * b i ^ v = 1 := by rw [← hτa, ← map_mul, ← hsplit, hf]
  have h2 : τ f' * (b i ^ v)⁻¹ = 1 := by
    have e := congrArg (fun x => g * x * g⁻¹) h1
    simp only [mul_one, mul_inv_cancel] at e
    rw [show g * (τ f' * b i ^ v) * g⁻¹ = (g * τ f' * g⁻¹) * (g * b i * g⁻¹) ^ v by
      rw [conj_pow]; group, hC f' hfi, hgi, inv_pow] at e
    exact e
  have h3 : b i ^ (2 * v) = 1 := by
    have e : b i ^ v = (b i ^ v)⁻¹ := by
      have := h1.trans h2.symm
      exact mul_left_cancel this
    rw [mul_comm, pow_mul, pow_two]
    nth_rewrite 1 [e]
    exact inv_mul_cancel _
  have hord : orderOf (b i) = p := orderOf_eq_prime (hb i) hbi
  have hdvd : p ∣ 2 * v := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have hpv : p ∣ v := ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_left fun h2' =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2')
  have hv0 : v = 0 := Nat.eq_zero_of_dvd_of_lt hpv (ZMod.val_lt _)
  have : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).1 hv0
  exact this

theorem dvd_of_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x y g g' : R}
    (hxy : Commute x y) (hx : orderOf x = p) (hy : orderOf y = p) (hg1 : g * x * g⁻¹ = x⁻¹)
    (hg2 : g * y * g⁻¹ = y * x) (hg'1 : g' * y * g'⁻¹ = y⁻¹) (hg'2 : g' * x * g'⁻¹ = x * y)
    {a b : ℕ} (h : x ^ a * y ^ b = 1) : p ∣ a ∧ p ∣ b := by
  set A : ℤ := (a : ℤ)
  set B : ℤ := (b : ℤ)
  have h' : x ^ A * y ^ B = 1 := by simpa [A, B] using h
  have hyB : y ^ B = x ^ (-A) := by rw [eq_inv_of_mul_eq_one_right h', zpow_neg]
  have hxA : x ^ A = y ^ (-B) := by rw [eq_inv_of_mul_eq_one_left h', zpow_neg]
  have hconj : ∀ w : R, w * (x ^ A * y ^ B) * w⁻¹ = (w * x * w⁻¹) ^ A * (w * y * w⁻¹) ^ B :=
    fun w => by rw [conj_zpow, conj_zpow]; group
  have e1 : x ^ (B - 2 * A) = 1 := by
    have e := hconj g
    rw [h', mul_one, mul_inv_cancel, hg1, hg2, (hxy.symm).mul_zpow, inv_zpow', hyB] at e
    rw [← zpow_add, ← zpow_add] at e
    rw [show B - 2 * A = -A + (-A + B) by ring]
    exact e.symm
  have e2 : y ^ (A - 2 * B) = 1 := by
    have e := hconj g'
    rw [h', mul_one, mul_inv_cancel, hg'1, hg'2, hxy.mul_zpow, inv_zpow', hxA] at e
    rw [← zpow_add, ← zpow_add] at e
    rw [show A - 2 * B = -B + A + -B by ring]
    exact e.symm
  have d1 : (p : ℤ) ∣ B - 2 * A := by rw [← hx]; exact orderOf_dvd_iff_zpow_eq_one.2 e1
  have d2 : (p : ℤ) ∣ A - 2 * B := by rw [← hy]; exact orderOf_dvd_iff_zpow_eq_one.2 e2
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h3B : (p : ℤ) ∣ 3 * B := by
    have : 3 * B = -(B - 2 * A) - 2 * (A - 2 * B) := by ring
    rw [this]
    exact dvd_sub (dvd_neg.2 d1) (dvd_mul_of_dvd_right d2 2)
  have hB : (p : ℤ) ∣ B := (hpz.dvd_or_dvd h3B).resolve_left fun h3 => hp3 (by
    have : p ∣ 3 := by exact_mod_cast h3
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
  have h2A : (p : ℤ) ∣ 2 * A := by
    have : 2 * A = B - (B - 2 * A) := by ring
    rw [this]
    exact dvd_sub hB d1
  have hA : (p : ℤ) ∣ A := (hpz.dvd_or_dvd h2A).resolve_left fun h2 => hp2 (by
    have : p ∣ 2 := by exact_mod_cast h2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  exact ⟨Int.natCast_dvd_natCast.1 hA, Int.natCast_dvd_natCast.1 hB⟩

end Inj

end TwE6Per

end CFSG.StandardType
