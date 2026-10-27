module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.SteinbergCDSmallDegreeNormalizer

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.ABGLocalTools

theorem exists_isSylowOf_map_eq {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] {π : G →* H} (hπ : Function.Surjective π) {X : Subgroup H}
    (hX : IsPGroup p X) : ∃ Y : Subgroup G, IsSylowOf p Y (X.comap π) ∧ Y.map π = X := by
  set C := X.comap π with hC
  obtain ⟨Y₀⟩ := (inferInstance : Nonempty (Sylow p C))
  set f : C →* X := (π.comp C.subtype).codRestrict X fun c => c.2 with hf
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hπ x
    exact ⟨⟨g, hx⟩, rfl⟩
  have htop : (Y₀ : Subgroup C).map f = ⊤ := by
    have h := (Y₀.mapSurjective hfs).is_maximal' (IsPGroup.to_subgroup hX ⊤) le_top
    rw [← Sylow.coe_mapSurjective hfs]
    exact h.symm
  refine ⟨(Y₀ : Subgroup C).map C.subtype, ⟨Y₀, rfl⟩, ?_⟩
  have e : π.comp C.subtype = X.subtype.comp f := by
    ext c
    rfl
  rw [Subgroup.map_map, e, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem central_extensions_scalar_quotients_trivial_large_prime_two_action {k : Type*}
    [Field k] (h2 : (2 : k) ≠ 0) {n : ℕ} (hn : n ≤ 3) {Γ : Subgroup (GL (Fin n) k)} [Finite Γ]
    {D : Subgroup Γ} [D.Normal]
    (hD : ∀ d ∈ D, ∃ a : k,
      ((d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.scalar (Fin n) a)
    {K : Type*} [Group K] [Finite K] {Z : Subgroup K} [Z.Normal] (hZ : Z ≤ center K)
    (α : K ⧸ Z ≃* Γ ⧸ D) {Q P : Subgroup K} (hQ : IsPGroup 2 Q) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hP : IsPGroup p P) (hPQ : P ≤ normalizer (Q : Set K)) :
    ⁅Q, P⁆ = ⊥ ∧ ¬ (Q = ⁅Q, P⁆ ∧ Q ≠ ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp6 : Nat.Coprime p 6 := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega))
  set ρ : Γ →* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin n) (Fin n) k))).comp Γ.subtype with hρ
  have hρinj : Function.Injective ρ := fun x y h =>
    Subtype.ext (Units.ext ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective h))
  have hDc : ∀ d ∈ D, ∀ g : Γ, d * g = g * d := by
    intro d hd g
    obtain ⟨a, ha⟩ := hD d hd
    apply Subtype.ext
    apply Units.ext
    change ((d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * ((g : GL (Fin n) k) : Matrix _ _ k) =
      ((g : GL (Fin n) k) : Matrix _ _ k) * ((d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    rw [ha]
    exact Matrix.scalar_commute a (fun b => Commute.all a b) _
  set η : K →* Γ ⧸ D := α.toMonoidHom.comp (QuotientGroup.mk' Z) with hη
  have hηker : ∀ x, η x = 1 ↔ x ∈ Z := by
    intro x
    rw [hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set π := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hπker : ∀ g, π g = 1 ↔ g ∈ D := fun g => QuotientGroup.eq_one_iff g
  obtain ⟨S, hS, hSπ⟩ := exists_isSylowOf_map_eq hπs (hQ.map η)
  obtain ⟨P', hP', hP'π⟩ := exists_isSylowOf_map_eq hπs (hP.map η)
  set A := (Q.map η).comap π with hA
  have hAn : A ≤ normalizer (S : Set Γ) := by
    intro a ha
    have ha' : π a ∈ S.map π := by rw [hSπ]; exact ha
    obtain ⟨s, hs, hsa⟩ := ha'
    have hd : s⁻¹ * a ∈ D := by
      rw [← hπker, map_mul, map_inv, hsa, inv_mul_cancel]
    rw [mem_normalizer_iff]
    intro x
    have e : a * x * a⁻¹ = s * x * s⁻¹ := by
      have hdx := hDc _ hd x
      calc a * x * a⁻¹ = s * ((s⁻¹ * a) * x) * (s⁻¹ * a)⁻¹ * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * a)) * (s⁻¹ * a)⁻¹ * s⁻¹ := by rw [hdx]
        _ = s * x * s⁻¹ := by group
    rw [e]
    constructor
    · intro hx
      exact mul_mem (mul_mem hs hx) (inv_mem hs)
    · intro hx
      have h1 := mul_mem (mul_mem (inv_mem hs) hx) hs
      simpa [mul_assoc] using h1
  have hS2 : ∀ X : Subgroup Γ, X ≤ A → IsPGroup 2 X → X ≤ S := by
    intro X hXA hX2
    have h := hS.eq_of_le le_sup_right (sup_le hXA hS.le)
      (IsPGroup.to_sup_of_normal_right' hX2 hS.isPGroup (hXA.trans hAn))
    rw [← h]
    exact le_sup_left
  have hηPQ : ∀ x ∈ P.map η, ∀ y ∈ Q.map η, x * y * x⁻¹ ∈ Q.map η := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨q, hq, rfl⟩
    refine ⟨u * q * u⁻¹, (mem_normalizer_iff.mp (hPQ hu) q).mp hq, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hP'S : ∀ v ∈ P', v ∈ normalizer (S : Set Γ) := by
    have hconj : ∀ v ∈ P', ∀ s ∈ S, v * s * v⁻¹ ∈ S := by
      intro v hv s hs
      have hvB : π v ∈ P.map η := hP'.le hv
      have hX : S.map (MulAut.conj v).toMonoidHom ≤ S := by
        refine hS2 _ ?_ (hS.isPGroup.map _)
        rintro _ ⟨t, ht, rfl⟩
        change π (v * t * v⁻¹) ∈ Q.map η
        rw [map_mul, map_mul, map_inv]
        exact hηPQ _ hvB _ (hS.le ht)
      exact hX ⟨s, hs, rfl⟩
    intro v hv
    rw [mem_normalizer_iff]
    intro s
    refine ⟨hconj v hv s, fun h => ?_⟩
    have h1 := hconj v⁻¹ (inv_mem hv) _ h
    simpa [mul_assoc] using h1
  have hcomm : ∀ v ∈ P', ∀ s ∈ S, v * s = s * v := by
    intro v hv s hs
    obtain ⟨m, hm⟩ := hP'.isPGroup ⟨v, hv⟩
    have h := rep_commute_of_finrank_le_three h2 (by rw [Module.finrank_fin_fun]; exact hn) ρ
      (Q := S) hS.isPGroup (hP'S v hv) (Nat.Coprime.pow_left m hp6)
      (congrArg Subtype.val hm) s hs
    exact hρinj (by rw [map_mul, map_mul]; exact h.eq)
  have hPQc : ∀ u ∈ P, ∀ q ∈ Q, u * q = q * u := by
    intro u hu q hq
    obtain ⟨v, hv, hvu⟩ : η u ∈ P'.map π := by rw [hP'π]; exact ⟨u, hu, rfl⟩
    obtain ⟨s, hs, hsq⟩ : η q ∈ S.map π := by rw [hSπ]; exact ⟨q, hq, rfl⟩
    set c := u * q * u⁻¹ * q⁻¹ with hc
    have hcZ : c ∈ Z := by
      rw [← hηker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, ← hvu, ← hsq,
        ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm v hv s hs,
        mul_inv_cancel_right, mul_inv_cancel, map_one]
    have hcQ : c ∈ Q := mul_mem ((mem_normalizer_iff.mp (hPQ hu) q).mp hq) (inv_mem hq)
    have hcen : ∀ g : K, c * g = g * c := fun g => (mem_center_iff.mp (hZ hcZ) g).symm
    have huq : u * q * u⁻¹ = c * q := by rw [hc, inv_mul_cancel_right]
    have hiter : ∀ j : ℕ, u ^ j * q * (u ^ j)⁻¹ = c ^ j * q := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hcj : ∀ g : K, c ^ j * g = g * c ^ j := fun g =>
          ((Commute.pow_left (hcen g) j).eq)
        calc u ^ (j + 1) * q * (u ^ (j + 1))⁻¹ = u * (u ^ j * q * (u ^ j)⁻¹) * u⁻¹ := by
              rw [pow_succ']; group
          _ = u * (c ^ j * q) * u⁻¹ := by rw [ih]
          _ = c ^ j * (u * q * u⁻¹) := by rw [← mul_assoc u, ← hcj u]; group
          _ = c ^ (j + 1) * q := by rw [huq, ← mul_assoc, ← pow_succ]
    obtain ⟨m, hm⟩ := hP ⟨u, hu⟩
    have hum : u ^ p ^ m = 1 := congrArg Subtype.val hm
    have hcN : c ^ p ^ m = 1 := by
      have h := hiter (p ^ m)
      rw [hum, inv_one, one_mul, mul_one] at h
      exact (mul_eq_right.mp h.symm)
    obtain ⟨l, hl⟩ := hQ ⟨c, hcQ⟩
    have hc2 : c ^ 2 ^ l = 1 := congrArg Subtype.val hl
    have hord : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow m l ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)))
      (orderOf_dvd_of_pow_eq_one hcN) (orderOf_dvd_of_pow_eq_one hc2)
    have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
    exact hc1
  have hbot : ⁅Q, P⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro q hq u hu
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hPQc u hu q hq).symm
  refine ⟨hbot, fun ⟨hQQ, hQ1⟩ => hQ1 ?_⟩
  rw [hQQ, hbot]

end CFSG.Quasithin.SteinbergCD
