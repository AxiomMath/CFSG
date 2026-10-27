module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OrthRestTail

section Cyclic

variable {G : Type*} [Group G]

theorem card_le_mul_inf_of_cyclic {N : Subgroup G} [N.Normal] (c : G)
    (hc : ∀ g : G, ∃ n ∈ N, ∃ k : ℕ, g = n * c ^ k) {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p * Nat.card (E ⊓ N : Subgroup G) := by
  have hcyc : IsCyclic (G ⧸ N) := ⟨⟨(c : G ⧸ N), fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn, k, rfl⟩ := hc g
    refine ⟨k, ?_⟩
    change (c : G ⧸ N) ^ (k : ℤ) = ((n * c ^ k : G) : G ⧸ N)
    rw [zpow_natCast, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul,
      QuotientGroup.mk_pow]⟩⟩
  set f : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype with hf
  have hker : f.ker = N.subgroupOf E := by
    ext x
    simp [hf, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : Nat.card f.range ≤ p := by
    have h1 : Monoid.exponent f.range ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      obtain ⟨_, ⟨e, rfl⟩⟩ := x
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow,
        show e ^ p = 1 from Subtype.ext (hE.2 _ e.2), map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd hp.pos h1
  have h2 : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h3 : Nat.card f.ker = Nat.card (E ⊓ N : Subgroup G) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  rw [h2, h3]
  exact Nat.mul_le_mul_right _ hrange

end Cyclic

section Vacuous

variable {R : Type} [Group R] [Finite R] {p r : ℕ}

theorem ggBstarBoundInnR_of_cyclic (hp : p.Prime) (hZ : Subgroup.center R = ⊥) (c : MulAut R)
    (hc : ∀ α : MulAut R, ∃ ι ∈ (MulAut.conj : R →* MulAut R).range, ∃ k : ℕ, α = ι * c ^ k)
    (hcard : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E ≤ p ^ r) (I : Set (MulAut R)) :
    GGBstarBoundInnR p r R I := by
  intro Eb Eh _ _ hr _ _ _ hEh hcardh
  exfalso
  have : Finite (MulAut R) :=
    Finite.of_injective (fun α : MulAut R => (α : R → R)) fun a b h => MulEquiv.ext (congrFun h)
  have hinj := OrthRest.conj_injective hZ
  set Inn := (MulAut.conj : R →* MulAut R).range with hInn
  have h1 := card_le_mul_inf_of_cyclic (N := Inn) c hc hp hEh
  have h2 : Nat.card (Eh ⊓ Inn : Subgroup (MulAut R)) ≤ p ^ r := by
    set E := (Eh ⊓ Inn).comap (MulAut.conj : R →* MulAut R) with hE
    have hcE : Nat.card E = Nat.card (Eh ⊓ Inn : Subgroup (MulAut R)) := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self (inf_le_right : Eh ⊓ Inn ≤ Inn)]
      rw [Subgroup.card_map_of_injective hinj]
    rw [← hcE]
    refine hcard E ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · change MulAut.conj ((a : R) * b) = MulAut.conj ((b : R) * a)
      rw [map_mul, map_mul, TableB.IsElemAbelian.comm hEh a.2.1 b.2.1]
    · rw [map_pow, hEh.2 _ hx.1, map_one]
  have h3 : p ^ (r + 2) ≤ Nat.card Eh := by
    calc p ^ (r + 2) = p ^ 2 * p ^ r := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcardh
  have h4 : p * p ^ r < p ^ (r + 2) := by
    rw [← pow_succ']
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have h5 := Nat.mul_le_mul_left p h2
  omega

end Vacuous

theorem exists_cyclic_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m n : ℕ} {b c : K}
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2 ^ n) :
    ∃ c₀ : MulAut (OrthRest.RMinus K m b c), ∀ α : MulAut (OrthRest.RMinus K m b c),
      ∃ ι ∈ (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)).range,
        ∃ k : ℕ, α = ι * c₀ ^ k := by
  have hn4 : 4 ≤ m + 1 := by omega
  let e : OrthRest.RMinus K m b c ≃* _ := RecipeFieldOmega.minusEquiv hn4 b c
  refine ⟨(MulAut.congr e).symm (AutOm.frobAut hn4 hirr), fun α => ?_⟩
  obtain ⟨ι, ⟨g, rfl⟩, k, hk⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hK (MulAut.congr e α)
  refine ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, k, ?_⟩
  apply (MulAut.congr e).injective
  rw [hk, map_mul, map_pow, MulEquiv.apply_symm_apply]
  congr 1
  refine MulEquiv.ext fun x => ?_
  change g * x * g⁻¹ = e (e.symm g * e.symm x * (e.symm g)⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end OrthRestTail

@[expose] def GGOrthRestMinusRankInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m → Odd m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ E : Subgroup (OrthRest.RMinus K m b c), IsElemAbelian p E → Nat.card E ≤ p ^ m

@[expose] def GGOrthRestBstarOddInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m → Even m →
    p.Prime → p ∣ 2 ^ n + 1 → p ∣ n → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGBstarBoundInnR p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _)

@[expose] def GGOrthRestBstarD4Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGBstarBoundInnR 3 3 (OrthRest.RPlus K 4) (LargeEvenInnSet _)

theorem ggOrthRestBstarRestInput_of_split (hZ : GGOrthRestCenterInput)
    (hR : GGOrthRestMinusRankInput) (hO : GGOrthRestBstarOddInput)
    (hD : GGOrthRestBstarD4Input) : GGOrthRestBstarRestInput := by
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hpd hbc => ?_, hD⟩
  rcases Nat.even_or_odd m with he | ho
  · exact hO K n m p b c hK hm he hp hpn hpd hbc
  · have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, h0, pow_zero] at h1
        omega
      · exact h0
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hn hK
    have : Finite (GL (LargeEvenMinusIdx m) K) :=
      Finite.of_injective (fun u : GL (LargeEvenMinusIdx m) K =>
        (u : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)) Units.val_injective
    obtain ⟨c₀, hc₀⟩ := OrthRestTail.exists_cyclic_minus hm hbc hK
    exact OrthRestTail.ggBstarBoundInnR_of_cyclic hp (hZ.1 K n m p b c hK hm hp hpn hbc).1 c₀ hc₀
      (hR K n m p b c hK hm ho hp hpn hbc) _

end CFSG.StandardType
