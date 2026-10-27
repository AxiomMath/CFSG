module

public import CFSG.Quasithin.SteinbergBTResidualAbelianIndexTwo
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.Quasithin.SteinbergBSSmallRankEscape

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

theorem two_le_pRank_of_exponent_of_card {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (R : Subgroup Y) (hR : ∀ r ∈ R, r ^ p = 1) (hcard : p ^ 2 ≤ Nat.card R) :
    2 ≤ CFSG.pRank p Y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hRp : IsPGroup p R := fun r =>
    ⟨1, Subtype.ext (by rw [pow_one, coe_pow, hR r r.2, coe_one])⟩
  have hpp : p < p ^ 2 :=
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hR1 : 1 < Nat.card R := lt_of_lt_of_le (hp.one_lt.trans hpp) hcard
  have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.1 hR1
  have := hRp.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center R)
  set c : Y := ((z : R) : Y) with hc
  have hcR : c ∈ R := (z : R).2
  have hc1 : c ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hcord : orderOf c = p := orderOf_eq_prime (hR c hcR) hc1
  have : Finite (zpowers c) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hcord]; exact hp.ne_zero)
  obtain ⟨y, hyR, hyc⟩ : ∃ y ∈ R, y ∉ zpowers c := by
    by_contra h
    push Not at h
    have hle := card_le_of_le (show R ≤ zpowers c from h)
    rw [Nat.card_zpowers, hcord] at hle
    omega
  have hy1 : y ≠ 1 := fun h => hyc (h ▸ one_mem _)
  have hyord : orderOf y = p := orderOf_eq_prime (hR y hyR) hy1
  have : Finite (zpowers y) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hyord]; exact hp.ne_zero)
  have hcy : Commute c y := by
    have h := congrArg Subtype.val (mem_center_iff.1 z.2 ⟨y, hyR⟩)
    exact h.symm
  have hcent : zpowers y ≤ centralizer (zpowers c : Set Y) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact (hcy.zpow_left n).eq
  have hdisj : zpowers c ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwc, hwy⟩ := mem_inf.1 hw
    by_contra hw1
    rw [mem_bot] at hw1
    have hwR : w ∈ R := (zpowers_le.2 hyR) hwy
    have hword : orderOf w = p := orderOf_eq_prime (hR w hwR) hw1
    have heq : zpowers w = zpowers y := eq_of_le_of_card_ge (zpowers_le.2 hwy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hword, hyord])
    apply hyc
    have : y ∈ zpowers w := heq ▸ mem_zpowers y
    exact (zpowers_le.2 hwc) this
  have : CFSG.IsElementaryAbelian p (zpowers c) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hR c hcR)
  have : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hR y hyR)
  have hE : CFSG.IsElementaryAbelian p (zpowers c ⊔ zpowers y : Subgroup Y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hcent
  have hEcard : Nat.card (zpowers c ⊔ zpowers y : Subgroup Y) = p ^ 2 := by
    rw [SteinbergBM.card_sup_of_commute hcent hdisj, Nat.card_zpowers, Nat.card_zpowers, hcord,
      hyord, sq]
  exact SteinbergBS.le_pRank_of_card hp.one_lt hE hEcard

theorem irreducible_two_prime_residual_image_rank_dichotomy {A : Type*} [Group A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q X : Subgroup A) [Q.Normal] [X.Normal]
    (hQX : Q ≤ X) (hQ : IsPGroup 2 Q) (hXQ : ∀ x ∈ X.map (QuotientGroup.mk' Q), x ^ p = 1)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hW : p ^ 2 ≤ Nat.card (X.map (QuotientGroup.mk' Q) ⧸ frattini (X.map (QuotientGroup.mk' Q))))
    (hirr : ∀ K : Subgroup (A ⧸ Q),
      (frattini (X.map (QuotientGroup.mk' Q))).map (X.map (QuotientGroup.mk' Q)).subtype ≤ K →
      K ≤ X.map (QuotientGroup.mk' Q) →
      (∀ a : A, ∀ k ∈ K, (a : A ⧸ Q) * k * (a : A ⧸ Q)⁻¹ ∈ K) →
      K = (frattini (X.map (QuotientGroup.mk' Q))).map (X.map (QuotientGroup.mk' Q)).subtype ∨
        K = X.map (QuotientGroup.mk' Q))
    {B : Type*} [Group B] [Finite B] (ρ : A →* B) :
    (X.map ρ = ⊥ ∨ 2 ≤ CFSG.pRank p (X.map ρ)) ∧ (CFSG.pRank p B ≤ 1 → X.map ρ = ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Q with hπ
  set Xb := X.map π with hXb
  set Φ' := (frattini Xb).map Xb.subtype with hΦ'
  have hXbN : Xb.Normal := (inferInstance : X.Normal).map π (QuotientGroup.mk'_surjective Q)
  set N := ρ.ker ⊓ X with hN
  have hNn : N.Normal := inferInstance
  set Nb := N.map π with hNb
  have hNbXb : Nb ≤ Xb := map_mono inf_le_right
  have hK : Nb ⊔ Φ' = Φ' ∨ Nb ⊔ Φ' = Xb := by
    refine hirr _ le_sup_right (sup_le hNbXb (map_subtype_le _)) ?_
    intro a k hk
    have hle : Nb ⊔ Φ' ≤ (Nb ⊔ Φ').comap (MulAut.conj (π a)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        refine mem_sup_left ⟨a * n * a⁻¹, hNn.conj_mem n hn a, ?_⟩
        simp [hπ, MulAut.conj_apply]
      · rintro _ ⟨w, hw, rfl⟩
        have hchar := (characteristic_iff_map_eq.1 (inferInstance : (frattini Xb).Characteristic))
          (MulAut.conjNormal (π a))
        have hw' : MulAut.conjNormal (π a) w ∈ frattini Xb := by
          rw [← hchar]
          exact ⟨w, hw, rfl⟩
        refine mem_sup_right ⟨MulAut.conjNormal (π a) w, hw', ?_⟩
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    exact hle hk
  have key : X.map ρ = ⊥ ∨ (2 ≤ CFSG.pRank p (X.map ρ) ∧ 2 ≤ CFSG.pRank p B) := by
    rcases hK with h | h
    ·
      right
      have hNbΦ : Nb ≤ Φ' := h ▸ le_sup_left
      set g : X →* A ⧸ Q := π.comp X.subtype with hg
      have hgker : g.ker = Q.subgroupOf X := by
        ext x
        change π (x : A) = 1 ↔ (x : A) ∈ Q
        exact QuotientGroup.eq_one_iff (x : A)
      have hgrange : g.range = Xb := by rw [hg, MonoidHom.range_comp, range_subtype]
      have hXcard : Nat.card X = Nat.card Q * Nat.card Xb := by
        rw [← card_mul_index g.ker, index_ker, hgrange, hgker,
          Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv]
      obtain ⟨a2, ha2⟩ := IsPGroup.iff_card.1 hQ
      have hXbp : IsPGroup p Xb := fun w =>
        ⟨1, Subtype.ext (by rw [pow_one, coe_pow, hXQ w w.2, coe_one])⟩
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hXbp
      obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
      set P' : Subgroup A := (P : Subgroup X).map X.subtype with hP'
      have hPX : P' ≤ X := by
        rintro _ ⟨u, -, rfl⟩
        exact u.2
      have hp2' : ¬p ∣ 2 ^ a2 := fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      have hPcard : Nat.card P' = p ^ m := by
        rw [hP', card_map_of_injective X.subtype_injective, P.card_eq_multiplicity, hXcard, ha2,
          hm, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.ne_zero),
          Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hp2', hp.factorization_pow,
          Finsupp.single_eq_same, zero_add]
      have hPQ : P' ⊓ Q = ⊥ := disjoint_iff.1 (disjoint_of_coprime_natCard (by
        rw [hPcard, ha2]
        exact Nat.Coprime.pow m a2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)))
      have hinjP : ∀ u ∈ P', ∀ v ∈ P', π u = π v → u = v := by
        intro u hu v hv huv
        have h1 : u⁻¹ * v ∈ Q := QuotientGroup.eq.1 huv
        have h2 : u⁻¹ * v ∈ P' ⊓ Q := mem_inf.2 ⟨mul_mem (inv_mem hu) hv, h1⟩
        rw [hPQ, mem_bot] at h2
        exact inv_mul_eq_one.1 h2
      have hpowP : ∀ u ∈ P', u ^ p = 1 := by
        intro u hu
        have h1 : π (u ^ p) = 1 := by
          rw [map_pow]
          exact hXQ (π u) ⟨u, hPX hu, rfl⟩
        have h2 : u ^ p ∈ P' ⊓ Q :=
          mem_inf.2 ⟨pow_mem hu p, (QuotientGroup.eq_one_iff _).1 h1⟩
        rwa [hPQ, mem_bot] at h2
      have hPker : Nat.card ↥(P' ⊓ ρ.ker) ≤ Nat.card (frattini Xb) := by
        have h1 : Nat.card ↥(P' ⊓ ρ.ker) ≤ Nat.card Φ' := by
          refine Nat.card_le_card_of_injective (fun u : ↥(P' ⊓ ρ.ker) =>
            (⟨π u, hNbΦ ⟨u, mem_inf.2 ⟨(mem_inf.1 u.2).2, hPX (mem_inf.1 u.2).1⟩, rfl⟩⟩ : Φ'))
            fun u v huv => ?_
          have h := congrArg Subtype.val huv
          exact Subtype.ext (hinjP u (mem_inf.1 u.2).1 v (mem_inf.1 v.2).1 h)
        rwa [hΦ', card_map_of_injective Xb.subtype_injective] at h1
      have hPsplit : Nat.card P' = Nat.card ↥(P' ⊓ ρ.ker) * Nat.card (P'.map ρ) := by
        set f : P' →* B := ρ.comp P'.subtype with hf
        have hfr : f.range = P'.map ρ := by rw [hf, MonoidHom.range_comp, range_subtype]
        have hfk : Nat.card f.ker = Nat.card ↥(P' ⊓ ρ.ker) := Nat.card_congr
          { toFun := fun x => ⟨x.1, x.1.2, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
            invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩,
              MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 (mem_inf.1 y.2).2)⟩
            left_inv := fun x => rfl
            right_inv := fun y => rfl }
        rw [← card_mul_index f.ker, index_ker, hfr, hfk]
      have hXbsplit := card_eq_card_quotient_mul_card_subgroup (frattini Xb)
      have hρP : p ^ 2 ≤ Nat.card (P'.map ρ) := by
        have hpos : 0 < Nat.card ↥(P' ⊓ ρ.ker) := Nat.card_pos
        refine Nat.le_of_mul_le_mul_right ?_ hpos
        calc p ^ 2 * Nat.card ↥(P' ⊓ ρ.ker)
            ≤ Nat.card (Xb ⧸ frattini Xb) * Nat.card (frattini Xb) := Nat.mul_le_mul hW hPker
          _ = Nat.card P' := by rw [← hXbsplit, hm, hPcard]
          _ = Nat.card (P'.map ρ) * Nat.card ↥(P' ⊓ ρ.ker) := by rw [hPsplit, mul_comm]
      have hρPpow : ∀ r ∈ P'.map ρ, r ^ p = 1 := by
        rintro _ ⟨u, hu, rfl⟩
        rw [← map_pow, hpowP u hu, map_one]
      have hPXρ : P'.map ρ ≤ X.map ρ := map_mono hPX
      refine ⟨?_, two_le_pRank_of_exponent_of_card hp _ hρPpow hρP⟩
      refine two_le_pRank_of_exponent_of_card hp ((P'.map ρ).subgroupOf (X.map ρ)) ?_ ?_
      · intro r hr
        apply Subtype.ext
        rw [coe_pow, coe_one]
        exact hρPpow _ (mem_subgroupOf.1 hr)
      · rwa [Nat.card_congr (subgroupOfEquivOfLe hPXρ).toEquiv]
    ·
      left
      have h1 : (Nb.subgroupOf Xb) ⊔ frattini Xb = ⊤ := by
        apply map_injective Xb.subtype_injective
        rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.2 hNbXb, ← hΦ', h,
          ← MonoidHom.range_eq_map, range_subtype]
      have h2 := frattini_nongenerating h1
      have hXNb : Xb ≤ Nb := fun w hw => by
        have : (⟨w, hw⟩ : Xb) ∈ Nb.subgroupOf Xb := h2 ▸ mem_top _
        exact this
      have hρQ : ∀ x ∈ X, ∃ q ∈ Q, ρ x = ρ q := by
        intro x hx
        obtain ⟨n, hn, hnx⟩ := hXNb ⟨x, hx, rfl⟩
        refine ⟨n⁻¹ * x, QuotientGroup.eq.1 hnx, ?_⟩
        rw [map_mul, map_inv, MonoidHom.mem_ker.1 (mem_inf.1 hn).1, inv_one, one_mul]
      set f : X →* B := ρ.comp X.subtype with hf
      have hf2 : IsPGroup 2 f.range := by
        rintro ⟨_, x, rfl⟩
        obtain ⟨q, hq, hqx⟩ := hρQ x x.2
        obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
        refine ⟨k, Subtype.ext ?_⟩
        change (ρ x) ^ 2 ^ k = 1
        have hk' : q ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          rwa [coe_pow, coe_one] at this
        rw [hqx, ← map_pow, hk', map_one]
      have hker := ker_eq_top_of_isPGroup_two_range hX2 f hf2
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      have : (⟨x, hx⟩ : X) ∈ f.ker := hker ▸ mem_top _
      exact this
  rcases key with h | ⟨h1, h2⟩
  · exact ⟨Or.inl h, fun _ => h⟩
  · exact ⟨Or.inr h1, fun h => absurd h (by omega)⟩

end CFSG.Quasithin.SteinbergBT
