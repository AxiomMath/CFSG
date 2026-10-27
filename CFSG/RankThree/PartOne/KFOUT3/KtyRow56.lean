module

public import CFSG.RankThree.PartOne.KFOUT3.KtySUBig
public import CFSG.RankThree.PartOne.KFOUT3.KtySUSmall
public import CFSG.RankThree.PartOne.KFOUT3.KtySUCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyRows
public import CFSG.RankThree.PartOne.KFOUT3.CQuot
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KF.SUSylow
public import CFSG.RankThree.PartOne.KF.R11Final
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.ToralQuot

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N1322 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem kf1322Kty_su
    {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n)
    (hc2 : D8Comb2 hc) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
      ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
      (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) →
      ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
        ∀ (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)),
          conjAut E g hg * t * (conjAut E g hg)⁻¹ ≠ s := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  rcases hF12.two with hG | hS
  · have hp := h12.prime
    have h5 := Sec12Three.five_le h12
    have hp2 : p ≠ 2 := by omega
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZ := hG.center_pPrime
    obtain ⟨hFexp, hFcomm, hmax⟩ := F_facts h12 hG
    obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
    obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
    have hchar : CharP K 2 := by
      have := Fintype.ofFinite K
      refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * f) ?_
      rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm]
    have hq2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    set σ : K ≃+* K := unitaryInvolution K 2 f with hσdef
    have hσ : ∀ x : K, σ x = x ^ 2 ^ f := fun x => unitaryInvolution_apply K 2 f x
    have hσσ : ∀ x : K, σ (σ x) = x := unitaryInvolution_involutive hK
    have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
      have hdvd : p ∣ Nat.card Kˣ := by
        rw [Nat.card_units, hK]
        have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 2 - 1 := by
          have : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
            zify [Nat.one_le_pow 2 (2 ^ f) (by omega), (by omega : 1 ≤ 2 ^ f)]
            ring
          rw [this]
          exact dvd_mul_right _ _
        exact hpq.trans h1
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
      refine ⟨z, ?_⟩
      have := IsPrimitiveRoot.orderOf z
      rwa [hz] at this
    have hσfix : ∀ u : rootsOfUnity p K, σ ((u : Kˣ) : K) = (u : Kˣ) := by
      intro u
      have h1 : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp u.2
      have h2 : (u : Kˣ) ^ (2 ^ f - 1) = 1 := by
        obtain ⟨k, hk⟩ := hpq
        rw [hk, pow_mul, h1, one_pow]
      rw [hσ, ← Units.val_pow_eq_pow_val]
      have : (u : Kˣ) ^ 2 ^ f = (u : Kˣ) := by
        calc (u : Kˣ) ^ 2 ^ f = (u : Kˣ) ^ (2 ^ f - 1) * (u : Kˣ) := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          _ = (u : Kˣ) := by rw [h2, one_mul]
      rw [this]
    have hT : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ SU σ n :=
      fun v => d8Vec_mem_SU hn hc σ hσfix v
    have hP : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
        (permGL τ : GL (Fin n) K) ∈ SU σ n := fun τ hτ => permGL_mem_SU σ τ hτ
    obtain ⟨SM, hSM⟩ := exists_d8ctx_tor hc hc2 hp hp2 hζ (SU σ n) hT hP
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
    have hε₀ := isCentralPQuot_center' e hcop
    let ψ₀ : SU σ n ≃* StatedSU n (2 ^ f) K := equivStatedSU hK n
    let N : Subgroup ↥(StatedSU n (2 ^ f) K) :=
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)
    let q : ↥(SU σ n) →* StatedProj (StatedSU n (2 ^ f) K) :=
      (QuotientGroup.mk' N).comp ψ₀.toMonoidHom
    have hker : q.ker = N.comap (ψ₀ : ↥(SU σ n) →* ↥(StatedSU n (2 ^ f) K)) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      exact QuotientGroup.eq_one_iff _
    have hq : IsCentralPQuot p q := by
      refine ⟨(QuotientGroup.mk'_surjective N).comp ψ₀.surjective, ?_, ?_⟩
      · intro x hx
        rw [hker] at hx
        have hxN : ((ψ₀ x : ↥(StatedSU n (2 ^ f) K)) : GL (Fin n) K) ∈
            Subgroup.center (GL (Fin n) K) := by
          rw [← statedScalars_eq_center]
          exact Subgroup.mem_subgroupOf.mp hx
        rw [Subgroup.mem_center_iff]
        intro z
        apply ψ₀.injective
        rw [map_mul, map_mul]
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp hxN ((ψ₀ z : ↥(StatedSU n (2 ^ f) K)) :
          GL (Fin n) K)
      · rw [hker, Subgroup.comap_equiv_eq_map_symm,
          Subgroup.card_map_of_injective (MulEquiv.injective _),
          (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.2]
        refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
        have h1 : p ∣ 2 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
        exact not_dvd_add_one_of_dvd_sub_one hp hp2 (by omega) hpq h1
    have hTexp : ∀ t ∈ (d8Tor p K n).subgroupOf (SU σ n), t ^ p = 1 := by
      intro t ht
      obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
      apply Subtype.ext
      show ((t : ↥(SU σ n)) : GL (Fin n) K) ^ p = 1
      rw [← hv]
      show diagU (d8Vec n v) ^ p = 1
      rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
    have hTcomm : ∀ s ∈ (d8Tor p K n).subgroupOf (SU σ n),
        ∀ t ∈ (d8Tor p K n).subgroupOf (SU σ n), s * t = t * s := by
      intro s hs t ht
      obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
      obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
      apply Subtype.ext
      show ((s : ↥(SU σ n)) : GL (Fin n) K) * (t : GL (Fin n) K) =
        (t : GL (Fin n) K) * (s : GL (Fin n) K)
      rw [← hv, ← hw]
      show diagU (d8Vec n v) * diagU (d8Vec n w) = diagU (d8Vec n w) * diagU (d8Vec n v)
      rw [diagU_mul, diagU_mul, mul_comm]
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ hTexp hTcomm
      (fun X hexp _ => exists_conj_into_d8Tor_su hn hc hK hp hp2 hpq X hexp)
      (inf_le_right : E ⊓ L ≤ L) hFexp hFcomm hmax
    have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
      Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
        (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
    obtain ⟨S, hrel⟩ := wctx_ofCentralQuot' hVexp SM q hq ε hε (inf_le_right : E ⊓ L ≤ L) hFexp
      hFT₁ hFT₂
    let torHom : D8Mod p K →* ↥(SU σ n) :=
      { toFun := fun v => ⟨diagU (d8Vec n v), hT v⟩
        map_one' := by
          apply Subtype.ext
          show diagU (d8Vec n 1) = 1
          have : d8Vec (p := p) (K := K) n 1 = 1 := (d8VecHom n).map_one
          rw [this]
          exact diagU_one
        map_mul' := fun v w => by
          apply Subtype.ext
          show diagU (d8Vec n (v * w)) = diagU (d8Vec n v) * diagU (d8Vec n w)
          have : d8Vec (p := p) (K := K) n (v * w) = d8Vec n v * d8Vec n w :=
            (d8VecHom n).map_mul v w
          rw [this, ← diagU_mul] }
    let Temb : D8Mod p K →* StatedProj (StatedSU n (2 ^ f) K) := q.comp torHom
    have hrel' : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = Temb d := by
      intro d
      rw [hrel d]
      show q (SM.tor d : ↥(SU σ n)) = q (torHom d)
      exact congrArg q (Subtype.ext (hSM d))
    have Hconj : ∀ γ : DihedralGroup 4, ∃ m : StatedProj (StatedSU n (2 ^ f) K),
        ∀ v, m * Temb v * m⁻¹ = Temb (d8Act γ v) := by
      intro γ
      refine ⟨q ⟨permGL (d8Perm hc γ), hP _ (hc2.comm_rev γ)⟩, fun v => ?_⟩
      show q _ * q (torHom v) * (q _)⁻¹ = q (torHom (d8Act γ v))
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
        (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = diagU (d8Vec n (d8Act γ v))
      rw [permGL_conj_diagU, d8Vec_act hc]
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq2 2
    have hpd : p ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 4 - 1 := by
        have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 4
        simpa using this
      have h2 : Nat.card K ^ 2 - 1 = (2 ^ f) ^ 4 - 1 := by
        rw [hK, ← pow_mul]
      rw [h2]
      exact Dvd.dvd.mul_left (hpq.trans h1) _
    have hTpow : ∀ v : D8Mod p K, (torHom v) ^ p = 1 := by
      intro v
      apply Subtype.ext
      show diagU (d8Vec n v) ^ p = 1
      rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
    have Hbig : ∀ a : rootsOfUnity p K, a ≠ 1 →
        BigAt p (Temb (a, a)) (fun m => m = Nat.card K * (Nat.card K ^ 2 - 1)) := by
      intro a ha
      have ha1 : (a : Kˣ) ≠ 1 := fun h => ha (Subtype.ext h)
      have ha2 : (a : Kˣ)⁻¹ ≠ (a : Kˣ) := fun h =>
        ha (eq_one_of_inv_eq_self (hp.odd_of_ne_two hp2) (Subtype.ext h))
      have hu : diagU (dvecN n (a : Kˣ) (a : Kˣ)) ∈ SU σ n := by
        have := hT (a, a)
        rwa [d8Vec_eq_dvecN] at this
      obtain ⟨S₀, hperf, hsimple, hord, hcomm, hnorm, hcard⟩ :=
        big_su hn hc σ hσσ h4 ha1 ha2 hp hpd hu
      have hTe : torHom (a, a) = ⟨diagU (dvecN n (a : Kˣ) (a : Kˣ)), hu⟩ := by
        apply Subtype.ext
        show diagU (d8Vec n (a, a)) = _
        rw [d8Vec_eq_dvecN]
      refine bigAt_of_central hp hq (hTpow (a, a)) hperf hsimple hord ?_ ?_ hcard
      · rw [hTe]; exact hcomm
      · rw [hTe]; exact hnorm
    have Hsmall : ∀ b : rootsOfUnity p K, b ≠ 1 →
        SmallAt (Temb (1, b)) (fun m => m = Nat.card K * (Nat.card K ^ 2 - 1)) := by
      intro b hb
      have hb1 : (b : Kˣ) ≠ 1 := fun h => hb (Subtype.ext h)
      have hb2 : (b : Kˣ)⁻¹ ≠ (b : Kˣ) := fun h =>
        hb (eq_one_of_inv_eq_self (hp.odd_of_ne_two hp2) (Subtype.ext h))
      have hu : diagU (dvecN n 1 (b : Kˣ)) ∈ SU σ n := by
        have := hT (1, b)
        rwa [d8Vec_eq_dvecN] at this
      have hTe : torHom (1, b) = ⟨diagU (dvecN n 1 (b : Kˣ)), hu⟩ := by
        apply Subtype.ext
        show diagU (d8Vec n (1, b)) = _
        rw [d8Vec_eq_dvecN]
        rfl
      refine smallAt_of_central hq (hTpow (1, b)) ?_
      intro T hT' hTc m hm hdvd
      rw [hTe] at hTc
      have h1 := small_su hn hc σ hb1 hb2 hu T hT' hTc
      have h2 : m ∣ Nat.card ↥(SU σ (n - 2)) := hdvd.trans h1
      rw [hm] at h2
      exact not_dvd_card_su hK hf1 hn h2
    exact kty_of_d8 h12 hG hEA hF13 hp2 hζ hε Temb S hrel' Hconj Hsmall Hbig t ht s hs hts g hg
  ·
    exfalso
    have hrow := kf123Row11 G p L A E (Sec12Three.table123SU5 h12 hS)
    have hcard : Nat.card E = p ^ 4 := hrow.2.1
    rw [hEA, h12.A_card] at hcard
    have h5 := Sec12Three.five_le h12
    have h1 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem kf1322KtyRow5_holds :
    KF1322KtyRow 5 := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  exact kf1322Kty_su (n := 4) (Or.inl rfl) d8Comb_four d8Comb2_four G p A c L E h12 hF12 hF13
    hno5 hEA hL3 hmodel t ht s hs hts g hg

theorem kf1322KtyRow6_holds :
    KF1322KtyRow 6 := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  exact kf1322Kty_su (n := 5) (Or.inr rfl) d8Comb_five d8Comb2_five G p A c L E h12 hF12 hF13
    hno5 hEA hL3 hmodel t ht s hs hts g hg

end CFSG.RankThree.PartOne.KFOUT3
