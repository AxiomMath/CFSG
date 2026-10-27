module

public import CFSG.RankThree.PartOne.KEXC.D8Class
public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KFOUT3.KtySUBig
public import CFSG.RankThree.PartOne.KFOUT3.KtySUSmall
public import CFSG.RankThree.PartOne.KFOUT3.KtySUCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KF.R56Final

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem unitary_weyl_scalar {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n]
    (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (hc2 : D8Comb2 hc) {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F)
    (hmodel : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h' : G, h' ∈ L ∧ h' ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h' * f ^ k * h'⁻¹ := by
  classical
  obtain ⟨f, K, hKf, hKfin, hchar, hK, hf1, hpq, hζ, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame hn hc h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  set σ : K ≃+* K := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ x : K, σ x = x ^ 2 ^ f := fun x => unitaryInvolution_apply K 2 f x
  have hσσ : ∀ x : K, σ (σ x) = x := unitaryInvolution_involutive hK
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
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq : IsCentralPQuot p (suQ n hK) := isCentralPQuot_suQ hp hp2 hn1 hpq hf1 hK
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  obtain ⟨S, hrel⟩ := wctx_ofCentralQuot' hVexp SM (suQ n hK) hq ε hε h.F_le h.F_exp hFT₁ hFT₂
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
  let Temb : D8Mod p K →* StatedProj (StatedSU n (2 ^ f) K) := (suQ n hK).comp torHom
  have hrel' : ∀ d, ε (Subgroup.inclusion h.F_le (S.tor d)) = Temb d := by
    intro d
    rw [hrel d]
    show suQ n hK (SM.tor d : ↥(SU σ n)) = suQ n hK (torHom d)
    exact congrArg (suQ n hK) (Subtype.ext (hSM d))
  have Hconj : ∀ γ : DihedralGroup 4, ∃ m : StatedProj (StatedSU n (2 ^ f) K),
      ∀ v, m * Temb v * m⁻¹ = Temb (d8Act γ v) := by
    intro γ
    refine ⟨suQ n hK ⟨permGL (d8Perm hc γ), hP _ (hc2.comm_rev γ)⟩, fun v => ?_⟩
    show suQ n hK _ * suQ n hK (torHom v) * (suQ n hK _)⁻¹ = suQ n hK (torHom (d8Act γ v))
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
  exact d8_weyl_scalar hp hp2 hζ hcop h.F_le S hε Temb hrel' Hconj Hsmall Hbig hyL hyF

theorem kf1215Scalar5 : KF1215Scalar 5 := by
  intro G _ _ p A c L E ctx hmodel n hn
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact unitary_weyl_scalar (n := 4) (Or.inl rfl) d8Comb_four d8Comb2_four ctx.table_core hmodel
    hyL hyF

theorem kf1215Scalar6 : KF1215Scalar 6 := by
  intro G _ _ p A c L E ctx hmodel n hn
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact unitary_weyl_scalar (n := 5) (Or.inr rfl) d8Comb_five d8Comb2_five ctx.table_core hmodel
    hyL hyF

end CFSG.RankThree.PartOne.KEXC
