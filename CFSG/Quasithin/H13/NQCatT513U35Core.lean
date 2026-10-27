module

public import CFSG.Quasithin.H13.NQCatT513L24

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open scoped commutatorElement Pointwise

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

section Perm

variable {A : Type} [Group A] (Q : Subgroup A) {P : Type*} [Group P]
variable (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

theorem aImg_perm {S D : Subgroup A} (hSN : S ≤ Subgroup.normalizer (Q : Set A))
    (hDN : D ≤ Subgroup.normalizer (Q : Set A))
    (hDS : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A)) (hS2 : IsPGroup 2 ↥S)
    {J : Subgroup (MulAut P)} (hDJ : aImg Q e D ≤ J) (hinnJ : ∀ y : P, MulAut.conj y ∈ J)
    (h2J : ∀ α ∈ J, (∃ n : ℕ, α ^ (2 ^ n) = 1) → ∃ y, α = MulAut.conj y)
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    (hT : ∀ X : Subgroup P, IsPGroup 2 X → pImg Q e (S ⊓ Q) ≤ X → X = pImg Q e (S ⊓ Q)) :
    ∀ t ∈ pImg Q e (S ⊓ Q), ∀ x ∈ aImg Q e D, ∃ x' ∈ aImg Q e D, ∃ t' ∈ pImg Q e (S ⊓ Q),
      MulAut.conj t * x = x' * MulAut.conj t' := by
  intro t ht x hx
  obtain ⟨q, hqQ, hqS, rfl⟩ := (mem_pImg Q e).1 ht
  obtain ⟨d, hdN, hdD, rfl⟩ := (mem_aImg Q e).1 hx
  have hqd : q * d ∈ (S : Set A) * (D : Set A) := Set.mul_mem_mul hqS.1 hdD
  rw [← hDS] at hqd
  obtain ⟨d', hd'D, s', hs'S, hds⟩ := hqd
  have hx'D := autOf_mem_aImg Q e (hDN hd'D) hd'D
  have hmul : (⟨q, Subgroup.le_normalizer hqQ⟩ : ↥(Subgroup.normalizer (Q : Set A))) *
      ⟨d, hdN⟩ = ⟨d', hDN hd'D⟩ * ⟨s', hSN hs'S⟩ := Subtype.ext hds.symm
  have h1 := congrArg (autOf Q e) hmul
  rw [map_mul, map_mul, autOf_of_mem Q e hqQ] at h1
  set t := toP Q e ⟨q, hqQ⟩ with htdef
  have hs' : autOf Q e ⟨s', hSN hs'S⟩ =
      (autOf Q e ⟨d', hDN hd'D⟩)⁻¹ * MulAut.conj t * autOf Q e ⟨d, hdN⟩ := by
    rw [mul_assoc, h1, inv_mul_cancel_left]
  have hs'J : autOf Q e ⟨s', hSN hs'S⟩ ∈ J := by
    rw [hs']
    exact mul_mem (mul_mem (inv_mem (hDJ hx'D)) (hinnJ t)) (hDJ (autOf_mem_aImg Q e hdN hdD))
  have hs'2 : ∃ n : ℕ, autOf Q e ⟨s', hSN hs'S⟩ ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hS2 ⟨s', hs'S⟩
    refine ⟨n, ?_⟩
    have hpow : (⟨s', hSN hs'S⟩ : ↥(Subgroup.normalizer (Q : Set A))) ^ (2 ^ n) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one (⟨s', hs'S⟩ : ↥S)
      rw [hn] at this
      have h2 := congrArg Subtype.val this
      simpa using h2
    rw [← map_pow, hpow, map_one]
  obtain ⟨y, hy⟩ := h2J _ hs'J hs'2
  have hS₁ : IsPGroup 2 (iPart Q e S) :=
    (isPGroup_aImg Q e hSN hS2).of_injective
      (((MulAut.conj : P →* MulAut P).comp (iPart Q e S).subtype).codRestrict (aImg Q e S)
        fun y => y.2)
      fun a b hab => Subtype.ext (hcj (congrArg Subtype.val hab))
  have hS₁T := hT _ hS₁ (pImg_le_iPart Q e)
  have hyT : y ∈ pImg Q e (S ⊓ Q) := by
    rw [← hS₁T]
    show MulAut.conj y ∈ aImg Q e S
    rw [← hy]
    exact autOf_mem_aImg Q e _ hs'S
  refine ⟨_, hx'D, y, hyT, ?_⟩
  rw [← hy, h1]

end Perm

section Core

variable {P : Type*} [Group P] [Finite P]

theorem core_u35 {T : Subgroup P} {z : P} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzc : ∀ t ∈ T, t * z = z * t)
    (hzN : ∀ N : Subgroup P, N ≤ T → T ≤ Subgroup.normalizer (N : Set P) → N ≠ ⊥ → z ∈ N)
    (h16 : ∀ X : Subgroup P, IsPGroup 2 X → Nat.card X ≤ 16)
    (hY : Nat.card ↥⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆ ≤ 120)
    {R₀ : Subgroup P} (hRp : ⁅R₀, R₀⁆ = R₀) (φ : ↥R₀ →* L24) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker)
    {E : Subgroup P} (hER : E ≤ R₀) (hET : E ≤ T) (hEn : T ≤ Subgroup.normalizer (E : Set P))
    (hE2 : IsPGroup 2 E) (hEi : ¬ 2 ∣ (E.subgroupOf R₀).index)
    {b : P} (hbR : b ∈ R₀) (hb3 : orderOf b = 3) (hbz : b * z = z * b)
    {x : MulAut P} (hxz : x z = z) : ∀ y ∈ R₀, x y ∈ R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := φ.ker with hK
  have hRK : Nat.card R₀ = Nat.card K * 60 := by
    have h1 := Subgroup.card_mul_index K
    rw [hK, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top,
      CFSG.Walter.JT.card_of_psl24 (MulEquiv.refl _)] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
  set E' := E.subgroupOf R₀ with hE'
  have hE'c : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE2
  have hEm := Subgroup.card_mul_index E'
  rw [hE'c, hm, hRK, hk] at hEm
  have hiodd : Odd E'.index := Nat.odd_iff.mpr (by omega)
  have hmk : m = k + 2 := by
    have e1 : 2 ^ m * E'.index = 2 ^ (k + 2) * 15 := by rw [hEm, pow_add]; ring
    have h1 : 2 ^ m ∣ 2 ^ (k + 2) := by
      have : 2 ^ m ∣ 2 ^ (k + 2) * 15 := ⟨E'.index, e1.symm⟩
      exact (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_right this
    have h2 : 2 ^ (k + 2) ∣ 2 ^ m := by
      have : 2 ^ (k + 2) ∣ 2 ^ m * E'.index := ⟨15, e1⟩
      exact (Nat.Coprime.pow_left (k + 2) (Nat.coprime_two_left.mpr hiodd)).dvd_of_dvd_mul_right
        this
    have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.mp h1
    have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.mp h2
    omega
  have hE16 := h16 E hE2
  rw [hm, hmk] at hE16
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ (k + 2) ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hK4 : Nat.card K ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hm
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hzE : z ∈ E := hzN E hET hEn hEne
  have hzR : z ∈ R₀ := hER hzE
  set z' : ↥R₀ := ⟨z, hzR⟩ with hz'
  set b' : ↥R₀ := ⟨b, hbR⟩ with hb'
  have hzK : z' ∈ K := by
    by_contra hzK
    have hφz : φ z' ≠ 1 := fun h => hzK (MonoidHom.mem_ker.mpr h)
    have hz'2 : z' ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2)
    have hφz2 : orderOf (φ z') = 2 :=
      orderOf_eq_prime (by rw [← map_pow, hz'2, map_one]) hφz
    have hφb : Odd (orderOf (φ b')) := by
      have h3 : orderOf (φ b') ∣ 3 :=
        (orderOf_map_dvd φ b').trans (by rw [Subgroup.orderOf_mk, hb3])
      exact Odd.of_dvd_nat (by decide) h3
    have hcomm : φ b' * φ z' = φ z' * φ b' := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hbz
    have h1 := CFSG.Walter.JT.eq_one_of_commute_of_psl24 (MulEquiv.refl _) hφb hφz2 hcomm
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hker ⟨b', h1⟩
    have hn' : orderOf b = 2 ^ n := by
      rw [← hn, ← Subgroup.orderOf_coe (⟨b', h1⟩ : ↥K), ← Subgroup.orderOf_coe b']
    rw [hb3] at hn'
    have hn := hn'
    rcases n with _ | n
    · norm_num at hn
    · have : 2 ∣ 2 ^ (n + 1) := dvd_pow_self 2 (by omega)
      omega
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hK2 : 2 ≤ Nat.card K := by
    have : 1 < Nat.card K := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro h
      rw [h] at hzK
      exact hz'1 ((Subgroup.mem_bot).mp hzK)
    omega
  set C := Subgroup.centralizer ({z'} : Set ↥R₀) with hC
  have hCi : C.index ≤ 3 := by
    rw [hC, Subgroup.index_centralizer_eq_ncard]
    have hsub : _root_.conjugatesOf z' ⊆ (K : Set ↥R₀) \ {1} := by
      intro w hw
      obtain ⟨g, rfl⟩ := isConj_iff.mp hw
      refine ⟨(MonoidHom.normal_ker φ).conj_mem z' hzK g, fun h => hz'1 ?_⟩
      rw [Set.mem_singleton_iff, conj_eq_one_iff] at h
      exact h
    calc (_root_.conjugatesOf z').ncard ≤ ((K : Set ↥R₀) \ {1}).ncard :=
          Set.ncard_le_ncard hsub
      _ = Nat.card K - 1 := by
          rw [Set.ncard_sdiff_singleton_of_mem (one_mem K), ← Nat.card_coe_set_eq]
          rfl
      _ ≤ 3 := by omega
  have hEC : E' ≤ C := by
    intro w hw
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hzc _ (hET (Subgroup.mem_subgroupOf.mp hw)))
  have hbC : b' ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hbz
  have h12 : 3 * 2 ^ (k + 2) ∣ Nat.card C := by
    have h1 : 2 ^ (k + 2) ∣ Nat.card C := by
      rw [← hmk, ← hm, ← hE'c]
      exact Subgroup.card_dvd_of_le hEC
    have h2 : 3 ∣ Nat.card C := by
      rw [← hb3, ← Subgroup.orderOf_mk b hbR, ← Subgroup.orderOf_mk (b' : ↥R₀) hbC]
      exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_top _) |>.trans
        (by rw [Subgroup.card_top])
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)) h2 h1
  have hCtop : C = ⊤ := by
    obtain ⟨j, hj⟩ := h12
    have h1 := Subgroup.card_mul_index C
    rw [hj, hRK, hk] at h1
    have h2 : 2 ^ k * (12 * (j * C.index)) = 2 ^ k * 60 := by
      rw [← h1, pow_add]
      ring
    have h3 : j * C.index = 5 := by
      have := Nat.eq_of_mul_eq_mul_left (by positivity) h2
      omega
    have h4 : C.index ∣ 5 := ⟨j, by rw [← h3, mul_comm]⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h4 with h5 | h5
    · exact Subgroup.index_eq_one.mp h5
    · omega
  have hRC : R₀ ≤ Subgroup.centralizer {z} := by
    intro r hr
    have : (⟨r, hr⟩ : ↥R₀) ∈ C := hCtop ▸ Subgroup.mem_top _
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val this
  have hRle : R₀ ≤ ⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆ := by
    rw [← hRp]
    exact Subgroup.commutator_mono hRC hRC
  have hReq : R₀ = ⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆ :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hRK]; omega)
  have hxC : (Subgroup.centralizer {z}).map x.toMonoidHom = Subgroup.centralizer {z} := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← hxz, ← map_mul, ← map_mul, hc']
    · intro c hc
      have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      refine ⟨x.symm c, Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        by simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
      have hxz' : x.symm z = z := (MulEquiv.symm_apply_eq x).mpr hxz.symm
      rw [← hxz', ← map_mul, ← map_mul, hc']
  intro y hy
  rw [hReq] at hy ⊢
  have : x y ∈ (⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆).map x.toMonoidHom :=
    ⟨y, hy, rfl⟩
  rwa [Subgroup.map_commutator, hxC] at this

end Core

end CFSG.Quasithin.H13.NQCat.T513
