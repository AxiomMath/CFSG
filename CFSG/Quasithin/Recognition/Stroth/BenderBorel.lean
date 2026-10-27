module

public import CFSG.Quasithin.EmptyFaithful.SBc5BlockAux
public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type*} [Group K]

private theorem rootCenter_map_conj_eq_of_mem_normalizer {Q : Subgroup K} {d : K}
    (hd : d ∈ Subgroup.normalizer (Q : Set K)) :
    (rootCenter Q).map (MulAut.conj d).toMonoidHom = rootCenter Q := by
  have hQ : Q.map (MulAut.conj d).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hd
  rw [← rootCenter_map (MulAut.conj d) Q, hQ]

private theorem invariant_le_rootCenter_trichotomy
    [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (Q : Sylow 2 K) (Y : Subgroup K)
    (hYZ : Y ≤ rootCenter (Q : Subgroup K))
    (hYnorm : ∀ d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = rootCenter (Q : Subgroup K) := by
  classical
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  by_cases hYbot : Y = ⊥
  · exact Or.inl hYbot
  · right
    refine le_antisymm hYZ ?_
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Y.one_mem
    · obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
        by_contra h
        push Not at h
        exact hYbot (le_bot_iff.mp fun y hy => Subgroup.mem_bot.mpr (h y hy))
      obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj (hYZ hyY) hy1 hz hz1
      have hd' : d⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
        (Subgroup.normalizer _).inv_mem (cartan_le_borel (Q : Subgroup K) t hd)
      rw [hdz]
      simpa using hYnorm d⁻¹ hd' y hyY

private theorem invariant_sup_rootCenter_eq_or
    [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (Q : Sylow 2 K) (Y : Subgroup K) (hYQ : Y ≤ (Q : Subgroup K))
    (hYnorm : ∀ d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y) :
    Y ⊔ rootCenter (Q : Subgroup K) = rootCenter (Q : Subgroup K) ∨
      Y ⊔ rootCenter (Q : Subgroup K) = (Q : Subgroup K) := by
  classical
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  set Z : Subgroup K := rootCenter Q
  set T : Subgroup K := (Q : Subgroup K)
  have hZY : Z ≤ Subgroup.normalizer (Y : Set K) :=
    le_normalizer_of_commute (fun a ha b hb =>
      ((mem_rootCenter_iff.mp hb).2 a (hYQ ha)))
  have hZW : Z ≤ Y ⊔ Z := le_sup_right
  have hWT : Y ⊔ Z ≤ T := sup_le hYQ (by simpa [Z, T] using rootCenter_le (Q : Subgroup K))
  have hWinv : ∀ d ∈ cartan Q t, ∀ w ∈ Y ⊔ Z, d * w * d⁻¹ ∈ Y ⊔ Z := by
    intro d hd w hw
    obtain ⟨y, hy, z, hz, hweq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZY).mp hw
    rw [hweq]
    have hdN : d ∈ Subgroup.normalizer (T : Set K) := cartan_le_borel Q t hd
    have hz' : d * z * d⁻¹ ∈ Z := by
      have hZmap := rootCenter_map_conj_eq_of_mem_normalizer (Q := (Q : Subgroup K)) hdN
      have h1 : (MulAut.conj d) z ∈ Z.map (MulAut.conj d).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj d).toMonoidHom hz
      rwa [hZmap] at h1
    have hy' : d * y * d⁻¹ ∈ Y := hYnorm d hdN y hy
    rw [show d * (y * z) * d⁻¹ = (d * y * d⁻¹) * (d * z * d⁻¹) by group]
    exact (Y ⊔ Z).mul_mem (Subgroup.mem_sup_left hy') (Subgroup.mem_sup_right hz')
  rcases hB.cases' with ⟨hi1, -, -⟩ | ⟨hi2, he2, a, ha, hn⟩ | ⟨hi3, -, -⟩
  · omega
  · subst hi2
    subst he2
    rcases hc.suzuki_irreducible (hB.suzuki_rootData Q) hZW hWT hWinv with h | h
    · exact Or.inl h
    · exact Or.inr h
  · subst hi3
    rcases hB.irreducible_unitary Q hc.sq_eq_one hc.not_mem (Y ⊔ Z) hZW hWT hWinv with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem eq_top_of_sup_rootCenter_eq_top
    [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (Q : Sylow 2 K) (Y : Subgroup K) (hYQ : Y ≤ (Q : Subgroup K))
    (hYnorm : ∀ d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y)
    (hW : Y ⊔ rootCenter (Q : Subgroup K) = (Q : Subgroup K)) :
    Y = (Q : Subgroup K) := by
  classical
  set Z : Subgroup K := rootCenter Q
  set T : Subgroup K := (Q : Subgroup K)
  have hZY : Z ≤ Subgroup.normalizer (Y : Set K) :=
    le_normalizer_of_commute (fun a ha b hb =>
      ((mem_rootCenter_iff.mp hb).2 a (hYQ ha)))
  have hcomm : ⁅T, T⁆ = Z := (BenderType.lemma_3_5_a hB hi Q).1
  have hTY : T ≤ Subgroup.normalizer (Y : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Y.map (MulAut.conj t).toMonoidHom ≤ Y := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      simpa using hYnorm t (Subgroup.le_normalizer ht) y' hy'
    have hcard : Nat.card (Y.map (MulAut.conj t).toMonoidHom) = Nat.card Y :=
      Subgroup.card_map_of_injective (K := Y) (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hYnormal : (Y.subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hTY
  let π : T →* T ⧸ Y.subgroupOf T := QuotientGroup.mk' _
  let φ : Z →* T ⧸ Y.subgroupOf T :=
    π.comp (Subgroup.inclusion (rootCenter_le (Q : Subgroup K)))
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨t, htq⟩ := QuotientGroup.mk'_surjective _ q
    rw [← htq]
    have htW : (t : K) ∈ Y ⊔ Z := by
      rw [hW]
      exact t.2
    obtain ⟨y, hy, z, hz, htz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZY).mp htW
    refine ⟨⟨z, hz⟩, ?_⟩
    have hzT : (Subgroup.inclusion (rootCenter_le (Q : Subgroup K)) ⟨z, hz⟩ : T) *
        (t : T)⁻¹ = ⟨y⁻¹, hYQ (Y.inv_mem hy)⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, htz]
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mk]
      group
    have hmem : (Subgroup.inclusion (rootCenter_le (Q : Subgroup K)) ⟨z, hz⟩ : T) *
        (t : T)⁻¹ ∈ Y.subgroupOf T := by
      rw [hzT]
      exact Y.inv_mem hy
    exact (QuotientGroup.eq_iff_div_mem).mpr (by simpa [div_eq_mul_inv] using hmem)
  have hZcomm : IsMulCommutative Z :=
    ⟨⟨fun a b => Subtype.ext
      ((mem_rootCenter_iff.mp a.2).2 b (rootCenter_le (Q : Subgroup K) b.2)).symm⟩⟩
  haveI : IsMulCommutative (T ⧸ Y.subgroupOf T) :=
    ⟨⟨fun a b => by
      obtain ⟨za, rfl⟩ := hφsurj a
      obtain ⟨zb, rfl⟩ := hφsurj b
      exact congrArg φ (hZcomm.is_comm.comm za zb)⟩⟩
  have hcommY : _root_.commutator T ≤ Y.subgroupOf T :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp inferInstance
  have hZleY : Z ≤ Y := by
    rw [← hcomm]
    have h1 : (_root_.commutator T).map T.subtype ≤ (Y.subgroupOf T).map T.subtype :=
      Subgroup.map_mono hcommY
    rw [map_commutator_eq, Subgroup.range_subtype T,
      Subgroup.map_subgroupOf_eq_of_le hYQ] at h1
    exact h1
  calc Y = Y ⊔ Z := (sup_eq_left.mpr hZleY).symm
    _ = T := hW

private theorem benderType_invariant_trichotomy
    [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (Q : Sylow 2 K) (Y : Subgroup K) (hYQ : Y ≤ (Q : Subgroup K))
    (hYnorm : ∀ d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = (Q : Subgroup K) ∨ Y = rootCenter (Q : Subgroup K) := by
  by_cases hYZ : Y ≤ rootCenter (Q : Subgroup K)
  · rcases invariant_le_rootCenter_trichotomy hB Q Y hYZ hYnorm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have hW := invariant_sup_rootCenter_eq_or hB hi Q Y hYQ hYnorm
    have hT : Y ⊔ rootCenter (Q : Subgroup K) = (Q : Subgroup K) := by
      rcases hW with h | h
      · exfalso
        apply hYZ
        intro y hy
        have h1 : y ∈ Y ⊔ rootCenter (Q : Subgroup K) := Subgroup.mem_sup_left hy
        rwa [h] at h1
      · exact h
    exact Or.inr (Or.inl (eq_top_of_sup_rootCenter_eq_top hB hi Q Y hYQ hYnorm hT))

private theorem map_normalizer_eq_of_central_odd_ker
    {K1 K : Type} [Group K1] [Group K] [Finite K1]
    (ψ : K1 →* K) (hψ : Function.Surjective ψ)
    (hZc : ψ.ker ≤ Subgroup.center K1)
    (hZo : ∀ z ∈ ψ.ker, Odd (orderOf z))
    (T1 : Subgroup K1) (hT1 : IsPGroup 2 T1) :
    (Subgroup.normalizer (T1 : Set K1)).map ψ =
      Subgroup.normalizer ((T1.map ψ : Subgroup K) : Set K) := by
  have hcomap : (T1.map ψ).comap ψ = T1 ⊔ ψ.ker := Subgroup.comap_map_eq ψ T1
  have hker_normal : (ψ.ker).Normal := by
    refine Subgroup.Normal.mk ?_
    intro z hz g
    have hcomm := Subgroup.mem_center_iff.mp (hZc hz) g
    rw [show g * z * g⁻¹ = z by
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hcomm]
        _ = z := by group]
    exact hz
  have hfwd : ∀ m ∈ Subgroup.normalizer (T1 : Set K1), ∀ y ∈ T1 ⊔ ψ.ker,
      m * y * m⁻¹ ∈ T1 ⊔ ψ.ker := by
    intro m hm y hy
    haveI : (ψ.ker).Normal := hker_normal
    obtain ⟨s, hs, z, hz, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := T1) (t := ψ.ker)).mp hy
    have h1 : m * s * m⁻¹ ∈ T1 ⊔ ψ.ker :=
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hm s).mp hs)
    have h2 : z ∈ T1 ⊔ ψ.ker := Subgroup.mem_sup_right hz
    have h3 : m * (s * z) * m⁻¹ = (m * s * m⁻¹) * z := by
      have hzc := Subgroup.mem_center_iff.mp (hZc hz) m
      have hzc' : z * m⁻¹ = m⁻¹ * z := (show Commute z m from hzc.symm).inv_right
      calc m * (s * z) * m⁻¹ = m * s * (z * m⁻¹) := by group
        _ = m * s * (m⁻¹ * z) := by rw [hzc']
        _ = (m * s * m⁻¹) * z := by group
    rw [h3]
    exact (T1 ⊔ ψ.ker).mul_mem h1 h2
  have hNsup : Subgroup.normalizer ((T1 ⊔ ψ.ker : Subgroup K1) : Set K1) =
      Subgroup.normalizer (T1 : Set K1) := by
    apply le_antisymm
    · intro n hn
      have hfwdT : T1.map (MulAut.conj n).toMonoidHom ≤ T1 := by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
        have h1 : n * t * n⁻¹ ∈ T1 ⊔ ψ.ker :=
          (Subgroup.mem_normalizer_iff.mp hn t).mp (Subgroup.mem_sup_left ht)
        haveI : (ψ.ker).Normal := hker_normal
        obtain ⟨s, hs, z, hz, hsz⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := T1) (t := ψ.ker)).mp h1
        obtain ⟨a, ha⟩ := hT1 ⟨t, ht⟩
        have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
        have hconj : orderOf (n * t * n⁻¹) = orderOf t := by
          have hsc : SemiconjBy n t (n * t * n⁻¹) := by
            show n * t = (n * t * n⁻¹) * n
            group
          exact (SemiconjBy.orderOf_eq n hsc).symm
        obtain ⟨b, hb⟩ := hT1 ⟨s, hs⟩
        have hb' : s ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
        have hcomm : s * z = z * s := Subgroup.mem_center_iff.mp (hZc hz) s
        have hzk : z ^ 2 ^ max a b = 1 := by
          have h1 : (s * z) ^ 2 ^ max a b = 1 := by
            refine orderOf_dvd_iff_pow_eq_one.mp ?_
            rw [hsz, hconj]
            exact dvd_trans (orderOf_dvd_of_pow_eq_one ha')
              (pow_dvd_pow 2 (le_max_left a b))
          rw [Commute.mul_pow hcomm] at h1
          have hs1 : s ^ 2 ^ max a b = 1 := by
            obtain ⟨c, hc⟩ := pow_dvd_pow 2 (le_max_right a b)
            rw [hc, pow_mul, hb', one_pow]
          rw [hs1, one_mul] at h1
          exact h1
        have hz1 : z = 1 := by
          have hdvd : orderOf z ∣ 2 ^ max a b := orderOf_dvd_of_pow_eq_one hzk
          have hcop : Nat.Coprime (orderOf z) (2 ^ max a b) :=
            (Nat.coprime_two_right.mpr (hZo z hz)).pow_right _
          exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)
        rw [hz1, mul_one] at hsz
        change n * t * n⁻¹ ∈ T1
        rw [← hsz]
        exact hs
      have hcard : Nat.card (T1.map (MulAut.conj n).toMonoidHom) = Nat.card T1 :=
        Subgroup.card_map_of_injective (K := T1) (f := (MulAut.conj n).toMonoidHom)
          (MulAut.conj n).injective
      have heq : T1.map (MulAut.conj n).toMonoidHom = T1 :=
        Subgroup.eq_of_le_of_card_ge hfwdT (by rw [hcard])
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    · exact Subgroup.normalizer_le_normalizer_sup_normal
  have h1 : (Subgroup.normalizer ((T1.map ψ : Subgroup K) : Set K)).comap ψ =
      Subgroup.normalizer (T1 : Set K1) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective (T1.map ψ) hψ, hcomap, hNsup]
  calc (Subgroup.normalizer (T1 : Set K1)).map ψ
      = ((Subgroup.normalizer ((T1.map ψ : Subgroup K) : Set K)).comap ψ).map ψ := by
        rw [h1]
    _ = Subgroup.normalizer ((T1.map ψ : Subgroup K) : Set K) :=
        Subgroup.map_comap_eq_self_of_surjective hψ _

private theorem trichotomy_of_cover
    {K1 K : Type} [Group K1] [Group K] [Finite K1] [Finite K]
    (ψ : K1 →* K) (hψ : Function.Surjective ψ)
    (hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (T1 : Subgroup K1) (hT1 : IsSylowTwoOf T1 ⊤)
    (hHmap : (Subgroup.normalizer (T1 : Set K1)).map ψ =
      Subgroup.normalizer ((T1.map ψ : Subgroup K) : Set K))
    (Y : Subgroup K1) (hYT : Y ≤ T1)
    (hYnorm : ∀ d ∈ Subgroup.normalizer (T1 : Set K1), ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = T1 ∨ ∀ t ∈ T1, t ∈ Y ↔ t ^ 2 = 1 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : ∀ a ∈ T1, ∀ b ∈ T1, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hmemT : a⁻¹ * b ∈ T1 := T1.mul_mem (T1.inv_mem ha) hb
    obtain ⟨k, hk⟩ := hT1.2.1 ⟨a⁻¹ * b, hmemT⟩
    have hk' : (a⁻¹ * b) ^ 2 ^ k = 1 := by simpa using hk
    have h3 : (a⁻¹ * b) ^ 3 = 1 := hker3 _ hmem
    have hdvd1 : orderOf (a⁻¹ * b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd2 : orderOf (a⁻¹ * b) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hodd : Odd (orderOf (a⁻¹ * b)) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with h | h
      · rw [h]; exact odd_one
      · rw [h]; exact ⟨1, rfl⟩
    have hcop : Nat.Coprime (orderOf (a⁻¹ * b)) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hodd).pow_right k
    have h1 : orderOf (a⁻¹ * b) = 1 := hcop.eq_one_of_dvd hdvd1
    have h2 : a⁻¹ * b = 1 := orderOf_eq_one_iff.mp h1
    exact inv_mul_eq_one.mp h2
  let P1 : Sylow 2 K1 := hT1.2.1.toSylow (by
    simpa [show (T1.subgroupOf ⊤).index = T1.index from Subgroup.relIndex_top_right _]
      using hT1.2.2)
  let P2 : Sylow 2 K := P1.mapSurjective hψ
  have hP2coe : (P2 : Subgroup K) = T1.map ψ := Sylow.coe_mapSurjective hψ P1
  let YK : Subgroup K := Y.map ψ
  have hYKle : YK ≤ (P2 : Subgroup K) := by
    rw [hP2coe]
    exact Subgroup.map_mono hYT
  have hYKnorm : ∀ d ∈ Subgroup.normalizer ((P2 : Subgroup K) : Set K), ∀ y ∈ YK,
      d * y * d⁻¹ ∈ YK := by
    intro d hd y hy
    rw [hP2coe, ← hHmap] at hd
    obtain ⟨d1, hd1, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨y1, hy1, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨d1 * y1 * d1⁻¹, hYnorm d1 hd1 y1 hy1, ?_⟩
    simp [map_mul]
  obtain ⟨t0, hc⟩ := hB.exists_benderCore P2
  rcases benderType_invariant_trichotomy hB hi P2 YK hYKle hYKnorm with h | h | h
  · left
    refine le_bot_iff.mp ?_
    intro y hy
    have hmem : ψ y ∈ YK := Subgroup.mem_map_of_mem ψ hy
    rw [h] at hmem
    have h1 : y = 1 := hinj y (hYT hy) 1 T1.one_mem (by simpa using hmem)
    simpa using h1
  · right
    left
    refine le_antisymm hYT ?_
    intro t ht
    have hmem : ψ t ∈ YK := by
      rw [h, hP2coe]
      exact Subgroup.mem_map_of_mem ψ ht
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp hmem
    have h1 : y = t := hinj y (hYT hy) t ht hyt
    rwa [h1] at hy
  · right
    right
    intro t ht
    constructor
    · intro hyt
      have h1 : ψ t ∈ rootCenter P2 := by
        rw [← h]
        exact Subgroup.mem_map_of_mem ψ hyt
      have h2 := hc.center_sq (ψ t) h1
      have hT2 : t * t ∈ T1 := T1.mul_mem ht ht
      have h3 : t * t = 1 := hinj (t * t) hT2 1 T1.one_mem (by simpa [map_mul] using h2)
      simpa [sq] using h3
    · intro ht2
      by_cases h1 : ψ t = 1
      · have h2 : t = 1 := hinj t ht 1 T1.one_mem (by simpa using h1)
        rw [h2]
        exact Y.one_mem
      · have hmem : ψ t ∈ rootCenter P2 := by
          refine hc.center_of_involution (ψ t) (le_borel (P2 : Subgroup K) ?_) ?_
          · rw [hP2coe]
            exact Subgroup.mem_map_of_mem ψ ht
          · apply orderOf_eq_prime _ h1
            rw [sq]
            simpa [sq, map_mul] using congrArg ψ ht2
        have h2 : ψ t ∈ YK := by
          rw [h]
          exact hmem
        obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp h2
        have h3 : y = t := hinj y (hYT hy) t ht hyt
        rwa [h3] at hy

private theorem normalizer_subgroupOf_eq {L T : Subgroup G} (hTL : T ≤ L) :
    Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) =
      (L ⊓ Subgroup.normalizer (T : Set G)).subgroupOf L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    intro t
    constructor
    · intro ht
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.mpr ht
      exact Subgroup.mem_subgroupOf.mp ((hx ⟨t, hTL ht⟩).mp h1)
    · intro ht
      have htL : t ∈ L := by
        have h1 : x * t * x⁻¹ ∈ L := hTL ht
        have h2 : x⁻¹ * (x * t * x⁻¹) * x ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem x.2) h1) x.2
        have h2' : x⁻¹ * (x * t * x⁻¹) * x = t := by
          change (x : G)⁻¹ * ((x : G) * t * (x : G)⁻¹) * (x : G) = t
          group
        rwa [h2'] at h2
      have h1 : (⟨t, htL⟩ : ↥L) ∈ T.subgroupOf L := by
        refine (hx ⟨t, htL⟩).mpr ?_
        exact Subgroup.mem_subgroupOf.mpr ht
      exact Subgroup.mem_subgroupOf.mp h1
  · rintro ⟨-, hxN⟩ t
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hxN t

theorem vertex_trichotomy_sz {L T X : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a)
    (e : oTwoQuot ↥L ≃* CFSG.Open.Sz a)
    (hT : IsSylowTwoOf T L) (hQX : pCoreOf 2 L ≤ X) (hXT : X ≤ T)
    (hXN : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = pCoreOf 2 L ∨ X = T ∨ ∀ t ∈ T, t ∈ X ↔ t ^ 2 ∈ pCoreOf 2 L := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let X1 : Subgroup K1 := X.subgroupOf L
  let Y : Subgroup (oTwoQuot K1) := X1.map π
  have hT1 : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.comap_of_injective L.subtype L.subtype_injective
    · intro h2
      apply hT.2.2
      have e : ((T1.subgroupOf ⊤).index) = T1.index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      rwa [e] at h2
  have hker_le_T1 : pCore 2 K1 ≤ T1 := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hXT (hQX (Subgroup.mem_map_of_mem L.subtype hq))
  have hT1' : IsSylowTwoOf (T1.map π) ⊤ := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 K1 := hT1.2.1.toSylow (by
      simpa [show (T1.subgroupOf ⊤).index = T1.index from Subgroup.relIndex_top_right _]
        using hT1.2.2)
    let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
    have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P2.isPGroup'
    · rw [show ((T1.map π).subgroupOf ⊤).index = (T1.map π).index from
        Subgroup.relIndex_top_right _]
      rw [← hcoe]
      exact P2.not_dvd_index
  have hker : π.ker ≤ T1 := by
    rw [show π.ker = pCore 2 K1 from QuotientGroup.ker_mk' _]
    exact hker_le_T1
  have hHmap : (Subgroup.normalizer (T1 : Set K1)).map π =
      Subgroup.normalizer ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) :=
    CFSG.Quasithin.SBc5.map_normalizer_eq_of_ker_le π
      (QuotientGroup.mk'_surjective _) (P := T1) hker
  have hN_eq : Subgroup.normalizer (T1 : Set K1) =
      (L ⊓ Subgroup.normalizer (T : Set G)).subgroupOf L :=
    normalizer_subgroupOf_eq hT.1
  have hX1T : X1 ≤ T1 := Subgroup.subgroupOf_mono L hXT
  have hYT : Y ≤ T1.map π := Subgroup.map_mono hX1T
  have hYnorm : ∀ d ∈ Subgroup.normalizer
      ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    rw [← hHmap] at hd
    obtain ⟨d1, hd1, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hd1' : (d1 : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) := by
      have h := hd1
      rw [hN_eq] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    refine Subgroup.mem_map.mpr ⟨d1 * x * d1⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hXN hd1') x).mp hxX
  have hB : BenderType (oTwoQuot K1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have htri := trichotomy_of_cover (ψ := MonoidHom.id (oTwoQuot K1))
    (by intro x; exact ⟨x, rfl⟩)
    (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
    hB (by norm_num) (T1.map π) hT1' (by simp) Y hYT hYnorm
  rcases htri with hbot | htop | hsq
  · left
    refine le_antisymm ?_ hQX
    intro x hxX
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hx1 : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h1 : π ⟨x, hxL⟩ ∈ Y := Subgroup.mem_map_of_mem π hx1
    rw [hbot] at h1
    have h2 : (⟨x, hxL⟩ : K1) ∈ pCore 2 K1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h1
    exact Subgroup.mem_map_of_mem L.subtype h2
  · right
    left
    refine le_antisymm hXT ?_
    intro t htT
    have htL : t ∈ L := hT.1 htT
    have ht1 : (⟨t, htL⟩ : K1) ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    have h1 : π ⟨t, htL⟩ ∈ Y := by
      rw [htop]
      exact Subgroup.mem_map_of_mem π ht1
    obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hxT : (x : G) ∈ T := hXT hxX
    have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ pCore 2 K1 := by
      refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
      show π ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = 1
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hdiffT : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ T1 := hker_le_T1 hdiff
    have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
    have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = ⟨t, htL⟩ := by group
    have h4 : (⟨t, htL⟩ : K1) ∈ X1 := by
      rw [← h5]
      exact X1.mul_mem hxX1' hdiffX
    rwa [Subgroup.mem_subgroupOf] at h4
  · right
    right
    intro t htT
    have htL : t ∈ L := hT.1 htT
    let tK : K1 := ⟨t, htL⟩
    have ht1 : tK ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    constructor
    · intro htX
      have htX1 : tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact htX
      have h1 : π tK ∈ Y := Subgroup.mem_map_of_mem π htX1
      have h2 := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mp h1
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : π (tK ^ 2) = 1 := by simpa [map_pow] using h2
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h4
      have h5 : (tK : G) ^ 2 ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype h3
      simpa using h5
    · intro ht2
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : (t : G) ^ 2 ∈ pCoreOf 2 L := ht2
        obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp h4
        have hqt' : q = tK ^ 2 := Subtype.ext hqt
        rwa [hqt'] at hq
      have h2 : (π tK) ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr h3
      have h1 : π tK ∈ Y := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mpr h2
      obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
      have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
      have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ pCore 2 K1 := by
        refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
        show π ((⟨x, hxL⟩ : K1)⁻¹ * tK) = 1
        rw [map_mul, map_inv, hxeq, inv_mul_cancel]
      have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
      have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hxX
      have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * tK) = tK := by group
      have h4 : tK ∈ X1 := by
        rw [← h5]
        exact X1.mul_mem hxX1' hdiffX
      exact Subgroup.mem_subgroupOf.mp h4

theorem vertex_trichotomy_psu {L T X : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))
    (hT : IsSylowTwoOf T L) (hQX : pCoreOf 2 L ≤ X) (hXT : X ≤ T)
    (hXN : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = pCoreOf 2 L ∨ X = T ∨ ∀ t ∈ T, t ∈ X ↔ t ^ 2 ∈ pCoreOf 2 L := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let X1 : Subgroup K1 := X.subgroupOf L
  let Y : Subgroup (oTwoQuot K1) := X1.map π
  have hT1 : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.comap_of_injective L.subtype L.subtype_injective
    · intro h2
      apply hT.2.2
      have e : ((T1.subgroupOf ⊤).index) = T1.index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      rwa [e] at h2
  have hker_le_T1 : pCore 2 K1 ≤ T1 := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hXT (hQX (Subgroup.mem_map_of_mem L.subtype hq))
  have hT1' : IsSylowTwoOf (T1.map π) ⊤ := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 K1 := hT1.2.1.toSylow (by
      simpa [show (T1.subgroupOf ⊤).index = T1.index from Subgroup.relIndex_top_right _]
        using hT1.2.2)
    let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
    have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P2.isPGroup'
    · rw [show ((T1.map π).subgroupOf ⊤).index = (T1.map π).index from
        Subgroup.relIndex_top_right _]
      rw [← hcoe]
      exact P2.not_dvd_index
  have hker : π.ker ≤ T1 := by
    rw [show π.ker = pCore 2 K1 from QuotientGroup.ker_mk' _]
    exact hker_le_T1
  have hHmap : (Subgroup.normalizer (T1 : Set K1)).map π =
      Subgroup.normalizer ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) :=
    CFSG.Quasithin.SBc5.map_normalizer_eq_of_ker_le π
      (QuotientGroup.mk'_surjective _) (P := T1) hker
  have hN_eq : Subgroup.normalizer (T1 : Set K1) =
      (L ⊓ Subgroup.normalizer (T : Set G)).subgroupOf L :=
    normalizer_subgroupOf_eq hT.1
  have hX1T : X1 ≤ T1 := Subgroup.subgroupOf_mono L hXT
  have hYT : Y ≤ T1.map π := Subgroup.map_mono hX1T
  have hYnorm : ∀ d ∈ Subgroup.normalizer
      ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    rw [← hHmap] at hd
    obtain ⟨d1, hd1, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hd1' : (d1 : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) := by
      have h := hd1
      rw [hN_eq] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    refine Subgroup.mem_map.mpr ⟨d1 * x * d1⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hXN hd1') x).mp hxX
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (oTwoQuot K1) n 3 e' := hBproj.of_mulEquiv e.symm
  have htri := trichotomy_of_cover (ψ := MonoidHom.id (oTwoQuot K1))
    (by intro x; exact ⟨x, rfl⟩)
    (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
    hB (by norm_num) (T1.map π) hT1' (by simp) Y hYT hYnorm
  rcases htri with hbot | htop | hsq
  · left
    refine le_antisymm ?_ hQX
    intro x hxX
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hx1 : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h1 : π ⟨x, hxL⟩ ∈ Y := Subgroup.mem_map_of_mem π hx1
    rw [hbot] at h1
    have h2 : (⟨x, hxL⟩ : K1) ∈ pCore 2 K1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h1
    exact Subgroup.mem_map_of_mem L.subtype h2
  · right
    left
    refine le_antisymm hXT ?_
    intro t htT
    have htL : t ∈ L := hT.1 htT
    have ht1 : (⟨t, htL⟩ : K1) ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    have h1 : π ⟨t, htL⟩ ∈ Y := by
      rw [htop]
      exact Subgroup.mem_map_of_mem π ht1
    obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hxT : (x : G) ∈ T := hXT hxX
    have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ pCore 2 K1 := by
      refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
      show π ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = 1
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hdiffT : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ T1 := hker_le_T1 hdiff
    have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
    have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = ⟨t, htL⟩ := by group
    have h4 : (⟨t, htL⟩ : K1) ∈ X1 := by
      rw [← h5]
      exact X1.mul_mem hxX1' hdiffX
    rwa [Subgroup.mem_subgroupOf] at h4
  · right
    right
    intro t htT
    have htL : t ∈ L := hT.1 htT
    let tK : K1 := ⟨t, htL⟩
    have ht1 : tK ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    constructor
    · intro htX
      have htX1 : tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact htX
      have h1 : π tK ∈ Y := Subgroup.mem_map_of_mem π htX1
      have h2 := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mp h1
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : π (tK ^ 2) = 1 := by simpa [map_pow] using h2
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h4
      have h5 : (tK : G) ^ 2 ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype h3
      simpa using h5
    · intro ht2
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : (t : G) ^ 2 ∈ pCoreOf 2 L := ht2
        obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp h4
        have hqt' : q = tK ^ 2 := Subtype.ext hqt
        rwa [hqt'] at hq
      have h2 : (π tK) ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr h3
      have h1 : π tK ∈ Y := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mpr h2
      obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
      have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
      have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ pCore 2 K1 := by
        refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
        show π ((⟨x, hxL⟩ : K1)⁻¹ * tK) = 1
        rw [map_mul, map_inv, hxeq, inv_mul_cancel]
      have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
      have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hxX
      have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * tK) = tK := by group
      have h4 : tK ∈ X1 := by
        rw [← h5]
        exact X1.mul_mem hxX1' hdiffX
      exact Subgroup.mem_subgroupOf.mp h4

theorem vertex_trichotomy_su {L T X : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedSU 3 (2 ^ n) F)
    (hT : IsSylowTwoOf T L) (hQX : pCoreOf 2 L ≤ X) (hXT : X ≤ T)
    (hXN : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = pCoreOf 2 L ∨ X = T ∨ ∀ t ∈ T, t ∈ X ↔ t ^ 2 ∈ pCoreOf 2 L := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let X1 : Subgroup K1 := X.subgroupOf L
  let S : Subgroup (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (CFSG.Open.StatedSU 3 (2 ^ n) F)
  let ψ : oTwoQuot K1 →* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (QuotientGroup.mk' S).comp e.toMonoidHom
  let Y : Subgroup (oTwoQuot K1) := X1.map π
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective S).comp e.surjective
  have hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have h1 : e z ∈ S := by
      have h2 : (QuotientGroup.mk' S) (e z) = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hz
      exact (QuotientGroup.eq_one_iff (e z)).mp h2
    have h2 : (e z) ^ 3 = 1 := CFSG.Quasithin.statedSU_three_kernel (e z) h1
    exact e.injective (by simpa using h2)
  have hZc : ψ.ker ≤ Subgroup.center (oTwoQuot K1) := by
    intro z hz
    have h1 : e z ∈ S := by
      have h2 : (QuotientGroup.mk' S) (e z) = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hz
      exact (QuotientGroup.eq_one_iff (e z)).mp h2
    have h2 : e z ∈ Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
      CFSG.Quasithin.statedSU_scalars_le_center h1
    have h3 : e z ∈ (Subgroup.center (oTwoQuot K1)).map e.toMonoidHom := by
      have h5 : (Subgroup.center (oTwoQuot K1)).map e.toMonoidHom =
          Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F) := Subgroup.map_center_eq e
      rw [h5]
      exact h2
    have h4 : e.symm (e z) ∈ Subgroup.center (oTwoQuot K1) := Subgroup.mem_map_equiv.mp h3
    simpa using h4
  have hZo : ∀ z ∈ ψ.ker, Odd (orderOf z) := by
    intro z hz
    have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (hker3 z hz)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  have hT1 : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.comap_of_injective L.subtype L.subtype_injective
    · intro h2
      apply hT.2.2
      have e : ((T1.subgroupOf ⊤).index) = T1.index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      rwa [e] at h2
  have hker_le_T1 : pCore 2 K1 ≤ T1 := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hXT (hQX (Subgroup.mem_map_of_mem L.subtype hq))
  have hT1' : IsSylowTwoOf (T1.map π) ⊤ := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 K1 := hT1.2.1.toSylow (by
      simpa [show (T1.subgroupOf ⊤).index = T1.index from Subgroup.relIndex_top_right _]
        using hT1.2.2)
    let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
    have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P2.isPGroup'
    · rw [show ((T1.map π).subgroupOf ⊤).index = (T1.map π).index from
        Subgroup.relIndex_top_right _]
      rw [← hcoe]
      exact P2.not_dvd_index
  have hker : π.ker ≤ T1 := by
    rw [show π.ker = pCore 2 K1 from QuotientGroup.ker_mk' _]
    exact hker_le_T1
  have hHmap : (Subgroup.normalizer (T1 : Set K1)).map π =
      Subgroup.normalizer ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) :=
    CFSG.Quasithin.SBc5.map_normalizer_eq_of_ker_le π
      (QuotientGroup.mk'_surjective _) (P := T1) hker
  have hHmap2 : (Subgroup.normalizer ((T1.map π : Subgroup (oTwoQuot K1)) :
        Set (oTwoQuot K1))).map ψ =
      Subgroup.normalizer (((T1.map π).map ψ :
        Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))) :
        Set (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))) :=
    map_normalizer_eq_of_central_odd_ker ψ hψ hZc hZo (T1.map π) hT1'.2.1
  have hN_eq : Subgroup.normalizer (T1 : Set K1) =
      (L ⊓ Subgroup.normalizer (T : Set G)).subgroupOf L :=
    normalizer_subgroupOf_eq hT.1
  have hX1T : X1 ≤ T1 := Subgroup.subgroupOf_mono L hXT
  have hYT : Y ≤ T1.map π := Subgroup.map_mono hX1T
  have hYnorm : ∀ d ∈ Subgroup.normalizer
      ((T1.map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)), ∀ y ∈ Y,
      d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    rw [← hHmap] at hd
    obtain ⟨d1, hd1, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hd1' : (d1 : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) := by
      have h := hd1
      rw [hN_eq] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    refine Subgroup.mem_map.mpr ⟨d1 * x * d1⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hXN hd1') x).mp hxX
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) n 3 e' := hBproj
  have htri := trichotomy_of_cover (ψ := ψ) hψ hker3 hB (by norm_num)
    (T1.map π) hT1' hHmap2 Y hYT hYnorm
  rcases htri with hbot | htop | hsq
  · left
    refine le_antisymm ?_ hQX
    intro x hxX
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hx1 : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h1 : π ⟨x, hxL⟩ ∈ Y := Subgroup.mem_map_of_mem π hx1
    rw [hbot] at h1
    have h2 : (⟨x, hxL⟩ : K1) ∈ pCore 2 K1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h1
    exact Subgroup.mem_map_of_mem L.subtype h2
  · right
    left
    refine le_antisymm hXT ?_
    intro t htT
    have htL : t ∈ L := hT.1 htT
    have ht1 : (⟨t, htL⟩ : K1) ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    have h1 : π ⟨t, htL⟩ ∈ Y := by
      rw [htop]
      exact Subgroup.mem_map_of_mem π ht1
    obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
    have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
    have hxT : (x : G) ∈ T := hXT hxX
    have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ pCore 2 K1 := by
      refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
      show π ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = 1
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hdiffT : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ T1 := hker_le_T1 hdiff
    have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩ ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
    have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
      rw [Subgroup.mem_subgroupOf]
      exact hxX
    have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * ⟨t, htL⟩) = ⟨t, htL⟩ := by group
    have h4 : (⟨t, htL⟩ : K1) ∈ X1 := by
      rw [← h5]
      exact X1.mul_mem hxX1' hdiffX
    rwa [Subgroup.mem_subgroupOf] at h4
  · right
    right
    intro t htT
    have htL : t ∈ L := hT.1 htT
    let tK : K1 := ⟨t, htL⟩
    have ht1 : tK ∈ T1 := by
      rw [Subgroup.mem_subgroupOf]
      exact htT
    constructor
    · intro htX
      have htX1 : tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact htX
      have h1 : π tK ∈ Y := Subgroup.mem_map_of_mem π htX1
      have h2 := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mp h1
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : π (tK ^ 2) = 1 := by simpa [map_pow] using h2
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp h4
      have h5 : (tK : G) ^ 2 ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype h3
      simpa using h5
    · intro ht2
      have h3 : tK ^ 2 ∈ pCore 2 K1 := by
        have h4 : (t : G) ^ 2 ∈ pCoreOf 2 L := ht2
        obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp h4
        have hqt' : q = tK ^ 2 := Subtype.ext hqt
        rwa [hqt'] at hq
      have h2 : (π tK) ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr h3
      have h1 : π tK ∈ Y := (hsq (π tK) (Subgroup.mem_map_of_mem π ht1)).mpr h2
      obtain ⟨x, hxX1, hxeq⟩ := Subgroup.mem_map.mp h1
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX1
      have hxL : (x : G) ∈ L := hT.1 (hXT hxX)
      have hdiff : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ pCore 2 K1 := by
        refine (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp ?_
        show π ((⟨x, hxL⟩ : K1)⁻¹ * tK) = 1
        rw [map_mul, map_inv, hxeq, inv_mul_cancel]
      have hdiffX : (⟨x, hxL⟩ : K1)⁻¹ * tK ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hQX (Subgroup.mem_map_of_mem L.subtype hdiff)
      have hxX1' : (⟨x, hxL⟩ : K1) ∈ X1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hxX
      have h5 : (⟨x, hxL⟩ : K1) * ((⟨x, hxL⟩ : K1)⁻¹ * tK) = tK := by group
      have h4 : tK ∈ X1 := by
        rw [← h5]
        exact X1.mul_mem hxX1' hdiffX
      exact Subgroup.mem_subgroupOf.mp h4

theorem vertex_trichotomy
    {L T X : Subgroup G} (hL : VSzBig L ∨ VU3Big L)
    (hT : IsSylowTwoOf T L) (hQX : pCoreOf 2 L ≤ X) (hXT : X ≤ T)
    (hXN : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = pCoreOf 2 L ∨ X = T ∨ ∀ t ∈ T, t ∈ X ↔ t ^ 2 ∈ pCoreOf 2 L := by
  rcases hL with ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, F, hFld, hFin, hF, hSUorPSU⟩
  · exact vertex_trichotomy_sz ha e hT hQX hXT hXN
  · letI : Field F := hFld
    letI : Finite F := hFin
    rcases hSUorPSU with hSUe | hPSUe
    · obtain ⟨e⟩ := hSUe
      exact vertex_trichotomy_su hn hF e hT hQX hXT hXN
    · obtain ⟨e⟩ := hPSUe
      exact vertex_trichotomy_psu hn hF e hT hQX hXT hXN

private theorem ker_inf_eq_bot_of_cube
    {K1 K : Type} [Group K1] [Group K]
    (ψ : K1 →* K) (hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {T : Subgroup K1} (hT : IsPGroup 2 T) :
    ψ.ker ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzk, hzT⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨k, hk⟩ := hT ⟨z, hzT⟩
  have hk' : z ^ 2 ^ k = 1 := by simpa using hk
  have h3 : z ^ 3 = 1 := hker3 z hzk
  have hdvd1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hodd : Odd (orderOf z) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  have h1 : orderOf z = 1 := hcop.eq_one_of_dvd hdvd1
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

private theorem relIndex_pCoreOf_sylow
    {L T : Subgroup G}
    {K : Type} [Group K] [Finite K]
    (ψ : oTwoQuot ↥L →* K) (hψ : Function.Surjective ψ)
    (hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (hT : IsSylowTwoOf T L)
    (hT1' : IsSylowTwoOf
      ((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ⊤) :
    (pCoreOf 2 L).relIndex T = (2 ^ n) ^ i := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let TK : Subgroup K := (T1.map π).map ψ
  have hTK : IsSylowTwoOf TK ⊤ := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 (oTwoQuot K1) := hT1'.2.1.toSylow (by
      have hidx : ((T1.map π).subgroupOf ⊤).index = (T1.map π).index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      have h2 := hT1'.2.2
      rwa [hidx] at h2)
    let P2 : Sylow 2 K := P1.mapSurjective hψ
    have hcoe : (P2 : Subgroup K) = TK := Sylow.coe_mapSurjective hψ P1
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P2.isPGroup'
    · rw [show (TK.subgroupOf ⊤).index = TK.index from Subgroup.relIndex_top_right _]
      rw [← hcoe]
      exact P2.not_dvd_index
  let QK : Sylow 2 K := hTK.2.1.toSylow (by
    simpa [show (TK.subgroupOf ⊤).index = TK.index from Subgroup.relIndex_top_right _]
      using hTK.2.2)
  have hQKcoe : (QK : Subgroup K) = TK := IsPGroup.toSylow_coe _ _
  obtain ⟨t, hc⟩ := hB.exists_benderCore QK
  have hcardTK : Nat.card TK = (2 ^ n) ^ i := by
    rw [← hQKcoe]
    exact hc.card_eq
  have hker : π.ker = pCore 2 K1 := QuotientGroup.ker_mk' _
  have hkerbot : ψ.ker ⊓ T1.map π = ⊥ :=
    ker_inf_eq_bot_of_cube ψ hker3 hT1'.2.1
  have hmap1 : (pCoreOf 2 L).relIndex T = (pCore 2 K1).relIndex T1 := by
    rw [pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact Subgroup.relIndex_map_map_of_injective (f := L.subtype) (pCore 2 K1) T1
      L.subtype_injective
  have hmap2 : (pCore 2 K1).relIndex T1 = Nat.card (T1.map π) := by
    have h := Subgroup.relIndex_ker (f := π) (K := T1)
    rwa [hker] at h
  have hmap3 : Nat.card (T1.map π) = Nat.card TK := by
    have h := Subgroup.relIndex_ker (f := ψ) (K := T1.map π)
    have hrel : ψ.ker.relIndex (T1.map π) = Nat.card (T1.map π) := by
      rw [← Subgroup.relIndex_mul_card (H := ψ.ker) (K := T1.map π), hkerbot,
        Subgroup.card_bot, mul_one]
    rw [hrel] at h
    exact h
  rw [hmap1, hmap2, hmap3, hcardTK]

private theorem isSylowTwoOf_map_pCoreQuot {L T : Subgroup G} (hT : IsSylowTwoOf T L) :
    IsSylowTwoOf ((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ⊤ := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  have hT1 : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.comap_of_injective L.subtype L.subtype_injective
    · intro h2
      apply hT.2.2
      have e : ((T1.subgroupOf ⊤).index) = T1.index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      rwa [e] at h2
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P1 : Sylow 2 K1 := hT1.2.1.toSylow (by
    have hidx : ((T1.subgroupOf ⊤).index) = T1.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    have h2 := hT1.2.2
    rwa [hidx] at h2)
  let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
  have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hcoe]
    exact P2.isPGroup'
  · rw [show ((T1.map π).subgroupOf ⊤).index = (T1.map π).index from
      Subgroup.relIndex_top_right _]
    rw [← hcoe]
    exact P2.not_dvd_index

theorem relIndex_pCoreOf_sylow_sz {L T : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (e : oTwoQuot ↥L ≃* CFSG.Open.Sz a) (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = (2 ^ (2 * a + 1)) ^ 2 := by
  have hB : BenderType (oTwoQuot ↥L) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  simpa using relIndex_pCoreOf_sylow (ψ := MonoidHom.id (oTwoQuot ↥L))
    (by intro x; exact ⟨x, rfl⟩)
    (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
    hB (by norm_num) hT hT1'

theorem relIndex_pCoreOf_sylow_psu {L T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))
    (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = (2 ^ n) ^ 3 := by
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (oTwoQuot ↥L) n 3 e' := hBproj.of_mulEquiv e.symm
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  simpa using relIndex_pCoreOf_sylow (ψ := MonoidHom.id (oTwoQuot ↥L))
    (by intro x; exact ⟨x, rfl⟩)
    (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
    hB (by norm_num) hT hT1'

theorem relIndex_pCoreOf_sylow_su {L T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedSU 3 (2 ^ n) F)
    (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = (2 ^ n) ^ 3 := by
  let K1 := ↥L
  let S : Subgroup (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (CFSG.Open.StatedSU 3 (2 ^ n) F)
  let ψ : oTwoQuot K1 →* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (QuotientGroup.mk' S).comp e.toMonoidHom
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective S).comp e.surjective
  have hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have h1 : e z ∈ S := by
      have h2 : (QuotientGroup.mk' S) (e z) = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hz
      exact (QuotientGroup.eq_one_iff (e z)).mp h2
    have h2 : (e z) ^ 3 = 1 := CFSG.Quasithin.statedSU_three_kernel (e z) h1
    exact e.injective (by simpa using h2)
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) n 3 e' := hBproj
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  simpa using relIndex_pCoreOf_sylow (ψ := ψ) hψ hker3 hB (by norm_num) hT hT1'

private theorem exists_X0_id
    {L T : Subgroup G}
    {n i e : ℕ} (hB : BenderType (oTwoQuot ↥L) n i e) (hi : 2 ≤ i)
    (hT : IsSylowTwoOf T L)
    (hT1' : IsSylowTwoOf
      ((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ⊤) :
    ∃ X₀ : Subgroup G,
      (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧
      (pCoreOf 2 L).relIndex X₀ = 2 ^ n ∧
      L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) ∧
      (∀ t ∈ T, t * t = 1 → t ∈ X₀) ∧
      X₀ ≠ T := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let Tbar : Subgroup (oTwoQuot K1) := T1.map π
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let QK : Sylow 2 (oTwoQuot K1) := hT1'.2.1.toSylow (by
    have hidx : ((Tbar.subgroupOf ⊤).index) = Tbar.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    have h2 := hT1'.2.2
    rwa [hidx] at h2)
  have hQKcoe : (QK : Subgroup (oTwoQuot K1)) = Tbar := IsPGroup.toSylow_coe _ _
  obtain ⟨t0, hc⟩ := hB.exists_benderCore QK
  let Z : Subgroup (oTwoQuot K1) := rootCenter QK
  have hZcard : Nat.card Z = 2 ^ n := hc.card_center
  have hker : π.ker = pCore 2 K1 := QuotientGroup.ker_mk' _
  have hker_le_T1 : pCore 2 K1 ≤ T1 := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT
      (Subgroup.mem_map_of_mem L.subtype hx)
  let X0K : Subgroup K1 := Z.comap π
  let X₀ : Subgroup G := X0K.map L.subtype
  have hZleTbar : Z ≤ Tbar := by
    have h := rootCenter_le (QK : Subgroup (oTwoQuot K1))
    rwa [hQKcoe] at h
  have hX0Kle : X0K ≤ T1 := by
    have h1 : X0K ≤ Tbar.comap π := Subgroup.comap_mono hZleTbar
    have h2 : Tbar.comap π = T1 := by
      rw [show Tbar = T1.map π from rfl, Subgroup.comap_map_eq,
        sup_eq_left.mpr (by rw [hker]; exact hker_le_T1)]
    rwa [h2] at h1
  have hX0le : X₀ ≤ T := by
    rw [show X₀ = X0K.map L.subtype from rfl, ← Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact Subgroup.map_mono hX0Kle
  have hmemX0 : ∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L := by
    intro t
    constructor
    · intro ht
      have htT : t ∈ T := hX0le ht
      have htL : t ∈ L := hT.1 htT
      let tK : K1 := ⟨t, htL⟩
      have htX0 : tK ∈ X0K := by
        have h := ht
        rw [show X₀ = X0K.map L.subtype from rfl] at h
        obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp h
        have hxeq : x = tK := Subtype.ext hxt
        rwa [hxeq] at hx
      have hπZ : π tK ∈ Z := htX0
      refine ⟨htT, ?_⟩
      have hsq : (π tK) ^ 2 = 1 := by
        simpa [sq] using hc.center_sq (π tK) hπZ
      have hpow : π (tK ^ 2) = 1 := by simpa [map_pow] using hsq
      have hQ : tK ^ 2 ∈ pCore 2 K1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp hpow
      have hmap : ((tK ^ 2 : K1) : G) ∈ pCoreOf 2 L :=
        Subgroup.mem_map_of_mem L.subtype hQ
      have hcoe : ((tK ^ 2 : K1) : G) = t ^ 2 := by
        rw [Subgroup.coe_pow]
      rwa [hcoe] at hmap
    · rintro ⟨htT, htQ⟩
      have htL : t ∈ L := hT.1 htT
      let tK : K1 := ⟨t, htL⟩
      have ht1 : tK ∈ T1 := by rw [Subgroup.mem_subgroupOf]; exact htT
      have hQ1 : tK ^ 2 ∈ pCore 2 K1 := by
        have h := htQ
        rw [pCoreOf] at h
        obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp h
        have hqt' : q = tK ^ 2 := Subtype.ext hqt
        rwa [hqt'] at hq
      have hπ1 : π (tK ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr hQ1
      have hsq : (π tK) ^ 2 = 1 := by simpa [map_pow] using hπ1
      have hπZ : π tK ∈ Z := by
        by_cases h1 : π tK = 1
        · rw [h1]; exact Z.one_mem
        · have hmemQK : π tK ∈ (QK : Subgroup (oTwoQuot K1)) := by
            rw [hQKcoe]
            exact Subgroup.mem_map_of_mem π ht1
          have hmemB : π tK ∈ borel (QK : Subgroup (oTwoQuot K1)) := by
            show π tK ∈ Subgroup.normalizer ((QK : Subgroup (oTwoQuot K1)) : Set _)
            rw [Subgroup.mem_normalizer_iff]
            intro x
            constructor
            · intro hx
              exact mul_mem (mul_mem hmemQK hx) (inv_mem hmemQK)
            · intro hx
              have h1 := mul_mem (mul_mem (inv_mem hmemQK) hx) hmemQK
              simpa [mul_assoc] using h1
          exact hc.center_of_involution (π tK) hmemB
            (orderOf_eq_prime (by simpa [sq] using hsq) h1)
      exact Subgroup.mem_map_of_mem L.subtype (show tK ∈ X0K from hπZ)
  have hQX0 : pCoreOf 2 L ≤ X₀ := by
    intro q hq
    have hqL : q ∈ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L hq
    let qK : K1 := ⟨q, hqL⟩
    have hqQ1 : qK ∈ pCore 2 K1 := by
      have h := hq
      rw [pCoreOf] at h
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp h
      have hxq' : x = qK := Subtype.ext hxq
      rwa [hxq'] at hx
    have hqT : qK ∈ T1 := hker_le_T1 hqQ1
    have hπq : π qK = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr hqQ1
    have hqX0K : qK ∈ X0K := by
      rw [show X0K = Z.comap π from rfl, Subgroup.mem_comap, hπq]
      exact Z.one_mem
    exact Subgroup.mem_map_of_mem L.subtype hqX0K
  have hrelX0 : (pCoreOf 2 L).relIndex X₀ = 2 ^ n := by
    have h1 : (pCoreOf 2 L).relIndex X₀ = (pCore 2 K1).relIndex X0K :=
      Subgroup.relIndex_map_map_of_injective (f := L.subtype) (pCore 2 K1) X0K
        L.subtype_injective
    have h2 : (pCore 2 K1).relIndex X0K = Nat.card (X0K.map π) := by
      have h := Subgroup.relIndex_ker (f := π) (K := X0K)
      rwa [hker] at h
    have h3 : X0K.map π = Z := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _) Z
    rw [h1, h2, h3, hZcard]
  have hNX0 : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) := by
    have hfwd : ∀ y ∈ L ⊓ Subgroup.normalizer (T : Set G), ∀ t, t ∈ X₀ → y * t * y⁻¹ ∈ X₀ := by
      intro y hy t ht
      have ht' := (hmemX0 t).mp ht
      rw [hmemX0 (y * t * y⁻¹)]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hy.2 t).mp ht'.1, ?_⟩
      have hyQ : y ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hy.1
      have hsq : (y * t * y⁻¹) ^ 2 = y * t ^ 2 * y⁻¹ := by
        rw [sq, sq]
        group
      rw [hsq]
      exact (Subgroup.mem_normalizer_iff.mp hyQ (t ^ 2)).mp ht'.2
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hfwd x hx t
    · intro ht
      have hx' : x⁻¹ ∈ L ⊓ Subgroup.normalizer (T : Set G) :=
        ⟨L.inv_mem hx.1, (Subgroup.normalizer (T : Set G)).inv_mem hx.2⟩
      have h1 := hfwd x⁻¹ hx' (x * t * x⁻¹) ht
      rwa [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h1
  have hinvX0 : ∀ t ∈ T, t * t = 1 → t ∈ X₀ := by
    intro t htT ht2
    rw [hmemX0 t]
    refine ⟨htT, ?_⟩
    have : (t : G) ^ 2 = 1 := by simpa [sq] using ht2
    rw [this]
    exact (pCoreOf 2 L).one_mem
  have hne : X₀ ≠ T := by
    intro heq
    have hrelT : (pCoreOf 2 L).relIndex T = (2 ^ n) ^ i :=
      relIndex_pCoreOf_sylow (ψ := MonoidHom.id (oTwoQuot ↥L))
        (by intro x; exact ⟨x, rfl⟩)
        (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
        hB hi hT hT1'
    rw [heq] at hrelX0
    have hpow : 2 ^ n = (2 ^ n) ^ i := hrelX0.symm.trans hrelT
    have hlt : 2 ^ n < (2 ^ n) ^ i := by
      calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
        _ < (2 ^ n) ^ i := Nat.pow_lt_pow_right
            (Nat.one_lt_two_pow (by have := hB.two_le.2; omega)) hi
    exact (lt_irrefl _) (by rwa [← hpow] at hlt)
  exact ⟨X₀, hmemX0, hQX0, hrelX0, hNX0, hinvX0, hne⟩

theorem exists_X0_sz {L T : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (e : oTwoQuot ↥L ≃* CFSG.Open.Sz a) (hT : IsSylowTwoOf T L) :
    ∃ X₀ : Subgroup G,
      (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧
      (pCoreOf 2 L).relIndex X₀ = (2 ^ (2 * a + 1)) ∧
      L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) ∧
      (∀ t ∈ T, t * t = 1 → t ∈ X₀) ∧
      X₀ ≠ T := by
  have hB : BenderType (oTwoQuot ↥L) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  exact exists_X0_id hB (by norm_num) hT hT1'

theorem exists_X0_psu {L T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))
    (hT : IsSylowTwoOf T L) :
    ∃ X₀ : Subgroup G,
      (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧
      (pCoreOf 2 L).relIndex X₀ = 2 ^ n ∧
      L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) ∧
      (∀ t ∈ T, t * t = 1 → t ∈ X₀) ∧
      X₀ ≠ T := by
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (oTwoQuot ↥L) n 3 e' := hBproj.of_mulEquiv e.symm
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  exact exists_X0_id hB (by norm_num) hT hT1'

private theorem exists_X0_of_quotient
    {L T : Subgroup G}
    {K : Type} [Group K] [Finite K]
    (ψ : oTwoQuot ↥L →* K) (hψ : Function.Surjective ψ)
    (hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {n i e : ℕ} (hB : BenderType K n i e) (hi : 2 ≤ i)
    (hT : IsSylowTwoOf T L)
    (hT1' : IsSylowTwoOf
      ((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ⊤) :
    ∃ X₀ : Subgroup G,
      (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧
      (pCoreOf 2 L).relIndex X₀ = 2 ^ n ∧
      L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) ∧
      (∀ t ∈ T, t * t = 1 → t ∈ X₀) ∧
      X₀ ≠ T := by
  classical
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  let TK : Subgroup K := (T1.map π).map ψ
  have hTK : IsSylowTwoOf TK ⊤ := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 (oTwoQuot K1) := hT1'.2.1.toSylow (by
      have hidx : ((T1.map π).subgroupOf ⊤).index = (T1.map π).index := by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      have h2 := hT1'.2.2
      rwa [hidx] at h2)
    let P2 : Sylow 2 K := P1.mapSurjective hψ
    have hcoe : (P2 : Subgroup K) = TK := Sylow.coe_mapSurjective hψ P1
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P2.isPGroup'
    · rw [show (TK.subgroupOf ⊤).index = TK.index from Subgroup.relIndex_top_right _]
      rw [← hcoe]
      exact P2.not_dvd_index
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let QK : Sylow 2 K := hTK.2.1.toSylow (by
    have hidx : ((TK.subgroupOf ⊤).index) = TK.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    have h2 := hTK.2.2
    rwa [hidx] at h2)
  have hQKcoe : (QK : Subgroup K) = TK := IsPGroup.toSylow_coe _ _
  obtain ⟨t0, hc⟩ := hB.exists_benderCore QK
  let Z : Subgroup K := rootCenter QK
  have hZcard : Nat.card Z = 2 ^ n := hc.card_center
  have hker : π.ker = pCore 2 K1 := QuotientGroup.ker_mk' _
  have hkerbot : ψ.ker ⊓ T1.map π = ⊥ := ker_inf_eq_bot_of_cube ψ hker3 hT1'.2.1
  have hker_le_T1 : pCore 2 K1 ≤ T1 := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT
      (Subgroup.mem_map_of_mem L.subtype hx)
  let X0K : Subgroup K1 := T1 ⊓ (Z.comap ψ).comap π
  let X₀ : Subgroup G := X0K.map L.subtype
  have hX0Kle : X0K ≤ T1 := inf_le_left
  have hX0le : X₀ ≤ T := by
    rw [show X₀ = X0K.map L.subtype from rfl, ← Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact Subgroup.map_mono hX0Kle
  have hmapX0K : X0K.map π = T1.map π ⊓ Z.comap ψ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem π (Subgroup.mem_inf.mp hx).1,
        (Subgroup.mem_inf.mp hx).2⟩
    · intro hy
      obtain ⟨hyT, hyZ⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨x, hxT, rfl⟩ := Subgroup.mem_map.mp hyT
      exact ⟨x, Subgroup.mem_inf.mpr ⟨hxT, hyZ⟩, rfl⟩
  have hinj : ∀ a ∈ T1.map π, ∀ b ∈ T1.map π, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hmemT : a⁻¹ * b ∈ T1.map π := (T1.map π).mul_mem ((T1.map π).inv_mem ha) hb
    have hbot : a⁻¹ * b ∈ (⊥ : Subgroup (oTwoQuot K1)) := by
      have h : a⁻¹ * b ∈ ψ.ker ⊓ T1.map π := Subgroup.mem_inf.mpr ⟨hmem, hmemT⟩
      rwa [hkerbot] at h
    exact inv_mul_eq_one.mp (by simpa using hbot)
  have hmemX0 : ∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L := by
    intro t
    constructor
    · intro ht
      have htT : t ∈ T := hX0le ht
      have htL : t ∈ L := hT.1 htT
      let tK : K1 := ⟨t, htL⟩
      have htX0 : tK ∈ X0K := by
        have h := ht
        rw [show X₀ = X0K.map L.subtype from rfl] at h
        obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp h
        have hxeq : x = tK := Subtype.ext hxt
        rwa [hxeq] at hx
      have ht1 : tK ∈ T1 := hX0Kle htX0
      have hπZ : ψ (π tK) ∈ Z := (Subgroup.mem_inf.mp htX0).2
      refine ⟨htT, ?_⟩
      have hsq : (ψ (π tK)) ^ 2 = 1 := by
        simpa [sq] using hc.center_sq (ψ (π tK)) hπZ
      have hψ1 : ψ (π (tK ^ 2)) = 1 := by simpa [map_pow] using hsq
      have hker : π (tK ^ 2) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact hψ1
      have hT1sq : π (tK ^ 2) ∈ T1.map π :=
        Subgroup.mem_map_of_mem π (by simpa [sq] using T1.mul_mem ht1 ht1)
      have hbot : π (tK ^ 2) ∈ (⊥ : Subgroup (oTwoQuot K1)) := by
        have h : π (tK ^ 2) ∈ ψ.ker ⊓ T1.map π := Subgroup.mem_inf.mpr ⟨hker, hT1sq⟩
        rwa [hkerbot] at h
      have hπ1 : π (tK ^ 2) = 1 := by simpa using hbot
      have hQ : tK ^ 2 ∈ pCore 2 K1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mp hπ1
      have hmap : ((tK ^ 2 : K1) : G) ∈ pCoreOf 2 L :=
        Subgroup.mem_map_of_mem L.subtype hQ
      have hcoe : ((tK ^ 2 : K1) : G) = t ^ 2 := by
        rw [Subgroup.coe_pow]
      rwa [hcoe] at hmap
    · rintro ⟨htT, htQ⟩
      have htL : t ∈ L := hT.1 htT
      let tK : K1 := ⟨t, htL⟩
      have ht1 : tK ∈ T1 := by rw [Subgroup.mem_subgroupOf]; exact htT
      have hQ1 : tK ^ 2 ∈ pCore 2 K1 := by
        have h := htQ
        rw [pCoreOf] at h
        obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp h
        have hqt' : q = tK ^ 2 := Subtype.ext hqt
        rwa [hqt'] at hq
      have hπ1 : π (tK ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr hQ1
      have hsq : (ψ (π tK)) ^ 2 = 1 := by
        rw [← map_pow, ← map_pow, hπ1, map_one]
      have hψZ : ψ (π tK) ∈ Z := by
        by_cases h1 : ψ (π tK) = 1
        · rw [h1]; exact Z.one_mem
        · have hmemQK : ψ (π tK) ∈ (QK : Subgroup K) := by
            rw [hQKcoe]
            exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_map_of_mem π ht1)
          have hmemB : ψ (π tK) ∈ borel (QK : Subgroup K) := by
            show ψ (π tK) ∈ Subgroup.normalizer ((QK : Subgroup K) : Set _)
            rw [Subgroup.mem_normalizer_iff]
            intro x
            constructor
            · intro hx
              exact mul_mem (mul_mem hmemQK hx) (inv_mem hmemQK)
            · intro hx
              have h := mul_mem (mul_mem (inv_mem hmemQK) hx) hmemQK
              simpa [mul_assoc] using h
          exact hc.center_of_involution (ψ (π tK)) hmemB
            (orderOf_eq_prime (by simpa [sq] using hsq) h1)
      exact Subgroup.mem_map_of_mem L.subtype
        (show tK ∈ X0K from Subgroup.mem_inf.mpr ⟨ht1, hψZ⟩)
  have hQX0 : pCoreOf 2 L ≤ X₀ := by
    intro q hq
    have hqL : q ∈ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L hq
    let qK : K1 := ⟨q, hqL⟩
    have hqQ1 : qK ∈ pCore 2 K1 := by
      have h := hq
      rw [pCoreOf] at h
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp h
      have hxq' : x = qK := Subtype.ext hxq
      rwa [hxq'] at hx
    have hqT : qK ∈ T1 := hker_le_T1 hqQ1
    have hπq : π qK = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 K1) _).mpr hqQ1
    have hψq : ψ (π qK) = 1 := by rw [hπq, map_one]
    have hqX0K : qK ∈ X0K := by
      refine Subgroup.mem_inf.mpr ⟨hqT, ?_⟩
      rw [Subgroup.mem_comap, Subgroup.mem_comap, hψq]
      exact Z.one_mem
    exact Subgroup.mem_map_of_mem L.subtype hqX0K
  have hcard_inter : Nat.card (T1.map π ⊓ Z.comap ψ : Subgroup (oTwoQuot K1)) = Nat.card Z := by
    have hmapψ : (T1.map π ⊓ Z.comap ψ).map ψ = Z := by
      apply le_antisymm
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact (Subgroup.mem_inf.mp hx).2
      · intro y hy
        have hyTK : y ∈ TK := by
          rw [← hQKcoe]
          exact rootCenter_le (QK : Subgroup K) hy
        obtain ⟨x, hxT, hxψ⟩ := Subgroup.mem_map.mp hyTK
        refine ⟨x, Subgroup.mem_inf.mpr ⟨hxT, ?_⟩, hxψ⟩
        rw [Subgroup.mem_comap, hxψ]
        exact hy
    have hinjSub : Function.Injective
        (ψ.comp (T1.map π ⊓ Z.comap ψ).subtype) := by
      intro a b hab
      apply Subtype.ext
      exact hinj a (Subgroup.mem_inf.mp a.2).1 b (Subgroup.mem_inf.mp b.2).1 hab
    have hcard := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥(T1.map π ⊓ Z.comap ψ)))
      (f := ψ.comp (T1.map π ⊓ Z.comap ψ).subtype) hinjSub
    have hrange : (ψ.comp (T1.map π ⊓ Z.comap ψ).subtype).range =
        (T1.map π ⊓ Z.comap ψ).map ψ := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top,
        Subgroup.range_subtype (T1.map π ⊓ Z.comap ψ)]
    rw [Subgroup.map_top, hrange, hmapψ] at hcard
    simpa [Subgroup.card_top] using hcard.symm
  have hrelX0 : (pCoreOf 2 L).relIndex X₀ = 2 ^ n := by
    have h1 : (pCoreOf 2 L).relIndex X₀ = (pCore 2 K1).relIndex X0K :=
      Subgroup.relIndex_map_map_of_injective (f := L.subtype) (pCore 2 K1) X0K
        L.subtype_injective
    have h2 : (pCore 2 K1).relIndex X0K = Nat.card (X0K.map π) := by
      have h := Subgroup.relIndex_ker (f := π) (K := X0K)
      rwa [hker] at h
    rw [h1, h2, hmapX0K, hcard_inter, hZcard]
  have hNX0 : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) := by
    have hfwd : ∀ y ∈ L ⊓ Subgroup.normalizer (T : Set G), ∀ t, t ∈ X₀ → y * t * y⁻¹ ∈ X₀ := by
      intro y hy t ht
      have ht' := (hmemX0 t).mp ht
      rw [hmemX0 (y * t * y⁻¹)]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hy.2 t).mp ht'.1, ?_⟩
      have hyQ : y ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hy.1
      have hsq : (y * t * y⁻¹) ^ 2 = y * t ^ 2 * y⁻¹ := by
        rw [sq, sq]
        group
      rw [hsq]
      exact (Subgroup.mem_normalizer_iff.mp hyQ (t ^ 2)).mp ht'.2
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hfwd x hx t
    · intro ht
      have hx' : x⁻¹ ∈ L ⊓ Subgroup.normalizer (T : Set G) :=
        ⟨L.inv_mem hx.1, (Subgroup.normalizer (T : Set G)).inv_mem hx.2⟩
      have h1 := hfwd x⁻¹ hx' (x * t * x⁻¹) ht
      rwa [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h1
  have hinvX0 : ∀ t ∈ T, t * t = 1 → t ∈ X₀ := by
    intro t htT ht2
    rw [hmemX0 t]
    refine ⟨htT, ?_⟩
    have : (t : G) ^ 2 = 1 := by simpa [sq] using ht2
    rw [this]
    exact (pCoreOf 2 L).one_mem
  have hne : X₀ ≠ T := by
    intro heq
    have hrelT : (pCoreOf 2 L).relIndex T = (2 ^ n) ^ i :=
      relIndex_pCoreOf_sylow (ψ := ψ) hψ hker3 hB hi hT hT1'
    rw [heq] at hrelX0
    have hpow : 2 ^ n = (2 ^ n) ^ i := hrelX0.symm.trans hrelT
    have hlt : 2 ^ n < (2 ^ n) ^ i := by
      calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
        _ < (2 ^ n) ^ i := Nat.pow_lt_pow_right
            (Nat.one_lt_two_pow (by have := hB.two_le.2; omega)) hi
    exact (lt_irrefl _) (by rwa [← hpow] at hlt)
  exact ⟨X₀, hmemX0, hQX0, hrelX0, hNX0, hinvX0, hne⟩

theorem exists_X0_su {L T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedSU 3 (2 ^ n) F)
    (hT : IsSylowTwoOf T L) :
    ∃ X₀ : Subgroup G,
      (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧
      (pCoreOf 2 L).relIndex X₀ = 2 ^ n ∧
      L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₀ : Set G) ∧
      (∀ t ∈ T, t * t = 1 → t ∈ X₀) ∧
      X₀ ≠ T := by
  let K1 := ↥L
  let S : Subgroup (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (CFSG.Open.StatedSU 3 (2 ^ n) F)
  let ψ : oTwoQuot K1 →* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
    (QuotientGroup.mk' S).comp e.toMonoidHom
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective S).comp e.surjective
  have hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have h1 : e z ∈ S := by
      have h2 : (QuotientGroup.mk' S) (e z) = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hz
      exact (QuotientGroup.eq_one_iff (e z)).mp h2
    have h2 : (e z) ^ 3 = 1 := CFSG.Quasithin.statedSU_three_kernel (e z) h1
    exact e.injective (by simpa using h2)
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) n 3 e' := hBproj
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  exact exists_X0_of_quotient (ψ := ψ) hψ hker3 hB (by norm_num) hT hT1'

end CFSG.Quasithin.Stroth