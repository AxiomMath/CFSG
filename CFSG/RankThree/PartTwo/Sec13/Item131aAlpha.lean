module

public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec13.Naturality
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Coprime

variable {X : Type} [Group X] [Finite X]

theorem map_inSubgroup_theta_centralizer_eq {N : Subgroup X} (hN : N.Normal) (b : N) :
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set N))).map N.subtype =
      N ⊓ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({(b : X)} : Set X)) := by
  set C := Subgroup.centralizer ({(b : X)} : Set X) with hC
  have hKC : (Subgroup.centralizer ({b} : Set N)).map N.subtype ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')
  have hK₀ : ((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf C =
      N.subgroupOf C := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, -, hy⟩
      exact hy ▸ y.2
    · intro hz
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      have hzc : (z : X) * b = b * z := Subgroup.mem_centralizer_singleton_iff.mp z.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hzc)
  have hnormal : (((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf C).Normal := by
    rw [hK₀]
    exact Subgroup.Normal.subgroupOf hN _
  have hsub := solvable_prime_complement_core_subnormal_intersection Nat.prime_three
    (Subgroup.Normal.isSubnormal hnormal)
  let e : Subgroup.centralizer ({b} : Set N) ≃*
      ((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf C :=
    ((Subgroup.centralizer ({b} : Set N)).equivMapOfInjective N.subtype
      N.subtype_injective).trans (Subgroup.subgroupOfEquivOfLe hKC).symm
  have hθ := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have hstep : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set N))).map
      N.subtype = (inSubgroup (aschbacherSolvableCore 3)
        (((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf C)).map C.subtype := by
    simp only [inSubgroup]
    rw [← hθ]
    simp only [Subgroup.map_map]
    congr 1
  rw [hstep, hsub, hK₀, Subgroup.map_inf _ _ _ C.subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  have hle : inSubgroup (aschbacherSolvableCore 3) C ≤ C := Subgroup.map_subtype_le _
  change N ⊓ C ⊓ inSubgroup (aschbacherSolvableCore 3) C = _
  rw [inf_assoc, inf_eq_right.mpr hle]

theorem eq_one_of_mem_inSubgroup_theta_of_pow_three {K : Subgroup X} {z : X}
    (hz : z ∈ inSubgroup (aschbacherSolvableCore 3) K) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hp := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hw3 : (⟨w, hw⟩ : aschbacherSolvableCore 3 K) ^ 3 = 1 :=
    Subtype.ext (Subtype.ext (by simpa using h3))
  have hdvd : orderOf (⟨w, hw⟩ : aschbacherSolvableCore 3 K) ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · have h1 := orderOf_eq_one_iff.mp h
    have : w = 1 := congrArg Subtype.val h1
    simp [this]
  · have hd := orderOf_dvd_natCard (⟨w, hw⟩ : aschbacherSolvableCore 3 K)
    rw [h] at hd
    exact absurd hd hp

theorem thetaJ_eq_bot_of_thetaAlpha_subgroupOf_eq_bot {N B : Subgroup X} (hN : N.Normal)
    (hBN : B ≤ N) (hB3 : ∀ β ∈ B, β ^ 3 = 1) (hBc : ∀ β ∈ B, ∀ γ ∈ B, β * γ = γ * β)
    (hα : thetaAlpha 3 (B.subgroupOf N) = ⊥) : thetaJ 3 B = ⊥ := by
  have hJN : thetaJ 3 (B.subgroupOf N) = ⊥ := eq_bot_iff.mpr (hα ▸ le_sup_left)
  refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro β hβ
  set Q := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hQ
  have hβC : β ∈ Subgroup.centralizer ({b} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hBc β hβ b hb)
  have hβN : β ∈ N := hBN hβ
  set z := β * q * β⁻¹ * q⁻¹ with hz
  have hzQ : z ∈ Q := Q.mul_mem (conj_mem_inSubgroup_theta hβC hq) (Q.inv_mem hq)
  have hzN : z ∈ N := by
    have h1 : q * β⁻¹ * q⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hβN) q
    have : z = β * (q * β⁻¹ * q⁻¹) := by rw [hz]; group
    rw [this]
    exact N.mul_mem hβN h1
  have hzβ : β * z = z * β := by
    have hmem : z ∈ N ⊓ Q := ⟨hzN, hzQ⟩
    rw [hQ, ← map_inSubgroup_theta_centralizer_eq hN ⟨b, hBN hb⟩] at hmem
    obtain ⟨z', hz', hz'eq⟩ := hmem
    have hb' : (⟨b, hBN hb⟩ : N) ∈ B.subgroupOf N := Subgroup.mem_subgroupOf.mpr hb
    have hb1' : (⟨b, hBN hb⟩ : N) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    have hle : ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({(⟨b, hBN hb⟩ : N)} : Set N)), B.subgroupOf N⁆ ≤ ⊥ := by
      rw [← hJN]
      exact le_iSup_of_le (⟨b, hBN hb⟩ : N) (le_iSup_of_le hb' (le_iSup_of_le hb1' le_rfl))
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hle
    have h1 := Subgroup.mem_centralizer_iff.mp (hle hz') ⟨β, hβN⟩
      (Subgroup.mem_subgroupOf.mpr hβ)
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    have hz'eq' : (z' : X) = z := hz'eq
    rw [hz'eq'] at h2
    exact h2
  have hpow : ∀ k : ℕ, β ^ k * q * (β ^ k)⁻¹ = z ^ k * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzk : β * z ^ k = z ^ k * β := (Commute.pow_right (Commute.eq hzβ) k).eq
      calc β ^ (k + 1) * q * (β ^ (k + 1))⁻¹ = β * (β ^ k * q * (β ^ k)⁻¹) * β⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = β * z ^ k * q * β⁻¹ := by rw [ih]; group
        _ = z ^ k * (β * q * β⁻¹) := by rw [hzk]; group
        _ = z ^ k * (z * q) := by rw [hz]; group
        _ = z ^ (k + 1) * q := by rw [pow_succ]; group
  have hz3 : z ^ 3 = 1 := by
    have h := hpow 3
    rw [hB3 β hβ, one_mul, inv_one, mul_one] at h
    have : z ^ 3 * q * q⁻¹ = q * q⁻¹ := by rw [← h]
    simpa using this
  have hz1 : z = 1 := eq_one_of_mem_inSubgroup_theta_of_pow_three hzQ hz3
  have : β * q * β⁻¹ * q⁻¹ = 1 := hz1
  have e : β * q = q * β := by
    calc β * q = (β * q * β⁻¹ * q⁻¹) * q * β := by group
      _ = q * β := by rw [this, one_mul]
  exact e

theorem thetaT_inf_eq_bot_of_thetaAlpha_subgroupOf_eq_bot {N B : Subgroup X} (hN : N.Normal)
    (hα : thetaAlpha 3 (B.subgroupOf N) = ⊥) : thetaT 3 B ⊓ N = ⊥ := by
  have hTN : thetaT 3 (B.subgroupOf N) = ⊥ := eq_bot_iff.mpr (hα ▸ le_sup_right)
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨hyT, hyN⟩ := Subgroup.mem_inf.mp hy
  have hmem : (⟨y, hyN⟩ : N) ∈ thetaT 3 (B.subgroupOf N) := by
    simp only [thetaT, Subgroup.mem_iInf]
    intro b hb hb1
    have hyb : y ∈ N ⊓ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({(b : X)} : Set X)) := by
      refine ⟨hyN, ?_⟩
      simp only [thetaT, Subgroup.mem_iInf] at hyT
      exact hyT b (Subgroup.mem_subgroupOf.mp hb) fun h => hb1 (Subtype.ext h)
    rw [← map_inSubgroup_theta_centralizer_eq hN b] at hyb
    obtain ⟨y', hy', hy'eq⟩ := hyb
    have : y' = ⟨y, hyN⟩ := Subtype.ext hy'eq
    rw [← this]
    exact hy'
  rw [hTN] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

end Coprime

section Ambient

variable {M : Type} [Group M] [Finite M]

theorem thetaAlpha_subgroupOf_eq_bot_of_le {B N X : Subgroup M} (hBN : B ≤ N) (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hB3 : ∀ β ∈ B, β ^ 3 = 1)
    (hBc : ∀ β ∈ B, ∀ γ ∈ B, β * γ = γ * β) (hX2 : ∀ x ∈ X, x ^ 2 ∈ N)
    (hα : thetaAlpha 3 (B.subgroupOf N) = ⊥)
    (hinv : ∀ t ∈ thetaT 3 (B.subgroupOf X), t ^ 2 = 1 → (t : M) ∈ N) :
    thetaAlpha 3 (B.subgroupOf X) = ⊥ := by
  set N' := N.subgroupOf X with hN'
  set B' := B.subgroupOf X with hB'
  have hB'N' : B' ≤ N' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hBN (Subgroup.mem_subgroupOf.mp hx))
  have hα' : thetaAlpha 3 (B'.subgroupOf N') = ⊥ := by
    let e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNX
    have he : (B'.subgroupOf N').map e.toMonoidHom = B.subgroupOf N := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp
          (Subgroup.mem_subgroupOf.mp hz))
      · intro hy
        refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_), by simp⟩
        exact Subgroup.mem_subgroupOf.mp hy
    have h := thetaAlpha_map_equiv Nat.prime_three e (B'.subgroupOf N')
    rw [he, hα] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  have hJ := thetaJ_eq_bot_of_thetaAlpha_subgroupOf_eq_bot hN hB'N'
    (fun β hβ => Subtype.ext (by simpa using hB3 _ (Subgroup.mem_subgroupOf.mp hβ)))
    (fun β hβ γ hγ => Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hβ) _
      (Subgroup.mem_subgroupOf.mp hγ))) hα'
  have hT := thetaT_inf_eq_bot_of_thetaAlpha_subgroupOf_eq_bot hN hα'
  have hT' : thetaT 3 B' = ⊥ := by
    refine eq_bot_iff.mpr fun t ht => ?_
    have ht2N : t ^ 2 ∈ N' := Subgroup.mem_subgroupOf.mpr (by simpa using hX2 t t.2)
    have ht21 : t ^ 2 = 1 := by
      have h : t ^ 2 ∈ thetaT 3 B' ⊓ N' := ⟨pow_mem ht 2, ht2N⟩
      rw [hT] at h
      exact Subgroup.mem_bot.mp h
    have h : t ∈ thetaT 3 B' ⊓ N' := ⟨ht, Subgroup.mem_subgroupOf.mpr (hinv t ht ht21)⟩
    rw [hT] at h
    exact h
  rw [thetaAlpha, hJ, hT', sup_bot_eq]

end Ambient

section Automizers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sq_mem_centralizer_of_mem_normalizer_zpowers {c h : G} (hc : orderOf c = 3)
    (hh : h ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    h ^ 2 ∈ Subgroup.centralizer ({c} : Set G) := by
  have hmem : h * c * h⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hh c).mp (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc
    omega
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    intro hdvd
    have h1 : c ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hc]
      exact_mod_cast hdvd
    rw [hk] at h1
    apply hc1
    have : c = h⁻¹ * (h * c * h⁻¹) * h := by group
    rw [this, h1]
    group
  have hkk : (3 : ℤ) ∣ k * k - 1 := by
    have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk' with h1 | h1
    · have e : k * k - 1 = (k - 1) * (k + 1) := by ring
      rw [e]
      exact Dvd.dvd.mul_right (by omega) _
    · have e : k * k - 1 = (k + 1) * (k - 1) := by ring
      rw [e]
      exact Dvd.dvd.mul_right (by omega) _
  have hconj : h ^ 2 * c * (h ^ 2)⁻¹ = c ^ (k * k) := by
    calc h ^ 2 * c * (h ^ 2)⁻¹ = h * (h * c * h⁻¹) * h⁻¹ := by
          rw [sq, mul_inv_rev]; simp only [mul_assoc]
      _ = h * c ^ k * h⁻¹ := by rw [hk]
      _ = (h * c * h⁻¹) ^ k := (conj_zpow).symm
      _ = (c ^ k) ^ k := by rw [hk]
      _ = c ^ (k * k) := by rw [← zpow_mul]
  have hcc : c ^ (k * k) = c := by
    have h1 : c ^ (k * k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hc]
      exact_mod_cast hkk
    calc c ^ (k * k) = c ^ (k * k - 1) * c := by
          rw [← zpow_add_one]; congr 1; ring
      _ = c := by rw [h1, one_mul]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h ^ 2 * c = (h ^ 2 * c * (h ^ 2)⁻¹) * h ^ 2 := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = c * h ^ 2 := by rw [hconj, hcc]

theorem sq_mem_autThetaQuot_centralizer {c : G} (hc : orderOf c = 3) (L : Subgroup G)
    {τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)}
    (hτ : τ ∈ Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L) :
    τ ^ 2 ∈ Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L := by
  obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨h ^ 2, pow_mem hN 2,
    sq_mem_centralizer_of_mem_normalizer_zpowers hc hH, ?_⟩
  have e : (⟨h ^ 2, pow_mem hN 2⟩ : Subgroup.normalizer (L : Set G)) = ⟨h, hN⟩ ^ 2 :=
    Subtype.ext (by simp)
  rw [e, map_pow, map_pow]

theorem autThetaQuot_pow_three {E L : Subgroup G} (hE : ∀ x ∈ E, x ^ 3 = 1)
    {τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hτ : τ ∈ Sec4.autThetaQuot E L) :
    τ ^ 3 = 1 := by
  obtain ⟨z, hzN, hzE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  have h1 : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hE z hzE)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem autThetaQuot_commute {E L : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {τ τ' : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hτ : τ ∈ Sec4.autThetaQuot E L)
    (hτ' : τ' ∈ Sec4.autThetaQuot E L) : τ * τ' = τ' * τ := by
  obtain ⟨z, hzN, hzE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  obtain ⟨z', hz'N, hz'E, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ'
  have h1 : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) * ⟨z', hz'N⟩ =
      ⟨z', hz'N⟩ * ⟨z, hzN⟩ := Subtype.ext (hE z hzE z' hz'E)
  rw [← map_mul, ← map_mul, h1, map_mul, map_mul]

end Automizers

@[expose] def KS131AlphaInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) = ⊥ →
    ∀ t ∈ thetaT 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)),
      t ^ 2 = 1 →
        (t : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈
          Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L

section PartOne

variable {G : Type} [Group G] [Finite G]

theorem thetaAlpha_autThetaQuot_centralizer_ne_bot (hK : KS131AlphaInvolution)
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥ := by
  intro hα
  apply hD.mem_lA.2.2.2
  exact thetaAlpha_subgroupOf_eq_bot_of_le (autThetaQuot_mono hD.A_le_centralizer L)
    (autThetaQuot_mono (centralizer_le_normalizer_zpowers c) L)
    (autThetaQuot_centralizer_normal c L)
    (fun β hβ => autThetaQuot_pow_three hD.isElemAbelian.2 hβ)
    (fun β hβ γ hγ => autThetaQuot_commute (fun x hx y hy => hD.commute hx hy) hβ hγ)
    (fun x hx => sq_mem_autThetaQuot_centralizer hD.orderOf_eq L hx) hα (hK G A c L hD hα)

theorem mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt {c : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 c) (h₂ : K₂ ∈ thetaComponentsAt 3 c) (hne : K₁ ≠ K₂)
    {x : G} (hx : x ∈ K₁) (hxN : x ∈ Subgroup.normalizer (K₂ : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer K₂ := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h₂]
  refine ⟨K₂.mul_mem (K₂.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl), ?_⟩
  have hlC : l⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
    inv_mem (Sec6.le_centralizer_of_mem_thetaComponentsAt h₂ hl)
  have h1 := conj_mem_inSubgroup_theta hlC (Sec10.commutator_mem_theta_of_ne h₁ h₂ hne hx hl)
  have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
  rwa [e] at h1

theorem thetaAlpha_autThetaQuot_centralizer_ne_bot_of_not_le (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hAL : ¬ A ⊓ L ≤ Subgroup.zpowers c) :
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥ := by
  have hst := hD.toPartTwoStanding
  obtain ⟨hcA, hc3, hstar⟩ := zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA
  have hc1 := hD.ne_one
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hAF := hD.mem_partTwoF
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hAC : A ≤ C := hD.A_le_centralizer
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp x.2)
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  have hmax : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'e, fun B hB hAB => ?_⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := x
        obtain ⟨_, y, hy, rfl⟩ := y
        apply Subtype.ext
        change (x : G) * y = y * x
        exact congrArg Subtype.val
          (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hB.2 x hx)
    have hAB' : A ≤ B.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hBA := hAF.2.1 _ hBe hAB'
    intro x hx
    have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  rcases h422 C hS4 A' hmax h27' c' hc'A hc'Z hc'1 with h1 | ⟨L', hL', h9, hα⟩
  · exact absurd h1 hstar
  set L₀ := L'.map C.subtype with hL₀def
  have hL₀c : L₀ ∈ thetaComponentsAt 3 c := ⟨L', hL', rfl⟩
  have hA'N : A' ≤ Subgroup.normalizer (L' : Set C) :=
    h45 C hS4 A' (fun x => ⟨1, Subtype.ext (by simpa using hA'e.2 x x.2)⟩)
      (Or.inr ⟨hA'e, 3, le_rfl, by rw [h27']; norm_num⟩) L' hL'
  have hAN : A ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro a ha
    have hmem : (⟨a, hAC ha⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr ha
    exact (coe_mem_normalizer_map_iff C).mpr (hA'N hmem)
  have hAut : Nat.card (Sec4.autThetaQuot A L₀) = 9 := by
    rw [← hA'map, hL₀def, ← map_autThetaQuot_sub C A' L',
      Subgroup.card_map_of_injective (MulAut.congr (thetaQuotEquivSub C L')).injective, h9]
  have hcT : c ∈ Sec4.thetaQuotCentralizer L₀ :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hL₀c
  have hzc : A ⊓ Sec4.thetaQuotCentralizer L₀ = Subgroup.zpowers c := by
    have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L₀ : Subgroup G) = 3 := by
      have := card_inf_mul_card_autThetaQuot hAN
      rw [hAut, h27] at this
      omega
    have hcmem : c ∈ A ⊓ Sec4.thetaQuotCentralizer L₀ := Subgroup.mem_inf.mpr ⟨hcA, hcT⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcmem)
      (by rw [h3, hc3])).symm
  have hL₀L : L₀ = L := by
    by_contra hne
    apply hAL
    intro d hd
    rw [← hzc]
    exact ⟨hd.1, mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt hD.mem_thetaComponentsAt
      hL₀c (Ne.symm hne) hd.2 (hAN hd.1)⟩
  have hC' : (⊤ : Subgroup C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (thetaQuotEquivSub C L'))
    (Sec4.autThetaQuot A' L') (Sec4.autThetaQuot ⊤ L')] at hα
  rw [map_autThetaQuot_sub, map_autThetaQuot_sub, hA'map, hC'] at hα
  rw [← hL₀L]
  exact hα

@[expose] def KS131AlphaInvolutionCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → A ⊓ L ≤ Subgroup.zpowers c →
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) = ⊥ →
    ∀ t ∈ thetaT 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)),
      t ^ 2 = 1 →
        (t : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈
          Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L

theorem ks131AlphaInvolutionCentral_of (h : KS131AlphaInvolution) :
    KS131AlphaInvolutionCentral :=
  fun G _ _ A c L hD _ hα => h G A c L hD hα

theorem thetaAlpha_autThetaQuot_centralizer_ne_bot_of_central (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hK : KS131AlphaInvolutionCentral) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) :
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥ := by
  by_cases hAL : A ⊓ L ≤ Subgroup.zpowers c
  · intro hα
    apply hD.mem_lA.2.2.2
    exact thetaAlpha_subgroupOf_eq_bot_of_le (autThetaQuot_mono hD.A_le_centralizer L)
      (autThetaQuot_mono (centralizer_le_normalizer_zpowers c) L)
      (autThetaQuot_centralizer_normal c L)
      (fun β hβ => autThetaQuot_pow_three hD.isElemAbelian.2 hβ)
      (fun β hβ γ hγ => autThetaQuot_commute (fun x hx y hy => hD.commute hx hy) hβ hγ)
      (fun x hx => sq_mem_autThetaQuot_centralizer hD.orderOf_eq L hx) hα
      (hK G A c L hD hAL hα)
  · exact thetaAlpha_autThetaQuot_centralizer_ne_bot_of_not_le h422 h45 hD hAL

end PartOne

@[expose] def Gap131Hyp1134 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥ →
    ∀ a ∈ A, a ≠ 1 →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) →
      Sec8.InvTwoBarNontrivial A L ∨
        ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
          ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
            Sec4.thetaQuotCentralizer L

section PartTwo

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_le_of_isSubnormal {K D : Subgroup G} (hKD : K ≤ D)
    (hsn : (K.subgroupOf D).IsSubnormal) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ inSubgroup (aschbacherSolvableCore 3) D := by
  have h1 := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hsn
  have h2 := congrArg (Subgroup.map D.subtype) h1
  have e1 := Sec6.map_inSubgroup_theta_of_injective D.subtype D.subtype_injective (K.subgroupOf D)
  rw [Subgroup.map_subgroupOf_eq_of_le hKD] at e1
  rw [e1, Subgroup.map_inf_eq _ _ D.subtype D.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hKD] at h2
  rw [h2]
  exact inf_le_right

theorem inSubgroup_theta_inf_centralizer_le {c a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) :
    inSubgroup (aschbacherSolvableCore 3) (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set D := C ⊓ Subgroup.centralizer ({a} : Set G) with hD
  have hLC : L ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hKD : L ⊓ Subgroup.centralizer ({a} : Set G) ≤ D := inf_le_inf_right _ hLC
  have hsnC : (L.subgroupOf C).IsSubnormal := (mem_thetaComponentsIn_iff.mp hL).2.2.1
  have hsn : ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D).IsSubnormal := by
    have h := hsnC.comap (Subgroup.inclusion (inf_le_left : D ≤ C))
    convert h using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
      Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  exact inSubgroup_theta_le_of_isSubnormal hKD hsn

omit [Finite G] in
theorem centralizer_closure_pair (c a : G) :
    Subgroup.centralizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem exists_hyperplane_of_theta_inf_centralizer {A L : Subgroup G} {c a : G}
    (hD : Sec13Data G A c L) (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c)
    (h : ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (L ⊓ Subgroup.centralizer ({a} : Set G)), A⁆ ≤
      Sec4.thetaQuotCentralizer L) :
    ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
      ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
        Sec4.thetaQuotCentralizer L := by
  have hA'A : Subgroup.closure {c, a} ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hD.mem_A
    · exact haA
  have hcA' : c ∈ Subgroup.closure ({c, a} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert c _)
  have haA' : a ∈ Subgroup.closure ({c, a} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  refine ⟨Subgroup.closure {c, a}, hA'A, ?_, hcA', ?_⟩
  · have hle := Sec10.card_closure_pair_le (hD.commute hD.mem_A haA) (hD.isElemAbelian.2 c hD.mem_A)
      (hD.isElemAbelian.2 a haA)
    have hlt : Subgroup.zpowers c < Subgroup.closure {c, a} :=
      lt_of_le_of_ne (Subgroup.zpowers_le.mpr hcA') fun he => hac (he ▸ haA')
    have hgt := Subgroup.card_lt_of_lt hlt
    rw [hD.card_zpowers] at hgt
    have hdvd : Nat.card (Subgroup.closure ({c, a} : Set G)) ∣ 3 ^ 3 := by
      rw [show 3 ^ 3 = 27 by norm_num, ← hD.card_eq]
      exact Subgroup.card_dvd_of_le hA'A
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk'] at hle hgt
    rw [hD.card_eq, hk']
    interval_cases k <;> simp_all
  · intro hle
    apply h
    refine le_trans (Subgroup.commutator_mono ?_ le_rfl) hle
    rw [centralizer_closure_pair]
    exact inSubgroup_theta_inf_centralizer_le hD.mem_thetaComponentsAt

end PartTwo

end CFSG.RankThree.PartTwo.Sec13
