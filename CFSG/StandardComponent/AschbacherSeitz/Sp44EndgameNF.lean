module

public import CFSG.StandardComponent.AschbacherSeitz.SpClassical
public import CFSG.StandardComponent.AschbacherSeitz.Cfg76NF
public import CFSG.Adapters.Certificate43Check

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

@[expose] def Sp44EndgameNF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R W L : Subgroup G) (y s y₃ : G),
    NF.Cfg76 A R (zpowers y) L → Sp44 A W L y s y₃ → False

namespace NF

open CFSG.ComponentClassification.RankTwoClassical

section Tools

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)


theorem j2A4_apply (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHypNF Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5) :
    (∀ x ∈ (M.map π).subgroupOf (rankTwoX (M.map π)), orderOf x = 5 →
      ∃ H : Subgroup ↥(rankTwoX (M.map π)),
        H ≤ ⁅centralizer ({x} : Set ↥(rankTwoX (M.map π))),
          centralizer ({x} : Set ↥(rankTwoX (M.map π)))⁆ ∧ Nat.card H = 60 ∧ IsSimpleGroup ↥H) ∧
    (∀ z ∈ (M.map π).subgroupOf (rankTwoX (M.map π)), orderOf z = 3 →
      ∀ β : MulAut ↥(rankTwoX (M.map π)), (∃ k : ℕ, β ^ 5 ^ k = 1) → β z = z → β = 1) ∧
    (∃ f ∈ centralizer (((M.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π))), orderOf f = 3 ∧
      f ∈ normalizer (((R.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π))) ∧
      f ∉ centralizer (((R.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π)))) := by
  set X := rankTwoX (M.map π) with hXdef
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ X := le_normalClosure
  have hRX := map_le_rankTwoX hH hX hR hRM hZM hwM hw5
  have hR2 := isPGroup_of_isElemAbelian hR
  have hcardV : Nat.card ((R.map π).subgroupOf X) = Nat.card R := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv, card_map_mk'_of_two hR2]
  have hcardΛ : Nat.card ((M.map π).subgroupOf X) = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hMX).toEquiv, card_map_mk'_of_inf hMO, hM60]
  have hΛp : ⁅(M.map π).subgroupOf X, (M.map π).subgroupOf X⁆ = (M.map π).subgroupOf X := by
    refine commutator_subgroupOf_eq hMX ?_
    rw [← Subgroup.map_commutator, hMp]
  have hVΛ : (R.map π).subgroupOf X ≤ centralizer (((M.map π).subgroupOf X : Subgroup ↥X) :
      Set ↥X) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    obtain ⟨m, hm, hml⟩ := mem_subgroupOf.mp hl
    apply Subtype.ext
    change (l : Q ⧸ O) * v = v * l
    rw [← hrv, ← hml, ← map_mul, ← map_mul, (mem_centralizer_iff.mp (hRM hr) m hm)]
  exact hJ ↥X hX ((R.map π).subgroupOf X) ((M.map π).subgroupOf X)
    (hR2.map _ |>.comap_subtype) (hcardV ▸ hR4) hcardΛ hΛp hVΛ

theorem exists_three_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHypNF Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5) :
    ∃ f : Q, f ∈ centralizer (M : Set Q) ∧ f ∈ normalizer (R : Set Q) ∧
      (∃ k : ℕ, f ^ 3 ^ k = 1) ∧ f ∉ centralizer (R : Set Q) := by
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hRX := map_le_rankTwoX hH hX hR hRM hZM hwM hw5
  obtain ⟨-, -, fb, hfΛ, hf3, hfV, hfV'⟩ :=
    j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hwM hw5
  have hf1M : ∀ m ∈ M, π m * (fb : Q ⧸ O) = (fb : Q ⧸ O) * π m := by
    intro m hm
    have h := mem_centralizer_iff.mp hfΛ ⟨π m, hMX (mem_map_of_mem _ hm)⟩
      (mem_subgroupOf.mpr (mem_map_of_mem _ hm))
    simpa using congrArg Subtype.val h
  have hf1R : (fb : Q ⧸ O) ∈ normalizer ((R.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h := (mem_normalizer_iff.mp hfV ⟨z, hRX hz⟩).mp (mem_subgroupOf.mpr hz)
      simpa using mem_subgroupOf.mp h
    · intro hz
      have hzX : z ∈ rankTwoX (M.map π) := by
        have h1 : (fb : Q ⧸ O) * z * (fb : Q ⧸ O)⁻¹ ∈ rankTwoX (M.map π) := hRX hz
        have h2 : (fb : Q ⧸ O)⁻¹ * ((fb : Q ⧸ O) * z * (fb : Q ⧸ O)⁻¹) * (fb : Q ⧸ O) ∈
            rankTwoX (M.map π) := mul_mem (mul_mem (inv_mem fb.2) h1) fb.2
        simpa [mul_assoc] using h2
      have h := (mem_normalizer_iff.mp hfV ⟨z, hzX⟩).mpr (mem_subgroupOf.mpr (by simpa using hz))
      exact mem_subgroupOf.mp h
  obtain ⟨f₀, hf₀⟩ := QuotientGroup.mk'_surjective O (fb : Q ⧸ O)
  rw [← hf₀] at hf1R
  obtain ⟨o, ho, hof⟩ := exists_mul_mem_normalizer_of_mk' (isPGroup_of_isElemAbelian hR) hf1R
  have hπf₂ : π (o * f₀) = (fb : Q ⧸ O) := by rw [map_mul, mk'_eq_one_of_mem ho, one_mul, hf₀]
  have hf₂M : o * f₀ ∈ centralizer (M : Set Q) := by
    refine mem_centralizer_of_disp_mem (oddCore_le_of_rankTwoHypNF hH)
      (isSimpleGroup_of_isQuasisimple hH.standard.1 hZM) (by rw [hM60]; decide) fun m hm => ?_
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      hπf₂]
    have h := hf1M m hm
    calc (π m)⁻¹ * ((fb : Q ⧸ O) * π m * (fb : Q ⧸ O)⁻¹)
        = (π m)⁻¹ * (π m * (fb : Q ⧸ O) * (fb : Q ⧸ O)⁻¹) := by rw [h]
      _ = 1 := by group
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (o * f₀)).ne' 3
    (by norm_num)
  refine ⟨(o * f₀) ^ b, Subgroup.pow_mem _ hf₂M b, Subgroup.pow_mem _ hof b, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  · intro hc
    apply hfV'
    have hcop : Nat.Coprime b (orderOf fb) := by
      rw [hf3]
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3)
    obtain ⟨c, hc'⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hc']
    refine Subgroup.pow_mem _ ?_ c
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    apply Subtype.ext
    have h2 := congrArg π (mem_centralizer_iff.mp hc r hr)
    rw [map_mul, map_mul, map_pow, hπf₂] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [← hrv]
    exact h2

theorem exists_five_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHypNF Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {x : Q} (hxM : x ∈ M) (hx5 : orderOf x = 5) :
    ∃ S : Subgroup Q, S ≤ centralizer ({x} : Set Q) ∧ ∀ N : Subgroup Q, N ≤ S →
      S ≤ normalizer (N : Set Q) → Odd (Nat.card N) →
        ∃ h ∈ S, (∃ k : ℕ, h ^ 5 ^ k = 1) ∧ h ∉ N := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hxX : π x ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hxM)
  obtain ⟨ha, -, -⟩ := j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hxM hx5
  obtain ⟨Hb, hHb, hHb60, hHbs⟩ := ha ⟨π x, hxX⟩ (mem_subgroupOf.mpr (mem_map_of_mem _ hxM))
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hxM, hx5])
  set H' := Hb.map (rankTwoX (M.map π)).subtype with hH'
  have hK : (centralizer ({(⟨π x, hxX⟩ : ↥(rankTwoX (M.map π)))} : Set ↥(rankTwoX (M.map π)))).map
      (rankTwoX (M.map π)).subtype = rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)) := by
    ext z
    rw [mem_map, mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff] at hw
      exact ⟨w.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hw)⟩
    · rintro ⟨hzX, hzC⟩
      exact ⟨⟨z, hzX⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hzC)), rfl⟩
  have hH'le : H' ≤ ⁅rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)),
      rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O))⁆ := by
    rw [← hK, ← map_commutator, hH']
    exact map_mono hHb
  set S := centralizer ({x} : Set Q) ⊓ H'.comap π with hS
  have hSlift : ∀ c ∈ H', ∃ c' ∈ S, π c' = c := by
    intro c hc
    obtain ⟨c', hc'x, hc'c⟩ := commutator_lift hH hxM (hH'le hc)
    exact ⟨c', mem_inf.mpr ⟨hc'x, mem_comap.mpr (hc'c ▸ hc)⟩, hc'c⟩
  have hH'card : Nat.card H' = 60 := by
    rw [hH', card_map_of_injective (rankTwoX (M.map π)).subtype_injective, hHb60]
  have hH's : IsSimpleGroup ↥H' := by
    have := hHbs
    exact (Hb.equivMapOfInjective _ (rankTwoX (M.map π)).subtype_injective).symm.isSimpleGroup
  refine ⟨S, inf_le_left, fun N hNS hSN hNodd => ?_⟩
  have hNH : N.map π ≤ H' := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_comap.mp (mem_inf.mp (hNS hn)).2
  have hNn : ((N.map π).subgroupOf H').Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNH]
    intro c hc
    obtain ⟨c', hc'S, rfl⟩ := hSlift c hc
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨c' * n * c'⁻¹, (mem_normalizer_iff.mp (hSN hc'S) n).mp hn, by simp⟩
    · rintro ⟨n, hn, hnz⟩
      refine ⟨c'⁻¹ * n * c', ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (hSN (inv_mem hc'S)) n).mp hn
        simpa [mul_assoc] using this
      · rw [map_mul, map_mul, map_inv, hnz]
        group
  have hNbot : N.map π = ⊥ := by
    have := hH's
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map π).subgroupOf H') with h | h
    · rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hNH hz⟩ : ↥H') ∈ (N.map π).subgroupOf H' := mem_subgroupOf.mpr hz
      rw [h, mem_bot] at hz'
      exact mem_bot.mpr (congrArg Subtype.val hz')
    · exfalso
      have heq : N.map π = H' := by
        refine le_antisymm hNH fun z hz => ?_
        have hz' : (⟨z, hz⟩ : ↥H') ∈ (N.map π).subgroupOf H' := by rw [h]; exact mem_top _
        exact mem_subgroupOf.mp hz'
      have hdvd : Nat.card (N.map π) ∣ Nat.card N := Subgroup.card_map_dvd _ _
      rw [heq, hH'card] at hdvd
      have := hNodd.of_dvd_nat hdvd
      norm_num at this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H') 5 (by rw [hH'card]; norm_num)
  obtain ⟨c', hc'S, hc'c⟩ := hSlift c c.2
  obtain ⟨a, b, hb5, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c').ne' 5
    (by norm_num)
  refine ⟨c' ^ b, Subgroup.pow_mem _ hc'S b, ⟨a, ?_⟩, fun hN => ?_⟩
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  · have h1 : π (c' ^ b) = 1 := by
      have : π (c' ^ b) ∈ N.map π := mem_map_of_mem _ hN
      rwa [hNbot, mem_bot] at this
    rw [map_pow, hc'c] at h1
    have h2 : orderOf (c : Q ⧸ O) ∣ b := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hc5] at h2
    exact hb5 h2

theorem mk'_eq_one_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHypNF Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5)
    {z : Q} (hzM : z ∈ M) (hz3 : orderOf z = 3) {t : Q} (ht5 : ∃ k : ℕ, t ^ 5 ^ k = 1)
    (htz : t * z = z * t) : π t = 1 := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hXn : (rankTwoX (M.map π)).Normal := normalClosure_normal
  obtain ⟨-, hc, -⟩ := j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hwM hw5
  have hzX : π z ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hzM)
  obtain ⟨k, hk⟩ := ht5
  have hβ := hc ⟨π z, hzX⟩ (mem_subgroupOf.mpr (mem_map_of_mem _ hzM))
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hzM, hz3]) (MulAut.conjNormal (π t))
    ⟨k, by rw [← map_pow, ← map_pow, hk, map_one, map_one]⟩
    (Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change π t * π z * (π t)⁻¹ = π z
      rw [← map_mul, htz, map_mul, mul_inv_cancel_right]))
  have hC : π t ∈ centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun β : MulAut ↥(rankTwoX (M.map π)) => ((β ⟨y, hy⟩ :
      ↥(rankTwoX (M.map π))) : Q ⧸ O)) hβ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * π t = π t * y * (π t)⁻¹ * π t := by rw [h]
      _ = π t * y := by group
  rw [centralizer_rankTwoX_eq_bot hH, mem_bot] at hC
  exact hC

theorem mk'_eq_one_of_m12 (hM : M12AutThreeFive) {M : Subgroup Q} (hH : RankTwoHypNF Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .M12) (hZM : center ↥M = ⊥) {x : Q}
    (hxM : x ∈ M) (hx5 : orderOf x = 5) {t : Q} (ht3 : ∃ k : ℕ, t ^ 3 ^ k = 1)
    (htx : t * x = x * t) : π t = 1 := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hXn : (rankTwoX (M.map π)).Normal := normalClosure_normal
  have hxX : π x ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hxM)
  obtain ⟨k, hk⟩ := ht3
  have hβ := hM ↥(rankTwoX (M.map π)) hX (MulAut.conjNormal (π t))
    ⟨k, by rw [← map_pow, ← map_pow, hk, map_one, map_one]⟩ ⟨π x, hxX⟩
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hxM, hx5])
    (Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change π t * π x * (π t)⁻¹ = π x
      rw [← map_mul, htx, map_mul, mul_inv_cancel_right]))
  have hC : π t ∈ centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun β : MulAut ↥(rankTwoX (M.map π)) => ((β ⟨y, hy⟩ :
      ↥(rankTwoX (M.map π))) : Q ⧸ O)) hβ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * π t = π t * y * (π t)⁻¹ * π t := by rw [h]
      _ = π t * y := by group
  rw [centralizer_rankTwoX_eq_bot hH, mem_bot] at hC
  exact hC

end Tools

section Levi

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {D : ClassicalModel A}
  {R T Y W L : Subgroup G} {g : G}

theorem Levi75Y.cfg76NF (hH : RankTwoHypNF G A) (hA : Hyp31 A)
    (hch : Choice74 D R T g) (hl : Levi75Y D T Y W L) (hD : D.IsLTwoFour) :
    Cfg76 A R Y L :=
  ⟨hH, hA, hch.sylowR, hch.not_le, hl.Y_le, hl.L_le, hl.a5 hD, hl.oddCenter,
    hl.standard, hl.not_normal, hl.noInv, hl.outerFree hD⟩

end Levi

end NF

theorem sp44EndgameNF_of
    (h32 : Lemma32) (h5 : Asc08Lemma310NF) (hJ : J2A4Facts) (hM : M12AutThreeFive) :
    Sp44EndgameNF := by
  intro G _ _ A R W L y s y₃ hc hsp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLA : L ≤ A := hc.L_le_A
  have hsN : s ∈ normalizer (A : Set G) := le_normalizer hsp.s_mem
  have hWA : W ≤ A := by
    rw [← hsp.conj_L, ← (rightConjugate_eq_self_iff A s).mpr hsN]
    exact map_mono hLA
  have hy₃A : y₃ ∈ A := hWA hsp.y₃_mem
  set x := s⁻¹ * y * s with hxdef
  have hxL : x ∈ L := by
    rw [← hsp.conj_W, mem_rightConjugate_iff]
    simpa [hxdef, mul_assoc] using hsp.y_mem
  have hx5 : orderOf x = 5 := by
    have := orderOf_injective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective y
    simpa [MulAut.conj_apply, hsp.orderOf_y, hxdef] using this
  have hcx : NF.Cfg76 A R (zpowers x) W := by
    have h := hc.conj hsp.s_mem
    rwa [rightConjugate_zpowers, hsp.conj_L] at h
  obtain ⟨f, hfA, ⟨k, hk⟩, hfRN, hfR⟩ : ∃ f : G, f ∈ centralizer (A : Set G) ∧
      (∃ k : ℕ, f ^ 3 ^ k = 1) ∧ f ∈ normalizer (R : Set G) ∧ f ∉ centralizer (R : Set G) := by
    have hLCy : L ≤ centralizer (zpowers y : Set G) := hc.L_le_centralizer
    obtain ⟨hHy, hZ, h60, hp, hRe, hR4, hRM, -⟩ :=
      hc.facts_at h32 hc.Y_le hLCy hc.standard hc.not_normal hc.noInv
    have hxM : (⟨x, hLCy hxL⟩ : ↥(centralizer (zpowers y : Set G))) ∈
        L.subgroupOf (centralizer (zpowers y : Set G)) := mem_subgroupOf.mpr hxL
    obtain ⟨f, hfM, hfN, ⟨k, hk⟩, hfR⟩ := NF.exists_three_of_j2A4 hJ hHy
      (hc.isSporadic_j2 h5) hRe hR4 hRM hZ hp h60 hxM (by rw [Subgroup.orderOf_mk, hx5])
    have hfL : (f : G) ∈ centralizer (L : Set G) := by
      rw [Lemma37.centralizer_subgroupOf hLCy, mem_subgroupOf] at hfM
      exact hfM
    have hfRN : (f : G) ∈ normalizer (R : Set G) := by
      rw [← subgroupOf_normalizer_eq hc.R_le_centralizer_Y] at hfN
      exact hfN
    have hfR' : (f : G) ∉ centralizer (R : Set G) := by
      intro h
      apply hfR
      rw [mem_centralizer_iff]
      intro r hr
      exact Subtype.ext (mem_centralizer_iff.mp h r (mem_subgroupOf.mp hr))
    have hk' : (f : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hfNA : (f : G) ∈ normalizer (A : Set G) := by
      have h := Lemma36.normalizer_le hc.hyp31 hc.sylowR 1
      rw [rightConjugate_one, rightConjugate_one] at h
      exact h hfRN
    have hfYL := mem_centralizer_sup f.2 hfL
    have hσ := hsp.noThree (conjAut hfNA) ⟨k, by
        rw [conjAut_pow]
        ext z
        simp [conjAut_apply, hk']⟩
      fun z hz => Subtype.ext (by
        rw [conjAut_apply, ← mem_centralizer_iff.mp hfYL z hz, mul_inv_cancel_right])
    refine ⟨f, ?_, ⟨k, hk'⟩, hfRN, hfR'⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h := congrArg (fun σ : MulAut ↥A => ((σ ⟨a, ha⟩ : ↥A) : G)) hσ
    simp only [conjAut_apply, MulAut.one_apply] at h
    calc a * f = f * a * (f : G)⁻¹ * f := by rw [h]
      _ = f * a := by group
  have hLC₃ : L ≤ centralizer (zpowers y₃ : Set G) := by
    intro l hl
    rw [mem_centralizer_zpowers_iff]
    exact mem_centralizer_iff.mp (hsp.W_le hsp.y₃_mem) l hl
  obtain ⟨hH₃, hZ₃, h60₃, hp₃, hRe₃, hR4₃, hRM₃, hRsyl₃, hno₃, ha5₃, hodd₃⟩ :=
    hc.facts_at h32 (zpowers_le.mpr hy₃A) hLC₃ hsp.standard₃ hsp.not_normal₃ hsp.noInv₃
  have hRC₃ : R ≤ centralizer (zpowers y₃ : Set G) :=
    hc.sylowR.le.trans (centralizer_le (zpowers_le.mpr hy₃A))
  have hxM₃ : (⟨x, hLC₃ hxL⟩ : ↥(centralizer (zpowers y₃ : Set G))) ∈
      L.subgroupOf (centralizer (zpowers y₃ : Set G)) := mem_subgroupOf.mpr hxL
  have hx5₃ : orderOf (⟨x, hLC₃ hxL⟩ : ↥(centralizer (zpowers y₃ : Set G))) = 5 := by
    rw [Subgroup.orderOf_mk, hx5]
  have hfC₃ : f ∈ centralizer (zpowers y₃ : Set G) := centralizer_le (zpowers_le.mpr hy₃A) hfA
  obtain ⟨e₃⟩ := ha5₃
  rcases h5 _ _ (NF.rankTwoHyp_map hH₃) standardComponentOddCore_quotient_eq_bot
      ⟨(NF.quotCenterMap hH₃).symm.trans e₃⟩ (NF.odd_card_center_map hH₃ hodd₃) _
      (NF.isSylowOf_map hH₃ hRsyl₃) (NF.not_conj_le_map hH₃ hRsyl₃.isPGroup hno₃) with hJ₃ | ⟨hM₃, -⟩
  ·
    obtain ⟨S, hSx, hS⟩ := NF.exists_five_of_j2A4 hJ hH₃ hJ₃ hRe₃ hR4₃ hRM₃ hZ₃ hp₃ h60₃ hxM₃ hx5₃
    set Cx := centralizer (zpowers x : Set G) with hCx
    set Ox : Subgroup G := (standardComponentOddCore ↥Cx).map Cx.subtype with hOx
    have hSCx : ∀ c ∈ S, (c : G) ∈ Cx := by
      intro c hc'
      have h1 := mem_centralizer_singleton_iff.mp (hSx hc')
      rw [mem_centralizer_zpowers_iff]
      exact congrArg Subtype.val h1
    have hOxN : ∀ c : G, c ∈ Cx → ∀ o ∈ Ox, c * o * c⁻¹ ∈ Ox := by
      rintro c hc' _ ⟨o, ho, rfl⟩
      exact ⟨⟨c, hc'⟩ * o * ⟨c, hc'⟩⁻¹,
        (inferInstance : (standardComponentOddCore ↥Cx).Normal).conj_mem o ho _, rfl⟩
    set N := S ⊓ Ox.comap (centralizer (zpowers y₃ : Set G)).subtype with hN
    have hSN : S ≤ normalizer (N : Set ↥(centralizer (zpowers y₃ : Set G))) := by
      intro c hc'
      refine mem_normalizer_inf (le_normalizer hc') ?_
      rw [mem_normalizer_iff]
      intro z
      simp only [mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · exact hOxN _ (hSCx c hc') _
      · intro h
        have := hOxN _ (inv_mem (hSCx c hc')) _ h
        simpa [mul_assoc] using this
    have hNodd : Odd (Nat.card N) := by
      have hle : N.map (centralizer (zpowers y₃ : Set G)).subtype ≤ Ox := by
        rintro _ ⟨z, hz, rfl⟩
        exact mem_comap.mp (mem_inf.mp hz).2
      have h1 := Subgroup.card_dvd_of_le hle
      rw [card_map_of_injective (centralizer (zpowers y₃ : Set G)).subtype_injective,
        hOx, card_map_of_injective Cx.subtype_injective] at h1
      exact (odd_card_standardComponentOddCore (G := ↥Cx)).of_dvd_nat h1
    obtain ⟨h, hhS, ⟨j, hj⟩, hhN⟩ := hS N inf_le_left hSN hNodd
    have hhOx : (h : G) ∉ Ox := fun hmem => hhN (mem_inf.mpr ⟨hhS, mem_comap.mpr hmem⟩)
    have hWCx : W ≤ Cx := hcx.L_le_centralizer
    obtain ⟨hHx, hZx, h60x, hpx, hRex, hR4x, hRMx, -⟩ :=
      hcx.facts_at h32 hcx.Y_le hWCx hcx.standard hcx.not_normal hcx.noInv
    have ht := NF.mk'_eq_one_of_j2A4 hJ hHx (hcx.isSporadic_j2 h5) hRex hR4x hRMx hZx hpx h60x
      (w := ⟨y, hWCx hsp.y_mem⟩) (mem_subgroupOf.mpr hsp.y_mem)
      (by rw [Subgroup.orderOf_mk, hsp.orderOf_y]) (z := ⟨y₃, hWCx hsp.y₃_mem⟩)
      (mem_subgroupOf.mpr hsp.y₃_mem) (by rw [Subgroup.orderOf_mk, hsp.orderOf_y₃])
      (t := ⟨(h : G), hSCx h hhS⟩) ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
      (Subtype.ext (mem_centralizer_zpowers_iff.mp h.2))
    apply hhOx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht
    exact ⟨_, ht, rfl⟩
  ·
    have ht := NF.mk'_eq_one_of_m12 hM hH₃ hM₃ hZ₃ hxM₃ hx5₃ (t := ⟨f, hfC₃⟩)
      ⟨k, Subtype.ext (by simpa using hk)⟩
      (Subtype.ext (mem_centralizer_iff.mp hfA x (hLA hxL)).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht
    apply hfR
    have hfN₃ : (⟨f, hfC₃⟩ : ↥(centralizer (zpowers y₃ : Set G))) ∈
        normalizer ((R.subgroupOf (centralizer (zpowers y₃ : Set G)) :
          Subgroup ↥(centralizer (zpowers y₃ : Set G))) :
            Set ↥(centralizer (zpowers y₃ : Set G))) := by
      rw [← subgroupOf_normalizer_eq hRC₃]
      exact hfRN
    have hc' := mem_centralizer_of_mem_oddCore (isPGroup_of_isElemAbelian hRe₃) ht hfN₃
    rw [mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc' ⟨r, hRC₃ hr⟩ (mem_subgroupOf.mpr hr))

theorem sp44Step_of (h : Sp44EndgameNF) : Sp44Step := by
  intro G _ _ A D R T Y W L g hH hA hch hl hfam hD
  obtain ⟨y, s, y₃, rfl, hsp⟩ := hl.spFour hD hfam
  exact h G A R W L y s y₃ (NF.Levi75Y.cfg76NF hH hA hch hl hD) hsp

end CFSG.ComponentClassification.RankTwoClassical
