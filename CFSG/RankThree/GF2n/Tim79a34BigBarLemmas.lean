module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

theorem bar_mem_of_sq_eq_one {Mb : Type} [Group Mb] {B K : Subgroup Mb}
    (hKN : K ≤ Subgroup.normalizer (B : Set Mb)) (hK : Odd (Nat.card K))
    {c : Mb} (hc : c ∈ B ⊔ K) (hc2 : c ^ 2 = 1) : c ∈ B := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left B K hKN
  rw [← SetLike.mem_coe, hmul] at hc
  obtain ⟨b, hb, k, hk, rfl⟩ := hc
  have hb2 : k * b * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKN hk) b).mp hb
  have hk2 : k ^ 2 = (b * (k * b * k⁻¹))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    calc b * (k * b * k⁻¹) * k ^ 2 = (b * k) ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := hc2
  have hk2B : k ^ 2 ∈ B := by
    rw [hk2]
    exact B.inv_mem (B.mul_mem hb hb2)
  obtain ⟨t, ht⟩ := hK
  have hkm : k ^ Nat.card K = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hk)
  have hkt : (k ^ 2) ^ t * k = 1 := by
    rw [← pow_mul, ← pow_succ, ← ht, hkm]
  have hkB : k ∈ B := by
    have := eq_inv_of_mul_eq_one_right hkt
    rw [this]
    exact B.inv_mem (B.pow_mem hk2B t)
  exact B.mul_mem hb hkB

theorem bar_exists_involution {Mb : Type} [Group Mb] [Finite Mb] {H : Subgroup Mb}
    (hH : Even (Nat.card H)) : ∃ t ∈ H, t ^ 2 = 1 ∧ t ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.mp hH)
  have h1 : orderOf (x : Mb) = 2 := (Subgroup.orderOf_coe x).trans hx
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [← h1]
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at h1
    omega

theorem bar_mem_normalizer_of_isTI {Mb : Type} [Group Mb] [Finite Mb] {B : Subgroup Mb}
    (hTI : IsTI B) {g t : Mb} (ht : t ∈ B) (htg : t ∈ conjSubgroup g B) (ht1 : t ≠ 1) :
    g ∈ Subgroup.normalizer (B : Set Mb) := by
  rcases hTI g with h | h
  · have hmem : t ∈ B ⊓ conjSubgroup g B := ⟨ht, htg⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact absurd hmem ht1
  · have hle : B ≤ conjSubgroup g B := inf_eq_left.mp h
    have hcard : Nat.card (conjSubgroup g B) = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have heq : B = conjSubgroup g B := Subgroup.eq_of_le_of_card_ge hle hcard.le
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    exact (Subgroup.ext_iff.mp heq x).trans mem_conjSubgroup

theorem bar_normalizer_le {Mb : Type} [Group Mb] {C B : Subgroup Mb} (hBC : B ≤ C)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (h2 : ∀ c ∈ C, c ^ 2 = 1 → c ∈ B) :
    Subgroup.normalizer (C : Set Mb) ≤ Subgroup.normalizer (B : Set Mb) := by
  have key : ∀ g ∈ Subgroup.normalizer (C : Set Mb), ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hg b hb
    refine h2 _ ((Subgroup.mem_normalizer_iff.mp hg b).mp (hBC hb)) ?_
    rw [conj_pow, hB2 b hb]
    simp
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key g hg b, fun hb => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hb
  simpa [mul_assoc] using this

theorem bar_normalizer_le_normalizer_centralizer {Mb : Type} [Group Mb] (R : Subgroup Mb) :
    Subgroup.normalizer (R : Set Mb) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set Mb) : Set Mb) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set Mb), ∀ h ∈ Subgroup.centralizer (R : Set Mb),
      g * h * g⁻¹ ∈ Subgroup.centralizer (R : Set Mb) := by
    intro g hg h hh
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ R := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    have hcomm := (Subgroup.mem_centralizer_iff.mp hh) _ hx'
    calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = g * h * g⁻¹ * x := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem bar_odd_card_inf_conj {Mb : Type} [Group Mb] [Finite Mb] {C B : Subgroup Mb}
    (hTI : IsTI B) (h2 : ∀ c ∈ C, c ^ 2 = 1 → c ∈ B)
    (hNB : Subgroup.normalizer (B : Set Mb) ≤ Subgroup.normalizer (C : Set Mb)) {g : Mb}
    (hg : g ∉ Subgroup.normalizer (C : Set Mb)) :
    Odd (Nat.card ↥(C ⊓ conjSubgroup g C)) := by
  by_contra hodd
  obtain ⟨t, htm, ht2, ht1⟩ := bar_exists_involution (Nat.not_odd_iff_even.mp hodd)
  have htC : t ∈ C := htm.1
  have htg : t ∈ conjSubgroup g C := htm.2
  have htB : t ∈ B := h2 t htC ht2
  have hcB : g⁻¹ * t * g ∈ B := by
    refine h2 _ (mem_conjSubgroup.mp htg) ?_
    calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * (t * t) * g := by rw [pow_two]; group
      _ = 1 := by rw [← pow_two, ht2]; group
  exact hg (hNB (bar_mem_normalizer_of_isTI hTI htB (mem_conjSubgroup.mpr hcB) ht1))

theorem bar_isQuasisimple {G : Type*} [Group G] [IsSimpleGroup G] (hG : ¬ IsMulCommutative G) :
    CFSG.Open.IsQuasisimple G := by
  have hcomm : commutator G = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator G) with h | h
    · exact absurd ((commutator_eq_bot_iff G).mp h) hG
    · exact h
  have hcenter : Subgroup.center G = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hG
  refine And.intro hcomm ?_
  exact ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).isSimpleGroup

theorem bar_commutator_ne_bot {Mb : Type} [Group Mb] [Finite Mb] {R B : Subgroup Mb}
    (hRs : IsSimpleGroup R) (hRn : ¬ IsMulCommutative R) (hRe : Even (Nat.card R))
    (hBc : IsMulCommutative B)
    (hCN : Subgroup.centralizer (R : Set Mb) ≤ Subgroup.normalizer (B : Set Mb))
    (h2 : ∀ c ∈ Subgroup.centralizer (R : Set Mb), c ^ 2 = 1 → c ∈ B) (g : Mb) :
    ⁅R, conjSubgroup g R⁆ ≠ ⊥ := by
  intro h
  have hle : conjSubgroup g R ≤ Subgroup.centralizer (R : Set Mb) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h
  let e : R ≃* conjSubgroup g R :=
    Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  haveI := hRs
  haveI := hBc
  haveI : IsSimpleGroup (conjSubgroup g R) := e.symm.isSimpleGroup
  have hcard : Nat.card (conjSubgroup g R) = Nat.card R := (Nat.card_congr e.toEquiv).symm
  obtain ⟨t, htR, ht2, ht1⟩ := bar_exists_involution (hcard ▸ hRe)
  have htB : t ∈ B := h2 t (hle htR) ht2
  have hnormal : ((conjSubgroup g R ⊓ B).subgroupOf (conjSubgroup g R)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    rintro x k ⟨hx1, hx2⟩ hk
    exact ⟨(conjSubgroup g R).mul_mem ((conjSubgroup g R).mul_mem hk hx1)
        ((conjSubgroup g R).inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (hCN (hle hk)) x).mp hx2⟩
  rcases (Subgroup.isSimpleGroup_iff.mp inferInstance).2 (conjSubgroup g R ⊓ B) inf_le_left
    hnormal with hbot | htop
  · have hmem : t ∈ conjSubgroup g R ⊓ B := ⟨htR, htB⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  · have hRB : conjSubgroup g R ≤ B := inf_eq_left.mp htop
    apply hRn
    refine IsMulCommutative.of_comm fun x y => ?_
    have hmem : ∀ z : R, g * (z : Mb) * g⁻¹ ∈ conjSubgroup g R := fun z =>
      mem_conjSubgroup.mpr (by
        have : g⁻¹ * (g * (z : Mb) * g⁻¹) * g = z := by group
        rw [this]
        exact z.2)
    have hxy := setLike_mul_comm (hRB (hmem x)) (hRB (hmem y))
    apply Subtype.ext
    have : g * ((x : Mb) * y) * g⁻¹ = g * ((y : Mb) * x) * g⁻¹ := by
      calc g * ((x : Mb) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hxy
        _ = g * ((y : Mb) * x) * g⁻¹ := by group
    simpa using this

theorem bar_exists_card_pow {Mb : Type} [Group Mb] [Finite Mb] {B : Subgroup Mb}
    (hBe : IsElemAbelian 2 B) (hB4 : 4 ≤ Nat.card B) :
    ∃ k : ℕ, 2 ≤ k ∧ Nat.card B = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  refine ⟨k, ?_, hk⟩
  by_contra hlt
  have hk1 : k ≤ 1 := by omega
  have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
  omega

theorem standardComponent_of_bar {Mb : Type} [Group Mb] [Finite Mb] (R B : Subgroup Mb)
    (hRs : IsSimpleGroup R) (hRn : ¬ IsMulCommutative R) (hRe : Even (Nat.card R))
    (hBe : IsElemAbelian 2 B) (hB4 : 4 ≤ Nat.card B)
    (hBR : B ≤ Subgroup.centralizer (R : Set Mb)) (hTI : IsTI B)
    (hN : Subgroup.normalizer (R : Set Mb) = Subgroup.normalizer (B : Set Mb))
    (hK : ∃ K : Subgroup Mb, Odd (Nat.card K) ∧
      Subgroup.centralizer (R : Set Mb) = B ⊔ K) :
    standardComponentIsStandard R := by
  obtain ⟨K, hKo, hKC⟩ := hK
  have hCN : Subgroup.centralizer (R : Set Mb) ≤ Subgroup.normalizer (B : Set Mb) :=
    (Subgroup.centralizer_le_normalizer _).trans hN.le
  have hKN : K ≤ Subgroup.normalizer (B : Set Mb) :=
    (le_sup_right : K ≤ B ⊔ K).trans (hKC.symm.le.trans hCN)
  have h2 : ∀ c ∈ Subgroup.centralizer (R : Set Mb), c ^ 2 = 1 → c ∈ B := fun c hc hc2 =>
    bar_mem_of_sq_eq_one hKN hKo (hKC.le hc) hc2
  have hNB : Subgroup.normalizer (B : Set Mb) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set Mb) : Set Mb) :=
    hN.symm.le.trans (bar_normalizer_le_normalizer_centralizer R)
  have hNC : Subgroup.normalizer (Subgroup.centralizer (R : Set Mb) : Set Mb) =
      Subgroup.normalizer (R : Set Mb) :=
    le_antisymm ((bar_normalizer_le hBR hBe.2 h2).trans hN.symm.le)
      (bar_normalizer_le_normalizer_centralizer R)
  have hEven : Even (Nat.card ↥(Subgroup.centralizer (R : Set Mb))) := by
    obtain ⟨k, hk2, hk⟩ := bar_exists_card_pow hBe hB4
    have hdvd : Nat.card B ∣ Nat.card (Subgroup.centralizer (R : Set Mb)) :=
      Subgroup.card_dvd_of_le hBR
    rw [even_iff_two_dvd]
    refine dvd_trans ?_ hdvd
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  haveI := hRs
  refine And.intro (bar_isQuasisimple hRn) (And.intro hEven (And.intro ?_ (And.intro hNC ?_)))
  · intro g hg
    exact bar_odd_card_inf_conj hTI h2 hNB hg
  · intro g
    exact bar_commutator_ne_bot hRs hRn hRe hBe.1 hCN h2 g

theorem two_le_pRank_centralizer_of_bar {Mb : Type} [Group Mb] [Finite Mb] (R B : Subgroup Mb)
    (hBe : IsElemAbelian 2 B) (hB4 : 4 ≤ Nat.card B)
    (hBR : B ≤ Subgroup.centralizer (R : Set Mb)) :
    2 ≤ pRank 2 (Subgroup.centralizer (R : Set Mb)) := by
  obtain ⟨k, hk2, hk⟩ := bar_exists_card_pow hBe hB4
  have hbdd : BddAbove {j : ℕ | ∃ E : Subgroup Mb, E ≤ Subgroup.centralizer (R : Set Mb) ∧
      IsElemAbelian 2 E ∧ Nat.card E = 2 ^ j} := by
    refine ⟨Nat.card Mb, ?_⟩
    rintro j ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card Mb := Subgroup.card_le_card_group E
    have h2 : j < 2 ^ j := Nat.lt_two_pow_self
    omega
  exact hk2.trans (le_csSup hbdd ⟨B, hBR, hBe, hk⟩)

end CFSG.RankThree.GF2n.Tim79a
