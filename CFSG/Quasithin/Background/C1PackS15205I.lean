module

public import CFSG.Quasithin.Background.A1cA132Struct
public import CFSG.Quasithin.Background.C1PackS15205E
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Eigen

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

theorem Ys_abelian_of_eigen' (h : S152Y.Data T Mc M)
    (hYE : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M))
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    {ρ e₁ e₂ : MulAut (V154 T Mc M)} {r : OTwoQuot M} (hrρ : S152Y.piStar h r = ρ)
    (hrN : r ∈ Subgroup.normalizer (S152Y.Ys T Mc M : Set (OTwoQuot M)))
    (hrK : ∀ k ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker, r * k = k * r)
    (he₁ : e₁ ∈ oTwoUpper (mBar0 T Mc M)) (he₂ : e₂ ∈ oTwoUpper (mBar0 T Mc M))
    (hgen : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∃ i j : ℕ, a = e₁ ^ i * e₂ ^ j)
    (h₁ : ρ * e₁ * ρ⁻¹ = e₁) (h₂ : ρ * e₂ * ρ⁻¹ = e₂⁻¹) :
    ∀ a ∈ S152Y.Ys T Mc M, ∀ b ∈ S152Y.Ys T Mc M, a * b = b * a := by
  have hKc := S152Y.K_central_Ys h
  have hmapY : (S152Y.Ys T Mc M).map (S152Y.piStar h) = oTwoUpper (mBar0 T Mc M) := by
    rw [S152Y.Data.map_Ys h, hYE]
  obtain ⟨y₁, hy₁, hπ₁⟩ := Subgroup.mem_map.mp (hmapY ▸ he₁)
  obtain ⟨y₂, hy₂, hπ₂⟩ := Subgroup.mem_map.mp (hmapY ▸ he₂)
  have hconj : ∀ y ∈ S152Y.Ys T Mc M, r * y * r⁻¹ ∈ S152Y.Ys T Mc M := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hrN y).mp hy
  have hk₁ : y₁⁻¹ * (r * y₁ * r⁻¹) ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker := by
    refine ⟨(S152Y.Ys T Mc M).mul_mem ((S152Y.Ys T Mc M).inv_mem hy₁) (hconj y₁ hy₁), ?_⟩
    refine MonoidHom.mem_ker.mpr ?_
    simp only [map_mul, map_inv, hπ₁, hrρ, h₁, inv_mul_cancel]
  have hk₂ : y₂ * (r * y₂ * r⁻¹) ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker := by
    refine ⟨(S152Y.Ys T Mc M).mul_mem hy₂ (hconj y₂ hy₂), ?_⟩
    refine MonoidHom.mem_ker.mpr ?_
    simp only [map_mul, map_inv, hπ₂, hrρ, h₂, mul_inv_cancel]
  set k₁ := y₁⁻¹ * (r * y₁ * r⁻¹) with hk₁def
  set k₂ := y₂ * (r * y₂ * r⁻¹) with hk₂def
  have e₁' : r * y₁ * r⁻¹ = y₁ * k₁ := by rw [hk₁def]; group
  have e₂' : r * y₂ * r⁻¹ = y₂⁻¹ * k₂ := by rw [hk₂def]; group
  have hcY : ⁅y₁, y₂⁆ ∈ S152Y.Ys T Mc M :=
    (S152Y.Ys T Mc M).mul_mem ((S152Y.Ys T Mc M).mul_mem ((S152Y.Ys T Mc M).mul_mem hy₁ hy₂)
      ((S152Y.Ys T Mc M).inv_mem hy₁)) ((S152Y.Ys T Mc M).inv_mem hy₂)
  have hcK : ⁅y₁, y₂⁆ ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker := by
    refine ⟨hcY, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_commutatorElement, hπ₁, hπ₂]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hEab _ he₁ _ he₂)
  have hrc : r * ⁅y₁, y₂⁆ * r⁻¹ = ⁅y₁, y₂⁆ := by
    rw [hrK _ hcK]; group
  have hconjc : r * ⁅y₁, y₂⁆ * r⁻¹ = ⁅r * y₁ * r⁻¹, r * y₂ * r⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hy₁k₁ : y₁ * k₁ ∈ S152Y.Ys T Mc M := (S152Y.Ys T Mc M).mul_mem hy₁ hk₁.1
  have hstep : ⁅r * y₁ * r⁻¹, r * y₂ * r⁻¹⁆ = ⁅y₁, y₂⁻¹⁆ := by
    rw [e₁', e₂', commutator_mul_central_right (hKc k₂ hk₂ _ hy₁k₁).symm,
      commutator_mul_central_left (hKc k₁ hk₁ _ ((S152Y.Ys T Mc M).inv_mem hy₂)).symm]
  have hinvc : ⁅y₁, y₂⁻¹⁆ = ⁅y₁, y₂⁆⁻¹ := by
    have e : ⁅y₁, y₂⁻¹⁆ = y₂⁻¹ * ⁅y₁, y₂⁆⁻¹ * y₂ := by
      simp only [commutatorElement_def]; group
    have hcy : y₂⁻¹ * ⁅y₁, y₂⁆ * y₂ = ⁅y₁, y₂⁆ := by
      rw [mul_assoc, ← hKc _ hcK y₂ hy₂, inv_mul_cancel_left]
    have : y₂⁻¹ * ⁅y₁, y₂⁆⁻¹ * y₂ = (y₂⁻¹ * ⁅y₁, y₂⁆ * y₂)⁻¹ := by group
    rw [e, this, hcy]
  have hcc : ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆⁻¹ := hrc.symm.trans (hconjc.trans (hstep.trans hinvc))
  have hc2 : ⁅y₁, y₂⁆ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    calc ⁅y₁, y₂⁆ * ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆ * ⁅y₁, y₂⁆⁻¹ := by rw [← hcc]
      _ = 1 := mul_inv_cancel _
  have hc1 : ⁅y₁, y₂⁆ = 1 :=
    eq_one_of_odd_of_two_power (S152Y.Data.Ys_inf_ker_odd h _ hcK) hc2
  have hcomm12 : Commute y₁ y₂ := commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hdecomp : ∀ a ∈ S152Y.Ys T Mc M, ∃ k ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar h).ker,
      ∃ i j : ℕ, a = k * (y₁ ^ i * y₂ ^ j) := by
    intro a ha
    obtain ⟨i, j, hij⟩ := hgen _ (S152Y.Data.piStar_mem_of_mem_Ys h ha)
    refine ⟨a * (y₁ ^ i * y₂ ^ j)⁻¹, ⟨(S152Y.Ys T Mc M).mul_mem ha
      ((S152Y.Ys T Mc M).inv_mem ((S152Y.Ys T Mc M).mul_mem ((S152Y.Ys T Mc M).pow_mem hy₁ i)
        ((S152Y.Ys T Mc M).pow_mem hy₂ j))), ?_⟩, i, j, (inv_mul_cancel_right a _).symm⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hπ₁, hπ₂, ← hij, mul_inv_cancel]
  intro a ha b hb
  obtain ⟨ka, hka, i, j, rfl⟩ := hdecomp a ha
  obtain ⟨kb, hkb, i', j', rfl⟩ := hdecomp b hb
  have hpow : ∀ i j : ℕ, y₁ ^ i * y₂ ^ j ∈ S152Y.Ys T Mc M := fun i j =>
    (S152Y.Ys T Mc M).mul_mem ((S152Y.Ys T Mc M).pow_mem hy₁ i)
      ((S152Y.Ys T Mc M).pow_mem hy₂ j)
  have h5 : Commute (y₁ ^ i * y₂ ^ j) (y₁ ^ i' * y₂ ^ j') :=
    Commute.mul_left
      (Commute.mul_right ((Commute.refl y₁).pow_pow i i') (hcomm12.pow_pow i j'))
      (Commute.mul_right (hcomm12.symm.pow_pow j i') ((Commute.refl y₂).pow_pow j j'))
  have hkab : ka * kb = kb * ka := hKc kb hkb ka hka.1
  have hkb' : (y₁ ^ i * y₂ ^ j) * kb = kb * (y₁ ^ i * y₂ ^ j) := hKc kb hkb _ (hpow i j)
  have hka' : (y₁ ^ i' * y₂ ^ j') * ka = ka * (y₁ ^ i' * y₂ ^ j') := hKc ka hka _ (hpow i' j')
  generalize y₁ ^ i * y₂ ^ j = A at h5 hkb' ⊢
  generalize y₁ ^ i' * y₂ ^ j' = B at h5 hka' ⊢
  calc ka * A * (kb * B) = ka * (A * kb) * B := by group
    _ = ka * (kb * A) * B := by rw [hkb']
    _ = (ka * kb) * (A * B) := by group
    _ = (kb * ka) * (B * A) := by rw [hkab, h5.eq]
    _ = kb * (ka * B) * A := by group
    _ = kb * (B * ka) * A := by rw [hka']
    _ = kb * B * (ka * A) := by group

end Eigen

section CaseII

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

theorem Ctr5.Rbar_centralizes_Q (c : Ctr5 T Mc M M₁) {Q : Subgroup (MulAut (V154 T Mc M))}
    (hQ : QD5 T Mc M M₁ Q) :
    ∀ ρ ∈ autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M), ∀ q ∈ Q, ρ * q = q * ρ := by
  have hd := c.std.data
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hR2 : IsPGroup 2 (autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M)) :=
    isPGroup_autOn' (pCoreOf_isPGroup 2 _) (hRM.trans hd.hMV)
  intro ρ hρ q hq
  have hHN : autOn (M₁ ⊓ M) (V154 T Mc M) ≤
      Subgroup.normalizer (autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M) : Set (MulAut (V154 T Mc M))) :=
    autOn_le_normalizer_autOn (inf_le_right.trans hd.hMV) (hRM.trans hd.hMV)
      (le_normalizer_pCoreOf 2 (M₁ ⊓ M))
  have hconj : q * ρ⁻¹ * q⁻¹ ∈ autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M) :=
    (Subgroup.mem_normalizer_iff.mp (hHN (hQ.le_Hb hq)) ρ⁻¹).mp (Subgroup.inv_mem _ hρ)
  have hρM : ρ ∈ autOn M (V154 T Mc M) := A4.autOn_mono hRM hρ
  have h1 : ρ * q * ρ⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQ.norm ρ hρM q hq) (Q.inv_mem hq)
  have h2 : ρ * q * ρ⁻¹ * q⁻¹ ∈ autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M) := by
    have e : ρ * q * ρ⁻¹ * q⁻¹ = ρ * (q * ρ⁻¹ * q⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hρ hconj
  have h3 : ρ * q * ρ⁻¹ * q⁻¹ = 1 := by
    have hm : ρ * q * ρ⁻¹ * q⁻¹ ∈ autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M) ⊓ Q := ⟨h2, h1⟩
    rw [inf_eq_bot_of_two_group_card_three hR2 hQ.card, Subgroup.mem_bot] at hm
    exact hm
  calc ρ * q = (ρ * q * ρ⁻¹ * q⁻¹) * (q * ρ) := by group
    _ = q * ρ := by rw [h3, one_mul]

theorem Ctr5.not_case_ii (h113 : StageLemma14113) (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁)
    (hV : V154 T Mc M = VZ T M) {Q : Subgroup (MulAut (V154 T Mc M))} (hQ : QD5 T Mc M M₁ Q) :
    ¬ Case15203ii T Mc M := by
  intro hii
  have hd := c.std.data
  have c3 := c.std.c1523
  have h3 := c.case_three
  obtain ⟨-, hA, -⟩ := id h3
  have sh : OmShape (mBar0 T Mc M) := S152Y.omShape_mBar0 hOm h3
  obtain ⟨-, -, -, hOO, hOY, hP, -⟩ := hii
  have hYE : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) := by
    rw [← hOY, ← hOO]
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hR2 : IsPGroup 2 (autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M)) :=
    isPGroup_autOn' (pCoreOf_isPGroup 2 _) (hRM.trans hd.hMV)
  obtain ⟨⟨ρ, hρR⟩, hρ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (c.Rbar_ne_bot h113)
  have hρM : ρ ∈ mBar0 T Mc M := by
    rw [← hA]
    exact A4.autOn_mono hRM hρR
  have hρ2 : ρ * ρ = 1 := by
    obtain ⟨k, hk⟩ := hR2 ⟨ρ, hρR⟩
    exact sh.two_elements ρ hρM ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hρne : ρ ≠ 1 := fun h => hρ1 (Subtype.ext h)
  have hnotinv : ¬ ∀ a ∈ oTwoUpper (mBar0 T Mc M), ρ * a * ρ⁻¹ = a⁻¹ := by
    intro hinv
    have hQne : Q ≠ ⊥ := fun h => by
      have hc := hQ.card
      rw [h, Subgroup.card_bot] at hc
      omega
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
    have hqO : (q : MulAut (V154 T Mc M)) ∈ oTwoUpper (mBar0 T Mc M) := hQ.le_P q.2
    have hcomm := c.Rbar_centralizes_Q hQ ρ hρR q q.2
    have h1 : ρ * q * ρ⁻¹ = q := by rw [hcomm]; group
    have h2 : (q : MulAut (V154 T Mc M)) = (q : MulAut (V154 T Mc M))⁻¹ := by
      rw [← hinv _ hqO, h1]
    have h3q : (q : MulAut (V154 T Mc M)) ^ 3 = 1 := sh.exp_O _ hqO
    set u : MulAut (V154 T Mc M) := (q : MulAut (V154 T Mc M)) with hu
    have h4 : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel _
    have h5 : u = 1 := by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [h3q, h4]; group
    exact hq1 (Subtype.ext h5)
  obtain ⟨e₁, he₁, e₂, he₂, -, -, h₁, h₂, hgen⟩ :=
    (sh.inv_or_eigen ρ hρM hρ2 hρne).resolve_left hnotinv
  have hdata : S152Y.Data T Mc M := hd
  have hρmem : ρ ∈ (imageOTwoQuot M (pCoreOf 2 (M₁ ⊓ M))).map (S152Y.piStar hdata) := by
    rw [S152Y.map_piStar_imageOTwoQuot hdata hRM]
    exact hρR
  obtain ⟨r, hrR, hrρ⟩ := Subgroup.mem_map.mp hρmem
  have hrM : r ∈ imageOTwoQuot M M := imageOTwoQuot_mono hRM hrR
  have hrN : r ∈ Subgroup.normalizer (S152Y.Ys T Mc M : Set (OTwoQuot M)) :=
    S152Y.imageOTwoQuot_le_normalizer (M := M) c3.normal hrM
  have hcomm0 := (lemma_14_1_17_three c.qtfe c.hyp_VZ (bot_le : (⊥ : Subgroup G) ≤ M)).1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm0
  have hrK : ∀ k ∈ S152Y.Ys T Mc M ⊓ (S152Y.piStar hdata).ker, r * k = k * r := by
    intro k hk
    have hk0 : k ∈ imageOTwoQuot M
        (yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
      rw [S152Y.imageOTwoQuot_inf_centralizer hdata]
      exact hk
    have hk' : k ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
      imageOTwoQuot_mono (inf_le_inf_right _ hd.yOf_le_M) hk0
    rw [hV] at hk'
    exact Subgroup.mem_centralizer_iff.mp (hcomm0 hk') r (Subgroup.mem_sup_right hrR)
  have hab := Ys_abelian_of_eigen' hdata hYE sh.comm_O hrρ hrN hrK he₁ he₂ hgen h₁ h₂
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hne⟩ := A1c.exists_not_commute_of_isPOnePlusTwo hP
  exact hne (Subtype.ext (hab a a.2 b b.2))

end CaseII

section Sylow

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

omit [Finite G] in
theorem eq_one_of_isPGroup_three_of_isThreePrime {P C : Subgroup G} (hP : IsPGroup 3 P)
    (hC : IsThreePrimeGroup C) {x : G} (hxP : x ∈ P) (hxC : x ∈ C) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨x, hxC⟩ : ↥C)
    rwa [Subgroup.orderOf_mk] at this
  by_contra hne
  have hord : orderOf x ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hj0 : j ≠ 0 := fun h0 => hord (by rw [hjo, h0]; rfl)
  have h3 : 3 ∣ orderOf x := by
    rw [hjo]
    exact dvd_pow_self 3 hj0
  exact hC (h3.trans h2)

theorem Ctr5.sylow_abelian (h113 : StageLemma14113) (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁)
    (hV : V154 T Mc M = VZ T M) {Q : Subgroup (MulAut (V154 T Mc M))} (hQ : QD5 T Mc M M₁ Q)
    {P : Subgroup G} (hP : IsSylowIn 3 P M) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have hd := c.std.data
  rcases c.std.c1523.cases with hi | hii | hiii
  ·
    have hC3 := hi.2.2 c.case_three
    have h3 := c.case_three
    obtain ⟨-, hA, -⟩ := id h3
    have sh : OmShape (mBar0 T Mc M) := S152Y.omShape_mBar0 hOm h3
    have hO : ∀ (x : G) (hx : x ∈ P), conjAct (V154 T Mc M) ⟨x, hd.hMV (hP.1 hx)⟩ ∈
        oTwoUpper (mBar0 T Mc M) := by
      intro x hx
      have hmem : conjAct (V154 T Mc M) ⟨x, hd.hMV (hP.1 hx)⟩ ∈ mBar0 T Mc M := by
        rw [← hA]
        exact mem_autOn_iff_exists.mpr ⟨x, hd.hMV (hP.1 hx), hP.1 hx, rfl⟩
      refine mem_oTwoUpper_of_odd hmem ?_
      obtain ⟨k, hk⟩ := hP.2.1 ⟨x, hx⟩
      have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h2 : orderOf (conjAct (V154 T Mc M) ⟨x, hd.hMV (hP.1 hx)⟩) ∣ orderOf x := by
        have := orderOf_map_dvd (conjAct (V154 T Mc M))
          (⟨x, hd.hMV (hP.1 hx)⟩ : Subgroup.normalizer (V154 T Mc M : Set G))
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat (Odd.of_dvd_nat (Odd.pow (by decide)) h1) h2
    intro a ha b hb
    have haN : a ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hd.hMV (hP.1 ha)
    have hbN : b ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hd.hMV (hP.1 hb)
    have hxP : a * b * a⁻¹ * b⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hxN : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
      hd.hMV (hP.1 hxP)
    have h1 : conjAct (V154 T Mc M) ⟨a * b * a⁻¹ * b⁻¹, hxN⟩ = 1 := by
      have e : (⟨a * b * a⁻¹ * b⁻¹, hxN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
          ⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcomm := sh.comm_O _ (hO a ha) _ (hO b hb)
      calc conjAct (V154 T Mc M) ⟨a, haN⟩ * conjAct (V154 T Mc M) ⟨b, hbN⟩ *
            (conjAct (V154 T Mc M) ⟨a, haN⟩)⁻¹ * (conjAct (V154 T Mc M) ⟨b, hbN⟩)⁻¹
          = (conjAct (V154 T Mc M) ⟨b, hbN⟩ * conjAct (V154 T Mc M) ⟨a, haN⟩) *
            (conjAct (V154 T Mc M) ⟨a, haN⟩)⁻¹ * (conjAct (V154 T Mc M) ⟨b, hbN⟩)⁻¹ := by
            rw [hcomm]
        _ = 1 := by group
    have hxC : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
      A4.conjAct_eq_one_iff.mp h1
    have hx1 := eq_one_of_isPGroup_three_of_isThreePrime hP.2.1 hC3 hxP
      (show a * b * a⁻¹ * b⁻¹ ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) from
        ⟨hP.1 hxP, hxC⟩)
    exact commutatorElement_eq_one_iff_mul_comm.mp hx1
  · exact absurd hii (c.not_case_ii h113 hOm hV hQ)
  ·
    obtain ⟨-, -, -, -, -, n, -, hn⟩ := hiii
    obtain ⟨e⟩ := hn P hP
    intro a ha b hb
    have : (⟨a, ha⟩ : ↥P) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val this

end Sylow

end C1Pack5

end CFSG.Quasithin
