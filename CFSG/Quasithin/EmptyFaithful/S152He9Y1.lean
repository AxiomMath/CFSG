module

public import CFSG.Quasithin.EmptyFaithful.S152He9X
public import CFSG.Quasithin.EmptyFaithful.S152He8Rank
public import CFSG.Quasithin.EmptyFaithful.S152Y02
public import CFSG.Quasithin.EmptyFaithful.S152Y03

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem no_three_elt {M V E : Subgroup G} {Y : Subgroup G}
    (hrk : CFSG.Open.pRank 3 M ≤ 2) (hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G))
    (hEM : E ≤ M) (hEV : E ≤ Subgroup.centralizer (V : Set G)) (hEab : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hYM : Y ≤ M)
    (hcent : ∀ y ∈ Y, ∀ e ∈ M ⊓ Subgroup.centralizer (V : Set G),
      y * e * y⁻¹ * e⁻¹ ∈ pCoreOf 2 M)
    {y : G} (hy : y ∈ Y) (hy3 : y ^ 3 ∈ pCoreOf 2 M)
    (hyV : y ∉ Subgroup.centralizer (V : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pCoreOf 2 M with hN
  have hNM : N ≤ M := pCoreOf_le 2 M
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pCoreOf 2 M
  let N' : Subgroup ↥M := N.subgroupOf M
  have : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  let π : ↥M →* ↥M ⧸ N' := QuotientGroup.mk' N'
  have hNp : IsPGroup 2 N := pCoreOf_isPGroup 2 M
  let EM : Subgroup ↥M := E.subgroupOf M
  let ψ : ↥EM →* ↥M ⧸ N' := π.comp EM.subtype
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : π (a : ↥M) = π (b : ↥M) := hab
    have h2 : (a : ↥M)⁻¹ * (b : ↥M) ∈ N' := by
      rw [← QuotientGroup.eq]
      exact h1
    have h3 : ((a : ↥M)⁻¹ * (b : ↥M) : ↥M) ∈ EM := EM.mul_mem (EM.inv_mem a.2) b.2
    have h4 : (((a : ↥M)⁻¹ * (b : ↥M) : ↥M) : G) ∈ N := h2
    have h5 : (((a : ↥M)⁻¹ * (b : ↥M) : ↥M) : G) ∈ E := h3
    have h6 : (((a : ↥M)⁻¹ * (b : ↥M) : ↥M) : G) = 1 := by
      obtain ⟨k, hk⟩ := hNp ⟨_, h4⟩
      have hk' : (((a : ↥M)⁻¹ * (b : ↥M) : ↥M) : G) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      exact WrH.eq_one_of_pow_two_three (a := k) (b := 1) hk' (by simpa using hEab.2 _ h5)
    have h7 : (a : ↥M)⁻¹ * (b : ↥M) = 1 := Subtype.ext h6
    exact Subtype.ext (inv_mul_eq_one.1 h7)
  let A : Subgroup (↥M ⧸ N') := ψ.range
  have hAcard : Nat.card A = 9 := by
    have h1 : Nat.card A = Nat.card ↥EM := (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have h2 : Nat.card ↥EM = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
    rw [h1, h2, hE9]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : ↥E => (z : G))
      (hEab.1.is_comm.comm (⟨((x : ↥M) : G), x.2⟩ : ↥E) ⟨((x' : ↥M) : G), x'.2⟩)
    simpa using this
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hEab.2 _ x.2
    rw [this, map_one]
  have hyM : y ∈ M := hYM hy
  let ym : ↥M := ⟨y, hyM⟩
  have hz3 : π ym ^ 3 = 1 := by
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    exact hy3
  have hzA : π ym ∉ A := by
    rintro ⟨x, hx⟩
    have hx' : (QuotientGroup.mk (s := N') (x : ↥M)) = QuotientGroup.mk ym := hx
    have h1 : ((x : ↥M)⁻¹ * ym : ↥M) ∈ N' := QuotientGroup.eq.1 hx'
    have h2 : (((x : ↥M) : G))⁻¹ * y ∈ N := h1
    have h3 : y = ((x : ↥M) : G) * ((((x : ↥M) : G))⁻¹ * y) := by group
    apply hyV
    rw [h3]
    exact Subgroup.mul_mem _ (hEV x.2) (hO2 h2)
  have hzc : ∀ a ∈ A, a * π ym = π ym * a := by
    rintro _ ⟨x, rfl⟩
    have h1 : π ym * π (x : ↥M) * (π ym)⁻¹ * (π (x : ↥M))⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      exact hcent y hy ((x : ↥M) : G) ⟨(x : ↥M).2, hEV x.2⟩
    have h2 : ψ x = π (x : ↥M) := rfl
    rw [h2]
    exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := π ym) (g₂ := π (x : ↥M))).mp
      (by simpa [commutatorElement_def] using h1)).symm
  have h3 := He8.three_le_pRank_of_central hAcomm hA3 hAcard hz3 hzA hzc
  have hnd : ¬ 3 ∣ Nat.card N' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hNp
    have : Nat.card N' = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    rw [this, hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ N')) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N' hnd, pRank_top_subtype]
    exact hrk
  omega

omit [Finite G] in
theorem exists_conjAct_ne_one_of_autOn_ne_bot {X V : Subgroup G} (hne : autOn X V ≠ ⊥) :
    ∃ x ∈ X, ∃ hx : x ∈ Subgroup.normalizer (V : Set G), conjAct V ⟨x, hx⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine eq_bot_iff.mpr fun a ha => ?_
  obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
  exact Subgroup.mem_bot.mpr (hcon x hxX hxN)

theorem false_of_card_three {M V E Y : Subgroup G}
    (hrk : CFSG.Open.pRank 3 M ≤ 2) (hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G))
    (hEM : E ≤ M) (hEV : E ≤ Subgroup.centralizer (V : Set G)) (hEab : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hYM : Y ≤ M)
    (hcent : ∀ y ∈ Y, ∀ e ∈ M ⊓ Subgroup.centralizer (V : Set G),
      y * e * y⁻¹ * e⁻¹ ∈ pCoreOf 2 M)
    (hYC : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 M)
    (hcard : Nat.card (autOn Y V) = 3) : False := by
  have hne : autOn Y V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨y, hyY, hyN, hy1⟩ := exists_conjAct_ne_one_of_autOn_ne_bot hne
  have hyV : y ∉ Subgroup.centralizer (V : Set G) := fun h =>
    hy1 (A4.conjAct_eq_one_iff.mpr h)
  have hb : conjAct V ⟨y, hyN⟩ ∈ autOn Y V := mem_autOn_iff_exists.mpr ⟨y, hyN, hyY, rfl⟩
  have hb3 : (conjAct V ⟨y, hyN⟩) ^ 3 = 1 := by
    have h1 : (⟨conjAct V ⟨y, hyN⟩, hb⟩ : ↥(autOn Y V)) ^ Nat.card ↥(autOn Y V) = 1 :=
      pow_card_eq_one'
    rw [hcard] at h1
    simpa using congrArg Subtype.val h1
  have hy3 : y ^ 3 ∈ pCoreOf 2 M := by
    have h1 : conjAct V (⟨y, hyN⟩ ^ 3) = 1 := by rw [map_pow]; exact hb3
    have h2 : (y ^ 3 : G) ∈ Subgroup.centralizer (V : Set G) := by
      have := A4.conjAct_eq_one_iff.mp h1
      simpa using this
    exact hYC ⟨Y.pow_mem hyY 3, h2⟩
  exact no_three_elt hrk hO2 hEM hEV hEab hE9 hYM hcent hyY hy3 hyV

structure YPack (T Mc M : Subgroup G) : Prop where
  card_five : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 5
  cent_le : yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M

theorem Y_pack {T Mc M : Subgroup G} (h : S152Y.Data T Mc M) (c3 : Lemma15203Concl T Mc M)
    {E : Subgroup G} (hEM : E ≤ M) (hEV : E ≤ Subgroup.centralizer (V154 T Mc M : Set G))
    (hEab : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hrk : CFSG.Open.pRank 3 M ≤ 2) :
    YPack T Mc M := by
  have hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    refine h.h1515.reduced.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M)
      fun d hd => ?_
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact Subgroup.one_mem _
  have hcent : ∀ y ∈ yOf152 T Mc M, ∀ e ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G),
      y * e * y⁻¹ * e⁻¹ ∈ pCoreOf 2 M := by
    intro y hy e he
    have := c3.centralizes (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hy) he)
    simpa [commutatorElement_def] using this
  have hYM := h.yOf_le_M
  rcases c3.cases with hi | hii | hiii
  · obtain ⟨hYb, hYC, hth⟩ := hi
    have h5 : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 5 := by
      rcases h.h1521.cases with ⟨-, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩, -⟩ | hThree | ⟨-, ⟨e⟩, -, -⟩
      · exfalso
        have := (dihedral_shape (n := 3) (by decide) e).1
        exact false_of_card_three hrk hO2 hEM hEV hEab hE9 hYM hcent hYC (by rw [hYb]; exact this)
      · exfalso
        have := (dihedral_shape (n := 3) (by decide) e).1
        exact false_of_card_three hrk hO2 hEM hEV hEab hE9 hYM hcent hYC (by rw [hYb]; exact this)
      · exfalso
        exact hth hThree (Nat.dvd_trans (by norm_num : 3 ∣ 9)
          (hE9 ▸ Subgroup.card_dvd_of_le (le_inf hEM hEV)))
      · have := (dihedral_shape (n := 5) (by decide) e).1
        rw [hYb]
        exact this
    exact ⟨h5, hYC⟩
  · exfalso
    obtain ⟨-, -, -, -, -, hP, -⟩ := hii
    obtain ⟨y, hyY, hyN, hy1⟩ := exists_conjAct_ne_one_of_autOn_ne_bot c3.ne_bot
    have hyV : y ∉ Subgroup.centralizer (V154 T Mc M : Set G) := fun h' =>
      hy1 (A4.conjAct_eq_one_iff.mpr h')
    have hyM : y ∈ M := hYM hyY
    have hmem : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M) ⟨y, hyM⟩ : OTwoQuot M) ∈
        imageOTwoQuot M (yOf152 T Mc M) := ⟨⟨y, hyM⟩, hyY, rfl⟩
    have h3 : (⟨_, hmem⟩ : ↥(imageOTwoQuot M (yOf152 T Mc M))) ^ 3 = 1 := hP.2.2 ⟨_, hmem⟩
    have h3' : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M) ⟨y, hyM⟩) ^ 3 = 1 :=
      congrArg Subtype.val h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3'
    exact no_three_elt hrk hO2 hEM hEV hEab hE9 hYM hcent hyY ⟨_, h3', rfl⟩ hyV
  · exfalso
    obtain ⟨-, -, -, hcard3, hYC, -⟩ := hiii
    exact false_of_card_three hrk hO2 hEM hEV hEab hE9 hYM hcent hYC hcard3

end CFSG.Quasithin.He9
