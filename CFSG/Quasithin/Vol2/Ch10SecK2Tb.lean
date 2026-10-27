module

public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Quasithin.Vol2.Ch10SecKIK2g

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

section NotTwo

variable {X : Type*} [Group X] [Finite X]

theorem not_isPGroup_of_three_dvd (h3 : 3 ∣ Nat.card X) : ¬ IsPGroup 2 X := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
  rw [hk] at h3
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem three_dvd_sq_sub_one {n : ℕ} : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 n

theorem three_dvd_card_statedSL_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 3 ∣ Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K) := by
  rw [card_statedSL_two1527d, hK]
  exact Dvd.dvd.mul_left three_dvd_sq_sub_one _

theorem three_dvd_card_statedSL_three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 3 ∣ Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 K) := by
  rw [card_statedSL_three1527d, hK]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right three_dvd_sq_sub_one _) _

end NotTwo

section TwoPow

variable {Γ : Type} [Group Γ] {H J V : Subgroup Γ}

theorem two_pow_mem_autOn (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) :
    ∀ x ∈ autOn H V, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn J V := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : (g : Γ) ∈ H := Subgroup.mem_subgroupOf.mp hg
  obtain ⟨e, he⟩ := h2 _ hg'
  refine ⟨e, ⟨g ^ 2 ^ e, ?_, (map_pow _ _ _)⟩⟩
  show g ^ 2 ^ e ∈ J.subgroupOf (Subgroup.normalizer (V : Set Γ))
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  exact he

theorem isPGroup_of_inf_eq_bot (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J)
    {X : Subgroup (MulAut ↥V)} (hX : X ≤ autOn H V) (hXJ : X ⊓ autOn J V = ⊥) : IsPGroup 2 ↥X := by
  intro x
  obtain ⟨e, he⟩ := two_pow_mem_autOn h2 x (hX x.2)
  refine ⟨e, Subtype.ext ?_⟩
  have hmem : (x : MulAut ↥V) ^ 2 ^ e ∈ X ⊓ autOn J V := ⟨X.pow_mem x.2 _, he⟩
  rw [hXJ, Subgroup.mem_bot] at hmem
  rw [Subgroup.coe_pow, hmem, Subgroup.coe_one]

end TwoPow

section Faithful

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {W : Type*} [CommGroup W]
  {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)} {U Z : Subgroup W}
  {π : ↥Γ₀ →* ↥H}

theorem injective_of_realizesVia_nat (h : (FFModel.nat Γ₀).RealizesVia H U Z π) :
    Function.Injective π := by
  obtain ⟨f, -, -, hfs, hfa⟩ := KGNat.exists_coord (KGNat.linModelNat Γ₀) h
  intro γ γ' hγ
  have hlin : ∀ x, ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x =
      ((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x := by
    intro x
    obtain ⟨u, hu, rfl⟩ := hfs x
    have h1 : f (((π γ : ↥H) : MulAut W) u) =
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f u :=
      (hfa γ u hu).trans (KGNat.linModelNat_lin _ _ _)
    have h2 : f (((π γ' : ↥H) : MulAut W) u) =
        ((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f u :=
      (hfa γ' u hu).trans (KGNat.linModelNat_lin _ _ _)
    have hπγ : ((π γ : ↥H) : MulAut W) = ((π γ' : ↥H) : MulAut W) := congrArg Subtype.val hγ
    rw [hπγ, h2] at h1
    exact h1.symm
  apply Subtype.ext
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun i => hlin _

theorem three_dvd_card_of_binaryNaturalSL_two [Finite W] {G : Subgroup (MulAut W)} {n : ℕ}
    (h : BinaryNaturalSL G U Z 2 n) : 3 ∣ Nat.card ↥G := by
  obtain ⟨K', _, _, hK', π', hπ'⟩ := h
  have hinj := injective_of_realizesVia_nat hπ'
  have hbij : Function.Bijective π' := ⟨hinj, hπ'.1⟩
  rw [← Nat.card_congr (Equiv.ofBijective π' hbij)]
  exact three_dvd_card_statedSL_two hK'

end Faithful

section Case1

theorem not_isPGroup_of_b56FactorList {X : Type} [Group X] [Finite X] (h : B56FactorList X) :
    ¬ IsPGroup 2 X := by
  apply not_isPGroup_of_three_dvd
  rcases h with ⟨n, K, _, _, -, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, K, _, _, -, -, hK, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_statedSL_two hK
  · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_statedSL_three hK

variable {Γ : Type} [Group Γ] [Finite Γ] {H R J L V : Subgroup Γ} {hV : IsElemAbelian 2 V}
  [IsMulCommutative ↥V]

theorem b56Case1_ffJ (h56 : AsB56) (hc : S5Core H R J L V hV) :
    autOn J V ≤ ffJ (autOn H V) ∧
      (∀ x ∈ ffJ (autOn H V), ∀ k ∈ autOn J V, x * k * x⁻¹ ∈ autOn J V) ∧
      pCoreOf 2 (ffJ (autOn H V)) = ⊥ ∧ quasithinGenFitting (ffJ (autOn H V)) = autOn J V ∧
      B51Conclusion (ffJ (autOn H V)) (autOn J V) := by
  obtain ⟨hJH, -, -, h2, -⟩ := s5_basic hc
  obtain ⟨hSQH, -, hRsyl, -, hHJ, -, -, hred, -, hJq', hJR, -⟩ := hc
  have hJq : CFSG.IsQuasisimple ↥(autOn J V) := isQuasisimple_of_open hJq'
  obtain ⟨A, -, hA, hLA⟩ := exists_offender_of_thompsonJ hV hred hRsyl hHJ h2 hJq hJR
  have hW2 : ∀ w ∈ V, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hV.2 w hw
  have hO2 : pCoreOf 2 (autOn H V) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  obtain ⟨hKJ, hn, hQ, -, hcases⟩ :=
    InternalSec.b56Cases_ffJ_autOn h56 hW2 hred.2.1 hJH hHJ hSQH hO2 hA hLA
  have hGH : ffJ (autOn H V) ≤ autOn H V := B6.ffJ_le _
  have hp : ∀ X ≤ ffJ (autOn H V), X ⊓ autOn J V = ⊥ → IsPGroup 2 ↥X := fun X hX hXJ =>
    isPGroup_of_inf_eq_bot h2 (hX.trans hGH) hXJ
  have hdisj : ∀ {X Y : Subgroup (MulAut ↥V)}, X ⊓ Y = ⊥ → autOn J V ≤ Y →
      X ⊓ autOn J V = ⊥ := fun hXY hJY =>
    le_bot_iff.mp (hXY ▸ inf_le_inf_left _ hJY)
  refine ⟨hKJ, hn, hQ, ?_⟩
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hcm, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, hinf, hcm, -, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hcm, -, ⟨e₁⟩, -, -, h₂⟩
  · have hF := InternalSec.eq_of_le_quasisimple hKJ hn hJq h1.1
    exact ⟨hF, hF ▸ h1.2.1⟩
  · exact (InternalSec.not_le_perm_three hJq hKJ e).elim
  · exfalso
    have h₁G : G₁ ≤ ffJ (autOn H V) := hsup ▸ le_sup_left
    have h₂G : G₂ ≤ ffJ (autOn H V) := hsup ▸ le_sup_right
    rcases InternalSec.le_or_le_of_sup_eq hsup hcm hKJ hn hJq with h | h
    · exact not_isPGroup_of_b56FactorList hf₂
        (hp G₂ h₂G (hdisj (by rw [inf_comm]; exact hinf) h))
    · exact not_isPGroup_of_b56FactorList hf₁ (hp G₁ h₁G (hdisj hinf h))
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h₂G : G₂ ≤ ffJ (autOn H V) := by
      rw [hJt]
      exact le_sup_right.trans le_sup_left
    rcases InternalSec.le_or_le_of_sup_zpowers hJt hcm ht₁ ht₂ hKJ hn hJq with h | h
    · exact not_isPGroup_of_three_dvd (by rw [hc₂])
        (hp G₂ h₂G (hdisj (by rw [inf_comm]; exact hinf) h))
    · exact InternalSec.not_le_of_card_prime hJq h hc₂
  · exfalso
    have h₁G : G₁ ≤ ffJ (autOn H V) := hsup ▸ le_sup_left
    have h₂G : G₂ ≤ ffJ (autOn H V) := hsup ▸ le_sup_right
    rcases InternalSec.le_or_le_of_sup_eq hsup hcm hKJ hn hJq with h | h
    · refine not_isPGroup_of_three_dvd ?_ (hp G₂ h₂G (hdisj (by rw [inf_comm]; exact hinf) h))
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, hB⟩
      · rw [Nat.card_congr e₂.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
        decide
      · exact three_dvd_card_of_binaryNaturalSL_two hB
    · refine not_isPGroup_of_three_dvd ?_ (hp G₁ h₁G (hdisj hinf h))
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      decide

end Case1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
