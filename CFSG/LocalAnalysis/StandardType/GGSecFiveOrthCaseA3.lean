module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthAInf
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private theorem ct_ca3_core {Γ : Type} [Group Γ] [Finite Γ] (R : Γ → Prop) (AL AK : Subgroup Γ)
    (hgen : AL = Subgroup.closure {a | a ∈ AL ∧ R a})
    (hconj : ∀ a ∈ AL, ∀ b ∈ AL, R a → R b → ∃ g ∈ AL, b = g * a * g⁻¹)
    (hAL : Nat.card ↥AL = 24) (hWK : Nat.card ↥(AL ⊔ AK) = 48)
    (hKL : ¬ AK ≤ AL) (hLK : ¬ AL ≤ AK) (hH6 : 6 ∣ Nat.card ↥(AL ⊓ AK))
    (r : Γ) (hr : r ∈ AL ⊓ AK) (hrR : R r) (h12 : Nat.card ↥AK ≠ 12) : False := by
  have hALfin : Finite ↥AL := inferInstance
  have _hKLuse : ¬ AK ≤ AL := hKL
  have hALW : AL ≤ AL ⊔ AK := le_sup_left
  have hAKW : AK ≤ AL ⊔ AK := le_sup_right
  have hrelW : AL.relIndex (AL ⊔ AK) = 2 := by
    have hmul := Subgroup.relIndex_mul_card (H := AL) (K := AL ⊔ AK)
    rw [inf_of_le_left hALW, hAL, hWK] at hmul
    omega
  have hindexAW : (AL.subgroupOf (AL ⊔ AK)).index = 2 := by
    simpa [Subgroup.relIndex] using hrelW
  have hNAW : (AL.subgroupOf (AL ⊔ AK)).Normal :=
    Subgroup.normal_of_index_eq_two hindexAW
  have hnormAW : (AL.subgroupOf (AL ⊔ AK)).Normal := hNAW
  have hsupAW : AL.subgroupOf (AL ⊔ AK) ⊔ AK.subgroupOf (AL ⊔ AK) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hALW hAKW, Subgroup.subgroupOf_self]
  have hrelAW : (AL.subgroupOf (AL ⊔ AK)).relIndex (AK.subgroupOf (AL ⊔ AK)) = 2 := by
    rw [← Subgroup.relIndex_sup_left (K := AL.subgroupOf (AL ⊔ AK))
      (H := AK.subgroupOf (AL ⊔ AK)), hsupAW, Subgroup.relIndex_top_right, hindexAW]
  have hrelAK : AL.relIndex AK = 2 := by
    rw [← Subgroup.relIndex_subgroupOf (H := AL) (K := AK) (L := AL ⊔ AK) hAKW]
    exact hrelAW
  have hAKcard : Nat.card ↥AK = 2 * Nat.card ↥(AL ⊓ AK) := by
    have hmul := Subgroup.relIndex_mul_card (H := AL) (K := AK)
    rw [hrelAK] at hmul
    omega
  have hHdvd : Nat.card ↥(AL ⊓ AK) ∣ 24 := by
    have h := Subgroup.card_dvd_of_le (H := AL ⊓ AK) (K := AL) inf_le_left
    rwa [hAL] at h
  rcases hH6 with ⟨k, hk⟩
  rw [hk] at hHdvd
  have hkpos : 0 < k := by
    have hpos : 0 < Nat.card ↥(AL ⊓ AK) := Nat.card_pos
    omega
  have hkle : k ≤ 4 := by
    have hle : 6 * k ≤ 24 := Nat.le_of_dvd (by norm_num) hHdvd
    omega
  interval_cases k
  ·
    have hHval : Nat.card ↥(AL ⊓ AK) = 6 := by omega
    exact h12 (by rw [hAKcard, hHval])
  ·
    have hHval : Nat.card ↥(AL ⊓ AK) = 12 := by omega
    have hrelH : (AL ⊓ AK).relIndex AL = 2 := by
      have hmul := Subgroup.relIndex_mul_card (H := AL ⊓ AK) (K := AL)
      rw [inf_eq_left.mpr inf_le_left, hHval, hAL] at hmul
      omega
    have hNormH : ((AL ⊓ AK).subgroupOf AL).Normal := by
      apply Subgroup.normal_of_index_eq_two
      simpa [Subgroup.relIndex] using hrelH
    have hclosure_le : AL ≤ AL ⊓ AK := by
      conv_lhs => rw [hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro b hb
      obtain ⟨hbAL, hbR⟩ := hb
      obtain ⟨g, hgAL, hgb⟩ := hconj r hr.1 b hbAL hrR hbR
      rw [hgb]
      have hx : ((⟨g, hgAL⟩ * ⟨r, hr.1⟩ * ⟨g, hgAL⟩⁻¹ : AL) : Γ) ∈ AL ⊓ AK :=
        hNormH.conj_mem ⟨r, hr.1⟩ ⟨hr.1, hr.2⟩ ⟨g, hgAL⟩
      exact hx
    exact hLK (le_trans hclosure_le inf_le_right)
  ·
    norm_num at hHdvd
  ·
    have hHval : Nat.card ↥(AL ⊓ AK) = 24 := by omega
    have heq : AL ⊓ AK = AL :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hHval, hAL])
    exact hLK (heq ▸ inf_le_right)

private theorem ct_ca3_six_dvd {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) (r r' : Γ) (hr : r ∈ H) (hr' : r' ∈ H)
    (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) (hord : orderOf (r * r') = 3) : 6 ∣ Nat.card ↥H := by
  have hrord : orderOf r = 2 :=
    @orderOf_eq_prime Γ _ r 2 ⟨by norm_num⟩ hr2 hr1
  have h2 : 2 ∣ Nat.card ↥H := by
    have h := Subgroup.orderOf_dvd_natCard H hr
    rwa [hrord] at h
  have h3 : 3 ∣ Nat.card ↥H := by
    have h := Subgroup.orderOf_dvd_natCard H (H.mul_mem hr hr')
    rwa [hord] at h
  simpa using (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3)

theorem ggOrth_caseA3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input) (hd : Module.finrank (ZMod 3) V = 4) (hminus : ¬ (∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0))
    (hA3 : GGWeylOfType 3 (CoxeterMatrix.A 3) (ggAutomizer L Bs)) : False := by
  have hfinV : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfdV : FiniteDimensional (ZMod 3) V :=
    @Module.Finite.of_finite (ZMod 3) V _ _ _ hfinV
  obtain ⟨c₁, c₂, y, K, hc₁₂, hc₁0, hc₂0, hnbr, hReflL, hKrefl, hKWeyl, hKG2,
    hJK, hJL, hKL, hLK, hWA, hB⟩ := S.exists_nbr hL hP hPump hFix
  let AL : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  let AK : Subgroup (MulAut ↥Bs) := ggAutomizer K Bs
  have hAI : Nat.card ↥(ggAInf 3 B Bs x L D J) = 1440 := by
    rw [S.card_ggAInf]
    exact @card_orthogonalGroup_four_minus V _ _ hfdV Q S.nondeg hd hminus
  have hALcard : Nat.card ↥AL = 24 := by
    have h := CFSG.StandardType.ggWeylOfType_A_card (p := 3) (m := 3) hA3
    norm_num at h
    simpa [AL] using h
  have h24 : 24 ∣ Nat.card ↥(AL ⊔ AK) := by
    have h := Subgroup.card_dvd_of_le (H := AL) (K := AL ⊔ AK) le_sup_left
    rwa [hALcard] at h
  have h1440 : Nat.card ↥(AL ⊔ AK) ∣ 1440 := by
    have h := Subgroup.card_dvd_of_le (H := AL ⊔ AK) (K := ggAInf 3 B Bs x L D J) hWA
    rwa [hAI] at h
  have hWK : Nat.card ↥(AL ⊔ AK) = 48 := by
    have hcases := card_of_nonSimplyLaced (p := 3) hB
    exact (orth_order_arith _ hcases).1 h24 h1440
  have hrc := S.refl_conj
  have hgen : AL = Subgroup.closure {a | a ∈ AL ∧ GGIsReflection 3 a} := hrc.1
  have hconj : ∀ a ∈ AL, ∀ b ∈ AL, GGIsReflection 3 a → GGIsReflection 3 b →
      ∃ g ∈ AL, b = g * a * g⁻¹ := hrc.2
  have h12 : Nat.card ↥AK ≠ 12 := card_ne_twelve_of_weyl (p := 3) hKWeyl hKG2
  obtain ⟨r, hrJ, r', hr'J, hrRefl, hr'Refl, hord⟩ :=
    hJA2 G 3 B Bs x L D J 𝒦 S.cfg S.split
  have hrH : r ∈ AL ⊓ AK := ⟨hJL hrJ, hJK hrJ⟩
  have hr'H : r' ∈ AL ⊓ AK := ⟨hJL hr'J, hJK hr'J⟩
  have hr1 : r ≠ 1 := by
    intro hr_eq
    have hfix : Nat.card {b : ↥Bs // r b = b} * 3 = Nat.card ↥Bs := hrRefl.2
    rw [hr_eq] at hfix
    let e : {b : ↥Bs // (1 : MulAut ↥Bs) b = b} ≃ ↥Bs :=
      { toFun := Subtype.val
        invFun := fun b => ⟨b, by simp⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun b => rfl }
    have hcard : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
      Nat.card_congr e
    rw [hcard] at hfix
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    omega
  have hH6 : 6 ∣ Nat.card ↥(AL ⊓ AK) :=
    ct_ca3_six_dvd (AL ⊓ AK) r r' hrH hr'H hrRefl.1 hr1 hord
  exact ct_ca3_core (R := fun φ => GGIsReflection 3 φ) (AL := AL) (AK := AK)
    hgen hconj hALcard hWK hLK hKL hH6 r hrH hrRefl h12

end CFSG.StandardType.OrthF3

end
