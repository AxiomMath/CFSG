module

public import CFSG.Quasithin.Background.B1MoreTen
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4
public import CFSG.Quasithin.Background.C1PackSubnormal
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_autI_eq_bot {X V : Subgroup G} (hV : IsElemAbelian 2 V) (hred : IsTwoReducedIn X V) :
    pCoreOf 2 (autI hV X) = ⊥ := by
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hQX : pCoreOf 2 (autI hV X) ≤ autI hV X := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hDX : preI hV X hXN (pCoreOf 2 (autI hV X)) ≤ X := preI_le hV
  have key : ∀ x ∈ X, ∀ d ∈ preI hV X hXN (pCoreOf 2 (autI hV X)),
      x * d * x⁻¹ ∈ preI hV X hXN (pCoreOf 2 (autI hV X)) := by
    intro x hx d hd
    obtain ⟨hdX, hdQ⟩ := (mem_preI hV).1 hd
    refine (mem_preI hV).2 ⟨X.mul_mem (X.mul_mem hx hdX) (X.inv_mem hx), ?_⟩
    have hx' : convHom hV X hXN ⟨x, hx⟩ ∈ autI hV X := convI_mem_autI hV hx (hXN hx)
    have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (autI hV X) hx'
    have h1 := (Subgroup.mem_normalizer_iff.1 hnorm _).1 hdQ
    have e : convHom hV X hXN ⟨x * d * x⁻¹, X.mul_mem (X.mul_mem hx hdX) (X.inv_mem hx)⟩ =
        convHom hV X hXN ⟨x, hx⟩ * convHom hV X hXN ⟨d, hdX⟩ * (convHom hV X hXN ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact h1
  have hDn : X ≤ Subgroup.normalizer (preI hV X hXN (pCoreOf 2 (autI hV X)) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have h2 : ∀ d ∈ preI hV X hXN (pCoreOf 2 (autI hV X)),
      ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨hdX, hdQ⟩ := (mem_preI hV).1 hd
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autI hV X)
      ⟨convHom hV X hXN ⟨d, hdX⟩, hdQ⟩
    refine ⟨k, ?_⟩
    have h1 : (convHom hV X hXN ⟨d, hdX⟩) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (convI_eq_one_iff hV ⟨d ^ 2 ^ k, hXN (X.pow_mem hdX _)⟩).1 h1
  have hDC := hred.2.2.2 _ hDX hDn h2
  have h3 : autI hV (preI hV X hXN (pCoreOf 2 (autI hV X))) = pCoreOf 2 (autI hV X) :=
    autI_preI hV hQX
  rw [← h3]
  exact autI_eq_bot_of_le_centralizer hV hDC

theorem isSolvable_autI_of_perfectCore_le {X V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (h : perfectCore X ≤ Subgroup.centralizer (V : Set G)) : Group.IsSolvable ↥(autI hV X) := by
  rw [isSolvable_iff_perfectCore_eq_bot]
  have h1 : perfectCore (autI hV X) =
      (perfectCore (X.subgroupOf (Subgroup.normalizer (V : Set G)))).map (convI hV) :=
    (map_perfectCore (convI hV) _).symm
  have h2 : (perfectCore (X.subgroupOf (Subgroup.normalizer (V : Set G)))).map
      (Subgroup.normalizer (V : Set G)).subtype = perfectCore X := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hXN]
  rw [h1, eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxG : (x : G) ∈ perfectCore X := by
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot]
  exact (convI_eq_one_iff hV x).2 (h hxG)

omit [Finite G] in
theorem card_autI_eq_three {X V K W : Subgroup G} {c : G} (hV : IsElemAbelian 2 V)
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hA4 : S14110.A4Data K W c)
    (hWV : W ≤ V) (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card (autI hV K) = 3 := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKX.trans hXN
  have h1 := card_autI_mul_card_inf hV hKN
  rw [hA4.card_X] at h1
  have hW : W ≤ K ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf hA4.le (fun w hw => B2F.le_centralizer_self hV (hWV hw))
  have h4 : 4 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) :=
    hA4.card_W ▸ Subgroup.card_dvd_of_le hW
  have hne : Nat.card (autI hV K) ≠ 1 := by
    intro h
    exact hKV ((autI_eq_bot_iff hV hKN).1 (Subgroup.eq_bot_of_card_eq _ h))
  obtain ⟨t, ht⟩ := h4
  have h5 : 4 * (Nat.card (autI hV K) * t) = 4 * 3 := by
    rw [← mul_assoc, mul_comm 4, mul_assoc, ← ht, h1]
  have h6 : Nat.card (autI hV K) * t = 3 := Nat.eq_of_mul_eq_mul_left (by norm_num) h5
  have h7 : Nat.card (autI hV K) ∣ 3 := Dvd.intro t h6
  rcases (Nat.dvd_prime Nat.prime_three).1 h7 with h8 | h8
  · exact absurd h8 hne
  · exact h8

omit [Finite G] in
theorem eq_bot_or_eq_of_card_eq_three {Γ : Type*} [Group Γ] [Finite Γ] {S K' : Subgroup Γ}
    (hK : Nat.card K' = 3) (hSK : S ≤ K') : S = ⊥ ∨ S = K' := by
  have hdvd : Nat.card S ∣ 3 := hK ▸ Subgroup.card_dvd_of_le hSK
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hSK (by rw [hK, h]))

theorem exists_offender_of_commutator {X T V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T X) (hKX : K ≤ X)
    (hKJ : ⁅K, thompsonJ T⁆ = K) (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G))
    (hK3 : Nat.card (autI hV K) = 3) :
    ∃ B ∈ offenderImages hV X, ⁅autI hV K, B⁆ = autI hV K := by
  have hJN : thompsonJ T ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hKJ.le
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hXN
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKX.trans hXN
  have hAN : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.normalizer (V : Set G) := fun A hA =>
    hA.1.trans hTN
  by_contra hcon
  push Not at hcon
  have hmemN : ∀ {k a : G}, k ∈ Subgroup.normalizer (V : Set G) →
      a ∈ Subgroup.normalizer (V : Set G) → ⁅k, a⁆ ∈ Subgroup.normalizer (V : Set G) := by
    intro k a hk ha
    simp only [commutatorElement_def]
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hk ha)
        ((Subgroup.normalizer (V : Set G)).inv_mem hk)) ((Subgroup.normalizer (V : Set G)).inv_mem ha)
  have hconvcomm : ∀ {k a : G} (hk : k ∈ Subgroup.normalizer (V : Set G))
      (ha : a ∈ Subgroup.normalizer (V : Set G)),
      ⁅convI hV ⟨k, hk⟩, convI hV ⟨a, ha⟩⁆ = convI hV ⟨⁅k, a⁆, hmemN hk ha⟩ := by
    intro k a hk ha
    rw [← map_commutatorElement]
    rfl
  have hcent : ∀ A, IsMaxElemAbelian T A →
      autI hV A ≤ Subgroup.centralizer (autI hV K : Set (MulAut (IntMod V hV))) := by
    intro A hA
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · rw [autI_eq_bot_of_le_centralizer hV hAC]
      exact bot_le
    have hB : autI hV A ∈ offenderImages hV X :=
      ⟨A, ⟨B6.isMaxElemAbelian_of_sylow hT hA, hAC⟩, rfl⟩
    have hle : ⁅autI hV K, autI hV A⁆ ≤ autI hV K := by
      rw [Subgroup.commutator_le]
      rintro x hx y hy
      obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hx
      obtain ⟨a, haA, rfl⟩ := (mem_autI hV).1 hy
      have hka : ⁅(k : G), (a : G)⁆ ∈ K := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hJN (hAJ haA)) (k : G)⁻¹).1 (K.inv_mem hkK)
        have h2 : ⁅(k : G), (a : G)⁆ = (k : G) * ((a : G) * (k : G)⁻¹ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h2]
        exact K.mul_mem hkK h1
      rw [hconvcomm k.2 a.2]
      exact convI_mem_autI hV hka (hmemN k.2 a.2)
    rcases eq_bot_or_eq_of_card_eq_three hK3 hle with h0 | h1
    · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
      exact h0
    · exact absurd h1 (hcon _ hB)
  have hJc : autI hV (thompsonJ T) ≤
      Subgroup.centralizer (autI hV K : Set (MulAut (IntMod V hV))) := by
    unfold thompsonJ
    rw [autI_iSup₂ hV (fun A hA => hA.1.trans hTN)]
    exact iSup₂_le fun A hA => hcent A hA
  have hKJC : ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have hkN := hKN hk
    have hjN : j ∈ Subgroup.normalizer (V : Set G) := hTN (B6.thompsonJ_le T hj)
    have hcomm := Subgroup.mem_centralizer_iff.1 (hJc (convI_mem_autI hV hj hjN))
      (convI hV ⟨k, hkN⟩) (convI_mem_autI hV hk hkN)
    have h1 : convI hV ⟨⁅k, j⁆, hmemN hkN hjN⟩ = 1 := by
      rw [← hconvcomm hkN hjN, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    exact (convI_eq_one_iff hV _).1 h1
  exact hKV (hKJ ▸ hKJC)

theorem autI_le_fittingOf {X V K : Subgroup G} (hV : IsElemAbelian 2 V) (hVX : V ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hO2 : pCoreOf 2 (autI hV X) = ⊥)
    (hsolv : Group.IsSolvable ↥(autI hV X)) (hKX : K ≤ X) (hK3 : Nat.card (autI hV K) = 3)
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ∈ offenderImages hV X)
    (hKB : ⁅autI hV K, B⁆ = autI hV K) : autI hV K ≤ fittingOf (autI hV X) := by
  have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have h := B1_10 hV2 hO2 (autI_mono hV hKX) (offenderImages_isFFStarOffender hV hVX hXN hB) hKB
    (Or.inr hK3)
  intro k hk
  have hkX : k ∈ autI hV X := autI_mono hV hKX hk
  have hF : (⟨k, hkX⟩ : ↥(autI hV X)) ∈
      Subgroup.centralizer (CFSG.generalizedFitting ↥(autI hV X) : Set ↥(autI hV X)) := by
    rw [generalizedFitting_eq_fittingSubgroup_of_isSolvable]
    refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
    have := Subgroup.mem_centralizer_iff.1 (h hk).2 (f : MulAut (IntMod V hV)) ⟨f, hf, rfl⟩
    exact Subtype.ext this
  have hF' := CFSG.centralizer_generalizedFitting_le ↥(autI hV X) hF
  rw [generalizedFitting_eq_fittingSubgroup_of_isSolvable] at hF'
  exact ⟨⟨k, hkX⟩, hF', rfl⟩

theorem isSubnormal_autI_of_le_fittingOf {X V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKF : autI hV K ≤ fittingOf (autI hV X)) :
    ((autI hV K).subgroupOf (autI hV X)).IsSubnormal := by
  have hFX : fittingOf (autI hV X) ≤ autI hV X := fittingOf_le _
  have hnil := fittingOf_nilpotent (autI hV X)
  have hB : ((autI hV K).subgroupOf (fittingOf (autI hV X))).IsSubnormal :=
    isSubnormal_of_isNilpotent' _
  have hN : ((fittingOf (autI hV X)).subgroupOf (autI hV X)).Normal := by
    have : (fittingOf (autI hV X)).subgroupOf (autI hV X) = CFSG.fittingSubgroup ↥(autI hV X) :=
      Subgroup.comap_map_eq_self_of_injective (autI hV X).subtype_injective _
    rw [this]
    infer_instance
  exact isSubnormal_subgroupOf_trans' hKF hFX hB hN.isSubnormal

omit [Finite G] in
theorem isSubnormal_preI {X V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hsub : ((autI hV K).subgroupOf (autI hV X)).IsSubnormal) :
    ((preI hV X hXN (autI hV K)).subgroupOf X).IsSubnormal := by
  let f : ↥X →* ↥(autI hV X) := (convHom hV X hXN).codRestrict (autI hV X) (fun x => by
    rw [← range_convHom hV X hXN]
    exact ⟨x, rfl⟩)
  have h1 := hsub.comap f
  have h2 : ((autI hV K).subgroupOf (autI hV X)).comap f =
      (preI hV X hXN (autI hV K)).subgroupOf X := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_preI]
    constructor
    · intro hx
      exact ⟨x.2, hx⟩
    · rintro ⟨hx, hx'⟩
      exact hx'
  rwa [h2] at h1

omit [Finite G] in
theorem preI_le_normalizer {X V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hKX : K ≤ X)
    (hC : X ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    preI hV X hXN (autI hV K) ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  have hxX : x ∈ X := preI_le hV hx
  have h := autI_preI (hA := hXN) hV (autI_mono hV hKX : autI hV K ≤ autI hV X)
  obtain ⟨y, hyK, hxy⟩ := exists_mul_inv_mem_centralizer hV (preI_le hV) hXN h hx
  have hg : x * y⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    hC ⟨X.mul_mem hxX (X.inv_mem (hKX hyK)), hxy⟩
  have : x = (x * y⁻¹) * y := by group
  rw [this]
  exact (Subgroup.normalizer (K : Set G)).mul_mem hg (Subgroup.le_normalizer hyK)

end CFSG.Quasithin.C1Pack
