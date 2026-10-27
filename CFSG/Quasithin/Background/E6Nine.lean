module

public import CFSG.Quasithin.Background.E6Gamma
public import CFSG.Quasithin.Background.E3Odd
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

theorem charTwo_of_hypE61 (h : HypE61 T M V) : CharTwo M := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  exact h.qtke.2.1 M h.inM.1.1 ⟨S, hS ▸ h.inM.2⟩

theorem e6_6_one (h : HypE61 T M V) (hUV : U ≤ V) :
    CharTwo (M ⊓ Subgroup.centralizer (U : Set G)) :=
  CT.CharTwo.inf_centralizer (charTwo_of_hypE61 h) (hUV.trans (h.le.trans h.inM.2))
    (h.isPGroup_V.to_le hUV)

omit [Finite G] in
theorem le_oddCoreIn_of_odd {X K : Subgroup G} (hKX : K ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn X := by
  have hnormal : (K.subgroupOf X).Normal := by
    constructor
    intro a ha x
    exact (Subgroup.mem_normalizer_iff.mp (hnorm x.property) a).mp ha
  have hodd' : Odd (Nat.card (K.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have hle : K.subgroupOf X ≤ fusionOddCore X := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKX hk⟩, hle hk, rfl⟩

theorem eq_bot_of_isPGroup_of_le_odd {P Z : Subgroup G} (hP : IsPGroup 2 P) (hPZ : P ≤ Z)
    (hZ : Odd (Nat.card Z)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hdvd : Nat.card P ∣ Nat.card Z := Subgroup.card_dvd_of_le hPZ
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

theorem oddCoreIn_eq_bot_of_charTwo' {X : Subgroup G} (hX : CharTwo X) : oddCoreIn X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn X with hOdef
  set P := pCoreOf 2 X with hPdef
  have hOX : O ≤ X := E3.oddCoreIn_le X
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hOodd : Odd (Nat.card O) := E3.odd_card_oddCoreIn' X
  have hOP : O ⊓ P = ⊥ := eq_bot_of_isPGroup_of_le_odd (hP2.to_le inf_le_right) inf_le_left hOodd
  have hc1 : ⁅O, P⁆ ≤ O :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (hPX.trans (E3.le_normalizer_oddCoreIn X))
  have hc2 : ⁅O, P⁆ ≤ P := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.1
      (hOX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have hc : ⁅O, P⁆ = ⊥ := le_bot_iff.1 (hOP ▸ le_inf hc1 hc2)
  have hOC : O ≤ X ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf hOX ((Subgroup.commutator_eq_bot_iff_le_centralizer).1 hc)
  have hOP' : O ≤ P := hOC.trans hX
  rw [eq_bot_iff, ← hOP]
  exact le_inf le_rfl hOP'

theorem e6_9_one (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    oddCoreIn (Subgroup.centralizer (U : Set G)) ⊓ M = ⊥ := by
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hle : oddCoreIn H ⊓ M ≤ oddCoreIn (M ⊓ H) := by
    refine le_oddCoreIn_of_odd (le_inf inf_le_right (inf_le_left.trans (E3.oddCoreIn_le H)))
      ?_ (Odd.of_dvd_nat (E3.odd_card_oddCoreIn' H) (Subgroup.card_dvd_of_le inf_le_left))
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxN := E3.le_normalizer_oddCoreIn H hx.2
    constructor
    · rintro ⟨hyO, hyM⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hyO,
        M.mul_mem (M.mul_mem hx.1 hyM) (M.inv_mem hx.1)⟩
    · rintro ⟨hyO, hyM⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hxN y).2 hyO, ?_⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hx.1) hyM) hx.1
      simpa [mul_assoc] using this
  rw [oddCoreIn_eq_bot_of_charTwo' (e6_6_one h hU.1)] at hle
  exact le_bot_iff.1 hle

theorem e6_9_two (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) ≠ ⊥) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ E3.mQuot V A = 1 ∧
      ¬ oddCoreIn (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer (A : Set G) ≤ M := by
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set O := oddCoreIn H with hOdef
  have hU' := hU
  obtain ⟨hUV, -, -, -⟩ := hU
  by_contra hall
  push Not at hall
  apply hO
  have hVQ : V ≤ T ⊓ Subgroup.centralizer (V : Set G) := h.le_inf_centralizer
  have hVH : V ≤ H := hVQ.trans (inf_le_right.trans (Subgroup.centralizer_le hUV))
  have hVN : V ≤ Subgroup.normalizer (O : Set G) := hVH.trans (E3.le_normalizer_oddCoreIn H)
  have hgen := E3.le_iSup_hyperplane_inf_centralizer (E3.odd_card_oddCoreIn' H) h.isElemAbelian
    h.ne_bot hVN
  have hOM : O ≤ M := by
    refine hgen.trans (iSup₂_le fun S hS => ?_)
    obtain ⟨hSV, hScard⟩ := hS
    by_cases hUS : U ≤ S
    · refine hall S hUS hSV ?_
      have h1 := Subgroup.relIndex_mul_card S V
      rw [inf_eq_left.2 hSV] at h1
      have h2 : S.relIndex V = 2 := by
        have hpos : 0 < Nat.card S := Nat.card_pos
        have : S.relIndex V * Nat.card S = 2 * Nat.card S := by rw [h1, hScard]
        exact Nat.eq_of_mul_eq_mul_right hpos this
      unfold E3.mQuot
      rw [h2]
      exact padicValNat_self (p := 2)
    ·
      have hSU : S ⊔ U = V := by
        have hle : S ⊔ U ≤ V := sup_le hSV hUV
        have hlt : S < S ⊔ U := lt_of_le_of_ne le_sup_left fun he => hUS (he ▸ le_sup_right)
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : S ≤ S ⊔ U)
        have hk1 : 1 < k := by
          by_contra hk1
          push Not at hk1
          have hpos : 0 < Nat.card S := Nat.card_pos
          have hcard := Subgroup.card_lt_of_lt hlt
          interval_cases k
          · rw [hk, mul_zero] at hcard
            omega
          · rw [hk, mul_one] at hcard
            omega
        rw [hScard, hk, mul_comm 2]
        exact Nat.mul_le_mul_left _ hk1
      intro x hx
      apply h.centralizer_le
      rw [← hSU, Subgroup.mem_centralizer_iff]
      intro y hy
      have hxS := Subgroup.mem_centralizer_iff.1 hx.2
      have hxU := Subgroup.mem_centralizer_iff.1 ((E3.oddCoreIn_le H) hx.1)
      have hle : S ⊔ U ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun s hs => ?_) (fun u hu => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hxS s hs
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hxU u hu
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  rw [eq_bot_iff, ← e6_9_one h hU']
  exact le_inf le_rfl hOM

theorem oddCoreIn_eq_bot_of_maximal (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hm : 1 < E3.mQuot V U) : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥ := by
  by_contra hO
  obtain ⟨A, hUA, hAV, hA1, hAM⟩ := e6_9_two h hU hO
  have hne : U ≠ A := fun he => by rw [he, hA1] at hm; exact lt_irrefl 1 hm
  exact hAM (inf_le_right.trans (hmax A (lt_of_le_of_ne hUA hne) hAV))

end E6
end CFSG.Quasithin
