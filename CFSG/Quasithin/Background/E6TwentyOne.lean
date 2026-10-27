module

public import CFSG.Quasithin.Background.E6Sixteen
public import CFSG.Quasithin.Background.E6Nine
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E618Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → U ∈ gammaE64 V M → E3.mQuot V U ≤ 2 →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    ¬ (Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) ∧
      (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3))

@[expose] def E619Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V W W₀ : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → W ≤ V → E3.mQuot V W = 1 → W₀ ≤ V → E3.mQuot V W₀ = 1 →
    oddCoreIn (Subgroup.centralizer (W : Set G)) ≤
      oddCoreIn (Subgroup.centralizer ((W ⊓ W₀ : Subgroup G) : Set G))

@[expose] def E620Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → U ≤ V → E3.mQuot V U = 1 →
    oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥

@[expose] def E621Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V A : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → A ≤ V → A ≠ ⊥ →
    oddCoreIn (Subgroup.centralizer (A : Set G)) = ⊥

@[expose] def E622Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → U ≤ V → E3.mQuot V U = 1 →
    CharTwo (Subgroup.centralizer (U : Set G))

section TwentyOne

variable {G : Type} [Group G] [Finite G] {T M V S A : Subgroup G}

theorem mQuot_eq_one_of_card (hSV : S ≤ V) (hScard : Nat.card V = 2 * Nat.card S) :
    E3.mQuot V S = 1 := by
  have h1 := Subgroup.relIndex_mul_card S V
  rw [inf_eq_left.2 hSV] at h1
  have h2 : S.relIndex V = 2 := by
    have hpos : 0 < Nat.card S := Nat.card_pos
    have : S.relIndex V * Nat.card S = 2 * Nat.card S := by rw [h1, hScard]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  unfold E3.mQuot
  rw [h2]
  exact padicValNat_self (p := 2)

theorem sup_eq_of_card (hSV : S ≤ V) (hAV : A ≤ V) (hScard : Nat.card V = 2 * Nat.card S)
    (hAS : ¬ A ≤ S) : S ⊔ A = V := by
  have hle : S ⊔ A ≤ V := sup_le hSV hAV
  have hlt : S < S ⊔ A := lt_of_le_of_ne le_sup_left fun he => hAS (he ▸ le_sup_right)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : S ≤ S ⊔ A)
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

theorem oddCoreIn_centralizer_V (h : HypE61 T M V) :
    oddCoreIn (Subgroup.centralizer (V : Set G)) = ⊥ := by
  have h1 := oddCoreIn_eq_bot_of_charTwo' (e6_6_one h (le_refl V))
  rwa [inf_eq_right.2 h.centralizer_le] at h1

end TwentyOne

theorem e621_of (h620 : E620Stmt) : E621Stmt := by
  intro G _ _ T M V A hV h h15 hAV hA1
  set H := Subgroup.centralizer (A : Set G) with hHdef
  set O := oddCoreIn H with hOdef
  have hVH : V ≤ H := fun v hv => Subgroup.mem_centralizer_iff.2 fun a ha =>
    B2F.isElemAbelian_comm h.isElemAbelian (hAV ha) hv
  have hVN : V ≤ Subgroup.normalizer (O : Set G) := hVH.trans (E3.le_normalizer_oddCoreIn H)
  have hgen := E3.le_iSup_hyperplane_inf_centralizer (E3.odd_card_oddCoreIn' H) h.isElemAbelian
    h.ne_bot hVN
  have hOodd : Odd (Nat.card O) := E3.odd_card_oddCoreIn' H
  rw [eq_bot_iff]
  refine hgen.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSV, hScard⟩ := hS
  have hodd : Odd (Nat.card ↥(O ⊓ Subgroup.centralizer (S : Set G))) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left)
  by_cases hAS : A ≤ S
  · have hCS : Subgroup.centralizer (S : Set G) ≤ H := Subgroup.centralizer_le hAS
    have hle : O ⊓ Subgroup.centralizer (S : Set G) ≤
        oddCoreIn (Subgroup.centralizer (S : Set G)) :=
      le_oddCoreIn_of_odd inf_le_right (B2F.le_normalizer_inf
        (hCS.trans (E3.le_normalizer_oddCoreIn H)) Subgroup.le_normalizer) hodd
    rwa [h620 G T M V S hV h h15 hSV (mQuot_eq_one_of_card hSV hScard)] at hle
  · have hSA : S ⊔ A = V := sup_eq_of_card hSV hAV hScard hAS
    have hCV : O ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer (V : Set G) := by
      intro x hx
      rw [← hSA, Subgroup.mem_centralizer_iff]
      intro y hy
      have hle : S ⊔ A ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun s hs => ?_) (fun a ha => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.1 hx.2 s hs
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.1 ((E3.oddCoreIn_le H) hx.1) a ha
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
    have hCVS : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.centralizer_le hSV
    have hCVH : Subgroup.centralizer (V : Set G) ≤ H := Subgroup.centralizer_le hAV
    have hle : O ⊓ Subgroup.centralizer (S : Set G) ≤
        oddCoreIn (Subgroup.centralizer (V : Set G)) :=
      le_oddCoreIn_of_odd hCV (B2F.le_normalizer_inf
        (hCVH.trans (E3.le_normalizer_oddCoreIn H)) (hCVS.trans Subgroup.le_normalizer)) hodd
    rwa [oddCoreIn_centralizer_V h] at hle

end E6

end CFSG.Quasithin
