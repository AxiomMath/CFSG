module

public import CFSG.Quasithin.Background.B1MoreTenB
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

@[expose] def B110Below (m : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G K A : Subgroup (MulAut V)), Nat.card ↥G < m → pCoreOf 2 G = ⊥ → K ≤ G →
      IsFFStarOffender G A → ⁅K, A⁆ = K → (CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) →
      ⁅fittingOf G, K⁆ = ⊥

section Step

variable {V : Type} [CommGroup V] [Finite V]

theorem odd_orderOf_of_card_three {Ω : Type*} [Group Ω] {K : Subgroup Ω} (h3 : Nat.card ↥K = 3)
    {k : Ω} (hk : k ∈ K) : Odd (orderOf k) := by
  have h1 : orderOf k ∣ Nat.card ↥K := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥K)
    rwa [Subgroup.orderOf_mk] at this
  rw [h3] at h1
  exact Odd.of_dvd_nat (by decide) h1

theorem le_sup_of_below (hV : ∀ v : V, v ^ 2 = 1) {G K A R : Subgroup (MulAut V)}
    (ih : B110Below (Nat.card ↥G)) (hO2 : pCoreOf 2 G = ⊥) (hKG : K ≤ G)
    (hA : IsFFStarOffender G A) (hKA : ⁅K, A⁆ = K)
    (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hRF : R ≤ fittingOf G)
    (hRn : ∀ g ∈ G, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hRK : ⁅R, K⁆ ≠ ⊥) : G ≤ R ⊔ (K ⊔ A) := by
  by_contra hGle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := R ⊔ (K ⊔ A) with hHdef
  have hRG : R ≤ G := hRF.trans (fittingOf_le G)
  have hAG : A ≤ G := hA.1
  have hHG : H ≤ G := sup_le hRG (sup_le hKG hAG)
  have hHlt : Nat.card ↥H < Nat.card ↥G := by
    by_contra hnot
    push Not at hnot
    exact hGle (Subgroup.eq_of_le_of_card_ge hHG hnot ▸ le_rfl)
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAnK : A ≤ Subgroup.normalizer (K : Set (MulAut V)) := le_normalizer_of_commutator_eq hKA
  have hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun a ha k hk =>
    B19Aux.conj_mem_of_le_normalizer hAnK ha hk
  have hKH : K ≤ H := le_sup_left.trans le_sup_right
  have hAH : A ≤ H := le_sup_right.trans le_sup_right
  have hRH : R ≤ H := le_sup_left
  have hKne : K ≠ ⊥ := by
    rcases hK with hq | h3
    · have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact (Subgroup.nontrivial_iff_ne_bot K).1 this
    · intro h
      rw [h, Subgroup.card_bot] at h3
      exact absurd h3 (by decide)
  have hRodd : ∀ r ∈ R, Odd (orderOf r) := fun r hr => B19Aux.odd_orderOf_of_mem_fittingOf hO2 r (hRF hr)
  have hKAnR : K ⊔ A ≤ Subgroup.normalizer (R : Set (MulAut V)) :=
    sup_le (le_normalizer_of_conj fun k hk r hr => hRn k (hKG hk) r hr)
      (le_normalizer_of_conj fun a ha r hr => hRn a (hAG ha) r hr)
  have hmul : ∀ h ∈ H, ∃ r ∈ R, ∃ y ∈ K ⊔ A, h = r * y := fun h hh =>
    (B19Aux.mem_sup_iff_of_le_normalizer hKAnR).1 hh
  have hRnH : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := fun h hh r hr => hRn h (hHG hh) r hr
  set Q := pCoreOf 2 H with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQY : Q ≤ K ⊔ A := pCoreOf_le_of_odd_factor hRH hRnH hRodd hmul
  have hKAnK : K ⊔ A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hAnK
  have hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q := by
    have hQnK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K := fun q hq k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKAnK (hQY hq)) k).mp hk
    have hKnQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
      conj_mem_pCoreOf_gen (hKH hk) hq
    rcases hK with hq | h3
    · refine commute_of_normal_not_le hq hQnK hKnQ ?_
      intro hle
      have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
      have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact Group.IsPerfect.not_isNilpotent ↥K (hQ2.to_le hle).isNilpotent
    · intro q hq k hk
      have h1 : q * k * q⁻¹ * k⁻¹ ∈ K := K.mul_mem (hQnK q hq k hk) (K.inv_mem hk)
      have h2 : q * k * q⁻¹ * k⁻¹ ∈ Q := by
        have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
        rw [e]
        exact Q.mul_mem hq (hKnQ k hk q⁻¹ (Q.inv_mem hq))
      obtain ⟨j, hj⟩ := hQ2 ⟨_, h2⟩
      have hj' : (q * k * q⁻¹ * k⁻¹) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have h3' : q * k * q⁻¹ * k⁻¹ = 1 :=
        B19Aux.eq_one_of_odd_orderOf_of_pow (odd_orderOf_of_card_three h3 h1) hj'
      calc q * k = (q * k * q⁻¹ * k⁻¹) * (k * q) := by group
        _ = k * q := by rw [h3', one_mul]
  have hQR := pCoreOf_commute_of_odd_normal hRH hRnH hRodd
  have hKnR : K ≤ Subgroup.normalizer (R : Set (MulAut V)) := le_sup_left.trans hKAnR
  have hAnD : A ≤ Subgroup.normalizer ((R ⊔ K : Subgroup (MulAut V)) : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha x hx =>
      conj_mem_sup_of_conj_mem hKnR (fun r hr => hRn a (hAG ha) r hr)
        (fun k hk => hAK a ha k hk) x hx
  have hHeq : H = (R ⊔ K) ⊔ A := (sup_assoc R K A).symm
  have hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ R ⊔ K := fun x hx ho =>
    mem_of_sq_mem_of_odd (sq_mem_of_mem_sup hAnD hAel.2 x (hHeq ▸ hx)) ho
  have hDQ : ∀ x ∈ R ⊔ K, ∀ q ∈ Q, x * q = q * x := by
    intro x hx q hq
    have hsup : R ⊔ K ≤ Subgroup.centralizer ({q} : Set (MulAut V)) := by
      refine sup_le (fun r hr => ?_) (fun k hk => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hQR q hq r hr).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hQK q hq k hk).symm
    have := hsup hx
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hker : H ⊓ centSub (fixV Q) = Q := kernel_eq_pCoreOf hV hD hDQ
  set U := fixV Q with hUdef
  have hst : H ≤ stabSub U := le_stabSub_fixV_pCoreOf H
  have hKU : K ≤ stabSub U := hKH.trans hst
  have hAU : A ≤ stabSub U := hAH.trans hst
  have hRU : R ≤ stabSub U := hRH.trans hst
  have hKnc : ¬ K ≤ centSub U := by
    intro hle
    have hKQ : K ≤ Q := hker ▸ le_inf hKH hle
    rcases hK with hq | h3
    · have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
      have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact Group.IsPerfect.not_isNilpotent ↥K (hQ2.to_le hKQ).isNilpotent
    · apply hKne
      refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => ?_
      obtain ⟨j, hj⟩ := hQ2 ⟨k, hKQ hk⟩
      exact B19Aux.eq_one_of_odd_orderOf_of_pow (odd_orderOf_of_card_three h3 hk)
        (congrArg Subtype.val hj)
  have hAnc : ¬ A ≤ centSub U := by
    intro hle
    have hAQ : A ≤ Q := hker ▸ le_inf hAH hle
    have h0 : ⁅K, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro k hk a ha
      show ⁅k, a⁆ ∈ (⊥ : Subgroup (MulAut V))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hQK a (hAQ ha) k hk).symm
    exact hKne (hKA ▸ h0)
  set Hb := autSub H U with hHb
  set Kb := autSub K U with hKb
  set Ab := autSub A U with hAb
  set Rb := autSub R U with hRb
  have hHbO2 : pCoreOf 2 Hb = ⊥ := pCoreOf_autSub_eq_bot hker
  have hKbHb : Kb ≤ Hb := autSub_mono hKH U
  have hHAoff : IsFFStarOffender H A := ⟨hAH, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hAbOff : IsFFStarOffender Hb Ab :=
    isFFStarOffender_autSub hHAoff (fun a ha w hw => (hAU ha w).2 hw) hAnc
  have hKbAb : ⁅Kb, Ab⁆ = Kb := commutator_autSub_eq hKU hAU hKA
  have hKbtype : CFSG.Open.IsQuasisimple ↥Kb ∨ Nat.card ↥Kb = 3 := by
    rcases hK with hq | h3
    · exact Or.inl (isQuasisimple_autSub hKU hq hKnc)
    · right
      have h1 := card_autSub_mul hKU
      have h2 : K ⊓ centSub U = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
        have hkQ : k ∈ Q := by rw [← hker]; exact ⟨hKH hk.1, hk.2⟩
        obtain ⟨j, hj⟩ := hQ2 ⟨k, hkQ⟩
        exact B19Aux.eq_one_of_odd_orderOf_of_pow (odd_orderOf_of_card_three h3 hk.1)
          (congrArg Subtype.val hj)
      rw [h2, Subgroup.card_bot, mul_one] at h1
      rw [h1, h3]
  have hHbcard : Nat.card ↥Hb < Nat.card ↥G := by
    have h1 := card_autSub_mul hst
    have hle : Nat.card ↥Hb ≤ Nat.card ↥H :=
      Nat.le_of_dvd Nat.card_pos (Dvd.intro _ h1)
    exact lt_of_le_of_lt hle hHlt
  have hV' : ∀ v : ↥U, v ^ 2 = 1 := B1.sq_eq_one_sub hV U
  have hih : ⁅fittingOf Hb, Kb⁆ = ⊥ :=
    ih ↥U hV' Hb Kb Ab hHbcard hHbO2 hKbHb hAbOff hKbAb hKbtype
  have hRnil : Group.IsNilpotent ↥R := by
    have hFnil : Group.IsNilpotent ↥(fittingOf G) := fittingOf_nilpotent G
    have h1 : Group.IsNilpotent ↥(R.subgroupOf (fittingOf G)) := inferInstance
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hRF)).mp h1
  have hRbnil : Group.IsNilpotent ↥Rb := by
    rw [hRb, autSub_eq_range hRU]
    exact Group.nilpotent_of_surjective
      ((resHom U).comp (Subgroup.inclusion hRU)).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hRbF : Rb ≤ fittingOf Hb :=
    le_fittingOf_of_nilpotent_normal (autSub_mono hRH U)
      (fun g hg n hn => autSub_conj_mem (fun x hx y hy => hRnH x hx y hy) hg hn)
  have hRbKb : ⁅Rb, Kb⁆ = ⊥ := eq_bot_iff.2 (hih ▸ Subgroup.commutator_mono hRbF le_rfl)
  apply hRK
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro r hr k hk
  show ⁅r, k⁆ ∈ (⊥ : Subgroup (MulAut V))
  rw [Subgroup.mem_bot]
  have hrs : r ∈ stabSub U := hRU hr
  have hks : k ∈ stabSub U := hKU hk
  have hcs : ⁅r, k⁆ ∈ stabSub U := (stabSub U).mul_mem ((stabSub U).mul_mem
    ((stabSub U).mul_mem hrs hks) ((stabSub U).inv_mem hrs)) ((stabSub U).inv_mem hks)
  have hrk : resHom U ⟨⁅r, k⁆, hcs⟩ ∈ ⁅Rb, Kb⁆ := by
    have e : resHom U ⟨⁅r, k⁆, hcs⟩ = ⁅resHom U ⟨r, hrs⟩, resHom U ⟨k, hks⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [e]
    exact Subgroup.commutator_mem_commutator (mem_autSub.2 ⟨⟨r, hrs⟩, hr, rfl⟩)
      (mem_autSub.2 ⟨⟨k, hks⟩, hk, rfl⟩)
  rw [hRbKb, Subgroup.mem_bot] at hrk
  have hcent : ⁅r, k⁆ ∈ centSub U := by
    have h1 : (⟨⁅r, k⁆, hcs⟩ : stabSub U) ∈ (resHom U).ker := hrk
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcH : ⁅r, k⁆ ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hRH hr) (hKH hk))
    (H.inv_mem (hRH hr))) (H.inv_mem (hKH hk))
  have hcQ : ⁅r, k⁆ ∈ Q := by rw [← hker]; exact ⟨hcH, hcent⟩
  have hcR : ⁅r, k⁆ ∈ R := by
    have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact R.mul_mem hr (hRn k (hKG hk) r⁻¹ (R.inv_mem hr))
  obtain ⟨j, hj⟩ := hQ2 ⟨_, hcQ⟩
  exact B19Aux.eq_one_of_odd_orderOf_of_pow (hRodd _ hcR) (congrArg Subtype.val hj)

end Step

end B1Red

end CFSG.Quasithin
