module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.B1MoreNineD

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Group

variable {Ω : Type*} [Group Ω]

theorem conj_mem_pCoreOf_gen {H : Subgroup Ω} {h q : Ω} (hh : h ∈ H) (hq : q ∈ pCoreOf 2 H) :
    h * q * h⁻¹ ∈ pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) q).mp hq

theorem pCoreOf_commute_of_odd_normal [Finite Ω] {H R : Subgroup Ω} (hRH : R ≤ H)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hRodd : ∀ r ∈ R, Odd (orderOf r)) :
    ∀ q ∈ pCoreOf 2 H, ∀ r ∈ R, q * r = r * q := by
  intro q hq r hr
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hqH : q ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hq
  have h1 : q * r * q⁻¹ * r⁻¹ ∈ R := R.mul_mem (hRn q hqH r hr) (R.inv_mem hr)
  have h2 : q * r * q⁻¹ * r⁻¹ ∈ pCoreOf 2 H := by
    have : r * q⁻¹ * r⁻¹ ∈ pCoreOf 2 H :=
      conj_mem_pCoreOf_gen (hRH hr) ((pCoreOf 2 H).inv_mem hq)
    have e : q * r * q⁻¹ * r⁻¹ = q * (r * q⁻¹ * r⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hq this
  obtain ⟨k, hk⟩ := hQ2 ⟨_, h2⟩
  have hk' : (q * r * q⁻¹ * r⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : q * r * q⁻¹ * r⁻¹ = 1 := B19Aux.eq_one_of_odd_orderOf_of_pow (hRodd _ h1) hk'
  calc q * r = (q * r * q⁻¹ * r⁻¹) * (r * q) := by group
    _ = r * q := by rw [h3, one_mul]

theorem pCoreOf_le_of_odd_factor [Finite Ω] {H R Y : Subgroup Ω} (hRH : R ≤ H)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hRodd : ∀ r ∈ R, Odd (orderOf r))
    (hmul : ∀ h ∈ H, ∃ r ∈ R, ∃ y ∈ Y, h = r * y) : pCoreOf 2 H ≤ Y := by
  intro q hq
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hcomm := pCoreOf_commute_of_odd_normal hRH hRn hRodd
  obtain ⟨r, hr, y, hy, hqry⟩ := hmul q (CFSG.LieType.BorelTits.pCoreOf_le 2 H hq)
  have hqr : q * r = r * q := hcomm q hq r hr
  have hry : Commute r y := by
    have hy' : y = r⁻¹ * q := by rw [hqry]; group
    show r * y = y * r
    rw [hy']
    calc r * (r⁻¹ * q) = q := by group
      _ = r⁻¹ * (r * q) := by group
      _ = r⁻¹ * (q * r) := by rw [hqr]
      _ = (r⁻¹ * q) * r := by group
  have hmodd : Odd (orderOf r) := hRodd r hr
  have hqm : q ^ orderOf r = y ^ orderOf r := by
    rw [hqry, hry.mul_pow, pow_orderOf_eq_one, one_mul]
  have hqm' : q ^ orderOf r ∈ Y := hqm ▸ Y.pow_mem hy _
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hQ2 ⟨q, hq⟩
  have hqo : orderOf q = 2 ^ j := by rw [← Subgroup.orderOf_coe] at hj; exact hj
  have hcop : Nat.Coprime (orderOf r) (orderOf q) := by
    rw [hqo]
    exact Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hmodd)
  exact (Subgroup.zpowers_le.2 hqm') (A4.mem_zpowers_pow_of_coprime hcop)

theorem commutator_eq_or_commute [Finite Ω] {K B : Subgroup Ω}
    (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (hBK : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K) :
    ⁅K, B⁆ = K ∨ ∀ b ∈ B, ∀ k ∈ K, b * k = k * b := by
  have hNK : ⁅K, B⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk b hb
    have h1 := hBK b hb k⁻¹ (K.inv_mem hk)
    have e : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
    show k * b * k⁻¹ * b⁻¹ ∈ K
    rw [e]
    exact K.mul_mem hk h1
  have hcomm_of_bot : ⁅K, B⁆ = ⊥ → ∀ b ∈ B, ∀ k ∈ K, b * k = k * b := by
    intro h b hb k hk
    have h1 : ⁅k, b⁆ ∈ ⁅K, B⁆ := Subgroup.commutator_mem_commutator hk hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rcases hK with hq | h3
  · by_cases hNe : ⁅K, B⁆ = K
    · exact Or.inl hNe
    · right
      apply hcomm_of_bot
      have hnle : ¬ K ≤ ⁅K, B⁆ := fun h => hNe (le_antisymm hNK h)
      have hLN : ∀ l ∈ K, ∀ n ∈ ⁅K, B⁆, l * n * l⁻¹ ∈ ⁅K, B⁆ := by
        intro l hl n hn
        have hn' : n ∈ ⁅B, K⁆ := by rw [Subgroup.commutator_comm]; exact hn
        have := conj_mem_commutator (H := B) (A := K) hl hn'
        rw [Subgroup.commutator_comm] at this
        exact this
      have hcomm := commute_of_normal_not_le hq
        (fun n hn l hl => K.mul_mem (K.mul_mem (hNK hn) hl) (K.inv_mem (hNK hn))) hLN hnle
      have hNc : ⁅K, B⁆ ≤ Subgroup.centralizer (K : Set Ω) := fun n hn =>
        Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn l hl).symm
      have hdouble : ⁅⁅K, B⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hNc
      have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
      exact CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K B hdouble
  · have hdvd : Nat.card ↥(⁅K, B⁆) ∣ 3 := by
      rw [← h3]
      exact Subgroup.card_dvd_of_le hNK
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · right
      exact hcomm_of_bot (Subgroup.eq_bot_of_card_eq _ h)
    · left
      exact Subgroup.eq_of_le_of_card_ge hNK (by rw [h, h3])

end Group

section Module

variable {V : Type*} [CommGroup V]

theorem commutator_autSub_eq [Finite V] {K A : Subgroup (MulAut V)} {U : Subgroup V}
    (hKU : K ≤ stabSub U) (hAU : A ≤ stabSub U) (hKA : ⁅K, A⁆ = K) :
    ⁅autSub K U, autSub A U⁆ = autSub K U := by
  have hAn : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun a ha k hk =>
    conj_mem_of_commutator_eq hKA ha hk
  apply le_antisymm
  · refine commutator_le_of_normalizes (le_normalizer_of_conj fun φ hφ ψ hψ => ?_)
    exact autSub_conj_mem hAn hφ hψ
  · intro φ hφ
    obtain ⟨k, hkK, rfl⟩ := mem_autSub.1 hφ
    have hk : (k : MulAut V) ∈ ⁅K, A⁆ := by rw [hKA]; exact hkK
    have key : ∀ x ∈ ⁅K, A⁆, ∃ hx : x ∈ stabSub U,
        resHom U ⟨x, hx⟩ ∈ ⁅autSub K U, autSub A U⁆ := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨k₁, hk₁, a₁, ha₁, rfl⟩ := hx
        have hk₁s : k₁ ∈ stabSub U := hKU hk₁
        have ha₁s : a₁ ∈ stabSub U := hAU ha₁
        have hx : ⁅k₁, a₁⁆ ∈ stabSub U :=
          (stabSub U).mul_mem ((stabSub U).mul_mem ((stabSub U).mul_mem hk₁s ha₁s)
            ((stabSub U).inv_mem hk₁s)) ((stabSub U).inv_mem ha₁s)
        refine ⟨hx, ?_⟩
        have e : resHom U ⟨⁅k₁, a₁⁆, hx⟩ = ⁅resHom U ⟨k₁, hk₁s⟩, resHom U ⟨a₁, ha₁s⟩⁆ := by
          rw [← map_commutatorElement]
          rfl
        rw [e]
        exact Subgroup.commutator_mem_commutator (mem_autSub.2 ⟨⟨k₁, hk₁s⟩, hk₁, rfl⟩)
          (mem_autSub.2 ⟨⟨a₁, ha₁s⟩, ha₁, rfl⟩)
      | one =>
        refine ⟨(stabSub U).one_mem, ?_⟩
        have : resHom U ⟨1, (stabSub U).one_mem⟩ = 1 := map_one _
        rw [this]
        exact Subgroup.one_mem _
      | mul x y hx' hy' ihx ihy =>
        obtain ⟨hxs, hxm⟩ := ihx
        obtain ⟨hys, hym⟩ := ihy
        refine ⟨(stabSub U).mul_mem hxs hys, ?_⟩
        have : resHom U ⟨x * y, (stabSub U).mul_mem hxs hys⟩ =
            resHom U ⟨x, hxs⟩ * resHom U ⟨y, hys⟩ :=
          map_mul (resHom U) (⟨x, hxs⟩ : stabSub U) ⟨y, hys⟩
        rw [this]
        exact Subgroup.mul_mem _ hxm hym
      | inv x hx' ih =>
        obtain ⟨hxs, hxm⟩ := ih
        refine ⟨(stabSub U).inv_mem hxs, ?_⟩
        have : resHom U ⟨x⁻¹, (stabSub U).inv_mem hxs⟩ = (resHom U ⟨x, hxs⟩)⁻¹ :=
          map_inv (resHom U) (⟨x, hxs⟩ : stabSub U)
        rw [this]
        exact Subgroup.inv_mem _ hxm
    obtain ⟨hx, h⟩ := key _ hk
    exact h

theorem le_fittingOf_of_nilpotent_normal [Finite V] {X N : Subgroup (MulAut V)} (hNX : N ≤ X)
    (hn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) [Group.IsNilpotent ↥N] : N ≤ fittingOf X := by
  have hnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hNX).2 fun n x hn' hx => hn x hx n hn'
  have hnil : Group.IsNilpotent ↥(N.subgroupOf X) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNX)).mpr inferInstance
  have h1 : N.subgroupOf X ≤ CFSG.fittingSubgroup ↥X := le_sSup ⟨hnorm, hnil⟩
  calc N = (N.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hNX).symm
    _ ≤ fittingOf X := Subgroup.map_mono h1

end Module

end B1Red

end CFSG.Quasithin
