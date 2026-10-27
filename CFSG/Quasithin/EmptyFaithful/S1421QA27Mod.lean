module

public import CFSG.LargeExtraspecial.S63CD4A
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Gen

public section

namespace CFSG.Quasithin

namespace S1421QA27

open CFSG.LargeExtraspecial.S63 CFSG.Open CFSG.LieType.BorelTits Subgroup

theorem finite_trialityGroup8 : Finite ↥trialityGroup8 :=
  Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)

section Aux


theorem pCoreOf_centralizer_d4z_le :
    pCoreOf 2 (centralizer ({d4z} : Set ↥trialityGroup8)) ≤ d4Q := by
  have hfin := finite_trialityGroup8
  set P := centralizer ({d4z} : Set ↥trialityGroup8) with hP
  have hQP : d4Q ≤ P := d4Q_le_centralizer
  have hQ2 : IsPGroup 2 ↥d4Q := IsPGroup.of_card (n := 9) (by rw [card_d4Q]; norm_num)
  have hPQ : P ≤ normalizer (d4Q : Set ↥trialityGroup8) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    obtain ⟨q, hq, l, hl, rfl⟩ := exists_of_mem_centralizer_d4z hc
    constructor
    · intro hx
      have h1 := d4L_normalizes l hl x hx
      have e : q * l * x * (q * l)⁻¹ = q * (l * x * l⁻¹) * q⁻¹ := by group
      rw [e]
      exact d4Q.mul_mem (d4Q.mul_mem hq h1) (d4Q.inv_mem hq)
    · intro hx
      have h1 := d4L_normalizes l⁻¹ (d4L.inv_mem hl) (q⁻¹ * (q * l * x * (q * l)⁻¹) * q)
        (d4Q.mul_mem (d4Q.mul_mem (d4Q.inv_mem hq) hx) hq)
      have e : l⁻¹ * (q⁻¹ * (q * l * x * (q * l)⁻¹) * q) * l⁻¹⁻¹ = x := by group
      rwa [e] at h1
  have hQN : d4Q ≤ pCoreOf 2 P := le_pCoreOf_of_le_normalizer 2 hQP hPQ hQ2
  intro r hr
  have hrP : r ∈ P := pCoreOf_le 2 P hr
  obtain ⟨q, hq, l, hl, hrl⟩ := exists_of_mem_centralizer_d4z hrP
  have hlN : l ∈ pCoreOf 2 P := by
    have e : l = q⁻¹ * r := by rw [hrl]; group
    rw [e]
    exact (pCoreOf 2 P).mul_mem ((pCoreOf 2 P).inv_mem (hQN hq)) hr
  have hK : d4L ⊓ pCoreOf 2 P = ⊥ := by
    refine d4L_core _ inf_le_left (fun l' hl' k hk => ⟨?_, ?_⟩)
      ((pCoreOf_isPGroup 2 P).to_le inf_le_right)
    · exact d4L.mul_mem (d4L.mul_mem hl' hk.1) (d4L.inv_mem hl')
    · have hl'P : l' ∈ P := d4L_le_centralizer hl'
      exact (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P hl'P) k).mp hk.2
  have hl1 : l = 1 := by
    have : l ∈ d4L ⊓ pCoreOf 2 P := ⟨hl, hlN⟩
    rw [hK] at this
    exact mem_bot.mp this
  rw [hrl, hl1, mul_one]
  exact hq

theorem d4_irred_aux (K Q W : Subgroup ↥trialityGroup8) (hK : Nat.card ↥K = 258048)
    (hKz : ∀ k ∈ K, k * d4z = d4z * k) (hQK : Q ≤ K)
    (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hQ : Nat.card ↥Q = 512) (hzW : d4z ∈ W)
    (hWQ : W ≤ Q) (hW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) :
    W = zpowers d4z ∨ W = Q := by
  have hfin := finite_trialityGroup8
  set P := centralizer ({d4z} : Set ↥trialityGroup8) with hP
  have hKP : K ≤ P := fun k hk => mem_centralizer_singleton_iff.mpr (hKz k hk)
  have hKeq : K = P :=
    Subgroup.eq_of_le_of_card_ge hKP (by rw [hK]; exact card_centralizer_d4z_le)
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.of_card (n := 9) (by rw [hQ]; norm_num)
  have hQP : Q ≤ P := hKeq ▸ hQK
  have hPQ : P ≤ normalizer (Q : Set ↥trialityGroup8) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    have hcK : c ∈ K := hKeq ▸ hc
    constructor
    · exact fun hx => hQn c hcK x hx
    · intro hx
      have h1 := hQn c⁻¹ (K.inv_mem hcK) (c * x * c⁻¹) hx
      have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [e] at h1
  have hQN : Q ≤ pCoreOf 2 P := le_pCoreOf_of_le_normalizer 2 hQP hPQ hQ2
  have hQd : Q ≤ d4Q := hQN.trans pCoreOf_centralizer_d4z_le
  have hQeq : Q = d4Q := Subgroup.eq_of_le_of_card_ge hQd (by rw [hQ, card_d4Q])
  subst hQeq
  have hirr := d4Q_irred W hWQ (fun l hl m hm => hW l (hKeq ▸ d4L_le_centralizer hl) m hm) hzW
  by_cases hex : ∃ m ∈ W, m ≠ 1 ∧ m ≠ d4z
  · exact Or.inr (le_antisymm hWQ (hirr hex))
  · left
    push Not at hex
    ext m
    constructor
    · intro hm
      by_cases h1 : m = 1
      · rw [h1]; exact one_mem _
      · rw [hex m hm h1]; exact mem_zpowers d4z
    · intro hm
      exact (zpowers_le.mpr hzW) hm

end Aux

section Lift


theorem exists_iso_conj {Y : Type*} [Group Y] (e : Y ≃* ↥trialityGroup8) {z : Y}
    (hz : orderOf z = 2) : ∃ e' : Y ≃* ↥trialityGroup8, e' z = d4z ∨ e' z = d4t := by
  obtain ⟨c, hc⟩ := exists_conj_of_orderOf_eq_two (s := e z) (by rw [MulEquiv.orderOf_eq]; exact hz)
  refine ⟨e.trans (MulAut.conj c⁻¹), ?_⟩
  rcases hc with hc | hc
  · left
    show c⁻¹ * e z * c⁻¹⁻¹ = d4z
    rw [hc]; group
  · right
    show c⁻¹ * e z * c⁻¹⁻¹ = d4t
    rw [hc]; group

theorem d4_irred_of_card {Y : Type*} [Group Y] (e : Y ≃* ↥trialityGroup8) (K Q W : Subgroup Y)
    (z : Y) (hz : orderOf z = 2) (hK : Nat.card ↥K = 258048) (hKz : ∀ k ∈ K, k * z = z * k)
    (hQK : Q ≤ K) (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hQ : Nat.card ↥Q = 512)
    (hzW : z ∈ W) (hWQ : W ≤ Q) (hW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) :
    W = zpowers z ∨ W = Q := by
  obtain ⟨e', he'⟩ := exists_iso_conj e hz
  have hinj : Function.Injective e'.toMonoidHom := e'.injective
  have hK' : Nat.card ↥(K.map e'.toMonoidHom) = 258048 := by
    rw [Subgroup.card_map_of_injective hinj]; exact hK
  have hKz' : ∀ k' ∈ K.map e'.toMonoidHom, k' * e' z = e' z * k' := by
    rintro _ ⟨k, hk, rfl⟩
    show e' k * e' z = e' z * e' k
    rw [← map_mul, ← map_mul, hKz k hk]
  rcases he' with he' | he'
  · have hz0 : ∀ k' ∈ K.map e'.toMonoidHom, k' * d4z = d4z * k' := he' ▸ hKz'
    have h := d4_irred_aux (K.map e'.toMonoidHom) (Q.map e'.toMonoidHom) (W.map e'.toMonoidHom)
      hK' hz0 (Subgroup.map_mono hQK)
      (by
        rintro _ ⟨k, hk, rfl⟩ _ ⟨q, hq, rfl⟩
        exact ⟨k * q * k⁻¹, hQn k hk q hq, by simp⟩)
      (by rw [Subgroup.card_map_of_injective hinj]; exact hQ)
      ⟨z, hzW, he'⟩ (Subgroup.map_mono hWQ)
      (by
        rintro _ ⟨k, hk, rfl⟩ _ ⟨w, hw, rfl⟩
        exact ⟨k * w * k⁻¹, hW k hk w hw, by simp⟩)
    rcases h with h | h
    · left
      have h2 : (zpowers z).map e'.toMonoidHom = zpowers (e' z) :=
        MonoidHom.map_zpowers e'.toMonoidHom z
      rw [← he'] at h
      exact Subgroup.map_injective hinj (h.trans h2.symm)
    · right
      exact Subgroup.map_injective hinj h
  · exfalso
    have hle : K.map e'.toMonoidHom ≤ centralizer ({d4t} : Set ↥trialityGroup8) := by
      intro k' hk'
      exact mem_centralizer_singleton_iff.mpr (he' ▸ hKz' k' hk')
    have hfin := finite_trialityGroup8
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_centralizer_d4t_le
    omega

end Lift

theorem d4_irred_of_lieModel
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y CFSG.Assembly.LowTwoRank.StatedLieTag.trialityD4 0 2 1)
    (K Q W : Subgroup Y) (z : Y) (hz : orderOf z = 2) (hK : Nat.card ↥K = 258048)
    (hKz : ∀ k ∈ K, k * z = z * k) (hQK : Q ≤ K)
    (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hQ : Nat.card ↥Q = 512) (hzW : z ∈ W)
    (hWQ : W ≤ Q) (hW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) : W = zpowers z ∨ W = Q := by
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 Y hY
  exact d4_irred_of_card e K Q W z hz hK hKz hQK hQn hQ hzW hWQ hW

theorem irredModel_of_lieModel
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y CFSG.Assembly.LowTwoRank.StatedLieTag.trialityD4 0 2 1) :
    IrredModel Y 258048 512 :=
  fun K Q W z hz hK hKz hQK hQn hQ hzW hWQ hW =>
    d4_irred_of_lieModel hY K Q W z hz hK hKz hQK hQn hQ hzW hWQ hW

end S1421QA27

end CFSG.Quasithin
