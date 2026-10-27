module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item812Res3 (IsMaxPSub)

namespace Item812Res4

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {a : G} {X Y P Q R Pa : Subgroup G}

theorem mem_normalizer_zpowers_of_conj {h : G} {k : ℤ} (hk : h * a * h⁻¹ = a ^ k) :
    h ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.zpowers a).map (MulAut.conj h).toMonoidHom ≤ Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    change h * a * h⁻¹ ∈ Subgroup.zpowers a
    rw [hk]
    exact Subgroup.zpow_mem_zpowers a k
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective])

theorem normalizer_q_of (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    ∀ g ∈ Subgroup.normalizer (Q : Set G), ∃ r ∈ R,
      ∃ k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G), g = r * k := by
  intro g hg
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hgaQ : g * a * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg a).mp (a_mem_q hc)
  have hgaA : g * a * g⁻¹ ∈ A := hc.omega_q _ hgaQ (by rw [conj_pow, ha3]; group)
  have hgaB : g * a * g⁻¹ ∉ sec8B A X := by
    intro hB
    have hle : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q := by
      rintro _ ⟨r, hr, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) r).mp (r_le_q hc hr)
      simpa using this
    have heq := hc.r_weak g⁻¹ hle
    apply hc.a_not_mem_r
    rw [← heq]
    exact ⟨g * a * g⁻¹, hc.b_le_r hB, by simp [mul_assoc]⟩
  obtain ⟨r, hr, k, hrk⟩ := exists_conj_eq_zpow hW hY hc hAab haA ha1 hA81 hYa hgaA hgaB
  refine ⟨r, hr, r⁻¹ * g, mem_normalizer_zpowers_of_conj (k := k) ?_, by group⟩
  calc r⁻¹ * g * a * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * a * g⁻¹) * r := by group
    _ = r⁻¹ * (r * a ^ k * r⁻¹) * r := by rw [hrk]
    _ = a ^ k := by group

theorem p_max_of (hc : Fin812Pre A a X Y P Q R Pa) (ha3 : a ^ 3 = 1)
    (hN : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∃ r ∈ R,
      ∃ k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G), g = r * k) :
    IsMaxPSub 3 P (Subgroup.normalizer (Q : Set G)) := by
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hc.p_eq]
    exact sup_le ((r_le_q hc).trans Subgroup.le_normalizer) hc.pa_le_normalizer
  refine ⟨hPQ, isPGroup_p hc, fun S hS hPS hSQ => le_antisymm (fun s hs => ?_) hPS⟩
  obtain ⟨r, hr, k, hk, rfl⟩ := hN s (hSQ hs)
  have hrS : r ∈ S := hPS (r_le_p hc hr)
  have hkS : k ∈ S := by
    have : k = r⁻¹ * (r * k) := by group
    rw [this]
    exact S.mul_mem (S.inv_mem hrS) hs
  obtain ⟨m, hm⟩ := hS ⟨k, hkS⟩
  have hkm : k ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hka := commute_of_mem_normalizer_zpowers ha3 hkm hk
  have hSC : IsPGroup 3 (S ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    hS.to_le inf_le_left
  have heq := hc.pa_max.2.2 _ hSC (le_inf (hPS.trans' (pa_le_p hc)) hc.pa_max.1) inf_le_right
  have hkPa : k ∈ Pa := by
    rw [← heq]
    exact ⟨hkS, Subgroup.mem_centralizer_singleton_iff.mpr hka⟩
  exact P.mul_mem (r_le_p hc hr) (pa_le_p hc hkPa)

theorem j_eq_of (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    ∀ E : Subgroup G, E ≤ P → CFSG.Assembly.IsElemAbelian 3 E → Nat.card A ≤ Nat.card E →
      E = A := by
  intro E hEP hEab hcard
  by_cases hEQ : E ≤ Q
  · have hEA : E ≤ A := fun x hx => hc.omega_q x (hEQ hx) (hEab.2 x hx)
    exact Subgroup.eq_of_le_of_card_ge hEA hcard
  exfalso
  obtain ⟨e, heE, heQ⟩ := Set.not_subset.mp hEQ
  obtain ⟨r, hr, p, hp, rfl⟩ := exists_eq_mul_of_mem_p hc (hEP heE)
  obtain ⟨i, y, hy, hpy⟩ := exists_eq_zpow_mul_of_mem_pa hc hYa hp
  have hB27 := card_b hc hAab haA ha1 hA81
  have hBab := isElemAbelian_of_le hAab (b_le_a (A := A) (X := X))
  have hyB : y ∉ sec8B A X := by
    intro hyB
    apply heQ
    have hpA : p ∈ A := hpy ▸ A.mul_mem (A.zpow_mem haA i) (b_le_a hyB)
    exact Q.mul_mem (r_le_q hc hr) (hc.le_q hpA)
  have hD := card_inf_centralizer_le hW hY inf_le_right (isPGroup_pa_inf_y hc)
    (b_le_pa_inf_y hc) hBab hB27 hy hyB
  have hER : Nat.card (R ⊓ E : Subgroup G) ≤ 3 := by
    refine le_trans (Subgroup.card_le_of_le fun x hx => ?_) hD
    obtain ⟨hxR, hxE⟩ := Subgroup.mem_inf.mp hx
    have hxB : x ∈ sec8B A X := hc.omega_r x hxR (hEab.2 x hxE)
    refine Subgroup.mem_inf.mpr ⟨hxB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxe : x * (r * p) = (r * p) * x := congrArg Subtype.val
      (hEab.1.is_comm.comm ⟨x, hxE⟩ ⟨r * p, heE⟩)
    have hxr : x * r = r * x := hc.r_comm x hxR r hr
    have hxp : x * p = p * x := by
      calc x * p = r⁻¹ * ((x * r) * p) := by rw [hxr]; group
        _ = r⁻¹ * (x * (r * p)) := by group
        _ = r⁻¹ * (r * p * x) := by rw [hxe]
        _ = p * x := by group
    have hxa : x * a ^ i = a ^ i * x := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨x, b_le_a hxB⟩ ⟨a ^ i, A.zpow_mem haA i⟩)
    rw [hpy] at hxp
    calc x * y = (a ^ i)⁻¹ * (a ^ i * x) * y := by group
      _ = (a ^ i)⁻¹ * (x * a ^ i) * y := by rw [hxa]
      _ = (a ^ i)⁻¹ * (x * (a ^ i * y)) := by group
      _ = (a ^ i)⁻¹ * (a ^ i * y * x) := by rw [hxp]
      _ = y * x := by group
  have hP := card_p_mul_le hW hY hc hAab haA ha1 hA81 hYa
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := R) (B := E) (hEP.trans (p_le_normalizer_r hc))
  have h2 : Nat.card (R ⊔ E : Subgroup G) ≤ Nat.card P :=
    Subgroup.card_le_of_le (sup_le (r_le_p hc) hEP)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h3 : Nat.card R * Nat.card E ≤ Nat.card P * 3 := by
    rw [← h1]
    exact Nat.mul_le_mul h2 hER
  have h4 : Nat.card R * Nat.card E ≤ Nat.card R * 27 := by nlinarith
  have h5 : Nat.card E ≤ 27 := Nat.le_of_mul_le_mul_left h4 hRpos
  omega

theorem card_p_of (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (haY : a ∉ Y) :
    Nat.card P = 3 * Nat.card (R ⊔ (P ⊓ Y) : Subgroup G) := by
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hB27 := card_b hc hAab haA ha1 hA81
  have hPY : P ⊓ Y = Pa ⊓ Y :=
    le_antisymm (fun x hx => ⟨p_inf_y_le_pa hc hYa hx, hx.2⟩) (inf_le_inf_right Y (pa_le_p hc))
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (pa_le_normalizer_r hc)
  rw [hc.p_eq, r_inf_pa_eq hW hY hc hAab haA ha1 hA81 hYa, hB27] at h1
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := R) (B := P ⊓ Y) (inf_le_left.trans (p_le_normalizer_r hc))
  have hRPY : R ⊓ (P ⊓ Y) = sec8B A X := by
    refine le_antisymm (fun x hx => ?_) (le_inf hc.b_le_r (le_inf
      ((b_le_a.trans hc.le_pa).trans (pa_le_p hc)) (b_le_y hc)))
    rw [← r_inf_pa_eq hW hY hc hAab haA ha1 hA81 hYa]
    exact ⟨hx.1, p_inf_y_le_pa hc hYa hx.2⟩
  have hPYc : Nat.card (P ⊓ Y : Subgroup G) = Nat.card (Pa ⊓ Y : Subgroup G) := by rw [hPY]
  rw [hRPY, hB27, hPYc] at h2
  have hPa : Nat.card Pa = 3 * Nat.card (Pa ⊓ Y : Subgroup G) := by
    have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left
        (show Commute a v from (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm)
          j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hinf : Subgroup.zpowers a ⊓ (Pa ⊓ Y) = ⊥ := by
      have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
      have hdvd : Nat.card (Subgroup.zpowers a ⊓ (Pa ⊓ Y) : Subgroup G) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ (Pa ⊓ Y) ≤ _)
        rwa [Nat.card_zpowers, hao] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers a ⊓ (Pa ⊓ Y) = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
        have : a ∈ Subgroup.zpowers a ⊓ (Pa ⊓ Y) := by
          rw [heq]
          exact Subgroup.mem_zpowers a
        exact haY this.2.2
    rw [hc.pa_eq, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime ha3 ha1] at hcard
    exact hcard
  rw [hPa] at h1
  have h3 : Nat.card P * 27 = 3 * (Nat.card (R ⊔ (P ⊓ Y) : Subgroup G) * 27) := by
    rw [h1, h2]
    ring
  omega

end Item812Res4

section Final


open Item812Res4

@[expose] def Fin812PaSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa

@[expose] def Fin812BEq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n → sec8B A X = A ⊓ Y

@[expose] def Fin812QR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      ∃ R : Subgroup G, R ⊔ Subgroup.zpowers a = Q ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
        Nat.card R = 3 ^ 6 ∧ (∀ x ∈ R, x ^ 9 = 1) ∧ sec8B A X ≤ R ∧
        (∀ x ∈ R, x ^ 3 = 1 → x ∈ sec8B A X) ∧ (∀ x ∈ Q, x ^ 3 = 1 → x ∈ A) ∧
        ∀ g : G, R.map (MulAut.conj g).toMonoidHom ≤ Q →
          R.map (MulAut.conj g).toMonoidHom = R

@[expose] def Fin812BWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ g : G, (sec8B A X).map (MulAut.conj g).toMonoidHom ≤ A →
      (sec8B A X).map (MulAut.conj g).toMonoidHom = sec8B A X

theorem fin812Local_of (hS : Fin812PaSplit) (hBq : Fin812BEq) (hQR : Fin812QR)
    (hBw : Fin812BWeak) (hW : KF812WreathCent) : Fin812Local := by
  intro G _ _ A c L a b X Y n h
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have hA81 : Nat.card A = 81 := h.card_eq
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hY : IsYQuot Y := h.item89_Y
  have haY : a ∉ Y := not_mem_of_mem_thetaComponentsAt ha3 ha1 h.mem_thetaComponentsAt_Y hY
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  obtain ⟨Pa, hPa, hAPa⟩ := exists_isMaxPSub_le (isPGroup_of_isElemAbelian hAab) hAC
  have hpaeq := hS G A c L a b X Y n h Pa hPa hAPa
  have hBeq := hBq G A c L a b X Y n h
  have hB27 : Nat.card (sec8B A X) = 27 := by
    have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ sec8B A X, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact hAc _ (A.zpow_mem haA j) v (b_le_a hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hsup : Subgroup.zpowers a ⊔ (sec8B A X) = A := by
      refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr haA) b_le_a) fun x hx => ?_
      have hx' : x ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
        rw [hpaeq]
        exact hAPa hx
      have hcomm' : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
        intro u hu v hv
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact (Commute.zpow_left (show Commute a v from
          (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm) j).eq
      rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm').2] at hx'
      obtain ⟨u, hu, v, hv, huv⟩ := hx'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hvA : v ∈ A := by
        have : v = (a ^ j)⁻¹ * x := by rw [← huv]; group
        rw [this]
        exact A.mul_mem (A.inv_mem (A.zpow_mem haA j)) hx
      have hvB : v ∈ sec8B A X := by
        rw [hBeq]
        exact ⟨hvA, hv.2⟩
      rw [← huv]
      exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers a j) hvB
    have hinf : Subgroup.zpowers a ⊓ (sec8B A X) = ⊥ := by
      have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
      have hdvd : Nat.card (Subgroup.zpowers a ⊓ (sec8B A X) : Subgroup G) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ (sec8B A X) ≤ _)
        rwa [Nat.card_zpowers, hao] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers a ⊓ (sec8B A X) = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
        have haB : a ∈ sec8B A X := by
          have : a ∈ Subgroup.zpowers a ⊓ (sec8B A X) := by
            rw [heq]
            exact Subgroup.mem_zpowers a
          exact this.2
        rw [hBeq] at haB
        exact haY haB.2
    rw [hsup, hinf, Subgroup.card_bot, mul_one, hA81, Nat.card_zpowers,
      orderOf_eq_prime ha3 ha1] at hcard
    omega
  have hPaN : Pa ≤ Subgroup.normalizer ((sec8B A X) : Set G) := by
    have hBS : sec8B A X ≤ Pa ⊓ Y :=
      le_inf (b_le_a.trans hAPa) (by rw [hBeq]; exact inf_le_right)
    have hS81 : Nat.card (Pa ⊓ Y : Subgroup G) ≤ 3 * Nat.card (sec8B A X) := by
      rw [hB27]
      exact (card_le_of_le hY inf_le_right (hPa.2.1.to_le inf_le_left)).trans (by norm_num)
    have hSN : Pa ⊓ Y ≤ Subgroup.normalizer ((sec8B A X) : Set G) :=
      le_normalizer_of_card_le (hPa.2.1.to_le inf_le_left) hBS hS81
    intro p hp
    have hp' : p ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
      rw [hpaeq]
      exact hp
    have hcomm' : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (show Commute a v from
        (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm) j).eq
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm').2] at hp'
    obtain ⟨u, hu, v, hv, rfl⟩ := hp'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine Subgroup.mul_mem _ ?_ (hSN hv)
    exact Item812Res3.mem_normalizer_of_forall_commute fun x hx =>
      hAc _ (A.zpow_mem haA j) x (b_le_a hx)
  obtain ⟨Q, hQ, hPaQ⟩ := exists_isMaxPSub_normalized hPa.2.1
    (fun p hp => mem_normalizer_centralizer (hPaN hp))
  obtain ⟨R, hqeq, hrc, hcr, hrp, hbr, hor, hoq, hrw⟩ :=
    hQR G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hAQ : A ≤ Q := by
    have hAB : A ≤ Subgroup.centralizer ((sec8B A X) : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (b_le_a hy) x hx
    have hQA := hQ.2.2 _ (isPGroup_sup hQ.2.1 (isPGroup_of_isElemAbelian hAab)
      (hAPa.trans hPaQ)) le_sup_left (sup_le hQ.1 hAB)
    exact hQA ▸ le_sup_right
  have hanr : a ∉ R := fun haR => by
    have haB : a ∈ sec8B A X := hor a haR ha3
    rw [hBeq] at haB
    exact haY haB.2
  set P := R ⊔ Pa with hPdef
  have hpre : Fin812Pre A a X Y P Q R Pa :=
    ⟨hPa, hAPa, hpaeq, hBeq, hQ, hPaQ, hqeq, hrc, hcr, hrp, hbr, hor, hAQ, hoq, hanr, hrw, rfl⟩
  have hN := normalizer_q_of hW hY hpre hAab haA ha1 hA81 hYa
  exact ⟨P, Q, R, R ⊔ (P ⊓ Y), Pa,
    { pa_max := hPa
      le_pa := hAPa
      pa_eq := hpaeq
      sec8B_eq := hBeq
      q_max := hQ
      pa_le_normalizer := hPaQ
      q_eq := hqeq
      r_comm := hrc
      card_r := hcr
      r_pow := hrp
      b_le_r := hbr
      omega_r := hor
      le_q := hAQ
      omega_q := hoq
      a_not_mem_r := hanr
      r_weak := hrw
      normalizer_q := hN
      p_eq := rfl
      p_max := p_max_of hpre ha3 hN
      j_eq := j_eq_of hW hY hpre hAab haA ha1 hA81 hYa
      b_weak := hBw G A c L a b X Y n h
      v_eq := rfl
      card_p := card_p_of hW hY hpre hAab haA ha1 hA81 hYa haY }⟩

end Final

end CFSG.RankThree.PartTwo.Sec8
