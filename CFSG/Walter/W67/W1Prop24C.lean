module

public import CFSG.Walter.W67.W1Prop24B
public import CFSG.Walter.W67.CentralExt
import CFSG.Walter.W67.Lemma26i

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_card_seven {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 21) :
    ∃ P : Subgroup Q, P.Normal ∧ Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 Q) := inferInstance
  have hP : Nat.card (P : Subgroup Q) = 7 := by
    rw [Sylow.card_eq_multiplicity, hQ, show (21 : ℕ) = 7 * 3 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hidx : (P : Subgroup Q).index = 3 := by
    have := (P : Subgroup Q).card_mul_index
    rw [hP, hQ] at this
    omega
  have hmod := card_sylow_modEq_one 7 Q
  have hdvd : Nat.card (Sylow 7 Q) ∣ 3 := hidx ▸ P.card_dvd_index
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have : Subsingleton (Sylow 7 Q) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨P, Sylow.normal_of_subsingleton P, hP⟩
  · rw [h3] at hmod
    exact absurd hmod (by decide)

theorem not_sq_dvd_168 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 168 := by
  intro hdvd
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p <;> (revert hp hp2 hdvd; norm_num)

theorem isMulCommutative_of_sq_not_dvd_index {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {Z : Subgroup X} (hZ : Z ≤ Subgroup.center X) (hidx : ¬ p ^ 2 ∣ Z.index)
    {P : Subgroup X} (hP : IsPGroup p P) : IsMulCommutative P := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  set φ := (QuotientGroup.mk' Z).comp P.subtype
  have hR : φ.range = P.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hRp : IsPGroup p φ.range := hR ▸ hP.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
  have hdvd : Nat.card φ.range ∣ Z.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    apply hidx
    refine dvd_trans ?_ (hk ▸ hdvd)
    exact pow_dvd_pow p (by omega)
  have : IsCyclic φ.range := by
    apply isCyclic_of_card_dvd_prime (p := p)
    rw [hk]
    calc p ^ k ∣ p ^ 1 := pow_dvd_pow p hk1
      _ = p := pow_one p
  have hker : φ.rangeRestrict.ker ≤ Subgroup.center P := by
    intro z hz
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ hz) y)
  exact φ.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_yData_of_normal
    (hq : h.q = 3) (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) = ⊤) :
    fr.E ≤ CFSG.pPrimeCore 2 G ∧ Nat.card G = 168 * Nat.card (CFSG.pPrimeCore 2 G) ∧
      ∃ Y : Subgroup G, fr.YData Y ∧ Nat.card Y = 56 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 G with hOdef
  have hO : Odd (Nat.card O) := odd_card_pPrimeCore G
  have hSn : (fr.S : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hEn : fr.E.Normal := ⟨fun x hx g => fr.conj_mem_E (hN ▸ Subgroup.mem_top g) hx⟩
  have hEO : fr.E ≤ O := le_sSup ⟨hEn, Nat.coprime_two_left.mpr fr.odd_card_E⟩
  have hEeq : fr.E = O := le_antisymm hEO (fr.pPrimeCore_le_E_of_three hq hidx)
  have hCS : Nat.card fr.CS = 8 * Nat.card O := by
    obtain ⟨hsup, hdisj, hcomm⟩ := fr.isInternalDirectProduct_CS.1
    have hc : ∀ x ∈ (fr.S : Subgroup G), ∀ y ∈ fr.E, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hcomm hx) y hy).symm
    obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
    rw [hsup, hdisj.eq_bot, Subgroup.card_bot, mul_one, fr.card_S, hEeq] at h1
    exact h1
  have hidx21 : fr.CS.index = 21 := by
    have := fr.index_CS_normalizer_S hidx
    rw [hN] at this
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  have hG : Nat.card G = 168 * Nat.card O := by
    have := fr.CS.card_mul_index
    rw [hCS, hidx21] at this
    rw [← this]
    ring
  refine ⟨hEO, hG, ?_⟩
  set π := QuotientGroup.mk' fr.CS
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hQ : Nat.card (G ⧸ fr.CS) = 21 := by rw [← Subgroup.index_eq_card, hidx21]
  obtain ⟨P, hPn, hP7⟩ := exists_normal_card_seven hQ
  set W := P.comap π
  have hWidx : W.index = 3 := by
    rw [Subgroup.index_comap_of_surjective P hπ]
    have := P.card_mul_index
    rw [hP7, hQ] at this
    omega
  have hCSW : fr.CS ≤ W := fun x hx => by
    change π x ∈ P
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact P.one_mem
  have hW : Nat.card W = 56 * Nat.card O := by
    have := W.card_mul_index
    rw [hWidx, hG] at this
    omega
  have hcommW : commutator G ≤ W := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic (G ⧸ W) :=
      isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index_eq_card, hWidx])
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' W)
    rwa [QuotientGroup.ker_mk'] at this
  have hPmem : ∀ x : G, x ∈ commutator G → π x ∈ P := fun x hx => hcommW hx
  set X := Subgroup.centralizer (O : Set G)
  set Y := ⁅X, X⁆
  have hYn : Y.Normal := Subgroup.commutator_normal X X
  have hYX : Y ≤ X := Subgroup.commutator_le_left X X
  have hYcomm : Y ≤ commutator G := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hKX : h.K ≤ X :=
    Subgroup.le_centralizer_iff.mp (fr.pPrimeCore_le_centralizer_K_of_three hq hidx)
  have hSX : (fr.S : Subgroup G) ≤ X :=
    Subgroup.le_centralizer_iff.mp (fr.pPrimeCore_le_CS_of_three hq hidx)
  have hYO : Y ⊓ O = ⊥ := by
    set Z : Subgroup X := O.subgroupOf X
    have hZc : Z ≤ Subgroup.center X := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 z hz).symm
    have hOidx : O.index = 168 := by
      have := O.card_mul_index
      rw [hG] at this
      have hpos : 0 < Nat.card O := Nat.card_pos
      nlinarith
    have hZidx : Z.index ∣ 168 := by
      have := Subgroup.relIndex_dvd_index_of_normal (H := O) (K := X)
      rw [hOidx] at this
      exact this
    have hZcard : Nat.card Z = Nat.card (O ⊓ X : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
    have hab : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z →
        ∃ (_ : Fact p.Prime) (P : Sylow p X), IsMulCommutative (P : Subgroup X) := by
      intro p hp hpZ
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨Q⟩ : Nonempty (Sylow p X) := inferInstance
      refine ⟨this, Q, isMulCommutative_of_sq_not_dvd_index hZc ?_ Q.isPGroup'⟩
      have hpO : p ∣ Nat.card O := by
        refine hpZ.trans ?_
        rw [hZcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hpO)
      exact fun h2 => not_sq_dvd_168 hp hp2 (h2.trans hZidx)
    have hZD := inf_commutator_eq_bot hZc hab
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyO⟩
    have hyY' : y ∈ (commutator X).map X.subtype := by
      rw [Subgroup.map_subtype_commutator]; exact hyY
    obtain ⟨x, hx, rfl⟩ := hyY'
    have hxZ : x ∈ Z ⊓ commutator X := ⟨hyO, hx⟩
    rw [hZD, Subgroup.mem_bot] at hxZ
    rw [hxZ]
    exact Subgroup.one_mem _
  have hY56 : Nat.card Y ∣ 56 := by
    have hc : ∀ x ∈ Y, ∀ y ∈ O, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hYX hx) y hy).symm
    obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute Y O hc
    rw [hYO, Subgroup.card_bot, mul_one] at h1
    have hle : Y ⊔ O ≤ W :=
      sup_le (hYcomm.trans hcommW) ((fr.pPrimeCore_le_CS_of_three hq hidx).trans hCSW)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [h1, hW] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd
  obtain ⟨k, hkK, hk3, hkfix⟩ := fr.exists_three hq
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ fr.T, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : fr.T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 : Nat.card fr.T = 4 := fr.card_T
    rw [this, Subgroup.card_bot] at h4
    omega
  have hkS : k ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) :=
    fr.K_le_normalizer_S_of_three hq hkK
  have hSY : (fr.S : Subgroup G) ≤ Y := by
    set s₀ := k * t * k⁻¹ * t⁻¹
    have hs₀Y : s₀ ∈ Y := by
      have := Subgroup.commutator_mem_commutator (hKX hkK) (hSX (fr.T_le_S htT))
      rwa [commutatorElement_def] at this
    have hs₀S : s₀ ∈ (fr.S : Subgroup G) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hkS t).mp (fr.T_le_S htT))
        (inv_mem (fr.T_le_S htT))
    have hs₀1 : s₀ ≠ 1 := fun h1 => ht1 (hkfix t htT (by
      calc k * t = s₀ * (t * k) := by simp only [s₀]; group
        _ = t * k := by rw [h1, one_mul]))
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1]; exact one_mem _
    obtain ⟨n, -, hn⟩ := fr.exists_conj_of_mem_S hidx hs₀S hs₀1 hs hs1
    rw [← hn]
    exact hYn.conj_mem _ hs₀Y n
  have hkCS : k ∉ fr.CS := fun hk => ht1 (hkfix t htT
    (Subgroup.mem_centralizer_iff.mp hk t (fr.T_le_S htT)).symm)
  have hk3' : orderOf (π k) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hk3, pow_orderOf_eq_one, map_one]
    · intro h1
      exact hkCS ((QuotientGroup.eq_one_iff k).mp h1)
  obtain ⟨n, hn⟩ : ∃ n : G, n * k * n⁻¹ * k⁻¹ ∉ fr.CS := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, -, hn⟩ := fr.exists_conj_of_mem_S hidx fr.J_mem h.J_ne_one (fr.T_le_S htT) ht1
    apply ht1
    apply hkfix t htT
    set c := n⁻¹ * k * n⁻¹⁻¹ * k⁻¹
    have hc : c ∈ fr.CS := hcon n⁻¹
    have hcJ : c * h.J = h.J * c := (Subgroup.mem_centralizer_iff.mp hc h.J fr.J_mem).symm
    have hkJ : k * h.J = h.J * k := h.commute_J (h.K_le_H hkK)
    have hkn : n * (c * k) = k * n := by simp only [c]; group
    rw [← hn]
    calc k * (n * h.J * n⁻¹) = (n * (c * k)) * h.J * n⁻¹ := by rw [hkn]; group
      _ = n * (c * (k * h.J)) * n⁻¹ := by group
      _ = n * (c * (h.J * k)) * n⁻¹ := by rw [hkJ]
      _ = n * ((c * h.J) * k) * n⁻¹ := by group
      _ = n * ((h.J * c) * k) * n⁻¹ := by rw [hcJ]
      _ = (n * h.J * n⁻¹) * (n * (c * k) * n⁻¹) := by group
      _ = (n * h.J * n⁻¹) * k := by rw [hkn]; group
  set u := n * k * n⁻¹ * k⁻¹
  have huX : u ∈ X := mul_mem (Subgroup.Normal.conj_mem inferInstance k (hKX hkK) n)
    (inv_mem (hKX hkK))
  have hu1 : π u ≠ 1 := fun h1 => hn ((QuotientGroup.eq_one_iff u).mp h1)
  have hord7 : ∀ x : G, x ∈ commutator G → π x ≠ 1 → orderOf (π x) = 7 := by
    intro x hx hx1
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have h1 : orderOf (π x) ∣ 7 := by
      rw [← hP7]
      have := Subgroup.orderOf_dvd_natCard P (hPmem x hx)
      exact this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h1 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have hucomm : u ∈ commutator G := by
    rw [commutator_def]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top k)
    rwa [commutatorElement_def] at this
  have hu7 : orderOf (π u) = 7 := hord7 u hucomm hu1
  set v := u * k * u⁻¹ * k⁻¹
  have hvY : v ∈ Y := by
    have := Subgroup.commutator_mem_commutator huX (hKX hkK)
    rwa [commutatorElement_def] at this
  have hv1 : π v ≠ 1 := by
    intro h1
    have hcomm : π u * π k = π k * π u := by
      have : π v = π u * π k * (π u)⁻¹ * (π k)⁻¹ := by simp only [v, map_mul, map_inv]
      rw [this] at h1
      calc π u * π k = (π u * π k * (π u)⁻¹ * (π k)⁻¹) * (π k * π u) := by group
        _ = π k * π u := by rw [h1, one_mul]
    set C := Subgroup.centralizer ({π k} : Set (G ⧸ fr.CS))
    have huC : π u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hkC : π k ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have h21 : 21 ∣ Nat.card C := by
      have h7 : 7 ∣ Nat.card C := hu7 ▸ Subgroup.orderOf_dvd_natCard C huC
      have h3 : 3 ∣ Nat.card C := hk3' ▸ Subgroup.orderOf_dvd_natCard C hkC
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
    have hCtop : C = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      exact Nat.dvd_antisymm (hQ ▸ Subgroup.card_subgroup_dvd_card C) (hQ ▸ h21)
    have hnC : π n ∈ C := hCtop ▸ Subgroup.mem_top _
    have hnk := Subgroup.mem_centralizer_singleton_iff.mp hnC
    apply hu1
    simp only [u, map_mul, map_inv]
    rw [hnk]
    group
  have hvcomm : v ∈ commutator G := by
    rw [commutator_def]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top k)
    rwa [commutatorElement_def] at this
  have h7 : 7 ∣ Nat.card Y := by
    have h1 : orderOf (π v) ∣ orderOf v := orderOf_map_dvd π v
    rw [hord7 v hvcomm hv1] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard Y hvY)
  have h8 : 8 ∣ Nat.card Y := fr.card_S ▸ Subgroup.card_dvd_of_le hSY
  have hY : Nat.card Y = 56 :=
    Nat.dvd_antisymm hY56 (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h7)
  refine ⟨Y, ⟨hYn, hYO, hYX, hSY, ?_⟩, hY⟩
  rw [hN, inf_top_eq, hY]
  norm_num

end Frame

end CFSG.Walter.W67
