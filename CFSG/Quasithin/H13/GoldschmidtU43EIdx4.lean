module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat4
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx1
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx2
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx3
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm7

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem Dbar_eq_centralizer_zbar :
    S.Dbar = Subgroup.centralizer ({S.zbar} : Set S.Nbar) := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdz : (d : G) * z = z * (d : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (S.Dg_le_Hz hd)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdz
  · exact fun x hx => S.centralizer_zbar_le hx

theorem ubar_mem_Dbar : S.ubar ∈ S.Dbar :=
  ⟨⟨(S.u : G), S.u_mem_Ng⟩, S.u_mem_Dg, rfl⟩

theorem vbar_mem_Dbar : S.vbar ∈ S.Dbar :=
  ⟨⟨(S.v : G), S.v_mem_Ng⟩, S.v_mem_Dg, rfl⟩

@[expose] noncomputable def DgEquivDbar : ↥S.Dg ≃* ↥S.Dbar :=
  MulEquiv.ofBijective
    ((S.piN.comp (Subgroup.inclusion S.Dg_le_Ng)).codRestrict S.Dbar fun d =>
      ⟨⟨(d : G), S.Dg_le_Ng d.2⟩, d.2, rfl⟩)
    ⟨fun a b hab => Subtype.ext (by
      have := S.piN_inj_on_Dg a.2 b.2 (congrArg Subtype.val hab)
      exact congrArg (fun x : ↥S.Ng => (x : G)) this),
      fun y => by
        obtain ⟨d, hd, hdy⟩ := y.2
        exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩⟩

theorem exists_dihedral_Dbar' : ∃ e : ↥S.Dbar ≃* DihedralGroup 4,
    e ⟨S.vbar, S.vbar_mem_Dbar⟩ = DihedralGroup.r 1 ∧
      e ⟨S.ubar, S.ubar_mem_Dbar⟩ = DihedralGroup.sr 0 := by
  obtain ⟨eD, hv, hu⟩ := S.exists_dihedral_Dg
  refine ⟨(eD.trans S.DgEquivDbar).symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have hvN : (⟨(eD (DihedralGroup.r 1) : G), S.Dg_le_Ng (eD (DihedralGroup.r 1)).2⟩ :
        ↥S.Ng) = ⟨(S.v : G), S.v_mem_Ng⟩ := Subtype.ext hv
    show S.vbar = S.piN ⟨(eD (DihedralGroup.r 1) : G), S.Dg_le_Ng (eD (DihedralGroup.r 1)).2⟩
    rw [hvN]
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have huN : (⟨(eD (DihedralGroup.sr 0) : G), S.Dg_le_Ng (eD (DihedralGroup.sr 0)).2⟩ :
        ↥S.Ng) = ⟨(S.u : G), S.u_mem_Ng⟩ := Subtype.ext hu
    show S.ubar = S.piN ⟨(eD (DihedralGroup.sr 0) : G), S.Dg_le_Ng (eD (DihedralGroup.sr 0)).2⟩
    rw [huN]

theorem zbar_mem_Dbar : S.zbar ∈ S.Dbar := ⟨⟨z, S.z_mem_Ng⟩, S.z_mem_Dg, rfl⟩

theorem eq_one_of_comm_zbar {x : S.Nbar} (hx : x * S.zbar = S.zbar * x) (h3 : x ^ 3 = 1) :
    x = 1 := by
  have hxD : x ∈ S.Dbar := by
    rw [S.Dbar_eq_centralizer_zbar]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hx
  have h8 : x ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥S.Dbar) (x := (⟨x, hxD⟩ : ↥S.Dbar))
    rw [S.card_Dbar] at this
    exact congrArg Subtype.val this
  have h1 : x ^ Nat.gcd 8 3 = 1 := pow_gcd_eq_one.mpr ⟨h8, h3⟩
  have h2 : Nat.gcd 8 3 = 1 := by decide
  rw [h2, pow_one] at h1
  exact h1

theorem exists_nu_of_index_two {J : Subgroup S.Nbar} (hJ : J.index = 2) :
    ∃ ν : S.Nbar, ν ^ 3 = 1 ∧ ν ≠ 1 ∧
      ((ν * S.zbar = S.ubar * ν ∧ ν * S.ubar = (S.zbar * S.ubar) * ν) ∨
       (ν * S.zbar = (S.ubar * S.vbar) * ν ∧
          ν * (S.ubar * S.vbar) = (S.zbar * (S.ubar * S.vbar)) * ν)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, hev, heu⟩ := S.exists_dihedral_Dbar'
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ
  obtain ⟨h8, h16⟩ := S.two_part_Nbar
  obtain ⟨m, hm⟩ := h8
  have hmodd : Odd m := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
    · exfalso
      apply h16
      exact ⟨k, by rw [hm, hk]; ring⟩
    · exact hodd
  have hJcard : Nat.card J = 4 * m := by
    have := Subgroup.card_mul_index J
    rw [hJ, hm] at this
    omega
  have hDJ : ¬ S.Dbar ≤ J := by
    intro hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [S.card_Dbar, hJcard] at h1
    obtain ⟨k, hk⟩ := h1
    have : Even m := ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hmodd) this
  have hrel : J.relIndex S.Dbar = 2 := by
    have hdvd : J.relIndex S.Dbar ∣ J.index := Subgroup.relIndex_dvd_index_of_normal J S.Dbar
    rw [hJ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hDJ
    · exact h
  have hQcard : Nat.card ↥(J ⊓ S.Dbar) = 4 := by
    have := Subgroup.relIndex_mul_card J S.Dbar
    rw [hrel, S.card_Dbar] at this
    omega
  set Q : Subgroup S.Nbar := J ⊓ S.Dbar with hQ
  have hQJ : Q ≤ J := inf_le_left
  have hQD : Q ≤ S.Dbar := inf_le_right
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have hc : IsMulCommutative ↥Q :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQcard]; norm_num)
    intro a ha b hb
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : ↥Q) ⟨b, hb⟩)
  have hzJ : S.zbar ∈ J := by
    have := Subgroup.mul_self_mem_of_index_two hJ S.vbar
    rwa [S.vbar_sq] at this
  have hzQ : S.zbar ∈ Q := ⟨hzJ, S.zbar_mem_Dbar⟩
  have hQ''card : Nat.card (Q.subgroupOf J) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQcard]
  have hab'' : ∀ a ∈ Q.subgroupOf J, ∀ b ∈ Q.subgroupOf J, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hQab _ ha _ hb)
  have hC'' : ∀ x : ↥J, (∀ q ∈ Q.subgroupOf J, x * q = q * x) → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hxz : (x : S.Nbar) * S.zbar = S.zbar * x :=
      congrArg Subtype.val (hx ⟨S.zbar, hzJ⟩ hzQ)
    have hxD : (x : S.Nbar) ∈ S.Dbar := by
      rw [S.Dbar_eq_centralizer_zbar]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
    refine ⟨3, ?_⟩
    have h8 := pow_card_eq_one' (G := ↥S.Dbar) (x := (⟨x, hxD⟩ : ↥S.Dbar))
    rw [S.card_Dbar] at h8
    have h8' : (x : S.Nbar) ^ 8 = 1 := congrArg (fun t : ↥S.Dbar => (t : S.Nbar)) h8
    apply Subtype.ext
    show (x : S.Nbar) ^ 8 = 1
    exact h8'
  have hNC'' : ¬ CFSG.HasNormalPComplement 2 ↥J := by
    intro h
    apply S.not_hasNormalPComplement_Nbar
    have h2 : IsPGroup 2 S.Nbar := u43_isPGroup_two_of_complement S.oddCore_Nbar hJ h
    exact ⟨⊥, inferInstance, by simp, h2.of_equiv QuotientGroup.quotientBot.symm⟩
  obtain ⟨y, hyN, hy3⟩ := u43_exists_order_three hNC'' hQ''card hab'' hmodd hJcard hC''
  have hν3 : (y : S.Nbar) ^ 3 = 1 := by
    have : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    exact congrArg Subtype.val this
  have hν1 : (y : S.Nbar) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  have hνQ : ∀ q ∈ Q, (y : S.Nbar) * q * (y : S.Nbar)⁻¹ ∈ Q := by
    intro q hq
    have hq' : (⟨q, hQJ hq⟩ : ↥J) ∈ Q.subgroupOf J := Subgroup.mem_subgroupOf.mpr hq
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mp hq')
  have hmove : ¬ ((y : S.Nbar) * S.zbar = S.zbar * (y : S.Nbar)) :=
    fun h => hν1 (S.eq_one_of_comm_zbar h hν3)
  have hui : S.ubar⁻¹ = S.ubar := inv_eq_of_mul_eq_one_right S.ubar_sq
  have hzi : S.zbar⁻¹ = S.zbar := inv_eq_of_mul_eq_one_right S.zbar_sq
  set c : S.Nbar := (y : S.Nbar) * S.zbar * (y : S.Nbar)⁻¹ with hc
  have hcQ : c ∈ Q := hνQ _ hzQ
  have hcD : c ∈ S.Dbar := hQD hcQ
  have hcc : c * c = 1 := by
    calc c * c = (y : S.Nbar) * (S.zbar * S.zbar) * (y : S.Nbar)⁻¹ := by rw [hc]; group
      _ = 1 := by rw [S.zbar_sq]; group
  have hc1 : c ≠ 1 := by
    intro h
    apply S.zbar_ne_one
    have : (y : S.Nbar)⁻¹ * c * (y : S.Nbar) = S.zbar := by rw [hc]; group
    rw [h] at this
    simpa using this.symm
  have hcz : c ≠ S.zbar := fun h => hmove (by
    rw [hc, mul_inv_eq_iff_eq_mul] at h
    exact h)
  have hez : e ⟨S.zbar, S.zbar_mem_Dbar⟩ = DihedralGroup.r 2 := by
    have : (⟨S.zbar, S.zbar_mem_Dbar⟩ : ↥S.Dbar) =
        ⟨S.vbar, S.vbar_mem_Dbar⟩ * ⟨S.vbar, S.vbar_mem_Dbar⟩ := Subtype.ext S.vbar_sq.symm
    rw [this, map_mul, hev]
    decide
  have hec : e ⟨c, hcD⟩ * e ⟨c, hcD⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hcc
  have hec1 : e ⟨c, hcD⟩ ≠ 1 := fun h => hc1 (congrArg Subtype.val
    (e.injective (h.trans (map_one e).symm)))
  have hec2 : e ⟨c, hcD⟩ ≠ DihedralGroup.r 2 := fun h => hcz (congrArg Subtype.val
    (e.injective (h.trans hez.symm)))
  have hcases := D8_noncentral _ hec hec1 hec2
  have hubD : (S.ubar * S.vbar) ∈ S.Dbar := mul_mem S.ubar_mem_Dbar S.vbar_mem_Dbar
  have hzD : S.zbar ∈ S.Dbar := S.zbar_mem_Dbar
  have main : ∀ w : S.Nbar, (w = S.ubar ∨ w = S.ubar * S.vbar) → (c = w ∨ c = S.zbar * w) →
      ∃ ν : S.Nbar, ν ^ 3 = 1 ∧ ν ≠ 1 ∧ ν * S.zbar = w * ν ∧ ν * w = (S.zbar * w) * ν := by
    intro w hw hcw
    have hwD : w ∈ S.Dbar := by
      rcases hw with rfl | rfl
      · exact S.ubar_mem_Dbar
      · exact hubD
    have hww : w * w = 1 := by
      rcases hw with rfl | rfl
      · exact S.ubar_sq
      · calc S.ubar * S.vbar * (S.ubar * S.vbar)
            = (S.ubar * S.vbar * S.ubar⁻¹) * S.vbar := by rw [hui]; group
          _ = 1 := by rw [S.ubar_vbar]; group
    have hew : e ⟨w, hwD⟩ = DihedralGroup.sr 0 ∨
        e ⟨w, hwD⟩ = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
      rcases hw with rfl | rfl
      · exact Or.inl heu
      · right
        have : (⟨S.ubar * S.vbar, hwD⟩ : ↥S.Dbar) =
            ⟨S.ubar, S.ubar_mem_Dbar⟩ * ⟨S.vbar, S.vbar_mem_Dbar⟩ := rfl
        rw [this, map_mul, heu, hev]
    have hwz : w * S.zbar = S.zbar * w := by
      have := hwD
      rw [S.Dbar_eq_centralizer_zbar] at this
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    have hwne1 : w ≠ 1 := by
      intro h
      have h1 : e ⟨w, hwD⟩ = 1 := by
        have : (⟨w, hwD⟩ : ↥S.Dbar) = 1 := Subtype.ext h
        rw [this, map_one]
      rcases hew with h2 | h2
      · rw [h2] at h1
        exact absurd h1 (by decide)
      · rw [h2] at h1
        exact absurd h1 (by decide)
    have hzw : S.zbar ≠ w := by
      intro h
      have : (⟨w, hwD⟩ : ↥S.Dbar) = ⟨S.zbar, hzD⟩ := Subtype.ext h.symm
      have h2 : e ⟨w, hwD⟩ = DihedralGroup.r 2 := by rw [this]; exact hez
      rcases hew with h3 | h3
      · rw [h2] at h3
        exact absurd h3 (by decide)
      · rw [h2] at h3
        exact absurd h3 (by decide)
    have hwQ : w ∈ Q := by
      rcases hcw with h | h
      · rw [← h]; exact hcQ
      · have : w = S.zbar * c := by rw [h, ← mul_assoc, S.zbar_sq, one_mul]
        rw [this]
        exact mul_mem hzQ hcQ
    have hdQ : (y : S.Nbar) * w * (y : S.Nbar)⁻¹ ∈ Q := hνQ _ hwQ
    have hdD : (y : S.Nbar) * w * (y : S.Nbar)⁻¹ ∈ S.Dbar := hQD hdQ
    have hdc : ((y : S.Nbar) * w * (y : S.Nbar)⁻¹) * c = c * ((y : S.Nbar) * w * (y : S.Nbar)⁻¹) :=
      hQab _ hdQ _ hcQ
    have hd8 := D8_centralizer _ hec hec1 hec2 (e ⟨(y : S.Nbar) * w * (y : S.Nbar)⁻¹, hdD⟩) (by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdc)
    have hdlist : (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = 1 ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = S.zbar ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = c ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = S.zbar * c := by
      rcases hd8 with h | h | h | h
      · left
        exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      · right; left
        exact congrArg Subtype.val (e.injective (h.trans hez.symm))
      · right; right; left
        exact congrArg Subtype.val (e.injective h)
      · right; right; right
        have this : (⟨S.zbar * c, mul_mem hzD hcD⟩ : ↥S.Dbar) = ⟨S.zbar, hzD⟩ * ⟨c, hcD⟩ := rfl
        have himg : e ⟨S.zbar * c, mul_mem hzD hcD⟩ = DihedralGroup.r 2 * e ⟨c, hcD⟩ := by
          rw [this, map_mul, hez]
        exact congrArg Subtype.val (e.injective (h.trans himg.symm))
    have hyb : (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = 1 ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = S.zbar ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = w ∨
        (y : S.Nbar) * w * (y : S.Nbar)⁻¹ = S.zbar * w := by
      rcases hcw with h | h
      · rw [h] at hdlist
        exact hdlist
      · rw [h] at hdlist
        rcases hdlist with h' | h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [h', ← mul_assoc, S.zbar_sq, one_mul]
    have hya : (y : S.Nbar) * S.zbar * (y : S.Nbar)⁻¹ = 1 ∨
        (y : S.Nbar) * S.zbar * (y : S.Nbar)⁻¹ = S.zbar ∨
        (y : S.Nbar) * S.zbar * (y : S.Nbar)⁻¹ = w ∨
        (y : S.Nbar) * S.zbar * (y : S.Nbar)⁻¹ = S.zbar * w := by
      rcases hcw with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    obtain ⟨ν, hν, h1, h2⟩ := u43_cyc3 hwz.symm hzw S.zbar_ne_one hwne1 hν3 hν1 hya hyb
      (fun x hx h3 => S.eq_one_of_comm_zbar hx h3) S.zbar_sq hww hmove
    refine ⟨ν, ?_, ?_, h1, h2⟩
    · rcases hν with rfl | rfl
      · exact hν3
      · rw [inv_pow, hν3, inv_one]
    · rcases hν with rfl | rfl
      · exact hν1
      · exact inv_ne_one.mpr hν1
  rcases hcases with h | h | h | h
  · have hcu : c = S.ubar := congrArg Subtype.val (e.injective (h.trans heu.symm))
    obtain ⟨ν, h3, h1, h4, h5⟩ := main S.ubar (Or.inl rfl) (Or.inl hcu)
    exact ⟨ν, h3, h1, Or.inl ⟨h4, h5⟩⟩
  · have hcu : c = S.zbar * S.ubar := by
      have : (⟨S.zbar * S.ubar, mul_mem hzD S.ubar_mem_Dbar⟩ : ↥S.Dbar) =
          ⟨S.zbar, hzD⟩ * ⟨S.ubar, S.ubar_mem_Dbar⟩ := rfl
      have himg : e ⟨S.zbar * S.ubar, mul_mem hzD S.ubar_mem_Dbar⟩ =
          DihedralGroup.r 2 * DihedralGroup.sr 0 := by rw [this, map_mul, hez, heu]
      exact congrArg Subtype.val (e.injective (h.trans himg.symm))
    obtain ⟨ν, h3, h1, h4, h5⟩ := main S.ubar (Or.inl rfl) (Or.inr hcu)
    exact ⟨ν, h3, h1, Or.inl ⟨h4, h5⟩⟩
  · have hcu : c = S.ubar * S.vbar := by
      have : (⟨S.ubar * S.vbar, hubD⟩ : ↥S.Dbar) =
          ⟨S.ubar, S.ubar_mem_Dbar⟩ * ⟨S.vbar, S.vbar_mem_Dbar⟩ := rfl
      have himg : e ⟨S.ubar * S.vbar, hubD⟩ = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
        rw [this, map_mul, heu, hev]
      exact congrArg Subtype.val (e.injective (h.trans himg.symm))
    obtain ⟨ν, h3, h1, h4, h5⟩ := main (S.ubar * S.vbar) (Or.inr rfl) (Or.inl hcu)
    exact ⟨ν, h3, h1, Or.inr ⟨h4, h5⟩⟩
  · have hcu : c = S.zbar * (S.ubar * S.vbar) := by
      have : (⟨S.zbar * (S.ubar * S.vbar), mul_mem hzD hubD⟩ : ↥S.Dbar) =
          ⟨S.zbar, hzD⟩ * (⟨S.ubar, S.ubar_mem_Dbar⟩ * ⟨S.vbar, S.vbar_mem_Dbar⟩) := rfl
      have himg : e ⟨S.zbar * (S.ubar * S.vbar), mul_mem hzD hubD⟩ =
          DihedralGroup.r 2 * (DihedralGroup.sr 0 * DihedralGroup.r 1) := by
        rw [this, map_mul, map_mul, hez, heu, hev]
      exact congrArg Subtype.val (e.injective (h.trans himg.symm))
    obtain ⟨ν, h3, h1, h4, h5⟩ := main (S.ubar * S.vbar) (Or.inr rfl) (Or.inr hcu)
    exact ⟨ν, h3, h1, Or.inr ⟨h4, h5⟩⟩

end JWSetup

end CFSG.Quasithin.H13.U43
