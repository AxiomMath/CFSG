module

public import CFSG.Quasithin.Recognition.G23Ctx.Inversion
public import CFSG.Quasithin.Recognition.G23Ctx.Sylow
public import CFSG.GH74.QTGen4.Recog.G23.MLettersI

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Cfg (G : Type) [Group G] (T H H₁ H₂ M : Subgroup G) (z : G) : Prop where
  one : G23One H H₁ H₂
  two : G23Two M
  isZ : IsZ H₁ H₂ z
  sylow : quasithinIsSylowTwo T
  tH : T ≤ H
  tM : T ≤ M
  zV : z ∈ quasithinGenFitting M
  vK : quasithinGenFitting M ≤ H₁ ⊔ H₂
  inv₁ : ∀ w ∈ H, w ∉ H₁ ⊔ H₂ → Inverts H₁ w
  inv₂ : ∀ w ∈ H, w ∉ H₁ ⊔ H₂ → Inverts H₂ w

variable {T H H₁ H₂ M : Subgroup G} {z : G}

theorem Cfg.sylowH (c : Cfg G T H H₁ H₂ M z) :
    quasithinIsSylowTwo (T.subgroupOf H) :=
  sylow_subgroupOf c.tH c.sylow

theorem orderOf_dvd_card_mem {N : Subgroup G} {n : G} (hn : n ∈ N) :
    orderOf n ∣ Nat.card N := by
  have h := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
  rwa [Subgroup.orderOf_mk] at h

theorem eq_one_of_pow4_odd {N : Subgroup G} {c : G} (hc : c ∈ N) (hc4 : c ^ 4 = 1)
    (hodd : Odd (Nat.card N)) : c = 1 := by
  have h1 : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one hc4
  have h2 : orderOf c ∣ Nat.card N := orderOf_dvd_card_mem hc
  have h3 : Nat.Coprime 4 (Nat.card N) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  have h4 : orderOf c ∣ 1 := by
    have h5 := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one h3] at h5
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

theorem comm_pow4_of_odd (hH : G23One H H₁ H₂) {N : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hodd : Odd (Nat.card N)) {n : G} (hn : n ∈ N)
    {q : G} (hq : q ∈ H₁) (hq4 : q ^ 4 = 1) : n * q = q * n := by
  have hnH : n ∈ H := hNH hn
  have hqH : q ∈ H := hH.le_one hq
  have hqN : q * n⁻¹ * q⁻¹ ∈ N := hN q hqH n⁻¹ (N.inv_mem hn)
  have hcN : n * q * n⁻¹ * q⁻¹ ∈ N := by
    have h := N.mul_mem hn hqN
    simpa only [mul_assoc] using h
  have hQ : n * q * n⁻¹ ∈ dq1Sub hH.iso_one := mem_dq1Sub.mpr (conj_mem_pow4 hH hnH hq hq4)
  have hQi : q⁻¹ ∈ dq1Sub hH.iso_one := (dq1Sub hH.iso_one).inv_mem (mem_dq1Sub.mpr ⟨hq, hq4⟩)
  have hc4 : (n * q * n⁻¹ * q⁻¹) ^ 4 = 1 :=
    (mem_dq1Sub.mp ((dq1Sub hH.iso_one).mul_mem hQ hQi)).2
  have hc1 : n * q * n⁻¹ * q⁻¹ = 1 := eq_one_of_pow4_odd hcN hc4 hodd
  calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
    _ = 1 * (q * n) := by rw [hc1]
    _ = q * n := one_mul _

theorem Cfg.center_eq [Finite G] (c : Cfg G T H H₁ H₂ M z) :
    ∀ t ∈ T, (∀ s ∈ T, s * t = t * s) → t = 1 ∨ t = z := by
  intro t ht hcen
  have htH : t ∈ H := c.tH ht
  have hcommT : ∀ q ∈ T, t * q = q * t := fun q hq => (hcen q hq).symm
  have hK : t ∈ H₁ ⊔ H₂ := by
    by_contra hK
    rcases inner_or_inverts₁ c.one htH with hin | ⟨_, q, hqH₁, hq4, hq⟩
    · exact not_inner_of_inverts₁ c.one htH (c.inv₁ t htH hK) hin
    · have hqT : q ∈ T := pow4_mem_sylow c.one c.tH c.sylowH hqH₁ hq4
      apply hq
      rw [hcommT q hqT]
      exact mul_inv_cancel_right q t
  have hA : ∀ q ∈ H₁, q ^ 4 = 1 → t * q = q * t := fun q hq hq4 =>
    hcommT q (pow4_mem_sylow c.one c.tH c.sylowH hq hq4)
  have hB : ∀ q ∈ H₂, q ^ 4 = 1 → t * q = q * t := fun q hq hq4 =>
    hcommT q (pow4_mem_sylow (g23One_symm c.one) c.tH c.sylowH hq hq4)
  exact eq_of_centralizes c.one c.isZ hK hA hB

theorem Cfg.oddCore_H [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have hord : Odd (orderOf n) := Odd.of_dvd_nat hodd (orderOf_dvd_card_mem hn)
  have hnK : n ∈ H₁ ⊔ H₂ := mem_sup_of_odd c.one (hNH hn) hord (pow_orderOf_eq_one n)
  have h₁ : ∀ q ∈ H₁, q ^ 4 = 1 → n * q = q * n := fun q hq hq4 =>
    comm_pow4_of_odd c.one hNH hN hodd hn hq hq4
  have h₂ : ∀ q ∈ H₂, q ^ 4 = 1 → n * q = q * n := fun q hq hq4 =>
    comm_pow4_of_odd (g23One_symm c.one) hNH hN hodd hn hq hq4
  rcases eq_of_centralizes c.one c.isZ hnK h₁ h₂ with h | h
  · exact h
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hzN : z ∈ N := by
      rw [← h]
      exact hn
    have hordz : orderOf z = 2 := orderOf_eq_prime c.isZ.sq c.isZ.ne_one
    have hdz := orderOf_dvd_card_mem hzN
    rw [hordz] at hdz
    obtain ⟨k, hk⟩ := hodd
    omega

theorem Cfg.oddCore_G [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hNH : N ⊓ H = ⊥ := by
    refine c.oddCore_H inf_le_right (fun h hh n hn => ⟨hN.conj_mem n hn.1 h, ?_⟩) ?_
    · exact H.mul_mem (H.mul_mem hh hn.2) (H.inv_mem hh)
    · exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hfix : ∀ m : G, ∀ n ∈ N, (m * z * m⁻¹) * n * (m * z * m⁻¹)⁻¹ = n → n = 1 := by
    intro m n hn hfixn
    have hn' : m⁻¹ * n * m ∈ N := by
      have := hN.conj_mem n hn m⁻¹
      simpa using this
    have hc : (m⁻¹ * n * m) * z = z * (m⁻¹ * n * m) := by
      have h1 : z * (m⁻¹ * n * m) * z⁻¹ = m⁻¹ * n * m := by
        have : z * (m⁻¹ * n * m) * z⁻¹ = m⁻¹ * ((m * z * m⁻¹) * n * (m * z * m⁻¹)⁻¹) * m := by
          group
        rw [this, hfixn]
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hmem : m⁻¹ * n * m ∈ N ⊓ H := ⟨hn', mem_H_of_comm c.one c.isZ hc⟩
    rw [hNH, Subgroup.mem_bot] at hmem
    have : n = m * (m⁻¹ * n * m) * m⁻¹ := by group
    rw [this, hmem]; group
  obtain ⟨a, b, y, h, haV, hbV, ha1, haz, -⟩ := exists_basis_act c.two c.zV c.isZ.ne_one
  have ha2 : a * a = 1 := G23Two.sq_fitting c.two haV
  have hzz : z * z = 1 := c.isZ.mul_self
  have hzV := c.zV
  have hazV : a * z ∈ quasithinGenFitting M := (quasithinGenFitting M).mul_mem haV hzV
  have haz1 : a * z ≠ 1 := by
    intro h1
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact inv_eq_of_mul_eq_one_right hzz
  obtain ⟨m₁, -, hm₁⟩ := G23Two.exists_conj_eq c.two hzV c.isZ.ne_one haV ha1
  obtain ⟨m₂, -, hm₂⟩ := G23Two.exists_conj_eq c.two hzV c.isZ.ne_one hazV haz1
  have hnorm : ∀ t : G, ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun t n hn => hN.conj_mem n hn t
  have hz_inv : ∀ n ∈ N, z * n * z⁻¹ = n⁻¹ := by
    refine fpf_inverts (by simpa using hzz) (hnorm z) fun n hn hfn => ?_
    exact (hfix 1 n hn (by simpa using hfn))
  have ha_inv : ∀ n ∈ N, a * n * a⁻¹ = n⁻¹ := by
    have haa : a * a = 1 := ha2
    refine fpf_inverts haa (hnorm a) fun n hn hfn => ?_
    exact hfix m₁ n hn (by rw [hm₁]; exact hfn)
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have h1 : (a * z) * n * (a * z)⁻¹ = n := by
    have e : (a * z) * n * (a * z)⁻¹ = a * (z * n * z⁻¹) * a⁻¹ := by group
    rw [e, hz_inv n hn, ha_inv _ (N.inv_mem hn)]
    simp
  have hazaz : (a * z) * (a * z) = 1 := G23Two.sq_fitting c.two hazV
  have h2 : ∀ n ∈ N, (a * z) * n * (a * z)⁻¹ = n⁻¹ := by
    refine fpf_inverts hazaz (hnorm _) fun n hn hfn => ?_
    exact hfix m₂ n hn (by rw [hm₂]; exact hfn)
  have hnn : n * n = 1 := by
    have h3 : n = n⁻¹ := h1.symm.trans (h2 n hn)
    calc n * n = n * n⁻¹ := congrArg (n * ·) h3
      _ = 1 := mul_inv_cancel n
  have hord : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
  have hord2 : orderOf n ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  have h1' : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · exfalso
      rw [h] at hord2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hord2)
  exact orderOf_eq_one_iff.mp h1'

theorem Cfg.z_mem [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hN : N.Normal)
    (hN1 : N ≠ ⊥) : z ∈ N := by
  have heven : ¬ Odd (Nat.card N) := fun hodd => hN1 (c.oddCore_G hN hodd)
  obtain ⟨t, htN, ht1, ht2⟩ := exists_involution_of_even heven
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow c.sylow ht2
  have hgN : g * t * g⁻¹ ∈ N := hN.conj_mem t htN g
  have hP : N ⊓ T ≠ ⊥ := by
    intro h
    have hmem : g * t * g⁻¹ ∈ N ⊓ T := ⟨hgN, hg⟩
    rw [h, Subgroup.mem_bot] at hmem
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, hmem]; group
  obtain ⟨p, hp, hp1, hpc⟩ := exists_mem_center_of_normalizes c.sylow.1 hP inf_le_right
    (fun t ht p hp => ⟨hN.conj_mem p hp.1 t, T.mul_mem (T.mul_mem ht hp.2) (T.inv_mem ht)⟩)
  rcases c.center_eq p hp.2 hpc with h | h
  · exact absurd h hp1
  · rw [← h]; exact hp.1

theorem Cfg.fitting_le [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hN : N.Normal)
    (hzN : z ∈ N) : quasithinGenFitting M ≤ N := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]; exact N.one_mem
  · obtain ⟨m, -, hm⟩ := G23Two.exists_conj_eq c.two c.zV c.isZ.ne_one hv hv1
    rw [← hm]
    exact hN.conj_mem z hzN m

theorem Cfg.exists_conj_not_mem_fitting [Finite G] (c : Cfg G T H H₁ H₂ M z) :
    ∃ u ∈ quasithinGenFitting M, u ≠ 1 ∧ ∃ g : G, g * u * g⁻¹ ∈ T ∧
      g * u * g⁻¹ ∉ quasithinGenFitting M := by
  obtain ⟨a, _, _, _, haV, _, ha1, haz, -⟩ := exists_basis_act c.two c.zV c.isZ.ne_one
  have ha2 : a * a = 1 := G23Two.sq_fitting c.two haV
  obtain ⟨a₁, ha₁, a₂, ha₂, hae, ha₁4, ha₂4⟩ := split_invol c.one c.isZ (c.vK haV) ha2
  obtain ⟨ha₁1, ha₁z⟩ := comp_ne c.one c.isZ ha₂ hae ha₁ ha2 ha1 haz
  obtain ⟨k, hk, hk3, hk1⟩ := exists_order_three c.one
  have hkH : k ∈ H := c.one.le_one hk
  have hka₂ : k * a₂ = a₂ * k := G23One.comm_one_two c.one hk ha₂
  have hcon : k * a₂ * k⁻¹ = a₂ := by rw [hka₂, mul_inv_cancel_right]
  have hfac : k * (a₁ * a₂) * k⁻¹ = k * a₁ * k⁻¹ * a₂ := by
    calc k * (a₁ * a₂) * k⁻¹ = (k * a₁ * k⁻¹) * (k * a₂ * k⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = k * a₁ * k⁻¹ * a₂ := by rw [hcon]
  have hconj := conj_mem_pow4 c.one hkH ha₁ ha₁4
  refine ⟨a, haV, ha1, k, ?_, ?_⟩
  ·
    have hT₁ : k * a₁ * k⁻¹ ∈ T := pow4_mem_sylow c.one c.tH c.sylowH hconj.1 hconj.2
    have hT₂ : a₂ ∈ T := pow4_mem_sylow (g23One_symm c.one) c.tH c.sylowH ha₂ ha₂4
    rw [hae, hfac]
    exact T.mul_mem hT₁ hT₂
  ·
    intro hmem
    obtain ⟨t, ht_def⟩ : ∃ t, t = a₁⁻¹ * (k * a₁ * k⁻¹) := ⟨_, rfl⟩
    have hc' : k * a₁ * k⁻¹ = a₁ * t := by rw [ht_def, mul_inv_cancel_left]
    have htH : t ∈ H₁ := by
      rw [ht_def]
      exact H₁.mul_mem (H₁.inv_mem ha₁) hconj.1
    have hdc : t * a₂ = a₂ * t := G23One.comm_one_two c.one htH ha₂
    have hkak : k * a * k⁻¹ = a₁ * a₂ * t := by
      rw [hae, hfac, hc', mul_assoc a₁ t a₂, hdc, ← mul_assoc a₁ a₂ t]
    have hxe : a⁻¹ * (k * a * k⁻¹) = t := by
      rw [hkak, hae]
      exact inv_mul_cancel_left _ _
    have htV : t ∈ quasithinGenFitting M := by
      rw [← hxe]
      exact (quasithinGenFitting M).mul_mem ((quasithinGenFitting M).inv_mem haV) hmem
    have ht2 : t * t = 1 := G23Two.sq_fitting c.two htV
    have hz2 : (⟨z, c.isZ.mem_left⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using c.isZ.sq)
    have hz1 : (⟨z, c.isZ.mem_left⟩ : ↥H₁) ≠ 1 :=
      fun h => c.isZ.ne_one (congrArg Subtype.val h)
    have hk3' : (⟨k, hk⟩ : ↥H₁) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    have hk1' : (⟨k, hk⟩ : ↥H₁) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
    have ha₁4' : (⟨a₁, ha₁⟩ : ↥H₁) ^ 4 = 1 := Subtype.ext (by simpa using ha₁4)
    have ha₁1' : (⟨a₁, ha₁⟩ : ↥H₁) ≠ 1 := fun h => ha₁1 (congrArg Subtype.val h)
    have ha₁z' : (⟨a₁, ha₁⟩ : ↥H₁) ≠ ⟨z, c.isZ.mem_left⟩ :=
      fun h => ha₁z (congrArg Subtype.val h)
    have hfpf := sl23_order_three_fpf c.one.iso_one hz2 hz1 ⟨k, hk⟩ hk3' hk1' ⟨a₁, ha₁⟩
      ha₁4' ha₁1' ha₁z'
    rcases invol_mem_left c.one c.isZ htH ht2 with h | h
    · have h1 : k * a₁ * k⁻¹ = a₁ := by rw [hc', h, mul_one]
      exact hfpf.1 (Subtype.ext (by simpa using h1))
    · have h2 : k * a₁ * k⁻¹ = a₁ * z := by rw [hc', h]
      exact hfpf.2 (Subtype.ext (by simpa using h2))

theorem Cfg.M_le [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hN : N.Normal)
    (hzN : z ∈ N) : M ≤ N := by
  have hVN := c.fitting_le hN hzN
  obtain ⟨u, huV, hu1, g, hgT, hgV⟩ := c.exists_conj_not_mem_fitting
  haveI : IsSimpleGroup SL(3, ZMod 2) := isSimpleGroup_sl3
  exact le_of_surj_simple (g23QuotMap c.two) (g23QuotMap_surjective c.two) (g23QuotMap_ker c.two)
    hN hVN (c.tM hgT) (hN.conj_mem u (hVN huV) g) hgV

theorem factor_le_normal {X : Subgroup G} (hX : Nonempty (↥X ≃* SL(2, ZMod 3)))
    {N T : Subgroup G} (hN : N.Normal) (hQT : ∀ x ∈ X, x ^ 4 = 1 → x ∈ T) (hTN : T ≤ N)
    {w : G} (hwN : w ∈ N) (hinv : Inverts X w) (hwX : ∀ x ∈ X, w * x * w⁻¹ ∈ X) : X ≤ N := by
  intro x hx
  have hq : w * x * w⁻¹ * x ∈ N := hTN (hQT _ (X.mul_mem (hwX x hx) hx) (hinv x hx))
  have hc : x * w * x⁻¹ * w⁻¹ ∈ N := N.mul_mem (hN.conj_mem w hwN x) (N.inv_mem hwN)
  have hsq : x * x ∈ N := by
    have : x * x = (x * w * x⁻¹ * w⁻¹) * (w * x * w⁻¹ * x) := by group
    rw [this]; exact N.mul_mem hc hq
  have hcube : x ^ 3 ∈ N := hTN (hQT _ (X.pow_mem hx 3) (sl23_pow12 hX ⟨x, hx⟩ |> fun h => by
    simpa using congrArg Subtype.val h))
  have : x = (x * x) * (x * x) * (x ^ 3)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    group
  rw [this]
  exact N.mul_mem (N.mul_mem hsq hsq) (N.inv_mem hcube)

theorem Cfg.H_le [Finite G] (c : Cfg G T H H₁ H₂ M z) {N : Subgroup G} (hN : N.Normal)
    (hMN : M ≤ N) : H ≤ N := by
  have hTN : T ≤ N := c.tM.trans hMN
  obtain ⟨w, hwT, hwK⟩ := exists_mem_sylow_not_mem_sup c.one c.tH c.sylowH
  have hwN : w ∈ N := hTN hwT
  have hwH : w ∈ H := c.tH hwT
  have h₁ : H₁ ≤ N := factor_le_normal c.one.iso_one hN
    (fun x hx hx4 => pow4_mem_sylow c.one c.tH c.sylowH hx hx4) hTN hwN (c.inv₁ w hwH hwK)
    (fun x hx => (Subgroup.mem_normalizer_iff.mp (c.one.normal_one hwH) x).mp hx)
  have h₂ : H₂ ≤ N := factor_le_normal c.one.iso_two hN
    (fun x hx hx4 => pow4_mem_sylow (g23One_symm c.one) c.tH c.sylowH hx hx4) hTN hwN
    (c.inv₂ w hwH hwK)
    (fun x hx => (Subgroup.mem_normalizer_iff.mp (c.one.normal_two hwH) x).mp hx)
  intro y hy
  by_cases hyK : y ∈ H₁ ⊔ H₂
  · exact (sup_le h₁ h₂) hyK
  · have hk : y * w⁻¹ ∈ H₁ ⊔ H₂ := mul_inv_mem_sup c.one hy hwH hyK hwK
    have : y = (y * w⁻¹) * w := by group
    rw [this]
    exact N.mul_mem ((sup_le h₁ h₂) hk) hwN

theorem Cfg.isSimpleGroup [Finite G] (c : Cfg G T H H₁ H₂ M z) : IsSimpleGroup G := by
  haveI : Nontrivial G := ⟨⟨z, 1, c.isZ.ne_one⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  · right
    have hzN := c.z_mem hN hN1
    have hMN := c.M_le hN hzN
    have hHN := c.H_le hN hMN
    have hTN : T ≤ N := c.tM.trans hMN
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, hn, x, hx, rfl⟩ := frattini_sylow hN c.sylow hTN g
    exact N.mul_mem hn (hHN (normalizer_le_H c.one c.isZ c.tH c.sylowH hx))

end CFSG.Quasithin.G23Type.Ctx
