module

public import CFSG.Quasithin.Background.E2SeventeenSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

theorem eq_one_or_eq_of_card_eq_two {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ Z) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) (hb : b ∈ Z) :
    b = 1 ∨ b = a := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hle : Subgroup.zpowers a ≤ Z := Subgroup.zpowers_le.2 ha
  have hcard : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have heq : Subgroup.zpowers a = Z := Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcard])
  exact eq_one_or_eq_of_mem_zpowers ha2 (heq ▸ hb)

theorem conj_eq_of_card_eq_two {G : Type*} [Group G] {Z : Subgroup G} (hZ : Nat.card Z = 2)
    (hZ2 : ∀ a ∈ Z, a ^ 2 = 1) {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) {a : G}
    (ha : a ∈ Z) : g * a * g⁻¹ = a := by
  by_cases ha1 : a = 1
  · rw [ha1]
    group
  · have hga : g * a * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    rcases eq_one_or_eq_of_card_eq_two hZ ha ha1 (hZ2 a ha) hga with h | h
    · exfalso
      apply ha1
      have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [this, h]
      group
    · exact h

namespace DihedralPair

variable {G : Type*} [Group G] [Finite G] {H T V U : Subgroup G} {x z : G}

omit [Finite G] in
theorem ZC_mem (_d : DihedralPair H T V U x z) {ζ : G} (hζ : ζ ∈ dpZ V z) : ζ ∈ dpI V z :=
  Subgroup.mem_sup_left hζ.1

omit [Finite G] in
theorem conj_x (d : DihedralPair H T V U x z) {u : G} (hu : u ∈ U) :
    x * (z * u * z⁻¹) * x⁻¹ = z⁻¹ * u * z := by
  have hxu : x * u * x⁻¹ = u := by
    rw [isElemAbelian_comm d.elem d.xV (d.UV hu)]
    group
  have hxz' : x * z⁻¹ * x⁻¹ = z := by
    calc x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
      _ = z := by rw [d.xz, inv_inv]
  calc x * (z * u * z⁻¹) * x⁻¹ = (x * z * x⁻¹) * (x * u * x⁻¹) * (x * z⁻¹ * x⁻¹) := by group
    _ = z⁻¹ * u * z := by rw [d.xz, hxu, hxz']

theorem norm_mem (d : DihedralPair H T V U x z) (hz3 : orderOf z = 3) {u : G} (hu : u ∈ U) :
    u * (z * u * z⁻¹) * (z⁻¹ * u * z) ∈ dpZ V z := by
  obtain ⟨a, ha⟩ : ∃ a, a = z * u * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = z⁻¹ * u * z := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hzz : z * z = z⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, show z * z * z = z ^ 3 by rw [pow_three, mul_assoc]]
    exact hz3'
  have haA : a ∈ dpA H V U z := by
    rw [d.Aeq, mem_cjSub, ha]
    simpa [mul_assoc] using hu
  have huI : u ∈ dpI V z := Subgroup.mem_sup_left (d.UV hu)
  have haI : a ∈ dpI V z := (d.AR.trans inf_le_left) haA
  have hxa : x * a * x⁻¹ = b := by rw [ha, hb, d.conj_x hu]
  have hc : b * a⁻¹ ∈ U := by
    have h1 : x * a * x⁻¹ * a⁻¹ ∈ U := by
      have := Subgroup.commutator_mem_commutator d.xV haA
      rw [commutatorElement_def] at this
      exact d.comm1 this
    rwa [hxa] at h1
  obtain ⟨c, hcU, hcdef⟩ : ∃ c ∈ U, c = b * a⁻¹ := ⟨_, hc, rfl⟩
  have hbca : b = c * a := by rw [hcdef]; group
  have hzb : z * b * z⁻¹ = u := by rw [hb]; group
  have hza : z * a * z⁻¹ = b := by
    rw [ha, hb]
    calc z * (z * u * z⁻¹) * z⁻¹ = (z * z) * u * (z * z)⁻¹ := by group
      _ = z⁻¹ * u * z := by rw [hzz, inv_inv]
  have heA : z * c * z⁻¹ ∈ dpA H V U z := by
    rw [d.Aeq, mem_cjSub]
    simpa [mul_assoc] using hcU
  have hu' : u = (z * c * z⁻¹) * c * a := by
    calc u = z * b * z⁻¹ := hzb.symm
      _ = (z * c * z⁻¹) * (z * a * z⁻¹) := by rw [hbca]; group
      _ = (z * c * z⁻¹) * c * a := by rw [hza, hbca]; group
  have hcomm : c * a * c⁻¹ * a⁻¹ ∈ dpZ V z := by
    have := Subgroup.commutator_mem_commutator hcU haA
    rw [commutatorElement_def] at this
    exact d.comm2 this
  have hζA : u * c⁻¹ ∈ dpA H V U z := by
    have e : u * c⁻¹ = (z * c * z⁻¹) * (c * a * c⁻¹ * a⁻¹) * a := by
      rw [hu']
      group
    rw [e]
    exact (dpA H V U z).mul_mem ((dpA H V U z).mul_mem heA (d.ZA hcomm)) haA
  have hζ : u * c⁻¹ ∈ dpZ V z := by
    rw [← d.U_inf_A]
    exact ⟨U.mul_mem hu (U.inv_mem hcU), hζA⟩
  obtain ⟨ζ, hζZ, hζdef⟩ : ∃ ζ ∈ dpZ V z, ζ = u * c⁻¹ := ⟨_, hζ, rfl⟩
  have hcζ : c = ζ⁻¹ * u := by rw [hζdef]; group
  have hP : u * a ∈ dpP H V U z := (dpP H V U z).mul_mem (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right haA)
  have hsq := d.sq_mem_Z hP
  have hζc : ∀ y ∈ dpI V z, y * ζ⁻¹ = ζ⁻¹ * y := fun y hy =>
    d.ZC ζ⁻¹ ((dpZ V z).inv_mem hζZ) y hy
  have e2 : u * a * b = ζ⁻¹ * (u * a * (u * a)) := by
    calc u * a * b = u * a * (ζ⁻¹ * u * a) := by rw [hbca, hcζ]
      _ = (u * a) * ζ⁻¹ * (u * a) := by group
      _ = ζ⁻¹ * (u * a) * (u * a) := by
        rw [hζc (u * a) ((dpI V z).mul_mem huI haI)]
      _ = ζ⁻¹ * (u * a * (u * a)) := by group
  rw [e2]
  exact (dpZ V z).mul_mem ((dpZ V z).inv_mem hζZ) hsq

theorem le_pCoreOf (d : DihedralPair H T V U x z) (hz3 : orderOf z = 3)
    (hV16 : Nat.card V = 2 ^ 4) (hZ2 : Nat.card (dpZ V z) = 2)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) : U ≤ pCoreOf 2 H := by
  set Q := pCoreOf 2 H with hQ
  have hZN : dpZ V z ≤ Subgroup.normalizer (Q : Set G) := fun ζ hζ => d.HQ (d.VH hζ.1)
  have hUQZ : ∀ u ∈ U, u ∈ Q ⊔ dpZ V z := by
    intro u hu
    have hn := d.norm_mem hz3 hu
    obtain ⟨q₁, hq₁, e1⟩ : ∃ q₁ ∈ Q, z * u * z⁻¹ = q₁ * u := ⟨_, d.zU u hu, by group⟩
    obtain ⟨q₂, hq₂, e2⟩ : ∃ q₂ ∈ Q, z⁻¹ * u * z = q₂ * u := ⟨_, d.zU' u hu, by group⟩
    have hui : u⁻¹ = u := by
      have h2 : u * u = 1 := by simpa [pow_two] using d.elem.2 u (d.UV hu)
      exact inv_eq_of_mul_eq_one_right h2
    have huq : u * q₁ * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (d.HQ (d.VH (d.UV hu))) q₁).mp hq₁
    have e4 : u * (q₁ * u) * (q₂ * u) = (u * q₁ * u⁻¹) * q₂ * u := by
      conv_rhs => rw [hui]
      group
    have hn' : u * (z * u * z⁻¹) * (z⁻¹ * u * z) = (u * q₁ * u⁻¹) * q₂ * u := by
      rw [e1, e2, e4]
    have e5 : u = ((u * q₁ * u⁻¹) * q₂)⁻¹ * (u * (z * u * z⁻¹) * (z⁻¹ * u * z)) := by
      rw [hn']
      group
    rw [e5]
    exact (Q ⊔ dpZ V z).mul_mem (Subgroup.mem_sup_left (Q.inv_mem (Q.mul_mem huq hq₂)))
      (Subgroup.mem_sup_right hn)
  have hzZ : ∀ ζ ∈ dpZ V z, z * ζ * z⁻¹ = ζ := fun ζ hζ => by
    rw [d.ZC ζ hζ z d.zI]
    group
  have hAQZ : dpA H V U z ≤ Q ⊔ dpZ V z := by
    intro a ha
    rw [d.Aeq, mem_cjSub] at ha
    have h1 := hUQZ _ ha
    have h1' : ((z⁻¹ * a * z : G) : G) ∈ ((Q ⊔ dpZ V z : Subgroup G) : Set G) := h1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at h1'
    obtain ⟨q, hq, ζ, hζ, hqζ⟩ := h1'
    have e : a = (z * q * z⁻¹) * (z * ζ * z⁻¹) := by
      have : a = z * (z⁻¹ * a * z) * z⁻¹ := by group
      rw [this, ← hqζ]
      group
    rw [e, hzZ ζ hζ]
    exact (Q ⊔ dpZ V z).mul_mem (Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (d.HQ d.zH) q).mp hq)) (Subgroup.mem_sup_right hζ)
  have hPQZ : dpP H V U z ≤ Q ⊔ dpZ V z := sup_le hUQZ hAQZ
  have hUcard : Nat.card U = 8 := by
    have := d.cardV
    rw [hV16] at this
    omega
  obtain ⟨g, hg, h, hh, hgh⟩ : ∃ g ∈ dpP H V U z, ∃ h ∈ dpP H V U z, g * h ≠ h * g := by
    by_contra hcon
    push Not at hcon
    have hUZ : U ≤ dpZ V z := fun u hu => d.mem_Z_of_comm hCA (Subgroup.mem_sup_left hu)
      (fun g hg => hcon g hg u (Subgroup.mem_sup_left hu))
    have := Subgroup.card_le_of_le hUZ
    rw [hUcard, hZ2] at this
    omega
  have hζ₀Z : g * h * g⁻¹ * h⁻¹ ∈ dpZ V z := d.comm_mem_Z hg hh
  have hζ₀1 : g * h * g⁻¹ * h⁻¹ ≠ 1 := fun h1 => hgh (by
    calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
      _ = h * g := by rw [h1, one_mul])
  have hPI : dpP H V U z ≤ dpI V z := d.PR.trans inf_le_left
  have hζ₀Q : g * h * g⁻¹ * h⁻¹ ∈ Q := by
    have hg' : g ∈ ((Q ⊔ dpZ V z : Subgroup G) : Set G) := hPQZ hg
    have hh' : h ∈ ((Q ⊔ dpZ V z : Subgroup G) : Set G) := hPQZ hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at hg' hh'
    obtain ⟨q, hq, ζ₁, hζ₁, rfl⟩ := hg'
    obtain ⟨q', hq', ζ₂, hζ₂, rfl⟩ := hh'
    have hqI : q ∈ dpI V z := by
      have : q = (q * ζ₁) * ζ₁⁻¹ := by group
      rw [this]
      exact (dpI V z).mul_mem (hPI hg) ((dpI V z).inv_mem (d.ZC_mem hζ₁))
    have hq'I : q' ∈ dpI V z := by
      have : q' = (q' * ζ₂) * ζ₂⁻¹ := by group
      rw [this]
      exact (dpI V z).mul_mem (hPI hh) ((dpI V z).inv_mem (d.ZC_mem hζ₂))
    have c1 : q' * ζ₁ = ζ₁ * q' := d.ZC ζ₁ hζ₁ q' hq'I
    have c2 : q⁻¹ * ζ₂ = ζ₂ * q⁻¹ := d.ZC ζ₂ hζ₂ q⁻¹ ((dpI V z).inv_mem hqI)
    have c3 : ζ₂ * ζ₁ = ζ₁ * ζ₂ := d.ZC ζ₁ hζ₁ ζ₂ (d.ZC_mem hζ₂)
    have e : q * ζ₁ * (q' * ζ₂) * (q * ζ₁)⁻¹ * (q' * ζ₂)⁻¹ = q * q' * q⁻¹ * q'⁻¹ := by
      calc q * ζ₁ * (q' * ζ₂) * (q * ζ₁)⁻¹ * (q' * ζ₂)⁻¹
          = q * (ζ₁ * q') * ζ₂ * ζ₁⁻¹ * q⁻¹ * ζ₂⁻¹ * q'⁻¹ := by group
        _ = q * (q' * ζ₁) * ζ₂ * ζ₁⁻¹ * q⁻¹ * ζ₂⁻¹ * q'⁻¹ := by rw [c1]
        _ = q * q' * (ζ₂ * ζ₁) * ζ₁⁻¹ * q⁻¹ * ζ₂⁻¹ * q'⁻¹ := by rw [c3]; group
        _ = q * q' * (ζ₂ * q⁻¹) * ζ₂⁻¹ * q'⁻¹ := by group
        _ = q * q' * (q⁻¹ * ζ₂) * ζ₂⁻¹ * q'⁻¹ := by rw [c2]
        _ = q * q' * q⁻¹ * q'⁻¹ := by group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq hq') (Q.inv_mem hq)) (Q.inv_mem hq')
  have hZQ : dpZ V z ≤ Q := fun ζ hζ => by
    rcases eq_one_or_eq_of_card_eq_two hZ2 hζ₀Z hζ₀1 (d.elem.2 _ hζ₀Z.1) hζ with h1 | h1
    · rw [h1]
      exact Q.one_mem
    · rw [h1]
      exact hζ₀Q
  exact fun u hu => (sup_le le_rfl hZQ : Q ⊔ dpZ V z ≤ Q) (hUQZ u hu)

omit [Finite G] in
theorem ofInv (d : DihedralPair H T V U x z) (hUQ : U ≤ pCoreOf 2 H) {w : G} (hwH : w ∈ H)
    (hwo : Odd (orderOf w)) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w⁻¹) :
    DihedralPair H T V U x w :=
  ⟨d.T2, d.TH, d.QT, d.char, d.VT, d.TV, d.elem, d.UV, d.VQU, d.xV, d.xU, d.U2, hwH, hwo, hw1,
    hxw, fun u hu => (pCoreOf 2 H).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (d.HQ hwH) u).mp (hUQ hu)) ((pCoreOf 2 H).inv_mem (hUQ hu))⟩

omit [Finite G] in
theorem dpZ_eq (d : DihedralPair H T V U x z) (hUQ : U ≤ pCoreOf 2 H)
    (hZ2 : Nat.card (dpZ V z) = 2)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) :
    dpZ V z = V ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  apply le_antisymm
  · intro ζ hζ
    refine ⟨hζ.1, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have hqV : q ∈ Subgroup.normalizer (V : Set G) := d.TV (d.QT hq)
    have hqVz : q ∈ Subgroup.normalizer (cjSub z V : Set G) := by
      have := conj_mem_normalizer_cjSub z (d.TV (d.QT (d.zQ' q hq)))
      simpa [mul_assoc] using this
    have hqZ : q ∈ Subgroup.normalizer (dpZ V z : Set G) :=
      B2F.le_normalizer_inf (Subgroup.zpowers_le.2 hqV) (Subgroup.zpowers_le.2 hqVz)
        (Subgroup.mem_zpowers q)
    have h1 := conj_eq_of_card_eq_two hZ2 (fun a ha => d.elem.2 a ha.1) hqZ hζ
    calc q * ζ = (q * ζ * q⁻¹) * q := by group
      _ = ζ * q := by rw [h1]
  · intro ζ hζ
    rw [← hCA]
    refine ⟨hζ.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hζ.2 a ((sup_le hUQ le_rfl) ha.2.2)

theorem inv_facts (d : DihedralPair H T V U x z) (hUQ : U ≤ pCoreOf 2 H)
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H)) {w : G} (hwH : w ∈ H)
    (hwo : Odd (orderOf w)) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w⁻¹) :
    orderOf w = 3 ∧ Nat.card (dpZ V w) = 2 ∧
      V ⊓ Subgroup.centralizer (dpA H V U w : Set G) = dpZ V w ∧
      dpZ V w = V ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  have gen : ∀ w' : G, w' ∈ H → Odd (orderOf w') → w' ≠ 1 → x * w' * x⁻¹ = w'⁻¹ →
      Nat.card (dpZ V w') = 2 ∧ V ⊓ Subgroup.centralizer (dpA H V U w' : Set G) = dpZ V w' ∧
      dpZ V w' = V ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro w' hw'H hw'o hw'1 hxw'
    have dw := d.ofInv hUQ hw'H hw'o hw'1 hxw'
    obtain ⟨-, hZ2, hCA⟩ := dw.counts hV16 (dw.cube_le_sq hq)
    exact ⟨hZ2, hCA, dw.dpZ_eq hUQ hZ2 hCA⟩
  obtain ⟨hZ2, hCA, hZeq⟩ := gen w hwH hwo hw1 hxw
  have dw := d.ofInv hUQ hwH hwo hw1 hxw
  refine ⟨dw.orderOf_eq_three_of_inf hV16 hZ2 hCA fun k hk0 hkp => ?_, hZ2, hCA, hZeq⟩
  have hwk1 : w ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' hkp
  have hwkodd : Odd (orderOf (w ^ k)) := Odd.of_dvd_nat hwo (orderOf_pow_dvd k)
  have hxwk : x * w ^ k * x⁻¹ = (w ^ k)⁻¹ :=
    conj_eq_inv_of_mem_zpowers hxw (Subgroup.npow_mem_zpowers w k)
  obtain ⟨-, -, hZk⟩ := gen (w ^ k) (H.pow_mem hwH k) hwkodd hwk1 hxwk
  rw [hZeq, ← hZk]
  exact inf_le_inf d.UV (cjSub_mono d.UV)

end DihedralPair

end E2

end CFSG.Quasithin
