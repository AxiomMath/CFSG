module

public import CFSG.Quasithin.H13.AS91Sec5Line
public import CFSG.Quasithin.H13.AS91Sec5Gamma
public import CFSG.Quasithin.H13.AS91Sec5Prim

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

@[expose] def Stmt5_2c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mem_conjSub_iff (E : Subgroup G) (g x : G) :
    x ∈ E.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom e) * g = e := by
      show g⁻¹ * (g * e * g⁻¹) * g = e
      group
    rw [this]
    exact he
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem z_mem_E : z ∈ c.E := by
  have hz : z ∈ (center (c.T : Subgroup G)).map (c.T : Subgroup G).subtype := by
    rw [c.center_T]
    exact Subgroup.mem_zpowers z
  obtain ⟨t₀, ht₀, ht₀z⟩ := Subgroup.mem_map.mp hz
  have hzT : z ∈ (c.T : Subgroup G) := by
    have h0 : (t₀ : G) = z := ht₀z
    have h1 := t₀.2
    rw [h0] at h1
    exact h1
  have hzc : ∀ t ∈ (c.T : Subgroup G), z * t = t * z := by
    intro t ht
    have h1 := Subgroup.mem_center_iff.mp ht₀ ⟨t, ht⟩
    have h2 := congrArg Subtype.val h1
    have h3 : t * (t₀ : G) = (t₀ : G) * t := h2
    rw [← ht₀z]
    exact h3.symm
  have hzG1 : z ∈ c.G1 := (Subgroup.mem_inf.mp (c.G13_le_inf (c.T_le hzT))).1
  exact c.centralizer_E z hzG1 fun e he => hzc e (c.E_le_T he)

theorem lineU_of_2c (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) : c.G1 ⊓ stabilizer G y ≤ c.G2 := by
  obtain ⟨g₀, hg₀, hg₀y⟩ := (c.mem_ptsL_iff y).mp hy
  have hg₀x : g₀ • c.x0 = y := by
    rw [← hg₀y, ← mul_one g₀, mk_mul_eq_smul]
    simp
  have h2 := h2c y hy hyx g₀ hg₀ hg₀x
  intro m hm
  obtain ⟨hm1, hmy⟩ := Subgroup.mem_inf.mp hm
  have hmy' : m • y = y := mem_stabilizer_iff.mp hmy
  have hn : g₀⁻¹ * m * g₀ ∈ c.G1 := by
    rw [← c.stab_x0]
    apply mem_stabilizer_iff.mpr
    calc (g₀⁻¹ * m * g₀) • c.x0 = g₀⁻¹ • m • g₀ • c.x0 := by rw [mul_smul, mul_smul]
      _ = c.x0 := by rw [hg₀x, hmy', ← hg₀x, inv_smul_smul]
  have hmE := Subgroup.mem_normalizer_iff.mp hm1
  have hnE := Subgroup.mem_normalizer_iff.mp hn
  have hZ : ∀ x : G, x ∈ c.Z ↔ (g₀⁻¹ * x * g₀ ∈ c.E ∧ x ∈ c.E) := by
    intro x
    rw [← h2, Subgroup.mem_inf, mem_conjSub_iff]
  show m ∈ normalizer (c.Z : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hZ, hZ]
  have e1 : g₀⁻¹ * (m * x * m⁻¹) * g₀ =
      (g₀⁻¹ * m * g₀) * (g₀⁻¹ * x * g₀) * (g₀⁻¹ * m * g₀)⁻¹ := by group
  rw [e1, ← hnE (g₀⁻¹ * x * g₀), ← hmE x]

theorem G3_comm_z {h : G} (hh : h ∈ c.G3) : h⁻¹ * z * h = z := by
  rw [Loc49.G3, H, Subgroup.mem_centralizer_iff] at hh
  have := hh z (Set.mem_singleton z)
  rw [mul_assoc, this, inv_mul_cancel_left]

theorem exists_K_conj {a b : G} (ha : a ∈ c.Z) (hb : b ∈ c.Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ k ∈ c.K, k * a * k⁻¹ = b := by
  have ha' : (⟨a, ha⟩ : ↥c.Z) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb' : (⟨b, hb⟩ : ↥c.Z) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := elem8_exists_mulAut_apply_eq c.Z_comm' c.Z_sq' c.card_Z ha' hb'
  obtain ⟨k, hk⟩ := c.exists_mem_K_conj_eq f
  refine ⟨k, k.2, ?_⟩
  have := hk ⟨a, ha⟩
  rw [hf] at this
  exact this.symm

theorem mem_ptsP_iff (b : G ⧸ c.G1) : b ∈ c.ptsP ↔ ∃ h ∈ c.G3, (h : G ⧸ c.G1) = b := by
  rw [Loc49.ptsP, Loc49.pi0, objOf_one]
  simp

theorem G3_smul_pi0 {h : G} (hh : h ∈ c.G3) : h • c.pi0 = c.pi0 := by
  have h1 : h • ((1 : G) : G ⧸ c.G3) = ((h : G) : G ⧸ c.G3) := by
    rw [← mk_mul_eq_smul, mul_one]
  exact h1.trans ((mk_eq_one_iff c.G3 h).mpr hh)

theorem gamma2_base (hJ : HypJ4 G z)
    (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    {b : G ⧸ c.G1} (hb : b ∈ c.ptsP) (hbx : b ≠ c.x0) {m : G ⧸ c.G2}
    (hxm : CInc c.G1 c.G2 c.x0 m) (hbm : CInc c.G1 c.G2 b m) : m ∈ c.lnsP := by
  obtain ⟨h, hh, hhb⟩ := (c.mem_ptsP_iff b).mp hb
  obtain ⟨u, hu1, hu2⟩ := hxm
  obtain ⟨t, ht1, ht2⟩ := hbm
  have huG1 : u ∈ c.G1 := (mk_eq_one_iff c.G1 u).mp hu1
  have hux : u • c.x0 = c.x0 := by
    have : u ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact huG1
    exact mem_stabilizer_iff.mp this
  have hu'x : u⁻¹ • c.x0 = c.x0 := by rw [inv_smul_eq_iff, hux]
  have hg₀ : u⁻¹ * t ∈ c.G2 := by
    have : (u : G ⧸ c.G2) = (t : G ⧸ c.G2) := hu2.trans ht2.symm
    rw [QuotientGroup.eq] at this
    exact this
  have htx : t • c.x0 = b := by
    rw [← ht1, ← mul_one t, mk_mul_eq_smul]
    simp
  have hgx : (u⁻¹ * t) • c.x0 ∈ c.ptsL := smul_mem_objOf_base hg₀ c.x0_mem_ptsL
  have hgxne : (u⁻¹ * t) • c.x0 ≠ c.x0 := by
    intro h'
    apply hbx
    rw [mul_smul, htx] at h'
    exact smul_left_cancel u⁻¹ (h'.trans hu'x.symm)
  have h2 := h2c _ hgx hgxne (u⁻¹ * t) hg₀ rfl
  have hn : h⁻¹ * t ∈ c.G1 := by
    have : (h : G ⧸ c.G1) = (t : G ⧸ c.G1) := hhb.trans ht1.symm
    rw [QuotientGroup.eq] at this
    exact this
  have hzE := c.z_mem_E
  have hz1 : z ≠ 1 := Loc49.z_ne_one hJ
  have hzh : h * z * h⁻¹ = z := by
    have := c.G3_comm_z hh
    have hcomm : z * h = h * z := by
      calc z * h = h * (h⁻¹ * z * h) := by group
        _ = h * z := by rw [this]
    rw [← hcomm]
    group
  have hz'E : u⁻¹ * z * u ∈ c.E := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem huG1) z).mp hzE
    simpa using this
  have hz'E' : u⁻¹ * z * u ∈ c.E.map (MulAut.conj (u⁻¹ * t)).toMonoidHom := by
    rw [mem_conjSub_iff]
    have e1 : (u⁻¹ * t)⁻¹ * (u⁻¹ * z * u) * (u⁻¹ * t) = (h⁻¹ * t)⁻¹ * z * (h⁻¹ * t) := by
      calc (u⁻¹ * t)⁻¹ * (u⁻¹ * z * u) * (u⁻¹ * t) = t⁻¹ * z * t := by group
        _ = t⁻¹ * (h * z * h⁻¹) * t := by rw [hzh]
        _ = (h⁻¹ * t)⁻¹ * z * (h⁻¹ * t) := by group
    rw [e1]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) z).mp hzE
    simpa using this
  have hz'Z : u⁻¹ * z * u ∈ c.Z := by
    rw [← h2]
    exact Subgroup.mem_inf.mpr ⟨hz'E', hz'E⟩
  have hz'1 : u⁻¹ * z * u ≠ 1 := by
    intro h'
    apply hz1
    have : z = u * (u⁻¹ * z * u) * u⁻¹ := by group
    rw [this, h']
    group
  obtain ⟨k, hkK, hk⟩ := c.exists_K_conj hz'Z c.z_mem_Z hz'1 hz1
  have hvG3 : u * k⁻¹ ∈ c.G3 := by
    rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have e2 : (u * k⁻¹)⁻¹ * z * (u * k⁻¹) = z := by
      calc (u * k⁻¹)⁻¹ * z * (u * k⁻¹) = k * (u⁻¹ * z * u) * k⁻¹ := by group
        _ = z := hk
    calc z * (u * k⁻¹) = (u * k⁻¹) * ((u * k⁻¹)⁻¹ * z * (u * k⁻¹)) := by group
      _ = (u * k⁻¹) * z := by rw [e2]
  have hvm : ((u * k⁻¹ : G) : G ⧸ c.G2) = m := by
    rw [← hu2, QuotientGroup.eq]
    have : (u * k⁻¹)⁻¹ * u = k := by group
    rw [this]
    exact c.K_le_G2 hkK
  exact ⟨u * k⁻¹, hvm, (mk_eq_one_iff c.G3 _).mpr hvG3⟩

theorem gamma2_of_2c (hJ : HypJ4 G z)
    (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z) :
    ∀ a b : G ⧸ c.G1, a ∈ c.ptsP → b ∈ c.ptsP → c.Delta.Adj a b →
      ∀ m : G ⧸ c.G2, CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m → m ∈ c.lnsP := by
  intro a b ha hb hadj m ham hbm
  obtain ⟨ha_G, haG3, haeq⟩ : ∃ g, g ∈ c.G3 ∧ (g : G ⧸ c.G1) = a := by
    obtain ⟨g, hg, hga⟩ := (c.mem_ptsP_iff a).mp ha
    exact ⟨g, hg, hga⟩
  obtain ⟨hb_G, hbG3, hbeq⟩ := (c.mem_ptsP_iff b).mp hb
  have haa : ha_G • c.x0 = a := by
    rw [← haeq, ← mul_one ha_G, mk_mul_eq_smul]
    simp
  have hb' : ha_G⁻¹ • b ∈ c.ptsP := by
    rw [c.mem_ptsP_iff]
    refine ⟨ha_G⁻¹ * hb_G, mul_mem (inv_mem haG3) hbG3, ?_⟩
    rw [← hbeq, mk_mul_eq_smul]
  have hb'x : ha_G⁻¹ • b ≠ c.x0 := by
    intro h'
    apply hadj.ne
    rw [← haa]
    exact (inv_smul_eq_iff.mp h').symm
  have hxm' : CInc c.G1 c.G2 c.x0 (ha_G⁻¹ • m) := by
    have := (cInc_smul c.G1 c.G2 ha_G⁻¹ a m).mpr ham
    rwa [← haa, inv_smul_smul] at this
  have hbm' : CInc c.G1 c.G2 (ha_G⁻¹ • b) (ha_G⁻¹ • m) :=
    (cInc_smul c.G1 c.G2 ha_G⁻¹ b m).mpr hbm
  have hm' : ha_G⁻¹ • m ∈ c.lnsP := c.gamma2_base hJ h2c hb' hb'x hxm' hbm'
  have h3 : CInc c.G2 c.G3 (ha_G • (ha_G⁻¹ • m)) (ha_G • c.pi0) :=
    (cInc_smul c.G2 c.G3 ha_G _ _).mpr hm'
  rw [c.G3_smul_pi0 haG3, smul_inv_smul] at h3
  exact h3

end Loc49

theorem stmt5_gamma2_of_2c (h : Stmt5_2c) : Stmt5_Gamma2 := by
  intro G _ _ z hJ c
  exact c.gamma2_of_2c hJ (h G z hJ c)

theorem stmt5_lineU_of_2c (h : Stmt5_2c) : Stmt5_LineU := by
  intro G _ _ z hJ c y hy hyx
  exact c.lineU_of_2c (h G z hJ c) hy hyx

end CFSG.Quasithin.H13.AS91
