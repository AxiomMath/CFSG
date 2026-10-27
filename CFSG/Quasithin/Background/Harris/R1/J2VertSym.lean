module

public import CFSG.Quasithin.Recognition.SzR1MNU
public import CFSG.Quasithin.Recognition.F112J2Torus

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.SzR1.MNU

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem mem_Zs_cases (hset : R1SettingLegacyBare K1 L2 S Zs) {z : G} (hz : z ∈ Zs) (hz1 : z ≠ 1) {x : G}
    (hx : x ∈ Zs) : x = 1 ∨ x = z := by
  have hsq : z * z = 1 := by
    have h1 : (⟨z, hz⟩ : ↥Zs) ^ Nat.card ↥Zs = 1 := pow_card_eq_one'
    rw [hset.card_Z] at h1
    simpa [pow_two] using congrArg Subtype.val h1
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hz1
  have hle : Subgroup.zpowers z ≤ Zs := Subgroup.zpowers_le.mpr hz
  have hcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  have heq : Zs = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hset.card_Z])).symm
  rw [heq] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk := zpow_mod_orderOf z k
  rw [hord] at hk
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by push_cast; omega
  rcases this with h | h
  · left
    rw [h, zpow_zero] at hk
    exact hk.symm
  · right
    rw [h, zpow_one] at hk
    exact hk.symm

theorem mem_centralizer_V_of_comm (hset : R1SettingLegacyBare K1 L2 S Zs) {v : G}
    (hv : v ∈ conjClosure Zs L2) (hvZ : v ∉ Zs) {y : G} (hyS : y ∈ S)
    (hy : y * v = v * y) : y ∈ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hyc : ∀ c ∈ Zs, y * c = c * y := fun c hc =>
    Subgroup.mem_centralizer_iff.mp (hset.Z_cent_S hc) y hyS
  by_cases hxZ : x ∈ Zs
  · exact (hyc x hxZ).symm
  · have hidx : (Zs.subgroupOf (conjClosure Zs L2)).index = 2 := by
      have hZV : Zs ≤ conjClosure Zs L2 := le_conjClosure Zs L2
      have h4 : (Zs.subgroupOf (conjClosure Zs L2)).index *
          Nat.card ↥(Zs.subgroupOf (conjClosure Zs L2)) = Nat.card ↥(conjClosure Zs L2) :=
        Subgroup.index_mul_card _
      have h5 : Nat.card ↥(Zs.subgroupOf (conjClosure Zs L2)) = 2 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv).trans hset.card_Z
      rw [h5, hset.V_card] at h4
      omega
    have hc : v⁻¹ * x ∈ Zs := F112J2.inv_mul_mem_of_not_mem hidx hv hx hvZ hxZ
    obtain ⟨c, hcZ, rfl⟩ : ∃ c ∈ Zs, x = v * c := ⟨v⁻¹ * x, hc, by group⟩
    calc v * c * y = v * (c * y) := mul_assoc _ _ _
      _ = v * (y * c) := by rw [← hyc c hcZ]
      _ = (v * y) * c := (mul_assoc _ _ _).symm
      _ = (y * v) * c := by rw [hy]
      _ = y * (v * c) := mul_assoc _ _ _

theorem conj_mem_S_cent (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) {g : G} (hg : g ∈ L2)
    {y : G} (hyS : y ∈ S) (hy : y ∈ Subgroup.centralizer (conjClosure Zs L2 : Set G)) :
    g * y * g⁻¹ ∈ S ∧ g * y * g⁻¹ ∈ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
  have hmem : y ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [pCore_eq_of_setting hset hR]
    exact Subgroup.mem_inf.mpr ⟨hyS, hy⟩
  have hn := (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 (L2 ⊔ S) ((le_sup_left : L2 ≤ L2 ⊔ S) hg)) y).mp hmem
  rw [pCore_eq_of_setting hset hR] at hn
  exact Subgroup.mem_inf.mp hn

theorem exists_symm_root_counts (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) {z : G}
    (hz : z ∈ Zs) (hz1 : z ≠ 1) :
    ∃ v ∈ conjClosure Zs L2, v * v = 1 ∧ v ≠ 1 ∧ v ≠ z ∧ v * z = z * v ∧
      (∀ s ∈ S, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = z * v) ∧
      Nat.card {y : S // (y : G) * v = v * y ∧ (y : G) * y = z} =
        Nat.card {y : S // (y : G) * v = v * y ∧ (y : G) * y = v} := by
  have hV := V_elemAbelian_of_setting hset hR
  have hVc : ∀ {a b : G}, a ∈ conjClosure Zs L2 → b ∈ conjClosure Zs L2 → a * b = b * a :=
    fun {a b} ha hb => congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ {a : G}, a ∈ conjClosure Zs L2 → a * a = 1 := fun {a} ha => by
    rw [← pow_two]; exact hV.2 a ha
  have hzsq : z * z = 1 := hVsq (le_conjClosure Zs L2 hz)
  obtain ⟨l, hl, hlN⟩ : ∃ l ∈ L2, l ∉ Subgroup.normalizer (Zs : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hset.Z_not_norm hcon
  set v : G := l * z * l⁻¹ with hvdef
  have hvV : v ∈ conjClosure Zs L2 := mem_conjClosure hl hz
  have hvz : v ≠ z := by
    intro hvz
    apply hlN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases mem_Zs_cases hset hz hz1 hx with rfl | rfl
      · simp
      · rw [← hvdef, hvz]; exact hz
    · intro hx
      rcases mem_Zs_cases hset hz hz1 hx with h | h
      · have : x = 1 := by
          have := congrArg (fun w => l⁻¹ * w * l) h
          simpa [mul_assoc] using this
        rw [this]; exact Zs.one_mem
      · have hx' : x = z := by
          have := congrArg (fun w => l⁻¹ * w * l) h
          have h2 : l⁻¹ * (l * x * l⁻¹) * l = x := by group
          have h3 : l⁻¹ * z * l = z := by
            have : z = l * z * l⁻¹ := hvz.symm
            calc l⁻¹ * z * l = l⁻¹ * (l * z * l⁻¹) * l := by rw [← this]
              _ = z := by group
          rw [h2, h3] at this
          exact this
        rw [hx']; exact hz
  have hv1 : v ≠ 1 := by
    intro h
    apply hz1
    have := congrArg (fun w => l⁻¹ * w * l) h
    simpa [hvdef, mul_assoc] using this
  have hvZ : v ∉ Zs := by
    intro h
    rcases mem_Zs_cases hset hz hz1 h with h | h
    · exact hv1 h
    · exact hvz h
  have hvsq : v * v = 1 := hVsq hvV
  have hvzc : v * z = z * v := hVc hvV (le_conjClosure Zs L2 hz)
  have hidx : (Zs.subgroupOf (conjClosure Zs L2)).index = 2 := by
    have hZV : Zs ≤ conjClosure Zs L2 := le_conjClosure Zs L2
    have h4 : (Zs.subgroupOf (conjClosure Zs L2)).index *
        Nat.card ↥(Zs.subgroupOf (conjClosure Zs L2)) = Nat.card ↥(conjClosure Zs L2) :=
      Subgroup.index_mul_card _
    have h5 : Nat.card ↥(Zs.subgroupOf (conjClosure Zs L2)) = 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv).trans hset.card_Z
    rw [h5, hset.V_card] at h4
    omega
  have hcentS : ∀ w ∈ Zs, ∀ s ∈ S, s * w = w * s := fun w hw s hs =>
    Subgroup.mem_centralizer_iff.mp (hset.Z_cent_S hw) s hs
  refine ⟨v, hvV, hvsq, hv1, hvz, hvzc, ?_, ?_⟩
  · intro s hs
    have hsN : s ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
      F112J2.mem_normalizer_conjClosure_of (hset.hyp.h2.normalizes hs)
        (Subgroup.le_centralizer_iff.mp hset.Z_cent_S hs)
    have hsv : s * v * s⁻¹ ∈ conjClosure Zs L2 := (Subgroup.mem_normalizer_iff.mp hsN v).mp hvV
    have hsvZ : s * v * s⁻¹ ∉ Zs := by
      intro h
      apply hvZ
      have h1 := hcentS _ h s hs
      have : v = s⁻¹ * (s * v * s⁻¹) * s := by group
      rw [this, show s⁻¹ * (s * v * s⁻¹) * s = (s * v * s⁻¹) by
        calc s⁻¹ * (s * v * s⁻¹) * s = s⁻¹ * ((s * v * s⁻¹) * s) := by rw [mul_assoc]
          _ = s⁻¹ * (s * (s * v * s⁻¹)) := by rw [h1]
          _ = s * v * s⁻¹ := by group]
      exact h
    have hc : v⁻¹ * (s * v * s⁻¹) ∈ Zs :=
      F112J2.inv_mul_mem_of_not_mem hidx hvV hsv hvZ hsvZ
    rcases mem_Zs_cases hset hz hz1 hc with h | h
    · left
      calc s * v * s⁻¹ = v * (v⁻¹ * (s * v * s⁻¹)) := by group
        _ = v := by rw [h, mul_one]
    · right
      calc s * v * s⁻¹ = v * (v⁻¹ * (s * v * s⁻¹)) := by group
        _ = v * z := by rw [h]
        _ = z * v := hvzc
  · have hlinv : l⁻¹ ∈ L2 := L2.inv_mem hl
    have hvl : l⁻¹ * v * l = z := by simp [hvdef, mul_assoc]
    have fwd : ∀ y : G, y ∈ S → y * v = v * y → y * y = z →
        l * y * l⁻¹ ∈ S ∧ (l * y * l⁻¹) * v = v * (l * y * l⁻¹) ∧
          (l * y * l⁻¹) * (l * y * l⁻¹) = v := by
      intro y hyS hyv hyy
      have hyC := mem_centralizer_V_of_comm hset hvV hvZ hyS hyv
      obtain ⟨h1, h2⟩ := conj_mem_S_cent hset hR hl hyS hyC
      refine ⟨h1, ?_, ?_⟩
      · exact (Subgroup.mem_centralizer_iff.mp h2 v hvV).symm
      · calc (l * y * l⁻¹) * (l * y * l⁻¹) = l * (y * y) * l⁻¹ := by group
          _ = v := by rw [hyy]
    have bwd : ∀ y : G, y ∈ S → y * v = v * y → y * y = v →
        l⁻¹ * y * l ∈ S ∧ (l⁻¹ * y * l) * v = v * (l⁻¹ * y * l) ∧
          (l⁻¹ * y * l) * (l⁻¹ * y * l) = z := by
      intro y hyS hyv hyy
      have hyC := mem_centralizer_V_of_comm hset hvV hvZ hyS hyv
      obtain ⟨h1, h2⟩ := conj_mem_S_cent hset hR hlinv hyS hyC
      simp only [inv_inv] at h1 h2
      refine ⟨h1, ?_, ?_⟩
      · exact (Subgroup.mem_centralizer_iff.mp h2 v hvV).symm
      · calc (l⁻¹ * y * l) * (l⁻¹ * y * l) = l⁻¹ * (y * y) * l := by group
          _ = z := by rw [hyy, hvl]
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨l * y * l⁻¹, (fwd y y.1.2 y.2.1 y.2.2).1⟩,
          (fwd y y.1.2 y.2.1 y.2.2).2.1, (fwd y y.1.2 y.2.1 y.2.2).2.2⟩
        invFun := fun y => ⟨⟨l⁻¹ * y * l, (bwd y y.1.2 y.2.1 y.2.2).1⟩,
          (bwd y y.1.2 y.2.1 y.2.2).2.1, (bwd y y.1.2 y.2.1 y.2.2).2.2⟩
        left_inv := fun y => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
        right_inv := fun y => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }

end CFSG.Quasithin.Background.Harris.R1.J2Vert
