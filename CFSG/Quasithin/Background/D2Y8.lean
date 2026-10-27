module

public import CFSG.Quasithin.Background.D2Y7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def kerMod (X : Subgroup (MulAut V)) (z : MulAut V) : Subgroup (MulAut V) where
  carrier := {g | g ∈ X ∧ g * z = z * g ∧
    ∀ r ∈ pCoreOf 3 X, g * r * g⁻¹ * r⁻¹ ∈ Subgroup.zpowers z}
  one_mem' := ⟨X.one_mem, by simp, fun r _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgX, hgz, hg⟩ ⟨hhX, hhz, hh⟩
    refine ⟨X.mul_mem hgX hhX, by rw [mul_assoc, hhz, ← mul_assoc, hgz, mul_assoc], fun r hr => ?_⟩
    have e : g * h * r * (g * h)⁻¹ * r⁻¹ =
        (g * (h * r * h⁻¹ * r⁻¹) * g⁻¹) * (g * r * g⁻¹ * r⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ (hg r hr)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hh r hr)
    rw [← hm, ← conj_zpow]
    have : g * z * g⁻¹ = z := by rw [hgz]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  inv_mem' := by
    rintro g ⟨hgX, hgz, hg⟩
    refine ⟨X.inv_mem hgX, ?_, fun r hr => ?_⟩
    · have : g⁻¹ * z = z * g⁻¹ := by
        calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hgz]
          _ = z * g⁻¹ := by group
      exact this
    · have hr' : g⁻¹ * r * g ∈ pCoreOf 3 X := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (X.inv_mem hgX)) r).mp hr
        simpa using this
      have h1 := hg _ hr'
      have e : g⁻¹ * r * g⁻¹⁻¹ * r⁻¹ = (g * (g⁻¹ * r * g) * g⁻¹ * (g⁻¹ * r * g)⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h1

omit [Finite V] in
theorem mem_kerMod {X : Subgroup (MulAut V)} {z g : MulAut V} :
    g ∈ kerMod X z ↔ g ∈ X ∧ g * z = z * g ∧
      ∀ r ∈ pCoreOf 3 X, g * r * g⁻¹ * r⁻¹ ∈ Subgroup.zpowers z := Iff.rfl

section Main

variable {X : Subgroup (MulAut V)}

omit [Finite V] in
theorem conj_zpowers_mem {h z : MulAut V} (hz : h * z * h⁻¹ ∈ Subgroup.zpowers z) {w : MulAut V}
    (hw : w ∈ Subgroup.zpowers z) : h * w * h⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hz m

omit [Finite V] in
theorem commute_zpowers_of_commute {k z : MulAut V} (hkz : k * z = z * k) {w : MulAut V}
    (hw : w ∈ Subgroup.zpowers z) : k * w = w * k := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((show Commute k z from hkz).zpow_right m).eq

omit [Finite V] in
theorem conj_mem_kerMod {z h k : MulAut V} (hZ : ∀ h ∈ X, h * z * h⁻¹ ∈ Subgroup.zpowers z)
    (hh : h ∈ X) (hk : k ∈ kerMod X z) : h * k * h⁻¹ ∈ kerMod X z := by
  obtain ⟨hkX, hkz, hk'⟩ := hk
  refine ⟨X.mul_mem (X.mul_mem hh hkX) (X.inv_mem hh), ?_, fun r hr => ?_⟩
  · have hw : h⁻¹ * z * h ∈ Subgroup.zpowers z := by simpa using hZ h⁻¹ (X.inv_mem hh)
    have hkw : k * (h⁻¹ * z * h) = (h⁻¹ * z * h) * k := commute_zpowers_of_commute hkz hw
    calc h * k * h⁻¹ * z = h * (k * (h⁻¹ * z * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * z * h) * k) * h⁻¹ := by rw [hkw]
      _ = z * (h * k * h⁻¹) := by group
  · have hr' : h⁻¹ * r * h ∈ pCoreOf 3 X := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (X.inv_mem hh)) r).mp hr
      simpa using this
    have h1 := hk' _ hr'
    have e : h * k * h⁻¹ * r * (h * k * h⁻¹)⁻¹ * r⁻¹ =
        h * (k * (h⁻¹ * r * h) * k⁻¹ * (h⁻¹ * r * h)⁻¹) * h⁻¹ := by group
    rw [e]
    exact conj_zpowers_mem (hZ h hh) h1

theorem kerMod_cube_mem (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {z k : MulAut V}
    (hz3 : z ^ 3 = 1) (hk : k ∈ kerMod X z) : k ^ 3 ∈ pCoreOf 3 X := by
  obtain ⟨hkX, hkz, hk'⟩ := hk
  rw [← c.fittingOf_eq hV]
  refine c.hyp.fstar ⟨X.pow_mem hkX 3, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro r hr
  have hr' : r ∈ pCoreOf 3 X := by rwa [c.fittingOf_eq hV] at hr
  obtain ⟨ζ, hζ, hζr⟩ : ∃ ζ ∈ Subgroup.zpowers z, k * r * k⁻¹ = ζ * r :=
    ⟨k * r * k⁻¹ * r⁻¹, hk' r hr', by group⟩
  have hkζc : Commute k ζ := commute_zpowers_of_commute hkz hζ
  have hζ3 : ζ ^ 3 = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
    exact zpow_cube_eq_one hz3 m
  have key : ∀ n : ℕ, k ^ n * r * (k ^ n)⁻¹ = ζ ^ n * r := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : k ^ (n + 1) * r * (k ^ (n + 1))⁻¹ = k * (k ^ n * r * (k ^ n)⁻¹) * k⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      have hc : k * ζ ^ n * k⁻¹ = ζ ^ n := by
        rw [(hkζc.pow_right n).eq]; group
      calc k * (ζ ^ n * r) * k⁻¹ = (k * ζ ^ n * k⁻¹) * (k * r * k⁻¹) := by group
        _ = ζ ^ n * (ζ * r) := by rw [hc, hζr]
        _ = ζ ^ (n + 1) * r := by rw [pow_succ, mul_assoc]
  have h3 := key 3
  rw [hζ3, one_mul] at h3
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

theorem kerMod_le_pCoreOf (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {z : MulAut V}
    (hz3 : z ^ 3 = 1) (hZ : ∀ h ∈ X, h * z * h⁻¹ ∈ Subgroup.zpowers z) :
    kerMod X z ≤ pCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK3 : IsPGroup 3 ↥(kerMod X z) := by
    rw [IsPGroup.iff_orderOf]
    intro k
    have hk3 := kerMod_cube_mem hV c hz3 k.2
    obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup 3 X) hk3
    have hdvd : orderOf (k : MulAut V) ∣ 3 ^ (a + 1) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_succ', pow_mul, ← ha]
      exact pow_orderOf_eq_one _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact ⟨j, by rw [← Subgroup.orderOf_coe]; exact hj⟩
  refine le_pCoreOf_of_le_normalizer 3 (fun g hg => hg.1) (fun h hh => ?_) hK3
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact conj_mem_kerMod hZ hh hk
  · intro hk
    have := conj_mem_kerMod hZ (X.inv_mem hh) hk
    simpa [mul_assoc] using this

theorem normalizes_Z_of_RP {t x z : MulAut V} (hg : Good X t x z)
    (hRP : centR X x = pCoreOf 3 X) {h : MulAut V} (hh : h ∈ X) :
    h * z * h⁻¹ ∈ Subgroup.zpowers z := by
  have hzR : z ∈ pCoreOf 3 X := by rw [← hRP]; exact hg.hz
  have hconj : h * z * h⁻¹ ∈ centR X x := by
    rw [hRP]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hh) z).mp hzR
  have hne1 : h * z * h⁻¹ ≠ 1 := by
    intro e
    apply hg.hz1
    have : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [this, e]
    group
  by_contra hnot
  have hne : Subgroup.zpowers (h * z * h⁻¹) ≠ Subgroup.zpowers z := fun e =>
    hnot (by rw [← e]; exact Subgroup.mem_zpowers _)
  have h4 := hg.rk4 _ hconj hne1 hne
  rw [rk_commV_zpowers_conj] at h4
  have := hg.rk6
  omega

theorem tinv_centralizes_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x z : MulAut V} (hg : Good X t x z)
    (hRP : centR X x = pCoreOf 3 X) {t' : MulAut V} (ht' : t' ∈ TInv X) : t' * z = z * t' := by
  have hzR : z ∈ pCoreOf 3 X := by rw [← hRP]; exact hg.hz
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hmem := normalizes_Z_of_RP hg hRP ht'.1
  rcases eq_of_mem_zpowers_cube hz3 hmem with e | e | e
  · exfalso
    apply hg.hz1
    have : z = t'⁻¹ * (t' * z * t'⁻¹) * t' := by group
    rw [this, e]
    group
  · exact mul_inv_eq_iff_eq_mul.mp e
  · exfalso
    have h1 := (inverted_data hV c hX1 ht' hzR hg.hz1 e).2.1
    have h2 := hg.rk6
    omega

theorem refl_mod_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x z : MulAut V} (hg : Good X t x z) (hRP : centR X x = pCoreOf 3 X) {t' : MulAut V}
    (ht' : t' ∈ TInv X) : ∀ r ∈ pCoreOf 3 X, t' * r * t'⁻¹ * r ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro r hr
  obtain ⟨l, hlR, hl1, hinv⟩ := exists_inverted hV c ht'
  obtain ⟨hlo, hlrk, -, -, -⟩ := inverted_data hV c hX1 ht' hlR hl1 hinv
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hg.hz1
  have hlP : l ∈ centR X x := by rw [hRP]; exact hlR
  have hlz : l * z = z * l := hg.comm l hlP z hg.hz
  have hne : Subgroup.zpowers l ≠ Subgroup.zpowers z := by
    intro e
    rw [e] at hlrk
    have := hg.rk6
    omega
  obtain ⟨hEcard, -, hform⟩ := E9_data hlo hzo hlz hne
  have hle : Subgroup.zpowers l ⊔ Subgroup.zpowers z ≤ centR X x :=
    sup_le (Subgroup.zpowers_le.mpr hlP) (Subgroup.zpowers_le.mpr hg.hz)
  have heq : Subgroup.zpowers l ⊔ Subgroup.zpowers z = centR X x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard, hg.card])
  have hr' : r ∈ Subgroup.zpowers l ⊔ Subgroup.zpowers z := by rw [heq, hRP]; exact hr
  obtain ⟨i, j, rfl⟩ := hform r hr'
  have htz : t' * z * t'⁻¹ = z := by
    rw [tinv_centralizes_z hV c hX1 hg hRP ht']
    group
  have hconj : t' * (l ^ i * z ^ j) * t'⁻¹ = (l⁻¹) ^ i * z ^ j := by
    calc t' * (l ^ i * z ^ j) * t'⁻¹ = (t' * l ^ i * t'⁻¹) * (t' * z ^ j * t'⁻¹) := by group
      _ = (t' * l * t'⁻¹) ^ i * (t' * z * t'⁻¹) ^ j := by rw [← conj_zpow, ← conj_zpow]
      _ = (l⁻¹) ^ i * z ^ j := by rw [hinv, htz]
  have hcomm : Commute (l ^ i) (z ^ j) := (show Commute l z from hlz).zpow_zpow i j
  rw [hconj]
  have e : (l⁻¹) ^ i * z ^ j * (l ^ i * z ^ j) = z ^ j * z ^ j := by
    calc (l⁻¹) ^ i * z ^ j * (l ^ i * z ^ j) = (l ^ i)⁻¹ * (z ^ j * l ^ i) * z ^ j := by
          rw [inv_zpow]; group
      _ = (l ^ i)⁻¹ * (l ^ i * z ^ j) * z ^ j := by rw [hcomm.symm.eq]
      _ = z ^ j * z ^ j := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j)
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j)

theorem D2_29 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x z : MulAut V} (hg : Good X t x z)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) : centR X x ≠ pCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hRP
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hzR : z ∈ pCoreOf 3 X := by rw [← hRP]; exact hg.hz
  have hZ : ∀ h ∈ X, h * z * h⁻¹ ∈ Subgroup.zpowers z := fun h hh =>
    normalizes_Z_of_RP hg hRP hh
  have hKR := kerMod_le_pCoreOf hV c hz3 hZ
  obtain ⟨Y₁, hY₁, Y₂, hY₂, hne⟩ := htwo
  obtain ⟨l₁, t₁, hp₁, hz₁, hlo₁, -⟩ := Yinv_data hV c hX1 hY₁
  obtain ⟨l₂, t₂, hp₂, hz₂, hlo₂, -⟩ := Yinv_data hV c hX1 hY₂
  have hcz₁ := tinv_centralizes_z hV c hX1 hg hRP hp₁.ht
  have hcz₂ := tinv_centralizes_z hV c hX1 hg hRP hp₂.ht
  have hgK : t₁ * t₂ ∈ kerMod X z := by
    refine ⟨X.mul_mem hp₁.ht.1 hp₂.ht.1, ?_, fun r hr => ?_⟩
    · rw [mul_assoc, hcz₂, ← mul_assoc, hcz₁, mul_assoc]
    · have hA₂ := refl_mod_z hV c hX1 hg hRP hp₂.ht r hr
      have hB₁ := refl_mod_z hV c hX1 hg hRP hp₁.ht r⁻¹ ((pCoreOf 3 X).inv_mem hr)
      have e : (t₁ * t₂) * r * (t₁ * t₂)⁻¹ * r⁻¹ =
          (t₁ * (t₂ * r * t₂⁻¹ * r) * t₁⁻¹) * (t₁ * r⁻¹ * t₁⁻¹ * r⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (conj_zpowers_mem (hZ t₁ hp₁.ht.1) hA₂) hB₁
  have hgR : t₁ * t₂ ∈ pCoreOf 3 X := hKR hgK
  have hgP : t₁ * t₂ ∈ centR X x := by rw [hRP]; exact hgR
  have hl₁P : l₁ ∈ centR X x := by rw [hRP]; exact hp₁.hx
  have hl₂P : l₂ ∈ centR X x := by rw [hRP]; exact hp₂.hx
  have hcomm : (t₁ * t₂) * l₁ = l₁ * (t₁ * t₂) := hg.comm _ hgP l₁ hl₁P
  have ht₁inv : t₁⁻¹ = t₁ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_two]
    exact hp₁.ht.2.2.1
  have hinv₁ : t₂ * l₁ * t₂⁻¹ = l₁⁻¹ := by
    calc t₂ * l₁ * t₂⁻¹ = t₁⁻¹ * ((t₁ * t₂) * l₁) * t₂⁻¹ := by group
      _ = t₁⁻¹ * (l₁ * (t₁ * t₂)) * t₂⁻¹ := by rw [hcomm]
      _ = t₁⁻¹ * l₁ * t₁ := by group
      _ = t₁ * l₁ * t₁⁻¹ := by rw [ht₁inv]
      _ = l₁⁻¹ := hp₁.hinv
  have hl₁o : orderOf l₁ = 3 := hlo₁
  have hl₂o : orderOf l₂ = 3 := hlo₂
  have hl₁₂ : l₁ * l₂ = l₂ * l₁ := hg.comm l₁ hl₁P l₂ hl₂P
  have hne' : Subgroup.zpowers l₁ ≠ Subgroup.zpowers l₂ := by
    rw [hz₁, hz₂]; exact hne
  obtain ⟨hEcard, -, hform⟩ := E9_data hl₁o hl₂o hl₁₂ hne'
  have hle : Subgroup.zpowers l₁ ⊔ Subgroup.zpowers l₂ ≤ centR X x :=
    sup_le (Subgroup.zpowers_le.mpr hl₁P) (Subgroup.zpowers_le.mpr hl₂P)
  have heq : Subgroup.zpowers l₁ ⊔ Subgroup.zpowers l₂ = centR X x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard, hg.card])
  have hzE : z ∈ Subgroup.zpowers l₁ ⊔ Subgroup.zpowers l₂ := by rw [heq]; exact hg.hz
  obtain ⟨i, j, hij⟩ := hform z hzE
  have hcomm' : Commute (l₁ ^ i) (l₂ ^ j) := (show Commute l₁ l₂ from hl₁₂).zpow_zpow i j
  have hzinv : t₂ * z * t₂⁻¹ = z⁻¹ := by
    have h1 : t₂ * z * t₂⁻¹ = (l₁⁻¹) ^ i * (l₂⁻¹) ^ j := by
      rw [hij]
      calc t₂ * (l₁ ^ i * l₂ ^ j) * t₂⁻¹
          = (t₂ * l₁ ^ i * t₂⁻¹) * (t₂ * l₂ ^ j * t₂⁻¹) := by group
        _ = (t₂ * l₁ * t₂⁻¹) ^ i * (t₂ * l₂ * t₂⁻¹) ^ j := by rw [← conj_zpow, ← conj_zpow]
        _ = (l₁⁻¹) ^ i * (l₂⁻¹) ^ j := by rw [hinv₁, hp₂.hinv]
    rw [h1, hij, inv_zpow, inv_zpow, ← mul_inv_rev, hcomm'.symm.eq]
  have hz' : z = z⁻¹ := by
    have := hcz₂
    calc z = t₂ * z * t₂⁻¹ := by rw [hcz₂]; group
      _ = z⁻¹ := hzinv
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hz'
  apply hg.hz1
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [hz3, hz2]; simp

end Main

end CFSG.Quasithin
