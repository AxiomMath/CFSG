module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D]

namespace IsNaturalAt

variable {H T : Subgroup D} {z : D} {V : Subgroup D} (hn : IsNaturalAt H T z V)

include hn

omit [Finite D] in
theorem le_pCoreOf : V ≤ pCoreOf 2 H := hn.le_center.trans inf_le_left

omit [Finite D] in
theorem comm_of_mem {u w : D} (hu : u ∈ V) (hw : w ∈ V) : u * w = w * u :=
  Subgroup.mem_centralizer_iff.mp (hn.le_center hw).2 u (hn.le_center hu).1

omit [Finite D] in
theorem mul_self_of_mem {u : D} (hu : u ∈ V) : u * u = 1 := by
  have := hn.reduced.2.2.1.2 u hu
  rwa [pow_two] at this

omit [Finite D] in
theorem z_mem_V : z ∈ V := by
  obtain ⟨a, -, -, hVset⟩ := hn.basis
  have : z ∈ (V : Set D) := by rw [hVset]; simp
  exact this

omit [Finite D] in
theorem conj_cases (hTH : T ≤ H) {t v : D} (ht : t ∈ T) (hv : v ∈ V) :
    t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * z := by
  obtain ⟨a, ha1, haz, hVset⟩ := hn.basis
  have hmemV : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
    intro u
    have := Set.ext_iff.mp hVset u
    simpa using this
  have hzt : t * z * t⁻¹ = z := by
    have h1 : t * z = z * t := Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht
    rw [h1]; group
  have hzV : z ∈ V := hn.z_mem_V
  have haV : a ∈ V := (hmemV a).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hcomm : z * a = a * z := hn.comm_of_mem hzV haV
  have hN : t ∈ Subgroup.normalizer (V : Set D) := hn.reduced.2.1 (hTH ht)
  have hta : t * a * t⁻¹ = a ∨ t * a * t⁻¹ = a * z := by
    have hu : t * a * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN a).mp haV
    rcases (hmemV _).mp hu with h | h | h | h
    · exfalso; apply ha1
      calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    · exfalso; apply haz
      calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
        _ = t⁻¹ * z * t := by rw [h]
        _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [hzt]
        _ = z := by group
    · left; exact h
    · right; rw [h, hcomm]
  rcases (hmemV v).mp hv with h | h | h | h
  · left; rw [h]; group
  · left; rw [h]; exact hzt
  · rw [h]; exact hta
  · rw [h]
    have e : t * (z * a) * t⁻¹ = z * (t * a * t⁻¹) := by
      calc t * (z * a) * t⁻¹ = (t * z * t⁻¹) * (t * a * t⁻¹) := by group
        _ = z * (t * a * t⁻¹) := by rw [hzt]
    rcases hta with h' | h'
    · left; rw [e, h']
    · right; rw [e, h', mul_assoc]

end IsNaturalAt

omit [Finite D] in
theorem Vertex.exists_hom {H T : Subgroup D} (hv : Vertex H T) :
    ∃ φ : ↥H →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      ∀ x : ↥H, φ x = 1 ↔ (x : D) ∈ pCoreOf 2 H := by
  obtain ⟨e⟩ := hv.quotient
  let φ : ↥H →* Equiv.Perm (Fin 3) :=
    (e : (↥H ⧸ CFSG.Open.pCore 2 ↥H) →* Equiv.Perm (Fin 3)).comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hφsurj : Function.Surjective φ := fun p => by
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hφker : ∀ x : ↥H, φ x = 1 ↔ (x : D) ∈ pCoreOf 2 H := by
    intro x
    have hx : φ x = e (QuotientGroup.mk x) := rfl
    rw [hx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
  exact ⟨φ, hφsurj, hφker⟩

theorem perm3_not_comm : ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → a * a = 1 → b ≠ 1 →
    b * b * b = 1 → a * (b * a * b⁻¹) ≠ (b * a * b⁻¹) * a := by
  decide

omit [Finite D] in
theorem conj_comm_of_transvections {a b z q : D} (haz : a * z * a⁻¹ = z) (hbz : b * z * b⁻¹ = z)
    (ha : a * q * a⁻¹ = q ∨ a * q * a⁻¹ = q * z) (hb : b * q * b⁻¹ = q ∨ b * q * b⁻¹ = q * z) :
    (a * b) * q * (a * b)⁻¹ = (b * a) * q * (b * a)⁻¹ := by
  have e1 : (a * b) * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
  have e2 : (b * a) * q * (b * a)⁻¹ = b * (a * q * a⁻¹) * b⁻¹ := by group
  have ha' : a * (q * z) * a⁻¹ = (a * q * a⁻¹) * z := by
    calc a * (q * z) * a⁻¹ = (a * q * a⁻¹) * (a * z * a⁻¹) := by group
      _ = (a * q * a⁻¹) * z := by rw [haz]
  have hb' : b * (q * z) * b⁻¹ = (b * q * b⁻¹) * z := by
    calc b * (q * z) * b⁻¹ = (b * q * b⁻¹) * (b * z * b⁻¹) := by group
      _ = (b * q * b⁻¹) * z := by rw [hbz]
  rw [e1, e2]
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2
  · rw [h2, h1, h2]
  · rw [h2, ha', h1, h2]
  · rw [h2, h1, hb', h2]
  · rw [h2, ha', h1, hb', h2]

theorem Vertex.false_of_transvection {H T : Subgroup D} (hv : Vertex H T) {z v : D}
    (hzZ : z ∈ centerOf T) (hzH : ∀ y ∈ H, y * z * y⁻¹ = z) (hvT : v ∈ T) (hv2 : v * v = 1)
    (hvQ : v ∉ pCoreOf 2 H)
    (hvq : ∀ q ∈ pCoreOf 2 H, q * v * q⁻¹ = v ∨ q * v * q⁻¹ = v * z) : False := by
  obtain ⟨φ, -, hφ⟩ := hv.exists_hom
  obtain ⟨y, hyH, hy3⟩ := hv.exists_order_three
  have hTH : T ≤ H := hv.T_le
  have hQT : pCoreOf 2 H ≤ T := hv.pCoreOf_le
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set D) := le_normalizer_pCoreOf 2 H
  have hvH : v ∈ H := hTH hvT
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hyT : y ∉ T := hv.not_mem_of_orderOf hy3
  have hvz : v * z = z * v := Subgroup.mem_centralizer_iff.mp hzZ.2 v hvT
  have haz : v * z * v⁻¹ = z := by rw [hvz]; group
  have hact : ∀ q ∈ pCoreOf 2 H, v * q * v⁻¹ = q ∨ v * q * v⁻¹ = q * z := by
    intro q hq
    have hqz : q * z = z * q := Subgroup.mem_centralizer_iff.mp hzZ.2 q (hQT hq)
    rcases hvq q hq with h | h
    · left
      have h1 : q * v = v * q := by
        calc q * v = (q * v * q⁻¹) * q := by group
          _ = v * q := by rw [h]
      calc v * q * v⁻¹ = q * v * v⁻¹ := by rw [h1]
        _ = q := by group
    · right
      have h1 : q * v = v * z * q := by
        calc q * v = (q * v * q⁻¹) * q := by group
          _ = v * z * q := by rw [h]
      calc v * q * v⁻¹ = v * q * v := by rw [hvinv]
        _ = v * (q * v) := by group
        _ = v * (v * z * q) := by rw [h1]
        _ = (v * v) * z * q := by group
        _ = z * q := by rw [hv2, one_mul]
        _ = q * z := hqz.symm
  obtain ⟨v', hv'⟩ : ∃ v' : D, v' = y * v * y⁻¹ := ⟨_, rfl⟩
  have hv'H : v' ∈ H := by
    rw [hv']; exact H.mul_mem (H.mul_mem hyH hvH) (H.inv_mem hyH)
  have hbz : v' * z * v'⁻¹ = z := by
    have h1 : y⁻¹ * z * y = z := by
      have := hzH y⁻¹ (H.inv_mem hyH)
      simpa using this
    calc v' * z * v'⁻¹ = y * (v * (y⁻¹ * z * y) * v⁻¹) * y⁻¹ := by rw [hv']; group
      _ = y * (v * z * v⁻¹) * y⁻¹ := by rw [h1]
      _ = y * z * y⁻¹ := by rw [haz]
      _ = z := hzH y hyH
  have hact' : ∀ q ∈ pCoreOf 2 H, v' * q * v'⁻¹ = q ∨ v' * q * v'⁻¹ = q * z := by
    intro q hq
    have hq' : y⁻¹ * q * y ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hQN (H.inv_mem hyH)) q).mp hq
      simpa using this
    have e : v' * q * v'⁻¹ = y * (v * (y⁻¹ * q * y) * v⁻¹) * y⁻¹ := by rw [hv']; group
    have e2 : y * (y⁻¹ * q * y) * y⁻¹ = q := by group
    rcases hact _ hq' with h | h
    · left; rw [e, h, e2]
    · right
      rw [e, h]
      calc y * (y⁻¹ * q * y * z) * y⁻¹ = (y * (y⁻¹ * q * y) * y⁻¹) * (y * z * y⁻¹) := by group
        _ = q * z := by rw [e2, hzH y hyH]
  have hcomm : ∀ q ∈ pCoreOf 2 H, (v * v') * q * (v * v')⁻¹ = (v' * v) * q * (v' * v)⁻¹ :=
    fun q hq => conj_comm_of_transvections haz hbz (hact q hq) (hact' q hq)
  have hgH : (v' * v)⁻¹ * (v * v') ∈ H :=
    H.mul_mem (H.inv_mem (H.mul_mem hv'H hvH)) (H.mul_mem hvH hv'H)
  have hgC : (v' * v)⁻¹ * (v * v') ∈ Subgroup.centralizer (pCoreOf 2 H : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : ((v' * v)⁻¹ * (v * v')) * q * ((v' * v)⁻¹ * (v * v'))⁻¹ = q := by
      calc ((v' * v)⁻¹ * (v * v')) * q * ((v' * v)⁻¹ * (v * v'))⁻¹
          = (v' * v)⁻¹ * ((v * v') * q * (v * v')⁻¹) * (v' * v) := by group
        _ = (v' * v)⁻¹ * ((v' * v) * q * (v' * v)⁻¹) * (v' * v) := by rw [hcomm q hq]
        _ = q := by group
    exact (mul_eq_of_conj_eq h1).symm
  have hgQ : (v' * v)⁻¹ * (v * v') ∈ pCoreOf 2 H := hv.charTwo ⟨hgH, hgC⟩
  let V' : ↥H := ⟨v, hvH⟩
  let Y : ↥H := ⟨y, hyH⟩
  let W : ↥H := ⟨v', hv'H⟩
  have hWdef : W = Y * V' * Y⁻¹ := Subtype.ext hv'
  have hGdef : (⟨(v' * v)⁻¹ * (v * v'), hgH⟩ : ↥H) = (W * V')⁻¹ * (V' * W) := Subtype.ext rfl
  have hφG : φ ((W * V')⁻¹ * (V' * W)) = 1 := by
    rw [← hGdef]; exact (hφ _).mpr hgQ
  simp only [map_mul, map_inv] at hφG
  rw [inv_mul_eq_one] at hφG
  have hWφ : φ W = φ Y * φ V' * (φ Y)⁻¹ := by
    rw [hWdef]; simp only [map_mul, map_inv]
  have ha1 : φ V' ≠ 1 := fun h => hvQ ((hφ V').mp h)
  have ha2 : φ V' * φ V' = 1 := by
    rw [← map_mul]
    have : V' * V' = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hb1 : φ Y ≠ 1 := fun h => hyT (hQT ((hφ Y).mp h))
  have hb3 : φ Y * φ Y * φ Y = 1 := by
    rw [← map_mul, ← map_mul]
    have : Y * Y * Y = 1 := Subtype.ext hy3'
    rw [this, map_one]
  exact perm3_not_comm (φ V') (φ Y) ha1 ha2 hb1 hb3 (by rw [← hWφ]; exact hφG.symm)

end GoldAmL

end F6

end CFSG.Quasithin
