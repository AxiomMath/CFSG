module

public import CFSG.Quasithin.Vol2.Ch12Sec5Odd

public section

namespace CFSG.Quasithin.H13.S125L7m

open Matrix

local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "W10" => Fin 10 → ZMod 2

@[expose] def uni (c : W10) : M5 :=
  !![1, c 0, c 1, c 2, c 3; 0, 1, c 4, c 5, c 6; 0, 0, 1, c 7, c 8; 0, 0, 0, 1, c 9;
    0, 0, 0, 0, 1]

@[expose] def cv (u : M5) : W10 := ![u 0 1, u 0 2, u 0 3, u 0 4, u 1 2, u 1 3, u 1 4, u 2 3,
  u 2 4, u 3 4]

theorem prod_eq_one : ∀ a b c d e : ZMod 2, a * b * c * d * e = 1 →
    a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 := by decide

theorem eq_uni {u : SL5} (hu : S125.IsUpperTri u) : (u : M5) = uni (cv u) := by
  have hdet : (u : M5).det = 1 := u.2
  rw [Matrix.det_of_isUpperTriangular (fun a b hab => hu a b hab), Fin.prod_univ_five] at hdet
  obtain ⟨h0, h1, h2, h3, h4⟩ := prod_eq_one _ _ _ _ _ hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, cv, h0, h1, h2, h3, h4, hu _ _ (by decide : (0 : Fin 5) < 1),
      hu _ _ (by decide : (0 : Fin 5) < 2), hu _ _ (by decide : (0 : Fin 5) < 3),
      hu _ _ (by decide : (0 : Fin 5) < 4), hu _ _ (by decide : (1 : Fin 5) < 2),
      hu _ _ (by decide : (1 : Fin 5) < 3), hu _ _ (by decide : (1 : Fin 5) < 4),
      hu _ _ (by decide : (2 : Fin 5) < 3), hu _ _ (by decide : (2 : Fin 5) < 4),
      hu _ _ (by decide : (3 : Fin 5) < 4)]

theorem mul01 (c d : W10) : (uni c * uni d) 0 1 = c 0 + d 0 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul02 (c d : W10) : (uni c * uni d) 0 2 = c 1 + c 0 * d 4 + d 1 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul12 (c d : W10) : (uni c * uni d) 1 2 = c 4 + d 4 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul13 (c d : W10) : (uni c * uni d) 1 3 = c 5 + c 4 * d 7 + d 5 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul23 (c d : W10) : (uni c * uni d) 2 3 = c 7 + d 7 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul03 (c d : W10) : (uni c * uni d) 0 3 = c 2 + c 0 * d 5 + c 1 * d 7 + d 2 := by
  simp [uni, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem fix1 : ∀ c : W10,
    JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 1 1 = Pi.single 1 1 ↔ c 4 = 0 := by
  decide +kernel

theorem fix4 : ∀ c : W10, c 4 = 0 →
    (JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 4 1 = Pi.single 4 1 ↔ c 0 = 0 ∧ c 1 = 0) := by
  decide +kernel

theorem fix2 : ∀ c : W10,
    JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 2 1 = Pi.single 2 1 ↔ c 5 = 0 ∧ c 7 = 0 := by
  decide +kernel

theorem fix5 : ∀ c : W10, c 0 = 0 → c 1 = 0 → c 4 = 0 → c 5 = 0 → c 7 = 0 →
    (JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 5 1 = Pi.single 5 1 ↔ c 2 = 0) := by
  decide +kernel

@[expose] def ub (b : Fin 4 → ZMod 2) : M5 := uni ![0, 0, 0, b 0, 0, 0, b 1, 0, b 2, b 3]

theorem ub_mul : ∀ b b' : Fin 4 → ZMod 2, ub b * ub b' = ub (b + b') := by decide +kernel

theorem ub_zero : ub 0 = 1 := by decide

theorem ub_inj : ∀ b b' : Fin 4 → ZMod 2, ub b = ub b' → b = b' := by decide +kernel

theorem uni_eq_ub {c : W10} (h0 : c 0 = 0) (h1 : c 1 = 0) (h2 : c 2 = 0) (h4 : c 4 = 0)
    (h5 : c 5 = 0) (h7 : c 7 = 0) : uni c = ub ![c 3, c 6, c 8, c 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni, ub, h0, h1, h2, h4, h5, h7]

theorem add_self_two : ∀ x : ZMod 2, x + x = 0 := by decide

theorem ub_sq (b : Fin 4 → ZMod 2) : ub b * ub b = 1 := by
  rw [ub_mul, show b + b = 0 from funext fun i => add_self_two (b i), ub_zero]

theorem det_ub (b : Fin 4 → ZMod 2) : (ub b).det = 1 :=
  S125Odd.det_eq_one_of_pow (n := 2) (by norm_num) (by rw [pow_two, ub_sq])

@[expose] def Ub (b : Fin 4 → ZMod 2) : SL5 := ⟨ub b, det_ub b⟩

@[expose] def Urad : Subgroup SL5 where
  carrier := {u | ∃ b, (u : M5) = ub b}
  one_mem' := ⟨0, by rw [ub_zero]; rfl⟩
  mul_mem' := by
    rintro u v ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b + b', by rw [Matrix.SpecialLinearGroup.coe_mul, hb, hb', ub_mul]⟩
  inv_mem' := by
    rintro u ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have h1 : u * u = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, hb, ub_sq]
      rfl)
    rw [inv_eq_of_mul_eq_one_right h1, hb]

theorem Ub_mem (b : Fin 4 → ZMod 2) : Ub b ∈ Urad := ⟨b, rfl⟩

theorem card_Urad : Nat.card Urad = 16 := by
  have hbij : Function.Bijective (fun b : Fin 4 → ZMod 2 => (⟨Ub b, Ub_mem b⟩ : ↥Urad)) := by
    refine ⟨fun b b' h => ub_inj b b' (congrArg (fun u : ↥Urad => ((u : SL5) : M5)) h), ?_⟩
    rintro ⟨u, b, hb⟩
    exact ⟨b, Subtype.ext (Subtype.ext hb.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  rfl

@[expose] def xb (b : Fin 4 → ZMod 2) : W10 := ![0, 0, 0, b 0, 0, 0, b 1, 0, b 2, b 3]

theorem ub_faithful : ∀ b : Fin 4 → ZMod 2,
    (∀ k : Fin 10, JonesParshall.wedgeMat (ub b) *ᵥ Pi.single k 1 = Pi.single k 1) → b = 0 := by
  decide +kernel

theorem ub_fix_xb : ∀ b : Fin 4 → ZMod 2, JonesParshall.wedgeMat (ub b) *ᵥ xb b = xb b := by
  decide +kernel

theorem ub_not_fix_xb : ∀ b b' : Fin 4 → ZMod 2, b ≠ 0 → b' ≠ 0 → b' ≠ b →
    JonesParshall.wedgeMat (ub b') *ᵥ xb b ≠ xb b := by
  decide +kernel

theorem ub_sq_one (b : Fin 4 → ZMod 2) : Ub b * Ub b = 1 := Subtype.ext (ub_sq b)

theorem Ub_ne_one {b : Fin 4 → ZMod 2} (hb : b ≠ 0) : Ub b ≠ 1 := fun h =>
  hb (ub_inj b 0 (by rw [ub_zero]; exact congrArg Subtype.val h))

theorem orderOf_Ub {b : Fin 4 → ZMod 2} (hb : b ≠ 0) : orderOf (Ub b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact ub_sq_one b) (Ub_ne_one hb)

theorem ub_fix_V6 : ∀ b : Fin 4 → ZMod 2, ∀ k : Fin 10,
    (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7) →
      JonesParshall.wedgeMat (ub b) *ᵥ Pi.single k 1 = Pi.single k 1 := by
  decide +kernel

theorem ub_rows : ∀ b : Fin 4 → ZMod 2,
    (Matrix.diagonal ![0, 0, 0, 1, 0, 0, 1, 0, 1, 1] : Matrix (Fin 10) (Fin 10) (ZMod 2)) *
      JonesParshall.wedgeMat (ub b) = Matrix.diagonal ![0, 0, 0, 1, 0, 0, 1, 0, 1, 1] := by
  decide +kernel

@[expose] def src : Fin 10 → Fin 10 := ![3, 3, 3, 0, 6, 6, 0, 8, 0, 0]

@[expose] def bsrc : Fin 10 → Fin 4 → ZMod 2 :=
  ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], 0, ![0, 0, 1, 0], ![0, 0, 0, 1], 0, ![0, 0, 0, 1],
    0, 0]

theorem single_eq_comm : ∀ l : Fin 10, (l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 4 ∨ l = 5 ∨ l = 7) →
    (Pi.single l 1 : W10) =
      Pi.single (src l) 1 - JonesParshall.wedgeMat (ub (bsrc l)) *ᵥ Pi.single (src l) 1 := by
  decide +kernel

theorem exists_ker {E : Subgroup SL5} (f g : SL5 → ZMod 2)
    (hf : ∀ u ∈ E, ∀ v ∈ E, f (u * v) = f u + f v)
    (hg : ∀ u ∈ E, ∀ v ∈ E, g (u * v) = g u + g v) :
    ∃ B : Subgroup SL5, B ≤ E ∧ B.relIndex E ≤ 4 ∧ ∀ u ∈ B, f u = 0 ∧ g u = 0 := by
  have hf1 : f 1 = 0 := by
    have := hf 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    calc f 1 = f 1 + f 1 - f 1 := by ring
      _ = 0 := by rw [← this, sub_self]
  have hg1 : g 1 = 0 := by
    have := hg 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    calc g 1 = g 1 + g 1 - g 1 := by ring
      _ = 0 := by rw [← this, sub_self]
  let φ : ↥E →* Multiplicative (ZMod 2 × ZMod 2) :=
    { toFun := fun u => Multiplicative.ofAdd (f u, g u)
      map_one' := by
        change Multiplicative.ofAdd (f 1, g 1) = 1
        rw [hf1, hg1]
        rfl
      map_mul' := fun u v => by
        change Multiplicative.ofAdd (f (u * v), g (u * v)) = Multiplicative.ofAdd (f u, g u) *
          Multiplicative.ofAdd (f v, g v)
        rw [hf u u.2 v v.2, hg u u.2 v v.2, ← ofAdd_add]
        rfl }
  refine ⟨φ.ker.map E.subtype, fun _ ⟨u, _, hu⟩ => hu ▸ u.2, ?_, ?_⟩
  · have h1 : (φ.ker.map E.subtype).subgroupOf E = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
    rw [Subgroup.relIndex, h1, Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 2 × ZMod 2)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 4 := by rw [Nat.card_eq_fintype_card]; rfl
  · rintro _ ⟨u, hu, rfl⟩
    have h := congrArg Multiplicative.toAdd (φ.mem_ker.1 hu)
    change (f u, g u) = (0, 0) at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sq02 : ∀ a b e : ZMod 2, a + b * e + a = b * e := by decide

theorem eq_urad {E : Subgroup SL5} (h1 : ∀ u ∈ E, S125.IsUpperTri u) (h2 : ∀ u ∈ E, u * u = 1)
    (h3 : E ≠ ⊥) (h4 : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E ≤ 4 →
      ∀ x : W10, (∀ u ∈ B, JonesParshall.wedgeRep u x = x) →
        ∀ u ∈ E, JonesParshall.wedgeRep u x = x) :
    E = Urad := by
  have huni : ∀ u ∈ E, (u : M5) = uni (cv u) := fun u hu => eq_uni (h1 u hu)
  have hmul : ∀ u ∈ E, ∀ v ∈ E, ((u * v : SL5) : M5) = uni (cv u) * uni (cv v) := fun u hu v hv =>
    by rw [Matrix.SpecialLinearGroup.coe_mul, ← huni u hu, ← huni v hv]
  have hcv : ∀ u ∈ E, ∀ v ∈ E, ∀ i j : Fin 5,
      ((u * v : SL5) : M5) i j = (uni (cv u) * uni (cv v)) i j := fun u hu v hv i j => by
    rw [hmul u hu v hv]
  have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv => by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (h2 u hu)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h2 v hv)
    have huv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (h2 (u * v) (E.mul_mem hu hv))
    calc u * v = (u * v)⁻¹ := huv.symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by rw [hu', hv']
  have hfix : ∀ (x : W10) (u : SL5), JonesParshall.wedgeRep u x = x ↔
      JonesParshall.wedgeMat (u : M5) *ᵥ x = x := fun x u => by rw [S125ZV.wedgeRep_apply]
  have hsq : ∀ u ∈ E, cv u 0 * cv u 4 = 0 := fun u hu => by
    have h := hcv u hu u hu 0 2
    rw [h2 u hu, mul02, sq02] at h
    exact h.symm
  have hc : ∀ u ∈ E, ∀ v ∈ E, cv u 0 * cv v 4 = cv v 0 * cv u 4 := fun u hu v hv => by
    have h := (hcv u hu v hv 0 2).symm.trans ((congrArg (fun w : SL5 => (w : M5) 0 2)
      (hcomm u hu v hv)).trans (hcv v hv u hu 0 2))
    rw [mul02, mul02] at h
    linear_combination h
  have hV3 : ∀ u ∈ E, cv u 0 = 0 ∧ cv u 1 = 0 ∧ cv u 4 = 0 := by
    have key : ∀ f g : SL5 → ZMod 2, (∀ u ∈ E, ∀ v ∈ E, f (u * v) = f u + f v) →
        (∀ u ∈ E, ∀ v ∈ E, g (u * v) = g u + g v) →
        (∀ u ∈ E, f u = 0 → g u = 0 → cv u 0 = 0 ∧ cv u 1 = 0 ∧ cv u 4 = 0) →
        ∀ u ∈ E, cv u 0 = 0 ∧ cv u 1 = 0 ∧ cv u 4 = 0 := by
      intro f g hf hg hker
      obtain ⟨B, hBE, hBi, hB⟩ := exists_ker f g hf hg
      have hx1 := h4 B hBE hBi (Pi.single 1 1) fun u hu => by
        obtain ⟨hfu, hgu⟩ := hB u hu
        obtain ⟨-, -, h4u⟩ := hker u (hBE hu) hfu hgu
        rw [hfix, huni u (hBE hu)]
        exact (fix1 _).2 h4u
      have hx4 := h4 B hBE hBi (Pi.single 4 1) fun u hu => by
        obtain ⟨hfu, hgu⟩ := hB u hu
        obtain ⟨h0u, h1u, h4u⟩ := hker u (hBE hu) hfu hgu
        rw [hfix, huni u (hBE hu)]
        exact (fix4 _ h4u).2 ⟨h0u, h1u⟩
      intro u hu
      have e1 := (fix1 (cv u)).1 (by rw [← huni u hu, ← hfix]; exact hx1 u hu)
      have e4 := (fix4 (cv u) e1).1 (by rw [← huni u hu, ← hfix]; exact hx4 u hu)
      exact ⟨e4.1, e4.2, e1⟩
    by_cases hA : ∀ u ∈ E, cv u 0 = 0
    · refine key (fun u => cv u 1) (fun u => cv u 4) (fun u hu v hv => ?_)
        (fun u hu v hv => ?_) (fun u hu h1u h4u => ⟨hA u hu, h1u, h4u⟩)
      · change ((u * v : SL5) : M5) 0 2 = _
        rw [hcv u hu v hv, mul02, hA u hu, zero_mul, add_zero]
      · change ((u * v : SL5) : M5) 1 2 = _
        rw [hcv u hu v hv, mul12]
    · simp only [not_forall] at hA
      obtain ⟨u₀, hu₀, h0⟩ := hA
      have h01 : cv u₀ 0 = 1 := (zmod2_cases _).resolve_left h0
      have hB : ∀ v ∈ E, cv v 4 = 0 := fun v hv => by
        have h := hc u₀ hu₀ v hv
        rw [h01, one_mul] at h
        have h4u : cv u₀ 4 = 0 := by
          have := hsq u₀ hu₀
          rwa [h01, one_mul] at this
        rw [h4u, mul_zero] at h
        exact h
      refine key (fun u => cv u 0) (fun u => cv u 1) (fun u hu v hv => ?_)
        (fun u hu v hv => ?_) (fun u hu h0u h1u => ⟨h0u, h1u, hB u hu⟩)
      · change ((u * v : SL5) : M5) 0 1 = _
        rw [hcv u hu v hv, mul01]
      · change ((u * v : SL5) : M5) 0 2 = _
        rw [hcv u hu v hv, mul02, hB v hv, mul_zero, add_zero]
  have hV3' : ∀ u ∈ E, cv u 5 = 0 ∧ cv u 7 = 0 := by
    obtain ⟨B, hBE, hBi, hB⟩ := exists_ker (E := E) (fun u => cv u 5) (fun u => cv u 7)
      (fun u hu v hv => by
        change ((u * v : SL5) : M5) 1 3 = _
        rw [hcv u hu v hv, mul13, (hV3 u hu).2.2, zero_mul, add_zero])
      (fun u hu v hv => by
        change ((u * v : SL5) : M5) 2 3 = _
        rw [hcv u hu v hv, mul23])
    have hx := h4 B hBE hBi (Pi.single 2 1) fun u hu => by
      rw [hfix, huni u (hBE hu)]
      exact (fix2 _).2 (hB u hu)
    intro u hu
    exact (fix2 (cv u)).1 (by rw [← huni u hu, ← hfix]; exact hx u hu)
  have hV6 : ∀ u ∈ E, cv u 2 = 0 := by
    obtain ⟨B, hBE, hBi, hB⟩ := exists_ker (E := E) (fun u => cv u 2) (fun _ => 0)
      (fun u hu v hv => by
        change ((u * v : SL5) : M5) 0 3 = _
        rw [hcv u hu v hv, mul03, (hV3 u hu).1, (hV3 u hu).2.1, zero_mul, zero_mul, add_zero,
          add_zero])
      (fun _ _ _ _ => by ring)
    have hx := h4 B hBE hBi (Pi.single 5 1) fun u hu => by
      obtain ⟨h0u, h1u, h4u⟩ := hV3 u (hBE hu)
      obtain ⟨h5u, h7u⟩ := hV3' u (hBE hu)
      rw [hfix, huni u (hBE hu)]
      exact (fix5 _ h0u h1u h4u h5u h7u).2 (hB u hu).1
    intro u hu
    obtain ⟨h0u, h1u, h4u⟩ := hV3 u hu
    obtain ⟨h5u, h7u⟩ := hV3' u hu
    exact (fix5 (cv u) h0u h1u h4u h5u h7u).1 (by rw [← huni u hu, ← hfix]; exact hx u hu)
  have hEU : E ≤ Urad := fun u hu => by
    obtain ⟨h0u, h1u, h4u⟩ := hV3 u hu
    obtain ⟨h5u, h7u⟩ := hV3' u hu
    exact ⟨_, (huni u hu).trans (uni_eq_ub h0u h1u (hV6 u hu) h4u h5u h7u)⟩
  have hub : ∀ u ∈ E, ∃ b, u = Ub b := fun u hu => by
    obtain ⟨b, hb⟩ := hEU hu
    exact ⟨b, Subtype.ext hb⟩
  have hdvd : Nat.card E ∣ 16 := by
    rw [← card_Urad]
    exact Subgroup.card_dvd_of_le hEU
  have hcard : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E * Nat.card B = Nat.card E := fun B hB => by
    have := Subgroup.relIndex_mul_card (H := B) (K := E)
    rwa [inf_of_le_left hB] at this
  have hgt4 : 4 < Nat.card E := by
    by_contra hle
    rw [not_lt] at hle
    have hrel : (⊥ : Subgroup SL5).relIndex E ≤ 4 := by
      rw [Subgroup.relIndex_bot_left]
      exact hle
    apply h3
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨b, rfl⟩ := hub u hu
    have hb : b = 0 := ub_faithful b fun k => by
      have := h4 ⊥ bot_le hrel (Pi.single k 1) (fun u hu => by
        rw [Subgroup.mem_bot.1 hu, map_one, Module.End.one_apply]) (Ub b) hu
      rwa [hfix] at this
    rw [Subgroup.mem_bot, hb]
    exact Subtype.ext ub_zero
  have hne8 : Nat.card E ≠ 8 := by
    intro h8
    obtain ⟨u, huE, hu1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left h3
    obtain ⟨b, hb⟩ := hub u huE
    have hb0 : b ≠ 0 := fun h => hu1 (by rw [hb, h]; exact Subtype.ext ub_zero)
    have hz : Nat.card (Subgroup.zpowers (u : SL5)) = 2 := by
      rw [Nat.card_zpowers]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact h2 u huE) hu1
    have hzE : Subgroup.zpowers (u : SL5) ≤ E := (Subgroup.zpowers_le (G := SL5)).2 huE
    have hrel : (Subgroup.zpowers (u : SL5)).relIndex E ≤ 4 := by
      have := hcard _ hzE
      rw [hz, h8] at this
      omega
    obtain ⟨u', hu'E, hu'z⟩ : ∃ u' ∈ E, u' ∉ Subgroup.zpowers (u : SL5) := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      have := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers (u : SL5) from hc)
      omega
    obtain ⟨b', hb'⟩ := hub u' hu'E
    have hb'0 : b' ≠ 0 := fun h => hu'z (by
      rw [hb', h, show Ub 0 = 1 from Subtype.ext ub_zero]
      exact Subgroup.one_mem _)
    have hb'b : b' ≠ b := fun h => hu'z (by
      rw [hb', h, ← hb]
      exact Subgroup.mem_zpowers _)
    have hx := h4 _ hzE hrel (xb b) (fun v hv => by
      have hst : Subgroup.zpowers (u : SL5) ≤ S125Odd.stab (xb b) :=
        (Subgroup.zpowers_le (G := SL5)).2 (by
          change JonesParshall.wedgeRep u (xb b) = xb b
          rw [hfix, hb]
          exact ub_fix_xb b)
      exact hst hv) u' hu'E
    rw [hfix, hb'] at hx
    exact ub_not_fix_xb b b' hb0 hb'0 hb'b hx
  have h16 : Nat.card E = 16 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card E ∣ 2 ^ 4 from hdvd)
    have hk4 : k = 4 := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · rw [hk'] at hgt4
        norm_num at hgt4
      · rw [hk'] at hgt4
        norm_num at hgt4
      · rw [hk'] at hgt4
        norm_num at hgt4
      · exact absurd (hk'.trans (by norm_num)) hne8
      · rfl
    rw [hk', hk4]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hEU (by rw [card_Urad, h16])

end CFSG.Quasithin.H13.S125L7m
