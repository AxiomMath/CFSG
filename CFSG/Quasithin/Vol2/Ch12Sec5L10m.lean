module

public import CFSG.Quasithin.Vol2.Ch12Sec5L7m

public section

namespace CFSG.Quasithin.H13.S125L10m

open Matrix S125L7m

local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "W10" => Fin 10 → ZMod 2

theorem com1 : ∀ c : W10, c 4 = 1 →
    JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 1 1 = Pi.single 1 1 + Pi.single 0 1 := by
  decide +kernel

theorem com4 : ∀ c : W10, c 0 = 0 → c 1 = 1 →
    JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 4 1 = Pi.single 4 1 + Pi.single 0 1 := by
  decide +kernel

theorem com2 : ∀ c : W10, c 5 = 1 → c 7 = 0 →
    JonesParshall.wedgeMat (uni c) *ᵥ Pi.single 2 1 = Pi.single 2 1 + Pi.single 0 1 := by
  decide +kernel

theorem exists_ker' {E : Subgroup SL5} (f g : SL5 → ZMod 2)
    (hf : ∀ u ∈ E, ∀ v ∈ E, f (u * v) = f u + f v)
    (hg : ∀ u ∈ E, ∀ v ∈ E, g (u * v) = g u + g v) :
    ∃ B : Subgroup SL5, B ≤ E ∧ B.relIndex E ≤ 4 ∧ (∀ u ∈ B, f u = 0 ∧ g u = 0) ∧
      (B.relIndex E ≤ 2 ∨ ∀ a b : ZMod 2, ∃ u ∈ E, f u = a ∧ g u = b) := by
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
  have hrel : (φ.ker.map E.subtype).relIndex E = Nat.card φ.range := by
    have h1 : (φ.ker.map E.subtype).subgroupOf E = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
    rw [Subgroup.relIndex, h1, Subgroup.index_ker]
  have hcard4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hdvd : Nat.card φ.range ∣ 4 := hcard4 ▸ Subgroup.card_subgroup_dvd_card _
  refine ⟨φ.ker.map E.subtype, fun _ ⟨u, _, hu⟩ => hu ▸ u.2, ?_, ?_, ?_⟩
  · rw [hrel]
    exact Nat.le_of_dvd (by norm_num) hdvd
  · rintro _ ⟨u, hu, rfl⟩
    have h := congrArg Multiplicative.toAdd (φ.mem_ker.1 hu)
    change (f u, g u) = (0, 0) at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rw [hrel]
    rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card φ.range ∣ 2 ^ 2 from hdvd) with
      ⟨k, hk, hk'⟩
    interval_cases k
    · left
      rw [hk']
      norm_num
    · left
      rw [hk']
      norm_num
    · right
      have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk', hcard4]; norm_num)
      intro a b
      obtain ⟨u, hu⟩ := (MonoidHom.range_eq_top.1 htop) (Multiplicative.ofAdd (a, b))
      refine ⟨u, u.2, ?_⟩
      have h := congrArg Multiplicative.toAdd hu
      change (f u, g u) = (a, b) at h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem le_urad {E : Subgroup SL5} (h1 : ∀ u ∈ E, S125.IsUpperTri u) (h2 : ∀ u ∈ E, u * u = 1)
    (h4 : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E ≤ 2 →
      ∀ x : W10, (∀ u ∈ B, JonesParshall.wedgeRep u x = x) →
        ∀ u ∈ E, JonesParshall.wedgeRep u x = x)
    (hgeo : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E ≤ 4 →
      ∀ x : W10, (∀ u ∈ B, JonesParshall.wedgeRep u x = x) →
        ∀ u ∈ E, JonesParshall.wedgeRep u x ≠ x + Pi.single 0 1) :
    E ≤ Urad := by
  have huni : ∀ u ∈ E, (u : M5) = uni (cv u) := fun u hu => eq_uni (h1 u hu)
  have hcv : ∀ u ∈ E, ∀ v ∈ E, ∀ i j : Fin 5,
      ((u * v : SL5) : M5) i j = (uni (cv u) * uni (cv v)) i j := fun u hu v hv i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← huni u hu, ← huni v hv]
  have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv => by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (h2 u hu)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h2 v hv)
    have huv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (h2 (u * v) (E.mul_mem hu hv))
    calc u * v = (u * v)⁻¹ := huv.symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by rw [hu', hv']
  have hfix : ∀ (x : W10) (u : SL5), JonesParshall.wedgeRep u x = x ↔
      JonesParshall.wedgeMat (u : M5) *ᵥ x = x := fun x u => by rw [S125ZV.wedgeRep_apply]
  have hrep : ∀ (x : W10) (u : SL5) (hu : u ∈ E), JonesParshall.wedgeRep u x =
      JonesParshall.wedgeMat (uni (cv u)) *ᵥ x := fun x u hu => by
    rw [S125ZV.wedgeRep_apply]
    conv_lhs => rw [huni u hu]
  have hsq : ∀ u ∈ E, cv u 0 * cv u 4 = 0 := fun u hu => by
    have h := hcv u hu u hu 0 2
    rw [h2 u hu, mul02, S125L7m.sq02] at h
    exact h.symm
  have hc : ∀ u ∈ E, ∀ v ∈ E, cv u 0 * cv v 4 = cv v 0 * cv u 4 := fun u hu v hv => by
    have h := (hcv u hu v hv 0 2).symm.trans ((congrArg (fun w : SL5 => (w : M5) 0 2)
      (hcomm u hu v hv)).trans (hcv v hv u hu 0 2))
    rw [mul02, mul02] at h
    linear_combination h
  have hV3 : ∀ u ∈ E, cv u 0 = 0 ∧ cv u 1 = 0 ∧ cv u 4 = 0 := by
    by_cases hA : ∀ u ∈ E, cv u 0 = 0
    · obtain ⟨B, hBE, hB4, hB, hB2⟩ := exists_ker' (E := E) (fun u => cv u 1) (fun u => cv u 4)
        (fun u hu v hv => by
          change ((u * v : SL5) : M5) 0 2 = _
          rw [hcv u hu v hv, mul02, hA u hu, zero_mul, add_zero])
        (fun u hu v hv => by
          change ((u * v : SL5) : M5) 1 2 = _
          rw [hcv u hu v hv, mul12])
      rcases hB2 with hB2 | hsurj
      · have hx1 := h4 B hBE hB2 (Pi.single 1 1) fun u hu => by
          rw [hfix, huni u (hBE hu)]
          exact (fix1 _).2 (hB u hu).2
        have hx4 := h4 B hBE hB2 (Pi.single 4 1) fun u hu => by
          rw [hfix, huni u (hBE hu)]
          exact (fix4 _ (hB u hu).2).2 ⟨hA u (hBE hu), (hB u hu).1⟩
        intro u hu
        have e1 := (fix1 (cv u)).1 (by rw [← huni u hu, ← hfix]; exact hx1 u hu)
        have e4 := (fix4 (cv u) e1).1 (by rw [← huni u hu, ← hfix]; exact hx4 u hu)
        exact ⟨e4.1, e4.2, e1⟩
      · exfalso
        obtain ⟨u, hu, -, hu4⟩ := hsurj 0 1
        refine hgeo B hBE hB4 (Pi.single 1 1) (fun v hv => ?_) u hu ?_
        · rw [hfix, huni v (hBE hv)]
          exact (fix1 _).2 (hB v hv).2
        · rw [hrep _ u hu]
          exact com1 _ hu4
    · simp only [not_forall] at hA
      obtain ⟨u₀, hu₀, h0⟩ := hA
      have h01 : cv u₀ 0 = 1 := (S125L7m.zmod2_cases _).resolve_left h0
      have hB4' : ∀ v ∈ E, cv v 4 = 0 := fun v hv => by
        have h := hc u₀ hu₀ v hv
        rw [h01, one_mul] at h
        have h4u : cv u₀ 4 = 0 := by
          have := hsq u₀ hu₀
          rwa [h01, one_mul] at this
        rw [h4u, mul_zero] at h
        exact h
      obtain ⟨B, hBE, hB4, hB, hB2⟩ := exists_ker' (E := E) (fun u => cv u 0) (fun u => cv u 1)
        (fun u hu v hv => by
          change ((u * v : SL5) : M5) 0 1 = _
          rw [hcv u hu v hv, mul01])
        (fun u hu v hv => by
          change ((u * v : SL5) : M5) 0 2 = _
          rw [hcv u hu v hv, mul02, hB4' v hv, mul_zero, add_zero])
      rcases hB2 with hB2 | hsurj
      · have hx4 := h4 B hBE hB2 (Pi.single 4 1) fun u hu => by
          rw [hfix, huni u (hBE hu)]
          exact (fix4 _ (hB4' u (hBE hu))).2 (hB u hu)
        intro u hu
        have e4 := (fix4 (cv u) (hB4' u hu)).1 (by rw [← huni u hu, ← hfix]; exact hx4 u hu)
        exact ⟨e4.1, e4.2, hB4' u hu⟩
      · exfalso
        obtain ⟨u, hu, hu0, hu1⟩ := hsurj 0 1
        refine hgeo B hBE hB4 (Pi.single 4 1) (fun v hv => ?_) u hu ?_
        · rw [hfix, huni v (hBE hv)]
          exact (fix4 _ (hB4' v (hBE hv))).2 (hB v hv)
        · rw [hrep _ u hu]
          exact com4 _ hu0 hu1
  have hV3' : ∀ u ∈ E, cv u 5 = 0 ∧ cv u 7 = 0 := by
    obtain ⟨B, hBE, hB4, hB, hB2⟩ := exists_ker' (E := E) (fun u => cv u 5) (fun u => cv u 7)
      (fun u hu v hv => by
        change ((u * v : SL5) : M5) 1 3 = _
        rw [hcv u hu v hv, mul13, (hV3 u hu).2.2, zero_mul, add_zero])
      (fun u hu v hv => by
        change ((u * v : SL5) : M5) 2 3 = _
        rw [hcv u hu v hv, mul23])
    rcases hB2 with hB2 | hsurj
    · have hx := h4 B hBE hB2 (Pi.single 2 1) fun u hu => by
        rw [hfix, huni u (hBE hu)]
        exact (fix2 _).2 (hB u hu)
      intro u hu
      exact (fix2 (cv u)).1 (by rw [← huni u hu, ← hfix]; exact hx u hu)
    · exfalso
      obtain ⟨u, hu, hu5, hu7⟩ := hsurj 1 0
      refine hgeo B hBE hB4 (Pi.single 2 1) (fun v hv => ?_) u hu ?_
      · rw [hfix, huni v (hBE hv)]
        exact (fix2 _).2 (hB v hv)
      · rw [hrep _ u hu]
        exact com2 _ hu5 hu7
  have hV6 : ∀ u ∈ E, cv u 2 = 0 := by
    obtain ⟨B, hBE, hB, hBi⟩ : ∃ B : Subgroup SL5, B ≤ E ∧ (∀ u ∈ B, cv u 2 = 0) ∧
        B.relIndex E ≤ 2 := by
      obtain ⟨B, hBE, -, hB, hB2⟩ := exists_ker' (E := E) (fun u => cv u 2) (fun _ => 0)
        (fun u hu v hv => by
          change ((u * v : SL5) : M5) 0 3 = _
          rw [hcv u hu v hv, mul03, (hV3 u hu).1, (hV3 u hu).2.1, zero_mul, zero_mul, add_zero,
            add_zero])
        (fun _ _ _ _ => by ring)
      rcases hB2 with hB2 | hsurj
      · exact ⟨B, hBE, fun u hu => (hB u hu).1, hB2⟩
      · obtain ⟨u, -, -, h⟩ := hsurj 0 1
        exact absurd h (by decide)
    have hx := h4 B hBE hBi (Pi.single 5 1) fun u hu => by
      obtain ⟨h0u, h1u, h4u⟩ := hV3 u (hBE hu)
      obtain ⟨h5u, h7u⟩ := hV3' u (hBE hu)
      rw [hfix, huni u (hBE hu)]
      exact (fix5 _ h0u h1u h4u h5u h7u).2 (hB u hu)
    intro u hu
    obtain ⟨h0u, h1u, h4u⟩ := hV3 u hu
    obtain ⟨h5u, h7u⟩ := hV3' u hu
    exact (fix5 (cv u) h0u h1u h4u h5u h7u).1 (by rw [← huni u hu, ← hfix]; exact hx u hu)
  intro u hu
  obtain ⟨h0u, h1u, h4u⟩ := hV3 u hu
  obtain ⟨h5u, h7u⟩ := hV3' u hu
  exact ⟨_, (huni u hu).trans (uni_eq_ub h0u h1u (hV6 u hu) h4u h5u h7u)⟩

@[expose] def ybM (b : Fin 4 → ZMod 2) : M5 :=
  if b = ![0, 0, 0, 1] then !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 0, 1, 0] then !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 0, 1, 1] then !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 0, 0] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 0, 1] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 1, 0] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 1, 1] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 0, 0] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 0, 1] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 1, 0] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 1, 1] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 0, 0] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 0, 1] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 1, 0] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 1, 1] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else 1

@[expose] def ybI (b : Fin 4 → ZMod 2) : M5 :=
  if b = ![0, 0, 0, 1] then !![0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 0, 1, 0] then !![0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 0, 1, 1] then !![0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 0, 0] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 0, 1] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 1, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 1, 0] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![0, 1, 1, 1] then !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 0, 0] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 0, 1] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 1, 0] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 0, 1, 1] then !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 0, 0] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 0, 1] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 1, 0] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else if b = ![1, 1, 1, 1] then !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  else 1

theorem ybM_spec : ∀ b : Fin 4 → ZMod 2, b ≠ 0 →
    ybM b * ub ![1, 0, 0, 0] = ub b * ybM b ∧ ybM b * ybI b = 1 := by
  decide +kernel

theorem ybM_row : ∀ b : Fin 4 → ZMod 2,
    ybM b 4 0 = 0 ∧ ybM b 4 1 = 0 ∧ ybM b 4 2 = 0 ∧ ybM b 4 3 = 0 := by
  decide +kernel

theorem det_ybM {b : Fin 4 → ZMod 2} (hb : b ≠ 0) : (ybM b).det = 1 := by
  have h := congrArg Matrix.det (ybM_spec b hb).2
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases S125L7m.zmod2_cases (ybM b).det with h0 | h0
  · rw [h0, zero_mul] at h
    exact absurd h (by decide)
  · exact h0

theorem ybM_zero : ybM 0 = 1 := by decide

theorem det_ybM_all (b : Fin 4 → ZMod 2) : (ybM b).det = 1 := by
  by_cases hb : b = 0
  · rw [hb, ybM_zero, Matrix.det_one]
  · exact det_ybM hb

@[expose] def YB (b : Fin 4 → ZMod 2) : SL5 := ⟨ybM b, det_ybM_all b⟩

theorem YB_val (b : Fin 4 → ZMod 2) : ((YB b : SL5) : M5) = ybM b := rfl

theorem YB_conj {b : Fin 4 → ZMod 2} (hb : b ≠ 0) :
    YB b * Ub ![1, 0, 0, 0] * (YB b)⁻¹ = Ub b := by
  have h : YB b * Ub ![1, 0, 0, 0] = Ub b * YB b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, YB_val]
    exact (ybM_spec b hb).1
  rw [h, mul_inv_cancel_right]

theorem YB_stab (b : Fin 4 → ZMod 2) : S125.StabGam 4 (YB b) := by
  intro i j hj hi
  have hi4 : i = 4 := Fin.ext (by have := i.2; omega)
  subst hi4
  rw [YB_val]
  obtain ⟨h0, h1, h2, h3⟩ := ybM_row b
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact absurd hj (by decide)

end CFSG.Quasithin.H13.S125L10m
