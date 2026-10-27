module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H54
public import CFSG.Quasithin.Vol2.Ch10SecQ9H11

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

open CFSG.Quasithin

variable {Y : Type} [Group Y] [Finite Y] {q : ℕ} [hq : Fact q.Prime]

omit [Finite Y] hq in
theorem pow_eq_one_of_mem_map {P : Subgroup ↥(CFSG.pCore q Y)} (hsc : IsSupercritical q P) :
    ∀ d ∈ P.map (CFSG.pCore q Y).subtype, d ^ q = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hsc.pow_eq_one x hx, map_one]

omit [Finite Y] in
theorem mem_frattiniIn_of_fix (hq2 : q ≠ 2) {V : Subgroup Y} (hexp : ∀ d ∈ V, d ^ q = 1)
    {w : Y} (hinv : ∀ d ∈ V, d * (w * d * w⁻¹) ∈ frattiniIn V) {d : Y} (hd : d ∈ V)
    (hw : w * d * w⁻¹ = d) : d ∈ frattiniIn V := by
  have h2 := hinv d hd
  rw [hw] at h2
  obtain ⟨k, hk⟩ := hq.out.odd_of_ne_two hq2
  have hd' : d = (d * d) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    have h : 2 * (k + 1) = q + 1 := by omega
    rw [h, pow_succ, hexp d hd, one_mul]
  rw [hd']
  exact (frattiniIn V).pow_mem h2 _

theorem frattiniIn_eq_bot_of_elem {P : Subgroup ↥(CFSG.pCore q Y)} (hsc : IsSupercritical q P)
    (hP : IsElemAbelianOfRank q 2 ↥P) : frattiniIn (P.map (CFSG.pCore q Y).subtype) = ⊥ := by
  set V := P.map (CFSG.pCore q Y).subtype with hV
  obtain ⟨f⟩ : Nonempty (↥P ≃* Multiplicative (Fin 2 → ZMod q)) := hP
  let e : ↥P ≃* ↥V :=
    P.equivMapOfInjective (CFSG.pCore q Y).subtype (CFSG.pCore q Y).subtype_injective
  have : Fact (IsPGroup q ↥V) := ⟨isPGroup_map P⟩
  have hcommV : ∀ a b : ↥V, a * b = b * a := by
    intro a b
    apply (e.symm.trans f).injective
    rw [map_mul, map_mul, mul_comm]
  have : IsElementaryAbelian q ↥V :=
    { toIsMulCommutative := IsMulCommutative.of_comm hcommV
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact pow_eq_one_of_mem_map hsc a a.2) }
  unfold frattiniIn
  rw [CFSG.frattini_eq_bot_of_isElementaryAbelian (R := ↥V) (p := q), Subgroup.map_bot]

omit [Finite Y] hq in
theorem card_frattini_le_of_extraspecial {R : Type*} [Group R] [Finite R] [Fact q.Prime]
    (hex : CFSG.IsExtraspecial q R) (hR : IsPGroup q R) : Nat.card (frattini R) ≤ q := by
  have : Fact (IsPGroup q (R ⧸ Subgroup.center R)) := ⟨hR.to_quotient _⟩
  have : IsElementaryAbelian q (R ⧸ Subgroup.center R) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian q R
  have hbot := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := R ⧸ Subgroup.center R) (p := q)
  have hle := frattini_le_comap_frattini_of_surjective
    (QuotientGroup.mk'_surjective (Subgroup.center R))
  rw [hbot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
  calc Nat.card (frattini R) ≤ Nat.card (Subgroup.center R) := Subgroup.card_le_of_le hle
    _ = q := CFSG.IsExtraspecial.center_order_p q R

theorem card_inf_centralizer_le (hq2 : q ≠ 2) {P : Subgroup ↥(CFSG.pCore q Y)}
    (hsc : IsSupercritical q P) (hPt : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P)
    (hO : IsPOnePlusTwo q ↥(CFSG.pCore q Y) ∨ IsHomocyclicRank2 q ↥(CFSG.pCore q Y)) {w : Y}
    (hinv : ∀ d ∈ P.map (CFSG.pCore q Y).subtype,
      d * (w * d * w⁻¹) ∈ frattiniIn (P.map (CFSG.pCore q Y).subtype)) :
    Nat.card ↥(CFSG.pCore q Y ⊓ Subgroup.centralizer ({w} : Set Y)) ≤ q := by
  set V := P.map (CFSG.pCore q Y).subtype with hV
  set W := CFSG.pCore q Y ⊓ Subgroup.centralizer ({w} : Set Y) with hW
  have hVO : V ≤ CFSG.pCore q Y := Subgroup.map_subtype_le P
  have hfix : ∀ d ∈ W, d ∈ V → d ∈ frattiniIn V := by
    intro d hdW hdV
    refine mem_frattiniIn_of_fix hq2 (pow_eq_one_of_mem_map hsc) hinv hdV ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hdW.2
    rw [← h, mul_inv_cancel_right]
  let e : ↥P ≃* ↥V :=
    P.equivMapOfInjective (CFSG.pCore q Y).subtype (CFSG.pCore q Y).subtype_injective
  have hcV : Nat.card ↥V = Nat.card ↥P := (Nat.card_congr e.toEquiv).symm
  rcases hPt with hPe | ⟨hexP, h3P, -⟩
  · have hΦ := frattiniIn_eq_bot_of_elem hsc hPe
    have hWV : ∀ d ∈ W, d ∈ V → d = 1 := fun d hdW hdV => by
      have h := hfix d hdW hdV
      rwa [hΦ, Subgroup.mem_bot] at h
    rcases hO with ⟨-, h3O, -⟩ | ⟨n, -, ⟨g⟩⟩
    ·
      obtain ⟨f⟩ : Nonempty (↥P ≃* Multiplicative (Fin 2 → ZMod q)) := hPe
      have hcP : Nat.card ↥P = q ^ 2 := by
        rw [Nat.card_congr f.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
          Nat.card_zmod, Nat.card_fin]
      have : P.Characteristic := hsc.characteristic
      have hVn : V.Normal := map_normal
      have hWN : W ≤ Subgroup.normalizer (V : Set Y) := fun x _ =>
        Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hVn.conj_mem h hh x, fun hh => by
          have := hVn.conj_mem _ hh x⁻¹
          simpa [mul_assoc] using this⟩
      have h := SecC.C10P4F.card_sup_mul_card_inf' hWN
      have hinf : V ⊓ W = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun d hd => hWV d hd.2 hd.1
      have hsup : Nat.card (V ⊔ W : Subgroup Y) ≤ q ^ 3 := by
        rw [← h3O]
        exact Subgroup.card_le_of_le (sup_le hVO inf_le_left)
      rw [hinf, Subgroup.card_bot, mul_one, hcV, hcP] at h
      have h1 : q ^ 2 * Nat.card W ≤ q ^ 2 * q := by rw [← h, ← pow_succ]; exact hsup
      exact Nat.le_of_mul_le_mul_left h1 (pow_pos hq.out.pos 2)
    ·
      have hOab : ∀ a b : ↥(CFSG.pCore q Y), a * b = b * a := fun a b => g.injective (by
        rw [map_mul, map_mul, mul_comm])
      have hW1 : W = ⊥ := by
        by_contra hne
        have hWq : IsPGroup q ↥W := CFSG.pCore_isPGroup.to_le inf_le_left
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWq
        have hk0 : k ≠ 0 := by
          rintro rfl
          exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) q
          (by rw [hk]; exact dvd_pow_self q hk0)
        have hxO : (x : Y) ∈ CFSG.pCore q Y := x.2.1
        have hxP : (⟨(x : Y), hxO⟩ : ↥(CFSG.pCore q Y)) ∈ P := by
          refine hsc.mem_of_orderOf_eq _ ?_ ?_
          · exact Subgroup.mem_centralizer_iff.mpr fun h _ => hOab h _
          · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
        have hx1 := hWV x x.2 ⟨_, hxP, rfl⟩
        have : orderOf x = 1 := by
          rw [← Subgroup.orderOf_coe, hx1, orderOf_one]
        rw [hx] at this
        exact hq.out.one_lt.ne' this
      rw [hW1, Subgroup.card_bot]
      exact hq.out.one_lt.le
  · rcases hO with ⟨-, h3O, -⟩ | ⟨n, -, ⟨g⟩⟩
    ·
      have hVeq : V = CFSG.pCore q Y := by
        refine Subgroup.eq_of_le_of_card_ge hVO ?_
        rw [hcV, h3P, h3O]
      have hWΦ : W ≤ frattiniIn V := fun d hd => hfix d hd (hVeq ▸ hd.1)
      have hPq : IsPGroup q ↥P := IsPGroup.of_equiv (isPGroup_map P) e.symm
      have hle : (frattini ↥V).map e.symm.toMonoidHom ≤ frattini ↥P :=
        Subgroup.map_le_iff_le_comap.mpr
          (frattini_le_comap_frattini_of_surjective e.symm.surjective)
      calc Nat.card W ≤ Nat.card (frattiniIn V) := Subgroup.card_le_of_le hWΦ
        _ = Nat.card (frattini ↥V) := Subgroup.card_map_of_injective V.subtype_injective
        _ = Nat.card ((frattini ↥V).map e.symm.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.symm.injective).symm
        _ ≤ Nat.card (frattini ↥P) := Subgroup.card_le_of_le hle
        _ ≤ q := card_frattini_le_of_extraspecial hexP hPq
    ·
      exfalso
      obtain ⟨x, y, hxy⟩ := exists_ne_of_isExtraspecial hexP
      apply hxy
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact g.injective (by rw [map_mul, map_mul, mul_comm])

end CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv
