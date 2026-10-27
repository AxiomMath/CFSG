module

public import CFSG.Timmesfeld.Bridge.SchurNarrowNorm

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

variable {K : Type*} [Group K]

theorem CentralIn.mul {S : Subgroup K} {a b : K} (ha : CentralIn S a) (hb : CentralIn S b) :
    CentralIn S (a * b) :=
  ⟨S.mul_mem ha.1 hb.1, fun q hq => (ha.2 q hq).mul_right (hb.2 q hq)⟩

theorem mem_zpowers_iff_of_orderOf_eq_two {x w : K} (hx : orderOf x = 2) :
    w ∈ Subgroup.zpowers x ↔ w = 1 ∨ w = x := by
  have hxx : x ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← hx, pow_orderOf_eq_one]
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hxx, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hxx, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem commute_inv_mul_of_conj_eq {p s t : K} (h : s * t * s⁻¹ = p * t * p⁻¹) :
    Commute (p⁻¹ * s) t := by
  show p⁻¹ * s * t = t * (p⁻¹ * s)
  calc p⁻¹ * s * t = p⁻¹ * (s * t * s⁻¹) * s := by group
    _ = p⁻¹ * (p * t * p⁻¹) * s := by rw [h]
    _ = t * (p⁻¹ * s) := by group

theorem card_le_three_of_forall {X T : Type*} [Finite T] (f : T → X)
    (hf : Function.Injective f) (a b c : X) (h : ∀ t, f t = a ∨ f t = b ∨ f t = c) :
    Nat.card T ≤ 3 := by
  classical
  have hsub : Set.range f ⊆ ({a, b, c} : Set X) := by
    rintro _ ⟨t, rfl⟩
    rcases h t with h1 | h1 | h1 <;> simp [h1]
  calc Nat.card T = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
    _ = (Set.range f).ncard := Nat.card_coe_set_eq _
    _ ≤ ({a, b, c} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]

variable {E : Type*} [Group E] {Z : Subgroup E} [Z.Normal] {x : E} {S : Subgroup E}

omit [Z.Normal] in
theorem commute_of_mk_eq (hZc : Z ≤ Subgroup.center E) {t u : E}
    (htu : (t : E ⧸ Z) = (u : E ⧸ Z)) {v : E} (htv : Commute t v) : Commute u v := by
  have hz := hZc (QuotientGroup.eq.mp htu)
  have hu : u = t * (t⁻¹ * u) := by group
  rw [hu]
  exact htv.mul_left (Subgroup.mem_center_iff.mp hz v).symm

theorem conj_eq_or_of_centralIn (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x) {s t : E} (hs : s ∈ S)
    (ht : CentralIn (quotImage Z S) (t : E ⧸ Z)) : s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * x := by
  have hs' : ((s : E) : E ⧸ Z) ∈ quotImage Z S := Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hs
  have hc : ((t : E) : E ⧸ Z) = ((s * t * s⁻¹ : E) : E ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, (ht.2 _ hs').eq,
      mul_inv_cancel_right]
  rcases (hZx _).mp (QuotientGroup.eq.mp hc) with h1 | h1
  · exact Or.inl (inv_mul_eq_one.mp h1).symm
  · exact Or.inr (mul_eq_of_eq_inv_mul h1.symm).symm

theorem commute_of_forall_not_isConj (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x)
    (hxZ : x ∈ Subgroup.center E) (hH : ∀ z : E, orderOf z = 2 → z ∉ Z → ¬ IsConj z (z * x))
    {z : E} (hz : CentralIn (quotImage Z S) (z : E ⧸ Z)) (hz2 : z * z = 1) :
    ∀ q ∈ S, Commute q z := by
  intro q hq
  by_contra hqz
  rcases conj_eq_or_of_centralIn hZx hq hz with h1 | h1
  · apply hqz
    show q * z = z * q
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [h1]
  · have hzZ : z ∉ Z := by
      intro hzZ
      apply hqz
      rcases (hZx z).mp hzZ with rfl | rfl
      · exact Commute.one_right q
      · exact Subgroup.mem_center_iff.mp hxZ q
    have hz1 : z ≠ 1 := fun h => hzZ (h ▸ Subgroup.one_mem _)
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two, hz2]) hz1
    exact hH z hzo hzZ (isConj_iff.mpr ⟨q, h1⟩)

theorem mul_comm_eq_of_sq_eq (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x) (hxx : x * x = 1)
    (hx1 : x ≠ 1) (hBD : SylowBorelData (E ⧸ Z) (quotImage Z S))
    (hP : ∀ g : E, CentralIn (quotImage Z S) (g : E ⧸ Z) → (g : E ⧸ Z) ≠ 1 → g * g = x)
    {a b : E} (ha : CentralIn (quotImage Z S) (a : E ⧸ Z))
    (hb : CentralIn (quotImage Z S) (b : E ⧸ Z)) (ha1 : (a : E ⧸ Z) ≠ 1)
    (hb1 : (b : E ⧸ Z) ≠ 1) (hab : (a : E ⧸ Z) ≠ b) : b * a = a * b * x := by
  have haa : (a : E ⧸ Z) * a = 1 := hBD.center_sq _ ha
  have hab1 : ((a * b : E) : E ⧸ Z) ≠ 1 := by
    rw [QuotientGroup.mk_mul]
    intro h
    apply hab
    calc (a : E ⧸ Z) = (a : E ⧸ Z) * ((a : E ⧸ Z) * (b : E ⧸ Z)) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, haa, one_mul]
  have habc : CentralIn (quotImage Z S) ((a * b : E) : E ⧸ Z) := by
    rw [QuotientGroup.mk_mul]
    exact ha.mul hb
  have hcomm : ((a * b : E) : E ⧸ Z) = ((b * a : E) : E ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact (hb.2 _ ha.1).eq
  have hsq := hP _ habc hab1
  rcases (hZx _).mp (QuotientGroup.eq.mp hcomm) with h1 | h1
  · exfalso
    have hba : b * a = a * b := (inv_mul_eq_one.mp h1).symm
    apply hx1
    calc x = (a * b) * (a * b) := hsq.symm
      _ = a * (b * a) * b := by group
      _ = (a * a) * (b * b) := by rw [hba]; group
      _ = x * x := by rw [hP a ha ha1, hP b hb hb1]
      _ = 1 := hxx
  · exact (mul_eq_of_eq_inv_mul h1.symm).symm

theorem false_of_three (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x) (hxZ : x ∈ Subgroup.center E)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hBD : SylowBorelData (E ⧸ Z) (quotImage Z S))
    (hP : ∀ g : E, CentralIn (quotImage Z S) (g : E ⧸ Z) → (g : E ⧸ Z) ≠ 1 → g * g = x)
    {g h k : E} (hg : CentralIn (quotImage Z S) (g : E ⧸ Z))
    (hh : CentralIn (quotImage Z S) (h : E ⧸ Z)) (hk : CentralIn (quotImage Z S) (k : E ⧸ Z))
    (hg1 : (g : E ⧸ Z) ≠ 1) (hh1 : (h : E ⧸ Z) ≠ 1) (hk1 : (k : E ⧸ Z) ≠ 1)
    (hgh : (g : E ⧸ Z) ≠ h) (hkg : (k : E ⧸ Z) ≠ g) (hkh : (k : E ⧸ Z) ≠ h)
    (hkgh : (k : E ⧸ Z) ≠ g * h) : False := by
  have hgg : (g : E ⧸ Z) * g = 1 := hBD.center_sq _ hg
  have hgh1 : ((g * h : E) : E ⧸ Z) ≠ 1 := by
    rw [QuotientGroup.mk_mul]
    intro h1
    apply hgh
    calc (g : E ⧸ Z) = (g : E ⧸ Z) * ((g : E ⧸ Z) * (h : E ⧸ Z)) := by rw [h1, mul_one]
      _ = h := by rw [← mul_assoc, hgg, one_mul]
  have hghc : CentralIn (quotImage Z S) ((g * h : E) : E ⧸ Z) := by
    rw [QuotientGroup.mk_mul]
    exact hg.mul hh
  have e1 := mul_comm_eq_of_sq_eq hZx hxx hx1 hBD hP hg hk hg1 hk1 (Ne.symm hkg)
  have e2 := mul_comm_eq_of_sq_eq hZx hxx hx1 hBD hP hh hk hh1 hk1 (Ne.symm hkh)
  have e3 := mul_comm_eq_of_sq_eq hZx hxx hx1 hBD hP hghc hk hgh1 hk1
    (by rw [QuotientGroup.mk_mul]; exact Ne.symm hkgh)
  have hxc : ∀ y : E, y * x = x * y := fun y => Subgroup.mem_center_iff.mp hxZ y
  apply hx1
  have key : g * h * k * x = g * h * k := by
    calc g * h * k * x = k * (g * h) := e3.symm
      _ = k * g * h := by group
      _ = g * k * (x * h) := by rw [e1]; group
      _ = g * k * (h * x) := by rw [hxc h]
      _ = g * (k * h) * x := by group
      _ = g * (h * k * x) * x := by rw [e2]
      _ = g * h * k * (x * x) := by group
      _ = g * h * k := by rw [hxx, mul_one]
  exact mul_eq_left.mp key

theorem false_of_quaternion (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x) (hxZ : x ∈ Subgroup.center E)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hZS : Z ≤ S)
    (hBD : SylowBorelData (E ⧸ Z) (quotImage Z S))
    (hP : ∀ g : E, CentralIn (quotImage Z S) (g : E ⧸ Z) → (g : E ⧸ Z) ≠ 1 → g * g = x)
    {g h : E} (hg : CentralIn (quotImage Z S) (g : E ⧸ Z))
    (hh : CentralIn (quotImage Z S) (h : E ⧸ Z)) (hg1 : (g : E ⧸ Z) ≠ 1)
    (hh1 : (h : E ⧸ Z) ≠ 1) (hgh : (g : E ⧸ Z) ≠ h)
    (hall : ∀ w : E ⧸ Z, CentralIn (quotImage Z S) w →
      w = 1 ∨ w = g ∨ w = h ∨ w = (g : E ⧸ Z) * h) : False := by
  have hZc : Z ≤ Subgroup.center E := by
    intro w hw
    rcases (hZx w).mp hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxZ
  have hxc : ∀ y : E, y * x = x * y := fun y => Subgroup.mem_center_iff.mp hxZ y
  have ehg : h * g = g * h * x := mul_comm_eq_of_sq_eq hZx hxx hx1 hBD hP hg hh hg1 hh1 hgh
  have hng : ¬ Commute g h := by
    intro hc
    apply hx1
    have : g * h * x = g * h := by rw [← ehg, hc.eq]
    exact mul_eq_left.mp this
  have chg : h * g * h⁻¹ = g * x := by
    rw [ehg, mul_assoc g h x, hxc h, ← mul_assoc, mul_inv_cancel_right]
  have cgh : g * h * g⁻¹ = h * x := by
    have e : g * h = h * g * x := by rw [ehg, mul_assoc, hxx, mul_one]
    rw [e, mul_assoc h g x, hxc g, ← mul_assoc, mul_inv_cancel_right]
  have cghg : (g * h) * g * (g * h)⁻¹ = g * x := by
    calc (g * h) * g * (g * h)⁻¹ = g * (h * g * h⁻¹) * g⁻¹ := by group
      _ = g * (g * x) * g⁻¹ := by rw [chg]
      _ = g * g * (x * g⁻¹) := by group
      _ = g * g * (g⁻¹ * x) := by rw [← hxc g⁻¹]
      _ = g * x := by group
  have cghh : (g * h) * h * (g * h)⁻¹ = h * x := by
    calc (g * h) * h * (g * h)⁻¹ = g * h * g⁻¹ := by group
      _ = h * x := cgh
  have hdec : ∀ s ∈ S, ∃ p : E, CentralIn (quotImage Z S) (p : E ⧸ Z) ∧
      Commute (p⁻¹ * s) g ∧ Commute (p⁻¹ * s) h := by
    intro s hs
    have hgh' : CentralIn (quotImage Z S) ((g * h : E) : E ⧸ Z) := by
      rw [QuotientGroup.mk_mul]
      exact hg.mul hh
    rcases conj_eq_or_of_centralIn hZx hs hg with h1 | h1 <;>
      rcases conj_eq_or_of_centralIn hZx hs hh with h2 | h2
    · refine ⟨1, by rw [QuotientGroup.mk_one]; exact centralIn_one _, ?_, ?_⟩
      · exact commute_inv_mul_of_conj_eq (by rw [h1]; group)
      · exact commute_inv_mul_of_conj_eq (by rw [h2]; group)
    · refine ⟨g, hg, ?_, ?_⟩
      · exact commute_inv_mul_of_conj_eq (by rw [h1]; group)
      · exact commute_inv_mul_of_conj_eq (by rw [h2, cgh])
    · refine ⟨h, hh, ?_, ?_⟩
      · exact commute_inv_mul_of_conj_eq (by rw [h1, chg])
      · exact commute_inv_mul_of_conj_eq (by rw [h2]; group)
    · refine ⟨g * h, hgh', ?_, ?_⟩
      · exact commute_inv_mul_of_conj_eq (by rw [h1, cghg])
      · exact commute_inv_mul_of_conj_eq (by rw [h2, cghh])
  obtain ⟨_, ⟨a, haS, rfl⟩, hanc⟩ := hBD.noncomm
  have hb : ∃ b ∈ S, ¬ Commute ((b : E) : E ⧸ Z) ((a : E) : E ⧸ Z) := by
    by_contra hcon
    push Not at hcon
    apply hanc
    refine ⟨Subgroup.mem_map_of_mem _ haS, ?_⟩
    rintro _ ⟨b, hbS, rfl⟩
    exact hcon b hbS
  obtain ⟨b, hbS, hbnc⟩ := hb
  obtain ⟨p, hp, hpg, hph⟩ := hdec a haS
  obtain ⟨p', hp', hpg', hph'⟩ := hdec b hbS
  have hpS : p ∈ S := (mk_mem_quotImage_iff hZS).mp hp.1
  have hp'S : p' ∈ S := (mk_mem_quotImage_iff hZS).mp hp'.1
  set c := p⁻¹ * a with hc
  set c' := p'⁻¹ * b with hc'
  have hcS : c ∈ S := S.mul_mem (S.inv_mem hpS) haS
  have hc'S : c' ∈ S := S.mul_mem (S.inv_mem hp'S) hbS
  have hcmem : ((c : E) : E ⧸ Z) ∈ quotImage Z S :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hcS
  have hc'mem : ((c' : E) : E ⧸ Z) ∈ quotImage Z S :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hc'S
  set y := c * c' * c⁻¹ * c'⁻¹ with hy
  have hyc : CentralIn (quotImage Z S) (y : E ⧸ Z) := by
    have := hBD.commutator_central _ hcmem _ hc'mem
    rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact this
  have hy1 : (y : E ⧸ Z) ≠ 1 := by
    intro h1
    apply hbnc
    have hcc : Commute ((c : E) : E ⧸ Z) ((c' : E) : E ⧸ Z) := by
      rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
      exact (commutatorElement_eq_one_iff_mul_comm (g₁ := ((c : E) : E ⧸ Z))
        (g₂ := ((c' : E) : E ⧸ Z))).mp h1
    have hab' : ((a : E) : E ⧸ Z) = (p : E ⧸ Z) * c := by
      rw [← QuotientGroup.mk_mul, hc, mul_inv_cancel_left]
    have hbb' : ((b : E) : E ⧸ Z) = (p' : E ⧸ Z) * c' := by
      rw [← QuotientGroup.mk_mul, hc', mul_inv_cancel_left]
    rw [hab', hbb']
    have hpc : (p : E ⧸ Z) * c ∈ quotImage Z S := Subgroup.mul_mem _ hp.1 hcmem
    exact Commute.mul_left (hp'.2 _ hpc).symm (Commute.mul_right (hp.2 _ hc'mem) hcc.symm)
  have hyg : Commute y g :=
    ((hpg.mul_left hpg').mul_left hpg.inv_left).mul_left hpg'.inv_left
  have hyh : Commute y h :=
    ((hph.mul_left hph').mul_left hph.inv_left).mul_left hph'.inv_left
  rcases hall _ hyc with h0 | h0 | h0 | h0
  · exact hy1 h0
  · exact hng (commute_of_mk_eq hZc h0 hyh)
  · exact hng (commute_of_mk_eq hZc h0 hyg).symm
  · have h0' : ((y : E) : E ⧸ Z) = ((g * h : E) : E ⧸ Z) := by rw [h0, QuotientGroup.mk_mul]
    have hghg : Commute (g * h) g := commute_of_mk_eq hZc h0' hyg
    apply hng
    have e : g * (h * g) = g * (g * h) := by rw [← mul_assoc, hghg.eq]
    exact (mul_left_cancel e).symm

theorem exists_involution_preimage [Finite E] (hZx : ∀ w, w ∈ Z ↔ w = 1 ∨ w = x)
    (hxZ : x ∈ Subgroup.center E) (hxx : x * x = 1) (hx1 : x ≠ 1) (hZS : Z ≤ S)
    (hBD : SylowBorelData (E ⧸ Z) (quotImage Z S)) :
    ∃ z : E, CentralIn (quotImage Z S) (z : E ⧸ Z) ∧ z * z = 1 ∧ (z : E ⧸ Z) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hP : ∀ g : E, CentralIn (quotImage Z S) (g : E ⧸ Z) → (g : E ⧸ Z) ≠ 1 → g * g = x := by
    intro g hg hg1
    have hgg : ((g * g : E) : E ⧸ Z) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact hBD.center_sq _ hg
    rcases (hZx _).mp ((QuotientGroup.eq_one_iff _).mp hgg) with h1 | h1
    · exact absurd (hcon g hg h1) hg1
    · exact h1
  have hcard := hBD.center_card
  obtain ⟨g', hg', hg1⟩ : ∃ w, CentralIn (quotImage Z S) w ∧ w ≠ 1 := by
    by_contra hne
    push Not at hne
    have := card_le_three_of_forall (fun t : {w : E ⧸ Z // CentralIn (quotImage Z S) w} =>
      (t : E ⧸ Z)) Subtype.val_injective 1 1 1 (fun t => Or.inl (hne t.1 t.2))
    omega
  obtain ⟨h', hh', hh1, hgh⟩ : ∃ w, CentralIn (quotImage Z S) w ∧ w ≠ 1 ∧ g' ≠ w := by
    by_contra hne
    push Not at hne
    have := card_le_three_of_forall (fun t : {w : E ⧸ Z // CentralIn (quotImage Z S) w} =>
      (t : E ⧸ Z)) Subtype.val_injective 1 g' g' (fun t => by
        by_cases ht : (t : E ⧸ Z) = 1
        · exact Or.inl ht
        · exact Or.inr (Or.inl (hne t.1 t.2 ht).symm))
    omega
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h'
  by_cases hall : ∀ w : E ⧸ Z, CentralIn (quotImage Z S) w →
      w = 1 ∨ w = g ∨ w = h ∨ w = (g : E ⧸ Z) * h
  · exact false_of_quaternion hZx hxZ hxx hx1 hZS hBD hP hg' hh' hg1 hh1 hgh hall
  · push Not at hall
    obtain ⟨k', hk', hk1, hkg, hkh, hkgh⟩ := hall
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
    exact false_of_three hZx hxZ hxx hx1 hBD hP hg' hh' hk' hg1 hh1 hk1 hgh hkg hkh hkgh

theorem exists_isConj_mul_of_borelData [Finite E] (hxZ : x ∈ Subgroup.center E)
    (hx2 : orderOf x = 2) (hxE : x ∈ commutator E) [(Subgroup.zpowers x).Normal]
    (S : Sylow 2 E)
    (hBD : SylowBorelData (E ⧸ Subgroup.zpowers x)
      (quotImage (Subgroup.zpowers x) (S : Subgroup E))) :
    ∃ z : E, orderOf z = 2 ∧ z ∉ Subgroup.zpowers x ∧ IsConj z (z * x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hH : ∀ z : E, orderOf z = 2 → z ∉ Subgroup.zpowers x → ¬ IsConj z (z * x) :=
    fun z h1 h2 h3 => hcon ⟨z, h1, h2, h3⟩
  have hZx : ∀ w, w ∈ Subgroup.zpowers x ↔ w = 1 ∨ w = x :=
    fun w => mem_zpowers_iff_of_orderOf_eq_two hx2
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hZc : Subgroup.zpowers x ≤ Subgroup.center E := Subgroup.zpowers_le.mpr hxZ
  have hZS : Subgroup.zpowers x ≤ (S : Subgroup E) := by
    have h2 : IsPGroup 2 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, hx2]
    exact h2.le_sylow_of_normal S
  obtain ⟨z, hz, hz2, hz1⟩ := exists_involution_preimage hZx hxZ hxx hx1 hZS hBD
  have hzS : z ∈ (S : Subgroup E) := (mk_mem_quotImage_iff hZS).mp hz.1
  have hzc := commute_of_forall_not_isConj hZx hxZ hH hz hz2
  have hzZ : z ∉ Subgroup.zpowers x := fun h => hz1 ((QuotientGroup.eq_one_iff z).mpr h)
  have hinf := inf_commutator_eq_bot_of_borelData hZc hxx (fun s hs => (hZx s).mp hs) hZS hBD
    hzS hzc hzZ
  have hxS := mem_commutator_sylow_of_mem_commutator S hxZ (hZS (Subgroup.mem_zpowers x)) hxE
  have hxbot : x ∈ (⊥ : Subgroup E) := hinf ▸ ⟨Subgroup.mem_zpowers x, hxS⟩
  exact hx1 (Subgroup.mem_bot.mp hxbot)

end CFSG.Timmesfeld.Bridge
