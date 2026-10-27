module

public import CFSG.GH74.GLS.IVK.L2.Lemma13
import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Red
import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local
import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Full
import CFSG.Dihedral.Glauberman.DicksonMaxNode

public section

namespace CFSG.LocalAnalysis.WeakClosure81.L2Seitz

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup Equiv

theorem isCoatom_map_iff {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (H : Subgroup X) :
    IsCoatom (H.map (φ : X →* Y)) ↔ IsCoatom H :=
  φ.mapSubgroup.isCoatom_iff H

theorem map_centralizer_singleton {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (u : X) :
    (centralizer ({u} : Set X)).map (φ : X →* Y) = centralizer ({φ u} : Set Y) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ x * φ u = φ u * φ x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    apply φ.injective
    simpa using hy

theorem dihedral_central_eq {k : ℕ} (hk : 3 ≤ k) {a b : DihedralGroup k}
    (ha : a ∈ center (DihedralGroup k)) (hb : b ∈ center (DihedralGroup k))
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  rcases Nat.even_or_odd k with hev | hodd
  · rw [DihedralGroup.center_eq_closure_of_even_ne_two hev (by omega)] at ha hb
    have : NeZero k := ⟨by omega⟩
    set g : DihedralGroup k := DihedralGroup.r ((k / 2 : ℕ) : ZMod k)
    have hg2 : g ^ 2 = 1 := by
      simp only [g, pow_two, DihedralGroup.r_mul_r]
      rw [show (1 : DihedralGroup k) = DihedralGroup.r 0 from rfl]
      congr 1
      obtain ⟨j, hj⟩ := hev
      rw [← Nat.cast_add, show k / 2 + k / 2 = k by omega, ZMod.natCast_self]
    have hg1 : g ≠ 1 := by
      intro h1
      have h0 : ((k / 2 : ℕ) : ZMod k) = 0 := DihedralGroup.r.inj h1
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
    have hcard : Nat.card ↥(zpowers g) = 2 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime hg2 hg1
    obtain ⟨x, y, -, hU⟩ := Nat.card_eq_two_iff.mp hcard
    have hmem : ∀ w : ↥(zpowers g), w = x ∨ w = y := fun w => by
      have : w ∈ ({x, y} : Set ↥(zpowers g)) := hU ▸ Set.mem_univ w
      simpa using this
    have h1 := hmem 1
    have ha' := hmem ⟨a, ha⟩
    have hb' := hmem ⟨b, hb⟩
    have hne1 : ∀ w : ↥(zpowers g), (w : DihedralGroup k) ≠ 1 → w ≠ 1 :=
      fun w hw h => hw (by rw [h]; rfl)
    have ha1' := hne1 ⟨a, ha⟩ ha1
    have hb1' := hne1 ⟨b, hb⟩ hb1
    have : (⟨a, ha⟩ : ↥(zpowers g)) = ⟨b, hb⟩ := by
      rcases h1 with h1 | h1 <;> rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
        first
        | exact ha'.trans hb'.symm
        | exact absurd (ha'.trans h1.symm) ha1'
        | exact absurd (hb'.trans h1.symm) hb1'
    simpa using congrArg Subtype.val this
  · rw [DihedralGroup.center_eq_bot_of_odd_ne_one hodd (by omega), Subgroup.mem_bot] at ha
    exact absurd ha ha1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem S4_no_invol_four_three : ∀ x g y : Perm (Fin 4), (x * x = 1 ∧ x ≠ 1 ∧ g * x = x * g ∧
    g * g ≠ 1 ∧ g * g * (g * g) = 1 ∧ y ≠ 1 ∧ y * y * y = 1) → x * y * x⁻¹ ≠ y⁻¹ := by
  decide +kernel

theorem dihedral4_facts : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.r 1 ≠ 1 ∧
    DihedralGroup.r 1 * DihedralGroup.r 1 * (DihedralGroup.r 1 * DihedralGroup.r 1) =
      (1 : DihedralGroup 4) := by decide

theorem dihedral3_facts : (DihedralGroup.r 1 : DihedralGroup 3) ≠ 1 ∧
    DihedralGroup.r 1 * DihedralGroup.r 1 * DihedralGroup.r 1 = (1 : DihedralGroup 3) ∧
    ∀ a : DihedralGroup 3, a * a = 1 → a ≠ 1 →
      a * DihedralGroup.r 1 * a⁻¹ = (DihedralGroup.r 1)⁻¹ := by decide

theorem conj_apply_eq {K : Type} [Group K] (φ : MulAut K) (u : K) :
    MulAut.conj (φ u) = φ * MulAut.conj u * φ⁻¹ := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_eps (hF : L2Field F) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
  obtain ⟨t, ht⟩ := hF.1
  by_cases h : t % 2 = 0
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩

theorem inner_type (hF : L2Field F) (e : K ≃* L2 F) {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {σ : MulAut K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσ : σ ∈ innAut K) :
    ∃ u : K, orderOf u = 2 ∧ σ = MulAut.conj u ∧
      fixedSubgroup K σ = centralizer ({u} : Set K) ∧
      (Nat.card ↥(fixedSubgroup K σ) : ℤ) = Nat.card F - ε := by
  obtain ⟨u, rfl⟩ := hσ
  have hinj := conj_injective_of_L2 e
  have hu2 : u ^ 2 = 1 := hinj (by rw [map_pow, hσ2, map_one])
  have hu1 : u ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
  have hfix := Proofs2.Lemma118.fixedSubgroup_conj u
  obtain ⟨k, hk, hk2, ⟨eD⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
  have : NeZero k := ⟨by omega⟩
  refine ⟨u, hu, rfl, hfix, ?_⟩
  rw [hfix, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, ← hd, hk]

theorem diag_type (hF : L2Field F) (e : K ≃* L2 F) {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {σ : MulAut K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσD : σ ∈ innDiagSub e) (hσI : σ ∉ innAut K) :
    (Nat.card ↥(fixedSubgroup K σ) : ℤ) = Nat.card F + ε := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
    ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
  obtain ⟨k, hk, hk2, ⟨eD⟩⟩ :=
    (ivk_1_3b F hF K e ε hε1 hε d hd σ hσD hσI (orderOf_eq_prime hσ2 hσ1)).2.1
  have : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, ← hd, hk]

theorem mul_mem_innDiagSub_of_not_mem (hF : L2Field F) (e : K ≃* L2 F) {σ τ : MulAut K}
    (hσ2 : σ ^ 2 = 1) (hτ2 : τ ^ 2 = 1) (hσ : σ ∉ innDiagSub e) (hτ : τ ∉ innDiagSub e) :
    σ * τ ∈ innDiagSub e := by
  obtain ⟨hcyc, -⟩ := ivk_1_2e F hF K e
  rw [mem_innDiagSub_iff] at hσ hτ ⊢
  set a := fieldProj e σ
  set b := fieldProj e τ
  have ha2 : a ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hb2 : b ^ 2 = 1 := by rw [← map_pow, hτ2, map_one]
  obtain ⟨-, ⟨eF⟩, -⟩ := ivk_1_2e F hF K e
  have : IsCyclic (F ≃+* F) := isCyclic_of_surjective eF.toMonoidHom eF.surjective
  have hab : a = b := by
    have hoa : orderOf a = 2 := orderOf_eq_prime ha2 hσ
    have hob : orderOf b = 2 := orderOf_eq_prime hb2 hτ
    classical
    have : Fintype (F ≃+* F) := Fintype.ofFinite _
    have h2 : 2 ∣ Fintype.card (F ≃+* F) := by
      rw [← hoa]; exact orderOf_dvd_card
    have hc := IsCyclic.card_orderOf_eq_totient h2
    rw [Nat.totient_two] at hc
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have ha' : a ∈ Finset.univ.filter (fun y => orderOf y = 2) := by simp [hoa]
    have hb' : b ∈ Finset.univ.filter (fun y => orderOf y = 2) := by simp [hob]
    rw [hx, Finset.mem_singleton] at ha' hb'
    rw [ha', hb']
  rw [map_mul]
  change a * b = 1
  rw [← hab, ← pow_two, ha2]

theorem exists_card_eq (hF : L2Field F) :
    ∃ p n : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ Nat.card F = p ^ n := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  refine ⟨ringChar F, n, hp, ?_, n.pos, hcard⟩
  intro h2
  have hodd := hF.1
  rw [hcard, h2] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' n.ne_zero).mpr even_two)

omit [Finite K] in
theorem isCoatom_centralizer (hF : L2Field F) (e : K ≃* L2 F)
    (h11 : 11 ≤ Nat.card F) {u : K} (hu : orderOf u = 2) :
    IsCoatom (centralizer ({u} : Set K)) := by
  obtain ⟨p, n, hp, hp2, -, hcard⟩ := exists_card_eq hF
  have : Fact p.Prime := ⟨hp⟩
  let φ : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := e.trans (L2.equivPSL F)
  have ht : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hco := CFSG.GH74.Generic.BProg.B2.psl2_isCoatom_centralizer_involution hcard hp2
    (hcard ▸ h11) ht
  rw [← map_centralizer_singleton φ u] at hco
  exact (isCoatom_map_iff φ _).mp hco

theorem field_type (hF : L2Field F) (e : K ≃* L2 F)
    (N : L2Notation e) {σ : MulAut K} (hσ2 : σ ^ 2 = 1) (hσD : σ ∉ innDiagSub e) :
    ∃ q₀ : ℕ, q₀ ^ 2 = Nat.card F ∧ 3 ≤ q₀ ∧
      Nat.card ↥(fixedSubgroup K σ) = q₀ * (q₀ ^ 2 - 1) ∧ IsCoatom (fixedSubgroup K σ) := by
  classical
  obtain ⟨F₀, _, _, hF₀, ⟨ψ⟩⟩ := Proofs2.exists_equiv_pgl2_fixedSubgroup hF e N hσ2 hσD
  set q₀ := Nat.card F₀ with hq₀
  have hcardfix : Nat.card ↥(fixedSubgroup K σ) = q₀ * (q₀ ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula]
  obtain ⟨p, n, hp, hp2, hn, hcard⟩ := exists_card_eq hF
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F₀
  obtain ⟨m, hr, hm⟩ := FiniteField.card F₀ (ringChar F₀)
  have hq₀m : q₀ = ringChar F₀ ^ (m : ℕ) := by rw [hq₀, Nat.card_eq_fintype_card, hm]
  have hpr : ringChar F₀ = p := by
    have h1 : ringChar F₀ ∣ p ^ n := by
      rw [← hcard, ← hF₀, hq₀m, ← pow_mul]
      exact dvd_pow_self _ (by positivity)
    exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h1)
  rw [hpr] at hq₀m
  have hn2 : n = 2 * m := by
    have h1 : p ^ n = p ^ (2 * (m : ℕ)) := by rw [← hcard, ← hF₀, hq₀m, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hq₀3 : 3 ≤ q₀ := by
    rw [hq₀m]
    calc 3 ≤ p := by have := hp.two_le; rcases hp.eq_two_or_odd' with h | ⟨k, hk⟩ <;> omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (m : ℕ) := Nat.pow_le_pow_right hp.pos m.pos
  refine ⟨q₀, hF₀, hq₀3, hcardfix, ?_⟩
  let φ : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := e.trans (L2.equivPSL F)
  have hGF : Nat.card (GaloisField p m) = p ^ (m : ℕ) := GaloisField.card p m m.ne_zero
  have := Fintype.ofFinite (GaloisField p m)
  have eR : F₀ ≃+* GaloisField p m := FiniteField.ringEquivOfCardEq (K := F₀) (K' := GaloisField p m)
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, ← hq₀m])
  let H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := (fixedSubgroup K σ).map (φ : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
  have eH : H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) :=
    ((Subgroup.equivMapOfInjective _ _ φ.injective).symm.trans ψ).trans
      (CFSG.GorensteinWalter.pgl2RingEquiv eR)
  have hco := CFSG.Glauberman.Dickson.MaxUp.isCoatom_of_mulEquiv_pgl2 hcard hp2 hn2 eH
  exact (isCoatom_map_iff φ _).mp hco

theorem eq_of_centralizer_eq (hF : L2Field F) (e : K ≃* L2 F) (h7 : 7 ≤ Nat.card F)
    {u v : K} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (h : centralizer ({u} : Set K) = centralizer ({v} : Set K)) : u = v := by
  obtain ⟨ε, hε1, hε⟩ := exists_eps hF
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
  obtain ⟨k, hk, hk2, ⟨eD⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
  have hk3 : 3 ≤ k := by rcases hε1 with rfl | rfl <;> omega
  have huC : u ∈ centralizer ({u} : Set K) := mem_centralizer_singleton_iff.mpr rfl
  have hvC : v ∈ centralizer ({u} : Set K) := h ▸ mem_centralizer_singleton_iff.mpr rfl
  have hcen : ∀ w (hw : w ∈ centralizer ({u} : Set K)),
      (∀ y ∈ centralizer ({u} : Set K), y * w = w * y) →
      eD ⟨w, hw⟩ ∈ center (DihedralGroup k) := by
    intro w hw hc
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := eD.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y' y'.2)
  have hu' := hcen u huC fun y hy => (mem_centralizer_singleton_iff.mp hy)
  have hv' := hcen v hvC fun y hy => by
    rw [h] at hy; exact mem_centralizer_singleton_iff.mp hy
  have hne : ∀ w (hw : w ∈ centralizer ({u} : Set K)), orderOf w = 2 → eD ⟨w, hw⟩ ≠ 1 := by
    intro w hw ho h1
    have : (⟨w, hw⟩ : ↥(centralizer ({u} : Set K))) = 1 := eD.injective (by rw [h1, map_one])
    have := congrArg Subtype.val this
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ho
    exact absurd ho (by norm_num)
  have := dihedral_central_eq hk3 hu' hv' (hne u huC hu) (hne v hvC hv)
  exact congrArg Subtype.val (eD.injective this)

theorem card_fixed_le_of_mem_innDiag (hF : L2Field F) (e : K ≃* L2 F) {σ : MulAut K}
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hσD : σ ∈ innDiagSub e) :
    Nat.card ↥(fixedSubgroup K σ) ≤ Nat.card F + 1 := by
  obtain ⟨ε, hε1, hε⟩ := exists_eps hF
  by_cases hI : σ ∈ innAut K
  · obtain ⟨u, -, -, -, hc⟩ := inner_type hF e hε1 hε hσ2 hσ1 hI
    have : (Nat.card ↥(fixedSubgroup K σ) : ℤ) ≤ Nat.card F + 1 := by
      rw [hc]; rcases hε1 with rfl | rfl <;> omega
    exact_mod_cast this
  · have hc := diag_type hF e hε1 hε hσ2 hσ1 hσD hI
    have : (Nat.card ↥(fixedSubgroup K σ) : ℤ) ≤ Nat.card F + 1 := by
      rw [hc]; rcases hε1 with rfl | rfl <;> omega
    exact_mod_cast this

omit [Finite K] in
theorem mem_fixed_mul {α β : MulAut K} {x : K} (hα : x ∈ fixedSubgroup K α)
    (hβ : x ∈ fixedSubgroup K β) : x ∈ fixedSubgroup K (α * β) := by
  change (α * β) x = x
  rw [MulAut.mul_apply]
  rw [show β x = x from hβ]
  exact hα

theorem sup_eq_top_of_field (hF : L2Field F) (e : K ≃* L2 F)
    (N : L2Notation e) {α β : MulAut K} (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hαβ : α ≠ β)
    (hc : α * β = β * α) (hαD : α ∉ innDiagSub e) (hβD : β ∉ innDiagSub e) :
    fixedSubgroup K α ⊔ fixedSubgroup K β = ⊤ := by
  obtain ⟨q₀, hq₀, hq₀3, hcα, hmax⟩ := field_type hF e N hα2 hαD
  obtain ⟨q₁, hq₁, -, hcβ, -⟩ := field_type hF e N hβ2 hβD
  have hq : q₁ = q₀ := Nat.pow_left_injective (by norm_num : 2 ≠ 0) (hq₁.trans hq₀.symm)
  rcases hmax.le_iff.mp (le_sup_left : fixedSubgroup K α ≤ _) with h | h
  · exact h
  · exfalso
    have hle : fixedSubgroup K β ≤ fixedSubgroup K α := h ▸ le_sup_right
    have heq : fixedSubgroup K β = fixedSubgroup K α :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcα, hcβ, hq])
    set γ := α * β
    have hγ2 : γ ^ 2 = 1 := by
      rw [(show Commute α β from hc).mul_pow, hα2, hβ2, one_mul]
    have hγ1 : γ ≠ 1 := fun h1 => hαβ (by
      have : α = β⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, inv_eq_of_mul_eq_one_left (by rw [← pow_two, hβ2])])
    have hγD := mul_mem_innDiagSub_of_not_mem hF e hα2 hβ2 hαD hβD
    have hsub : fixedSubgroup K α ≤ fixedSubgroup K γ := fun x hx =>
      mem_fixed_mul hx (heq ▸ hx)
    have h1 := Subgroup.card_le_of_le hsub
    have h2 := card_fixed_le_of_mem_innDiag hF e hγ2 hγ1 hγD
    rw [hcα] at h1
    rw [← hq₀] at h2
    have h3 : q₀ ^ 2 + 1 < q₀ * (q₀ ^ 2 - 1) := by
      have : 9 ≤ q₀ ^ 2 := by nlinarith
      have h4 : q₀ * (q₀ ^ 2 - 1) = q₀ ^ 3 - q₀ := by
        rw [Nat.mul_sub, mul_one]; ring_nf
      rw [h4]
      have : q₀ ^ 3 = q₀ * q₀ ^ 2 := by ring
      have : 3 * q₀ ^ 2 ≤ q₀ * q₀ ^ 2 := Nat.mul_le_mul_right _ hq₀3
      have : q₀ ≤ q₀ ^ 2 := Nat.le_self_pow two_ne_zero q₀
      omega
    omega

theorem sup_eq_top_of_inner_inner (hF : L2Field F)
    (e : K ≃* L2 F) (h11 : 11 ≤ Nat.card F) {u v : K} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) :
    centralizer ({u} : Set K) ⊔ centralizer ({v} : Set K) = ⊤ := by
  have hmax := isCoatom_centralizer hF e h11 hu
  rcases hmax.le_iff.mp (le_sup_left : centralizer ({u} : Set K) ≤ _) with h | h
  · exact h
  · exfalso
    have hle : centralizer ({v} : Set K) ≤ centralizer ({u} : Set K) := h ▸ le_sup_right
    obtain ⟨ε, hε1, hε⟩ := exists_eps hF
    have hcu := (inner_type hF e hε1 hε (σ := MulAut.conj u)
      (by rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one])
      (fun h1 => by
        have := conj_injective_of_L2 e (h1.trans (map_one _).symm)
        rw [this, orderOf_one] at hu; exact absurd hu (by norm_num)) ⟨u, rfl⟩)
    have hcv := (inner_type hF e hε1 hε (σ := MulAut.conj v)
      (by rw [← map_pow, ← hv, pow_orderOf_eq_one, map_one])
      (fun h1 => by
        have := conj_injective_of_L2 e (h1.trans (map_one _).symm)
        rw [this, orderOf_one] at hv; exact absurd hv (by norm_num)) ⟨v, rfl⟩)
    obtain ⟨u', -, hu'σ, hfu, hcu⟩ := hcu
    obtain ⟨v', -, hv'σ, hfv, hcv⟩ := hcv
    rw [Proofs2.Lemma118.fixedSubgroup_conj] at hcu hcv
    have heq : centralizer ({v} : Set K) = centralizer ({u} : Set K) :=
      Subgroup.eq_of_le_of_card_ge hle (by
        have : (Nat.card ↥(centralizer ({u} : Set K)) : ℤ) =
            Nat.card ↥(centralizer ({v} : Set K)) := by rw [hcu, hcv]
        exact_mod_cast this.le)
    exact huv (eq_of_centralizer_eq hF e (by omega) hu hv heq.symm)

theorem sup_eq_top_of_inner_diag (hF : L2Field F)
    (e : K ≃* L2 F) (h11 : 11 ≤ Nat.card F) {u : K} (hu : orderOf u = 2) {β : MulAut K}
    (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1) (hβD : β ∈ innDiagSub e) (hβI : β ∉ innAut K) :
    centralizer ({u} : Set K) ⊔ fixedSubgroup K β = ⊤ := by
  have hmax := isCoatom_centralizer hF e h11 hu
  rcases hmax.le_iff.mp (le_sup_left : centralizer ({u} : Set K) ≤ _) with h | h
  · exact h
  · exfalso
    have hle : fixedSubgroup K β ≤ centralizer ({u} : Set K) := h ▸ le_sup_right
    obtain ⟨ε, hε1, hε⟩ := exists_eps hF
    obtain ⟨u', -, -, hfu, hcu⟩ := inner_type hF e hε1 hε (σ := MulAut.conj u)
      (by rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one])
      (fun h1 => by
        have := conj_injective_of_L2 e (h1.trans (map_one _).symm)
        rw [this, orderOf_one] at hu; exact absurd hu (by norm_num)) ⟨u, rfl⟩
    rw [Proofs2.Lemma118.fixedSubgroup_conj] at hcu
    have hcβ := diag_type hF e hε1 hε hβ2 hβ1 hβD hβI
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
    have hm' : ((Nat.card F : ℤ) - ε) = (Nat.card F + ε) * m := by
      rw [← hcu, ← hcβ]; exact_mod_cast hm
    rcases hε1 with rfl | rfl
    ·
      rcases m with _ | _ | m
      · simp at hm'; omega
      · push_cast at hm'; omega
      · push_cast at hm'; nlinarith
    ·
      rcases m with _ | _ | m
      · simp at hm'; omega
      · push_cast at hm'; omega
      · push_cast at hm'; nlinarith

@[expose] def Small7 (e : K ≃* L2 F) : Prop :=
  ∀ (u : K) (β : MulAut K), orderOf u = 2 → β ^ 2 = 1 → β ≠ 1 → β ∈ innDiagSub e →
    β ∉ innAut K → MulAut.conj u * β = β * MulAut.conj u →
    centralizer ({u} : Set K) ⊔ fixedSubgroup K β = ⊤

theorem fix_sup_eq_top (hF : L2Field F) (e : K ≃* L2 F)
    (N : L2Notation e) {σ τ : MulAut K} (hσ2 : σ ^ 2 = 1) (hτ2 : τ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) (hστ : σ ≠ τ) (hc : σ * τ = τ * σ) (h5 : Nat.card F ≠ 5)
    (h9 : Nat.card F ≠ 9) (hexc : ¬ (σ ∈ innAut K ∧ τ ∈ innAut K ∧ Nat.card F = 7))
    (h7 : Nat.card F = 7 → Small7 e) :
    fixedSubgroup K σ ⊔ fixedSubgroup K τ ⊔ fixedSubgroup K (σ * τ) = ⊤ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, σ * τ = ρ := ⟨_, rfl⟩
  rw [hρ]
  have hcomm : Commute σ τ := hc
  have hσσ : σ * σ = 1 := by rw [← pow_two, hσ2]
  have hττ : τ * τ = 1 := by rw [← pow_two, hτ2]
  have hρ2 : ρ ^ 2 = 1 := by rw [← hρ, hcomm.mul_pow, hσ2, hτ2, one_mul]
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hττ
  have hρ1 : ρ ≠ 1 := fun h1 => hστ (by
    have : σ = τ⁻¹ := eq_inv_of_mul_eq_one_left (hρ.trans h1)
    rw [this, hτinv])
  have hσρ : σ * ρ = τ := by rw [← hρ, ← mul_assoc, hσσ, one_mul]
  have hρσ : ρ * σ = τ := by rw [← hρ, hc, mul_assoc, hσσ, mul_one]
  have hτρ : τ * ρ = σ := by rw [← hρ, hc, ← mul_assoc, hττ, one_mul]
  have hρτ : ρ * τ = σ := by rw [← hρ, mul_assoc, hττ, mul_one]
  have hσρne : σ ≠ ρ := fun h => hτ1 (by rw [← hσρ, ← h, ← pow_two, hσ2])
  have hτρne : τ ≠ ρ := fun h => hσ1 (by rw [← hτρ, ← h, ← pow_two, hτ2])
  have hD := innDiagSub_normal e
  have key : ∀ α β : MulAut K, (α = σ ∨ α = τ ∨ α = ρ) → (β = σ ∨ β = τ ∨ β = ρ) →
      fixedSubgroup K α ⊔ fixedSubgroup K β = ⊤ →
      fixedSubgroup K σ ⊔ fixedSubgroup K τ ⊔ fixedSubgroup K ρ = ⊤ := by
    intro α β hα hβ h
    have hle : ∀ γ, (γ = σ ∨ γ = τ ∨ γ = ρ) →
        fixedSubgroup K γ ≤ fixedSubgroup K σ ⊔ fixedSubgroup K τ ⊔ fixedSubgroup K ρ := by
      rintro γ (rfl | rfl | rfl)
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    exact eq_top_iff.mpr (h ▸ sup_le (hle α hα) (hle β hβ))
  have hq : 3 < Nat.card F := hF.2
  have hqodd : Odd (Nat.card F) := hF.1
  by_cases hσD : σ ∈ innDiagSub e
  · by_cases hτD : τ ∈ innDiagSub e
    ·
      have h711 : Nat.card F = 7 ∨ 11 ≤ Nat.card F := by
        obtain ⟨t, ht⟩ := hqodd; omega
      obtain ⟨ε, hε1, hε⟩ := exists_eps hF
      by_cases hσI : σ ∈ innAut K
      · obtain ⟨u, hu, rfl, hfu, -⟩ := inner_type hF e hε1 hε hσ2 hσ1 hσI
        by_cases hτI : τ ∈ innAut K
        · obtain ⟨v, hv, rfl, hfv, -⟩ := inner_type hF e hε1 hε hτ2 hτ1 hτI
          have h11 : 11 ≤ Nat.card F := by
            rcases h711 with h | h
            · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩, h⟩ hexc
            · exact h
          refine key _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_
          rw [hfu, hfv]
          exact sup_eq_top_of_inner_inner hF e h11 hu hv (fun h => hστ (by rw [h]))
        · refine key _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_
          rw [hfu]
          rcases h711 with h | h
          · exact h7 h u τ hu hτ2 hτ1 hτD hτI hc
          · exact sup_eq_top_of_inner_diag hF e h hu hτ2 hτ1 hτD hτI
      · by_cases hτI : τ ∈ innAut K
        · obtain ⟨v, hv, rfl, hfv, -⟩ := inner_type hF e hε1 hε hτ2 hτ1 hτI
          refine key _ _ (Or.inr (Or.inl rfl)) (Or.inl rfl) ?_
          rw [hfv]
          rcases h711 with h | h
          · exact h7 h v σ hv hσ2 hσ1 hσD hσI hc.symm
          · exact sup_eq_top_of_inner_diag hF e h hv hσ2 hσ1 hσD hσI
        ·
          have hρI : ρ ∈ innAut K := hρ ▸
            CFSG.GH74.GLS.Th2.Bal.mul_mem_innAut_of_mem_innDiagSub hF e hσD hτD hσI hτI
          obtain ⟨w, hw, hwρ, hfw, -⟩ := inner_type hF e hε1 hε hρ2 hρ1 hρI
          refine key _ _ (Or.inr (Or.inr rfl)) (Or.inl rfl) ?_
          rw [hfw]
          have hcw : MulAut.conj w * σ = σ * MulAut.conj w := by
            rw [← hwρ, hρσ, hσρ]
          rcases h711 with h | h
          · exact h7 h w σ hw hσ2 hσ1 hσD hσI hcw
          · exact sup_eq_top_of_inner_diag hF e h hw hσ2 hσ1 hσD hσI
    ·
      have hρD : ρ ∉ innDiagSub e := fun h => hτD (by rw [← hσρ]; exact mul_mem hσD h)
      exact key _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        (sup_eq_top_of_field hF e N hτ2 hρ2 hτρne (by rw [hτρ, hρτ]) hτD hρD)
  · by_cases hτD : τ ∈ innDiagSub e
    · have hρD : ρ ∉ innDiagSub e := fun h => hσD (by rw [← hρτ]; exact mul_mem h hτD)
      exact key _ _ (Or.inl rfl) (Or.inr (Or.inr rfl))
        (sup_eq_top_of_field hF e N hσ2 hρ2 hσρne (by rw [hσρ, hρσ]) hσD hρD)
    · exact key _ _ (Or.inl rfl) (Or.inr (Or.inl rfl))
        (sup_eq_top_of_field hF e N hσ2 hτ2 hστ hc hσD hτD)

theorem nonempty_perm4_of_card
    (hF7 : Nat.card F = 7) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (hH : Nat.card H = 24) : Nonempty (H ≃* Perm (Fin 4)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hF : Nat.card F = 7 ^ 1 := by rw [hF7]; norm_num
  rcases (CFSG.Glauberman.Dickson.dickson_psl2_subgroups_and_maximal_subgroups hF).1 H with
    ⟨m, hm, hc, -⟩ | ⟨z, hz, hc, -⟩ | ⟨z, -, hz, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA⟩⟩ |
    ⟨m, t, hm1, hm, -, -, E, C, -, -, hE, -⟩ | ⟨m, hm, ⟨eP⟩⟩ | ⟨m, hm, ⟨eP⟩⟩
  · interval_cases m <;> simp_all
  · norm_num at hz; rw [hH] at hc; subst hc; omega
  · norm_num at hz
    have : Nat.card H = 2 * z := by
      have : NeZero z := ⟨by rintro rfl; simp at hz⟩
      rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
  · rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card] at hH
    exact absurd hH (by decide)
  · exact ⟨eS⟩
  · rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card] at hH
    exact absurd hH (by decide)
  ·
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rw [hE, hH] at hdvd
    have : 7 ∣ 7 ^ m := dvd_pow_self 7 (by omega)
    have := this.trans hdvd
    omega
  · have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst hm1
    have h7 : Nat.card (GaloisField 7 1) = 7 := by
      rw [GaloisField.card 7 1 (by norm_num)]; norm_num
    rw [Nat.card_congr eP.toEquiv] at hH
    have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 7 1)
      ⟨7, 1, by norm_num, by decide, le_rfl, by rw [h7]; norm_num⟩
    rw [this, h7] at hH
    norm_num at hH
  · have : m = 0 := by
      rcases Nat.dvd_one.mp hm with h
      omega
    subst this
    norm_num at hm

theorem small7 (hF : L2Field F) (e : K ≃* L2 F)
    (h7 : Nat.card F = 7) : Small7 e := by
  intro u β hu hβ2 hβ1 hβD hβI hc
  have hε : (Nat.card F : ℤ) ≡ -1 [ZMOD 4] := by rw [h7]; decide
  obtain ⟨k, hk, -, ⟨eU⟩⟩ := (ivk_1_3a F hF K e (-1) (Or.inr rfl) hε 8
    (by rw [h7]; norm_num) u hu).2.1
  obtain rfl : k = 4 := by omega
  obtain ⟨k', hk', -, ⟨eB⟩⟩ := (ivk_1_3b F hF K e (-1) (Or.inr rfl) hε 6
    (by rw [h7]; norm_num) β hβD hβI (orderOf_eq_prime hβ2 hβ1)).2.1
  obtain rfl : k' = 3 := by omega
  have hcU : Nat.card ↥(centralizer ({u} : Set K)) = 8 := by
    rw [Nat.card_congr eU.toEquiv, DihedralGroup.nat_card]
  have hcB : Nat.card ↥(fixedSubgroup K β) = 6 := by
    rw [Nat.card_congr eB.toEquiv, DihedralGroup.nat_card]
  have hcK : Nat.card K = 168 := by
    rw [ivk_1_2b F hF K e, h7]; norm_num
  have huB : u ∈ fixedSubgroup K β := by
    have h1 : MulAut.conj (β u) = MulAut.conj u := by
      rw [conj_apply_eq, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    exact conj_injective_of_L2 e h1
  by_contra hX
  set X := centralizer ({u} : Set K) ⊔ fixedSubgroup K β with hXdef
  have h8 : 8 ∣ Nat.card X := hcU ▸ Subgroup.card_dvd_of_le le_sup_left
  have h6 : 6 ∣ Nat.card X := hcB ▸ Subgroup.card_dvd_of_le le_sup_right
  have hdvd : Nat.card X ∣ 168 := hcK ▸ Subgroup.card_subgroup_dvd_card X
  have hne : Nat.card X ≠ 168 := fun h => hX (Subgroup.eq_top_of_card_eq X (hcK ▸ h))
  have h24 : Nat.card X = 24 := by
    obtain ⟨a, ha⟩ := h8
    obtain ⟨b, hb⟩ := h6
    have hpos : 0 < Nat.card X := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have : Nat.card X ∈ ({24, 48, 72, 96, 120, 144, 168} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h | h | h | h
    · exact h
    · exact absurd (h ▸ hdvd) (by decide)
    · exact absurd (h ▸ hdvd) (by decide)
    · exact absurd (h ▸ hdvd) (by decide)
    · exact absurd (h ▸ hdvd) (by decide)
    · exact absurd (h ▸ hdvd) (by decide)
    · exact absurd h hne
  let φ : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := e.trans (L2.equivPSL F)
  have hH : Nat.card ↥(X.map φ.toMonoidHom) = 24 := by
    rw [← h24]
    exact Nat.card_congr (Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective).symm.toEquiv
  obtain ⟨ψ⟩ := nonempty_perm4_of_card h7 _ hH
  let Ψ : X ≃* Perm (Fin 4) :=
    (Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective).trans ψ
  set g₀ : K := (eU.symm (DihedralGroup.r 1) : K)
  set y₀ : K := (eB.symm (DihedralGroup.r 1) : K)
  have hg₀U : g₀ ∈ centralizer ({u} : Set K) := (eU.symm (DihedralGroup.r 1)).2
  have hy₀B : y₀ ∈ fixedSubgroup K β := (eB.symm (DihedralGroup.r 1)).2
  have huX : u ∈ X :=
    (le_sup_left : centralizer ({u} : Set K) ≤ X) (mem_centralizer_singleton_iff.mpr rfl)
  have hgX : g₀ ∈ X := (le_sup_left : centralizer ({u} : Set K) ≤ X) hg₀U
  have hyX : y₀ ∈ X := (le_sup_right : fixedSubgroup K β ≤ X) hy₀B
  have hgu : g₀ * u = u * g₀ := mem_centralizer_singleton_iff.mp hg₀U
  obtain ⟨hD4a, hD4b⟩ := dihedral4_facts
  obtain ⟨hD3a, hD3b, hD3c⟩ := dihedral3_facts
  have hgg : g₀ * g₀ ≠ 1 := fun h => hD4a (by
    have : eU.symm (DihedralGroup.r 1 * DihedralGroup.r 1) = 1 := by
      rw [map_mul]; exact Subtype.ext h
    rw [← MulEquiv.apply_symm_apply eU (DihedralGroup.r 1 * DihedralGroup.r 1), this, map_one])
  have hg4 : g₀ * g₀ * (g₀ * g₀) = 1 := by
    have := congrArg (fun w => (eU.symm w : K)) hD4b
    simp only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] at this
    exact this
  have hy1 : y₀ ≠ 1 := fun h => hD3a (by
    have : eB.symm (DihedralGroup.r 1) = 1 := Subtype.ext h
    rw [← MulEquiv.apply_symm_apply eB (DihedralGroup.r 1), this, map_one])
  have hy3 : y₀ * y₀ * y₀ = 1 := by
    have := congrArg (fun w => (eB.symm w : K)) hD3b
    simp only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] at this
    exact this
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; exact absurd hu (by norm_num)
  have huy : u * y₀ * u⁻¹ = y₀⁻¹ := by
    set a := eB ⟨u, huB⟩
    have ha2 : a * a = 1 := by
      rw [← map_mul]; rw [show (⟨u, huB⟩ : ↥(fixedSubgroup K β)) * ⟨u, huB⟩ = 1 from
        Subtype.ext hu2, map_one]
    have ha1 : a ≠ 1 := fun h => hu1 (by
      have : (⟨u, huB⟩ : ↥(fixedSubgroup K β)) = 1 := eB.injective (h.trans (map_one eB).symm)
      exact congrArg Subtype.val this)
    have := congrArg (fun w => (eB.symm w : K)) (hD3c a ha2 ha1)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, a,
      MulEquiv.symm_apply_apply] at this
    exact this
  have hX' := S4_no_invol_four_three (Ψ ⟨u, huX⟩) (Ψ ⟨g₀, hgX⟩) (Ψ ⟨y₀, hyX⟩)
  apply hX'
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, show (⟨u, huX⟩ : X) * ⟨u, huX⟩ = 1 from Subtype.ext hu2, map_one]
    · intro h
      have : (⟨u, huX⟩ : X) = 1 := Ψ.injective (by rw [h, map_one])
      exact hu1 (congrArg Subtype.val this)
    · rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hgu
    · intro h
      rw [← map_mul] at h
      have : (⟨g₀, hgX⟩ : X) * ⟨g₀, hgX⟩ = 1 := Ψ.injective (by rw [h, map_one])
      exact hgg (congrArg Subtype.val this)
    · simp only [← map_mul]
      rw [show (⟨g₀, hgX⟩ : X) * ⟨g₀, hgX⟩ * (⟨g₀, hgX⟩ * ⟨g₀, hgX⟩) = 1 from Subtype.ext hg4,
        map_one]
    · intro h
      have : (⟨y₀, hyX⟩ : X) = 1 := Ψ.injective (by rw [h, map_one])
      exact hy1 (congrArg Subtype.val this)
    · simp only [← map_mul]
      rw [show (⟨y₀, hyX⟩ : X) * ⟨y₀, hyX⟩ * ⟨y₀, hyX⟩ = 1 from Subtype.ext hy3, map_one]
  · simp only [← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using huy)

end CFSG.LocalAnalysis.WeakClosure81.L2Seitz
