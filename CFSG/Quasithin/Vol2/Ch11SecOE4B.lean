module

public import CFSG.Quasithin.Background.A1cA130
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BCaseAux
public import CFSG.Quasithin.H13.NQRigidOverlapSylow

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

open CFSG.Quasithin

theorem nonempty_omegaTwo_equiv {Q : Type*} [CommGroup Q] [Finite Q] {q e : ℕ}
    [hq : Fact q.Prime] (he : 2 ≤ e)
    (φ : Q ≃* (Multiplicative (ZMod (q ^ e)) × Multiplicative (ZMod (q ^ e)))) :
    Nonempty (↥(powMonoidHom (q ^ 2) : Q →* Q).ker ≃* Multiplicative (Fin 2 → ZMod (q ^ 2))) := by
  classical
  have hΩ : Nat.card (powMonoidHom q : Q →* Q).ker = q ^ 2 :=
    (H13.NQBlock.homocyclic_frattini_transport (by omega : 1 ≤ e) φ
      (1 : Q →* MulAut Q)).2.choose_spec.2.2.1
  have hord : orderOf (Multiplicative.ofAdd (1 : ZMod (q ^ e))) = q ^ e := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  set a : Q := φ.symm (Multiplicative.ofAdd 1, 1) with ha
  set b : Q := φ.symm (1, Multiplicative.ofAdd 1) with hb
  have hoa : orderOf a = q ^ e := by
    rw [ha, MulEquiv.orderOf_eq, Prod.orderOf_mk, hord, orderOf_one, Nat.lcm_one_right]
  have hob : orderOf b = q ^ e := by
    rw [hb, MulEquiv.orderOf_eq, Prod.orderOf_mk, hord, orderOf_one, Nat.lcm_one_left]
  have hab : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    rw [Subgroup.mem_bot]
    have hφa : φ (a ^ i) = ((Multiplicative.ofAdd (1 : ZMod (q ^ e))) ^ i, 1) := by
      rw [map_zpow, ha, MulEquiv.apply_symm_apply]
      ext <;> simp
    have hφb : φ (b ^ j) = (1, (Multiplicative.ofAdd (1 : ZMod (q ^ e))) ^ j) := by
      rw [map_zpow, hb, MulEquiv.apply_symm_apply]
      ext <;> simp
    have hj' : φ (b ^ j) = φ (a ^ i) := congrArg φ hj
    rw [hφa, hφb, Prod.mk.injEq] at hj'
    apply φ.injective
    rw [hφa, φ.map_one, ← hj'.1]
    rfl
  obtain ⟨ψ⟩ := A36B.omegaTwo_equiv hq.out he hΩ.le hoa hob hab
  exact ⟨ψ.trans (A36B.multFinTwoEquiv (q ^ 2)).symm⟩

variable {X : Type} [Group X] [Finite X]

theorem exists_five_elem_of_isSL2 (hs : IsSL2 5 (X ⧸ CFSG.fittingSubgroup X)) :
    ∃ y : X, y ∉ CFSG.fittingSubgroup X ∧ y ^ 5 ∈ CFSG.fittingSubgroup X ∧
      ∃ k : ℕ, y ^ 5 ^ k = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ⟩ := hs
  set z : X ⧸ CFSG.fittingSubgroup X := ψ.symm (A1c.sl2U 5) with hz
  have hz5 : orderOf z = 5 := by rw [hz, MulEquiv.orderOf_eq, A1c.orderOf_sl2U]
  have hz5' : z ^ 5 = 1 := by
    rw [← hz5]
    exact pow_orderOf_eq_one z
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, m, hm, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 5 (by norm_num)
  refine ⟨x ^ m, ?_, ?_, c, ?_⟩
  · intro hmem
    have h1 := (QuotientGroup.eq_one_iff (N := CFSG.fittingSubgroup X) _).mpr hmem
    rw [QuotientGroup.mk_pow, hx] at h1
    exact hm (hz5 ▸ orderOf_dvd_of_pow_eq_one h1)
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_pow, hx, ← pow_mul,
      mul_comm, pow_mul, hz5', one_pow]
  · rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]

theorem false_of_isSL2_five_of_homocyclic (hs : IsSL2 5 (X ⧸ CFSG.fittingSubgroup X))
    (hext : A36Extra X) {e : ℕ} (he : 2 ≤ e)
    (φ : ↥(CFSG.pCore 5 X) ≃* (Multiplicative (ZMod (5 ^ e)) × Multiplicative (ZMod (5 ^ e)))) :
    False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := CFSG.pCore 5 X with hP
  have hPc : ∀ a b : ↥P, a * b = b * a := fun a b =>
    φ.injective (by rw [map_mul, map_mul, mul_comm])
  let _ : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := hPc }
  have h5F : 5 ∣ Nat.card (CFSG.fittingSubgroup X) := by
    have hcard : Nat.card ↥P = 5 ^ e * 5 ^ e := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]
    have h1 : 5 ∣ Nat.card ↥P := by
      rw [hcard]
      exact (dvd_pow_self 5 (by omega)).mul_right _
    exact h1.trans (Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting X 5))
  obtain ⟨P₀, hP₀, -, -, hker⟩ := hext 5 h5.out h5F
  obtain ⟨y, hyF, hy5, k, hyk⟩ := exists_five_elem_of_isSL2 hs
  have hy5P : y ^ 5 ∈ P := by
    obtain ⟨j, -, hj⟩ : ∃ j ≤ k, orderOf (y ^ 5) = 5 ^ j := (Nat.dvd_prime_pow h5.out).mp
      (orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hyk, one_pow]))
    exact H13.NQRigid.mem_pCore_of_mem_fitting hy5 hj
  set α := H13.NQBlock.omegaAut (5 ^ 2) (MulAut.conjNormal y : MulAut ↥P) with hα
  have hc5 : (MulAut.conjNormal (y ^ 5) : MulAut ↥P) = 1 := by
    ext u
    have h1 := congrArg Subtype.val (hPc ⟨y ^ 5, hy5P⟩ u)
    simp only [Subgroup.coe_mul] at h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [h1, mul_inv_cancel_right]
  have hα5 : α ^ 5 = 1 := by
    rw [hα, ← map_pow, ← map_pow, hc5, map_one]
  obtain ⟨Ψ⟩ := nonempty_omegaTwo_equiv he φ
  have hfix : ∀ w : ↥(powMonoidHom (5 ^ 2) : ↥P →* ↥P).ker, w ^ 5 = 1 → α w = w := by
    intro w hw
    rcases (Nat.dvd_prime h5.out).mp (orderOf_dvd_of_pow_eq_one hα5) with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1, MulAut.one_apply]
    · exact fixes_of_orderOf_eq_prime_of_mulEquiv ⟨Ψ⟩ (by norm_num) h1 hw
  have htriv : ActsTriviallyOnFrattiniQuotient (P₀.map P.subtype) y := by
    rintro _ ⟨d, hd, rfl⟩
    have hd5 : d ^ 5 = 1 := hP₀.pow_eq_one d hd
    have hdΩ : d ∈ (powMonoidHom (5 ^ 2) : ↥P →* ↥P).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_two, pow_mul, hd5, one_pow]
    have h1 := congrArg (fun w : ↥(powMonoidHom (5 ^ 2) : ↥P →* ↥P).ker => ((w : ↥P) : X))
      (hfix ⟨d, hdΩ⟩ (Subtype.ext hd5))
    simp only [hα, H13.NQBlock.omegaAut, H13.NQBlock.autRestrict_apply,
      MulAut.conjNormal_apply] at h1
    simp only [Subgroup.coe_subtype]
    rw [h1, inv_mul_cancel]
    exact one_mem _
  exact hyF ((hker y).mp htriv)

end CFSG.Quasithin.Vol2.Ch11.OE4
