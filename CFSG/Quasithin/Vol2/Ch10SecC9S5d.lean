module

public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.Quasithin.Vol2.Ch10SecC9S5a
public import CFSG.Quasithin.Vol2.Ch10SecC9S5b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_case_three_of_SL2 {n : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ Case10_1_1Three T L I := by
  rintro ⟨⟨e3⟩, -⟩
  classical
  have := Fintype.ofFinite F
  have hc := (Nat.card_congr eL.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [h3, Matrix.card_SL_field, Fin.prod_univ_two] at hc
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at hc
  rw [Nat.card_eq_fintype_card] at hF
  rw [hF] at hc
  set q := 2 ^ n with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < q - 1 := by omega
  have hsq : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, pow_two]
  rw [hsq, ← mul_assoc, Nat.mul_div_cancel _ hpos] at hc
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    rw [hq, hn2] at hc
    norm_num at hc
  · have hq8 : 8 ≤ q := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 63 ≤ q ^ 2 - 1 := by
      have : 64 ≤ q ^ 2 := by nlinarith
      omega
    have : 504 ≤ (q ^ 2 - 1) * q := by nlinarith
    omega

omit [Finite G] in
theorem exists_autI_hom {V J : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) :
    ∃ ρ : ↥J →* ↥(autI hV J), Function.Surjective ρ ∧
      ∀ j : ↥J, ρ j = 1 ↔ (j : G) ∈ Subgroup.centralizer (V : Set G) := by
  set ψ := convHom hV J hJN with hψ
  have hrange : ψ.range = autI hV J := range_convHom hV J hJN
  refine ⟨(MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict,
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective, fun j => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← convI_eq_one_iff hV ⟨j, hJN j.2⟩, ← convHom_apply hV hJN j, ← hψ]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

omit [Finite G] in
theorem nonempty_quotient_equiv {V J : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G))
    (hCJ : J ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 J) {S : Type*} [Group S]
    (e : ↥(autI hV J) ≃* S) : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* S) := by
  obtain ⟨ρ, hρs, hρ1⟩ := exists_autI_hom hV hJN
  have hker : CFSG.pCore 2 ↥J = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, hρ1, ← C1Pack.coe_mem_pCoreOf_iff J x, ← hCJ]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)).trans e⟩

omit [Finite G] in
theorem exists_quotient_oTwoZIn {V J : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G))
    (hJC : ¬ J ≤ Subgroup.centralizer (V : Set G))
    (hQ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) {S : Type*} [Group S]
    (e : ↥(autI hV J) ≃* S) (hZ : Subgroup.center S = ⊥) :
    ∃ φ : ↥J →* S, Function.Surjective φ ∧ φ.ker = (oTwoZIn J).subgroupOf J := by
  obtain ⟨ρ, hρs, hρ1⟩ := exists_autI_hom hV hJN
  have hOle : CFSG.pCore 2 ↥J ≤ ρ.ker := fun x hx =>
    (hρ1 x).mpr (hO ((C1Pack.coe_mem_pCoreOf_iff J x).mpr hx))
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hmk
  have key : ∀ j : ↥J, (j : G) ∈ Subgroup.centralizer (V : Set G) ↔
      mk j ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
    intro j
    constructor
    · intro hj
      set N := ρ.ker.map mk
      have hNn : N.Normal := Subgroup.Normal.map inferInstance mk (QuotientGroup.mk'_surjective _)
      have hNt : N ≠ ⊤ := by
        intro htop
        apply hJC
        intro x hx
        have hx' : mk ⟨x, hx⟩ ∈ N := htop ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hkx⟩ := hx'
        have hk' : k⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥J := by
          rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
          exact hkx
        have h1 := hO ((C1Pack.coe_mem_pCoreOf_iff J _).mpr hk')
        have h2 := (hρ1 k).mp hk
        have e1 : x = (k : G) * ((k⁻¹ * ⟨x, hx⟩ : ↥J) : G) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
        rw [e1]
        exact Subgroup.mul_mem _ h2 h1
      exact Ch11.SecA.le_center_of_normal_ne_top hQ hNt ⟨j, (hρ1 j).mpr hj, rfl⟩
    · intro hj
      set ρb := QuotientGroup.lift (CFSG.pCore 2 ↥J) ρ hOle
      have hρbs : Function.Surjective ρb := by
        intro y
        obtain ⟨x, rfl⟩ := hρs y
        exact ⟨mk x, rfl⟩
      have hes : Function.Surjective (e.toMonoidHom.comp ρb) := e.surjective.comp hρbs
      have hc := Subgroup.map_center_le_center hes ⟨mk j, hj, rfl⟩
      rw [hZ, Subgroup.mem_bot] at hc
      have hc' : e (ρ j) = 1 := hc
      rw [MulEquiv.map_eq_one_iff] at hc'
      exact (hρ1 j).mp hc'
  refine ⟨e.toMonoidHom.comp ρ, e.surjective.comp hρs, ?_⟩
  ext j
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    hρ1, Subgroup.mem_subgroupOf, key, oTwoZIn, preimageModTwoCore]
  constructor
  · intro h
    exact ⟨j, h, rfl⟩
  · rintro ⟨y, hy, hyj⟩
    have : y = j := Subtype.ext hyj
    rw [← this]
    exact hy

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem false_of_caseA (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two)
    (hK8a : FactK8a) (hK8b : FactK8b) {n : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (htor : fsuUL T L I ≤ VI T L I J w → ∃ x ∈ J ⊓ Subgroup.normalizer (L : Set G),
      Odd (orderOf x) ∧ (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∣ 2 ^ n - 1) ∧
      (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) ∧
      x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) : False := by
  have hV1 := c.fsuUL_le_VI h37 h38 h1011 h1012 h1027 h322 hK8a hK8b
    (Or.inl (not_case_three_of_SL2 hn hF eL))
  obtain ⟨x, hx, hodd, hp, hxL, hxC⟩ := htor hV1
  exact false_of_torus h37 h38 c.hyp h1011 h1013 h1026 c.ht c.htn hF eL hx.2 hodd hp hxL hxC

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
