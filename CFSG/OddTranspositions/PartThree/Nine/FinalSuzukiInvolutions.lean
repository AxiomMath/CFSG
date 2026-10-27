module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzukiSylow

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem card_inf_of_sz (h3 : Conclusion9_3 D hC) (h5 : Conclusion9_5 D hC T S)
    (hU : DeltaSetup hC T S U) {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m) :
    Nat.card ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) =
        (2 ^ (2 * m + 1)) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  set e := (eL.trans eH).trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz m))
  have : Finite (CFSG.Open.Sz m) := Finite.of_equiv _ e.toEquiv
  obtain ⟨P⟩ : Nonempty (Sylow 2 (CFSG.Open.Sz m)) := inferInstance
  have hP := ((CFSG.Open.bender_suzuki_borel_full m hm) P).2.2.2.2
  rw [← hR, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv, ← Sylow.card_eq_multiplicity P, hP]

theorem card_sup_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) :
    Nat.card (U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : Subgroup G) =
          2 ^ (3 * (2 * m + 1)) := by
  have hbij : Function.Bijective (fun p : U × ((T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :
        Subgroup G) =>
      (⟨g * p.1 * g⁻¹ * p.2, (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mpr
        ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : (U.map (MulAut.conj g).toMonoidHom ⊔
          ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
            CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : Subgroup G))) := by
    constructor
    · rintro ⟨a, r⟩ ⟨a', r'⟩ h
      have h' : g * (a : G) * g⁻¹ * r = g * a' * g⁻¹ * r' := congrArg Subtype.val h
      obtain ⟨ha, hr⟩ := hU.eq_of_conj_mul_eq hH h3 h5 hzU he a.2 a'.2 r.2.1 r'.2.1 h'
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hr)
    · rintro ⟨v, hv⟩
      obtain ⟨a, ha, r, hr, rfl⟩ :=
        (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mp hv
      exact ⟨(⟨a, ha⟩, ⟨r, hr⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, hUn, card_inf_of_sz h3 h5 hU hm eH]
  ring

theorem conj_mem_sup_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {h : G} (hhz : Commute (h * z * h⁻¹) z) {b : G} (hb : b ∈ U) :
    h * b * h⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  have hbS : h * b * h⁻¹ ∈ (S : Subgroup G) :=
    hU.regularCore_eq_sylow h3 h4 hQ hUn (odd_two_mul_add_one m) ▸
      hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hhz hb
  have hbK : h * b * h⁻¹ ∈ commutator G :=
    (inferInstance : (commutator G).Normal).conj_mem _
      (pResidualOf_le_commutator hH h3 hU h5.1 (hU.le_pResidualOf hb)) h
  exact hU.mem_sup_of_mem_commutator_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he hbS hbK

theorem eq_one_of_conj_mul_eq_conj_mul_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {h : G} (hhz : Commute (h * z * h⁻¹) z)
    (hhEU : ∀ a ∈ U, ∀ w ∈ U, h * z * h⁻¹ ≠ g * a * g⁻¹ * w)
    {b w a w' : G} (hb : b ∈ U) (hw : w ∈ U) (ha : a ∈ U) (hw' : w' ∈ U)
    (heq : h * b * h⁻¹ * w = g * a * g⁻¹ * w') : a = 1 := by
  by_contra ha1
  have := hU.isElementaryAbelian
  have hUc : ∀ x ∈ U, ∀ y ∈ U, Commute x y := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hzV := hU.conj_mem_sup_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he hhz hzU
  obtain ⟨a₁, ha₁, r₁, hr₁, hzr⟩ :=
    (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mp hzV
  have hA : g * a * g⁻¹ = h * b * h⁻¹ * (w * w'⁻¹) := by
    calc g * a * g⁻¹ = g * a * g⁻¹ * w' * w'⁻¹ := by group
      _ = h * b * h⁻¹ * w * w'⁻¹ := by rw [heq]
      _ = h * b * h⁻¹ * (w * w'⁻¹) := by group
  have hzC : h * z * h⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
    hU.regularCore_eq_centralizer hH h3 h5 hQ ▸
      hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hhz hzU
  have hc1 : Commute (h * z * h⁻¹) (h * b * h⁻¹) := (Commute.conj_iff h).mpr (hUc z hzU b hb)
  have hc2 : Commute (h * z * h⁻¹) (w * w'⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hzC _ (U.mul_mem hw (U.inv_mem hw'))).symm
  have hcA : Commute (h * z * h⁻¹) (g * a * g⁻¹) := by
    rw [hA]
    exact hc1.mul_right hc2
  have hcA₁ : Commute (g * a₁ * g⁻¹) (g * a * g⁻¹) := (Commute.conj_iff g).mpr (hUc a₁ ha₁ a ha)
  have hr₁A : Commute r₁ (g * a * g⁻¹) := by
    have hr : r₁ = (g * a₁ * g⁻¹)⁻¹ * (h * z * h⁻¹) := by rw [hzr]; group
    rw [hr]
    exact hcA₁.inv_left.mul_left hcA
  exact hhEU a₁ ha₁ r₁
    (hU.mem_of_commute_conj_of_sz hH h3 h5 hQ h7 hm eH hUn hzU hz1 hgz he ha ha1 hr₁ hr₁A) hzr

theorem conj_mul_mul_self_eq_one (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {h : G} (hhz : Commute (h * z * h⁻¹) z) {b w : G}
    (hb : b ∈ U) (hw : w ∈ U) : h * b * h⁻¹ * w * (h * b * h⁻¹ * w) = 1 := by
  have := hU.isElementaryAbelian
  have hbC : h * b * h⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
    hU.regularCore_eq_centralizer hH h3 h5 hQ ▸
      hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hhz hb
  have hc : w * (h * b * h⁻¹) = h * b * h⁻¹ * w := Subgroup.mem_centralizer_iff.mp hbC w hw
  calc h * b * h⁻¹ * w * (h * b * h⁻¹ * w) = h * b * h⁻¹ * (w * (h * b * h⁻¹)) * w := by group
    _ = h * (b * b) * h⁻¹ * (w * w) := by rw [hc]; group
    _ = 1 := by
      rw [← pow_two, ← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian b hb,
        CFSG.elemPow_eq_one_of_isElementaryAbelian w hw, mul_one, mul_one, mul_inv_cancel]

theorem exists_conj_mul_eq_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {h : G} (hhz : Commute (h * z * h⁻¹) z)
    (hhEU : ∀ a ∈ U, ∀ w ∈ U, h * z * h⁻¹ ≠ g * a * g⁻¹ * w) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hrU : r ∉ U) :
    ∃ b ∈ U, b ≠ 1 ∧ ∃ w ∈ U, ∃ a ∈ U, h * b * h⁻¹ * w = g * a * g⁻¹ * r := by
  classical
  have := hU.isElementaryAbelian
  have hhe : h * z * h⁻¹ ∉ U := fun hzU' => hhEU 1 U.one_mem _ hzU' (by group)
  have hUV : U ≤ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
    le_sup_of_le_right (le_inf hU.le_sylow_map hU.le_pResidualOf)
  have hdec : ∀ p : U × U, ∃ ρ ∈ (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
        ∃ a ∈ U, h * (p.1 : G) * h⁻¹ * p.2 = g * a * g⁻¹ * ρ := by
    intro p
    obtain ⟨a, ha, ρ, hρ, heq⟩ := (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mp
      (Subgroup.mul_mem _ (hU.conj_mem_sup_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he hhz
        p.1.2) (hUV p.2.2))
    exact ⟨ρ, hρ, a, ha, heq⟩
  choose ρ hρR α hαU hρ using hdec
  have hαρ : ∀ p p' : U × U, ρ p = ρ p' →
      h * (p.1 : G) * h⁻¹ * p.2 = h * (p'.1 : G) * h⁻¹ * p'.2 := by
    intro p p' hpp
    rw [hρ p, hρ p', hpp]
    by_cases hρU : ρ p' ∈ U
    · have hρU' : ρ p ∈ U := by rw [hpp]; exact hρU
      have h1 := hU.eq_one_of_conj_mul_eq_conj_mul_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he
        hhz hhEU p.1.2 p.2.2 (hαU p) hρU' (hρ p)
      have h2 := hU.eq_one_of_conj_mul_eq_conj_mul_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he
        hhz hhEU p'.1.2 p'.2.2 (hαU p') hρU (hρ p')
      rw [h1, h2]
    · have hi : ∀ q : U × U, g * α q * g⁻¹ * ρ q * (g * α q * g⁻¹ * ρ q) = 1 := fun q => by
        rw [← hρ q]
        exact hU.conj_mul_mul_self_eq_one hH h3 h5 hQ h7 hzU hz1 hhz q.1.2 q.2.2
      have hq := hi p
      rw [hpp] at hq
      rw [hU.eq_of_mul_self_eq_one_of_sz hH h3 h5 hQ h7 hm eH hUn hzU hz1 hgz he (hαU p)
        (hαU p') (hρR p') hρU hq (hi p')]
  let Φ : U × U → ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) := fun p => ⟨ρ p, hρR p⟩
  have hΦ : Function.Injective Φ := by
    intro p p' hpp
    have heq := hαρ p p' (congrArg Subtype.val hpp)
    obtain ⟨hb, hw⟩ := hU.eq_of_conj_mul_eq hH h3 h5 hzU hhe p.1.2 p'.1.2
      (hU.le_sylow_map p.2.2) (hU.le_sylow_map p'.2.2) heq
    exact Prod.ext (Subtype.ext hb) (Subtype.ext hw)
  have hcard : Nat.card ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) ≤ Nat.card (U × U) := by
    rw [card_inf_of_sz h3 h5 hU hm eH, Nat.card_prod, hUn, pow_two]
  obtain ⟨p, hp⟩ := (hΦ.bijective_of_nat_card_le hcard).2 ⟨r, hr⟩
  have hρr : ρ p = r := congrArg Subtype.val hp
  refine ⟨p.1, p.1.2, fun hb1 => hrU ?_, p.2, p.2.2, α p, hαU p, hρr ▸ hρ p⟩
  have hw : g * 1 * g⁻¹ * (p.2 : G) = g * α p * g⁻¹ * r := by
    rw [← hρr, ← hρ p, hb1]
    group
  obtain ⟨-, hwr⟩ := hU.eq_of_conj_mul_eq hH h3 h5 hzU he U.one_mem (hαU p)
    (hU.le_sylow_map p.2.2) hr.1 hw
  exact hwr ▸ p.2.2

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
