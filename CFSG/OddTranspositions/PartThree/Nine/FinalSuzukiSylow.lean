module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzuki
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem eq_of_conj_mul_eq (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {z : G} (hzU : z ∈ U) {g : G}
    (he : g * z * g⁻¹ ∉ U) {a a' r r' : G} (haU : a ∈ U) (ha'U : a' ∈ U)
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hr' : r' ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (h : g * a * g⁻¹ * r = g * a' * g⁻¹ * r') : a = a' ∧ r = r' := by
  have h' : g * (a'⁻¹ * a) * g⁻¹ = r' * r⁻¹ := by
    calc g * (a'⁻¹ * a) * g⁻¹ = (g * a' * g⁻¹)⁻¹ * (g * a * g⁻¹ * r) * r⁻¹ := by group
      _ = (g * a' * g⁻¹)⁻¹ * (g * a' * g⁻¹ * r') * r⁻¹ := by rw [h]
      _ = r' * r⁻¹ := by group
  have hT : g * (a'⁻¹ * a) * g⁻¹ ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [h']
    exact Subgroup.mul_mem _ hr' (Subgroup.inv_mem _ hr)
  have h1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he (U.mul_mem (U.inv_mem ha'U) haU) hT
  have haa : a = a' := (inv_mul_eq_one.mp h1).symm
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

theorem le_normalizer_inf_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) :
    U.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer
      (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) : Set G) := by
  have := hU.isElementaryAbelian
  rintro _ ⟨a, haU, rfl⟩
  have hA2 : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian a haU, mul_one, mul_inv_cancel]
  intro r
  change r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ↔
    g * a * g⁻¹ * r * (g * a * g⁻¹)⁻¹ ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  refine ⟨fun hr => hU.conj_mem_inf_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he haU hr,
    fun hr => ?_⟩
  have h := hU.conj_mem_inf_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he haU hr
  have heq : g * a * g⁻¹ * (g * a * g⁻¹ * r * (g * a * g⁻¹)⁻¹) * (g * a * g⁻¹)⁻¹ = r := by
    generalize g * a * g⁻¹ = A at hA2 ⊢
    calc A * (A * r * A⁻¹) * A⁻¹ = A * A * r * (A * A)⁻¹ := by group
      _ = r := by rw [hA2, inv_one, one_mul, mul_one]
  rwa [heq] at h

theorem mem_sup_iff_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {x : G} :
    x ∈ U.map (MulAut.conj g).toMonoidHom ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ↔
      ∃ a ∈ U, ∃ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), x = g * a * g⁻¹ * r := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hU.le_normalizer_inf_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he), Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨a, haU, rfl⟩, r, hr, rfl⟩
    exact ⟨a, haU, r, hr, rfl⟩
  · rintro ⟨a, haU, r, hr, rfl⟩
    exact ⟨_, ⟨a, haU, rfl⟩, r, hr, rfl⟩

theorem sup_le_commutator (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) (g : G) :
    U.map (MulAut.conj g).toMonoidHom ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ≤ commutator G := by
  have hLK := pResidualOf_le_commutator hH h3 hU h5.1
  refine sup_le ?_ (inf_le_right.trans hLK)
  rintro _ ⟨a, haU, rfl⟩
  exact (inferInstance : (commutator G).Normal).conj_mem _ (hLK (hU.le_pResidualOf haU)) g

theorem sup_le_sylow_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hUn : Nat.card U = 2 ^ (2 * m + 1)) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G}
    (hgz : Commute (g * z * g⁻¹) z) :
    U.map (MulAut.conj g).toMonoidHom ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ≤ (S : Subgroup G) := by
  rw [← hU.regularCore_eq_sylow h3 h4 hQ hUn (odd_two_mul_add_one m)]
  refine sup_le ?_ fun r hr => ?_
  · rintro _ ⟨a, haU, rfl⟩
    exact hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz haU
  · rw [hU.regularCore_eq_centralizer hH h3 h5 hQ, Subgroup.mem_centralizer_iff]
    exact fun v hv => (commute_of_mem_sylow_map h5 hU hr.1 hv).symm.eq

theorem d_not_mem_sup_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) :
    hC.d ∉ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  intro hu
  obtain ⟨a, haU, r, hr, hur⟩ :=
    (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mp hu
  have haT : g * a * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    have h : g * a * g⁻¹ = hC.d * r⁻¹ := by rw [hur]; group
    rw [h]
    exact Subgroup.mul_mem _ (d_mem_sylow_map hC h3 T) (Subgroup.inv_mem _ hr.1)
  have ha1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he haU haT
  rw [ha1, mul_one, mul_inv_cancel, one_mul] at hur
  exact not_mem_pResidualOf_of_mem hH h3 hC.hd (hur ▸ hr.2)

theorem mul_d_mem_sup_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxV : x ∉ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) :
    x * hC.d ∈ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hxQ : x ∈ Q := (hU.regularCore_eq_sylow h3 h4 hQ hUn (odd_two_mul_add_one m)) ▸ hxS
  obtain ⟨a, haU, t, htT, rfl⟩ :=
    hU.exists_eq_conj_mul_of_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz he hxQ
  obtain ⟨r, hr, hrt | hrt⟩ := exists_mem_inf_of_mem_sylow_map h3 htT
  · exact (hxV ((hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mpr
      ⟨a, haU, r, hr, by rw [hrt]⟩)).elim
  · subst hrt
    refine (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mpr ⟨a, haU, r, hr, ?_⟩
    have hc := commute_d_of_mem_sylow_map hr.1
    calc g * a * g⁻¹ * (hC.d * r) * hC.d = g * a * g⁻¹ * (r * hC.d) * hC.d := by rw [hc.eq]
      _ = g * a * g⁻¹ * r * (hC.d * hC.d) := by group
      _ = g * a * g⁻¹ * r := by rw [hu2, mul_one]

theorem relIndex_sup_eq_two_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) :
    (U.map (MulAut.conj g).toMonoidHom ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))).relIndex (S : Subgroup G) = 2 := by
  have huS : hC.d ∈ (S : Subgroup G) := by
    have h : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
    exact h.1
  have huV := hU.d_not_mem_sup_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨hC.d, huS⟩, fun x => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hx : (x : G) ∈ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
  · refine Or.inr ⟨hx, fun hxu => huV ?_⟩
    have h : hC.d = (x : G)⁻¹ * ((x : G) * hC.d) := by group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hxu
  · exact Or.inl ⟨hU.mul_d_mem_sup_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he x.2 hx, hx⟩

theorem d_not_mem_commutator_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) : hC.d ∉ commutator G := by
  set V := U.map (MulAut.conj g).toMonoidHom ⊔
    ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) with hV
  have hVS : V ≤ (S : Subgroup G) := hU.sup_le_sylow_of_sz hH h3 h4 h5 hQ h7 hUn hzU hz1 hgz
  have hUV : U ≤ V := le_sup_of_le_right (le_inf hU.le_sylow_map hU.le_pResidualOf)
  have huV := hU.d_not_mem_sup_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he
  have hconj : ∀ x : G, x⁻¹ * hC.d * x ∉ V := by
    intro x hx
    have hxD : x⁻¹ * hC.d * x ∈ D := by simpa using hC.setup.conj_mem x⁻¹ hC.hd
    have hxΔ : x⁻¹ * hC.d * x ∈ (S : Set G) ∩ D := ⟨hVS hx, hxD⟩
    rw [hU.sylow_inter] at hxΔ
    obtain ⟨w, hw, hwx⟩ := hxΔ
    have hwx' : hC.d * w = x⁻¹ * hC.d * x := hwx
    apply huV
    have h : hC.d = x⁻¹ * hC.d * x * w⁻¹ := by rw [← hwx']; group
    rw [h]
    exact V.mul_mem hx (V.inv_mem (hUV hw))
  obtain ⟨N, hNn, hsq, huN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal S hVS
    (hU.relIndex_sup_eq_two_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he)
    (hC.setup.oddT.orderOf_eq_two hC.hd) hconj
  intro huK
  apply huN
  have hKN : commutator G ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h : ⁅x, y⁆ = (x * y) ^ 2 * (y⁻¹ * x⁻¹ ^ 2 * y⁻¹⁻¹) * y⁻¹ ^ 2 := by
      simp only [commutatorElement_def, pow_two]
      group
    rw [h]
    exact N.mul_mem (N.mul_mem (hsq _) (hNn.conj_mem _ (hsq _) _)) (hsq _)
  exact hKN huK

theorem mem_sup_of_mem_commutator_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {x : G} (hxS : x ∈ (S : Subgroup G)) (hxK : x ∈ commutator G) :
    x ∈ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  by_contra hxV
  have hxu := hU.mul_d_mem_sup_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he hxS hxV
  apply hU.d_not_mem_commutator_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he
  have h : hC.d = x⁻¹ * (x * hC.d) := by group
  rw [h]
  exact (commutator G).mul_mem ((commutator G).inv_mem hxK) (hU.sup_le_commutator hH h3 h5 g hxu)

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
