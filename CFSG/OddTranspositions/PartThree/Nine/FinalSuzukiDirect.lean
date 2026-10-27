module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzukiUnion
public import CFSG.OddTranspositions.PartThree.Nine.SquareMap.Assembly
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
  (cosetNormalizerPerm cosetNormalizerPerm_apply
    cosetNormalizerPerm_ker_eq_entire_centralizer)

private theorem commutator_mem_of_sq_mem {G : Type*} [Group G] {S U : Subgroup G}
    (hSq : ∀ s ∈ S, s * s ∈ U) {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    x * y * x⁻¹ * y⁻¹ ∈ U := by
  have ha : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
  have hxx : x * x ∈ U := hSq x hx
  have haa : (x⁻¹ * y) * (x⁻¹ * y) ∈ U := hSq _ ha
  have hyy : y * y ∈ U := hSq y hy
  have h1 : x * y * x⁻¹ * y = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) := by group
  have h2 : x * y * x⁻¹ * y⁻¹ =
      ((x * x) * ((x⁻¹ * y) * (x⁻¹ * y))) * (y * y)⁻¹ := by
    rw [← h1]; group
  rw [h2]
  exact U.mul_mem (U.mul_mem hxx haa) (U.inv_mem hyy)

private theorem le_normalizer_centralizer {G : Type*} [Group G] {U : Subgroup G} :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro u hu
  have hxu : x⁻¹ * u * x ∈ U := (Subgroup.mem_set_normalizer_iff''.mp hx u).mp hu
  calc u * (x * c * x⁻¹) = x * (x⁻¹ * u * x) * c * x⁻¹ := by group
    _ = x * c * (x⁻¹ * u * x) * x⁻¹ := by
      rw [show x * (x⁻¹ * u * x) * c * x⁻¹
            = x * ((x⁻¹ * u * x) * c) * x⁻¹ by group, hc _ hxu]
      group
    _ = (x * c * x⁻¹) * u := by group

theorem false_of_wcl_not_commutative_of_sz_direct (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1)) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hW : ¬ IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUel : IsElementaryAbelian 2 U := hU.isElementaryAbelian
  haveI : IsMulCommutative U := hUel.toIsMulCommutative
  have hQS : Q = (S : Subgroup G) := hU.regularCore_eq_sylow h3 h4 hQ hUn (odd_two_mul_add_one m)
  have hQC : Q = Subgroup.centralizer (U : Set G) := hU.regularCore_eq_centralizer hH h3 h5 hQ
  have hSU : (S : Subgroup G) = Subgroup.centralizer (U : Set G) := hQS.symm.trans hQC
  have hUc' : (S : Subgroup G) ≤ Subgroup.centralizer (U : Set G) := hSU.le
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huS : hC.d ∈ (S : Subgroup G) := by
    have h : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
    exact h.1
  have hUcom : ∀ x ∈ U, ∀ y ∈ U, Commute x y := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨e, he, heU⟩ : ∃ e ∈ CFSG.LargeExtraspecial.S11.wclSet z, e ∉ U := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hW
    have hle : CFSG.LargeExtraspecial.S11.wcl z ≤ U := (Subgroup.closure_le U).mpr hall
    exact ⟨⟨fun a b => Subtype.ext (hUcom _ (hle a.2) _ (hle b.2)).eq⟩⟩
  obtain ⟨g, rfl, hgz⟩ := he
  have hgz' : Commute (g * z * g⁻¹) z := hgz
  have he0 : g * z * g⁻¹ ∉ U := heU
  obtain ⟨y, hy, hyEU⟩ : ∃ y ∈ CFSG.LargeExtraspecial.S11.wclSet z,
      ∀ a ∈ U, ∀ w ∈ U, y ≠ g * a * g⁻¹ * w := by
    by_contra hall
    push Not at hall
    apply hW
    refine Subgroup.isMulCommutative_closure ?_
    intro y₁ hy₁ y₂ hy₂ _
    obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := hall y₁ hy₁
    obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := hall y₂ hy₂
    have hEC : ∀ a ∈ U, g * a * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := fun a ha =>
      hQC ▸ hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz' ha
    have hAA : Commute (g * a₁ * g⁻¹) (g * a₂ * g⁻¹) :=
      (Commute.conj_iff g).mpr (hUcom _ ha₁ _ ha₂)
    have h12 : Commute (g * a₁ * g⁻¹) c₂ :=
      (Subgroup.mem_centralizer_iff.mp (hEC a₁ ha₁) c₂ hc₂).symm
    have h21 : Commute c₁ (g * a₂ * g⁻¹) := Subgroup.mem_centralizer_iff.mp (hEC a₂ ha₂) c₁ hc₁
    exact (hAA.mul_right h12).mul_left (h21.mul_right (hUcom _ hc₁ _ hc₂))
  obtain ⟨h, rfl, hhz⟩ := hy
  have hhz' : Commute (h * z * h⁻¹) z := hhz
  have hhEU : ∀ a ∈ U, ∀ w ∈ U, h * z * h⁻¹ ≠ g * a * g⁻¹ * w := hyEU
  have hhe : h * z * h⁻¹ ∉ U := fun hzU' =>
    hhEU 1 U.one_mem (h * z * h⁻¹) hzU' (by group)
  let TG : Subgroup G := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  let Lsub : Subgroup G := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  let E : Subgroup G := U.map (MulAut.conj g).toMonoidHom
  let F : Subgroup G := U.map (MulAut.conj h).toMonoidHom
  let R : Subgroup G := TG ⊓ Lsub
  let V : Subgroup G := E ⊔ R
  let A : Subgroup G := E ⊔ U
  let B : Subgroup G := F ⊔ U
  let X : Subgroup G := Lsub ⊓ Subgroup.normalizer (U : Set G)
  let NN : Subgroup G := Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))
  let Δ : Set G := (fun v : G => hC.d * v) '' (U : Set G)
  let q : ℕ := 2 ^ (2 * m + 1)
  have hSq : ∀ s ∈ (S : Subgroup G), s * s ∈ U := fun s ss =>
    hU.mul_self_mem_of_mem_regularCore_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz' he0
      (hQS.symm ▸ ss)
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian a ha, mul_one, mul_inv_cancel]
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hf
    calc h * b * h⁻¹ * (h * b * h⁻¹) = h * (b * b) * h⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian b hb, mul_one, mul_inv_cancel]
  have hEc : E ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hQC ▸ hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz' ha
  have hFc : F ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hQC ▸ hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hhz' hb
  have hEN : E ≤ Subgroup.normalizer (U : Set G) :=
    hEc.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hFN : F ≤ Subgroup.normalizer (U : Set G) :=
    hFc.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hUV : U ≤ V := le_sup_of_le_right (le_inf hU.le_sylow_map hU.le_pResidualOf)
  have hVS : V ≤ (S : Subgroup G) :=
    hU.sup_le_sylow_of_sz hH h3 h4 h5 hQ h7 hUn hzU hz1 hgz'
  have hVK : V ≤ commutator G := hU.sup_le_commutator hH h3 h5 g
  have hLK : Lsub ≤ commutator G := pResidualOf_le_commutator hH h3 hU h5.1
  have hFV : F ≤ V := by
    rintro _ ⟨b, hb, rfl⟩
    exact hU.conj_mem_sup_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz' he0 hhz' hb
  have hAV : A ≤ V := sup_le le_sup_left hUV
  have hBV : B ≤ V := sup_le hFV hUV
  have hUB : U ≤ B := le_sup_right
  have hUcard : Nat.card U = q := hUn
  have hRcard : Nat.card R = q ^ 2 := hU.card_inf_of_sz h3 h5 hm eH
  have hEcard : Nat.card E = q := by
    rw [← hUcard]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
  have hFcard : Nat.card F = q := by
    rw [← hUcard]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective
  have hEiU : E ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx.1
    have ha1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he0 ha (hU.le_sylow_map hx.2)
    simp [ha1]
  have hFiU : F ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx.1
    have hb1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU hhe hb (hU.le_sylow_map hx.2)
    simp [hb1]
  have hAcard : Nat.card A = q ^ 2 := by
    have hcard :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := E) (K := U) hEN
    rw [hEiU, Subgroup.card_bot, mul_one, hEcard, hUcard] at hcard
    simpa [pow_two] using hcard
  have hBcard : Nat.card B = q ^ 2 := by
    have hcard :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := F) (K := U) hFN
    rw [hFiU, Subgroup.card_bot, mul_one, hFcard, hUcard] at hcard
    simpa [pow_two] using hcard
  have hR_eq : R = V ⊓ Subgroup.centralizer ({hC.d} : Set G) := by
    refine le_antisymm (le_inf le_sup_right ?_) ?_
    · intro r hr
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_d_of_mem_sylow_map hr.1).symm.eq
    · intro v hv
      have hvS : v ∈ (S : Subgroup G) := hVS hv.1
      have hvC : v ∈ Subgroup.centralizer (U : Set G) := hSU ▸ hvS
      have hvu : v * hC.d = hC.d * v := Subgroup.mem_centralizer_singleton_iff.mp hv.2
      have hvu' : v * hC.d * v⁻¹ = hC.d := by rw [hvu]; group
      have hvT : v ∈ TG := hU.mem_sylow_map_of_mem_centralizer h5 hvC hvu'
      obtain ⟨r, hr, hvr | hvr⟩ := exists_mem_inf_of_mem_sylow_map h3 hvT
      · rw [hvr]; exact hr
      · exfalso
        apply hU.d_not_mem_commutator_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz' he0
        have hu : hC.d = v * r⁻¹ := by rw [hvr]; group
        rw [hu]
        exact (commutator G).mul_mem (hVK hv.1) ((commutator G).inv_mem (hLK hr.2))
  have hRI : ∀ r ∈ R, r * r = 1 → r ∈ U := by
    intro r hr hr2
    have h := hU.inv_mul_mem_of_mul_self_eq_of_sz hH h3 h5 hm eH hr (Subgroup.one_mem _)
      (by rw [hr2, mul_one])
    rw [mul_one] at h
    exact inv_mem_iff.mp h
  have hAiB : A ⊓ B = U := by
    refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
    intro x hx
    have hxA : x ∈ E ⊔ U := hx.1
    have hxB : x ∈ F ⊔ U := hx.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right E U hEN,
      Set.mem_mul] at hxA
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F U hFN,
      Set.mem_mul] at hxB
    obtain ⟨e, he, w, hw, rfl⟩ := hxA
    obtain ⟨f, hf, w', hw', hx'⟩ := hxB
    obtain ⟨a, ha, hea⟩ := Subgroup.mem_map.mp he
    obtain ⟨b, hb, hfb⟩ := Subgroup.mem_map.mp hf
    have heq : h * b * h⁻¹ * w' = g * a * g⁻¹ * w := by
      have hfb' : h * b * h⁻¹ = f := hfb
      have hea' : g * a * g⁻¹ = e := hea
      rw [hfb', hea']
      exact hx'
    have ha1 := hU.eq_one_of_conj_mul_eq_conj_mul_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1
      hgz' he0 hhz' hhEU hb hw' ha hw heq
    have he1 : e = 1 := by
      rw [← hea]
      simp [ha1]
    rw [he1, one_mul]
    exact hw
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro x hx
    have hx' : x ∈ E ⊔ U := hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right E U hEN,
      Set.mem_mul] at hx'
    obtain ⟨e, he, w, hw, rfl⟩ := hx'
    have he2 : e * e = 1 := hE2 e he
    have hw2 : w * w = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian w hw
    have hwe : w * e = e * w := Subgroup.mem_centralizer_iff.mp (hEc he) w hw
    calc e * w * (e * w) = e * (w * e) * w := by group
      _ = e * (e * w) * w := by rw [hwe]
      _ = (e * e) * (w * w) := by group
      _ = 1 := by rw [he2, hw2, mul_one]
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro x hx
    have hx' : x ∈ F ⊔ U := hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F U hFN,
      Set.mem_mul] at hx'
    obtain ⟨f, hf, w, hw, rfl⟩ := hx'
    have hf2 : f * f = 1 := hF2 f hf
    have hw2 : w * w = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian w hw
    have hwf : w * f = f * w := Subgroup.mem_centralizer_iff.mp (hFc hf) w hw
    calc f * w * (f * w) = f * (w * f) * w := by group
      _ = f * (f * w) * w := by rw [hwf]
      _ = (f * f) * (w * w) := by group
      _ = 1 := by rw [hf2, hw2, mul_one]
  have hA_norm_B : A ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have hcomm := commutator_mem_of_sq_mem hSq (hVS (hAV ha)) (hVS (hBV hb))
    have h : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [h]
    exact B.mul_mem (hUB hcomm) hb
  have hcardAB : Nat.card (A ⊔ B : Subgroup G) = q ^ 3 := by
    have hcard :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := A) (K := B) hA_norm_B
    rw [hAiB, hUcard, hAcard, hBcard] at hcard
    have hqpos : 0 < q := pow_pos (show (0 : ℕ) < 2 by norm_num) (2 * m + 1)
    exact Nat.mul_right_cancel hqpos (by rw [hcard]; ring)
  have hVcard : Nat.card V = q ^ 3 := by
    have h := hU.card_sup_of_sz hH h3 h5 hQ h7 hm eH hUn hzU hz1 hgz' he0
    rw [h]
    show 2 ^ (3 * (2 * m + 1)) = q ^ 3
    rw [show q = 2 ^ (2 * m + 1) from rfl, ← pow_mul]
    congr 1
    ring
  have hAB : A ⊔ B = V := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAV hBV) ?_
    rw [hVcard, hcardAB]
  have hI : ∀ v ∈ V, v * v = 1 → v ∈ A ∨ v ∈ B := fun v hv hv2 =>
    mem_sup_or_mem_sup_of_sz hH h3 h4 h5 hU hQ h7 hm eH hUn hzU hz1 hgz' he0 hhz' hhEU hv hv2
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := fun _ hx => hx.2
  have hXu : X ≤ Subgroup.centralizer ({hC.d} : Set G) := fun x hx =>
    PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hx.1)
  have hXS : X ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    hXU.trans le_normalizer_centralizer
  have hVSK : V = (S : Subgroup G) ⊓ commutator G := by
    refine le_antisymm (le_inf hVS hVK) ?_
    intro x hx
    exact hU.mem_sup_of_mem_commutator_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz' he0
      hx.1 hx.2
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx v hv
    have hv' : v ∈ (S : Subgroup G) ⊓ commutator G := hVSK ▸ hv
    have hvC : v ∈ Subgroup.centralizer (U : Set G) := hSU ▸ hv'.1
    have : x * v * x⁻¹ ∈ (S : Subgroup G) ⊓ commutator G :=
      ⟨hSU.symm ▸ (Subgroup.mem_set_normalizer_iff.mp (hXS hx) v).mp hvC,
        (inferInstance : (commutator G).Normal).conj_mem v hv'.2 x⟩
    rwa [← hVSK] at this
  have hXN : X ≤ NN := by
    intro x hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hcx : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
      refine ⟨x * v * x⁻¹, (Subgroup.mem_set_normalizer_iff.mp (hXU hx) v).mp hv, ?_⟩
      calc hC.d * (x * v * x⁻¹) = x * hC.d * v * x⁻¹ := by rw [hcx]; group
        _ = x * (hC.d * v) * x⁻¹ := by group
    · rintro ⟨v, hv, hv2⟩
      refine ⟨x⁻¹ * v * x, (Subgroup.mem_set_normalizer_iff''.mp (hXU hx) v).mp hv, ?_⟩
      have hcx : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
      have h1 : x⁻¹ * hC.d * x = hC.d := by
        calc x⁻¹ * hC.d * x = x⁻¹ * (hC.d * x) := by group
          _ = x⁻¹ * (x * hC.d) := by rw [← hcx]
          _ = hC.d := by group
      have hcx' : hC.d * x⁻¹ = x⁻¹ * hC.d := by
        calc hC.d * x⁻¹ = (x⁻¹ * hC.d * x) * x⁻¹ := by rw [h1]
          _ = x⁻¹ * hC.d := by group
      have hv2' : hC.d * v = x * y * x⁻¹ := hv2
      have hyv : y = x⁻¹ * (hC.d * v) * x := by rw [hv2']; group
      rw [hyv]
      calc hC.d * (x⁻¹ * v * x) = hC.d * (x⁻¹ * v) * x := by group
        _ = hC.d * x⁻¹ * v * x := by group
        _ = x⁻¹ * hC.d * v * x := by rw [hcx']
        _ = x⁻¹ * (hC.d * v) * x := by group
  let Y : Subgroup (Equiv.Perm Δ) := (X.subgroupOf NN).map (cosetNormalizerPerm Δ)
  have hYcyc : IsCyclic Y := hU.singer_isCyclic
  have hYodd : Odd (Nat.card Y) := by
    have hYcard : Nat.card Y = Nat.card U - 1 := hU.singer_card
    rw [hYcard, hUn]
    have hp : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by rw [pow_succ, mul_comm]
    rw [hp]
    refine ⟨2 ^ (2 * m) - 1, ?_⟩
    have h1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
    omega
  let ρ : X →* Y :=
    { toFun := fun x =>
        ⟨cosetNormalizerPerm Δ ⟨x, hXN x.2⟩,
          Subgroup.mem_map.mpr ⟨⟨x, hXN x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (cosetNormalizerPerm Δ))
      map_mul' := fun x y =>
        Subtype.ext (map_mul (cosetNormalizerPerm Δ) ⟨x, hXN x.2⟩ ⟨y, hXN y.2⟩) }
  have hρ : Function.Surjective ρ := by
    intro σ
    obtain ⟨x', hx', hx'σ⟩ := Subgroup.mem_map.mp σ.2
    refine ⟨⟨x'.1, Subgroup.mem_subgroupOf.mp hx'⟩, ?_⟩
    apply Subtype.ext
    rw [← hx'σ]
    congr 1
  have htrans : ∀ z ∈ U, ∀ z' ∈ U, z ≠ 1 → z' ≠ 1 → ∃ x ∈ X, x * z * x⁻¹ = z' := by
    intro z1 hz1U z2 hz2U hz11 hz21
    let p1 : Δ := ⟨hC.d * z1, ⟨z1, hz1U, rfl⟩⟩
    let p2 : Δ := ⟨hC.d * z2, ⟨z2, hz2U, rfl⟩⟩
    have hp1 : (p1 : G) ≠ hC.d := by
      intro hc
      apply hz11
      apply mul_left_cancel (a := hC.d)
      have hc' : hC.d * z1 = hC.d := hc
      rw [hc', mul_one]
    have hp2 : (p2 : G) ≠ hC.d := by
      intro hc
      apply hz21
      apply mul_left_cancel (a := hC.d)
      have hc' : hC.d * z2 = hC.d := hc
      rw [hc', mul_one]
    obtain ⟨σ, hσ, -⟩ := hU.singer_regular p1 p2 hp1 hp2
    obtain ⟨x, hx⟩ := hρ σ
    refine ⟨x, x.2, ?_⟩
    have h2 : (cosetNormalizerPerm Δ ⟨x, hXN x.2⟩ : Equiv.Perm Δ) p1 = p2 := by
      change (ρ x : Equiv.Perm Δ) p1 = p2
      rw [hx]; exact hσ
    have happ : (x : G) * (hC.d * z1) * (x : G)⁻¹ = hC.d * z2 := by
      rw [← cosetNormalizerPerm_apply Δ ⟨x, hXN x.2⟩ p1]
      exact congrArg (fun t : Δ => (t : G)) h2
    have hcx : (x : G) * hC.d = hC.d * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hXu x.2)
    have hconv : (x : G) * (hC.d * z1) * (x : G)⁻¹ = hC.d * ((x : G) * z1 * (x : G)⁻¹) := by
      calc (x : G) * (hC.d * z1) * (x : G)⁻¹ = (x : G) * hC.d * z1 * (x : G)⁻¹ := by group
        _ = hC.d * (x : G) * z1 * (x : G)⁻¹ := by rw [hcx]
        _ = hC.d * ((x : G) * z1 * (x : G)⁻¹) := by group
    rw [hconv] at happ
    exact mul_left_cancel happ
  have hker : ∀ x : X, ρ x = 1 → (x : G) ∈ Subgroup.centralizer (U : Set G) ∧
      ∀ v ∈ V, v⁻¹ * ((x : G) * v * (x : G)⁻¹) ∈ U := by
    intro x hxρ
    have hxker : (cosetNormalizerPerm Δ ⟨x, hXN x.2⟩ : Equiv.Perm Δ) = 1 := by
      change (ρ x : Equiv.Perm Δ) = 1
      rw [hxρ]; rfl
    have hxNmem : (⟨x, hXN x.2⟩ : NN) ∈ (cosetNormalizerPerm Δ).ker := by
      rw [MonoidHom.mem_ker]; exact hxker
    rw [cosetNormalizerPerm_ker_eq_entire_centralizer, Subgroup.mem_subgroupOf] at hxNmem
    have hu_mem : hC.d ∈ Δ := ⟨1, U.one_mem, mul_one _⟩
    have hxu : hC.d * (x : G) = (x : G) * hC.d :=
      Subgroup.mem_centralizer_iff.mp hxNmem hC.d hu_mem
    have hxC : (x : G) ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : (hC.d * u) * (x : G) = (x : G) * (hC.d * u) :=
        Subgroup.mem_centralizer_iff.mp hxNmem (hC.d * u) ⟨u, hu, rfl⟩
      have h2 : hC.d * (u * (x : G)) = hC.d * ((x : G) * u) := by
        calc hC.d * (u * (x : G)) = (hC.d * u) * (x : G) := by group
          _ = (x : G) * (hC.d * u) := h1
          _ = ((x : G) * hC.d) * u := by group
          _ = (hC.d * (x : G)) * u := by rw [← hxu]
          _ = hC.d * ((x : G) * u) := by group
      exact mul_left_cancel h2
    refine ⟨hxC, ?_⟩
    intro v hv
    have hxS : (x : G) ∈ (S : Subgroup G) := hSU.symm ▸ hxC
    have hvS : v ∈ (S : Subgroup G) := hVS hv
    have hcomm : (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ U :=
      commutator_mem_of_sq_mem hSq hxS hvS
    have hcv : v * ((x : G) * v * (x : G)⁻¹ * v⁻¹) = ((x : G) * v * (x : G)⁻¹ * v⁻¹) * v :=
      (Subgroup.mem_centralizer_iff.mp (hUc' hvS) _ hcomm).symm
    have heq : v⁻¹ * ((x : G) * v * (x : G)⁻¹) = (x : G) * v * (x : G)⁻¹ * v⁻¹ := by
      calc v⁻¹ * ((x : G) * v * (x : G)⁻¹)
          = v⁻¹ * (((x : G) * v * (x : G)⁻¹ * v⁻¹) * v) := by group
        _ = v⁻¹ * (v * ((x : G) * v * (x : G)⁻¹ * v⁻¹)) := by rw [← hcv]
        _ = (x : G) * v * (x : G)⁻¹ * v⁻¹ := by group
    rw [heq]
    exact hcomm
  have hq : 1 < q := by
    simpa [q] using Nat.one_lt_two_pow (show 2 * m + 1 ≠ 0 by omega)
  have hcommR : IsMulCommutative R :=
    isMulCommutative_of_two_elementary_and_cyclic_image (S := (S : Subgroup G)) (V := V)
      (U := U) (R := R) (A := A) (B := B) (X := X) (u := hC.d) (q := q) (Y := Y)
      hq hVS hUV huS hu2 hUc' hSq hR_eq hUcard hRcard hRI hAB hAiB hA2 hB2 hAcard hBcard hI
      hXV hXU hXu ρ hρ hYcyc hYodd hker htrans
  have hRU : R ≤ U := by
    obtain ⟨R₀, hR₀⟩ := exists_sylow_pResidualOf T
    intro r hr
    have hr' : r ∈ (R₀ : Subgroup Lsub).map Lsub.subtype := by
      rw [hR₀]; exact hr
    obtain ⟨x, hxR₀, hxr⟩ := Subgroup.mem_map.mp hr'
    have hxr' : (x : G) = r := hxr
    have hxcen : x ∈
        CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (R₀ : Subgroup Lsub) := by
      rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter]
      refine ⟨hxR₀, fun t ht => ?_⟩
      refine Subtype.ext ?_
      have htR : (t : G) ∈ R := by
        have ht' : (t : G) ∈ (R₀ : Subgroup Lsub).map Lsub.subtype :=
          Subgroup.mem_map_of_mem _ ht
        rwa [hR₀] at ht'
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val
        (hcommR.is_comm.comm ⟨(t : G), htR⟩ ⟨(x : G), hxr'.symm ▸ hr⟩)
    have hxU := hU.mem_of_mem_sylowCenter hH h3 h5 hR₀ hxcen
    rwa [hxr'] at hxU
  have hcardle : Nat.card R ≤ Nat.card U := Subgroup.card_le_of_le hRU
  have hlt : Nat.card U < Nat.card R := by
    rw [hUcard, hRcard]
    simpa using Nat.pow_lt_pow_right hq (show 1 < 2 by norm_num)
  omega

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
