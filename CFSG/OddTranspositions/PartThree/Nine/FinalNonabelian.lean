module

public import CFSG.OddTranspositions.PartThree.Nine.FinalCentral
public import CFSG.OddTranspositions.PartThree.Nine.FinalUnitary
public import CFSG.LargeExtraspecial.S111SHCor3

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem conj_mem_D2 (hU : DeltaSetup hC T S U) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) (g : G) :
    g * hC.d * g⁻¹ ∈ D ∧ g * (hC.d * z) * g⁻¹ ∈ D ∧
      g * hC.d * g⁻¹ ≠ g * (hC.d * z) * g⁻¹ ∧
      Commute (g * hC.d * g⁻¹) (g * (hC.d * z) * g⁻¹) ∧
      g * hC.d * g⁻¹ * (g * (hC.d * z) * g⁻¹) = g * z * g⁻¹ := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huzD : hC.d * z ∈ D := by
    have h : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hzU, rfl⟩
    exact h.2
  have hus : Commute hC.d z :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hzU)))).symm
  refine ⟨hC.setup.conj_mem g hC.hd, hC.setup.conj_mem g huzD, fun h => hz1 ?_,
    (Commute.conj_iff g).mpr ((Commute.refl _).mul_right hus), ?_⟩
  · have h' : hC.d = hC.d * z := by simpa using h
    simpa using h'.symm
  · calc g * hC.d * g⁻¹ * (g * (hC.d * z) * g⁻¹) = g * (hC.d * hC.d) * z * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hu2, mul_one]

theorem mem_regularCore_of_mem_wclSet (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {y : G}
    (hy : y ∈ CFSG.LargeExtraspecial.S11.wclSet z) : y ∈ Q := by
  obtain ⟨g, rfl, hyz⟩ := hy
  obtain ⟨hd, he, hne, hc, hprod⟩ := hU.conj_mem_D2 hzU hz1 g
  have hyN : g * z * g⁻¹ ∈ Subgroup.normalizer ((S : Set G) ∩ D) := by
    rw [hU.sylow_inter]
    exact hU.centralizer_le_normalizer_delta hH h3 h5 hzU hz1
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have h := h7 _ hd _ he hne hc (hprod ▸ hyN)
  rwa [hprod] at h

omit [Finite G] in
theorem mul_conj_mem_of_mem_normalizer {u x : G} (hu2 : u * u = 1)
    (hxN : x ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    u * (x * u * x⁻¹) ∈ U := by
  obtain ⟨b, hb, hbx⟩ := (hxN u).mp ⟨1, U.one_mem, mul_one _⟩
  rw [← hbx]
  show u * (u * b) ∈ U
  rw [← mul_assoc, hu2, one_mul]
  exact hb

theorem mem_sylow_map_of_mem_centralizer (h5 : Conclusion9_5 D hC T S)
    (hU : DeltaSetup hC T S U) {x : G} (hxU : x ∈ Subgroup.centralizer (U : Set G))
    (hxu : x * hC.d * x⁻¹ = hC.d) :
    x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  rw [← h5.1, hU.sylow_inter, Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  have hxv : v * x = x * v := Subgroup.mem_centralizer_iff.mp hxU v hv
  have hxu' : hC.d * x = x * hC.d := by
    calc hC.d * x = x * hC.d * x⁻¹ * x := by rw [hxu]
      _ = x * hC.d := by group
  calc hC.d * v * x = hC.d * (x * v) := by rw [mul_assoc, hxv]
    _ = x * (hC.d * v) := by rw [← mul_assoc, hxu', mul_assoc]

theorem eq_one_of_conj_mem_sylow_map (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {z : G} (hzU : z ∈ U) {g : G}
    (he : g * z * g⁻¹ ∉ U) {a : G} (haU : a ∈ U)
    (haT : g * a * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    a = 1 := by
  classical
  by_contra ha1
  have := hU.isElementaryAbelian
  set Δ := (fun v : G => hC.d * v) '' (U : Set G) with hΔ
  have hcent : ∀ v ∈ Δ, Commute v (g * a * g⁻¹) := by
    intro v hv
    rw [← h5.1, hU.sylow_inter] at haT
    exact Subgroup.mem_centralizer_iff.mp haT v hv
  have hsub : ∀ v ∈ Δ, g⁻¹ * v * g ∈ Δ := by
    intro v hv
    rw [hU.mem_delta_iff_commute hH h3 h5 haU ha1]
    have hvD : v ∈ D := by
      rw [hΔ, ← hU.sylow_inter] at hv
      exact hv.2
    refine ⟨by simpa using hC.setup.conj_mem g⁻¹ hvD, ?_⟩
    have h := (Commute.conj_iff g⁻¹).mpr (hcent v hv)
    simpa [mul_assoc] using h
  let f : Δ → Δ := fun v => ⟨g⁻¹ * v * g, hsub v v.2⟩
  have hf : Function.Injective f := fun v w h => by
    have h' : g⁻¹ * (v : G) * g = g⁻¹ * w * g := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  have hfs := Finite.injective_iff_surjective.mp hf
  have hgN : g ∈ Subgroup.normalizer Δ := by
    intro x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := hfs ⟨x, hx⟩
      have hv' : g⁻¹ * (v : G) * g = x := congrArg Subtype.val hv
      rw [← hv']
      simp [mul_assoc]
    · intro hx
      simpa [mul_assoc] using hsub _ hx
  exact he (((hU.affine h3).1 hgN z).mp hzU)

theorem conj_mem_regularCore (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z) {a : G}
    (haU : a ∈ U) : g * a * g⁻¹ ∈ Q := by
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact Q.one_mem
  have hQC := hU.regularCore_eq_centralizer hH h3 h5 hQ
  have hinv : g⁻¹ * z * g ∈ CFSG.LargeExtraspecial.S11.wclSet z := by
    refine ⟨g⁻¹, by rw [inv_inv], ?_⟩
    have h := (Commute.conj_iff g⁻¹).mpr hgz
    simp only [inv_inv] at h
    have h' : Commute z (g⁻¹ * z * g) := by simpa [mul_assoc] using h
    exact h'.eq.symm
  have hzQ := hU.mem_regularCore_of_mem_wclSet hH h3 h5 h7 hzU hz1 hinv
  rw [hQC] at hzQ
  have hza : Commute (g * a * g⁻¹) z := by
    have h := Subgroup.mem_centralizer_iff.mp hzQ a haU
    have h' : Commute a (g⁻¹ * z * g) := h
    have h'' := (Commute.conj_iff g).mpr h'
    simpa [mul_assoc] using h''
  obtain ⟨hd, he, hne, hc, hprod⟩ := hU.conj_mem_D2 haU ha1 g
  have hN : g * a * g⁻¹ ∈ Subgroup.normalizer ((S : Set G) ∩ D) := by
    rw [hU.sylow_inter]
    exact hU.centralizer_le_normalizer_delta hH h3 h5 hzU hz1
      (Subgroup.mem_centralizer_singleton_iff.mpr hza.eq)
  have h := h7 _ hd _ he hne hc (hprod ▸ hN)
  rwa [hprod] at h

theorem exists_eq_conj_mul_of_mem_regularCore (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {x : G} (hxQ : x ∈ Q) :
    ∃ a ∈ U, ∃ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      x = g * a * g⁻¹ * t := by
  classical
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hQC := hU.regularCore_eq_centralizer hH h3 h5 hQ
  have hQN : Q ≤ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ hQ.1
  have hEQ : ∀ a ∈ U, g * a * g⁻¹ ∈ Q := fun a ha =>
    hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz ha
  let β : U → U := fun a => ⟨hC.d * ((g * a * g⁻¹) * hC.d * (g * a * g⁻¹)⁻¹),
    mul_conj_mem_of_mem_normalizer hu2 (hQN (hEQ a a.2))⟩
  have hβ : Function.Injective β := by
    intro a a' h
    have h' : (g * a * g⁻¹) * hC.d * (g * a * g⁻¹)⁻¹ =
        (g * a' * g⁻¹) * hC.d * (g * a' * g⁻¹)⁻¹ := by
      have h0 := congrArg (fun y : U => hC.d * (y : G)) h
      simpa only [β, ← mul_assoc, hu2, one_mul] using h0
    set y := (g * a * g⁻¹)⁻¹ * (g * a' * g⁻¹) with hy
    have hyQ : y ∈ Q := Q.mul_mem (Q.inv_mem (hEQ a a.2)) (hEQ a' a'.2)
    have hyu : y * hC.d * y⁻¹ = hC.d := by
      rw [hy]
      calc (g * a * g⁻¹)⁻¹ * (g * a' * g⁻¹) * hC.d * ((g * a * g⁻¹)⁻¹ * (g * a' * g⁻¹))⁻¹
          = (g * a * g⁻¹)⁻¹ * ((g * a' * g⁻¹) * hC.d * (g * a' * g⁻¹)⁻¹) * (g * a * g⁻¹) := by
            group
        _ = hC.d := by rw [← h']; group
    have hyT := hU.mem_sylow_map_of_mem_centralizer h5 (hQC ▸ hyQ) hyu
    have hyeq : y = g * ((a : G)⁻¹ * a') * g⁻¹ := by rw [hy]; group
    rw [hyeq] at hyT
    have h1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he
      (U.mul_mem (U.inv_mem a.2) a'.2) hyT
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hβs := Finite.injective_iff_surjective.mp hβ
  obtain ⟨a, ha⟩ := hβs ⟨hC.d * (x * hC.d * x⁻¹),
    mul_conj_mem_of_mem_normalizer hu2 (hQN hxQ)⟩
  have ha' : (g * a * g⁻¹) * hC.d * (g * a * g⁻¹)⁻¹ = x * hC.d * x⁻¹ := by
    have h0 := congrArg (fun y : U => hC.d * (y : G)) ha
    simpa only [β, ← mul_assoc, hu2, one_mul] using h0
  set t := (g * a * g⁻¹)⁻¹ * x with ht
  have htQ : t ∈ Q := Q.mul_mem (Q.inv_mem (hEQ a a.2)) hxQ
  have htu : t * hC.d * t⁻¹ = hC.d := by
    rw [ht]
    calc (g * a * g⁻¹)⁻¹ * x * hC.d * ((g * a * g⁻¹)⁻¹ * x)⁻¹
        = (g * a * g⁻¹)⁻¹ * (x * hC.d * x⁻¹) * (g * a * g⁻¹) := by group
      _ = hC.d := by rw [← ha']; group
  refine ⟨a, a.2, t, hU.mem_sylow_map_of_mem_centralizer h5 (hQC ▸ htQ) htu, ?_⟩
  rw [ht]
  group

theorem false_of_wcl_not_commutative_of_sylow_map (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    (hTU : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      t ∈ U ∨ hC.d * t ∈ U)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hW : ¬ IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)) : False := by
  classical
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hQC := hU.regularCore_eq_centralizer hH h3 h5 hQ
  have hQN : Q ≤ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ hQ.1
  have hUc : ∀ x ∈ U, ∀ y ∈ U, Commute x y := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have huU : ∀ x ∈ U, Commute hC.d x := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hx)))).symm
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨e, he, heU⟩ : ∃ e ∈ CFSG.LargeExtraspecial.S11.wclSet z, e ∉ U := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hW
    have hle : CFSG.LargeExtraspecial.S11.wcl z ≤ U := (Subgroup.closure_le U).mpr hall
    exact ⟨⟨fun a b => Subtype.ext (hUc _ (hle a.2) _ (hle b.2)).eq⟩⟩
  obtain ⟨g, rfl, hgz⟩ := he
  have hgz' : Commute (g * z * g⁻¹) z := hgz
  have hEQ : ∀ a ∈ U, g * a * g⁻¹ ∈ Q := fun a ha =>
    hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz' ha
  have hEC : ∀ a ∈ U, g * a * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := fun a ha =>
    hQC ▸ hEQ a ha
  have hgen : ∀ y ∈ CFSG.LargeExtraspecial.S11.wclSet z, ∃ a ∈ U, ∃ c ∈ U,
      y = g * a * g⁻¹ * c := by
    intro y hy
    have hyQ := hU.mem_regularCore_of_mem_wclSet hH h3 h5 h7 hzU hz1 hy
    obtain ⟨a, haU, t, htT, hyt⟩ :=
      hU.exists_eq_conj_mul_of_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz' heU hyQ
    rcases hTU t htT with htU | hutU
    · exact ⟨a, haU, t, htU, hyt⟩
    · exfalso
      obtain ⟨m, rfl, -⟩ := hy
      have hy2 : m * z * m⁻¹ * (m * z * m⁻¹) = 1 := by
        calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
          _ = 1 := by rw [hsq z hzU, mul_one, mul_inv_cancel]
      set c := hC.d * t with hc
      have htc : t = hC.d * c := by rw [hc, ← mul_assoc, hu2, one_mul]
      set A := g * a * g⁻¹ with hA
      have hAc : Commute A c := (Subgroup.mem_centralizer_iff.mp (hEC a haU) c hutU).symm
      have huc : Commute hC.d c := huU c hutU
      have hA2 : A * A = 1 := by
        rw [hA]
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [hsq a haU, mul_one, mul_inv_cancel]
      have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
      have hbU := mul_conj_mem_of_mem_normalizer hu2 (hQN (hEQ a haU))
      set b := hC.d * (A * hC.d * A⁻¹) with hb
      have hAub : A * hC.d * A⁻¹ = hC.d * b := by rw [hb, ← mul_assoc, hu2, one_mul]
      have hy2' : m * z * m⁻¹ * (m * z * m⁻¹) = b := by
        rw [hyt, htc]
        calc A * (hC.d * c) * (A * (hC.d * c)) = A * hC.d * (c * A) * hC.d * c := by group
          _ = A * hC.d * A * (c * hC.d) * c := by rw [← hAc.eq]; group
          _ = A * hC.d * A * hC.d * (c * c) := by rw [← huc.eq]; group
          _ = A * hC.d * A⁻¹ * hC.d := by rw [hsq c hutU, mul_one, hAinv]
          _ = hC.d * b * hC.d := by rw [hAub]
          _ = b := by rw [mul_assoc, ← (huU b hbU).eq, ← mul_assoc, hu2, one_mul]
      have hb1 : b = 1 := hy2'.symm.trans hy2
      have hAu : A * hC.d * A⁻¹ = hC.d := by rw [hAub, hb1, mul_one]
      have hAT := hU.mem_sylow_map_of_mem_centralizer h5 (hEC a haU) hAu
      have ha1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU heU haU hAT
      have hyD : m * z * m⁻¹ ∈ D := by
        rw [hyt, hA, ha1, mul_one, mul_inv_cancel, one_mul, htc]
        have h : hC.d * c ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨c, hutU, rfl⟩
        exact h.2
      obtain ⟨hd, he, hne, hcm, hprod⟩ := hU.conj_mem_D2 hzU hz1 m
      exact mul_not_mem_of_commute hH h3 hd he hne hcm (hprod ▸ hyD)
  apply hW
  refine Subgroup.isMulCommutative_closure ?_
  intro y₁ hy₁ y₂ hy₂ _
  obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := hgen y₁ hy₁
  obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := hgen y₂ hy₂
  have hAA : Commute (g * a₁ * g⁻¹) (g * a₂ * g⁻¹) := (Commute.conj_iff g).mpr (hUc _ ha₁ _ ha₂)
  have h12 : Commute (g * a₁ * g⁻¹) c₂ :=
    (Subgroup.mem_centralizer_iff.mp (hEC a₁ ha₁) c₂ hc₂).symm
  have h21 : Commute c₁ (g * a₂ * g⁻¹) := Subgroup.mem_centralizer_iff.mp (hEC a₂ ha₂) c₁ hc₁
  exact (hAA.mul_right h12).mul_left (h21.mul_right (hUc _ hc₁ _ hc₂))

theorem mem_or_mul_mem_of_psl2 (h3 : Conclusion9_3 D hC) (h5 : Conclusion9_5 D hC T S)
    (hU : DeltaSetup hC T S U) {n : ℕ} (hn : 1 ≤ n)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model n)
    (hUn : Nat.card U = 2 ^ n) :
    ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      t ∈ U ∨ hC.d * t ∈ U := by
  classical
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huT : hC.d ∈ TG := d_mem_sylow_map hC h3 T
  have hsub : (U : Set G) ∪ (fun v => hC.d * v) '' (U : Set G) ⊆ (TG : Set G) := by
    rintro x (hx | ⟨v, hv, rfl⟩)
    · exact hU.le_sylow_map hx
    · exact TG.mul_mem huT (hU.le_sylow_map hv)
  have hdisj : Disjoint (U : Set G) ((fun v => hC.d * v) '' (U : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨v, hv, rfl⟩
    apply hU.d_not_mem h3
    have : hC.d = hC.d * v * v⁻¹ := by group
    rw [this]
    exact U.mul_mem hx (U.inv_mem hv)
  have hcard : ((U : Set G) ∪ (fun v => hC.d * v) '' (U : Set G)).ncard = 2 * 2 ^ n := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h), ← Nat.card_coe_set_eq]
    change Nat.card U + Nat.card U = _
    omega
  have hT := card_sylow_map_le_of_psl2 h3 h5 hU hn eH
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [hcard, ← Nat.card_coe_set_eq]; exact hT) (Set.toFinite _)
  intro t ht
  have ht' : t ∈ (U : Set G) ∪ (fun v => hC.d * v) '' (U : Set G) := heq ▸ ht
  rcases ht' with htU | ⟨v, hv, rfl⟩
  · exact Or.inl htU
  · right
    change hC.d * (hC.d * v) ∈ U
    rw [← mul_assoc, hu2, one_mul]
    exact hv

theorem false_of_wcl_not_commutative_of_psl2 (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {n : ℕ} (hn : 1 ≤ n)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model n)
    (hUn : Nat.card U = 2 ^ n) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hW : ¬ IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)) : False :=
  hU.false_of_wcl_not_commutative_of_sylow_map hH h3 h5 hQ h7
    (hU.mem_or_mul_mem_of_psl2 h3 h5 hn eH hUn) hzU hz1 hW

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
