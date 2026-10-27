module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofLocal
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSp62

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction)
open Item812Res3 (IsMaxPSub)

namespace Item812Res5

theorem card_mulAut_alt9 :
    Nat.card (MulAut (alternatingGroup (Fin 9))) = Nat.card (Equiv.Perm (Fin 9)) :=
  (Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num)))).symm

theorem conj_injective_of_center_eq_bot {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  intro g h hgh
  have hc : h⁻¹ * g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut M => φ x) hgh
    simp only [MulAut.conj_apply] at h1
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = h⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem card_mulAut_sp62 :
    Nat.card (MulAut (projSp 3 (GaloisField 2 1))) = Nat.card (projSp 3 (GaloisField 2 1)) := by
  set M := projSp 3 (GaloisField 2 1)
  set e := Sec4.Item434SmallTwoIII.sp62Equiv
  have hinj := conj_injective_of_center_eq_bot Item812Res3.isYModel_projSp_three_two.1
  have hsurj : Function.Surjective (MulAut.conj : M →* MulAut M) := by
    intro β
    obtain ⟨h, hh⟩ := Sec4.Item434SmallTwoIII.mem_range_conj_H6 (MulAut.congr e β)
    refine ⟨e.symm h, MulEquiv.ext fun x => e.injective ?_⟩
    have h1 := congrArg (fun φ => φ (e x)) hh
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h1]
    simp
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

theorem factorization_card_mulAut {M : Type} [Group M]
    (hM : Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (M ≃* projSp 3 (GaloisField 2 1))) :
    (Nat.card (MulAut M)).factorization 3 = 4 := by
  rcases hM with h9 | h6
  · obtain ⟨e⟩ := h9
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_alt9]
    exact Sec4.Item434AltPerm.factorization_nine
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_sp62,
      Sec21.Item223CensusResProof.card_projSp_three_two,
      show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem factorization_card_of_isYGroup {M : Type} [Group M]
    (hM : Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (M ≃* projSp 3 (GaloisField 2 1))) :
    (Nat.card M).factorization 3 = 4 := by
  rcases Item812Res4.card_of_isYGroup hM with h | h <;> rw [h]
  · rw [show (181440 : ℕ) = 3 ^ 4 * 2240 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]
  · rw [show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev actY (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
  (thetaQuotMulAut Y).comp (compAction Y)

theorem actY_apply_mk (Y : Subgroup G) (w : Subgroup.normalizer (Y : Set G)) (z : Y) :
    actY Y w (z : Y ⧸ aschbacherSolvableCore 3 Y) =
      ((compAction Y w z : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :=
  rfl

theorem commutator_mem_of_actY_eq_one {Y : Subgroup G} {w : Subgroup.normalizer (Y : Set G)}
    (hw : actY Y w = 1) :
    ∀ z ∈ Y, (w : G) * z * (w : G)⁻¹ * z⁻¹ ∈ (aschbacherSolvableCore 3 Y).map Y.subtype := by
  intro z hz
  have h1 := congrArg (fun φ => φ ((⟨z, hz⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y)) hw
  simp only [actY_apply_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  set u : Y := compAction Y w ⟨z, hz⟩ with hu
  have hu' : (u : G) = (w : G) * z * (w : G)⁻¹ := rfl
  have h2 : u * (⟨z, hz⟩ : Y)⁻¹ ∈ aschbacherSolvableCore 3 Y := by
    have h3 := (aschbacherSolvableCore 3 Y).inv_mem h1
    have h4 := (inferInstance : (aschbacherSolvableCore 3 Y).Normal).conj_mem _ h3 ⟨z, hz⟩
    have e : (⟨z, hz⟩ : Y) * (u⁻¹ * ⟨z, hz⟩)⁻¹ * (⟨z, hz⟩ : Y)⁻¹ = u * (⟨z, hz⟩ : Y)⁻¹ := by
      group
    rwa [e] at h4
  refine ⟨_, h2, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hu']

theorem actY_of_mem {Y : Subgroup G} {w : Subgroup.normalizer (Y : Set G)} (hwY : (w : G) ∈ Y) :
    actY Y w = MulAut.conj ((⟨w, hwY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H z =>
    rw [actY_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

theorem card_inf_of_isMaxPSub {H Y Pa : Subgroup G} (hPa : IsMaxPSub 3 Pa H) (hYH : Y ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card (Pa ⊓ Y : Subgroup G) = 3 ^ (Nat.card Y).factorization 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPaH : Pa ≤ H := hPa.1
  let S : Sylow 3 H :=
    { toSubgroup := Pa.subgroupOf H
      isPGroup' := hPa.2.1.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hQ' : IsPGroup 3 (Q.map H.subtype) := hQ.map _
        have hPaQ : Pa ≤ Q.map H.subtype := fun x hx =>
          ⟨⟨x, hPaH hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have heq := hPa.2.2 _ hQ' hPaQ (Subgroup.map_subtype_le Q)
        ext x
        rw [Subgroup.mem_subgroupOf, ← heq]
        exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => by rwa [Subtype.ext hyx] at hy⟩ }
  have hN : (Y.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hHN
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S (N := Y.subgroupOf H)
  have h1 : Nat.card (((S : Subgroup H) ⊓ Y.subgroupOf H : Subgroup H)) = Nat.card P := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (S : Subgroup H) ⊓ Y.subgroupOf H ≤ Y.subgroupOf H)).toEquiv, ← hP]
  have h2 : ((S : Subgroup H) ⊓ Y.subgroupOf H : Subgroup H) = (Pa ⊓ Y).subgroupOf H := by
    ext x
    simp [S, Subgroup.mem_subgroupOf]
  have h3 : Nat.card ((Pa ⊓ Y).subgroupOf H) = Nat.card (Pa ⊓ Y : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPaH)).toEquiv
  have h4 : Nat.card (Y.subgroupOf H) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  rw [← h3, ← h2, h1, Sylow.card_eq_multiplicity, h4]

end Item812Res5


section Final


open Item812Res5

namespace Item812Res5

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_of_mem_pa {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) {Pa : Subgroup G}
    (hPa : IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G))) {p : G} (hp : p ∈ Pa) :
    ∃ y ∈ Pa ⊓ Y, ∃ hpN : p * y⁻¹ ∈ Subgroup.normalizer (Y : Set G),
      actY Y ⟨p * y⁻¹, hpN⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.centralizer ({a} : Set G) with hH
  set NY := Subgroup.normalizer (Y : Set G) with hNYdef
  have hNY := h.normalizer_zpowers_le_normalizer_Y
  have hHN : H ≤ NY := fun x hx =>
    hNY (Item812Res2.mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp hx))
  have hYH : Y ≤ H := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hPaH : Pa ≤ H := hPa.1
  have hPaN : Pa ≤ NY := hPaH.trans hHN
  have hYq : Item812Res4.IsYQuot Y := h.item89_Y
  have hYfact : (Nat.card Y).factorization 3 = 4 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 Y)
    have hq0 : Nat.card (Y ⧸ aschbacherSolvableCore 3 Y) ≠ 0 := Nat.card_pos.ne'
    have hθ0 : Nat.card (aschbacherSolvableCore 3 Y) ≠ 0 := Nat.card_pos.ne'
    rw [hc, Nat.factorization_mul hq0 hθ0, Finsupp.add_apply,
      factorization_card_of_isYGroup hYq,
      Nat.factorization_eq_zero_of_not_dvd (Item812Res4.not_dvd_card_core Y)]
  have hcardPY : Nat.card (Pa ⊓ Y : Subgroup G) = 81 := by
    rw [card_inf_of_isMaxPSub hPa hYH hHN, hYfact]
    norm_num
  have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
    rcases hYq with h9 | h6
    · obtain ⟨e⟩ := h9
      rw [← Subgroup.map_center_eq e.symm, Item812Res3.isYModel_alternatingGroup_nine.1,
        Subgroup.map_bot]
    · obtain ⟨e⟩ := h6
      rw [← Subgroup.map_center_eq e.symm, Item812Res3.isYModel_projSp_three_two.1,
        Subgroup.map_bot]
  set Ψ := actY Y with hΨ
  set PaN := Pa.subgroupOf NY with hPaNdef
  set PYN := (Pa ⊓ Y).subgroupOf NY with hPYNdef
  have hle : PYN.map Ψ ≤ PaN.map Ψ := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have hPaNp : IsPGroup 3 PaN := hPa.2.1.comap_subtype
  have : Finite (MulAut (Y ⧸ aschbacherSolvableCore 3 Y)) :=
    Finite.of_injective (fun f : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) =>
      (f : (Y ⧸ aschbacherSolvableCore 3 Y) → (Y ⧸ aschbacherSolvableCore 3 Y)))
      (fun f g hfg => MulEquiv.ext (congrFun hfg))
  have hI2 : Nat.card (PaN.map Ψ) ≤ 81 := by
    have h1 := Sec4.Item434AltPerm.card_le_of_isPGroup (hPaNp.map Ψ)
    rw [factorization_card_mulAut hYq] at h1
    simpa using h1
  have hinj : Set.InjOn Ψ PYN := by
    intro u hu v hv huv
    have hw : u⁻¹ * v ∈ PYN := PYN.mul_mem (PYN.inv_mem hu) hv
    have hwY : ((u⁻¹ * v : NY) : G) ∈ Y := (Subgroup.mem_subgroupOf.mp hw).2
    have hwPa : ((u⁻¹ * v : NY) : G) ∈ Pa := (Subgroup.mem_subgroupOf.mp hw).1
    have h1 : Ψ (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, huv, inv_mul_cancel]
    rw [hΨ, actY_of_mem hwY] at h1
    set g : Y ⧸ aschbacherSolvableCore 3 Y := ((⟨_, hwY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y)
      with hg
    have h2 : g ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h3 := congrArg (fun φ => φ x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hZ, Subgroup.mem_bot, hg, QuotientGroup.eq_one_iff] at h2
    obtain ⟨k, hk⟩ := hPa.2.1 ⟨_, hwPa⟩
    have hk' : (⟨_, hwY⟩ : Y) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h3 := KFacts.eq_one_of_pow_three_pow_eq_one (Item812Res4.not_dvd_card_core Y) h2 hk'
    have h4 : u⁻¹ * v = 1 := Subtype.ext (by simpa using congrArg Subtype.val h3)
    exact inv_mul_eq_one.mp h4
  have hI1 : Nat.card (PYN.map Ψ) = 81 := by
    rw [Item812Res4.card_map_of_injOn Ψ hinj, hPYNdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPaN)).toEquiv, hcardPY]
  have heq : PYN.map Ψ = PaN.map Ψ := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hpmem : Ψ ⟨p, hPaN hp⟩ ∈ PaN.map Ψ :=
    ⟨⟨p, hPaN hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  rw [← heq] at hpmem
  obtain ⟨y', hy', hy'e⟩ := hpmem
  refine ⟨y', Subgroup.mem_subgroupOf.mp hy', NY.mul_mem (hPaN hp) (NY.inv_mem y'.2), ?_⟩
  have e : (⟨p * (y' : G)⁻¹, NY.mul_mem (hPaN hp) (NY.inv_mem y'.2)⟩ : NY) =
      ⟨p, hPaN hp⟩ * y'⁻¹ := rfl
  rw [e, map_mul, map_inv, hy'e, mul_inv_cancel]

end Item812Res5

@[expose] def Fin812PaExp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      ∀ w ∈ Pa, (∀ z ∈ Y, w * z * w⁻¹ * z⁻¹ ∈ (aschbacherSolvableCore 3 Y).map Y.subtype) →
        w ^ 3 = 1

theorem fin812PaSplit_of_exp (hE : Fin812PaExp) : Fin812PaSplit := by
  intro G _ _ A c L a b X Y n h Pa hPa hAPa
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a haA
  have h3 := h.toTheoremFourHyp.localRank_three.le
  refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr (hAPa haA)) inf_le_left) ?_
  intro p hp
  obtain ⟨y, hyPY, hpN, hact⟩ := exists_mem_inf_of_mem_pa h hPa hp
  have hwPa : p * y⁻¹ ∈ Pa := Pa.mul_mem hp (Pa.inv_mem hyPY.1)
  have hcomm := commutator_mem_of_actY_eq_one hact
  have hw3 : (p * y⁻¹) ^ 3 = 1 := hE G A c L a b X Y n h Pa hPa hAPa _ hwPa hcomm
  have hwa : p * y⁻¹ * a = a * (p * y⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPa.1 hwPa)
  have hwz : p * y⁻¹ ∈ Subgroup.zpowers a := by
    rcases h.item89_Y with h9 | h6
    · obtain ⟨e⟩ := h9
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1
        h.mem_thetaComponentsAt_Y Item812Res3.isYModel_alternatingGroup_nine e hwa hw3 hpN hact
    · obtain ⟨e⟩ := h6
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1
        h.mem_thetaComponentsAt_Y Item812Res3.isYModel_projSp_three_two e hwa hw3 hpN hact
  have e : p = p * y⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem_sup hwz hyPY

end Final

end CFSG.RankThree.PartTwo.Sec8
