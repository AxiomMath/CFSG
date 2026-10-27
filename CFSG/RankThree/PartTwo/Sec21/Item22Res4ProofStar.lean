module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofConfig

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped Pointwise

namespace Item22Res4Proof

theorem signedMat_pow_twelve : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) → (KFacts.KP14.signedMat π s) ^ 12 = 1 := by
  decide +kernel

theorem monomial_pow_twelve {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ KFacts.KP14.monomial) :
    g ^ 12 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact KFacts.KP14.forall_mem_monomial (P := fun M => M ^ 12 = 1) signedMat_pow_twelve hg)

theorem exists_conj_of_card_eq {G : Type*} [Group G] [Finite G] {H D D' : Subgroup G}
    (hD : D ≤ H) (hD' : D' ≤ H) (hD3 : IsPGroup 3 D) (hcard : Nat.card D' = Nat.card D)
    (hidx : ¬ 3 ∣ D.relIndex H) : ∃ h ∈ H, D.map (MulAut.conj h).toMonoidHom = D' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := D.subgroupOf H
  set Q := D'.subgroupOf H
  have hP3 : IsPGroup 3 P := hD3.comap_of_injective H.subtype H.subtype_injective
  have hcP : Nat.card P = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  have hcQ : Nat.card Q = Nat.card D' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD').toEquiv
  have hQ3 : IsPGroup 3 Q := by
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [hcQ, hcard, ← hcP, hk])
  have hidxP : ¬ 3 ∣ P.index := hidx
  have hidxQ : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index P
    have h2 := Subgroup.card_mul_index Q
    have : Q.index = P.index := by
      have hpos : 0 < Nat.card P := Nat.card_pos
      rw [hcQ, hcard, ← hcP] at h2
      exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)
    rwa [this]
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (hP3.toSylow hidxP) (hQ3.toSylow hidxQ)
  refine ⟨h, h.2, ?_⟩
  have hh' : MulAut.conj h • P = Q := by
    have := congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hh
    simpa [Sylow.coe_subgroup_smul] using this
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwP : (⟨w, hD hw⟩ : H) ∈ P := hw
    have h1 : MulAut.conj h • (⟨w, hD hw⟩ : H) ∈ MulAut.conj h • P :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hwP
    rw [hh'] at h1
    exact h1
  · intro hz
    have hzQ : (⟨z, hD' hz⟩ : H) ∈ Q := hz
    rw [← hh', Subgroup.mem_smul_pointwise_iff_exists] at hzQ
    obtain ⟨w, hw, hwz⟩ := hzQ
    exact ⟨w, hw, congrArg Subtype.val hwz⟩

section Decomp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_of_elemAbelian {A : Subgroup G} (hA : IsElemAbelian 3 A) : IsPGroup 3 A :=
  CFSG.Open.IsElemAbelian.isPGroup hA

theorem conj_injective_of_center_eq_bot {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have : z ∈ Subgroup.center Y := by rw [← Sec4.ker_conj_eq_center]; exact hz
  rwa [hZ, Subgroup.mem_bot] at this

theorem exists_mem_conj_eq_thetaAct {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) (a : A) :
    ∃ d : X, (d : G) ∈ A ∧
      MulAut.conj (d : X ⧸ aschbacherSolvableCore 3 X) = Sec4.thetaAct hAN a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hAmax.prop
  have hEinn := Sec4.range_thetaAct_le_inner hAN hin
  have hinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨yb, hyb⟩ := hEinn ⟨a, rfl⟩
  have hyb3 : yb ^ 3 = 1 := by
    apply hinj
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 a a.2)
    rw [map_pow, hyb, ← map_pow, ha3, map_one, map_one]
  have hfix : ∀ b : A, Item223KFactsProof.barAct hAN b yb = yb := by
    intro b
    obtain ⟨zb, hzb⟩ := hEinn ⟨b, rfl⟩
    change Sec4.thetaAct hAN b yb = yb
    have hc : MulAut.conj (zb * yb) = MulAut.conj (yb * zb) := by
      rw [map_mul, map_mul, hyb, hzb, ← map_mul, ← map_mul, hAe.1.is_comm.comm b a]
    have h1 := hinj hc
    rw [← hzb, MulAut.conj_apply, h1, mul_inv_cancel_right]
  obtain ⟨y, hy, hyC⟩ := Item223KFactsProof.exists_lift_of_fixed hAN
    (isPGroup_of_elemAbelian hAe) yb hfix
  set N := Nat.card (aschbacherSolvableCore 3 X) with hN
  have hN3 : ¬ 3 ∣ N := three_not_dvd_card_aschbacherSolvableCore
  have hN1 : N ^ 2 % 3 = 1 := by
    have : N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have hy3 : y ^ 3 ∈ aschbacherSolvableCore 3 X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy, hyb3]
  refine ⟨y ^ (N ^ 2), ?_, ?_⟩
  · refine Sec4.mem_of_maximal_of_commute hAmax ?_ ?_
    · have h1 : (⟨y ^ 3, hy3⟩ : aschbacherSolvableCore 3 X) ^ N = 1 := pow_card_eq_one'
      have h2 : ((y : G) ^ 3) ^ N = 1 := by
        have := congrArg (fun t : aschbacherSolvableCore 3 X => ((t : X) : G)) h1
        simpa using this
      rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, sq, pow_mul, h2, one_pow]
    · intro b hb
      have hcomm : Commute b (y : G) := Subgroup.mem_centralizer_iff.mp hyC b hb
      rw [Subgroup.coe_pow]
      exact (hcomm.pow_right _).eq
  · rw [QuotientGroup.mk_pow, hy, ← Nat.div_add_mod (N ^ 2) 3, pow_add, pow_mul, hyb3, one_pow,
      one_mul, hN1, pow_one, hyb]

theorem exists_mul_eq {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) {a : G} (ha : a ∈ A) :
    ∃ d ∈ A ⊓ X, ∃ c ∈ A ⊓ Sec4.thetaQuotCentralizer X, a = d * c := by
  obtain ⟨d, hdA, hd⟩ := exists_mem_conj_eq_thetaAct hAmax hAN hin hZ ⟨a, ha⟩
  refine ⟨d, ⟨hdA, d.2⟩, (d : G)⁻¹ * a, ⟨A.mul_mem (A.inv_mem hdA) ha, ?_⟩, by group⟩
  have hdN : (d : G) ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer d.2
  have hN : (d : G)⁻¹ * a ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hdN) (hAN ha)
  refine ⟨⟨(d : G)⁻¹ * a, hN⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
  have h1 : (⟨(d : G)⁻¹ * a, hN⟩ : Subgroup.normalizer (X : Set G)) =
      (⟨d, hdN⟩)⁻¹ * ⟨a, hAN ha⟩ := rfl
  rw [h1, map_mul, map_mul, map_inv, map_inv]
  have h2 : Sec4.thetaQuotMulAut X (X.normalizerMonoidHom ⟨a, hAN ha⟩) =
      Sec4.thetaAct hAN ⟨a, ha⟩ := rfl
  have h3 : Sec4.thetaQuotMulAut X (X.normalizerMonoidHom ⟨d, hdN⟩) =
      MulAut.conj (d : X ⧸ aschbacherSolvableCore 3 X) := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
  rw [h2, h3, hd, inv_mul_cancel]

end Decomp

section Lift

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_relIndex {Q : Type*} [Group Q] {D H : Subgroup G} (hDH : D ≤ H)
    (f : G →* Q) (hker : ¬ 3 ∣ Nat.card (H ⊓ f.ker : Subgroup G)) (hinj : D ⊓ f.ker = ⊥)
    (hmap : H.map f = D.map f) : ¬ 3 ∣ D.relIndex H := by
  set fH := f.comp H.subtype with hfH
  have h1 : Nat.card fH.ker * Nat.card fH.range = Nat.card H := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hk : Nat.card fH.ker = Nat.card (H ⊓ f.ker : Subgroup G) := by
    have hker' : fH.ker = (f.ker ⊓ H).subgroupOf H := by
      ext x
      simp [hfH, Subgroup.mem_subgroupOf]
    rw [hker', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : f.ker ⊓ H ≤ H)).toEquiv,
      inf_comm]
  have hr : Nat.card fH.range = Nat.card D := by
    have hinjD : Function.Injective (f.comp D.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have : (x : G) ∈ D ⊓ f.ker := ⟨x.2, hx⟩
      rw [hinj, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have h2 : fH.range = (f.comp D.subtype).range := by
      rw [hfH, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
        Subgroup.range_subtype, hmap]
    rw [h2]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjD).toEquiv).symm
  have h3 := Subgroup.relIndex_mul_card (H := D) (K := H)
  rw [inf_eq_left.mpr hDH] at h3
  rw [hk, hr] at h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h4 : D.relIndex H = Nat.card (H ⊓ f.ker : Subgroup G) :=
    Nat.eq_of_mul_eq_mul_right hpos (h3.trans h1.symm)
  rw [h4]
  exact hker

noncomputable abbrev imgInf (X A : Subgroup G) : Subgroup (X ⧸ aschbacherSolvableCore 3 X) :=
  ((A ⊓ X).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 X))

theorem exists_normalizer_lift {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥)
    {g : X ⧸ aschbacherSolvableCore 3 X} (hg : ∀ e ∈ imgInf X A, g * e * g⁻¹ ∈ imgInf X A) :
    ∃ x : X, (x : G) ∈ Subgroup.normalizer (A : Set G) ∧
      (x : X ⧸ aschbacherSolvableCore 3 X) = g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hAmax.prop
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hθn : (aschbacherSolvableCore 3 X).Normal := inferInstance
  set C₀ : Subgroup G := A ⊓ Sec4.thetaQuotCentralizer X with hC₀
  set D : Subgroup G := A ⊓ X with hD
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hT
  have hTX : T ≤ X := Subgroup.map_subtype_le _
  have hC₀N : C₀ ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hAN
  have hC₀3 : IsPGroup 3 C₀ := (isPGroup_of_elemAbelian hAe).to_le inf_le_left
  have hD3 : IsPGroup 3 D := (isPGroup_of_elemAbelian hAe).to_le inf_le_left
  have hfix : ∀ c : C₀, Item223KFactsProof.barAct hC₀N c g = g := by
    intro c
    have h1 : Item223KFactsProof.barAct hC₀N c = 1 :=
      (Item223CensusProof.mem_thetaQuotCentralizer_iff_of_mem (hC₀N c.2)).mp c.2.2
    rw [h1, MulAut.one_apply]
  obtain ⟨y₁, hy₁, hy₁C⟩ := Item223KFactsProof.exists_lift_of_fixed hC₀N hC₀3 g hfix
  have hXT : X ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨t', ht', rfl⟩
      refine ⟨⟨x, hx⟩ * t' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
      exact hθn.conj_mem _ ht' _
    · rintro ⟨t', ht', ht'e⟩
      refine ⟨⟨x, hx⟩⁻¹ * t' * ⟨x, hx⟩, ?_, ?_⟩
      · have := hθn.conj_mem _ ht' (⟨x, hx⟩⁻¹)
        simpa using this
      · have h1 : (t' : G) = x * t * x⁻¹ := ht'e
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, h1]
        group
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := inf_le_right.trans hXT
  set H : Subgroup G := (D ⊔ T) ⊓ Subgroup.centralizer (C₀ : Set G) with hH
  have hDC : D ≤ Subgroup.centralizer (C₀ : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun c hc => hAc c hc.1 d hd.1
  have hDH : D ≤ H := le_inf le_sup_left hDC
  set D' : Subgroup G := D.map (MulAut.conj (y₁ : G)).toMonoidHom with hD'
  have hD'H : D' ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨?_, ?_⟩
    · set dX : X := ⟨d, hd.2⟩
      have he : (dX : X ⧸ aschbacherSolvableCore 3 X) ∈ imgInf X A :=
        ⟨dX, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
      obtain ⟨d₂, hd₂, hd₂e⟩ := hg _ he
      have h1 : (d₂ : X ⧸ aschbacherSolvableCore 3 X) =
          ((y₁ * dX * y₁⁻¹ : X) : X ⧸ aschbacherSolvableCore 3 X) := by
        rw [QuotientGroup.mk'_apply] at hd₂e
        rw [hd₂e, ← hy₁, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h2 := QuotientGroup.eq.mp h1
      have h3 : (MulAut.conj (y₁ : G)).toMonoidHom d =
          (d₂ : G) * ((d₂⁻¹ * (y₁ * dX * y₁⁻¹) : X) : G) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv, dX]
        group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hd₂))
        (Subgroup.mem_sup_right ⟨_, h2, rfl⟩)
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro c hc
      have h1 : c * (y₁ : G) = y₁ * c := Subgroup.mem_centralizer_iff.mp hy₁C c hc
      have h1' : c * (y₁ : G)⁻¹ = (y₁ : G)⁻¹ * c := by
        calc c * (y₁ : G)⁻¹ = (y₁ : G)⁻¹ * (y₁ * c) * (y₁ : G)⁻¹ := by group
          _ = (y₁ : G)⁻¹ * (c * y₁) * (y₁ : G)⁻¹ := by rw [h1]
          _ = (y₁ : G)⁻¹ * c := by group
      have h2 : c * d = d * c := Subgroup.mem_centralizer_iff.mp (hDC hd) c hc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * ((y₁ : G) * d * (y₁ : G)⁻¹) = (c * y₁) * d * (y₁ : G)⁻¹ := by group
        _ = y₁ * (c * d) * (y₁ : G)⁻¹ := by rw [h1]; group
        _ = y₁ * d * (c * (y₁ : G)⁻¹) := by rw [h2]; group
        _ = (y₁ : G) * d * (y₁ : G)⁻¹ * c := by rw [h1']; group
  have hcard : Nat.card D' = Nat.card D := by
    rw [hD', Subgroup.card_map_of_injective (MulAut.conj (y₁ : G)).injective]
  have hDX : D ≤ X := inf_le_right
  have hHX : H ≤ X := inf_le_left.trans (sup_le hDX hTX)
  have hidx : ¬ 3 ∣ D.relIndex H := by
    rw [← Subgroup.relIndex_subgroupOf hHX]
    refine not_three_dvd_relIndex (fun x hx => hDH hx)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) ?_ ?_ ?_
    · rw [QuotientGroup.ker_mk']
      intro h3
      exact three_not_dvd_card_aschbacherSolvableCore (G := X)
        (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
    · rw [QuotientGroup.ker_mk', eq_bot_iff]
      rintro x ⟨hxD, hxθ⟩
      have hxD' := Subgroup.mem_subgroupOf.mp hxD
      exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_theta hAe hxD'.1 ⟨x, hxθ, rfl⟩))
    · refine le_antisymm ?_ (Subgroup.map_mono (fun x hx => hDH hx))
      rintro _ ⟨h, hh, rfl⟩
      have hh' := Subgroup.mem_subgroupOf.mp hh
      have hmem : (h : G) ∈ (D ⊔ T : Subgroup G) := hh'.1
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D T hDT] at hmem
      obtain ⟨d, hd, t, ht, hdt⟩ := hmem
      obtain ⟨t', ht', rfl⟩ := ht
      refine ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, ?_⟩
      have h1 : h = ⟨d, hd.2⟩ * t' := Subtype.ext hdt.symm
      have ht1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) t' = 1 :=
        (QuotientGroup.eq_one_iff t').mpr ht'
      rw [h1, map_mul, ht1, mul_one]
  obtain ⟨h, hhH, hhD⟩ := exists_conj_of_card_eq hDH hD'H hD3 hcard hidx
  have hmemh : h ∈ (T ⊔ D : Subgroup G) := sup_comm D T ▸ hhH.1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left T D hDT] at hmemh
  obtain ⟨t, ht, d, hd, rfl⟩ := hmemh
  have htX : t ∈ X := hTX ht
  have htC : t ∈ Subgroup.centralizer (C₀ : Set G) := by
    have := Subgroup.mul_mem _ hhH.2 (Subgroup.inv_mem _ (hDC hd))
    simpa using this
  set x : X := ⟨t, htX⟩⁻¹ * y₁ with hx
  have hxD : ∀ e ∈ D, (x : G) * e * (x : G)⁻¹ ∈ D := by
    intro e he
    have h1 : (y₁ : G) * e * (y₁ : G)⁻¹ ∈ D' := ⟨e, he, rfl⟩
    rw [← hhD] at h1
    obtain ⟨e', he', he'e⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he'e
    have h2 : (x : G) * e * (x : G)⁻¹ = d * e' * d⁻¹ := by
      simp only [hx, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      calc t⁻¹ * (y₁ : G) * e * ((y₁ : G)⁻¹ * t) = t⁻¹ * ((y₁ : G) * e * (y₁ : G)⁻¹) * t := by
            group
        _ = t⁻¹ * (t * d * e' * (t * d)⁻¹) * t := by rw [he'e]
        _ = d * e' * d⁻¹ := by group
    rw [h2]
    exact D.mul_mem (D.mul_mem hd he') (D.inv_mem hd)
  have hxD' : ∀ e ∈ D, (x : G)⁻¹ * e * (x : G) ∈ D := by
    have hle : D.map (MulAut.conj (x : G)).toMonoidHom ≤ D := by
      rintro _ ⟨e, he, rfl⟩
      exact hxD e he
    have heq : D.map (MulAut.conj (x : G)).toMonoidHom = D :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective])
    intro e he
    rw [← heq] at he
    obtain ⟨e', he', rfl⟩ := he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show (x : G)⁻¹ * ((x : G) * e' * (x : G)⁻¹) * (x : G) = e' by group]
  have hxc : ∀ c ∈ C₀, (x : G) * c = c * x := by
    intro c hc
    have h1 : c * (y₁ : G) = y₁ * c := Subgroup.mem_centralizer_iff.mp hy₁C c hc
    have h2 : c * t = t * c := Subgroup.mem_centralizer_iff.mp htC c hc
    simp only [hx, Subgroup.coe_mul, Subgroup.coe_inv]
    calc t⁻¹ * (y₁ : G) * c = t⁻¹ * (c * y₁) := by rw [mul_assoc, ← h1]
      _ = t⁻¹ * c * y₁ := by group
      _ = c * t⁻¹ * y₁ := by
        rw [show t⁻¹ * c = c * t⁻¹ by
          calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
            _ = t⁻¹ * (t * c) * t⁻¹ := by rw [h2]
            _ = c * t⁻¹ := by group]
      _ = c * (t⁻¹ * y₁) := by group
  refine ⟨x, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨e, he, c, hc, rfl⟩ := exists_mul_eq hAmax hAN hin hZ ha
      have hxcx : (x : G) * c * (x : G)⁻¹ = c := by rw [hxc c hc]; group
      have h1 : (x : G) * (e * c) * (x : G)⁻¹ = ((x : G) * e * (x : G)⁻¹) * c := by
        calc (x : G) * (e * c) * (x : G)⁻¹ =
            ((x : G) * e * (x : G)⁻¹) * ((x : G) * c * (x : G)⁻¹) := by group
          _ = ((x : G) * e * (x : G)⁻¹) * c := by rw [hxcx]
      rw [h1]
      exact A.mul_mem (hxD e he).1 hc.1
    · intro ha
      obtain ⟨e, he, c, hc, hec⟩ := exists_mul_eq hAmax hAN hin hZ ha
      have h1 : a = (x : G)⁻¹ * e * (x : G) * c := by
        have hxc' : (x : G)⁻¹ * c = c * (x : G)⁻¹ := by
          calc (x : G)⁻¹ * c = (x : G)⁻¹ * (c * x) * (x : G)⁻¹ := by group
            _ = (x : G)⁻¹ * (x * c) * (x : G)⁻¹ := by rw [hxc c hc]
            _ = c * (x : G)⁻¹ := by group
        calc a = (x : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * x := by group
          _ = (x : G)⁻¹ * (e * c) * x := by rw [hec]
          _ = (x : G)⁻¹ * e * (x : G) * ((x : G)⁻¹ * c * x) := by group
          _ = (x : G)⁻¹ * e * (x : G) * c := by
            rw [hxc', mul_assoc c, inv_mul_cancel, mul_one]
      rw [h1]
      exact A.mul_mem (hxD' e he).1 hc.1
  · rw [hx, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy₁,
      (QuotientGroup.eq_one_iff (⟨t, htX⟩ : X)).mpr ?_, inv_one, one_mul]
    obtain ⟨t', ht', ht'e⟩ := ht
    have : (⟨t, htX⟩ : X) = t' := Subtype.ext ht'e.symm
    rw [this]
    exact ht'

end Lift

section Eight

variable {G : Type} [Group G] [Finite G]

theorem thetaAct_eq_conj {X A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (X : Set G))
    {d : X} (hdA : (d : G) ∈ A) :
    Sec4.thetaAct hAN ⟨d, hdA⟩ = MulAut.conj (d : X ⧸ aschbacherSolvableCore 3 X) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [Item223CensusProof.thetaAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem card_imgInf {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) :
    Nat.card (imgInf X A) = 9 := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have hmap : (imgInf X A).map (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →* _) =
      (Sec4.thetaAct hAN).range := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨⟨d, (Subgroup.mem_subgroupOf.mp hd).1⟩,
        thetaAct_eq_conj hAN (Subgroup.mem_subgroupOf.mp hd).1⟩
    · rintro _ ⟨a, rfl⟩
      obtain ⟨d, hdA, hd⟩ := exists_mem_conj_eq_thetaAct hAmax hAN hin hZ a
      exact ⟨(d : X ⧸ aschbacherSolvableCore 3 X), ⟨d, Subgroup.mem_subgroupOf.mpr ⟨hdA, d.2⟩,
        rfl⟩, hd⟩
  have h1 : Nat.card (Sec4.thetaAct hAN).range *
      Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = Nat.card A :=
    Item223CensusProof.card_range_thetaAct hAN
  rw [hAC, hA27] at h1
  rw [← Subgroup.card_map_of_injective (K := imgInf X A) hinj, hmap]
  omega

theorem false_of_order_eight {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥)
    (hmono : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial)
    {g : X ⧸ aschbacherSolvableCore 3 X} (hg : ∀ e ∈ imgInf X A, g * e * g⁻¹ ∈ imgInf X A)
    (h8 : ∀ e ∈ imgInf X A, g ^ 8 * e = e * g ^ 8)
    (h4 : ∃ e ∈ imgInf X A, g ^ 4 * e ≠ e * g ^ 4) : False := by
  obtain ⟨x, hxN, hxg⟩ := exists_normalizer_lift hAmax hAN hin hZ hg
  obtain ⟨f, hf⟩ := hmono
  set n : Subgroup.normalizer (A : Set G) := ⟨x, hxN⟩ with hn
  have hρ : A.normalizerMonoidHom n ∈ starOf A X := ⟨n, x.2, rfl⟩
  have hM := hf ⟨_, hρ, rfl⟩
  have h12 : A.normalizerMonoidHom (n ^ 12) = 1 := by
    rw [map_pow]
    apply coordGL_injective f
    rw [map_pow, monomial_pow_twelve hM, map_one]
  have hx12 : ∀ a ∈ A, (x : G) ^ 12 * a * ((x : G) ^ 12)⁻¹ = a := by
    intro a ha
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h12
    simp only [MulAut.one_apply] at h1
    rw [Sec4.normalizerMonoidHom_apply_coe] at h1
    simpa [hn] using h1
  have hg12 : ∀ e ∈ imgInf X A, g ^ 12 * e = e * g ^ 12 := by
    rintro _ ⟨⟨d, hdX⟩, hd, rfl⟩
    have hdA := (Subgroup.mem_subgroupOf.mp hd).1
    have h2 : (x ^ 12 * ⟨d, hdX⟩ * (x ^ 12)⁻¹ : X) = ⟨d, hdX⟩ :=
      Subtype.ext (by simpa using hx12 d hdA)
    have h3 := congrArg (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) h2
    rw [map_mul, map_mul, map_inv, map_pow, QuotientGroup.mk'_apply, hxg] at h3
    calc g ^ 12 * QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨d, hdX⟩ =
        g ^ 12 * QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨d, hdX⟩ * (g ^ 12)⁻¹ *
          g ^ 12 := by group
      _ = QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨d, hdX⟩ * g ^ 12 := by rw [h3]
  obtain ⟨e, he, hne⟩ := h4
  apply hne
  have hc12 : Commute (g ^ 12) e := hg12 e he
  have hc8 : Commute (g ^ 8) e := h8 e he
  have h48 : g ^ 4 = g ^ 12 * (g ^ 8)⁻¹ := by group
  rw [h48]
  exact (hc12.mul_left hc8.inv_left).eq

end Eight

section AutEight

@[expose] def AutEight228 (S : Type) [Group S] : Prop :=
  ∀ B : Subgroup S, Nat.card B = 9 → ∃ g : S, (∀ b ∈ B, g * b * g⁻¹ ∈ B) ∧
    (∀ b ∈ B, g ^ 8 * b = b * g ^ 8) ∧ ∃ b ∈ B, g ^ 4 * b ≠ b * g ^ 4

theorem autEight228_of_mulEquiv {Y S : Type} [Group Y] [Group S] (e : Y ≃* S)
    (hS : AutEight228 S) : AutEight228 Y := by
  intro B hB
  obtain ⟨g, hgN, h8, b, hb, h4⟩ := hS (B.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hB])
  refine ⟨e.symm g, fun c hc => ?_, fun c hc => ?_, e.symm b, ?_, fun h => h4 ?_⟩
  · obtain ⟨c', hc', hc'e⟩ := hgN (e c) ⟨c, hc, rfl⟩
    have : c' = e.symm g * c * (e.symm g)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact hc'e
    rw [← this]
    exact hc'
  · apply e.injective
    rw [map_mul, map_mul, map_pow, e.apply_symm_apply]
    exact h8 (e c) ⟨c, hc, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := hb
    simpa using hc
  · have := congrArg e h
    rwa [map_mul, map_mul, map_pow, e.apply_symm_apply, e.apply_symm_apply] at this

theorem autEight228_of_sylow {S : Type} [Group S] [Finite S]
    (hS : (Nat.card S).factorization 3 = 2) {P₀ : Subgroup S} (hP₀ : Nat.card P₀ = 9) {g : S}
    (hgN : ∀ b ∈ P₀, g * b * g⁻¹ ∈ P₀) (h8 : ∀ b ∈ P₀, g ^ 8 * b = b * g ^ 8)
    (h4 : ∃ b ∈ P₀, g ^ 4 * b ≠ b * g ^ 4) : AutEight228 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro B hB
  have hc : ∀ P : Subgroup S, Nat.card P = 9 → Nat.card P = 3 ^ (Nat.card S).factorization 3 :=
    fun P hP => by rw [hS, hP]; norm_num
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq S (Sylow.ofCard P₀ (hc P₀ hP₀))
    (Sylow.ofCard B (hc B hB))
  have hh' : MulAut.conj h • P₀ = B := by
    have := congrArg (fun P : Sylow 3 S => (P : Subgroup S)) hh
    simpa [Sylow.coe_subgroup_smul] using this
  have hmemB : ∀ c, c ∈ B ↔ h⁻¹ * c * h ∈ P₀ := by
    intro c
    rw [← hh', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine ⟨h * g * h⁻¹, fun c hc => ?_, fun c hc => ?_, ?_⟩
  · rw [hmemB] at hc ⊢
    have := hgN _ hc
    simpa [mul_assoc] using this
  · rw [hmemB] at hc
    have h1 := h8 _ hc
    have hpow : (h * g * h⁻¹) ^ 8 = h * g ^ 8 * h⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hpow]
    calc h * g ^ 8 * h⁻¹ * c = h * (g ^ 8 * (h⁻¹ * c * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * c * h) * g ^ 8) * h⁻¹ := by rw [h1]
      _ = c * (h * g ^ 8 * h⁻¹) := by group
  · obtain ⟨b, hb, hne⟩ := h4
    refine ⟨h * b * h⁻¹, (hmemB _).mpr (by simpa [mul_assoc] using hb), fun heq => hne ?_⟩
    have hpow : (h * g * h⁻¹) ^ 4 = h * g ^ 4 * h⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hpow] at heq
    have := congrArg (fun z => h⁻¹ * z * h) heq
    simpa [mul_assoc] using this

variable {G : Type} [Group G] [Finite G]

theorem false_of_autEight228 {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hmono : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial)
    (hS : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X))
    (hE : AutEight228 (X ⧸ aschbacherSolvableCore 3 X)) : False := by
  have hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center
      (X ⧸ aschbacherSolvableCore 3 X)) with hb | ht
    · exact hb
    · exfalso
      have h1 : Nat.card (Sec4.thetaAct hAN).range *
          Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = Nat.card A :=
        Item223CensusProof.card_range_thetaAct hAN
      have hinn := Sec4.range_thetaAct_le_inner hAN hin
      have hbot : (Sec4.thetaAct hAN).range = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        obtain ⟨z, hz⟩ := hinn hσ
        rw [Subgroup.mem_bot, ← hz]
        ext w
        rw [MulAut.conj_apply, MulAut.one_apply,
          (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top z) w).symm, mul_inv_cancel_right]
      rw [hbot, Subgroup.card_bot, hAC, hA27] at h1
      norm_num at h1
  obtain ⟨g, hgN, h8, h4⟩ := hE (imgInf X A) (card_imgInf hAmax hA27 hAN hAC hin hZ)
  exact false_of_order_eight hAmax hAN hin hZ hmono hgN h8 h4

end AutEight

section Three

open Matrix

theorem signedMat_fixed_le_three : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) → KFacts.KP14.signedMat π s ^ 3 = 1 →
      KFacts.KP14.signedMat π s ≠ 1 →
        (Finset.univ.filter fun v : Fin 3 → ZMod 3 =>
          KFacts.KP14.signedMat π s *ᵥ v = v).card ≤ 3 := by
  decide +kernel

theorem monomial_fixed_le_three {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ KFacts.KP14.monomial)
    (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    (Finset.univ.filter fun v : Fin 3 → ZMod 3 =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v).card ≤ 3 := by
  have h3' : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h1' : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ≠ 1 := fun h => h1 (Units.ext h)
  exact KFacts.KP14.forall_mem_monomial (P := fun M => M ^ 3 = 1 → M ≠ 1 →
    (Finset.univ.filter fun v : Fin 3 → ZMod 3 => M *ᵥ v = v).card ≤ 3)
    signedMat_fixed_le_three hg h3' h1'

variable {G : Type} [Group G]

theorem exists_fixed_ne_one {A : Subgroup G} (hAe : IsElemAbelian 3 A) {ρ : MulAut A}
    (hρ3 : ρ ^ 3 = 1) {D : Subgroup A} (hD : ∀ d ∈ D, ρ d ∈ D) {d : A} (hdD : d ∈ D)
    (hd : ρ d ≠ d) : ∃ d₀ ∈ D, d₀ ≠ 1 ∧ ρ d₀ = d₀ := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hAe.1.is_comm.comm }
  have he : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hρρρ : ∀ a : A, ρ (ρ (ρ a)) = a := by
    intro a
    have := congrArg (fun σ : MulAut A => σ a) hρ3
    simpa [pow_succ, MulAut.mul_apply] using this
  by_cases hs1 : d * ρ d * ρ (ρ d) = 1
  · refine ⟨d⁻¹ * ρ d, D.mul_mem (D.inv_mem hdD) (hD d hdD), fun h => hd ?_, ?_⟩
    · have := congrArg (fun z => d * z) h
      simpa using this
    · have h2 : ρ (ρ d) = (d * ρ d)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, mul_comm]
        exact hs1
      have hrr : (ρ d)⁻¹ * (ρ d)⁻¹ = ρ d := by
        calc (ρ d)⁻¹ * (ρ d)⁻¹ = (ρ d)⁻¹ * (ρ d)⁻¹ * (ρ d) ^ 3 := by rw [he, mul_one]
          _ = ρ d := by group
      rw [map_mul, map_inv, h2, mul_inv, mul_left_comm, hrr]
  · refine ⟨d * ρ d * ρ (ρ d), D.mul_mem (D.mul_mem hdD (hD d hdD)) (hD _ (hD d hdD)), hs1, ?_⟩
    rw [map_mul, map_mul, hρρρ, mul_comm (ρ d * ρ (ρ d)) d, mul_assoc]

variable [Finite G]

theorem false_of_order_three {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥)
    (hmono : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial)
    {g : X ⧸ aschbacherSolvableCore 3 X} (hg : ∀ e ∈ imgInf X A, g * e * g⁻¹ ∈ imgInf X A)
    (h3 : ∀ e ∈ imgInf X A, g ^ 3 * e = e * g ^ 3)
    (h1 : ∃ e ∈ imgInf X A, g * e ≠ e * g) : False := by
  have hAe : IsElemAbelian 3 A := hAmax.prop
  obtain ⟨x, hxN, hxg⟩ := exists_normalizer_lift hAmax hAN hin hZ hg
  obtain ⟨f, hf⟩ := hmono
  set n : Subgroup.normalizer (A : Set G) := ⟨x, hxN⟩ with hn
  set ρ := A.normalizerMonoidHom n with hρdef
  have hρ : ρ ∈ starOf A X := ⟨n, x.2, rfl⟩
  have hρa : ∀ a : A, ((ρ a : A) : G) = (x : G) * a * (x : G)⁻¹ := fun a => rfl
  set D : Subgroup A := X.subgroupOf A with hD
  have hDρ : ∀ d ∈ D, ρ d ∈ D := by
    intro d hd
    rw [hD, Subgroup.mem_subgroupOf, hρa]
    exact X.mul_mem (X.mul_mem x.2 (Subgroup.mem_subgroupOf.mp hd)) (X.inv_mem x.2)
  have hact : ∀ k : ℕ, ∀ d : A, ∀ hdX : (d : G) ∈ X,
      ((⟨(x : G) ^ k * d * ((x : G) ^ k)⁻¹, X.mul_mem (X.mul_mem (X.pow_mem x.2 k) hdX)
        (X.inv_mem (X.pow_mem x.2 k))⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) =
        g ^ k * ((⟨d, hdX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) * (g ^ k)⁻¹ := by
    intro k d hdX
    rw [← hxg]
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl
  have hρ3 : ρ ^ 3 = 1 := by
    ext a
    obtain ⟨e, he, c, hc, hec⟩ := exists_mul_eq hAmax hAN hin hZ a.2
    have hρc : ρ ⟨c, hc.1⟩ = ⟨c, hc.1⟩ := fix_of_mem_starOf hAe hρ hc.1 hc.2
    have hx3 : (x : G) ^ 3 * e * ((x : G) ^ 3)⁻¹ = e := by
      have hee : ((⟨e, he.2⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) ∈ imgInf X A :=
        ⟨⟨e, he.2⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
      have h1 := hact 3 ⟨e, he.1⟩ he.2
      rw [show g ^ 3 * ((⟨e, he.2⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) * (g ^ 3)⁻¹ =
        ((⟨e, he.2⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) by
          rw [h3 _ hee, mul_inv_cancel_right]] at h1
      have h2 := QuotientGroup.eq.mp h1
      have hw : ((x : G) ^ 3 * e * ((x : G) ^ 3)⁻¹)⁻¹ * e ∈ A := by
        have hxA : (x : G) ^ 3 * e * ((x : G) ^ 3)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxN 3) e).mp he.1
        exact A.mul_mem (A.inv_mem hxA) he.1
      have := eq_one_of_mem_theta hAe hw ⟨_, h2, rfl⟩
      rw [inv_mul_eq_one] at this
      exact this
    have hρe : (ρ ^ 3) ⟨e, he.1⟩ = ⟨e, he.1⟩ := by
      apply Subtype.ext
      rw [hρdef, ← map_pow]
      change ((n ^ 3 : Subgroup.normalizer (A : Set G)) : G) * e *
        ((n ^ 3 : Subgroup.normalizer (A : Set G)) : G)⁻¹ = e
      rw [Subgroup.coe_pow]
      exact hx3
    have hρc3 : (ρ ^ 3) ⟨c, hc.1⟩ = ⟨c, hc.1⟩ := by
      rw [pow_succ, MulAut.mul_apply, hρc, pow_succ, MulAut.mul_apply, hρc, pow_one, hρc]
    have ha : a = ⟨e, he.1⟩ * ⟨c, hc.1⟩ := Subtype.ext hec
    rw [ha, map_mul, hρe, hρc3, MulAut.one_apply]
  obtain ⟨e, he, hne⟩ := h1
  obtain ⟨⟨d, hdX⟩, hd, rfl⟩ := he
  have hdA : d ∈ A := (Subgroup.mem_subgroupOf.mp hd).1
  have hmove : ρ ⟨d, hdA⟩ ≠ ⟨d, hdA⟩ := by
    intro h
    apply hne
    have h2 : (x : G) * d * (x : G)⁻¹ = d := congrArg Subtype.val h
    have h4 := hact 1 ⟨d, hdA⟩ hdX
    simp only [pow_one] at h4
    have h5 : ((⟨(x : G) * d * (x : G)⁻¹, X.mul_mem (X.mul_mem x.2 hdX) (X.inv_mem x.2)⟩ : X) :
        X ⧸ aschbacherSolvableCore 3 X) = ((⟨d, hdX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) := by
      congr 1
      exact Subtype.ext h2
    rw [h5] at h4
    rw [QuotientGroup.mk'_apply]
    calc g * ((⟨d, hdX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) =
        g * ((⟨d, hdX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) * g⁻¹ * g := by group
      _ = ((⟨d, hdX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) * g := by rw [← h4]
  obtain ⟨d₀, hd₀D, hd₀1, hd₀⟩ := exists_fixed_ne_one hAe hρ3 hDρ
    (Subgroup.mem_subgroupOf.mpr hdX) hmove
  set C₀ : Subgroup A := (Sec4.thetaQuotCentralizer X).subgroupOf A with hC₀
  have hC₀F : C₀ ≤ fixedSubgroupOf ρ := fun c hc =>
    (mem_fixedSubgroupOf ρ c).mpr (fix_of_mem_starOf hAe hρ c.2 (Subgroup.mem_subgroupOf.mp hc))
  have hd₀C : d₀ ∉ C₀ := by
    intro hc
    apply hd₀1
    have hdθ : ((d₀ : G)) ∈ A ⊓ X ⊓ Sec4.thetaQuotCentralizer X :=
      ⟨⟨d₀.2, Subgroup.mem_subgroupOf.mp hd₀D⟩, Subgroup.mem_subgroupOf.mp hc⟩
    have hdX0 : (d₀ : G) ∈ X := Subgroup.mem_subgroupOf.mp hd₀D
    have h1 : Sec4.thetaAct hAN d₀ = 1 :=
      (Item223CensusProof.mem_thetaQuotCentralizer_iff_of_mem (hAN d₀.2)).mp hdθ.2
    have h2 := thetaAct_eq_conj hAN (d := ⟨d₀, hdX0⟩) d₀.2
    rw [show (⟨((⟨d₀, hdX0⟩ : X) : G), d₀.2⟩ : A) = d₀ from rfl, h1] at h2
    have h3 : ((⟨d₀, hdX0⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) = 1 :=
      conj_injective_of_center_eq_bot hZ (by rw [← h2, map_one])
    have h4 := (QuotientGroup.eq_one_iff _).mp h3
    exact Subtype.ext (eq_one_of_mem_theta hAe d₀.2 ⟨_, h4, rfl⟩)
  have hlt : C₀ < fixedSubgroupOf ρ :=
    lt_of_le_of_ne hC₀F (fun h => hd₀C (h ▸ (mem_fixedSubgroupOf ρ d₀).mpr hd₀))
  have hcard : 3 < Nat.card (fixedSubgroupOf ρ) := by
    have h1 : Nat.card C₀ = 3 := by
      rw [← hAC, hC₀, ← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
          Sec4.thetaQuotCentralizer X ⊓ A ≤ A)).toEquiv, inf_comm]
    rw [← h1]
    exact Subgroup.card_lt_of_lt hlt
  have hM := hf ⟨ρ, hρ, rfl⟩
  have hM3 : coordGL f ρ ^ 3 = 1 := by rw [← map_pow, hρ3, map_one]
  have hM1 : coordGL f ρ ≠ 1 := fun h => hmove (by
    have := coordGL_injective f (h.trans (map_one _).symm)
    rw [this, MulAut.one_apply])
  have hle := monomial_fixed_le_three hM hM3 hM1
  have hinj : Nat.card (fixedSubgroupOf ρ) ≤ (Finset.univ.filter fun v : Fin 3 → ZMod 3 =>
      ((coordGL f ρ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective
      (fun a => ⟨Multiplicative.toAdd (f.symm (a : A)), ?_⟩) ?_
    · rw [coordGL_mulVec, coordLin3_apply]
      simp only [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rw [(mem_fixedSubgroupOf ρ a).mp a.2]
    · intro a b hab
      apply Subtype.ext
      exact f.symm.injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))
  omega

end Three

section AutThree

@[expose] def AutThree228 (S : Type) [Group S] : Prop :=
  ∀ B : Subgroup S, Nat.card B = 9 → ∃ g : S, (∀ b ∈ B, g * b * g⁻¹ ∈ B) ∧
    (∀ b ∈ B, g ^ 3 * b = b * g ^ 3) ∧ ∃ b ∈ B, g * b ≠ b * g

theorem autThree228_of_mulEquiv {Y S : Type} [Group Y] [Group S] (e : Y ≃* S)
    (hS : AutThree228 S) : AutThree228 Y := by
  intro B hB
  obtain ⟨g, hgN, h3, b, hb, h1⟩ := hS (B.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hB])
  refine ⟨e.symm g, fun c hc => ?_, fun c hc => ?_, e.symm b, ?_, fun h => h1 ?_⟩
  · obtain ⟨c', hc', hc'e⟩ := hgN (e c) ⟨c, hc, rfl⟩
    have : c' = e.symm g * c * (e.symm g)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact hc'e
    rw [← this]
    exact hc'
  · apply e.injective
    rw [map_mul, map_mul, map_pow, e.apply_symm_apply]
    exact h3 (e c) ⟨c, hc, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := hb
    simpa using hc
  · have := congrArg e h
    rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at this

theorem exists_three_of_automizer {L T : Type*} [Group L] [Group T] {B : Subgroup L}
    (f : Asc83Table.Automizer B ≃* T) {t : T} (h3 : t ^ 3 = 1) (h1 : t ≠ 1) :
    ∃ g : L, (∀ b ∈ B, g * b * g⁻¹ ∈ B) ∧ (∀ b ∈ B, g ^ 3 * b = b * g ^ 3) ∧
      ∃ b ∈ B, g * b ≠ b * g := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f.symm t)
  have hq3 : (QuotientGroup.mk n : Asc83Table.Automizer B) ^ 3 = 1 := by
    rw [hn, ← map_pow, h3, map_one]
  have hq1 : (QuotientGroup.mk n : Asc83Table.Automizer B) ≠ 1 := by
    rw [hn]
    exact fun h => h1 (by simpa using congrArg f h)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq3
  rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  refine ⟨n, fun b hb => (Subgroup.mem_normalizer_iff.mp n.2 b).mp hb, fun b hb => ?_, ?_⟩
  · rw [Subgroup.coe_pow] at hq3
    exact (Subgroup.mem_centralizer_iff.mp hq3 b hb).symm
  · by_contra hall
    push Not at hall
    exact hq1 (Subgroup.mem_centralizer_iff.mpr fun b hb => (hall b hb).symm)

variable {G : Type} [Group G] [Finite G]

theorem false_of_autThree228 {X A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X)
    (hmono : ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial)
    (hS : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X))
    (hE : AutThree228 (X ⧸ aschbacherSolvableCore 3 X)) : False := by
  have hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center
      (X ⧸ aschbacherSolvableCore 3 X)) with hb | ht
    · exact hb
    · exfalso
      have h1 : Nat.card (Sec4.thetaAct hAN).range *
          Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = Nat.card A :=
        Item223CensusProof.card_range_thetaAct hAN
      have hinn := Sec4.range_thetaAct_le_inner hAN hin
      have hbot : (Sec4.thetaAct hAN).range = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        obtain ⟨z, hz⟩ := hinn hσ
        rw [Subgroup.mem_bot, ← hz]
        ext w
        rw [MulAut.conj_apply, MulAut.one_apply,
          (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top z) w).symm, mul_inv_cancel_right]
      rw [hbot, Subgroup.card_bot, hAC, hA27] at h1
      norm_num at h1
  obtain ⟨g, hgN, h3, h1⟩ := hE (imgInf X A) (card_imgInf hAmax hA27 hAN hAC hin hZ)
  exact false_of_order_three hAmax hAN hAC hin hZ hmono hgN h3 h1

end AutThree

end Item22Res4Proof

end CFSG.RankThree.PartTwo.Sec21
