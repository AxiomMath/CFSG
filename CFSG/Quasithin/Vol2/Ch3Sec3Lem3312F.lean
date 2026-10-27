module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace L3312

variable {G : Type} [Group G] [Finite G]

namespace Hyp3312

variable {T M L D Y : Subgroup G} (H : Hyp3312 G T M L D Y)

include H

omit H in
theorem modO2_equiv :
    Nonempty (ModO2 (modO2Image (Y ⊔ T ⊔ D) Y) ≃* (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  set X := Y ⊔ T ⊔ D with hX
  have hYX : Y ≤ X := le_sup_left.trans le_sup_left
  let f : ↥Y →* ↥(modO2Image X Y) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hYX)).codRestrict _
      (fun y => ⟨Subgroup.inclusion hYX y, y.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hk : IsPGroup 2 ↥f.ker := by
    rintro ⟨y, hy⟩
    have hy' : Subgroup.inclusion hYX y ∈ CFSG.pCore 2 ↥X := by
      have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Subgroup.inclusion hYX y) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, hy'⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : G)) hk
    simpa using h1
  obtain ⟨e⟩ := modO2_equiv_of_surjective f hf hk
  exact ⟨e⟩

omit H in
theorem inf_pCoreOf_le : Y ⊓ pCoreOf 2 (Y ⊔ T ⊔ D) ≤ pCoreOf 2 Y := by
  have hYX : Y ≤ Y ⊔ T ⊔ D := le_sup_left.trans le_sup_left
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T ⊔ D) (hYX hy)) x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨Y.mul_mem (Y.mul_mem hy hx1) (Y.inv_mem hy), h1.mp hx2⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, h1.mpr hx2⟩
    have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx1) hy
    simpa [mul_assoc] using this

omit H in
theorem inducesInnerOn_of (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hinner : ∀ (t : G) (ht : t ∈ Y ⊔ T ⊔ D), t ∈ T →
      ∃ y₀ : G, ∃ hy₀ : y₀ ∈ Y ⊔ T ⊔ D, y₀ ∈ Y ∧
      ∀ (x : G) (hx : x ∈ Y ⊔ T ⊔ D), x ∈ Y →
        (QuotientGroup.mk ⟨t, ht⟩ * QuotientGroup.mk ⟨x, hx⟩ * (QuotientGroup.mk ⟨t, ht⟩)⁻¹ :
          ↥(Y ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(Y ⊔ T ⊔ D)) =
          QuotientGroup.mk ⟨y₀, hy₀⟩ * QuotientGroup.mk ⟨x, hx⟩ * (QuotientGroup.mk ⟨y₀, hy₀⟩)⁻¹) :
    InducesInnerOn T Y := by
  intro t ht
  have hYX : Y ≤ Y ⊔ T ⊔ D := le_sup_left.trans le_sup_left
  have htX : t ∈ Y ⊔ T ⊔ D := (le_sup_right.trans le_sup_left : T ≤ Y ⊔ T ⊔ D) ht
  obtain ⟨y₀, hy₀X, hy₀, hc⟩ := hinner t htX ht
  refine ⟨y₀, hy₀, fun x hx => ?_⟩
  have h1 := hc x (hYX hx) hx
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at h1
  have h2 : (t * x * t⁻¹)⁻¹ * (y₀ * x * y₀⁻¹) ∈ pCoreOf 2 (Y ⊔ T ⊔ D) := by
    rw [pCoreOf]
    exact ⟨_, h1, by simp⟩
  have h3 : (t * x * t⁻¹) * (y₀ * x * y₀⁻¹)⁻¹ ∈ pCoreOf 2 (Y ⊔ T ⊔ D) := by
    have hn := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T ⊔ D)
        ((Y ⊔ T ⊔ D).mul_mem ((Y ⊔ T ⊔ D).mul_mem htX (hYX hx)) ((Y ⊔ T ⊔ D).inv_mem htX)))
      ((y₀ * x * y₀⁻¹)⁻¹ * (t * x * t⁻¹))
    have h4 : (y₀ * x * y₀⁻¹)⁻¹ * (t * x * t⁻¹) ∈ pCoreOf 2 (Y ⊔ T ⊔ D) := by
      convert (pCoreOf 2 (Y ⊔ T ⊔ D)).inv_mem h2 using 1
      group
    have h5 := hn.mp h4
    simpa [mul_assoc] using h5
  have h6 : (t * x * t⁻¹) * (y₀ * x * y₀⁻¹)⁻¹ ∈ Y := by
    have hxt : t * x * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht) x).mp hx
    exact Y.mul_mem hxt (Y.inv_mem (Y.mul_mem (Y.mul_mem hy₀ hx) (Y.inv_mem hy₀)))
  exact inf_pCoreOf_le ⟨h6, h3⟩

theorem j1_case (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h128 : Lemma128One)
    (hJ1 : FactJ1Norm3312) {K : Subgroup G} (hK : K ∈ cComp (Y ⊔ T ⊔ D)) (hYK : Y ≤ K)
    (hHK : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G))
    (hc : A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) K))
    (htype : Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      InducesInnerOn T Y := by
  set X := Y ⊔ T ⊔ D with hX
  obtain ⟨⟨eY⟩, ⟨eK⟩⟩ := hc
  have hKH : K ≤ X := le_of_mem_cComp hK
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨e⟩ := Hyp3312.modO2_equiv (T := T) (D := D) (Y := Y)
    have hc60 : Nat.card ↥(modO2Image X Y) = 60 := by
      rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hdvd : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ 60 := by
      rw [← Nat.card_congr e.toEquiv, ← hc60]
      exact Subgroup.card_quotient_dvd_card _
    apply htype.isPSL_two_two_two_of_card
    rcases htype.card with ⟨n, hn, hcn⟩ | hcn | hcn
    · rw [hcn] at hdvd ⊢
      have h4 := Type3312R.three_le_pow hn
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hn2 : n = 2 := by
        by_contra hne
        have h8 : 8 ≤ 2 ^ n :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h63 : 8 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Type3312R.le_sq_sub_one h8
        have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by simpa using h63)
        omega
      subst hn2
      norm_num
    · rw [hcn] at hdvd
      norm_num at hdvd
    · rw [hcn] at hdvd
      norm_num at hdvd
  · obtain ⟨f⟩ := modO2_mulEquiv hK
    exact ⟨f.trans eK⟩
  ·
    have : (modO2Image X K).Normal := modO2Image_normal hKH hHK
    let ψ : (↥X ⧸ CFSG.pCore 2 ↥X) →* MulAut ↥(modO2Image X K) := MulAut.conjNormal
    have hInn : (MulAut.conj : ↥(modO2Image X K) →* MulAut ↥(modO2Image X K)).range ≤
        ψ.range := by
      rintro _ ⟨n, rfl⟩
      exact ⟨_, MulAut.conjNormal_val⟩
    have hS := isSylowTwoOf_map_range ψ H.isSylowTwoOf_modO2Image_T
    have hYK' : modO2Image X Y ≤ modO2Image X K := Subgroup.map_mono fun y hy => hYK hy
    have hSB : (modO2Image X T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image X K))
        ((modO2Image X Y).subgroupOf (modO2Image X K)) := by
      rintro _ ⟨tb, htb, rfl⟩
      obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
      refine (conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
      exact mk_mem_normalizer_modO2Image htX (H.le_normalizer_Y h14 h37 h128 ht)
    have hB5 : IsAlt 5 ↥((modO2Image X Y).subgroupOf (modO2Image X K)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hYK').trans eY⟩
    have hJ := (hJ1 _ ⟨eK⟩ ψ.range _ _ hInn hS hB5 hSB).1
    refine Hyp3312.inducesInnerOn_of (D := D) (H.le_normalizer_Y h14 h37 h128) fun t htX ht => ?_
    obtain ⟨b, hb, hbc⟩ := hJ (ψ (QuotientGroup.mk ⟨t, htX⟩))
      ⟨QuotientGroup.mk ⟨t, htX⟩, ⟨⟨t, htX⟩, ht, rfl⟩, rfl⟩
    have hbY : (b : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ modO2Image X Y := hb
    obtain ⟨⟨y₀, hy₀X⟩, hy₀, hy₀b⟩ := hbY
    refine ⟨y₀, hy₀X, hy₀, fun x hxX hx => ?_⟩
    have hxY : (QuotientGroup.mk ⟨x, hxX⟩ : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ modO2Image X Y :=
      ⟨⟨x, hxX⟩, hx, rfl⟩
    have h1 := congrArg Subtype.val (hbc ⟨_, hYK' hxY⟩ hxY)
    simp only [ψ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1, ← hy₀b]
    rfl

end Hyp3312

end L3312

end CFSG.Quasithin.H13
