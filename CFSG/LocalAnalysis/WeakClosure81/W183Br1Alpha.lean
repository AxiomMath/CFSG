module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1AlphaLift
import CFSG.LocalAnalysis.WeakClosure81.W183Br1AlphaAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev alphaX (Y L : Subgroup (LGL 2 V)) : Subgroup (LGL 2 V) :=
  Y ⊓ Subgroup.normalizer (L : Set (LGL 2 V))

abbrev alphaC (Y L : Subgroup (LGL 2 V)) : Subgroup (LGL 2 V) :=
  Y ⊓ Subgroup.centralizer (L : Set (LGL 2 V))

instance alphaC_normal (Y L : Subgroup (LGL 2 V)) :
    ((alphaC Y L).subgroupOf (alphaX Y L)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (le_inf inf_le_left
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer (L : Set (LGL 2 V)))))).mpr ?_
  intro n g hn hg
  rw [Subgroup.mem_inf] at hn ⊢
  refine ⟨Y.mul_mem (Y.mul_mem hg.1 hn.1) (Y.inv_mem hg.1), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := ((Subgroup.mem_normalizer_iff''.mp hg.2) l).mp hl
  calc l * (g * n * g⁻¹)
      = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [hn.2 (g⁻¹ * l * g) hl']
    _ = (g * n * g⁻¹) * l := by group

abbrev alphaQuot (Y L : Subgroup (LGL 2 V)) : Type :=
  ↥(alphaX Y L) ⧸ (alphaC Y L).subgroupOf (alphaX Y L)

abbrev alphaMk (Y L : Subgroup (LGL 2 V)) : ↥(alphaX Y L) →* alphaQuot Y L :=
  QuotientGroup.mk' ((alphaC Y L).subgroupOf (alphaX Y L))

abbrev alphaA (Y L A : Subgroup (LGL 2 V)) : Subgroup (alphaQuot Y L) :=
  (A.subgroupOf (alphaX Y L)).map (alphaMk Y L)

abbrev alphaL (Y L : Subgroup (LGL 2 V)) : Subgroup (alphaQuot Y L) :=
  (L.subgroupOf (alphaX Y L)).map (alphaMk Y L)

variable {Y T L₁ L₂ A : Subgroup (LGL 2 V)}

private theorem w183_inf_centralizer_self_eq_bot {G : Type*} [Group G] {L : Subgroup G}
    (hsimple : IsSimpleGroup ↥L) (hnonab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) :
    L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hnc : ¬ IsMulCommutative ↥L := by
    intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    exact hab (congrArg Subtype.val (isMulCommutative_iff.mp hc ⟨a, ha⟩ ⟨b, hb⟩))
  have hZ : Subgroup.center ↥L = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using hxC g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

private theorem w183_cj_eq_components (htwo : Br2TwoComp Y T L₁ L₂) {x : LGL 2 V}
    (hx : x ∈ alphaX Y L₁) : cj x L₁ = L₁ ∧ cj x L₂ = L₂ := by
  have hcj1 : cj x L₁ = L₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₁) (g := x)).mp hx.2
  rcases htwo.perm x hx.1 with h | h
  · exact h
  · exact absurd (hcj1.symm.trans h.1) htwo.ne

private theorem w183_inf_centralizer_L2_le_normalizer (htwo : Br2TwoComp Y T L₁ L₂) :
    Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤
      Subgroup.normalizer (L₁ : Set (LGL 2 V)) := by
  intro y hy
  rw [Subgroup.mem_inf] at hy
  rcases htwo.perm y hy.1 with h | h
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.1
  · exact absurd (h.2.symm.trans ((Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := y)).mp
      (Subgroup.centralizer_le_normalizer (L₂ : Set (LGL 2 V)) hy.2))) htwo.ne

private theorem w183_conj_mem_centralizer {G : Type*} [Group G] {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := ((Subgroup.mem_normalizer_iff''.mp hg) l).mp hl
  calc l * (g * c * g⁻¹)
      = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc (g⁻¹ * l * g) hl']
    _ = (g * c * g⁻¹) * l := by group

private noncomputable def w183_equivMapOfInjOn {G G' : Type*} [Group G] [Group G']
    (f : G →* G') {H : Subgroup G}
    (hinj : ∀ a ∈ H, ∀ b ∈ H, f a = f b → a = b) : ↥H ≃* ↥(H.map f) :=
  let φ : ↥H →* ↥(H.map f) :=
    { toFun := fun h => ⟨f h, Subgroup.mem_map_of_mem f h.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : G) (b : G)) }
  MulEquiv.ofBijective φ (by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab))
    · intro y
      obtain ⟨h, hh, hy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨h, hh⟩, Subtype.ext hy⟩)

private theorem w183_mk_inj_of_inf_bot {Y L : Subgroup (LGL 2 V)} {H : Subgroup (LGL 2 V)}
    (hHX : H ≤ alphaX Y L) (hC : H ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥) :
    ∀ a ∈ H.subgroupOf (alphaX Y L), ∀ b ∈ H.subgroupOf (alphaX Y L),
      alphaMk Y L a = alphaMk Y L b → a = b := by
  intro a ha b hb hab
  have hd : a * b⁻¹ ∈ (alphaC Y L).subgroupOf (alphaX Y L) := by
    have hker : alphaMk Y L (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L))
      (a * b⁻¹)).mp hker
  have hdC : (a * b⁻¹).1 ∈ Subgroup.centralizer (L : Set (LGL 2 V)) :=
    (Subgroup.mem_inf.mp hd).2
  have hdH : (a * b⁻¹).1 ∈ H :=
    (H.subgroupOf (alphaX Y L)).mul_mem ha ((H.subgroupOf (alphaX Y L)).inv_mem hb)
  have hbot : (a * b⁻¹).1 ∈ H ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) := ⟨hdH, hdC⟩
  rw [hC, Subgroup.mem_bot] at hbot
  exact mul_inv_eq_one.mp (Subtype.ext hbot)

theorem w183_alpha_finite (Y L : Subgroup (LGL 2 V)) : Finite (alphaQuot Y L) := by
  haveI : Finite ↥(alphaX Y L) := Subtype.finite
  exact Quotient.finite _

theorem w183_alpha_normal_cent (htwo : Br2TwoComp Y T L₁ L₂) :
    (alphaL Y L₁).Normal ∧ Subgroup.centralizer (alphaL Y L₁ : Set (alphaQuot Y L₁)) = ⊥ := by
  have hL₁X : L₁ ≤ alphaX Y L₁ := le_inf htwo.le₁ L₁.le_normalizer
  have hLnorm : (L₁.subgroupOf (alphaX Y L₁)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hL₁X).mpr ?_
    intro l x hl hx
    exact ((Subgroup.mem_normalizer_iff.mp hx.2) l).mp hl
  constructor
  · exact hLnorm.map (alphaMk Y L₁) (QuotientGroup.mk'_surjective _)
  · rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨xX, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hxX_cent : xX.1 ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlX : (⟨l, hL₁X hl⟩ : ↥(alphaX Y L₁)) ∈ L₁.subgroupOf (alphaX Y L₁) :=
        Subgroup.mem_subgroupOf.mpr hl
      have hcomm := hq (alphaMk Y L₁ ⟨l, hL₁X hl⟩) (Subgroup.mem_map_of_mem (alphaMk Y L₁) hlX)
      have hd : xX * ⟨l, hL₁X hl⟩ * xX⁻¹ * ⟨l, hL₁X hl⟩⁻¹ ∈
          (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
        have hker : alphaMk Y L₁ (xX * ⟨l, hL₁X hl⟩ * xX⁻¹ * ⟨l, hL₁X hl⟩⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [← hcomm]
          group
        exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp hker
      have hdL : (xX * ⟨l, hL₁X hl⟩ * xX⁻¹ * ⟨l, hL₁X hl⟩⁻¹).1 ∈ L₁ := by
        have h1 : xX * ⟨l, hL₁X hl⟩ * xX⁻¹ ∈ L₁.subgroupOf (alphaX Y L₁) := by
          rw [Subgroup.mem_subgroupOf]
          exact ((Subgroup.mem_normalizer_iff.mp xX.2.2) l).mp hl
        exact (L₁.subgroupOf (alphaX Y L₁)).mul_mem h1
          ((L₁.subgroupOf (alphaX Y L₁)).inv_mem hlX)
      have hdC : (xX * ⟨l, hL₁X hl⟩ * xX⁻¹ * ⟨l, hL₁X hl⟩⁻¹).1 ∈
          Subgroup.centralizer (L₁ : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hd).2
      have hbot : (xX * ⟨l, hL₁X hl⟩ * xX⁻¹ * ⟨l, hL₁X hl⟩⁻¹).1 ∈
          L₁ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := ⟨hdL, hdC⟩
      rw [w183_inf_centralizer_self_eq_bot htwo.simple₁ htwo.nonab₁, Subgroup.mem_bot] at hbot
      have hxl : xX.1 * l * xX.1⁻¹ = l := mul_inv_eq_one.mp hbot
      have hcommx : xX.1 * l = l * xX.1 := by
        calc xX.1 * l = (xX.1 * l * xX.1⁻¹) * xX.1 := by group
          _ = l * xX.1 := by rw [hxl]
      exact hcommx.symm
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁))
      xX).mpr ⟨xX.2.1, hxX_cent⟩

theorem w183_alpha_shape (htwo : Br2TwoComp Y T L₁ L₂) :
    Nonempty (↥L₁ ≃* ↥(alphaL Y L₁)) := by
  have hL₁X : L₁ ≤ alphaX Y L₁ := le_inf htwo.le₁ L₁.le_normalizer
  have hinj := w183_mk_inj_of_inf_bot hL₁X
    (w183_inf_centralizer_self_eq_bot htwo.simple₁ htwo.nonab₁)
  exact ⟨(Subgroup.subgroupOfEquivOfLe hL₁X).symm.trans
    (w183_equivMapOfInjOn (alphaMk Y L₁) hinj)⟩

theorem w183_alpha_card_elem (hA : A ≤ Y) (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hC₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥) (hcard : Nat.card ↥A = 4)
    (hel : IsElemAbelian 2 A) :
    Nat.card ↥(alphaA Y L₁ A) = 4 ∧ IsElemAbelian 2 (alphaA Y L₁ A) := by
  have hAX : A ≤ alphaX Y L₁ := le_inf hA hAn₁
  have hinj := w183_mk_inj_of_inf_bot hAX hC₁
  refine ⟨?_, (hel.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁)⟩
  rw [← Nat.card_congr (w183_equivMapOfInjOn (alphaMk Y L₁) hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hcard]

theorem w183_alpha_ti (htwo : Br2TwoComp Y T L₁ L₂) (hA : A ≤ Y)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hC₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hTI : IsTISub ↥Y (A.subgroupOf Y)) : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) := by
  intro t ht ht1 g hgt
  obtain ⟨tX, htXA, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨xX, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have ht0A : tX.1 ∈ A := Subgroup.mem_subgroupOf.mp htXA
  have ht0Y : tX.1 ∈ Y := tX.2.1
  have hxY : xX.1 ∈ Y := xX.2.1
  have ht0ne : tX.1 ≠ 1 := by
    intro h
    exact ht1 (by rw [show tX = 1 from Subtype.ext h, map_one])
  have hd : xX * tX * xX⁻¹ * tX⁻¹ ∈ (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
    have hker : alphaMk Y L₁ (xX * tX * xX⁻¹ * tX⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hgt]
      group
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp hker
  have hdC₁ : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
    (Subgroup.mem_inf.mp hd).2
  have hdY : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈ Y := (Subgroup.mem_inf.mp hd).1
  have hxN₂ : xX.1 ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := xX.1)).mpr
      (w183_cj_eq_components htwo xX.2).2
  have hdC₂ : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₂ : Set (LGL 2 V))).mul_mem
      (w183_conj_mem_centralizer hxN₂ (hC₂ ht0A))
      ((Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem (hC₂ ht0A))
  have hd_one : (xX * tX * xX⁻¹ * tX⁻¹).1 = 1 :=
    htwo.cent _ hdY
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hdC₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hdC₂ l hl).symm)
  have hcomm_amb : xX.1 * tX.1 = tX.1 * xX.1 := by
    have h1 : xX.1 * tX.1 * xX.1⁻¹ = tX.1 := mul_inv_eq_one.mp hd_one
    calc xX.1 * tX.1 = (xX.1 * tX.1 * xX.1⁻¹) * xX.1 := by group
      _ = tX.1 * xX.1 := by rw [h1]
  have hcommY : (⟨xX.1, hxY⟩ : ↥Y) * ⟨tX.1, ht0Y⟩ = ⟨tX.1, ht0Y⟩ * ⟨xX.1, hxY⟩ :=
    Subtype.ext hcomm_amb
  have hN := hTI ⟨tX.1, ht0Y⟩ (Subgroup.mem_subgroupOf.mpr ht0A)
    (fun h => ht0ne (congrArg Subtype.val h)) ⟨xX.1, hxY⟩ hcommY
  have hxN : xX.1 ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hA] at hN
    exact Subgroup.mem_subgroupOf.mp hN
  have hxNX : xX ∈ Subgroup.normalizer (A.subgroupOf (alphaX Y L₁) : Set ↥(alphaX Y L₁)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (le_inf hA hAn₁)]
    exact Subgroup.mem_subgroupOf.mpr hxN
  exact Subgroup.le_normalizer_map (alphaMk Y L₁)
    (Subgroup.mem_map_of_mem (alphaMk Y L₁) hxNX)

theorem w183_alpha_dynkin [Finite (alphaQuot Y L₁)] (htwo : Br2TwoComp Y T L₁ L₂) {τ : LGL 2 V}
    (hτY : τ ∈ Y) (hτ : ActsOnDynkinMod ⊥ L₁ τ) :
    ∃ τ' : alphaQuot Y L₁, ActsOnDynkinMod ⊥ (alphaL Y L₁) τ' := by
  haveI : Finite ↥(alphaX Y L₁) := Subtype.finite
  have hL₁X : L₁ ≤ alphaX Y L₁ := le_inf htwo.le₁ L₁.le_normalizer
  have hτX : τ ∈ alphaX Y L₁ := ⟨hτY, hτ.1⟩
  have hinj := w183_mk_inj_of_inf_bot hL₁X
    (w183_inf_centralizer_self_eq_bot htwo.simple₁ htwo.nonab₁)
  exact ⟨alphaMk Y L₁ ⟨τ, hτX⟩,
    w183_actsOnDynkin_map (alphaMk Y L₁) hinj (w183_dynkin_subgroupOf hL₁X hτX hτ)⟩

theorem w183_alpha_lift (htwo : Br2TwoComp Y T L₁ L₂) (hA : A ≤ Y)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hC₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (h : CorConfig (alphaQuot Y L₁) (alphaA Y L₁ A)) :
    CorConfig ↥(alphaX Y L₁) (A.subgroupOf (alphaX Y L₁)) := by
  have hAX : A ≤ alphaX Y L₁ := le_inf hA hAn₁
  have hG₂le : Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ alphaX Y L₁ :=
    le_inf inf_le_left (w183_inf_centralizer_L2_le_normalizer htwo)
  have hG₂ : ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
      (alphaX Y L₁)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hG₂le).mpr ?_
    intro n g hn hg
    rw [Subgroup.mem_inf] at hn ⊢
    refine ⟨Y.mul_mem (Y.mul_mem hg.1 hn.1) (Y.inv_mem hg.1), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro l hl
    have hgN : g ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := g)).mpr
        (w183_cj_eq_components htwo hg).2
    have hl' : g⁻¹ * l * g ∈ L₂ := ((Subgroup.mem_normalizer_iff''.mp hgN) l).mp hl
    calc l * (g * n * g⁻¹)
        = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [hn.2 (g⁻¹ * l * g) hl']
      _ = (g * n * g⁻¹) * l := by group
  have hinj : ∀ a ∈ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁),
      ∀ b ∈ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁),
        alphaMk Y L₁ a = alphaMk Y L₁ b → a = b := by
    intro a ha b hb hab
    have hd : a * b⁻¹ ∈ (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
      have hker : alphaMk Y L₁ (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁))
        (a * b⁻¹)).mp hker
    have hmem : a * b⁻¹ ∈ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁) :=
      ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)).mul_mem ha
        (((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
          (alphaX Y L₁)).inv_mem hb)
    have hbot : (a * b⁻¹).1 = 1 :=
      htwo.cent (a * b⁻¹).1 (Subgroup.mem_inf.mp hd).1
        (fun l hl => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 l hl).symm)
        (fun l hl => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2 l hl).symm)
    exact mul_inv_eq_one.mp (Subtype.ext hbot)
  have hA₀ : A.subgroupOf (alphaX Y L₁) ≤
      (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁) := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact ⟨hA ha, hC₂ ha⟩
  exact w183_corConfig_lift (alphaMk Y L₁) (QuotientGroup.mk'_surjective _) hG₂ hinj hA₀ h

end CFSG.LocalAnalysis.WeakClosure81

end
