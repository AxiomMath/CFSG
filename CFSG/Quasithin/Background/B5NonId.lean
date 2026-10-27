module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.B5NonB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

theorem IsL345Type.of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsL345Type Y) :
    IsL345Type X := by
  rcases h with ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | ⟨K, hK, hf, hc, ⟨e'⟩⟩ | ⟨K, hK, hf, hc, ⟨e'⟩⟩
  · exact Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨K, hK, hf, hc, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨K, hK, hf, hc, ⟨e.trans e'⟩⟩)

theorem realizesVia_injective {V : Type*} [CommGroup V] {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H} {U Z : Subgroup V}
    (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

section Ident

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W U : Subgroup V}

theorem isL345_lift (hA36 : AsA36NoOddCover) (h : B51Hyp G L) (c : SecCtx G L A W U)
    (hT : IsL345Type ↥(autSec L W U)) : IsL345Type ↥L := by
  have hLM : L ≤ L ⊔ A := le_sup_left
  have hmem : ∀ l : ↥L, (secHom (L ⊔ A) c.hMW c.hMU) (Subgroup.inclusion hLM l) ∈ autSec L W U := by
    intro l
    rw [← map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU hLM]
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLM l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  let f : ↥L →* ↥(autSec L W U) :=
    ((secHom (L ⊔ A) c.hMW c.hMU).comp (Subgroup.inclusion hLM)).codRestrict (autSec L W U) hmem
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MulAut (Sec W U)) ∈ (L.subgroupOf (L ⊔ A)).map (secHom (L ⊔ A) c.hMW c.hMU) := by
      rw [map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU hLM]; exact y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext hgy⟩
  have hodd : ∀ x ∈ f.ker, Odd (orderOf x) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : Subgroup.inclusion hLM x ∈ (secHom (L ⊔ A) c.hMW c.hMU).ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    have h2 := (mem_ker_secHom (L ⊔ A) c.hMW c.hMU _).1 h1
    have hxc : (x : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
      (secKernel_le h c).2 ⟨Subgroup.mem_sup_left x.2, h2⟩
    have hxG : (x : MulAut V) ∈ G := le_G h x.2
    have := odd_orderOf_of_mem_centralizer h hxG hxc
    rwa [Subgroup.orderOf_coe] at this
  have hinj := hA36 ↥L ↥(autSec L W U) (quasi_L h) h.2.2.1 f hsurj hodd hT
  exact IsL345Type.of_equiv (MulEquiv.ofBijective f ⟨hinj, hsurj⟩) hT

theorem isL345_of_irr (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (c : SecCtx G L A W U) (hirr : XMod.IsIrrSec ↥(autSec L W U) (⊥ : Subgroup (Sec W U)) ⊤)
    {B : Subgroup (MulAut (Sec W U))} (hB : IsFFStarOffender (autSec (L ⊔ A) W U) B)
    (hq : qOf (autSec (L ⊔ A) W U) ≤ ((1 / 2 : ℚ) : WithTop ℚ)) :
    IsL345Type ↥(autSec L W U) := by
  have hc := hB42 (Sec W U) (sq_eq_one_sec hV W U) _ _ (b4Hyp_sec' h c hA21 hirr) B hB
  have key : ∀ r : ℚ, qOf (autSec (L ⊔ A) W U) = ((r : ℚ) : WithTop ℚ) → 1 / 2 < r → False := by
    intro r hr hlt
    rw [hr] at hq
    exact absurd (WithTop.coe_le_coe.1 hq) (not_le.2 hlt)
  rcases hc with ⟨-, -, -, hq1⟩ | ⟨-, ⟨n, hn⟩, -⟩ | ⟨-, hq3⟩ | ⟨-, hq4⟩ | ⟨-, hq5⟩ |
    ⟨-, -, -, hq6, -⟩ | ⟨-, -, -, -, hq7, -⟩ | ⟨-, -, hq8, -⟩ | ⟨-, n, hn45, hnat, -⟩ |
    ⟨-, ⟨-, -, -, hq10⟩ | ⟨-, -, hq10⟩⟩ | ⟨-, -, -, hq11, -⟩
  · exact (key _ hq1 (by norm_num)).elim
  · obtain ⟨K, hK, hf, hcK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
    exact Or.inl ⟨n, K, hK, hf, hcK, ⟨e.symm⟩⟩
  · exact (key _ hq3 (by norm_num)).elim
  · exact (key _ hq4 (by norm_num)).elim
  · exact (key _ hq5 (by norm_num)).elim
  · exact (key _ hq6 (by norm_num)).elim
  · exact (key _ hq7 (by norm_num)).elim
  · exact (key _ hq8 (by norm_num)).elim
  · obtain ⟨K, hK, hf, hcK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
    rcases hn45 with rfl | rfl
    · exact Or.inr (Or.inl ⟨K, hK, hf, by simpa using hcK, ⟨e.symm⟩⟩)
    · exact Or.inr (Or.inr ⟨K, hK, hf, by simpa using hcK, ⟨e.symm⟩⟩)
  · exact (key _ hq10 (by norm_num)).elim
  · exact (key _ hq10 (by norm_num)).elim
  · exact (key _ hq11 (by norm_num)).elim


theorem nonirr_identify (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover) (hIH : B51Part1Below (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) :
    IsL345Type ↥L := by
  classical
  obtain ⟨A₀, hA₀⟩ := exists_offender h
  obtain ⟨A, hA, -⟩ := B1Red.exists_isFFStarMin_below hA₀
  have hAG : A ≤ G := hA.1.1
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hAne : A ≠ ⊥ := hA.1.2.1
  have hA2 : IsPGroup 2 A := hAel.isPGroup
  have hquad : IsQuadratic A := B1_4_3 hV hA
  obtain ⟨I, Y₂, W₂, hI, hMI, hIY₂, hY₂W₂, hMY₂, hMW₂, hnc₂, hch⟩ := exists_chief_pair hV h hU hA
  obtain ⟨hIL, hIcomm, hIlt, hIirr⟩ := irr_data hI
  set Y := I ⊓ fixV L with hYdef
  have hAn : ∀ a ∈ A, ∀ x ∈ L, a * x * a⁻¹ ∈ L := fun a ha x hx => normal_L h a (hAG ha) x hx
  have hIA : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I := fun a ha w hw =>
    (hMI (Subgroup.mem_sup_right ha) w).2 hw
  have hMY : L ⊔ A ≤ stabSub Y := by
    refine sup_le_stabSub (fun x hx w hw => ?_) (fun a ha w hw => ?_)
    · have : x w = w := hw.2 x hx
      rw [this]; exact hw
    · exact ⟨hIA a ha w hw.1, B1Red.fixV_inv_of_normalizes hAn a ha w hw.2⟩
  have hnc₁ : ¬ commSub I L ≤ Y := by
    rw [hIcomm]
    intro hle
    exact lt_irrefl _ (lt_of_lt_of_le hIlt hle)
  have c₁ : SecCtx G L A I Y := ⟨hAG, hAel, hAne, inf_le_left, hMI, hMY, hnc₁⟩
  have hlt₂ : Y₂ < W₂ := by
    refine lt_of_le_of_ne hY₂W₂ fun heq => hnc₂ ?_
    exact (commSub_le_of_invariant (fun x hx w hw =>
      (hMW₂ (Subgroup.mem_sup_left hx) w).2 hw)).trans heq.symm.le
  have c₂ : SecCtx G L A W₂ Y₂ := ⟨hAG, hAel, hAne, hY₂W₂, hMW₂, hMY₂, hnc₂⟩
  have hAI : A ≤ stabSub I := le_sup_right.trans hMI
  have hAW₂ : A ≤ stabSub W₂ := le_sup_right.trans hMW₂
  have hAY₂ : A ≤ stabSub Y₂ := le_sup_right.trans hMY₂
  have hAY : A ≤ stabSub Y := le_sup_right.trans hMY
  have hsum := rAV_add_le_one hV hA.1 (inf_le_left : Y ≤ I) hIY₂ hY₂W₂ hAI hAW₂ hAY₂ hAY
    (sec_A_inf_centSec h c₁) (sec_A_inf_centSec h c₂)
  have hq₁ := qOf_secX_le h c₁ hquad
  have hq₂ := qOf_secX_le h c₂ hquad
  have hMG : IsFFStarOffender (L ⊔ A) A := ⟨le_sup_right, hAne, hAel, hA.1.2.2.2⟩
  have hFs : quasithinGenFitting (L ⊔ A) = L := genFitting_sup_eq h hAG hA2
  have hq₀ : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ A)) := by rw [hFs]; exact quasi_L h
  have hO2 : pCoreOf 2 (L ⊔ A) = ⊥ := pCoreOf_sup_eq_bot h hAG hA2
  by_cases hr₁ : rAV (autSec A I Y) ≤ 1 / 2
  ·
    obtain ⟨-, ⟨B, -, hB⟩, -⟩ := B1_5_8 hV hMG (W := I) (U := Y) inf_le_left hMI hMY hq₀ hO2
      (by rw [hFs]; exact hnc₁)
    have hirr := isIrrSec_autSec hIlt hIirr (le_sup_left.trans hMI) (le_sup_left.trans hMY)
    exact isL345_lift hA36 h c₁ (isL345_of_irr hA21 hB42 hV h c₁ hirr hB
      (hq₁.trans (WithTop.coe_le_coe.2 hr₁)))
  · have hr₂ : rAV (autSec A W₂ Y₂) ≤ 1 / 2 := by
      by_contra hcon
      push Not at hr₁ hcon
      linarith
    obtain ⟨-, ⟨B, -, hB⟩, -⟩ := B1_5_8 hV hMG (W := W₂) (U := Y₂) hY₂W₂ hMW₂ hMY₂ hq₀ hO2
      (by rw [hFs]; exact hnc₂)
    have hirrX := isIrrSec_secX c₂ hlt₂ hch
    have hq₂' : qOf (autSec (L ⊔ A) W₂ Y₂) ≤ ((1 / 2 : ℚ) : WithTop ℚ) :=
      hq₂.trans (WithTop.coe_le_coe.2 hr₂)
    have hcard : Nat.card (Sec W₂ Y₂) < Nat.card V := by
      have h1 := card_sec_mul hY₂W₂
      have h2 : Nat.card W₂ ≤ Nat.card V := Subgroup.card_le_card_group W₂
      have h3 : Nat.card I ≤ Nat.card Y₂ := Subgroup.card_le_of_le hIY₂
      have hIne : I ≠ ⊥ := by
        rintro rfl
        exact not_lt_bot hIlt
      have h4 : 1 < Nat.card I := (Subgroup.one_lt_card_iff_ne_bot I).2 hIne
      have h5 : 0 < Nat.card (Sec W₂ Y₂) := Nat.card_pos
      nlinarith
    obtain ⟨-, hcase⟩ := hIH (Sec W₂ Y₂) hcard (sq_eq_one_sec hV W₂ Y₂) _ _ (b51Hyp_secY h c₂ hA21 hB)
    refine isL345_lift hA36 h c₂ ?_
    rcases hcase with hi | hii | ⟨n, hiii⟩ | hiv
    · exact isL345_of_irr hA21 hB42 hV h c₂ (isIrrSec_secL_of_irrPlus h c₂ hirrX hi.1) hB hq₂'
    · obtain ⟨-, n, K, hK, hf, hcK, I', π, -, -, hreal, -, -⟩ := hii
      have hπ := hreal 0
      exact Or.inl ⟨n, K, hK, hf, hcK, ⟨(MulEquiv.ofBijective π
        ⟨realizesVia_injective (FFModel.nat_faithful _) hπ, hπ.1⟩).symm⟩⟩
    · obtain ⟨-, hn45, π, U₁, U₂, -, hr1, -⟩ := hiii
      have hbij : Function.Bijective π :=
        ⟨realizesVia_injective (FFModel.nat_faithful _) hr1, hr1.1⟩
      rcases hn45 with rfl | rfl
      · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
          ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩)
      · exact Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
          ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩)
    · obtain ⟨-, n, hn45, k, hk1, -, I', π, -, -, -, hreal⟩ := hiv
      have hr1 := hreal ⟨0, hk1⟩
      have hbij : Function.Bijective π :=
        ⟨realizesVia_injective (FFModel.nat_faithful _) hr1, hr1.1⟩
      rcases hn45 with rfl | rfl
      · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
          ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩)
      · exact Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
          ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩)

end Ident


end B5

end CFSG.Quasithin
