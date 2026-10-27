module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Inv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_trivial_mul {W : Type*} [CommGroup W] {C : Subgroup W} {x y : MulAut W}
    (hx : ∀ w : W, x w * w⁻¹ ∈ C) (hy : ∀ w : W, y w * w⁻¹ ∈ C) :
    ∀ w : W, (x * y) w * w⁻¹ ∈ C := by
  intro w
  rw [MulAut.mul_apply]
  convert C.mul_mem (hx (y w)) (hy w) using 1
  group

private theorem s16t3_trivial_inv {W : Type*} [CommGroup W] {C : Subgroup W} {x : MulAut W}
    (hx : ∀ w : W, x w * w⁻¹ ∈ C) : ∀ w : W, x⁻¹ w * w⁻¹ ∈ C := by
  intro w
  have h : w * (x⁻¹ w)⁻¹ ∈ C := by simpa using hx (x⁻¹ w)
  convert C.inv_mem h using 1
  group

private theorem s16t3_trivial_conj {W : Type*} [CommGroup W] {C : Subgroup W}
    {x y : MulAut W} (hx : ∀ w : W, x w * w⁻¹ ∈ C) (hy : ∀ z : W, z ∈ C → y z ∈ C) :
    ∀ w : W, (y * x * y⁻¹) w * w⁻¹ ∈ C := by
  intro w
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have heq : y (x (y⁻¹ w)) * w⁻¹ = y (x (y⁻¹ w) * (y⁻¹ w)⁻¹) := by
    rw [map_mul, map_inv]
    simp
  rw [heq]
  exact hy _ (hx (y⁻¹ w))

private theorem s16t3_two_lt_rkIdx_of_eight_mul {X : Type*} [Group X] [Finite X]
    (S : Subgroup X) (hpow : ∃ e : ℕ, S.index = 2 ^ e) (h : 8 * Nat.card S ≤ Nat.card X) :
    2 < rkIdx S := by
  obtain ⟨e, he⟩ := hpow
  haveI : Nonempty ↥S := ⟨1⟩
  have hcard : Nat.card S * S.index = Nat.card X := Subgroup.card_mul_index S
  rw [← hcard] at h
  have h8le : 8 ≤ S.index := by
    have h' : Nat.card S * 8 ≤ Nat.card S * S.index := by
      rw [Nat.mul_comm (Nat.card S) 8]
      exact h
    exact Nat.le_of_mul_le_mul_left h' Nat.card_pos
  have h3 : 3 ≤ e := by
    have h23 : 2 ^ 3 ≤ 2 ^ e := by simpa [he] using h8le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h23
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : rkIdx S = e := by rw [rkIdx, he, padicValNat.prime_pow]
  omega

theorem threeNat_of_component_data
    {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}
    (helem : ∀ w : W, w * w = 1) (hle : L ≤ A)
    (hnormal : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T A)
    (hquasi : CFSG.Open.IsQuasisimple ↥L)
    (hcomm : commSub ⊤ L = ⊤)
    (hsum : SumOfNatShape L ⊤ (fixV L) 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut W)),
        I₂ = I₁.map g.toMonoidHom) : ThreeNat A L T := by
  refine
    { elem := helem
      le := hle
      normal := hnormal
      sylow := hT
      quasi := hquasi
      comm := hcomm
      sum := hsum
      trans := htrans
      faithful := ?_ }
  intro a ha hfix
  refine s16g_eq_one_of_commSub hcomm (fun l hl => ?_) hfix
  have haN : a ∈ Subgroup.normalizer (L : Set (MulAut W)) := hnormal ha
  have hala : a * l * a⁻¹ ∈ L :=
    ((Subgroup.mem_normalizer_iff.mp haN) l).1 hl
  have hc : a * l * a⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem hala (L.inv_mem hl)
  obtain ⟨I, -, -, hI1⟩ := SumOfNatShape.exists_summand hsum (0 : Fin 3)
  have hC : ∀ z : W, z ∈ fixV L → l z ∈ fixV L :=
    fun z hz => fixV_apply_mem_of_mem_normalizer (Subgroup.le_normalizer hl) hz
  have hconj : ∀ w : W,
      (l * a⁻¹ * l⁻¹) w * w⁻¹ ∈ fixV L :=
    s16t3_trivial_conj (s16t3_trivial_inv hfix) hC
  have htriv : ∀ u ∈ I, (a * l * a⁻¹ * l⁻¹) u * u⁻¹ ∈ fixV L := by
    intro u _
    have h := s16t3_trivial_mul hfix hconj u
    simpa [mul_assoc] using h
  have hcone : a * l * a⁻¹ * l⁻¹ = 1 :=
    SumOfNatShape.eq_one_of_trivial hquasi hI1 hc htriv
  have h2 : a * l * a⁻¹ = l := mul_inv_eq_one.mp hcone
  calc a * l = (a * l * a⁻¹) * a := by group
    _ = l * a := by rw [h2]

theorem S16gRowCtx.threeNat (h : S16gRowCtx D V₀ V L hV)
    (hsum : SumOfNatShape (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))), I₂ = I₁.map g.toMonoidHom) :
    ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Vtil V₀ V hV) := inferInstance
  have hMS : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  refine threeNat_of_component_data (fun w => ?_) ?_ h.mBar_le_normalizer ?_ h.quasi h.comm_top ?_ htrans
  · simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  · simpa [lBar] using barSub_mono V₀ V hV h.setting.hyp151.le
  · have hsub : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf (stabTil V₀ V))
        (D.M.subgroupOf (stabTil V₀ V)) := by
      have hT := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      exact ⟨Subgroup.subgroupOf_mono (stabTil V₀ V) hT.1, hT.2.1.comap_subtype,
        by rw [Subgroup.relIndex_subgroupOf hMS]; exact hT.2.2⟩
    have hmap := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hsub (actTil V₀ V hV)
    simpa only [barSub, Mbar] using hmap
  · simpa [h.comm_top] using hsum

theorem mBarGT_two_of_threeNat
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T)) : MBarGT D.M V₀ V 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Vtil V₀ V hV) := inferInstance
  have hMS : D.M ≤ stabTil V₀ V := s16g_le_stabTil hS
  have hV₀le : V₀ ≤ V := hS.hyp16.hyp125.pairFacts.le
  unfold MBarGT
  constructor
  · intro m hm hC hC2
    set g : stabTil V₀ V := ⟨m, hMS hm⟩ with hg
    have ht : actTil V₀ V hV g ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV hm (hMS hm)
    have ht1 : actTil V₀ V hV g ≠ 1 := fun h1 =>
      hC ((actTil_eq_one_iff V₀ V hV g).1 h1)
    have ht2 : actTil V₀ V hV g * actTil V₀ V hV g = 1 := by
      rw [← map_mul]
      exact (actTil_eq_one_iff V₀ V hV (g * g)).2 hC2
    have h8 := hT.eight_mul_card_fixV_le ht ht1 ht2
    have hpow : ∃ e : ℕ, (fixV (Subgroup.zpowers (actTil V₀ V hV g))).index = 2 ^ e := by
      obtain ⟨a, ha⟩ := exists_pow_card_Vtil V₀ V hV
      have h1 : (fixV (Subgroup.zpowers (actTil V₀ V hV g))).index ∣ 2 ^ a :=
        ha ▸ Subgroup.index_dvd_card _
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      exact ⟨k, hk⟩
    exact (centMod_card_iff V₀ V hV g 2).2
      (s16t3_two_lt_rkIdx_of_eight_mul _ hpow h8)
  · intro _
    have hcard := card_Vtil_eq V₀ V hV hV₀le
    have h8 := hT.eight_le_card
    calc 2 ^ (2 + 1) * Nat.card V₀ = 8 * Nat.card V₀ := by norm_num
      _ ≤ Nat.card V₀ * Nat.card (Vtil V₀ V hV) := by
          rw [Nat.mul_comm 8 (Nat.card V₀)]
          exact Nat.mul_le_mul_left _ h8
      _ = Nat.card V := hcard.symm

theorem S16gRowCtx.mBarGT_two (h : S16gRowCtx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T)) :
    MBarGT D.M V₀ V 2 :=
  mBarGT_two_of_threeNat h.setting hT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
