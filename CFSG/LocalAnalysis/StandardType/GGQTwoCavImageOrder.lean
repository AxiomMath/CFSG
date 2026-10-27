module

public import CFSG.GroupTheory.AutomorphismImageOrder
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenKernel
public import CFSG.LocalAnalysis.StandardType.GGQTwoOriginalNormalizerLift

public section

namespace CFSG.StandardType.QTwoCav

variable {G : Type} [Group G] {Bs L J : Subgroup G}
  (hN : Bs ≤ Subgroup.normalizer (L : Set G))

theorem card_automizer_image_dvd {H : Subgroup (MulAut L)}
    (hlift : ∀ a ∈ ggAutomizer H (ggGamma L hN).range,
      ∃ c ∈ ggAutomizer J Bs, GGOverGamma hN c a) :
    Nat.card (ggAutomizer H (ggGamma L hN).range) ∣ Nat.card (ggAutomizer J Bs) :=
  CFSG.GroupTheory.card_dvd_of_lifts_automorphisms
    (ggGamma L hN).rangeRestrict (ggGamma L hN).rangeRestrict_surjective
    (ggAutomizer J Bs) (ggAutomizer H (ggGamma L hN).range) hlift

section Original

variable [Finite G] {p : ℕ} {B D : Subgroup G} {x : G}

theorem gamma_j_range (hJL : J ≤ L) :
    (ggGamma L (hJL.trans Subgroup.le_normalizer)).range =
      (J.subgroupOf L).map (MulAut.conj : L →* MulAut L) := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨⟨j, hJL j.property⟩, j.property, ?_⟩
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rfl
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rfl

theorem exists_overGamma_of_setting (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hJL : J ≤ L)
    {a : MulAut ↥(ggGamma L hN).range}
    (ha : a ∈ ggAutomizer (ggGamma L (hJL.trans Subgroup.le_normalizer)).range
      (ggGamma L hN).range) :
    ∃ c ∈ ggAutomizer J Bs, GGOverGamma hN c a := by
  obtain ⟨t, htJ, htN, hta⟩ := mem_ggAutomizer_iff.mp ha
  obtain ⟨j₀, rfl⟩ := MonoidHom.mem_range.mp htJ
  obtain ⟨j, hjJ, hjB, hjL, hjact⟩ :=
    exists_original_normalizer_lift hS hp hp2 hN j₀.property htN
  refine ⟨ggConjAut Bs hjB, ggConjAut_mem_ggAutomizer hjJ hjB, ?_⟩
  intro b
  apply Subtype.ext
  rw [hta]
  have hconj := ggGamma_conj_normalizer L hN ⟨j, hjL⟩ b
    (ggConjAut Bs hjB b).property
  rw [hjact] at hconj
  exact hconj.symm

theorem card_automizer_image_dvd_of_setting (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hJL : J ≤ L) :
    Nat.card (ggAutomizer (ggGamma L (hJL.trans Subgroup.le_normalizer)).range
      (ggGamma L hN).range) ∣ Nat.card (ggAutomizer J Bs) :=
  card_automizer_image_dvd hN (fun _ ha =>
    exists_overGamma_of_setting hN hS hp hp2 hJL ha)

theorem card_automizer_inner_image_dvd_of_setting (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range) ∣ Nat.card (ggAutomizer J Bs) := by
  have hJL : J ≤ L := hS.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  rw [← gamma_j_range hJL]
  exact card_automizer_image_dvd_of_setting hN hS hp hp2 hJL

theorem eq_one_of_overGamma_one_of_setting
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p.Prime)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {c : MulAut Bs} (hc : c ∈ ggAutomizer J Bs) (hover : GGOverGamma hN c 1) : c = 1 := by
  have hJL : J ≤ L := hS.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hBs : CFSG.Assembly.IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hCL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBs
      (hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1)
      hS.1.1.1.2.2.2.2.2.2.1.2.2.1
      hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
      hS.1.1.1.2.2.2.2.2.2.1.2.2.2.2
  have hZ : Nat.card (Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤ p := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hcard : Nat.card (Bs ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = p := by
      rw [hCL, Nat.card_zpowers]
      letI : Fact p.Prime := ⟨hp⟩
      have hSS : CFSG.Assembly.LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
      exact orderOf_eq_prime (hBs.2 x (hS.1.1.2.1.1 hSS.2.1)) hSS.2.2.1
    exact (Subgroup.card_le_of_le hle).trans hcard.le
  exact eq_one_of_ggOverGamma_one hp hBs hS.1.2.2.2.1 hN hZ
    ((ggAutomizer_mono Bs hJL) hc) hover

theorem card_automizer_inner_image_eq_of_setting
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range) = Nat.card (ggAutomizer J Bs) := by
  have hJL : J ≤ L := hS.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  let A := ggAutomizer J Bs
  let H := (J.subgroupOf L).map (MulAut.conj : L →* MulAut L)
  let I := ggAutomizer H (ggGamma L hN).range
  have hlift : ∀ a ∈ I, ∃ c ∈ A, GGOverGamma hN c a := by
    intro a ha
    change a ∈ ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range at ha
    rw [← gamma_j_range hJL] at ha
    exact exists_overGamma_of_setting hN hS hp hp2 hJL ha
  choose c hc hov using hlift
  let f : I →* A :=
    { toFun := fun a => ⟨c a a.property, hc a a.property⟩
      map_one' := by
        apply Subtype.ext
        exact eq_one_of_overGamma_one_of_setting hS hp hN (hc 1 I.one_mem)
          (hov 1 I.one_mem)
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hOver : GGOverGamma hN
            ((c (a * b) (I.mul_mem a.property b.property))⁻¹ *
              (c a a.property * c b b.property)) 1 := by
          have h := (hov (a * b) (I.mul_mem a.property b.property)).inv.mul
            ((hov a a.property).mul (hov b b.property))
          simpa using h
        exact inv_mul_eq_one.mp (eq_one_of_overGamma_one_of_setting hS hp hN
          (A.mul_mem (A.inv_mem (hc _ _)) (A.mul_mem (hc _ _) (hc _ _))) hOver) }
  have hf : Function.Injective f := by
    intro a b hab
    have hcEq : c a a.property = c b b.property := congrArg Subtype.val hab
    apply Subtype.ext
    exact GGOverGamma.unique (hcEq ▸ hov a a.property)
      (hov b b.property)
  have hs : Function.Surjective f := by
    intro d
    obtain ⟨j, hjJ, hjN, hdj⟩ := mem_ggAutomizer_iff.mp d.property
    have hjL : j ∈ L := hJL hjJ
    let hjA := conj_mem_normalizer_range_ggGamma hN hjL hjN
    let a : I := ⟨ggConjAut (ggGamma L hN).range hjA,
      ggConjAut_mem_ggAutomizer
        (show MulAut.conj (⟨j, hjL⟩ : L) ∈ H from ⟨⟨j, hjL⟩, hjJ, rfl⟩) hjA⟩
    have hdEq : (d : MulAut Bs) = ggConjAut Bs hjN :=
      MulEquiv.ext fun b => Subtype.ext (hdj b)
    have hdOver : GGOverGamma hN (d : MulAut Bs) (a : MulAut _) := by
      rw [hdEq]
      exact ggOverGamma_conjAut hjL hjN
    refine ⟨a, Subtype.ext ?_⟩
    have hOver : GGOverGamma hN ((c a a.property)⁻¹ * d) 1 := by
      simpa using (hov a a.property).inv.mul hdOver
    exact inv_mul_eq_one.mp (eq_one_of_overGamma_one_of_setting hS hp hN
      (A.mul_mem (A.inv_mem (hc _ _)) d.property) hOver)
  exact Nat.card_congr (MulEquiv.ofBijective f ⟨hf, hs⟩).toEquiv


end Original

end CFSG.StandardType.QTwoCav

end
