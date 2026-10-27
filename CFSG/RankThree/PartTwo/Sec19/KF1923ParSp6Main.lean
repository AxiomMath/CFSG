module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Reduce
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Levi
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Solv
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open scoped Pointwise
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem card_stated_three : Nat.card (StatedSp 3 (ZMod 2)) = 1451520 := by
  rw [card_statedSp, Nat.card_zmod]
  decide

theorem card_borel_three : Nat.card (borelSubgroup 3 (ZMod 2)) = 512 := by
  rw [card_borelSubgroup, Nat.card_zmod]
  norm_num

theorem borel_index_odd : ¬ 2 ∣ (borelSubgroup 3 (ZMod 2)).index := by
  have h := (borelSubgroup 3 (ZMod 2)).card_mul_index
  rw [card_borel_three, card_stated_three] at h
  have hi : (borelSubgroup 3 (ZMod 2)).index = 2835 := by omega
  rw [hi]
  decide

noncomputable def borelSyl : Sylow 2 (StatedSp 3 (ZMod 2)) :=
  (IsPGroup.of_card (by rw [card_borel_three]; norm_num : Nat.card (borelSubgroup 3 (ZMod 2)) =
    2 ^ 9)).toSylow borel_index_odd

theorem exists_conj_borelSyl (T : Sylow 2 (StatedSp 3 (ZMod 2))) :
    ∃ g : StatedSp 3 (ZMod 2), g • borelSyl = T :=
  MulAction.exists_smul_eq _ _ _

theorem conj_injective_three :
    Function.Injective (MulAut.conj : StatedSp 3 (ZMod 2) →* MulAut (StatedSp 3 (ZMod 2))) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : z ∈ Subgroup.center (StatedSp 3 (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun hz g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hz'
  exact hz'

theorem not_alt10_three : ¬ Nonempty (StatedSp 3 (ZMod 2) ≃* alternatingGroup (Fin 10)) := by
  rintro ⟨e⟩
  have h1 := Nat.card_congr e.toEquiv
  rw [card_stated_three] at h1
  have h2 : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 10)
    have hp : Nat.card (Equiv.Perm (Fin 10)) = 3628800 := by
      rw [Nat.card_perm, Nat.card_fin]
      rfl
    rw [hp] at h
    omega
  omega

theorem borel_le_conj (P : Subgroup (StatedSp 3 (ZMod 2)))
    (T : Sylow 2 (StatedSp 3 (ZMod 2)))
    (hT : Subgroup.normalizer ((T : Subgroup (StatedSp 3 (ZMod 2))) : Set (StatedSp 3 (ZMod 2)))
      ≤ P) :
    ∃ g : StatedSp 3 (ZMod 2),
      borelSubgroup 3 (ZMod 2) ≤
        P.map (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃* _).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conj_borelSyl T
  refine ⟨g, fun x hx => ?_⟩
  have hcoe : (borelSyl : Subgroup (StatedSp 3 (ZMod 2))) = borelSubgroup 3 (ZMod 2) :=
    IsPGroup.toSylow_coe _ _
  have hT' : MulAut.conj g • (borelSubgroup 3 (ZMod 2)) = (T : Subgroup (StatedSp 3 (ZMod 2))) := by
    rw [← hcoe, ← Sylow.coe_subgroup_smul, hg]
  have hcx : MulAut.conj g x ∈ (T : Subgroup (StatedSp 3 (ZMod 2))) := by
    rw [← hT']
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hP : MulAut.conj g x ∈ P :=
    hT (Subgroup.le_normalizer hcx)
  refine Subgroup.mem_map.mpr ⟨MulAut.conj g x, hP, ?_⟩
  simp [MulAut.conj_apply]
  group

theorem pull_config {P : Subgroup (StatedSp 3 (ZMod 2))}
    {D : Subgroup (MulAut (StatedSp 3 (ZMod 2)))} {t : MulAut (StatedSp 3 (ZMod 2))}
    (hDP : D ≤ P.map (MulAut.conj : StatedSp 3 (ZMod 2) →* MulAut (StatedSp 3 (ZMod 2))))
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDO : D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : StatedSp 3 (ZMod 2) →*
        MulAut (StatedSp 3 (ZMod 2))))).map (P.map (MulAut.conj : StatedSp 3 (ZMod 2) →*
        MulAut (StatedSp 3 (ZMod 2)))).subtype)
    (htP : t ∈ P.map (MulAut.conj : StatedSp 3 (ZMod 2) →* MulAut (StatedSp 3 (ZMod 2))))
    (htN : t ∈ Subgroup.normalizer (D : Set (MulAut (StatedSp 3 (ZMod 2)))))
    (hall : ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹) :
    ∃ (D₀ : Subgroup (StatedSp 3 (ZMod 2))) (t₀ : StatedSp 3 (ZMod 2)),
      D₀ ≤ P ∧ Nat.card D₀ = 9 ∧ (∀ d ∈ D₀, d ^ 3 = 1) ∧ t₀ ∈ P ∧
      (∀ d ∈ D₀, t₀ * d * t₀⁻¹ ∈ D₀) ∧ (∀ d ∈ D₀, t₀ ^ 2 * d * (t₀ ^ 2)⁻¹ = d⁻¹) ∧
      D₀ ≤ (Sec4.oTwoP 3 ↥P).map P.subtype := by
  set c := (MulAut.conj : StatedSp 3 (ZMod 2) →* MulAut (StatedSp 3 (ZMod 2))) with hc
  have hcinj : Function.Injective c := conj_injective_three
  have hrange : D ≤ c.range := fun d hd => by
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp (hDP hd)
    exact ⟨x, rfl⟩
  obtain ⟨t₀, ht₀P, ht₀eq⟩ := Subgroup.mem_map.mp htP
  have hmap : (D.comap c).map c = D := Subgroup.map_comap_eq_self hrange
  refine ⟨D.comap c, t₀, ?_, ?_, ?_, ht₀P, ?_, ?_, ?_⟩
  · intro x hx
    have hcx : c x ∈ D := Subgroup.mem_comap.mp hx
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hDP hcx)
    have hyx : y = x := hcinj hyeq
    rw [← hyx]
    exact hy
  · calc Nat.card (D.comap c) = Nat.card ((D.comap c).map c) :=
          (Subgroup.card_map_of_injective hcinj).symm
      _ = Nat.card D := by rw [hmap]
      _ = 9 := hD9
  · intro x hx
    apply hcinj
    rw [map_pow, map_one]
    exact hD.2 (c x) (Subgroup.mem_comap.mp hx)
  · intro x hx
    rw [Subgroup.mem_comap]
    have hcx := Subgroup.mem_comap.mp hx
    have h1 : t * c x * t⁻¹ ∈ (D : Set (MulAut (StatedSp 3 (ZMod 2)))) :=
      (Subgroup.mem_normalizer_iff.mp htN (c x)).mp hcx
    show c (t₀ * x * t₀⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv, ht₀eq]
    exact h1
  · intro x hx
    apply hcinj
    have hcx := Subgroup.mem_comap.mp hx
    rw [map_mul, map_mul, map_inv, map_pow, ht₀eq, map_inv]
    exact hall (c x) hcx
  · intro x hx
    have hcx : c x ∈ D := Subgroup.mem_comap.mp hx
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hDO hcx)
    have hψ := oTwoP_map_mulEquiv 3 (Subgroup.equivMapOfInjective P c hcinj)
    rw [← hψ] at hy
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    apply hcinj
    have hzx : c (z : StatedSp 3 (ZMod 2)) = c x := by
      rw [← hyeq, ← hzeq]
      rfl
    exact hzx

theorem flag_one_no_E9 (D : Subgroup (StatedSp 3 (ZMod 2)))
    (t : StatedSp 3 (ZMod 2))
    (hDP : D ≤ flagStabilizer 3 (ZMod 2) (↑({1} : Finset ℕ) : Set ℕ))
    (hDO : D ≤ (Sec4.oTwoP 3 ↥(flagStabilizer 3 (ZMod 2) (↑({1} : Finset ℕ) : Set ℕ))).map
      (flagStabilizer 3 (ZMod 2) (↑({1} : Finset ℕ) : Set ℕ)).subtype)
    (hD9 : Nat.card D = 9) (hexp : ∀ d ∈ D, d ^ 3 = 1)
    (htP : t ∈ flagStabilizer 3 (ZMod 2) (↑({1} : Finset ℕ) : Set ℕ))
    (htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D) (ht2 : ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹) : False := by
  haveI hWn : (Sec4.oTwoP 3 ↥P1).Normal := by
    unfold Sec4.oTwoP
    infer_instance
  haveI hWs : Group.IsSolvable ↥(Sec4.oTwoP 3 ↥P1) := sp6_oTwoP_solvable ↥P1
  obtain ⟨ψ⟩ : Nonempty (StatedSp 2 (ZMod 2) ≃* Equiv.Perm (Fin 6)) :=
    CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (ZMod.card 2)
  haveI hNn : ((Sec4.oTwoP 3 ↥P1).map leviS).Normal :=
    Subgroup.Normal.map hWn leviS leviS_surjective
  let φ : ↥(Sec4.oTwoP 3 ↥P1) →* ↥((Sec4.oTwoP 3 ↥P1).map leviS) :=
    (leviS.comp (Sec4.oTwoP 3 ↥P1).subtype).codRestrict _
      (fun w => Subgroup.mem_map_of_mem leviS w.2)
  have hφs : Function.Surjective φ := by
    intro n
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.mp n.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwn⟩
  haveI hNs : Group.IsSolvable ↥((Sec4.oTwoP 3 ↥P1).map leviS) :=
    Group.isSolvable_of_surjective hφs
  have hcard := sp6_card_le_two_of_normal_solvable ψ ((Sec4.oTwoP 3 ↥P1).map leviS)
  have hDwW : D.subgroupOf P1 ≤ Sec4.oTwoP 3 ↥P1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hDO (Subgroup.mem_subgroupOf.1 hx))
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  let ρ : ↥(D.subgroupOf P1) →* ↥((Sec4.oTwoP 3 ↥P1).map leviS) :=
    (leviS.comp (D.subgroupOf P1).subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem leviS (hDwW x.2))
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : leviS x.1 = 1 := congrArg Subtype.val hx
    have h2 : leviUnit x.1 = 1 := congrArg Subtype.val hx1
    have hl : levi (x.1.1 : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1 :=
      congrArg Units.val h2
    have hxD : x.1.1 ∈ D := Subgroup.mem_subgroupOf.1 x.2
    have hx3 : x.1.1 = 1 := eq_one_of_levi_eq_one x.1.2 hl (hexp _ hxD)
    exact Subtype.ext (Subtype.ext hx3)
  have hcardD : Nat.card ↥(D.subgroupOf P1) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv).trans hD9
  have hle := Nat.card_le_card_of_injective ⇑ρ hρinj
  have h9 : 9 ≤ 2 := hcardD.symm.le.trans (hle.trans hcard)
  omega

theorem flagStabilizer_empty_three : flagStabilizer 3 (ZMod 2) (↑(∅ : Finset ℕ) : Set ℕ) = ⊤ := by
  ext g
  simp [mem_flagStabilizer]

theorem core_B (P : Subgroup (StatedSp 3 (ZMod 2)))
    (D : Subgroup (MulAut (StatedSp 3 (ZMod 2)))) (t : MulAut (StatedSp 3 (ZMod 2)))
    (hpr : NSPremises (StatedSp 3 (ZMod 2)) P D t)
    (hBP : borelSubgroup 3 (ZMod 2) ≤ P) :
    ∃ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ ≠ d⁻¹ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hsh, hDP, hD, hD9, hDO, htP, htN⟩ := hpr
  obtain ⟨D₀, t₀, hD₀P, hD₀9, hexp₀, ht₀P, ht₀N, ht₀2, hD₀O⟩ :=
    pull_config hDP hD hD9 hDO htP htN hcon
  have hPne : P ≠ ⊤ := by
    rcases hsh with ⟨_, hP⟩ | ⟨⟨e10⟩, _⟩
    · exact hP.1
    · exact absurd ⟨e10⟩ not_alt10_three
  obtain ⟨hPeq, -⟩ := borel_overgroups P hBP
  classical
  set I' : Finset ℕ := ({1, 2, 3} : Finset ℕ).filter
    (fun i => i ∈ borelCuts (ZMod 2) P) with hI'
  have hcoe : (↑I' : Set ℕ) = borelCuts (ZMod 2) P := by
    ext i
    simp only [hI', Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      obtain ⟨h1, h2⟩ := borelCuts_le P i h
      exact ⟨by omega, h⟩
  have hI'0 : I' ≠ ∅ := by
    intro h
    apply hPne
    rw [hPeq, ← hcoe, h, flagStabilizer_empty_three]
  have hsubI' : I' ⊆ ({1, 2, 3} : Finset ℕ) := Finset.filter_subset _ _
  have hPeq' : P = flagStabilizer 3 (ZMod 2) (↑I' : Set ℕ) := by
    rw [hcoe]
    exact hPeq
  rw [hPeq'] at hD₀P ht₀P hD₀O
  by_cases h1 : I' = {1}
  · rw [h1] at hD₀P ht₀P hD₀O
    exact flag_one_no_E9 D₀ t₀ hD₀P hD₀O hD₀9 hexp₀ ht₀P ht₀N ht₀2
  · exact flag_no_E9 I' hsubI' hI'0 h1 D₀ t₀ hD₀P hD₀9 hexp₀ ht₀P ht₀N ht₀2

theorem noSquare_H6 : NoSquareInvertingInParabolic (StatedSp 3 (ZMod 2)) := by
  intro P D hsh hDP hD hD9 hDO t htP htN hall
  have hPp : Sec19.IsProperParabolic P := by
    rcases hsh with ⟨_, hP⟩ | ⟨⟨e10⟩, _⟩
    · exact hP
    · exact absurd ⟨e10⟩ not_alt10_three
  obtain ⟨-, T, hT⟩ := hPp
  obtain ⟨g, hgB⟩ := borel_le_conj P T hT
  have hprem : NSPremises (StatedSp 3 (ZMod 2)) P D t := ⟨hsh, hDP, hD, hD9, hDO, htP, htN⟩
  have hpr := nsPremises_map (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃* StatedSp 3 (ZMod 2))
    not_alt10_three hprem
  obtain ⟨d', hd', hne⟩ := core_B (P.map (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃*
      StatedSp 3 (ZMod 2)).toMonoidHom)
    (D.map (MulAut.congr (MulAut.conj g⁻¹ :
      StatedSp 3 (ZMod 2) ≃* StatedSp 3 (ZMod 2))).toMonoidHom)
    (MulAut.congr (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃* StatedSp 3 (ZMod 2)) t) hpr hgB
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
  apply hne
  have h := congrArg (MulAut.congr (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃*
    StatedSp 3 (ZMod 2))) (hall d hd)
  simpa [map_mul, map_inv, map_pow] using h

theorem noSquare_of_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (hY : ¬ Nonempty (Y ≃* alternatingGroup (Fin 10)))
    (hYns : NoSquareInvertingInParabolic Y) : NoSquareInvertingInParabolic X := by
  intro P D hsh hDP hD hD9 hDO t htP htN hall
  have hpr := nsPremises_map e hY (⟨hsh, hDP, hD, hD9, hDO, htP, htN⟩ :
    NSPremises X P D t)
  refine hYns (P.map e.toMonoidHom) (D.map (MulAut.congr e).toMonoidHom) hpr.1 hpr.2.1
    hpr.2.2.1 hpr.2.2.2.1 hpr.2.2.2.2.1 (MulAut.congr e t) hpr.2.2.2.2.2.1 hpr.2.2.2.2.2.2 ?_
  intro d' hd'
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
  have h := congrArg (MulAut.congr e) (hall d hd)
  simpa [map_mul, map_inv, map_pow] using h

theorem kfPar_Sp6 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* projSp 3 (GaloisField 2 1))) : NoSquareInvertingInParabolic X := by
  obtain ⟨e⟩ := hX
  exact noSquare_of_map (e.trans CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp62Equiv)
    not_alt10_three noSquare_H6

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
