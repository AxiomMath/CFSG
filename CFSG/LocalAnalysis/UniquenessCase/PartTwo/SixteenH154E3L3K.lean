module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Gl3K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3ThreeAsm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (card_eq_of_isL3)

private theorem s16h_e3_isSLn_three_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) :
    IsSLn X 3 1 := by
  have hc : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := hc
  obtain ⟨f⟩ := s15k_jp_projEquiv hK (StatedSL 3 K)
  exact ⟨K, hF, hfin, by simpa using hK, ⟨e.trans f⟩⟩

theorem s16h_e3_l3_seven_K {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1)
    (hsum : SumOfNat (fun H V Z => BinaryNaturalSL H V Z 3 1) L U ⊥ 3)
    (hrank : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 7 E → Nat.card ↥E ≤ 343)
    (hrk3 : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 7 E ∧ Nat.card ↥E = 343)
    (hbad : ∃ w ∈ U, w ≠ 1 ∧ ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 7 E →
      (∀ e ∈ E, e w = w) → Nat.card ↥E ≤ 7) :
    (∃ Z : Subgroup (MulAut W), Nat.card ↥Z = 7 ∧ Z ≤ X ∧
        (∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
        (∀ z ∈ Z, ∀ a ∈ L ⊔ L', z * a = a * z) ∧
        Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
          Set (MulAut W))) ∧
        ∀ N : Subgroup (MulAut W), N ≤ X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
          Set (MulAut W)) → (∀ x ∈ X, N.map (MulAut.conj x).toMonoidHom = N) →
          Group.IsNilpotent ↥N → N ≤ Z) ∨
      IsL3 ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) 1 := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨w, hwU, -, hbadw⟩ := hbad
  obtain ⟨t, -, hLt, -⟩ := F.swap
  have h168 : Nat.card ↥L = 168 := card_eq_of_isL3 hL
  have hLe : ↥L ≃* ↥L' :=
    (L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hLt)
  have hL' : IsL3 ↥L' 1 := CFSG.Blueprint.LieModel.of_mulEquiv hLe hL
  have hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1 := fun a ha hc => by
    have h1 := s16h_isL3_centreless hL ⟨a, ha⟩ fun b => Subtype.ext (hc b b.2)
    exact congrArg Subtype.val h1
  have hpL : 7 ∣ Nat.card ↥L := by rw [h168]; norm_num
  have hAut : ¬ 7 ^ 2 ∣ Nat.card (MulAut ↥L) := fun h9 =>
    absurd (h9.trans (card_mulAut_dvd_of_isL3 hL)) (by decide)
  have hrk : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 7 E ∧ Nat.card ↥E = 7 ^ 3 := by
    obtain ⟨E, h1, h2, h3⟩ := hrk3
    exact ⟨E, h1, h2, by rw [h3]; norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨d, hdK, hdord⟩, hnomove⟩ :=
    s16h_e3_frame_p F (by norm_num : Nat.Prime 7) (by norm_num) hcen hpL hAut hrk hwU hbadw
  have hN : ∀ I : Subgroup W, BinaryNaturalSL L I ⊥ 3 1 → s16h_SimpleScalar L I ⊥ :=
    fun I hI => s16h_simpleScalar_binarySL3 (s16c7_isQuasisimple_of_isL3 hL)
      (s16h_e3_isSLn_three_of_isL3 hL) hI
  have hN' : ∀ I : Subgroup W, BinaryNaturalSL L' I ⊥ 3 1 → s16h_SimpleScalar L' I ⊥ :=
    fun I hI => s16h_simpleScalar_binarySL3 (s16c7_isQuasisimple_of_isL3 hL')
      (s16h_e3_isSLn_three_of_isL3 hL') hI
  have hsum' : SumOfNat (fun H V Z => BinaryNaturalSL H V Z 3 1) L' U' ⊥ 3 :=
    s16h_e3_frame_sum_conj F (N := fun H V Z => BinaryNaturalSL H V Z 3 1)
      (fun f H I h => s16h_e3_sl3_conj_stable f H I h) hsum
  obtain ⟨π₁, π₂, hπ₁, hπ₂⟩ := s16h_e3_frame_cent_hom F
    (N := fun H V Z => BinaryNaturalSL H V Z 3 1) (k := 3) hN hN' hsum hsum'
  have hinj : ∀ x : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W))), π₁ x = 1 → π₂ x = 1 → x = 1 := by
    intro x h1 h2
    have hU1 := (hπ₁ x).mp h1
    have hU2 := (hπ₂ x).mp h2
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    have hv : v ∈ U ⊔ U' := by rw [F.sup_eq]; exact Subgroup.mem_top v
    obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp hv
    show (x : MulAut W) (u * u') = u * u'
    rw [map_mul, hU1 u hu, hU2 u' hu']
  have hno : ∀ x : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W))), orderOf x = 7 → π₁ x ≠ 1 ∧ π₂ x ≠ 1 := by
    intro x hx
    have hx7 : (x : MulAut W) ^ 7 = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      simpa using congrArg Subtype.val h
    have hx1 : (x : MulAut W) ≠ 1 := fun h1 => by
      have h2 : x = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hx
      omega
    obtain ⟨⟨u, hu, hxu⟩, ⟨u', hu', hxu'⟩⟩ := hnomove (x : MulAut W) x.2 hx7 hx1
    exact ⟨fun h1 => hxu ((hπ₁ x).mp h1 u hu), fun h2 => hxu' ((hπ₂ x).mp h2 u' hu')⟩
  have hd : orderOf (⟨d, hdK⟩ : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W)))) = 7 := by
    rw [Subgroup.orderOf_mk]
    exact hdord
  rcases s16h_e3_gl3_K_structure π₁ π₂ hinj hno hd with hK3 | ⟨ZK, hZK7, hZKuniq, hsolv, hnil⟩
  · exact Or.inr hK3
  · obtain ⟨hZcard, hZX, hZnorm, hZcomm⟩ := s16h_e3_frame_Z_of_unique F hZK7 hZKuniq
    refine Or.inl ⟨_, hZcard, hZX, hZnorm, hZcomm, hsolv, ?_⟩
    intro N hNK hNnorm hNnil
    set K : Subgroup (MulAut W) :=
      X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) with hKdef
    have hNn : (N.subgroupOf K).Normal := by
      refine ⟨fun n hn k => ?_⟩
      have hkX : (k : MulAut W) ∈ X := k.2.1
      have hmem := hNnorm (k : MulAut W) hkX
      have hn' : (n : MulAut W) ∈ N := hn
      have h2 : (k : MulAut W) * n * (k : MulAut W)⁻¹ ∈ N := by
        have : (MulAut.conj (k : MulAut W)).toMonoidHom (n : MulAut W) ∈
            N.map (MulAut.conj (k : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn'
        rw [hmem] at this
        simpa [MulAut.conj_apply] using this
      exact h2
    have hNnilK : Group.IsNilpotent ↥(N.subgroupOf K) := by
      haveI := hNnil
      exact nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hNK).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hNK).symm.surjective
    intro n hn
    have hle := hnil (N.subgroupOf K) hNn hNnilK
    exact ⟨⟨n, hNK hn⟩, hle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem s16h_e3_l3_three_false {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1)
    (hsum : SumOfNat (fun H V Z => BinaryNaturalSL H V Z 3 1) L U ⊥ 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (hrank : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 3 E → Nat.card ↥E ≤ 27)
    (hrk3 : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 27) :
    ∀ w ∈ U, w ≠ 1 → ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, e w = w :=
  s16h_e3_l3_three_asm F hL hsum htrans hrank hrk3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
