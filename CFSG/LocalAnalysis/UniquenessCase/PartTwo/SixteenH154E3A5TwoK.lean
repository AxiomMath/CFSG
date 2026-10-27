module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Gl2K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowA5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_finite_mulAut (W : Type) [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_e3_a5_isQuasisimple {X : Type} [Group X] (h : IsAlt X 5) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by norm_num))
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hP : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      haveI := hP
      exact Group.IsPerfect.not_isMulCommutative X
        (IsMulCommutative.of_comm fun x y => by
          have hy : y ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top y
          exact Subgroup.mem_center_iff.mp hy x)
  refine ⟨hP.commutator_eq_top, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem s16h_e3_center_eq_bot_of_isAlt5 {X : Type} [Group X] (h : IsAlt X 5) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  rw [eq_bot_iff]
  intro x hx
  have hxe : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [alternatingGroup.center_eq_bot (by norm_num)] at hxe
  exact Subgroup.mem_bot.mpr
    (e.injective ((Subgroup.mem_bot.mp hxe).trans (map_one e).symm))

theorem s16h_e3_a5_two_center {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2)
    (hrank : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 3 E → Nat.card ↥E ≤ 27)
    (hrk3 : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 27)
    (hbad : ∃ w ∈ U, w ≠ 1 ∧ ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 3 E →
      (∀ e ∈ E, e w = w) → Nat.card ↥E ≤ 3) :
    ∃ Z : Subgroup (MulAut W), Nat.card ↥Z = 3 ∧ Z ≤ X ∧
      (∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ a ∈ L ⊔ L', z * a = a * z) ∧
      ∀ k ∈ X, (∀ a ∈ L ⊔ L', k * a = a * k) →
        k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹) := by
  classical
  haveI : Finite (MulAut W) := s16h_e3_finite_mulAut W
  obtain ⟨w, hwU, -, hbadw⟩ := hbad
  obtain ⟨t, -, hLt, -⟩ := F.swap
  have h60 : Nat.card ↥L = 60 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hAltL' : IsAlt ↥L' 5 := by
    obtain ⟨e⟩ := hL
    exact ⟨((L.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).trans (MulEquiv.subgroupCongr hLt)).symm.trans e⟩
  have hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1 := fun a ha hc => by
    have hmem : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.mpr fun b => Subtype.ext (hc b b.2).symm
    rw [s16h_e3_center_eq_bot_of_isAlt5 hL] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hpL : 3 ∣ Nat.card ↥L := by rw [h60]; norm_num
  have hAut : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥L) := fun h9 =>
    absurd (h9.trans (s16h_card_mulAut_alt5_dvd hL)) (by decide)
  have hrk : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 := by
    obtain ⟨E, h1, h2, h3⟩ := hrk3
    exact ⟨E, h1, h2, by rw [h3]; norm_num⟩
  obtain ⟨⟨d, hdK, hdord⟩, hnomove⟩ :=
    s16h_e3_frame_p F Nat.prime_three (by norm_num) hcen hpL hAut hrk hwU hbadw
  have hN : ∀ I : Subgroup W, AlternatingNatural L I ⊥ 5 → s16h_SimpleScalar L I ⊥ :=
    fun I hI => s16h_simpleScalar_alt5 (s16h_e3_a5_isQuasisimple hL) hL hI
  have hN' : ∀ I : Subgroup W, AlternatingNatural L' I ⊥ 5 → s16h_SimpleScalar L' I ⊥ :=
    fun I hI => s16h_simpleScalar_alt5 (s16h_e3_a5_isQuasisimple hAltL') hAltL' hI
  have hsum' : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L' U' ⊥ 2 :=
    s16h_e3_frame_sum_conj F (N := fun H V Z => AlternatingNatural H V Z 5)
      (fun f H I h => s16h_e3_alt5_conj_stable f H I h) hsum
  obtain ⟨π₁, π₂, hπ₁, hπ₂⟩ := s16h_e3_frame_cent_hom F
    (N := fun H V Z => AlternatingNatural H V Z 5) (k := 2) hN hN' hsum hsum'
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
      Set (MulAut W))), orderOf x = 3 → π₁ x ≠ 1 ∧ π₂ x ≠ 1 := by
    intro x hx
    have hx3 : (x : MulAut W) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      simpa using congrArg Subtype.val h
    have hx1 : (x : MulAut W) ≠ 1 := fun h1 => by
      have h2 : x = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hx
      omega
    obtain ⟨⟨u, hu, hxu⟩, ⟨u', hu', hxu'⟩⟩ := hnomove (x : MulAut W) x.2 hx3 hx1
    exact ⟨fun h1 => hxu ((hπ₁ x).mp h1 u hu), fun h2 => hxu' ((hπ₂ x).mp h2 u' hu')⟩
  have hd : orderOf (⟨d, hdK⟩ : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W)))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hdord
  obtain ⟨ZK, hZK3, -, hZKuniq, hZKcases⟩ := s16h_e3_gl2_K_structure π₁ π₂ hinj hno hd
  obtain ⟨hZcard, hZX, hZnorm, hZcomm⟩ := s16h_e3_frame_Z_of_unique F hZK3 hZKuniq
  refine ⟨_, hZcard, hZX, hZnorm, hZcomm, fun k hkX hkc => ?_⟩
  have hkK : k ∈ X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W)) :=
    ⟨hkX, Subgroup.mem_centralizer_iff.mpr fun a ha => (hkc a ha).symm⟩
  rcases hZKcases ⟨k, hkK⟩ with hk | ⟨hk2, hkinv⟩
  · exact Or.inl ⟨⟨k, hkK⟩, hk, rfl⟩
  · refine Or.inr ⟨by simpa using congrArg Subtype.val hk2, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa using congrArg Subtype.val (hkinv z hz)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
