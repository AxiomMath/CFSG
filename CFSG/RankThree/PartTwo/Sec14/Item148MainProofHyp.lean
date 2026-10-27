module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Main148

theorem isElemAbelian_map148 {Γ Γ' : Type*} [Group Γ] [Group Γ'] {p : ℕ} {E : Subgroup Γ}
    (hE : CFSG.Assembly.IsElemAbelian p E) (f : Γ →* Γ') :
    CFSG.Assembly.IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_of_le148 {Γ : Type*} [Group Γ] {p : ℕ} {E F : Subgroup Γ}
    (hF : CFSG.Assembly.IsElemAbelian p F) (hEF : E ≤ F) : CFSG.Assembly.IsElemAbelian p E :=
  CFSG.Open.IsElemAbelian.mono hF hEF

theorem mem_of_coprime_three_of_mem_sup {Γ : Type*} [Group Γ] [Finite Γ] {L Â : Subgroup Γ}
    (hÂL : Â ≤ Subgroup.normalizer (L : Set Γ)) (hÂ3 : ∀ a ∈ Â, a ^ 3 = 1) {g : Γ}
    (hg : g ∈ L ⊔ Â) (hcop : Nat.Coprime 3 (orderOf g)) : g ∈ L := by
  have hgC : g ∈ (L : Set Γ) * (Â : Set Γ) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Â hÂL]
    exact hg
  obtain ⟨l, hl, a, ha, hla⟩ := hgC
  have hla' : l * a = g := hla
  have hg3 : g ^ 3 ∈ L := by
    have e1 : g ^ 3 = l * (a * l * a⁻¹) * (a * a * l * a⁻¹ * a⁻¹) * (a ^ 3) := by
      rw [← hla', pow_succ, pow_succ, pow_succ, pow_zero, one_mul, pow_succ, pow_succ, pow_succ,
        pow_zero, one_mul]
      group
    rw [e1, hÂ3 a ha, mul_one]
    have h1 : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hÂL ha) l).mp hl
    have h2 : a * a * l * a⁻¹ * a⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hÂL ha) _).mp h1
      simpa [mul_assoc] using this
    exact L.mul_mem (L.mul_mem hl h1) h2
  exact (Subgroup.zpowers_le.mpr hg3) (mem_zpowers_pow_three hcop)

theorem localRank_le_of_top_eq_sup {Γ : Type*} [Group Γ] [Finite Γ] {L Â : Subgroup Γ}
    (hÂL : Â ≤ Subgroup.normalizer (L : Set Γ)) (htop : L ⊔ Â = ⊤) (hÂ3 : ∀ a ∈ Â, a ^ 3 = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    localRank p Γ ≤ localRank p ↥L := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ g : Γ, Nat.Coprime 3 (orderOf g) → g ∈ L := fun g hg =>
    mem_of_coprime_three_of_mem_sup hÂL hÂ3 (htop ▸ Subgroup.mem_top g) hg
  refine csSup_le' ?_
  rintro k ⟨H, ⟨U, hU0, hU2, rfl⟩, rfl⟩
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (U : Set Γ))
  have hEL : E ≤ L := by
    intro x hx
    refine hmem x ?_
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    exact Nat.Coprime.coprime_dvd_right h1 ((Nat.coprime_primes Nat.prime_three hp).mpr
      (Ne.symm hp3))
  have hUL : U ≤ L := by
    intro x hx
    refine hmem x ?_
    obtain ⟨n, hn⟩ := hU2 ⟨x, hx⟩
    have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hn)
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right n (by norm_num))
  set E' := E.subgroupOf L with hE'def
  set U' := U.subgroupOf L with hU'def
  have hE'card : Nat.card E' = p ^ CFSG.Open.pRank p (Subgroup.normalizer (U : Set Γ)) := by
    rw [hE'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hEcard]
  have hE' : CFSG.Assembly.IsElemAbelian p E' := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨((x : ↥L) : Γ), x.2⟩
        ⟨((y : ↥L) : Γ), y.2⟩)
      simpa using h
    · simpa using hE.2 _ hx
  have hE'U' : E' ≤ Subgroup.normalizer (U' : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := Subgroup.mem_normalizer_iff.mp (hEH hx) (u : Γ)
    simp only [hU'def, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU0 ((Subgroup.card_eq_one).mp hm)
  have hcop : Nat.Coprime p (Nat.card U') := by
    rw [hU'card, hm]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h2 : 2 ∣ Nat.card U' := by
    rw [hU'card, hm]
    exact dvd_pow_self 2 hm0
  exact CFSG.RankThree.Classical2.le_localRank_of_normalizes hp hE'U' hE' hE'card hcop h2

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem nonempty_img148_section_equiv (X : Subgroup G) :
    Nonempty (↥(X.subgroupOf (Y ⊔ A)) ⧸ (ker148 A Y).subgroupOf (X.subgroupOf (Y ⊔ A)) ≃*
      ↥(img148 A Y X)) := by
  set H := X.subgroupOf (Y ⊔ A) with hH
  set ψ : ↥H →* ↥(Y ⊔ A) ⧸ ker148 A Y := (QuotientGroup.mk' (ker148 A Y)).comp H.subtype
    with hψ
  have hker : ψ.ker = (ker148 A Y).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hrange : ψ.range = img148 A Y X := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

omit [(ker148 A Y).Normal] in
theorem not_three_dvd_card_ker148 : ¬ 3 ∣ Nat.card ↥(ker148 A Y) := by
  have hle : pPrimeCoreOf 3 Y ≤ Y ⊔ A := (pPrimeCoreOf_le 3 Y).trans le_sup_left
  have hc : Nat.card ↥(ker148 A Y) = Nat.card ↥(pPrimeCoreOf 3 Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hc]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)

theorem eq_of_mem_partTwoE_of_le (hEF : partTwoF G = partTwoE G)
    {C : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} {E B : Subgroup ↥C} (hE : E ∈ partTwoE ↥C)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hEB : E ≤ B) : B = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := ker148 A Y with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_ker148
  obtain ⟨hEab, hE27, U, hU0, hU2, hEU⟩ := hE
  set Bh := B.map C.subtype with hBh
  set Eh := E.map C.subtype with hEh
  have hBhab : CFSG.Assembly.IsElemAbelian 3 Bh := isElemAbelian_map148 hB C.subtype
  obtain ⟨S, hSB, hS, hScard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN3 hBhab
  have hScardB : Nat.card S = Nat.card B := by
    rw [hScard, hBh, Subgroup.card_map_of_injective C.subtype_injective]
  have hS3 : IsPGroup 3 S := fun x => ⟨1, Subtype.ext (by simpa using hS.2 x x.2)⟩
  have hSN : S ⊓ N = ⊥ := CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hN3 hS3
  have hinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : b⁻¹ * a ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      have := N.inv_mem hab
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : b⁻¹ * a ∈ S ⊓ N := ⟨S.mul_mem (S.inv_mem hb) ha, h1⟩
    rw [hSN, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  have hSmap : S.map π = Bh := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr hSB) ?_
    rw [← hScard]
    have hcard : Nat.card (S.map π) = Nat.card S := by
      refine Nat.card_congr (Equiv.ofBijective (fun s : S => (⟨π s, s, s.2, rfl⟩ : S.map π))
        ⟨fun s t hst => Subtype.ext (hinj s s.2 t t.2 (congrArg Subtype.val hst)), ?_⟩).symm
      rintro ⟨_, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    exact hcard.ge
  set SE := S ⊓ Eh.comap π with hSE
  have hEhBh : Eh ≤ Bh := Subgroup.map_mono hEB
  have hSEmap : SE.map π = Eh := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact hs.2
    · intro x hx
      have hxB : x ∈ S.map π := hSmap ▸ hEhBh hx
      obtain ⟨s, hs, rfl⟩ := hxB
      exact ⟨s, ⟨hs, hx⟩, rfl⟩
  have hSEcard : Nat.card SE = 27 := by
    have hcard : Nat.card (SE.map π) = Nat.card SE := by
      refine Nat.card_congr (Equiv.ofBijective (fun s : SE => (⟨π s, s, s.2, rfl⟩ : SE.map π))
        ⟨fun s t hst => Subtype.ext (hinj s s.2.1 t t.2.1 (congrArg Subtype.val hst)), ?_⟩).symm
      rintro ⟨_, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    rw [← hcard, hSEmap, hEh, Subgroup.card_map_of_injective C.subtype_injective, hE27]
  have hSEab : CFSG.Assembly.IsElemAbelian 3 SE := isElemAbelian_of_le148 hS inf_le_left
  have hSE3 : IsPGroup 3 SE := fun x => ⟨1, Subtype.ext (by simpa using hSEab.2 x x.2)⟩
  set Uh := U.map C.subtype with hUh
  set D := Uh.comap π with hD
  have hSED : SE ≤ Subgroup.normalizer (D : Set ↥(Y ⊔ A)) := by
    intro s hs
    obtain ⟨e, he, hes⟩ := hs.2
    have heN : C.subtype e ∈ Subgroup.normalizer (Uh : Set (↥(Y ⊔ A) ⧸ N)) :=
      Subgroup.le_normalizer_map C.subtype ⟨e, hEU he, rfl⟩
    rw [hes] at heN
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have h := Subgroup.mem_normalizer_iff.mp heN (π d)
    change π d ∈ Uh ↔ π (s * d * s⁻¹) ∈ Uh
    rw [map_mul, map_mul, map_inv]
    exact h
  have hDcard : Nat.card D = Nat.card N * Nat.card Uh :=
    QuotientGroup.card_preimage_mk N (Uh : Set (↥(Y ⊔ A) ⧸ N))
  have hUhcard : Nat.card Uh = Nat.card U := Subgroup.card_map_of_injective C.subtype_injective
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU0 ((Subgroup.card_eq_one).mp hm)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hUhcard, hm]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hUhcard, hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  obtain ⟨T, hSET, hT0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two SE D hSE3 hSED hcop h2
  set f := (Y ⊔ A).subtype with hf
  set T' := (T : Subgroup D).map D.subtype with hT'
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map D.subtype
  have hSG : SE.map f ∈ partTwoE G := by
    refine ⟨isElemAbelian_map148 hSEab f, ?_, T'.map f, ?_, hT'2.map f, ?_⟩
    · rw [Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, hSEcard]
    · exact fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective _ (Y ⊔ A).subtype_injective).mp h)
    · exact (Subgroup.map_mono hSET).trans (Subgroup.le_normalizer_map f)
  rw [← hEF] at hSG
  have hmax := hSG.2.1 (S.map f) (isElemAbelian_map148 hS f) (Subgroup.map_mono inf_le_left)
  have hcardS : Nat.card S = Nat.card SE := by
    have h1 : Nat.card (S.map f) = Nat.card S :=
      Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective
    have h2 : Nat.card (SE.map f) = Nat.card SE :=
      Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective
    rw [← h1, ← h2, hmax]
  refine (Subgroup.eq_of_le_of_card_ge hEB ?_).symm
  rw [← hScardB, hcardS, hSEcard, hE27]

theorem partTwoE_eq_partTwoF_of_le (hEF : partTwoF G = partTwoE G)
    (C : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) : partTwoE ↥C = partTwoF ↥C := by
  ext E'
  constructor
  · intro hE
    exact ⟨hE.1, fun B hB hEB => eq_of_mem_partTwoE_of_le hEF hE hB hEB, E', hE, le_rfl⟩
  · rintro ⟨hE'ab, -, E, hE, hEE'⟩
    rw [eq_of_mem_partTwoE_of_le hEF hE hE'ab hEE']
    exact hE

end Quot

end Main148

open Main148

theorem hyp429In148_of (h1 : Sec4.Item4_1LargePrime) : Hyp429In148 := by
  intro G _ _ A c L h Y hY hs J hJ hAJ h3J
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJ1 : J ≠ ⊥ := by
    intro hJb
    rw [hJb, Subgroup.card_bot] at h3J
    norm_num at h3J
  have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · exact hJ1 (le_bot_iff.mp (hY1 ▸ hJY))
    · exact hY.1 hYt
  have hX4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hN3 : ¬ 3 ∣ Nat.card ↥(ker148 A Y) := not_three_dvd_card_ker148
  set C := img148 A Y (J ⊔ A) with hCdef
  have hCeq : C = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hLC : img148 A Y J ≤ C := img148_mono le_sup_left
  have hAC : img148 A Y A ≤ C := img148_mono le_sup_right
  obtain ⟨eC⟩ := nonempty_img148_section_equiv (A := A) (Y := Y) (J ⊔ A)
  have hK : IsKGroup ↥C :=
    CFSG.SectionRank.K_group_section_closure_inCatalog hX4.kGroup _ _ eC
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p ↥C < 3 := by
    intro p hp hp3
    obtain ⟨eJ⟩ := nonempty_img148_section_equiv (A := A) (Y := Y) J
    have hJq := (img148_isQuasisimple (A := A) (Y := Y) hJ h3J).1
    have hNJ3 : ¬ 3 ∣ Nat.card ↥((ker148 A Y).subgroupOf (J.subgroupOf (Y ⊔ A))) := fun h3 =>
      hN3 (h3.trans (Sec4.Item41Narrow.card_subgroupOf_dvd _ _))
    have hJ4 := Sec4.Item41Narrow.sectionFourHyp_section h1 hX4 (J.subgroupOf (Y ⊔ A)) _ hNJ3
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hJq)
    have hJlt : localRank p ↥(img148 A Y J) < 3 := by
      rw [← Census.localRank_eq_of_mulEquiv eJ hp]
      exact hJ4.localRank_lt p hp hp3
    set L' := (img148 A Y J).subgroupOf C with hL'
    set Â' := (img148 A Y A).subgroupOf C with hÂ'
    have hÂ'L' : Â' ≤ Subgroup.normalizer (L' : Set ↥C) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := Subgroup.mem_normalizer_iff.mp (hAαJα hx) (y : ↥(Y ⊔ A) ⧸ ker148 A Y)
      simp only [hL', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact h
    have htop : L' ⊔ Â' = ⊤ := by
      rw [hL', hÂ', ← Subgroup.subgroupOf_sup hLC hAC, ← hCeq, Subgroup.subgroupOf_self]
    have hÂ'3 : ∀ a ∈ Â', a ^ 3 = 1 := fun a ha => Subtype.ext (by simpa using hAα3 _ ha)
    have hle := localRank_le_of_top_eq_sup hÂ'L' htop hÂ'3 hp (by omega) (by omega)
    rw [Census.localRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC) hp] at hle
    exact hle.trans_lt hJlt
  refine ⟨⟨hK, Sec4.Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩,
    partTwoE_eq_partTwoF_of_le
      ((h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1) C⟩
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact ((localRank_subgroup_le Nat.prime_three C).trans
      (CFSG.RankThree.Classical2.localRank_quotient_le Nat.prime_three (by norm_num) _ hN3)).trans
      ((CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans
        hX4.evenRank_le)
  · exact (hlt p hp hp3).le

section Certificates


theorem step148Lift429_of_item4_1
    (h429 : Sec4.Item4_29) (h1 : Sec4.Item4_1LargePrime)
    (hEps : Step148Lift429Eps) : Step148Lift429 :=
  step148Lift429_of h429 (hyp429In148_of h1) hEps

end Certificates

end CFSG.RankThree.PartTwo.Sec14
