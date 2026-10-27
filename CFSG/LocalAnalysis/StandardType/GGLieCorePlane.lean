module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem ggLiePlane_exists_generators {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 2) :
    ∃ x y : G, x ∈ A ∧ y ∈ A ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x ∧
      A = Subgroup.closure ({x, y} : Set G) := by
  classical
  haveI : Finite ↥A :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hcard_gt : 1 < Nat.card A := by
    rw [hcard]
    exact Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt
  have hne_bot : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).mp hcard_gt
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne_bot
  obtain ⟨x, hx, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial A
  have hxp : x ^ p = 1 := hel.2 x hx
  have hxorder : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf x) (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxne
    · exact h
  have hcard_zx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxorder]
  have hlt : Nat.card (Subgroup.zpowers x) < Nat.card A := by
    rw [hcard_zx, hcard, pow_two]
    exact Nat.lt_mul_self_iff.mpr hp.one_lt
  have hnotle : ¬ A ≤ Subgroup.zpowers x := by
    intro hle
    have heq : Subgroup.zpowers x = A := le_antisymm (Subgroup.zpowers_le.mpr hx) hle
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨y, hyA, hyzx⟩ :=
    Set.not_subset.mp (show ¬ (A : Set G) ⊆ (Subgroup.zpowers x : Set G) from hnotle)
  set B : Subgroup G := Subgroup.closure ({x, y} : Set G) with hB
  have hxB : x ∈ B := by rw [hB]; exact Subgroup.subset_closure (by simp)
  have hyB : y ∈ B := by rw [hB]; exact Subgroup.subset_closure (by simp)
  have hBle : B ≤ A := by
    rw [hB]
    refine (Subgroup.closure_le A).2 ?_
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hyA
  have hzxB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hxB
  have hBne : B ≠ Subgroup.zpowers x := by
    intro h
    exact hyzx (h ▸ hyB)
  have hpdvd : p ∣ Nat.card B := by
    have h := Subgroup.card_dvd_of_le hzxB
    rwa [hcard_zx] at h
  have hBdvd : Nat.card B ∣ p ^ 2 := by
    have h := Subgroup.card_dvd_of_le hBle
    rwa [hcard] at h
  have hBcard : Nat.card B = p ^ 2 := by
    obtain ⟨d, hd⟩ := hpdvd
    have hdp : d ∣ p := by
      have h' : p * d ∣ p * p := by
        rw [← hd]
        simpa [pow_two] using hBdvd
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos h'
    rcases hp.eq_one_or_self_of_dvd d hdp with h1 | h1
    · exfalso
      rw [h1, mul_one] at hd
      haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hd]; exact hp.ne_zero)
      have heq : B = Subgroup.zpowers x := by
        refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers x) (K := B) hzxB ?_).symm
        rw [hd, hcard_zx]
      exact hBne heq
    · rw [h1] at hd
      rw [hd, pow_two]
  have hBA : B = A := Subgroup.eq_of_le_of_card_ge hBle (by rw [hcard, hBcard])
  refine ⟨x, y, hx, hyA, hxne, hyzx, ?_⟩
  exact hB ▸ hBA.symm

private theorem ggLiePlane_exists_generators_le_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hfin : Finite A) (hel : IsElemAbelian p A) (hcard : Nat.card A ≤ p ^ 2) :
    ∃ x y : G, x ∈ A ∧ y ∈ A ∧ A = Subgroup.closure ({x, y} : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite A := hfin
  have hisP : IsPGroup p A := by
    intro y
    have hy : y ^ p = 1 := Subtype.ext (by simpa using hel.2 y y.2)
    have h1 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact ⟨0, by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp h⟩
    · exact ⟨1, by rw [pow_one]; exact hy⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hisP
  have hk2 : k ≤ 2 := by
    have h := hcard
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl
  · have hbot : A = ⊥ := by
      apply Subgroup.card_eq_one.mp
      simpa using hk
    exact ⟨1, 1, by rw [hbot]; exact Subgroup.mem_bot.mpr rfl,
      by rw [hbot]; exact Subgroup.mem_bot.mpr rfl,
      by rw [hbot]; exact (Subgroup.closure_eq_bot_iff.mpr (by simp)).symm⟩
  · have hcardp : Nat.card A = p := by simpa using hk
    have hAne : A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcardp
      exact hp.ne_one hcardp.symm
    obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have hgen : Subgroup.zpowers x = A := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA) ?_
      simp [hcardp, Nat.card_zpowers,
        orderOf_eq_prime (hel.2 x hxA) (fun h => hx1 (Subtype.ext h))]
    refine ⟨x, 1, hxA, Subgroup.one_mem _, ?_⟩
    refine hgen.symm.trans ?_
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro z (hz | hz)
      · rw [hz]; exact Subgroup.mem_zpowers x
      · rw [hz]; exact Subgroup.one_mem _
  · obtain ⟨x, y, hx, hy, _hxne, _hyzx, hAeq⟩ := ggLiePlane_exists_generators hp hel hk
    exact ⟨x, y, hx, hy, hAeq⟩

theorem ggLieFrame_le_sq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} (hf : 1 ≤ f)
    {Φ : ModGL τ L →* ModGL τ L} (hΦ : IsSteinbergEnd τ L (2 ^ f) Φ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (ModGL τ L)} (hA : A ≤ ratPoints Φ)
    (hel : IsElemAbelian p A) (hcard : Nat.card A ≤ p ^ 2) (hT : IsToralSubgroup τ L A) :
    ∃ (w : WeylGroup τ) (g : ModGL τ L) (hg : g ∈ adjointGroup τ L)
      (hlang : Φ g = g * canonicalRep (coxeterSystem τ) L w) (a₁ a₂ : Fin τ.rank → Lˣ),
      (ratPoints Φ).map (MulAut.conj g⁻¹).toMonoidHom =
        (langDatumOfPosition hΦ w g hg hlang).model ∧
      rootDiagUnit τ a₁ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
      rootDiagUnit τ a₂ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
      rootDiagUnit τ a₁ ^ p = 1 ∧ rootDiagUnit τ a₂ ^ p = 1 ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom =
        Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} := by
  classical
  have hfin : Finite ↥(ratPoints Φ) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  have hAfin : Finite A :=
    (Set.toFinite (ratPoints Φ : Set (ModGL τ L))).subset (fun x hx => hA hx) |>.to_subtype
  obtain ⟨w, g, hg, hlang, hA'le⟩ :=
    ggLieLangPosition_holds τ (isExcTag τ) L f hf Φ (isSteinbergEndZ_of_isSteinbergEnd hΦ)
      hfin p hp hp2 A hA hel hT
  obtain ⟨hmodel, htorus⟩ := langDatumOfPosition_transport hΦ w g hg hlang hA'le
  obtain ⟨x, y, hx, hyA, hAeq⟩ := ggLiePlane_exists_generators_le_sq hp hAfin hel hcard
  have hx' : (MulAut.conj g⁻¹).toMonoidHom x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hy' : (MulAut.conj g⁻¹).toMonoidHom y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.mem_map.2 ⟨y, hyA, rfl⟩
  have hxT : (MulAut.conj g⁻¹).toMonoidHom x ∈
      (langDatumOfPosition hΦ w g hg hlang).torus := htorus hx'
  have hyT : (MulAut.conj g⁻¹).toMonoidHom y ∈
      (langDatumOfPosition hΦ w g hg hlang).torus := htorus hy'
  obtain ⟨a₁, ha₁⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hxT).1
  obtain ⟨a₂, ha₂⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hyT).1
  have hmap : A.map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} := by
    rw [hAeq, MonoidHom.map_closure]
    congr 1
    rw [Set.image_insert_eq, Set.image_singleton, ha₁, ha₂]
  exact ⟨w, g, hg, hlang, a₁, a₂, hmodel,
    by rw [← ha₁]; exact hxT, by rw [← ha₂]; exact hyT,
    by rw [← ha₁, ← map_pow, hel.2 x hx, map_one],
    by rw [← ha₂, ← map_pow, hel.2 y hyA, map_one],
    hmap⟩

theorem ggLiePlaneFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} (hf : 1 ≤ f)
    {Φ : ModGL τ L →* ModGL τ L} (hΦ : IsSteinbergEnd τ L (2 ^ f) Φ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (ModGL τ L)} (hA : A ≤ ratPoints Φ)
    (hel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 2) (hT : IsToralSubgroup τ L A) :
    ∃ (w : WeylGroup τ) (g : ModGL τ L) (hg : g ∈ adjointGroup τ L)
      (hlang : Φ g = g * canonicalRep (coxeterSystem τ) L w) (a₁ a₂ : Fin τ.rank → Lˣ),
      (ratPoints Φ).map (MulAut.conj g⁻¹).toMonoidHom =
        (langDatumOfPosition hΦ w g hg hlang).model ∧
      rootDiagUnit τ a₁ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
      rootDiagUnit τ a₂ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
      rootDiagUnit τ a₁ ^ p = 1 ∧ rootDiagUnit τ a₂ ^ p = 1 ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom =
        Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} :=
  ggLieFrame_le_sq hf hΦ hp hp2 hA hel hcard.le hT

end CFSG.StandardType.LieCore
