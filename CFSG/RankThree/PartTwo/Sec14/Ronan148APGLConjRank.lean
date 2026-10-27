module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Rank
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCent
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Ronan148DM24
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

@[expose] def KF148U3NineE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 1 ≤ f → Sec4.IsoLThreePi X 2 f → 2 ^ f % 9 = 8 →
    ∀ x : X, x ^ 3 = 1 → ∃ E : Subgroup X, x ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9

theorem exists_e9_mem_of_isoLThreePi_two (hU : KF148U3NineE9) {X : Type} [Group X] [Finite X]
    {f : ℕ} (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X 2 f) (h91 : ¬ 9 ∣ 2 ^ f - 1) {x : X}
    (hx : x ^ 3 = 1) :
    ∃ E : Subgroup X, x ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  by_cases h8 : 2 ^ f % 9 = 8
  · exact hU X f hf hiso h8 x hx
  · have h9 : ¬ (2 ^ f % 9 = 1 ∨ 2 ^ f % 9 = 8) := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ f := ⟨_, rfl⟩
      rw [← hn] at h91 h8 h1 ⊢
      omega
    exact Ronan148W.exists_e9_mem_of_isoLThreePi hf hiso h9 hx

section Quot

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_e81_of_conj148_of_e9 {J : Subgroup G} {p f : ℕ} [Fact p.Prime]
    (hE9 : ∀ (X : Type) [Group X] [Finite X], Sec4.IsoLThreePi X p f → ∀ x : X, x ^ 3 = 1 →
      ∃ E : Subgroup X, x ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hJpi : Sec4.IsoLThreePi ↥(img148 A Y J) p f)
    (hJZ : Subgroup.center ↥(img148 A Y J) = ⊥) (x : ↥(Y ⊔ A) ⧸ ker148 A Y)
    (hDC : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {e : G} (he : e ∈ A) (he3 : e ^ 3 = 1)
    (heD : alpha148 A Y e he ∈ (img148 A Y J).map (MulAut.conj x).toMonoidHom) :
    ∃ F : Subgroup G, e ∈ F ∧ CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Jb := img148 A Y J with hJb
  set D := Jb.map (MulAut.conj x).toMonoidHom with hD
  have hDpi : Sec4.IsoLThreePi ↥D p f :=
    isoLThreePi_of_mulEquiv148 (Jb.equivMapOfInjective _ (MulAut.conj x).injective).symm hJpi
  obtain ⟨E₁', -, hE₁', hE₁9'⟩ := hE9 _ hJpi 1 (one_pow 3)
  have heα3 : (⟨alpha148 A Y e he, heD⟩ : ↥D) ^ 3 = 1 := by
    apply Subtype.ext
    have h' : (⟨e, Subgroup.mem_sup_right he⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext he3
    change (QuotientGroup.mk' (ker148 A Y) ⟨e, Subgroup.mem_sup_right he⟩) ^ 3 = 1
    rw [← map_pow, h', map_one]
  obtain ⟨E₂', heE₂', hE₂', hE₂9'⟩ := hE9 _ hDpi _ heα3
  set E₁ := E₁'.map Jb.subtype with hE₁def
  set E₂ := E₂'.map D.subtype with hE₂def
  have hE₁J : E₁ ≤ Jb := Subgroup.map_subtype_le _
  have hE₂D : E₂ ≤ D := Subgroup.map_subtype_le _
  have hE₁ : CFSG.Open.IsElemAbelian 3 E₁ := Ronan148W.isElemAbelian_map _ hE₁'
  have hE₂ : CFSG.Open.IsElemAbelian 3 E₂ := Ronan148W.isElemAbelian_map _ hE₂'
  have hE₁9 : Nat.card E₁ = 9 := by
    rw [hE₁def, Subgroup.card_map_of_injective Jb.subtype_injective, hE₁9']
  have hE₂9 : Nat.card E₂ = 9 := by
    rw [hE₂def, Subgroup.card_map_of_injective D.subtype_injective, hE₂9']
  have heE₂ : alpha148 A Y e he ∈ E₂ := ⟨_, heE₂', rfl⟩
  have hcomm : ∀ s ∈ E₁, ∀ t ∈ E₂, s * t = t * s := fun s hs t ht =>
    Subgroup.mem_centralizer_iff.mp (hDC (hE₂D ht)) s (hE₁J hs)
  set E := E₁ ⊔ E₂ with hE
  have hEab : CFSG.Open.IsElemAbelian 3 E := Ronan148W.isElemAbelian_sup_of_commute hE₁ hE₂ hcomm
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzJ : z ∈ Jb := hE₁J hz.1
    have hzZ : (⟨z, hzJ⟩ : ↥Jb) ∈ Subgroup.center ↥Jb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDC (hE₂D hz.2)) g g.2)
    rw [hJZ, Subgroup.mem_bot] at hzZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzZ
  have hcard := Sec6.card_sup_mul_card_inf (Ronan148W.le_normalizer_of_commute hcomm)
  rw [hinf, Subgroup.card_bot, mul_one, hE₁9, hE₂9] at hcard
  set φ : ↥(Y ⊔ A) →* ↥(Y ⊔ A) ⧸ ker148 A Y := QuotientGroup.mk' (ker148 A Y) with hφ
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hφ, QuotientGroup.ker_mk']
    exact Main148.not_three_dvd_card_ker148
  have hEU : E ≤ (⊤ : Subgroup ↥(Y ⊔ A)).map φ := by
    intro z _
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) z
    exact ⟨w, trivial, rfl⟩
  set e' : ↥(Y ⊔ A) := ⟨e, Subgroup.mem_sup_right he⟩ with he'
  have he'3 : e' ^ 3 = 1 := Subtype.ext he3
  have hDE : (Subgroup.zpowers e').map φ ≤ E := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right heE₂
  have hDp : IsPGroup 3 (Subgroup.zpowers e') := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact (Ronan148W.isElemAbelian_zpowers he'3).2 g g.2)⟩
  obtain ⟨T, -, hDT, -, hT81, hT⟩ :=
    Ronan148D.exists_lift_elemAbelian Nat.prime_three φ hker hEU hEab le_top hDE hDp
  refine ⟨T.map (Y ⊔ A).subtype, ⟨e', hDT (Subgroup.mem_zpowers e'), rfl⟩,
    Ronan148W.isElemAbelian_map _ hT, ?_⟩
  rw [Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, hT81, hcard]

end Quot


theorem step148PGLConjOmega2_of_rank (hR : Ronan148W.Step148OmegaRankThree)
    (hU : KF148U3NineE9) : Step148PGLConjOmega2 := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq f hf h91 hpgl heΩ
    hLeA hX1 y hy D hDne hDC hAD heD hVc hVex a₀ ha₀ ha₀1 ha₀J
  exfalso
  letI := ker148_normal hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.mem_partTwoF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  haveI : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  haveI hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hDne
    show (img148 A Y J).map _ = img148 A Y J
    rw [hbot, Subgroup.map_bot]
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
  have hJs : IsSimpleGroup ↥(img148 A Y J) :=
    (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hf hJpi).1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  obtain ⟨F, heF, hF, hF81⟩ := exists_e81_of_conj148_of_e9
    (fun X _ _ hX x hx => exists_e9_mem_of_isoLThreePi_two hU hf hX h91 hx) hJpi hJZ _ hDC he
    (hA3 e he) heD
  have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 f := by
    rw [show img148 A Y K = img148 A Y J from hEq]
    exact hJpi
  exact hR G A c L h e he heΩ Le hLeA (Ronan148W.isLThreePi_of_kType148 hkt hf hKpi) F heF hF
    hF81

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
