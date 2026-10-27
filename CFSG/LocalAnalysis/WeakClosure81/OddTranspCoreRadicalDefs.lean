module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def RadicalOutcome (Y : Type) [Group Y] (t : Y) : Prop :=
  CoreStar.HasCoreStar Y t ∨
    ∃ L : Subgroup Y, ∃ htL : t ∈ L,
      Subgroup.normalClosure ({⟨t, htL⟩} : Set ↥L) = ⊤ ∧
      Nat.card ↥(Subgroup.center ↥L) ∣ 2 ∧
      ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥L ⧸ Subgroup.center ↥L) n

private def HasSubgroupOutcome (Y : Type) [Group Y] (t : Y) : Prop :=
  ∃ L : Subgroup Y, ∃ htL : t ∈ L,
    Subgroup.normalClosure ({⟨t, htL⟩} : Set ↥L) = ⊤ ∧
    Nat.card ↥(Subgroup.center ↥L) ∣ 2 ∧
    ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥L ⧸ Subgroup.center ↥L) n

private theorem HasSubgroupOutcome.map {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {t : G} (h : HasSubgroupOutcome G t) :
    HasSubgroupOutcome H (φ t) := by
  obtain ⟨L, htL, hncl, hZ, n, hn, hL2⟩ := h
  have htL' : φ t ∈ L.map φ := Subgroup.mem_map_of_mem φ htL
  let ψ : ↥L ≃* ↥(L.map φ) := Subgroup.equivMapOfInjective L φ hφ
  have hψ : ψ.toMonoidHom ⟨t, htL⟩ = ⟨φ t, htL'⟩ := Subtype.ext rfl
  refine ⟨L.map φ, htL', ?_, ?_, n, hn, ?_⟩
  · have hmap := Subgroup.map_normalClosure ({⟨t, htL⟩} : Set ↥L) ψ.toMonoidHom ψ.surjective
    rw [hncl, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective, Set.image_singleton,
      hψ] at hmap
    exact hmap.symm
  · rw [← Nat.card_congr (Subgroup.centerCongr ψ).toEquiv]
    exact hZ
  · let e := QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.map φ)) ψ
      (Subgroup.map_center_eq ψ)
    exact hL2.imp (CFSG.Quasithin.IsPSL.of_mulEquiv e) (CFSG.Quasithin.IsSz.of_mulEquiv e)

variable {Y Y' : Type} [Group Y] [Group Y']

theorem RadicalOutcome.of_mulEquiv (e : Y ≃* Y') {t : Y} (h : RadicalOutcome Y' (e t)) :
    RadicalOutcome Y t := by
  rcases h with h | h
  · exact Or.inl (by
      simpa using CoreStar.hasCoreStar_map e.symm.toMonoidHom e.symm.injective h)
  · have h' := HasSubgroupOutcome.map e.symm.toMonoidHom e.symm.injective h
    rw [show e.symm.toMonoidHom (e t) = t from by simp] at h'
    exact Or.inr h'

theorem RadicalOutcome.of_le {H : Subgroup Y} {t : Y} (ht : t ∈ H)
    (h : RadicalOutcome ↥H ⟨t, ht⟩) : RadicalOutcome Y t := by
  rcases h with h | h
  · exact Or.inl (by
      simpa using CoreStar.hasCoreStar_map H.subtype H.subtype_injective h)
  · exact Or.inr (HasSubgroupOutcome.map H.subtype H.subtype_injective h)

theorem RadicalOutcome.of_isConj {t t' : Y} (hc : IsConj t t') (h : RadicalOutcome Y t') :
    RadicalOutcome Y t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  exact RadicalOutcome.of_mulEquiv (MulAut.conj g) (by simpa [MulAut.conj_apply, hg] using h)

theorem RadicalOutcome.of_top {t : Y} (hncl : Subgroup.normalClosure ({t} : Set Y) = ⊤)
    (hZ : Nat.card ↥(Subgroup.center Y) ∣ 2) {n : ℕ} (hn : 1 < n)
    (h : IsL2OrSz (Y ⧸ Subgroup.center Y) n) : RadicalOutcome Y t := by
  let e : ↥(⊤ : Subgroup Y) ≃* Y := Subgroup.topEquiv
  have hncl' : Subgroup.normalClosure ({⟨t, Subgroup.mem_top t⟩} : Set ↥(⊤ : Subgroup Y)) = ⊤ := by
    have hmap := Subgroup.map_normalClosure ({⟨t, Subgroup.mem_top t⟩} : Set ↥(⊤ : Subgroup Y))
      e.toMonoidHom e.surjective
    rw [Set.image_singleton] at hmap
    have himg : e.toMonoidHom ⟨t, Subgroup.mem_top t⟩ = t := rfl
    rw [himg, hncl] at hmap
    exact Subgroup.map_injective e.injective
      (hmap.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm)
  have hZ' : Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup Y)) ∣ 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ
  let e' := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center ↥(⊤ : Subgroup Y)) e.symm
    (Subgroup.map_center_eq e.symm)
  have hL2' : IsL2OrSz (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)) n :=
    h.imp (CFSG.Quasithin.IsPSL.of_mulEquiv e') (CFSG.Quasithin.IsSz.of_mulEquiv e')
  exact Or.inr ⟨⊤, Subgroup.mem_top t, hncl', hZ', n, hn, hL2'⟩

theorem RadicalOutcome.of_center_eq_bot (hZ : Subgroup.center Y = ⊥) {t : Y}
    (h : RadicalOutcome (Y ⧸ Subgroup.center Y) (QuotientGroup.mk t)) : RadicalOutcome Y t := by
  let e : Y ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have he : e t = QuotientGroup.mk t := by simp [e]
  exact RadicalOutcome.of_mulEquiv e (by simpa [he] using h)

theorem RadicalOutcome.of_surjective_sl2 {L : Subgroup Y} {t : Y} (htL : t ∈ L)
    (hncl : Subgroup.normalClosure ({⟨t, htL⟩} : Set ↥L) = ⊤) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center ↥L) (hker2 : Nat.card ↥ρ.ker ∣ 2) :
    RadicalOutcome Y t := by
  have hCharP : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    @CFSG.Walter.sl2_center_eq_bot_of_charTwo F _ hCharP
  have hcenter_le : Subgroup.center ↥L ≤ ρ.ker := by
    intro z hz
    have hz' : ρ z ∈ Subgroup.map ρ (Subgroup.center ↥L) := ⟨z, hz, rfl⟩
    have hz'' := Subgroup.map_center_le_center hρ hz'
    rwa [hcenterSL, Subgroup.mem_bot] at hz''
  have hZ : Subgroup.center ↥L = ρ.ker := le_antisymm hcenter_le hker
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    ((QuotientGroup.quotientMulEquivOfEq hcenterSL).trans
      QuotientGroup.quotientBot).symm
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := ρ) hρ)
  have hPSL : IsL2OrSz (↥L ⧸ Subgroup.center ↥L) n := by
    refine Or.inl ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
      ?_⟩
    · intro h2
      have h2' : 2 ^ n = 2 := congrArg Prod.snd h2
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · intro h2
      have h2' : 2 ^ n = 3 := congrArg Prod.snd h2
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact ⟨e.trans (eSL.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩
  exact Or.inr ⟨L, htL, hncl, by rw [hZ]; exact hker2, n, hn, hPSL⟩

theorem RadicalOutcome.of_injective_sl2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (φ : Matrix.SpecialLinearGroup (Fin 2) F →* Y)
    (hφ : Function.Injective φ) {t : Y} (ht : t ∈ φ.range) (ht1 : t ≠ 1) :
    RadicalOutcome Y t := by
  have hCharP : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    @CFSG.Walter.sl2_center_eq_bot_of_charTwo F _ hCharP
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSimplePSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    ((QuotientGroup.quotientMulEquivOfEq hcenterSL).trans QuotientGroup.quotientBot).symm
  have hSimpleSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hSimplePSL eSL
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥φ.range :=
    MonoidHom.ofInjective (f := φ) hφ
  have hSimpleRange : IsSimpleGroup ↥φ.range :=
    @MulEquiv.isSimpleGroup _ _ _ _ hSimpleSL e.symm
  have hnc : Subgroup.normalClosure ({⟨t, ht⟩} : Set ↥φ.range) = ⊤ := by
    have hmem : (⟨t, ht⟩ : ↥φ.range) ∈ Subgroup.normalClosure ({⟨t, ht⟩} : Set ↥φ.range) :=
      Subgroup.subset_normalClosure (Set.mem_singleton _)
    have hne : (⟨t, ht⟩ : ↥φ.range) ≠ 1 := fun h' => ht1 (congrArg Subtype.val h')
    rcases @Subgroup.Normal.eq_bot_or_eq_top ↥φ.range _ hSimpleRange
      (Subgroup.normalClosure ({⟨t, ht⟩} : Set ↥φ.range))
      Subgroup.normalClosure_normal with hbot | htop
    · rw [hbot, Subgroup.mem_bot] at hmem
      exact absurd hmem hne
    · exact htop
  have hker_bot : e.symm.toMonoidHom.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact e.symm.injective (by simpa using MonoidHom.mem_ker.mp hz)
  refine RadicalOutcome.of_surjective_sl2 ht hnc hF hn e.symm.toMonoidHom e.symm.surjective ?_ ?_
  · rw [hker_bot]
    exact bot_le
  · rw [hker_bot, Subgroup.card_bot]
    norm_num

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
