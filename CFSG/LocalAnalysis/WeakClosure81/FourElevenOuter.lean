module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover
public import CFSG.Dihedral.Glauberman.DicksonMaxQuaternion
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Quasithin.E2P.Asc80
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q]

theorem nonempty_pgl2_of_inf_centralizer {L : Subgroup Q} [L.Normal] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {b : Q}
    (hpsl2 : Nonempty (↥⁅L ⊓ centralizer ({b} : Set Q),
        L ⊓ centralizer ({b} : Set Q)⁆ ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hbot : L ⊓ centralizer ((⁅L ⊓ centralizer ({b} : Set Q),
      L ⊓ centralizer ({b} : Set Q)⁆ : Subgroup Q) : Set Q) = ⊥)
    (hcard : Nat.card ↥(L ⊓ centralizer ({b} : Set Q)) = p * (p ^ 2 - 1)) :
    Nonempty (↥(L ⊓ centralizer ({b} : Set Q)) ≃*
      CFSG.GorensteinWalter.PGL2 (ZMod p)) := by
  set H : Subgroup Q := L ⊓ centralizer ({b} : Set Q) with hH
  have hNle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_self H
  have hNnormal : (⁅H, H⁆.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr
      (Subgroup.normalizer_commutator_ge_left H H)
  obtain ⟨eΩ⟩ := hpsl2
  let θ : (⁅H, H⁆.subgroupOf H) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe hNle).trans eΩ
  have hcent : ∀ z : ↥H, (∀ n ∈ ⁅H, H⁆.subgroupOf H, z * n = n * z) → z = 1 := by
    intro z hz
    have hzL : (z : Q) ∈ L := z.2.1
    have hzc : (z : Q) ∈ centralizer ((⁅H, H⁆ : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwh : w ∈ H := hNle hw
      have hwN : (⟨w, hwh⟩ : ↥H) ∈ ⁅H, H⁆.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hw
      exact (congrArg Subtype.val (hz ⟨w, hwh⟩ hwN)).symm
    have hmem : (z : Q) ∈ L ⊓ centralizer ((⁅H, H⁆ : Subgroup Q) : Set Q) :=
      ⟨hzL, hzc⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  obtain ⟨Y, eY, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.Family.aut_structure (p := p) hp5
      (N := ⁅H, H⁆.subgroupOf H) θ hcent
  have hYfin : Finite ↥Y := Finite.of_equiv ↥H eY.toEquiv
  have hYtop : Y = ⊤ := by
    refine Subgroup.eq_top_of_card_eq Y ?_
    rw [← Nat.card_congr eY.toEquiv, hcard,
      CFSG.GorensteinWalter.pgl2_card_formula, Nat.card_zmod]
  exact ⟨(hYtop ▸ eY).trans Subgroup.topEquiv⟩

omit [Finite Q] in
theorem disjoint_subgroupOf_zpowers_of_notMem {L H C : Subgroup Q} {b : Q} (hHL : H ≤ L)
    (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    Disjoint (H.subgroupOf C) ((Subgroup.zpowers b).subgroupOf C) := by
  rw [Subgroup.disjoint_def]
  intro x hxH hxB
  rw [Subgroup.mem_subgroupOf] at hxH hxB
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxB
  have hLab : b ^ n ∈ L := hn.symm ▸ hHL hxH
  have hb2' : b ^ 2 = 1 := by simpa [hb2] using pow_orderOf_eq_one b
  have h2 : b ^ n = b ^ (n % (2 : ℤ)) := by
    simpa using zpow_eq_zpow_emod' n hb2'
  have h1 : b ^ n = 1 := by
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [h] at h2
      simpa using h2
    · rw [h, zpow_one] at h2
      exact absurd (h2 ▸ hLab) hbL
  exact Subtype.ext (by rw [← hn]; exact h1)

theorem outerData_psl3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {L : Subgroup Q} [L.Normal]
    (hC : centralizer (L : Set Q) = ⊥) (e : ↥L ≃* PSL3 p) {b : Q} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) : OuterData L p b := by
  obtain ⟨hpsl2, hnorm, hbot, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec20.outerData_L3 (G := Q) hp5 hC e hbL hb2
  exact ⟨nonempty_pgl2_of_inf_centralizer hp5 hpsl2 hbot hcard, hpsl2, hnorm, hbot, hcard⟩

theorem outerData_psu3 {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (hp5 : 5 ≤ p)
    (hF : Nat.card F = p ^ 2) {L : Subgroup Q} [L.Normal] (hC : centralizer (L : Set Q) = ⊥)
    (ψ : PSU3F p F ≃* ↥L) {b : Q} (hbL : b ∉ L) (hb2 : orderOf b = 2) : OuterData L p b := by
  obtain ⟨hpsl2, hnorm, hbot, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec20.outerData_U3 (G := Q) hp5 hF hC ψ hbL hb2
  exact ⟨nonempty_pgl2_of_inf_centralizer hp5 hpsl2 hbot hcard, hpsl2, hnorm, hbot, hcard⟩

theorem outerData_of_lieModel {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup Q} [L.Normal]
    (hC : centralizer (L : Set Q) = ⊥) (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1)
    {b : Q} (hbL : b ∉ L) (hb2 : orderOf b = 2) : OuterData L p b := by
  have hpf : Fact p.Prime := ⟨hp⟩
  rcases hL with hL | hL
  · obtain ⟨e⟩ := exists_equiv_psl3 (K := L)
      (LieModel.statedClassicalModel hL (by decide))
    exact outerData_psl3 hp5 hC e hbL hb2
  · obtain ⟨F, hFld, -, hF, ⟨e⟩⟩ := exists_equiv_psu3 (K := L)
      (LieModel.statedClassicalModel hL (by decide))
    exact outerData_psu3 hp5 hF hC e.symm hbL hb2

theorem OuterData.exists_hom_pgl2 {L : Subgroup Q} [L.Normal] {p : ℕ} [Fact p.Prime] {b : Q}
    (hb : OuterData L p b) (hidx : L.index ≤ 2) (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    ∃ π : ↥(centralizer ({b} : Set Q)) →* CFSG.GorensteinWalter.PGL2 (ZMod p),
      Function.Surjective π ∧ IsPGroup 2 π.ker ∧ ∀ x ∈ π.ker, (x : Q) ∈ L → x = 1 := by
  classical
  set C : Subgroup Q := centralizer ({b} : Set Q) with hC
  set H : Subgroup Q := L ⊓ C with hH
  set B : Subgroup ↥C := (Subgroup.zpowers b).subgroupOf C with hB
  have hbC : b ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbH : b ∉ H := fun h => hbL h.1
  have hLindex : L.index = 2 := by
    have hlt : 1 < L.index :=
      Subgroup.one_lt_index_of_ne_top (fun h => hbL (h ▸ Subgroup.mem_top b))
    omega
  have hrel : H.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨b, hbC, hbH, fun x hxC => ?_⟩
    by_cases hxL : (x : Q) ∈ L
    · exact Or.inr ⟨hxL, hxC⟩
    · refine Or.inl ⟨?_, C.mul_mem hbC hxC⟩
      exact (Subgroup.mul_mem_iff_of_index_two hLindex).mpr (by simp [hbL, hxL])
  have hidxHC : (H.subgroupOf C).index = 2 := hrel
  have hHle : H ≤ C := inf_le_right
  have hHcard : Nat.card ↥(H.subgroupOf C) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  have hzple : Subgroup.zpowers b ≤ C := by
    rw [Subgroup.zpowers_le]
    exact hbC
  have hBcard : Nat.card ↥B = 2 := by
    rw [show Nat.card ↥B = Nat.card ↥(Subgroup.zpowers b) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers, hb2]
  have hcardC : Nat.card ↥C = 2 * Nat.card ↥(H.subgroupOf C) := by
    rw [← Subgroup.index_mul_card (H := H.subgroupOf C), hidxHC]
  have hBcenter : B ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    rw [hB, Subgroup.mem_subgroupOf] at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hyb : (y : Q) * b = b * (y : Q) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2
    apply Subtype.ext
    have hcomm : b ^ n * (y : Q) = (y : Q) * b ^ n :=
      (Commute.zpow_left hyb.symm n).eq
    rw [hn] at hcomm
    exact hcomm.symm
  have hBnormal : B.Normal := Subgroup.normal_of_le_center hBcenter
  have hdisj : Disjoint (H.subgroupOf C) B :=
    disjoint_subgroupOf_zpowers_of_notMem inf_le_left hbL hb2
  have hcompl : (H.subgroupOf C).IsComplement' B := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisj
    rw [hBcard, hcardC, Nat.mul_comm]
  obtain ⟨ΦH⟩ := hb.pgl2
  let φ : ↥(H.subgroupOf C) ≃* CFSG.GorensteinWalter.PGL2 (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe hHle).trans ΦH
  let π : ↥C →* CFSG.GorensteinWalter.PGL2 (ZMod p) :=
    φ.toMonoidHom.comp (hcompl.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' B))
  have hker : π.ker = B := by
    have h1 : (hcompl.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' B)).ker =
        (QuotientGroup.mk' B).ker :=
      MonoidHom.ker_comp_of_injective _ _ hcompl.QuotientMulEquiv.injective
    have h2 : π.ker = (hcompl.QuotientMulEquiv.toMonoidHom.comp
        (QuotientGroup.mk' B)).ker :=
      MonoidHom.ker_comp_of_injective _ _ φ.injective
    rw [h2, h1, QuotientGroup.ker_mk']
  have hdisjL : Disjoint (L.subgroupOf C) B :=
    disjoint_subgroupOf_zpowers_of_notMem le_rfl hbL hb2
  refine ⟨π, φ.surjective.comp (hcompl.QuotientMulEquiv.surjective.comp
    (QuotientGroup.mk'_surjective B)), ?_, ?_⟩
  · rw [hker]
    exact IsPGroup.of_card (by rw [hBcard, pow_one])
  · intro x hx hxL
    have hxB : x ∈ B := by rwa [← hker]
    have hxLc : x ∈ L.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hxL
    exact Subgroup.disjoint_def.mp hdisjL hxLc hxB

theorem OuterData.not_le_centralizer {L : Subgroup Q} {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {b : Q} (hb : OuterData L p b) {Y : Subgroup Q} (hYL : Y ≤ L)
    (hY : Nonempty (↥Y ≃* SL(2, ZMod p))) : ¬ Y ≤ centralizer ({b} : Set Q) := by
  intro hYc
  set H : Subgroup Q := L ⊓ centralizer ({b} : Set Q) with hH
  have hYH : Y ≤ H := le_inf hYL hYc
  obtain ⟨eY⟩ := hY
  have hcardY : Nat.card ↥Y = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr eY.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod]
  have hcardH : Nat.card ↥H = p * (p ^ 2 - 1) := hb.card_eq
  have hYeqH : Y = H := by
    refine Subgroup.eq_of_le_of_card_ge hYH ?_
    rw [hcardH, hcardY]
  have hNle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_self H
  have hwcen : (-1 : SL(2, ZMod p)) ∈ Subgroup.center (SL(2, ZMod p)) :=
    CFSG.Glauberman.Dickson.QuatTable.neg_one_mem_center_SL
  have hwne : (-1 : SL(2, ZMod p)) ≠ 1 := by
    intro h
    have hchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    refine Ring.neg_one_ne_one_of_char_ne_two (R := ZMod p) hchar ?_
    have hmat : ((-1 : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((1 : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by rw [h]
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 0) hmat
    simpa using h00
  let z : ↥Y := eY.symm (-1)
  have hzcen : z ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply eY.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hwcen (eY y)
  have hzne : z ≠ 1 := by
    intro h
    apply hwne
    have h1 : eY z = eY 1 := by rw [h]
    have h2 : eY z = -1 := by simp [z]
    rw [h2, map_one] at h1
    exact h1
  have hzmem : (z : Q) ∈ L ⊓ centralizer ((⁅H, H⁆ : Subgroup Q) : Set Q) := by
    refine ⟨hYL z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w' hw'
    have hw'Y : w' ∈ Y := hYeqH.symm ▸ hNle hw'
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzcen (⟨w', hw'Y⟩ : ↥Y))
  rw [hb.inf_centralizer_eq_bot] at hzmem
  exact hzne (Subtype.ext (Subgroup.mem_bot.mp hzmem))

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
