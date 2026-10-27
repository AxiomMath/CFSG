module

public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.SeitzReduction.LinearPilot

namespace LinTypeAk

section Generic

variable {G : Type*} [Group G]

theorem nonempty_quotient_center_mulEquiv_range {H : Type*} [Group H] (hU : commutator H = ⊤)
    (φ : H →* G) (hker : φ.ker ≤ Subgroup.center H) :
    Nonempty (H ⧸ Subgroup.center H ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  let q : H →* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.mk' _).comp φ.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp φ.rangeRestrict_surjective
  have hqk : q.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ.rangeRestrict u) : ↥φ.range ⧸ Subgroup.center ↥φ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hU φ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := φ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩

theorem eq_of_isComponentOf_of_le {L₁ K H : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L₁ H)
    (hLK : L₁ ≤ K) (hKH : K ≤ H) (hK : CFSG.Assembly.IsQuasisimple K) : L₁ = K := by
  have hq := hL.2.2
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hLK).mp (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hLK hKH)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hK' hc.2 with h' | h'
  · exact le_antisymm hLK (Subgroup.subgroupOf_eq_top.mp h')
  · exfalso
    refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
    have hxc : (⟨x, hLK hx⟩ : K) ∈ Subgroup.center K := h' (Subgroup.mem_subgroupOf.mpr hx)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hLK hy⟩)).symm

theorem three_le_of_dvd_two_pow_sub_one {p f : ℕ} (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) : 3 ≤ f := by
  by_contra hf3
  interval_cases f
  · have := Nat.le_of_dvd (by norm_num) hpf
    norm_num at this
    omega
  · have := Nat.le_of_dvd (by norm_num) hpf
    norm_num at this
    omega

theorem two_le_of_dvd_two_pow_add_one {p f : ℕ} (hp5 : 5 ≤ p) (hpf : p ∣ 2 ^ f + 1) :
    2 ≤ f := by
  by_contra hf
  have hle := Nat.le_of_dvd (by positivity) hpf
  interval_cases f <;> norm_num at hle <;> omega

end Generic

section Linear

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem lieModel_map_blockSpecialLinear_of_card_two [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {V : Finset (Fin (m + 1))} (hV : V.card = 2) :
    LieModel (↥((blockSpecialLinear (K := F) V).map ψ) ⧸
      Subgroup.center ↥((blockSpecialLinear (K := F) V).map ψ)) .PSL 2 2 f := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hF2 : Nat.card F ≠ 2 := by omega
  have hq := LinSemisimple.isQuasisimple_specialLinearGroup_finset (F := F) (I := V) (by omega)
    (Or.inr hF2)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup V F) := hq.1
  let ε₀ : Matrix.SpecialLinearGroup V F ≃* ↥(blockSpecialLinear (K := F) V) :=
    (MonoidHom.ofInjective (blockEmbed_injective (K := F) V)).trans
      (MulEquiv.subgroupCongr (range_blockEmbed V))
  have hU : commutator ↥(blockSpecialLinear (K := F) V) = ⊤ :=
    Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective (f := ε₀.toMonoidHom) ε₀.surjective)
  rw [← LinTorus.range_comp_subtype]
  obtain ⟨e₁⟩ := nonempty_quotient_center_mulEquiv_range hU
    (ψ.comp (blockSpecialLinear (K := F) V).subtype) (LinTorus.ker_comp_subtype_le hker V)
  let e₀ := (LinTorus.blockSLMulEquiv (F := F) V hV).symm
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      (↥(blockSpecialLinear (K := F) V) ⧸ Subgroup.center ↥(blockSpecialLinear (K := F) V)) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hadm : StatedLieAdmissible .PSL (1 + 1) 2 f := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  exact Or.inl ⟨by decide, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv (e₂.trans e₁)
    (SpecialLinear.statedClassicalModel_center_quotient 1 F hadm hF)⟩

theorem ggTypeAk_of_isComponentOf_sl [Finite G] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnp : m + 1 = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hbig : p ^ 2 < Nat.card E)
    (hEdiag : ∀ e ∈ E, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ e)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) {b : G} (hb : b ∈ E)
    {L₁ : Subgroup G} (hL : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}))
    (hex : ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f) : GGTypeAk f L₁ := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hm : 2 ≤ m := by omega
  have hf3 : 3 ≤ f := three_le_of_dvd_two_pow_sub_one hp5 hf hpf
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ := fun e he =>
    LinFusion.exists_mem_ggInducedPairs hm ψ hker (hEdiag e⁻¹ (E.inv_mem he))
  have hbig' : p ^ ((m + 1) / p + 1) < Nat.card E := by
    rw [hnp, Nat.div_self hp.pos]
    exact hbig
  obtain ⟨P, hP⟩ := LinTorus.exists_le_ggFrameTorus hp (by omega) (by rw [hF]; exact hpf) hker
    hE hbig' hEA hEC
  have hker' := LinTorus.ker_comp_conjSL_le hker P⁻¹
  obtain ⟨d, hd⟩ := hP hb
  have hd' : (b, InnerDiagA.diagGL d) ∈
      LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) :=
    LinTorus.mem_ggInducedPairs_frame hd
  have hL' : CFSG.Assembly.IsComponentOf L₁ ((ψ.comp (InnerDiagA.conjSL P⁻¹)).range ⊓
      Subgroup.centralizer (Set.range fun _ : Unit => b)) := by
    rw [Set.range_const, LinTorus.range_comp_conjSL ψ P⁻¹]
    exact hL
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hker'
    (d := fun _ : Unit => d) (b := fun _ => b) (fun _ => hd') hL'
  obtain ⟨h2, -⟩ := LinSemisimple.two_le_card_of_isQuasisimple_le hL'.2.2 hi.le
  subst hi
  rcases (show (LinSemisimple.eigClass (fun _ : Unit => d) i).card = 2 ∨
      3 ≤ (LinSemisimple.eigClass (fun _ : Unit => d) i).card by omega) with h2' | h3
  · exact absurd (lieModel_map_blockSpecialLinear_of_card_two hF (by omega) hker' h2') hex
  · exact ⟨_, h3, Or.inl (LinTorus.lieModel_map_blockSpecialLinear hF hf hker' h3)⟩

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits InnerDiagSU
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel SUTorus

variable {K : Type} [Field K] {f n : ℕ} {G : Type} [Group G]

theorem lieModel_map_blockSU_of_card_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {V : Finset (Fin n)} (hV : V.card = 2) :
    LieModel (↥((TableBUE.blockSU (K := K) (n := f) V).map ψ) ⧸
      Subgroup.center ↥((TableBUE.blockSU (K := K) (n := f) V).map ψ)) .PSL 2 2 f := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_comp_subtype_blockSU]
  set U := TableBUE.blockSU (K := K) (n := f) V with hU
  have hUq : CFSG.IsQuasisimple ↥U := SURepair.isQuasisimple_blockSU_two h hf hV
  have hUp : commutator ↥U = ⊤ := Group.isPerfect_def.mp hUq.1
  obtain ⟨e₁⟩ := nonempty_quotient_center_mulEquiv_range hUp (ψ.comp U.subtype)
    (ker_comp_subtype_blockSU_le hker V)
  obtain ⟨e₃⟩ := SURepair.nonempty_sl2_mulEquiv_unitarySU_two (f := f) h.card_eq_sq
  have key : ∀ k, V.card = k → Nonempty (↥U ≃* ↥(unitarySU 2 f K k)) := by
    rintro k rfl
    exact ⟨(TableBUE.blockSUEquiv V h).symm⟩
  obtain ⟨e₄⟩ := key 2 hV
  let e₀ : Matrix.SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) ≃*
      ↥U := e₃.trans e₄.symm
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) ≃* (↥U ⧸ Subgroup.center ↥U) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hFq : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .PSL (1 + 1) 2 f := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h'
      simp only [Prod.mk.injEq] at h'
      omega
    · intro h'
      simp only [Prod.mk.injEq] at h'
      omega
  exact Or.inl ⟨by decide, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv (e₂.trans e₁)
    (SpecialLinear.statedClassicalModel_center_quotient 1 _ hadm hFq)⟩

theorem ggTypeAk_of_isComponentOf_su [Finite G] {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnp : m + 1 = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hbig : p ^ 2 < Nat.card E)
    (hEdiag : ∀ e ∈ E,
      GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ e)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) {b : G} (hb : b ∈ E)
    {L₁ : Subgroup G} (hL : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}))
    (hex : ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f) : GGTypeAk f L₁ := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ m + 1 := by omega
  have hf2 : 2 ≤ f := two_le_of_dvd_two_pow_add_one hp5 hpf
  have hq : 2 ^ f ≠ 2 := by
    intro h2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq (congrArg Prod.snd h')
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) =
      unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) :=
    ker_comp_symm_le hker Φ
  have hEB : ∀ e ∈ E, ∃ B, B ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * f)) (m + 1)) ∧
      (e, B) ∈ suPairs ψ₁ := by
    intro e he
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF (by omega) G ψ hker e⁻¹ (hEdiag e⁻¹ (E.inv_mem he))
    refine ⟨P * A * P⁻¹, mem_primeFormUnitary_of_isIdUnitary h (isIdUnitary_conj hP hA),
      mem_suPairs_transfer P hP hSU hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ suPairs ψ₁ := fun e he => by
    obtain ⟨B, -, hB⟩ := hEB e he
    exact ⟨B, hB⟩
  have hEC₁ : E ⊓ Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by rw [hr₁]; exact hEC
  have hbig' : p ^ ((m + 1) / p + 1) < Nat.card E := by
    rw [hnp, Nat.div_self hp.pos]
    exact hbig
  have hT := isToral_inducedMatrices h hn3 hnq hp hp2 hpf hker₁ hE hbig' hEA hEC₁
  obtain ⟨Q, hQ, hQd⟩ := exists_unitary_frame h hp hp2 hpf
    (isProjElem_inducedMatrices h hn3 hnq hp hpf hker₁ hE) hT
  set ψ₂ := ψ₁.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom with hψ₂
  have hr₂ : ψ₂.range = ψ.range := by rw [hψ₂, range_comp_conjSU_symm, hr₁]
  have hker₂ := ker_comp_conjSU_symm_le h hker₁ Q hQ
  have hδ' : ∀ e ∈ E, ∃ d : Fin (m + 1) → (GaloisField 2 (2 * f))ˣ,
      (e, diagHom (m + 1) d) ∈ suPairs ψ₂ := by
    intro e he
    obtain ⟨B, hBU, hB⟩ := hEB e he
    obtain ⟨d, hd⟩ := hQd B (mem_inducedMatrices.mpr ⟨e, he, hB⟩) hBU
    refine ⟨d, ?_⟩
    rw [← hd]
    exact mem_suPairs_frame h hQ hB
  choose! δ hδ using hδ'
  rw [← hr₂] at hL
  have hδb : ∀ e ∈ ({b} : Set G), (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ₂ := fun e he => by
    rw [Set.mem_singleton_iff.mp he]
    exact hδ b hb
  obtain ⟨i, hLI⟩ := exists_le_map_blockSU h hp hpf hker₂ hδb hL
  have hI2 : 2 ≤ (LinTorus.diagClass ({b} : Set G) δ i).card := by
    by_contra hlt
    have h1 : 1 ≤ (LinTorus.diagClass ({b} : Set G) δ i).card :=
      Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ δ i⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
      (show (LinTorus.diagClass ({b} : Set G) δ i).card = 1 by omega)
    rw [ha, blockSU_singleton h, Subgroup.map_bot] at hLI
    apply commutator_ne_bot_of_isQuasisimple hL.2.2
    rw [le_bot_iff.mp hLI]
    exact Subgroup.commutator_bot_left _
  have hKq := SURepair.isQuasisimple_map_blockSU_of_two_le h hf2 hker₂ hI2
  have hsub := isSubnormal_map_blockSU hker₂ hδb i
  have hLeq := eq_of_isComponentOf_of_le hL hLI (isSubnormal_le_of_assembly hsub) hKq
  subst hLeq
  rcases (show (LinTorus.diagClass ({b} : Set G) δ i).card = 2 ∨
      3 ≤ (LinTorus.diagClass ({b} : Set G) δ i).card by omega) with h2 | h3
  · exact absurd (lieModel_map_blockSU_of_card_two h hf2 hker₂ h2) hex
  · have hVq : ((LinTorus.diagClass ({b} : Set G) δ i).card, 2 ^ f) ≠ (3, 2) :=
      fun h' => hq (congrArg Prod.snd h')
    exact ⟨_, h3, Or.inr (lieModel_map_blockSU h hker₂ h3 hVq)⟩

end Unitary

end LinTypeAk

end CFSG.StandardType
