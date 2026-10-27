module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUBlock
public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightCharts
import CFSG.ClassicalInvolution.WeakCT.UnitaryEightWeakCT
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL2 weakCT_unitary_eight_of_charts
  weakCT_unitary_eight_even_of_charts)
open CFSG.Blueprint
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.StandardType.SelectedRoot CFSG.StandardType.SelectedRoot.SelPSU
open CFSG.LieType.Steinberg (fixedSubfield mem_fixedSubfield)
open CFSG.ClassicalInvolution.WeakCT (hom_ext_sl2)
open CFSG.Timmesfeld (tv)
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open scoped MatrixGroups


theorem exists_selectedModel_PSU_rL
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF 6) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot 6 (2 : Fin 6)),
      model.phi = CFSG.RankThree.PartTwo.CTU6.rL F f := by
  classical
  have hi : (2 : Fin 6) ≠ Fin.rev 2 := by decide
  obtain ⟨model, -, hmat⟩ := exists_selectedModel_PSU_chart_rootPair_at hF (2 : Fin 6) hi
  let σ := unitaryInvolution F 2 f
  let k := fixedSubfield F 2 f
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : ∀ c ∈ k, σ c = c := fun c hc => mem_fixedSubfield.mp hc
  have hphi : ∀ A, model.phi A = chart σ k (pairCoord_injective hi) (pairCoord_rev 2) h2 hk A := by
    intro A
    apply Subtype.ext
    apply Units.ext
    exact hmat A
  refine ⟨model, ?_⟩
  apply hom_ext_sl2
  · intro c
    rw [CFSG.RankThree.PartTwo.CTU6.rL_tv01, hphi, tv01_eq_sl2Upper,
      chart_upper σ k hi h2 hk]
    rfl
  · intro c
    rw [CFSG.RankThree.PartTwo.CTU6.rL_tv10, hphi, tv10_eq_sl2Lower,
      chart_lower σ k hi h2 hk]
    rfl


theorem ggCompatPresented_of_unitary_long_node
    {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G]
    (Ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8 →* G)
    (hΨ : Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6))
    (hnode : (CFSG.LieType.CurtisTits.rankOne
      (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8).rootGroup
      (⟨3, by change 3 < 4; decide⟩ :
        Fin (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8).rank)).map Ψ =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * f)) f)).range) :
    GGCompatPresented (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8) Ψ κ.range := by
  classical
  have hF := card_galoisField_two_mul 2 f hf
  obtain ⟨model, hm, -⟩ :=
    exists_selectedModel_PSU_chart_rootPair_at hF (3 : Fin 8) (by decide)
  obtain ⟨model', hm'⟩ := exists_selectedModel_PSU_rL hF
  have hγ : InnerDiagSU.twoWtRoot 8 (3 : Fin 8) =
      Pi.single (⟨3, by change 3 < 4; decide⟩ : Fin (Unitary.rootDatum hF 8).rank) 1 := by
    change (InnerDiagSU.twoWtRoot 8 (3 : Fin 8) : Fin 4 → ℤ) = Pi.single (3 : Fin 4) 1
    funext j
    fin_cases j <;> decide +kernel
  have hr : (Ψ.comp model.phi).range = (κ.comp model'.phi).range := by
    calc (Ψ.comp model.phi).range = model.phi.range.map Ψ := by rw [MonoidHom.range_comp]
      _ = (CFSG.LieType.CurtisTits.rankOne (Unitary.rootDatum hF 8).rootGroup
          (⟨3, by change 3 < 4; decide⟩ : Fin (Unitary.rootDatum hF 8).rank)).map Ψ := by
        rw [hm, hγ]
        rfl
      _ = (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * f)) f)).range := hnode
      _ = (κ.comp model'.phi).range := by rw [hm']
  have hconj : (MulAut.conj (1 : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8)).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  obtain ⟨u, hmatch⟩ := SelectedRoot.selectedRootMatch_of_map_eq model model' Ψ κ hΨ hκ 1
    (by simpa only [hconj, MonoidHom.comp_id] using hr)
  have hadm : StatedLieAdmissible .PSU 6 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have hM6 : ggU .PSU 6 f =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6,
        Unitary.rootDatum hF 6⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  unfold GGCompatPresented
  refine ⟨.PSU, 6, f, ?_⟩
  rw [hM6]
  refine ⟨κ, hadm, ?_, hκ, rfl, InnerDiagSU.twoWtRoot 6 (2 : Fin 6), model'.root_mem,
    InnerDiagSU.twoWtRoot 8 (3 : Fin 8), model.root_mem, u, hmatch⟩
  change 2 ≤ 6 / 2
  norm_num

theorem ggCompatPresented_unitaryEight_embSU6
    {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8 →* G)
    (hψ : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8)) :
    GGCompatPresented (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8) ψ
      (ψ.comp (CFSG.ClassicalInvolution.WeakCT.UnitaryEight.embSU6
        (unitaryInvolution (GaloisField 2 (2 * f)) 2 f))).range := by
  classical
  let F := GaloisField 2 (2 * f)
  let σ := unitaryInvolution F 2 f
  let U : Matrix (Fin 8) (Fin 6) F := CFSG.ClassicalInvolution.Phan.blockSel F 8 6 1
  let V : Matrix (Fin 6) (Fin 8) F := Matrix.transpose U
  let E : Matrix (Fin 8) (Fin 8) F := U * V
  have hVU : V * U = 1 :=
    CFSG.ClassicalInvolution.Phan.blockSel_transpose_mul_self (by norm_num)
  have hUmap : U.map σ.toRingHom = U := by
    ext i j
    simp [U, CFSG.ClassicalInvolution.Phan.blockSel_apply]
  have hVmap : V.map σ.toRingHom = V := by
    change Matrix.transpose (U.map σ.toRingHom) = Matrix.transpose U
    rw [hUmap]
  have hJ : (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) * U =
      U * (Unitary.antidiag 6 : Matrix (Fin 6) (Fin 6) F) :=
    CFSG.ClassicalInvolution.WeakCT.UnitaryEight.antidiag_mul_blockSel_eight
  have hVJ : V * (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) =
      (Unitary.antidiag 6 : Matrix (Fin 6) (Fin 6) F) * V := by
    have h := congrArg Matrix.transpose hJ
    simpa only [Matrix.transpose_mul,
      CFSG.RankThree.PartTwo.CTU6.antidiag_transpose] using h
  have hA : Matrix.transpose (U.map σ.toRingHom) *
      (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) * U = Unitary.antidiag 6 := by
    rw [hUmap, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hEmap : E.map σ.toRingHom = E := by
    dsimp only [E]
    rw [Matrix.map_mul, hUmap, hVmap]
  have hEtr : Matrix.transpose E = E := by
    dsimp only [E, V]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hE : Matrix.transpose (E.map σ.toRingHom) *
      (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) = Unitary.antidiag 8 * E := by
    rw [hEmap, hEtr]
    change (U * V) * (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) =
      (Unitary.antidiag 8 : Matrix (Fin 8) (Fin 8) F) * (U * V)
    rw [Matrix.mul_assoc, hVJ, ← Matrix.mul_assoc, ← hJ, Matrix.mul_assoc]
  have hιform : ∀ x : SU σ 6,
      (((CFSG.ClassicalInvolution.WeakCT.UnitaryEight.embSU6 σ x : SU σ 8) : GL (Fin 8) F) :
        Matrix (Fin 8) (Fin 8) F) =
      U * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * V + (1 - E) := by
    intro x
    rw [CFSG.ClassicalInvolution.WeakCT.UnitaryEight.coe_embSU6]
    change 1 + U * (((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) - 1) * V =
      U * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * V + (1 - U * V)
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  exact ggCompatPresented_of_unitary_block hf (by norm_num) (by norm_num) rfl hVU hA hE
    (CFSG.ClassicalInvolution.WeakCT.UnitaryEight.embSU6 σ) hιform ψ hψ


theorem ggSU8_presents_compat_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hagree : φ.comp (blockSL (GaloisField 2 (2 * a)) 4 3 1 (by norm_num)) =
      κ.comp (CFSG.RankThree.PartTwo.CTU6.embSL3 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega)))))
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range ∧
      GGPresentsG0 Ψ.range (ggU .PSU 8 a).D .PSU 8 a Ψ ∧
      GGCompatPresented (ggU .PSU 8 a).D Ψ κ.range := by
  have hF := card_galoisField_two_mul 2 a (by omega)
  obtain ⟨Ψ, hker, hrange, -, hκ⟩ :=
    weakCT_unitary_eight_of_charts hF ha φ hφ κ hagree hcross
  have hcomp := ggCompatPresented_unitaryEight_embSU6 (by omega : 1 ≤ a) Ψ hker
  rw [hκ] at hcomp
  have hpres : GGPresentsG0 Ψ.range (Unitary.rootDatum hF 8) .PSU 8 a Ψ :=
    ggPresentsG0_of_unitary_hom hF (by omega) (by norm_num) Ψ hker
  have ha1 : 1 ≤ a := by omega
  have e : ggU .PSU 8 a =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 8,
        Unitary.rootDatum hF 8⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, ha1, ↓reduceDIte]
  rw [e]
  exact ⟨Ψ, hker, hrange, hpres, hcomp⟩

theorem ggSecFiveCompat_of_suCharts
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {a : ℕ} (ha : 2 ≤ a)
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hagree : φ.comp (blockSL (GaloisField 2 (2 * a)) 4 3 1 (by norm_num)) =
      κ.comp (CFSG.RankThree.PartTwo.CTU6.embSL3 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega)))))
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y)
    (hG0 : ggG0 p B x L D J = φ.range ⊔ κ.range)
    (hK : κ.range = L ∨ ∃ y : G, GGNbr p B x D J y κ.range) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨Ψ, -, hrange, hpres, hcomp⟩ := ggSU8_presents_compat_of_charts ha φ hφ κ hagree hcross
  have hpres0 : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU 8 a).D .PSU 8 a Ψ := by
    rw [← hrange.trans hG0.symm]
    exact hpres
  exact ⟨.PSU, 8, a, Ψ, hpres0, κ.range, hK, hcomp⟩

theorem GGSecFiveRouteCfg.compat_of_suCharts
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hK : K ∈ 𝒦)
    {a : ℕ} (ha : 2 ≤ a) (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.range = K)
    (hagree : φ.comp (blockSL (GaloisField 2 (2 * a)) 4 3 1 (by norm_num)) =
      κ.comp (CFSG.RankThree.PartTwo.CTU6.embSL3 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega)))))
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y)
    (hG0 : ggG0 p B x L D J = φ.range ⊔ κ.range) :
    GGSecFiveCompat p B x L D J := by
  apply ggSecFiveCompat_of_suCharts ha φ hφ κ hagree hcross hG0
  obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
  exact Or.inr ⟨y, by simpa only [hκ] using hy⟩


theorem ggSU8_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hagree : φ.comp (blockSL (GaloisField 2 (2 * a)) 4 3 1 (by norm_num)) =
      κ.comp (CFSG.RankThree.PartTwo.CTU6.embSL3 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega)))))
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range := by
  obtain ⟨Ψ, hker, hrange, -, -⟩ :=
    ggSU8_presents_compat_of_charts ha φ hφ κ hagree hcross
  exact ⟨Ψ, hker, hrange⟩

theorem ggSU8_even_presents_compat_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range ∧
      GGPresentsG0 Ψ.range (ggU .PSU 8 a).D .PSU 8 a Ψ ∧
      GGCompatPresented (ggU .PSU 8 a).D Ψ κ.range := by
  have hF := card_galoisField_two_mul 2 a (by omega)
  obtain ⟨Ψ, hker, hrange, hnode⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_unitary_eight_even_of_charts_with_long_root
      hF ha φ hφ κ hκ h1 h2 hcross
  have hcomp := ggCompatPresented_of_unitary_long_node (by omega : 1 ≤ a) Ψ hker κ hκ hnode
  have hpres := ggPresentsG0_of_unitary_hom hF (by omega : 1 ≤ a) (by norm_num : 4 ≤ 8) Ψ hker
  have ha1 : 1 ≤ a := by omega
  have e : ggU .PSU 8 a =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 8,
        Unitary.rootDatum hF 8⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, ha1, ↓reduceDIte]
  rw [e]
  exact ⟨Ψ, hker, hrange, hpres, hcomp⟩

theorem ggSU8_even_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range := by
  obtain ⟨Ψ, hker, hrange, -, -⟩ :=
    ggSU8_even_presents_compat_of_charts ha φ hφ κ hκ h1 h2 hcross
  exact ⟨Ψ, hker, hrange⟩

theorem ggSecFiveData_of_suCharts {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {a : ℕ} (ha : 2 ≤ a) (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hagree : φ.comp (blockSL (GaloisField 2 (2 * a)) 4 3 1 (by norm_num)) =
      κ.comp (CFSG.RankThree.PartTwo.CTU6.embSL3 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega)))))
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y)
    (hG0 : ggG0 p B x L D J = φ.range ⊔ κ.range) :
    GGSecFiveData p B x L D J := by
  obtain ⟨Ψ, hker, hrange⟩ := ggSU8_of_charts ha φ hφ κ hagree hcross
  have hadm : StatedLieAdmissible .PSU 8 2 a :=
    ⟨Nat.prime_two, by omega, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  refine Or.inr (Or.inr ⟨.PSU, 8, a, ggSecFivePres_of_psi_PSU hadm ?_ Ψ hker
    (hrange.trans hG0.symm)⟩)
  simp only [bnRank]
  omega


theorem GGSecFiveRouteCfg.compat_of_suRanges
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hK : K ∈ 𝒦)
    {a : ℕ} (ha : 2 ≤ a) (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (hκrange : κ.range = K)
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y)
    (hG0 : ggG0 p B x L D J = φ.range ⊔ κ.range) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨Ψ, -, hrange, hpres, hcomp⟩ :=
    ggSU8_even_presents_compat_of_charts ha φ hφ κ hκ h1 h2 hcross
  have hpres0 : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU 8 a).D .PSU 8 a Ψ := by
    rw [← hrange.trans hG0.symm]
    exact hpres
  obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
  exact ⟨.PSU, 8, a, Ψ, hpres0, κ.range,
    Or.inr ⟨y, by simpa only [hκrange] using hy⟩, hcomp⟩

end CFSG.StandardType

end
