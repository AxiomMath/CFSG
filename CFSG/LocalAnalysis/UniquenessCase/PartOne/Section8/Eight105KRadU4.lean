module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDefs
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDiag
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Lines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar (suToStated wittMat coe_suToStated)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Comb_four d8Vec_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines
  (torusD coe_torusD unitaryInvolution_rootsOfUnity mapL mapL_mono mapL_inj embedOf)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

omit [Finite F] [CharP F 2] in
private theorem unit_data {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    ((ω : Fˣ) : F) ≠ 1 ∧ ((ω : Fˣ) : F) ^ 3 = 1 ∧
      ((ω : Fˣ) : F) ≠ ((ω : Fˣ) : F)⁻¹ := by
  have hω3 : (ω : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 (ω : Fˣ)).mp ω.2
  have h1 : ((ω : Fˣ) : F) ≠ 1 := by
    intro h
    exact hω (Subtype.ext (Units.ext h))
  have h3 : ((ω : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hne : ω ≠ ω⁻¹ := by
    intro heq
    apply hω
    have h2 : ω ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [heq]
      exact mul_inv_cancel ω
    have h3' : ω ^ 3 = ω := by rw [pow_succ, h2, one_mul]
    have hω3' : ω ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hω3
    rwa [h3'] at hω3'
  refine ⟨h1, h3, ?_⟩
  intro h
  apply hne
  apply Subtype.ext
  rw [← Units.val_inv_eq_inv_val] at h
  exact Units.ext h

omit [Finite F] [CharP F 2] in
private theorem card_fiber_diag (a : F) (ha : a ≠ a⁻¹) :
    Nat.card {i : Fin 4 // (![a, a, a⁻¹, a⁻¹] : Fin 4 → F) i = a} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin 4 =>
      (![a, a, a⁻¹, a⁻¹] : Fin 4 → F) i = a) = {0, 1} := by
    ext i
    fin_cases i <;> simp [ha.symm]
  rw [h]
  decide

omit [Finite F] [CharP F 2] in
private theorem card_fiber_diag_inv (a : F) (ha : a ≠ a⁻¹) :
    Nat.card {i : Fin 4 // (![a, a, a⁻¹, a⁻¹] : Fin 4 → F) i = a⁻¹} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin 4 =>
      (![a, a, a⁻¹, a⁻¹] : Fin 4 → F) i = a⁻¹) = {2, 3} := by
    ext i
    fin_cases i <;> simp [ha]
  rw [h]
  decide

private theorem model_x_data {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {x : ↥(SU (unitaryInvolution F 2 m) 4)}
    (hx : (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F)) :
    x ^ 3 = 1 ∧ x ≠ 1 := by
  obtain ⟨ha1, -, -⟩ := unit_data hω
  have hω3 : (ω : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 (ω : Fˣ)).mp ω.2
  have hω3' : ω ^ 3 = 1 := Subtype.ext hω3
  have hD3 : ((ω, ω) : D8Mod 3 F) ^ 3 = 1 := by
    rw [Prod.pow_def]
    simp [hω3']
  have ht3 : torusD ((ω, ω) : D8Mod 3 F) ^ 3 = 1 := by
    rw [← map_pow, hD3, map_one]
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (x : GL (Fin 4) F) ^ 3 = 1
    rw [hx, ht3]
  refine ⟨hx3, ?_⟩
  intro h1
  have h2 : (x : GL (Fin 4) F) = 1 := by rw [h1]; rfl
  rw [hx] at h2
  have h00 := congrArg (fun z : GL (Fin 4) F =>
    ((z : Matrix (Fin 4) (Fin 4) F) 0 0)) h2
  rw [coe_torusD] at h00
  simp only [Matrix.diagonal_apply_eq] at h00
  exact ha1 h00

private theorem radSetup_equiv (hme : Even m) (hF : Nat.card F = (2 ^ m) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {x : ↥(SU (unitaryInvolution F 2 m) 4)}
    (hx : (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F)) :
    RadSetup 0 (suToStated (p := 2) (f := m) hF 4 x) ((ω : Fˣ) : F) := by
  obtain ⟨ha1, ha3, hainv⟩ := unit_data hω
  have hω3 : (ω : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 (ω : Fˣ)).mp ω.2
  set a : F := ((ω : Fˣ) : F) with ha
  have hd : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    congr 1
    funext i
    fin_cases i <;> simp [ha]
  have hmat : (((suToStated (p := 2) (f := m) hF 4 x : StatedSU 4 (2 ^ m) F) :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (wittMat (p := 2) (f := m) hF 4 : Matrix (Fin 4) (Fin 4) F) *
        diagonal ![a, a, a⁻¹, a⁻¹] *
        ((wittMat (p := 2) (f := m) hF 4)⁻¹ : GL (Fin 4) F) := by
    rw [coe_suToStated]
    simp only [Units.val_mul]
    rw [hx, hd]
  have hfr : Module.finrank F (eigSU (suToStated (p := 2) (f := m) hF 4 x) a) = 2 := by
    rw [finrank_eigSU_of_conj_diagonal (P := wittMat (p := 2) (f := m) hF 4)
      (d := ![a, a, a⁻¹, a⁻¹]) hmat a]
    exact card_fiber_diag a hainv
  have hfr' : Module.finrank F (eigSU (suToStated (p := 2) (f := m) hF 4 x) a⁻¹) = 2 := by
    rw [finrank_eigSU_of_conj_diagonal (P := wittMat (p := 2) (f := m) hF 4)
      (d := ![a, a, a⁻¹, a⁻¹]) hmat a⁻¹]
    exact card_fiber_diag_inv a hainv
  have hω3' : ω ^ 3 = 1 := Subtype.ext hω3
  have hD3 : ((ω, ω) : D8Mod 3 F) ^ 3 = 1 := by
    rw [Prod.pow_def]
    simp [hω3']
  have ht3 : torusD ((ω, ω) : D8Mod 3 F) ^ 3 = 1 := by
    rw [← map_pow, hD3, map_one]
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (x : GL (Fin 4) F) ^ 3 = 1
    rw [hx, ht3]
  have hb3 : (suToStated (p := 2) (f := m) hF 4 x) ^ 3 = 1 := by
    have h := map_pow (suToStated (p := 2) (f := m) hF 4).toMonoidHom x 3
    rw [hx3, map_one] at h
    exact h.symm
  exact ⟨hme, Nat.zero_le 1, ha1, ha3, hb3, hfr, hfr'⟩

private theorem kOf_ne_bot (hm : 0 < m) (hme : Even m)
    (hF : Nat.card F = (2 ^ m) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {x : ↥(SU (unitaryInvolution F 2 m) 4)}
    (hx : (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F)) :
    F08.KOf8103 ⊤ (zpowers x) ≠ ⊥ := by
  obtain ⟨ha1, -, -⟩ := unit_data hω
  let L : Subgroup (GL (Fin 4) F) := SU (unitaryInvolution F 2 m) 4
  let E : L ≃* (⊤ : Subgroup ↥(SU (unitaryInvolution F 2 m) 4)) := Subgroup.topEquiv.symm
  have hmem₃ : torusD ((ω, ω) : D8Mod 3 F) ∈ L :=
    d8Vec_mem_SU (Or.inl rfl) d8Comb_four (unitaryInvolution F 2 m)
      (unitaryInvolution_rootsOfUnity hme) _
  have hmem₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∈ L :=
    d8Vec_mem_SU (Or.inl rfl) d8Comb_four (unitaryInvolution F 2 m)
      (unitaryInvolution_rootsOfUnity hme) _
  have hℓ₃ : zpowers (torusD ((ω, ω) : D8Mod 3 F)) ≤ L :=
    Subgroup.zpowers_le.mpr hmem₃
  have hℓ₄ : zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ≤ L :=
    Subgroup.zpowers_le.mpr hmem₄
  let g : ↥(SU (unitaryInvolution F 2 m) 4) := ⟨torusD ((ω, ω) : D8Mod 3 F), hmem₃⟩
  have hgx : g = x := Subtype.ext hx.symm
  have hsub : (zpowers (torusD ((ω, ω) : D8Mod 3 F))).subgroupOf L = zpowers g := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩,
      fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
  have hmap₃ : mapL E (zpowers (torusD ((ω, ω) : D8Mod 3 F))) = zpowers x := by
    rw [mapL, hsub, MonoidHom.map_zpowers]
    have hemb : embedOf E g = g := rfl
    rw [hemb, hgx]
  have hmapK : mapL E (F08.KOf8103 L (zpowers (torusD ((ω, ω) : D8Mod 3 F)))) =
      F08.KOf8103 ⊤ (zpowers x) := by
    rw [mapL_kOf8103 E hℓ₃, hmap₃]
  have hle₄ : zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ≤
      F08.KOf8103 L (zpowers (torusD ((ω, ω) : D8Mod 3 F))) :=
    (u4_line_le_kOf hm hme hF hω).1
  have hle : mapL E (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) ≤
      F08.KOf8103 ⊤ (zpowers x) := by
    rw [← hmapK]
    exact mapL_mono E hle₄
  have hℓ₄ne : zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ≠ ⊥ := by
    intro hz
    rw [Subgroup.zpowers_eq_bot] at hz
    have h1 := hz
    have h00 := congrArg (fun z : GL (Fin 4) F =>
      ((z : Matrix (Fin 4) (Fin 4) F) 0 0)) h1
    rw [coe_torusD] at h00
    simp only [Matrix.diagonal_apply_eq] at h00
    exact ha1 h00
  have hmapne : mapL E (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) ≠ ⊥ := by
    intro hbot
    have hbot' : mapL E (⊥ : Subgroup (GL (Fin 4) F)) = ⊥ := by simp [mapL]
    exact hℓ₄ne (mapL_inj E hℓ₄ bot_le (hbot.trans hbot'.symm))
  intro hbot
  rw [hbot] at hle
  exact hmapne (le_bot_iff.mp hle)

private theorem kOf_and_card_equiv (hm : 0 < m) (hme : Even m)
    (hF : Nat.card F = (2 ^ m) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {x : ↥(SU (unitaryInvolution F 2 m) 4)}
    (hx : (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F)) :
    F08.KOf8103 ⊤ (zpowers (suToStated (p := 2) (f := m) hF 4 x)) ≠ ⊥ ∧
      Nat.card (zpowers (suToStated (p := 2) (f := m) hF 4 x)) = 3 := by
  obtain ⟨hx3, hx1⟩ := model_x_data hω hx
  have hKx := kOf_ne_bot hm hme hF hω hx
  let e : ↥(SU (unitaryInvolution F 2 m) 4) ≃* StatedSU 4 (2 ^ m) F :=
    suToStated (p := 2) (f := m) hF 4
  have hcardx : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hker : e.toMonoidHom.ker ≤ center ↥(SU (unitaryInvolution F 2 m) 4) := by
    rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective]
    exact bot_le
  have hcop : Nat.Coprime (Nat.card e.toMonoidHom.ker) 6 := by
    rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective, Subgroup.card_bot]
    norm_num
  have hmap := kOf8103_map_of_central e.toMonoidHom e.surjective hker hcop hcardx
  have hmap' : F08.KOf8103 ⊤ (zpowers (e x)) =
      (F08.KOf8103 ⊤ (zpowers x)).map e.toMonoidHom := by
    change F08.KOf8103 ⊤ (zpowers (e.toMonoidHom x)) = _
    rw [← MonoidHom.map_zpowers e.toMonoidHom x]
    exact hmap
  have hb1 : e x ≠ 1 := by
    intro h1
    exact hx1 (e.injective (by rw [h1, map_one]))
  have hb3 : (e x) ^ 3 = 1 := by
    have h := map_pow e.toMonoidHom x 3
    rw [hx3, map_one] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · intro hbot
    rw [hmap'] at hbot
    exact hKx ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hbot)
  · rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]

theorem u4_radicalFacts (hm : 0 < m) (hme : Even m) (hF : Nat.card F = (2 ^ m) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {x : ↥(SU (unitaryInvolution F 2 m) 4)}
    (hx : (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F)) :
    RadicalFacts ↥(SU (unitaryInvolution F 2 m) 4) (zpowers x) := by
  have h : UnitaryFieldData 2 m F :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hF (by omega)
  have hS := radSetup_equiv hme hF hω hx
  obtain ⟨hK₀, hB⟩ := kOf_and_card_equiv hm hme hF hω hx
  have harg : (suToStated (p := 2) (f := m) hF 4).symm.toMonoidHom
      ((suToStated (p := 2) (f := m) hF 4) x) = x :=
    MulEquiv.symm_apply_apply _ _
  have hres := RadicalFacts.of_mulEquiv (suToStated (p := 2) (f := m) hF 4).symm hB
    (hS.radicalFacts h hK₀)
  rw [MonoidHom.map_zpowers, harg] at hres
  exact hres

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
