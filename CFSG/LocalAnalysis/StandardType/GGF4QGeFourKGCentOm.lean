module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourL1
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGKGCentOmTableB
import CFSG.LocalAnalysis.StandardType.GGKGCentStdPair
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOmegaMinusTorality
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourLocalMaps
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4SharedRefl
import CFSG.LocalAnalysis.StandardType.GGF4CrossMissed
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped MatrixGroups

private theorem closure_sup_closure_eq_top {G : Type} [Group G] {Bs L K X Y : Subgroup G}
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hXA : ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hYA : ggAutomizer Y Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hLK : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer X Bs ⊔ ggAutomizer Y Bs)
    {a b : Fin 3 → CoxeterMatrix.F₄.Group}
    (haX : ∀ z, z ∈ Subgroup.closure (Set.range a) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hbY : ∀ z, z ∈ Subgroup.closure (Set.range b) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs) :
    Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  let ι : CoxeterMatrix.F₄.Group →* MulAut ↥Bs :=
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hle : ggAutomizer X Bs ⊔ ggAutomizer Y Bs ≤
      (Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b)).map ι := by
    refine sup_le ?_ ?_
    · intro m hm
      refine ⟨e.symm ⟨m, hXA hm⟩,
        le_sup_left (a := Subgroup.closure (Set.range a)) ((haX _).mpr ?_), ?_⟩
      · simpa using hm
      · simp [ι]
    · intro m hm
      refine ⟨e.symm ⟨m, hYA hm⟩,
        le_sup_right (a := Subgroup.closure (Set.range a)) ((hbY _).mpr ?_), ?_⟩
      · simpa using hm
      · simp [ι]
  obtain ⟨z', hz', hzz'⟩ := hle (hLK (e z).2)
  have : z' = z := hι (by simpa [ι] using hzz')
  rwa [← this]

private theorem mem_normalizer_ggRankOneIn_of {G : Type} [Group G] [Finite G] {Bs Y : Subgroup G}
    {t : G}
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htB : t ∈ Subgroup.centralizer (Bs : Set G))
    (r : MulAut ↥Bs) : t ∈ Subgroup.normalizer (ggRankOneIn Y Bs r : Set G) := by
  have ha : ∀ b : ↥Bs, (((1 : MulAut ↥Bs) b : ↥Bs) : G) = t * b * t⁻¹ := by
    intro b
    rw [MulAut.one_apply, ← Subgroup.mem_centralizer_iff.mp htB b b.2, mul_inv_cancel_right]
  have h := ggRankOneIn_map_conj (X := Y) (g := t) (a := 1) ha r
  have hY : Y.map (MulAut.conj t).toMonoidHom = Y := Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
  rw [hY, one_mul, inv_one, mul_one] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private theorem map_conj_word {ι : Type} {M : CoxeterMatrix ι} {N : Type} [Group N]
    (φ : M.Group →* N) (σ : Fin 3 → ι) (l : List (Fin 3)) (k : Fin 3) :
    φ ((l.map fun j => M.simple (σ j)).prod * M.simple (σ k) *
        ((l.map fun j => M.simple (σ j)).prod)⁻¹) =
      (l.map fun j => φ (M.simple (σ j))).prod * φ (M.simple (σ k)) *
        ((l.map fun j => φ (M.simple (σ j))).prod)⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_list_prod, List.map_map]
  rfl

private theorem eps_eq_of_shared {G : Type} [Group G] {Bs L K X Y : Subgroup G}
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    {ι₁ ι₂ : Type} {M₁ : CoxeterMatrix ι₁} {M₂ : CoxeterMatrix ι₂}
    {ε₁ : M₁.Group ≃* ↥(ggAutomizer X Bs)} {ε₂ : M₂.Group ≃* ↥(ggAutomizer Y Bs)}
    {φ₁ : M₁.Group →* CoxeterMatrix.F₄.Group} {φ₂ : M₂.Group →* CoxeterMatrix.F₄.Group}
    (hφ₁ : ∀ u, ((e (φ₁ u) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) =
      ((ε₁ u : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hφ₂ : ∀ u, ((e (φ₂ u) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) =
      ((ε₂ u : ↥(ggAutomizer Y Bs)) : MulAut ↥Bs))
    (σ₁ : Fin 3 → ι₁) (σ₂ : Fin 3 → ι₂) {u v : List (Fin 3)} {c d : Fin 3}
    (huv : (u.map fun k => φ₁ (M₁.simple (σ₁ k))).prod * φ₁ (M₁.simple (σ₁ c)) *
        ((u.map fun k => φ₁ (M₁.simple (σ₁ k))).prod)⁻¹ =
      (v.map fun k => φ₂ (M₂.simple (σ₂ k))).prod * φ₂ (M₂.simple (σ₂ d)) *
        ((v.map fun k => φ₂ (M₂.simple (σ₂ k))).prod)⁻¹) :
    ((ε₁ ((u.map fun k => M₁.simple (σ₁ k)).prod * M₁.simple (σ₁ c) *
        ((u.map fun k => M₁.simple (σ₁ k)).prod)⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      ((ε₂ ((v.map fun k => M₂.simple (σ₂ k)).prod * M₂.simple (σ₂ d) *
        ((v.map fun k => M₂.simple (σ₂ k)).prod)⁻¹) : ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := by
  rw [← hφ₁, ← hφ₂, map_conj_word, map_conj_word, huv]

private theorem val_lt_two_of_ne {d : Fin 3} (hd : d ≠ 2) : d.val < 2 := by
  have h3 := d.isLt
  have h2 : d.val ≠ 2 := fun h => hd (Fin.ext h)
  omega


theorem ggF4QGeFourKGCent_S2_omegaMinusTarget (ha₀ : GGLNoncyclicInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput) (hKG : GGF4QGeFourKGPosInput .S2)
    (hM : GGF4QGeFourRk2MissedInput .S2)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp .S2 f L K)
    {X Y : Subgroup G} (hXY : X = L ∧ Y = K ∨ X = K ∧ Y = L)
    (hY : GGTableBPosImage p Bs .POmegaMinus 4 f Y) {t : G} (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (htB : t ∈ Subgroup.centralizer (Bs : Set G)) (htX : t ∈ Subgroup.centralizer (X : Set G)) :
    t ∈ Subgroup.centralizer (Y : Set G) := by
  classical
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  have hxB : x ∈ Bs := hcfg.1.1.2.1.1 (hDB hxD)
  have hyB : y ∈ Bs := by
    refine hcfg.1.1.2.1.1 (hDB ?_)
    rw [hcfg.2.2.2.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem : ∀ Z : Subgroup G, Z = L ∨ Z = K → ∃ z, z ∈ Bs ∧
      CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)) := by
    rintro Z (rfl | rfl)
    · exact ⟨x, hxB, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1⟩
    · exact ⟨y, hyB, hcfg.2.2.2.1.2.2.2.2.1.2.1⟩
  have hXm : X = L ∨ X = K := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hYm : Y = L ∨ Y = K := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hXA : ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hXm with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hYA : ggAutomizer Y Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hYm with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hLK : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer X Bs ⊔ ggAutomizer Y Bs := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · exact (sup_comm _ _).le
  have hZXY : ∀ Z : Subgroup G, Z = L ∨ Z = K → Z = X ∨ Z = Y := by
    rintro Z (rfl | rfl) <;> rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨xX, hxXB, hXx⟩ := hmem X hXm
  obtain ⟨yY, hyYB, hYy⟩ := hmem Y hYm
  obtain ⟨hLpos, hKpos⟩ := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hpf hrow
  have hXpos : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨ GGTableBPosImage p Bs .PSU 6 f X := by
    rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl hLpos
    · exact hKpos.symm
  have hYpos := hY
  obtain ⟨ψ, hker, hrange, hpos⟩ := hY
  have hTor := F4KGPosition.exists_ggTorus_conj_of_tableBPos_POmegaMinus hcfg hYm hf hpf ψ hker
    hrange hpos
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, by omega, le_rfl⟩
  obtain ⟨-, -, hrank⟩ := ggF4QGeFour_localMap_of_mp ggInnerDiagMpInput_holds hcfg hYm ψ hadm
    (two_le_lieUniversal_rank .POmegaMinus 4 2 f Nat.prime_two hadm (by decide)) hker hrange
  obtain ⟨εY, hεY, hlevY, -⟩ := hpos
  have hirr := minusCoeffs_irr 2 f
  have hψ : Function.Injective ψ := by
    have hc := CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (by decide : 4 ≤ 4) hirr
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hc.le
  have htH : t ∈ Subgroup.centralizer (ggHyperplane Bs 1 : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (Subgroup.map_subtype_le _)) htB
  have hNY : t ∈ Subgroup.normalizer (Y : Set G) := by
    rcases hYm with rfl | rfl
    · exact ggF4QGeFour_centralizer_le_normalizer_L ha₀ hcfg (one_mem _) htH
    · exact ggF4QGeFour_centralizer_le_normalizer_K_of_noncyclic hTBF hFC hcfg hRC e hpres
        (exists_noncyclic_pSubgroup_K_S2 hKG hcfg e hpres hf hpf hrow) (one_mem _) htH
  obtain ⟨m, hm⟩ := ht2
  obtain ⟨σO, hσO, hMO⟩ : ∃ σ : Fin 3 ≃ Fin (ggU .POmegaMinus 4 f).D.rank,
      (∀ k, (σ k).val = k.val) ∧ ∀ k l, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
        (σ k) (σ l) = CoxeterMatrix.B 3 k l := by
    refine ⟨Equiv.refl _, fun k => rfl, fun k l => ?_⟩
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  suffices hkey : ∃ v : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group,
      ∀ z ∈ ggRankOneIn Y Bs
        ((εY (v * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO 2) * v⁻¹) : ↥(ggAutomizer Y Bs)) : MulAut ↥Bs), t * z = z * t by
    obtain ⟨v, hv⟩ := hkey
    have E : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple (σO 2) =
        (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple ((Equiv.refl (Fin 3)) 2) := by
      congr 1
      exact Fin.ext (hσO 2)
    rw [E] at hv
    have hF : ∃ c' : GaloisField 2 f, c' ≠ 0 ∧ c' ≠ 1 := by
      by_contra hcon
      simp only [not_exists, not_and, ne_eq, not_not] at hcon
      have hinj : Function.Injective (fun z : GaloisField 2 f => decide (z = 0)) := by
        intro z z' hzz
        by_cases hz : z = 0
        · have hz' : z' = 0 := by simpa [hz] using hzz.symm
          rw [hz, hz']
        · have hz' : z' ≠ 0 := fun h => hz (by simpa [h] using hzz)
          rw [hcon z hz, hcon z' hz']
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
        GaloisField.card 2 f (by omega)] at h1
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    exact KGCentOmMinus.mem_centralizer_of_tableBPos_short (F := GaloisField 2 f) (by omega)
      (GaloisField.card 2 f (by omega)) hF hpp hirr ψ hψ hrange εY hεY hlevY hTor hrank m hm
      (fun b hb => (Subgroup.mem_centralizer_iff.mp htB b hb).symm) hNY v hv
  obtain ⟨φY, hφY, hrefY, hY01, hY12, hY02, hYc⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hYA εY hεY σO hMO
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  have hYR := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefY k)
  have hqY : ∀ {r : MulAut ↥Bs}, r ∈ ggAutomizer Y Bs → GGIsReflection p r →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn Y Bs r) := fun hrA hr =>
    isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inl hYpos) hrA hr
  rcases hXpos with hXom | hXsu
  ·
    have hXom' := hXom
    obtain ⟨ψX, hkerX, -, εX, hεX, hlevX, -⟩ := hXom
    obtain ⟨φX, hφX, hrefX, hX01, hX12, hX02, hXc⟩ :=
      exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hXA εX hεX σO hMO
    have hXR := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefX k)
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : CoxeterMatrix.F₄.Group,
        g₀ * φX ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO 0)) * g₀⁻¹ =
        φY ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO 0)) := by
      obtain ⟨u, v, c, d, huv, hd⟩ :=
        R.exists_shared_refl_ne_two hXR hX01 hX12 hX02 hYR hY01 hY12 hY02
      have hrr := eps_eq_of_shared hφX hφY σO σO huv
      obtain ⟨wX, hwX⟩ : ∃ w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group,
          w = (u.map fun k => (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
            (σO k)).prod := ⟨_, rfl⟩
      obtain ⟨wY, hwY⟩ : ∃ w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group,
          w = (v.map fun k => (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
            (σO k)).prod := ⟨_, rfl⟩
      rw [← hwX, ← hwY] at hrr
      obtain ⟨r, hr⟩ : ∃ r : MulAut ↥Bs, r = ((εX (wX *
          (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple (σO c) *
            wX⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := ⟨_, rfl⟩
      have hrAX : r ∈ ggAutomizer X Bs := hr ▸ (εX _).2
      have hrAY : r ∈ ggAutomizer Y Bs := (hr.trans hrr) ▸ (εY _).2
      have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hεX ⟨wX, _, hr⟩
      have hSYX : ggRankOneIn Y Bs r = ggRankOneIn X Bs r :=
        ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyYB hxXB hYy hXx
          (hcfg.bstar_le_normalizer hXm) hrAY hrAX (hqY hrAY hrefl)
          (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inl hXom')
            hrAX hrefl) hrefl.1 (GGIsReflection.ne_one hpp hrefl)
      obtain ⟨F1, _, _, θ1, -, hθ1, hθ1r, hc1⟩ :=
        exists_sl2_ggRankOneIn_node_POmegaMinus (f := f) (by omega) hkerX hlevX wX
          (σO c)
      obtain ⟨F2, _, _, θ2, -, hθ2, hθ2r, hc2⟩ :=
        exists_sl2_ggRankOneIn_node_POmegaMinus (f := f) (by omega) hker hlevY wY
          (σO d)
      have hcard : Nat.card SL(2, F1) = Nat.card SL(2, F2) := by
        rw [Nat.card_congr (MonoidHom.ofInjective hθ1).toEquiv,
          Nat.card_congr (MonoidHom.ofInjective hθ2).toEquiv, hθ1r, hθ2r, ← hrr, ← hr, hSYX]
      have hFF := ggSL2_card_inj hcard
      have hd2 := val_lt_two_of_ne hd
      have hc2' : c.val < 2 := by
        by_contra hcl
        rw [hc1, hc2, hσO c, hσO d] at hFF
        simp only [hd2, hcl, if_true, if_false] at hFF
        have := Nat.pow_right_injective (le_refl 2) hFF
        omega
      obtain ⟨g1, hg1⟩ := R.exists_conj_zero_of_lt_two hXR hX01 hc2'
      obtain ⟨g2, hg2⟩ := R.exists_conj_zero_of_lt_two hYR hY01 hd2
      refine ⟨g2⁻¹ * ((v.map fun k => φY ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO k))).prod)⁻¹ *
        (u.map fun k => φX ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO k))).prod * g1, ?_⟩
      rw [show ∀ (A B C D E : CoxeterMatrix.F₄.Group), A⁻¹ * B⁻¹ * C * D * E * (A⁻¹ * B⁻¹ * C * D)⁻¹ =
          A⁻¹ * B⁻¹ * (C * (D * E * D⁻¹) * C⁻¹) * B * A from fun A B C D E => by group, hg1, huv,
        ← hg2]
      group
    have hgen := closure_sup_closure_eq_top hXA hYA hLK hXc hYc
    obtain ⟨w, i, j, hij3, hwi, hwj, ⟨h, hh⟩, hni⟩ :=
      R.exists_missed_cross hXR hX01 hX12 hX02 hYR hY01 hY12 hY02 hgen hg₀
    have hord : orderOf (R.s i * R.s j) = CoxeterMatrix.F₄ i j := by
      rw [hsimp, hsimp]
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        CoxeterMatrix.F₄.toCoxeterSystem.orderOf_simple_mul_simple i j
    have hniY : ∀ h' : CoxeterMatrix.F₄.Group, h' * φY ((coxeterMatrix
        (ggU .POmegaMinus 4 f).D.isFiniteType).simple (σO 0)) * h'⁻¹ ≠ R.s i := by
      intro h' e'
      apply hni (h' * g₀)
      rw [← e', ← hg₀]
      group
    rw [hsimp] at hwi hwj
    have hi' := (hXc _).mp hwi
    have hj' := (hYc _).mp hwj
    have hmiss : ∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup G), (Z = L ∨ Z = K) →
        (↑(e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Z Bs →
        (↑(e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹)) : MulAut ↥Bs) ∉ ggAutomizer Z Bs := by
      intro w' Z hZ h1 h2
      rcases hZXY Z hZ with hZ' | hZ'
      · rw [hZ'] at h1 h2
        exact R.not_pair_mem_of_not_conj hXR hX01 hX12 hX02 hij3 hord hni w'
          (by rw [hsimp]; exact (hXc _).mpr h1) (by rw [hsimp]; exact (hXc _).mpr h2)
      · rw [hZ'] at h1 h2
        exact R.not_pair_mem_of_not_conj hYR hY01 hY12 hY02 hij3 hord hniY w'
          (by rw [hsimp]; exact (hYc _).mpr h1) (by rw [hsimp]; exact (hYc _).mpr h2)
    have hKom : GGF4QGeFourRow.S2 = .S2 → GGCentralImage .POmegaMinus 4 f K := by
      intro _
      have hK' : GGTableBPosImage p Bs .POmegaMinus 4 f K := by
        rcases hXY with ⟨-, hYK⟩ | ⟨hXK, -⟩
        · rw [← hYK]; exact hYpos
        · rw [← hXK]; exact hXom'
      obtain ⟨ψK, hkerK, hrK, -⟩ := hK'
      exact ⟨ψK, hadm, hkerK, hrK⟩
    obtain ⟨F, _, _, Wp, hchar, hpair⟩ := hM G p B Bs x L D J y K hcfg hRC e hpres f hf hpf hrow
      hKom X Y hXY w i j hij3 hi' hj' hmiss
    have hr'refl : GGIsReflection p
        ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) :=
      ggCoxRefl_isReflection hpres.2 ⟨w, j, rfl⟩
    obtain ⟨k₀, v', hk⟩ := exists_node_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hεY hj' hr'refl
    obtain ⟨k, rfl⟩ : ∃ k : Fin 3, σO k = k₀ := ⟨σO.symm k₀, σO.apply_symm_apply k₀⟩
    have hφ' : φY v' * φY ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
        (σO k)) * (φY v')⁻¹ = w * CoxeterMatrix.F₄.simple j * w⁻¹ := by
      have h1 := e.injective (Subtype.ext ((hφY _).trans hk.symm))
      rw [map_mul, map_mul, map_inv] at h1
      exact h1
    have hk2 : k.val = 2 := by
      by_contra hk2
      have hk3 : k.val < 3 := k.isLt
      obtain ⟨g, hg⟩ := R.exists_conj_zero_of_lt_two hYR hY01 (c := k) (by omega)
      apply R.not_conj_zero_two hYR hY01 hY12 hY02 (h * w⁻¹ * φY v' * g)
      calc h * w⁻¹ * φY v' * g * φY ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
            (σO 0)) * (h * w⁻¹ * φY v' * g)⁻¹
          = h * w⁻¹ * (φY v' * (g * φY ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
            (σO 0)) * g⁻¹) * (φY v')⁻¹) * w * h⁻¹ := by group
        _ = h * w⁻¹ * (w * CoxeterMatrix.F₄.simple j * w⁻¹) * w * h⁻¹ := by rw [hg, hφ']
        _ = h * R.s j * h⁻¹ := by rw [hsimp]; group
        _ = _ := hh
    have hkeq : k = 2 := Fin.ext hk2
    subst hkeq
    obtain ⟨F3, _, _, θ3, -, hθ3, hθ3r, hc3⟩ :=
      exists_sl2_ggRankOneIn_node_POmegaMinus (f := f) (by omega) hker hlevY v'
        (σO 2)
    have hcardV := ggLinearBlockPair_card_right hpair
    rw [hk, ← hθ3r, ← Nat.card_congr (MonoidHom.ofInjective hθ3).toEquiv] at hcardV
    have hFF := ggSL2_card_inj hcardV
    have hc3' : Nat.card F3 = 2 ^ (2 * f) := by simp [hc3, hσO]
    have hF4 : 4 < Nat.card F := by
      rw [← hFF, hc3']
      calc 4 < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htU : ∀ u ∈ ggRankOneIn X Bs
        ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs), t * u = u * t := fun u hu =>
      (Subgroup.mem_centralizer_iff.mp htX u (((ggOTwoPrime_le _).trans inf_le_left) hu)).symm
    have htV := mem_normalizer_ggRankOneIn_of hNY htB
      ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs)
    have hcV := KGCentSL2.mem_centralizer_of_standardPair hF4 hpair htU htV m hm
    refine ⟨v', fun z hz => hcV z ?_⟩
    rw [hk]
    exact hz
  ·
    have hXsu' := hXsu
    obtain ⟨ψX, hkerX, -, εX, hεX, hlevX, -⟩ := hXsu
    obtain ⟨σX, hσX, hMX⟩ := exists_coxeterMatrix_PSU_six (f := f) (by omega)
    obtain ⟨φX, hφX, hrefX, hX01, hX12, hX02, -⟩ :=
      exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hXA εX hεX σX hMX
    have hXR := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefX k)
    obtain ⟨u, v, c, d, huv, hd⟩ :=
      R.exists_shared_refl_ne_two hYR hY01 hY12 hY02 hXR hX01 hX12 hX02
    have hrr := eps_eq_of_shared hφY hφX σO σX huv
    obtain ⟨wY, hwY⟩ : ∃ w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group,
        w = (u.map fun k => (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
          (σO k)).prod := ⟨_, rfl⟩
    obtain ⟨wX, hwX⟩ : ∃ w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group,
        w = (v.map fun k => (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σX k)).prod :=
      ⟨_, rfl⟩
    rw [← hwX, ← hwY] at hrr
    obtain ⟨r, hr⟩ : ∃ r : MulAut ↥Bs, r = ((εY (wY *
        (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple (σO c) *
          wY⁻¹) : ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := ⟨_, rfl⟩
    have hrAY : r ∈ ggAutomizer Y Bs := hr ▸ (εY _).2
    have hrAX : r ∈ ggAutomizer X Bs := (hr.trans hrr) ▸ (εX _).2
    have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hεY ⟨wY, _, hr⟩
    have hSYX : ggRankOneIn Y Bs r = ggRankOneIn X Bs r :=
      ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyYB hxXB hYy hXx (hcfg.bstar_le_normalizer hXm)
        hrAY hrAX (hqY hrAY hrefl)
        (isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hEl hNT hf (Or.inr hXsu') hrAX
          hrefl) hrefl.1 (GGIsReflection.ne_one hpp hrefl)
    obtain ⟨F1, _, _, θ1, -, hθ1, hθ1r, hc1⟩ :=
      exists_sl2_ggRankOneIn_node_PSU (f := f) (by omega) hkerX hlevX wX (σX d)
    obtain ⟨F2, _, _, θ2, -, hθ2, hθ2r, hc2⟩ :=
      exists_sl2_ggRankOneIn_node_POmegaMinus (f := f) (by omega) hker hlevY wY
        (σO c)
    have hcard : Nat.card SL(2, F1) = Nat.card SL(2, F2) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hθ1).toEquiv,
        Nat.card_congr (MonoidHom.ofInjective hθ2).toEquiv, hθ1r, hθ2r, ← hrr, ← hr, hSYX]
    have hFF := ggSL2_card_inj hcard
    have hd2 := val_lt_two_of_ne hd
    have hc2' : c = 2 := by
      have hcl : ¬ c.val < 2 := by
        intro hcl
        rw [hc1, hc2, hσX d, hσO c] at hFF
        simp only [hd2, hcl, if_true] at hFF
        have := Nat.pow_right_injective (le_refl 2) hFF
        omega
      have h3 := c.isLt
      exact Fin.ext (by show c.val = 2; omega)
    subst hc2'
    refine ⟨wY, fun z hz => ?_⟩
    rw [← hr, hSYX] at hz
    exact (Subgroup.mem_centralizer_iff.mp htX z (((ggOTwoPrime_le _).trans inf_le_left) hz)).symm

end CFSG.StandardType

end
