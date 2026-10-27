module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.UnitaryHeisPhan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan

namespace CFSG.RankThree.PartTwo.Sec19

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem heisB12_le_of_generic_homology (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) {a : K} (ha : orderOf a = ℓ ^ f + 1)
    {Q : Subgroup (unitarySU ℓ f K 3)}
    (hge1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hge3 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {w : Fin 3 → K}
    (hwN : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = 1)
    (hw0 : w 0 ≠ 0) (hw1 : w 1 ≠ 0) (hw2 : w 2 ≠ 0) (hn2 : h.bar (w 2) * w 2 ≠ 1)
    (hgw : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) w) :
    heisB12 ℓ f K ≤ Q := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨ge1, hge1Q, hge1m⟩ := hge1
  obtain ⟨ge3, hge3Q, hge3m⟩ := hge3
  obtain ⟨gw, hgwQ, hgwm⟩ := hgw
  have hApp := su2_block_mem_of_generic h hℓ3 h17 hq3 ha (Q.map (unitarySU ℓ f K 3).subtype)
    ⟨(ge1 : GL (Fin 3) K), ⟨ge1, hge1Q, rfl⟩, hge1m⟩
    ⟨(ge3 : GL (Fin 3) K), ⟨ge3, hge3Q, rfl⟩, hge3m⟩
    (w := w) hwN hw0 hw1 hw2
    (by
      intro h0
      apply hn2
      linear_combination hwN - h0)
    ⟨(gw : GL (Fin 3) K), ⟨gw, hgwQ, rfl⟩, hgwm⟩
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨x, hx, hxA⟩ := hApp A hA
  have : x = g := Subtype.ext (hxA.trans (Units.ext hgA).symm)
  rw [← this]
  exact hx

theorem heisB12_conj_le_of_generic_homology
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f)
    {a : K} (ha : orderOf a = ℓ ^ f + 1)
    {Q : Subgroup (unitarySU ℓ f K 3)} (s : unitarySU ℓ f K 3)
    (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS)
    (hge1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0])
    (hge3 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    {z : Fin 3 → K}
    (hzN : h.bar (z 0) * z 0 + h.bar (z 1) * z 1 + h.bar (z 2) * z 2 = 1)
    (hz0 : z 0 ≠ 0) (hz1 : z 1 ≠ 0) (hz2 : z 2 ≠ 0) (hn0 : h.bar (z 0) * z 0 ≠ 1)
    (hgz : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) z) :
    ∀ x ∈ heisB12 ℓ f K, s * x * s⁻¹ ∈ Q := by
  let H' : Subgroup (unitarySU ℓ f K 3) := Q.comap (MulAut.conj s).toMonoidHom
  have hmemH' : ∀ x : unitarySU ℓ f K 3, x ∈ H' ↔ s * x * s⁻¹ ∈ Q := fun x => Iff.rfl
  have hs' : (((s⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hSᵀ := by
    rw [val_inv_eq_star h s, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS]
  have hconjmat : ∀ g : unitarySU ℓ f K 3,
      (((s⁻¹ * g * s : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        hSᵀ * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * hS := fun g => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs', hs]
  have hPT : (hSᵀ.map h.bar)ᵀ = hS := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS]
  have hP : hSᵀ * (hSᵀ.map h.bar)ᵀ = 1 := by
    rw [hPT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS, Matrix.mul_apply, Fin.sum_univ_three]
  have hconjhom : ∀ u : Fin 3 → K, hSᵀ * homMat h a (a⁻¹ ^ 2 - a) u * hS =
      homMat h a (a⁻¹ ^ 2 - a) (hSᵀ *ᵥ u) := fun u => by
    have hc := conj_homMat h (ρ := a) (κ := a⁻¹ ^ 2 - a) u hP
    rwa [hPT] at hc
  have hcancel : ∀ g : unitarySU ℓ f K 3, s * (s⁻¹ * g * s) * s⁻¹ = g := fun g => by group
  have hwit : ∀ g ∈ Q, ∃ x ∈ H', ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hSᵀ * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * hS := fun g hg =>
    ⟨s⁻¹ * g * s, (hmemH' _).2 (by rw [hcancel]; exact hg), hconjmat g⟩
  have hvT1 : hSᵀ *ᵥ ![0, 1, 0] = (![1, 0, 0] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hvT2 : hSᵀ *ᵥ ![1, 0, 0] = (![0, 0, 1] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hvTz : hSᵀ *ᵥ z = ![z 1, z 2, z 0] := by
    ext i
    fin_cases i <;> simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  obtain ⟨g1, hg1Q, hg1m⟩ := hge1
  obtain ⟨g3, hg3Q, hg3m⟩ := hge3
  obtain ⟨gz, hgzQ, hgzm⟩ := hgz
  have hH1 : ∃ x ∈ H', ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0] := by
    obtain ⟨x, hx, hxm⟩ := hwit g1 hg1Q
    exact ⟨x, hx, by rw [hxm, hg1m, hconjhom, hvT1]⟩
  have hH3 : ∃ x ∈ H', ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1] := by
    obtain ⟨x, hx, hxm⟩ := hwit g3 hg3Q
    exact ⟨x, hx, by rw [hxm, hg3m, hconjhom, hvT2]⟩
  have hHz : ∃ x ∈ H', ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![z 1, z 2, z 0] := by
    obtain ⟨x, hx, hxm⟩ := hwit gz hgzQ
    exact ⟨x, hx, by rw [hxm, hgzm, hconjhom, hvTz]⟩
  have hwN' : h.bar (![z 1, z 2, z 0] 0) * ![z 1, z 2, z 0] 0 +
      h.bar (![z 1, z 2, z 0] 1) * ![z 1, z 2, z 0] 1 +
      h.bar (![z 1, z 2, z 0] 2) * ![z 1, z 2, z 0] 2 = 1 := by
    show h.bar (z 1) * z 1 + h.bar (z 2) * z 2 + h.bar (z 0) * z 0 = 1
    linear_combination hzN
  have hw := heisB12_le_of_generic_homology h hq3 hℓ3 h17 ha (Q := H') hH1 hH3
    (w := ![z 1, z 2, z 0]) hwN' hz1 hz2 hz0 hn0 hHz
  intro x hx
  exact (hmemH' x).1 (hw hx)

theorem eq_top_of_heisB12_conj_le (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    {Q : Subgroup (unitarySU ℓ f K 3)} {s : unitarySU ℓ f K 3}
    (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS)
    (hB : heisB12 ℓ f K ≤ Q) (hB' : ∀ x ∈ heisB12 ℓ f K, s * x * s⁻¹ ∈ Q) : Q = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  let ε : Su K ℓ f 3 ≃* unitarySU ℓ f K 3 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3)
  have hε : ∀ x : Su K ℓ f 3, ((ε x : unitarySU ℓ f K 3) : GL (Fin 3) K) = (x : GL (Fin 3) K) :=
    fun x => rfl
  have hmem2 : ∀ x : Su K ℓ f 2, ((x : GL (Fin 2) K)) ∈ unitarySU ℓ f K 2 := fun x => by
    exact (Subgroup.ext_iff.1 (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2)
      (x : GL (Fin 2) K)).1 x.2
  have h0mem : ∀ x : Su K ℓ f 2, ε (blockEmb2 K ℓ f 2 0 x) ∈ heisB12 ℓ f K := fun x => by
    rw [mem_heisB12]
    refine ⟨(x : GL (Fin 2) K), hmem2 x, ?_⟩
    rw [hε, blockEmb2, coe_coe_blockEmb]
    change blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [blockMat_zero_eq]
    rfl
  have h0 : ∀ x : Su K ℓ f 2, ε (blockEmb2 K ℓ f 2 0 x) ∈ Q := fun x => hB (h0mem x)
  have h1 : ∀ x : Su K ℓ f 2, ε (blockEmb2 K ℓ f 2 1 x) ∈ Q := fun x => by
    have e : ε (blockEmb2 K ℓ f 2 1 x) = s * ε (blockEmb2 K ℓ f 2 0 x) * s⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      have hs' : (((s⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          hSᵀ := by
        rw [val_inv_eq_star h s, hs]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hS]
      rw [hε, blockEmb2, coe_coe_blockEmb, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, hs', hs, hε, blockEmb2, coe_coe_blockEmb]
      change blockMat 3 1 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        hS * blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * hSᵀ
      rw [blockMat_one_eq, blockMat_zero_eq]
    rw [e]
    exact hB' _ (h0mem x)
  have hgen : ⨆ i : Fin 2, (ε.toMonoidHom.comp (blockEmb2 K ℓ f 2 i)).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) hK hq 2
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [MonoidHom.range_comp] using h2
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun i => ?_
  rintro _ ⟨x, rfl⟩
  fin_cases i
  · exact h0 x
  · exact h1 x

end CFSG.RankThree.PartTwo.Sec19
