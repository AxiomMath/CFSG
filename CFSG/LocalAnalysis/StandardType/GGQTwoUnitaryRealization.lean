module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage

public section

namespace CFSG.StandardType.QTwoUnitary

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.TableBUD
open CFSG.StandardType.InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {K : Type} [Field K] [Finite K] {d : ℕ}

theorem three_pow_lt_full (d : ℕ) (hd : 4 ≤ d) :
    3 ^ (d / 3 + 1) < 3 ^ (d - 1) := by
  apply Nat.pow_lt_pow_right (by norm_num)
  omega

theorem three_pow_lt_heart (d : ℕ) (hd : 6 ≤ d) :
    3 ^ (d / 3 + 1) < 3 ^ (d - 2) := by
  apply Nat.pow_lt_pow_right (by norm_num)
  omega

theorem card_normalized_weights {K : Type} [Field K] {d : ℕ}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 1 ≤ d) :
    Nat.card {σ : Fin d → Kˣ // σ ⟨0, hd⟩ = 1} = 3 ^ (d - 1) := by
  have hK3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
    norm_num
  set ev : (Fin d → Kˣ) →* Kˣ := Pi.evalMonoidHom (fun _ => Kˣ) ⟨0, hd⟩ with hev
  have hrange : ev.range = ⊤ := MonoidHom.range_eq_top.mpr fun a => ⟨fun _ => a, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range ev
  rw [hrange, Subgroup.card_top, Nat.card_fun, Nat.card_fin, hK3] at h1
  have h2 : 3 ^ d = 3 ^ (d - 1) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

omit [Finite G] [Finite K] in
theorem range_ggBeta_le_inndiagU_of_induces (h : UnitaryFieldData 2 1 K)
    (hd : 1 ≤ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ inndiagU h hd,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    (ggBeta L θ hN).range ≤ inndiagU h hd := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨φ, hφ, hind⟩ := h3 b b.2
  have hφeq : φ = ggLAut L θ ⟨b⁻¹, Subgroup.inv_mem _ (hN b.2)⟩ :=
    eq_ggLAut_of_induces L θ (hN b.2) hind
  have hinv : ggLAut L θ ⟨b, hN b.2⟩ =
      (ggLAut L θ ⟨b⁻¹, Subgroup.inv_mem _ (hN b.2)⟩)⁻¹ := by
    have h1 : (⟨b, hN b.2⟩ : Subgroup.normalizer (L : Set G)) *
        ⟨b⁻¹, Subgroup.inv_mem _ (hN b.2)⟩ = 1 := by
      ext; simp
    have h2 := congrArg (ggLAut L θ) h1
    rw [map_mul, map_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  rw [ggBeta_eq, hinv]
  exact Subgroup.inv_mem _ (hφeq ▸ hφ)

omit [Finite G] in
theorem exists_frame_full (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hd : 4 ≤ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 3 Bs)
    (hI : (ggBeta L θ hN).range ≤ inndiagU h (by omega))
    (hcard : Nat.card ↥(ggBeta L θ hN).range = 3 ^ (d - 1)) :
    ∃ (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d)),
      (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧ FrameAct h Q hQ e σ) ∧
      (∀ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 →
        ∃ e ∈ (ggBeta L θ hN).range, FrameAct h Q hQ e σ) := by
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ 1 = 2) := by omega
  have hEA : IsElemAbelian 3 (ggBeta L θ hN).range := isElemAbelian_range_ggBeta θ hE hN
  have hbig : 3 ^ (d / 3 + 1) < Nat.card ↥(ggBeta L θ hN).range := by
    rw [hcard]
    exact three_pow_lt_full d hd
  obtain ⟨Q, hQ, hfr⟩ := exists_frame_inndiag (n := 1) (h := h) hK hd3 hdq hq
    Nat.prime_three (by norm_num) hEA hI hbig
  refine ⟨Q, hQ, hfr, ?_⟩
  classical
  let F : ↥(ggBeta L θ hN).range → {σ : Fin d → Kˣ // σ ⟨0, by omega⟩ = 1} := fun e =>
    ⟨Classical.choose (hfr e e.2), (Classical.choose_spec (hfr e e.2)).1⟩
  have hFinj : Function.Injective F := by
    intro e e' hee
    obtain ⟨h0, hp', hn, hfr'⟩ := Classical.choose_spec (hfr e e.2)
    obtain ⟨h0', hp'', hn', hfr''⟩ := Classical.choose_spec (hfr e' e'.2)
    have hσ : Classical.choose (hfr e e.2) = Classical.choose (hfr e' e'.2) :=
      congrArg Subtype.val hee
    rw [hσ] at hfr'
    exact Subtype.ext (FrameAct.unique hn' hfr' hfr'')
  have hcardW : Nat.card {σ : Fin d → Kˣ // σ ⟨0, by omega⟩ = 1} = 3 ^ (d - 1) :=
    card_normalized_weights hK (by omega)
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr ⟨hFinj, by rw [hcard, hcardW]⟩
  intro σ hσ
  obtain ⟨e, he⟩ := hbij.2 ⟨σ, hσ⟩
  refine ⟨e, e.2, ?_⟩
  have hσeq : Classical.choose (hfr e e.2) = σ := congrArg Subtype.val he
  have hfr' := (Classical.choose_spec (hfr e e.2)).2.2.2
  rwa [hσeq] at hfr'

omit [Finite G] in
theorem exists_frame_heart (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hd : 6 ≤ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 3 Bs)
    (hI : (ggBeta L θ hN).range ≤ inndiagU h (by omega))
    (hcard : Nat.card ↥(ggBeta L θ hN).range = 3 ^ (d - 2)) :
    ∃ (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d)),
      (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧ FrameAct h Q hQ e σ) ∧
      Nat.card ↥(frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range) = 3 ^ (d - 2) := by
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ 1 = 2) := by omega
  have hEA : IsElemAbelian 3 (ggBeta L θ hN).range := isElemAbelian_range_ggBeta θ hE hN
  have hbig : 3 ^ (d / 3 + 1) < Nat.card ↥(ggBeta L θ hN).range := by
    rw [hcard]
    exact three_pow_lt_heart d hd
  obtain ⟨Q, hQ, hfr⟩ := exists_frame_inndiag (n := 1) (h := h) hK hd3 hdq hq
    Nat.prime_three (by norm_num) hEA hI hbig
  refine ⟨Q, hQ, hfr, ?_⟩
  rw [card_frameWeights hK hd3 hdq Nat.prime_three (by norm_num) hfr, hcard]

theorem exists_frame_full_of_index (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 4 ≤ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ inndiagU h (by omega),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ (d - 1)) :
    ∃ (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d)),
      (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧ FrameAct h Q hQ e σ) ∧
      (∀ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 →
        ∃ e ∈ (ggBeta L θ hN).range, FrameAct h Q hQ e σ) := by
  have hL : commutator L = ⊤ := hS.2.1.1
  have hE : IsElemAbelian 3 Bs := by
    rw [← hp3]
    exact hS.1.1.2.1.2.1
  have hcard : Nat.card ↥(ggBeta L θ hN).range = 3 ^ (d - 1) := by
    rw [QTwoCav.beta_card hL θ hN, hidx]
  exact exists_frame_full h (by simpa using hK) hd θ hN hE
    (range_ggBeta_le_inndiagU_of_induces h (by omega) θ hN h3) hcard

theorem exists_frame_heart_of_index (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 6 ≤ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ inndiagU h (by omega),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ (d - 2)) :
    ∃ (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d)),
      (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧ FrameAct h Q hQ e σ) ∧
      Nat.card ↥(frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range) = 3 ^ (d - 2) := by
  have hL : commutator L = ⊤ := hS.2.1.1
  have hE : IsElemAbelian 3 Bs := by
    rw [← hp3]
    exact hS.1.1.2.1.2.1
  have hcard : Nat.card ↥(ggBeta L θ hN).range = 3 ^ (d - 2) := by
    rw [QTwoCav.beta_card hL θ hN, hidx]
  exact exists_frame_heart h (by simpa using hK) hd θ hN hE
    (range_ggBeta_le_inndiagU_of_induces h (by omega) θ hN h3) hcard

theorem exists_frame_of_marking_twA_full
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ lab.rank) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1))),
        (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
          σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
          (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
          FrameAct h Q hQ e σ) ∧
        (∀ σ : Fin (lab.rank + 1) → Kˣ, σ ⟨0, by omega⟩ = 1 →
          ∃ e ∈ (ggBeta L θ hN).range, FrameAct h Q hQ e σ) := by
  classical
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, _, hpred⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hlab'eq, -, -⟩ := hpred
  rw [hlab'eq] at hraw hlab'
  have hn1 : lab.n = 1 := by
    rw [GGLabQTwo] at hq2
    exact Nat.le_antisymm (by omega) hlab'.1
  have hd4 : 4 ≤ lab.rank + 1 := by
    rw [GGLabQTwo] at hq2
    rw [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab'
    simp only at hlab'
    omega
  rw [CFSG.Assembly.LargeEvenRawDatumLegacy, htag] at hraw
  rw [hn1] at hraw
  obtain ⟨K, hfield, hfin, hKcard, hQc⟩ := hraw
  letI := hfield
  letI := hfin
  obtain ⟨-, -, θ, hpred'⟩ := hQc
  obtain ⟨-, hN, h3I⟩ := hpred'
  let hU : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hKcard (by norm_num)
  have h3D : ∀ b ∈ Bs, ∃ φ ∈ inndiagU hU (by omega),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    obtain ⟨φ, hφI, hind⟩ := h3I b hb
    exact ⟨φ, (mem_inndiagU (h := hU) (hd := by omega)).mpr
      (congr_mem_primeFormD hU (by omega) hKcard hφI), hind⟩
  have hidx' : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      3 ^ ((lab.rank + 1) - 1) := by
    have hsub : (lab.rank + 1) - 1 = lab.rank := by omega
    rw [hsub, ← hp3]
    exact hidx
  obtain ⟨Q, hQ, hfr, hex⟩ := exists_frame_full_of_index hS hp3 hU hKcard hd4 θ hN h3D hidx'
  exact ⟨K, hfield, hfin, hU, hKcard, θ, hN, Q, hQ, hfr, hex⟩

theorem exists_frame_of_marking_twA_heart
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1)) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1))),
        (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
          σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
          (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
          FrameAct h Q hQ e σ) ∧
        Nat.card ↥(frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range) =
          3 ^ ((lab.rank + 1) - 2) := by
  classical
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, _, hpred⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hlab'eq, -, -⟩ := hpred
  rw [hlab'eq] at hraw hlab'
  have hn1 : lab.n = 1 := by
    rw [GGLabQTwo] at hq2
    exact Nat.le_antisymm (by omega) hlab'.1
  have hd6 : 6 ≤ lab.rank + 1 := by
    rw [GGLabQTwo] at hq2
    rw [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab'
    simp only at hlab'
    obtain ⟨k, hk⟩ := h3d
    omega
  rw [CFSG.Assembly.LargeEvenRawDatumLegacy, htag] at hraw
  rw [hn1] at hraw
  obtain ⟨K, hfield, hfin, hKcard, hQc⟩ := hraw
  letI := hfield
  letI := hfin
  obtain ⟨-, -, θ, hpred'⟩ := hQc
  obtain ⟨-, hN, h3I⟩ := hpred'
  let hU : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hKcard (by norm_num)
  have h3D : ∀ b ∈ Bs, ∃ φ ∈ inndiagU hU (by omega),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    obtain ⟨φ, hφI, hind⟩ := h3I b hb
    exact ⟨φ, (mem_inndiagU (h := hU) (hd := by omega)).mpr
      (congr_mem_primeFormD hU (by omega) hKcard hφI), hind⟩
  have hsub : (lab.rank + 1) - 2 = lab.rank - 1 := by omega
  have hidx' : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      3 ^ ((lab.rank + 1) - 2) := by
    rw [hsub, ← hp3]
    exact hidx
  obtain ⟨Q, hQ, hfr, hcardW⟩ :=
    exists_frame_heart_of_index hS hp3 hU hKcard hd6 θ hN h3D hidx'
  exact ⟨K, hfield, hfin, hU, hKcard, θ, hN, Q, hQ, hfr, hcardW⟩

end CFSG.StandardType.QTwoUnitary

end
