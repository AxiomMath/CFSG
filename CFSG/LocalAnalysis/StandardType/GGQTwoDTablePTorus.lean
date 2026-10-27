module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryTorusCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.StandardType.LineU CFSG.StandardType.UnitTB

private theorem ggDelUTorus_card_le_of_diagModel
    {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent 3 A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t) :
    3 ^ (d - 2) ≤ Nat.card A := by
  classical
  have hTle : CFSG.RankThree.PartOne.KFU.torusSU 3 d K ≤ unitarySU 2 n K d :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hM.field hpq
  set T : Subgroup ↥(unitarySU 2 n K d) :=
    (CFSG.RankThree.PartOne.KFU.torusSU 3 d K).subgroupOf (unitarySU 2 n K d) with hTdef
  have hTcard : Nat.card T = 3 ^ (d - 1) := by
    rw [hTdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact ggTwA_torusSU_card hK hn Nat.prime_three hpq (by omega)
  set ψ : ↥T →* MulAut L' :=
    (MulAut.conj : L' →* MulAut L').comp (φ.comp T.subtype) with hψ
  have hrange : ψ.range ≤ A := by
    rintro _ ⟨t, rfl⟩
    have hTmem : (t.1 : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU 3 d K :=
      Subgroup.mem_subgroupOf.mp t.2
    obtain ⟨e, _he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hTmem
    have hmat : ((t.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => (e i : K)) := by
      rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_val]
    have hfix : ∀ a ∈ A, a (φ t.1) = φ t.1 := by
      intro a ha
      obtain ⟨u, hu⟩ := hdiag a ha
      exact hu.fix_of_diagonal t.1 hmat
    have hpow : (φ t.1) ^ 3 = 1 := by
      rw [← map_pow, ggTwA_torus_pow t.1 hTmem, map_one]
    exact hsc (φ t.1) hfix hpow
  have hker : ψ.ker.map T.subtype ≤
      T ⊓ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t.2, ?_⟩
    have h1 : ∀ y : ↥(unitarySU 2 n K d), φ (t.1 * y * t.1⁻¹) = φ y := by
      intro y
      have h := congrArg (fun f : MulAut L' => f (φ y)) (MonoidHom.mem_ker.mp ht)
      simpa [hψ, MulAut.conj_apply, map_mul, map_inv] using h
    obtain ⟨c, hc⟩ := UnitTB.scalar_of_map_conj_eq hM hK hd h1
    exact ggTwA_mem_scalars (by omega) (Subgroup.mem_subgroupOf.mp t.2) hc
  have hZs : Nat.card (T ⊓ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) :
      Subgroup ↥(unitarySU 2 n K d)) ≤ 3 :=
    ggTwA_scalarSubgroup_card_le Nat.prime_three (by omega)
  have hkercard : Nat.card ψ.ker ≤ 3 := by
    have h1 := Subgroup.card_le_of_le hker
    rw [Subgroup.card_map_of_injective T.subtype_injective] at h1
    exact h1.trans hZs
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card T :=
    Subgroup.card_ker_mul_card_range ψ
  have hAcard : Nat.card ψ.range ≤ Nat.card A := Subgroup.card_le_of_le hrange
  have h2 : 3 ^ (d - 1) ≤ 3 * Nat.card A := by
    calc 3 ^ (d - 1) = Nat.card ψ.ker * Nat.card ψ.range := by rw [hmul, hTcard]
      _ ≤ 3 * Nat.card A := Nat.mul_le_mul hkercard hAcard
  have h3 : 3 ^ (d - 1) = 3 * 3 ^ (d - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h3] at h2
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

private theorem ggDelUTorus_exists_unitary_model {p : ℕ} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {labX : LargeEvenLabel} (hA : labX.tag = .twA)
    (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ labX.n) ^ 2 ∧
      ∃ θ : X ⧸ Subgroup.center X ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)),
        GGInducedInn A θ (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)))
          (LargeEvenGUSet (Fin (labX.rank + 1)) K (2 ^ labX.n))) := by
  classical
  rw [GGTPNMarked, LargeEvenMarking] at hm
  obtain ⟨-, lab, hlab, hraw⟩ := hm
  obtain ⟨t, l, n⟩ := labX
  subst hA
  obtain ⟨R, _, I, F, -, -, θ₀, hlab, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfin, hcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hhalf, hind⟩ := hQ
  exact ⟨K, hKfield, hKfin, hcard, θ, hind⟩

theorem ggDelU_torus_le_card
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hself : GGTPNSelfCent 3 A)
    (hm : GGTPNMarked 3 (fun _ _ => True) A) (hperf : commutator X = ⊤) {N : ℕ} (hN9 : 9 ≤ N)
    (h3N : 3 ∣ N) (hhX : GGHasLabel ⟨.twA, N - 1, 1⟩ (X ⧸ Subgroup.center X))
    (hbig : 3 ^ (N / 3 + 1) < Nat.card A) : 3 ^ (N - 2) ≤ Nat.card A := by
  classical
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hΛX : LargeEvenInLambda2 (⟨.twA, N - 1, 1⟩ : LargeEvenLabel) := by
    norm_num [LargeEvenInLambda2]
    omega
  have hRA : GGKacRA (⟨.twA, N - 1, 1⟩ : LargeEvenLabel) 3 := by
    refine Or.inr ⟨rfl, ?_, by norm_num⟩
    have hN1 : 1 ≤ N := by omega
    rwa [Nat.sub_add_cancel hN1]
  have hm' : GGTPNMarked 3 (fun _ lab => lab = (⟨.twA, N - 1, 1⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have hN1 : 1 ≤ N := by omega
  let M : ℕ := (⟨.twA, N - 1, 1⟩ : LargeEvenLabel).rank + 1
  have hMN : M = N := by
    change (⟨.twA, N - 1, 1⟩ : LargeEvenLabel).rank + 1 = N
    simp [Nat.sub_add_cancel hN1]
  obtain ⟨K, hKfield, hKfin, hcard, θ, hind⟩ :=
    ggDelUTorus_exists_unitary_model (labX := (⟨.twA, N - 1, 1⟩ : LargeEvenLabel)) rfl hm'
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hcard4 : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hcard
  have hA3 : IsPGroup 3 A := isPGroup_of_isElemAbelian hA
  obtain ⟨k, hk⟩ := hA3.exists_card_eq
  have hkbig : N / 3 + 2 ≤ k := by
    have h : 3 ^ (N / 3 + 1) < 3 ^ k := by rw [← hk]; exact hbig
    exact Nat.succ_le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h)
  have hcardA : 3 ^ (M / 3 + 2) ≤ Nat.card A := by
    rw [hMN, hk]
    exact Nat.pow_le_pow_right (by norm_num) hkbig
  have hM5 : 5 ≤ M := by omega
  have hM6 : (M, 1) ≠ (6, 1) := by
    intro h
    have h1 : M = 6 := congrArg Prod.fst h
    omega
  have h3M : 3 ∣ M := by rw [hMN]; exact h3N
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K M))
      (LargeEvenGUSet (Fin M) K (2 ^ 1)), ∀ l : X,
        x (θ (l : X ⧸ Subgroup.center X)) = θ ((a l : X) : X ⧸ Subgroup.center X) := by
    intro a ha
    exact ⟨ggInducedAut θ a, hind a ha, fun l => ggInducedAut_apply θ a l⟩
  let ψ : X →* LargeEvenProj (unitarySU 2 1 K M) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ ((x : X ⧸ Subgroup.center X)) = 1 := hx
    have h1 : (x : X ⧸ Subgroup.center X) = 1 := θ.injective (by rw [map_one]; exact hx')
    rwa [QuotientGroup.eq_one_iff] at h1
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hcard4 le_rfl hM5 Nat.prime_three (by norm_num) h3M
      (LineU.unitaryCoverAt hcard4 hM5 hM6) hψ hker hperf hA hAI hcardA
  have hMdl : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hcard4 le_rfl, hφs, hφker⟩
  have hres :=
    ggDelUTorus_card_le_of_diagModel hcard4 le_rfl (by norm_num) (by omega) hMdl hself hdiag
  simpa [hMN] using hres

end CFSG.StandardType

end
