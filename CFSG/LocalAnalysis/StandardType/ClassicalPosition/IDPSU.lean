module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Assembly.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_levelWeyl_agree_last {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2)
    {G : Type*} [Group G] (ψ β : SU (unitaryInvolution F 2 f) n →* G)
    (d : Fin n → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1)
    (hker : (ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd))).ker ≤ Subgroup.center _)
    (hpos : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1),
      β z = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z))
    (t : Fin n → F) (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1)
    (hneg : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1),
      β z = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z)) :
    β (levelWeyl (unitaryInvolution_involutive hF) oneTZ k) =
      ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)
        (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)) := by
  have hp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hp
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have h0t := ne_zero_of_unitary ht
  have h0d := ne_zero_of_unitary hd
  have hdi : ∀ s, unitaryInvolution F 2 f ((d s)⁻¹) * (d (Fin.rev s))⁻¹ = 1 := fun s => by
    rw [map_inv₀, ← mul_inv, hd s, inv_one]
  set p := lowIdx (n := n) k with hpdef
  set e := (d (Fin.rev p))⁻¹ * t (Fin.rev p) * (t (Fin.rev (Fin.rev p)))⁻¹ *
    d (Fin.rev (Fin.rev p)) with he
  have hX : ∀ z, β (longRootHom _ hp (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp (Multiplicative.ofAdd z)) := fun z =>
    hpos _ (longRootHom_mem_last hF hk z).1
  have hY : ∀ z : traceZero (unitaryInvolution F 2 f), ∃ z' : traceZero (unitaryInvolution F 2 f),
      (z' : F) = e * z ∧ β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
        γ' (longRootHom _ hp' (Multiplicative.ofAdd z')) := by
    intro z
    set w : traceZero (unitaryInvolution F 2 f) :=
      ⟨t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹, (mem_traceZero _).mpr
        (mul_mem_traceZero_of_unitary ht (Fin.rev p) ((mem_traceZero _).mp z.2))⟩ with hw
    refine ⟨⟨(d (Fin.rev p))⁻¹ * w * ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹, (mem_traceZero _).mpr
      (mul_mem_traceZero_of_unitary hdi (Fin.rev p) ((mem_traceZero _).mp w.2))⟩, ?_, ?_⟩
    · show (d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
        ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹ = e * z
      rw [he, inv_inv]
      ring
    · rw [hneg _ (longRootHom_mem_last hF hk z).2]
      show ψ (conjSU (diagJ t ht) _ (longRootHom _ hp' (Multiplicative.ofAdd z))) =
        ψ (conjSU (diagJ d hd) _ (longRootHom _ hp' (Multiplicative.ofAdd _)))
      rw [conjSU_diagJ_longRootHom, conjSU_diagJ_longRootHom]
      congr 1
      apply longRootHom_congr
      show t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹ =
        d (Fin.rev p) * ((d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
          ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹) * (d (Fin.rev (Fin.rev p)))⁻¹
      field_simp [h0d (Fin.rev p), h0d (Fin.rev (Fin.rev p)), h0t (Fin.rev (Fin.rev p))]
      rw [mul_div_mul_right _ _ (h0d _)]
  have he1 : e = 1 := eq_one_of_rankOne_long hF (by omega) hnq hp β γ' hker e hX hY
  have hY1 : ∀ z, β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp' (Multiplicative.ofAdd z)) := by
    intro z
    obtain ⟨z', hz', h⟩ := hY z
    rw [h, longRootHom_congr hp' (by rw [hz', he1, one_mul] : (z' : F) = z)]
  show β (levelWeyl _ oneTZ k) = γ' (levelWeyl _ oneTZ k)
  unfold levelWeyl
  rw [dite_eq_right hk, longWeyl_def]
  simp only [map_mul, hX, hY1]

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_exists_diagJ_of_torus {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (h2f : 2 ^ f ≠ 2)
    {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (hker : ψ.ker ≤ Subgroup.center _) (x : G)
    (hx : ∀ γ ∈ (rootDatum hF n).roots, ∃ h ∈ ggTorus (rootDatum hF n),
      ∀ z ∈ (rootDatum hF n).rootGroup γ, x⁻¹ * ψ z * x = ψ (h * z * h⁻¹)) :
    ∃ (d : Fin n → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1),
      ∀ u, x⁻¹ * ψ u * x = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) u) := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h => h2f (congrArg Prod.snd h)
  have hσ := unitaryInvolution_involutive hF
  have hdiag : ∀ γ ∈ (rootDatum hF n).roots, ∃ t : Fin n → F,
      ∃ ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1,
        ∀ z ∈ rootGroup _ hσ n γ,
          x⁻¹ * ψ z * x = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z) := by
    intro γ hγ
    obtain ⟨h, hh, hz⟩ := hx γ hγ
    obtain ⟨hd1, hd2⟩ := eq_diagonal_of_mem_ggTorus hF hh
    exact ⟨_, hd2, fun z hzm => by rw [hz z hzm, conj_eq_conjSU_diagJ hd1 hd2]⟩
  choose! T hT hTz using hdiag
  have hsr : ∀ k : Fin (n / 2), Pi.single k 1 ∈ (rootDatum hF n).roots := fun k =>
    single_mem_roots (D := rootDatum hF n) k
  have hnr : ∀ k : Fin (n / 2), -Pi.single k 1 ∈ (rootDatum hF n).roots := fun k =>
    neg_single_mem_roots (D := rootDatum hF n) k
  set Tp : Fin (n / 2) → Fin n → F := fun k => T (Pi.single k 1) with hTp
  have hTp0 : ∀ k s, Tp k s ≠ 0 := fun k s => ne_zero_of_unitary (hT _ (hsr k)) s
  set L : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩ with hL
  have hLlast : ¬ L.val + 1 < n / 2 := by simp only [hL]; omega
  set μ : F := if h : Even n then 1 else Tp L (midIdx n h) with hμ
  have hμu : unitaryInvolution F 2 f μ * μ = 1 := by
    rw [hμ]
    split_ifs with h
    · rw [map_one, one_mul]
    · have := hT _ (hsr L) (midIdx n h)
      rwa [rev_midIdx h] at this
  set lam := lowPart n Tp (Tp L (lowIdx L)) with hlam
  have hlam0 : ∀ a, lam a ≠ 0 := lowPart_ne_zero hTp0 (hTp0 L _)
  set d := extU (unitaryInvolution F 2 f) n lam μ with hddef
  have hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1 :=
    extU_unitary hσ hlam0 hμu
  refine ⟨d, hd, ?_⟩
  set β : SU (unitaryInvolution F 2 f) n →* G := (MulAut.conj x⁻¹).toMonoidHom.comp ψ with hβ
  have hβx : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [hβ]
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have hker' : γ'.ker ≤ Subgroup.center _ := ker_comp_conjSU_le_center ψ hker _ _
  have hA : ∀ k : Fin (n / 2), ∀ z ∈ rootGroup _ hσ n (Pi.single k 1), β z = γ' z := by
    intro k z hz
    rw [hβx, hTz _ (hsr k) z hz]
    show ψ _ = ψ _
    congr 1
    refine conjSU_diagJ_eq_of_ratio _ _ _ _ z (ratio_of_mem_simple hσ (hT _ (hsr k)) hd ?_ ?_ hz)
    · intro hk
      rw [hddef, extU_lowIdx, extU_lowIdx, hlam]
      exact lowPart_ratio hTp0 (hTp0 L _) hk
    · intro hk
      have hkL : k = L := Fin.ext (by simp only [hL]; omega)
      subst hkL
      refine ⟨?_, fun s hs => ?_⟩
      · rw [hddef, extU_lowIdx, hlam, lowPart_last _ _ hk]
        rfl
      · have hodd : ¬ Even n := fun he => rev_ne_self_of_even he s hs
        have hs' : s = midIdx n hodd := Fin.ext (by
          have h1 := congrArg Fin.val hs
          simp only [Fin.val_rev] at h1
          simp only [midIdx]
          omega)
        rw [hddef, extU_of_rev_eq _ _ hs, hμ, dite_eq_right hodd, hs']
        rfl
  have hW : ∀ k : Fin (n / 2), β (levelWeyl hσ oneTZ k) = γ' (levelWeyl hσ oneTZ k) := by
    intro k
    by_cases hk : k.val + 1 < n / 2
    · exact levelWeyl_agree_short hF (by omega) hk ψ β d hd hker' (fun z hz => hA k z hz)
        (T (-Pi.single k 1)) (hT _ (hnr k)) (fun z hz => by rw [hβx]; exact hTz _ (hnr k) z hz)
    · exact idPSU_levelWeyl_agree_last hF hn hnq hk ψ β d hd hker' (fun z hz => hA k z hz)
        (T (-Pi.single k 1)) (hT _ (hnr k)) (fun z hz => by rw [hβx]; exact hTz _ (hnr k) z hz)
  have hE : β.eqLocus γ' = ⊤ :=
    eq_top_of_rankOne_le (isCTGroupDatum hF n (by omega) oneTZ one_ne_zero) _ fun k =>
      sup_le (fun z hz => hA k z hz)
        (fun y hy => agree_neg_of_levelWeyl hF (by omega) β γ' (hA k) (hW k) y hy)
  intro u
  have hu : u ∈ β.eqLocus γ' := by rw [hE]; exact Subgroup.mem_top u
  rw [← hβx]
  exact hu

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_suInnerDiagConj_three_large {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h2f : 2 ^ f ≠ 2) :
    InnerDiagSU.SUInnerDiagConj hF 3 := by
  intro G _ ψ hker c hc
  obtain ⟨g, ⟨s, rfl⟩, hγ⟩ := hc
  obtain ⟨d, hd, hD⟩ := idPSU_exists_diagJ_of_torus hF (by norm_num) h2f ψ hker
    (c * ψ s) hγ
  refine ⟨(s : GL (Fin 3) F) * InnerDiagSU.diagJ d hd,
    (InnerDiagSU.isJUnitary_of_mem_SU s).mul (InnerDiagSU.isJUnitary_diagJ d hd), fun u => ?_⟩
  have h1 : c⁻¹ * ψ u * c = ψ s * ((c * ψ s)⁻¹ * ψ u * (c * ψ s)) * (ψ s)⁻¹ := by group
  rw [h1, hD u, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, InnerDiagSU.coe_conjSU]
  group

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_scalar_torus_small {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (h2f : 2 ^ f = 2)
    {h : SU (unitaryInvolution F 2 f) 3}
    (hh : h ∈ ggTorus (rootDatum hF 3)) :
    ∃ l : F, ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) l := by
  obtain ⟨hd, huni⟩ := eq_diagonal_of_mem_ggTorus hF hh
  set d : Fin 3 → F := fun s => mat (unitaryInvolution F 2 f) 3 h s s with hddef
  have hrel : ∀ s, d s ^ 2 * d (Fin.rev s) = 1 := by
    intro s
    have h := huni s
    rw [unitaryInvolution_apply, h2f] at h
    exact h
  have hrel0 : d 0 ^ 2 * d 2 = 1 := by
    simpa only [show Fin.rev (0 : Fin 3) = 2 from rfl] using hrel 0
  have hrel2 : d 2 ^ 2 * d 0 = 1 := by
    simpa only [show Fin.rev (2 : Fin 3) = 0 from rfl] using hrel 2
  have hdet : d 0 * d 1 * d 2 = 1 := by
    have h1 : (mat (unitaryInvolution F 2 f) 3 h).det = 1 := by
      rw [mat_apply]
      exact h.2.1
    rw [hd, Matrix.det_diagonal, Fin.prod_univ_three] at h1
    exact h1
  have hd0 : d 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hrel0
    exact zero_ne_one hrel0
  have hd2 : d 2 ≠ 0 := by
    intro h2
    rw [h2, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hrel2
    exact zero_ne_one hrel2
  have h01 : d 0 = d 1 := by
    have h : d 0 ^ 2 = d 0 * d 1 := by
      apply mul_right_cancel₀ hd2
      rw [hrel0, hdet]
    rw [pow_two] at h
    exact mul_left_cancel₀ hd0 h
  have h02 : d 0 = d 2 := by
    have hA : d 0 * d 2 = d 2 * d 2 := by
      apply mul_right_cancel₀ hd0
      calc (d 0 * d 2) * d 0 = d 0 ^ 2 * d 2 := by ring
        _ = d 2 ^ 2 * d 0 := hrel0.trans hrel2.symm
        _ = (d 2 * d 2) * d 0 := by ring
    exact mul_right_cancel₀ hd2 hA
  refine ⟨d 0, ?_⟩
  have hmat : ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d := by
    rw [← mat_apply]
    exact hd
  rw [hmat]
  have hdeq : d = fun _ => d 0 := by
    funext s
    fin_cases s
    · rfl
    · exact h01.symm
    · exact h02.symm
  rw [hdeq]
  rfl

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_suInnerDiagConj_three_small {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h2f : 2 ^ f = 2) :
    InnerDiagSU.SUInnerDiagConj hF 3 := by
  intro G _ ψ hker c hc
  obtain ⟨g, ⟨s, rfl⟩, hroot⟩ := hc
  have hxcent : ∀ u : SU (unitaryInvolution F 2 f) 3,
      (c * ψ s)⁻¹ * ψ u * (c * ψ s) = ψ u := by
    intro u
    set β : SU (unitaryInvolution F 2 f) 3 →* G :=
      (MulAut.conj (c * ψ s)⁻¹).toMonoidHom.comp ψ with hβ
    have hβx : ∀ w, β w = (c * ψ s)⁻¹ * ψ w * (c * ψ s) := fun w => by
      rw [hβ, MonoidHom.comp_apply]
      change (MulAut.conj (c * ψ s)⁻¹) (ψ w) = (c * ψ s)⁻¹ * ψ w * (c * ψ s)
      rw [MulAut.conj_apply, inv_inv]
    have hCT := isCTGroupDatum hF 3 (by norm_num) oneTZ one_ne_zero
    have hrootle : ∀ γ ∈ (rootDatum hF 3).roots,
        (rootDatum hF 3).rootGroup γ ≤ β.eqLocus ψ := by
      intro γ hγ z hz
      change β z = ψ z
      rw [hβx]
      obtain ⟨h, hh, hzh⟩ := hroot γ hγ
      rw [hzh z hz]
      congr 1
      obtain ⟨l, hl⟩ := idPSU_scalar_torus_small hF h2f hh
      have hcomm : h * z = z * h := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hl]
        exact (Matrix.scalar_commute l (fun r => Commute.all _ r)
          ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).eq
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hE : β.eqLocus ψ = ⊤ :=
      eq_top_of_rankOne_le hCT _ fun k =>
        sup_le (hrootle _ (single_mem_roots (D := rootDatum hF 3) k))
          (hrootle _ (neg_single_mem_roots (D := rootDatum hF 3) k))
    have hu : u ∈ β.eqLocus ψ := by rw [hE]; exact Subgroup.mem_top u
    rw [← hβx]
    exact hu
  refine ⟨(s : GL (Fin 3) F), isJUnitary_of_mem_SU s, fun u => ?_⟩
  have h1 : c⁻¹ * ψ u * c = ψ s * ((c * ψ s)⁻¹ * ψ u * (c * ψ s)) * (ψ s)⁻¹ := by group
  rw [h1, hxcent u, ← map_inv, ← map_mul, ← map_mul]
  congr 1

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_three {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) : InnerDiagSU.SUInnerDiagConj hF 3 := by
  by_cases h2 : 2 ^ f = 2
  · exact idPSU_suInnerDiagConj_three_small hF h2
  · exact idPSU_suInnerDiagConj_three_large hF h2

theorem exists_isGLLift_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {b : X} (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hb : GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b) :
    ∃ s : GL (Fin n) F, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n ∧ IsGLLift
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b := by
  by_cases hn4 : 4 ≤ n
  · obtain ⟨A, hA, hAu⟩ := InnerDiagSU.suInnerDiagConj hc hn4 X ψ hψ b hb
    refine ⟨A, by simpa only [InnerDiagSU.IsJUnitary] using hA, fun u => ?_⟩
    exact ⟨InnerDiagSU.conjSU A hA u, InnerDiagSU.coe_conjSU A hA u, hAu u⟩
  · have hn3 : n = 3 := by omega
    subst hn3
    obtain ⟨A, hA, hAu⟩ := idPSU_three hc X ψ hψ b hb
    refine ⟨A, by simpa only [InnerDiagSU.IsJUnitary] using hA, fun u => ?_⟩
    exact ⟨InnerDiagSU.conjSU A hA u, InnerDiagSU.coe_conjSU A hA u, hAu u⟩

private theorem idPSU_unit_eq_one_of_pow_two {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {c : Fˣ} {k : ℕ} (h : c ^ (2 ^ k) = 1) :
    c = 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hpowF : Nat.card F = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hc
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm f 2]
      _ = 2 * 2 ^ (2 * f - 1) := by
            conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 by omega]
            rw [pow_add, pow_one]
            ring
  have hodd : Odd (Nat.card F - 1) := by
    rw [hpowF]
    refine ⟨2 ^ (2 * f - 1) - 1, ?_⟩
    have hX : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
    omega
  have hc_odd : c ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one (c : F) (Units.ne_zero c)
  have hdvd2 : orderOf c ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr h
  have hdvd1 : orderOf c ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.mpr hc_odd
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hg : orderOf c ∣ Nat.gcd (2 ^ k) (Nat.card F - 1) := Nat.dvd_gcd hdvd2 hdvd1
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras in
private theorem idPSU_rootHom_sq {F : Type} [Field F] [CharP F 2] {n : ℕ} {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    (rootHom σ hσ hij hi hj c) ^ 2 = 1 := by
  have hc2 : c ^ 2 = 1 := by
    conv_lhs => rw [← ofAdd_toAdd c]
    rw [pow_two, ← ofAdd_add, ← ofAdd_zero]
    change c.toAdd + c.toAdd = (0 : F)
    exact CharTwo.add_self_eq_zero c.toAdd
  rw [← map_pow, hc2, map_one]

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras in
private theorem idPSU_longRootHom_sq {F : Type} [Field F] [CharP F 2] {n : ℕ} {σ : F ≃+* F}
    {i : Fin n} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero σ)) : (longRootHom σ hi c) ^ 2 = 1 := by
  have hc2 : c ^ 2 = 1 := by
    conv_lhs => rw [← ofAdd_toAdd c]
    rw [pow_two, ← ofAdd_add, ← ofAdd_zero]
    change c.toAdd + c.toAdd = (0 : traceZero σ)
    exact Subtype.ext (CharTwo.add_self_eq_zero (c.toAdd : F))
  rw [← map_pow, hc2, map_one]

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras in
private theorem idPSU_heisenberg_pow_four {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (σ : F ≃+* F) {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) : (heisenbergMatrix σ i k a b) ^ 4 = 1 := by
  have h2 : (heisenbergMatrix σ i k a b) ^ 2 =
      heisenbergMatrix σ i k 0 (b + b - a * σ a) := by
    rw [pow_two, heisenbergMatrix_mul σ hi hik hk a b a b, CharTwo.add_self_eq_zero a]
  calc (heisenbergMatrix σ i k a b) ^ 4
      = ((heisenbergMatrix σ i k a b) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (heisenbergMatrix σ i k 0 (b + b - a * σ a)) ^ 2 := by rw [h2]
    _ = heisenbergMatrix σ i k (0 + 0)
          ((b + b - a * σ a) + (b + b - a * σ a) - 0 * σ 0) := by
          rw [pow_two, heisenbergMatrix_mul σ hi hik hk]
    _ = 1 := by
          rw [zero_add, zero_mul, sub_zero, CharTwo.add_self_eq_zero]
          exact heisenbergMatrix_zero σ i k

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras in
private theorem idPSU_two_scalar {F : Type} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    (h1 : M * longRootMatrix (0 : Fin 2) (1 : F) = longRootMatrix 0 1 * M)
    (h2 : M * longRootMatrix (1 : Fin 2) (1 : F) = longRootMatrix 1 1 * M) :
    ∃ c : F, M = Matrix.scalar (Fin 2) c := by
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h2 0) 0
  simp [longRootMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have h10 : M 1 0 = 0 := e1
  have h01 : M 0 1 = 0 := e3
  have h11 : M 1 1 = M 0 0 := by
    have h := e2
    rw [e3, zero_add, add_zero] at h
    exact h.symm
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h10, h01, h11]

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.InnerDiagSU in
private theorem idPSU_unique_core {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} {s s' : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b)
    (hs' : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s' b)
    :
    ∃ c : F, ((s'⁻¹ * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c := by
  haveI : Fintype F := Fintype.ofFinite F
  set g : GL (Fin n) F := s'⁻¹ * s with hg
  by_cases hn3 : 3 ≤ n
  · have hf : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      subst hf0
      have h1 : 1 < Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      rw [hc] at h1
      norm_num at h1
    let E : Subgroup (SU (unitaryInvolution F 2 f) n) :=
      (Subgroup.centralizer ({g} : Set (GL (Fin n) F))).comap
        (SU (unitaryInvolution F 2 f) n).subtype
    have htwo : ∀ (u : SU (unitaryInvolution F 2 f) n) (k : ℕ),
        u ^ (2 ^ k) = 1 → u ∈ E := by
      intro u k hum
      obtain ⟨u₁, hu₁, hψu₁⟩ := hs u
      obtain ⟨u₂, hu₂, hψu₂⟩ := hs' u
      set z : SU (unitaryInvolution F 2 f) n := u₁ * u₂⁻¹ with hzdef
      have hzker : z ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, ← hψu₁, hψu₂, mul_inv_cancel]
      have hzcenter : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) := hψ hzker
      have hzcomm : ∀ v : SU (unitaryInvolution F 2 f) n,
          (↑z : GL (Fin n) F) * ↑v = ↑v * ↑z := by
        intro v
        exact congrArg (fun w : SU (unitaryInvolution F 2 f) n => (w : GL (Fin n) F))
          (Subgroup.mem_center_iff.mp hzcenter v).symm
      obtain ⟨c, hzc⟩ := UnitaryCenter.exists_scalar_of_commute_SU hc hf hn3 hzcomm
      have hzu₁ : (↑u₁ : GL (Fin n) F) = ↑z * ↑u₂ := by
        have : u₁ = z * u₂ := by rw [hzdef]; group
        rw [this, Subgroup.coe_mul]
      have hconjz : s'⁻¹ * (↑z : GL (Fin n) F) * s' = ↑z := by
        rw [hzc]
        rw [show s'⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) c =
            Matrix.GeneralLinearGroup.scalar (Fin n) c * s'⁻¹ from
          (Matrix.GeneralLinearGroup.scalar_commute c s'⁻¹).symm]
        group
      have heq : g * ↑u * g⁻¹ = (↑z : GL (Fin n) F) * ↑u := by
        calc g * ↑u * g⁻¹ = s'⁻¹ * ↑u₁ * s' := by
              rw [show g = s'⁻¹ * s from hg]
              rw [show (↑u₁ : GL (Fin n) F) = s * ↑u * s⁻¹ from hu₁]
              group
          _ = s'⁻¹ * (↑z * ↑u₂) * s' := by rw [hzu₁]
          _ = (s'⁻¹ * ↑z * s') * (s'⁻¹ * ↑u₂ * s') := by group
          _ = ↑z * ↑u := by
              rw [hconjz, show (↑u₂ : GL (Fin n) F) = s' * ↑u * s'⁻¹ from hu₂]
              group
      have hc2 : c ^ (2 ^ k) = 1 := by
        have h := congrArg (fun A : GL (Fin n) F => A ^ (2 ^ k)) heq
        rw [hzc] at h
        have hL : (g * ↑u * g⁻¹) ^ (2 ^ k) = 1 := by
          have h1 : (g * ↑u * g⁻¹) ^ (2 ^ k) = g * (↑u) ^ (2 ^ k) * g⁻¹ := by
            rw [show g * ↑u * g⁻¹ = (MulAut.conj g) ↑u from (MulAut.conj_apply g ↑u).symm]
            rw [← map_pow]
            rfl
          rw [h1, ← Subgroup.coe_pow, hum, Subgroup.coe_one]
          group
        rw [hL] at h
        have hR : (Matrix.GeneralLinearGroup.scalar (Fin n) c * (↑u : GL (Fin n) F)) ^ (2 ^ k) =
            Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ (2 ^ k)) := by
          rw [Commute.mul_pow (show Commute (Matrix.GeneralLinearGroup.scalar (Fin n) c)
            (↑u : GL (Fin n) F) from
              Matrix.GeneralLinearGroup.scalar_commute c (↑u : GL (Fin n) F))]
          rw [show ((↑u : GL (Fin n) F)) ^ (2 ^ k) = 1 from by
            rw [← Subgroup.coe_pow, hum, Subgroup.coe_one]]
          rw [mul_one, ← map_pow]
        rw [hR] at h
        have hpow : (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ (2 ^ k) = 1 := by
          rw [← map_pow]
          exact h.symm
        haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        have hinj : Function.Injective
            (Matrix.GeneralLinearGroup.scalar (Fin n) : Fˣ → GL (Fin n) F) := by
          intro a b hab
          apply Units.ext
          have h2 := congrArg
            (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hab
          simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h2
          exact Matrix.scalar_inj.mp h2
        have hord : orderOf c = orderOf (Matrix.GeneralLinearGroup.scalar (Fin n) c) := by
          symm
          exact orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin n)) hinj c
        have hdvd : orderOf c ∣ 2 ^ k := by
          rw [hord]
          exact orderOf_dvd_iff_pow_eq_one.mpr hpow
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hc1 : c = 1 := idPSU_unit_eq_one_of_pow_two hc hf hc2
      have hz1 : (↑z : GL (Fin n) F) = 1 := by rw [hzc, hc1, map_one]
      have heq1 : g * ↑u * g⁻¹ = ↑u := by rw [heq, hz1, one_mul]
      have hcomm : g * ↑u = ↑u * g := by
        calc g * ↑u = g * ↑u * g⁻¹ * g := by group
          _ = ↑u * g := by rw [heq1]
      change u ∈ (Subgroup.centralizer ({g} : Set (GL (Fin n) F))).comap
        (SU (unitaryInvolution F 2 f) n).subtype
      rw [Subgroup.mem_comap]
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm
    have hroot : ∀ γ ∈ (rootDatum hc n).roots, (rootDatum hc n).rootGroup γ ≤ E := by
      intro γ hγ
      change Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n γ ≤ E
      unfold Unitary.rootGroup
      refine sup_le (sup_le ?_ ?_) ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
          iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
        rintro _ ⟨c, rfl⟩
        exact htwo _ 1 (by
          simpa using idPSU_rootHom_sq (unitaryInvolution_involutive hc) hij hi hj c)
      · refine iSup_le fun i => iSup_le fun hi => iSup_le fun _ => ?_
        rintro _ ⟨c, rfl⟩
        exact htwo _ 1 (by simpa using idPSU_longRootHom_sq hi c)
      · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
          iSup_le fun hk => iSup_le fun _ => ?_
        intro x hx
        obtain ⟨a, b, -, hxmat⟩ := hx
        refine htwo x 2 ?_
        apply Subtype.ext
        apply Units.ext
        change ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 4 = 1
        rw [hxmat]
        exact idPSU_heisenberg_pow_four (unitaryInvolution F 2 f) hi hik hk a b
    have hEtop : E = ⊤ :=
      eq_top_of_rankOne_le (isCTGroupDatum hc n (by omega) oneTZ one_ne_zero) E fun k =>
        sup_le (hroot _ (single_mem_roots (D := rootDatum hc n) k))
          (hroot _ (neg_single_mem_roots (D := rootDatum hc n) k))
    have hcentral : ∀ u : SU (unitaryInvolution F 2 f) n, g * ↑u = ↑u * g := by
      intro u
      have hu : u ∈ E := by rw [hEtop]; exact Subgroup.mem_top u
      have hu' : (SU (unitaryInvolution F 2 f) n).subtype u ∈
          Subgroup.centralizer ({g} : Set (GL (Fin n) F)) := by
        have hu2 := hu
        change u ∈ (Subgroup.centralizer ({g} : Set (GL (Fin n) F))).comap
          (SU (unitaryInvolution F 2 f) n).subtype at hu2
        rwa [Subgroup.mem_comap] at hu2
      exact (Subgroup.mem_centralizer_iff.mp hu') g (by simp)
    obtain ⟨c, hc⟩ := UnitaryCenter.exists_scalar_of_commute_SU hc hf hn3 hcentral
    refine ⟨(c : F), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
  · have hn2 : n = 2 := by omega
    subst hn2
    have hcomm : ∀ u : SU (unitaryInvolution F 2 f) 2, g * ↑u = ↑u * g := by
      intro u
      obtain ⟨u₁, hu₁, hψu₁⟩ := hs u
      obtain ⟨u₂, hu₂, hψu₂⟩ := hs' u
      set z : SU (unitaryInvolution F 2 f) 2 := u₁ * u₂⁻¹ with hzdef
      have hzker : z ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, ← hψu₁, hψu₂, mul_inv_cancel]
      have hzcenter : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) 2) := hψ hzker
      have hzcomm : ∀ v : SU (unitaryInvolution F 2 f) 2,
          (↑z : GL (Fin 2) F) * ↑v = ↑v * ↑z := by
        intro v
        exact congrArg (fun w : SU (unitaryInvolution F 2 f) 2 => (w : GL (Fin 2) F))
          (Subgroup.mem_center_iff.mp hzcenter v).symm
      have hzscal : ∃ c : F,
          ((↑z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := by
        apply idPSU_two_scalar
        · have hv := hzcomm (longRootHom (unitaryInvolution F 2 f)
            (show (0 : Fin 2) ≠ Fin.rev 0 from by decide)
            (Multiplicative.ofAdd oneTZ))
          have hmat := congrArg (fun A : GL (Fin 2) F =>
            (A : Matrix (Fin 2) (Fin 2) F)) hv
          simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ] using hmat
        · have hv := hzcomm (longRootHom (unitaryInvolution F 2 f)
            (show (1 : Fin 2) ≠ Fin.rev 1 from by decide)
            (Multiplicative.ofAdd oneTZ))
          have hmat := congrArg (fun A : GL (Fin 2) F =>
            (A : Matrix (Fin 2) (Fin 2) F)) hv
          simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ] using hmat
      obtain ⟨c, hc⟩ := hzscal
      have hc1 : c = 1 := by
        have hdet : ((↑z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := z.2.1
        rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
        have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
        have hsq : (c - 1) * (c - 1) = 0 := by linear_combination hdet - (c - 1) * h2
        exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
      have hz1 : z = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hc, hc1]
        simp [Matrix.scalar_apply, Matrix.diagonal_one]
      have hzu₁ : (↑u₁ : GL (Fin 2) F) = ↑z * ↑u₂ := by
        have : u₁ = z * u₂ := by rw [hzdef]; group
        rw [this, Subgroup.coe_mul]
      have hconjz : s'⁻¹ * (↑z : GL (Fin 2) F) * s' = ↑z := by
        rw [hz1, Subgroup.coe_one]
        group
      have heq : g * ↑u * g⁻¹ = (↑z : GL (Fin 2) F) * ↑u := by
        calc g * ↑u * g⁻¹ = s'⁻¹ * ↑u₁ * s' := by
              rw [show g = s'⁻¹ * s from hg]
              rw [show (↑u₁ : GL (Fin 2) F) = s * ↑u * s⁻¹ from hu₁]
              group
          _ = s'⁻¹ * (↑z * ↑u₂) * s' := by rw [hzu₁]
          _ = (s'⁻¹ * ↑z * s') * (s'⁻¹ * ↑u₂ * s') := by group
          _ = ↑z * ↑u := by
              rw [hconjz, show (↑u₂ : GL (Fin 2) F) = s' * ↑u * s'⁻¹ from hu₂]
              group
      have heq1 : g * ↑u * g⁻¹ = ↑u := by rw [heq, hz1, Subgroup.coe_one, one_mul]
      calc g * ↑u = g * ↑u * g⁻¹ * g := by group
        _ = ↑u * g := by rw [heq1]
    have hgscal : ∃ c : F,
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := by
      apply idPSU_two_scalar
      · have hv := hcomm (longRootHom (unitaryInvolution F 2 f)
          (show (0 : Fin 2) ≠ Fin.rev 0 from by decide)
          (Multiplicative.ofAdd oneTZ))
        have hmat := congrArg (fun A : GL (Fin 2) F =>
          (A : Matrix (Fin 2) (Fin 2) F)) hv
        simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ] using hmat
      · have hv := hcomm (longRootHom (unitaryInvolution F 2 f)
          (show (1 : Fin 2) ≠ Fin.rev 1 from by decide)
          (Multiplicative.ofAdd oneTZ))
        have hmat := congrArg (fun A : GL (Fin 2) F =>
          (A : Matrix (Fin 2) (Fin 2) F)) hv
        simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ] using hmat
    obtain ⟨c, hc⟩ := hgscal
    exact ⟨c, hc⟩

theorem isGLLift_unique_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} {s s' : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b)
    (hs' : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s' b)
    :
    ∃ c : F, ((s'⁻¹ * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c := by
  by_cases hn : 2 ≤ n
  · exact idPSU_unique_core hc hn ψ hψ hs hs'
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact ⟨0, Subsingleton.elim _ _⟩
    · refine ⟨((s'⁻¹ * s : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) 0 0, ?_⟩
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.scalar, Matrix.diagonal]

end CFSG.StandardType.ClassicalPosition
