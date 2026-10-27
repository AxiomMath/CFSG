module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvFrame
public import CFSG.GroupTheory.ElemAbelianClosure

import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Fin.Basic

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly TableB

theorem center_projectiveSL_eq_bot_charTwo {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (projectiveSL n K) = ⊥ := by
  rcases le_or_gt n 2 with hn | hn
  ·
    have hscal : scalars n K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro A hA
      obtain ⟨c, hc, hA'⟩ := mem_scalars.mp hA
      interval_cases n
      · exact Subtype.ext (Subsingleton.elim _ _)
      · refine Subtype.ext ?_
        have hc1 : c = 1 := by simpa using hc
        simp [hA', hc1]
      · refine Subtype.ext ?_
        have hval : (c : K) ^ 2 = 1 := by
          rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
        have hc1 : c = 1 := by
          rcases sq_eq_one_iff.mp hval with h | h
          · exact Units.ext (by simpa using h)
          · exact Units.ext (by simpa using (h.trans (CharTwo.neg_eq (1 : K))))
        simp [hA', hc1]
    have hinj : Function.Injective (proj n K) := by
      intro A B hAB
      have h1 : proj n K (A⁻¹ * B) = 1 := by rw [map_mul, map_inv, hAB, inv_mul_cancel]
      rw [proj_eq_one_iff, hscal, Subgroup.mem_bot] at h1
      exact inv_mul_eq_one.mp h1
    let e : SpecialLinearGroup (Fin n) K ≃* projectiveSL n K :=
      MulEquiv.ofBijective (proj n K) ⟨hinj, proj_surjective n K⟩
    have hcenter : Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
      rw [← scalars_eq_center, hscal]
    have h1 := Subgroup.map_center_eq e
    rw [hcenter, Subgroup.map_bot] at h1
    exact h1.symm
  ·
    exact CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by omega)

theorem exists_conjAut_eq_conj_proj {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 1 ≤ d) {B : GL (Fin d) K}
    (hBp : (conjAut d K B) ^ p = 1) :
    ∃ X : SpecialLinearGroup (Fin d) K, conjAut d K B = MulAut.conj (proj d K X) := by
  have h1 : conjAut d K (B ^ p) = 1 := by rw [map_pow, hBp]
  have h2 := AutPSL.mem_center_of_conjAut_eq_one hd h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  obtain ⟨μ, hμ⟩ := OrdPNS.exists_pow_eq hp hpK c
  set B' : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ⁻¹ * B with hB'
  have hB'p : B' ^ p = 1 := TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow (by rw [← hc, hμ])
  have hdet : (B' : Matrix (Fin d) (Fin d) K).det = 1 :=
    OrdPNS.det_eq_one_of_pow_eq_one hp hpK (by
      rw [← Units.val_pow_eq_pow_val, hB'p]
      simp)
  let X : SpecialLinearGroup (Fin d) K := ⟨B', hdet⟩
  have hXA : conjAut d K (Matrix.SpecialLinearGroup.toGL X) = conjAut d K B := by
    have e : Matrix.SpecialLinearGroup.toGL X = B' := Units.ext rfl
    rw [e, hB', map_mul, conjAut_scalar, one_mul]
  exact ⟨X, by rw [← hXA, conjAut_toGL]⟩

theorem exists_isBlockTorusModel {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) {g : K[X]} [Fact (Irreducible g)]
    (hgd : g ∣ cyclotomic p K) (hC : (rootMat g).det = 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l, φa (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    ∃ (s r : ℕ) (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (φ : SpecialLinearGroup (Fin d) K →* L'), Function.Surjective φ ∧
        (∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K)) ∧
        3 ≤ s ∧ IsBlockTorusModel φ ε hC A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty K := ⟨0⟩
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have := Nat.card_pos (α := K)
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hCp : rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hdim2 : 2 ≤ (rootPB g).dim := LinTwoTv.two_le_rootPB_dim fun c =>
    CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd 1 hp.not_dvd_one c
  have hZ : Subgroup.center (projectiveSL d K) = ⊥ := center_projectiveSL_eq_bot_charTwo
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    subst hd
    have hL1 : Subsingleton L' := by
      have htop : Subgroup.center L' = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hker (by rw [MonoidHom.mem_ker]; exact Subsingleton.elim _ _)
      have hbot : (⊤ : Subgroup L') = ⊥ := by
        rw [← hperf]
        exact (commutator_eq_bot_iff_center_eq_top L').mpr htop
      refine ⟨fun x y => ?_⟩
      have hx : x = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x)
      have hy : y = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top y)
      rw [hx, hy]
    have hAle : Nat.card A ≤ 1 := by
      haveI : Subsingleton (MulAut L') :=
        ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
      have h1 : Nat.card A = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨1, A.one_mem⟩⟩⟩
      omega
    have h8 : 8 ≤ p ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
    omega
  set Λ : projectiveSL d K →* MulAut L' := ReflInner.liftConj ψ hψ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZ
  have hΛmap : ∀ (e : projectiveSL d K) (l : L'), ψ (Λ e l) = e * ψ l * e⁻¹ :=
    ReflInner.map_liftConj_apply hψ hker
  have hAΛ : ∀ a ∈ A, ∃ e : projectiveSL d K, Λ e = a := by
    intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l : L', (conjAut d K B ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
    have hφp : (conjAut d K B) ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨X, hX⟩ := exists_conjAut_eq_conj_proj hp hpK' hd hφp
    refine ⟨proj d K X, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφa l, hX, MulAut.conj_apply]
  set E : Subgroup (projectiveSL d K) := A.comap Λ
  have hEab : IsElemAbelian p E := CFSG.Open.IsElemAbelian.comap hA hΛinj
  have hEA : Nat.card E = Nat.card A := by
    have hle : A ≤ Λ.range := by
      intro a ha
      obtain ⟨e, he⟩ := hAΛ a ha
      exact ⟨e, he⟩
    rw [← Subgroup.card_map_of_injective (f := Λ) hΛinj, Subgroup.map_comap_eq_self hle]
  have hnp : ∀ z ∈ (proj d K).ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rw [ker_proj] at hz
    obtain ⟨c, -, hcz⟩ := mem_scalars.mp hz
    have hval : (c : K) ^ p = 1 := by
      have h3 : ((z ^ p : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩ = 1 := by
        simp [hzp]
      rw [Matrix.SpecialLinearGroup.coe_pow, hcz, Matrix.scalar_apply, Matrix.diagonal_pow,
        Matrix.diagonal_apply_eq] at h3
      simpa using h3
    have hc1 : c = 1 := Units.ext (by
      simpa using OrdPNS.eq_one_of_pow_eq_one hp hpK' hval)
    refine Subtype.ext ?_
    rw [hcz, hc1]
    simp
  obtain ⟨Ab, hAbmap, -, hAbel, hAbcard⟩ :=
    TableBUE.exists_lift_of_noTorsion (proj d K) (proj_surjective d K) hp hnp hEab
  let S : Set (Matrix (Fin d) (Fin d) K) :=
    Set.range fun b : Ab => (b : Matrix (Fin d) (Fin d) K)
  have hAbcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    have h := congrArg (fun w : SpecialLinearGroup (Fin d) K =>
      (w : Matrix (Fin d) (Fin d) K)) (TableB.IsElemAbelian.comm hAbel b.2 c.2)
    have h' : (b : Matrix (Fin d) (Fin d) K) * (c : Matrix (Fin d) (Fin d) K) =
        (c : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
    exact h'
  have hAbpow : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    have h := congrArg (fun w : SpecialLinearGroup (Fin d) K =>
      (w : Matrix (Fin d) (Fin d) K)) (hAbel.2 (b : SpecialLinearGroup (Fin d) K) b.2)
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using h
  obtain ⟨s, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd S hAbcomm hAbpow
  have hframeAb : ∀ b ∈ Ab, ∃ k : Fin s → ℕ, b = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe ((b : SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) ⟨⟨b, hb⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : (b : SpecialLinearGroup (Fin d) K) * A₀ = A₀ * SLNS.nsSL ε hC k := by
      refine Subtype.ext ?_
      exact hk
    rw [← h1, mul_inv_cancel_right]
  have hcardAb : Nat.card Ab ≤ p ^ s := by
    set τ : Multiplicative (Fin s → ZMod p) →* SpecialLinearGroup (Fin d) K :=
      CoordSL.frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp with hτ
    have hle : Ab ≤ τ.range := by
      intro b hb
      obtain ⟨k, hk⟩ := hframeAb b hb
      refine ⟨Multiplicative.ofAdd fun i => (k i : ZMod p), ?_⟩
      rw [hτ, CoordSL.frameHom_natCast, SLRep.ggFrame_apply, MonoidHom.id_apply, ← hk]
    have hpow : Nat.card (Multiplicative (Fin s → ZMod p)) = p ^ s := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_pi_const,
        ZMod.card]
    calc Nat.card Ab ≤ Nat.card τ.range := Subgroup.card_le_of_le hle
      _ ≤ Nat.card (Multiplicative (Fin s → ZMod p)) := by
        refine Nat.card_le_card_of_surjective
          (fun y => (⟨τ y, ⟨y, rfl⟩⟩ : τ.range)) ?_
        rintro ⟨z, ⟨y, hy⟩⟩
        exact ⟨y, Subtype.ext hy⟩
      _ = p ^ s := hpow
  have h3s : 3 ≤ s := by
    have hps : p ^ 3 ≤ p ^ s := by
      have h := h3
      rw [← hEA, ← hAbcard] at h
      exact h.trans hcardAb
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hps
  have hd5 : 5 ≤ d := by
    have hdcard : d = (rootPB g).dim * s + r := by
      have h := Fintype.card_congr ε
      simpa [Fintype.card_sum, Fintype.card_prod] using h
    have h6 : 6 ≤ (rootPB g).dim * s := by
      calc 6 = 2 * 3 := by norm_num
        _ ≤ (rootPB g).dim * s := Nat.mul_le_mul hdim2 h3s
    omega
  obtain ⟨φ₀, hφ₀s, hφ₀⟩ :=
    TypeA.exists_sl_cover (TypeA.slHasSections_of_five_le hd5) ψ hψ hker hperf
  let φ : SpecialLinearGroup (Fin d) K →* L' := SLRep.ggFrame φ₀ A₀
  have hφapp : ∀ x : SpecialLinearGroup (Fin d) K, φ x = φ₀ (A₀ * x * A₀⁻¹) := fun x =>
    SLRep.ggFrame_apply φ₀ A₀ x
  have hφs : Function.Surjective φ := hφ₀s.comp (MulAut.conj A₀).surjective
  have hφker : ∀ x, φ x ∈ Subgroup.center L' →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
    intro x hx
    have hψx : ψ (φ x) ∈ Subgroup.center (projectiveSL d K) :=
      Subgroup.map_center_le_center hψ (Subgroup.mem_map.mpr ⟨φ x, hx, rfl⟩)
    rw [hZ, Subgroup.mem_bot] at hψx
    have hproj1 : proj d K (A₀ * x * A₀⁻¹) = 1 := by
      rw [← hφ₀ (A₀ * x * A₀⁻¹)]
      simpa only [hφapp] using hψx
    have hcen : A₀ * x * A₀⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      rw [← scalars_eq_center]
      exact proj_eq_one_iff.mp hproj1
    have hx : x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      have h1 : MulAut.conj A₀ x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
        simpa only [MulAut.conj_apply] using hcen
      have hmap := Subgroup.map_center_eq (MulAut.conj A₀).symm
      have hmem : x ∈ Subgroup.map (↑(MulAut.conj A₀).symm)
          (Subgroup.center (SpecialLinearGroup (Fin d) K)) :=
        Subgroup.mem_map.mpr ⟨(MulAut.conj A₀) x, h1, by
          show (MulAut.conj A₀).symm ((MulAut.conj A₀) x) = x
          rw [MulEquiv.symm_apply_apply]⟩
      rwa [hmap] at hmem
    exact hx
  refine ⟨s, r, ε, φ, hφs, hφker, h3s, ?_⟩
  have hfwd : ∀ a ∈ A, ∃ t : Fin s → ℕ, a = MulAut.conj (φ (SLNS.nsSL ε hC t)) := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    have heE : e ∈ E := by
      show Λ e ∈ A
      rw [he]
      exact ha
    have hemap : e ∈ Ab.map (proj d K) := by rw [hAbmap]; exact heE
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hemap
    obtain ⟨k, hk⟩ := hframeAb y hy
    refine ⟨k, ?_⟩
    rw [← he, ReflInner.liftConj_eq hψ hker ((hφ₀ y).trans hye)]
    congr 1
    rw [hφapp, ← hk]
  refine fun a => ⟨hfwd a, ?_⟩
  rintro ⟨t, rfl⟩
  refine hsc (φ (SLNS.nsSL ε hC t)) ?_ ?_
  · intro a ha
    obtain ⟨k, hk⟩ := hfwd a ha
    rw [hk, MulAut.conj_apply]
    have hcomm : φ (SLNS.nsSL ε hC k) * φ (SLNS.nsSL ε hC t) =
        φ (SLNS.nsSL ε hC t) * φ (SLNS.nsSL ε hC k) := by
      rw [← map_mul, ← map_mul, SLNS.nsSL_comm]
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · rw [← map_pow, SLNS.nsSL_pow_p ε hC hCp t, map_one]

theorem IsBlockTorusModel.fixed_lt_dim {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {d p s r : ℕ} {hC : (rootMat g).det = 1} (hCp : rootMat g ^ p = 1)
    (hns : ∀ c : K, rootMat g ≠ c • (1 : Matrix (Fin (rootPB g).dim) (Fin (rootPB g).dim) K))
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {A : Subgroup (MulAut L')}
    (hφc : ∀ x, φ x ∈ Subgroup.center L' →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K))
    (hM : IsBlockTorusModel φ ε hC A) (hsc : GGTorusSelfCent p A) :
    r < (rootPB g).dim := by
  by_contra hlt
  have hge : (rootPB g).dim ≤ r := by omega
  let e := (rootPB g).dim
  have he : e = (rootPB g).dim := rfl
  let C := rootMat g
  have hCdef : C = rootMat g := rfl
  have hCp' : C ^ p = 1 := by rw [hCdef, hCp]
  have her : r = e + (r - e) := by rw [he]; omega
  let σ : Fin r ≃ Fin e ⊕ Fin (r - e) :=
    (finCongr her).trans finSumFinEquiv.symm
  let B : Matrix (Fin e ⊕ Fin (r - e)) (Fin e ⊕ Fin (r - e)) K :=
    fromBlocks C 0 0 (1 : Matrix (Fin (r - e)) (Fin (r - e)) K)
  have hBdef : B =
      fromBlocks C 0 0 (1 : Matrix (Fin (r - e)) (Fin (r - e)) K) := rfl
  let W : Matrix (Fin r) (Fin r) K := B.submatrix σ σ
  have hWdef : W = B.submatrix σ σ := rfl
  have submatrix_pow : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (A : Matrix α α K) (τ : β ≃ α) (j : ℕ),
      (A.submatrix τ τ) ^ j = (A ^ j).submatrix τ τ := by
    intro α β _ _ _ _ A τ j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.submatrix_one_equiv]
    | succ j ih =>
      rw [pow_succ, pow_succ, ih, ← Matrix.submatrix_mul_equiv (A ^ j) A τ τ τ]
  have hBp : B ^ p = 1 := by
    rw [hBdef, Matrix.fromBlocks_diagonal_pow, hCp']
    simp
  have hWp : W ^ p = 1 := by
    rw [hWdef, submatrix_pow B σ p, hBp, Matrix.submatrix_one_equiv]
  let B₂ : Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) K :=
    fromBlocks (1 : Matrix (Fin e × Fin s) (Fin e × Fin s) K) 0 0 W
  have hB₂def : B₂ =
      fromBlocks (1 : Matrix (Fin e × Fin s) (Fin e × Fin s) K) 0 0 W := rfl
  let U : Matrix (Fin d) (Fin d) K := B₂.submatrix ε ε
  have hUdef : U = B₂.submatrix ε ε := rfl
  have hB₂p : B₂ ^ p = 1 := by
    rw [hB₂def, Matrix.fromBlocks_diagonal_pow, hWp]
    simp
  have hUp : U ^ p = 1 := by
    rw [hUdef, submatrix_pow B₂ ε p, hB₂p, Matrix.submatrix_one_equiv]
  have hdetW : W.det = 1 := by
    rw [hWdef, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, hCdef, hC]
    simp
  have hdetU : U.det = 1 := by
    rw [hUdef, Matrix.det_submatrix_equiv_self, hB₂def, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul, hdetW]
  let u : SpecialLinearGroup (Fin d) K := ⟨U, hdetU⟩
  have hu_coe : (u : Matrix (Fin d) (Fin d) K) = U := rfl
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_pow, hu_coe] using hUp
  have hmulcore : ∀ t : Fin s → ℕ, B₂ * SLNS.nsCore C t = SLNS.nsCore C t * B₂ := by
    intro t
    have hnsCore : SLNS.nsCore C t =
        fromBlocks (Matrix.blockDiagonal fun i => C ^ t i) 0 0
          (1 : Matrix (Fin r) (Fin r) K) := rfl
    rw [hB₂def, hnsCore]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add]
  have hcomm_mat : ∀ t : Fin s → ℕ, U * SLNS.nsMat ε C t = SLNS.nsMat ε C t * U := by
    intro t
    have hns : SLNS.nsMat ε C t = (SLNS.nsCore C t).submatrix ε ε := rfl
    calc U * SLNS.nsMat ε C t = (B₂ * SLNS.nsCore C t).submatrix ε ε := by
          rw [hUdef, hns, ← Matrix.submatrix_mul_equiv B₂ (SLNS.nsCore C t) ε ε ε]
      _ = (SLNS.nsCore C t * B₂).submatrix ε ε := by rw [hmulcore t]
      _ = SLNS.nsMat ε C t * U := by
          rw [hns, hUdef, Matrix.submatrix_mul_equiv (SLNS.nsCore C t) B₂ ε ε ε]
  have hcomm : ∀ t : Fin s → ℕ, u * SLNS.nsSL ε hC t = SLNS.nsSL ε hC t * u := by
    intro t
    apply Subtype.ext
    show U * SLNS.nsMat ε C t = SLNS.nsMat ε C t * U
    exact hcomm_mat t
  have hfix : ∀ a ∈ A, a (φ u) = φ u := by
    intro a ha
    obtain ⟨t, ht⟩ := (hM a).mp ha
    rw [ht, MulAut.conj_apply]
    have hmap : φ (SLNS.nsSL ε hC t) * φ u = φ u * φ (SLNS.nsSL ε hC t) := by
      rw [← map_mul, ← map_mul, hcomm t]
    rw [hmap, mul_assoc, mul_inv_cancel, mul_one]
  have hφup : (φ u) ^ p = 1 := by
    rw [← map_pow, hup, map_one]
  have hconjmem : MulAut.conj (φ u) ∈ A := hsc (φ u) hfix hφup
  obtain ⟨t₀, ht₀⟩ := (hM (MulAut.conj (φ u))).mp hconjmem
  let x : SpecialLinearGroup (Fin d) K := u * (SLNS.nsSL ε hC t₀)⁻¹
  have hxdef : x = u * (SLNS.nsSL ε hC t₀)⁻¹ := rfl
  have hconj1 : MulAut.conj (φ x) = 1 := by
    rw [hxdef, map_mul, map_inv, map_mul, map_inv, ht₀, mul_inv_cancel]
  have hxmem : φ x ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut L' => f y) hconj1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * φ x = (φ x * y * (φ x)⁻¹) * φ x := by
          conv_lhs => rw [← h]
      _ = φ x * y := by group
  have hxcenter : x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := hφc x hxmem
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxcenter
  have hUeq : U = c • SLNS.nsMat ε C t₀ := by
    have hnsSL : (SLNS.nsSL ε hC t₀ : Matrix (Fin d) (Fin d) K) = SLNS.nsMat ε C t₀ := rfl
    have hc' : (Matrix.scalar (Fin d) c) = U * (SLNS.nsMat ε C t₀).adjugate := by
      simpa [hxdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        hu_coe, hnsSL] using hc
    have h1 : (Matrix.scalar (Fin d) c) * SLNS.nsMat ε C t₀ = U := by
      rw [hc', Matrix.mul_assoc, Matrix.adjugate_mul, SLNS.det_nsMat ε hC t₀]
      simp
    have h2 : (Matrix.scalar (Fin d) c) * SLNS.nsMat ε C t₀ =
        c • SLNS.nsMat ε C t₀ := by
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [← h1, h2]
  have hcore_eq : B₂ = c • SLNS.nsCore C t₀ := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) K => M.submatrix ε.symm ε.symm) hUeq
    have hUsub : U.submatrix ε.symm ε.symm = B₂ := by
      rw [hUdef, Matrix.submatrix_submatrix]
      simp
    have hNsub : (c • SLNS.nsMat ε C t₀).submatrix ε.symm ε.symm =
        c • SLNS.nsCore C t₀ := by
      change c • (SLNS.nsMat ε C t₀).submatrix ε.symm ε.symm = c • SLNS.nsCore C t₀
      rw [show SLNS.nsMat ε C t₀ = (SLNS.nsCore C t₀).submatrix ε ε from rfl,
        Matrix.submatrix_submatrix]
      simp
    rwa [hUsub, hNsub] at h
  have hW_eq : W = c • (1 : Matrix (Fin r) (Fin r) K) := by
    ext i j
    have h := congrArg (fun M : Matrix ((Fin e × Fin s) ⊕ Fin r)
        ((Fin e × Fin s) ⊕ Fin r) K => M (Sum.inr i) (Sum.inr j)) hcore_eq
    simpa [hB₂def,
      show SLNS.nsCore C t₀ = fromBlocks (Matrix.blockDiagonal fun k => C ^ t₀ k) 0 0
        (1 : Matrix (Fin r) (Fin r) K) from rfl] using h
  have hC_eq : B = c • (1 : Matrix (Fin e ⊕ Fin (r - e)) (Fin e ⊕ Fin (r - e)) K) := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) K => M.submatrix σ.symm σ.symm) hW_eq
    have hWsub : W.submatrix σ.symm σ.symm = B := by
      rw [hWdef, Matrix.submatrix_submatrix]
      simp
    have h1sub : (c • (1 : Matrix (Fin r) (Fin r) K)).submatrix σ.symm σ.symm =
        c • (1 : Matrix (Fin e ⊕ Fin (r - e)) (Fin e ⊕ Fin (r - e)) K) := by
      change c • ((1 : Matrix (Fin r) (Fin r) K).submatrix σ.symm σ.symm) = c • 1
      rw [Matrix.submatrix_one_equiv]
    rwa [hWsub, h1sub] at h
  have hCscalar : C = c • (1 : Matrix (Fin e) (Fin e) K) := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin e ⊕ Fin (r - e)) (Fin e ⊕ Fin (r - e)) K =>
      M (Sum.inl i) (Sum.inl j)) hC_eq
    simpa [hBdef, Matrix.one_apply, Sum.inl.injEq] using h
  exact hns c (by rw [← hCdef]; exact hCscalar)

end CFSG.StandardType.SlNsRootGen

end
