module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Pair
public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9U
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveDiag
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Monomial
import CFSG.HardMathSupport.RichardWeiss.Proving.ThreeCycleTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec16.Proof166Res6 (permSU)

namespace U3Normal

theorem exists_norm_one_cube_root_of_mod {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) {x : F} (hx0 : x ≠ 0)
    (hx : h.norm x = 1) :
    ∃ s : F, s ≠ 0 ∧ h.norm s = 1 ∧ s ^ 3 = x := by
  let xu : Fˣ := Units.mk0 x hx0
  have hxnorm : h.norm (xu : F) = 1 := by
    simpa [xu] using hx
  have hxN : xu ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    have hx1 := hxnorm
    rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ'] at hx1
    simpa [xu] using hx1
  have hdvd : orderOf xu ∣ p ^ f + 1 := orderOf_dvd_of_pow_eq_one hxN
  have hcopN : Nat.Coprime (p ^ f + 1) 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by
      intro h3
      have hmod : (p ^ f + 1) % 3 = 2 := by
        rw [Nat.add_mod, hq]
      rw [Nat.mod_eq_zero_of_dvd h3] at hmod
      omega)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers xu)) 3 := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.of_dvd_left hdvd hcopN
  let N : Subgroup Fˣ :=
    { carrier := {a | h.norm (a : F) = 1}
      one_mem' := by simp [UnitaryFieldData.norm]
      mul_mem' := by
        intro a b ha hb
        have ha' : h.norm (a : F) = 1 := ha
        have hb' : h.norm (b : F) = 1 := hb
        show h.norm ((a * b : Fˣ) : F) = 1
        rw [Units.val_mul, norm_mul_eq h, ha', hb', one_mul]
      inv_mem' := by
        intro a ha
        have ha' : h.norm (a : F) = 1 := ha
        show h.norm (((a⁻¹ : Fˣ)) : F) = 1
        rw [Units.val_inv_eq_inv_val, norm_inv_eq h, ha', inv_one] }
  have hxNmem : xu ∈ N := hxnorm
  have hsub : Subgroup.zpowers xu ≤ N := Subgroup.zpowers_le.mpr hxNmem
  obtain ⟨s, hs⟩ := (powCoprime (n := 3) hcop).surjective
    (⟨xu, Subgroup.mem_zpowers xu⟩ : Subgroup.zpowers xu)
  have hs3u : (s : Fˣ) ^ 3 = xu := by
    have hval := congrArg Subtype.val hs
    simpa [powCoprime] using hval
  refine ⟨((s : Fˣ) : F), Units.ne_zero (s : Fˣ), hsub s.2, ?_⟩
  have hs3 : ((s : Fˣ) : F) ^ 3 = x := by
    have hval := congrArg (fun u : Fˣ => (u : F)) hs3u
    simpa [xu] using hval
  simpa using hs3

theorem diagHom_mem_unitarySU_of_norm_one_prod_one {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {d : Fin 3 → Fˣ}
    (hd : ∀ i, h.norm (d i : F) = 1) (hdet : ∏ i, ((d i : Fˣ) : F) = 1) :
    CFSG.SectionRank.OddCover.diagHom 3 d ∈ unitarySU p f F 3 := by
  refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
  · rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.det_diagonal, hdet]
  · rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hi := hd i
    rw [UnitaryFieldData.norm, mul_comm] at hi
    exact hi


theorem exists_diag_conj_data {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (h7 : 7 ∣ p ^ f + 1)
    {B R : Subgroup (unitarySU p f F 3)} (hBR : IsKGenPair B R) :
    ∃ (P : unitarySU p f F 3) (R₁ : Subgroup (unitarySU p f F 3))
      (b₁ : unitarySU p f F 3),
      R₁ = R.map (MulAut.conj P⁻¹).toMonoidHom ∧
      R₁ ≤ CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.diagP p f 7 3 F ∧
      B.map (MulAut.conj P⁻¹).toMonoidHom = Subgroup.zpowers b₁ ∧
      b₁ ^ 3 = 1 ∧ b₁ ≠ 1 ∧
      (∀ r ∈ R₁, b₁ * r * b₁⁻¹ ∈ R₁) ∧
      (∃ r ∈ R₁, b₁ * r ≠ r * b₁) := by
  obtain ⟨hB3, hR7, hR49, hBN, hRC⟩ := hBR
  obtain ⟨P, hP⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_conj_le_diagP
      (ℓ := p) (f := f) (K := F) (p := 7) (n := 3)
      h (by norm_num) h7 R hR7
  let fP : unitarySU p f F 3 →* unitarySU p f F 3 := (MulAut.conj P⁻¹).toMonoidHom
  let R₁ : Subgroup (unitarySU p f F 3) := R.map fP
  let B₁ : Subgroup (unitarySU p f F 3) := B.map fP
  have hR₁diag : R₁ ≤ CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.diagP p f 7 3 F := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, hu, hru⟩ := Subgroup.mem_map.mp (hP hr)
    rw [← hru]
    have hconj : (MulAut.conj P⁻¹) ((MulAut.conj P) u) = u := by
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    change (MulAut.conj P⁻¹) ((MulAut.conj P) u) ∈
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.diagP p f 7 3 F
    rw [hconj]
    exact hu
  have hB₁card : Nat.card B₁ = 3 := by
    dsimp [B₁]
    rw [Subgroup.card_map_of_injective (MulAut.conj P⁻¹).injective, hB3]
  obtain ⟨b₁, hb₁mem, hb₁ord, hb₁gen⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_zpowers_eq_of_card_three hB₁card
  have hb₁pow : b₁ ^ 3 = 1 := by
    simpa [hb₁ord] using pow_orderOf_eq_one b₁
  have hb₁ne : b₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb₁ord
    omega
  have hB₁N : B₁ ≤ Subgroup.normalizer (R₁ : Set (unitarySU p f F 3)) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb r hr
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨b₀ * r₀ * b₀⁻¹, ?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp hBN) b₀ hb₀ r₀ hr₀
    · rw [map_mul, map_mul, map_inv]
  have hb₁norm : ∀ r ∈ R₁, b₁ * r * b₁⁻¹ ∈ R₁ :=
    fun r hr => (Subgroup.le_normalizer_iff.mp hB₁N) b₁ hb₁mem r hr
  have hb₁nc : ∃ r ∈ R₁, b₁ * r ≠ r * b₁ := by
    by_contra hcon
    push Not at hcon
    have hRleC : R ≤ Subgroup.centralizer (B : Set (unitarySU p f F 3)) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb₁ : P⁻¹ * b * P ∈ B₁ := by
        refine Subgroup.mem_map.mpr ⟨b, hb, ?_⟩
        simp [fP]
      have hr₁ : P⁻¹ * r * P ∈ R₁ := by
        refine Subgroup.mem_map.mpr ⟨r, hr, ?_⟩
        simp [fP]
      have hcomm₁ : Commute b₁ (P⁻¹ * r * P) := hcon _ hr₁
      have hb₁zp : P⁻¹ * b * P ∈ Subgroup.zpowers b₁ := by
        rw [hb₁gen]
        exact hb₁
      have hbc : Commute (P⁻¹ * b * P) (P⁻¹ * r * P) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb₁zp
        rw [← hn]
        exact hcomm₁.zpow_left n
      calc b * r = P * ((P⁻¹ * b * P) * (P⁻¹ * r * P)) * P⁻¹ := by group
        _ = P * ((P⁻¹ * r * P) * (P⁻¹ * b * P)) * P⁻¹ := by
              rw [(commute_iff_eq _ _).mp hbc]
        _ = r * b := by group
    have hRbot : R = ⊥ := by
      have hinf : R ⊓ Subgroup.centralizer (B : Set (unitarySU p f F 3)) = R :=
        inf_eq_left.mpr hRleC
      rw [hRC] at hinf
      exact hinf.symm
    rw [hRbot, Subgroup.card_bot] at hR49
    omega
  refine ⟨P, R₁, b₁, rfl, hR₁diag, ?_, hb₁pow, hb₁ne, hb₁norm, hb₁nc⟩
  exact hb₁gen.symm


theorem diag_entries_of_diag_mul_perm {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {d : Fin 3 → F} {k : ℕ} {b : GL (Fin 3) F}
    (hb : (b : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k)
    (hbSU : b ∈ unitarySU p f F 3) :
    (∀ i, d i ≠ 0) ∧ (∀ i, h.norm (d i) = 1) ∧ d 0 * d 1 * d 2 = 1 := by
  let σG : GL (Fin 3) F := CFSG.RankThree.PartTwo.Sec16.Proof166Res6.permGL
  have hσmat : ((σG : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
    CFSG.RankThree.PartTwo.Sec16.Proof166Res6.coe_permGL
  let D : GL (Fin 3) F := b * (σG ^ k)⁻¹
  have hσk : ((σG ^ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k := by
    rw [Units.val_pow_eq_pow_val, hσmat]
  have hcancel : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k : Matrix (Fin 3) (Fin 3) F) *
      (((σG ^ k)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← hσk, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hDmat : ((D : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal d := by
    dsimp [D]
    change ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((σG ^ k)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal d
    rw [hb, mul_assoc, hcancel, mul_one]
  have hDmem : D ∈ unitarySU p f F 3 := by
    dsimp [D]
    exact mul_mem hbSU (inv_mem (pow_mem
      (CFSG.RankThree.PartTwo.Sec16.Proof166Res6.permGL_mem_unitarySU h) k))
  have hDdet : ((D : Matrix (Fin 3) (Fin 3) F)).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSU hDmem
  have hprod : ∏ i, d i = 1 := by
    rw [← Matrix.det_diagonal, ← hDmat]
    exact hDdet
  have hdne : ∀ i, d i ≠ 0 := by
    have hne : ∏ i, d i ≠ 0 := by
      rw [hprod]
      exact one_ne_zero
    intro i
    exact (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hdunitary : ((D : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      (D : Matrix (Fin 3) (Fin 3) F) = 1 :=
    (mem_unitarySU_iff h).mp hDmem |>.2
  have hdnorm : ∀ i, h.norm (d i) = 1 := by
    intro i
    have hentry := congrFun (congrFun hdunitary i) i
    rw [hDmat, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hentry
    have h1 : h.bar (d i) * d i = 1 := by simpa using hentry
    rw [UnitaryFieldData.norm, mul_comm]
    exact h1
  refine ⟨hdne, hdnorm, ?_⟩
  have hp := hprod
  simpa [Fin.prod_univ_three] using hp

theorem exists_diagonal_mul_perm_data {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {R₁ : Subgroup (unitarySU p f F 3)}
    (hR₁card : Nat.card R₁ = 49)
    (hR₁diag : R₁ ≤ CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.diagP p f 7 3 F)
    {b₁ : unitarySU p f F 3} (hb₁pow : b₁ ^ 3 = 1)
    (hb₁norm : ∀ r ∈ R₁, b₁ * r * b₁⁻¹ ∈ R₁)
    (hb₁nc : ∃ r ∈ R₁, b₁ * r ≠ r * b₁) :
    ∃ (d : Fin 3 → F) (k : ℕ), (k = 1 ∨ k = 2) ∧
      ((b₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k ∧
      (∀ i, d i ≠ 0) ∧ (∀ i, h.norm (d i) = 1) ∧ d 0 * d 1 * d 2 = 1 := by
  let S : Subgroup (GL (Fin 3) F) := R₁.map (unitarySU p f F 3).subtype
  have hSdiag : ∀ u ∈ S, ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    exact (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.mem_diagP.mp (hR₁diag hr)).1
  have hScard : Nat.card S = 7 ^ 2 := by
    have hcard : Nat.card S = Nat.card R₁ := by
      dsimp [S]
      exact Subgroup.card_map_of_injective (unitarySU p f F 3).subtype_injective
    rw [hcard, hR₁card]
    norm_num
  have hSdet : ∀ u ∈ S, ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU r.2
  have hSexp : ∀ u ∈ S, u ^ 7 = 1 := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    have hr7 : r ^ 7 = 1 :=
      (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.mem_diagP.mp (hR₁diag hr)).2
    exact congrArg (fun x : unitarySU p f F 3 => ((x : GL (Fin 3) F))) hr7
  have hSsep : ∀ i j : Fin 3, i ≠ j →
      ∃ u ∈ S, ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i ≠
        ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j := by
    intro i j hij
    exact exists_diag_entry_ne_of_card (p := 7) (by norm_num) hSdiag hSdet hSexp hScard hij
  have hbG3 : ((b₁ : GL (Fin 3) F)) ^ 3 = 1 := by
    simpa using congrArg (fun x : unitarySU p f F 3 => ((x : GL (Fin 3) F))) hb₁pow
  have hbGR : ∀ u ∈ S, (b₁ : GL (Fin 3) F) * u * (b₁ : GL (Fin 3) F)⁻¹ ∈ S := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨b₁ * r * b₁⁻¹, hb₁norm r hr, ?_⟩
    simp
  have hbGc : ∃ u ∈ S, (b₁ : GL (Fin 3) F) * u ≠ u * (b₁ : GL (Fin 3) F) := by
    obtain ⟨r, hr, hnc⟩ := hb₁nc
    refine ⟨(r : GL (Fin 3) F), Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    intro heq
    apply hnc
    have h' : ((b₁ * r : unitarySU p f F 3) : GL (Fin 3) F) =
        ((r * b₁ : unitarySU p f F 3) : GL (Fin 3) F) := by
      simpa using heq
    exact Subtype.ext h'
  obtain ⟨d, k, hk, hbd⟩ := exists_diagonal_mul_shift_pow hSdiag hSsep hbG3 hbGR hbGc
  obtain ⟨hdne, hdnorm, hdprod⟩ := diag_entries_of_diag_mul_perm h hbd b₁.2
  exact ⟨d, k, hk, hbd, hdne, hdnorm, hdprod⟩


theorem exists_unitary_diag_of_tau {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {τ : Fin 3 → F} (hτ0 : ∀ i, τ i ≠ 0)
    (hτn : ∀ i, h.norm (τ i) = 1) (hτp : ∏ i, τ i = 1) :
    ∃ t : unitarySU p f F 3,
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal τ := by
  let τu : Fin 3 → Fˣ := fun i => Units.mk0 (τ i) (hτ0 i)
  have hτu : ∀ i, ((τu i : Fˣ) : F) = τ i := fun i => Units.val_mk0 (hτ0 i)
  have hnorm : ∀ i, h.norm (τu i : F) = 1 := by
    intro i
    rw [hτu i]
    exact hτn i
  have hprod : ∏ i, ((τu i : Fˣ) : F) = 1 := by
    calc ∏ i, ((τu i : Fˣ) : F) = ∏ i, τ i := Finset.prod_congr rfl fun i _ => hτu i
      _ = 1 := hτp
  refine ⟨⟨CFSG.SectionRank.OddCover.diagHom 3 τu,
    diagHom_mem_unitarySU_of_norm_one_prod_one h hnorm hprod⟩, ?_⟩
  rw [CFSG.SectionRank.OddCover.coe_diagHom]
  exact congrArg Matrix.diagonal (funext hτu)

theorem diag_conj_shift_one {F : Type} [Field F] {τ d : Fin 3 → F}
    (hτ : ∀ i, τ i ≠ 0) (h0 : τ 0 * d 0 = τ 2) (h1 : τ 1 * d 1 = τ 0)
    (h2 : τ 2 * d 2 = τ 1) :
    diagonal τ * (diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) *
        (diagonal τ)⁻¹ = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  have hinv : (diagonal τ : Matrix (Fin 3) (Fin 3) F)⁻¹ =
      diagonal (fun i => (τ i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hτ i)
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h0, h1, h2,
      mul_inv_cancel₀ (hτ 0), mul_inv_cancel₀ (hτ 1), mul_inv_cancel₀ (hτ 2)]

theorem diag_conj_shift_two {F : Type} [Field F] {τ d : Fin 3 → F}
    (hτ : ∀ i, τ i ≠ 0) (h0 : τ 0 * d 0 = τ 1) (h1 : τ 1 * d 1 = τ 2)
    (h2 : τ 2 * d 2 = τ 0) :
    diagonal τ * (diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ 2) *
        (diagonal τ)⁻¹ = !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ 2 := by
  have hsq : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) ^ 2 =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have hinv : (diagonal τ : Matrix (Fin 3) (Fin 3) F)⁻¹ =
      diagonal (fun i => (τ i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hτ i)
  rw [hsq, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h0, h1, h2,
      mul_inv_cancel₀ (hτ 0), mul_inv_cancel₀ (hτ 1), mul_inv_cancel₀ (hτ 2)]

theorem exists_unitary_conj_perm_one {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) {d : Fin 3 → F}
    (hdne : ∀ i, d i ≠ 0) (hdnorm : ∀ i, h.norm (d i) = 1)
    (hdprod : d 0 * d 1 * d 2 = 1) {b : unitarySU p f F 3}
    (hb : ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) :
    ∃ t : unitarySU p f F 3,
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag ∧
      t * b * t⁻¹ = permSU h := by
  have hd1 : d 1 ≠ 0 := hdne 1
  have htarget : d 1 ^ 2 * d 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero (mul_ne_zero hd1 hd1) (hdne 2)
  have htargetnorm : h.norm (d 1 ^ 2 * d 2) = 1 := by
    rw [norm_mul_eq h, pow_two, norm_mul_eq h, hdnorm 1, hdnorm 2, one_mul, one_mul]
  obtain ⟨s, hs0, hsnorm, hs3⟩ := exists_norm_one_cube_root_of_mod h hq htarget htargetnorm
  let τ : Fin 3 → F := ![s, s / d 1, s * d 0]
  have hτ0 : ∀ i, τ i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [τ] using hs0
    · simpa [τ] using div_ne_zero hs0 hd1
    · simpa [τ] using mul_ne_zero hs0 (hdne 0)
  have hτn : ∀ i, h.norm (τ i) = 1 := by
    intro i
    fin_cases i
    · simpa [τ] using hsnorm
    · have hdiv : h.norm (s / d 1) = 1 := by
        simp [div_eq_mul_inv, norm_mul_eq h, norm_inv_eq h, hsnorm, hdnorm]
      simpa [τ] using hdiv
    · have hmul : h.norm (s * d 0) = 1 := by
        simp [norm_mul_eq h, hsnorm, hdnorm]
      simpa [τ] using hmul
  have hτp : ∏ i, τ i = 1 := by
    have hs : s ^ 3 * d 0 = d 1 := by
      rw [hs3]
      linear_combination (d 1) * hdprod
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    calc s * (s / d 1) * (s * d 0) = s ^ 3 * d 0 / d 1 := by
          field_simp [hd1]
      _ = d 1 / d 1 := by rw [hs]
      _ = 1 := div_self hd1
  have heq0 : τ 0 * d 0 = τ 2 := by simp [τ]
  have heq1 : τ 1 * d 1 = τ 0 := by
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [div_mul_cancel₀ _ hd1]
  have heq2 : τ 2 * d 2 = τ 1 := by
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [eq_div_iff hd1]
    calc s * d 0 * d 2 * d 1 = s * (d 0 * d 1 * d 2) := by ring
      _ = s := by rw [hdprod, mul_one]
  obtain ⟨t, htmat⟩ := exists_unitary_diag_of_tau h hτ0 hτn hτp
  refine ⟨t, ?_, ?_⟩
  · rw [htmat]
    exact Matrix.isDiag_diagonal _
  · apply Subtype.ext
    change (t : GL (Fin 3) F) * (b : GL (Fin 3) F) * (t : GL (Fin 3) F)⁻¹ =
      CFSG.RankThree.PartTwo.Sec16.Proof166Res6.permGL
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, htmat, hb,
      CFSG.RankThree.PartTwo.Sec16.Proof166Res6.coe_permGL]
    exact diag_conj_shift_one hτ0 heq0 heq1 heq2


theorem exists_unitary_conj_perm_two {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) {d : Fin 3 → F}
    (hdne : ∀ i, d i ≠ 0) (hdnorm : ∀ i, h.norm (d i) = 1)
    (hdprod : d 0 * d 1 * d 2 = 1) {b : unitarySU p f F 3}
    (hb : ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ 2) :
    ∃ t : unitarySU p f F 3,
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag ∧
      t * b * t⁻¹ = permSU h ^ 2 := by
  have hd2 : d 2 ≠ 0 := hdne 2
  have htarget : d 1 * d 2 ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero (hdne 1) (mul_ne_zero hd2 hd2)
  have htargetnorm : h.norm (d 1 * d 2 ^ 2) = 1 := by
    rw [norm_mul_eq h, pow_two, norm_mul_eq h, hdnorm 1, hdnorm 2, one_mul, one_mul]
  obtain ⟨s, hs0, hsnorm, hs3⟩ := exists_norm_one_cube_root_of_mod h hq htarget htargetnorm
  let τ : Fin 3 → F := ![s, s * d 0, s / d 2]
  have hτ0 : ∀ i, τ i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [τ] using hs0
    · simpa [τ] using mul_ne_zero hs0 (hdne 0)
    · simpa [τ] using div_ne_zero hs0 hd2
  have hτn : ∀ i, h.norm (τ i) = 1 := by
    intro i
    fin_cases i
    · simpa [τ] using hsnorm
    · have hmul : h.norm (s * d 0) = 1 := by
        simp [norm_mul_eq h, hsnorm, hdnorm]
      simpa [τ] using hmul
    · have hdiv : h.norm (s / d 2) = 1 := by
        simp [div_eq_mul_inv, norm_mul_eq h, norm_inv_eq h, hsnorm, hdnorm]
      simpa [τ] using hdiv
  have hτp : ∏ i, τ i = 1 := by
    have hs : s ^ 3 * d 0 = d 2 := by
      rw [hs3]
      linear_combination (d 2) * hdprod
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    calc s * (s * d 0) * (s / d 2) = s ^ 3 * d 0 / d 2 := by
          field_simp [hd2]
      _ = d 2 / d 2 := by rw [hs]
      _ = 1 := div_self hd2
  have heq0 : τ 0 * d 0 = τ 1 := by simp [τ]
  have heq1 : τ 1 * d 1 = τ 2 := by
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [eq_div_iff hd2]
    calc s * d 0 * d 1 * d 2 = s * (d 0 * d 1 * d 2) := by ring
      _ = s := by rw [hdprod, mul_one]
  have heq2 : τ 2 * d 2 = τ 0 := by
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [div_mul_cancel₀ _ hd2]
  obtain ⟨t, htmat⟩ := exists_unitary_diag_of_tau h hτ0 hτn hτp
  refine ⟨t, ?_, ?_⟩
  · rw [htmat]
    exact Matrix.isDiag_diagonal _
  · apply Subtype.ext
    change (t : GL (Fin 3) F) * (b : GL (Fin 3) F) * (t : GL (Fin 3) F)⁻¹ =
      CFSG.RankThree.PartTwo.Sec16.Proof166Res6.permGL ^ 2
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, htmat, hb,
      Units.val_pow_eq_pow_val, CFSG.RankThree.PartTwo.Sec16.Proof166Res6.coe_permGL]
    exact diag_conj_shift_two hτ0 heq0 heq1 heq2

theorem conj_eq_zpowers_perm_of_conj {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {P t : unitarySU p f F 3}
    {B R R₁ : Subgroup (unitarySU p f F 3)} {b₁ : unitarySU p f F 3} {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hR₁eq : R₁ = R.map (MulAut.conj P⁻¹).toMonoidHom)
    (hR₁diag : R₁ ≤ CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.diagP p f 7 3 F)
    (hB₁gen : B.map (MulAut.conj P⁻¹).toMonoidHom = Subgroup.zpowers b₁)
    (htdiag : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (htconj : t * b₁ * t⁻¹ = permSU h ^ k) :
    B.map (MulAut.conj (t * P⁻¹)).toMonoidHom = Subgroup.zpowers (permSU h) ∧
      ∀ x : unitarySU p f F 3, ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag →
        x ∈ centralizer ((R.map (MulAut.conj (t * P⁻¹)).toMonoidHom :
          Subgroup (unitarySU p f F 3)) : Set (unitarySU p f F 3)) := by
  have hBmap : B.map (MulAut.conj (t * P⁻¹)).toMonoidHom =
      (B.map (MulAut.conj P⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (MulAut.conj (t * P⁻¹)) x = (MulAut.conj t) ((MulAut.conj P⁻¹) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hRmap : R.map (MulAut.conj (t * P⁻¹)).toMonoidHom =
      (R.map (MulAut.conj P⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (MulAut.conj (t * P⁻¹)) x = (MulAut.conj t) ((MulAut.conj P⁻¹) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hBz : B.map (MulAut.conj (t * P⁻¹)).toMonoidHom = Subgroup.zpowers (permSU h) := by
    rw [hBmap, hB₁gen, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj t) b₁) = Subgroup.zpowers (permSU h)
    rw [MulAut.conj_apply, htconj]
    rcases hk with rfl | rfl
    · simp
    · have hσ2 : permSU h ^ (2 : ℕ) = (permSU h)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc permSU h ^ 2 * permSU h = permSU h ^ 3 := (pow_succ (permSU h) 2).symm
          _ = 1 := by
            apply Subtype.ext
            exact CFSG.RankThree.PartTwo.Sec16.Proof166Res6.permGL_pow_three
      rw [hσ2, Subgroup.zpowers_inv]
  refine ⟨hBz, ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hRmap] at hy
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← hR₁eq] at hr
  have hrdiag : ((r : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag :=
    (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.mem_diagP.mp (hR₁diag hr)).1
  have hdiag : ((((t * r * t⁻¹ : unitarySU p f F 3)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).IsDiag := by
    change (((t : GL (Fin 3) F) * (r : GL (Fin 3) F) * (t : GL (Fin 3) F)⁻¹ :
      GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag
    exact CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_mul'
      (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_mul' htdiag hrdiag)
      (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_units_inv_val htdiag)
  apply Subtype.ext
  apply Units.ext
  simpa using (CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.commute_of_isDiag hdiag hx)

end U3Normal

theorem exists_conj_eq_zpowers_permSU {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) (h7 : 7 ∣ p ^ f + 1)
    {B R : Subgroup (unitarySU p f F 3)} (hBR : IsKGenPair B R) :
    ∃ g : unitarySU p f F 3, B.map (MulAut.conj g).toMonoidHom = zpowers (permSU h) ∧
      ∀ x : unitarySU p f F 3, ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag →
        x ∈ centralizer ((R.map (MulAut.conj g).toMonoidHom : Subgroup (unitarySU p f F 3)) :
          Set (unitarySU p f F 3)) := by
  obtain ⟨P, R₁, b₁, hR₁eq, hR₁diag, hB₁gen, hb₁pow, hb₁ne, hb₁norm, hb₁nc⟩ :=
    U3Normal.exists_diag_conj_data h h7 hBR
  have hR49 : Nat.card R = 49 := by
    obtain ⟨-, -, hR49, -, -⟩ := hBR
    exact hR49
  have hR₁card : Nat.card R₁ = 49 := by
    rw [hR₁eq, Subgroup.card_map_of_injective (MulAut.conj P⁻¹).injective, hR49]
  obtain ⟨d, k, hk, hbd, hdne, hdnorm, hdprod⟩ :=
    U3Normal.exists_diagonal_mul_perm_data h hR₁card hR₁diag hb₁pow hb₁norm hb₁nc
  rcases hk with hk1 | hk2
  · subst hk1
    obtain ⟨t, htdiag, htconj⟩ :=
      U3Normal.exists_unitary_conj_perm_one h hq hdne hdnorm hdprod (by simpa using hbd)
    exact ⟨t * P⁻¹, U3Normal.conj_eq_zpowers_perm_of_conj h (Or.inl rfl) hR₁eq hR₁diag
      hB₁gen htdiag (by simpa using htconj)⟩
  · subst hk2
    obtain ⟨t, htdiag, htconj⟩ :=
      U3Normal.exists_unitary_conj_perm_two h hq hdne hdnorm hdprod hbd
    exact ⟨t * P⁻¹, U3Normal.conj_eq_zpowers_perm_of_conj h (Or.inr rfl) hR₁eq hR₁diag
      hB₁gen htdiag htconj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
