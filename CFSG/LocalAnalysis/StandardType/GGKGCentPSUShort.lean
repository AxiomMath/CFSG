module

public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.StandardType.GGKGPosSUStd
public import CFSG.LocalAnalysis.StandardType.GGKGPosSUTableB
import all CFSG.LieType.Universal.Unitary.Roots
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.LiftAutPSU
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LieType.Universal.Unitary.Clause0
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.KGCentSU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def coordDiag (ζ : F) (s i : Fin 6) : F :=
  if i = s then ζ else if i = Fin.rev s then ζ⁻¹ else 1

theorem entry_of_mul_diagonal {M : Matrix (Fin 6) (Fin 6) F} {φ : F ≃+* F} {t : Fin 6 → F}
    (h : M * (diagonal t).map φ = diagonal t * M) (i j : Fin 6) :
    M i j * φ (t j) = t i * M i j := by
  have h1 := congrFun (congrFun h i) j
  rwa [diagonal_map (map_zero φ), mul_diagonal, diagonal_mul] at h1

theorem rootMatrix_map (φ : F ≃+* F) (i j : Fin 6) (c : F) :
    (rootMatrix σ i j c).map φ =
      1 + single i j (φ c) - single (Fin.rev j) (Fin.rev i) (φ (σ c)) := by
  change φ.mapMatrix (rootMatrix σ i j c) = _
  rw [rootMatrix, map_sub, map_add, map_one, RingEquiv.mapMatrix_apply, RingEquiv.mapMatrix_apply,
    map_single, map_single]

theorem root_entry_ab {M : Matrix (Fin 6) (Fin 6) F} {φ : F ≃+* F} {a b : Fin 6}
    (hba : b ≠ Fin.rev a) (c : F)
    (h : M * (rootMatrix σ a b c).map φ = rootMatrix σ a b c * M) :
    M a a * φ c = c * M b b := by
  have h1 := congrFun (congrFun h a) b
  have hab' : a ≠ Fin.rev b := fun e => hba (by rw [e, Fin.rev_rev])
  rw [rootMatrix_map, rootMatrix, mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul] at h1
  simp only [Matrix.sub_apply, Matrix.add_apply, mul_single_apply_same,
    mul_single_apply_of_ne (hbj := hba), single_mul_apply_same, single_mul_apply_of_ne (h := hab'),
    sub_zero] at h1
  linear_combination h1

theorem root_entry_rev {M : Matrix (Fin 6) (Fin 6) F} {φ : F ≃+* F} {a b : Fin 6}
    (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hba : b ≠ Fin.rev a) (c : F)
    (h : M * (rootMatrix σ a b c).map φ = rootMatrix σ a b c * M) :
    σ c * M (Fin.rev a) a = 0 := by
  have h1 := congrFun (congrFun h (Fin.rev b)) a
  have hrb : Fin.rev b ≠ a := fun e => hba (by rw [← e, Fin.rev_rev])
  rw [rootMatrix_map, rootMatrix, mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul] at h1
  simp only [Matrix.sub_apply, Matrix.add_apply, mul_single_apply_of_ne (hbj := hab),
    mul_single_apply_of_ne (hbj := ha), single_mul_apply_of_ne (h := hrb),
    single_mul_apply_same, add_zero, sub_zero] at h1
  linear_combination h1

theorem eq_one_of_fix_PSU [Fintype F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (α : MulAut ↥(SU σ 6)) (A : GL (Fin 6) F) (φ : F ≃+* F)
    (hA : ∀ u : ↥(SU σ 6),
      ((α u : ↥(SU σ 6)) : GL (Fin 6) F) = A * glAut φ (u : GL (Fin 6) F) * A⁻¹)
    (hT : ∀ s : Fin 6, ∃ d : ↥(SU σ 6), α d = d ∧ ∃ ζ : F, ζ ≠ 0 ∧ ζ ^ 2 ≠ 1 ∧
      mat σ 6 d = diagonal (coordDiag ζ s))
    {a b : Fin 6} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a)
    (hR : ∀ c : Multiplicative F, α (rootHom σ hσ hab ha hb c) = rootHom σ hσ hab ha hb c)
    (m : ℕ) (h2 : α ^ (2 ^ m) = 1) : α = 1 := by
  classical
  set M : Matrix (Fin 6) (Fin 6) F := (A : Matrix (Fin 6) (Fin 6) F) with hM
  have hfix : ∀ u : ↥(SU σ 6), α u = u → M * (mat σ 6 u).map φ = mat σ 6 u * M := by
    intro u hu
    have h1 := hA u
    rw [hu] at h1
    have h2 : A * glAut φ (u : GL (Fin 6) F) = (u : GL (Fin 6) F) * A := by
      calc A * glAut φ (u : GL (Fin 6) F) = (A * glAut φ (u : GL (Fin 6) F) * A⁻¹) * A := by group
        _ = (u : GL (Fin 6) F) * A := by rw [← h1]
    have h3 := congrArg (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) h2
    simp only [Units.val_mul, coe_glAut] at h3
    rw [mat_apply]
    exact h3
  have hKT : ∀ s : Fin 6, ∃ ζ : F, ζ ≠ 0 ∧ ζ ^ 2 ≠ 1 ∧
      ∀ i j, M i j * φ (coordDiag ζ s j) = coordDiag ζ s i * M i j := by
    intro s
    obtain ⟨d, hd, ζ, hζ0, hζ, hdm⟩ := hT s
    refine ⟨ζ, hζ0, hζ, fun i j => entry_of_mul_diagonal ?_ i j⟩
    rw [← hdm]
    exact hfix d hd
  have hroot : ∀ c : F, M * (rootMatrix σ a b c).map φ = rootMatrix σ a b c * M := by
    intro c
    have h := hfix _ (hR (Multiplicative.ofAdd c))
    rwa [mat_apply, coe_rootHom, toAdd_ofAdd] at h
  have hζ1 : ∀ ζ : F, ζ ^ 2 ≠ 1 → ζ ≠ 1 := fun ζ hζ h => hζ (by rw [h, one_pow])
  have hcol : ∀ i, i ≠ a → M i a = 0 := by
    intro i hi
    by_cases hia : i = Fin.rev a
    · subst hia
      have h := root_entry_rev hab ha hba 1 (hroot 1)
      rwa [map_one, one_mul] at h
    · obtain ⟨ζ, -, hζ, hK⟩ := hKT a
      have h := hK i a
      simp only [coordDiag, if_neg hi, if_neg hia, if_true] at h
      by_contra hne
      have h' : φ ζ = 1 := by
        have h2 : M i a * φ ζ = M i a * 1 := by rw [h, one_mul, mul_one]
        exact mul_left_cancel₀ hne h2
      exact hζ1 ζ hζ (φ.injective (h'.trans (map_one φ).symm))
  have hMinv : (↑A⁻¹ : Matrix (Fin 6) (Fin 6) F) * M = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have haa : M a a ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hMinv a) a
    rw [mul_apply, one_apply_eq] at h1
    rw [Finset.sum_eq_zero fun k _ => ?_] at h1
    · exact zero_ne_one h1
    · by_cases hk : k = a
      · rw [hk, h0, mul_zero]
      · rw [hcol k hk, mul_zero]
  have hab1 := root_entry_ab hba 1 (hroot 1)
  rw [map_one, mul_one, one_mul] at hab1
  have hφ : ∀ c, φ c = c := by
    intro c
    have h := root_entry_ab hba c (hroot c)
    rw [← hab1] at h
    exact mul_left_cancel₀ haa (h.trans (mul_comm c (M a a)))
  have hdiag : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    obtain ⟨ζ, hζ0, hζ, hK⟩ := hKT j
    have h := hK i j
    rw [hφ] at h
    by_contra hne
    have h' : coordDiag ζ j j = coordDiag ζ j i := by
      have := h.trans (mul_comm _ _)
      exact mul_left_cancel₀ hne this
    simp only [coordDiag, if_neg hij, if_true] at h'
    by_cases hir : i = Fin.rev j
    · rw [if_pos hir] at h'
      apply hζ
      rw [pow_two]
      nth_rewrite 2 [h']
      exact mul_inv_cancel₀ hζ0
    · rw [if_neg hir] at h'
      exact hζ1 ζ hζ h'
  have hii : ∀ i, M i i ≠ 0 := by
    intro i h0
    have h1 := congrFun (congrFun hMinv i) i
    rw [mul_apply, one_apply_eq] at h1
    rw [Finset.sum_eq_zero fun k _ => ?_] at h1
    · exact zero_ne_one h1
    · by_cases hk : k = i
      · rw [hk, h0, mul_zero]
      · rw [hdiag k i hk, mul_zero]
  have hglId : ∀ x : GL (Fin 6) F, glAut φ x = x := by
    intro x
    ext i j
    rw [coe_glAut, Matrix.map_apply, hφ]
  have hαA : ∀ u : ↥(SU σ 6), ((α u : ↥(SU σ 6)) : GL (Fin 6) F) = A * u * A⁻¹ := by
    intro u
    rw [hA, hglId]
  have hpow : ∀ (n : ℕ) (u : ↥(SU σ 6)),
      (((α ^ n) u : ↥(SU σ 6)) : GL (Fin 6) F) = A ^ n * u * (A ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, hαA, ih, pow_succ']
      group
  have hAN : A ^ (Fintype.card F - 1) = 1 := by
    have hMd : M = diagonal (fun i => M i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij]
        exact hdiag i j hij
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hM, hMd, diagonal_pow, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    exact FiniteField.pow_card_sub_one_eq_one _ (hii i)
  have hαN : α ^ (Fintype.card F - 1) = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hpow, hAN, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hodd : Odd (Fintype.card F - 1) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩) odd_one
  have hcop : Nat.Coprime (2 ^ m) (Fintype.card F - 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) hcop)
    (orderOf_dvd_of_pow_eq_one hαN))

theorem exists_pos_toStd_weylAction_short {n : ℕ}
    (w : (coxeterMatrix (isFiniteType_cartan n)).Group) {l : Fin (n / 2)} (hl : l.val + 1 < n / 2) :
    ∃ i j : Fin n, i ≠ j ∧ i ≠ Fin.rev i ∧ j ≠ Fin.rev j ∧ j ≠ Fin.rev i ∧
      toStd n (weylAction (isFiniteType_cartan n) w (Pi.single l 1)) = weight n i - weight n j := by
  induction w using (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    rw [map_one, Module.End.one_apply]
    exact ⟨lowIdx l, lowIdx ⟨l.val + 1, hl⟩, Fin.ne_of_val_ne (by simp [lowIdx]),
      lowIdx_ne_rev l l, lowIdx_ne_rev _ _, lowIdx_ne_rev _ _,
      by rw [toStd_single_of_lt n hl, weight_lowIdx, weight_lowIdx]⟩
  | mul_simple_left w k ih =>
    obtain ⟨i, j, hij, hi, hj, hji, h⟩ := ih
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, h]
    refine ⟨levelPerm k i, levelPerm k j, (levelPerm k).injective.ne hij,
      levelPerm_ne_rev k hi, levelPerm_ne_rev k hj, ?_, ?_⟩
    · rw [← levelPerm_rev]
      exact (levelPerm k).injective.ne hji
    · rw [stdRefl_sub, weight_levelPerm, weight_levelPerm]

theorem eq_one_of_mul_inv_mem_center {K : Type*} [Group K] (hK : commutator K = ⊤)
    (β : MulAut K) (h : ∀ u, β u * u⁻¹ ∈ Subgroup.center K) : β = 1 := by
  let z : K →* K :=
    { toFun := fun u => β u * u⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        have hv := Subgroup.mem_center_iff.mp (h v)
        calc β (u * v) * (u * v)⁻¹ = β u * (β v * v⁻¹) * u⁻¹ := by rw [map_mul]; group
          _ = β u * (u⁻¹ * (β v * v⁻¹)) := by rw [mul_assoc, ← hv u⁻¹]
          _ = β u * u⁻¹ * (β v * v⁻¹) := by group }
  have hz : commutator K ≤ z.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (h a) (z b)).symm
  refine MulEquiv.ext fun u => ?_
  have hu : z u = 1 := hz (hK ▸ Subgroup.mem_top u)
  change β u * u⁻¹ = 1 at hu
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp hu

section Torus

open CFSG.StandardType.TableCRes

variable {g : ℕ}

theorem isDiag_mul_of {A B : Matrix (Fin 6) (Fin 6) (PSUF g)} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A * B).IsDiag := by
  rw [← ha.diagonal_diag, ← hb.diagonal_diag, diagonal_mul_diagonal]
  exact isDiag_diagonal _

theorem isDiag_pow_of {A : Matrix (Fin 6) (Fin 6) (PSUF g)} (ha : A.IsDiag) (k : ℕ) :
    (A ^ k).IsDiag := by
  rw [← ha.diagonal_diag, diagonal_pow]
  exact isDiag_diagonal _

theorem mat_comm_of_isDiag {x y : ↥(SU (PSUσ g) 6)} (hx : (mat (PSUσ g) 6 x).IsDiag)
    (hy : (mat (PSUσ g) 6 y).IsDiag) : x * y = y * x := by
  apply mat_injective
  rw [map_mul, map_mul, ← hx.diagonal_diag, ← hy.diagonal_diag, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mem_range_of_isDiag {p : ℕ} (hp : 0 < p) {B : Type*} [Group B]
    (ℓ : B →* ↥(SU (PSUσ g) 6)) (hpow : ∀ b, ℓ b ^ p = 1)
    (hdiag : ∀ b, (mat (PSUσ g) 6 (ℓ b)).IsDiag) (hcard : p ^ 3 ≤ Nat.card ℓ.range)
    {d : ↥(SU (PSUσ g) 6)} (hd : (mat (PSUσ g) 6 d).IsDiag) (hdp : d ^ p = 1) : d ∈ ℓ.range := by
  let E : Subgroup ↥(SU (PSUσ g) 6) := Subgroup.closure (Set.range ℓ ∪ {d})
  have hP : ∀ x ∈ E, (mat (PSUσ g) 6 x).IsDiag ∧ x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | hx
      · exact ⟨hdiag b, hpow b⟩
      · rw [Set.mem_singleton_iff.mp hx]
        exact ⟨hd, hdp⟩
    | one => exact ⟨by rw [map_one]; exact isDiag_one, one_pow p⟩
    | mul x y _ _ hx hy =>
      have hc : Commute x y := mat_comm_of_isDiag hx.1 hy.1
      refine ⟨by rw [map_mul]; exact isDiag_mul_of hx.1 hy.1, ?_⟩
      rw [hc.mul_pow, hx.2, hy.2, one_mul]
    | inv x _ hx =>
      have hinv : x⁻¹ = x ^ (p - 1) :=
        (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hp.ne', hx.2])).symm
      refine ⟨by rw [hinv, map_pow]; exact isDiag_pow_of hx.1 _, by rw [inv_pow, hx.2, inv_one]⟩
  have hle : ℓ.range ≤ E := by
    rintro _ ⟨b, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)
  have hcardE := KGPosSU.card_range_le_of_isDiag hp E (fun x hx => (hP x hx).1)
    (fun x hx => (hP x hx).2)
  have heq : ℓ.range = E := Subgroup.eq_of_le_of_card_ge hle (hcardE.trans hcard)
  rw [heq]
  exact Subgroup.subset_closure (Or.inr rfl)

end Torus

section Wrapper

open CFSG.StandardType.TableCRes CFSG.StandardType.ClassicalPosition CFSG.LieType.BorelTits
  CFSG.Open CFSG.Assembly

variable {g : ℕ}

theorem exists_coordDiag_SU {ζ : PSUF g} (hζ0 : ζ ≠ 0) (hσζ : PSUσ g ζ = ζ) (s : Fin 6) :
    ∃ d : ↥(SU (PSUσ g) 6), mat (PSUσ g) 6 d = diagonal (coordDiag ζ s) := by
  have hrev : ∀ i : Fin 6, Fin.rev i ≠ i := by decide
  have ht : ∀ i, unitaryInvolution (PSUF g) 2 (g + 1) (coordDiag ζ s i) *
      coordDiag ζ s (Fin.rev i) = 1 := by
    intro i
    change PSUσ g (coordDiag ζ s i) * coordDiag ζ s (Fin.rev i) = 1
    by_cases his : i = s
    · subst his
      simp [coordDiag, hrev i, hσζ, hζ0]
    · by_cases hir : i = Fin.rev s
      · subst hir
        simp [coordDiag, his, hσζ, hζ0]
      · have h1 : Fin.rev i ≠ s := fun e => hir (by rw [← e, Fin.rev_rev])
        have h2 : Fin.rev i ≠ Fin.rev s := fun e => his (Fin.rev_injective e)
        simp only [coordDiag, if_neg his, if_neg hir, if_neg h1, if_neg h2, map_one, mul_one]
  have hsplit : ∀ i, coordDiag ζ s i =
      (if i = s then ζ else 1) * (if i = Fin.rev s then ζ⁻¹ else 1) := by
    intro i
    by_cases his : i = s
    · subst his
      simp [coordDiag, (hrev i).symm]
    · simp only [coordDiag, if_neg his, one_mul]
  have hp : ∏ i, coordDiag ζ s i = 1 := by
    simp only [hsplit, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hζ0
  exact ⟨MpStdSU.diagSU (coordDiag ζ s) ht hp, MpStdSU.mat_diagSU _ ht hp⟩

theorem mem_centralizer_of_tableBPos_PSU_short {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs Y : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (g + 1) - 1)
    (ψ : (ggU .PSU 6 (g + 1)).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .PSU 6 (g + 1)).K)
    (hrange : ψ.range = Y)
    (ε : (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).Group ≃* ↥(ggAutomizer Y Bs))
    (hlev : ∀ (w : (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).Group)
      (i : Fin (ggU .PSU 6 (g + 1)).D.rank),
      ggRankOneIn Y Bs
        ((ε (w * (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU .PSU 6 (g + 1)).D
          (weylAction (ggU .PSU 6 (g + 1)).D.isFiniteType w (Pi.single i 1))).map ψ)
    (ℓ : ↥Bs →* (ggU .PSU 6 (g + 1)).K)
    (hℓ : ∀ (b : ↥Bs) (u : (ggU .PSU 6 (g + 1)).K),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hpow : ∀ b, ℓ b ^ p = 1) (hcard : p ^ 3 ≤ Nat.card ℓ.range)
    (hdiag : ∀ b, (mat (PSUσ g) 6 (ℓ b)).IsDiag)
    {t : G} (m : ℕ) (ht2 : t ^ (2 ^ m) = 1) (htB : t ∈ Subgroup.centralizer (Bs : Set G))
    (htN : t ∈ Subgroup.normalizer (Y : Set G))
    (v : (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).Group)
    (k : Fin (ggU .PSU 6 (g + 1)).D.rank) (hk : k.val < 2)
    (hcent : ∀ z ∈ ggRankOneIn Y Bs
      ((ε (v * (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).simple k * v⁻¹) :
        ↥(ggAutomizer Y Bs)) : MulAut ↥Bs), t * z = z * t) :
    t ∈ Subgroup.centralizer (Y : Set G) := by
  classical
  have hσ : ∀ c, PSUσ g (PSUσ g c) = c := unitaryInvolution_involutive (card_PSUF g)
  have hadm : StatedLieAdmissible .PSU 6 2 (g + 1) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  let ψn : ↥(SU (PSUσ g) 6) →* G := ψ
  have hkerN : ψn.ker ≤ Subgroup.center ↥(SU (PSUσ g) 6) := hker
  have htN' : t ∈ Subgroup.normalizer (ψn.range : Set G) := by
    change t ∈ Subgroup.normalizer (ψ.range : Set G)
    rw [hrange]
    exact htN
  obtain ⟨α, A, φ, hα, hA⟩ :=
    exists_mulAut_lift_PSU (card_PSUF g) (by omega) (by norm_num : 4 ≤ 6) hkerN htN'
  have hpq' : ¬ p ∣ 2 ^ (g + 1) + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  let ℓn : ↥Bs →* ↥(SU (PSUσ g) 6) := ℓ
  have hαℓ : ∀ b, α (ℓn b) = ℓn b := fun b =>
    mulAut_apply_liftHom_PSU_eq (n := 6) (g := g) (by norm_num) ψn hkerN hp hpq' Bs ℓn hℓ hpow
      htB α hα b
  obtain ⟨ζ, hζ0, hζp, hζ2, hσζ⟩ : ∃ ζ : PSUF g, ζ ≠ 0 ∧ ζ ^ p = 1 ∧ ζ ^ 2 ≠ 1 ∧
      PSUσ g ζ = ζ := by
    have hdvd : p ∣ Nat.card (PSUF g)ˣ := by
      rw [Nat.card_units, card_PSUF]
      exact hpq.trans (Nat.sub_one_dvd_pow_sub_one _ 2)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hup : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    refine ⟨(u : PSUF g), u.ne_zero, by rw [← Units.val_pow_eq_pow_val, hup, Units.val_one], ?_, ?_⟩
    · intro h
      have h' : u ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have h2 := orderOf_dvd_of_pow_eq_one h'
      rw [hu] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · obtain ⟨c, hc⟩ := hpq
      have he : 2 ^ (g + 1) = p * c + 1 := by
        have := Nat.one_le_two_pow (n := g + 1)
        omega
      change unitaryInvolution (PSUF g) 2 (g + 1) (u : PSUF g) = (u : PSUF g)
      rw [unitaryInvolution_apply, he, pow_succ, pow_mul, ← Units.val_pow_eq_pow_val, hup,
        Units.val_one, one_pow, one_mul]
  have hT : ∀ s : Fin 6, ∃ d : ↥(SU (PSUσ g) 6), α d = d ∧ ∃ ζ' : PSUF g, ζ' ≠ 0 ∧
      ζ' ^ 2 ≠ 1 ∧ mat (PSUσ g) 6 d = diagonal (coordDiag ζ' s) := by
    intro s
    obtain ⟨d, hd⟩ := exists_coordDiag_SU hζ0 hσζ s
    have hdD : (mat (PSUσ g) 6 d).IsDiag := by
      rw [hd]
      exact isDiag_diagonal _
    have hdp : d ^ p = 1 := by
      apply mat_injective
      rw [map_pow, hd, diagonal_pow, map_one, ← diagonal_one]
      congr 1
      funext i
      simp only [coordDiag, Pi.pow_apply]
      split_ifs <;> simp [hζp, inv_pow]
    obtain ⟨b, rfl⟩ := mem_range_of_isDiag hp.pos ℓn hpow hdiag hcard hdD hdp
    exact ⟨ℓn b, hαℓ b, ζ, hζ0, hζ2, hd⟩
  have hk' : k.val + 1 < 6 / 2 := by
    change k.val + 1 < 3
    omega
  obtain ⟨a, b, hab, ha, hb, hba, hγ⟩ := exists_pos_toStd_weylAction_short (n := 6) v (l := k) hk'
  have hR : ∀ c : Multiplicative (PSUF g),
      α (rootHom (PSUσ g) hσ hab ha hb c) = rootHom (PSUσ g) hσ hab ha hb c := by
    intro c
    set x := rootHom (PSUσ g) hσ hab ha hb c with hx
    have hxmem : ψn x ∈ ggRankOneIn Y Bs
        ((ε (v * (coxeterMatrix (ggU .PSU 6 (g + 1)).D.isFiniteType).simple k * v⁻¹) :
          ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := by
      rw [hlev v k]
      exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_sup_left
        (rootHom_mem hσ hab ha hb hba hγ.symm c))
    have htx := hcent _ hxmem
    have h1 : ψn (α x) = ψn x := by
      rw [hα]
      calc t⁻¹ * ψn x * t = t⁻¹ * (t * ψn x) := by rw [mul_assoc, ← htx]
        _ = ψn x := by group
    have hz : α x * x⁻¹ ∈ Subgroup.center ↥(SU (PSUσ g) 6) :=
      hkerN (by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel])
    have hx2 : x * x = 1 := by
      rw [hx, ← map_mul, show c * c = 1 from
        Multiplicative.toAdd.injective (by rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]),
        map_one]
    have hax2 : α x * α x = 1 := by rw [← map_mul, hx2, map_one]
    have hzz : (α x * x⁻¹) * (α x * x⁻¹) = 1 := by
      have hzc := Subgroup.mem_center_iff.mp hz
      calc (α x * x⁻¹) * (α x * x⁻¹) = α x * (x⁻¹ * (α x * x⁻¹)) := by group
        _ = α x * ((α x * x⁻¹) * x⁻¹) := by rw [hzc x⁻¹]
        _ = (α x * α x) * (x * x)⁻¹ := by group
        _ = 1 := by rw [hax2, hx2, inv_one, one_mul]
    obtain ⟨c', hc'⟩ := PSU_center_scalar hadm hz
    have hc1 : c' * c' = 1 := by
      have h := congrArg (mat (PSUσ g) 6) hzz
      rw [map_mul, map_one, mat_apply, hc', ← map_mul (Matrix.scalar (Fin 6)),
        ← map_one (Matrix.scalar (Fin 6) : PSUF g →+* Matrix (Fin 6) (Fin 6) (PSUF g))] at h
      exact (Matrix.scalar_inj (n := Fin 6)).mp h
    have hc1' : c' = 1 := MpStdSU.eq_one_of_mul_self_eq_one hc1
    have hz1 : α x * x⁻¹ = 1 := by
      apply mat_injective
      rw [mat_apply, hc', hc1', map_one, map_one]
    exact mul_inv_eq_one.mp hz1
  have hαpow : ∀ (n : ℕ) (u : ↥(SU (PSUσ g) 6)), ψn ((α ^ n) u) = (t ^ n)⁻¹ * ψn u * t ^ n := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, hα, ih, pow_succ]
      group
  have hperf : commutator ↥(SU (PSUσ g) 6) = ⊤ :=
    (isQuasisimple_SU (n := 6) (card_PSUF g) (by norm_num) (by simp)).1.commutator_eq_top
  have h2 : α ^ (2 ^ m) = 1 := by
    apply eq_one_of_mul_inv_mem_center hperf
    intro u
    apply hkerN
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαpow, ht2, inv_one, one_mul, mul_one,
      mul_inv_cancel]
  have : Fintype (PSUF g) := Fintype.ofFinite _
  have hα1 := eq_one_of_fix_PSU hσ α A φ hA hT hab ha hb hba hR m h2
  rw [← hrange, Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h : ψn u = t⁻¹ * ψn u * t := by
    have h' := hα u
    rwa [hα1] at h'
  calc ψn u * t = t * (t⁻¹ * ψn u * t) := by group
    _ = t * ψn u := by rw [← h]

theorem exists_tableBPos_centCriterion_PSU {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {f : ℕ} {ψ : (ggU .PSU 6 f).K →* G}
    (hloc : GGKGPosLocalHypTw p Bs X .PSU 6 f ψ) :
    ∃ ψ' : (ggU .PSU 6 f).K →* G, (∃ k, ψ' = ψ.comp (MulAut.conj k).toMonoidHom) ∧
      ψ'.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ ψ'.range = X ∧
      ∃ ε : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs),
        (∀ i, GGIsReflection p
          ((ε ((coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
            MulAut ↥Bs)) ∧
        (∀ (w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group)
          (i : Fin (ggU .PSU 6 f).D.rank),
          ggRankOneIn X Bs
            ((ε (w * (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple i * w⁻¹) :
              ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
            (ggRootLevi (ggU .PSU 6 f).D
              (weylAction (ggU .PSU 6 f).D.isFiniteType w (Pi.single i 1))).map ψ') ∧
        Nat.card ↥Bs ≤ p ^ (ggU .PSU 6 f).D.rank *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
        (∀ b ∈ Bs, ∃ s ∈ ggTorus (ggU .PSU 6 f).D, ∀ z, b * ψ' z * b⁻¹ = ψ' (s * z * s⁻¹)) ∧
        ∀ t : G, (∃ m : ℕ, t ^ (2 ^ m) = 1) → t ∈ Subgroup.centralizer (Bs : Set G) →
          t ∈ Subgroup.normalizer (X : Set G) →
          ∀ (w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group)
            (k : Fin (ggU .PSU 6 f).D.rank), k.val < 2 →
            t ∈ Subgroup.centralizer (((ggRootLevi (ggU .PSU 6 f).D
              (weylAction (ggU .PSU 6 f).D.isFiniteType w (Pi.single k 1))).map ψ') : Set G) →
            t ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := hloc.1.2.2.1; omega⟩
  obtain ⟨⟨hp, hp2, -, hpq⟩, ⟨hker, hrange⟩, ⟨hBs, hN, hC3⟩, hdiag, hcard, h4⟩ := hloc
  let ψn : ↥(SU (PSUσ g) 6) →* G := ψ
  have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF g) 6) ψn b := hdiag
  obtain ⟨k, ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ, hdiagℓ⟩ :=
    KGPosSU.exists_diag_lift_SU ψn hp hp2 hpq hker hrange hBs hN hdiag' hcard h4
  obtain ⟨ψ', hψ'k, hk, hr, hℓ'⟩ := KGPosSU.exists_conj_lift ψn k ℓ hℓ
  have hker' : ψ'.ker ≤ Subgroup.center _ := hk ▸ hker
  have hrange' : ψ'.range = X := hr ▸ hrange
  have hℓT : ∀ b, ℓ b ∈ KGPosSU.diagP (PSUF g) (g + 1) p := fun b =>
    ⟨KGPosSU.mem_diagSubgroup_iff_isDiag.mpr (hdiagℓ b), hpowℓ b⟩
  obtain ⟨htor, hcardB⟩ := KGPosSU.torus_card_of_diag_lift hp.pos ψ' ℓ hℓ' hkerℓ hpowℓ hdiagℓ
  have hadm : StatedLieAdmissible .PSU 6 2 (g + 1) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_PSU hadm (by decide)).2.1
  obtain ⟨ε, hrefl, hrk⟩ :=
    KGPosSU.exists_tableB_chart ψ' hp hp2 hpq hker' hrange' hBs hC3 ℓ hℓ' hℓT hrankℓ hν
  refine ⟨ψ', ⟨k⁻¹, hψ'k⟩, hker', hrange', ε, hrefl, hrk, hcardB, htor, ?_⟩
  rintro t ⟨m, ht2⟩ htB htN w j hj htC
  refine mem_centralizer_of_tableBPos_PSU_short hp hp2 hpq ψ' hker' hrange' ε hrk ℓ hℓ' hpowℓ
    hrankℓ hdiagℓ m ht2 htB htN w j hj fun z hz => ?_
  have hz' := (congrArg (fun H : Subgroup G => z ∈ H) (hrk w j)).mp hz
  exact ((Subgroup.mem_centralizer_iff.mp htC) z hz').symm

end Wrapper

end CFSG.StandardType.KGCentSU

end
