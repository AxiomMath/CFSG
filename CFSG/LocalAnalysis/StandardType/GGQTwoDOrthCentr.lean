module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.ClassicalInvolution.Phan.PhanDn.KLinearIsometry
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)
open Matrix

section Centr

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

omit [Finite K] [Algebra F K] [CharP K 2] in
private theorem pmoc_eq_zero_or_one (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (α := F) (by rw [hF]; norm_num)
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F ≤ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have h : (Finset.univ : Finset F) = {0, 1} := Finset.univ_of_card_le_two hcard
  have ha : a ∈ (Finset.univ : Finset F) := Finset.mem_univ a
  rw [h] at ha
  simpa using ha

private theorem pmoc_matrix (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    {n : ℕ} (out : Fin n → Prop) (ζ : normOne (unitaryInvolution K 2 1)) (hζ : ζ ≠ 1)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (h2 : ∃ e : ℕ, g ^ (2 ^ e) = 1)
    (hglob : g * diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) =
      diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) * g)
    (hout : ∀ l : Fin n, out l →
      g * diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) =
        diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) * g) :
    ∃ M : Matrix (Fin n) (Fin n) K, (∀ v : Fin n → K, M *ᵥ v = g v) ∧
      (∀ x y : Fin n → K, herm (unitaryInvolution K 2 1) (M *ᵥ x) (M *ᵥ y) =
        herm (unitaryInvolution K 2 1) x y) ∧ M.det = 1 ∧
      (∀ l : Fin n, out l → ∀ b : Fin n, b ≠ l → M l b = 0) ∧
      (∀ l : Fin n, out l → ∀ a : Fin n, a ≠ l → M a l = 0) ∧
      (∀ l : Fin n, out l → M l l = 1) := by
  classical
  set ζ' : K := (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) with hζ'def
  have hζ'_ne_zero : ζ' ≠ 0 := by
    rw [hζ'def]
    exact Units.ne_zero ((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ)
  have hζ'_ne_one : ζ' ≠ 1 := by
    intro hone
    rw [hζ'def] at hone
    exact hζ (Subtype.ext (Units.ext hone))
  have hζ'_not_range : ∀ a : F, algebraMap F K a ≠ ζ' := by
    intro a ha
    rcases pmoc_eq_zero_or_one hF a with rfl | rfl
    · rw [map_zero] at ha
      exact hζ'_ne_zero ha.symm
    · rw [map_one] at ha
      exact hζ'_ne_one ha.symm
  let b : Module.Basis (Fin 2) F K := E.basisOneR hζ'_not_range
  have hb0 : b 0 = 1 := by
    simp only [b, QuadExt.basisOneR_apply]
    simp
  have hb1 : b 1 = ζ' := by
    simp only [b, QuadExt.basisOneR_apply]
    simp
  have hD_apply : ∀ x : Fin n → K,
      diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) x = ζ' • x := by
    intro x
    funext i
    rw [diagHom_apply, Pi.smul_apply]
    rfl
  have hglob_apply : ∀ x : Fin n → K,
      g (diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) x) =
        diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) (g x) := by
    intro x
    exact congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) => e x) hglob
  have hz : ∀ x : Fin n → K, g (ζ' • x) = ζ' • g x := by
    intro x
    rw [← hD_apply x, hglob_apply x, hD_apply (g x)]
  have hK : ∀ (a : K) (x : Fin n → K), g (a • x) = a • g x := by
    let S : Submodule F K :=
      { carrier := {a : K | ∀ x : Fin n → K, g (a • x) = a • g x}
        zero_mem' := by intro x; simp
        add_mem' := by
          intro a b ha hb x
          rw [add_smul, map_add, ha x, hb x, add_smul]
        smul_mem' := by
          intro c a ha x
          rw [smul_assoc, map_smul, ha x, smul_assoc] }
    have hspan : Submodule.span F ({1, ζ'} : Set K) ≤ S := by
      rw [Submodule.span_le]
      intro a ha
      rcases ha with rfl | rfl
      · intro x; simp
      · intro x; exact hz x
    have hrange : (Set.range b : Set K) = {1, ζ'} := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [hb0, hb1]
      · intro ha
        rcases ha with rfl | rfl
        · exact ⟨0, hb0⟩
        · exact ⟨1, hb1⟩
    have htop : Submodule.span F ({1, ζ'} : Set K) = ⊤ := by
      rw [← hrange, b.span_eq]
    intro a x
    exact hspan (by rw [htop]; exact Submodule.mem_top) x
  obtain ⟨e, he⟩ := h2
  have hherm : ∀ x y : Fin n → K,
      herm (unitaryInvolution K 2 1) (g x) (g y) =
        herm (unitaryInvolution K 2 1) x y :=
    fun x y => herm_map_of_isKLinear E hg hK x y
  let gK : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := g, map_add' := g.map_add, map_smul' := hK }
  let M : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' gK
  have hM_apply : ∀ v : Fin n → K, M *ᵥ v = g v := by
    intro v
    exact LinearMap.toMatrix'_mulVec gK v
  have hgK_pow : ∀ (t : ℕ) (v : Fin n → K), (gK ^ t) v = (g ^ t) v := by
    intro t
    induction t with
    | zero => intro v; simp
    | succ t ih =>
        intro v
        rw [pow_succ', Module.End.mul_apply, ih, pow_succ', LinearEquiv.mul_apply]
        rfl
  have hgK_one : gK ^ (2 ^ e) = 1 := by
    apply LinearMap.ext
    intro v
    rw [hgK_pow (2 ^ e) v, he]
    rfl
  have hpow : ∀ (t : ℕ) (v : Fin n → K), (M ^ t) *ᵥ v = (gK ^ t) v := by
    intro t
    induction t with
    | zero => intro v; simp
    | succ t ih =>
        intro v
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hM_apply, pow_succ', Module.End.mul_apply]
        rfl
  have hMpow : M ^ (2 ^ e) = 1 := by
    ext i j
    have h1 : (M ^ (2 ^ e)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [hpow (2 ^ e) (Pi.single j 1), hgK_one, Module.End.one_apply]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simpa [Pi.single_eq_same] using h2
    · rw [if_neg hij]
      rw [Pi.single_eq_of_ne hij] at h2
      simpa using h2
  have hDl_apply : ∀ (l : Fin n) (x : Fin n → K) (i : Fin n),
      diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) x i =
        (if i = l then ζ' else 1) * x i := by
    intro l x i
    rw [diagHom_apply]
    by_cases hi : i = l
    · subst hi
      rw [Pi.mulSingle_eq_same, if_pos rfl]
    · rw [Pi.mulSingle_eq_of_ne hi, if_neg hi]
      rfl
  have hout_comm : ∀ (l : Fin n), out l →
      ∀ x : Fin n → K,
        g (diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) x) =
          diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) (g x) := by
    intro l hl x
    have h := congrArg
      (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) => e x) (hout l hl)
    rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  have hrow : ∀ l : Fin n, out l →
      ∀ b : Fin n, b ≠ l → M l b = 0 := by
    intro l hl b hb
    have h := hout_comm l hl (Pi.single b 1)
    have hfix : diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ)
        (Pi.single b 1) = Pi.single b 1 := by
      funext i
      rw [hDl_apply]
      by_cases hib : i = b
      · subst hib
        rw [if_neg hb, one_mul]
      · rw [Pi.single_eq_of_ne hib, mul_zero]
    rw [hfix] at h
    have hL : (g (Pi.single b 1)) l = M l b := by
      rw [← hM_apply, Matrix.mulVec_single_one]
      rfl
    have hcoord := congrFun h l
    rw [hL, hDl_apply l (g (Pi.single b 1)) l, if_pos rfl, hL] at hcoord
    have hzero : (1 - ζ') * M l b = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hcoord
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (Ne.symm hζ'_ne_one))
  have hcol : ∀ l : Fin n, out l →
      ∀ a : Fin n, a ≠ l → M a l = 0 := by
    intro l hl a ha
    have h := hout_comm l hl (Pi.single l 1)
    have hfix : diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ)
        (Pi.single l 1) = ζ' • Pi.single l 1 := by
      funext i
      rw [hDl_apply, Pi.smul_apply]
      by_cases hil : i = l
      · subst hil
        rw [if_pos rfl]
        rfl
      · rw [if_neg hil, Pi.single_eq_of_ne hil]
        simp
    rw [hfix, hz (Pi.single l 1)] at h
    have hL : (g (Pi.single l 1)) a = M a l := by
      rw [← hM_apply, Matrix.mulVec_single_one]
      rfl
    have hcoord := congrFun h a
    rw [Pi.smul_apply, hDl_apply l (g (Pi.single l 1)) a, if_neg ha, one_mul, hL] at hcoord
    have hzero : (ζ' - 1) * M a l = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hcoord
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hζ'_ne_one)
  have hdiag : ∀ l : Fin n, out l → M l l = 1 := by
    intro l hl
    have hsingle : g (Pi.single l 1) = M l l • Pi.single l 1 := by
      rw [← hM_apply]
      funext b
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply]
      by_cases hb : b = l
      · subst hb
        simp
      · rw [hcol l hl b hb, Pi.single_eq_of_ne hb]
        simp
    have heig : ∀ t : ℕ, (g ^ t) (Pi.single l 1) = (M l l) ^ t • Pi.single l 1 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          rw [pow_succ', LinearEquiv.mul_apply, ih, hK ((M l l) ^ t) (Pi.single l 1),
            hsingle, smul_smul, pow_succ]
    have hfinal : (M l l) ^ (2 ^ e) • Pi.single l 1 = Pi.single l 1 := by
      rw [← heig (2 ^ e), he]
      rfl
    have hcoord := congrFun hfinal l
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hcoord
    have hsub : (M l l - 1) ^ (2 ^ e) = 0 := by
      rw [sub_pow_char_pow, hcoord]
      simp
    exact sub_eq_zero.mp
      ((pow_eq_zero_iff (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp hsub)
  have hdetM : M.det = 1 := by
    have h := congrArg Matrix.det hMpow
    rw [Matrix.det_pow, Matrix.det_one] at h
    have hsub : (M.det - 1) ^ (2 ^ e) = 0 := by
      rw [sub_pow_char_pow, h]
      simp
    exact sub_eq_zero.mp
      ((pow_eq_zero_iff (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp hsub)
  have hisoM : ∀ x y : Fin n → K,
      herm (unitaryInvolution K 2 1) (M *ᵥ x) (M *ᵥ y) =
        herm (unitaryInvolution K 2 1) x y := by
    intro x y
    rw [hM_apply x, hM_apply y]
    exact hherm x y
  exact ⟨M, hM_apply, hisoM, hdetM, hrow, hcol, hdiag⟩

theorem qtwoOrth_centr_window (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    (m k d : ℕ) (hd : 2 ≤ d) (h : k + d ≤ m + 1)
    (ζ : normOne (unitaryInvolution K 2 1)) (hζ : ζ ≠ 1)
    (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (h2 : ∃ e : ℕ, g ^ (2 ^ e) = 1)
    (hglob : g * diagHom F (unitaryInvolution K 2 1) (m + 1) (fun _ => ζ) =
      diagHom F (unitaryInvolution K 2 1) (m + 1) (fun _ => ζ) * g)
    (hout : ∀ l : Fin (m + 1), (l.val < k ∨ k + d ≤ l.val) →
      g * diagHom F (unitaryInvolution K 2 1) (m + 1) (Pi.mulSingle l ζ) =
        diagHom F (unitaryInvolution K 2 1) (m + 1) (Pi.mulSingle l ζ) * g) :
    g ∈ (qtwoStdWin (F := F) (K := K) m k d h).range := by
  classical
  obtain ⟨M, hM_apply, hisoM, hdetM, hrow, hcol, hdiag⟩ :=
    pmoc_matrix E hF (fun l : Fin (m + 1) => l.val < k ∨ k + d ≤ l.val) ζ hζ g hg h2 hglob hout
  have huni : conjTr (unitaryInvolution K 2 1) M * M = 1 :=
    conjTr_mul_self_of_isometry (unitaryInvolution K 2 1) hisoM
  let A : Matrix (Fin d) (Fin d) K :=
    Matrix.of fun x y => M (blockIdx k h x) (blockIdx k h y)
  have hMeq : M = blockMat (m + 1) k A := by
    ext a b
    by_cases ha : k ≤ a.val ∧ a.val < k + d
    · by_cases hb : k ≤ b.val ∧ b.val < k + d
      · have ha' : a = blockIdx k h ⟨a.val - k, by omega⟩ :=
          Fin.ext (by simp only [blockIdx_val]; omega)
        have hb' : b = blockIdx k h ⟨b.val - k, by omega⟩ :=
          Fin.ext (by simp only [blockIdx_val]; omega)
        rw [ha', hb', blockMat_apply_blockIdx]
        rfl
      · have hb_out : b.val < k ∨ k + d ≤ b.val := by omega
        have hab : a ≠ b := fun hab => hb (hab ▸ ha)
        rw [blockMat_apply_of_not_mem_right A a hb, hcol b hb_out a hab, Matrix.one_apply,
          if_neg hab]
    · have ha_out : a.val < k ∨ k + d ≤ a.val := by omega
      by_cases hb : k ≤ b.val ∧ b.val < k + d
      · have hab : a ≠ b := fun hab => ha (hab ▸ hb)
        rw [blockMat_apply_of_not_mem_left A ha b, hrow a ha_out b (Ne.symm hab), Matrix.one_apply,
          if_neg hab]
      · by_cases hab : a = b
        · subst hab
          rw [blockMat_apply_of_not_mem_left A ha a, hdiag a ha_out, Matrix.one_apply, if_pos rfl]
        · rw [blockMat_apply_of_not_mem_left A ha b, hrow a ha_out b (Ne.symm hab),
            Matrix.one_apply, if_neg hab]
  have huniA : conjTr (unitaryInvolution K 2 1) A * A = 1 := by
    refine blockMat_injective h ?_
    rw [blockMat_mul h, ← conjTr_blockMat, ← hMeq, huni, blockMat_one]
  have hisoA : ∀ x y : Fin d → K,
      herm (unitaryInvolution K 2 1) (A *ᵥ x) (A *ᵥ y) =
        herm (unitaryInvolution K 2 1) x y := by
    intro x y
    rw [herm_mulVec, huniA, Matrix.one_mulVec]
  have hdetA : A.det = 1 := by
    rw [← det_blockMat h A, ← hMeq]
    exact hdetM
  let A' : Su K 2 1 d := mkSU (unitaryInvolution K 2 1) A hdetA hisoA
  have hA'_mat : (((A' : Su K 2 1 d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = A := rfl
  have hwin_apply : ∀ v : Fin (m + 1) → K,
      qtwoStdWin (F := F) (K := K) m k d h A' v = g v := by
    intro v
    unfold qtwoStdWin
    rw [MonoidHom.comp_apply, suEndN_apply, smul_def, coe_coe_blockEmb, hA'_mat, ← hMeq]
    exact hM_apply v
  refine ⟨A', ?_⟩
  apply LinearEquiv.ext
  intro v
  exact hwin_apply v

theorem qtwoOrth_centr_coordBlockSU (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {n : ℕ} (T : Finset (Fin n))
    (ζ : normOne (unitaryInvolution K 2 1)) (hζ : ζ ≠ 1)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (h2 : ∃ e : ℕ, g ^ (2 ^ e) = 1)
    (hglob : g * diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) =
      diagHom F (unitaryInvolution K 2 1) n (fun _ => ζ) * g)
    (hout : ∀ l ∉ T,
      g * diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) =
        diagHom F (unitaryInvolution K 2 1) n (Pi.mulSingle l ζ) * g) :
    g ∈ (coordBlockSU K 2 1 T).map (suEndN (F := F) (unitaryInvolution K 2 1) n) := by
  classical
  obtain ⟨M, hM_apply, hisoM, hdetM, hrow, hcol, hdiag⟩ :=
    pmoc_matrix E hF (fun l => l ∉ T) ζ hζ g hg h2 hglob hout
  refine ⟨mkSU (unitaryInvolution K 2 1) M hdetM hisoM, ?_, ?_⟩
  · refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1) (J := T)).mpr fun i j hij => ?_
    change M i j = if i = j then 1 else 0
    by_cases hij' : i = j
    · subst hij'
      rw [if_pos rfl]
      exact hdiag i (hij.elim id id)
    · rw [if_neg hij']
      rcases hij with hi | hj
      · exact hrow i hi j (Ne.symm hij')
      · exact hcol j hj i hij'
  · refine LinearEquiv.ext fun v => ?_
    rw [suEndN_apply, mkSU_smul]
    exact hM_apply v

end Centr

end CFSG.StandardType.QTwo

end
