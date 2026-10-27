module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenFrame
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenSmall
import CFSG.GH74.GLS.LU.Local.FiveSL3
import CFSG.RankThree.PartTwo.Sec16.KL3SubProofMain
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenRoots

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG Matrix CFSG.RankThree.PartTwo.Sec16.KL3SubProof
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj)

variable {F : Type} [Field F]

theorem frame_expand {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) (v : Fin 3 → F) :
    v = ∑ m, (f m ⬝ᵥ v) • e m := by
  have h1 := congrArg (fun M => M *ᵥ v) (frameMat_mul_frameInv h)
  simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h1
  conv_lhs => rw [← h1]
  ext r
  simp [frameMat, frameInv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

theorem elat_coord_mem [CharP F 2] {D : Subgroup (GL (Fin 3) F)} {K₀ : Subfield F}
    (hν : ∀ z ∈ D, ∀ w ∈ D, ∀ p ℓ b ψ : Fin 3 → F, IsElat z p ℓ → IsElat w b ψ → ℓ ⬝ᵥ b ≠ 0 →
      ψ ⬝ᵥ p ≠ 0 → (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₀)
    {e f : Fin 3 → Fin 3 → F} (hfr : IsFrame e f)
    (hX : ∀ i j, i ≠ j → ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j))
    {z : GL (Fin 3) F} (hz : z ∈ D) {c χ : Fin 3 → F} (hzE : IsElat z c χ) (i j : Fin 3) :
    (f i ⬝ᵥ c) * (χ ⬝ᵥ e j) ∈ K₀ := by
  have hd1 : ∀ m : Fin 3, f m ⬝ᵥ e m = 1 := fun m => by rw [hfr m m, if_pos rfl]
  have hoff : ∀ i j, i ≠ j → (f i ⬝ᵥ c) * (χ ⬝ᵥ e j) ∈ K₀ := by
    intro i j hij
    obtain ⟨g, hg, hgm⟩ := hX j i (Ne.symm hij)
    have hgE := isElat_of_frame hfr (Ne.symm hij) hgm
    by_cases h1 : f i ⬝ᵥ c = 0
    · rw [h1, zero_mul]
      exact K₀.zero_mem
    by_cases h2 : χ ⬝ᵥ e j = 0
    · rw [h2, mul_zero]
      exact K₀.zero_mem
    exact hν g hg z hz (e j) (f i) c χ hgE hzE h1 h2
  have hdiag : ∀ i k, i ≠ k → (f i ⬝ᵥ c) * (χ ⬝ᵥ e i) + (f k ⬝ᵥ c) * (χ ⬝ᵥ e k) ∈ K₀ := by
    intro i k hik
    obtain ⟨g, hg, hgm⟩ := hX k i (Ne.symm hik)
    obtain ⟨x', hx', hx'm⟩ := hX i k hik
    have hgE := isElat_of_frame hfr (Ne.symm hik) hgm
    have hx'E := isElat_of_frame hfr hik hx'm
    have hyE := hx'E.conj g
    have hcen : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ e i = e i + e k := by
      rw [hgm, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec', hd1, one_smul]
    have hax : f k ᵥ* ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = f k + f i := by
      rw [elat_inv_eq hgE, hgm, Matrix.vecMul_add, Matrix.vecMul_one, vecMul_vecMulVec', hd1,
        one_smul]
    rw [hcen, hax] at hyE
    have hy : g * x' * g⁻¹ ∈ D := D.mul_mem (D.mul_mem hg hx') (D.inv_mem hg)
    have key : ((f k + f i) ⬝ᵥ c) * (χ ⬝ᵥ (e i + e k)) ∈ K₀ := by
      by_cases h1 : (f k + f i) ⬝ᵥ c = 0
      · rw [h1, zero_mul]
        exact K₀.zero_mem
      by_cases h2 : χ ⬝ᵥ (e i + e k) = 0
      · rw [h2, mul_zero]
        exact K₀.zero_mem
      exact hν _ hy z hz _ _ c χ hyE hzE h1 h2
    rw [add_dotProduct, dotProduct_add] at key
    have h3 := K₀.sub_mem (K₀.sub_mem key (hoff k i (Ne.symm hik))) (hoff i k hik)
    convert h3 using 1
    ring
  have htr : ∑ m, (f m ⬝ᵥ c) * (χ ⬝ᵥ e m) = 0 := by
    have h0 := hzE.2.2.1
    rw [frame_expand hfr c, dotProduct_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
  rw [Fin.sum_univ_three] at htr
  by_cases hij : i = j
  · subst hij
    fin_cases i
    · have h0 : (f 0 ⬝ᵥ c) * (χ ⬝ᵥ e 0) =
          -((f 1 ⬝ᵥ c) * (χ ⬝ᵥ e 1) + (f 2 ⬝ᵥ c) * (χ ⬝ᵥ e 2)) := by
        linear_combination htr
      simp only [Fin.zero_eta, Fin.isValue]
      rw [h0]
      exact K₀.neg_mem (hdiag 1 2 (by decide))
    · have h0 : (f 1 ⬝ᵥ c) * (χ ⬝ᵥ e 1) =
          -((f 0 ⬝ᵥ c) * (χ ⬝ᵥ e 0) + (f 2 ⬝ᵥ c) * (χ ⬝ᵥ e 2)) := by
        linear_combination htr
      simp only [Fin.mk_one, Fin.isValue]
      rw [h0]
      exact K₀.neg_mem (hdiag 0 2 (by decide))
    · have h0 : (f 2 ⬝ᵥ c) * (χ ⬝ᵥ e 2) =
          -((f 0 ⬝ᵥ c) * (χ ⬝ᵥ e 0) + (f 1 ⬝ᵥ c) * (χ ⬝ᵥ e 1)) := by
        linear_combination htr
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h0]
      exact K₀.neg_mem (hdiag 0 1 (by decide))
  · exact hoff i j hij

@[expose] noncomputable def frameSL {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f)
    (K₀ : Subfield F) : SpecialLinearGroup (Fin 3) K₀ →* GL (Fin 3) F :=
  (MulAut.conj (frameUnit h)).toMonoidHom.comp
    (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map K₀.subtype))

theorem coe_frameSL {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) (K₀ : Subfield F)
    (M : SpecialLinearGroup (Fin 3) K₀) :
    (frameSL h K₀ M : Matrix (Fin 3) (Fin 3) F) =
      frameMat e * K₀.subtype.mapMatrix (M : Matrix (Fin 3) (Fin 3) K₀) * frameInv f := rfl

theorem frameSL_injective {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) (K₀ : Subfield F) :
    Function.Injective (frameSL h K₀) := by
  intro M N hMN
  have h1 := congrArg (fun g : GL (Fin 3) F => frameInv f * (g : Matrix (Fin 3) (Fin 3) F) *
    frameMat e) hMN
  simp only [coe_frameSL] at h1
  have hCB := frameInv_mul_frameMat h
  have e1 : ∀ X : Matrix (Fin 3) (Fin 3) F,
      frameInv f * (frameMat e * X * frameInv f) * frameMat e = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCB, Matrix.one_mul, Matrix.mul_assoc, hCB,
      Matrix.mul_one]
  rw [e1, e1] at h1
  ext i j
  have := congrFun (congrFun h1 i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Subfield.coe_subtype] at this
  exact this

theorem coe_frameSL_transvection {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) (K₀ : Subfield F)
    {i j : Fin 3} (hij : i ≠ j) (a : K₀) :
    (frameSL h K₀ (SpecialLinearGroup.transvection hij a) : Matrix (Fin 3) (Fin 3) F) =
      1 + (a : F) • vecMulVec (e i) (f j) := by
  rw [coe_frameSL, SpecialLinearGroup.transvection_coe, RingHom.map_add, RingHom.map_one,
    RingHom.mapMatrix_apply, Matrix.map_single, Subfield.coe_subtype, frame_conj_transvection h]

theorem frameSL_mem {D : Subgroup (GL (Fin 3) F)} {K₀ : Subfield F}
    {e f : Fin 3 → Fin 3 → F} (hfr : IsFrame e f)
    (hX : ∀ i j, i ≠ j → ∀ a ∈ K₀,
      ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + a • vecMulVec (e i) (f j))
    (M : SpecialLinearGroup (Fin 3) K₀) : frameSL hfr K₀ M ∈ D := by
  have htr : ∀ (i j : Fin 3) (hij : i ≠ j) (a : K₀),
      frameSL hfr K₀ (SpecialLinearGroup.transvection hij a) ∈ D := by
    intro i j hij a
    obtain ⟨g, hg, hgm⟩ := hX i j hij a a.2
    have : frameSL hfr K₀ (SpecialLinearGroup.transvection hij a) = g :=
      Units.ext (by rw [coe_frameSL_transvection, hgm])
    rw [this]
    exact hg
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun M => frameSL hfr K₀ M ∈ D) M
    ?_ htr ?_
  · intro i j hij c hc
    show frameSL hfr K₀ (SpecialLinearGroup.diag2n hij c hc) ∈ D
    rw [CFSG.GH74.GLS.LU.Local.Five.diag2n_eq_diag2nWord hij c hc]
    simp only [CFSG.GH74.GLS.LU.Local.Five.diag2nWord, map_mul]
    exact D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem (htr _ _ _ _) (htr _ _ _ _))
      (htr _ _ _ _)) (htr _ _ _ _)) (htr _ _ _ _)) (htr _ _ _ _)
  · intro A B hA hB
    rw [map_mul]
    exact D.mul_mem hA hB

theorem mem_range_frameSL {K₀ : Subfield F} {e f : Fin 3 → Fin 3 → F} (hfr : IsFrame e f)
    {z : GL (Fin 3) F} {c χ : Fin 3 → F} (hzE : IsElat z c χ)
    (hco : ∀ i j, (f i ⬝ᵥ c) * (χ ⬝ᵥ e j) ∈ K₀) : z ∈ (frameSL hfr K₀).range := by
  set N := frameInv f * (z : Matrix (Fin 3) (Fin 3) F) * frameMat e with hNdef
  have hCB := frameInv_mul_frameMat hfr
  have hBC := frameMat_mul_frameInv hfr
  have hNij : ∀ i j, N i j = (if i = j then 1 else 0) + (f i ⬝ᵥ c) * (χ ⬝ᵥ e j) := by
    intro i j
    rw [hNdef, hzE.2.2.2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCB, mul_vecMulVec,
      vecMulVec_mul]
    simp only [Matrix.add_apply, Matrix.one_apply, vecMulVec_apply]
    congr 1
  have hNmem : ∀ i j, N i j ∈ K₀ := by
    intro i j
    rw [hNij]
    refine K₀.add_mem ?_ (hco i j)
    split_ifs
    · exact K₀.one_mem
    · exact K₀.zero_mem
  set M₀ : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨N i j, hNmem i j⟩ with hM₀
  have hmap : K₀.subtype.mapMatrix M₀ = N := by
    ext i j
    rfl
  have hdetN : N.det = 1 := by
    rw [hNdef, Matrix.det_mul, Matrix.det_mul, hzE.det_eq_one, mul_one, ← Matrix.det_mul, hCB,
      Matrix.det_one]
  have hdet : M₀.det = 1 := by
    apply Subtype.ext
    have := RingHom.map_det K₀.subtype M₀
    rw [hmap, hdetN] at this
    simpa using this
  set M : SpecialLinearGroup (Fin 3) K₀ := ⟨M₀, hdet⟩ with hMdef
  have hMc : (M : Matrix (Fin 3) (Fin 3) K₀) = M₀ := rfl
  refine ⟨M, Units.ext ?_⟩
  rw [coe_frameSL, hMc, hmap, hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBC, Matrix.one_mul,
    Matrix.mul_assoc, hBC, Matrix.mul_one]

theorem normal_le_center_or_eq_top_of_quasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ Subgroup.center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q), MonoidHom.mem_ker, map_mul, map_inv, ← hπ,
        hnq, inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = n₁ * (n₁⁻¹ * x) := by group
    have hy : y = n₂ * (n₂⁻¹ * y) := by group
    set z₁ := n₁⁻¹ * x
    set z₂ := n₂⁻¹ * y
    have c₁ := Subgroup.mem_center_iff.mp hz₁
    have c₂ := Subgroup.mem_center_iff.mp hz₂
    rw [hx, hy, commutatorElement_def]
    have e : n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by
            rw [← c₁ (n₂ * z₂), mul_assoc _ z₁, mul_inv_cancel, mul_one]
        _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
        _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [← c₂ n₁⁻¹]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

theorem normalClosure_eq_top_of_elat [CharP F 2] {D : Subgroup (GL (Fin 3) F)}
    (hDq : IsQuasisimple D) (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1) {x : GL (Fin 3) F}
    (hx : x ∈ D) {a φ : Fin 3 → F} (hxE : IsElat x a φ) :
    Subgroup.normalClosure {(⟨x, hx⟩ : D)} = ⊤ := by
  have hxN : (⟨x, hx⟩ : D) ∈ Subgroup.normalClosure {(⟨x, hx⟩ : D)} :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  rcases normal_le_center_or_eq_top_of_quasisimple hDq
    (Subgroup.normalClosure {(⟨x, hx⟩ : D)}) with h | h
  · exfalso
    have h3 := hZ3 _ (h hxN)
    have h2 : (⟨x, hx⟩ : D) ^ 2 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hxE.mul_self)
    have h1 : (⟨x, hx⟩ : D) = 1 := by
      calc (⟨x, hx⟩ : D) = (⟨x, hx⟩ : D) ^ 3 * ((⟨x, hx⟩ : D) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, mul_one]
    exact hxE.ne_one (congrArg Subtype.val h1)
  · exact h

theorem frame_of_special [Finite F] [CharP F 2] {D : Subgroup (GL (Fin 3) F)}
    (hirr : SubgroupLists.IsIrreducibleOn D) {K₀ : Subfield F}
    (hR : ∀ z ∈ D, ∀ p ℓ : Fin 3 → F, IsElat z p ℓ → rootSet D p ℓ = K₀)
    (hν : ∀ z ∈ D, ∀ w ∈ D, ∀ p ℓ b ψ : Fin 3 → F, IsElat z p ℓ → IsElat w b ψ → ℓ ⬝ᵥ b ≠ 0 →
      ψ ⬝ᵥ p ≠ 0 → (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₀)
    {s t : GL (Fin 3) F} (hs : s ∈ D) (ht : t ∈ D) {a φ b ψ : Fin 3 → F}
    (hsE : IsElat s a φ) (htE : IsElat t b ψ) (hφb : φ ⬝ᵥ b = 0) (hψa : ψ ⬝ᵥ a ≠ 0) :
    ∃ e f : Fin 3 → Fin 3 → F, IsFrame e f ∧
      ∀ i j, i ≠ j → ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j) := by
  have hirr' : CFSG.RankThree.PartTwo.Sec16.KSL3TwoIrrProof.IsIrr D := fun W hW => hirr W hW
  set ν' := ψ ⬝ᵥ a with hν'
  have hr : s * t * (s * t) ∈ D := D.mul_mem (D.mul_mem hs ht) (D.mul_mem hs ht)
  have hrE : IsElat (s * t * (s * t)) (ν' • b) φ := by
    refine ⟨smul_ne_zero hψa htE.1, hsE.2.1, by rw [dotProduct_smul, hφb, smul_zero], ?_⟩
    simp only [Units.val_mul]
    rw [hsE.2.2.2, htE.2.2.2, sq_mul_of_dotProduct_eq_zero hsE.2.2.1 htE.2.2.1 hφb,
      smul_vecMulVec, vecMulVec_smul]
  have htE' : IsElat t (ν' • b) (ν'⁻¹ • ψ) := by
    refine ⟨smul_ne_zero hψa htE.1, smul_ne_zero (inv_ne_zero hψa) htE.2.1, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, htE.2.2.1, smul_zero, smul_zero]
    · rw [htE.2.2.2, smul_vecMulVec, vecMulVec_smul, smul_smul, mul_inv_cancel₀ hψa, one_smul]
  obtain ⟨u, hu, b₁, ψ₁, huE, hφb₁, hψ₁a⟩ := exists_genPos hirr' hr hrE
  refine exists_frame hR hν hr hu hs ht hrE huE hsE htE' hφb₁ hψ₁a ?_
  rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hψa]
  exact one_ne_zero

theorem evenSL3IrredLarge : EvenSL3IrredLarge := by
  intro F _ _ e he hF hq D hdet hDq hZ3 hirr hcomm hprim hnd hlarge
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  right
  obtain ⟨x, hx, y, hy, a, φ, c, hxE, hyE, hxy⟩ := hlarge
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hxy
    apply Units.ext
    rw [hxE.2.2.2, hyE.2.2.2, one_smul]
  have hc0 : c ≠ 0 := by
    intro h
    apply hyE.2.1
    rw [h, zero_smul]
  have hcR : c ∈ rootSet D a φ := ⟨y, hy, by rw [hyE.2.2.2, vecMulVec_smul]⟩
  obtain ⟨K₀, -, hR, hν⟩ := root_structure hirr hx hxE
    (normalClosure_eq_top_of_elat hDq hZ3 hx hxE) hc0 hc1 hcR
  obtain ⟨s, t, hs2, ht2, hst, hev⟩ := hnd
  have hss : (s : GL (Fin 3) F) * s = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, hs2, Subgroup.coe_one]
  have htt : (t : GL (Fin 3) F) * t = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, ht2, Subgroup.coe_one]
  have hs1 : (s : GL (Fin 3) F) ≠ 1 := by
    intro h
    apply hst
    rw [show s = 1 from Subtype.ext h, one_mul, mul_one]
  have ht1 : (t : GL (Fin 3) F) ≠ 1 := by
    intro h
    apply hst
    rw [show t = 1 from Subtype.ext h, one_mul, mul_one]
  obtain ⟨a₁, φ₁, hsE⟩ := exists_isElat_of_mul_self hss hs1
  obtain ⟨b₁, ψ₁, htE⟩ := exists_isElat_of_mul_self htt ht1
  have hstGL : (s : GL (Fin 3) F) * t ≠ t * s := fun h => hst (Subtype.ext (by simpa using h))
  have hevGL : Even (orderOf ((s : GL (Fin 3) F) * t)) := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    exact hev
  have hss' : s * s = 1 := by rw [← pow_two]; exact hs2
  have htt' : t * t = 1 := by rw [← pow_two]; exact ht2
  have hcomm2 : ∀ u v : D, u * u = 1 → v * v = 1 → u * v * (u * v) = 1 → u * v = v * u := by
    intro u v hu hv h
    calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
      _ = v⁻¹ * u⁻¹ := _root_.mul_inv_rev _ _
      _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]
  have hframe : ∃ e f : Fin 3 → Fin 3 → F, IsFrame e f ∧
      ∀ i j, i ≠ j → ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j) := by
    rcases special_of_even hsE htE hstGL hevGL with h | h
    · have hψa : ψ₁ ⬝ᵥ a₁ ≠ 0 := by
        intro h'
        apply hst
        refine hcomm2 s t hss' htt' (Subtype.ext ?_)
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, hsE.2.2.2, htE.2.2.2,
          sq_mul_of_dotProduct_eq_zero hsE.2.2.1 htE.2.2.1 h, h', zero_smul, vecMulVec_zero,
          add_zero]
      exact frame_of_special hirr hR hν s.2 t.2 hsE htE h hψa
    · have hφb : φ₁ ⬝ᵥ b₁ ≠ 0 := by
        intro h'
        apply hst
        refine (hcomm2 t s htt' hss' (Subtype.ext ?_)).symm
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, hsE.2.2.2, htE.2.2.2,
          sq_mul_of_dotProduct_eq_zero htE.2.2.1 hsE.2.2.1 h, h', zero_smul, vecMulVec_zero,
          add_zero]
      exact frame_of_special hirr hR hν t.2 s.2 htE hsE h hφb
  obtain ⟨e', f', hfr, hX⟩ := hframe
  have hX' : ∀ i j, i ≠ j → ∀ a ∈ K₀,
      ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + a • vecMulVec (e' i) (f' j) := by
    intro i j hij a ha
    obtain ⟨g, hg, hgm⟩ := hX i j hij
    have : a ∈ rootSet D (e' i) (f' j) := by
      rw [hR g hg _ _ (isElat_of_frame hfr hij hgm)]
      exact ha
    exact this
  have hle1 : (frameSL hfr K₀).range ≤ D := by
    rintro _ ⟨M, rfl⟩
    exact frameSL_mem hfr hX' M
  have hle2 : D ≤ (frameSL hfr K₀).range := by
    intro g hg
    have hgN : (⟨g, hg⟩ : D) ∈ Subgroup.normalClosure {(⟨s, s.2⟩ : D)} := by
      rw [normalClosure_eq_top_of_elat hDq hZ3 s.2 hsE]
      exact Subgroup.mem_top _
    have hle : Subgroup.normalClosure {(⟨s, s.2⟩ : D)} ≤ (frameSL hfr K₀).range.subgroupOf D := by
      change Subgroup.closure (Group.conjugatesOfSet {(⟨s, s.2⟩ : D)}) ≤ _
      rw [Subgroup.closure_le]
      intro w hw
      obtain ⟨b', hb', hw'⟩ := Group.mem_conjugatesOfSet_iff.mp hw
      rw [Set.mem_singleton_iff] at hb'
      subst hb'
      obtain ⟨d, rfl⟩ := isConj_iff.mp hw'
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hdE := hsE.conj d
      have hdD : (d : GL (Fin 3) F) * s * (d : GL (Fin 3) F)⁻¹ ∈ D :=
        D.mul_mem (D.mul_mem d.2 s.2) (D.inv_mem d.2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mem_range_frameSL hfr hdE (elat_coord_mem hν hfr hX hdD hdE)
    exact hle hgN
  have hDeq : D = (frameSL hfr K₀).range := le_antisymm hle2 hle1
  set eD : D ≃* SpecialLinearGroup (Fin 3) K₀ :=
    (MulEquiv.subgroupCongr hDeq).trans (MonoidHom.ofInjective (frameSL_injective hfr K₀)).symm
  have eQ : D ⧸ Subgroup.center D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K₀ :=
    QuotientGroup.congr _ _ eD (Subgroup.map_center_eq eD)
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ 2 := charP_of_injective_algebraMap' K₀ 2
  obtain ⟨m, hm1, hK₀⟩ := CFSG.RankThree.PartOne.CTP.exists_card_eq_two_pow K₀
  have hme : m ∣ e := by
    have h1 := Module.card_eq_pow_finrank (K := K₀) (V := F)
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, hK₀, ← pow_mul] at h1
    exact ⟨_, Nat.pow_right_injective (le_refl 2) h1⟩
  refine ⟨m, hm1, hme, Or.inl ?_⟩
  exact CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    ⟨⟨Nat.prime_two, hm1, by norm_num, by simp, by simp⟩, K₀, inferInstance, inferInstance, hK₀,
      ⟨eQ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K₀)⟩⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
