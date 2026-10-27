module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueRootPlaneA
import CFSG.LocalAnalysis.StandardType.GGRootPlaneOm
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.LieType.SteinbergBRSemidirectSLEven
import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace KGPSL

noncomputable abbrev rootInvPSL (m : ℕ) (K : Type) [Field K] [CharP K 2] (hm : 2 ≤ m) :
    projectiveSL (m + 1) K :=
  proj (m + 1) K (AutPSL.rootInv (by omega))

noncomputable abbrev rootInvTransposePSL (m : ℕ) (K : Type) [Field K] [CharP K 2] (hm : 2 ≤ m) :
    projectiveSL (m + 1) K :=
  proj (m + 1) K
    (SpecialLinearGroup.transvection (AutPSL.last_ne_zero (by omega)).symm 1)

noncomputable abbrev leviFullPSL (m : ℕ) (K : Type) [Field K] [CharP K 2] (hm : 2 ≤ m) :
    Subgroup (projectiveSL (m + 1) K) :=
  Subgroup.centralizer {rootInvPSL m K hm} ⊓ Subgroup.centralizer {rootInvTransposePSL m K hm}

theorem conjAut_fixes_of_comm {m : ℕ} {K : Type} [Field K]
    {A : GL (Fin (m + 1)) K} {g : SpecialLinearGroup (Fin (m + 1)) K}
    (h : A * SpecialLinearGroup.toGL g = SpecialLinearGroup.toGL g * A) :
    conjAut (m + 1) K A (proj (m + 1) K g) = proj (m + 1) K g := by
  rw [conjAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, h]
  group

theorem exists_diag_decomp {m : ℕ} {K : Type} [Field K] [CharP K 2] (hm : 2 ≤ m)
    (A : GL (Fin (m + 1)) K) :
    ∃ (s : SpecialLinearGroup (Fin (m + 1)) K) (D : GL (Fin (m + 1)) K),
      A = SpecialLinearGroup.toGL s * D ∧
        D * SpecialLinearGroup.toGL (AutPSL.rootInv (by omega)) =
          SpecialLinearGroup.toGL (AutPSL.rootInv (by omega)) * D ∧
        D * SpecialLinearGroup.toGL
            (SpecialLinearGroup.transvection (AutPSL.last_ne_zero (by omega)).symm 1) =
          SpecialLinearGroup.toGL
            (SpecialLinearGroup.transvection (AutPSL.last_ne_zero (by omega)).symm 1) * D := by
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  set d : K := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  set e' : Fin (m + 1) → K := fun l => if l = i₁ then d else 1 with he'
  have hdetD : (Matrix.diagonal e').det = d := by
    rw [Matrix.det_diagonal]
    simp [e']
  set D : GL (Fin (m + 1)) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e')
    (by rw [hdetD]; exact hd0) with hDdef
  have hDval : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal e' := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hDval,
      hdetD]
  obtain ⟨s, hs⟩ : A * D⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) K →*
      GL (Fin (m + 1)) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  have h0 : e' 0 = 1 := by
    simp only [e', hi₁, ite_eq_right_iff]
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have hlast : e' (Fin.last m) = 1 := by
    simp only [e', hi₁, ite_eq_right_iff]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have hmat1 : (1 + Matrix.single (Fin.last m) 0 (1 : K)) * Matrix.diagonal e' =
      Matrix.diagonal e' * (1 + Matrix.single (Fin.last m) 0 (1 : K)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hlast, h0]
    · simp
  have hmat2 : (1 + Matrix.single 0 (Fin.last m) (1 : K)) * Matrix.diagonal e' =
      Matrix.diagonal e' * (1 + Matrix.single 0 (Fin.last m) (1 : K)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [h0, hlast]
    · simp
  refine ⟨s, D, by rw [hs]; group, ?_, ?_⟩
  · exact (Units.ext hmat1).symm
  · exact (Units.ext hmat2).symm

@[expose]
def KGOTwoPSLCentInput (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hm : 2 ≤ m) : Prop :=
  ∃ Q : Subgroup (projectiveSL (m + 1) K),
    Subgroup.centralizer {rootInvPSL m K hm} = Q ⊔ leviFullPSL m K hm ∧
      leviFullPSL m K hm ≤ Subgroup.normalizer (Q : Set (projectiveSL (m + 1) K)) ∧
      Disjoint Q (leviFullPSL m K hm) ∧
      pCoreOf 2 (Subgroup.centralizer {rootInvPSL m K hm}) = Q

@[expose]
def KGOTwoPSLLeviInput (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m) : Prop :=
  ∀ (c : MulAut (projectiveSL (m + 1) K)), c ∈ AutPSL.compl →
    ∀ A : GL (Fin (m + 1)) K,
      A * SpecialLinearGroup.toGL (AutPSL.rootInv (by omega)) =
          SpecialLinearGroup.toGL (AutPSL.rootInv (by omega)) * A →
      A * SpecialLinearGroup.toGL
            (SpecialLinearGroup.transvection (AutPSL.last_ne_zero (by omega)).symm 1) =
          SpecialLinearGroup.toGL
            (SpecialLinearGroup.transvection (AutPSL.last_ne_zero (by omega)).symm 1) * A →
      ∀ h ∈ leviFullPSL m K (by omega),
        (∀ k ∈ leviFullPSL m K (by omega),
          (conjAut (m + 1) K A * c) k ∈ leviFullPSL m K (by omega) →
            h * (conjAut (m + 1) K A * c) k * h⁻¹ = k) →
        c = 1

theorem pCoreOf_le_range_of_rootInv {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 3 ≤ m) (hbig : 4 ≤ m ∨ 4 ≤ Nat.card K)
    {Q : Subgroup (projectiveSL (m + 1) K)}
    (hCx : Subgroup.centralizer {rootInvPSL m K (by omega)} = Q ⊔ leviFullPSL m K (by omega))
    (hLQ : leviFullPSL m K (by omega) ≤ Subgroup.normalizer (Q : Set (projectiveSL (m + 1) K)))
    (hdisj : Disjoint Q (leviFullPSL m K (by omega)))
    (hQ : pCoreOf 2 (Subgroup.centralizer {rootInvPSL m K (by omega)}) = Q)
    (hlevi : KGOTwoPSLLeviInput m K hm)
    {G : Type} [Group G] {ψ : projectiveSL (m + 1) K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (rootInvPSL m K (by omega))}) ≤ ψ.range := by
  intro a ha
  have haM : a ∈ Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (rootInvPSL m K (by omega))} := GGRootNorm.pCoreOf_le _ ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  set e : projectiveSL (m + 1) K ≃* ψ.range := MonoidHom.ofInjective hψ with he
  set α : MulAut (projectiveSL (m + 1) K) :=
    (MulAut.congr e).symm (ψ.range.normalizerMonoidHom ⟨a, ha_norm⟩) with hαdef
  have hα : ∀ k, a * ψ k * a⁻¹ = ψ (α k) := by
    intro k
    set n : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨a, ha_norm⟩ with hn
    have h1 : (n (e k) : G) = a * ψ k * a⁻¹ := by
      rw [hn, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [← h1]
    have h2 : n (e k) = e (α k) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply (MulAut.congr e) n]
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [h2]
    rfl
  obtain ⟨i, hi, c, hc, hαi⟩ := AutPSL.exists_mul_compl (K := K) (n := m + 1) (by omega) α
  obtain ⟨A, rfl⟩ := hi
  obtain ⟨s, D, hA, hD1, hD2⟩ := exists_diag_decomp (K := K) (m := m) (by omega) A
  set c' : MulAut (projectiveSL (m + 1) K) := conjAut (m + 1) K D * c with hc'
  have hα' : α = conjAut (m + 1) K (SpecialLinearGroup.toGL s) * c' := by
    rw [hαi, hA, hc', map_mul, mul_assoc]
  have hcroot : c' (rootInvPSL m K (by omega)) = rootInvPSL m K (by omega) := by
    show (conjAut (m + 1) K D * c) (proj (m + 1) K (AutPSL.rootInv (by omega))) = _
    rw [MulAut.mul_apply, AutPSL.compl_fixes_rootInv (by omega) hc,
      conjAut_fixes_of_comm hD1]
  have hg : ∀ k : projectiveSL (m + 1) K,
      a * ψ k * a⁻¹ = ψ (proj (m + 1) K s * c'.toMonoidHom k * (proj (m + 1) K s)⁻¹) := by
    intro k
    rw [hα k, hα', MulAut.mul_apply, MulAut.mul_apply, AutPSL.conjAut_toGL]
    rfl
  obtain ⟨h, hhL, hkey⟩ :=
    KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha
      (c := c'.toMonoidHom) hcroot hg
  have hc1 : c = 1 :=
    hlevi c hc D hD1 hD2 h hhL fun k hk hkL => hkey k hk hkL
  have hαI : α ∈ (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) K))) := by
    rw [hαi, hc1, mul_one]
    exact ⟨A, rfl⟩
  have hP2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (rootInvPSL m K (by omega))})) := GGRootNorm.isPGroup_pCoreOf _
  obtain ⟨k, hk⟩ := hP2 ⟨a, ha⟩
  have hak : a ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hαk : α ^ 2 ^ k = 1 := by
    have h1 : (⟨a, ha_norm⟩ : ↥(Subgroup.normalizer (ψ.range : Set G))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hak
    have h2 : (ψ.range.normalizerMonoidHom ⟨a, ha_norm⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow, h1, map_one]
    calc α ^ 2 ^ k = ((MulAut.congr e).symm
            (ψ.range.normalizerMonoidHom ⟨a, ha_norm⟩)) ^ 2 ^ k := by rw [hαdef]
      _ = (MulAut.congr e).symm
            ((ψ.range.normalizerMonoidHom ⟨a, ha_norm⟩) ^ 2 ^ k) := by rw [map_pow]
      _ = 1 := by rw [h2, map_one]
  have hinn : α ∈ (MulAut.conj : projectiveSL (m + 1) K →*
      MulAut (projectiveSL (m + 1) K)).range := by
    set I := (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) K))) with hI
    set H : Subgroup ↥I := (MulAut.conj : projectiveSL (m + 1) K →*
      MulAut (projectiveSL (m + 1) K)).range.subgroupOf I with hH
    have hHn : H.Normal := Subgroup.normal_subgroupOf
    have hodd : Odd H.index := AutPSL.odd_relIndex_inn_inndiag
    set g : ↥I := ⟨α, hαI⟩ with hg
    have hgk : g ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hαk)
    have h1 : orderOf (QuotientGroup.mk' H g) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgk, map_one])
    have h2 : orderOf (QuotientGroup.mk' H g) ∣ H.index := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) H.index := (Nat.coprime_two_left.mpr hodd).pow_left k
    have hdvd : orderOf (QuotientGroup.mk' H g) ∣ (2 ^ k).gcd H.index := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
    have h3 : orderOf (QuotientGroup.mk' H g) = 1 := Nat.dvd_one.mp hdvd
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨g, hg⟩ := hinn
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := g) fun k => by
    rw [hα k, ← hg, MulAut.conj_apply]

end KGPSL

section Tags

theorem ggRootCentOTwoTag_PSL_of
    (hcent : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hm : 2 ≤ m),
      KGPSL.KGOTwoPSLCentInput m K hm)
    (hlevi : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m),
      4 ≤ m ∨ 4 ≤ Nat.card K → KGPSL.KGOTwoPSLLeviInput m K hm) :
    GGRootCentOTwoTag .PSL := by
  intro G _ _ n f ψ hadm hrank hker _ _ hC hBs r hr _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm2 : 2 ≤ m := hrank
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G),
      ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
      Subgroup.centralizer (ψ.range : Set G) = ⊥ →
      (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧
        p ^ 4 ≤ Nat.card Bs ∧ Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧
        ∀ b ∈ Bs,
          GGPsiInnerDiag (CFSG.LieType.Universal.SpecialLinear.rootDatum m
            (GaloisField 2 f)) ψ b) →
      ∀ r : G,
        GGRootInvolution (CFSG.LieType.Universal.SpecialLinear.rootDatum m
          (GaloisField 2 f)) .PSL ψ r →
        pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
          Subgroup.centralizer ({r} : Set G)) ≤ ψ.range := by
    intro ψ hker hC hBs r hr
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · exfalso
      obtain ⟨p, Bs, hp, hp2, hBsE, hcard, hBsN, hBsI⟩ := hBs
      exact AutPSL.pslThreeRankInput_holds G f ψ hf hker hC p Bs hp hp2 hBsE hcard hBsN hBsI
    ·
      have hmain : ∀ (_ : 4 ≤ m ∨ 4 ≤ Nat.card (GaloisField 2 f)),
          pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
            Subgroup.centralizer ({r} : Set G)) ≤ ψ.range := by
        intro hbig
        obtain ⟨Q, hCx, hLQ, hdisj, hQ⟩ := hcent m (GaloisField 2 f) (by omega)
        obtain ⟨w, hw⟩ := AutPSL.exists_conj_rootInv_of_rootInvolution (K := GaloisField 2 f)
          (m := m) (G := G) (ψ := ψ) (r := r) (by omega) hr
        set Θ : projectiveSL (m + 1) (GaloisField 2 f) ≃* ψ.range :=
          AutPSL.projEquiv (K := GaloisField 2 f) (m := m) hker hC with hΘ
        set ψ' : projectiveSL (m + 1) (GaloisField 2 f) →* G :=
          ψ.range.subtype.comp Θ.toMonoidHom with hψ'
        set w' : projectiveSL (m + 1) (GaloisField 2 f) := proj (m + 1) (GaloisField 2 f) w
          with hw'
        set ψ'' : projectiveSL (m + 1) (GaloisField 2 f) →* G :=
          ψ'.comp (MulAut.conj w').toMonoidHom with hψ''
        have hψ'range : ψ'.range = ψ.range := by
          rw [hψ', MonoidHom.range_comp]
          have h : Θ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr Θ.surjective
          rw [h, Subgroup.map_top, Subgroup.range_subtype]
        have hψ''range : ψ''.range = ψ.range := by
          rw [hψ'', MonoidHom.range_comp]
          have h : (MulAut.conj w').toMonoidHom.range = ⊤ :=
            MonoidHom.range_eq_top.mpr (MulAut.conj w').surjective
          rw [h, Subgroup.map_top, hψ'range]
        have hψ'inj : Function.Injective ψ' := by
          intro x y h
          exact Θ.injective (Subtype.ext h)
        have hψ''inj : Function.Injective ψ'' := by
          intro x y h
          have h1 : w' * x * w'⁻¹ = w' * y * w'⁻¹ := hψ'inj (by simpa [hψ''] using h)
          calc x = w'⁻¹ * (w' * x * w'⁻¹) * w' := by group
            _ = w'⁻¹ * (w' * y * w'⁻¹) * w' := by rw [h1]
            _ = y := by group
        have hΘw : (Θ w' : G) = ψ w := by
          rw [hw', hΘ]
          exact AutPSL.projEquiv_proj hker hC w
        have hΘr : (Θ (KGPSL.rootInvPSL m (GaloisField 2 f) (by omega)) : G) =
            ψ (AutPSL.rootInv (by omega)) := by
          rw [hΘ]
          exact AutPSL.projEquiv_proj hker hC (AutPSL.rootInv (by omega))
        have hψ''root : ψ'' (KGPSL.rootInvPSL m (GaloisField 2 f) (by omega)) = r := by
          rw [hψ'']
          show ψ' (w' * KGPSL.rootInvPSL m (GaloisField 2 f) (by omega) * w'⁻¹) = r
          have e1 : ψ' (w' * KGPSL.rootInvPSL m (GaloisField 2 f) (by omega) * w'⁻¹) =
              (Θ w' : G) * (Θ (KGPSL.rootInvPSL m (GaloisField 2 f) (by omega)) : G) *
                (Θ w' : G)⁻¹ := by
            simp only [hψ', MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
            rfl
          rw [e1, hΘw, hΘr, ← hw]
        have hC'' : Subgroup.centralizer (ψ''.range : Set G) = ⊥ := by
          rw [hψ''range]
          exact hC
        have hres := KGPSL.pCoreOf_le_range_of_rootInv (m := m) (K := GaloisField 2 f)
          (by omega) hbig hCx hLQ hdisj hQ (hlevi m (GaloisField 2 f) hm3 hbig)
          hψ''inj hC''
        rwa [hψ''range, hψ''root] at hres
      rcases (show m = 3 ∨ 4 ≤ m by omega) with hm3' | hm4
      · rcases (show f = 1 ∨ 2 ≤ f by omega) with hf1 | hf2
        ·
          subst hf1
          subst hm3'
          exfalso
          obtain ⟨p, Bs, hp, hp2, hBsE, hcard, hBsN, hBsI⟩ := hBs
          have hcenter : Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) =
              ⊥ :=
            CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (m := 3 + 1) (by norm_num)
              (Or.inr (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num))
          have hψinj : Function.Injective ψ := by
            rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
            exact hker.trans hcenter.le
          have hBsψ : Bs ≤ ψ.range := by
            refine bstar_le_range_of_inner hC fun b hb => ?_
            obtain ⟨A, hA⟩ :=
              RootPlaneA.exists_gl_of_psiInnerDiag (m := 3) (by norm_num) hker (hBsI b hb)
            have hdet1 : (A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 1)).det = 1 := by
              have hcardu : Nat.card (Units (GaloisField 2 1)) = 1 := by
                rw [Nat.card_units, GaloisField.card 2 1 (by norm_num)]
                norm_num
              haveI : Subsingleton (Units (GaloisField 2 1)) :=
                (Nat.card_eq_one_iff_unique.mp hcardu).1
              have hdet : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
              rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet]
              rfl
            set s : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1) :=
              ⟨(A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 1)), hdet1⟩ with hs
            have htoGL : SpecialLinearGroup.toGL s = A := by
              rw [hs]
              exact Units.ext rfl
            have hconj : ∀ u : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1),
                ψ (InnerDiagA.conjSL A u) = ψ s * ψ u * (ψ s)⁻¹ := by
              intro u
              rw [show ψ s * ψ u * (ψ s)⁻¹ = ψ (s * u * s⁻¹) by
                simp only [map_mul, map_inv]]
              congr 1
              apply SpecialLinearGroup.toGL_injective
              simp only [RootPlaneA.toGL_conjSL, map_mul, map_inv, htoGL]
            refine ⟨ψ s, ⟨s, rfl⟩, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            obtain ⟨u, rfl⟩ := hy
            have h1 : ψ u = (b * ψ s) * ψ u * (b * ψ s)⁻¹ := by
              calc ψ u = b * (b⁻¹ * ψ u * b) * b⁻¹ := by group
                _ = b * ψ (InnerDiagA.conjSL A u) * b⁻¹ := by rw [hA u]
                _ = b * (ψ s * ψ u * (ψ s)⁻¹) * b⁻¹ := by rw [hconj u]
                _ = (b * ψ s) * ψ u * (b * ψ s)⁻¹ := by group
            calc ψ u * (b * ψ s) = ((b * ψ s) * ψ u * (b * ψ s)⁻¹) * (b * ψ s) := by
                  conv_lhs => rw [h1]
              _ = (b * ψ s) * ψ u := by group
          have hpow : p ^ 4 ∣ Nat.card Bs := by
            have hcardBs :=
              CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (G := G) hp hBsE
            rw [hcardBs]
            refine Nat.pow_dvd_pow p ?_
            have hle : p ^ 4 ≤ p ^ CFSG.Open.pRank p Bs := by rw [← hcardBs]; exact hcard
            exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
          have hBdvd : Nat.card Bs ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hBsψ
          have hUeq : Nat.card ψ.range =
              Nat.card (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) :=
            (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
          have h20160 : Nat.card (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) =
              20160 := by
            rw [← CFSG.Open.StatedAPI.card_statedSL (3 + 1) (GaloisField 2 1)]
            exact CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two
              (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num)
          have hdvd : p ^ 4 ∣ 20160 := by
            rw [← h20160, ← hUeq]
            exact hpow.trans hBdvd
          have hp3 : 3 ≤ p := by have := hp.two_le; omega
          have hle : p ^ 4 ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
          have hp11 : p ≤ 11 := by
            by_contra h
            have h12 : 12 ≤ p := by omega
            have hgt : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h12 4
            norm_num at hgt
            omega
          interval_cases p <;> norm_num at hdvd
        · subst hm3'
          exact hmain (Or.inr (by
            have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
            rw [hK]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2))
      · exact hmain (Or.inl hm4)
  exact key ψ hker hC hBs r hr

end Tags

end CFSG.StandardType

end
