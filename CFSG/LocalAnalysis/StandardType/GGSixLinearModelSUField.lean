module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUModel
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] {G : Type} [Group G] (h : UnitaryFieldData 2 f K) {m : ℕ}
  {φ : ↥(unitarySU 2 f K (m + 1)) →* G}

theorem twistNorm_scalar (c : Kˣ) (σ : K ≃+* K) (k : ℕ) : ∃ c' : Kˣ,
    LinModel.twistNorm (GeneralLinearGroup.scalar (Fin (m + 1)) c) σ k =
      GeneralLinearGroup.scalar (Fin (m + 1)) c' := by
  induction k with
  | zero => exact ⟨1, by rw [LinModel.twistNorm_zero, map_one]⟩
  | succ k ih =>
    obtain ⟨c', hc'⟩ := ih
    refine ⟨c * Units.map (σ : K →* K) c', ?_⟩
    rw [LinModel.twistNorm_succ, hc', LinModel.map_scalar_ringAut, ← map_mul]

variable {h} in
theorem eq_one_of_semiActs_scalar (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) {x : G}
    {c : Kˣ} (hx : SemiActs h φ x (GeneralLinearGroup.scalar (Fin (m + 1)) c) 1) : x = 1 := by
  have h1 := (SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ c⁻¹)
    (semiActs_one_iff.mp hx).2
  rw [Prod.mk_mul_mk, one_mul, ← map_mul, inv_mul_cancel, map_one] at h1
  have h2 := SUTorus.mem_centralizer_of_mem_suPairs_one h1
  rwa [hC, Subgroup.mem_bot] at h2

variable (hn : 3 ≤ m + 1) (hq : ¬(m + 1 = 3 ∧ 2 ^ f = 2))
  (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
  (hC : Subgroup.centralizer (φ.range : Set G) = ⊥)

include hn hq hker hC in
theorem false_of_semiActs_diag_field {p : ℕ} {Bs : Subgroup G}
    (hBs : UnitModel.frameTorus p h φ = Bs)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {σ : K ≃+* K}
    (hσ1 : σ ≠ 1) (hfix : ∀ x : K, x ^ p = 1 → σ x = x) {y : G} (hyp : y ^ p = 1)
    {a : Fin (m + 1) → Kˣ} (hy : SemiActs h φ y (diagHom (m + 1) a) σ) : False := by
  have hyC : y ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, he, hbe⟩ := hb
    have hb' := semiActs_of_frameActs (h := h) hbe
    have hσe : glAut σ (diagHom (m + 1) e) = diagHom (m + 1) e := by
      apply Units.ext
      rw [coe_glAut, coe_diagHom, diagonal_map (map_zero σ)]
      congr 1
      funext i
      exact hfix _ (by rw [← Units.val_pow_eq_pow_val, he i, Units.val_one])
    have e1 := hy.mul hb'
    have e2 := hb'.mul hy
    rw [hσe, mul_one, ← map_mul, mul_comm a e, map_mul] at e1
    rw [glAut_one_apply, one_mul] at e2
    refine SURep.eq_of_act_eqU hC fun s => ?_
    rw [e2.apply s, e1.apply s]
  have hyB := hom y hyC hyp
  rw [← hBs] at hyB
  obtain ⟨d, -, hyd⟩ := hyB
  exact hσ1 (eq_of_semiActs hn hq hker hC hy (semiActs_of_frameActs (h := h) hyd))


end SUModel

namespace SUModel

section Field

variable {G : Type} [Group G] {f e : ℕ} (h : UnitaryFieldData 2 f (GaloisField 2 e)) {m : ℕ}
  {φ : ↥(unitarySU 2 f (GaloisField 2 e) (m + 1)) →* G}
  (hn : 3 ≤ m + 1) (hq : ¬(m + 1 = 3 ∧ 2 ^ f = 2))
  (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 e) (m + 1)))
  (hC : Subgroup.centralizer (φ.range : Set G) = ⊥)

include hn hq hker hC in
theorem exists_semiActs_one_of_mem_normalizer (he : e ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hmp : m + 1 = p) (hpq : p ∣ 2 ^ f + 1) {ω : (GaloisField 2 e)ˣ}
    (hω : IsPrimitiveRoot ω p)
    (hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω))
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {y : G}
    (hy : y ∈ Subgroup.normalizer (φ.range : Set G))
    (hyN : y ∈ Subgroup.normalizer (Bs : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin (m + 1)) (GaloisField 2 e), SemiActs h φ y A 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hζ : IsPrimitiveRoot (ω : GaloisField 2 e) p := IsPrimitiveRoot.coe_units_iff.mpr hω
  have hωp := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one hp.one_lt
  obtain ⟨A, σ, hA⟩ := exists_semiActs h hn hq hker hC hy
  have hAp := hA.pow p
  rw [hyp] at hAp
  have hσp : σ ^ p = 1 := eq_of_semiActs hn hq hker hC hAp (semiActs_one φ)
  rw [hσp] at hAp
  obtain ⟨l₀, hl₀⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker
    (semiActs_one_iff.mp hAp).2
  by_cases hσ1 : σ = 1
  · rw [hσ1] at hA
    exact ⟨A, hA⟩
  exfalso
  have hfix : ∀ x : GaloisField 2 e, x ^ p = 1 → σ x = x := fun x hx =>
    LinModel.fieldAut_fixes_root hp hζ (k := 1) (by rw [pow_one]; exact hσp) hx
  obtain ⟨π, hπ⟩ : ∃ π, LinModel.IsPermOf
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 e)) π := by
    refine LinModel.exists_isPermOf fun i l l' hl hl' =>
      LinModel.eq_of_ne_zero_of_mul_diagGL hω1 (fun l => ?_) hl hl'
    obtain ⟨g, hg⟩ := hreal1 l
    have hgBs : g ∈ Bs := by
      rw [← hBs]
      exact mem_frameTorus_of_mulSingle h hωp hg
    have hb : y⁻¹ * g * y ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) g).mp hgBs
      rwa [inv_inv] at this
    rw [← hBs] at hb
    obtain ⟨d, hd, hbd⟩ := hb
    have e1 := hA.mul (semiActs_of_frameActs (h := h) hbd)
    have e2 := (semiActs_of_frameActs (h := h) hg).mul hA
    rw [glAut_diagHom_eq hp hζ (k := 1) (by rw [pow_one]; exact hσp) hd, mul_one] at e1
    rw [glAut_one_apply, one_mul, show g * y = y * (y⁻¹ * g * y) by group] at e2
    obtain ⟨κ, hκ⟩ := e1.exists_scalar hn hnq hp hpq hker e2
    refine ⟨κ⁻¹, d, ?_⟩
    rw [← LinModel.scalar_mul_diagGL, ← diagHom_eq_diagGL, ← diagHom_eq_diagGL, mul_assoc, hκ,
      ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hπp : π ^ p = 1 := by
    have h1 := LinModel.isPermOf_twistNorm hπ σ p
    rw [hl₀] at h1
    have h2 : LinModel.IsPermOf ((GeneralLinearGroup.scalar (Fin (m + 1)) l₀ :
        GL (Fin (m + 1)) (GaloisField 2 e)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 e)) 1 := by
      have := LinModel.IsPermOf.scalar_mul (A := (1 : GL (Fin (m + 1)) (GaloisField 2 e)))
        (by rw [Units.val_one]; exact LinModel.isPermOf_one) l₀
      rwa [mul_one] at this
    exact h1.unique h2
  by_cases hπ1 : π = 1
  · rw [hπ1] at hπ
    obtain ⟨a, ha⟩ := LinModel.IsPermOf.exists_eq_diagGL hπ
    rw [ha, ← diagHom_eq_diagGL] at hA
    exact false_of_semiActs_diag_field h hn hq hker hC hBs hom hσ1 hfix hyp hA
  have hord : orderOf π = p := orderOf_eq_prime hπp hπ1
  have hcyc : π.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact hp)
    (by rw [Fintype.card_fin, hord, hmp]; omega)
  have hsupp : π.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hord, Fintype.card_fin, hmp]
  have hσl : σ (l₀ : GaloisField 2 e) = l₀ := by
    have h1 := LinModel.twistNorm_succ' A σ p
    rw [LinModel.twistNorm_succ, hσp, LinModel.map_one_ringAut, hl₀, LinModel.map_scalar_ringAut,
      (TypeA.PGLTor.commute_scalar l₀ A).eq] at h1
    have h2 := mul_left_cancel h1
    have h3 := congrArg (fun X : GL (Fin (m + 1)) (GaloisField 2 e) =>
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 e)) 0 0) h2
    simpa [GeneralLinearGroup.coe_scalar] using h3
  obtain ⟨μ, hμ⟩ := LinModel.exists_pow_eq_of_fixed he hp hζ hσp hσ1 hσl
  have hne : ∀ i, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 e)) (π i) i ≠ 0 :=
    fun i => (hπ i (π i)).mpr rfl
  set a : Fin (m + 1) → (GaloisField 2 e)ˣ := fun i => Units.mk0 _ (hne i) with hadef
  have ha : ∀ i, (a i : GaloisField 2 e) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 e)) (π i) i := fun i => rfl
  have hσu : ∀ x : (GaloisField 2 e)ˣ, ∃ c : (GaloisField 2 e)ˣ,
      σ (x : GaloisField 2 e) = x * c ^ p := by
    intro x
    obtain ⟨c, hc⟩ := LinModel.exists_pow_eq_mul_of_fixes he hp.pos hζ (hfix _ hζ.pow_eq_one)
      (x : GaloisField 2 e)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero, mul_zero] at hc
      exact x.ne_zero ((map_eq_zero σ).mp hc)
    exact ⟨Units.mk0 c hc0, by rw [hc]; rfl⟩
  obtain ⟨c, hc⟩ := LinModel.exists_twistNorm_apply_eq hπ hσu a ha p 0
  rw [hπp, Equiv.Perm.one_apply, hl₀, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_eq] at hc
  have hc' : l₀ = (∏ j ∈ Finset.range p, a ((π ^ j) 0)) * c ^ p := Units.ext (by
    rw [hc, Units.val_mul, Units.val_pow_eq_pow_val])
  have hdet : GeneralLinearGroup.det A = ∏ i, a i := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, LinModel.det_eq_prod_of_isPermOf hπ, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (ha i).symm
  have hdetp : GeneralLinearGroup.det A = (μ * c⁻¹) ^ p := by
    calc GeneralLinearGroup.det A = ∏ i, a i := hdet
      _ = ∏ j ∈ Finset.range p, a ((π ^ j) 0) :=
        (LinModel.prod_range_pow_apply_zero hmp hcyc hsupp hπp a).symm
      _ = l₀ * (c ^ p)⁻¹ := by rw [hc', mul_inv_cancel_right]
      _ = (μ * c⁻¹) ^ p := by rw [← hμ, mul_pow, inv_pow]
  set ν := μ * c⁻¹ with hν
  have hνN : ν ^ (2 ^ f + 1) = 1 := SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hdetp.symm
    (UnitModel.det_pow_eq_one_of_mem h hA.1)
  set A' := GeneralLinearGroup.scalar (Fin (m + 1)) ν⁻¹ * A with hA'
  have hA'U : A' ∈ primeFormUnitary h (idGram (GaloisField 2 e) (m + 1)) :=
    (primeFormUnitary h _).mul_mem (scalar_mem_unitary h (by rw [inv_pow, hνN, inv_one])) hA.1
  have hA'det : GeneralLinearGroup.det A' = 1 := by
    have hpm : ∀ u : (GaloisField 2 e)ˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
    rw [hA', map_mul, det_scalar, hpm, hdetp, inv_pow, inv_mul_cancel]
  have hA'SU : A' ∈ unitarySU 2 f (GaloisField 2 e) (m + 1) := by
    rw [mem_unitarySU_iff h]
    refine ⟨by rw [← GeneralLinearGroup.val_det_apply, hA'det, Units.val_one], ?_⟩
    have h1 := mem_primeFormUnitary.mp hA'U
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1
  set s : ↥(unitarySU 2 f (GaloisField 2 e) (m + 1)) := ⟨A', hA'SU⟩ with hs
  have hsA : SemiActs h φ (φ s) A' 1 := semiActs_one_iff.mpr ⟨hA'U, UnitModel.mem_suPairs_coe φ s⟩
  have hsi := hsA.inv
  rw [inv_one, glAut_one_apply] at hsi
  have hy'' := hsi.mul hA
  rw [glAut_one_apply, one_mul] at hy''
  have hA'A : A'⁻¹ * A = GeneralLinearGroup.scalar (Fin (m + 1)) ν := by
    rw [hA', _root_.mul_inv_rev, mul_assoc, ← map_inv, inv_inv,
      (TypeA.PGLTor.commute_scalar ν A).eq, inv_mul_cancel_left]
  rw [hA'A] at hy''
  have hy''p : ((φ s)⁻¹ * y) ^ p = 1 := by
    have h1 := hy''.pow p
    rw [hσp] at h1
    obtain ⟨c', hc'⟩ := twistNorm_scalar ν σ p
    rw [hc'] at h1
    exact eq_one_of_semiActs_scalar hC h1
  have hdiag : GeneralLinearGroup.scalar (Fin (m + 1)) ν = diagHom (m + 1) (fun _ => ν) :=
    Units.ext (by rw [GeneralLinearGroup.coe_scalar, coe_diagHom, scalar_apply])
  rw [hdiag] at hy''
  exact false_of_semiActs_diag_field h hn hq hker hC hBs hom hσ1 hfix hy''p hy''

end Field

section Transfer

variable {G : Type} [Group G] {f n : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)]
  [CharP K 2]

theorem mem_suInducedPairs_of_mem_suPairs (hF : Nat.card K = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f K) {ψ : SU (unitaryInvolution K 2 f) n →* G} {P : GL (Fin n) K}
    (hP : conjTr (unitaryInvolution K 2 f) (P : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = antidiag n)
    {g : G} {B : GL (Fin n) K} (hBU : B ∈ primeFormUnitary h (idGram K n))
    (hB : (g, B) ∈ SUTorus.suPairs (SURep.ggFrameU hF ψ P hP)) :
    (g, P⁻¹ * B * P) ∈ UFusion.suInducedPairs ψ := by
  have hBI : InnerDiagSU.IsIdUnitary (unitaryInvolution K 2 f) B := by
    unfold InnerDiagSU.IsIdUnitary
    rw [SURep.conjTr_eq_bar h]
    have h1 := mem_primeFormUnitary.mp hBU
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1
  have hA := UFusion.isJUnitary_frame hP hBI
  refine ⟨hA, fun u => ?_⟩
  set E := SURep.ggFrameEquiv hF P hP with hE
  have h1 := hB.2 (E u) (E (InnerDiagSU.conjSU _ hA u)) (by
    change P * ((InnerDiagSU.conjSU _ hA u : SU (unitaryInvolution K 2 f) n) : GL (Fin n) K) *
      P⁻¹ = B * (P * (u : GL (Fin n) K) * P⁻¹) * B⁻¹
    rw [InnerDiagSU.coe_conjSU]
    group)
  rwa [SURep.ggFrameU_apply, SURep.ggFrameU_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply] at h1

end Transfer

variable {G : Type} [Group G]

theorem exists_mem_suInducedPairs_of_dvd [Finite G] {p m f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmp : m + 1 = p) (hpq : p ∣ 2 ^ (f + 1) + 1) (hpf : p ∣ f + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum
      (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) {y : G}
    (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))), (y, A) ∈ UFusion.suInducedPairs ψ := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn : 3 ≤ m + 1 := by omega
  have hq : ¬(m + 1 = 3 ∧ 2 ^ (f + 1) = 2) := fun h' => by omega
  have hnq : (m + 1, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : m + 1 = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P, hP, hBsD, -⟩ := UnitModel.exists_frame_of_su hp hp5 hmp hpq hker hC hBsM hBsE hBsI hU
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hφr : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P hP
  have hcent : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hφr]; exact hC
  have hkerφ : SURep.GGFrameKer φ := SURep.ggFrameKer_ggFrameU hF ψ P hP (by omega) hnq hker
  have hkerφ' : φ.ker ≤
      Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1)) :=
    SURep.ker_ggFrameU_le hF ψ P hP hker
  have hBs : UnitModel.frameTorus p h φ = Bs := frameTorus_eq h hn hkerφ hcent hBsD hBsE.2 hom
  obtain ⟨ω, hωo, hωN⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hp hpq
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.iff_orderOf.mpr hωo
  obtain ⟨ζ', hζ', hζ'N⟩ : ∃ ζ' : (GaloisField 2 (2 * (f + 1)))ˣ, ζ' ^ p = ω ∧
      (ζ' : GaloisField 2 (2 * (f + 1))) ^ (2 ^ (f + 1) + 1) = 1 := by
    have hsq := UnitModel.sq_dvd_two_pow_add_one hp hp2 hpf hpq
    have hcardK : p ^ 2 ∣ Nat.card (GaloisField 2 (2 * (f + 1)))ˣ := by
      rw [Nat.card_units, hF]
      refine hsq.trans ⟨2 ^ (f + 1) - 1, ?_⟩
      rw [← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ', hζ'⟩ := LinModel.exists_pow_eq_of_sq_dvd hp hcardK hω.pow_eq_one
    refine ⟨ζ', hζ', ?_⟩
    rw [← Units.val_pow_eq_pow_val, SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hζ' hωN,
      Units.val_one]
  have hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω) := by
    intro l
    obtain ⟨g, hg⟩ := UnitModel.exists_frameActs_of_pow_eq h hmp φ hζ' hζ'N
      (Pi.single l (1 : ZMod p))
    refine ⟨g, ?_⟩
    have e : (fun i => ω ^ ((Pi.single l (1 : ZMod p) : Fin (m + 1) → ZMod p) i).val) =
        Pi.mulSingle l ω := by
      funext i
      by_cases hi : i = l
      · subst hi
        rw [Pi.single_eq_same, Pi.mulSingle_eq_same, ZMod.val_one, pow_one]
      · rw [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, ZMod.val_zero, pow_zero]
    rwa [e] at hg
  obtain ⟨g, hgM, hgN⟩ := LinModel.exists_conj_mem_normalizer hp hBsE hBsM hU hyM hyp
  have hy'M : g⁻¹ * y * g ∈ Subgroup.normalizer (φ.range : Set G) := by
    rw [hφr]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgM) hyM) hgM
  have hy'p : (g⁻¹ * y * g) ^ p = 1 := by
    rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by rw [MulAut.conj_apply, inv_inv], ← map_pow, hyp,
      map_one]
  obtain ⟨A', hA'⟩ := exists_semiActs_one_of_mem_normalizer h hn hq hkerφ' hcent (by omega) hp
    hp2 hmp hpq hω hreal1 hBs hom hy'M hgN hy'p
  have hyM' : y ∈ Subgroup.normalizer (φ.range : Set G) := by rw [hφr]; exact hyM
  have hgM' : g ∈ Subgroup.normalizer (φ.range : Set G) := by rw [hφr]; exact hgM
  obtain ⟨Y, ρ, hY⟩ := exists_semiActs h hn hq hkerφ' hcent hyM'
  obtain ⟨B, τ, hB⟩ := exists_semiActs h hn hq hkerφ' hcent hgM'
  have e1 := hY.mul hB
  have e2 := hB.mul hA'
  rw [mul_one, show g * (g⁻¹ * y * g) = y * g by group] at e2
  have hρ : ρ * τ = 1 * τ := (eq_of_semiActs hn hq hkerφ' hcent e1 e2).trans (one_mul τ).symm
  rw [mul_right_cancel hρ] at hY
  obtain ⟨hYU, hYp⟩ := semiActs_one_iff.mp hY
  exact ⟨_, mem_suInducedPairs_of_mem_suPairs hF h hP hYU hYp⟩

end SUModel

end CFSG.StandardType
