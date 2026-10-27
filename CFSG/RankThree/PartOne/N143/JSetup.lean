module

public import CFSG.RankThree.PartOne.N143.GroupLemmas
public import CFSG.RankThree.PartOne.KFOUT3.Torus
public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.N143.JGood
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PerfectCover CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFOUT3 (SL3 PSL3 Tor)
open Matrix

section SL

variable {n : ℕ} {K : Type} [Field K]

theorem statedSL_eq_det_ker' : StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det n K

theorem mem_statedSL_iff {g : GL (Fin n) K} :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem statedSL_normal : (StatedSL n K).Normal := by
  rw [statedSL_eq_det_ker']
  exact MonoidHom.normal_ker _

@[expose] noncomputable def conjSL (g : GL (Fin n) K) : ↥(StatedSL n K) ≃* ↥(StatedSL n K) where
  toFun x := ⟨g * x * g⁻¹, (statedSL_normal (n := n) (K := K)).conj_mem x.1 x.2 g⟩
  invFun x := ⟨g⁻¹ * x * g, by
    simpa using (statedSL_normal (n := n) (K := K)).conj_mem x.1 x.2 g⁻¹⟩
  left_inv x := by apply Subtype.ext; simp [mul_assoc]
  right_inv x := by apply Subtype.ext; simp [mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

@[expose] noncomputable def conjSL3 (g : GL (Fin n) K) :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (specialLinearGroupEquivStatedSL n K).trans
    ((conjSL g).trans (specialLinearGroupEquivStatedSL n K).symm)

theorem coe_conjSL3 (g : GL (Fin n) K) (x : Matrix.SpecialLinearGroup (Fin n) K) :
    ((conjSL3 g x : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h := specialLinearGroupEquivStatedSL_coe n K
    ((specialLinearGroupEquivStatedSL n K).symm (conjSL g (specialLinearGroupEquivStatedSL n K x)))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem conjSL3_symm_apply (g : GL (Fin n) K) (x : Matrix.SpecialLinearGroup (Fin n) K) :
    conjSL3 g⁻¹ (conjSL3 g x) = x := by
  apply Subtype.ext
  rw [coe_conjSL3, coe_conjSL3]
  simp [mul_assoc]

theorem conjSL3_apply_symm (g : GL (Fin n) K) (x : Matrix.SpecialLinearGroup (Fin n) K) :
    conjSL3 g (conjSL3 g⁻¹ x) = x := by
  have := conjSL3_symm_apply g⁻¹ x
  simpa using this

end SL

section Cover

theorem card_hopfMultiplier_psl_three
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {f : ℕ} (hf : 3 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) = Nat.gcd 3 (2 ^ f - 1) := by
  have hadm : StatedLieAdmissible .PSL 3 2 f := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have hcl : StatedClassicalModel (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) .PSL 3 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 3 K⟩⟩
  have hm : Models.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) .PSL 3 2 f :=
    ⟨hadm, Or.inl hcl⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSL 3 2 f hm
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := ⟨hcomm⟩
  refine ⟨hperf, ?_⟩
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e.toEquiv]
  have hgen : Blueprint.Multiplier.genericOrders .PSL 3 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 3 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem exists_cover_psl_three
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {f : ℕ} (hf : 3 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    {L : Type} [Group L] [Finite L] (hLp : Group.IsPerfect L)
    (p : L →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center L) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) K →* L, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) ∧
        p.comp ρ =
          QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  obtain ⟨hperf, hcardM⟩ := card_hopfMultiplier_psl_three hGA hf hK
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  set π : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    QuotientGroup.ker_mk' _
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) = Nat.card π.ker := by
    rw [hcardM, hπk, ← LinearFlag.scalars_eq_center, card_scalars (by omega), hK]
  obtain ⟨ρ, hρ, hρs⟩ := exists_hom_of_card_multiplier_eq hperf hSL π hπs hπk.le hcard p hp hpc
  refine ⟨ρ, hρs hLp, fun x hx => ?_, hρ⟩
  have h1 : π x = 1 := by
    rw [← hρ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  rw [← hπk]
  exact h1

end Cover

section Data

variable {G : Type} [Group G] [Finite G]

theorem card_Tor_le' {K : Type} [Field K] [Finite K] {p : ℕ} (hp : 0 < p) :
    Nat.card (Tor p K) ≤ p ^ 2 := by
  have h1 : Function.Injective (fun t : Tor p K =>
      (⟨Matrix.SpecialLinearGroup.toGL (t : SL3 K), t.2⟩ : torusSU p 3 K)) := by
    intro s t hst
    apply Subtype.ext
    exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hst)
  exact (Nat.card_le_card_of_injective _ h1).trans (card_torusSU_le hp 2)

theorem not_dvd_card_ker_of_central {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {H : Type} [Group H] (ρ : SL3 K →* H) (hker : ρ.ker ≤ Subgroup.center (SL3 K)) :
    ¬ p ∣ Nat.card ρ.ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h3 : (x : SL3 K) ^ 3 = 1 := KFOUT3.center_pow_three (hker x.2)
  have h4 : orderOf (x : SL3 K) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h5' : orderOf (x : SL3 K) = p := by rw [Subgroup.orderOf_coe, hx]
  rw [h5'] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem mulEquiv_mem_center {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {z : X}
    (hz : z ∈ Subgroup.center X) : φ z ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h := hz (φ.symm g)
  have := congrArg φ h
  simpa using this

variable {p : ℕ} {A : Subgroup G} {c : G}

theorem JGood.A_le_normalizer {J : Subgroup G} (h : JGood p A c J) :
    A ≤ Subgroup.normalizer (J : Set G) := fun a ha =>
  h.mem_normalizer_of_scalar (Subgroup.le_normalizer ha) ⟨1, fun x hx => by
    rw [pow_one]
    exact mul_inv_eq_iff_eq_mul.2 (Sec12Three.mul_comm_of_mem_A h.hyp ha hx)⟩

theorem JGood.Tof_le_self {J : Subgroup G} (h : JGood p A c J) : Tof A J ≤ J := by
  rw [Tof, Subgroup.commutator_le]
  intro a ha w hw
  have h1 : a * w * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (h.A_le_normalizer ha) w).1 hw.1
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw.1)

theorem JGood.isElementaryAbelian_Tof {J : Subgroup G} (h : JGood p A c J) :
    IsElementaryAbelian p (Tof A J) :=
  Torsion37.isElementaryAbelian_of_forall
    (fun _ hx _ hy => Sec12Three.mul_comm_of_mem_A h.hyp (Tof_le A J hx) (Tof_le A J hy))
    (fun _ hx => Sec12Three.pow_eq_one_of_mem_A h.hyp (Tof_le A J hx))

structure IsPSL3Cover (p : ℕ) (A J : Subgroup G) {K : Type} [Field K] (ρ : SL3 K →* G) : Prop where
  range_eq : ρ.range = J
  ker_central : ρ.ker ≤ Subgroup.center (SL3 K)
  ker_coprime : ¬ p ∣ Nat.card ρ.ker
  map_torus : (Tor p K).map ρ = Tof A J

theorem exists_psl3Data
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Subgroup G} (h : JGood p A c J) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      ∃ ρ : SL3 K →* G, IsPSL3Cover p A J ρ := by
  classical
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  have hp : p.Prime := h.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := Sec12Three.five_le h.hyp
  have hf1 : 1 ≤ f := hadm.2.1
  have hf3 : 3 ≤ f := by
    by_contra hlt
    have hf12 : f = 1 ∨ f = 2 := by omega
    rcases hf12 with rfl | rfl
    · have := Nat.le_of_dvd (by norm_num) hf
      norm_num at this
      omega
    · have := Nat.le_of_dvd (by norm_num) hf
      norm_num at this
      omega
  refine ⟨K, hKf, hKfin, hK, ?_⟩
  have hJperf : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsAt h.hyp.L_mem.2
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥J)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.generic.center_pPrime
  let e' : ↥J ⧸ Subgroup.center ↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  have hq := isCentralPQuot_center e' hcop
  obtain ⟨ρ₀, hρ₀s, hρ₀k, hρ₀sq⟩ :=
    exists_cover_psl_three hGA hf3 hK hJperf _ hq.surjective hq.central
  let ρ₁ : SL3 K →* G := J.subtype.comp ρ₀
  have hρ₁range : ρ₁.range = J := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (ρ₀ s).2
    · intro hx
      obtain ⟨y, hy⟩ := hρ₀s ⟨x, hx⟩
      exact ⟨y, by simp [ρ₁, hy]⟩
  have hρ₁ker : ρ₁.ker ≤ Subgroup.center (SL3 K) := by
    intro s hs
    have hs' : ((ρ₀ s : ↥J) : G) = 1 := hs
    exact hρ₀k (Subtype.ext hs')
  have hTle : Tof A J ≤ J := h.Tof_le_self
  have hTel : IsElementaryAbelian p (Tof A J) := h.isElementaryAbelian_Tof
  have hkerp : ¬ p ∣ Nat.card ρ₀.ker := not_dvd_card_ker_of_central hp hp5 ρ₀ hρ₀k
  have hT'el : IsElementaryAbelian p ((Tof A J).subgroupOf J) := IsElementaryAbelian.subgroupOf hTle
  have hT'card : Nat.card ((Tof A J).subgroupOf J) = p ^ 2 := by
    rw [card_subgroupOf_of_le hTle]
    exact h.card_Tof
  obtain ⟨E₀, hE₀el, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian ρ₀ hp hkerp
    ((Tof A J).subgroupOf J) (by rw [MonoidHom.range_eq_top.2 hρ₀s]; exact le_top) hT'card
  have hpu : (p : ℕ) ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hf
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpu
  have hζ : IsPrimitiveRoot (u : K) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hu)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hE₀pow : ∀ x ∈ E₀, x ^ p = 1 := fun x hx =>
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E₀) ⟨x, hx⟩)
  obtain ⟨g, hg⟩ := exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀
    (fun x hx y hy => Torsion37.mul_comm_of_isElementaryAbelian hE₀el hx hy) hE₀pow
  have hconj : E₀.map (conjSL3 g).toMonoidHom ≤ Tor p K := by
    rintro _ ⟨y, hyE, rfl⟩
    set z : SL3 K := conjSL3 g y with hz
    have hzmat : (z : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := coe_conjSL3 g y
    have hdiag : ((Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := fun i j hij => by
      have : ((Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (z : Matrix (Fin 3) (Fin 3) K) := rfl
      rw [this, hzmat]
      exact hg y hyE i j hij
    obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
    have hzp : z ^ p = 1 := by
      rw [hz, ← map_pow, hE₀pow y hyE, map_one]
    have hzpGL : (Matrix.SpecialLinearGroup.toGL z) ^ p = 1 := by
      rw [← map_pow, hzp, map_one]
    show Matrix.SpecialLinearGroup.toGL z ∈ torusSU p 3 K
    refine mem_torusSU_iff.2 ⟨d, fun i => ?_, ?_, hd⟩
    · have h1 : diagU (d ^ p) = diagU (1 : Fin 3 → Kˣ) := by
        rw [← diagU_pow, hd, diagU_one, hzpGL]
      have h2 : d ^ p = 1 := diagU_injective h1
      have := congrFun h2 i
      simpa using this
    · have hdet : ((Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).det = 1 := z.2
      rw [← hd, det_diagU] at hdet
      apply Units.ext
      simpa using hdet
  have hconjeq : E₀.map (conjSL3 g).toMonoidHom = Tor p K := by
    refine Subgroup.eq_of_le_of_card_ge hconj ?_
    rw [Subgroup.card_map_of_injective (conjSL3 g).injective, hE₀card]
    exact card_Tor_le' hp.pos
  have hTE : (Tor p K).map (conjSL3 g⁻¹).toMonoidHom = E₀ := by
    rw [← hconjeq, Subgroup.map_map]
    have : (conjSL3 g⁻¹).toMonoidHom.comp (conjSL3 g).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x => conjSL3_symm_apply g x
    rw [this, Subgroup.map_id]
  let ρ₂ : SL3 K →* G := ρ₁.comp (conjSL3 g⁻¹).toMonoidHom
  have hρ₂ker : ρ₂.ker ≤ Subgroup.center (SL3 K) := by
    intro s hs
    have h1 : conjSL3 g⁻¹ s ∈ ρ₁.ker := hs
    have := mulEquiv_mem_center (conjSL3 g) (hρ₁ker h1)
    rwa [conjSL3_apply_symm] at this
  refine ⟨ρ₂, ?_, hρ₂ker, not_dvd_card_ker_of_central hp hp5 ρ₂ hρ₂ker, ?_⟩
  · rw [← hρ₁range]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨conjSL3 g s, by
        show ρ₁ (conjSL3 g⁻¹ (conjSL3 g s)) = ρ₁ s
        rw [conjSL3_symm_apply]⟩
  · show (Tor p K).map (ρ₁.comp (conjSL3 g⁻¹).toMonoidHom) = Tof A J
    have hE₀ρ : E₀.map ρ₁ = Tof A J := by
      have : ρ₁ = J.subtype.comp ρ₀ := rfl
      rw [this, ← Subgroup.map_map, hE₀map, Subgroup.map_subgroupOf_eq_of_le hTle]
    rw [← Subgroup.map_map, hTE, hE₀ρ]

end Data

end CFSG.RankThree.PartOne.N143
