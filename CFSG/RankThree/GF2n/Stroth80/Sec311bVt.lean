module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
import CFSG.RankThree.GF2n.Stroth80.Sec5SL
import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_T_Q_mem_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {x : G} (hxL : x ∈ LB M Q B)
    (hK1 : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z) {a : G} (ha : a ∈ Q) :
    ⁅x, a⁆ ∈ Vt M (LB M Q B) B Z t := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hxH : x ∈ H0 M Z := hc.LB_le_H0 hxL
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, -, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨S, hS⟩ : ∃ S : M₀.E ≃ₗ[GaloisField 2 n] M₀.E, S = φ ⟨x, hxH⟩ := ⟨_, rfl⟩
  have hSπ : ∀ a ∈ Q, M₀.π (x * a * x⁻¹) = S (M₀.π a) := by
    intro a ha'
    rw [hS]
    exact hφπ ⟨x, hxH⟩ a ha'
  have hSQf : ∀ e, M₀.Qf (S e) = M₀.Qf e := by
    intro e
    rw [hS]
    exact hφiso ⟨x, hxH⟩ e
  have hSB : ∀ e f, M₀.B (S e) (S f) = M₀.B e f := by
    intro e f
    have h1 := M₀.Qf_add e f
    have h2 := M₀.Qf_add (S e) (S f)
    have h3 : S (e + f) = S e + S f := map_add S e f
    rw [← h3, hSQf, hSQf, hSQf] at h2
    linear_combination h1 - h2
  have hfix : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), S (M₀.π w) = M₀.π w := by
    intro w hw
    have hwQ : w ∈ Q := hw.1
    have hK : ⁅x, w⁆ ∈ Z := hK1 w hw
    have hcQ : ⁅x, w⁆ ∈ Q := hZQ hK
    have hxw : x * w * x⁻¹ = ⁅x, w⁆ * w := by rw [commutatorElement_def]; group
    calc S (M₀.π w) = M₀.π (x * w * x⁻¹) := (hSπ w hwQ).symm
      _ = M₀.π (⁅x, w⁆ * w) := by rw [hxw]
      _ = M₀.π ⁅x, w⁆ + M₀.π w := M₀.π_mul _ hcQ _ hwQ
      _ = M₀.π w := by rw [(M₀.π_ker _ hcQ).mpr hK, zero_add]
  have hyQ : ⁅x, a⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (hQn x hxM a ha) (Q.inv_mem ha)
  have hA : M₀.π ⁅x, a⁆ = S (M₀.π a) - M₀.π a := by
    have hxa : x * a * x⁻¹ = ⁅x, a⁆ * a := by rw [commutatorElement_def]; group
    rw [← hSπ a ha, hxa, M₀.π_mul _ hyQ _ ha, add_sub_cancel_right]
  obtain ⟨Vsub, hVsub⟩ : ∃ Vsub : Submodule (GaloisField 2 n) M₀.E,
      ∀ e, e ∈ Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    ⟨imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c e he => hc.smul_mem_img_Vt h t c he),
      fun e => mem_imgSub⟩
  have hnd : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := fun u v huv => by rw [Tim79.QuadModel.B_comm, huv, neg_zero]
  have hOO : M₀.B.orthogonal (M₀.B.orthogonal Vsub) = Vsub :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl Vsub
  have hW : ∀ e : M₀.E,
      e ∈ M₀.B.orthogonal Vsub ↔ e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
    intro e
    rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_img_Wt_iff M₀ h.reg hVQ]
    constructor
    · intro h1 v hv
      rw [Tim79.QuadModel.B_comm e v, h1 v ((hVsub v).mpr hv), neg_zero]
    · intro h1 v hv
      rw [Tim79.QuadModel.B_comm v e, h1 v ((hVsub v).mp hv), neg_zero]
  have hPy : M₀.π ⁅x, a⁆ ∈ M₀.B.orthogonal (M₀.B.orthogonal Vsub) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨w, hwW, hwQ, rfl⟩ := (hW n).mp hn
    have e1 : M₀.B (M₀.π w) (S (M₀.π a)) = M₀.B (M₀.π w) (M₀.π a) := by
      rw [← hSB (M₀.π w) (M₀.π a), hfix w hwW]
    rw [hA, map_sub, e1, sub_self]
  rw [hOO] at hPy
  exact (M₀.mem_img_iff hZV hyQ).mp ((hVsub _).mp hPy)

theorem Ctx.T_le_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {x : G} (hxL : x ∈ LB M Q B) (hxR : ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q) :
    x ∈ hc.CN t := by
  have hQN : Q ≤ hc.CN t := fun y hy =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hy, fun v hv => hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  have hxRt : x ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht hxL
  obtain ⟨xR, hxRdef⟩ : ∃ xR : ↥(Rt M (LB M Q B) t), xR = ⟨x, hxRt⟩ := ⟨_, rfl⟩
  have hxRc : (xR : G) = x := by rw [hxRdef]
  have hkerQ : ∀ r : ↥(Rt M (LB M Q B) t), (r : G) ∈ Q → r ∈ φ.ker := by
    intro r hr
    rw [hker, Subgroup.mem_subgroupOf]
    exact hQN hr
  have hcomm : ∀ s : ↥(Rt M (LB M Q B) t), φ s * φ xR = φ xR * φ s := by
    intro s
    have hsx : ((⁅s, xR⁆ : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
      have e : ((⁅s, xR⁆ : ↥(Rt M (LB M Q B) t)) : G) = ⁅(s : G), x⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hxRc]
      rw [e]
      exact hxR (s : G) s.2
    have h1 : φ ⁅s, xR⁆ = 1 := MonoidHom.mem_ker.mp (hkerQ _ hsx)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  obtain ⟨f, hfv⟩ : ∃ f : (ι → K) →+ (ι → K), ∀ v, f v = (φ xR : Matrix ι ι K) *ᵥ v :=
    ⟨AddMonoidHom.mk' (fun v => (φ xR : Matrix ι ι K) *ᵥ v)
      (fun v w => Matrix.mulVec_add _ _ _), fun v => rfl⟩
  have hf : ∀ A ∈ X, ∀ v : ι → K, f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v := by
    intro A hA v
    have hAr : A ∈ φ.range := by rw [hφ]; exact hA
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hAr
    have hm := congrArg Units.val (hcomm s)
    rw [Units.val_mul, Units.val_mul] at hm
    rw [hfv, hfv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
  obtain ⟨c0, hc0⟩ := hX f hf
  have hc0' : ∀ v : ι → K, (φ xR : Matrix ι ι K) *ᵥ v = c0 • v :=
    fun v => (hfv v).symm.trans (hc0 v)
  have hMM : (φ xR : Matrix ι ι K) * (φ xR : Matrix ι ι K) = 1 := by
    have hsq : ((xR * xR : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
      rw [Subgroup.coe_mul, hxRc, ← sq]
      exact hc.sq_mem_Q_of_mem_LB hxL
    have h2 : φ (xR * xR) = 1 := MonoidHom.mem_ker.mp (hkerQ _ hsq)
    rw [map_mul] at h2
    have h3 := congrArg Units.val h2
    rwa [Units.val_mul, Units.val_one] at h3
  have hinv : ∀ v : ι → K, c0 • (c0 • v) = v := by
    intro v
    have h4 : (φ xR : Matrix ι ι K) *ᵥ ((φ xR : Matrix ι ι K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rwa [hc0' v, Matrix.mulVec_smul, hc0' v] at h4
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hc0sq : c0 * c0 = 1 := by
    have h5 := congrFun (hinv (Pi.single i₀ 1)) i₀
    simpa [Pi.single_apply, smul_eq_mul] using h5
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : c0 = 1 := by
    have h6 : (c0 - 1) * (c0 - 1) = 0 := by linear_combination hc0sq - (c0 - 1) * h2K
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h6)
  have hid : ∀ v : ι → K, (φ xR : Matrix ι ι K) *ᵥ v = v := by
    intro v
    rw [hc0' v, hc1, one_smul]
  have hmat : (φ xR : Matrix ι ι K) = 1 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [hid v, Matrix.one_mulVec]
  have hone : φ xR = 1 := Units.ext (by rw [Units.val_one]; exact hmat)
  have hmem : xR ∈ φ.ker := MonoidHom.mem_ker.mpr hone
  rw [hker, Subgroup.mem_subgroupOf, hxRc] at hmem
  exact hmem

end CFSG.RankThree.GF2n.Stroth80
