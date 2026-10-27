module

public import CFSG.RankThree.GF2n.Stroth80.Sec118I4Spin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118CMSp
public import CFSG.LieType.Sp6Spin.Sp6
import CFSG.RankThree.GF2n.Stroth80.Sec118I4Fix

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.LieType.Universal.Symplectic TauCeti.GLSymplecticFin
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open CFSG.LieType.Sp6Spin CFSG.LieType.D4Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem isShortIndex_imp {n : ℕ} (r : RootSubgroupIndex n) (hr : IsShortIndex r) :
    (∀ i, r ≠ .positiveLong i) ∧ (∀ i, r ≠ .negativeLong i) := by
  cases r <;> simp [IsShortIndex] at hr ⊢

section Certificates


theorem Ctx.false_of_spinCase
    (hU : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
        ∀ (V : Type) [AddCommGroup V] [Module K V], Module.finrank K V = 8 →
        ∀ (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
        ∀ (ψ : StatedSp 3 K →* (V ≃ₗ[K] V)), (∀ g v, Q (ψ g v) = Q v) →
        (∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
        (∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K, c ≠ 0 →
          IsLongRootElement Q (ψ (SpExtras.elt r c))) →
        ∃ e : V ≃ₗ[K] (Fin (2 * 4) → K), (∀ v, coordinateQuadPlus 4 K (e v) = Q v) ∧
          (∀ g, ∃ M ∈ spinSeven K, ∀ v,
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v =
              e (ψ g v)) ∧
          ∀ M ∈ spinSeven K, ∃ g, ∀ v,
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = e (ψ g v))
    (hG : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (s : ℕ)
        (QC : QuadraticForm K (Fin (2 * s) → K)) (b : Fin (2 * 4) → K),
        b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
        ∀ (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
          (A : Subgroup (GL (Fin (2 * 4)) K)),
          A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype →
          (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b) →
          (∀ t : K, (t • b, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0) →
          (∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 b = 0) →
          (∀ M ∈ spinSeven K, Odd (orderOf M) →
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b →
            (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
              w.2) ∈ W) ∧
            ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A) →
          (∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x b = 0 →
            ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
            (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • b) →
          (∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
            ∃ t : K, w = (t • b, 0)) →
          Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s) → False)
    (hN : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
        ∀ g : GL (Fin (2 * 4)) K,
          (∀ v : Fin (2 * 4) → K,
            coordinateQuadPlus 4 K ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
              coordinateQuadPlus 4 K v) →
          (∀ M ∈ spinSeven K,
            g * (M : GL (Fin (2 * 4)) K) * g⁻¹ ∈
              (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype) →
          g ∈ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype)
    (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp 3 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B 3 x a h) (hq : 2 ^ x = Nat.card Z) : False := by
  classical
  have ha2 : ∃ a' ∈ LB M Q B, IsA2 Q Z a' := ⟨(a : G), h.1, h.2⟩
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hK : Nat.card K = 2 ^ x := hD.card.trans hq.symm
  obtain ⟨-, hq4, h8, hpol, Θ, ψ, hΘ, hΘk, hψΘ, hψQ, hirr, hsieg⟩ :=
    hc.exists_spin_input hLm ha2 hnT hD hK φ hφπ hφk hφQ
  obtain ⟨e, heQ, hef, heb⟩ := hU K hq4 ↥(cmComm M Q Z B K γ M₀ φ) h8 (cmCommQf B φ) hpol ψ hψQ
    hirr (fun r hr c hc0 => hsieg r (isShortIndex_imp r hr).1 (isShortIndex_imp r hr).2 c hc0)
  have hSC : IsCompl (cmComm M Q Z B K γ M₀ φ) (M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) :=
    hc.isCompl_cmComm_orthogonal hD φ hφπ
  have hK1 : 1 < Nat.card K := by
    have := hc.hyp.q4
    rw [hD.card]
    omega
  have hE : Module.finrank K M₀.E = 2 * n := hD.finrank_E hw hK1
  have hdim := Submodule.finrank_add_eq_of_isCompl hSC
  have hdimC : Module.finrank K ↥(M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) = 2 * (n - 4) := by
    rw [h8, hE] at hdim
    omega
  have hn4 : 4 ≤ n := by
    rw [h8, hE] at hdim
    omega
  set s := n - 4 with hs
  let c : ↥(M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) ≃ₗ[K] (Fin (2 * s) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hdimC, Module.finrank_fin_fun])
  obtain ⟨b₀, hb0, hb0s, hB, hperp, -⟩ := hc.dictB hD
  have hb₀S : b₀ ∈ cmComm M Q Z B K γ M₀ φ :=
    hc.mem_cmComm_of_mem_img_B hD φ hφπ ha2 hB
  let b : Fin (2 * 4) → K := e ⟨b₀, hb₀S⟩
  let V : AddSubgroup M₀.E := M₀.img (Q ⊓ QB B)
  let Ψ := complProdEquiv hSC e c
  let W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)) :=
    V.map (Ψ : M₀.E →ₗ[K] ((Fin (2 * 4) → K) × (Fin (2 * s) → K))).toAddMonoidHom
  let LBH : Subgroup ↥(H0 M Z) := (LB M Q B).subgroupOf (H0 M Z)
  let A : Subgroup (GL (Fin (2 * 4)) K) := ((cmCommGL hc hD φ hφπ e).comp LBH.subtype).range
  let QC : QuadraticForm K (Fin (2 * s) → K) :=
    M₀.toQuadraticForm.comp (((M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)).subtype).comp
      c.symm.toLinearMap)
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hSQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hsing : ∀ v ∈ V, M₀.Qf v = 0 := (M₀.isElemAbelian_iff hD.reg hSQ).mp hc.inf_QB_elemAbelian
  have hVperp : ∀ v ∈ V, M₀.B v b₀ = 0 := fun v hv => hc.img_inf_QB_orthogonal hperp hv
  have hBV : ∀ t : K, t • b₀ ∈ V := fun t =>
    M₀.img_mono (le_inf hc.le (Ctx.B_le_QB hc)) ((hB _).mpr ⟨t, rfl⟩)
  have hΨadd : ∀ {x y : M₀.E} (hx : x ∈ cmComm M Q Z B K γ M₀ φ)
      (hy : y ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)),
      Ψ (x + y) = (e ⟨x, hx⟩, c ⟨y, hy⟩) := fun hx hy => complProdEquiv_add hSC e c hx hy
  have hΨS : ∀ {x : M₀.E} (hx : x ∈ cmComm M Q Z B K γ M₀ φ), Ψ x = (e ⟨x, hx⟩, 0) := by
    intro x hx
    have h1 := hΨadd hx (Submodule.zero_mem _)
    rw [add_zero] at h1
    rw [h1]
    exact Prod.ext rfl (map_zero c)
  have hΨmem : ∀ w ∈ W, ∃ v ∈ V, Ψ v = w := fun w hw => AddSubgroup.mem_map.mp hw
  have hLBC : ∀ ℓ : ↥(H0 M Z), (ℓ : G) ∈ LB M Q B →
      ∀ z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ), φ ℓ z = z := fun ℓ hℓ z hz =>
    hc.action_fixes_orthogonal hD φ hφπ ha2 hℓ ℓ.2 hz
  have hflag : ∀ ℓ : ↥(H0 M Z), (ℓ : G) ∈ LB M Q B →
      φ ℓ b₀ = b₀ ∧ ∀ v ∈ V, ∃ t : K, φ ℓ v - v = t • b₀ := fun ℓ hℓ =>
    hc.LB_act_fix_line hD hB hℓ (T := ((φ ℓ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
      (fun y hy => hφπ ℓ y hy)
  have hXS1 := hc.cmCommGL_XbarH_mem_spinSevenGL hD φ hφπ e ψ Θ hψΘ hef
  have hXS2 : ∀ M' ∈ spinSeven K, ∃ s : ↥(XbarH M Q Z B),
      cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) = (M' : GL (Fin (2 * 4)) K) := fun M' hM' =>
    hc.exists_XbarH_cmCommGL_eq hD φ hφπ e ψ Θ hΘ hψΘ heb M' hM'
  have hiso := cmCommGL_isometry hc hD φ hφπ hφQ e heQ
  have hbS : ∀ ℓ : ↥(H0 M Z), (ℓ : G) ∈ LB M Q B →
      ((cmCommGL hc hD φ hφπ e ℓ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b
        = b := by
    intro ℓ hℓ
    show _ *ᵥ e ⟨b₀, hb₀S⟩ = e ⟨b₀, hb₀S⟩
    rw [cmCommGL_mulVec]
    congr 1
    exact Subtype.ext (hflag ℓ hℓ).1
  have hsymm : ∀ u v : M₀.E, M₀.B u v = M₀.B v u := fun u v => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  refine hG K hq4 s QC b ?_ ?_ W A ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h0
    apply hb0
    have := e.injective (h0.trans (map_zero e).symm)
    exact congrArg Subtype.val this
  · rw [heQ]
    exact hb0s
  · rintro _ ⟨ℓ, rfl⟩
    exact hc.cmCommGL_mem_spinSevenGL hD φ hφπ e hXS1 hXS2 hiso (hN K hq4) ℓ.1
  · rintro _ ⟨ℓ, rfl⟩
    exact hbS ℓ.1 (Subgroup.mem_subgroupOf.mp ℓ.2)
  · intro t
    refine AddSubgroup.mem_map.mpr ⟨t • b₀, hBV t, ?_⟩
    show Ψ (t • b₀) = _
    have hb' : t • b₀ ∈ cmComm M Q Z B K γ M₀ φ := Submodule.smul_mem _ t hb₀S
    rw [hΨS hb']
    show (e ⟨t • b₀, hb'⟩, (0 : Fin (2 * s) → K)) = (t • e ⟨b₀, hb₀S⟩, 0)
    congr 1
    rw [← map_smul]
    rfl
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hΨmem w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mem_add_eq_of_isCompl hSC v
    rw [hΨadd hx hy]
    show coordinateQuadPlus 4 K (e ⟨x, hx⟩) + QC (c ⟨y, hy⟩) = 0
    have hQCy : QC (c ⟨y, hy⟩) = M₀.Qf y := by
      show M₀.Qf (((c.symm (c ⟨y, hy⟩) :
        ↥(M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ))) : M₀.E)) = M₀.Qf y
      rw [LinearEquiv.symm_apply_apply]
    rw [heQ, hQCy, cmCommQf_apply]
    have hxy : M₀.B x y = 0 := hy x hx
    have h1 := M₀.Qf_add x y
    rw [hxy, add_zero] at h1
    show M₀.Qf x + M₀.Qf y = 0
    rw [← h1]
    exact hsing _ hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hΨmem w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mem_add_eq_of_isCompl hSC v
    rw [hΨadd hx hy]
    show polar (coordinateQuadPlus 4 K) (e ⟨x, hx⟩) (e ⟨b₀, hb₀S⟩) = 0
    rw [polar_coordinateQuadPlus_e φ e heQ]
    show M₀.B x b₀ = 0
    have h1 := hVperp _ hv
    have hyb : M₀.B y b₀ = 0 := by
      have := hy b₀ hb₀S
      rw [hsymm]
      exact this
    rw [map_add, LinearMap.add_apply, hyb, add_zero] at h1
    exact h1
  · intro M' hM' hodd hMb
    obtain ⟨s', hs'odd, hs'⟩ := hc.exists_XbarH_oddLift hD φ hφπ hφk hQ2 e M' (hXS2 M' hM') hodd
    have hfix : φ (s' : ↥(H0 M Z)) b₀ = b₀ := by
      have h1 := cmCommGL_mulVec hc hD φ hφπ e (s' : ↥(H0 M Z)) ⟨b₀, hb₀S⟩
      rw [hs'] at h1
      have h2 : e (cmCommActH hc hD φ hφπ (s' : ↥(H0 M Z)) ⟨b₀, hb₀S⟩) = e ⟨b₀, hb₀S⟩ := by
        rw [← h1]
        exact hMb
      exact congrArg Subtype.val (e.injective h2)
    have hcent := hc.mem_centralizer_B_of_odd_fix φ hφπ hB (s' : ↥(H0 M Z)).2 hs'odd hfix
    have hnorm : ((s' : ↥(H0 M Z)) : G) ∈ Subgroup.normalizer (B : Set G) :=
      Subgroup.centralizer_le_normalizer (B : Set G) hcent
    refine ⟨fun w hw => ?_, ?_⟩
    · obtain ⟨v, hv, rfl⟩ := hΨmem w hw
      refine AddSubgroup.mem_map.mpr ⟨φ (s' : ↥(H0 M Z)) v,
        hc.act_mem_img_inf_QB_of_normalizer φ hφπ (s' : ↥(H0 M Z)).2 hnorm hv, ?_⟩
      show Ψ (φ (s' : ↥(H0 M Z)) v) = _
      rw [hc.complProdEquiv_act hD φ hφπ e c
        (fun z hz => hc.action_fixes_orthogonal_of_mem_XbarH hD φ hφπ s' hz) v, hs']
    · rintro _ ⟨ℓ, rfl⟩
      have hℓL : (((ℓ : ↥LBH) : ↥(H0 M Z)) : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp ℓ.2
      refine ⟨⟨(s' : ↥(H0 M Z)) * (ℓ : ↥(H0 M Z)) * (s' : ↥(H0 M Z))⁻¹, ?_⟩, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr
          (hc.conj_mem_LB_of_normalizer (s' : ↥(H0 M Z)).2.1 hnorm hℓL)
      · show cmCommGL hc hD φ hφπ e ((s' : ↥(H0 M Z)) * (ℓ : ↥(H0 M Z)) * (s' : ↥(H0 M Z))⁻¹) =
          (M' : GL (Fin (2 * 4)) K) * cmCommGL hc hD φ hφπ e (ℓ : ↥(H0 M Z)) *
            (M' : GL (Fin (2 * 4)) K)⁻¹
        rw [map_mul, map_mul, map_inv, hs']
  · rintro _ ⟨ℓ, rfl⟩ x hx
    obtain ⟨x', rfl⟩ := e.surjective x
    have hℓL : (((ℓ : ↥LBH) : ↥(H0 M Z)) : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp ℓ.2
    have hxb : M₀.B (x' : M₀.E) b₀ = 0 := by
      have := polar_coordinateQuadPlus_e φ e heQ x' ⟨b₀, hb₀S⟩
      rw [← this]
      exact hx
    have hu := hc.map_sub_one_mem_img_inf_QB φ hφπ hperp hℓL (ℓ : ↥LBH).1.2 hxb
    refine AddSubgroup.mem_map.mpr ⟨_, hu, ?_⟩
    have hu_S : φ (ℓ : ↥(H0 M Z)) (x' : M₀.E) - (x' : M₀.E) ∈ cmComm M Q Z B K γ M₀ φ :=
      Submodule.sub_mem _ (hc.mem_cmComm_of_act hD φ hφπ (ℓ : ↥(H0 M Z)).2 x'.2) x'.2
    show Ψ (φ (ℓ : ↥(H0 M Z)) (x' : M₀.E) - (x' : M₀.E)) = _
    rw [hΨS hu_S]
    show (e ⟨_, hu_S⟩, (0 : Fin (2 * s) → K)) = (_, 0)
    congr 1
    rw [show (⟨φ (ℓ : ↥(H0 M Z)) (x' : M₀.E) - (x' : M₀.E), hu_S⟩ :
      ↥(cmComm M Q Z B K γ M₀ φ)) = cmCommActH hc hD φ hφπ (ℓ : ↥(H0 M Z)) x' - x' from rfl,
      map_sub]
    show e (cmCommActH hc hD φ hφπ (ℓ : ↥(H0 M Z)) x') - e x' =
      ((cmCommGL hc hD φ hφπ e (ℓ : ↥(H0 M Z)) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e x' - e x'
    rw [cmCommGL_mulVec]
  · rintro _ ⟨ℓ, rfl⟩ w hw
    obtain ⟨v, hv, rfl⟩ := hΨmem w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mem_add_eq_of_isCompl hSC v
    have hℓL : (((ℓ : ↥LBH) : ↥(H0 M Z)) : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp ℓ.2
    obtain ⟨t, ht⟩ := (hflag (ℓ : ↥(H0 M Z)) hℓL).2 (x + y) hv
    refine ⟨t, ?_⟩
    rw [hΨadd hx hy]
    show ((cmCommGL hc hD φ hφπ e (ℓ : ↥(H0 M Z)) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e ⟨x, hx⟩ - e ⟨x, hx⟩ = t • b
    rw [cmCommGL_mulVec]
    have h1 : φ (ℓ : ↥(H0 M Z)) x - x = t • b₀ := by
      rw [map_add, hLBC (ℓ : ↥(H0 M Z)) hℓL y hy] at ht
      rw [← ht]
      abel
    have hb' : t • b₀ ∈ cmComm M Q Z B K γ M₀ φ := Submodule.smul_mem _ t hb₀S
    rw [← map_sub]
    show e (cmCommActH hc hD φ hφπ (ℓ : ↥(H0 M Z)) ⟨x, hx⟩ - ⟨x, hx⟩) = t • e ⟨b₀, hb₀S⟩
    rw [← map_smul]
    congr 1
    exact Subtype.ext h1
  · intro w hw hfixw
    obtain ⟨v, hv, rfl⟩ := hΨmem w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mem_add_eq_of_isCompl hSC v
    rw [hΨadd hx hy] at hfixw ⊢
    have hfixl : ∀ (l : G) (_hl : l ∈ LB M Q B) (hlH : l ∈ H0 M Z),
        φ ⟨l, hlH⟩ (x + y) = x + y := by
      intro l hl hlH
      have h1 := hfixw (cmCommGL hc hD φ hφπ e ⟨l, hlH⟩)
        ⟨⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl⟩, rfl⟩
      rw [cmCommGL_mulVec] at h1
      have h2 := e.injective h1
      have h3 : φ ⟨l, hlH⟩ x = x := congrArg Subtype.val h2
      rw [map_add, h3, hLBC ⟨l, hlH⟩ hl y hy]
    obtain ⟨t, ht⟩ := hc.eq_smul_of_fixed_mem_img_inf_QB φ hφπ hB hv hfixl
    have hb' : t • b₀ ∈ cmComm M Q Z B K γ M₀ φ := Submodule.smul_mem _ t hb₀S
    have hyS : y ∈ cmComm M Q Z B K γ M₀ φ := by
      have : y = t • b₀ - x := by rw [← ht]; abel
      rw [this]
      exact Submodule.sub_mem _ hb' hx
    have hy0 : y = 0 := Submodule.disjoint_def.mp hSC.disjoint y hyS hy
    subst hy0
    have hx' : x = t • b₀ := by simpa using ht
    refine ⟨t, ?_⟩
    subst hx'
    show (e ⟨t • b₀, hx⟩, c ⟨0, hy⟩) = (t • b, 0)
    refine Prod.ext ?_ (map_zero c)
    show e ⟨t • b₀, hx⟩ = t • e ⟨b₀, hb₀S⟩
    rw [← map_smul]
    rfl
  · have h1 := hc.card_cmCommGL_range_mul hD φ hφπ hφk ha2 e
    have h2 := hc.card_LB_mul hw
    have hZS : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (Ctx.Z_le_QB hc).1
    have h3 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card V := M₀.card_eq hSQ hZS
    have h4 : Nat.card W = Nat.card V :=
      AddSubgroup.card_map_of_injective
        (f := (Ψ : M₀.E →ₗ[K] ((Fin (2 * 4) → K) × (Fin (2 * s) → K))).toAddMonoidHom)
        Ψ.injective
    have hKZ : Nat.card K = Nat.card Z := hD.card
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hposQ : 0 < Nat.card Q := Nat.card_pos
    have h5 : Nat.card A * Nat.card V = Nat.card Z ^ (2 * n - 1) := by
      rw [← h1, h3] at h2
      have h6 : Nat.card Z ^ (2 * n) = Nat.card Z * Nat.card Z ^ (2 * n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h6] at h2
      have h7 : Nat.card Q * (Nat.card Z * (Nat.card A * Nat.card V)) =
          Nat.card Q * (Nat.card Z * Nat.card Z ^ (2 * n - 1)) := by
        rw [← h2]
        ring
      have h8 := Nat.eq_of_mul_eq_mul_left hposQ h7
      exact Nat.eq_of_mul_eq_mul_left hpos h8
    rw [h4, hKZ, h5]
    congr 1
    omega

end Certificates

section Certificates


theorem stroth118_hI4_of_spin
    (hU : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
        ∀ (V : Type) [AddCommGroup V] [Module K V], Module.finrank K V = 8 →
        ∀ (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
        ∀ (ψ : StatedSp 3 K →* (V ≃ₗ[K] V)), (∀ g v, Q (ψ g v) = Q v) →
        (∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
        (∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K, c ≠ 0 →
          IsLongRootElement Q (ψ (SpExtras.elt r c))) →
        ∃ e : V ≃ₗ[K] (Fin (2 * 4) → K), (∀ v, coordinateQuadPlus 4 K (e v) = Q v) ∧
          (∀ g, ∃ M ∈ spinSeven K, ∀ v,
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v =
              e (ψ g v)) ∧
          ∀ M ∈ spinSeven K, ∃ g, ∀ v,
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = e (ψ g v))
    (hG : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (s : ℕ)
        (QC : QuadraticForm K (Fin (2 * s) → K)) (b : Fin (2 * 4) → K),
        b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
        ∀ (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
          (A : Subgroup (GL (Fin (2 * 4)) K)),
          A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype →
          (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b) →
          (∀ t : K, (t • b, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0) →
          (∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 b = 0) →
          (∀ M ∈ spinSeven K, Odd (orderOf M) →
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b →
            (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
              w.2) ∈ W) ∧
            ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A) →
          (∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x b = 0 →
            ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
            (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • b) →
          (∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
            ∃ t : K, w = (t • b, 0)) →
          Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s) → False)
    (hN : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
        ∀ g : GL (Fin (2 * 4)) K,
          (∀ v : Fin (2 * 4) → K,
            coordinateQuadPlus 4 K ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
              coordinateQuadPlus 4 K v) →
          (∀ M ∈ spinSeven K,
            g * (M : GL (Fin (2 * 4)) K) * g⁻¹ ∈
              (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype) →
          g ∈ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal],
          Ctx M Q Z B → ∀ n m x : ℕ, Width Q Z n → 2 < n →
          CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x →
          ∀ (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)),
            ¬ CMSpTransvAt M Q Z B m x a h →
            2 ^ x = Nat.card Z →
            m = 3 → Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 →
            (∀ W : Subgroup G, Z ≤ W → W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ →
              (∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
              W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) →
            (∃ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ Xbar M Q Z B ∧
              Odd (orderOf (QuotientGroup.mk y : Mbar M Q)) ∧
              ∀ v ∈ Z ⊔ ⁅Q, XbarPre M Q Z B⁆, ⁅(y : G), v⁆ ∈ Z → v ∈ Z) →
            False := by
  intro G _ _ M Q Z B _ hc n m x hw hn hLm a h hnT hq hm3 _ _ _
  subst hm3
  exact Ctx.false_of_spinCase hU hG hN hc hw hn hLm hnT hq

end Certificates

end CFSG.RankThree.GF2n.Stroth80
