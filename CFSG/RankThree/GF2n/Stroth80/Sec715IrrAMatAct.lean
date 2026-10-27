module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerPair

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module Matrix

variable {K L H : Type*} [Field K] [AddCommGroup L] [Module K L] [Group H]

theorem exists_eq_matAct_of_commute (ρ : H →* (L ≃ₗ[K] L))
    (hEnd : ∀ T : L →ₗ[K] L, (∀ h y, T (ρ h y) = ρ h (T y)) → ∃ c : K, T = c • LinearMap.id)
    (T : (Fin 2 → L) →ₗ[K] (Fin 2 → L))
    (hT : ∀ h x, T (fun i => ρ h (x i)) = fun i => ρ h (T x i)) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, T = matAct A := by
  classical
  have hblock : ∀ i j : Fin 2, ∃ c : K,
      (LinearMap.proj i).comp (T.comp (LinearMap.single K (fun _ => L) j)) = c • LinearMap.id := by
    intro i j
    refine hEnd _ fun h y => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single]
    have e : (Pi.single j (ρ h y) : Fin 2 → L) = fun k => ρ h ((Pi.single j y : Fin 2 → L) k) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    rw [e, hT]
  choose A hA using hblock
  refine ⟨Matrix.of A, LinearMap.ext fun x => funext fun i => ?_⟩
  have hx : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
    funext k
    fin_cases k <;> simp
  have h0 := LinearMap.congr_fun (hA i 0) (x 0)
  have h1 := LinearMap.congr_fun (hA i 1) (x 1)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.coe_single, LinearMap.smul_apply, LinearMap.id_apply] at h0 h1
  rw [matAct_apply, Matrix.of_apply, Matrix.of_apply, ← h0, ← h1]
  conv_lhs => rw [hx]
  rw [map_add, Pi.add_apply]

section Conj

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem exists_conj_deltaSub (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    {z : G} (hzK : z ∈ NormH0 M Z Z0) (hzR : ∀ x ∈ Rt M (LB M Q B) t, ⁅z, x⁆ ∈ hc.CN t) :
    ∃ T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t),
      (∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t))
        (hzx : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzK.1.1⟩ * x *
          (QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzK.1.1⟩)⁻¹ ∈ bar M Q (hc.CN t)),
        T ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ =
          ⟨delta hS t _ (mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩) ∧
      ∀ y f, T (deltaAct hS hs.toSec5.mem y f) = deltaAct hS hs.toSec5.mem y (T f) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hzM : z ∈ M := hzK.1.1
  let zm : ↥M := ⟨z, hzM⟩
  set zb : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) zm with hzb
  have hzH : zb ∈ bar M Q (H0 M Z) := mk_mem_bar zm hzK.1
  have hNn : conjSubgroup z (hc.CN t) = hc.CN t := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hzK
  have hzN : ∀ m ∈ bar M Q (hc.CN t), zb * m * zb⁻¹ ∈ bar M Q (hc.CN t) := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := exists_of_mem_bar hm
    have h1 : z * (m' : G) * z⁻¹ ∈ conjSubgroup z (hc.CN t) := ⟨m', hm', rfl⟩
    rw [hNn] at h1
    exact mk_mem_bar (zm * m' * zm⁻¹) h1
  have hzW' : ∀ w ∈ wsub hS t, (ρ zb⁻¹).toAdd w ∈ wsub hS t := by
    have h := stab_wsub_of_mem_NormH0 hS hZt hZcard hs hZ0 ((NormH0 M Z Z0).inv_mem hzK)
    intro w hw
    exact h w hw
  set C := conjE hS zb hzH hzW' with hC
  have hCΔ : ∀ (m : Mbar M Q) (hm : m ∈ bar M Q (hc.CN t)),
      C (delta hS t m (mem_bar_H0_of_CN hm)) =
        delta hS t (zb * m * zb⁻¹) (mem_bar_H0_of_CN (hzN m hm)) := fun m hm =>
    (delta_conj_of_stab hS zb hzH hzW' (mem_bar_H0_of_CN hm)).symm
  have hCmem : ∀ f ∈ deltaSub hS t, C f ∈ deltaSub hS t := by
    intro f hf
    obtain ⟨m, hm, rfl⟩ := hSΔ f hf
    rw [hCΔ m hm]
    exact delta_mem_deltaSub hS (hzN m hm)
  set T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t) := C.restrict hCmem with hT
  have hNR : ∀ c ∈ bar M Q (hc.CN t), c ∈ bar M Q (Rt M (LB M Q B) t) := by
    intro c hc'
    obtain ⟨c', hc'', rfl⟩ := exists_of_mem_bar hc'
    exact mk_mem_bar c' (Ctx.mem_CN.mp hc'').1
  have hTapp : ∀ f : ↥(deltaSub hS t), ((T f : ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E) =
      C f := fun f => rfl
  have hNtriv : ∀ (c : Mbar M Q) (hc' : c ∈ bar M Q (hc.CN t)) (m : Mbar M Q)
      (hm : m ∈ bar M Q (hc.CN t)),
      delta hS t (c * m * c⁻¹) (mem_bar_H0_of_CN (hc.bar_CN_conj_mem ht
        (hNR _ hc') hm)) =
        delta hS t m (mem_bar_H0_of_CN hm) := by
    intro c hc' m hm
    have hcR : c ∈ bar M Q (Rt M (LB M Q B) t) := hNR _ hc'
    have h1 := deltaAct_delta hS ht ⟨c, hcR⟩ hm
    rw [deltaAct_of_mem_CN h310chi h52a hS hs hr ⟨c, hcR⟩ hc'] at h1
    exact (congrArg Subtype.val h1).symm
  refine ⟨T, fun x hx hzx => Subtype.ext ?_, fun y f => ?_⟩
  · rw [hTapp]
    exact hCΔ x hx
  obtain ⟨f, hf⟩ := f
  obtain ⟨m, hm, rfl⟩ := hSΔ f hf
  have hxm := hc.bar_CN_conj_mem ht y.2 hm
  refine Subtype.ext ?_
  rw [hTapp, deltaAct_delta hS ht y hm]
  show C (delta hS t _ _) = ((deltaAct hS ht y ⟨C (delta hS t m _), _⟩ :
    ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E)
  have e1 : (⟨C (delta hS t m (mem_bar_H0_of_CN hm)), hCmem _ (delta_mem_deltaSub hS hm)⟩ :
      ↥(deltaSub hS t)) = ⟨delta hS t (zb * m * zb⁻¹) (mem_bar_H0_of_CN (hzN m hm)),
        delta_mem_deltaSub hS (hzN m hm)⟩ := Subtype.ext (hCΔ m hm)
  rw [e1, deltaAct_delta hS ht y (hzN m hm), hCΔ _ hxm]
  show delta hS t (zb * ((y : Mbar M Q) * m * (y : Mbar M Q)⁻¹) * zb⁻¹) _ =
    delta hS t ((y : Mbar M Q) * (zb * m * zb⁻¹) * (y : Mbar M Q)⁻¹) _
  obtain ⟨yr, hyr, hye⟩ := exists_of_mem_bar y.2
  have hcN : ⁅zb, (y : Mbar M Q)⁆ ∈ bar M Q (hc.CN t) := by
    rw [← hye, show ⁅zb, (QuotientGroup.mk yr : Mbar M Q)⁆ = QuotientGroup.mk ⁅zm, yr⁆ from
      (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) zm yr).symm]
    exact mk_mem_bar _ (hzR _ hyr)
  have hy := hc.bar_CN_conj_mem ht y.2 (hzN m hm)
  have e2 : zb * ((y : Mbar M Q) * m * (y : Mbar M Q)⁻¹) * zb⁻¹ =
      ⁅zb, (y : Mbar M Q)⁆ * ((y : Mbar M Q) * (zb * m * zb⁻¹) * (y : Mbar M Q)⁻¹) *
        ⁅zb, (y : Mbar M Q)⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [delta_congr hS t e2 _ (mem_bar_H0_of_CN (hc.bar_CN_conj_mem ht
    (hNR _ hcN) hy))]
  exact hNtriv _ hcN _ hy

end Conj

end CFSG.RankThree.GF2n.Stroth80.S715L
