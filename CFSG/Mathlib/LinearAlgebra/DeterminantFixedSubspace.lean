module

public import CFSG.RankThree.GF2n.Smith81.Lin26Linear

public section
namespace LinearEquiv

theorem displacement_mem_of_fix_submodule_of_det_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (T : V ≃ₗ[k] V) (S : Submodule k V)
    (hcodim : Module.finrank k V ≤ Module.finrank k S + 1)
    (hfix : ∀ v ∈ S, T v = v) (hdet : T.det = 1) :
    ∀ v, T v - v ∈ S := by
  let f : V →ₗ[k] V := T.toLinearMap
  have hS : S ≤ S.comap f := by intro v hv; change T v ∈ S; rw [hfix v hv]; exact hv
  have hres : f.restrict hS = LinearMap.id := by ext v; exact hfix v.1 v.2
  let q : (V ⧸ S) →ₗ[k] (V ⧸ S) := S.mapQ S f hS
  have hqdet : LinearMap.det q = 1 := by
    have hd : LinearMap.det f = 1 := by
      change LinearMap.det T.toLinearMap = 1
      rw [← LinearEquiv.coe_det, hdet, Units.val_one]
    rw [LinearMap.det_eq_det_mul_det S f hS,hres,LinearMap.det_id,one_mul] at hd
    exact hd
  have hdim : Module.finrank k (V ⧸ S) ≤ 1 := by
    have hh := Submodule.finrank_quotient_add_finrank S
    omega
  have hq : q = LinearMap.id := by
    by_cases h0 : Module.finrank k (V ⧸ S) = 0
    · have : Subsingleton (V ⧸ S) := (Module.finrank_zero_iff (R := k)).mp h0
      exact LinearMap.ext fun _ => Subsingleton.elim _ _
    · have h1 : Module.finrank k (V ⧸ S) = 1 := by omega
      obtain ⟨c,hc,-⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 q
      have hdc : c = 1 := by
        rw [hc,LinearMap.det_smul,h1,pow_one,LinearMap.det_id,mul_one] at hqdet
        exact hqdet
      rw [hc,hdc,one_smul]
  intro v
  have hv := congrArg (fun l : (V ⧸ S) →ₗ[k] (V ⧸ S) => l (Submodule.Quotient.mk v)) hq
  have he : (Submodule.Quotient.mk (T v) : V ⧸ S) = Submodule.Quotient.mk v := by
    simpa only [q,Submodule.mapQ_apply,LinearMap.id_apply,f,LinearEquiv.coe_coe] using hv
  exact (Submodule.Quotient.eq S).mp he

theorem det_eq_of_scalar_quotient_of_fix_plane {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (T : V ≃ₗ[k] V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span k {y}) (A c mu : k) (hc : c ≠ 0)
    (hTy : T y = y) (hTz : T z = A • y + c • z)
    (hmove : ∀ v, T v - mu • v ∈ Submodule.span k {y,z}) :
    (T.det : k) = c * mu ^ (Module.finrank k V - 2) := by
  let F := Submodule.span k {y,z}
  have hyF : y ∈ F := Submodule.subset_span (by simp)
  have hTF : F ≤ F.comap T.toLinearMap := by
    intro v hv
    change T v ∈ F
    simpa only [sub_add_cancel] using F.add_mem (hmove v) (F.smul_mem mu hv)
  have hq : F.mapQ F T.toLinearMap hTF = mu • LinearMap.id := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change (Submodule.Quotient.mk (T v) : V ⧸ F) = Submodule.Quotient.mk (mu • v)
      exact (Submodule.Quotient.eq F).mpr (hmove v)
  have hdet : LinearMap.det T.toLinearMap =
      LinearMap.det (T.toLinearMap.restrict hTF) * mu ^ Module.finrank k (V ⧸ F) := by
    rw [LinearMap.det_eq_det_mul_det F T.toLinearMap hTF,hq,LinearMap.det_smul,
      LinearMap.det_id,mul_one]
  have hdim : Module.finrank k F = 2 := by
    have hspan : F = Submodule.span k {y} ⊔ Submodule.span k {z} := by
      dsimp only [F]
      rw [← Submodule.span_union]
      congr 1
    rw [hspan,Submodule.finrank_sup_span_singleton hz,finrank_span_singleton hy]
  have hscaleF : ∀ v ∈ F, (c⁻¹ • T.toLinearMap) v ∈ F := by
    intro v hv
    exact F.smul_mem _ (hTF hv)
  have hscaleY : (c⁻¹ • T.toLinearMap) y = c⁻¹ • y := by
    simp only [LinearMap.smul_apply,LinearEquiv.coe_coe,hTy]
  have hscaleMove : ∀ v ∈ F,
      (c⁻¹ • T.toLinearMap) v - v ∈ Submodule.span k {y} := by
    intro v hv
    have hspan : F = Submodule.span k {y} ⊔ Submodule.span k {z} := by
      dsimp only [F]
      rw [← Submodule.span_union]; congr 1
    rw [hspan] at hv
    obtain ⟨v1,hv1,v2,hv2,hv12⟩ := Submodule.mem_sup.mp hv
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv1
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv2
    rw [← hv12]
    have heq : (c⁻¹ • T.toLinearMap) (r • y + t • z) - (r • y + t • z) =
        (c⁻¹ * r + c⁻¹ * t * A - r) • y := by
      simp only [LinearMap.smul_apply,map_add,map_smul,LinearEquiv.coe_coe,hTy,hTz,
        smul_add,smul_smul]
      rw [show c⁻¹ * (t * c) = t by field_simp]
      module
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  have hs := CFSG.RankThree.GF2n.Smith81.det_restrict_homology F (c⁻¹ • T.toLinearMap)
    hscaleF hyF hy c⁻¹ hscaleY hscaleMove
  have hres : (c⁻¹ • T.toLinearMap).restrict hscaleF =
      c⁻¹ • T.toLinearMap.restrict hTF := by ext v; rfl
  rw [hres,LinearMap.det_smul,hdim] at hs
  have hval : LinearMap.det (T.toLinearMap.restrict hTF) = c := by
    field_simp [hc] at hs
    exact hs
  rw [← LinearEquiv.coe_det] at hdet
  rw [hval] at hdet
  have hdimQ := Submodule.finrank_quotient_add_finrank F
  rw [hdim] at hdimQ
  rw [show Module.finrank k (V ⧸ F) = Module.finrank k V - 2 by omega] at hdet
  exact hdet




theorem det_eq_of_displacement_mem_plane {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (T : V ≃ₗ[k] V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span k {y}) (A c : k) (hc : c ≠ 0)
    (hTy : T y = y) (hTz : T z = A • y + c • z)
    (hmove : ∀ v, T v - v ∈ Submodule.span k {y,z}) : (T.det : k) = c := by
  simpa only [one_pow,mul_one] using
    det_eq_of_scalar_quotient_of_fix_plane T y z hy hz A c 1 hc hTy hTz
      (by simpa only [one_smul] using hmove)

end LinearEquiv
