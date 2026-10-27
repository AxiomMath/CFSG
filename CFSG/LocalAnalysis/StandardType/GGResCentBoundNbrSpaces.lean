module

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrKernel
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundLin

public section
namespace CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_plane_dual_coordinates {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (y z : V) (hy : y ≠ 0) (hz : z ∉ Submodule.span k {y}) :
    ∃ l a : Module.Dual k V, l y = 1 ∧ l z = 0 ∧ a y = 0 ∧ a z = 1 ∧
      ∀ v ∈ Submodule.span k {y,z}, v = l v • y + a v • z := by
  classical
  obtain ⟨a0,ha0z,ha0ker⟩ := Submodule.exists_le_ker_of_notMem hz
  let a : Module.Dual k V := (a0 z)⁻¹ • a0
  have haz : a z = 1 := by simp [a,ha0z]
  have hay : a y = 0 := by
    have h := ha0ker (Submodule.mem_span_singleton_self y)
    simp [a,LinearMap.mem_ker.mp h]
  have hyz : y ∉ Submodule.span k {z} := by
    intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    have hca : c = 0 := by
      have hh := congrArg a hc
      simp [hay,haz] at hh
      exact hh
    exact hy (by simpa [hca] using hc.symm)
  obtain ⟨l0,hl0y,hl0ker⟩ := Submodule.exists_le_ker_of_notMem hyz
  let l : Module.Dual k V := (l0 y)⁻¹ • l0
  have hly : l y = 1 := by simp [l,hl0y]
  have hlz : l z = 0 := by
    have h := hl0ker (Submodule.mem_span_singleton_self z)
    simp [l,LinearMap.mem_ker.mp h]
  refine ⟨l,a,hly,hlz,hay,haz,?_⟩
  intro v hv
  have hspan : Submodule.span k {y,z} = Submodule.span k {y} ⊔ Submodule.span k {z} := by
    rw [← Submodule.span_union]; congr 1
  rw [hspan] at hv
  obtain ⟨v1,hv1,v2,hv2,hv12⟩ := Submodule.mem_sup.mp hv
  obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv1
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hv2
  rw [← hv12]
  simp [map_add,map_smul,hly,hlz,hay,haz]


private theorem exists_dual_span_complement_of_codim_le_one {k V : Type} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] (S : Submodule k V)
    (hcodim : Module.finrank k V ≤ Module.finrank k S + 1) :
    ∃ d : Module.Dual k V, (∀ v ∈ S, d v = 0) ∧ ∀ v, v ∈ S ↔ d v = 0 := by
  classical
  by_cases htop : S = ⊤
  · exact ⟨0, fun _ _ => rfl, fun v => by simp [htop]⟩
  obtain ⟨v,hv⟩ : ∃ v, v ∉ S := by
    by_contra h
    push Not at h
    apply htop
    ext x
    simp [h x]
  obtain ⟨d,hdv,hdS⟩ := Submodule.exists_le_ker_of_notMem hv
  have hbig : S ⊔ Submodule.span k {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hfin := Submodule.finrank_sup_span_singleton hv
    have hle := Submodule.finrank_le (S ⊔ Submodule.span k {v})
    omega
  refine ⟨d, fun x hx => hdS hx, fun x => ?_⟩
  constructor
  · exact fun hx => hdS hx
  · intro hdx
    obtain ⟨u,hu,w,hw,huw⟩ := Submodule.mem_sup.mp (hbig ▸ Submodule.mem_top (x := x))
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hdz : c * d v = 0 := by
      have h := congrArg d huw
      rw [map_add, map_smul, hdS hu, hdx] at h
      simpa [smul_eq_mul] using h
    have hc : c = 0 := (mul_eq_zero.mp hdz).resolve_right hdv
    rw [hc, zero_smul, add_zero] at huw
    exact huw ▸ hu


private theorem exists_disjoint_subspace_sup_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (U F : Submodule k V) : ∃ U0 : Submodule k V, U0 ≤ U ∧ Disjoint U0 F ∧ U0 ⊔ F = U ⊔ F := by
  classical
  let I := F.comap U.subtype
  obtain ⟨Q,hQ⟩ := I.exists_isCompl
  let U0 := Q.map U.subtype
  have hU0 : U0 ≤ U := by
    rintro v ⟨q,hq,rfl⟩
    exact q.2
  have hdis : Disjoint U0 F := by
    rw [Submodule.disjoint_def]
    intro v hv hvF
    obtain ⟨q,hq,rfl⟩ := hv
    have hI : q ∈ I := hvF
    have hq0 := Submodule.disjoint_def.mp hQ.disjoint q hI hq
    exact congrArg Subtype.val hq0
  have hUF : U ≤ U0 ⊔ F := by
    intro u hu
    have htop : (⟨u,hu⟩ : U) ∈ I ⊔ Q := by rw [hQ.sup_eq_top]; trivial
    obtain ⟨i,hi,q,hq,hiq⟩ := Submodule.mem_sup.mp htop
    refine Submodule.mem_sup.mpr ⟨q,⟨q,hq,rfl⟩,i,hi,?_⟩
    have h := congrArg Subtype.val hiq
    simpa only [Submodule.coe_add,add_comm] using h
  refine ⟨U0,hU0,hdis,le_antisymm (sup_le (hU0.trans le_sup_left) le_sup_right)
    (sup_le hUF le_sup_right)⟩


private theorem exists_dual_coordinates_vanishing_on_disjoint {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] (U F : Submodule k V) (hdis : Disjoint U F)
    (l a : Module.Dual k V) : ∃ l' a' : Module.Dual k V,
    (∀ v ∈ U, l' v = 0 ∧ a' v = 0) ∧ ∀ v ∈ F, l' v = l v ∧ a' v = a v := by
  let f : U × F →ₗ[k] V := U.subtype.coprod F.subtype
  have hf : f.ker = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range U.subtype F.subtype
      (by simpa only [Submodule.range_subtype] using hdis), Submodule.ker_subtype,
      Submodule.ker_subtype]
    ext x
    simp
  obtain ⟨r,hr⟩ := f.exists_leftInverse_of_injective hf
  let pr : V →ₗ[k] V := F.subtype.comp ((LinearMap.snd k U F).comp r)
  refine ⟨l.comp pr, a.comp pr, ?_, ?_⟩
  · intro v hv
    have h : r v = (⟨v,hv⟩,0) := by
      have hh := congrArg (fun h : U × F →ₗ[k] U × F => h (⟨v,hv⟩,0)) hr
      simpa [f] using hh
    simp [pr,h]
  · intro v hv
    have h : r v = (0,⟨v,hv⟩) := by
      have hh := congrArg (fun h : U × F →ₗ[k] U × F => h (0,⟨v,hv⟩)) hr
      simpa [f] using hh
    simp [pr,h]


private theorem exists_smul_eq_of_ker_le {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (d b : Module.Dual k V) (hker : d.ker ≤ b.ker) :
    ∃ c : k, b = c • d := by
  have hmem : b ∈ Submodule.span k (Set.range (fun _ : Unit => d)) :=
    mem_span_of_iInf_ker_le_ker (by simpa using hker)
  have hm : b ∈ Submodule.span k {d} := by simpa only [Set.range_const] using hmem
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨c,hc.symm⟩

private theorem exists_plane_action_coordinates {k V H : Type} [Field k] [AddCommGroup V]
    [Module k V] [Module.Finite k V] [Group H] (T : H →* (V ≃ₗ[k] V))
    (U F : Submodule k V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span k {y}) (hF : F = Submodule.span k {y,z})
    (mu : H →* kˣ)
    (hmove : ∀ g : H, ∀ v, T g v - (mu g : k) • v ∈ F)
    (hU : ∀ g : H, ∀ v ∈ U, T g v = (mu g : k) • v)
    (hGy : ∀ g : H, T g y = y)
    (hcodim : Module.finrank k V ≤ Module.finrank k ↥(U ⊔ F) + 1) :
    ∃ (l a d : Module.Dual k V) (c : H →* kˣ) (A B D : H → k),
      (∀ g : H, ∀ v, T g v = (mu g : k) • v +
        (((1 - (mu g : k)) * l v + A g * a v + B g * d v) • y) +
          (((c g : k) - (mu g : k)) * a v + D g * d v) • z) ∧
      l y = 1 ∧ l z = 0 ∧ a y = 0 ∧ a z = 1 ∧ d y = 0 ∧ d z = 0 := by
  classical
  obtain ⟨l0,a0,hly0,hlz0,hay0,haz0,hcoords0⟩ := exists_plane_dual_coordinates y z hy hz
  obtain ⟨U0,hU0,hdis,hSup⟩ := exists_disjoint_subspace_sup_eq U F
  obtain ⟨l,a,hzero,hagree⟩ := exists_dual_coordinates_vanishing_on_disjoint U0 F hdis l0 a0
  have hyF : y ∈ F := by rw [hF]; exact Submodule.subset_span (by simp)
  have hzF : z ∈ F := by rw [hF]; exact Submodule.subset_span (by simp)
  have hly : l y = 1 := ((hagree y hyF).1).trans hly0
  have hlz : l z = 0 := ((hagree z hzF).1).trans hlz0
  have hay : a y = 0 := ((hagree y hyF).2).trans hay0
  have haz : a z = 1 := ((hagree z hzF).2).trans haz0
  have hcoords : ∀ v ∈ Submodule.span (k) {y,z}, v = l v • y + a v • z := by
    intro v hv
    have hvF : v ∈ F := hF ▸ hv
    rw [(hagree v hvF).1,(hagree v hvF).2]
    exact hcoords0 v hv
  have hTy (g : H) : T g y = y := hGy g
  have hTz (g : H) : T g z = l (T g z) • y + a (T g z) • z := by
    have hzF : z ∈ F := by rw [hF]; exact Submodule.subset_span (by simp)
    have htF : T g z ∈ F := by
      have h := hmove g z
      have he := F.add_mem h (F.smul_mem (mu g : k) hzF)
      simpa using he
    exact hcoords _ (hF ▸ htF)
  have haz0 (g : H) : a (T g z) ≠ 0 := by
    intro h0
    have hval : T g z = l (T g z) • y := by simpa only [h0,zero_smul,add_zero] using hTz g
    have he : T g z = T g (l (T g z) • y) := by rw [map_smul,hTy]; exact hval
    have hze := (T g).injective he
    exact hz (hze ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  have hc_mul (g k : H) : a (T (g*k) z) = a (T g z) * a (T k z) := by
    have hTk : T (g*k) z = T g (T k z) := by simp only [map_mul,LinearEquiv.mul_apply]
    rw [hTk,hTz k,map_add,map_smul,map_smul,hTy]
    simp [map_add,map_smul,hay,haz,mul_comm]
  let c : H →* (k)ˣ := MonoidHom.mk' (fun g => Units.mk0 (a (T g z)) (haz0 g))
    (fun g k => Units.ext (hc_mul g k))
  let N (g : H) : V →ₗ[k] V := (T g).toLinearMap - (mu g : k) • LinearMap.id
  let bY (g : H) : Module.Dual (k) V := l.comp (N g) -
    (1 - (mu g : k)) • l - l (T g z) • a
  let bZ (g : H) : Module.Dual (k) V := a.comp (N g) -
    ((c g : k) - (mu g : k)) • a
  have hbYF (g : H) : ∀ v ∈ F, bY g v = 0 := by
    intro v hv
    have hvC := hcoords v (hF ▸ hv)
    rw [hvC]
    simp only [map_add,map_smul]
    have hby : bY g y = 0 := by
      simp [bY,N,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,hTy,hly,hay,smul_eq_mul]
    have hbz : bY g z = 0 := by
      simp [bY,N,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,hlz,haz,smul_eq_mul]
    rw [hby,hbz,smul_zero,smul_zero,add_zero]
  have hbZF (g : H) : ∀ v ∈ F, bZ g v = 0 := by
    intro v hv
    have hvC := hcoords v (hF ▸ hv)
    rw [hvC]
    simp only [map_add,map_smul]
    have hby : bZ g y = 0 := by
      simp [bZ,N,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,hTy,hay,smul_eq_mul]
    have hbz : bZ g z = 0 := by
      simp [bZ,N,c,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,haz,smul_eq_mul]
    rw [hby,hbz,smul_zero,smul_zero,add_zero]
  have hbYU (g : H) : ∀ v ∈ U0, bY g v = 0 := by
    intro v hv
    have hUv : T g v = (mu g : k) • v := hU g v (hU0 hv)
    have hzv := hzero v hv
    simp [bY,N,LinearMap.comp_apply,hUv,hzv.1,hzv.2]
  have hbZU (g : H) : ∀ v ∈ U0, bZ g v = 0 := by
    intro v hv
    have hUv : T g v = (mu g : k) • v := hU g v (hU0 hv)
    have hzv := hzero v hv
    simp [bZ,N,LinearMap.comp_apply,hUv,hzv.2]
  obtain ⟨d,hdS,hdiff⟩ := exists_dual_span_complement_of_codim_le_one (U0 ⊔ F) (by rwa [hSup])
  have hbyker (g : H) : d.ker ≤ (bY g).ker := by
    intro v hv
    have hvS := (hdiff v).mpr hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hvS
    simp [map_add,hbYU g u hu,hbYF g w hw]
  have hbzker (g : H) : d.ker ≤ (bZ g).ker := by
    intro v hv
    have hvS := (hdiff v).mpr hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hvS
    simp [map_add,hbZU g u hu,hbZF g w hw]
  have hyrep (g : H) : ∃ b : k, bY g = b • d := by
    exact exists_smul_eq_of_ker_le d (bY g) (hbyker g)
  have hzrep (g : H) : ∃ b : k, bZ g = b • d := by
    exact exists_smul_eq_of_ker_le d (bZ g) (hbzker g)
  choose bY' hbY' using hyrep
  choose bZ' hbZ' using hzrep
  have hshape : ∀ g : H, ∀ v, T g v = (mu g : k) • v +
      ((1 - (mu g : k)) * l v + l (T g z) * a v + bY' g * d v) • y +
        (((c g : k) - (mu g : k)) * a v + bZ' g * d v) • z := by
    intro g v
    have hn : N g v ∈ F := hmove g v
    have hcoord := hcoords (N g v) (hF ▸ hn)
    have hycoef := congrArg (fun b : Module.Dual (k) V => b v) (hbY' g)
    have hzcoef := congrArg (fun b : Module.Dual (k) V => b v) (hbZ' g)
    simp only [bY,bZ,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      smul_eq_mul] at hycoef hzcoef
    have hyval : l (N g v) = (1 - (mu g : k)) * l v + l (T g z) * a v + bY' g * d v := by
      linear_combination hycoef
    have hzval : a (N g v) = ((c g : k) - (mu g : k)) * a v + bZ' g * d v := by
      linear_combination hzcoef
    rw [hyval,hzval] at hcoord
    change T g v - (mu g : k) • v = _ at hcoord
    calc T g v = (mu g : k) • v + (T g v - (mu g : k) • v) := by abel
      _ = _ := by rw [hcoord]; abel
  exact ⟨l,a,d,c,(fun g => l (T g z)),bY',bZ',hshape,hly,hlz,hay,haz,
    (hdS y (Submodule.mem_sup_right hyF)), (hdS z (Submodule.mem_sup_right hzF))⟩


theorem card_weyl_commutant_plane_le_six {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hNT : GGNoTransvection 3 Bs) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (U F : Submodule (ZMod 3) V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span (ZMod 3) {y}) (hF : F = Submodule.span (ZMod 3) {y,z})
    (mu : H →* (ZMod 3)ˣ)
    (hmove : ∀ g : H, ∀ v, ggLin (p := 3) ι g.1 v - (mu g : ZMod 3) • v ∈ F)
    (hU : ∀ g : H, ∀ v ∈ U, ggLin (p := 3) ι g.1 v = (mu g : ZMod 3) • v)
    (hGy : ∀ g : H, ggLin (p := 3) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) ↥(U ⊔ F) + 1) :
    Nat.card H ≤ 6 := by
  obtain ⟨l,a,d,c,A,B,D,hshape,hly,hlz,hay,haz,hdy,hdz⟩ :=
    exists_plane_action_coordinates ((ggLin (p := 3) ι).comp H.subtype) U F y z hy hz hF
      mu hmove hU hGy hcodim
  exact card_plane_correlated_le_six hNT ι H hH y z hy l a d mu c A B D
    (by simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply] using hshape)
    hly hlz hay haz hdy hdz

private theorem card_weyl_commutant_le_of_plane_bound {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (bound : ℕ) (hunits : p - 1 ≤ bound)
    (hplane : ∀ (U F : Submodule (ZMod p) V) (z : V),
      z ∉ Submodule.span (ZMod p) {y} → F = Submodule.span (ZMod p) {y,z} →
      ∀ mu : H →* (ZMod p)ˣ,
      (∀ g : H, ∀ v, ggLin (p := p) ι g.1 v - (mu g : ZMod p) • v ∈ F) →
      (∀ g : H, ∀ v ∈ U, ggLin (p := p) ι g.1 v = (mu g : ZMod p) • v) →
      Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ F) + 1 →
        Nat.card H ≤ bound) : Nat.card H ≤ bound := by
  classical
  let F : Submodule (ZMod p) V := (LinearMap.pi a).ker
  let U := Submodule.span (ZMod p) (Set.range h)
  let T : H →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp H.subtype
  obtain ⟨mu,hmu,hcor⟩ := exists_weyl_commutant_character hp2 hM hC h a hpair T hcomm
  have hm (g : H) (v : V) : ggLin (p := p) ι g.1 v - (mu g : ZMod p) • v ∈ F := by
    simp only [F,LinearMap.mem_ker,LinearMap.pi_apply,funext_iff,Pi.zero_apply]
    intro i
    simp only [map_sub,map_smul,smul_eq_mul]
    rw [show a i (ggLin (p := p) ι g.1 v) = (mu g : ZMod p) * a i v from hmu g i v]
    exact sub_self _
  have hu (g : H) : ∀ v ∈ U, ggLin (p := p) ι g.1 v = (mu g : ZMod p) • v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i,rfl⟩; exact hcor g i
    · simp
    · intro v w _ _ hv hw; simp only [map_add,hv,hw,smul_add]
    · intro c v _ hv; rw [map_smul,hv]; module
  have hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ F) + 1 :=
    finrank_le_sup_coroot_rootker_add_one hp2 hM hC h a hpair
  have hyF : y ∈ F := by simpa only [F,LinearMap.mem_ker,LinearMap.pi_apply,funext_iff,Pi.zero_apply] using hay
  have hyle : Submodule.span (ZMod p) {y} ≤ F := (Submodule.span_le).mpr (by simpa using hyF)
  by_cases hline : F = Submodule.span (ZMod p) {y}
  · have hinj : Function.Injective mu := (injective_iff_map_eq_one _).mpr fun g hg => by
      have hmv : ∀ v, ggLin (p := p) ι g.1 v - v ∈ Submodule.span (ZMod p) {y} := by
        intro v; simpa only [hg,Units.val_one,one_smul,hline] using hm g v
      let N : V →ₗ[ZMod p] V := (ggLin (p := p) ι g.1).toLinearMap - LinearMap.id
      have hn : N.range ≤ Submodule.span (ZMod p) {y} := by
        rintro _ ⟨v,rfl⟩; exact hmv v
      have hr := Submodule.finrank_mono hn
      rw [finrank_span_singleton hy] at hr
      have hsum := LinearMap.finrank_range_add_finrank_ker N
      have hc : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) N.ker + 1 := by omega
      have hfix : ∀ v ∈ N.ker, ggLin (p := p) ι g.1 v = v := by
        intro v hv
        have he := LinearMap.mem_ker.mp hv
        exact sub_eq_zero.mp he
      have hsq : ∀ v, ggLin (p := p) ι g.1 (ggLin (p := p) ι g.1 v - v) = ggLin (p := p) ι g.1 v - v := by
        intro v
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hmv v)
        rw [← hc,map_smul,hGy]
      exact Subtype.ext (eq_one_of_fix_submodule_of_codim_le_one hNT ι (hH g.2) N.ker hc hfix hsq)
    exact (Nat.card_le_card_of_injective mu hinj).trans ((by
      rw [Nat.card_eq_fintype_card,ZMod.card_units] : Nat.card (ZMod p)ˣ = p - 1).le.trans hunits)
  · obtain ⟨z,hzF,hz⟩ : ∃ z ∈ F, z ∉ Submodule.span (ZMod p) {y} := by
      by_contra hn
      push Not at hn
      exact hline (le_antisymm (fun z hz => hn z hz) hyle)
    have hspan : Submodule.span (ZMod p) {y,z} = F := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact Submodule.span_le.mpr (by intro v hv; rcases hv with rfl | rfl; exact hyF; exact hzF)
      · have he : Submodule.span (ZMod p) {y,z} = Submodule.span (ZMod p) {y} ⊔ Submodule.span (ZMod p) {z} := by
          rw [← Submodule.span_union]; congr 1
        rw [he,Submodule.finrank_sup_span_singleton hz,finrank_span_singleton hy]
        exact hF
    exact hplane U F z hz hspan.symm mu hm hu hcodim



theorem card_weyl_commutant_three_le_six {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hNT : GGNoTransvection 3 Bs) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod 3))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := 3) ι g.1 (v - a i v • h i) =
      ggLin (p := 3) ι g.1 v - a i (ggLin (p := 3) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := 3) ι g.1 y = y)
    (hF : Module.finrank (ZMod 3) (LinearMap.pi a).ker ≤ 2) : Nat.card H ≤ 6 := by
  exact card_weyl_commutant_le_of_plane_bound (by decide : 3 ≠ 2) hNT ι H hH
    hM hC h a hpair hcomm y hy hay hGy hF 6 (by norm_num)
    (fun U F z hz hspan mu hm hu hc =>
      card_weyl_commutant_plane_le_six hNT ι H hH U F y z hy hz hspan mu hm hu hGy hc)

theorem card_plane_displacement_sign_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (U F : Submodule (ZMod p) V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span (ZMod p) {y}) (hF : F = Submodule.span (ZMod p) {y,z})
    (hmove : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v - v ∈ F)
    (hU : ∀ g : H, ∀ v ∈ U, ggLin (p := p) ι g.1 v = v)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ F) + 1)
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1) :
    Nat.card H ≤ 2 * p := by
  obtain ⟨l,a,d,c,A,B,D,hshape,hly,hlz,hay,haz,hdy,hdz⟩ :=
    exists_plane_action_coordinates ((ggLin (p := p) ι).comp H.subtype) U F y z hy hz hF 1
      (by simpa using hmove) (by simpa using hU) hGy hcodim
  have hshape1 : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v = v +
      (A g * a v + B g * d v) • y + (((c g : ZMod p) - 1) * a v) • z + (D g * d v) • z := by
    intro g v
    have hh := hshape g v
    simp only [MonoidHom.comp_apply,Subgroup.subtype_apply,MonoidHom.one_apply,
      Units.val_one,sub_self,zero_mul,zero_add,one_smul] at hh
    rw [hh]
    module
  have hc (g : H) : c g = 1 ∨ c g = -1 := by
    have hzval : ggLin (p := p) ι g.1 z = A g • y + (c g : ZMod p) • z := by
      rw [hshape1,haz,hdz]
      module
    have he := LinearEquiv.det_eq_of_displacement_mem_plane (ggLin (p := p) ι g.1) y z hy hz (A g)
      (c g : ZMod p) (Units.ne_zero _) (hGy g) hzval (by simpa only [hF] using hmove g)
    have hs : (c g : ZMod p) ^ 2 = 1 := by
      rw [← he]
      exact congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) (hdet g)
    exact Units.eq_or_eq_neg_of_sq_eq_sq (c g) 1
      (by apply Units.ext; simpa using hs)
  exact card_plane_kernel_le_two_mul_prime hNT ι H hH y z hy a d A B c D
    hshape1 hay hdy haz hdz hc

theorem card_weyl_commutant_axis_in_coroot_sign_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hyU : y ∈ Submodule.span (ZMod p) (Set.range h))
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1) :
    Nat.card H ≤ 2 * p := by
  classical
  let F : Submodule (ZMod p) V := (LinearMap.pi a).ker
  let U := Submodule.span (ZMod p) (Set.range h)
  let T : H →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp H.subtype
  obtain ⟨mu,hmu,hcor⟩ := exists_weyl_commutant_character hp2 hM hC h a hpair T hcomm
  have hu (g : H) : ∀ v ∈ U, T g v = (mu g : ZMod p) • v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i,rfl⟩; exact hcor g i
    · simp
    · intro v w _ _ hv hw; simp only [map_add,hv,hw,smul_add]
    · intro c v _ hv; rw [map_smul,hv]; module
  have hmu1 (g : H) : mu g = 1 := by
    have he := hu g y hyU
    rw [show T g y = y from hGy g] at he
    have hh : ((mu g : ZMod p) - 1) • y = 0 := by rw [sub_smul,← he,one_smul,sub_self]
    apply Units.ext
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hy)
  have hm (g : H) (v : V) : ggLin (p := p) ι g.1 v - v ∈ F := by
    simp only [F,LinearMap.mem_ker,LinearMap.pi_apply,funext_iff,Pi.zero_apply]
    intro i
    rw [map_sub,show a i (ggLin (p := p) ι g.1 v) = (mu g : ZMod p) * a i v from hmu g i v,
      hmu1 g,Units.val_one,one_mul,sub_self]
  have hu1 (g : H) : ∀ v ∈ U, ggLin (p := p) ι g.1 v = v := by
    intro v hv
    simpa only [T,MonoidHom.comp_apply,Subgroup.subtype_apply,hmu1 g,Units.val_one,one_smul] using hu g v hv
  have hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ F) + 1 :=
    finrank_le_sup_coroot_rootker_add_one hp2 hM hC h a hpair
  have hyF : y ∈ F := by
    simpa only [F,LinearMap.mem_ker,LinearMap.pi_apply,funext_iff,Pi.zero_apply] using hay
  have hyle : Submodule.span (ZMod p) {y} ≤ F := Submodule.span_le.mpr (by simpa using hyF)
  by_cases hline : F = Submodule.span (ZMod p) {y}
  · have hinj : Function.Injective mu := (injective_iff_map_eq_one _).mpr fun g _ => by
      have hmv : ∀ v, ggLin (p := p) ι g.1 v - v ∈ Submodule.span (ZMod p) {y} := by
        intro v; simpa only [hline] using hm g v
      let N : V →ₗ[ZMod p] V := (ggLin (p := p) ι g.1).toLinearMap - LinearMap.id
      have hn : N.range ≤ Submodule.span (ZMod p) {y} := by
        rintro _ ⟨v,rfl⟩; exact hmv v
      have hr := Submodule.finrank_mono hn
      rw [finrank_span_singleton hy] at hr
      have hsum := LinearMap.finrank_range_add_finrank_ker N
      have hc : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) N.ker + 1 := by omega
      have hfix : ∀ v ∈ N.ker, ggLin (p := p) ι g.1 v = v := by
        intro v hv
        exact sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
      have hsq : ∀ v, ggLin (p := p) ι g.1 (ggLin (p := p) ι g.1 v - v) =
          ggLin (p := p) ι g.1 v - v := by
        intro v
        obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (hmv v)
        rw [← hr,map_smul,hGy g]
      exact Subtype.ext (eq_one_of_fix_submodule_of_codim_le_one hNT ι (hH g.2) N.ker hc hfix hsq)
    have hh := Nat.card_le_card_of_injective mu hinj
    rw [Nat.card_eq_fintype_card (α := (ZMod p)ˣ),ZMod.card_units] at hh
    omega
  · obtain ⟨z,hzF,hz⟩ : ∃ z ∈ F, z ∉ Submodule.span (ZMod p) {y} := by
      by_contra hn
      push Not at hn
      exact hline (le_antisymm (fun z hz => hn z hz) hyle)
    have hspan : Submodule.span (ZMod p) {y,z} = F := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact Submodule.span_le.mpr (by intro v hv; rcases hv with rfl | rfl; exact hyF; exact hzF)
      · have he : Submodule.span (ZMod p) {y,z} =
            Submodule.span (ZMod p) {y} ⊔ Submodule.span (ZMod p) {z} := by
          rw [← Submodule.span_union]; congr 1
        rw [he,Submodule.finrank_sup_span_singleton hz,finrank_span_singleton hy]
        exact hF
    exact card_plane_displacement_sign_le hNT ι H hH U F y z hy hz hspan.symm
      hm hu1 hGy hcodim hdet

private theorem card_weyl_commutant_plane_coprime_sign_le
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (U F : Submodule (ZMod p) V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span (ZMod p) {y}) (hF : F = Submodule.span (ZMod p) {y,z})
    (mu : H →* (ZMod p)ˣ)
    (hmove : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v - (mu g : ZMod p) • v ∈ F)
    (hU : ∀ g : H, ∀ v ∈ U, ggLin (p := p) ι g.1 v = (mu g : ZMod p) • v)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ F) + 1)
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1)
    (hcop : Nat.Coprime (p - 1) (2 * Module.finrank (ZMod p) V - 3)) :
    Nat.card H ≤ 2 * p := by
  classical
  let T : H →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp H.subtype
  obtain ⟨l,a,d,c,A,B,D,hshape,hly,hlz,hay,haz,hdy,hdz⟩ :=
    exists_plane_action_coordinates T U F y z hy hz hF mu hmove hU hGy hcodim
  have hshape' : ∀ g : H, ∀ v, ggLin (p := p) ι g.1 v = (mu g : ZMod p) • v +
      (((1 - (mu g : ZMod p)) * l v + A g * a v + B g * d v) • y) +
        (((c g : ZMod p) - (mu g : ZMod p)) * a v + D g * d v) • z := hshape
  have hTz (g : H) : T g z = A g • y + (c g : ZMod p) • z := by
    change ggLin (p := p) ι g.1 z = _
    rw [hshape',hlz,haz,hdz]
    module
  have hd (g : H) : ((T g).det : ZMod p) =
      (c g : ZMod p) * (mu g : ZMod p) ^ (Module.finrank (ZMod p) V - 2) :=
    LinearEquiv.det_eq_of_scalar_quotient_of_fix_plane (T g) y z hy hz (A g) (c g) (mu g)
      (Units.ne_zero _) (hGy g) (hTz g) (by simpa only [T,MonoidHom.comp_apply,Subgroup.subtype_apply,hF] using hmove g)
  let N := (mu.prod c).ker
  have hzero (g : H) (hmg : mu g = 1) (hcg : c g = 1) (hd0 : d = 0) : g = 1 := by
    have hlin : ∀ v, ggLin (p := p) ι g.1 v = v + (A g * a v) • y := by
      intro v
      rw [hshape',hmg,hcg,hd0]
      simp only [Units.val_one,sub_self,zero_mul,LinearMap.zero_apply,mul_zero,
        add_zero,zero_add,one_smul,zero_smul]
    by_cases hA : A g = 0
    · apply Subtype.ext
      apply ggLin_injective (p := p) ι
      ext v
      rw [hlin,hA,zero_mul,zero_smul,add_zero]
      change v = ggLin (p := p) ι (1 : MulAut Bs) v
      rw [map_one]
      rfl
    · have hane : a ≠ 0 := by intro h; simp [h] at haz
      have he : A g • a ≠ 0 := smul_ne_zero hA hane
      exact (ggNoTransvection_of_le_automizer hNT hH g.1 g.2
        (ggIsTransvection_of_apply ι hy he (by simp [hay])
          (by intro v; simpa [LinearMap.smul_apply,smul_eq_mul] using hlin v))).elim
  by_cases hnt : Nontrivial ↥N
  · have hd0 : d ≠ 0 := by
      intro hd0
      let : Nontrivial N := hnt
      obtain ⟨u,hu⟩ := exists_ne (1 : N)
      apply hu
      apply Subtype.ext
      exact hzero u.1 (congrArg Prod.fst (MonoidHom.mem_ker.mp u.2))
        (congrArg Prod.snd (MonoidHom.mem_ker.mp u.2)) hd0
    obtain ⟨v,hv⟩ : ∃ v, d v ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (LinearMap.ext h)
    let v0 := (d v)⁻¹ • v
    have hdv : d v0 = 1 := by simp [v0,hv]
    have hsc : ∀ g : H, mu g = c g ^ 2 :=
      plane_scalar_eq_sq_of_nontrivial_kernel hNT ι H hH y z v0 hy l a d mu c A B D
        hshape' hly hlz hay haz hdy hdz hdv hnt
    have hm1 : ∀ g : H, mu g = 1 := by
      intro g
      rw [hsc g]
      have hdg : (T g).det = c g * (mu g) ^ (Module.finrank (ZMod p) V - 2) :=
        Units.ext (by simpa using hd g)
      have hd2 := hdet g
      change (T g).det ^ 2 = 1 at hd2
      rw [hdg,hsc g,mul_pow,← pow_mul] at hd2
      have hdim2 : 2 ≤ Module.finrank (ZMod p) V := by
        have hspan : F = Submodule.span (ZMod p) {y} ⊔ Submodule.span (ZMod p) {z} := by
          rw [hF,← Submodule.span_union]; congr 1
        have hr : Module.finrank (ZMod p) F = 2 := by
          rw [hspan,Submodule.finrank_sup_span_singleton hz,finrank_span_singleton hy]
        simpa only [hr] using Submodule.finrank_le F
      have hs : (c g ^ 2) ^ (2 * Module.finrank (ZMod p) V - 3) = 1 := by
        rw [show 2 * Module.finrank (ZMod p) V - 3 =
          1 + (Module.finrank (ZMod p) V - 2) * 2 by omega,pow_add,pow_one]
        exact hd2
      have hpow : (c g ^ 2) ^ (p - 1) = 1 := by
        have hcPow : (c g) ^ (p - 1) = 1 := by
          apply Units.ext
          simpa using (ZMod.pow_card_sub_one_eq_one (p := p) (c g).ne_zero)
        rw [← pow_mul,Nat.mul_comm,pow_mul,hcPow,one_pow]
      exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hpow,hs⟩
    exact card_plane_displacement_sign_le hNT ι H hH U F y z hy hz hF
      (by simpa only [hm1,Units.val_one,one_smul] using hmove)
      (by simpa only [hm1,Units.val_one,one_smul] using hU) hGy hcodim hdet
  · have hu : Subsingleton N := not_nontrivial_iff_subsingleton.mp hnt
    have hpairinj : Function.Injective (mu.prod c) := (injective_iff_map_eq_one _).mpr fun g hg => by
      have he : (⟨g,MonoidHom.mem_ker.mpr hg⟩ : N) = 1 := @Subsingleton.elim _ hu _ _
      exact congrArg Subtype.val he
    let delta : H →* (ZMod p)ˣ := LinearEquiv.det.comp T
    have hinj : Function.Injective (mu.prod delta) := (injective_iff_map_eq_one _).mpr fun g hg => by
      have hmg : mu g = 1 := congrArg Prod.fst hg
      have hdg : delta g = 1 := congrArg Prod.snd hg
      have hcg : c g = 1 := by
        apply Units.ext
        have he := hd g
        have hd1 : ((T g).det : ZMod p) = 1 := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hdg
        simpa only [hmg,Units.val_one,one_pow,mul_one,hd1] using he.symm
      apply hpairinj
      change (mu g,c g) = (mu 1,c 1)
      rw [mu.map_one,c.map_one]
      exact Prod.ext hmg hcg
    let S := Subgroup.zpowers (-1 : (ZMod p)ˣ)
    have hdS (g : H) : delta g ∈ S := by
      have hs : delta g = 1 ∨ delta g = -1 := Units.eq_or_eq_neg_of_sq_eq_sq (delta g) 1
        (by change (T g).det ^ 2 = 1 ^ 2; simpa only [T,MonoidHom.comp_apply,Subgroup.subtype_apply,one_pow] using hdet g)
      rcases hs with hs|hs
      · rw [hs]; exact S.one_mem
      · rw [hs]; exact Subgroup.mem_zpowers _
    let q : H → (ZMod p)ˣ × S := fun g => (mu g,⟨delta g,hdS g⟩)
    have hq : Function.Injective q := by
      intro g k hgk
      apply hinj
      change (mu g,delta g) = (mu k,delta k)
      exact Prod.ext (congrArg (fun x : (ZMod p)ˣ × S => x.1) hgk)
        (congrArg (fun x : (ZMod p)ˣ × S => x.2.1) hgk)
    have hcard : Nat.card S ≤ 2 := (Nat.card_zpowers _).trans_le
      (orderOf_le_of_pow_eq_one (by norm_num) (by simp))
    calc Nat.card H ≤ Nat.card ((ZMod p)ˣ × S) := Nat.card_le_card_of_injective q hq
      _ = (p - 1) * Nat.card S := by
        rw [Nat.card_prod,Nat.card_eq_fintype_card (α := (ZMod p)ˣ),ZMod.card_units]
      _ ≤ (p - 1) * 2 := Nat.mul_le_mul_left _ hcard
      _ ≤ 2 * p := by omega



private theorem card_weyl_commutant_plane_five_sign_le_ten
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)] {Bs : Subgroup G} (hNT : GGNoTransvection 5 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 5) V] [Module.Finite (ZMod 5) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    (U F : Submodule (ZMod 5) V) (y z : V) (hy : y ≠ 0)
    (hz : z ∉ Submodule.span (ZMod 5) {y}) (hF : F = Submodule.span (ZMod 5) {y,z})
    (mu : H →* (ZMod 5)ˣ)
    (hmove : ∀ g : H, ∀ v, ggLin (p := 5) ι g.1 v - (mu g : ZMod 5) • v ∈ F)
    (hU : ∀ g : H, ∀ v ∈ U, ggLin (p := 5) ι g.1 v = (mu g : ZMod 5) • v)
    (hGy : ∀ g : H, ggLin (p := 5) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod 5) V ≤ Module.finrank (ZMod 5) ↥(U ⊔ F) + 1)
    (hdet : ∀ g : H, (ggLin (p := 5) ι g.1).det ^ 2 = 1) : Nat.card H ≤ 10 := by
  have hdim2 : 2 ≤ Module.finrank (ZMod 5) V := by
    have hspan : F = Submodule.span (ZMod 5) {y} ⊔ Submodule.span (ZMod 5) {z} := by
      rw [hF,← Submodule.span_union]; congr 1
    have hr : Module.finrank (ZMod 5) F = 2 := by
      rw [hspan,Submodule.finrank_sup_span_singleton hz,finrank_span_singleton hy]
    simpa only [hr] using Submodule.finrank_le F
  have hodd : Odd (2 * Module.finrank (ZMod 5) V - 3) := by
    refine ⟨Module.finrank (ZMod 5) V - 2,?_⟩
    omega
  have hcop : Nat.Coprime (5 - 1) (2 * Module.finrank (ZMod 5) V - 3) := by
    change Nat.Coprime (2 ^ 2) _
    exact (Nat.coprime_two_left.mpr hodd).pow_left 2
  exact card_weyl_commutant_plane_coprime_sign_le hNT ι H hH U F y z hy hz hF mu
    hmove hU hGy hcodim hdet hcop

theorem card_weyl_commutant_five_sign_le_ten {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)] {Bs : Subgroup G}
    (hNT : GGNoTransvection 5 Bs) {V : Type} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod 5) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod 5))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := 5) ι g.1 (v - a i v • h i) =
      ggLin (p := 5) ι g.1 v - a i (ggLin (p := 5) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := 5) ι g.1 y = y)
    (hF : Module.finrank (ZMod 5) (LinearMap.pi a).ker ≤ 2)
    (hdet : ∀ g : H, (ggLin (p := 5) ι g.1).det ^ 2 = 1) : Nat.card H ≤ 10 := by
  exact card_weyl_commutant_le_of_plane_bound (by decide : 5 ≠ 2) hNT ι H hH
    hM hC h a hpair hcomm y hy hay hGy hF 10 (by norm_num)
    (fun U F z hz hspan mu hm hu hc =>
      card_weyl_commutant_plane_five_sign_le_ten hNT ι H hH U F y z hy hz hspan mu hm hu hGy hc hdet)

theorem card_weyl_commutant_coprime_sign_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hNT : GGNoTransvection p Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime (p - 1) (2 * Module.finrank (ZMod p) V - 3)) :
    Nat.card H ≤ 2 * p := by
  exact card_weyl_commutant_le_of_plane_bound hp2 hNT ι H hH
    hM hC h a hpair hcomm y hy hay hGy hF (2 * p) (by omega)
    (fun U F z hz hspan mu hm hu hc =>
      card_weyl_commutant_plane_coprime_sign_le hNT ι H hH U F y z hy hz hspan mu hm hu hGy hc hdet hcop)

theorem finrank_le_coroot_line_add_one_of_full_rank {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p)) (y : V) (hy : y ≠ 0)
    (hay : ∀ i, a i y = 0)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {y}) + 1 := by
  classical
  let F := (LinearMap.pi a).ker
  let U := Submodule.span (ZMod p) (Set.range h)
  let Y := Submodule.span (ZMod p) {y}
  have htop : U ⊔ F = ⊤ := sup_coroot_rootker_eq_top_of_full_rank h a hpair hfull
  have hyF : y ∈ F := by
    simpa only [F,LinearMap.mem_ker,LinearMap.pi_apply,funext_iff,Pi.zero_apply] using hay
  have hyle : Y ≤ F := Submodule.span_le.mpr (by simpa using hyF)
  have hdim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ Y) + 1 := by
    have hF0 : Module.finrank (ZMod p) F ≤ 2 := hF
    have hi := Submodule.finrank_sup_add_finrank_inf_eq U F
    have hiY := Submodule.finrank_sup_add_finrank_inf_eq U Y
    have hmono := Submodule.finrank_mono (show U ⊓ Y ≤ U ⊓ F from inf_le_inf_left U hyle)
    have hYrank : Module.finrank (ZMod p) Y = 1 := finrank_span_singleton hy
    rw [htop] at hi
    simp only [finrank_top] at hi
    omega
  exact hdim

theorem card_weyl_commutant_coroot_line_le_units_mul_card_det {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {y}) + 1) :
    Nat.card H ≤ (p - 1) * Nat.card (LinearEquiv.det.comp
      ((ggLin (p := p) ι).comp H.subtype)).range := by
  classical
  let U := Submodule.span (ZMod p) (Set.range h)
  let T : H →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp H.subtype
  obtain ⟨mu,hmu,hcor⟩ := exists_weyl_commutant_character hp2 hM hC h a hpair T hcomm
  let Y := Submodule.span (ZMod p) {y}
  have hUfix (g : H) (hg : mu g = 1) : ∀ u ∈ U, T g u = u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i,rfl⟩; simpa [hg] using hcor g i
    · simp
    · intro u v _ _ hu hv; rw [map_add,hu,hv]
    · intro c u _ hu; rw [map_smul,hu]
  let d : H →* (ZMod p)ˣ := LinearEquiv.det.comp T
  have hinj : Function.Injective (mu.prod d) := (injective_iff_map_eq_one _).mpr fun g hg => by
    have hmg : mu g = 1 := congrArg Prod.fst hg
    have hdg : (T g).det = 1 := congrArg Prod.snd hg
    have hSY : ∀ v ∈ U ⊔ Y, ggLin (p := p) ι g.1 v = v := by
      intro v hv
      change T g v = v
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add,hUfix g hmg u hu]
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
      rw [← hc,map_smul]
      change u + c • T g y = u + c • y
      rw [show T g y = y from hGy g]
    have hdim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) ↥(U ⊔ Y) + 1 := hcodim
    exact Subtype.ext (eq_one_of_fix_submodule_of_det_one hNT ι (hH g.2) (U ⊔ Y) hdim hSY hdg)
  let q : H → (ZMod p)ˣ × d.range := fun g => (mu g,⟨d g, g, rfl⟩)
  have hq : Function.Injective q := by
    intro g k hgk
    apply hinj
    change (mu g, d g) = (mu k, d k)
    exact Prod.ext (congrArg (fun v : (ZMod p)ˣ × d.range => v.1) hgk)
      (congrArg (fun v : (ZMod p)ˣ × d.range => (v.2 : (ZMod p)ˣ)) hgk)
  calc Nat.card H ≤ Nat.card ((ZMod p)ˣ × d.range) := Nat.card_le_card_of_injective q hq
    _ = (p - 1) * Nat.card d.range := by
      rw [Nat.card_prod,Nat.card_eq_fintype_card,ZMod.card_units]


theorem card_weyl_commutant_full_rank_le_units_mul_card_det {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Nat.card H ≤ (p - 1) * Nat.card (LinearEquiv.det.comp
      ((ggLin (p := p) ι).comp H.subtype)).range := by
  have hdim := finrank_le_coroot_line_add_one_of_full_rank h a hpair y hy hay hF hfull
  exact card_weyl_commutant_coroot_line_le_units_mul_card_det hp2 hNT ι H hH hM hC
    h a hpair hcomm y hGy hdim

theorem card_weyl_commutant_full_rank_le_square {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (H : Subgroup (MulAut ↥Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Nat.card H ≤ (p - 1)^2 := by
  have hbound := card_weyl_commutant_full_rank_le_units_mul_card_det hp2 hNT ι H hH
    hM hC h a hpair hcomm y hy hay hGy hF hfull
  have hdet : Nat.card (LinearEquiv.det.comp ((ggLin (p := p) ι).comp H.subtype)).range ≤ p - 1 := by
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (by
      rw [Nat.card_eq_fintype_card,ZMod.card_units])
  exact (hbound.trans (Nat.mul_le_mul_left (p - 1) hdet)).trans_eq (by ring)

theorem card_weyl_commutant_coroot_line_sign_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hcodim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {y}) + 1)
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1) :
    Nat.card H ≤ 2 * (p - 1) := by
  have hbound := card_weyl_commutant_coroot_line_le_units_mul_card_det hp2 hNT ι H hH
    hM hC h a hpair hcomm y hGy hcodim
  let d : H →* (ZMod p)ˣ := LinearEquiv.det.comp ((ggLin (p := p) ι).comp H.subtype)
  have hinc : d.range ≤ Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
    rintro _ ⟨g,rfl⟩
    have hs : d g = 1 ∨ d g = -1 := Units.eq_or_eq_neg_of_sq_eq_sq (d g) 1
      (by change (ggLin (p := p) ι g.1).det ^ 2 = 1 ^ 2; simpa only [one_pow] using hdet g)
    rcases hs with h|h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hcard : Nat.card d.range ≤ 2 := by
    exact (Subgroup.card_le_of_le hinc).trans ((Nat.card_zpowers _).trans_le
      (orderOf_le_of_pow_eq_one (by norm_num) (by simp)))
  exact (hbound.trans (Nat.mul_le_mul_left (p - 1) hcard)).trans_eq (by omega)


theorem card_weyl_commutant_full_rank_sign_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive Bs ≃+ V) (H : Subgroup (MulAut Bs)) (hH : H ≤ ggAutomizer ⊤ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    (hcomm : ∀ g : H, ∀ i v, ggLin (p := p) ι g.1 (v - a i v • h i) =
      ggLin (p := p) ι g.1 v - a i (ggLin (p := p) ι g.1 v) • h i)
    (y : V) (hy : y ≠ 0) (hay : ∀ i, a i y = 0)
    (hGy : ∀ g : H, ggLin (p := p) ι g.1 y = y)
    (hF : Module.finrank (ZMod p) (LinearMap.pi a).ker ≤ 2)
    (hfull : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ)
    (hdet : ∀ g : H, (ggLin (p := p) ι g.1).det ^ 2 = 1) :
    Nat.card H ≤ 2 * (p - 1) := by
  have hdim := finrank_le_coroot_line_add_one_of_full_rank h a hpair y hy hay hF hfull
  exact card_weyl_commutant_coroot_line_sign_le hp2 hNT ι H hH hM hC h a hpair hcomm
    y hGy hdim hdet

end CFSG.StandardType
