module

public import CFSG.Quasithin.Recognition.G112A2D6ZornAut

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open

@[expose] def z6TrL : z6O →ₗ[ZMod 2] ZMod 2 where
  toFun := z6Tr
  map_add' x y := by
    simp only [z6Tr, Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c x := by
    simp only [z6Tr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] def z6O0 : Submodule (ZMod 2) z6O := LinearMap.ker z6TrL

theorem z6_mem_O0 {x : z6O} : x ∈ z6O0 ↔ z6Tr x = 0 :=
  LinearMap.mem_ker

theorem z6_tr_sub (a b : z6O) : z6Tr (a - b) = z6Tr a - z6Tr b := by
  obtain ⟨p, u, v, q⟩ := a
  obtain ⟨p', u', v', q'⟩ := b
  simp only [z6Tr, Prod.mk_sub_mk]
  ring

theorem z6_tr_add (a b : z6O) : z6Tr (a + b) = z6Tr a + z6Tr b := by
  obtain ⟨p, u, v, q⟩ := a
  obtain ⟨p', u', v', q'⟩ := b
  simp only [z6Tr, Prod.mk_add_mk]
  ring

theorem z6_tr_smul (c : ZMod 2) (a : z6O) : z6Tr (c • a) = c * z6Tr a := by
  obtain ⟨p, u, v, q⟩ := a
  simp only [z6Tr, Prod.smul_mk, smul_eq_mul]
  ring

theorem z6_nrm_add (x y : z6O) : z6Nrm (x + y) = z6Nrm x + z6Nrm y + z6Pol x y := by
  obtain ⟨a, u, v, b⟩ := x
  obtain ⟨a', u', v', b'⟩ := y
  simp only [z6Nrm, z6Pol, Prod.mk_add_mk, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem z6_nrm_one : z6Nrm z6One = 1 := by
  simp [z6Nrm, z6One]

theorem z6_pol_one (x : z6O) : z6Pol x z6One = z6Tr x := by
  obtain ⟨a, u, v, b⟩ := x
  simp [z6Pol, z6One, z6Tr]

theorem z6_pol_zero_right (x : z6O) : z6Pol x 0 = 0 := by
  obtain ⟨a, u, v, b⟩ := x
  simp [z6Pol]

theorem z6_pol_sub_left (x x' y : z6O) : z6Pol (x - x') y = z6Pol x y - z6Pol x' y := by
  have h := z6_pol_add_left (x - x') x' y
  rw [sub_add_cancel] at h
  linear_combination -h

theorem z6_pol_sub_right (x y y' : z6O) : z6Pol x (y - y') = z6Pol x y - z6Pol x y' := by
  rw [z6_pol_comm, z6_pol_sub_left, z6_pol_comm y, z6_pol_comm y']

theorem z6_pol_add_right (x y y' : z6O) : z6Pol x (y + y') = z6Pol x y + z6Pol x y' := by
  rw [z6_pol_comm, z6_pol_add_left, z6_pol_comm y, z6_pol_comm y']

theorem z6_sub_twice (a b : z6O) : a - b - (b - a) = 0 := by
  have h : a - b - (b - a) = (a - b) + (a - b) := by abel
  rw [h, z6_add_self]

@[expose] def z6NL (g : z6O ≃ₗ[ZMod 2] z6O) : z6O →ₗ[ZMod 2] z6O where
  toFun x := g x - x
  map_add' x y := by
    simp only [map_add]
    abel
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply, smul_sub]

theorem z6NL_apply (g : z6O ≃ₗ[ZMod 2] z6O) (x : z6O) : z6NL g x = g x - x :=
  rfl

theorem z6t_rank_nullity {W X : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X] (f : W →ₗ[ZMod 2] X) :
    Module.finrank (ZMod 2) (LinearMap.range f) + Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) W :=
  LinearMap.finrank_range_add_finrank_ker f



theorem z6t_finrank_span1 {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {v : W} (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 :=
  finrank_span_singleton hv

theorem z6t_finrank_mono {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {U U' : Submodule (ZMod 2) W} (h : U ≤ U') :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) U' :=
  Submodule.finrank_mono h

theorem z6t_finrank_le {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (U : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) W :=
  Submodule.finrank_le U

theorem z6t_finrank_sup_inf {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (U U' : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) ↥(U ⊔ U') + Module.finrank (ZMod 2) ↥(U ⊓ U') =
      Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) U' :=
  Submodule.finrank_sup_add_finrank_inf_eq U U'

theorem z6t_finrank_orth {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {B : LinearMap.BilinForm (ZMod 2) W} (hB : B.Nondegenerate)
    (U : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) (B.orthogonal U) =
      Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) U :=
  LinearMap.BilinForm.finrank_orthogonal hB U

theorem z6t_orth_orth {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {B : LinearMap.BilinForm (ZMod 2) W} (hB : B.Nondegenerate)
    (hB₀ : B.IsRefl) (U : Submodule (ZMod 2) W) : B.orthogonal (B.orthogonal U) = U :=
  LinearMap.BilinForm.orthogonal_orthogonal hB hB₀ U

theorem z6s_end (f : z6O →ₗ[ZMod 2] z6O) :
    Module.finrank (ZMod 2) (LinearMap.range f) + Module.finrank (ZMod 2) (LinearMap.ker f) = 8 :=
  (@z6t_rank_nullity z6O z6O _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) _ (inferInstance : Module (ZMod 2) z6O) f).trans
    z6_finrank

theorem z6s_Z2 (f : z6O →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range f) + Module.finrank (ZMod 2) (LinearMap.ker f) = 8 :=
  (@z6t_rank_nullity z6O (ZMod 2) _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) _ (inferInstance : Module (ZMod 2) (ZMod 2)) f).trans
    z6_finrank

theorem z6s_le (U : Submodule (ZMod 2) z6O) : Module.finrank (ZMod 2) U ≤ 8 :=
  (@z6t_finrank_le z6O _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) U).trans z6_finrank.le

theorem z6s_mono {U U' : Submodule (ZMod 2) z6O} (h : U ≤ U') :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) U' :=
  @z6t_finrank_mono z6O _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) U U' h

theorem z6s_orth (U : Submodule (ZMod 2) z6O) :
    Module.finrank (ZMod 2) (z6B.orthogonal U) = 8 - Module.finrank (ZMod 2) U := by
  have h : Module.finrank (ZMod 2) (z6B.orthogonal U) =
      Module.finrank (ZMod 2) z6O - Module.finrank (ZMod 2) U :=
    @z6t_finrank_orth z6O _ (inferInstance : Module (ZMod 2) z6O)
      (inferInstance : Module.Finite (ZMod 2) z6O) z6B z6B_nondegenerate U
  rw [h, z6_finrank]

theorem z6s_orth_orth (U : Submodule (ZMod 2) z6O) : z6B.orthogonal (z6B.orthogonal U) = U :=
  @z6t_orth_orth z6O _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) z6B z6B_nondegenerate z6B_isRefl U

theorem z6s_span1 {v : z6O} (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 :=
  @z6t_finrank_span1 z6O _ (inferInstance : Module (ZMod 2) z6O) v hv

theorem z6s_sup_inf (U U' : Submodule (ZMod 2) z6O) :
    Module.finrank (ZMod 2) ↥(U ⊔ U') + Module.finrank (ZMod 2) ↥(U ⊓ U') =
      Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) U' :=
  @z6t_finrank_sup_inf z6O _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) U U'

theorem z6_four_sum : ∀ ne nz nz' bez bez' bzz' : ZMod 2,
    ne + (ne + nz + bez) + (ne + nz' + bez') + (ne + (nz + nz' + bzz') + (bez + bez')) = bzz' := by
  decide +kernel

theorem z6_zmod2_ne_one (c : ZMod 2) (h : c ≠ 1) : c = 0 := by
  revert c
  decide +kernel

theorem z6s_rank_V {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (f : z6O →ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (LinearMap.range f) + Module.finrank (ZMod 2) (LinearMap.ker f) = 8 :=
  (@z6t_rank_nullity z6O V _ (inferInstance : Module (ZMod 2) z6O)
    (inferInstance : Module.Finite (ZMod 2) z6O) _ (inferInstance : Module (ZMod 2) V) f).trans
    z6_finrank

theorem z6_pi_n_ker {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (n : z6O →ₗ[ZMod 2] z6O)
    (π : z6O →ₗ[ZMod 2] V) (hRO : LinearMap.range n ≤ z6O0)
    (hπk : ∀ x, z6Tr x = 0 → (π x = 0 ↔ ∃ c : ZMod 2, x = (c, 0, 0, c)))
    (y : z6O) (hy : π (n y) = 0) : ∃ c : ZMod 2, n y = c • z6One := by
  obtain ⟨c, hc⟩ := (hπk (n y) (z6_mem_O0.mp (hRO ⟨y, rfl⟩))).mp hy
  exact ⟨c, by rw [z6_smul_one]; exact hc⟩

theorem z6_thmZ_tail {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (g : z6O ≃ₗ[ZMod 2] z6O) (n : z6O →ₗ[ZMod 2] z6O) (hn : ∀ x, n x = g x - x)
    (π : z6O →ₗ[ZMod 2] V)
    (hπk : ∀ x, z6Tr x = 0 → (π x = 0 ↔ ∃ c : ZMod 2, x = (c, 0, 0, c)))
    (hdim : Module.finrank (ZMod 2) (Submodule.map π (Submodule.map n z6O0)) = 2)
    (hRO : LinearMap.range n ≤ z6O0) (hAB : LinearMap.ker n = z6B.orthogonal (LinearMap.range n))
    (hdimAR : Module.finrank (ZMod 2) (LinearMap.range n) +
      Module.finrank (ZMod 2) (LinearMap.ker n) = 8)
    (H1 : ∀ x, n x ≠ z6One) :
    ∃ u : z6O, g u = u ∧ z6Tr u = 1 ∧ z6Nrm u = 1 := by
  have hE : ∃ e, n e = 0 ∧ z6Tr e = 1 := by
    by_contra hcon
    push Not at hcon
    have htr0 : ∀ a, n a = 0 → z6Tr a = 0 := by
      intro a ha
      rcases z6_zmod2 (z6Tr a) with h | h
      · exact h
      · exact absurd h (hcon a ha)
    have h1mem : z6One ∈ z6B.orthogonal (LinearMap.ker n) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro a ha
      rw [LinearMap.mem_ker] at ha
      rw [z6B_apply, z6_pol_one, htr0 a ha]
    rw [hAB, z6s_orth_orth] at h1mem
    obtain ⟨x, hx⟩ := h1mem
    exact H1 x hx
  obtain ⟨e, he, het⟩ := hE
  have hRmap : LinearMap.range n = Submodule.map n z6O0 := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine Submodule.mem_map.mpr ⟨y - z6Tr y • e, ?_, ?_⟩
      · rw [z6_mem_O0, z6_tr_sub, z6_tr_smul, het, mul_one, sub_self]
      · rw [map_sub, map_smul, he, smul_zero]
        exact sub_zero _
    · rintro _ ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
  have hkerPn : LinearMap.ker (π.comp n) = LinearMap.ker n := by
    ext y
    constructor
    · intro hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hy
      obtain ⟨c, hc⟩ := z6_pi_n_ker n π hRO hπk y hy
      rw [LinearMap.mem_ker]
      rcases z6_zmod2 c with h0 | h1
      · rw [hc, h0, zero_smul]
      · exact absurd (by rw [hc, h1, one_smul]) (H1 y)
    · intro hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
  have hR2 : Module.finrank (ZMod 2) (LinearMap.range n) = 2 := by
    have hrk := z6s_rank_V (π.comp n)
    have hrange : LinearMap.range (π.comp n) = Submodule.map π (LinearMap.range n) :=
      LinearMap.range_comp n π
    have hq0 : Module.finrank (ZMod 2) (Submodule.map π (LinearMap.range n)) =
        Module.finrank (ZMod 2) (Submodule.map π (Submodule.map n z6O0)) :=
      congrArg (fun X : Submodule (ZMod 2) V => Module.finrank (ZMod 2) X)
        (congrArg (Submodule.map π) hRmap)
    have hq : Module.finrank (ZMod 2) (Submodule.map π (LinearMap.range n)) = 2 :=
      hq0.trans hdim
    have hr' : Module.finrank (ZMod 2) (LinearMap.range (π.comp n)) =
        Module.finrank (ZMod 2) (Submodule.map π (LinearMap.range n)) :=
      congrArg (fun X : Submodule (ZMod 2) V => Module.finrank (ZMod 2) X) hrange
    have hk : Module.finrank (ZMod 2) (LinearMap.ker (π.comp n)) =
        Module.finrank (ZMod 2) (LinearMap.ker n) :=
      congrArg (fun X : Submodule (ZMod 2) z6O => Module.finrank (ZMod 2) X) hkerPn
    omega
  have hZ0 : Module.finrank (ZMod 2) z6O0 = 7 := by
    have hrange : LinearMap.range z6TrL = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨(c, 0, 0, 0), by simp [z6TrL, z6Tr]⟩
    have h : Module.finrank (ZMod 2) (LinearMap.range z6TrL) +
        Module.finrank (ZMod 2) (LinearMap.ker z6TrL) = 8 := z6s_Z2 z6TrL
    rw [hrange] at h
    have h1 : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (ZMod 2)) = 1 := by
      simp
    have h2 : Module.finrank (ZMod 2) z6O0 = Module.finrank (ZMod 2) (LinearMap.ker z6TrL) := rfl
    omega
  have hA0 : 5 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊓ z6O0) := by
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊔ z6O0) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊓ z6O0) =
          Module.finrank (ZMod 2) (LinearMap.ker n) + Module.finrank (ZMod 2) z6O0 :=
      z6s_sup_inf (LinearMap.ker n) z6O0
    have h2 : Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊔ z6O0) ≤ 8 := z6s_le _
    omega
  have hex : ∃ z ∈ LinearMap.ker n ⊓ z6O0, ∃ z' ∈ LinearMap.ker n ⊓ z6O0, z6Pol z z' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : LinearMap.ker n ⊓ z6O0 ≤ z6B.orthogonal (LinearMap.ker n ⊓ z6O0) := by
      intro z' hz'
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      rw [z6B_apply]
      exact hcon z hz z' hz'
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊓ z6O0) ≤
        Module.finrank (ZMod 2) ↥(z6B.orthogonal (LinearMap.ker n ⊓ z6O0)) := z6s_mono hsub
    have h2 : Module.finrank (ZMod 2) ↥(z6B.orthogonal (LinearMap.ker n ⊓ z6O0)) =
        8 - Module.finrank (ZMod 2) ↥(LinearMap.ker n ⊓ z6O0) := z6s_orth _
    omega
  obtain ⟨z, hz, z', hz', hzz⟩ := hex
  have hpol : z6Pol z z' = 1 := by
    rcases z6_zmod2 (z6Pol z z') with h | h
    · exact absurd h hzz
    · exact h
  have hw : ∃ w ∈ LinearMap.ker n ⊓ z6O0, z6Nrm (e + w) = 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : z6Nrm (e + 0) = 0 := z6_zmod2_ne_one _ (hcon 0 (Submodule.zero_mem _))
    have h1 : z6Nrm (e + z) = 0 := z6_zmod2_ne_one _ (hcon z hz)
    have h2 : z6Nrm (e + z') = 0 := z6_zmod2_ne_one _ (hcon z' hz')
    have h3 : z6Nrm (e + (z + z')) = 0 :=
      z6_zmod2_ne_one _ (hcon (z + z') (Submodule.add_mem _ hz hz'))
    have hid : z6Nrm (e + 0) + z6Nrm (e + z) + z6Nrm (e + z') + z6Nrm (e + (z + z')) =
        z6Pol z z' := by
      rw [add_zero, z6_nrm_add e z, z6_nrm_add e z', z6_nrm_add e (z + z'), z6_nrm_add z z',
        z6_pol_add_right]
      exact z6_four_sum _ _ _ _ _ _
    rw [h0, h1, h2, h3, hpol] at hid
    exact absurd hid (by decide +kernel)
  obtain ⟨w, hwA, hwN⟩ := hw
  obtain ⟨hwker, hwO⟩ := Submodule.mem_inf.mp hwA
  have hwn : n w = 0 := LinearMap.mem_ker.mp hwker
  refine ⟨e + w, ?_, ?_, hwN⟩
  · have hu : n (e + w) = 0 := by rw [map_add, he, hwn, add_zero]
    rw [hn, sub_eq_zero] at hu
    exact hu
  · rw [z6_tr_add, het, z6_mem_O0.mp hwO, add_zero]

theorem z6_thmZ {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (g : z6O ≃ₗ[ZMod 2] z6O) (hg : z6Aut g) (hg2 : ∀ x, g (g x) = x)
    (π : z6O →ₗ[ZMod 2] V)
    (hπk : ∀ x, z6Tr x = 0 → (π x = 0 ↔ ∃ c : ZMod 2, x = (c, 0, 0, c)))
    (hdim : Module.finrank (ZMod 2) (Submodule.map π (Submodule.map (z6NL g) z6O0)) = 2) :
    ∃ u : z6O, g u = u ∧ z6Tr u = 1 ∧ z6Nrm u = 1 := by
  obtain ⟨n, hn_def⟩ : ∃ n : z6O →ₗ[ZMod 2] z6O, n = z6NL g := ⟨_, rfl⟩
  rw [← hn_def] at hdim
  have hn : ∀ x, n x = g x - x := fun x => by rw [hn_def]; rfl
  have hg1 : g z6One = z6One := z6_aut_one hg
  have htn : ∀ x, z6Tr (g x) = z6Tr x := fun x => (z6_aut_tr_nrm hg x).1
  have hNn : ∀ x, z6Nrm (g x) = z6Nrm x := fun x => (z6_aut_tr_nrm hg x).2
  have hβg : ∀ x y, z6Pol (g x) (g y) = z6Pol x y := by
    intro x y
    have h := z6_nrm_add x y
    have h' := z6_nrm_add (g x) (g y)
    rw [← map_add, hNn, hNn, hNn] at h'
    linear_combination h - h'
  have hsa : ∀ x y, z6Pol (n x) y = z6Pol x (n y) := by
    intro x y
    have h1 : z6Pol (g x) y = z6Pol x (g y) := by
      rw [← hβg (g x) y, hg2]
    rw [hn, hn, z6_pol_sub_left, z6_pol_sub_right, h1]
  have hnn : ∀ x, n (n x) = 0 := by
    intro x
    rw [hn (n x), hn x, map_sub, hg2]
    exact z6_sub_twice x (g x)
  have hRA : LinearMap.range n ≤ LinearMap.ker n := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hnn x)
  have hRO : LinearMap.range n ≤ z6O0 := by
    rintro _ ⟨x, rfl⟩
    rw [z6_mem_O0, hn, z6_tr_sub, htn, sub_self]
  have hAB : LinearMap.ker n = z6B.orthogonal (LinearMap.range n) := by
    ext m
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hm r hr
      obtain ⟨x, rfl⟩ := hr
      rw [z6B_apply, hsa, hm, z6_pol_zero_right]
    · intro hm
      have hnm : n m = 0 := by
        refine z6B_nondegenerate.2 (n m) (fun x => ?_)
        rw [z6B_apply, ← hsa]
        exact hm (n x) ⟨x, rfl⟩
      exact hnm
  have hdimAR : Module.finrank (ZMod 2) (LinearMap.range n) +
      Module.finrank (ZMod 2) (LinearMap.ker n) = 8 :=
    z6s_end n
  have hπ1 : π z6One = 0 := (hπk z6One (by decide +kernel)).2 ⟨1, rfl⟩
  have H1 : ∀ x, n x ≠ z6One := by
    intro x hx
    have hx' : g x - x = z6One := by rw [← hn]; exact hx
    have hgx : g x = z6One + x := sub_eq_iff_eq_add.mp hx'
    have htr : z6Tr x = 1 := by
      have h := hNn x
      rw [hgx, z6_nrm_add, z6_nrm_one, z6_pol_comm, z6_pol_one] at h
      have key : ∀ a b : ZMod 2, 1 + a + b = a → b = 1 := by decide +kernel
      exact key _ _ h
    have hAR1 : ∀ a, n a = 0 → n (quasithinZornMul x a) = a := by
      intro a ha
      have ha' : g a - a = 0 := by rw [← hn]; exact ha
      have hga : g a = a := sub_eq_zero.mp ha'
      rw [hn, hg x a, hgx, hga, z6_mul_add_left, z6_mul_one_left, add_sub_cancel_right]
    have hAeqR : LinearMap.ker n = LinearMap.range n := by
      refine le_antisymm ?_ hRA
      intro a ha
      rw [LinearMap.mem_ker] at ha
      exact ⟨_, hAR1 a ha⟩
    have hR4 : Module.finrank (ZMod 2) (LinearMap.range n) = 4 := by
      have h := hdimAR
      rw [hAeqR] at h
      omega
    have hR1 : Submodule.map π (LinearMap.range n) = Submodule.map π (Submodule.map n z6O0) := by
      apply le_antisymm
      · rintro _ ⟨r, ⟨y, rfl⟩, rfl⟩
        refine Submodule.mem_map.mpr ⟨n (y - z6Tr y • x), Submodule.mem_map.mpr
          ⟨y - z6Tr y • x, ?_, rfl⟩, ?_⟩
        · rw [z6_mem_O0, z6_tr_sub, z6_tr_smul, htr, mul_one, sub_self]
        · have hsplit : n y = n (y - z6Tr y • x) + z6Tr y • z6One := by
            rw [map_sub, map_smul, hx]
            abel
          show π (n (y - z6Tr y • x)) = π (n y)
          rw [hsplit, map_add, map_smul, hπ1, smul_zero, add_zero]
      · apply Submodule.map_mono
        rintro _ ⟨y, _, rfl⟩
        exact ⟨y, rfl⟩
    have hxne : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx
      exact absurd hx.symm (by decide +kernel)
    have hker1 : LinearMap.ker (π.comp n) ≤ LinearMap.ker n ⊔ Submodule.span (ZMod 2) {x} := by
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hy
      obtain ⟨c, hc⟩ := z6_pi_n_ker n π hRO hπk y hy
      have h0 : y - c • x ∈ LinearMap.ker n := by
        rw [LinearMap.mem_ker, map_sub, map_smul, hc, hx]
        exact sub_self _
      have hy' : y = (y - c • x) + c • x := by abel
      rw [hy']
      exact Submodule.add_mem_sup h0 (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x))
    have hfin1 : Module.finrank (ZMod 2) (LinearMap.ker (π.comp n)) ≤ 5 := by
      have h1 := z6s_mono hker1
      have h2 := z6s_sup_inf (LinearMap.ker n) (Submodule.span (ZMod 2) {x})
      have h3 := z6s_span1 hxne
      omega
    have hrk := z6s_rank_V (π.comp n)
    have hrange : LinearMap.range (π.comp n) = Submodule.map π (LinearMap.range n) :=
      LinearMap.range_comp n π
    have hq0 : Module.finrank (ZMod 2) (LinearMap.range (π.comp n)) =
        Module.finrank (ZMod 2) (Submodule.map π (Submodule.map n z6O0)) :=
      congrArg (fun X : Submodule (ZMod 2) V => Module.finrank (ZMod 2) X) (hrange.trans hR1)
    have hq : Module.finrank (ZMod 2) (LinearMap.range (π.comp n)) = 2 :=
      hq0.trans hdim
    omega
  exact z6_thmZ_tail g n hn π hπk hdim hRO hAB hdimAR H1

end CFSG.Quasithin.G112A2
