module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Pair

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem autAddHom_mul_eq_of_comm {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {g h : MulAut W}
    (hg : g * x = x * g) (hh : h * x = x * h)
    (hgh : (g * h) * x = x * (g * h)) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom (g * h) v = autAddHom g (autAddHom h v) := by
  letI := galoisModule hw2 x hx3 hfix
  rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix (g * h) hgh v,
    ← hGaloisLinearEquiv_apply hw2 x hx3 hfix g hg (autAddHom h v),
    ← hGaloisLinearEquiv_apply hw2 x hx3 hfix h hh v]
  rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix g h hg hh hgh]
  rfl

theorem autAddHom_one_apply {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom (1 : MulAut W) v = v := by
  letI := galoisModule hw2 x hx3 hfix
  rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix 1 (by group) v,
    hGaloisLinearEquiv_one hw2 x hx3 hfix (by group)]
  rfl

theorem autAddHom_pow_eq_of_comm {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {g : MulAut W} (hg : g * x = x * g)
    (n : ℕ) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    (autAddHom g)^[n] v = autAddHom (g ^ n) v := by
  letI := galoisModule hw2 x hx3 hfix
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, pow_zero]
      exact (autAddHom_one_apply hw2 x hx3 hfix v).symm
  | succ n ih =>
      have hgn : (g ^ n) * x = x * (g ^ n) := (show Commute g x from hg).pow_left n
      have hgh : (g * g ^ n) * x = x * (g * g ^ n) := by
        calc (g * g ^ n) * x = g * (g ^ n * x) := by group
          _ = g * (x * g ^ n) := by rw [hgn]
          _ = (g * x) * g ^ n := by group
          _ = (x * g) * g ^ n := by rw [hg]
          _ = x * (g * g ^ n) := by group
      rw [Function.iterate_succ_apply', ih,
        ← autAddHom_mul_eq_of_comm hw2 x hx3 hfix hg hgn hgh v, ← pow_succ']

theorem autAddHom_smul_eq_of_comm {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {g : MulAut W} (hg : g * x = x * g)
    (c : GaloisField 2 2) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom g (c • v) = c • autAddHom g v := by
  letI := galoisModule hw2 x hx3 hfix
  rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix g hg (c • v),
    ← hGaloisLinearEquiv_apply hw2 x hx3 hfix g hg v]
  exact map_smul (hGaloisLinearEquiv hw2 x hx3 hfix g hg) c v

private theorem pair_basis_and_U_aux {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ {G X H : Subgroup (MulAut W)}
      (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
      (hxgen : X = Subgroup.zpowers x)
      (hcommH : ∀ h ∈ H, h * x = x * h)
      {L M : LineOf (K := GaloisField 2 2) (V := Additive W)}
      {H0 : Subgroup ↥H} {d : ↥H}
      (hLM : L ≠ M) (hH0card : Nat.card H0 = 9)
      (hH0mem : ∀ h : ↥H, h ∈ H0 ↔
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = L ∧
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = M)
      (hcover : ∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0)
      (hdL : lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L = M)
      (hdM : lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M = L)
      {K0 : Subgroup ↥H} {vS : ↥K0} {dS : ↥H} {s0 : MulAut W}
      (hvSord : orderOf vS = 3) (hdS2 : dS * dS = 1) (hdSnot : dS ∉ K0)
      (hdvS : (dS : MulAut W) * (((vS : ↥K0) : ↥H) : MulAut W) * (dS : MulAut W)⁻¹ =
        (((vS ^ 2 : ↥K0) : ↥H) : MulAut W))
      (hs0sq : s0 * s0 = 1) (hs0x : s0 * x * s0⁻¹ = x ^ 2)
      (hs0vS : s0 * (((vS : ↥K0) : ↥H) : MulAut W) * s0⁻¹ =
        (((vS : ↥K0) : ↥H) : MulAut W))
      (hs0dS : s0 * (dS : MulAut W) * s0⁻¹ = (dS : MulAut W)),
    ∃ (l m : Additive W) (a : GaloisField 2 2) (U : Subgroup W),
      a ^ 3 = 1 ∧ a ≠ 1 ∧
      LinearIndependent (GaloisField 2 2) ![l, m] ∧
      (autAddHom ((((vS : ↥K0) : ↥H) : MulAut W))) l = a • l ∧
      (autAddHom ((((vS : ↥K0) : ↥H) : MulAut W))) m = a ^ 2 • m ∧
      (autAddHom (dS : MulAut W)) l = m ∧
      (autAddHom (dS : MulAut W)) m = l ∧
      (autAddHom s0) l = m ∧ (autAddHom s0) m = l ∧
      orderOf ((((vS : ↥K0) : ↥H) : MulAut W)) = 3 ∧
      (dS : MulAut W) * (dS : MulAut W) = 1 ∧ s0 * s0 = 1 ∧
      s0 * x * s0⁻¹ = x ^ 2 ∧
      s0 * ((((vS : ↥K0) : ↥H) : MulAut W)) * s0⁻¹ =
        ((((vS : ↥K0) : ↥H) : MulAut W)) ∧
      s0 * (dS : MulAut W) * s0⁻¹ = (dS : MulAut W) ∧
      (U : Set W) = {w : W | autAddHom s0 (Additive.ofMul w) = Additive.ofMul w} ∧
      Nat.card U = 4 ∧
      (∀ u ∈ U,
        Additive.toMul ((autAddHom ((((vS : ↥K0) : ↥H) : MulAut W))) (Additive.ofMul u)) ∈ U ∧
        Additive.toMul ((autAddHom (dS : MulAut W)) (Additive.ofMul u)) ∈ U) ∧
      Submodule.span (GaloisField 2 2) (Additive.ofMul '' (U : Set W)) = ⊤ := by
  letI := galoisModule hw2 x hx3 hfix
  intro G X H hH hxgen hcommH L M H0 d hLM hH0card hH0mem hcover hdL hdM K0 vS dS s0
    hvSord hdS2 hdSnot hdvS hs0sq hs0x hs0vS hs0dS
  let vH : ↥H := ((vS : ↥K0) : ↥H)
  let v0 : MulAut W := (vH : MulAut W)
  let d0 : MulAut W := (dS : MulAut W)
  have hs0v : s0 * v0 * s0⁻¹ = v0 := by simpa [v0] using hs0vS
  have hs0d : s0 * d0 * s0⁻¹ = d0 := by simpa [d0] using hs0dS
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hv0commx : v0 * x = x * v0 := by
    have hmem : v0 ∈ H := vH.2
    rw [hH] at hmem
    have hcent : v0 ∈ Subgroup.centralizer (X : Set (MulAut W)) := (Subgroup.mem_inf.mp hmem).2
    exact ((Subgroup.mem_centralizer_iff.mp hcent) x hxX).symm
  have hd0commx : d0 * x = x * d0 := by
    have hmem : d0 ∈ H := dS.2
    rw [hH] at hmem
    have hcent : d0 ∈ Subgroup.centralizer (X : Set (MulAut W)) := (Subgroup.mem_inf.mp hmem).2
    exact ((Subgroup.mem_centralizer_iff.mp hcent) x hxX).symm
  have hvHord : orderOf vH = 3 := by
    have h1 : orderOf vH = orderOf vS := Subgroup.orderOf_coe vS
    rw [h1]
    exact hvSord
  have hv0ord : orderOf v0 = 3 := by
    have h2 : orderOf v0 = orderOf vH := Subgroup.orderOf_coe vH
    rw [h2]
    exact hvHord
  have hv03 : v0 ^ 3 = 1 := by
    have := pow_orderOf_eq_one v0
    rwa [hv0ord] at this
  have hvH3 : vH ^ 3 = 1 := by
    have := pow_orderOf_eq_one vH
    rwa [hvHord] at this
  have hd0sq : d0 * d0 = 1 := by
    have := congrArg (fun z : ↥H => (z : MulAut W)) hdS2
    simpa [d0] using this
  have hd0ne : d0 ≠ 1 := by
    intro h
    apply hdSnot
    have h' : dS = 1 := Subtype.ext (by simpa [d0] using h)
    rw [h']
    exact K0.one_mem
  have hd0ord : orderOf d0 = 2 := by
    have hpow : d0 ^ 2 = 1 := by rw [pow_two]; exact hd0sq
    exact orderOf_eq_prime hpow hd0ne
  have hpair_action : ∀ h : ↥H,
      (lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = L ∧
       lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = M) ∨
      (lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M ∧
       lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = L) := by
    intro h
    rcases hcover h with hh | hh
    · exact Or.inl ((hH0mem h).mp hh)
    · right
      have hkd : h = (h * d⁻¹) * d := by group
      have hkfix := (hH0mem (h * d⁻¹)).mp hh
      constructor
      · calc lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L
            = lineMap (HLinHom hw2 x hx3 hfix H hcommH ((h * d⁻¹) * d)) L := by
                conv_lhs => rw [hkd]
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹) *
                HLinHom hw2 x hx3 hfix H hcommH d) L := by
                rw [map_mul]
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹))
                (lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L) :=
                lineMap_mul_apply _ _ _
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹)) M := by rw [hdL]
          _ = M := hkfix.2
      · calc lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M
            = lineMap (HLinHom hw2 x hx3 hfix H hcommH ((h * d⁻¹) * d)) M := by
                conv_lhs => rw [hkd]
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹) *
                HLinHom hw2 x hx3 hfix H hcommH d) M := by
                rw [map_mul]
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹))
                (lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M) :=
                lineMap_mul_apply _ _ _
          _ = lineMap (HLinHom hw2 x hx3 hfix H hcommH (h * d⁻¹)) L := by rw [hdM]
          _ = L := hkfix.1
  have hv0fix : lineMap (HLinHom hw2 x hx3 hfix H hcommH vH) L = L ∧
      lineMap (HLinHom hw2 x hx3 hfix H hcommH vH) M = M := by
    rcases hpair_action vH with h | h
    · exact h
    · exfalso
      have h2L : lineMap (HLinHom hw2 x hx3 hfix H hcommH (vH ^ 2)) L = L := by
        rw [pow_two, map_mul, lineMap_mul_apply, h.1, h.2]
      have h3L : lineMap (HLinHom hw2 x hx3 hfix H hcommH (vH ^ 3)) L = L := by
        rw [hvH3, map_one]
        exact lineMap_one_apply L
      have h3L' : lineMap (HLinHom hw2 x hx3 hfix H hcommH (vH ^ 3)) L = M := by
        rw [show vH ^ 3 = vH * vH ^ 2 by group]
        rw [map_mul, lineMap_mul_apply, h2L, h.1]
      exact hLM (h3L.symm.trans h3L')
  have hd0swap : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0commx) L = M ∧
      lineMap (hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0commx) M = L := by
    rcases hpair_action dS with h | h
    · exfalso
      have hdmem : dS ∈ H0 := (hH0mem dS).mpr h
      have hdvd : orderOf dS ∣ Nat.card H0 := Subgroup.orderOf_dvd_natCard H0 hdmem
      rw [hH0card] at hdvd
      have hdSord : orderOf dS = 2 := by
        have hpow : dS ^ 2 = 1 := by rw [pow_two]; exact hdS2
        exact orderOf_eq_prime hpow (by
          intro h1
          apply hdSnot
          rw [h1]
          exact K0.one_mem)
      rw [hdSord] at hdvd
      norm_num at hdvd
    · refine ⟨?_, ?_⟩
      · have h' := h.1
        rw [HLinHom_apply] at h'
        simpa [d0] using h'
      · have h' := h.2
        rw [HLinHom_apply] at h'
        simpa [d0] using h'
  have hv0L : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix v0 hv0commx) L = L := by
    have h := hv0fix.1
    rw [HLinHom_apply] at h
    simpa [v0] using h
  have hv0M : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix v0 hv0commx) M = M := by
    have h := hv0fix.2
    rw [HLinHom_apply] at h
    simpa [v0] using h
  have hcomm_mul : ∀ {g h : MulAut W}, g * x = x * g → h * x = x * h →
      (g * h) * x = x * (g * h) := by
    intro g h hg hh
    calc (g * h) * x = g * (h * x) := by group
      _ = g * (x * h) := by rw [hh]
      _ = (g * x) * h := by group
      _ = (x * g) * h := by rw [hg]
      _ = x * (g * h) := by group
  have hcomm_dv : (d0 * v0) * x = x * (d0 * v0) := hcomm_mul hd0commx hv0commx
  have hcomm_dvd : (d0 * (v0 * d0)) * x = x * (d0 * (v0 * d0)) :=
    hcomm_mul hd0commx (hcomm_mul hv0commx hd0commx)
  have hcomm_vd : (v0 * d0) * x = x * (v0 * d0) := hcomm_mul hv0commx hd0commx
  have hcomm_vv : (v0 * v0) * x = x * (v0 * v0) := hcomm_mul hv0commx hv0commx
  let Gv : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
    hGaloisLinearEquiv hw2 x hx3 hfix v0 hv0commx
  let Gd : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
    hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0commx
  have hVf : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  haveI hFD : FiniteDimensional (GaloisField 2 2) (Additive W) :=
    FiniteDimensional.of_finrank_pos (by rw [hVf]; norm_num)
  have htop : L.1 ⊔ M.1 = ⊤ := line_sup_eq_top hVf hLM
  obtain ⟨l0, hl0_mem, hl0_ne⟩ : ∃ l0 : Additive W, l0 ∈ L.1 ∧ l0 ≠ 0 := by
    obtain ⟨l, hl⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < Module.finrank (GaloisField 2 2) L.1 by rw [L.2]; norm_num)
    exact ⟨l, l.2, fun h => hl (Subtype.ext h)⟩
  obtain ⟨m1, hm1_mem, hm1_ne⟩ : ∃ m1 : Additive W, m1 ∈ M.1 ∧ m1 ≠ 0 := by
    obtain ⟨l, hl⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < Module.finrank (GaloisField 2 2) M.1 by rw [M.2]; norm_num)
    exact ⟨l, l.2, fun h => hl (Subtype.ext h)⟩
  have hspanL : L.1 = Submodule.span (GaloisField 2 2) {l0} :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2 hl0_mem hl0_ne
  have hspanM : M.1 = Submodule.span (GaloisField 2 2) {m1} :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2 hm1_mem hm1_ne
  have hmapL : L.1.map (Gv : Additive W →ₗ[GaloisField 2 2] Additive W) = L.1 := by
    have h := congrArg Subtype.val hv0L
    simpa [lineMap, Gv] using h
  have hmapM : M.1.map (Gv : Additive W →ₗ[GaloisField 2 2] Additive W) = M.1 := by
    have h := congrArg Subtype.val hv0M
    simpa [lineMap, Gv] using h
  have hv0l_mem : Gv l0 ∈ L.1 := by
    have h := Submodule.mem_map_of_mem
      (f := (Gv : Additive W →ₗ[GaloisField 2 2] Additive W)) hl0_mem
    rwa [hmapL] at h
  have hv0m_mem : Gv m1 ∈ M.1 := by
    have h := Submodule.mem_map_of_mem
      (f := (Gv : Additive W →ₗ[GaloisField 2 2] Additive W)) hm1_mem
    rwa [hmapM] at h
  have hv0l_span : Gv l0 ∈ Submodule.span (GaloisField 2 2) {l0} := by
    rw [← hspanL]
    exact hv0l_mem
  have hv0m_span : Gv m1 ∈ Submodule.span (GaloisField 2 2) {m1} := by
    rw [← hspanM]
    exact hv0m_mem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv0l_span
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv0m_span
  have hva_l : autAddHom v0 l0 = a • l0 := by
    rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix v0 hv0commx l0]
    exact ha.symm
  have hvb_m : autAddHom v0 m1 = b • m1 := by
    rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix v0 hv0commx m1]
    exact hb.symm
  have hvs : ∀ (c : GaloisField 2 2) (v : Additive W),
      autAddHom v0 (c • v) = c • autAddHom v0 v :=
    fun c v => autAddHom_smul_eq_of_comm hw2 x hx3 hfix hv0commx c v
  have hds : ∀ (c : GaloisField 2 2) (v : Additive W),
      autAddHom d0 (c • v) = c • autAddHom d0 v :=
    fun c v => autAddHom_smul_eq_of_comm hw2 x hx3 hfix hd0commx c v
  have ha3 : a ^ 3 = 1 := by
    have hiter : ∀ n : ℕ, (autAddHom v0)^[n] l0 = (a ^ n) • l0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, hvs, hva_l, smul_smul, pow_succ]
    have h3 : (autAddHom v0)^[3] l0 = l0 := by
      rw [autAddHom_pow_eq_of_comm hw2 x hx3 hfix hv0commx 3 l0, hv03]
      exact autAddHom_one_apply hw2 x hx3 hfix l0
    rw [hiter 3] at h3
    have hsub : (a ^ 3 - 1) • l0 = 0 := by
      rw [sub_smul, h3, one_smul, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hl0_ne
  have ha0 : a ≠ 0 := by
    intro h
    apply hl0_ne
    have hGv0 : Gv l0 = 0 := by
      rw [show Gv l0 = a • l0 from ha.symm, h, zero_smul]
    have h' : Gv l0 = Gv 0 := by rw [hGv0, map_zero]
    exact Gv.injective h'
  have hd0l_mem : autAddHom d0 l0 ∈ M.1 := by
    have h := congrArg Subtype.val hd0swap.1
    have hmap : L.1.map (Gd : Additive W →ₗ[GaloisField 2 2] Additive W) = M.1 := by
      simpa [lineMap, Gd] using h
    have hm := Submodule.mem_map_of_mem
      (f := (Gd : Additive W →ₗ[GaloisField 2 2] Additive W)) hl0_mem
    rw [hmap] at hm
    have hgl : Gd l0 = autAddHom d0 l0 :=
      hGaloisLinearEquiv_apply hw2 x hx3 hfix d0 hd0commx l0
    rw [← hgl]
    exact hm
  have hd0m_mem : autAddHom d0 m1 ∈ L.1 := by
    have h := congrArg Subtype.val hd0swap.2
    have hmap : M.1.map (Gd : Additive W →ₗ[GaloisField 2 2] Additive W) = L.1 := by
      simpa [lineMap, Gd] using h
    have hm := Submodule.mem_map_of_mem
      (f := (Gd : Additive W →ₗ[GaloisField 2 2] Additive W)) hm1_mem
    rw [hmap] at hm
    have hgl : Gd m1 = autAddHom d0 m1 :=
      hGaloisLinearEquiv_apply hw2 x hx3 hfix d0 hd0commx m1
    rw [← hgl]
    exact hm
  have hd0l_span : autAddHom d0 l0 ∈ Submodule.span (GaloisField 2 2) {m1} := by
    rw [← hspanM]
    exact hd0l_mem
  have hd0m_span : autAddHom d0 m1 ∈ Submodule.span (GaloisField 2 2) {l0} := by
    rw [← hspanL]
    exact hd0m_mem
  obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp hd0l_span
  obtain ⟨c1', hc1'⟩ := Submodule.mem_span_singleton.mp hd0m_span
  have hd0l : autAddHom d0 l0 = c1 • m1 := hc1.symm
  have hd0m1 : autAddHom d0 m1 = c1' • l0 := hc1'.symm
  have hd0l_ne : autAddHom d0 l0 ≠ 0 := by
    intro h
    have hGd0 : Gd l0 = 0 := by
      rw [show Gd l0 = autAddHom d0 l0 from
        hGaloisLinearEquiv_apply hw2 x hx3 hfix d0 hd0commx l0]
      exact h
    have h' : Gd l0 = Gd 0 := by rw [hGd0, map_zero]
    exact hl0_ne (Gd.injective h')
  have hc1c1' : c1 * c1' = 1 := by
    have h2 : autAddHom d0 (autAddHom d0 l0) = l0 :=
      autAddHom_autAddHom_eq hd0sq l0
    rw [hd0l, hds, hd0m1, smul_smul] at h2
    have hsub : (c1 * c1' - 1) • l0 = 0 := by
      rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hl0_ne
  have hdv0 : d0 * v0 * d0⁻¹ = v0 ^ 2 := by
    simpa [v0, d0, Subgroup.coe_pow] using hdvS
  have hd0inv : d0⁻¹ = d0 := (inv_eq_iff_mul_eq_one).mpr hd0sq
  have hconj_eq : d0 * v0 * d0 = v0 ^ 2 := by
    rw [hd0inv] at hdv0
    exact hdv0
  have hcomp_vv : autAddHom (v0 * v0) l0 = autAddHom v0 (autAddHom v0 l0) :=
    autAddHom_mul_eq_of_comm hw2 x hx3 hfix (g := v0) (h := v0) hv0commx hv0commx
      hcomm_vv l0
  have hcomp_vd : autAddHom (v0 * d0) l0 = autAddHom v0 (autAddHom d0 l0) :=
    autAddHom_mul_eq_of_comm hw2 x hx3 hfix (g := v0) (h := d0) hv0commx hd0commx
      hcomm_vd l0
  have hcomp_dvd : autAddHom (d0 * (v0 * d0)) l0 =
      autAddHom d0 (autAddHom (v0 * d0) l0) :=
    autAddHom_mul_eq_of_comm hw2 x hx3 hfix (g := d0) (h := v0 * d0) hd0commx hcomm_vd
      hcomm_dvd l0
  have hconj : autAddHom v0 (autAddHom v0 l0) = b • l0 := by
    calc autAddHom v0 (autAddHom v0 l0)
        = autAddHom (v0 * v0) l0 := hcomp_vv.symm
      _ = autAddHom (d0 * v0 * d0) l0 := by
          rw [show v0 * v0 = v0 ^ 2 by rw [pow_two], hconj_eq]
      _ = autAddHom (d0 * (v0 * d0)) l0 := by rw [mul_assoc]
      _ = autAddHom d0 (autAddHom (v0 * d0) l0) := hcomp_dvd
      _ = autAddHom d0 (autAddHom v0 (autAddHom d0 l0)) := by rw [hcomp_vd]
      _ = autAddHom d0 (autAddHom v0 (c1 • m1)) := by rw [hd0l]
      _ = autAddHom d0 (c1 • autAddHom v0 m1) := by rw [hvs]
      _ = autAddHom d0 (c1 • (b • m1)) := by rw [hvb_m]
      _ = c1 • autAddHom d0 (b • m1) := by rw [hds]
      _ = c1 • (b • autAddHom d0 m1) := by rw [hds]
      _ = c1 • (b • (c1' • l0)) := by rw [hd0m1]
      _ = (c1 * b * c1') • l0 := by
          rw [smul_smul, smul_smul]
      _ = b • l0 := by
          rw [show c1 * b * c1' = b by
            calc c1 * b * c1' = b * (c1 * c1') := by ring
              _ = b * 1 := by rw [hc1c1']
              _ = b := mul_one b]
  have hconj2 : autAddHom v0 (autAddHom v0 l0) = (a ^ 2) • l0 := by
    calc autAddHom v0 (autAddHom v0 l0)
        = autAddHom v0 (a • l0) := by rw [hva_l]
      _ = a • autAddHom v0 l0 := hvs a l0
      _ = a • (a • l0) := by rw [hva_l]
      _ = (a * a) • l0 := by rw [smul_smul]
      _ = (a ^ 2) • l0 := by rw [pow_two]
  have hb_eq : b = a ^ 2 := by
    have h : b • l0 = (a ^ 2) • l0 := by rw [← hconj, hconj2]
    have hsub : (b - a ^ 2) • l0 = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hl0_ne
  have ha_ne_one : a ≠ 1 := by
    intro ha1
    have hb1 : b = 1 := by rw [hb_eq, ha1]; norm_num
    have hvl : autAddHom v0 l0 = l0 := by rw [hva_l, ha1, one_smul]
    have hvm : autAddHom v0 m1 = m1 := by rw [hvb_m, hb1, one_smul]
    have hid : ∀ y : Additive W, autAddHom v0 y = y := by
      intro y
      have hx : y ∈ L.1 ⊔ M.1 := by rw [htop]; exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      rw [hspanL] at hu
      rw [hspanM] at hw
      obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hw
      rw [← hα, ← hβ, map_add, hvs α l0, hvs β m1, hvl, hvm]
    have hGv_one : Gv = 1 := by
      ext y
      calc Gv y = autAddHom v0 y := hGaloisLinearEquiv_apply hw2 x hx3 hfix v0 hv0commx y
        _ = y := hid y
        _ = (1 : Additive W ≃ₗ[GaloisField 2 2] Additive W) y := rfl
    have hHL_one : HLinHom hw2 x hx3 hfix H hcommH vH = 1 := by
      rw [HLinHom_apply]
      calc hGaloisLinearEquiv hw2 x hx3 hfix v0 (hcommH v0 vH.2)
          = Gv := congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix v0 hc)
              (Subsingleton.elim _ _)
        _ = 1 := hGv_one
    have hvH_one : vH = 1 :=
      hLinHom_injective hw2 x hx3 hfix H hcommH (by rw [hHL_one, map_one])
    have hv0_one : v0 = 1 := by
      have := congrArg (fun z : ↥H => (z : MulAut W)) hvH_one
      simpa [v0] using this
    rw [hv0_one, orderOf_one] at hv0ord
    omega
  have ha_ne_sq : a ^ 2 ≠ a := by
    intro h
    apply ha_ne_one
    have h2 : a * a = a * 1 := by simpa [mul_one, pow_two] using h
    exact mul_left_cancel₀ ha0 h2
  have hcommsv : s0 * v0 = v0 * s0 := by
    calc s0 * v0 = (s0 * v0 * s0⁻¹) * s0 := by group
      _ = v0 * s0 := by rw [hs0v]
  have hcommsd : s0 * d0 = d0 * s0 := by
    calc s0 * d0 = (s0 * d0 * s0⁻¹) * s0 := by group
      _ = d0 * s0 := by rw [hs0d]
  let E : Submodule (GaloisField 2 2) (Additive W) :=
    { carrier := {v | autAddHom v0 v = b • v}
      zero_mem' := by simp
      add_mem' := by
        intro u w hu hw
        change autAddHom v0 (u + w) = b • (u + w)
        rw [map_add, hu, hw, smul_add]
      smul_mem' := by
        intro c u hu
        change autAddHom v0 (c • u) = b • (c • u)
        rw [hvs, hu, smul_smul, smul_smul, mul_comm c b] }
  have hMleE : M.1 ≤ E := by
    rw [hspanM]
    apply Submodule.span_le.mpr
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hvb_m
  have hEne : E ≠ ⊤ := by
    intro htopE
    have hlE : l0 ∈ E := by rw [htopE]; exact Submodule.mem_top
    have h1 : a • l0 = b • l0 := by
      rw [← hva_l]
      exact hlE
    have hab : a = b := by
      have hsub : (a - b) • l0 = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hl0_ne
    rw [hb_eq] at hab
    exact ha_ne_sq hab.symm
  have hEfinrank : Module.finrank (GaloisField 2 2) E = 1 := by
    have hElt : Module.finrank (GaloisField 2 2) E <
        Module.finrank (GaloisField 2 2) (Additive W) := Submodule.finrank_lt hEne
    rw [hVf] at hElt
    have hMle' : Module.finrank (GaloisField 2 2) M.1 ≤
        Module.finrank (GaloisField 2 2) E := Submodule.finrank_mono hMleE
    rw [M.2] at hMle'
    omega
  have hEeq : M.1 = E :=
    Submodule.eq_of_le_of_finrank_eq hMleE (by rw [M.2, hEfinrank])
  have h_eig : autAddHom v0 (autAddHom s0 l0) = b • autAddHom s0 l0 := by
    calc autAddHom v0 (autAddHom s0 l0)
        = autAddHom s0 (autAddHom v0 l0) := by
            have h := autAddHom_iterate_commute v0 s0 hcommsv.symm 1 l0
            simpa using h
      _ = autAddHom s0 (a • l0) := by rw [hva_l]
      _ = (a ^ 2) • autAddHom s0 l0 :=
            autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x a l0
      _ = b • autAddHom s0 l0 := by rw [hb_eq]
  have hs0l_memM : autAddHom s0 l0 ∈ M.1 := by
    have hE : autAddHom s0 l0 ∈ E := h_eig
    rwa [← hEeq] at hE
  have hs0l_ne : autAddHom s0 l0 ≠ 0 := by
    intro h
    have h2 : autAddHom s0 (autAddHom s0 l0) = 0 := by rw [h, map_zero]
    rw [autAddHom_autAddHom_eq hs0sq l0] at h2
    exact hl0_ne h2
  let m0 : Additive W := autAddHom s0 l0
  have hm0_mem : m0 ∈ M.1 := hs0l_memM
  have hm0_ne : m0 ≠ 0 := hs0l_ne
  have hspanM0 : M.1 = Submodule.span (GaloisField 2 2) {m0} :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2 hm0_mem hm0_ne
  have hs0m0 : autAddHom s0 m0 = l0 := by
    change autAddHom s0 (autAddHom s0 l0) = l0
    exact autAddHom_autAddHom_eq hs0sq l0
  have hv_m0 : autAddHom v0 m0 = b • m0 := by
    change autAddHom v0 (autAddHom s0 l0) = b • autAddHom s0 l0
    exact h_eig
  have hd0l_spanM0 : autAddHom d0 l0 ∈ Submodule.span (GaloisField 2 2) {m0} := by
    rw [← hspanM0]
    exact hd0l_mem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd0l_spanM0
  have hd0l_c : autAddHom d0 l0 = c • m0 := hc.symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hd0l_ne
    rw [hd0l_c, h, zero_smul]
  have hd0m0 : autAddHom d0 m0 = c ^ 2 • l0 := by
    calc autAddHom d0 m0
        = autAddHom d0 (autAddHom s0 l0) := rfl
      _ = autAddHom s0 (autAddHom d0 l0) := by
            have h := autAddHom_iterate_commute d0 s0 hcommsd.symm 1 l0
            simpa using h
      _ = autAddHom s0 (c • m0) := by rw [hd0l_c]
      _ = c ^ 2 • autAddHom s0 m0 :=
            autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x c m0
      _ = c ^ 2 • l0 := by rw [hs0m0]
  let l : Additive W := c • l0
  let m : Additive W := c ^ 2 • m0
  have hl_mem : l ∈ L.1 := L.1.smul_mem c hl0_mem
  have hm_mem : m ∈ M.1 := M.1.smul_mem (c ^ 2) hm0_mem
  have hl_ne : l ≠ 0 := by
    intro h
    have hc' : c = 0 := by
      rcases smul_eq_zero.mp (show c • l0 = 0 from h) with h' | h'
      · exact h'
      · exact absurd h' hl0_ne
    exact hc0 hc'
  have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  have hm_ne : m ≠ 0 := by
    intro h
    have h' : c ^ 2 = 0 := by
      rcases smul_eq_zero.mp (show c ^ 2 • m0 = 0 from h) with h2 | h2
      · exact h2
      · exact absurd h2 hm0_ne
    exact hc2_ne h'
  have hv_l : autAddHom v0 l = a • l := by
    calc autAddHom v0 (c • l0) = c • autAddHom v0 l0 := hvs c l0
      _ = c • (a • l0) := by rw [hva_l]
      _ = (c * a) • l0 := by rw [smul_smul]
      _ = (a * c) • l0 := by rw [mul_comm c a]
      _ = a • (c • l0) := by rw [smul_smul]
  have hv_m : autAddHom v0 m = a ^ 2 • m := by
    calc autAddHom v0 (c ^ 2 • m0) = c ^ 2 • autAddHom v0 m0 := hvs (c ^ 2) m0
      _ = c ^ 2 • (b • m0) := by rw [hv_m0]
      _ = (c ^ 2 * b) • m0 := by rw [smul_smul]
      _ = (c ^ 2 * a ^ 2) • m0 := by rw [hb_eq]
      _ = (a ^ 2 * c ^ 2) • m0 := by rw [mul_comm (c ^ 2) (a ^ 2)]
      _ = a ^ 2 • (c ^ 2 • m0) := by rw [smul_smul]
  have hd_l : autAddHom d0 l = m := by
    calc autAddHom d0 (c • l0) = c • autAddHom d0 l0 := hds c l0
      _ = c • (c • m0) := by rw [hd0l_c]
      _ = (c * c) • m0 := by rw [smul_smul]
      _ = c ^ 2 • m0 := by rw [pow_two]
  have hd_m : autAddHom d0 m = l := by
    calc autAddHom d0 (c ^ 2 • m0) = c ^ 2 • autAddHom d0 m0 := hds (c ^ 2) m0
      _ = c ^ 2 • (c ^ 2 • l0) := by rw [hd0m0]
      _ = (c ^ 2 * c ^ 2) • l0 := by rw [smul_smul]
      _ = c • l0 := by
          rw [show c ^ 2 * c ^ 2 = c from by
            rw [← pow_two (c ^ 2)]
            exact hroot_f4 c]
  have hs_l : autAddHom s0 l = m := by
    calc autAddHom s0 (c • l0) = c ^ 2 • autAddHom s0 l0 :=
          autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x c l0
      _ = c ^ 2 • m0 := rfl
  have hs_m : autAddHom s0 m = l := by
    calc autAddHom s0 (c ^ 2 • m0) = (c ^ 2) ^ 2 • autAddHom s0 m0 :=
          autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x (c ^ 2) m0
      _ = (c ^ 2) ^ 2 • l0 := by rw [hs0m0]
      _ = c • l0 := by rw [hroot_f4 c]
  have hspanL' : L.1 = Submodule.span (GaloisField 2 2) {l} :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2 hl_mem hl_ne
  have hspanM' : M.1 = Submodule.span (GaloisField 2 2) {m} :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2 hm_mem hm_ne
  have hli : LinearIndependent (GaloisField 2 2) ![l, m] := by
    rw [LinearIndependent.pair_iff]
    intro alpha beta hab
    have hinf : L.1 ⊓ M.1 = ⊥ := line_inf_eq_bot hLM
    have hamem : alpha • l ∈ L.1 ⊓ M.1 := by
      refine Submodule.mem_inf.mpr ⟨L.1.smul_mem alpha hl_mem, ?_⟩
      have h : alpha • l = -(beta • m) := (add_eq_zero_iff_eq_neg).mp hab
      rw [h]
      exact M.1.neg_mem (M.1.smul_mem beta hm_mem)
    rw [hinf] at hamem
    have ha0' : alpha • l = 0 := by simpa using hamem
    have haz : alpha = 0 := by
      rcases smul_eq_zero.mp ha0' with h | h
      · exact h
      · exact absurd h hl_ne
    subst haz
    have hb0' : beta • m = 0 := by simpa using hab
    rcases smul_eq_zero.mp hb0' with h | h
    · exact ⟨rfl, h⟩
    · exact absurd h hm_ne
  let U : Subgroup W :=
    { carrier := {w : W | autAddHom s0 (Additive.ofMul w) = Additive.ofMul w}
      one_mem' := by
        change autAddHom s0 (Additive.ofMul (1 : W)) = Additive.ofMul (1 : W)
        simp
      mul_mem' := by
        intro u v hu hv
        change autAddHom s0 (Additive.ofMul (u * v)) = Additive.ofMul (u * v)
        rw [show Additive.ofMul (u * v) = Additive.ofMul u + Additive.ofMul v from rfl,
          map_add, hu, hv]
      inv_mem' := by
        intro u hu
        change autAddHom s0 (Additive.ofMul u⁻¹) = Additive.ofMul u⁻¹
        rw [show Additive.ofMul u⁻¹ = -Additive.ofMul u from rfl, map_neg, hu] }
  have hUmem : ∀ w : W,
      w ∈ U ↔ autAddHom s0 (Additive.ofMul w) = Additive.ofMul w := fun w => Iff.rfl
  let f : GaloisField 2 2 → U := fun c =>
    ⟨Additive.toMul (c • l + c ^ 2 • m), by
      rw [hUmem]
      change autAddHom s0 (c • l + c ^ 2 • m) = c • l + c ^ 2 • m
      calc autAddHom s0 (c • l + c ^ 2 • m)
          = c ^ 2 • autAddHom s0 l + (c ^ 2) ^ 2 • autAddHom s0 m := by
              rw [map_add, autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x c l,
                autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x (c ^ 2) m]
        _ = c ^ 2 • m + ((c ^ 2) ^ 2) • l := by rw [hs_l, hs_m]
        _ = c ^ 2 • m + c • l := by rw [hroot_f4 c]
        _ = c • l + c ^ 2 • m := by rw [add_comm]⟩
  have hf_inj : Function.Injective f := by
    intro c1 c2 h12
    have h : c1 • l + c1 ^ 2 • m = c2 • l + c2 ^ 2 • m := by
      have h' : Additive.ofMul (f c1).1 = Additive.ofMul (f c2).1 :=
        congrArg Additive.ofMul (congrArg Subtype.val h12)
      simpa [f] using h'
    have hzero : (c1 - c2) • l + (c1 ^ 2 - c2 ^ 2) • m = 0 := by
      have h' : (c1 - c2) • l + (c1 ^ 2 - c2 ^ 2) • m =
          (c1 • l + c1 ^ 2 • m) - (c2 • l + c2 ^ 2 • m) := by
        rw [sub_smul, sub_smul]; abel
      rw [h', h, sub_self]
    have hcoeff := (LinearIndependent.pair_iff.mp hli) (c1 - c2) (c1 ^ 2 - c2 ^ 2) hzero
    exact sub_eq_zero.mp hcoeff.1
  have hf_surj : Function.Surjective f := by
    intro u
    have hu : autAddHom s0 (Additive.ofMul (u : W)) = Additive.ofMul (u : W) :=
      (hUmem (u : W)).mp u.2
    have hdecomp : ∀ v : Additive W, ∃ x y : GaloisField 2 2, v = x • l + y • m := by
      intro v
      have hv : v ∈ L.1 ⊔ M.1 := by rw [htop]; exact Submodule.mem_top
      obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Submodule.mem_sup.mp hv
      rw [hspanL'] at ha1
      rw [hspanM'] at ha2
      obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp ha1
      obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp ha2
      exact ⟨x, y, by rw [← hx, ← hy]⟩
    obtain ⟨alpha, beta, hxy⟩ := hdecomp (Additive.ofMul (u : W))
    have hfixu := hu
    rw [hxy] at hfixu
    have hs0xy : autAddHom s0 (alpha • l + beta • m) = beta ^ 2 • l + alpha ^ 2 • m := by
      rw [map_add, autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x alpha l,
        autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x beta m, hs_l, hs_m, add_comm]
    have hrel : beta ^ 2 • l + alpha ^ 2 • m = alpha • l + beta • m := by
      calc beta ^ 2 • l + alpha ^ 2 • m = autAddHom s0 (alpha • l + beta • m) := hs0xy.symm
        _ = autAddHom s0 (Additive.ofMul (u : W)) := by rw [hxy]
        _ = Additive.ofMul (u : W) := hu
        _ = alpha • l + beta • m := hxy
    have hzero : (beta ^ 2 - alpha) • l + (alpha ^ 2 - beta) • m = 0 := by
      have h' : (beta ^ 2 - alpha) • l + (alpha ^ 2 - beta) • m =
          (beta ^ 2 • l + alpha ^ 2 • m) - (alpha • l + beta • m) := by
        rw [sub_smul, sub_smul]; abel
      rw [h', hrel, sub_self]
    have hcoeff := (LinearIndependent.pair_iff.mp hli) (beta ^ 2 - alpha) (alpha ^ 2 - beta) hzero
    have hx : alpha = beta ^ 2 := (sub_eq_zero.mp hcoeff.1).symm
    refine ⟨beta ^ 2, ?_⟩
    apply Subtype.ext
    apply Additive.ofMul.injective
    change Additive.ofMul (Additive.toMul (beta ^ 2 • l + (beta ^ 2) ^ 2 • m)) =
      Additive.ofMul (u : W)
    rw [show Additive.ofMul (Additive.toMul (beta ^ 2 • l + (beta ^ 2) ^ 2 • m)) =
        beta ^ 2 • l + (beta ^ 2) ^ 2 • m from rfl]
    rw [hroot_f4 beta, ← hx, ← hxy]
  have hcardU : Nat.card U = 4 := by
    have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
    calc Nat.card U = Nat.card (GaloisField 2 2) :=
          Nat.card_congr (Equiv.ofBijective f hbij).symm
      _ = 4 := by
          rw [GaloisField.card 2 2 (by norm_num)]
          norm_num
  have hpres : ∀ u ∈ U,
      Additive.toMul ((autAddHom v0) (Additive.ofMul u)) ∈ U ∧
      Additive.toMul ((autAddHom d0) (Additive.ofMul u)) ∈ U := by
    intro u hu
    have hu' : autAddHom s0 (Additive.ofMul u) = Additive.ofMul u := hu
    constructor
    · rw [hUmem]
      rw [show Additive.ofMul
          (Additive.toMul (autAddHom v0 (Additive.ofMul u))) =
          autAddHom v0 (Additive.ofMul u) from rfl]
      calc autAddHom s0 (autAddHom v0 (Additive.ofMul u))
          = autAddHom v0 (autAddHom s0 (Additive.ofMul u)) := by
              have h := autAddHom_iterate_commute s0 v0 hcommsv 1 (Additive.ofMul u)
              simpa using h
        _ = autAddHom v0 (Additive.ofMul u) := by rw [hu']
    · rw [hUmem]
      rw [show Additive.ofMul
          (Additive.toMul (autAddHom d0 (Additive.ofMul u))) =
          autAddHom d0 (Additive.ofMul u) from rfl]
      calc autAddHom s0 (autAddHom d0 (Additive.ofMul u))
          = autAddHom d0 (autAddHom s0 (Additive.ofMul u)) := by
              have h := autAddHom_iterate_commute s0 d0 hcommsd 1 (Additive.ofMul u)
              simpa using h
        _ = autAddHom d0 (Additive.ofMul u) := by rw [hu']
  have hspan_top : Submodule.span (GaloisField 2 2)
      (Additive.ofMul '' (U : Set W)) = ⊤ := by
    let S : Submodule (GaloisField 2 2) (Additive W) :=
      Submodule.span (GaloisField 2 2) (Additive.ofMul '' (U : Set W))
    have hlm_mem : l + m ∈ S := by
      apply Submodule.subset_span
      exact ⟨(f 1 : U).1, (f 1).2, by
        change Additive.ofMul (Additive.toMul (1 • l + 1 ^ 2 • m)) = l + m
        simp⟩
    have hlam_mem : a • l + a ^ 2 • m ∈ S := by
      apply Submodule.subset_span
      exact ⟨(f a : U).1, (f a).2, by
        change Additive.ofMul (Additive.toMul (a • l + a ^ 2 • m)) = a • l + a ^ 2 • m
        simp⟩
    have hstep : (l + m) - a⁻¹ • (a • l + a ^ 2 • m) = (1 - a) • m := by
      have hgen : ∀ x y : Additive W,
          (x + y) - a⁻¹ • (a • x + a ^ 2 • y) = (1 - a) • y := by
        intro x y
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        rw [sub_smul, one_smul, show a⁻¹ * a ^ 2 = a from by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]]
        abel
      exact hgen l m
    have hstep_mem : (1 - a) • m ∈ S := by
      rw [← hstep]
      exact S.sub_mem hlm_mem (S.smul_mem a⁻¹ hlam_mem)
    have h1a : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha_ne_one)
    have hm_mem_S : m ∈ S := by
      have h := S.smul_mem (1 - a)⁻¹ hstep_mem
      rwa [smul_smul, inv_mul_cancel₀ h1a, one_smul] at h
    have hl_mem_S : l ∈ S := by
      simpa using S.sub_mem hlm_mem hm_mem_S
    have hLle : L.1 ≤ S := by
      rw [hspanL']
      exact Submodule.span_le.mpr (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hl_mem_S)
    have hMle : M.1 ≤ S := by
      rw [hspanM']
      exact Submodule.span_le.mpr (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hm_mem_S)
    have htop_le : (⊤ : Submodule (GaloisField 2 2) (Additive W)) ≤ S := by
      rw [← htop]
      exact sup_le hLle hMle
    exact top_le_iff.mp htop_le
  refine ⟨l, m, a, U, ha3, ha_ne_one, hli, hv_l, hv_m, hd_l, hd_m, hs_l, hs_m,
    hv0ord, hd0sq, hs0sq, hs0x, hs0v, hs0d, rfl, hcardU, hpres, hspan_top⟩

theorem pair_basis_and_U_full {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ (L M : LineOf (K := GaloisField 2 2) (V := Additive W)) (H0 : Subgroup ↥H)
      (v : ↥H0) (d : ↥H) (s0 : MulAut W) (l m : Additive W) (a : GaloisField 2 2)
      (U : Subgroup W),
      (L ≠ M ∧ (X.subgroupOf H) ≤ H0 ∧ Nat.card H0 = 9 ∧
        ((X.subgroupOf H).subgroupOf H0) ⊔ Subgroup.zpowers v = ⊤ ∧
        ((X.subgroupOf H).subgroupOf H0) ⊓ Subgroup.zpowers v = ⊥ ∧
        v ∉ (X.subgroupOf H).subgroupOf H0 ∧ orderOf v = 3 ∧
        (d : MulAut W) ∈ D ∧ d * d = 1 ∧ d ∉ H0 ∧
        (∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0) ∧
        (d : MulAut W) * (((v : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
          (((v ^ 2 : ↥H0) : ↥H) : MulAut W) ∧
        (s0 = s ∨ s0 = s * (d : MulAut W)) ∧
        s0 ∈ G ∧ s0 * s0 = 1 ∧ s0 ∉ H ∧
        s0 * x * s0⁻¹ = x ^ 2 ∧
        s0 * (((v : ↥H0) : ↥H) : MulAut W) * s0⁻¹ = (((v : ↥H0) : ↥H) : MulAut W) ∧
        s0 * (d : MulAut W) * s0⁻¹ = (d : MulAut W) ∧
        (∀ h : MulAut W, h ∈ Subgroup.zpowers (((v : ↥H0) : ↥H) : MulAut W) ⊔
          Subgroup.zpowers (d : MulAut W) → s0 * h = h * s0)) ∧
      (a ^ 3 = 1 ∧ a ≠ 1 ∧
        LinearIndependent (GaloisField 2 2) ![l, m] ∧
        (autAddHom ((((v : ↥H0) : ↥H) : MulAut W))) l = a • l ∧
        (autAddHom ((((v : ↥H0) : ↥H) : MulAut W))) m = a ^ 2 • m ∧
        (autAddHom (d : MulAut W)) l = m ∧
        (autAddHom (d : MulAut W)) m = l ∧
        (autAddHom s0) l = m ∧ (autAddHom s0) m = l ∧
        orderOf ((((v : ↥H0) : ↥H) : MulAut W)) = 3 ∧
        (d : MulAut W) * (d : MulAut W) = 1 ∧ s0 * s0 = 1 ∧
        s0 * x * s0⁻¹ = x ^ 2 ∧
        s0 * ((((v : ↥H0) : ↥H) : MulAut W)) * s0⁻¹ =
          ((((v : ↥H0) : ↥H) : MulAut W)) ∧
        s0 * (d : MulAut W) * s0⁻¹ = (d : MulAut W) ∧
        (U : Set W) = {w : W | autAddHom s0 (Additive.ofMul w) = Additive.ofMul w} ∧
        Nat.card U = 4 ∧
        (∀ u ∈ U,
          Additive.toMul ((autAddHom ((((v : ↥H0) : ↥H) : MulAut W)))
            (Additive.ofMul u)) ∈ U ∧
          Additive.toMul ((autAddHom (d : MulAut W)) (Additive.ofMul u)) ∈ U) ∧
        Submodule.span (GaloisField 2 2) (Additive.ofMul '' (U : Set W)) = ⊤) := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨L, M, H0, v, d, s0, hLM, hXle, hH0card, hsup, hdisj, hvnotX, hvord, hdD, hd2,
    hdnot, hcoverS3, hdv, hs0cases, hs0G, hs0sq, hs0notH, hs0x, hs0v, hs0d, hs0comm⟩ :=
    sixfourteen_n2_pair_S3 hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  obtain ⟨Lt, Mt, H0t, -, dt, hLMt, -, -, -, hH0cardt, hH0memt, -, -, -, -, -, -, hcovert,
    -, -, hdLt, hdMt⟩ :=
    sixfourteen_n2_pair_torus hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  obtain ⟨l, m, a, U, hbasis⟩ :=
    pair_basis_and_U_aux hw2 x hx3 hfix hW hH hxgen hcommH hLMt hH0cardt hH0memt hcovert
      hdLt hdMt hvord hd2 hdnot hdv hs0sq hs0x hs0v hs0d
  refine ⟨L, M, H0, v, d, s0, l, m, a, U, ?_, ?_⟩
  · exact ⟨hLM, hXle, hH0card, hsup, hdisj, hvnotX, hvord, hdD, hd2, hdnot, hcoverS3, hdv,
      hs0cases, hs0G, hs0sq, hs0notH, hs0x, hs0v, hs0d, hs0comm⟩
  · exact hbasis

end CFSG.LocalAnalysis.WeakClosure81
