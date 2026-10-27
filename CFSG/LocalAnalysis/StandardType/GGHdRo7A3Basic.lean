module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Defs

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section P

variable {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}

theorem mem_a3Aug {u : Fin m → ZMod p} : u ∈ a3Aug p m ↔ ∑ i, u i = 0 :=
  Iff.rfl

theorem a3Aug_perm {u : Fin m → ZMod p} (hu : u ∈ a3Aug p m) (σ : Equiv.Perm (Fin m)) :
    (fun i => u (σ i)) ∈ a3Aug p m := by
  change ∑ i, u (σ i) = 0
  rw [Equiv.sum_comp σ u]
  exact hu

theorem a3P_one : A3P p m θ z 1 :=
  ⟨1, fun _ _ => rfl, rfl⟩

theorem a3P_mul {a b : V ≃ₗ[ZMod p] V} (ha : A3P p m θ z a) (hb : A3P p m θ z b) :
    A3P p m θ z (a * b) := by
  obtain ⟨σ, hσ, haz⟩ := ha
  obtain ⟨τ, hτ, hbz⟩ := hb
  refine ⟨σ * τ, fun u hu => ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hτ u hu, hσ _ (a3Aug_perm hu τ.symm)]
    rfl
  · rw [LinearEquiv.mul_apply, hbz, haz]

theorem a3P_inv {a : V ≃ₗ[ZMod p] V} (ha : A3P p m θ z a) : A3P p m θ z a⁻¹ := by
  obtain ⟨σ, hσ, haz⟩ := ha
  refine ⟨σ⁻¹, fun u hu => ?_, ?_⟩
  · have h := hσ _ (a3Aug_perm hu σ)
    have h' : (fun i => (fun j => u (σ j)) (σ.symm i)) = u := by
      funext i
      simp
    rw [h'] at h
    rw [← h]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    rfl
  · conv_lhs => rw [← haz]
    simp

theorem a3_const_mem (hpm : p ∣ m) (c : ZMod p) : (fun _ : Fin m => c) ∈ a3Aug p m := by
  rw [mem_a3Aug]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) m c, hm0]
  exact zero_smul _ _

theorem a3_single_sub_mem (i j : Fin m) :
    (Pi.single i 1 - Pi.single j 1 : Fin m → ZMod p) ∈ a3Aug p m := by
  rw [mem_a3Aug]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin m, (Pi.single i (1 : ZMod p) : Fin m → ZMod p) k) = 1 := by
    have h := Fintype.sum_pi_single (M := fun _ : Fin m => ZMod p) i (fun _ => (1 : ZMod p))
    simpa [Pi.single_apply, eq_comm] using h
  have h2 : (∑ k : Fin m, (Pi.single j (1 : ZMod p) : Fin m → ZMod p) k) = 1 := by
    have h := Fintype.sum_pi_single (M := fun _ : Fin m => ZMod p) j (fun _ => (1 : ZMod p))
    simpa [Pi.single_apply, eq_comm] using h
  rw [h1, h2, sub_self]

theorem a3_theta_eq (hfr : A3Frame p m θ z) {u v : Fin m → ZMod p} (hu : u ∈ a3Aug p m)
    (hv : v ∈ a3Aug p m) (h : θ u = θ v) : ∃ c : ZMod p, ∀ i, u i = v i + c := by
  have hmem : u - v ∈ a3Aug p m := (a3Aug p m).sub_mem hu hv
  have hzero : θ (u - v) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨c, hc⟩ := hfr.1 _ hmem hzero
  refine ⟨c, fun i => ?_⟩
  have hi : u i - v i = c := congrFun hc i
  rw [← hi]
  abel

end P

section Frame

variable {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}

private noncomputable def hdRo7A3BasicAux_pairMap
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V)
    (e : (Fin m → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p)) :
    (↥(a3Aug p m) × ZMod p) →ₗ[ZMod p] V where
  toFun x := θ (e x.1.1) + x.2 • z
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, add_smul]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_add,
      smul_smul, RingHom.id_apply, smul_eq_mul]

private noncomputable def hdRo7A3BasicAux_permLM (σ : Equiv.Perm (Fin m)) :
    (Fin m → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) where
  toFun u := fun i => u (σ.symm i)
  map_add' u v := by
    ext i
    rfl
  map_smul' c u := by
    ext i
    rfl

private theorem hdRo7A3BasicAux_pairMap_surjective (hfr : A3Frame p m θ z) :
    Function.Surjective (hdRo7A3BasicAux_pairMap θ z (LinearMap.id)) := by
  intro v
  obtain ⟨u, hu, c, hvc⟩ := hfr.2.1 v
  exact ⟨(⟨u, hu⟩, c), by simp [hdRo7A3BasicAux_pairMap, hvc]⟩

theorem a3_moduleFinite (hfr : A3Frame p m θ z) : Module.Finite (ZMod p) V :=
  Module.Finite.of_surjective _ (hdRo7A3BasicAux_pairMap_surjective hfr)

theorem a3_finite (hfr : A3Frame p m θ z) : Finite V :=
  Finite.of_surjective _ (hdRo7A3BasicAux_pairMap_surjective hfr)

private theorem hdRo7A3BasicAux_finrank_aug (hm : 1 ≤ m) :
    Module.finrank (ZMod p) ↥(a3Aug p m) = m - 1 := by
  let S : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p :=
    ∑ i : Fin m, LinearMap.proj (R := ZMod p) (φ := fun _ => ZMod p) i
  have hS : a3Aug p m = LinearMap.ker S := by
    ext u
    simp [S, a3Aug]
  have hsurj : Function.Surjective S := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    have h := Fintype.sum_pi_single (M := fun _ : Fin m => ZMod p) (⟨0, hm⟩ : Fin m)
      (fun _ => c)
    simpa [S, Pi.single_apply, eq_comm] using h
  have hrange : LinearMap.range S = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker S
  have htop : Module.finrank (ZMod p) (LinearMap.range S) = 1 := by
    rw [hrange, finrank_top, Module.finrank_self]
  have hdom : Module.finrank (ZMod p) (Fin m → ZMod p) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [htop, hdom] at hrn
  rw [hS]
  omega

private theorem hdRo7A3BasicAux_ker_subtype (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (hM : θ (fun _ => 1) = 0) :
    LinearMap.ker (θ.comp (a3Aug p m).subtype) =
      Submodule.span (ZMod p)
        {⟨fun _ : Fin m => (1 : ZMod p), a3_const_mem hpm 1⟩} := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨c, hc⟩ := hfr.1 x.1 x.2 hx
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    ext i
    simp [hc]
  · intro hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [← hc]
    simp [hM]

private theorem hdRo7A3BasicAux_finrank_map (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm : 2 ≤ m)
    (hM : θ (fun _ => 1) = 0) : Module.finrank (ZMod p) ((a3Aug p m).map θ) = m - 2 := by
  let g : ↥(a3Aug p m) →ₗ[ZMod p] V := θ.comp (a3Aug p m).subtype
  have hrange : LinearMap.range g = (a3Aug p m).map θ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker g =
      Submodule.span (ZMod p)
        {⟨fun _ : Fin m => (1 : ZMod p), a3_const_mem hpm 1⟩} :=
    hdRo7A3BasicAux_ker_subtype hfr hpm hM
  have hone : (⟨fun _ : Fin m => (1 : ZMod p), a3_const_mem hpm 1⟩ : ↥(a3Aug p m)) ≠ 0 := by
    intro h
    have h0 : (fun _ : Fin m => (1 : ZMod p)) = 0 := by
      simpa using congrArg Subtype.val h
    have := congrFun h0 ⟨0, by omega⟩
    simp at this
  have hkerdim : Module.finrank (ZMod p) (LinearMap.ker g) = 1 := by
    rw [hker, finrank_span_singleton hone]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hdim : Module.finrank (ZMod p) ↥(a3Aug p m) = m - 1 :=
    hdRo7A3BasicAux_finrank_aug (p := p) (m := m) (by omega)
  rw [hkerdim, hdim] at hrn
  rw [← hrange]
  omega

theorem a3_finrank (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm : 2 ≤ m) :
    Module.finrank (ZMod p) V = m - 1 := by
  have hVfin : Module.Finite (ZMod p) V := a3_moduleFinite hfr
  have hdim : Module.finrank (ZMod p) ↥(a3Aug p m) = m - 1 :=
    hdRo7A3BasicAux_finrank_aug (p := p) (m := m) (by omega)
  rcases hfr.2.2 with ⟨hU, hz⟩ | ⟨hM, hzn⟩
  · let g : ↥(a3Aug p m) →ₗ[ZMod p] V := θ.comp (a3Aug p m).subtype
    have hrange : LinearMap.range g = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      obtain ⟨u, hu, c, hvc⟩ := hfr.2.1 v
      have hconst : c • (fun _ : Fin m => 1) = (fun _ : Fin m => c) := by
        ext i
        simp [smul_eq_mul]
      have hmem : u + c • (fun _ : Fin m => 1) ∈ a3Aug p m :=
        (a3Aug p m).add_mem hu (hconst.symm ▸ a3_const_mem hpm c)
      refine ⟨⟨u + c • (fun _ : Fin m => 1), hmem⟩, ?_⟩
      show θ (u + c • (fun _ : Fin m => 1)) = v
      rw [map_add, map_smul, hU]
      exact hvc.symm
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hxy' : θ x.1 = θ y.1 := hxy
      have hzero : θ (x.1 - y.1) = 0 := by
        rw [map_sub, hxy', sub_self]
      obtain ⟨c, hc⟩ := hfr.1 _ ((a3Aug p m).sub_mem x.2 y.2) hzero
      have hc' : x.1 - y.1 = c • (fun _ : Fin m => 1) := by
        rw [hc]
        ext i
        simp [smul_eq_mul]
      have hc0 : c = 0 := by
        have h1 : θ (x.1 - y.1) = c • z := by
          rw [hc', map_smul, hU]
        rw [hzero] at h1
        exact (smul_eq_zero.mp h1.symm).resolve_right hz
      have hsub : x.1 - y.1 = 0 := by
        rw [hc', hc0, zero_smul]
      exact sub_eq_zero.mp hsub
    have hrange' : Module.finrank (ZMod p) V =
        Module.finrank (ZMod p) (LinearMap.range g) := by
      rw [hrange, finrank_top]
    rw [hrange', LinearMap.finrank_range_of_inj hinj, hdim]
  · have hMfin : Module.finrank (ZMod p) ((a3Aug p m).map θ) = m - 2 :=
      hdRo7A3BasicAux_finrank_map hfr hpm hm hM
    have hz0 : z ≠ 0 := by
      intro h
      exact hzn 0 (zero_mem _) (by rw [map_zero]; exact h.symm)
    let W : Submodule (ZMod p) V := (a3Aug p m).map θ
    have hsup : W ⊔ Submodule.span (ZMod p) {z} = ⊤ := by
      rw [Submodule.sup_eq_top_iff]
      intro v
      obtain ⟨u, hu, c, hvc⟩ := hfr.2.1 v
      exact ⟨θ u, ⟨u, hu, rfl⟩, c • z,
        Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton z)), hvc⟩
    have hinf : W ⊓ Submodule.span (ZMod p) {z} = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwm, hws⟩ := Submodule.mem_inf.mp hw
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hwm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hws
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        rw [← hc]
        exact Submodule.zero_mem _
      · exfalso
        have hz_eq : z = θ (c⁻¹ • u) := by
          rw [map_smul]
          calc z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
            _ = c⁻¹ • θ u := by rw [hc]
        exact hzn _ (Submodule.smul_mem _ _ hu) hz_eq.symm
    have hspan1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {z}) = 1 :=
      finrank_span_singleton hz0
    have hdimsup : Module.finrank (ZMod p) ↥(W ⊔ Submodule.span (ZMod p) {z}) =
        Module.finrank (ZMod p) V := by
      rw [hsup, finrank_top]
    have hdiminf : Module.finrank (ZMod p) ↥(W ⊓ Submodule.span (ZMod p) {z}) = 0 := by
      rw [hinf, finrank_bot]
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span (ZMod p) {z})
    rw [hdimsup, hdiminf, hMfin, hspan1] at h
    omega

theorem a3_finrank_M (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm : 2 ≤ m)
    (hM : θ (fun _ => 1) = 0) : Module.finrank (ZMod p) ((a3Aug p m).map θ) = m - 2 :=
  hdRo7A3BasicAux_finrank_map hfr hpm hm hM

private lemma hdRo7A3BasicAux_exists_notMem (s : Finset (Fin m)) (h : s.card < m) :
    ∃ k : Fin m, k ∉ s := by
  have h' : s.card < (Finset.univ : Finset (Fin m)).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using h
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h'
  exact ⟨k, hk⟩

private lemma hdRo7A3BasicAux_mem_pair_iff {a b k : Fin m} (hab : a ≠ b) :
    k ∈ ({a, b} : Finset (Fin m)) ↔
      ((Pi.single a (1 : ZMod p) : Fin m → ZMod p) -
        (Pi.single b (1 : ZMod p) : Fin m → ZMod p)) k ≠ 0 := by
  by_cases hka : k = a
  · subst hka
    simp [Pi.sub_apply, hab]
  · by_cases hkb : k = b
    · subst hkb
      simp [Pi.sub_apply, hka]
    · simp [hka, hkb, Pi.sub_apply]

private theorem hdRo7A3BasicAux_pair_sets (hfr : A3Frame p m θ z) (hm : 5 ≤ m)
    {σ τ : Equiv.Perm (Fin m)}
    (h : ∀ u ∈ a3Aug p m, θ (fun i => u (σ.symm i)) = θ (fun i => u (τ.symm i)))
    {i j : Fin m} (hij : i ≠ j) :
    ({σ i, σ j} : Finset (Fin m)) = {τ i, τ j} := by
  set wσ : Fin m → ZMod p :=
    fun k => ((Pi.single i (1 : ZMod p) : Fin m → ZMod p) -
      (Pi.single j (1 : ZMod p) : Fin m → ZMod p)) (σ.symm k) with hwσdef
  set wτ : Fin m → ZMod p :=
    fun k => ((Pi.single i (1 : ZMod p) : Fin m → ZMod p) -
      (Pi.single j (1 : ZMod p) : Fin m → ZMod p)) (τ.symm k) with hwτdef
  have hu : wσ ∈ a3Aug p m := a3Aug_perm (a3_single_sub_mem i j) σ.symm
  have hv : wτ ∈ a3Aug p m := a3Aug_perm (a3_single_sub_mem i j) τ.symm
  have hθ : θ wσ = θ wτ := h _ (a3_single_sub_mem i j)
  obtain ⟨c, hc⟩ := a3_theta_eq hfr hu hv hθ
  have hS : ({σ i, σ j, τ i, τ j} : Finset (Fin m)).card < m := by
    have hle : ({σ i, σ j, τ i, τ j} : Finset (Fin m)).card ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨k, hk⟩ := hdRo7A3BasicAux_exists_notMem ({σ i, σ j, τ i, τ j} : Finset (Fin m)) hS
  have hk' : k ≠ σ i ∧ k ≠ σ j ∧ k ≠ τ i ∧ k ≠ τ j := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
  have hwk : wσ k = 0 := by
    simp [wσ, Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq, hk'.1, hk'.2.1]
  have hwk' : wτ k = 0 := by
    simp [wτ, Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq, hk'.2.2.1, hk'.2.2.2]
  have hc0 : c = 0 := by
    have h := hc k
    rw [hwk, hwk', zero_add] at h
    exact h.symm
  have hw : wσ = wτ := by
    funext k
    have h := hc k
    rwa [hc0, add_zero] at h
  ext k
  have h1 : k ∈ ({σ i, σ j} : Finset (Fin m)) ↔
      ((Pi.single (σ i) (1 : ZMod p) : Fin m → ZMod p) -
        (Pi.single (σ j) (1 : ZMod p) : Fin m → ZMod p)) k ≠ 0 :=
    hdRo7A3BasicAux_mem_pair_iff (σ.injective.ne hij)
  have h2 : k ∈ ({τ i, τ j} : Finset (Fin m)) ↔
      ((Pi.single (τ i) (1 : ZMod p) : Fin m → ZMod p) -
        (Pi.single (τ j) (1 : ZMod p) : Fin m → ZMod p)) k ≠ 0 :=
    hdRo7A3BasicAux_mem_pair_iff (τ.injective.ne hij)
  have hpt : ((Pi.single (σ i) (1 : ZMod p) : Fin m → ZMod p) -
      (Pi.single (σ j) (1 : ZMod p) : Fin m → ZMod p)) k = wσ k := by
    rw [hwσdef]
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq]
  have hpt' : ((Pi.single (τ i) (1 : ZMod p) : Fin m → ZMod p) -
      (Pi.single (τ j) (1 : ZMod p) : Fin m → ZMod p)) k = wτ k := by
    rw [hwτdef]
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq]
  rw [h1, h2, hpt, hpt', hw]

private lemma hdRo7A3BasicAux_perm_eq_of_pair_sets {m : ℕ} (hm : 3 ≤ m)
    {σ τ : Equiv.Perm (Fin m)}
    (h : ∀ i j : Fin m, i ≠ j → ({σ i, σ j} : Finset (Fin m)) = {τ i, τ j}) :
    σ = τ := by
  apply Equiv.ext
  intro i
  have hcard : 1 < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hcard' : 1 < Fintype.card {x : Fin m // x ≠ i} := by
    have hc : Fintype.card {x : Fin m // x ≠ i} = m - 1 := by
      simpa [Fintype.card_fin] using Set.card_ne_eq (α := Fin m) i
    omega
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard' ⟨j, hji⟩
  have hki : (k : Fin m) ≠ i := k.2
  have hkji : (k : Fin m) ≠ j := by
    intro hk
    exact hkj (Subtype.ext hk)
  have hij : i ≠ j := hji.symm
  have hik : i ≠ k.1 := hki.symm
  have hjk : j ≠ k.1 := hkji.symm
  by_cases hcase : σ i = τ i
  · exact hcase
  · exfalso
    have hpij : ∀ x : Fin m, (x = σ i ∨ x = σ j) ↔ (x = τ i ∨ x = τ j) := by
      intro x
      have hx := congrArg (fun s : Finset (Fin m) => x ∈ s) (h i j hij)
      simpa using hx
    have hpjk : ∀ x : Fin m, (x = σ j ∨ x = σ k.1) ↔ (x = τ j ∨ x = τ k.1) := by
      intro x
      have hx := congrArg (fun s : Finset (Fin m) => x ∈ s) (h j k.1 hjk)
      simpa using hx
    have hτi : τ i = σ j := by
      have hx : τ i = σ i ∨ τ i = σ j := (hpij (τ i)).mpr (Or.inl rfl)
      rcases hx with hx | hx
      · exact absurd hx.symm hcase
      · exact hx
    have hx : τ i = τ j ∨ τ i = τ k.1 := (hpjk (τ i)).mp (Or.inl hτi)
    rcases hx with hx | hx
    · exact hij (τ.injective hx)
    · exact hik (τ.injective hx)

theorem a3_theta_single_sub_ne_zero (hfr : A3Frame p m θ z) (hm : 3 ≤ m) {i j : Fin m}
    (hij : i ≠ j) : θ (Pi.single i 1 - Pi.single j 1) ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := hfr.1 _ (a3_single_sub_mem i j) h0
  obtain ⟨k, hk⟩ := hdRo7A3BasicAux_exists_notMem ({i, j} : Finset (Fin m)) (by
    have hle : ({i, j} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    omega)
  have hki : k ≠ i := by
    intro h
    exact hk (by simp [h])
  have hkj : k ≠ j := by
    intro h
    exact hk (by simp [h])
  have hc0 : c = 0 := by
    have h := congrFun hc k
    rw [Pi.sub_apply] at h
    simp only [Pi.single_apply, hki, hkj, ite_false, sub_self] at h
    exact h.symm
  have h1 : (1 : ZMod p) = 0 := by
    have h := congrFun hc i
    rw [Pi.sub_apply] at h
    simp only [Pi.single_apply, hij, hc0, ite_true, ite_false, sub_zero] at h
    exact h
  exact one_ne_zero h1

private noncomputable def hdRo7A3BasicAux_liftQ
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (F : M →ₗ[ZMod p] V) (hF : Function.Surjective F) (G : M →ₗ[ZMod p] W)
    (h : LinearMap.ker F ≤ LinearMap.ker G) : V →ₗ[ZMod p] W :=
  (Submodule.liftQ (LinearMap.ker F) G h).comp
    ((LinearMap.quotKerEquivOfSurjective F hF).symm : V →ₗ[ZMod p] (M ⧸ LinearMap.ker F))

private theorem hdRo7A3BasicAux_liftQ_apply
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (F : M →ₗ[ZMod p] V) (hF : Function.Surjective F) (G : M →ₗ[ZMod p] W)
    (h : LinearMap.ker F ≤ LinearMap.ker G) (x : M) :
    hdRo7A3BasicAux_liftQ F hF G h (F x) = G x := by
  have h1 : (LinearMap.quotKerEquivOfSurjective F hF) (Submodule.Quotient.mk x) = F x :=
    LinearMap.quotKerEquivOfSurjective_apply_mk F hF x
  have h2 : (LinearMap.quotKerEquivOfSurjective F hF).symm (F x) = Submodule.Quotient.mk x := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  simp only [hdRo7A3BasicAux_liftQ, LinearMap.comp_apply, LinearEquiv.coe_coe, h2,
    Submodule.liftQ_apply]

private theorem hdRo7A3BasicAux_const_of_ker (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    {u : Fin m → ZMod p} (hu : u ∈ a3Aug p m) {c : ZMod p}
    (hx : θ u + c • z = 0) : ∃ d : ZMod p, u = fun _ => d := by
  rcases hfr.2.2 with ⟨hU, hz⟩ | ⟨hM, hzn⟩
  · have hconst : c • (fun _ : Fin m => 1) = (fun _ : Fin m => c) := by
      ext i
      simp [smul_eq_mul]
    have hmem : u + c • (fun _ : Fin m => 1) ∈ a3Aug p m :=
      (a3Aug p m).add_mem hu (hconst.symm ▸ a3_const_mem hpm c)
    have hzero : θ (u + c • (fun _ : Fin m => 1)) = 0 := by
      rw [map_add, map_smul, hU]
      exact hx
    obtain ⟨d, hd⟩ := hfr.1 _ hmem hzero
    refine ⟨d - c, ?_⟩
    funext k
    have hk := congrFun hd k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] at hk
    rw [eq_sub_iff_add_eq]
    exact hk
  · have hz0 : z ≠ 0 := by
      intro h
      exact hzn 0 (zero_mem _) (by rw [map_zero]; exact h.symm)
    have hc0 : c = 0 := by
      by_contra hc
      have hx'' : c • z + θ u = 0 := by rw [add_comm]; exact hx
      have h1 : c • z = -θ u := eq_neg_of_add_eq_zero_left hx''
      have hz_eq : z = θ (c⁻¹ • (-u)) := by
        calc z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = c⁻¹ • (-θ u) := by rw [h1]
          _ = θ (c⁻¹ • (-u)) := by rw [map_smul, map_neg]
      exact hzn _ (Submodule.smul_mem _ _ (Submodule.neg_mem _ hu)) hz_eq.symm
    rw [hc0, zero_smul, add_zero] at hx
    obtain ⟨d, hd⟩ := hfr.1 u hu hx
    exact ⟨d, hd⟩

private theorem hdRo7A3BasicAux_ker_le_perm (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (τ : Equiv.Perm (Fin m)) :
    LinearMap.ker (hdRo7A3BasicAux_pairMap θ z LinearMap.id) ≤
      LinearMap.ker (hdRo7A3BasicAux_pairMap θ z (hdRo7A3BasicAux_permLM τ)) := by
  rintro ⟨⟨u, hu⟩, c⟩ hx
  have hx' : θ u + c • z = 0 := by
    simpa [hdRo7A3BasicAux_pairMap] using hx
  obtain ⟨d, hd⟩ := hdRo7A3BasicAux_const_of_ker hfr hpm hu hx'
  have hpermu : (fun i => u (τ.symm i)) = u := by
    funext i
    rw [hd]
  simpa [hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM, hpermu] using hx'

private noncomputable def hdRo7A3BasicAux_coord (i : Fin m) :
    ↥(a3Aug p m) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (R := ZMod p) (φ := fun _ => ZMod p) i).comp
    (Submodule.subtype (a3Aug p m))

private noncomputable def hdRo7A3BasicAux_coordForm (i j : Fin m) :
    (↥(a3Aug p m) × ZMod p) →ₗ[ZMod p] ZMod p :=
  (hdRo7A3BasicAux_coord i).comp (LinearMap.fst _ _ _) -
    (hdRo7A3BasicAux_coord j).comp (LinearMap.fst _ _ _)

private theorem hdRo7A3BasicAux_ker_le_coord (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (i j : Fin m) :
    LinearMap.ker (hdRo7A3BasicAux_pairMap θ z LinearMap.id) ≤
      LinearMap.ker (hdRo7A3BasicAux_coordForm i j) := by
  rintro ⟨⟨u, hu⟩, c⟩ hx
  have hx' : θ u + c • z = 0 := by
    simpa [hdRo7A3BasicAux_pairMap] using hx
  obtain ⟨d, hd⟩ := hdRo7A3BasicAux_const_of_ker hfr hpm hu hx'
  have hgoal : u i - u j = 0 := by
    rw [hd]
    simp
  simpa [hdRo7A3BasicAux_coordForm, hdRo7A3BasicAux_coord, hdRo7A3BasicAux_pairMap,
    LinearMap.fst_apply, LinearMap.comp_apply, LinearMap.sub_apply] using hgoal

theorem a3_exists_perm (hfr : A3Frame p m θ z) (hpm : p ∣ m) (σ : Equiv.Perm (Fin m)) :
    ∃ a : V ≃ₗ[ZMod p] V, (∀ u ∈ a3Aug p m, a (θ u) = θ (fun i => u (σ.symm i))) ∧ a z = z := by
  let F : (↥(a3Aug p m) × ZMod p) →ₗ[ZMod p] V :=
    hdRo7A3BasicAux_pairMap θ z LinearMap.id
  let G : (↥(a3Aug p m) × ZMod p) →ₗ[ZMod p] V :=
    hdRo7A3BasicAux_pairMap θ z (hdRo7A3BasicAux_permLM σ)
  let G' : (↥(a3Aug p m) × ZMod p) →ₗ[ZMod p] V :=
    hdRo7A3BasicAux_pairMap θ z (hdRo7A3BasicAux_permLM σ.symm)
  have hF : Function.Surjective F := hdRo7A3BasicAux_pairMap_surjective hfr
  have hker : LinearMap.ker F ≤ LinearMap.ker G := hdRo7A3BasicAux_ker_le_perm hfr hpm σ
  have hker' : LinearMap.ker F ≤ LinearMap.ker G' := hdRo7A3BasicAux_ker_le_perm hfr hpm σ.symm
  let a : V →ₗ[ZMod p] V := hdRo7A3BasicAux_liftQ F hF G hker
  let b : V →ₗ[ZMod p] V := hdRo7A3BasicAux_liftQ F hF G' hker'
  have haF : ∀ x, a (F x) = G x := fun x => hdRo7A3BasicAux_liftQ_apply F hF G hker x
  have hbF : ∀ x, b (F x) = G' x := fun x => hdRo7A3BasicAux_liftQ_apply F hF G' hker' x
  have hcomp1 : a.comp b = LinearMap.id := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨⟨u, hu⟩, c⟩, rfl⟩ := hF v
    show a (b (F (⟨u, hu⟩, c))) = F (⟨u, hu⟩, c)
    rw [hbF]
    have hG'F : G' (⟨u, hu⟩, c) = F (⟨fun i => u (σ i), a3Aug_perm hu σ⟩, c) := by
      simp [G', F, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM, Equiv.symm_symm]
    rw [hG'F, haF]
    simp [G, F, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM]
  have hcomp2 : b.comp a = LinearMap.id := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨⟨u, hu⟩, c⟩, rfl⟩ := hF v
    show b (a (F (⟨u, hu⟩, c))) = F (⟨u, hu⟩, c)
    rw [haF]
    have hGF : G (⟨u, hu⟩, c) = F (⟨fun i => u (σ.symm i), a3Aug_perm hu σ.symm⟩, c) := by
      simp [G, F, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM]
    rw [hGF, hbF]
    simp [G', F, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM, Equiv.symm_symm]
  let e : V ≃ₗ[ZMod p] V := LinearEquiv.ofLinearMap a b hcomp1 hcomp2
  have he : (e : V →ₗ[ZMod p] V) = a := rfl
  refine ⟨e, ?_, ?_⟩
  · intro u hu
    have h := haF (⟨u, hu⟩, 0)
    have hF0 : F (⟨u, hu⟩, 0) = θ u := by simp [F, hdRo7A3BasicAux_pairMap]
    have hG0 : G (⟨u, hu⟩, 0) = θ (fun i => u (σ.symm i)) := by
      simp [G, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM]
    calc e (θ u) = a (θ u) := rfl
      _ = a (F (⟨u, hu⟩, 0)) := by rw [hF0]
      _ = G (⟨u, hu⟩, 0) := h
      _ = θ (fun i => u (σ.symm i)) := hG0
  · have h := haF (⟨0, zero_mem _⟩, 1)
    have hF1 : F (⟨0, zero_mem _⟩, 1) = z := by
      simp [F, hdRo7A3BasicAux_pairMap]
    have hG1 : G (⟨0, zero_mem _⟩, 1) = z := by
      have h0 : (fun i : Fin m => (0 : ZMod p)) = 0 := rfl
      simp [G, hdRo7A3BasicAux_pairMap, hdRo7A3BasicAux_permLM, h0]
    calc e z = a z := rfl
      _ = a (F (⟨0, zero_mem _⟩, 1)) := by rw [hF1]
      _ = G (⟨0, zero_mem _⟩, 1) := h
      _ = z := hG1

theorem a3P_ext (hfr : A3Frame p m θ z) {a b : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin m)}
    (ha : ∀ u ∈ a3Aug p m, a (θ u) = θ (fun i => u (σ.symm i))) (haz : a z = z)
    (hb : ∀ u ∈ a3Aug p m, b (θ u) = θ (fun i => u (σ.symm i))) (hbz : b z = z) : a = b := by
  obtain ⟨-, hsurj, -⟩ := hfr
  ext v
  obtain ⟨u, hu, c, rfl⟩ := hsurj v
  simp only [map_add, map_smul]
  rw [ha u hu, hb u hu, haz, hbz]

theorem a3_perm_unique (hfr : A3Frame p m θ z) (hm : 5 ≤ m) {σ τ : Equiv.Perm (Fin m)}
    (h : ∀ u ∈ a3Aug p m, θ (fun i => u (σ.symm i)) = θ (fun i => u (τ.symm i))) : σ = τ :=
  hdRo7A3BasicAux_perm_eq_of_pair_sets (by omega) fun i j hij =>
    hdRo7A3BasicAux_pair_sets hfr hm h hij

private lemma hdRo7A3BasicAux_swap_symm {i j : Fin m} :
    (Equiv.swap i j).symm = Equiv.swap i j := by
  apply Equiv.ext
  intro k
  exact (Equiv.symm_apply_eq (Equiv.swap i j)).mpr (Equiv.swap_apply_self i j k).symm

private lemma hdRo7A3BasicAux_swap_fun {i j : Fin m} (hij : i ≠ j) (u : Fin m → ZMod p) :
    (fun k => u ((Equiv.swap i j).symm k)) =
      u - (u i - u j) • ((Pi.single i (1 : ZMod p) : Fin m → ZMod p) -
        (Pi.single j (1 : ZMod p) : Fin m → ZMod p)) := by
  rw [hdRo7A3BasicAux_swap_symm]
  funext k
  rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Pi.single_apply,
    Equiv.swap_apply_def]
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj]

private lemma hdRo7A3BasicAux_neg_two_eq_one : (-(2 : ZMod 3)) = 1 := by decide

theorem a3_transp (hp : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm : 3 ≤ m) {i j : Fin m}
    (hij : i ≠ j) :
    ∃ (t : V ≃ₗ[ZMod p] V) (ψ : Module.Dual (ZMod p) V),
      (∀ u ∈ a3Aug p m, t (θ u) = θ (fun k => u ((Equiv.swap i j).symm k))) ∧ t z = z ∧
      (∀ u ∈ a3Aug p m, ψ (θ u) = u i - u j) ∧ ψ z = 0 ∧
      (∀ v, t v = v - ψ v • θ (Pi.single i 1 - Pi.single j 1)) ∧ GGLinRefl t := by
  subst hp
  obtain ⟨t, ht, htz⟩ := a3_exists_perm hfr hpm (Equiv.swap i j)
  let root : V := θ (Pi.single i 1 - Pi.single j 1)
  let F : (↥(a3Aug 3 m) × ZMod 3) →ₗ[ZMod 3] V :=
    hdRo7A3BasicAux_pairMap θ z LinearMap.id
  have hF : Function.Surjective F := hdRo7A3BasicAux_pairMap_surjective hfr
  have hkerφ : LinearMap.ker F ≤ LinearMap.ker (hdRo7A3BasicAux_coordForm i j) :=
    hdRo7A3BasicAux_ker_le_coord hfr hpm i j
  let ψ : Module.Dual (ZMod 3) V :=
    hdRo7A3BasicAux_liftQ F hF (hdRo7A3BasicAux_coordForm i j) hkerφ
  have hψF : ∀ x, ψ (F x) = hdRo7A3BasicAux_coordForm i j x :=
    fun x => hdRo7A3BasicAux_liftQ_apply F hF (hdRo7A3BasicAux_coordForm i j) hkerφ x
  have hψu : ∀ u ∈ a3Aug 3 m, ψ (θ u) = u i - u j := by
    intro u hu
    have h := hψF (⟨u, hu⟩, 0)
    have hF0 : F (⟨u, hu⟩, 0) = θ u := by simp [F, hdRo7A3BasicAux_pairMap]
    rw [hF0] at h
    simpa [hdRo7A3BasicAux_coordForm, hdRo7A3BasicAux_coord] using h
  have hψz : ψ z = 0 := by
    have h := hψF (⟨0, zero_mem _⟩, 1)
    have hF1 : F (⟨0, zero_mem _⟩, 1) = z := by simp [F, hdRo7A3BasicAux_pairMap]
    rw [hF1] at h
    simpa [hdRo7A3BasicAux_coordForm, hdRo7A3BasicAux_coord] using h
  have hψroot : ψ root = 2 := by
    have h := hψu _ (a3_single_sub_mem i j)
    have h2 : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) -
        (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3)) i -
        ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) -
        (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3)) j = 2 := by
      simp [Pi.sub_apply, hij]
      ring
    exact h.trans h2
  have hformula : ∀ v, t v = v - ψ v • root := by
    intro v
    obtain ⟨⟨⟨u, hu⟩, c⟩, rfl⟩ := hF v
    have hFapply : F (⟨u, hu⟩, c) = θ u + c • z := by
      simp [F, hdRo7A3BasicAux_pairMap]
    have htapply : t (F (⟨u, hu⟩, c)) =
        θ (fun k => u ((Equiv.swap i j).symm k)) + c • z := by
      rw [hFapply]
      simp only [map_add, map_smul]
      rw [ht u hu, htz]
    have hψv : ψ (F (⟨u, hu⟩, c)) = u i - u j := by
      have h := hψF (⟨u, hu⟩, c)
      simpa [hdRo7A3BasicAux_coordForm, hdRo7A3BasicAux_coord, F,
        hdRo7A3BasicAux_pairMap] using h
    rw [htapply, hdRo7A3BasicAux_swap_fun hij, map_sub, map_smul, hψv, hFapply]
    dsimp only [root]
    module
  have htt : t * t = 1 := by
    apply a3P_ext hfr (σ := 1)
    · intro u hu
      have hu' : (fun k => u ((Equiv.swap i j).symm k)) ∈ a3Aug 3 m :=
        a3Aug_perm hu (Equiv.swap i j).symm
      rw [LinearEquiv.mul_apply, ht u hu, ht _ hu']
      congr 1
      funext k
      rw [hdRo7A3BasicAux_swap_symm]
      exact congrArg u (Equiv.swap_apply_self i j k)
    · rw [LinearEquiv.mul_apply, htz, htz]
    · intro u hu
      rfl
    · rfl
  have hroot_ne : root ≠ 0 := a3_theta_single_sub_ne_zero hfr hm hij
  have hrange : ggLinMove t = Submodule.span (ZMod 3) {root} := by
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      have hsub : (t.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) v =
          -(ψ v) • root := by
        change t v - v = -(ψ v) • root
        rw [hformula v]
        module
      rw [hsub]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton root))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨root, ?_⟩
      have hsub : (t.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) root =
          -(ψ root) • root := by
        change t root - root = -(ψ root) • root
        rw [hformula root]
        module
      rw [hsub, hψroot]
      have hneg : (-(2 : ZMod 3)) = 1 := hdRo7A3BasicAux_neg_two_eq_one
      rw [hneg, one_smul]
  refine ⟨t, ψ, ht, htz, hψu, hψz, hformula, htt, ?_⟩
  rw [hrange, finrank_span_singleton hroot_ne]

end Frame

end CFSG.StandardType.HdRo7A3
