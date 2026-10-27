module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceUAux

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

theorem hdRo7SUReduceUAux_sum_coord_eq_repr {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (v : V) :
    (∑ i, b.coord i) v = ∑ i, b.repr v i := by
  rw [LinearMap.sum_apply]
  simp only [Module.Basis.coord_apply]

theorem hdRo7SUReduceUAux_sum_perm {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (a : V ≃ₗ[ZMod p] V) (ha : SUPerm p b a) (v : V) :
    (∑ i, b.coord i) (a v) = (∑ i, b.coord i) v := by
  obtain ⟨σ, hσ⟩ := ha
  have hcoord : ∀ i, b.coord i (a v) = b.coord (σ.symm i) v := by
    intro i
    have h1 : b.coord i ∘ₗ (a : V →ₗ[ZMod p] V) = b.coord (σ.symm i) := by
      refine b.ext (fun j => ?_)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hσ j, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply]
      by_cases hij : σ j = i
      · have hji : j = σ.symm i := by rw [← hij, Equiv.symm_apply_apply]
        simp [hij, hji]
      · have hji : j ≠ σ.symm i := by
          intro h'; exact hij (by rw [h', Equiv.apply_symm_apply])
        simp [hij, hji]
    exact congrArg (fun f : V →ₗ[ZMod p] (ZMod p) => f v) h1
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp_rw [hcoord]
  exact Equiv.sum_comp σ.symm (fun i => b.coord i v)

theorem hdRo7SUReduceUAux_perm_ones {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (a : V ≃ₗ[ZMod p] V) (ha : SUPerm p b a) : a (SUOnes p b) = SUOnes p b := by
  obtain ⟨σ, hσ⟩ := ha
  unfold SUOnes
  rw [map_sum]
  simp_rw [hσ]
  exact Equiv.sum_comp σ (fun i => b i)

@[expose] noncomputable def hdRo7SUReduceUAux_proj {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) : V →ₗ[ZMod p] V :=
  LinearMap.id - (m : ZMod p)⁻¹ • (∑ i, b.coord i).smulRight (SUOnes p b)

theorem hdRo7SUReduceUAux_proj_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) (v : V) :
    hdRo7SUReduceUAux_proj b hm v =
      v - ((m : ZMod p)⁻¹ * (∑ i, b.coord i) v) • SUOnes p b := by
  simp only [hdRo7SUReduceUAux_proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_smul]

theorem hdRo7SUReduceUAux_proj_fix {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) (u : V)
    (hu : u ∈ SUAug p b) : hdRo7SUReduceUAux_proj b hm u = u := by
  rw [hdRo7SUReduceUAux_proj_apply]
  have hfu : (∑ i, b.coord i) u = 0 := LinearMap.mem_ker.mp hu
  rw [hfu, mul_zero, zero_smul, sub_zero]

theorem hdRo7SUReduceUAux_proj_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) (v : V) :
    hdRo7SUReduceUAux_proj b hm v ∈ SUAug p b := by
  rw [hdRo7SUReduceUAux_proj_apply]
  change (∑ i, b.coord i)
    (v - ((m : ZMod p)⁻¹ * (∑ i, b.coord i) v) • SUOnes p b) = 0
  rw [map_sub, map_smul, hdRo7SUReduceUAux_sum_ones b, smul_eq_mul]
  have h1 : (m : ZMod p)⁻¹ * (∑ i, b.coord i) v * (m : ZMod p) = (∑ i, b.coord i) v := by
    rw [mul_assoc, mul_comm ((∑ i, b.coord i) v) (m : ZMod p), ← mul_assoc,
      inv_mul_cancel₀ hm, one_mul]
  rw [h1]
  exact sub_self _

theorem hdRo7SUReduceUAux_proj_comm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0)
    (a : V ≃ₗ[ZMod p] V) (ha : SUPerm p b a) (v : V) :
    hdRo7SUReduceUAux_proj b hm (a v) = a (hdRo7SUReduceUAux_proj b hm v) := by
  rw [hdRo7SUReduceUAux_proj_apply, hdRo7SUReduceUAux_proj_apply, hdRo7SUReduceUAux_sum_perm b a ha v,
    map_sub, map_smul, hdRo7SUReduceUAux_perm_ones b a ha]


theorem hdRo7SUReduceUAux_irreducible (hP1 : SUPInvLeaf) {p : ℕ} [Fact p.Prime] {m : ℕ}
    [NeZero m] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V)
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : SULinData p m V b H A)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b)) (hm0 : (m : ZMod p) ≠ 0) :
    ∀ W' : Submodule (ZMod p) ↥(SUAug p b),
      (∀ a ∈ (hdRo7SUReduceUAux_res (SUAug p b) H hHK).range, ∀ w ∈ W', a w ∈ W') →
      W' = ⊥ ∨ W' = ⊤ := by
  intro W' hstab
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let Wv : Submodule (ZMod p) V := W'.map (SUAug p b).subtype
  have hWv : ∀ a, SUPerm p b a → ∀ w ∈ Wv, a w ∈ Wv := by
    intro a ha w hw
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
    have haH : a ∈ H := hD.hPH a ha
    have hmem : res ⟨a, haH⟩ ∈ res.range := MonoidHom.mem_range.mpr ⟨⟨a, haH⟩, rfl⟩
    have hstw := hstab (res ⟨a, haH⟩) hmem w' hw'
    refine ⟨res ⟨a, haH⟩ w', hstw, ?_⟩
    exact hdRo7SUReduceUAux_restrict_apply (SUAug p b) a (hHK haH) w'
  have hcases := hP1 p hD.hp m hD.hm hD.h3 V b Wv hWv
  rcases hcases with h | h | h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hthis : (SUAug p b).subtype w ∈ Wv := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    rw [h] at hthis
    exact Subtype.ext (by simpa using hthis)
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hthis : (SUAug p b).subtype w ∈ Wv := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    have hmemU : (SUAug p b).subtype w ∈ SUAug p b := w.2
    have hinf := hdRo7SUReduceUAux_inf_span_ones_eq_bot b hm0
    have hmemI : (SUAug p b).subtype w ∈ SUAug p b ⊓ Submodule.span (ZMod p) {SUOnes p b} := by
      rw [Submodule.mem_inf]
      exact ⟨hmemU, by rw [h] at hthis; exact hthis⟩
    rw [hinf] at hmemI
    exact Subtype.ext (by simpa using hmemI)
  · right
    rw [Submodule.eq_top_iff']
    intro w
    have hthis : (SUAug p b).subtype w ∈ Wv := by rw [h]; exact w.2
    obtain ⟨w', hw', hw'w⟩ := Submodule.mem_map.mp hthis
    have hw'w' : w' = w := Subtype.ext hw'w
    rwa [hw'w'] at hw'
  · exfalso
    have hle : Wv ≤ SUAug p b := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    rw [h] at hle
    exact hdRo7SUReduceUAux_ones_notMem_aug b hm0 (hle trivial)

theorem hdRo7SUReduceUAux_commutant (hP2 : SUPCentLeaf) {p : ℕ} [Fact p.Prime] {m : ℕ}
    [NeZero m] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V)
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : SULinData p m V b H A)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b)) (hm0 : (m : ZMod p) ≠ 0) :
    ∀ T : Module.End (ZMod p) ↥(SUAug p b),
      (∀ a ∈ (hdRo7SUReduceUAux_res (SUAug p b) H hHK).range,
        T ∘ₗ (a : ↥(SUAug p b) →ₗ[ZMod p] ↥(SUAug p b)) =
          (a : ↥(SUAug p b) →ₗ[ZMod p] ↥(SUAug p b)) ∘ₗ T) →
      ∃ c : ZMod p, T = c • LinearMap.id := by
  intro T hT
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let π : V →ₗ[ZMod p] V := hdRo7SUReduceUAux_proj b hm0
  let π' : V →ₗ[ZMod p] ↥(SUAug p b) :=
    π.codRestrict (SUAug p b) (hdRo7SUReduceUAux_proj_mem b hm0)
  let T' : V →ₗ[ZMod p] V := (SUAug p b).subtype.comp (T.comp π')
  have hT'comm : ∀ a, SUPerm p b a →
      T' ∘ₗ (a : V →ₗ[ZMod p] V) = (a : V →ₗ[ZMod p] V) ∘ₗ T' := by
    intro a ha
    ext v
    have haH : a ∈ H := hD.hPH a ha
    have hmem : res ⟨a, haH⟩ ∈ res.range := MonoidHom.mem_range.mpr ⟨⟨a, haH⟩, rfl⟩
    have hcomm := hT (res ⟨a, haH⟩) hmem
    have hπva : π (a v) = a (π v) := hdRo7SUReduceUAux_proj_comm b hm0 a ha v
    have h1 : π' (a v) = (hdRo7SUReduceUAux_restrict (SUAug p b) a (hHK haH)) (π' v) := by
      apply Subtype.ext
      exact hπva
    have h2 : T (π' (a v)) =
        (hdRo7SUReduceUAux_restrict (SUAug p b) a (hHK haH)) (T (π' v)) := by
      rw [h1]
      have hcomm' : T ∘ₗ (hdRo7SUReduceUAux_restrict (SUAug p b) a (hHK haH) :
          ↥(SUAug p b) →ₗ[ZMod p] ↥(SUAug p b)) =
          (hdRo7SUReduceUAux_restrict (SUAug p b) a (hHK haH) :
          ↥(SUAug p b) →ₗ[ZMod p] ↥(SUAug p b)) ∘ₗ T := hcomm
      exact LinearMap.congr_fun hcomm' (π' v)
    change T' (a v) = a (T' v)
    calc T' (a v) = (SUAug p b).subtype (T (π' (a v))) := rfl
      _ = (SUAug p b).subtype
            ((hdRo7SUReduceUAux_restrict (SUAug p b) a (hHK haH)) (T (π' v))) := by rw [h2]
      _ = a ((SUAug p b).subtype (T (π' v))) :=
            hdRo7SUReduceUAux_restrict_apply (SUAug p b) a (hHK haH) (T (π' v))
      _ = a (T' v) := rfl
  obtain ⟨α, β, hαβ⟩ := hP2 p hD.hp m hD.hm hD.h3 V b T' hT'comm
  refine ⟨α, ?_⟩
  apply LinearMap.ext
  intro u
  have hfix : T' (u : V) = T u := by
    change (SUAug p b).subtype (T (π' (u : V))) = T u
    have hπu : π' (u : V) = u := Subtype.ext (hdRo7SUReduceUAux_proj_fix b hm0 (u : V) u.2)
    rw [hπu]
    rfl
  have hthis := hαβ (u : V)
  rw [hfix] at hthis
  have hsum0 : ∑ i, b.repr (u : V) i = 0 := by
    have h := LinearMap.mem_ker.mp u.2
    rwa [hdRo7SUReduceUAux_sum_coord_eq_repr] at h
  rw [hsum0, mul_zero, zero_smul, add_zero] at hthis
  exact Subtype.ext (by simpa using hthis)


theorem hdRo7SUReduceUAux_move_map_restrict {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V) (s : V ≃ₗ[ZMod p] V)
    (hs : s ∈ hdRo7SUReduceUAux_kerAug p U) (hinv : s * s = 1) (h2 : (2 : ZMod p) ≠ 0) :
    (ggLinMove (hdRo7SUReduceUAux_restrict U s hs)).map U.subtype = ggLinMove s := by
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
  have hcomp : U.subtype.comp ((hdRo7SUReduceUAux_restrict U s hs).toLinearMap -
        (LinearMap.id : ↥U →ₗ[ZMod p] ↥U)) =
      (s.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)).comp U.subtype := by
    ext u
    change (((hdRo7SUReduceUAux_restrict U s hs) u : ↥U) : V) - (u : V) = s (u : V) - (u : V)
    rw [hdRo7SUReduceUAux_restrict_apply]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    rw [← hu]
    simpa using (LinearMap.congr_fun hcomp u).symm
  · intro w hw
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
    have hwU : w ∈ U := by rw [← hv]; exact hs v
    have hsw : s w = -w := by
      rw [← hv]
      change s (s v - v) = -(s v - v)
      rw [map_sub, show s (s v) = v from by rw [← LinearEquiv.mul_apply, hinv]; rfl]
      abel
    have hfw : (s.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) w = (-2 : ZMod p) • w := by
      have h1 : s.toLinearMap w = -w := hsw
      rw [LinearMap.sub_apply, LinearMap.id_apply, h1]
      rw [show -w - w = -(w + w) by abel, ← two_smul (ZMod p) w]
      exact (neg_smul (2 : ZMod p) w).symm
    rw [Submodule.mem_map]
    refine ⟨⟨w, hwU⟩, ?_, rfl⟩
    refine LinearMap.mem_range.mpr ⟨⟨(-2 : ZMod p)⁻¹ • w, U.smul_mem _ hwU⟩, ?_⟩
    apply Subtype.ext
    have hcu := LinearMap.congr_fun hcomp ⟨(-2 : ZMod p)⁻¹ • w, U.smul_mem _ hwU⟩
    refine hcu.trans ?_
    change (s.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) ((-2 : ZMod p)⁻¹ • w) = w
    rw [map_smul, hfw, smul_smul, inv_mul_cancel₀ hneg2, one_smul]


theorem hdRo7SUReduceUAux_refl_restrict {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V) (s : V ≃ₗ[ZMod p] V)
    (hs : s ∈ hdRo7SUReduceUAux_kerAug p U) (hinv : s * s = 1) (h2 : (2 : ZMod p) ≠ 0)
    (hfr : Module.finrank (ZMod p) (ggLinMove s) = 1) :
    GGLinRefl (hdRo7SUReduceUAux_restrict U s hs) := by
  have hmap := hdRo7SUReduceUAux_move_map_restrict U s hs hinv h2
  refine ⟨?_, ?_⟩
  · ext u
    change s (s u) = u
    rw [show s (s u) = (s * s) u from (LinearEquiv.mul_apply s s u).symm, hinv]
    rfl
  · rw [← Submodule.finrank_map_subtype_eq U (ggLinMove (hdRo7SUReduceUAux_restrict U s hs)),
      hmap]
    exact hfr

theorem hdRo7SUReduceUAux_range_eq_closure {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (S : Set (V ≃ₗ[ZMod p] V)) (hS : ∀ s ∈ S, s ∈ H ∧ GGLinRefl s)
    (hScl : H = Subgroup.closure S)
    (h2 : (2 : ZMod p) ≠ 0) :
    (hdRo7SUReduceUAux_res (SUAug p b) H hHK).range =
      Subgroup.closure {r | r ∈ (hdRo7SUReduceUAux_res (SUAug p b) H hHK).range ∧
        GGLinRefl r} := by
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let S' : Set ↥H := {g | (g : V ≃ₗ[ZMod p] V) ∈ S}
  have hS'img : H.subtype '' S' = S := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hx
      exact ⟨⟨x, (hS x hx).1⟩, hx, rfl⟩
  have hmap : Subgroup.map H.subtype (Subgroup.closure S') = H := by
    rw [MonoidHom.map_closure, hS'img, hScl]
  have hS'gen : Subgroup.closure S' = ⊤ := by
    apply le_antisymm le_top
    intro g _
    have hg : (g : V ≃ₗ[ZMod p] V) ∈ Subgroup.map H.subtype (Subgroup.closure S') := by
      rw [hmap]; exact g.2
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    have hkg' : k = g := Subtype.ext hkg
    rwa [hkg'] at hk
  have hrange : res.range = Subgroup.closure (res '' S') := by
    rw [MonoidHom.range_eq_map, ← hS'gen, MonoidHom.map_closure]
  have himage : res '' S' ⊆ {r | r ∈ res.range ∧ GGLinRefl r} := by
    rintro r ⟨g, hgS, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    have hrefl : GGLinRefl (g : V ≃ₗ[ZMod p] V) := (hS (g : V ≃ₗ[ZMod p] V) hgS).2
    have hthis := hdRo7SUReduceUAux_refl_restrict (SUAug p b) g.1 (hHK g.2)
      (by simpa using hrefl.1) h2 hrefl.2
    change GGLinRefl (hdRo7SUReduceUAux_restrict (SUAug p b) g.1 (hHK g.2))
    exact hthis
  rw [hrange] at himage
  apply le_antisymm
  · rw [hrange]
    exact Subgroup.closure_mono himage
  · exact (Subgroup.closure_le _).mpr (fun r hr => hr.1)

theorem hdRo7SUReduceUAux_card_range {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (hresinj : Function.Injective (hdRo7SUReduceUAux_res (SUAug p b) H hHK)) :
    Nat.card ↥(hdRo7SUReduceUAux_res (SUAug p b) H hHK).range = Nat.card ↥H := by
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let f : ↥H → ↥res.range := fun g => ⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hresinj
      exact congrArg Subtype.val hab
    · rintro ⟨r, hr⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
      exact ⟨g, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm


theorem hdRo7SUReduceUAux_linWeyl_lift {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (h2 : (2 : ZMod p) ≠ 0)
    (hresinj : Function.Injective (hdRo7SUReduceUAux_res (SUAug p b) H hHK)) :
    ZS.LinWeyl p (hdRo7SUReduceUAux_res (SUAug p b) H hHK).range → ZS.LinWeyl p H := by
  intro hR
  obtain ⟨ι, M, hM, f, hf⟩ := hR
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let eHom : ↥H →* ↥res.range :=
    { toFun := fun g => ⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have heHom : Function.Bijective eHom := by
    constructor
    · intro a b hab
      apply hresinj
      exact congrArg Subtype.val hab
    · rintro ⟨r, hr⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
      exact ⟨g, rfl⟩
  let e : ↥H ≃* ↥res.range := MulEquiv.ofBijective eHom heHom
  refine ⟨ι, M, hM, f.trans e.symm, ?_⟩
  intro i
  let gH : ↥H := e.symm (f (M.simple i))
  let gV : V ≃ₗ[ZMod p] V := gH
  have hres_e : res gH = (f (M.simple i)).1 :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply e (f (M.simple i)))
  have hsq : gH * gH = 1 := by
    apply hresinj
    rw [map_mul, map_one, hres_e]
    exact (hf i).1
  have hsqV : gV * gV = 1 := by
    change (gH : V ≃ₗ[ZMod p] V) * (gH : V ≃ₗ[ZMod p] V) = 1
    simpa using congrArg Subtype.val hsq
  have hfr : Module.finrank (ZMod p) (ggLinMove gV) = 1 := by
    have hmap := hdRo7SUReduceUAux_move_map_restrict (SUAug p b) gV (hHK gH.2) hsqV h2
    rw [← hmap, Submodule.finrank_map_subtype_eq]
    change Module.finrank (ZMod p) (ggLinMove (res gH)) = 1
    rw [hres_e]
    exact (hf i).2
  have : ZS.IsRefl p gV := ⟨hsqV, hfr⟩
  simpa [gV, gH] using this

theorem hdRo7SUReduceUAux_card_le {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm0 : (m : ZMod p) ≠ 0)
    (hN : SUNormalizerLeaf) (hP3 : SUStabCardLeaf)
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : SULinData p m V b H A)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b)) :
    Nat.card ↥H ≤ 2 * 3 ^ (m - 1) * ((m - 1 + 1).factorial) := by
  haveI hfinV : Fintype V := Fintype.ofEquiv (Fin m →₀ ZMod p) b.repr.toEquiv.symm
  haveI hfinFun : Fintype (V → V) := Fintype.ofFinite (V → V)
  haveI hfinEnd : Fintype (V ≃ₗ[ZMod p] V) :=
    Fintype.ofInjective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun v => congrArg (fun f : V → V => f v) h))
  have hm7 : 7 ≤ m := hD.hm
  haveI hfinH : Fintype ↥H := Fintype.ofFinite ↥H
  haveI hfinU : Fintype ↥(SUAug p b) := Fintype.ofFinite ↥(SUAug p b)
  let x : V := SUOnes p b
  haveI hfinOrb : Fintype (MulAction.orbit ↥H x) := Fintype.ofFinite _
  haveI hfinStab : Fintype (MulAction.stabilizer ↥H x) := Fintype.ofFinite _
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥H) x
  have hcardNat :
      Nat.card (MulAction.orbit ↥H x) * Nat.card (MulAction.stabilizer ↥H x) = Nat.card ↥H := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hcard
  have horbit : Nat.card (MulAction.orbit ↥H x) ≤ 3 ^ (m - 1) := by
    have hinj : Function.Injective (fun y : MulAction.orbit ↥H x =>
        (⟨y.1 - x, by
          obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.2
          rw [← hg]
          exact hHK g.2 x⟩ : ↥(SUAug p b))) := by
      intro y1 y2 h
      have hz : y1.1 - x = y2.1 - x := congrArg Subtype.val h
      apply Subtype.ext
      have := congrArg (fun z : V => z + x) hz
      simpa using this
    have hle := Nat.card_le_card_of_injective _ hinj
    have hcardU : Nat.card ↥(SUAug p b) = 3 ^ (m - 1) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := ↥(SUAug p b)),
        ZMod.card, hdRo7SUReduceUAux_finrank_aug b hm0, hD.hp]
    rwa [hcardU] at hle
  have hstab : Nat.card (MulAction.stabilizer ↥H x) ≤ 2 * m.factorial := by
    let est : MulAction.stabilizer ↥H x ≃
        {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a x = x} :=
      { toFun := fun g => ⟨(g.1 : V ≃ₗ[ZMod p] V), g.1.2, MulAction.mem_stabilizer_iff.mp g.2⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, by
          rw [MulAction.mem_stabilizer_iff]
          exact a.2.2⟩
        left_inv := by intro g; ext; rfl
        right_inv := by intro a; ext; rfl }
    rw [Nat.card_congr est]
    exact hP3 hN p m V b H A hD
  calc Nat.card ↥H = Nat.card (MulAction.orbit ↥H x) * Nat.card (MulAction.stabilizer ↥H x) :=
        hcardNat.symm
    _ ≤ 3 ^ (m - 1) * (2 * m.factorial) := Nat.mul_le_mul horbit hstab
    _ = 2 * 3 ^ (m - 1) * ((m - 1 + 1).factorial) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        ring

end CFSG.StandardType.HdRo7SU
