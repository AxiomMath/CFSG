module

public import CFSG.Quasithin.EmptyFaithful.S143NK
public import CFSG.Quasithin.EmptyFaithful.S143ND

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section IndexTwo

variable {A : Type*} [Group A] {Ω K : Subgroup A}

theorem conj_mem_of_relIndex_two (hle : Ω ≤ K) (h : Ω.relIndex K = 2) {x y : A} (hx : x ∈ K)
    (hy : y ∈ Ω) : x * y * x⁻¹ ∈ Ω := by
  have hn : (Ω.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h
  have := hn.conj_mem ⟨y, hle hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem mul_self_mem_of_relIndex_two (h : Ω.relIndex K = 2) {x : A} (hx : x ∈ K) : x * x ∈ Ω := by
  have := Subgroup.mul_self_mem_of_index_two h ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem mem_of_cube_of_relIndex_two (h : Ω.relIndex K = 2) {x : A} (hx : x ∈ K) (h3 : x ^ 3 = 1) :
    x ∈ Ω := by
  have h2 := mul_self_mem_of_relIndex_two h hx
  have h3' : x * (x * x) = 1 := by
    rw [← pow_three]
    exact h3
  have : x = (x * x)⁻¹ := eq_inv_of_mul_eq_one_left h3'
  rw [this]
  exact Ω.inv_mem h2

end IndexTwo

section Omega

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

section Pkg

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.exists_OmegaPkg :
    ∃ Ω : Subgroup (MulAut (UT T M)), Ω ≤ c.actK.range ∧ Ω.relIndex c.actK.range = 2 ∧
      Nat.card ↥Ω = 36 ∧ Nonempty (↥Ω ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      c.alphaOf hrW hrV hr2 ∈ Ω := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup (UT T M) :=
    { (inferInstance : Group (UT T M)) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  have hrange : c.actK.range = orthogonalGroupOf q := c.actK_range.trans hq6
  obtain ⟨Ω, hΩO, hrel, hcard, hiso, hfix⟩ :=
    exists_Omega (W := UT T M) (q := q) (tilde_mul_self h) hq4 hq1 hq2 hq3
  refine ⟨Ω, by rw [hrange]; exact hΩO, by rw [hrange]; exact hrel, hcard, hiso, ?_⟩
  have hαT := c.alphaOf_mem_T hrW hrV hr2
  have hα1 := c.alphaOf_ne_one hrW hrV hr2
  have hα2 := c.alphaOf_sq hrW hrV hr2
  have hαx := c.alphaOf_tclsE hrW hrV hr2
  obtain ⟨hfixα, -⟩ := c.swap_facts hrW hrV hr2 hαT hα1 hα2 hαx
  have hαO : c.alphaOf hrW hrV hr2 ∈ orthogonalGroupOf q := by
    rw [← hrange]
    exact ⟨⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩, rfl⟩
  exact hfix _ hαO hα2 hfixα

end Pkg

section RQ

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)
  {Ω : Subgroup (MulAut (UT T M))} (hΩle : Ω ≤ c.actK.range)
  (hrel : Ω.relIndex c.actK.range = 2) (hα : c.alphaOf hrW hrV hr2 ∈ Ω)
  {t : G} (htT : t ∈ T)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)

include c hrW hrV hr2 hΩle hrel hα htT hAAt

theorem Counter.actK_rq_mem_Omega {ρ : G} (hρ : ρ ∈ rOf T M ⊔ qOf T) (hρH : ρ ∈ mcOf T) :
    c.actK ⟨ρ, hρH⟩ ∈ Ω := by
  set Dsub : Subgroup G := (Ω.comap c.actK).map (mcOf T).subtype with hD
  have hmemD : ∀ {w : G} (hw : w ∈ mcOf T), c.actK ⟨w, hw⟩ ∈ Ω → w ∈ Dsub := fun {w} hw h =>
    ⟨⟨w, hw⟩, h, rfl⟩
  have hDmem : ∀ {w : G}, w ∈ Dsub → ∃ hw : w ∈ mcOf T, c.actK ⟨w, hw⟩ ∈ Ω := by
    rintro w ⟨⟨w', hw'⟩, h, rfl⟩
    exact ⟨hw', h⟩
  have htH : t ∈ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H htT
  have hQD : qOf T ≤ Dsub := fun x hx =>
    hmemD (pCoreOf_le 2 _ hx) (by rw [c.actK_eq_one_of_mem_qOf hx]; exact Ω.one_mem)
  have hAD : c.Ac hrW hrV hr2 ≤ Dsub := fun a ha =>
    hmemD (c.Ac_le_mcOf hrW hrV hr2 ha) (by
      rcases c.actK_Ac hrW hrV hr2 ha with h | h
      · rw [h]; exact Ω.one_mem
      · rw [h]; exact hα)
  have hAtD : conjSubgroup (c.Ac hrW hrV hr2) t ≤ Dsub := by
    intro w hw
    have hwA : t * w * t⁻¹ ∈ c.Ac hrW hrV hr2 := mem_conjSubgroup_iff.mp hw
    have ha1 := hDmem (hAD hwA)
    obtain ⟨ha1H, ha1Ω⟩ := ha1
    have hwH : w ∈ mcOf T := by
      have e : w = t⁻¹ * (t * w * t⁻¹) * t := by group
      rw [e]
      exact (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem htH) ha1H) htH
    refine hmemD hwH ?_
    have e : (⟨w, hwH⟩ : ↥(mcOf T)) =
        (⟨t, htH⟩ : ↥(mcOf T))⁻¹ * ⟨t * w * t⁻¹, ha1H⟩ * (⟨t, htH⟩ : ↥(mcOf T)) :=
      Subtype.ext (by
        show w = t⁻¹ * (t * w * t⁻¹) * t
        group)
    rw [e, map_mul, map_mul, map_inv]
    have hxR : (c.actK ⟨t, htH⟩)⁻¹ ∈ c.actK.range := c.actK.range.inv_mem ⟨⟨t, htH⟩, rfl⟩
    have := conj_mem_of_relIndex_two hΩle hrel hxR ha1Ω
    simpa using this
  have hRD : rOf T M ≤ Dsub := by
    rw [hAAt]
    exact sup_le hAD hAtD
  have := sup_le hRD hQD hρ
  obtain ⟨hw, h⟩ := hDmem this
  exact h

end RQ

end Omega

section Centralizes

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_tclsE (w : UT T M) :
    ∃ (u : G) (hu : u ∈ uOfL22 T M), w = tclsE c.hUN hu := by
  obtain ⟨x, hxU, hxw⟩ := mem_secImg.1 w.2
  refine ⟨(x : G), hxU, ?_⟩
  apply Subtype.ext
  exact hxw.symm

theorem Counter.actK_eq_one_of_centralizes {x : G} (hxH : x ∈ mcOf T)
    (hx : ∀ u ∈ uOfL22 T M, x * u * x⁻¹ = u) : c.actK ⟨x, hxH⟩ = 1 := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨u, hu, rfl⟩ := c.exists_tclsE w
  have hu' : x * u * x⁻¹ ∈ uOfL22 T M := by rw [hx u hu]; exact hu
  show actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T) c.hHU ⟨x, hxH⟩
    (tclsE c.hUN hu) = tclsE c.hUN hu
  rw [actTilde_tclsE c.hUN (hHN_of T) c.hHU ⟨x, hxH⟩ hu hu']
  exact tclsE_congr c.hUN hu' hu (hx u hu)

end Centralizes


section DeltaFacts

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)

omit [Finite G] in
theorem mem_zpowers_of_sq_eq_one {δ : G} (h : δ * δ = 1) {w : G} (hw : w ∈ Subgroup.zpowers δ) :
    w = 1 ∨ w = δ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h2 : δ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

include hS htT htRQ hM hδ hδA in
theorem not_mem_uOfL22_delta : δ ∉ uOfL22 T M := by
  intro hδU
  have hδK : δ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    c.rOf_sup_uOfL22_le_kOf hrW hrV hr2 ((le_sup_right : uOfL22 T M ≤ rOf T M ⊔ uOfL22 T M) hδU)
  exact hδA (hS.kOf_inf_centralizer_le htT htRQ hM ⟨hδK, hδ⟩)

include hS htT htRQ hM hC1 hδ hδA in
theorem U_inf_zpowers_delta : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.zpowers δ → u = 1 := by
  intro u hu hu'
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  rcases mem_zpowers_of_sq_eq_one hδ2 hu' with h | h
  · exact h
  · exact absurd (h ▸ hu) (not_mem_uOfL22_delta hS htT htRQ hM hδ hδA)

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA in
theorem exists_decomp_of_qOf_centralizer (hq : qOf T = uOfL22 T M ⊔ dOf T M) {w : G}
    (hw : w ∈ qOf T) (hwδ : w * δ = δ * w) :
    ∃ u ∈ uOfL22 T M, ∃ e ∈ Subgroup.zpowers δ, w = u * e := by
  have hDN : dOf T M ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ hd.2
  rw [hq] at hw
  obtain ⟨u, hu, e, he, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDN).1 hw
  have hcu : δ * u = u * δ := (Subgroup.mem_centralizer_iff.mp hδD.2 u hu).symm
  have heδ : e * δ = δ * e := by
    have : u * (e * δ) = u * (δ * e) := by
      calc u * (e * δ) = (u * e) * δ := by group
        _ = δ * (u * e) := hwδ
        _ = (δ * u) * e := by group
        _ = (u * δ) * e := by rw [hcu]
        _ = u * (δ * e) := by group
    exact mul_left_cancel this
  have hz : z ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.z_V
  rcases centralizer_D_delta hS htT htRQ hM hP hVl hC1 hδD hδ hδA he heδ with h | h | h | h
  · exact ⟨u, hu, 1, one_mem _, by rw [h]⟩
  · exact ⟨u * z, (uOfL22 T M).mul_mem hu hz, 1, one_mem _, by rw [h]; group⟩
  · exact ⟨u, hu, δ, Subgroup.mem_zpowers δ, by rw [h]⟩
  · exact ⟨u * z, (uOfL22 T M).mul_mem hu hz, δ, Subgroup.mem_zpowers δ, by rw [h]; group⟩

end DeltaFacts

end S143

end CFSG.Quasithin
