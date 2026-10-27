module

public import CFSG.Monster.B.Recog.GenericCovering
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.Recog

open SimpleGraph

section CosetGraph

variable {Z : Type*} [Group Z]

@[expose] def cosetGraph (K : Subgroup Z) (s : Z) : SimpleGraph (Z ⧸ K) :=
  SimpleGraph.fromRel fun x y => ∃ z : Z, x = (z : Z ⧸ K) ∧ y = ((z * s : Z) : Z ⧸ K)

variable {K : Subgroup Z} {s : Z}

theorem cosetGraph_adj_mk_iff (hs : s ∉ K) (hs₂ : s * s ∈ K) {z : Z} {y : Z ⧸ K} :
    (cosetGraph K s).Adj (z : Z ⧸ K) y ↔ ∃ a ∈ K, y = ((z * a * s : Z) : Z ⧸ K) := by
  rw [cosetGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨z', hz', rfl⟩ | ⟨z', rfl, hz'⟩⟩
    · rw [QuotientGroup.eq] at hz'
      exact ⟨z⁻¹ * z', hz', by rw [mul_inv_cancel_left]⟩
    · rw [QuotientGroup.eq] at hz'
      refine ⟨z⁻¹ * (z' * s), hz', ?_⟩
      rw [QuotientGroup.eq]
      have : z' = z * (z⁻¹ * (z' * s)) * s⁻¹ := by group
      rw [this]
      convert hs₂ using 1
      group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun h => hs ?_, Or.inl ⟨z * a, ?_, rfl⟩⟩
    · rw [QuotientGroup.eq] at h
      have : s = a⁻¹ * (z⁻¹ * (z * a * s)) := by group
      rw [this]
      exact K.mul_mem (K.inv_mem ha) h
    · rw [QuotientGroup.eq]
      simpa using ha

theorem cosetGraph_adj_mk_mul (hs : s ∉ K) (hs₂ : s * s ∈ K) (z : Z) {c : Z}
    (hc : s⁻¹ * c ∈ K) : (cosetGraph K s).Adj (z : Z ⧸ K) ((z * c : Z) : Z ⧸ K) := by
  rw [cosetGraph_adj_mk_iff hs hs₂]
  refine ⟨1, K.one_mem, ?_⟩
  rw [QuotientGroup.eq]
  convert K.inv_mem hc using 1
  group

theorem cosetGraph_adj_smul {x y : Z ⧸ K} (g : Z) (h : (cosetGraph K s).Adj x y) :
    (cosetGraph K s).Adj (g • x) (g • y) := by
  rw [cosetGraph, SimpleGraph.fromRel_adj] at h ⊢
  refine ⟨fun hxy => h.1 (smul_left_cancel g hxy), ?_⟩
  rcases h.2 with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
  · exact Or.inl ⟨g * z, by simp [MulAction.Quotient.smul_mk], by
      simp [MulAction.Quotient.smul_mk, mul_assoc]⟩
  · exact Or.inr ⟨g * z, by simp [MulAction.Quotient.smul_mk], by
      simp [MulAction.Quotient.smul_mk, mul_assoc]⟩

@[expose] def cosetGraphSMul (K : Subgroup Z) (s g : Z) : cosetGraph K s →g cosetGraph K s where
  toFun x := g • x
  map_rel' h := cosetGraph_adj_smul g h

end CosetGraph

section Covering

variable {V : Type*} {G : SimpleGraph V} {X : Type*} [Group X] [MulAction X V]
  {Z : Type*} [Group Z]

@[expose] def cosetMap (p : Z →* X) (K : Subgroup Z) (v : V) (hK : ∀ a ∈ K, p a • v = v) :
    Z ⧸ K → V :=
  Quotient.lift (fun z => p z • v) fun a b hab => by
    have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    calc p a • v = p a • p (a⁻¹ * b) • v := by rw [hK _ hab']
      _ = p b • v := by rw [smul_smul, ← map_mul, mul_inv_cancel_left]

theorem cosetMap_mk (p : Z →* X) (K : Subgroup Z) (v : V) (hK : ∀ a ∈ K, p a • v = v) (z : Z) :
    cosetMap p K v hK (z : Z ⧸ K) = p z • v := rfl

@[expose] def cosetHom (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (p : Z →* X) (K : Subgroup Z) (s : Z) (v : V) (hK : ∀ a ∈ K, p a • v = v)
    (hs : G.Adj v (p s • v)) : cosetGraph K s →g G where
  toFun := cosetMap p K v hK
  map_rel' {x y} h := by
    rw [cosetGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
    · simpa [cosetMap_mk, mul_smul] using hadj (p z) hs
    · simpa [cosetMap_mk, mul_smul] using (hadj (p z) hs).symm

theorem cosetHom_mk (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (p : Z →* X) (K : Subgroup Z) (s : Z) (v : V) (hK : ∀ a ∈ K, p a • v = v)
    (hs : G.Adj v (p s • v)) (z : Z) : cosetHom hadj p K s v hK hs (z : Z ⧸ K) = p z • v := rfl

namespace Tits

variable (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
  {v w : V} (hvw : G.Adj v w)
  {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
  (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
  (p : Z →* X) {Zv Ze : Subgroup Z}
  (hinjv : Set.InjOn p Zv) (hinje : Set.InjOn p Ze)
  (himv : Zv.map p = Xv) (hime : Ze.map p = Xe) (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p)

include hXv himv in
theorem smul_eq_of_mem {a : Z} (ha : a ∈ Zv) : p a • v = v :=
  (hXv _).1 (himv ▸ Subgroup.mem_map_of_mem p ha)

include hXv hinje hime hve in
theorem mem_of_mem_of_smul_eq {z : Z} (hz : z ∈ Ze) (hzv : p z • v = v) : z ∈ Zv := by
  obtain ⟨c, hc, hcz⟩ := hve ⟨(hXv _).2 hzv, hime ▸ Subgroup.mem_map_of_mem p hz⟩
  rw [← hinje hc.2 hz hcz]
  exact hc.1

include hXv hXe hinjv himv hve in
theorem mem_of_mem_of_smul_eq' {z : Z} (hz : z ∈ Zv) (hzw : p z • w = w) : z ∈ Ze := by
  have hzv : p z ∈ Xv := himv ▸ Subgroup.mem_map_of_mem p hz
  obtain ⟨c, hc, hcz⟩ := hve ⟨hzv, (hXe _).2 (Or.inl ⟨(hXv _).1 hzv, hzw⟩)⟩
  rw [← hinjv hc.1 hz hcz]
  exact hc.2

include hXe hime in
theorem exists_swap_lift (hswap : ∃ g : X, g • v = w ∧ g • w = v) :
    ∃ s ∈ Ze, p s • v = w ∧ p s • w = v := by
  obtain ⟨g, hgv, hgw⟩ := hswap
  obtain ⟨s, hs, rfl⟩ : g ∈ Ze.map p := hime ▸ (hXe g).2 (Or.inr ⟨hgv, hgw⟩)
  exact ⟨s, hs, hgv, hgw⟩

include hvw hXv himv in
theorem not_mem_of_smul_eq {s : Z} (hsv : p s • v = w) : s ∉ Zv := fun h =>
  hvw.ne ((smul_eq_of_mem hXv p himv h).symm.trans hsv)

include hXv hinje hime hve in
theorem mul_self_mem {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w) (hsw : p s • w = v) :
    s * s ∈ Zv :=
  mem_of_mem_of_smul_eq hXv p hinje hime hve (Ze.mul_mem hsZe hsZe)
    (by rw [map_mul, mul_smul, hsv, hsw])

include hadj hvw hXv hXe hinjv hinje himv hime hve in
theorem isCovering_cosetHom (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w) (hsw : p s • w = v) :
    IsCovering (cosetHom hadj p Zv s v (fun _ ha => smul_eq_of_mem hXv p himv ha)
      (hsv ▸ hvw)) := by
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  refine IsCovering.of_existsUnique fun x y hxy => ?_
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [cosetHom_mk] at hxy
  have hy : G.Adj v ((p z)⁻¹ • y) := by simpa using hadj (p z)⁻¹ hxy
  obtain ⟨g, hgv, hgw⟩ := hloc _ hy
  obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map p := himv ▸ (hXv g).2 hgv
  refine ⟨((z * a * s : Z) : Z ⧸ Zv), ⟨(cosetGraph_adj_mk_iff hs hs₂).2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
  · rw [cosetHom_mk, map_mul, map_mul, mul_smul, mul_smul, hsv, hgw, smul_inv_smul]
  · rintro b ⟨hb, hby⟩
    obtain ⟨a', ha', rfl⟩ := (cosetGraph_adj_mk_iff hs hs₂).1 hb
    rw [cosetHom_mk, map_mul, map_mul, mul_smul, mul_smul, hsv] at hby
    have h₁ : p a' • w = p a • w := by rw [hgw, ← hby, inv_smul_smul]
    have hc : p (a'⁻¹ * a) • w = w := by rw [map_mul, mul_smul, ← h₁, map_inv, inv_smul_smul]
    have hcv : a'⁻¹ * a ∈ Zv := Zv.mul_mem (Zv.inv_mem ha') ha
    have hce : a'⁻¹ * a ∈ Ze := mem_of_mem_of_smul_eq' hXv hXe p hinjv himv hve hcv hc
    have hsc : s⁻¹ * (a'⁻¹ * a) * s ∈ Zv := by
      refine mem_of_mem_of_smul_eq hXv p hinje hime hve
        (Ze.mul_mem (Ze.mul_mem (Ze.inv_mem hsZe) hce) hsZe) ?_
      rw [map_mul, map_mul, mul_smul, mul_smul, hsv, hc, map_inv, inv_smul_eq_iff, hsv]
    rw [QuotientGroup.eq]
    convert hsc using 1
    group

theorem _root_.CFSG.Monster.B.Recog.cosetGraphSMul_apply (K : Subgroup Z) (s g : Z)
    (x : Z ⧸ K) : cosetGraphSMul K s g x = g • x := rfl

include hXv hXe hinje hime hve in
theorem reachable_cosetGraph {s : Z} (hs : s ∉ Zv) (hs₂ : s * s ∈ Zv) (hsZe : s ∈ Ze)
    (hsv : p s • v = w) {z : Z} (hz : z ∈ Zv ⊔ Ze) :
    (cosetGraph Zv s).Reachable ((1 : Z) : Z ⧸ Zv) (z : Z ⧸ Zv) := by
  have hcl : Zv ⊔ Ze = Subgroup.closure ((Zv : Set Z) ∪ Ze) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hcl] at hz
  have hone : ∀ x ∈ Zv, ((x : Z) : Z ⧸ Zv) = ((1 : Z) : Z ⧸ Zv) := fun x hx =>
    QuotientGroup.eq.2 (by simpa using Zv.inv_mem hx)
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [hone x hx]
    · rcases (hXe (p x)).1 (hime ▸ Subgroup.mem_map_of_mem p hx) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [hone x (mem_of_mem_of_smul_eq hXv p hinje hime hve hx h)]
      · refine SimpleGraph.Adj.reachable ?_
        have hsx : s⁻¹ * x ∈ Zv := mem_of_mem_of_smul_eq hXv p hinje hime hve
          (Ze.mul_mem (Ze.inv_mem hsZe) hx)
          (by rw [map_mul, mul_smul, h, map_inv, inv_smul_eq_iff, hsv])
        simpa using cosetGraph_adj_mk_mul hs hs₂ 1 hsx
  | one => rfl
  | mul x y _ _ ihx ihy =>
    refine ihx.trans ?_
    simpa [cosetGraphSMul_apply, MulAction.Quotient.smul_mk] using
      ihy.map (cosetGraphSMul Zv s x)
  | inv x _ ih =>
    refine SimpleGraph.Reachable.symm ?_
    simpa [cosetGraphSMul_apply, MulAction.Quotient.smul_mk] using
      ih.map (cosetGraphSMul Zv s x⁻¹)

variable {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
  (hinjt : ∀ j, Set.InjOn p (Zt j)) (himt : ∀ j, (Zt j).map p = Xt j)
  (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p)

include hXv hinjt himt hvt in
theorem mem_of_mem_tri_of_smul_eq {j : ι} {z : Z} (hz : z ∈ Zt j) (hzv : p z • v = v) :
    z ∈ Zv := by
  obtain ⟨c, hc, hcz⟩ := hvt j ⟨(hXv _).2 hzv, himt j ▸ Subgroup.mem_map_of_mem p hz⟩
  rw [← hinjt j hc.2 hz hcz]
  exact hc.1

include hXv hXe hinje hime hve hinjt himt hvt het in
theorem inv_mul_mem_of_tri {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w) {j : ι} {t r : Z}
    (ht : t ∈ Zt j) (htv : p t • v = w) (htw : p t • w = v) (hr : r ∈ Zt j)
    (hrv : p r • v = w) : s⁻¹ * r ∈ Zv := by
  obtain ⟨c, hc, hct⟩ :=
    het j ⟨(hXe _).2 (Or.inr ⟨htv, htw⟩), himt j ▸ Subgroup.mem_map_of_mem p ht⟩
  have htZe : t ∈ Ze := hinjt j hc.2 ht hct ▸ hc.1
  have h₁ : s⁻¹ * t ∈ Zv := mem_of_mem_of_smul_eq hXv p hinje hime hve
    (Ze.mul_mem (Ze.inv_mem hsZe) htZe)
    (by rw [map_mul, mul_smul, htv, map_inv, inv_smul_eq_iff, hsv])
  have h₂ : t⁻¹ * r ∈ Zv := mem_of_mem_tri_of_smul_eq hXv p hinjt himt hvt
    ((Zt j).mul_mem ((Zt j).inv_mem ht) hr)
    (by rw [map_mul, mul_smul, hrv, map_inv, inv_smul_eq_iff, htv])
  simpa [mul_assoc] using Zv.mul_mem h₁ h₂

include hadj hvw hXv hXe hinje himv hime hve hinjt himt hvt het in
theorem liftsTriangles_cosetHom {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w)
    (hsw : p s • w = v) (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂) :
    LiftsTriangles (cosetHom hadj p Zv s v (fun _ ha => smul_eq_of_mem hXv p himv ha)
      (hsv ▸ hvw)) := by
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  intro x y₁ y₂ h₁ h₂ h₃
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [cosetHom_mk] at h₁ h₃
  obtain ⟨j, g, hgv, hgw, hgu⟩ := htri ((p z)⁻¹ • y₁) ((p z)⁻¹ • y₂)
    (by simpa using hadj (p z)⁻¹ h₁) (hadj (p z)⁻¹ h₂) (by simpa using hadj (p z)⁻¹ h₃)
  obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map p := himv ▸ (hXv g).2 hgv
  obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
  obtain ⟨t, ht, rfl⟩ : τ ∈ (Zt j).map p := (himt j).symm ▸ hτm
  obtain ⟨ρ, hρm, hρv, hρw, hρu⟩ := hρ j
  obtain ⟨r, hr, rfl⟩ : ρ ∈ (Zt j).map p := (himt j).symm ▸ hρm
  have hsr : s⁻¹ * r ∈ Zv :=
    inv_mul_mem_of_tri hXv hXe p hinje hime hve hinjt himt hvt het hsZe hsv ht hτv hτw hr hρv
  have hr₃ : r * r * r ∈ Zv := mem_of_mem_tri_of_smul_eq hXv p hinjt himt hvt
    ((Zt j).mul_mem ((Zt j).mul_mem hr hr) hr) (by simp only [map_mul, mul_smul, hρv, hρw, hρu])
  have e₁ : ((z : Z) : Z ⧸ Zv) = ((z * a : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa using ha)
  have e₂ : ((z : Z) : Z ⧸ Zv) = ((z * a * r * r * r : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha hr₃)
  refine ⟨((z * a * r : Z) : Z ⧸ Zv), ((z * a * r * r : Z) : Z ⧸ Zv), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [e₂]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [cosetHom_mk, map_mul, map_mul, mul_smul, mul_smul, hρv, hgw, smul_inv_smul]
  · rw [cosetHom_mk, map_mul, map_mul, map_mul, mul_smul, mul_smul, mul_smul, hρv, hρw, hgu,
      smul_inv_smul]

end Tits

open Tits in
theorem injOn_sup_of_triangulable (hG : Triangulable G)
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    {v w : V} (hvw : G.Adj v w) (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X}
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    (p : Z →* X) {Zv Ze : Subgroup Z} {Zt : ι → Subgroup Z}
    (hinjv : Set.InjOn p Zv) (hinje : Set.InjOn p Ze) (hinjt : ∀ j, Set.InjOn p (Zt j))
    (himv : Zv.map p = Xv) (hime : Ze.map p = Xe) (himt : ∀ j, (Zt j).map p = Xt j)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p) (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p)
    (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p) :
    Set.InjOn p (Zv ⊔ Ze : Subgroup Z) := by
  obtain ⟨s, hsZe, hsv, hsw⟩ := exists_swap_lift hXe p hime hswap
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  have hcov := isCovering_cosetHom hadj hvw hXv hXe p hinjv hinje himv hime hve hloc hsZe hsv hsw
  have htr := liftsTriangles_cosetHom hadj hvw hXv hXe p hinje himv hime hve hinjt himt hvt het
    hsZe hsv hsw hτ hρ htri
  have key : ∀ z ∈ Zv ⊔ Ze, p z = 1 → z = 1 := by
    intro z hz hpz
    have heq := hcov.eq_of_reachable htr hG
      (reachable_cosetGraph hXv hXe p hinje hime hve hs hs₂ hsZe hsv hz)
      (by rw [cosetHom_mk, cosetHom_mk, hpz, map_one])
    have hzv : z ∈ Zv := by simpa using QuotientGroup.eq.1 heq
    exact hinjv hzv Zv.one_mem (by rw [hpz, map_one])
  intro z₁ h₁ z₂ h₂ h
  exact inv_mul_eq_one.1 (key _ ((Zv ⊔ Ze).mul_mem ((Zv ⊔ Ze).inv_mem h₁) h₂)
    (by rw [map_mul, map_inv, h, inv_mul_cancel]))

end Covering

theorem sup_eq_top_of_preconnected {V : Type*} {G : SimpleGraph V} {X : Type*} [Group X]
    [MulAction X V] (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hconn : G.Preconnected) {v w : V} (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v) {Xv Xe : Subgroup X}
    (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v)) :
    Xv ⊔ Xe = ⊤ := by
  obtain ⟨s, hsv, hsw⟩ := hswap
  have hs : s ∈ Xe := (hXe s).2 (Or.inr ⟨hsv, hsw⟩)
  have step : ∀ {a x : V} (q : G.Walk a x), (∃ k ∈ Xv ⊔ Xe, k • v = a) →
      ∃ k ∈ Xv ⊔ Xe, k • v = x := by
    intro a x q
    induction q with
    | nil => exact id
    | @cons a b x h q ih =>
      rintro ⟨k, hk, rfl⟩
      apply ih
      obtain ⟨g, hgv, hgw⟩ := hloc _ (by simpa using hadj k⁻¹ h)
      refine ⟨k * g * s, (Xv ⊔ Xe).mul_mem ((Xv ⊔ Xe).mul_mem hk
        (Subgroup.mem_sup_left ((hXv g).2 hgv))) (Subgroup.mem_sup_right hs), ?_⟩
      rw [mul_smul, mul_smul, hsv, hgw, smul_inv_smul]
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨q⟩ := hconn v (x • v)
  obtain ⟨k, hk, hkx⟩ := step q ⟨1, (Xv ⊔ Xe).one_mem, one_smul _ _⟩
  have : k⁻¹ * x ∈ Xv := (hXv _).2 (by rw [mul_smul, ← hkx, inv_smul_smul])
  simpa using (Xv ⊔ Xe).mul_mem hk (Subgroup.mem_sup_left this)

section HomGraph

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def homGraph {H : Subgroup X} (φ : H →* Y) : Subgroup (Y × X) :=
  (φ.prod H.subtype).range

theorem mem_homGraph {H : Subgroup X} {φ : H →* Y} {q : Y × X} :
    q ∈ homGraph φ ↔ ∃ a : H, (φ a, (a : X)) = q :=
  MonoidHom.mem_range

theorem mk_mem_homGraph {H : Subgroup X} (φ : H →* Y) (a : H) : (φ a, (a : X)) ∈ homGraph φ :=
  mem_homGraph.2 ⟨a, rfl⟩

theorem injOn_snd_homGraph {H : Subgroup X} (φ : H →* Y) :
    Set.InjOn (MonoidHom.snd Y X) (homGraph φ) := by
  rintro _ h₁ _ h₂ h
  obtain ⟨a₁, rfl⟩ := mem_homGraph.1 h₁
  obtain ⟨a₂, rfl⟩ := mem_homGraph.1 h₂
  obtain rfl : a₁ = a₂ := Subtype.ext h
  rfl

theorem map_snd_homGraph {H : Subgroup X} (φ : H →* Y) :
    (homGraph φ).map (MonoidHom.snd Y X) = H := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨a, rfl⟩ := mem_homGraph.1 hq
    exact a.2
  · exact fun hx => ⟨_, mk_mem_homGraph φ ⟨x, hx⟩, rfl⟩

theorem inf_le_map_inf_homGraph {H₁ H₂ : Subgroup X} {φ₁ : H₁ →* Y} {φ₂ : H₂ →* Y}
    (h : ∀ a (h₁ : a ∈ H₁) (h₂ : a ∈ H₂), φ₁ ⟨a, h₁⟩ = φ₂ ⟨a, h₂⟩) :
    H₁ ⊓ H₂ ≤ (homGraph φ₁ ⊓ homGraph φ₂).map (MonoidHom.snd Y X) := by
  rintro a ⟨ha₁, ha₂⟩
  refine ⟨(φ₁ ⟨a, ha₁⟩, a), ⟨mk_mem_homGraph φ₁ ⟨a, ha₁⟩, ?_⟩, rfl⟩
  rw [h a ha₁ ha₂]
  exact mk_mem_homGraph φ₂ ⟨a, ha₂⟩

end HomGraph

theorem tits_universal_completion {V : Type*} {G : SimpleGraph V} {X : Type*} [Group X]
    [MulAction X V] (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hconn : G.Preconnected) (hG : Triangulable G)
    {v w : V} (hvw : G.Adj v w) (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    (Xv Xe : Subgroup X) (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} (u : ι → V) (Xt : ι → Subgroup X)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    {Y : Type*} [Group Y] (φv : Xv →* Y) (φe : Xe →* Y) (φt : ∀ j, Xt j →* Y)
    (hve : ∀ a (ha : a ∈ Xv) (hb : a ∈ Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ Xv) (hb : a ∈ Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ Xe) (hb : a ∈ Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : Xv, Φ a = φv a) ∧ (∀ a : Xe, Φ a = φe a) ∧
      ∀ j (a : Xt j), Φ a = φt j a := by
  set K := homGraph φv ⊔ homGraph φe with hK
  have hinj : Set.InjOn (MonoidHom.snd Y X) K :=
    injOn_sup_of_triangulable hG hadj hvw hloc hswap hXv hXe hτ hρ htri (MonoidHom.snd Y X)
      (injOn_snd_homGraph φv) (injOn_snd_homGraph φe) (fun j => injOn_snd_homGraph (φt j))
      (map_snd_homGraph φv) (map_snd_homGraph φe) (fun j => map_snd_homGraph (φt j))
      (inf_le_map_inf_homGraph hve) (fun j => inf_le_map_inf_homGraph (hvt j))
      (fun j => inf_le_map_inf_homGraph (het j))
  have htop : Xv ⊔ Xe = ⊤ := sup_eq_top_of_preconnected hadj hconn hloc hswap hXv hXe
  have hsurj : K.map (MonoidHom.snd Y X) = ⊤ := by
    rw [hK, Subgroup.map_sup, map_snd_homGraph, map_snd_homGraph, htop]
  have htK : ∀ j (a : Xt j), (φt j a, (a : X)) ∈ K := by
    intro j
    let L := K.comap ((φt j).prod (Xt j).subtype)
    have hLv : ∀ a : Xt j, (a : X) • v = v → a ∈ L := fun ⟨a, ha⟩ hav => by
      change (φt j ⟨a, ha⟩, a) ∈ K
      rw [← hvt j a ((hXv a).2 hav) ha]
      exact Subgroup.mem_sup_left (mk_mem_homGraph φv ⟨a, _⟩)
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨ρ, hρm, hρv, hρw, -⟩ := hρ j
    have hτL : (⟨τ, hτm⟩ : Xt j) ∈ L := by
      change (φt j ⟨τ, hτm⟩, τ) ∈ K
      rw [← het j τ ((hXe τ).2 (Or.inr ⟨hτv, hτw⟩)) hτm]
      exact Subgroup.mem_sup_right (mk_mem_homGraph φe ⟨τ, _⟩)
    have hLw : ∀ a : Xt j, (a : X) • v = w → a ∈ L := fun a hav => by
      have : (⟨τ, hτm⟩ : Xt j)⁻¹ * a ∈ L := hLv _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hav, inv_smul_eq_iff, hτv])
      simpa using L.mul_mem hτL this
    intro a
    rcases hXt j a a.2 with h | h | h
    · exact hLv a h
    · exact hLw a h
    · have : (⟨ρ, hρm⟩ : Xt j)⁻¹ * a ∈ L := hLw _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, inv_smul_eq_iff, hρw])
      exact (by simpa using L.mul_mem (hLw ⟨ρ, hρm⟩ hρv) this : a ∈ L)
  let f : K →* X := (MonoidHom.snd Y X).comp K.subtype
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 h), fun x => ?_⟩
    obtain ⟨q, hq, hqx⟩ : x ∈ K.map (MonoidHom.snd Y X) := hsurj ▸ Subgroup.mem_top x
    exact ⟨⟨q, hq⟩, hqx⟩
  let e : K ≃* X := MulEquiv.ofBijective f hf
  have he : ∀ (q : Y × X) (hq : q ∈ K), e.symm q.2 = ⟨q, hq⟩ := fun q hq =>
    e.symm_apply_eq.2 rfl
  let Φ : X →* Y := (MonoidHom.fst Y X).comp (K.subtype.comp e.symm.toMonoidHom)
  have hΦ : ∀ (q : Y × X), q ∈ K → Φ q.2 = q.1 := fun q hq => by
    change ((e.symm q.2 : K) : Y × X).1 = q.1
    rw [he q hq]
  refine ⟨Φ, ⟨fun a => hΦ (φv a, a) (Subgroup.mem_sup_left (mk_mem_homGraph φv a)),
    fun a => hΦ (φe a, a) (Subgroup.mem_sup_right (mk_mem_homGraph φe a)),
    fun j a => hΦ (φt j a, a) (htK j a)⟩, ?_⟩
  rintro Ψ ⟨hΨv, hΨe, -⟩
  have hle : Xv ⊔ Xe ≤ MonoidHom.eqLocus Ψ Φ := sup_le
    (fun a ha => (hΨv ⟨a, ha⟩).trans
      (hΦ (φv ⟨a, ha⟩, a) (Subgroup.mem_sup_left (mk_mem_homGraph φv ⟨a, ha⟩))).symm)
    (fun a ha => (hΨe ⟨a, ha⟩).trans
      (hΦ (φe ⟨a, ha⟩, a) (Subgroup.mem_sup_right (mk_mem_homGraph φe ⟨a, ha⟩))).symm)
  rw [htop] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

theorem tits_universal_completion_of_arcTransitive {V : Type*} {G : SimpleGraph V} {X : Type*}
    [Group X] [MulAction X V] (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hconn : G.Preconnected) (hG : Triangulable G)
    (harc : ∀ a b c d, G.Adj a b → G.Adj c d → ∃ g : X, g • a = c ∧ g • b = d)
    {v w : V} (hvw : G.Adj v w)
    (Xv Xe : Subgroup X) (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} (u : ι → V) (Xt : ι → Subgroup X)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    {Y : Type*} [Group Y] (φv : Xv →* Y) (φe : Xe →* Y) (φt : ∀ j, Xt j →* Y)
    (hve : ∀ a (ha : a ∈ Xv) (hb : a ∈ Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ Xv) (hb : a ∈ Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ Xe) (hb : a ∈ Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : Xv, Φ a = φv a) ∧ (∀ a : Xe, Φ a = φe a) ∧
      ∀ j (a : Xt j), Φ a = φt j a :=
  tits_universal_completion hadj hconn hG hvw (fun y hy => harc v w v y hvw hy)
    (harc v w w v hvw hvw.symm) Xv Xe hXv hXe u Xt hXt hτ hρ htri φv φe φt hve hvt het

end CFSG.Monster.B.Recog
