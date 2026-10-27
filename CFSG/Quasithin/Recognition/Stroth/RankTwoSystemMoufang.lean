module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang
public import CFSG.GH74.BNPair.Lemma309

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair

open scoped Pointwise

universe u

variable {X : Type u} [Group X] {n : ℕ}

@[reducible, expose] def rtsMulAction (R : RankTwoSystem X n) : MulAction X R.Vertex :=
  MulAction.compHom _ R.action

@[instance_reducible]
noncomputable def rankTwoVertexFintype (R : RankTwoSystem X n) [Fintype X] : Fintype R.Vertex := by
  classical
  exact Fintype.ofSurjective
    (fun q : Bool × X => vtx R.B R.N R.w₁ R.w₂ q.1 q.2)
    (by
      rintro ⟨v, hv⟩
      obtain ⟨i, x, h⟩ := exists_vtx ⟨v, hv⟩
      exact ⟨(i, x), h.symm⟩)

theorem faithfulSMul_of_faithfulOnBuilding (R : RankTwoSystem X n) :
    letI : MulAction X R.Vertex := rtsMulAction R
    FaithfulSMul X R.Vertex := by
  letI : MulAction X R.Vertex := rtsMulAction R
  refine ⟨fun {a b} hab => ?_⟩
  classical
    have hg : ∀ v : R.Vertex, (b⁻¹ * a) • v = v := by
      intro v
      rw [mul_smul, hab v, inv_smul_smul]
    have hmem : ∀ v ∈ rankTwoVertices R.B R.N R.w₁ R.w₂,
        v * ({(b⁻¹ * a : X)} : Set X) = v := by
      intro v hv
      have h1 : (R.action (b⁻¹ * a)) ⟨v, hv⟩ = ⟨v, hv⟩ := by
        have h := hg ⟨v, hv⟩
        rwa [show (b⁻¹ * a) • (⟨v, hv⟩ : R.Vertex) = R.action (b⁻¹ * a) ⟨v, hv⟩ from rfl] at h
      have h : v * ({(b⁻¹ * a : X)⁻¹} : Set X) = v := by
        change (R.action (b⁻¹ * a) ⟨v, hv⟩ : Set X) = v
        exact congrArg (fun u : R.Vertex => (u : Set X)) h1
      have h2 : v * ({(b⁻¹ * a : X)⁻¹} : Set X) * ({(b⁻¹ * a : X)} : Set X) =
          v * ({(b⁻¹ * a : X)} : Set X) := by
        rw [h]
      have h3 : v * ({(b⁻¹ * a : X)⁻¹} : Set X) * ({(b⁻¹ * a : X)} : Set X) = v := by
        rw [mul_assoc, Set.singleton_mul_singleton, inv_mul_cancel, Set.singleton_one, mul_one]
      exact h2 ▸ h3
    have h1 : b⁻¹ * a = 1 := R.faithful _ hmem
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]

noncomputable instance rankTwoGraphDecidableRel (R : RankTwoSystem X n) :
    DecidableRel R.graph.Adj :=
  Classical.decRel _

theorem rtsGraphAction (R : RankTwoSystem X n) :
    letI := rtsMulAction R
    GraphAction X R.graph := by
  letI := rtsMulAction R
  refine ⟨fun g a b => ?_⟩
  exact rankTwoAction_adj g a b

private theorem exists_basePath_map_eq (R : RankTwoSystem X n) {l : List R.Vertex}
    (hl : IsGLSPath R.graph l) (hlen : l.length = n + 1) :
    ∃ (m₁ m₂ : R.N) (_hm₁ : (m₁ : R.Weyl) = R.w₁) (_hm₂ : (m₂ : R.Weyl) = R.w₂)
      (first : Bool) (g : X), (R.basePath m₁ m₂ first).map (R.action g) = l := by
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective R.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective R.w₂
  have hne : l ≠ [] := by
    rintro rfl
    simp at hlen
  obtain ⟨u, hu⟩ : ∃ u, l.head? = some u := ⟨l.head hne, List.head?_eq_some_head hne⟩
  by_cases hu1 : R.IsTypeOne u
  · refine ⟨m₁, m₂, hm₁, hm₂, false, ?_⟩
    have hhead : (R.basePath m₁ m₂ false).head? = some (R.vv m₁ m₂ false 0) :=
      R.basePath_head m₁ m₂ false
    have htype : R.IsTypeOne (R.vv m₁ m₂ false 0) := by
      rw [R.isTypeOne_iff, R.vtype_vv_zero]
      rfl
    have htype_cond : ∀ a b, (R.basePath m₁ m₂ false).head? = some a →
        l.head? = some b → (R.IsTypeOne a ↔ R.IsTypeOne b) := by
      intro a b ha hb
      rw [hhead] at ha
      rw [hu] at hb
      obtain rfl : a = R.vv m₁ m₂ false 0 := (Option.some.inj ha).symm
      obtain rfl : b = u := (Option.some.inj hb).symm
      exact ⟨fun _ => hu1, fun _ => htype⟩
    obtain ⟨g, hg⟩ := lemma30_8 X n R n le_rfl (R.basePath m₁ m₂ false) l
      (R.basePath_isGLSPath m₁ m₂ hm₁ hm₂ false) hl (R.basePath_length m₁ m₂ false) hlen
      htype_cond
    exact ⟨g, hg⟩
  · refine ⟨m₁, m₂, hm₁, hm₂, true, ?_⟩
    have hhead : (R.basePath m₁ m₂ true).head? = some (R.vv m₁ m₂ true 0) :=
      R.basePath_head m₁ m₂ true
    have htype : ¬ R.IsTypeOne (R.vv m₁ m₂ true 0) := by
      rw [R.isTypeOne_iff, R.vtype_vv_zero]
      simp
    have htype_cond : ∀ a b, (R.basePath m₁ m₂ true).head? = some a →
        l.head? = some b → (R.IsTypeOne a ↔ R.IsTypeOne b) := by
      intro a b ha hb
      rw [hhead] at ha
      rw [hu] at hb
      obtain rfl : a = R.vv m₁ m₂ true 0 := (Option.some.inj ha).symm
      obtain rfl : b = u := (Option.some.inj hb).symm
      exact ⟨fun h => absurd h htype, fun h => absurd h hu1⟩
    obtain ⟨g, hg⟩ := lemma30_8 X n R n le_rfl (R.basePath m₁ m₂ true) l
      (R.basePath_isGLSPath m₁ m₂ hm₁ hm₂ true) hl (R.basePath_length m₁ m₂ true) hlen
      htype_cond
    exact ⟨g, hg⟩

theorem rankTwoSystem_moufang (R : RankTwoSystem X n) :
    letI := rtsMulAction R
    haveI := rtsGraphAction R
    MoufangCondition X R.graph n := by
  letI := rtsMulAction R
  haveI := rtsGraphAction R
  intro p hp y y' hy hy' hyn hy'n
  let l : List R.Vertex := (List.range (n + 1)).map p
  have hl : IsGLSPath R.graph l := by
    dsimp only [l]
    exact isGLSPath_map_range p n (fun i hi => p.adj i hi) (fun i hi => hp i hi)
  have hlen : l.length = n + 1 := by simp [l]
  obtain ⟨m₁, m₂, hm₁, hm₂, first, g, hg⟩ := exists_basePath_map_eq R hl hlen
  let π : List R.Vertex := R.basePath m₁ m₂ first
  have hπgls : IsGLSPath R.graph π := R.basePath_isGLSPath m₁ m₂ hm₁ hm₂ first
  have hπlen : π.length = n + 1 := R.basePath_length m₁ m₂ first
  have hπfix : ∀ x ∈ R.root (jIdx n first 0), ∀ v ∈ interiorVertices π,
      ∀ w, R.graph.Adj v w → R.action x w = w :=
    fun x hx => R.basePath_fix m₁ m₂ hm₁ hm₂ first (g := x) hx
  have hπtrans := R.basePath_trans m₁ m₂ hm₁ hm₂ first
  have hn := R.three_le
  let b : R.Vertex := π[n]'(by omega)
  let a : R.Vertex := π[n - 1]'(by omega)
  have hb : π[n]? = some b := by
    rw [List.getElem?_eq_getElem (by omega)]
  have ha : π[n - 1]? = some a := by
    rw [List.getElem?_eq_getElem (by omega)]
  have hmapb : R.action g b = p n := by
    have h1 : (π.map (R.action g))[n]? = l[n]? := by rw [hg]
    rw [List.getElem?_map, hb, Option.map_some] at h1
    have h2 : l[n]? = some (p n) := by
      dsimp only [l]
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    rw [h2] at h1
    exact Option.some.inj h1
  have hmapa : R.action g a = p (n - 1) := by
    have h1 : (π.map (R.action g))[n - 1]? = l[n - 1]? := by rw [hg]
    rw [List.getElem?_map, ha, Option.map_some] at h1
    have h2 : l[n - 1]? = some (p (n - 1)) := by
      dsimp only [l]
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    rw [h2] at h1
    exact Option.some.inj h1
  have hlastπ : π.getLast? = some b := by
    rw [getLast?_eq_getElem?_of_length hπlen, hb]
  have hprevπ : π.dropLast.getLast? = some a := by
    rw [List.getLast?_dropLast]
    simp [show ¬ π.length ≤ 1 by omega]
    rw [show π.length - 2 = n - 1 by omega, List.getElem?_eq_getElem (by omega)]
  have hπsplit : π = π.dropLast ++ [b] :=
    (List.dropLast_append_getLast? b hlastπ).symm
  let z : R.Vertex := R.action g⁻¹ y
  let z' : R.Vertex := R.action g⁻¹ y'
  have hgz : R.action g z = y := by simp [z]
  have hgz' : R.action g z' = y' := by simp [z']
  have hadj_z : R.graph.Adj b z := by
    have h1 : R.graph.Adj (R.action g b) (R.action g z) := by
      rw [hmapb, hgz]
      exact hy
    exact (rankTwoAction_adj g b z).1 h1
  have hadj_z' : R.graph.Adj b z' := by
    have h1 : R.graph.Adj (R.action g b) (R.action g z') := by
      rw [hmapb, hgz']
      exact hy'
    exact (rankTwoAction_adj g b z').1 h1
  have hza : z ≠ a := by
    intro h
    have h1 : R.action g z = R.action g a := by rw [h]
    rw [hmapa, hgz] at h1
    exact hyn h1
  have hz'a : z' ≠ a := by
    intro h
    have h1 : R.action g z' = R.action g a := by rw [h]
    rw [hmapa, hgz'] at h1
    exact hy'n h1
  have hgls_z : IsGLSPath R.graph (π ++ [z]) := by
    have hπ' : IsGLSPath R.graph (π.dropLast ++ [b]) := by rwa [hπsplit] at hπgls
    have hprev : ∀ w, π.dropLast.getLast? = some w → w ≠ z := by
      intro w hw
      have hw_eq : w = a := by
        rw [hprevπ] at hw
        exact (Option.some.inj hw).symm
      rw [hw_eq] at *
      exact fun h => hza h.symm
    have h1 : IsGLSPath R.graph (π.dropLast ++ [b, z]) :=
      (isGLSPath_concat (G := R.graph) (l := π.dropLast) (y := b) (x := z)).2
        ⟨hπ', hadj_z, hprev⟩
    have e : π.dropLast ++ [b, z] = π ++ [z] := by
      rw [hπsplit]
      simp
    rwa [e] at h1
  have hgls_z' : IsGLSPath R.graph (π ++ [z']) := by
    have hπ' : IsGLSPath R.graph (π.dropLast ++ [b]) := by rwa [hπsplit] at hπgls
    have hprev : ∀ w, π.dropLast.getLast? = some w → w ≠ z' := by
      intro w hw
      have hw_eq : w = a := by
        rw [hprevπ] at hw
        exact (Option.some.inj hw).symm
      rw [hw_eq] at *
      exact fun h => hz'a h.symm
    have h1 : IsGLSPath R.graph (π.dropLast ++ [b, z']) :=
      (isGLSPath_concat (G := R.graph) (l := π.dropLast) (y := b) (x := z')).2
        ⟨hπ', hadj_z', hprev⟩
    have e : π.dropLast ++ [b, z'] = π ++ [z'] := by
      rw [hπsplit]
      simp
    rwa [e] at h1
  have hlen_z : (π ++ [z]).length = n + 2 := by simp [hπlen]
  have hlen_z' : (π ++ [z']).length = n + 2 := by simp [hπlen]
  obtain ⟨x, hxroot, hxmap⟩ := hπtrans (π ++ [z]) (π ++ [z']) hgls_z hgls_z'
    hlen_z hlen_z' ⟨[z], by simp [π]⟩ ⟨[z'], by simp [π]⟩
  have hxfix := hπfix x hxroot
  have hxz : R.action x z = z' := by
    have h := congrArg List.getLast? hxmap
    simpa using h
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · intro i hi1 hin w hw
    let v : R.Vertex := π[i]'(by omega)
    let w₀ : R.Vertex := R.action g⁻¹ w
    have hv_int : v ∈ interiorVertices π := by
      dsimp only [v]
      exact getElem_mem_interiorVertices (l := π) hi1 (by omega)
    have hmapv : R.action g v = p i := by
      have h1 : (π.map (R.action g))[i]? = l[i]? := by rw [hg]
      rw [List.getElem?_map, show π[i]? = some v by rw [List.getElem?_eq_getElem (by omega)],
        Option.map_some] at h1
      have h2 : l[i]? = some (p i) := by
        dsimp only [l]
        rw [List.getElem?_map, List.getElem?_range (by omega)]
        rfl
      rw [h2] at h1
      exact Option.some.inj h1
    have hgw₀ : R.action g w₀ = w := by simp [w₀]
    have hadj_v_w₀ : R.graph.Adj v w₀ := by
      have h1 : R.graph.Adj (R.action g v) (R.action g w₀) := by
        rw [hmapv, hgw₀]
        exact hw
      exact (rankTwoAction_adj g v w₀).1 h1
    have hxw₀ : R.action x w₀ = w₀ := hxfix v hv_int w₀ hadj_v_w₀
    show R.action (g * x * g⁻¹) w = w
    rw [show R.action (g * x * g⁻¹) w = R.action g (R.action x w₀) by
      simp [w₀, map_mul, map_inv, mul_assoc]]
    rw [hxw₀, hgw₀]
  · show R.action (g * x * g⁻¹) y = y'
    rw [show R.action (g * x * g⁻¹) y = R.action g (R.action x z) by
      simp [z, map_mul, map_inv, mul_assoc]]
    rw [hxz, hgz']

theorem rankTwoSystem_rootGroup (R : RankTwoSystem X n) (m₁ m₂ : R.N)
    (hm₁ : (m₁ : R.Weyl) = R.w₁) (hm₂ : (m₂ : R.Weyl) = R.w₂) (first : Bool) (x : X) :
    (∀ v ∈ interiorVertices (R.basePath m₁ m₂ first),
        ∀ w, R.graph.Adj v w → R.action x w = w) ↔
      x ∈ R.root (jIdx n first 0) := by
  have hA : pathFixer R.graph (R.basePath m₁ m₂ first) =
      (R.root (jIdx n first 0)).map R.action :=
    R.pathFixer_eq_map_root (R.basePath_isGLSPath m₁ m₂ hm₁ hm₂ first)
      (R.basePath_length m₁ m₂ first)
      (fun x hx => R.basePath_fix m₁ m₂ hm₁ hm₂ first (g := x) hx)
      (R.basePath_trans m₁ m₂ hm₁ hm₂ first)
  constructor
  · intro hx
    have hmem : R.action x ∈ pathFixer R.graph (R.basePath m₁ m₂ first) :=
      mem_pathFixer_iff.2 ⟨R.action_mem_graphAut x, hx⟩
    rw [hA] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : y = x := R.action_injective hyx
    rwa [hyx'] at hy
  · intro hx v hv w hw
    have hmem : R.action x ∈ pathFixer R.graph (R.basePath m₁ m₂ first) := by
      rw [hA]
      exact ⟨x, hx, rfl⟩
    exact (mem_pathFixer_iff.1 hmem).2 v hv w hw

theorem rankTwoSystem_rootGroup_conj (R : RankTwoSystem X n) {l : List R.Vertex}
    (hl : IsGLSPath R.graph l) (hlen : l.length = n + 1) :
    ∃ (g : X) (k : ℤ), k ∈ ({1, (n : ℤ)} : Set ℤ) ∧
      ∀ x : X, (∀ v ∈ interiorVertices l, ∀ w, R.graph.Adj v w → R.action x w = w) ↔
        g⁻¹ * x * g ∈ R.root k := by
  obtain ⟨m₁, m₂, hm₁, hm₂, first, g, hg⟩ := exists_basePath_map_eq R hl hlen
  refine ⟨g, jIdx n first 0, ?_, ?_⟩
  · cases first <;> simp [jIdx, stType]
  · intro x
    have hconj : (∀ v ∈ interiorVertices l, ∀ w, R.graph.Adj v w → R.action x w = w) ↔
        (∀ v ∈ interiorVertices (R.basePath m₁ m₂ first), ∀ w,
          R.graph.Adj v w → R.action (g⁻¹ * x * g) w = w) := by
      have h1 : (∀ v ∈ interiorVertices l, ∀ w, R.graph.Adj v w → R.action x w = w) ↔
          R.action x ∈ pathFixer R.graph l := by
        rw [mem_pathFixer_iff]
        exact ⟨fun h => ⟨R.action_mem_graphAut x, h⟩, fun h => h.2⟩
      have h2 : (∀ v ∈ interiorVertices (R.basePath m₁ m₂ first), ∀ w,
            R.graph.Adj v w → R.action (g⁻¹ * x * g) w = w) ↔
          R.action (g⁻¹ * x * g) ∈ pathFixer R.graph (R.basePath m₁ m₂ first) := by
        rw [mem_pathFixer_iff]
        exact ⟨fun h => ⟨R.action_mem_graphAut _, h⟩, fun h => h.2⟩
      rw [h1, h2, ← hg]
      have hmap := mem_pathFixer_map (G := R.graph) (σ := R.action g)
        (R.action_mem_graphAut g) (l := R.basePath m₁ m₂ first) (τ := R.action x)
      have e : (R.action g)⁻¹ * R.action x * R.action g = R.action (g⁻¹ * x * g) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e] at hmap
      exact hmap
    rw [hconj]
    exact rankTwoSystem_rootGroup R m₁ m₂ hm₁ hm₂ first (g⁻¹ * x * g)

end CFSG.Quasithin.Stroth
