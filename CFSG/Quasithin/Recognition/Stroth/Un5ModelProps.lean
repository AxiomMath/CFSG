module

public import CFSG.Quasithin.Recognition.Stroth.Un5ModelFacts
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts
public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN

public noncomputable section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Geometry.GeneralizedPolygons
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.LieEmbed
open Classical
open scoped Pointwise

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]

private abbrev Un5Heis (hF : Nat.card F = (2 ^ k) ^ 2) :
    Subgroup (SU (unitaryInvolution F 2 k) 5) :=
  heisenbergSubgroup (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
    (n := 5) (i := (1 : Fin 5)) (k := (2 : Fin 5)) (by decide) (by decide) (by decide)

private theorem weight_five_one :
    weight 5 (1 : Fin 5) = toStd 5 (octRootB 4) := by
  rw [octRootB_four]
  funext c
  fin_cases c <;> simp [weight, toStd, Nat.even_iff]

private theorem un5Oct_four_le_heisenberg (hF : Nat.card F = (2 ^ k) ^ 2) :
    un5Oct (p := 2) (f := k) hF 4 ≤ Un5Heis hF := by
  show CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 k)
    (unitaryInvolution_involutive hF) 5 (octRootB 4) ≤ _
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun ha =>
      iSup_le fun hb => iSup_le fun hba => iSup_le fun hw' => ?_
    exfalso
    revert hab ha hb hba hw'
    fin_cases a <;> fin_cases b <;> decide
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hw' => ?_
    exfalso
    revert ha hw'
    fin_cases a <;> decide
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun ha => iSup_le fun hab =>
      iSup_le fun hb => iSup_le fun hw' => ?_
    have ha1 : a = 1 := by
      revert hw'
      fin_cases a <;> decide
    have hb2 : b = 2 := by
      revert hb
      fin_cases b <;> decide
    subst ha1 hb2
    exact le_rfl

private theorem exists_heis_constraint (hF : Nat.card F = (2 ^ k) ^ 2) (a : F) :
    ∃ b : F, b + unitaryInvolution F 2 k b + unitaryInvolution F 2 k a * a = 0 := by
  have hfix : unitaryInvolution F 2 k (-(unitaryInvolution F 2 k a * a)) =
      -(unitaryInvolution F 2 k a * a) := by
    rw [map_neg, map_mul, unitaryInvolution_involutive hF, mul_comm]
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF hfix
  exact ⟨c, by rw [hc]; ring⟩

private theorem heisMat_apply_irev (a b : F) :
    heisenbergMatrix (unitaryInvolution F 2 k) (1 : Fin 5) 2 a b 1 (Fin.rev 1) = b := by
  have r1 : Fin.rev (1 : Fin 5) = 3 := by decide
  rw [r1]
  simp [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply,
    Matrix.one_apply]

private noncomputable abbrev un5HeisElt (hF : Nat.card F = (2 ^ k) ^ 2) (a b : F)
    (hab : b + unitaryInvolution F 2 k b + unitaryInvolution F 2 k a * a = 0) :
    SU (unitaryInvolution F 2 k) 5 :=
  heisElt (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
    (n := 5) (i := (1 : Fin 5)) (k := (2 : Fin 5)) (a := a) (b := b)
    (by decide) (by decide) (by decide) hab

private theorem mat_un5HeisElt (hF : Nat.card F = (2 ^ k) ^ 2) (a b : F)
    (hab : b + unitaryInvolution F 2 k b + unitaryInvolution F 2 k a * a = 0) :
    mat (unitaryInvolution F 2 k) 5 (un5HeisElt hF a b hab) =
      heisenbergMatrix (unitaryInvolution F 2 k) (1 : Fin 5) 2 a b := by
  rw [mat_apply, ← suMat_apply]
  exact suMat_heisElt (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
    (n := 5) (i := (1 : Fin 5)) (k := (2 : Fin 5))
    (by decide) (by decide) (by decide) hab

private theorem heis_constraint (hF : Nat.card F = (2 ^ k) ^ 2)
    {x : SU (unitaryInvolution F 2 k) 5} (hx : x ∈ Un5Heis hF) :
    mat (unitaryInvolution F 2 k) 5 x 1 (Fin.rev 1) +
        unitaryInvolution F 2 k (mat (unitaryInvolution F 2 k) 5 x 1 (Fin.rev 1)) +
        unitaryInvolution F 2 k (mat (unitaryInvolution F 2 k) 5 x 1 2) *
          mat (unitaryInvolution F 2 k) 5 x 1 2 = 0 := by
  obtain ⟨a, b, hab, hmat⟩ := hx
  have hik : (1 : Fin 5) ≠ 2 := by decide
  have hk : Fin.rev (2 : Fin 5) = 2 := by decide
  have h2 : mat (unitaryInvolution F 2 k) 5 x 1 2 = a := by
    rw [mat_apply, hmat]
    exact heisenbergMatrix_apply_ik hik hk a b
  have h3 : mat (unitaryInvolution F 2 k) 5 x 1 (Fin.rev 1) = b := by
    rw [mat_apply, hmat]
    exact heisMat_apply_irev a b
  rw [h2, h3]
  exact hab

private noncomputable def heisParamEquiv (hF : Nat.card F = (2 ^ k) ^ 2) :
    Un5Heis hF ≃
      {ab : F × F // ab.2 + unitaryInvolution F 2 k ab.2 +
        unitaryInvolution F 2 k ab.1 * ab.1 = 0} where
  toFun x := ⟨(mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1 2,
    mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1 (Fin.rev 1)),
    heis_constraint hF x.2⟩
  invFun ab := ⟨un5HeisElt hF ab.1.1 ab.1.2 ab.2,
    ⟨ab.1.1, ab.1.2, ab.2, mat_un5HeisElt hF ab.1.1 ab.1.2 ab.2⟩⟩
  left_inv x := by
    obtain ⟨a, b, hab, hmat⟩ := x.2
    have hik : (1 : Fin 5) ≠ 2 := by decide
    have hk : Fin.rev (2 : Fin 5) = 2 := by decide
    have h2 : mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1 2 = a := by
      rw [mat_apply, hmat]
      exact heisenbergMatrix_apply_ik hik hk a b
    have h3 : mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1
        (Fin.rev 1) = b := by
      rw [mat_apply, hmat]
      exact heisMat_apply_irev a b
    apply Subtype.ext
    apply mat_injective
    rw [mat_un5HeisElt hF (mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1 2)
      (mat (unitaryInvolution F 2 k) 5 (x : SU (unitaryInvolution F 2 k) 5) 1 (Fin.rev 1))
      (heis_constraint hF x.2)]
    rw [h2, h3, mat_apply, hmat]
  right_inv ab := by
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    apply Subtype.ext
    show ((mat (unitaryInvolution F 2 k) 5 (un5HeisElt hF a b hab) 1 2,
      mat (unitaryInvolution F 2 k) 5 (un5HeisElt hF a b hab) 1 (Fin.rev 1)) : F × F) = (a, b)
    apply Prod.ext
    · rw [mat_un5HeisElt hF a b hab]
      exact heisenbergMatrix_apply_ik (by decide) (by decide) a b
    · rw [mat_un5HeisElt hF a b hab]
      exact heisMat_apply_irev a b

private noncomputable def paramTraceEquiv (hF : Nat.card F = (2 ^ k) ^ 2) :
    {ab : F × F // ab.2 + unitaryInvolution F 2 k ab.2 +
        unitaryInvolution F 2 k ab.1 * ab.1 = 0} ≃
      F × traceZero (unitaryInvolution F 2 k) := by
  classical
  choose b₀ hb₀ using exists_heis_constraint (k := k) (F := F) hF
  refine
    { toFun := fun ab => (ab.1.1, ⟨ab.1.2 - b₀ ab.1.1, ?_⟩)
      invFun := fun ac => ⟨(ac.1, b₀ ac.1 + (ac.2 : F)), ?_⟩
      left_inv := fun ab => ?_
      right_inv := fun ac => ?_ }
  · rw [mem_traceZero, map_sub]
    linear_combination ab.2 - hb₀ ab.1.1
  · have hc := (mem_traceZero (unitaryInvolution F 2 k)).1 ac.2.2
    rw [map_add]
    linear_combination hb₀ ac.1 + hc
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    apply Subtype.ext
    exact Prod.ext rfl (by ring)
  · obtain ⟨a, c⟩ := ac
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      show b₀ a + (c : F) - b₀ a = (c : F)
      ring

private theorem card_heisenbergSubgroup (hF : Nat.card F = (2 ^ k) ^ 2) :
    Nat.card (Un5Heis hF) = (2 ^ k) ^ 3 := by
  rw [Nat.card_congr (heisParamEquiv hF), Nat.card_congr (paramTraceEquiv hF), Nat.card_prod, hF,
    CFSG.LieType.Steinberg.card_traceZero hF]
  ring

private theorem un5Oct_four_card (hF : Nat.card F = (2 ^ k) ^ 2) :
    Nat.card (un5Oct (p := 2) (f := k) hF 4) = (2 ^ k) ^ 3 := by
  refine le_antisymm ?_ ?_
  · calc Nat.card (un5Oct (p := 2) (f := k) hF 4)
        ≤ Nat.card (Un5Heis hF) := Subgroup.card_le_of_le (un5Oct_four_le_heisenberg hF)
      _ = (2 ^ k) ^ 3 := card_heisenbergSubgroup hF
  · have hw : weight 5 (1 : Fin 5) = toStd 5 (octRootB 4) := weight_five_one
    have hle : Un5Heis hF ≤ un5Oct (p := 2) (f := k) hF 4 :=
      heisenberg_le (hσ := unitaryInvolution_involutive hF) (i := (1 : Fin 5)) (k := (2 : Fin 5))
        (by decide) (by decide) (by decide) hw
    calc (2 ^ k) ^ 3 = Nat.card (Un5Heis hF) := (card_heisenbergSubgroup hF).symm
      _ ≤ Nat.card (un5Oct (p := 2) (f := k) hF 4) := Subgroup.card_le_of_le hle

private theorem mem_interiorVertices_range_map_gpath {V : Type} {Γ : SimpleGraph V} {n : ℕ}
    {p : GPath Γ n} {v : V} (hn : 1 ≤ n) :
    v ∈ interiorVertices ((List.range (n + 1)).map p) ↔
      ∃ i, 1 ≤ i ∧ i ≤ n - 1 ∧ p i = v := by
  have harith : n - 1 + 2 = n + 1 := by omega
  constructor
  · intro hv
    have hv' : v ∈ interiorVertices ((List.range ((n - 1) + 2)).map p) := by
      rw [← harith] at hv
      exact hv
    obtain ⟨i, hi, rfl⟩ := CFSG.GH74.BNPair.mem_interior_map_range (f := p) (k := n - 1) hv'
    exact ⟨i + 1, by omega, by omega, rfl⟩
  · rintro ⟨i, hi1, hi2, rfl⟩
    have hmem : p i ∈ interiorVertices ((List.range ((n - 1) + 2)).map p) := by
      have h := CFSG.GH74.BNPair.getElem_mem_interiorVertices
        (l := (List.range ((n - 1) + 2)).map p) (i := i) hi1 (by
          rw [List.length_map, List.length_range]; omega)
      simpa [List.getElem_map, List.getElem_range] using h
    simpa [harith] using hmem

variable (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [hζ : Fact ((ζ : F) ≠ 0)]

private theorem un5System_root_four_card :
    Nat.card ((un5System hF ζ).root 4) = (2 ^ k) ^ 3 := by
  have hroot : (un5System hF ζ).root 4 =
      (un5Oct (p := 2) (f := k) hF 4).map (un5Proj (F := F) (f := k)) := rfl
  rw [hroot, card_map_eq_card_of_injOn (un5Proj (F := F) (f := k))
    (octGroup_le_un5U (p := 2) (f := k) hF (by norm_num) (by norm_num))
    (fun x hx y hy h => un5Proj_injOn_unU hF hx hy h), un5Oct_four_card]

private theorem exists_baseGPath
    (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) :
    ∃ p : GPath (un5System hF ζ).graph 4,
      p.NoBack ∧ p 4 = (un5System hF ζ).vv m₁ m₂ first 4 ∧
        pathRootGroup (Un5Group k F) (un5System hF ζ).graph p =
          (un5System hF ζ).root (jIdx 4 first 0) := by
  classical
  letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex :=
    rtsMulAction (un5System hF ζ)
  haveI : FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex :=
    un5System_faithfulSMul (hF := hF) (ζ := ζ)
  haveI : GraphAction (Un5Group k F) (un5System hF ζ).graph :=
    rtsGraphAction (un5System hF ζ)
  let l : List (un5System hF ζ).Vertex := (un5System hF ζ).basePath m₁ m₂ first
  have hl : IsGLSPath (un5System hF ζ).graph l :=
    (un5System hF ζ).basePath_isGLSPath m₁ m₂ hm₁ hm₂ first
  have hlen : l.length = 5 := by
    simpa using (un5System hF ζ).basePath_length m₁ m₂ first
  have hne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨p, hpnb, hmap⟩ := exists_gPath_of_isGLSPath hl hne
  have hp_apply : ∀ (i : ℕ) (hi : i < l.length), p i = l[i]'hi := by
    intro i hi
    have h := congrArg (fun m => m[i]?) hmap
    rw [List.getElem?_map, List.getElem?_range hi, Option.map_some,
      List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  have hp4 : p 4 = (un5System hF ζ).vv m₁ m₂ first 4 := by
    have h4 : 4 < l.length := by rw [hlen]; norm_num
    rw [hp_apply 4 h4]
    simp [l, CFSG.GH74.BNPair.RankTwoSystem.basePath]
  have hroot : pathRootGroup (Un5Group k F) (un5System hF ζ).graph p =
      (un5System hF ζ).root (jIdx 4 first 0) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [← rankTwoSystem_rootGroup (un5System hF ζ) m₁ m₂ hm₁ hm₂ first x]
      intro v hv w hw
      have hv' : v ∈ interiorVertices ((List.range ((l.length - 1) + 1)).map p) := by
        rw [show l.length - 1 + 1 = l.length by rw [hlen], hmap]
        exact hv
      obtain ⟨i, hi1, hi3, rfl⟩ :=
        (mem_interiorVertices_range_map_gpath (n := l.length - 1) (p := p)
          (by rw [hlen]; norm_num)).1 hv'
      exact (mem_pathRootGroup.mp hx) i hi1 hi3 w hw
    · intro x hx
      rw [mem_pathRootGroup]
      intro i hi1 hi3 w hw
      have hv' : p i ∈ interiorVertices ((List.range ((l.length - 1) + 1)).map p) :=
        (mem_interiorVertices_range_map_gpath (n := l.length - 1) (p := p)
          (by rw [hlen]; norm_num)).2 ⟨i, hi1, hi3, rfl⟩
      have hv'' : p i ∈ interiorVertices l := by
        rw [show l.length - 1 + 1 = l.length by rw [hlen], hmap] at hv'
        exact hv'
      exact (rankTwoSystem_rootGroup (un5System hF ζ) m₁ m₂ hm₁ hm₂ first x).mpr hx
        (p i) hv'' w hw
  exact ⟨p, hpnb, hp4, hroot⟩

private theorem degree_vv_four (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) :
    (un5System hF ζ).graph.degree ((un5System hF ζ).vv m₁ m₂ first 4) =
      1 + Nat.card ((un5System hF ζ).root (jIdx 4 first 0)) := by
  classical
  letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex :=
    rtsMulAction (un5System hF ζ)
  haveI : FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex :=
    un5System_faithfulSMul (hF := hF) (ζ := ζ)
  haveI : GraphAction (Un5Group k F) (un5System hF ζ).graph :=
    rtsGraphAction (un5System hF ζ)
  have hP : IsGeneralizedPolygon (un5System hF ζ).graph 4 :=
    un5System_isGeneralizedPolygon (hF := hF) (ζ := ζ)
  have hT : IsThick (un5System hF ζ).graph := un5System_isThick (hF := hF) (ζ := ζ)
  have hM : MoufangCondition (Un5Group k F) (un5System hF ζ).graph 4 :=
    rankTwoSystem_moufang _
  obtain ⟨p, hpnb, hp4, hroot⟩ := exists_baseGPath hF ζ m₁ m₂ hm₁ hm₂ first
  have hdeg := card_pathRootGroup_add_one (n := 4) (by norm_num) hP hT hM p hpnb
  rw [hroot, hp4] at hdeg
  exact hdeg.symm.trans (Nat.add_comm _ _)

private theorem isTypeOne_vv_false (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) :
    (un5System hF ζ).IsTypeOne ((un5System hF ζ).vv m₁ m₂ false 4) := by
  rw [(un5System hF ζ).isTypeOne_iff]
  rw [show (un5System hF ζ).vv m₁ m₂ false 4 = (un5System hF ζ).vv m₁ m₂ false (3 + 1) from rfl]
  rw [(un5System hF ζ).vtype_vv_succ m₁ m₂ false 3]
  decide

private theorem isTypeTwo_vv_true (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) :
    (un5System hF ζ).IsTypeTwo ((un5System hF ζ).vv m₁ m₂ true 4) := by
  rw [(un5System hF ζ).isTypeTwo_iff]
  rw [show (un5System hF ζ).vv m₁ m₂ true 4 = (un5System hF ζ).vv m₁ m₂ true (3 + 1) from rfl]
  rw [(un5System hF ζ).vtype_vv_succ m₁ m₂ true 3]
  decide

private theorem degree_eq_short (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂)
    (v : (un5System hF ζ).Vertex) (hv : (un5System hF ζ).IsTypeOne v) :
    (un5System hF ζ).graph.degree v = (2 ^ k) ^ 2 + 1 := by
  have hbase := degree_vv_four hF ζ m₁ m₂ hm₁ hm₂ false
  have hj : jIdx 4 false 0 = 1 := by decide
  rw [hj, un5System_root_one_card] at hbase
  obtain ⟨g, hg⟩ := ((un5System hF ζ).lemma30_6_iii).2.1 _ _
    (isTypeOne_vv_false hF ζ m₁ m₂ hm₁ hm₂) hv
  rw [← hg]
  rw [show (un5System hF ζ).action g ((un5System hF ζ).vv m₁ m₂ false 4) =
      g • ((un5System hF ζ).vv m₁ m₂ false 4) from rfl, degree_smul]
  exact hbase.trans (Nat.add_comm _ _)

private theorem degree_eq_long (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂)
    (v : (un5System hF ζ).Vertex) (hv : (un5System hF ζ).IsTypeTwo v) :
    (un5System hF ζ).graph.degree v = (2 ^ k) ^ 3 + 1 := by
  have hbase := degree_vv_four hF ζ m₁ m₂ hm₁ hm₂ true
  have hj : jIdx 4 true 0 = 4 := by decide
  rw [hj, un5System_root_four_card] at hbase
  obtain ⟨g, hg⟩ := ((un5System hF ζ).lemma30_6_iii).2.2 _ _
    (isTypeTwo_vv_true hF ζ m₁ m₂ hm₁ hm₂) hv
  rw [← hg]
  rw [show (un5System hF ζ).action g ((un5System hF ζ).vv m₁ m₂ true 4) =
      g • ((un5System hF ζ).vv m₁ m₂ true 4) from rfl, degree_smul]
  exact hbase.trans (Nat.add_comm _ _)

private theorem un5Oct_one_eq_rootHom_range :
    un5Oct (p := 2) (f := k) hF 1 =
      (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)).range := by
  have hσ := unitaryInvolution_involutive hF
  have hw : weight 5 (0 : Fin 5) - weight 5 1 = toStd 5 (octRootB 1) := by decide
  have hge : (rootHom (unitaryInvolution F 2 k) hσ
      (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)).range ≤
      un5Oct (p := 2) (f := k) hF 1 := by
    rintro x ⟨c, rfl⟩
    exact SUExtras.rootHom_mem hσ (by decide) (by decide) (by decide) (by decide) hw c
  refine (Subgroup.eq_of_le_of_card_ge hge ?_).symm
  rw [un5Oct_one_card, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤)
      (rootHom_injective (F := F) (σ := unitaryInvolution F 2 k) (hσ := hσ)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide) (by decide)),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, hF]

private theorem root_one_comm :
    ∀ x ∈ (un5System hF ζ).root 1, ∀ y ∈ (un5System hF ζ).root 1, x * y = y * x := by
  have hroot : (un5System hF ζ).root 1 =
      ((un5Proj (F := F) (f := k)).comp
        (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
          (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide))).range := by
    rw [show (un5System hF ζ).root 1 =
        (un5Oct (p := 2) (f := k) hF 1).map (un5Proj (F := F) (f := k)) from rfl,
      un5Oct_one_eq_rootHom_range, MonoidHom.map_range]
  intro x hx y hy
  rw [hroot] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  change (un5Proj (F := F) (f := k)).comp
      (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)) a *
      (un5Proj (F := F) (f := k)).comp
      (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)) b =
    (un5Proj (F := F) (f := k)).comp
      (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)) b *
      (un5Proj (F := F) (f := k)).comp
      (rootHom (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        (n := 5) (i := 0) (j := 1) (by decide) (by decide) (by decide)) a
  rw [← MonoidHom.map_mul, ← MonoidHom.map_mul]
  congr 1
  exact mul_comm a b

private theorem pathRootGroup_conj (p : GPath (un5System hF ζ).graph 4) (hp : p.NoBack) :
    ∃ (g : Un5Group k F) (kk : ℤ), kk ∈ ({1, 4} : Set ℤ) ∧
      ∀ x : Un5Group k F, x ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p ↔
        g⁻¹ * x * g ∈ (un5System hF ζ).root kk := by
  classical
  letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex := rtsMulAction _
  haveI : FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex :=
    un5System_faithfulSMul (hF := hF) (ζ := ζ)
  haveI : GraphAction (Un5Group k F) (un5System hF ζ).graph :=
    rtsGraphAction (un5System hF ζ)
  let l : List (un5System hF ζ).Vertex := (List.range 5).map p
  have hl : IsGLSPath (un5System hF ζ).graph l := by
    dsimp only [l]
    exact CFSG.GH74.BNPair.isGLSPath_map_range p 4 (fun i hi => p.adj i hi)
      (fun i hi => hp i hi)
  have hlen : l.length = 4 + 1 := by simp [l]
  obtain ⟨g, kk, hk, hiff⟩ := rankTwoSystem_rootGroup_conj (un5System hF ζ) hl hlen
  refine ⟨g, kk, hk, fun x => ?_⟩
  have hmem : x ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p ↔
      ∀ v ∈ interiorVertices l, ∀ w, (un5System hF ζ).graph.Adj v w →
        (un5System hF ζ).action x w = w := by
    rw [mem_pathRootGroup]
    constructor
    · intro h v hv w hw
      have hv' : v ∈ interiorVertices ((List.range (4 + 1)).map p) := by simpa [l] using hv
      obtain ⟨i, hi1, hi2, rfl⟩ :=
        (mem_interiorVertices_range_map_gpath (n := 4) (p := p) (by norm_num)).1 hv'
      exact h i hi1 hi2 w hw
    · intro h i hi1 hi2 w hw
      have hv : p i ∈ interiorVertices l := by
        have hv' : p i ∈ interiorVertices ((List.range (4 + 1)).map p) :=
          (mem_interiorVertices_range_map_gpath (n := 4) (p := p) (by norm_num)).2
            ⟨i, hi1, hi2, rfl⟩
        simpa [l] using hv'
      exact h (p i) hv w hw
  rw [hmem, hiff]

private theorem vtype_gpath_four (p : GPath (un5System hF ζ).graph 4) :
    vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂ (p 4) =
      vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂
        (p 0) := by
  have h1 := (un5System hF ζ).rank2.vtype_not_of_adj (p.adj 0 (by norm_num))
  have h2 := (un5System hF ζ).rank2.vtype_not_of_adj (p.adj 1 (by norm_num))
  have h3 := (un5System hF ζ).rank2.vtype_not_of_adj (p.adj 2 (by norm_num))
  have h4 := (un5System hF ζ).rank2.vtype_not_of_adj (p.adj 3 (by norm_num))
  calc vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂ (p 4)
      = !vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂
          (p 3) := h4
    _ = !(!vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂
          (p 2)) := by rw [h3]
    _ = vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂
          (p 2) := by simp
    _ = vtype (un5System hF ζ).B (un5System hF ζ).N (un5System hF ζ).w₁ (un5System hF ζ).w₂
          (p 0) := by rw [h2, h1]; simp

theorem un5RootGroupOrders :
    ∀ (k : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
      (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
      [Fact ((ζ : F) ≠ 0)],
      Nat.card ((un5System hF ζ).root 1) = (2 ^ k) ^ 2 ∧
        Nat.card ((un5System hF ζ).root 4) = (2 ^ k) ^ 3 := by
  intro k F _ _ _ _ hF ζ hζ
  exact ⟨un5System_root_one_card (hF := hF) (ζ := ζ),
    un5System_root_four_card (hF := hF) (ζ := ζ)⟩

theorem un5VertexDegrees :
    ∀ (k : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
      (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
      [Fact ((ζ : F) ≠ 0)],
      (∀ v : (un5System hF ζ).Vertex,
          (un5System hF ζ).graph.degree v = (2 ^ k) ^ 2 + 1 ∨
            (un5System hF ζ).graph.degree v = (2 ^ k) ^ 3 + 1) ∧
        (∃ v : (un5System hF ζ).Vertex, (un5System hF ζ).graph.degree v = (2 ^ k) ^ 2 + 1) ∧
        ∃ v : (un5System hF ζ).Vertex, (un5System hF ζ).graph.degree v = (2 ^ k) ^ 3 + 1 := by
  intro k F _ _ _ _ hF ζ hζ
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₂
  refine ⟨?_, ⟨(un5System hF ζ).vv m₁ m₂ false 4, ?_⟩,
    ⟨(un5System hF ζ).vv m₁ m₂ true 4, ?_⟩⟩
  · intro v
    rcases (un5System hF ζ).isTypeOne_or_isTypeTwo v with hv | hv
    · exact Or.inl (degree_eq_short hF ζ m₁ m₂ hm₁ hm₂ v hv)
    · exact Or.inr (degree_eq_long hF ζ m₁ m₂ hm₁ hm₂ v hv)
  · exact degree_eq_short hF ζ m₁ m₂ hm₁ hm₂ _ (isTypeOne_vv_false hF ζ m₁ m₂ hm₁ hm₂)
  · exact degree_eq_long hF ζ m₁ m₂ hm₁ hm₂ _ (isTypeTwo_vv_true hF ζ m₁ m₂ hm₁ hm₂)

theorem un5ShortRootGroupsAbelian :
    ∀ (k : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
      (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
      [Fact ((ζ : F) ≠ 0)],
      ∀ p : GPath (un5System hF ζ).graph 4, p.NoBack →
        (un5System hF ζ).graph.degree (p 0) = (2 ^ k) ^ 2 + 1 →
        ∀ a b : Un5Group k F,
          a ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p →
          b ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p →
          a * b = b * a := by
  intro k F _ _ _ _ hF ζ hζ p hp hdeg a b ha hb
  classical
  letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex := rtsMulAction _
  haveI : FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex :=
    un5System_faithfulSMul (hF := hF) (ζ := ζ)
  haveI : GraphAction (Un5Group k F) (un5System hF ζ).graph :=
    rtsGraphAction (un5System hF ζ)
  have hP : IsGeneralizedPolygon (un5System hF ζ).graph 4 :=
    un5System_isGeneralizedPolygon (hF := hF) (ζ := ζ)
  have hT : IsThick (un5System hF ζ).graph := un5System_isThick (hF := hF) (ζ := ζ)
  have hM : MoufangCondition (Un5Group k F) (un5System hF ζ).graph 4 :=
    rankTwoSystem_moufang _
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₂
  obtain ⟨g, kk, hk, hiff⟩ := pathRootGroup_conj hF ζ p hp
  have hlt : (2 ^ k) ^ 2 < (2 ^ k) ^ 3 :=
    Nat.pow_lt_pow_right (CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF) (by norm_num)
  have htype0 : (un5System hF ζ).IsTypeOne (p 0) := by
    rcases (un5System hF ζ).isTypeOne_or_isTypeTwo (p 0) with h | h
    · exact h
    · exfalso
      have hlong := degree_eq_long hF ζ m₁ m₂ hm₁ hm₂ (p 0) h
      rw [hdeg] at hlong
      omega
  have htype4 : (un5System hF ζ).IsTypeOne (p 4) := by
    rw [(un5System hF ζ).isTypeOne_iff] at htype0 ⊢
    rwa [vtype_gpath_four]
  have hdeg4 : (un5System hF ζ).graph.degree (p 4) = (2 ^ k) ^ 2 + 1 :=
    degree_eq_short hF ζ m₁ m₂ hm₁ hm₂ (p 4) htype4
  have hU : Nat.card ↥(pathRootGroup (Un5Group k F) (un5System hF ζ).graph p) = (2 ^ k) ^ 2 := by
    have h := card_pathRootGroup_add_one (n := 4) (by norm_num) hP hT hM p hp
    rw [hdeg4] at h
    omega
  have hcard : Nat.card ↥(pathRootGroup (Un5Group k F) (un5System hF ζ).graph p) =
      Nat.card ↥((un5System hF ζ).root kk) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨g⁻¹ * (x : Un5Group k F) * g, (hiff x.1).mp x.2⟩
        invFun := fun y => ⟨g * (y : Un5Group k F) * g⁻¹, ?_⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun y => Subtype.ext (by group) }
    refine (hiff (g * (y : Un5Group k F) * g⁻¹)).mpr ?_
    convert y.2 using 1
    group
  have hk1 : kk = 1 := by
    have hk' : kk = 1 ∨ kk = 4 := by simpa using hk
    rcases hk' with rfl | rfl
    · rfl
    · exfalso
      rw [hcard] at hU
      rw [un5System_root_four_card (hF := hF) (ζ := ζ)] at hU
      omega
  have hmem1 : ∀ x : Un5Group k F,
      x ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p →
        g⁻¹ * x * g ∈ (un5System hF ζ).root 1 := by
    intro x hx
    have h := (hiff x).mp hx
    rwa [hk1] at h
  have hcomm : ∀ x y : Un5Group k F,
      x ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p →
      y ∈ pathRootGroup (Un5Group k F) (un5System hF ζ).graph p → x * y = y * x := by
    intro x y hx hy
    have hc := root_one_comm hF ζ (g⁻¹ * x * g) (hmem1 x hx) (g⁻¹ * y * g) (hmem1 y hy)
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = y * x := by group
  exact hcomm a b ha hb

end CFSG.Quasithin.Stroth
