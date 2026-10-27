module

public import CFSG.Quasithin.Background.HZCoc24B
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.F7E1
public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.Quasithin.Recognition.Stroth.Str86Props

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G]

theorem f112CosetSMul_stab {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) :
    CosetGeom.stab (f112CosetSMul g v) = conjSub (g : X) (CosetGeom.stab v) := by
  rw [f112CosetSMul_eq_smul]
  exact CosetGeom.stab_smul g v

abbrev f112BaseGroup (L1 L2 S : Subgroup G) : Subgroup G := P1 L1 L2 S ⊔ P2 L1 L2 S

abbrev f112C1 (L1 L2 S : Subgroup G) : Subgroup ↥(f112BaseGroup L1 L2 S) :=
  (f112Completion L1 L2 S).φ1.range

abbrev f112C2 (L1 L2 S : Subgroup G) : Subgroup ↥(f112BaseGroup L1 L2 S) :=
  (f112Completion L1 L2 S).φ2.range

abbrev f112Act (L1 L2 S : Subgroup G) : Type := ↥(f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)

abbrev f112Verts (L1 L2 S : Subgroup G) : Type :=
  CosetGeom (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S)

noncomputable def f112VertexCore (L1 L2 S : Subgroup G)
    (v : f112Verts L1 L2 S) : Subgroup G :=
  (pCoreOf 2 (CosetGeom.stab v)).map (f112BaseGroup L1 L2 S).subtype

theorem f112_range_φ1 (L1 L2 S : Subgroup G) :
    f112C1 L1 L2 S = (P1 L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) :=
  Subgroup.inclusion_range (le_sup_left : P1 L1 L2 S ≤ f112BaseGroup L1 L2 S)

theorem f112_range_φ2 (L1 L2 S : Subgroup G) :
    f112C2 L1 L2 S = (P2 L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) :=
  Subgroup.inclusion_range (le_sup_right : P2 L1 L2 S ≤ f112BaseGroup L1 L2 S)

theorem f112VertexCore_γ₀ (L1 L2 S : Subgroup G) :
    f112VertexCore L1 L2 S
      (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) = Q1 L1 L2 S := by
  rw [f112VertexCore, CosetGeom.stab_γ₀ (le_sup_left :
    f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]
  rw [f112_range_φ1,
    CFSG.Quasithin.H.Coc24.pCoreOf_subgroupOf
      (le_sup_left : P1 L1 L2 S ≤ f112BaseGroup L1 L2 S) 2,
    Subgroup.map_subgroupOf_eq_of_le (K := f112BaseGroup L1 L2 S)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S)).trans
        (le_sup_left : P1 L1 L2 S ≤ f112BaseGroup L1 L2 S))]

theorem f112VertexCore_γ₁ (L1 L2 S : Subgroup G) :
    f112VertexCore L1 L2 S
      (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) = Q2 L1 L2 S := by
  rw [f112VertexCore, CosetGeom.stab_γ₁ (le_sup_right :
    f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]
  rw [f112_range_φ2,
    CFSG.Quasithin.H.Coc24.pCoreOf_subgroupOf
      (le_sup_right : P2 L1 L2 S ≤ f112BaseGroup L1 L2 S) 2,
    Subgroup.map_subgroupOf_eq_of_le (K := f112BaseGroup L1 L2 S)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)).trans
        (le_sup_right : P2 L1 L2 S ≤ f112BaseGroup L1 L2 S))]

theorem f112C1_pCore_map (L1 L2 S : Subgroup G) :
    (pCoreOf 2 (f112C1 L1 L2 S)).map (f112BaseGroup L1 L2 S).subtype = Q1 L1 L2 S := by
  rw [← f112VertexCore_γ₀ L1 L2 S, f112VertexCore, CosetGeom.stab_γ₀ (le_sup_left :
    f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]

theorem f112C2_pCore_map (L1 L2 S : Subgroup G) :
    (pCoreOf 2 (f112C2 L1 L2 S)).map (f112BaseGroup L1 L2 S).subtype = Q2 L1 L2 S := by
  rw [← f112VertexCore_γ₁ L1 L2 S, f112VertexCore, CosetGeom.stab_γ₁ (le_sup_right :
    f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]

theorem f112VertexCore_smul_γ₀ (L1 L2 S : Subgroup G) (a : f112Act L1 L2 S) :
    f112VertexCore L1 L2 S
        (f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      (Q1 L1 L2 S).map (MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G)).toMonoidHom := by
  rw [f112VertexCore, f112CosetSMul_stab, CosetGeom.stab_γ₀ (le_sup_left :
    f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]
  rw [show conjSub (a : ↥(f112BaseGroup L1 L2 S)) (f112C1 L1 L2 S) =
      (f112C1 L1 L2 S).map
        (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))).toMonoidHom from rfl]
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))) (f112C1 L1 L2 S), Subgroup.map_map]
  have hcomp : (f112BaseGroup L1 L2 S).subtype.comp
        (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))).toMonoidHom =
      (MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G)).toMonoidHom.comp
        (f112BaseGroup L1 L2 S).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, f112C1_pCore_map]

theorem f112CosetSMul_γ₁_of_mem {X : Type} [Group X] {A B : Subgroup X}
    {a : ↥(A ⊔ B)} (ha : (a : X) ∈ B) :
    f112CosetSMul a (CosetGeom.γ₁ (A ⊔ B) A B) = CosetGeom.γ₁ (A ⊔ B) A B := by
  rw [f112CosetSMul_eq_smul]
  exact CosetGeom.smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) ha

theorem f112CosetSMul_γ₀_of_mem {X : Type} [Group X] {A B : Subgroup X}
    {a : ↥(A ⊔ B)} (ha : (a : X) ∈ A) :
    f112CosetSMul a (CosetGeom.γ₀ (A ⊔ B) A B) = CosetGeom.γ₀ (A ⊔ B) A B := by
  rw [f112CosetSMul_eq_smul]
  exact CosetGeom.smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) ha

theorem f112CosetSMul_mul {X : Type} [Group X] {A B : Subgroup X} (g h : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) :
    f112CosetSMul g (f112CosetSMul h v) = f112CosetSMul (g * h) v := by
  rw [f112CosetSMul_eq_smul, f112CosetSMul_eq_smul, f112CosetSMul_eq_smul, mul_smul]

theorem f112CosetSMul_one {X : Type} [Group X] {A B : Subgroup X}
    (v : CosetGeom (A ⊔ B) A B) : f112CosetSMul (1 : ↥(A ⊔ B)) v = v := by
  rw [f112CosetSMul_eq_smul, one_smul]

theorem f112CosetSMul_inv_smul {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) :
    f112CosetSMul g⁻¹ (f112CosetSMul g v) = v := by
  rw [f112CosetSMul_mul, inv_mul_cancel, f112CosetSMul_one]

theorem f112CosetSMul_smul_inv {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) :
    f112CosetSMul g (f112CosetSMul g⁻¹ v) = v := by
  rw [f112CosetSMul_mul, mul_inv_cancel, f112CosetSMul_one]

theorem f112CosetSMul_adj {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    {u v : CosetGeom (A ⊔ B) A B} :
    (CosetGeom.graph (A ⊔ B) A B).Adj (f112CosetSMul g u) (f112CosetSMul g v) ↔
      (CosetGeom.graph (A ⊔ B) A B).Adj u v := by
  rw [f112CosetSMul_eq_smul, f112CosetSMul_eq_smul]
  exact CosetGeom.smul_adj g

theorem f112CosetSMul_conj_fix {X : Type} [Group X] {A B : Subgroup X}
    (x h : ↥(A ⊔ B)) {v : CosetGeom (A ⊔ B) A B}
    (hv : f112CosetSMul h v = v) :
    f112CosetSMul (x⁻¹ * h * x) (f112CosetSMul x⁻¹ v) = f112CosetSMul x⁻¹ v := by
  rw [← f112CosetSMul_mul, ← f112CosetSMul_mul]
  calc f112CosetSMul x⁻¹ (f112CosetSMul h (f112CosetSMul x (f112CosetSMul x⁻¹ v)))
      = f112CosetSMul x⁻¹ (f112CosetSMul h v) := by rw [f112CosetSMul_smul_inv]
    _ = f112CosetSMul x⁻¹ v := by rw [hv]

variable [Finite G]

theorem f112_mem_S_of_mem_bigB_of_two_element
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {x : G} (hxB : x ∈ bigB L1 L2 S) (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) : x ∈ S := by
  classical
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) :=
    F1.isSylowTwoOf_bigB_of_normal (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hSB
  have hSnormal : (S.subgroupOf (bigB L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_right : S ≤ bigB L1 L2 S)).mpr hSB
  have hX : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := hx2
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨k, fun y => ?_⟩
    have hy : (y : G) ∈ Subgroup.zpowers x := y.2
    have hydvd : orderOf (y : G) ∣ 2 ^ k :=
      (orderOf_dvd_of_mem_zpowers hy).trans (by rw [hk])
    rw [← Subgroup.orderOf_coe y]
    exact hydvd
  have hle : Subgroup.zpowers x ≤ S :=
    CFSG.Quasithin.F7.le_of_normal_sylow hSylB hSnormal
      (Subgroup.zpowers_le.mpr hxB) hX
  exact hle (Subgroup.mem_zpowers x)

theorem f112_mem_C1_of_fixes_γ₀ (L1 L2 S : Subgroup G) {h : f112Act L1 L2 S}
    (hfix : f112CosetSMul h (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) :
    (h : ↥(f112BaseGroup L1 L2 S)) ∈ f112C1 L1 L2 S := by
  have hmem : (h : ↥(f112BaseGroup L1 L2 S)) ∈
      CosetGeom.stab (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
    apply CosetGeom.mem_stab_of_smul_eq
    simpa [f112CosetSMul_eq_smul] using hfix
  rwa [CosetGeom.stab_γ₀ (le_sup_left :
    f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)] at hmem

theorem f112_mem_C2_of_fixes_γ₁ (L1 L2 S : Subgroup G) {h : f112Act L1 L2 S}
    (hfix : f112CosetSMul h (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) :
    (h : ↥(f112BaseGroup L1 L2 S)) ∈ f112C2 L1 L2 S := by
  have hmem : (h : ↥(f112BaseGroup L1 L2 S)) ∈
      CosetGeom.stab (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
    apply CosetGeom.mem_stab_of_smul_eq
    simpa [f112CosetSMul_eq_smul] using hfix
  rwa [CosetGeom.stab_γ₁ (le_sup_right :
    f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)] at hmem

theorem mem_f112C1_of_mem_P1 {L1 L2 S : Subgroup G}
    {x : ↥(f112BaseGroup L1 L2 S)} (hx : ((x : G)) ∈ P1 L1 L2 S) :
    x ∈ f112C1 L1 L2 S := by
  exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩

theorem mem_f112C2_of_mem_P2 {L1 L2 S : Subgroup G}
    {x : ↥(f112BaseGroup L1 L2 S)} (hx : ((x : G)) ∈ P2 L1 L2 S) :
    x ∈ f112C2 L1 L2 S := by
  exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩

theorem f112_C1_inf_C2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    f112C1 L1 L2 S ⊓ f112C2 L1 L2 S =
      (bigB L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : (x : G) ∈ P1 L1 L2 S := by
      have := hx.1
      rw [f112_range_φ1] at this
      exact Subgroup.mem_subgroupOf.mp this
    have hx2 : (x : G) ∈ P2 L1 L2 S := by
      have := hx.2
      rw [f112_range_φ2] at this
      exact Subgroup.mem_subgroupOf.mp this
    rw [← f112_parabolic_inf_eq_bigB hF]
    exact ⟨hx1, hx2⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ P1 L1 L2 S ⊓ P2 L1 L2 S :=
      (f112_parabolic_inf_eq_bigB hF).ge hx
    have hx1 : (x : G) ∈ P1 L1 L2 S := hx'.1
    have hx2 : (x : G) ∈ P2 L1 L2 S := hx'.2
    refine ⟨?_, ?_⟩
    · rw [f112_range_φ1]
      exact Subgroup.mem_subgroupOf.mpr hx1
    · rw [f112_range_φ2]
      exact Subgroup.mem_subgroupOf.mpr hx2

theorem f112_conj_mem_S_of_fixes_nbr_γ₀ {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {h c : f112Act L1 L2 S}
    (hcP1 : ((c : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S)
    (hhP1 : (h : ↥(f112BaseGroup L1 L2 S)) ∈ f112C1 L1 L2 S)
    (hfixc : f112CosetSMul h (f112CosetSMul c (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul c (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ((((c : ↥(f112BaseGroup L1 L2 S))⁻¹ * (h : ↥(f112BaseGroup L1 L2 S)) *
      (c : ↥(f112BaseGroup L1 L2 S)) : ↥(f112BaseGroup L1 L2 S)) : G)) ∈ S := by
  let Y := ↥(f112BaseGroup L1 L2 S)
  have hstab : (h : Y) ∈ conjSub (c : Y) (f112C2 L1 L2 S) := by
    have hmem : (h : Y) ∈ CosetGeom.stab (f112CosetSMul c
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S))) := by
      apply CosetGeom.mem_stab_of_smul_eq
      simpa [f112CosetSMul_eq_smul] using hfixc
    rwa [f112CosetSMul_stab, CosetGeom.stab_γ₁ (le_sup_right :
      f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)] at hmem
  have hcC1 : (c : Y) ∈ f112C1 L1 L2 S := mem_f112C1_of_mem_P1 hcP1
  have hxP1 : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈ f112C1 L1 L2 S :=
    (f112C1 L1 L2 S).mul_mem
      ((f112C1 L1 L2 S).mul_mem ((f112C1 L1 L2 S).inv_mem hcC1) hhP1) hcC1
  have hxP2 : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈ f112C2 L1 L2 S :=
    mem_conjSub.mp hstab
  have hxB : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈
      (bigB L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) := by
    rw [← f112_C1_inf_C2 hF]
    exact ⟨hxP1, hxP2⟩
  refine f112_mem_S_of_mem_bigB_of_two_element hF hSB hxB ?_
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  have hconj : (((c : Y)⁻¹ * (h : Y) * (c : Y) : Y) : G) =
      (MulAut.conj ((c : Y) : G)⁻¹) ((h : Y) : G) := by
    simp [MulAut.conj_apply]
  rw [hconj, (MulAut.conj ((c : Y) : G)⁻¹).orderOf_eq, hk]

theorem f112C1_mem_P1 {L1 L2 S : Subgroup G} {x : ↥(f112BaseGroup L1 L2 S)}
    (hx : x ∈ f112C1 L1 L2 S) : ((x : G)) ∈ P1 L1 L2 S := by
  rcases MonoidHom.mem_range.mp hx with ⟨p, hp⟩
  rw [← hp]
  exact p.2

theorem f112C2_mem_P2 {L1 L2 S : Subgroup G} {x : ↥(f112BaseGroup L1 L2 S)}
    (hx : x ∈ f112C2 L1 L2 S) : ((x : G)) ∈ P2 L1 L2 S := by
  rcases MonoidHom.mem_range.mp hx with ⟨p, hp⟩
  rw [← hp]
  exact p.2

theorem f112_exists_C1_smul_γ1_of_adj_γ0 (L1 L2 S : Subgroup G)
    {u : f112Verts L1 L2 S}
    (hu : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj
      (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) u) :
    ∃ a : f112Act L1 L2 S,
      ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S ∧
        f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = u := by
  cases u with
  | inl x => exact hu.elim
  | inr y =>
    obtain ⟨g, hgC1, hgy⟩ :=
      (CosetGeom.adj_γ₀_inr_iff (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S)).mp hu
    refine ⟨⟨g, (le_sup_left : f112C1 L1 L2 S ≤
      f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hgC1⟩, f112C1_mem_P1 hgC1, ?_⟩
    rw [f112CosetSMul_eq_smul, CosetGeom.smul_γ₁]
    exact congrArg Sum.inr hgy

theorem f112_exists_C2_smul_γ0_of_adj_γ1 (L1 L2 S : Subgroup G)
    {u : f112Verts L1 L2 S}
    (hu : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj
      (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)) u) :
    ∃ a : f112Act L1 L2 S,
      ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S ∧
        f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = u := by
  cases u with
  | inr y => exact hu.elim
  | inl x =>
    obtain ⟨g, hgC2, hgx⟩ :=
      (CosetGeom.adj_γ₁_inl_iff (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S)).mp hu
    refine ⟨⟨g, (le_sup_right : f112C2 L1 L2 S ≤
      f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hgC2⟩, f112C2_mem_P2 hgC2, ?_⟩
    rw [f112CosetSMul_eq_smul, CosetGeom.smul_γ₀]
    exact congrArg Sum.inl hgx

theorem f112VertexCore_smul_γ₁ (L1 L2 S : Subgroup G) (a : f112Act L1 L2 S) :
    f112VertexCore L1 L2 S
        (f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      (Q2 L1 L2 S).map (MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G)).toMonoidHom := by
  rw [f112VertexCore, f112CosetSMul_stab, CosetGeom.stab_γ₁ (le_sup_right :
    f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)]
  rw [show conjSub (a : ↥(f112BaseGroup L1 L2 S)) (f112C2 L1 L2 S) =
      (f112C2 L1 L2 S).map
        (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))).toMonoidHom from rfl]
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))) (f112C2 L1 L2 S), Subgroup.map_map]
  have hcomp : (f112BaseGroup L1 L2 S).subtype.comp
        (MulAut.conj (a : ↥(f112BaseGroup L1 L2 S))).toMonoidHom =
      (MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G)).toMonoidHom.comp
        (f112BaseGroup L1 L2 S).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, f112C2_pCore_map]

theorem f112_mem_Q1_of_fixes_two_nbrs_γ₀ {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1v : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1))
    {h a b : f112Act L1 L2 S}
    (haP1 : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S)
    (hbP1 : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S)
    (hne : f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) ≠
      f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (hfix0 : f112CosetSMul h (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S))
    (hfixa : f112CosetSMul h (f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (hfixb : f112CosetSMul h (f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ((h : ↥(f112BaseGroup L1 L2 S)) : G) ∈ Q1 L1 L2 S := by
  let Y := ↥(f112BaseGroup L1 L2 S)
  have hhP1 : (h : Y) ∈ f112C1 L1 L2 S := f112_mem_C1_of_fixes_γ₀ L1 L2 S hfix0
  let xa : Y := (a : Y)⁻¹ * (h : Y) * (a : Y)
  have hxaS : ((xa : Y) : G) ∈ S := by
    simpa [xa] using f112_conj_mem_S_of_fixes_nbr_γ₀ hF hSB haP1 hhP1 hfixa h2
  have hxaP1 : (xa : Y) ∈ f112C1 L1 L2 S := by
    have haC1 : (a : Y) ∈ f112C1 L1 L2 S := mem_f112C1_of_mem_P1 haP1
    exact (f112C1 L1 L2 S).mul_mem
      ((f112C1 L1 L2 S).mul_mem ((f112C1 L1 L2 S).inv_mem haC1) hhP1) haC1
  let xb : Y := (b : Y)⁻¹ * (h : Y) * (b : Y)
  have hxbS : ((xb : Y) : G) ∈ S := by
    simpa [xb] using f112_conj_mem_S_of_fixes_nbr_γ₀ hF hSB hbP1 hhP1 hfixb h2
  let gY : Y := (a : Y)⁻¹ * (b : Y)
  have hgC1 : gY ∈ f112C1 L1 L2 S := by
    have haC1 : (a : Y) ∈ f112C1 L1 L2 S := mem_f112C1_of_mem_P1 haP1
    have hbC1 : (b : Y) ∈ f112C1 L1 L2 S := mem_f112C1_of_mem_P1 hbP1
    exact (f112C1 L1 L2 S).mul_mem ((f112C1 L1 L2 S).inv_mem haC1) hbC1
  have hgP1 : ((gY : Y) : G) ∈ P1 L1 L2 S := f112C1_mem_P1 hgC1
  have hgB : ((gY : Y) : G) ∉ bigB L1 L2 S := by
    intro hgB
    have hgC2 : gY ∈ f112C2 L1 L2 S :=
      mem_f112C2_of_mem_P2 ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hgB)
    let hgA : f112Act L1 L2 S :=
      ⟨gY, (le_sup_right : f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hgC2⟩
    have hfixg : f112CosetSMul hgA (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
        CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) :=
      f112CosetSMul_γ₁_of_mem (A := f112C1 L1 L2 S) (B := f112C2 L1 L2 S) hgC2
    have hb_eq : b = a * hgA := by
      apply Subtype.ext
      simp [hgA, gY, mul_assoc]
    apply hne
    calc f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S))
        = f112CosetSMul a (f112CosetSMul hgA (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
            f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) := by rw [hfixg]
      _ = f112CosetSMul (a * hgA) (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
          rw [f112CosetSMul_eq_smul, f112CosetSMul_eq_smul, f112CosetSMul_eq_smul,
            mul_smul]
      _ = f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by rw [← hb_eq]
  have hTI : S ⊓ MulAut.conj ((gY : Y) : G) • S = Q1 L1 L2 S :=
    f112_sylow_inf_conj_eq_pCoreOf_left hF hSB h1v hgP1 hgB
  have hxaConj : ((xa : Y) : G) ∈ MulAut.conj ((gY : Y) : G) • S := by
    change ((xa : Y) : G) ∈ conjSub ((gY : Y) : G) S
    refine mem_conjSub.mpr ?_
    convert hxbS using 1
    simp [xa, xb, gY]
    group
  have hxaQ1 : ((xa : Y) : G) ∈ Q1 L1 L2 S := by
    rw [← hTI]
    exact ⟨hxaS, hxaConj⟩
  have hQ1conj : conjSub ((a : Y) : G) (Q1 L1 L2 S) = Q1 L1 L2 S := by
    change (Q1 L1 L2 S).map (MulAut.conj ((a : Y) : G)).toMonoidHom = Q1 L1 L2 S
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)) haP1)
  have hmem : ((h : Y) : G) ∈ conjSub ((a : Y) : G) (Q1 L1 L2 S) := by
    refine mem_conjSub.mpr ?_
    simpa [xa] using hxaQ1
  rwa [hQ1conj] at hmem

theorem f112_conj_mem_S_of_fixes_nbr_γ₁ {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {h c : f112Act L1 L2 S}
    (hcP2 : ((c : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S)
    (hhP2 : (h : ↥(f112BaseGroup L1 L2 S)) ∈ f112C2 L1 L2 S)
    (hfixc : f112CosetSMul h (f112CosetSMul c (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul c (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ((((c : ↥(f112BaseGroup L1 L2 S))⁻¹ * (h : ↥(f112BaseGroup L1 L2 S)) *
      (c : ↥(f112BaseGroup L1 L2 S)) : ↥(f112BaseGroup L1 L2 S)) : G)) ∈ S := by
  let Y := ↥(f112BaseGroup L1 L2 S)
  have hstab : (h : Y) ∈ conjSub (c : Y) (f112C1 L1 L2 S) := by
    have hmem : (h : Y) ∈ CosetGeom.stab (f112CosetSMul c
        (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S))) := by
      apply CosetGeom.mem_stab_of_smul_eq
      simpa [f112CosetSMul_eq_smul] using hfixc
    rwa [f112CosetSMul_stab, CosetGeom.stab_γ₀ (le_sup_left :
      f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)] at hmem
  have hcC2 : (c : Y) ∈ f112C2 L1 L2 S := mem_f112C2_of_mem_P2 hcP2
  have hxP2 : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈ f112C2 L1 L2 S :=
    (f112C2 L1 L2 S).mul_mem
      ((f112C2 L1 L2 S).mul_mem ((f112C2 L1 L2 S).inv_mem hcC2) hhP2) hcC2
  have hxP1 : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈ f112C1 L1 L2 S :=
    mem_conjSub.mp hstab
  have hxB : (c : Y)⁻¹ * (h : Y) * (c : Y) ∈
      (bigB L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) := by
    rw [← f112_C1_inf_C2 hF]
    exact ⟨hxP1, hxP2⟩
  refine f112_mem_S_of_mem_bigB_of_two_element hF hSB hxB ?_
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  have hconj : (((c : Y)⁻¹ * (h : Y) * (c : Y) : Y) : G) =
      (MulAut.conj ((c : Y) : G)⁻¹) ((h : Y) : G) := by
    simp [MulAut.conj_apply]
  rw [hconj, (MulAut.conj ((c : Y) : G)⁻¹).orderOf_eq, hk]

theorem f112_mem_Q2_of_fixes_two_nbrs_γ₁ {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h2v : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2))
    {h a b : f112Act L1 L2 S}
    (haP2 : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S)
    (hbP2 : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S)
    (hne : f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) ≠
      f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (hfix0 : f112CosetSMul h (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S))
    (hfixa : f112CosetSMul h (f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (hfixb : f112CosetSMul h (f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
      f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
      f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)))
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ((h : ↥(f112BaseGroup L1 L2 S)) : G) ∈ Q2 L1 L2 S := by
  let Y := ↥(f112BaseGroup L1 L2 S)
  have hhP2 : (h : Y) ∈ f112C2 L1 L2 S := f112_mem_C2_of_fixes_γ₁ L1 L2 S hfix0
  let xa : Y := (a : Y)⁻¹ * (h : Y) * (a : Y)
  have hxaS : ((xa : Y) : G) ∈ S := by
    simpa [xa] using f112_conj_mem_S_of_fixes_nbr_γ₁ hF hSB haP2 hhP2 hfixa h2
  let xb : Y := (b : Y)⁻¹ * (h : Y) * (b : Y)
  have hxbS : ((xb : Y) : G) ∈ S := by
    simpa [xb] using f112_conj_mem_S_of_fixes_nbr_γ₁ hF hSB hbP2 hhP2 hfixb h2
  let gY : Y := (a : Y)⁻¹ * (b : Y)
  have hgC2 : gY ∈ f112C2 L1 L2 S := by
    have haC2 : (a : Y) ∈ f112C2 L1 L2 S := mem_f112C2_of_mem_P2 haP2
    have hbC2 : (b : Y) ∈ f112C2 L1 L2 S := mem_f112C2_of_mem_P2 hbP2
    exact (f112C2 L1 L2 S).mul_mem ((f112C2 L1 L2 S).inv_mem haC2) hbC2
  have hgP2 : ((gY : Y) : G) ∈ P2 L1 L2 S := f112C2_mem_P2 hgC2
  have hgB : ((gY : Y) : G) ∉ bigB L1 L2 S := by
    intro hgB
    have hgC1 : gY ∈ f112C1 L1 L2 S :=
      mem_f112C1_of_mem_P1 ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hgB)
    let hgA : f112Act L1 L2 S :=
      ⟨gY, (le_sup_left : f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hgC1⟩
    have hfixg : f112CosetSMul hgA (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
        CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) :=
      f112CosetSMul_γ₀_of_mem (A := f112C1 L1 L2 S) (B := f112C2 L1 L2 S) hgC1
    have hb_eq : b = a * hgA := by
      apply Subtype.ext
      simp [hgA, gY, mul_assoc]
    apply hne
    calc f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S))
        = f112CosetSMul a (f112CosetSMul hgA (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
            f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) := by rw [hfixg]
      _ = f112CosetSMul (a * hgA) (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
          rw [f112CosetSMul_mul]
      _ = f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by rw [← hb_eq]
  have hTI : S ⊓ MulAut.conj ((gY : Y) : G) • S = Q2 L1 L2 S :=
    f112_sylow_inf_conj_eq_pCoreOf_right hF hSB h2v hgP2 hgB
  have hxaConj : ((xa : Y) : G) ∈ MulAut.conj ((gY : Y) : G) • S := by
    change ((xa : Y) : G) ∈ conjSub ((gY : Y) : G) S
    refine mem_conjSub.mpr ?_
    convert hxbS using 1
    simp [xa, xb, gY]
    group
  have hxaQ2 : ((xa : Y) : G) ∈ Q2 L1 L2 S := by
    rw [← hTI]
    exact ⟨hxaS, hxaConj⟩
  have hQ2conj : conjSub ((a : Y) : G) (Q2 L1 L2 S) = Q2 L1 L2 S := by
    change (Q2 L1 L2 S).map (MulAut.conj ((a : Y) : G)).toMonoidHom = Q2 L1 L2 S
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)) haP2)
  have hmem : ((h : Y) : G) ∈ conjSub ((a : Y) : G) (Q2 L1 L2 S) := by
    refine mem_conjSub.mpr ?_
    simpa [xa] using hxaQ2
  rwa [hQ2conj] at hmem

theorem f112_mem_vertexCore_of_fixes_two_nbrs
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1v : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1))
    (h2v : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2))
    {h : f112Act L1 L2 S} {v u w : f112Verts L1 L2 S}
    (hu : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj v u)
    (hw : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj v w)
    (hne : u ≠ w)
    (hfixv : f112CosetSMul h v = v)
    (hfixu : f112CosetSMul h u = u)
    (hfixw : f112CosetSMul h w = w)
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ((h : ↥(f112BaseGroup L1 L2 S)) : G) ∈ f112VertexCore L1 L2 S v := by
  let Y := ↥(f112BaseGroup L1 L2 S)
  cases hv : CosetGeom.vtype v with
  | false =>
    obtain ⟨x, hxv⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S) hv
    have hxv' : f112CosetSMul x (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = v := hxv.symm
    let h' : f112Act L1 L2 S := x⁻¹ * h * x
    have hxinvv : f112CosetSMul x⁻¹ v =
        CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) := by
      rw [← hxv', f112CosetSMul_inv_smul]
    have hfix0 : f112CosetSMul h' (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
        CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) := by
      have := f112CosetSMul_conj_fix x h hfixv
      rwa [hxinvv] at this
    have hu' : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)).Adj
        (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)) (f112CosetSMul x⁻¹ u) := by
      have := (f112CosetSMul_adj x⁻¹).mpr hu
      rwa [hxinvv] at this
    have hw' : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)).Adj
        (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)) (f112CosetSMul x⁻¹ w) := by
      have := (f112CosetSMul_adj x⁻¹).mpr hw
      rwa [hxinvv] at this
    have hfixa : f112CosetSMul h' (f112CosetSMul x⁻¹ u) = f112CosetSMul x⁻¹ u :=
      f112CosetSMul_conj_fix x h hfixu
    have hfixb : f112CosetSMul h' (f112CosetSMul x⁻¹ w) = f112CosetSMul x⁻¹ w :=
      f112CosetSMul_conj_fix x h hfixw
    have hne' : f112CosetSMul x⁻¹ u ≠ f112CosetSMul x⁻¹ w := by
      intro hEq
      apply hne
      have := congrArg (f112CosetSMul x) hEq
      simpa [f112CosetSMul_smul_inv] using this
    obtain ⟨a, haP1, haγ⟩ := f112_exists_C1_smul_γ1_of_adj_γ0 L1 L2 S hu'
    obtain ⟨b, hbP1, hbγ⟩ := f112_exists_C1_smul_γ1_of_adj_γ0 L1 L2 S hw'
    have hfixa' : f112CosetSMul h' (f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
        f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
        f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [haγ]
      exact hfixa
    have hfixb' : f112CosetSMul h' (f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔
        f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
        f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [hbγ]
      exact hfixb
    have hneab : f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) ≠
        f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [haγ, hbγ]
      exact hne'
    have h2' : ∃ k : ℕ, orderOf ((h' : Y) : G) = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hconj : ((h' : Y) : G) = (MulAut.conj ((x : Y) : G)⁻¹) ((h : Y) : G) := by
        simp [h', MulAut.conj_apply]
      rw [hconj, (MulAut.conj ((x : Y) : G)⁻¹).orderOf_eq, hk]
    have hQ1 : ((h' : Y) : G) ∈ Q1 L1 L2 S :=
      f112_mem_Q1_of_fixes_two_nbrs_γ₀ hF hSB h1v haP1 hbP1 hneab hfix0 hfixa' hfixb' h2'
    have hmem : ((h : Y) : G) ∈ conjSub ((x : Y) : G) (Q1 L1 L2 S) := by
      refine mem_conjSub.mpr ?_
      simpa [h'] using hQ1
    rw [show f112VertexCore L1 L2 S v =
        (Q1 L1 L2 S).map (MulAut.conj ((x : Y) : G)).toMonoidHom by
      rw [← hxv']
      exact f112VertexCore_smul_γ₀ L1 L2 S x]
    change ((h : Y) : G) ∈ conjSub ((x : Y) : G) (Q1 L1 L2 S)
    exact hmem
  | true =>
    obtain ⟨x, hxv⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S) hv
    have hxv' : f112CosetSMul x (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = v := hxv.symm
    let h' : f112Act L1 L2 S := x⁻¹ * h * x
    have hxinvv : f112CosetSMul x⁻¹ v =
        CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) := by
      rw [← hxv', f112CosetSMul_inv_smul]
    have hfix0 : f112CosetSMul h' (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
        CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S) := by
      have := f112CosetSMul_conj_fix x h hfixv
      rwa [hxinvv] at this
    have hu' : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)).Adj
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)) (f112CosetSMul x⁻¹ u) := by
      have := (f112CosetSMul_adj x⁻¹).mpr hu
      rwa [hxinvv] at this
    have hw' : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S)).Adj
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)) (f112CosetSMul x⁻¹ w) := by
      have := (f112CosetSMul_adj x⁻¹).mpr hw
      rwa [hxinvv] at this
    have hfixa : f112CosetSMul h' (f112CosetSMul x⁻¹ u) = f112CosetSMul x⁻¹ u :=
      f112CosetSMul_conj_fix x h hfixu
    have hfixb : f112CosetSMul h' (f112CosetSMul x⁻¹ w) = f112CosetSMul x⁻¹ w :=
      f112CosetSMul_conj_fix x h hfixw
    have hne' : f112CosetSMul x⁻¹ u ≠ f112CosetSMul x⁻¹ w := by
      intro hEq
      apply hne
      have := congrArg (f112CosetSMul x) hEq
      simpa [f112CosetSMul_smul_inv] using this
    obtain ⟨a, haP2, haγ⟩ := f112_exists_C2_smul_γ0_of_adj_γ1 L1 L2 S hu'
    obtain ⟨b, hbP2, hbγ⟩ := f112_exists_C2_smul_γ0_of_adj_γ1 L1 L2 S hw'
    have hfixa' : f112CosetSMul h' (f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
        f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
        f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [haγ]
      exact hfixa
    have hfixb' : f112CosetSMul h' (f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔
        f112C2 L1 L2 S) (f112C1 L1 L2 S) (f112C2 L1 L2 S))) =
        f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [hbγ]
      exact hfixb
    have hneab : f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) ≠
        f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
      rw [haγ, hbγ]
      exact hne'
    have h2' : ∃ k : ℕ, orderOf ((h' : Y) : G) = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hconj : ((h' : Y) : G) = (MulAut.conj ((x : Y) : G)⁻¹) ((h : Y) : G) := by
        simp [h', MulAut.conj_apply]
      rw [hconj, (MulAut.conj ((x : Y) : G)⁻¹).orderOf_eq, hk]
    have hQ2 : ((h' : Y) : G) ∈ Q2 L1 L2 S :=
      f112_mem_Q2_of_fixes_two_nbrs_γ₁ hF hSB h2v haP2 hbP2 hneab hfix0 hfixa' hfixb' h2'
    have hmem : ((h : Y) : G) ∈ conjSub ((x : Y) : G) (Q2 L1 L2 S) := by
      refine mem_conjSub.mpr ?_
      simpa [h'] using hQ2
    rw [show f112VertexCore L1 L2 S v =
        (Q2 L1 L2 S).map (MulAut.conj ((x : Y) : G)).toMonoidHom by
      rw [← hxv']
      exact f112VertexCore_smul_γ₁ L1 L2 S x]
    change ((h : Y) : G) ∈ conjSub ((x : Y) : G) (Q2 L1 L2 S)
    exact hmem

theorem f112CosetSMul_injective {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B)) :
    Function.Injective (f112CosetSMul g) := by
  intro a b hab
  have h := congrArg (f112CosetSMul g⁻¹) hab
  simpa [f112CosetSMul_smul_inv] using h

theorem f112_path_mem_vertexCore
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1v : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1))
    (h2v : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2))
    {p : GPath (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)) 5}
    (hp : p.NoBack)
    {h : f112Act L1 L2 S}
    (hfix : ∀ i, i ≤ 5 → f112CosetSMul h (p i) = p i)
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ∀ i, 1 ≤ i → i ≤ 4 →
      ((h : ↥(f112BaseGroup L1 L2 S)) : G) ∈ f112VertexCore L1 L2 S (p i) := by
  intro i hi1 hi4
  have hu : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj (p i) (p (i - 1)) := by
    have := (p.adj (i - 1) (by omega)).symm
    rwa [Nat.sub_add_cancel hi1] at this
  have hw : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj (p i) (p (i + 1)) := p.adj i (by omega)
  have hne : p (i - 1) ≠ p (i + 1) := by
    have := hp (i - 1) (by omega)
    rwa [show i - 1 + 2 = i + 1 by omega] at this
  exact f112_mem_vertexCore_of_fixes_two_nbrs hF.toW hSB h1v h2v hu hw hne
    (hfix i (by omega)) (hfix (i - 1) (by omega)) (hfix (i + 1) (by omega)) h2

end CFSG.Quasithin.Stroth
