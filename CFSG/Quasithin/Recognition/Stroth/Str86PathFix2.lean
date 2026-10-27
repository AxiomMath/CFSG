module

public import CFSG.Quasithin.Recognition.Stroth.Str86PathFix

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem f112_fixes_map_conj {L1 L2 S : Subgroup G} {n : ℕ}
    {p : GPath (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)) n}
    {h x : f112Act L1 L2 S}
    (hfix : ∀ i, i ≤ n → f112CosetSMul h (p i) = p i) :
    ∀ i, i ≤ n →
      f112CosetSMul (x⁻¹ * h * x)
        ((p.map (f112CosetSMul x⁻¹)
          (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab)) i) =
        (p.map (f112CosetSMul x⁻¹)
          (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab)) i := by
  intro i hi
  rw [GPath.map_apply]
  exact f112CosetSMul_conj_fix x h (hfix i hi)

theorem f112_orderOf_conj_two_power {L1 L2 S : Subgroup G} {h x : f112Act L1 L2 S}
    (h2 : ∃ k : ℕ, orderOf ((h : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k) :
    ∃ k : ℕ, orderOf (((x⁻¹ * h * x : f112Act L1 L2 S) : ↥(f112BaseGroup L1 L2 S)) : G) =
      2 ^ k := by
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  have hconj : (((x⁻¹ * h * x : f112Act L1 L2 S) : ↥(f112BaseGroup L1 L2 S)) : G) =
      (MulAut.conj ((x : ↥(f112BaseGroup L1 L2 S)) : G)⁻¹)
        ((h : ↥(f112BaseGroup L1 L2 S)) : G) := by
    simp [MulAut.conj_apply]
  rw [hconj, (MulAut.conj ((x : ↥(f112BaseGroup L1 L2 S)) : G)⁻¹).orderOf_eq, hk]

theorem f112_vtype_smul {L1 L2 S : Subgroup G} (x : f112Act L1 L2 S)
    (v : f112Verts L1 L2 S) :
    CosetGeom.vtype (f112CosetSMul x v) = CosetGeom.vtype v := by
  rw [f112CosetSMul_eq_smul]
  exact CosetGeom.vtype_smul x v


theorem str86_pathFix_of_shape {L1 L2 S : Subgroup G} {k : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2) (hsh : Str86Shape L1 L2 S k) :
    let c := f112Completion L1 L2 S
    ∀ p : GPath c.graph 5, p.NoBack →
    ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
      (∀ i, i ≤ 5 → f112CosetSMul g (p i) = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
  dsimp only
  intro p hp g hfix hg2
  have h1v : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1) :=
    Or.inr (Or.inl h1)
  obtain ⟨n, hn⟩ := h2
  have h2v : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2) :=
    Or.inr (Or.inr ⟨n, CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hn, hn⟩)
  obtain ⟨kg, hkg⟩ := hg2
  have hg2G : ∃ r : ℕ, orderOf ((g : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ r := by
    refine ⟨kg, ?_⟩
    rw [Subgroup.orderOf_coe (g : ↥(f112BaseGroup L1 L2 S)), Subgroup.orderOf_coe g, hkg]
  have hadj23 : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
      (f112C2 L1 L2 S)).Adj (p 2) (p 3) := p.adj 2 (by norm_num)
  by_cases hp2 : CosetGeom.vtype (p 2) = true
  · obtain ⟨x, hx | hx⟩ := CosetGeom.exists_smul_edge hadj23
    · have hv : CosetGeom.vtype (p 2) = false := by
        rw [← hx.1, CosetGeom.vtype_smul, CosetGeom.vtype_γ₀]
      rw [hp2] at hv
      exact (Bool.false_ne_true hv.symm).elim
    · let r : GPath (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) 5 :=
        p.map (f112CosetSMul x⁻¹) (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab)
      have hx1 : f112CosetSMul x (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = p 2 := by
        simpa [f112CosetSMul_eq_smul] using hx.2
      have hx0 : f112CosetSMul x (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = p 3 := by
        simpa [f112CosetSMul_eq_smul] using hx.1
      have hr2 : r 2 = CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S) := by
        change f112CosetSMul x⁻¹ (p 2) = _
        rw [← hx1, f112CosetSMul_inv_smul]
      have hr3 : r 3 = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S) := by
        change f112CosetSMul x⁻¹ (p 3) = _
        rw [← hx0, f112CosetSMul_inv_smul]
      have hr : r.NoBack :=
        GPath.NoBack.map_of_injective (f := f112CosetSMul x⁻¹)
          (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab) (f112CosetSMul_injective x⁻¹) hp
      let h' : f112Act L1 L2 S := x⁻¹ * g * x
      have hrfix : ∀ i, i ≤ 5 → f112CosetSMul h' (r i) = r i := by
        simpa [h', r] using
          (f112_fixes_map_conj (L1 := L1) (L2 := L2) (S := S) (n := 5)
            (p := p) (h := g) (x := x) hfix)
      have h2' : ∃ r : ℕ, orderOf ((h' : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ r := by
        simpa [h'] using f112_orderOf_conj_two_power (L1 := L1) (L2 := L2) (S := S)
          (h := g) (x := x) hg2G
      have hmem1 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 1
        (by norm_num) (by norm_num)
      have hmem2 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 2
        (by norm_num) (by norm_num)
      have hmem3 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 3
        (by norm_num) (by norm_num)
      have hmem4 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 4
        (by norm_num) (by norm_num)
      have hrn1 : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)).Adj (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) (r 1) := by
        have := (r.adj 1 (by norm_num)).symm
        rwa [hr2] at this
      obtain ⟨a, haP2, haγ⟩ := f112_exists_C2_smul_γ0_of_adj_γ1 L1 L2 S hrn1
      have hrn4 : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)).Adj (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) (r 4) := by
        have := r.adj 3 (by norm_num)
        rwa [hr3] at this
      obtain ⟨b, hbP1, hbγ⟩ := f112_exists_C1_smul_γ1_of_adj_γ0 L1 L2 S hrn4
      have haB : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∉ bigB L1 L2 S := by
        intro haB
        have haP1 : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S :=
          (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) haB
        have haC1 : (a : ↥(f112BaseGroup L1 L2 S)) ∈ f112C1 L1 L2 S :=
          mem_f112C1_of_mem_P1 haP1
        have hfixa := f112CosetSMul_γ₀_of_mem (A := f112C1 L1 L2 S)
          (B := f112C2 L1 L2 S) haC1
        have hne := hr 1 (by norm_num)
        apply hne
        calc r 1 = f112CosetSMul a (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := haγ.symm
          _ = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
                (f112C2 L1 L2 S) := hfixa
          _ = r 3 := hr3.symm
      have hbB : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∉ bigB L1 L2 S := by
        intro hbB
        have hbP2 : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S :=
          (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hbB
        have hbC2 : (b : ↥(f112BaseGroup L1 L2 S)) ∈ f112C2 L1 L2 S :=
          mem_f112C2_of_mem_P2 hbP2
        have hfixb := f112CosetSMul_γ₁_of_mem (A := f112C1 L1 L2 S)
          (B := f112C2 L1 L2 S) hbC2
        have hne := hr 2 (by norm_num)
        apply hne
        calc r 2 = CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S) := hr2
          _ = f112CosetSMul b (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
                (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := hfixb.symm
          _ = r 4 := hbγ
      have hcore1 : f112VertexCore L1 L2 S (r 1) =
          MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G) • Q1 L1 L2 S := by
        rw [← haγ, f112VertexCore_smul_γ₀]
        rfl
      have hcore2 : f112VertexCore L1 L2 S (r 2) = Q2 L1 L2 S := by
        rw [hr2]
        exact f112VertexCore_γ₁ L1 L2 S
      have hcore3 : f112VertexCore L1 L2 S (r 3) = Q1 L1 L2 S := by
        rw [hr3]
        exact f112VertexCore_γ₀ L1 L2 S
      have hcore4 : f112VertexCore L1 L2 S (r 4) =
          MulAut.conj ((b : ↥(f112BaseGroup L1 L2 S)) : G) • Q2 L1 L2 S := by
        rw [← hbγ, f112VertexCore_smul_γ₁]
        rfl
      have hmemR : ((h' : ↥(f112BaseGroup L1 L2 S)) : G) ∈
          MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G) • Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓
            Q1 L1 L2 S ⊓
              MulAut.conj ((b : ↥(f112BaseGroup L1 L2 S)) : G) • Q2 L1 L2 S := by
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rwa [hcore1] at hmem1
        · rwa [hcore2] at hmem2
        · rwa [hcore3] at hmem3
        · rwa [hcore4] at hmem4
      have hbot := hsh.bprime ((a : ↥(f112BaseGroup L1 L2 S)) : G) haP2 haB
        ((b : ↥(f112BaseGroup L1 L2 S)) : G) hbP1 hbB
      rw [hbot] at hmemR
      have hh'G : ((h' : ↥(f112BaseGroup L1 L2 S)) : G) = 1 :=
        Subgroup.mem_bot.mp (show ((h' : ↥(f112BaseGroup L1 L2 S)) : G) ∈
          (⊥ : Subgroup G) from hmemR)
      have hh' : h' = 1 := by
        apply Subtype.ext
        exact Subgroup.subtype_injective (f112BaseGroup L1 L2 S) (by simpa using hh'G)
      have hg : g = x * h' * x⁻¹ := by
        show g = x * (x⁻¹ * g * x) * x⁻¹
        group
      rw [hg, hh']
      simp
  · have hp2f : CosetGeom.vtype (p 2) = false := by
      cases h : CosetGeom.vtype (p 2) <;> simp_all
    obtain ⟨x, hx | hx⟩ := CosetGeom.exists_smul_edge hadj23
    · let r : GPath (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) 5 :=
        p.map (f112CosetSMul x⁻¹) (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab)
      have hx0 : f112CosetSMul x (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = p 2 := by
        simpa [f112CosetSMul_eq_smul] using hx.1
      have hx1 : f112CosetSMul x (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) = p 3 := by
        simpa [f112CosetSMul_eq_smul] using hx.2
      have hr2 : r 2 = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S) := by
        change f112CosetSMul x⁻¹ (p 2) = _
        rw [← hx0, f112CosetSMul_inv_smul]
      have hr3 : r 3 = CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S) := by
        change f112CosetSMul x⁻¹ (p 3) = _
        rw [← hx1, f112CosetSMul_inv_smul]
      have hr : r.NoBack :=
        GPath.NoBack.map_of_injective (f := f112CosetSMul x⁻¹)
          (fun a b hab => (f112CosetSMul_adj x⁻¹).mpr hab) (f112CosetSMul_injective x⁻¹) hp
      let h' : f112Act L1 L2 S := x⁻¹ * g * x
      have hrfix : ∀ i, i ≤ 5 → f112CosetSMul h' (r i) = r i := by
        simpa [h', r] using
          (f112_fixes_map_conj (L1 := L1) (L2 := L2) (S := S) (n := 5)
            (p := p) (h := g) (x := x) hfix)
      have h2' : ∃ r : ℕ, orderOf ((h' : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ r := by
        simpa [h'] using f112_orderOf_conj_two_power (L1 := L1) (L2 := L2) (S := S)
          (h := g) (x := x) hg2G
      have hmem1 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 1
        (by norm_num) (by norm_num)
      have hmem2 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 2
        (by norm_num) (by norm_num)
      have hmem3 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 3
        (by norm_num) (by norm_num)
      have hmem4 := f112_path_mem_vertexCore hF hSB h1v h2v hr hrfix h2' 4
        (by norm_num) (by norm_num)
      have hrn1 : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)).Adj (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) (r 1) := by
        have := (r.adj 1 (by norm_num)).symm
        rwa [hr2] at this
      obtain ⟨a, haP1, haγ⟩ := f112_exists_C1_smul_γ1_of_adj_γ0 L1 L2 S hrn1
      have hrn4 : (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
          (f112C2 L1 L2 S)).Adj (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
            (f112C1 L1 L2 S) (f112C2 L1 L2 S)) (r 4) := by
        have := r.adj 3 (by norm_num)
        rwa [hr3] at this
      obtain ⟨b, hbP2, hbγ⟩ := f112_exists_C2_smul_γ0_of_adj_γ1 L1 L2 S hrn4
      have haB : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∉ bigB L1 L2 S := by
        intro haB
        have haP2 : ((a : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P2 L1 L2 S :=
          (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) haB
        have haC2 : (a : ↥(f112BaseGroup L1 L2 S)) ∈ f112C2 L1 L2 S :=
          mem_f112C2_of_mem_P2 haP2
        have hfixa := f112CosetSMul_γ₁_of_mem (A := f112C1 L1 L2 S)
          (B := f112C2 L1 L2 S) haC2
        have hne := hr 1 (by norm_num)
        apply hne
        calc r 1 = f112CosetSMul a (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := haγ.symm
          _ = CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
                (f112C2 L1 L2 S) := hfixa
          _ = r 3 := hr3.symm
      have hbB : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∉ bigB L1 L2 S := by
        intro hbB
        have hbP1 : ((b : ↥(f112BaseGroup L1 L2 S)) : G) ∈ P1 L1 L2 S :=
          (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hbB
        have hbC1 : (b : ↥(f112BaseGroup L1 L2 S)) ∈ f112C1 L1 L2 S :=
          mem_f112C1_of_mem_P1 hbP1
        have hfixb := f112CosetSMul_γ₀_of_mem (A := f112C1 L1 L2 S)
          (B := f112C2 L1 L2 S) hbC1
        have hne := hr 2 (by norm_num)
        apply hne
        calc r 2 = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S) := hr2
          _ = f112CosetSMul b (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
                (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := hfixb.symm
          _ = r 4 := hbγ
      have hcore1 : f112VertexCore L1 L2 S (r 1) =
          MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G) • Q2 L1 L2 S := by
        rw [← haγ, f112VertexCore_smul_γ₁]
        rfl
      have hcore2 : f112VertexCore L1 L2 S (r 2) = Q1 L1 L2 S := by
        rw [hr2]
        exact f112VertexCore_γ₀ L1 L2 S
      have hcore3 : f112VertexCore L1 L2 S (r 3) = Q2 L1 L2 S := by
        rw [hr3]
        exact f112VertexCore_γ₁ L1 L2 S
      have hcore4 : f112VertexCore L1 L2 S (r 4) =
          MulAut.conj ((b : ↥(f112BaseGroup L1 L2 S)) : G) • Q1 L1 L2 S := by
        rw [← hbγ, f112VertexCore_smul_γ₀]
        rfl
      have hmemR' : ((h' : ↥(f112BaseGroup L1 L2 S)) : G) ∈
          MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G) • Q2 L1 L2 S ⊓ Q1 L1 L2 S ⊓
            Q2 L1 L2 S ⊓
              MulAut.conj ((b : ↥(f112BaseGroup L1 L2 S)) : G) • Q1 L1 L2 S := by
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rwa [hcore1] at hmem1
        · rwa [hcore2] at hmem2
        · rwa [hcore3] at hmem3
        · rwa [hcore4] at hmem4
      have hbot := hsh.bprime ((b : ↥(f112BaseGroup L1 L2 S)) : G) hbP2 hbB
        ((a : ↥(f112BaseGroup L1 L2 S)) : G) haP1 haB
      have hmemR : ((h' : ↥(f112BaseGroup L1 L2 S)) : G) ∈
          MulAut.conj ((b : ↥(f112BaseGroup L1 L2 S)) : G) • Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓
            Q1 L1 L2 S ⊓
              MulAut.conj ((a : ↥(f112BaseGroup L1 L2 S)) : G) • Q2 L1 L2 S := by
        simpa [inf_assoc, inf_left_comm, inf_comm] using hmemR'
      rw [hbot] at hmemR
      have hh'G : ((h' : ↥(f112BaseGroup L1 L2 S)) : G) = 1 :=
        Subgroup.mem_bot.mp (show ((h' : ↥(f112BaseGroup L1 L2 S)) : G) ∈
          (⊥ : Subgroup G) from hmemR)
      have hh' : h' = 1 := by
        apply Subtype.ext
        exact Subgroup.subtype_injective (f112BaseGroup L1 L2 S) (by simpa using hh'G)
      have hg : g = x * h' * x⁻¹ := by
        show g = x * (x⁻¹ * g * x) * x⁻¹
        group
      rw [hg, hh']
      simp
    · have hv : CosetGeom.vtype (p 2) = true := by
        rw [← hx.2, CosetGeom.vtype_smul, CosetGeom.vtype_γ₁]
      rw [hp2f] at hv
      exact (Bool.false_ne_true hv).elim

end CFSG.Quasithin.Stroth
