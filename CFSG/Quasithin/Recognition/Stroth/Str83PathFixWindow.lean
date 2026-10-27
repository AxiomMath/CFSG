module

public import CFSG.Quasithin.Recognition.Stroth.Str83SevenPath
public import CFSG.Quasithin.Recognition.Stroth.Str86PathFix2
public import CFSG.Quasithin.Background.F3PathFix
public import CFSG.Quasithin.Recognition.Stroth.Str83LocTransParts
public import CFSG.Quasithin.Recognition.Stroth.Str83OrdersParts

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem vtype_odd_path {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G} {n : ℕ}
    (p : GPath (CosetGeom.graph G₀ G₁ G₂) n) (hn : Odd n) :
    CosetGeom.vtype (p n) = !CosetGeom.vtype (p 0) := by
  have key : ∀ i, i ≤ n → CosetGeom.vtype (p i) =
      if i % 2 = 0 then CosetGeom.vtype (p 0) else !CosetGeom.vtype (p 0) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i < n := by omega
      have hne := CosetGeom.vtype_ne_of_adj (p.adj i hi')
      have hih := ih (by omega)
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · have hmod : (i + 1) % 2 = 1 := by omega
        rw [hih, if_pos h0] at hne
        rw [hmod, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
        cases hb : CosetGeom.vtype (p 0) <;>
          cases hb' : CosetGeom.vtype (p (i + 1))
        all_goals simp_all
      · have hmod : (i + 1) % 2 = 0 := by omega
        rw [hih, if_neg (by omega : i % 2 ≠ 0)] at hne
        rw [hmod, if_pos rfl]
        cases hb : CosetGeom.vtype (p 0) <;>
          cases hb' : CosetGeom.vtype (p (i + 1))
        all_goals simp_all
  have h := key n le_rfl
  rw [h, Nat.odd_iff.mp hn]
  simp

private theorem f112_pathFix_of_sevenPath_data
    {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hBig : VBig L2) (hL2 : VL2 L2)
    (hm : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ (2 * (2 * a + 1)))
    (hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ (2 * a + 1))
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hmB : Odd (S.relIndex (bigB L1 L2 S)))
    (hB : Nat.card ↥((f112Completion L1 L2 S).φ1.range ⊓
      (f112Completion L1 L2 S).φ2.range) =
      ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ 4 *
        S.relIndex (bigB L1 L2 S))
    (h : Str83SevenPath) :
    ∀ p : GPath (f112Completion L1 L2 S).graph 9, p.NoBack →
      ∀ g : f112Act L1 L2 S,
        (∀ i, i ≤ 9 → f112CosetSMul g (p i) = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
  let c' := f112Completion L1 L2 S
  have hc' : c'.IsFaithful := f112Completion_isFaithful L1 L2 S
  have h1v : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1) :=
    Or.inl ⟨a, ha, hSz⟩
  have h2v : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2) :=
    Or.inr (Or.inr ⟨2 * a + 1,
      CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hBig hm, hm⟩)
  obtain ⟨x1, hx1P1, hx1B, x2, hx2P2, hx2B, hwin⟩ := h G L1 L2 S a hF ha hSz hBig hL2
  let x1' : f112BaseGroup L1 L2 S :=
    ⟨x1, (le_sup_left : P1 L1 L2 S ≤ f112BaseGroup L1 L2 S) hx1P1⟩
  let x2' : f112BaseGroup L1 L2 S :=
    ⟨x2, (le_sup_right : P2 L1 L2 S ≤ f112BaseGroup L1 L2 S) hx2P2⟩
  have hx1C1 : x1' ∈ f112C1 L1 L2 S := mem_f112C1_of_mem_P1 hx1P1
  have hx2C2 : x2' ∈ f112C2 L1 L2 S := mem_f112C2_of_mem_P2 hx2P2
  let X1 : f112Act L1 L2 S :=
    ⟨x1', (le_sup_left : f112C1 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hx1C1⟩
  let X2 : f112Act L1 L2 S :=
    ⟨x2', (le_sup_right : f112C2 L1 L2 S ≤ f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) hx2C2⟩
  have hX1fix0 : f112CosetSMul X1 (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S) :=
    f112CosetSMul_γ₀_of_mem (A := f112C1 L1 L2 S) (B := f112C2 L1 L2 S) (a := X1) hx1C1
  have hX2fix1 : f112CosetSMul X2 (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S) :=
    f112CosetSMul_γ₁_of_mem (A := f112C1 L1 L2 S) (B := f112C2 L1 L2 S) (a := X2) hx2C2
  let τa : f112Act L1 L2 S := X2 * X1
  have hτG : ((τa : ↥(f112BaseGroup L1 L2 S)) : G) = x2 * x1 := by
    simp [τa, X1, X2, x1', x2']
  let A : f112Verts L1 L2 S := f112CosetSMul τa⁻¹ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
    (f112C1 L1 L2 S) (f112C2 L1 L2 S))
  let B : f112Verts L1 L2 S := CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
    (f112C1 L1 L2 S) (f112C2 L1 L2 S)
  have hX2invfix1 : f112CosetSMul X2⁻¹ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S) := by
    rw [← hX2fix1, f112CosetSMul_inv_smul, hX2fix1]
  have hX1invfix0 : f112CosetSMul X1⁻¹ (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
      CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
        (f112C2 L1 L2 S) := by
    rw [← hX1fix0, f112CosetSMul_inv_smul, hX1fix0]
  have hA : A = f112CosetSMul X1⁻¹ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
    show f112CosetSMul τa⁻¹ _ = _
    have htau : τa = X2 * X1 := rfl
    rw [show τa⁻¹ = X1⁻¹ * X2⁻¹ by rw [htau]; group, ← f112CosetSMul_mul, hX2invfix1]
  have hAB : c'.graph.Adj A B := by
    have h := (f112CosetSMul_adj X1⁻¹).mpr
      (CosetGeom.adj_γ₀_γ₁ (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S)).symm
    rw [hX1invfix0] at h
    rwa [← hA] at h
  have hτA : f112CosetSMul τa A = CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S) := by
    show f112CosetSMul τa (f112CosetSMul τa⁻¹ _) = _
    rw [f112CosetSMul_smul_inv]
  have hBτA : c'.graph.Adj B (f112CosetSMul τa A) := by
    rw [hτA, show B = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (f112C1 L1 L2 S) (f112C2 L1 L2 S) from rfl]
    exact CosetGeom.adj_γ₀_γ₁
  have hAne : A ≠ f112CosetSMul τa A := by
    intro h
    rw [hτA] at h
    have hX1C2 : x1' ∈ f112C2 L1 L2 S := by
      have hfix : f112CosetSMul X1⁻¹ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) =
          CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
            (f112C2 L1 L2 S) := by
        rw [← hA]
        exact h
      have h2 := f112_mem_C2_of_fixes_γ₁ L1 L2 S hfix
      have h2' : x1'⁻¹ ∈ f112C2 L1 L2 S := by simpa [X1] using h2
      exact (f112C2 L1 L2 S).inv_mem_iff.mp h2'
    have hx1B' : x1' ∈ (bigB L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) := by
      rw [← f112_C1_inf_C2 hF]
      exact ⟨hx1C1, hX1C2⟩
    exact hx1B (Subgroup.mem_subgroupOf.mp hx1B')
  have hBne : B ≠ f112CosetSMul τa B := by
    intro h
    have hτB : f112CosetSMul τa B = f112CosetSMul X2 B := by
      show f112CosetSMul (X2 * X1) B = f112CosetSMul X2 B
      rw [← f112CosetSMul_mul, hX1fix0]
    rw [hτB] at h
    have hX2C1 : x2' ∈ f112C1 L1 L2 S := by
      have hfix : f112CosetSMul X2 B = B := h.symm
      have h2 := f112_mem_C1_of_fixes_γ₀ L1 L2 S hfix
      simpa [X2, B] using h2
    have hx2B' : x2' ∈ (bigB L1 L2 S).subgroupOf (f112BaseGroup L1 L2 S) := by
      rw [← f112_C1_inf_C2 hF]
      exact ⟨hX2C1, hx2C2⟩
    exact hx2B (Subgroup.mem_subgroupOf.mp hx2B')
  have hstepA : ∀ j, f112CosetSMul (τa ^ (j + 1)) A =
      f112CosetSMul (τa ^ j) (f112CosetSMul τa A) := by
    intro j
    calc f112CosetSMul (τa ^ (j + 1)) A
        = f112CosetSMul (τa ^ j * τa) A := by rw [pow_succ]
      _ = f112CosetSMul (τa ^ j) (f112CosetSMul τa A) :=
        (f112CosetSMul_mul (τa ^ j) τa A).symm
  have hstepB : ∀ j, f112CosetSMul (τa ^ (j + 1)) B =
      f112CosetSMul (τa ^ j) (f112CosetSMul τa B) := by
    intro j
    calc f112CosetSMul (τa ^ (j + 1)) B
        = f112CosetSMul (τa ^ j * τa) B := by rw [pow_succ]
      _ = f112CosetSMul (τa ^ j) (f112CosetSMul τa B) :=
        (f112CosetSMul_mul (τa ^ j) τa B).symm
  have hAne' : ∀ j, f112CosetSMul (τa ^ j) A ≠ f112CosetSMul (τa ^ (j + 1)) A := by
    intro j h
    exact hAne (f112CosetSMul_injective (τa ^ j) (h.trans (hstepA j)))
  have hBne' : ∀ j, f112CosetSMul (τa ^ j) B ≠ f112CosetSMul (τa ^ (j + 1)) B := by
    intro j h
    exact hBne (f112CosetSMul_injective (τa ^ j) (h.trans (hstepB j)))
  have h1 : ∀ j, c'.graph.Adj (f112CosetSMul (τa ^ j) A) (f112CosetSMul (τa ^ j) B) :=
    fun j => (f112CosetSMul_adj (τa ^ j)).mpr hAB
  have h2 : ∀ j, c'.graph.Adj (f112CosetSMul (τa ^ j) B)
      (f112CosetSMul (τa ^ (j + 1)) A) := by
    intro j
    have h := (f112CosetSMul_adj (τa ^ j)).mpr hBτA
    rwa [← hstepA j] at h
  let z : ℕ → f112Verts L1 L2 S := fun i => match min i 9 with
    | 0 => A
    | 1 => B
    | 2 => f112CosetSMul τa A
    | 3 => f112CosetSMul τa B
    | 4 => f112CosetSMul (τa ^ 2) A
    | 5 => f112CosetSMul (τa ^ 2) B
    | 6 => f112CosetSMul (τa ^ 3) A
    | 7 => f112CosetSMul (τa ^ 3) B
    | 8 => f112CosetSMul (τa ^ 4) A
    | _ => f112CosetSMul (τa ^ 4) B
  let ρ : GPath (CosetGeom.graph (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
    (f112C1 L1 L2 S) (f112C2 L1 L2 S)) 9 :=
    { toFun := z
      adj := by
        intro i hi
        have hi8 : i ≤ 8 := by omega
        interval_cases i
        · change c'.graph.Adj A B
          exact hAB
        · change c'.graph.Adj B (f112CosetSMul τa A)
          exact hBτA
        · change c'.graph.Adj (f112CosetSMul τa A) (f112CosetSMul τa B)
          simpa using h1 1
        · change c'.graph.Adj (f112CosetSMul τa B) (f112CosetSMul (τa ^ 2) A)
          simpa using h2 1
        · change c'.graph.Adj (f112CosetSMul (τa ^ 2) A) (f112CosetSMul (τa ^ 2) B)
          exact h1 2
        · change c'.graph.Adj (f112CosetSMul (τa ^ 2) B) (f112CosetSMul (τa ^ 3) A)
          simpa using h2 2
        · change c'.graph.Adj (f112CosetSMul (τa ^ 3) A) (f112CosetSMul (τa ^ 3) B)
          exact h1 3
        · change c'.graph.Adj (f112CosetSMul (τa ^ 3) B) (f112CosetSMul (τa ^ 4) A)
          simpa using h2 3
        · change c'.graph.Adj (f112CosetSMul (τa ^ 4) A) (f112CosetSMul (τa ^ 4) B)
          exact h1 4
      tail := by
        intro i hi
        show z i = z 9
        simp only [z]
        rw [Nat.min_eq_right hi, Nat.min_self] }
  have hρnb : ρ.NoBack := by
    intro i hi
    have hi7 : i ≤ 7 := by omega
    interval_cases i
    · change A ≠ f112CosetSMul τa A
      exact hAne
    · change B ≠ f112CosetSMul τa B
      exact hBne
    · change f112CosetSMul τa A ≠ f112CosetSMul (τa ^ 2) A
      simpa using hAne' 1
    · change f112CosetSMul τa B ≠ f112CosetSMul (τa ^ 2) B
      simpa using hBne' 1
    · change f112CosetSMul (τa ^ 2) A ≠ f112CosetSMul (τa ^ 3) A
      simpa using hAne' 2
    · change f112CosetSMul (τa ^ 2) B ≠ f112CosetSMul (τa ^ 3) B
      simpa using hBne' 2
    · change f112CosetSMul (τa ^ 3) A ≠ f112CosetSMul (τa ^ 4) A
      simpa using hAne' 3
    · change f112CosetSMul (τa ^ 3) B ≠ f112CosetSMul (τa ^ 4) B
      simpa using hBne' 3
  have hρ0true : CosetGeom.vtype (ρ 0) = true := by
    have h : ρ 0 = f112CosetSMul τa⁻¹ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := rfl
    rw [h, f112_vtype_smul]
    exact CosetGeom.vtype_γ₁
  have hρfix : ∀ g : f112Act L1 L2 S,
      (∀ i, i ≤ 9 → f112CosetSMul g (ρ i) = ρ i) →
      (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
    intro g hfix hg2
    have h2G : ∃ k : ℕ,
        orderOf (((g : f112Act L1 L2 S) : ↥(f112BaseGroup L1 L2 S)) : G) = 2 ^ k := by
      obtain ⟨k, hk⟩ := hg2
      exact ⟨k, by simpa only [Subgroup.orderOf_coe] using hk⟩
    have hcore : ∀ i, 1 ≤ i → i ≤ 8 →
        ((g : f112Act L1 L2 S) : G) ∈ f112VertexCore L1 L2 S (ρ i) := by
      intro i hi1 hi8
      have hu : c'.graph.Adj (ρ i) (ρ (i - 1)) := by
        have h := (ρ.adj (i - 1) (by omega)).symm
        rwa [Nat.sub_add_cancel hi1] at h
      have hw : c'.graph.Adj (ρ i) (ρ (i + 1)) := ρ.adj i (by omega)
      have hne : ρ (i - 1) ≠ ρ (i + 1) := by
        have h := hρnb (i - 1) (by omega)
        rwa [show i - 1 + 2 = i + 1 by omega] at h
      exact f112_mem_vertexCore_of_fixes_two_nbrs hF hSB h1v h2v hu hw hne
        (hfix i (by omega)) (hfix (i - 1) (by omega)) (hfix (i + 1) (by omega)) h2G
    have hcore1 : f112VertexCore L1 L2 S (ρ 1) = Q1 L1 L2 S := by
      rw [show ρ 1 = CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S) from rfl]
      exact f112VertexCore_γ₀ L1 L2 S
    have hcore2 : f112VertexCore L1 L2 S (ρ 2) = Q2 L1 L2 S := by
      rw [show ρ 2 = f112CosetSMul τa A from rfl, hτA]
      exact f112VertexCore_γ₁ L1 L2 S
    have hτpow : ∀ j : ℕ, ((τa ^ j : f112Act L1 L2 S) : G) = (x2 * x1) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, pow_succ]
        change (((τa ^ j : f112Act L1 L2 S) : G) *
          ((τa : f112Act L1 L2 S) : G)) = (x2 * x1) ^ j * (x2 * x1)
        rw [ih, show ((τa : ↥(f112BaseGroup L1 L2 S)) : G) = x2 * x1 from hτG]
    have hcore3 : f112VertexCore L1 L2 S (ρ 3) =
        (Q1 L1 L2 S).map (MulAut.conj (x2 * x1)).toMonoidHom := by
      rw [show ρ 3 = f112CosetSMul τa (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) from rfl]
      rw [f112VertexCore_smul_γ₀]
      rw [show ((τa : ↥(f112BaseGroup L1 L2 S)) : G) = x2 * x1 from hτG]
    have hcore4 : f112VertexCore L1 L2 S (ρ 4) =
        (Q2 L1 L2 S).map (MulAut.conj (x2 * x1)).toMonoidHom := by
      rw [show ρ 4 = f112CosetSMul (τa ^ 2) A from rfl]
      rw [show f112CosetSMul (τa ^ 2) A = f112CosetSMul τa
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) by
        rw [pow_two (τa : f112Act L1 L2 S)]
        rw [show f112CosetSMul (τa * τa) A = f112CosetSMul τa (f112CosetSMul τa A) from
          (f112CosetSMul_mul τa τa A).symm, hτA]]
      rw [f112VertexCore_smul_γ₁]
      rw [show ((τa : ↥(f112BaseGroup L1 L2 S)) : G) = x2 * x1 from hτG]
    have hcore5 : f112VertexCore L1 L2 S (ρ 5) =
        (Q1 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 2)).toMonoidHom := by
      rw [show ρ 5 = f112CosetSMul (τa ^ 2) (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) from rfl]
      rw [f112VertexCore_smul_γ₀, hτpow 2]
    have hcore6 : f112VertexCore L1 L2 S (ρ 6) =
        (Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 2)).toMonoidHom := by
      rw [show ρ 6 = f112CosetSMul (τa ^ 3) A from rfl]
      rw [show f112CosetSMul (τa ^ 3) A = f112CosetSMul (τa ^ 2)
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) by
        rw [pow_succ (τa : f112Act L1 L2 S) 2]
        rw [show f112CosetSMul (τa ^ 2 * τa) A =
          f112CosetSMul (τa ^ 2) (f112CosetSMul τa A) from
          (f112CosetSMul_mul (τa ^ 2) τa A).symm, hτA]]
      rw [f112VertexCore_smul_γ₁, hτpow 2]
    have hcore7 : f112VertexCore L1 L2 S (ρ 7) =
        (Q1 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 3)).toMonoidHom := by
      rw [show ρ 7 = f112CosetSMul (τa ^ 3) (CosetGeom.γ₀ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
        (f112C1 L1 L2 S) (f112C2 L1 L2 S)) from rfl]
      rw [f112VertexCore_smul_γ₀, hτpow 3]
    have hcore8 : f112VertexCore L1 L2 S (ρ 8) =
        (Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 3)).toMonoidHom := by
      rw [show ρ 8 = f112CosetSMul (τa ^ 4) A from rfl]
      rw [show f112CosetSMul (τa ^ 4) A = f112CosetSMul (τa ^ 3)
        (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
          (f112C1 L1 L2 S) (f112C2 L1 L2 S)) by
        rw [pow_succ (τa : f112Act L1 L2 S) 3]
        rw [show f112CosetSMul (τa ^ 3 * τa) A =
          f112CosetSMul (τa ^ 3) (f112CosetSMul τa A) from
          (f112CosetSMul_mul (τa ^ 3) τa A).symm, hτA]]
      rw [f112VertexCore_smul_γ₁, hτpow 3]
    have hm1 := hcore 1 (by norm_num) (by norm_num)
    have hm2 := hcore 2 (by norm_num) (by norm_num)
    have hm3 := hcore 3 (by norm_num) (by norm_num)
    have hm4 := hcore 4 (by norm_num) (by norm_num)
    have hm5 := hcore 5 (by norm_num) (by norm_num)
    have hm6 := hcore 6 (by norm_num) (by norm_num)
    have hm7 := hcore 7 (by norm_num) (by norm_num)
    have hm8 := hcore 8 (by norm_num) (by norm_num)
    have hW0 : ((g : f112Act L1 L2 S) : G) ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
      refine ⟨?_, ?_⟩
      · rwa [hcore1] at hm1
      · rwa [hcore2] at hm2
    have hW1 : ((g : f112Act L1 L2 S) : G) ∈
        (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj (x2 * x1)).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (x2 * x1)).injective]
      refine ⟨?_, ?_⟩
      · rwa [hcore3] at hm3
      · rwa [hcore4] at hm4
    have hW2 : ((g : f112Act L1 L2 S) : G) ∈
        (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 2)).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj ((x2 * x1) ^ 2)).injective]
      refine ⟨?_, ?_⟩
      · rwa [hcore5] at hm5
      · rwa [hcore6] at hm6
    have hW3 : ((g : f112Act L1 L2 S) : G) ∈
        (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 3)).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj ((x2 * x1) ^ 3)).injective]
      refine ⟨?_, ?_⟩
      · rwa [hcore7] at hm7
      · rwa [hcore8] at hm8
    have hmemW : ((g : f112Act L1 L2 S) : G) ∈
        (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊓
          (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj (x2 * x1)).toMonoidHom ⊓
          (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 2)).toMonoidHom ⊓
          (Q1 L1 L2 S ⊓ Q2 L1 L2 S).map (MulAut.conj ((x2 * x1) ^ 3)).toMonoidHom :=
      ⟨⟨⟨hW0, hW1⟩, hW2⟩, hW3⟩
    rw [hwin] at hmemW
    have hG1 : ((g : f112Act L1 L2 S) : G) = 1 := Subgroup.mem_bot.mp hmemW
    exact Subtype.ext (by simpa using hG1)
  have htrans : ∀ q' : GPath c'.graph 9, q' ∈ GPath.nbPaths c'.graph (ρ 0) 9 →
      ∃ g : f112Act L1 L2 S, f112CosetSMul g (ρ 0) = ρ 0 ∧ g • ρ = q' := by
    intro q' hq'
    obtain ⟨g, hg0, hgq⟩ :=
      exists_smul_eq_of_stabPath_two c' hc' (j := 4) (e₁ := 2 * (2 * a + 1))
        (e₂ := 2 * a + 1) (m := S.relIndex (bigB L1 L2 S)) hq1 hq2 hmB hB
        (a := ρ 0) (q := ρ) ⟨rfl, hρnb⟩ hq'
        (fun g hfix hg => hρfix g (fun i hi => by
          simpa [f112CosetSMul_eq_smul] using hfix i hi) hg)
    exact ⟨g, by simpa [f112CosetSMul_eq_smul] using hg0, hgq⟩
  have hpath_case : ∀ q : GPath c'.graph 9, q.NoBack →
      CosetGeom.vtype (q 0) = CosetGeom.vtype (ρ 0) →
      ∀ g : f112Act L1 L2 S, (∀ i, i ≤ 9 → f112CosetSMul g (q i) = q i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
    intro q hq hvq g hfixq hg2
    have hq0true : CosetGeom.vtype (q 0) = true := by rw [hvq, hρ0true]
    obtain ⟨a₁, ha₁⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S) (γ := q 0) hq0true
    obtain ⟨b₁, hb₁⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
      (G₁ := f112C1 L1 L2 S) (G₂ := f112C2 L1 L2 S) (γ := ρ 0) hρ0true
    let y : f112Act L1 L2 S := b₁ * a₁⁻¹
    have hy : f112CosetSMul y (q 0) = ρ 0 := by
      calc f112CosetSMul y (q 0)
          = f112CosetSMul y (f112CosetSMul a₁ (CosetGeom.γ₁
              (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S) (f112C1 L1 L2 S)
              (f112C2 L1 L2 S))) := by
            rw [ha₁, f112CosetSMul_eq_smul]
            all_goals rfl
        _ = f112CosetSMul (y * a₁) (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by rw [f112CosetSMul_mul]
        _ = f112CosetSMul b₁ (CosetGeom.γ₁ (f112C1 L1 L2 S ⊔ f112C2 L1 L2 S)
              (f112C1 L1 L2 S) (f112C2 L1 L2 S)) := by
          rw [show y * a₁ = b₁ by simp [y]]
        _ = ρ 0 := by rw [hb₁, f112CosetSMul_eq_smul]
    let qy : GPath c'.graph 9 :=
      q.map (f112CosetSMul y) (fun a b hab => (f112CosetSMul_adj y).mpr hab)
    have hqy0 : qy 0 = ρ 0 := by
      change f112CosetSMul y (q 0) = ρ 0
      exact hy
    have hqynb : qy.NoBack :=
      GPath.NoBack.map_of_injective (f := f112CosetSMul y)
        (fun a b hab => (f112CosetSMul_adj y).mpr hab) (f112CosetSMul_injective y) hq
    have hq' : qy ∈ GPath.nbPaths c'.graph (ρ 0) 9 := ⟨hqy0, hqynb⟩
    obtain ⟨z, -, hzq⟩ := htrans qy hq'
    let u : f112Act L1 L2 S := y⁻¹ * z
    have hu : ∀ i, i ≤ 9 → f112CosetSMul u (ρ i) = q i := by
      intro i hi
      have hz i (hi : i ≤ 9) : f112CosetSMul z (ρ i) = f112CosetSMul y (q i) := by
        have h := congrArg (fun p : GPath c'.graph 9 => p i) hzq
        exact h
      calc f112CosetSMul u (ρ i)
          = f112CosetSMul y⁻¹ (f112CosetSMul z (ρ i)) := by
            rw [show u = y⁻¹ * z from rfl, f112CosetSMul_mul]
        _ = f112CosetSMul y⁻¹ (f112CosetSMul y (q i)) := by rw [hz i hi]
        _ = q i := f112CosetSMul_inv_smul y (q i)
    have hfixρ : ∀ i, i ≤ 9 → f112CosetSMul (u⁻¹ * g * u) (ρ i) = ρ i := by
      intro i hi
      have hpi : q i = f112CosetSMul u (ρ i) := (hu i hi).symm
      calc f112CosetSMul (u⁻¹ * g * u) (ρ i)
          = f112CosetSMul u⁻¹ (f112CosetSMul g (f112CosetSMul u (ρ i))) := by
            rw [← f112CosetSMul_mul, ← f112CosetSMul_mul]
        _ = f112CosetSMul u⁻¹ (f112CosetSMul g (q i)) := by rw [← hpi]
        _ = f112CosetSMul u⁻¹ (q i) := by rw [hfixq i hi]
        _ = ρ i := by rw [hpi, f112CosetSMul_inv_smul]
    have hord : ∃ k : ℕ, orderOf (u⁻¹ * g * u) = 2 ^ k := by
      obtain ⟨k, hk⟩ := hg2
      refine ⟨k, ?_⟩
      have hconj : u⁻¹ * g * u = (MulAut.conj u⁻¹) g := by
        rw [MulAut.conj_apply, inv_inv]
      rw [hconj, (MulAut.conj u⁻¹).orderOf_eq, hk]
    have h1 := hρfix (u⁻¹ * g * u) hfixρ hord
    calc g = u * (u⁻¹ * g * u) * u⁻¹ := by group
      _ = 1 := by rw [h1]; simp
  have hfix112 : ∀ p : GPath c'.graph 9, p.NoBack → ∀ g : f112Act L1 L2 S,
      (∀ i, i ≤ 9 → f112CosetSMul g (p i) = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
    intro p hp g hfix hg2
    by_cases hv : CosetGeom.vtype (p 0) = CosetGeom.vtype (ρ 0)
    · exact hpath_case p hp hv g hfix hg2
    · have hp0 : CosetGeom.vtype (p 0) = false := by
        cases h : CosetGeom.vtype (p 0)
        · rfl
        · exfalso
          apply hv
          rw [h, hρ0true]
      have hvrev : CosetGeom.vtype (p.rev 0) = CosetGeom.vtype (ρ 0) := by
        rw [GPath.rev_apply p (by norm_num), show 9 - 0 = 9 by norm_num]
        rw [vtype_odd_path p ⟨4, by norm_num⟩, hp0, hρ0true]
        rfl
      have hfixrev : ∀ i, i ≤ 9 → f112CosetSMul g (p.rev i) = p.rev i := by
        intro i hi
        rw [GPath.rev_apply p hi]
        exact hfix (9 - i) (by omega)
      exact hpath_case p.rev hp.rev hvrev g hfixrev hg2
  exact hfix112

theorem str83PathFix_of_sevenPath (hO : Str83Orders)
    (h : Str83SevenPath) : Str83PathFix := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2 Y _ _ c hc p hp g hfix hg2
  obtain ⟨hm, hQ1, hQ2, hS⟩ := hO G L1 L2 S a hF ha hSz hBig hL2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    str83_bigB_le_normalizer hF.1 ha hSz hm
  have hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) =
      2 ^ (2 * (2 * a + 1)) + 1 := by
    have hrel : (borelOf L1 S).relIndex L1 = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      have h' := index_borelOf_of_sz ha hF.1.h1.sylow (Classical.choice hSz)
      simpa [Subgroup.relIndex] using h'
    rw [F112W.relIndex_sup_eq_relIndex_inf (N := L1) (B := bigB L1 L2 S)
      ((F1.bigB_le_normalizer_left hR).1), F1.inf_bigB_eq_borelOf hR, hrel, ← pow_mul]
    congr 1
    ring
  have hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) =
      2 ^ (2 * a + 1) + 1 := by
    have hrel : (borelOf L2 S).relIndex L2 = 2 ^ (2 * a + 1) + 1 := by
      have h' := CFSG.Quasithin.F112R.St84.index_borelOf_of_psl2 (f := 2 * a + 1)
        (by omega) hF.1.h2.sylow hm
      simpa [Subgroup.relIndex] using h'
    have hinf : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
      have h := F1.inf_bigB_eq_borelOf hR.symm
      rwa [bigB_comm] at h
    rw [F112W.relIndex_sup_eq_relIndex_inf (N := L2) (B := bigB L1 L2 S)
      ((F1.bigB_le_normalizer_left hR).2), hinf]
    exact hrel
  have hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ (2 * (2 * a + 1)) :=
    f112_qOne hF hv1
  have hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ (2 * a + 1) :=
    f112_qTwo hF hv2
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF)
      le_sup_right le_sup_right
  have hmB : Odd (S.relIndex (bigB L1 L2 S)) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hSylB
  let c' := f112Completion L1 L2 S
  have hc' : c'.IsFaithful := f112Completion_isFaithful L1 L2 S
  have hB : Nat.card ↥(c'.φ1.range ⊓ c'.φ2.range) =
      ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ 4 *
        S.relIndex (bigB L1 L2 S) := by
    change Nat.card ↥((f112Completion L1 L2 S).φ1.range ⊓
      (f112Completion L1 L2 S).φ2.range) = _
    have hpow : (2 ^ (2 * (2 * a + 1)) * 2 ^ (2 * a + 1)) ^ 4 =
        (2 ^ (2 * a + 1)) ^ 12 := by
      rw [← pow_add, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hinf : S ⊓ bigB L1 L2 S = S := by
      show S ⊓ (borelOf L1 S ⊔ borelOf L2 S ⊔ S) = S
      exact inf_eq_left.mpr (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S)
    have h := Subgroup.relIndex_mul_card (H := S) (K := bigB L1 L2 S)
    rw [hinf] at h
    rw [f112_card_edge hF, hq1, hq2, hpow]
    calc Nat.card ↥(bigB L1 L2 S) =
          S.relIndex (bigB L1 L2 S) * Nat.card ↥S := h.symm
      _ = S.relIndex (bigB L1 L2 S) * (2 ^ (2 * a + 1)) ^ 12 := by rw [hS]
      _ = (2 ^ (2 * a + 1)) ^ 12 * S.relIndex (bigB L1 L2 S) := by rw [mul_comm]
  have hfix112 : ∀ p : GPath (f112Completion L1 L2 S).graph 9, p.NoBack →
      ∀ g : f112Act L1 L2 S,
        (∀ i, i ≤ 9 → f112CosetSMul g (p i) = p i) →
        (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 :=
    f112_pathFix_of_sevenPath_data (G := G) hF ha hSz hBig hL2 hm hq1 hq2 hSB hmB hB h
  exact CFSG.Quasithin.RankTwoAmalgam.Completion.pathFix_transfer c (f112Completion L1 L2 S)
    hc (f112Completion_isFaithful L1 L2 S) 9
    (fun p hp g hfix hg => hfix112 p hp g (fun i hi => by
      simpa [f112CosetSMul_eq_smul] using hfix i hi) hg) p hp g hfix hg2

end CFSG.Quasithin.Stroth

end
