module

public import CFSG.Quasithin.H13.U3E61
public import CFSG.Quasithin.H13.U3Transport6
public import CFSG.Quasithin.H13.U3Lag
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB Module
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Pull

variable {V : Subgroup G} [IsElementaryAbelian 2 V] (Φ : Additive V ≃ₗ[ZMod 2] W6)

noncomputable def pullSub (P : Submodule (ZMod 2) W6) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ V, Φ (Additive.ofMul ⟨g, hg⟩) ∈ P}
  mul_mem' := by
    rintro a b ⟨ha, hPa⟩ ⟨hb, hPb⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    have h : Additive.ofMul (⟨a * b, V.mul_mem ha hb⟩ : V) =
        Additive.ofMul ⟨a, ha⟩ + Additive.ofMul ⟨b, hb⟩ := rfl
    rw [h, map_add]
    exact P.add_mem hPa hPb
  one_mem' := by
    refine ⟨V.one_mem, ?_⟩
    have h : Additive.ofMul (⟨1, V.one_mem⟩ : V) = 0 := rfl
    rw [h, map_zero]
    exact P.zero_mem
  inv_mem' := by
    rintro a ⟨ha, hPa⟩
    refine ⟨V.inv_mem ha, ?_⟩
    have h : Additive.ofMul (⟨a⁻¹, V.inv_mem ha⟩ : V) = -Additive.ofMul ⟨a, ha⟩ := rfl
    rw [h, map_neg]
    exact P.neg_mem hPa

variable {Φ}

theorem mem_pullSub {P : Submodule (ZMod 2) W6} {g : G} :
    g ∈ pullSub Φ P ↔ ∃ hg : g ∈ V, Φ (Additive.ofMul ⟨g, hg⟩) ∈ P :=
  Iff.rfl

theorem pullSub_le (P : Submodule (ZMod 2) W6) : pullSub Φ P ≤ V := fun _ ⟨hg, _⟩ => hg

theorem pullSub_mono {P Q : Submodule (ZMod 2) W6} (h : P ≤ Q) : pullSub Φ P ≤ pullSub Φ Q :=
  fun _ ⟨hg, hP⟩ => ⟨hg, h hP⟩

theorem card_pullSub (P : Submodule (ZMod 2) W6) : Nat.card (pullSub Φ P) = Nat.card P :=
  Nat.card_congr
    { toFun := fun g => ⟨Φ (Additive.ofMul ⟨g, g.2.1⟩), g.2.2⟩
      invFun := fun x => ⟨((Additive.toMul (Φ.symm x) : V) : G), (Additive.toMul (Φ.symm x)).2,
        by
          have h : Additive.ofMul (⟨((Additive.toMul (Φ.symm x) : V) : G),
              (Additive.toMul (Φ.symm x)).2⟩ : V) = Φ.symm x := rfl
          rw [h, LinearEquiv.apply_symm_apply]
          exact x.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp
      right_inv := fun x => by
        apply Subtype.ext
        change Φ (Additive.ofMul (Additive.toMul (Φ.symm (x : W6)))) = x
        rw [ofMul_toMul, LinearEquiv.apply_symm_apply] }

theorem pullSub_map_subOf {F : Subgroup G} (hFV : F ≤ V) :
    pullSub Φ ((subOf V F).map (Φ : Additive V →ₗ[ZMod 2] W6)) = F := by
  ext g
  rw [mem_pullSub]
  constructor
  · rintro ⟨hg, hP⟩
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hP
    exact mem_subOf.1 hP
  · intro hgF
    refine ⟨hFV hgF, ?_⟩
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    exact mem_subOf.2 hgF

theorem phi_conj {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {x : G} (hx : x ∈ V) :
    Φ (Additive.ofMul ⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn x).1 hx⟩) =
      glLin k (Φ (Additive.ofMul ⟨x, hx⟩)) := by
  rw [← hk, linConj_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem pullSub_map_glLin {n : G} (hn : n ∈ normalizer (V : Set G))
    {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    (P : Submodule (ZMod 2) W6) :
    pullSub Φ (P.map (glLin k : W6 →ₗ[ZMod 2] W6)) = CFSG.conjugate (pullSub Φ P) n⁻¹ := by
  have hact : ∀ (x : G) (hx : x ∈ V), Φ (Additive.ofMul ⟨n * x * n⁻¹,
      (mem_normalizer_iff.1 hn x).1 hx⟩) = glLin k (Φ (Additive.ofMul ⟨x, hx⟩)) := by
    intro x hx
    rw [← hk, linConj_apply, LinearEquiv.symm_apply_apply]
    rfl
  ext g
  rw [mem_conjugate_iff', inv_inv, mem_pullSub, mem_pullSub]
  constructor
  · rintro ⟨hg, hP⟩
    obtain ⟨y, hy, hyg⟩ := Submodule.mem_map.1 hP
    have hgV' : n⁻¹ * g * n ∈ V := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hn) g).1 hg
      rwa [inv_inv] at h1
    refine ⟨hgV', ?_⟩
    have h2 := hact _ hgV'
    have h3 : (⟨n * (n⁻¹ * g * n) * n⁻¹, (mem_normalizer_iff.1 hn _).1 hgV'⟩ : V) = ⟨g, hg⟩ :=
      Subtype.ext (by group)
    rw [h3] at h2
    rw [LinearEquiv.coe_coe] at hyg
    have h4 : y = Φ (Additive.ofMul ⟨n⁻¹ * g * n, hgV'⟩) :=
      (glLin k).injective (by rw [hyg, h2])
    rw [← h4]
    exact hy
  · rintro ⟨hgV', hP⟩
    have hg : g ∈ V := by
      have h1 := (mem_normalizer_iff.1 hn _).1 hgV'
      rwa [show n * (n⁻¹ * g * n) * n⁻¹ = g by group] at h1
    refine ⟨hg, Submodule.mem_map.2 ⟨_, hP, ?_⟩⟩
    rw [LinearEquiv.coe_coe, ← hact _ hgV']
    congr 2
    exact Subtype.ext (by group)

end Pull

section Adapted

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂]
  [Module (ZMod 2) V₂] [AddCommGroup V₃] [Module (ZMod 2) V₃]

theorem linConj_trans (Φ : V₁ ≃ₗ[ZMod 2] V₂) (Ψ : V₂ ≃ₗ[ZMod 2] V₃) (g : V₁ ≃ₗ[ZMod 2] V₁) :
    linConj (Φ.trans Ψ) g = linConj Ψ (linConj Φ g) := by
  ext x
  rw [linConj_apply, linConj_apply, linConj_apply]
  rfl

end Adapted

theorem linConj_glLin (k : GL (Fin 6) (ZMod 2)) (h : W6 ≃ₗ[ZMod 2] W6) :
    linConj (glLin k) h = glLin k * h * (glLin k)⁻¹ := by
  ext x
  rw [linConj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rfl

theorem u3_six_module_transport_adapted
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G}
    {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z) :
    ∃ Φ : Additive V ≃ₗ[ZMod 2] W6,
      (∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      (∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      (∀ n : normalizer (V : Set G), ∃ k ∈ N6,
        linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) ∧
      ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Φ₀, hL, hLs, hN⟩ := u3_six_module_transport h1332 hH hU3 hF
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1
  set τ : normalizer (V : Set G) →* GL (Fin 6) (ZMod 2) :=
    glLin.symm.toMonoidHom.comp
      ((linConj Φ₀).toMonoidHom.comp (u3ConjLin V (normalizer (V : Set G)) le_rfl)) with hτ
  have hτN : ∀ n, τ n ∈ N6 := fun n => by
    obtain ⟨k, hk, hkn⟩ := hN n
    simp only [hτ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hkn,
      MulEquiv.symm_apply_apply]
    exact hk
  have hτ' : ∀ n, linConj Φ₀ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin (τ n) :=
    fun n => by
      simp only [hτ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.apply_symm_apply]
  set T₀ := (T.subgroupOf (normalizer (V : Set G))).map τ with hT₀
  have hT₀N : T₀ ≤ N6 := by
    rintro _ ⟨t, -, rfl⟩
    exact hτN t
  have hT₀2 : IsPGroup 2 T₀ :=
    ((hH.sylow.1.comap_subtype (K := normalizer (V : Set G))).map τ)
  obtain ⟨k, hk, hkT⟩ := exists_conj_le_S0 hT₀N hT₀2
  have hkJ : ∀ j ∈ J6, k⁻¹ * j * k ∈ J6 := by
    intro j hj
    have hk' : k⁻¹ ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
      rw [normalizer_J6_eq]
      exact inv_mem hk
    have h1 := (mem_normalizer_iff.1 hk' j).1 hj
    rwa [inv_inv] at h1
  have hkJ' : ∀ j ∈ J6, k * j * k⁻¹ ∈ J6 := by
    intro j hj
    have hk' : k ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
      rw [normalizer_J6_eq]
      exact hk
    exact (mem_normalizer_iff.1 hk' j).1 hj
  refine ⟨Φ₀.trans (glLin k⁻¹), ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨j, hj, hjl⟩ := hL l hl
    refine ⟨k⁻¹ * j * k, hkJ j hj, ?_⟩
    rw [linConj_trans, hjl, linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  · intro j hj
    obtain ⟨l, hl, hjl⟩ := hLs _ (hkJ' j hj)
    refine ⟨l, hl, ?_⟩
    rw [linConj_trans, hjl, linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
    congr 1
    group
  · intro n
    refine ⟨k⁻¹ * τ n * k, mul_mem (mul_mem (inv_mem hk) (hτN n)) hk, ?_⟩
    rw [linConj_trans, hτ', linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  · intro t ht
    refine ⟨k⁻¹ * τ ⟨t, hTV ht⟩ * k, hkT _ ⟨⟨t, hTV ht⟩, ht, rfl⟩, ?_⟩
    rw [linConj_trans, hτ', linConj_glLin, ← map_inv, ← map_mul, ← map_mul, inv_inv]

@[expose] def U3NondegLineCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G) [IsElementaryAbelian 2 V],
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ b : LinearMap.BilinForm (ZMod 2) (Additive V), b.Nondegenerate → b.IsAlt →
      (∀ (n : normalizer (V : Set G)) (x y : Additive V),
        b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) →
      ∀ (u v : G) (hu : u ∈ V) (hv : v ∈ V),
        b (Additive.ofMul ⟨u, hu⟩) (Additive.ofMul ⟨v, hv⟩) ≠ 0 →
        centralizer ({u, v} : Set G) ≤ normalizer (L : Set G)

@[expose] def U3V3Centralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ V₂ V₃ : Subgroup G, V ⊓ centralizer (T : Set G) ≤ V₂ → V₂ ≤ V₃ → V₃ ≤ V →
      T ≤ normalizer (V₂ : Set G) → T ≤ normalizer (V₃ : Set G) → Nat.card V₂ = 4 →
        Nat.card V₃ = 8 → centralizer (V₃ : Set G) ≤ normalizer (V : Set G)

omit [Group G] in
theorem mem_normalizer_of_conjugate_eq {G : Type} [Group G] {X : Subgroup G} {g : G}
    (h : CFSG.conjugate X g = X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff', h]

theorem s0c_fix_fifteen : ∀ e ∈ s0c, vapp e 15 = 15 := by
  decide +kernel

theorem u3_codim_three_of_claims
    (h1332 : Stmt13_3_2) (h311 : Theorem311Stmt)
    (h612 : ASInputs.AS_E_6_12) (hA : U3NondegLineCentralizer) (hB : U3V3Centralizer) :
    U3CodimThreeCentralizerControl := by
  intro G _ _ T L V z hH hU3 hF F hFV hidx
  classical
  have : IsElementaryAbelian 2 V := hF.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1
  have hVz : V ⊓ centralizer (T : Set G) = zpowers z := hF.2.2.2.2.2.2.2.2.2.2.2.1
  set M := normalizer (L : Set G) with hM
  obtain ⟨-, -, hTIM, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  have hFcard : 8 ≤ Nat.card F := by
    have h1 := card_mul_relIndex hFV
    rw [hV64] at h1
    nlinarith
  have hF1 : F ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hFcard
    norm_num at hFcard
  have hTIF : ∀ c ∈ M, c ∈ centralizer (F : Set G) → c ∈ normalizer (V : Set G) := by
    intro c hcM hc
    rcases hTIM c hcM with h | h
    · rw [mem_normalizer_iff]
      intro x
      rw [← mem_conjugate_iff', h]
    · exfalso
      apply hF1
      rw [eq_bot_iff, ← h]
      intro f hf
      refine ⟨hFV hf, mem_conjugate_iff'.2 ?_⟩
      rw [← (mem_centralizer_iff.1 hc) f hf, mul_inv_cancel_right]
      exact hFV hf
  obtain ⟨Φ, -, hΦLs, hΦN, hΦT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  set P := (subOf V F).map (Φ : Additive V →ₗ[ZMod 2] W6) with hP
  have hFP : pullSub Φ P = F := pullSub_map_subOf hFV
  have hPcard : Nat.card P = Nat.card F := by rw [← card_pullSub (Φ := Φ) P, hFP]
  have hmemP : ∀ x ∈ P, ∃ (g : G) (hg : g ∈ V), g ∈ F ∧ x = Φ (Additive.ofMul ⟨g, hg⟩) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨_, (Additive.toMul y).2, mem_subOf.1 hy, rfl⟩
  by_cases hti : IsTI P
  ·
    have hP8 : Nat.card P = 8 := le_antisymm (card_le_eight_of_isTI hti) (hPcard ▸ hFcard)
    obtain ⟨m, hm, hPm⟩ := exists_hasMask_lag hti hP8
    rcases hm with hm | hm
    ·
      obtain ⟨j, hj, hPj⟩ := exists_eq_map_V3sub hPm hm
      obtain ⟨l, hl, hlj⟩ := hΦLs j hj
      have hFl : F = CFSG.conjugate (pullSub Φ V3sub) l⁻¹ := by
        rw [← hFP, hPj, pullSub_map_glLin _ hlj]
      have hTinv : ∀ Q : Submodule (ZMod 2) W6,
          (∀ s ∈ S0, Q.map (glLin s : W6 →ₗ[ZMod 2] W6) = Q) →
            T ≤ normalizer (pullSub Φ Q : Set G) := by
        intro Q hQ t ht
        obtain ⟨s, hs, hst⟩ := hΦT t ht
        have h1 := pullSub_map_glLin (hTV ht) hst Q
        rw [hQ s hs] at h1
        exact (inv_mem_iff).1 (mem_normalizer_of_conjugate_eq h1.symm)
      have hz15 : z ∈ pullSub Φ V2sub := by
        set x15 := Φ.symm (vecOf 15)
        set g15 : G := ((Additive.toMul x15 : V) : G)
        have hg15V : g15 ∈ V := (Additive.toMul x15).2
        have hg15 : Φ (Additive.ofMul ⟨g15, hg15V⟩) = vecOf 15 := by
          change Φ (Additive.ofMul (Additive.toMul x15)) = vecOf 15
          rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
        have hg15C : g15 ∈ V ⊓ centralizer (T : Set G) := by
          refine ⟨hg15V, mem_centralizer_iff.2 fun t ht => ?_⟩
          obtain ⟨s, hs, hst⟩ := hΦT t ht
          obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
          have h2 : Φ (Additive.ofMul ⟨t * g15 * t⁻¹,
              (mem_normalizer_iff.1 (hTV ht) g15).1 hg15V⟩) = vecOf 15 := by
            rw [phi_conj (hTV ht) hst hg15V, hg15, glLin_apply, coe_s0GL hi, colMat_mulVec_vecOf,
              s0c_fix_fifteen _ (by
                rw [s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; exact hi)]
                exact List.getElem_mem _)]
          have h3 : (⟨t * g15 * t⁻¹, (mem_normalizer_iff.1 (hTV ht) g15).1 hg15V⟩ : V) =
              ⟨g15, hg15V⟩ := by
            apply Additive.ofMul.injective
            apply Φ.injective
            rw [h2, hg15]
          have h4 : t * g15 * t⁻¹ = g15 := congrArg Subtype.val h3
          calc t * g15 = t * g15 * t⁻¹ * t := by group
            _ = g15 * t := by rw [h4]
        rw [hVz] at hg15C
        have hg151 : g15 ≠ 1 := by
          intro h
          have : Additive.ofMul (⟨g15, hg15V⟩ : V) = 0 := by
            change Additive.ofMul (⟨g15, hg15V⟩ : V) = Additive.ofMul 1
            congr 1
            exact Subtype.ext h
          rw [this, map_zero] at hg15
          exact absurd hg15.symm (by
            intro h'
            have := vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
              (h'.trans vecOf_zero.symm)
            norm_num at this)
        have hz2 : orderOf z = 2 := hF.2.2.2.2.2.2.2.2.2.2.2.2
        have hgz : g15 = z := by
          rw [mem_zpowers_iff_mem_range_orderOf, hz2, Finset.mem_image] at hg15C
          obtain ⟨k, hk, hkz⟩ := hg15C
          rw [Finset.mem_range] at hk
          interval_cases k
          · rw [pow_zero] at hkz
            exact absurd hkz.symm hg151
          · rw [pow_one] at hkz
            exact hkz.symm
        rw [← hgz]
        exact ⟨hg15V, by rw [hg15]; exact vecOf_fifteen_mem_V2sub⟩
      have hV1 : V ⊓ centralizer (T : Set G) ≤ pullSub Φ V2sub := by
        rw [hVz, zpowers_le]
        exact hz15
      have hCV3 := hB G T L V z hH hU3 hF (pullSub Φ V2sub) (pullSub Φ V3sub) hV1
        (pullSub_mono V2sub_le_V3sub) (pullSub_le _)
        (hTinv _ fun s hs => map_V2sub_of_mem_S0 hs) (hTinv _ fun s hs => map_V3sub_of_mem_S0 hs)
        (by rw [card_pullSub, card_V2sub]) (by rw [card_pullSub, card_V3sub])
      intro c hc
      rw [hFl] at hc
      have hlV := hLV hl
      have h1 : l⁻¹ * c * l ∈ centralizer (pullSub Φ V3sub : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        have hx' : l * x * l⁻¹ ∈ CFSG.conjugate (pullSub Φ V3sub) l⁻¹ := by
          rw [mem_conjugate_iff', inv_inv]
          simpa [mul_assoc] using hx
        have h2 := (mem_centralizer_iff.1 hc) _ hx'
        calc x * (l⁻¹ * c * l) = l⁻¹ * ((l * x * l⁻¹) * c) * l := by group
          _ = l⁻¹ * (c * (l * x * l⁻¹)) * l := by rw [h2]
          _ = l⁻¹ * c * l * x := by group
      have h2 := hCV3 h1
      have h3 : l * (l⁻¹ * c * l) * l⁻¹ ∈ normalizer (V : Set G) :=
        mul_mem (mul_mem hlV h2) (inv_mem hlV)
      rwa [show l * (l⁻¹ * c * l) * l⁻¹ = c by group] at h3
    ·
      have hfix : ∀ n : normalizer (V : Set G), (n : G) ∈ centralizer (F : Set G) →
          (n : G) ∈ centralizer (V : Set G) := by
        intro n hn
        obtain ⟨k, hk, hkn⟩ := hΦN n
        have hk1 : k = 1 := by
          refine eq_one_of_fixes_lagY hPm hm hk fun x hx => ?_
          obtain ⟨g, hg, hgF, rfl⟩ := hmemP x hx
          rw [← hkn, linConj_apply, LinearEquiv.symm_apply_apply]
          congr 1
          exact (u3ConjLin_apply_eq_self_iff n _).2 ((mem_centralizer_iff.1 hn) g hgF).symm
        rw [hk1, map_one] at hkn
        have h1 : u3ConjLin V (normalizer (V : Set G)) le_rfl n = 1 :=
          (linConj Φ).injective (by rw [hkn, map_one])
        exact (u3ConjLin_eq_one_iff n).1 h1
      have hCMF : M ⊓ centralizer (F : Set G) = M ⊓ centralizer (V : Set G) := by
        refine le_antisymm (fun m ⟨hmM, hmF⟩ => ⟨hmM, ?_⟩)
          (inf_le_inf_left _ (Subgroup.centralizer_le hFV))
        exact hfix ⟨m, hTIF m hmM hmF⟩ hmF
      by_contra hCF
      have hCFM : ¬ centralizer (F : Set G) ≤ M := fun h => hCF fun c hc => hTIF c (h hc) hc
      obtain ⟨⟨U₁, hFU, hUV, hU1, hCU⟩, -⟩ :=
        h612 G T M V F (u3_E61 h1332 hH hF) hF1 hFV hCMF hCFM
      obtain ⟨k, -, hk⟩ := exists_relIndex_eq_two_pow hUV (n := 6) (by rw [hV64]; norm_num)
      have hk1 : k = 1 := by
        have := hU1
        rw [E3.mQuot, hk, padicValNat.prime_pow] at this
        exact this
      rw [hk1, pow_one] at hk
      exact hCU (u3_hyperplane_centralizer h1332 h311 hH hU3 hF hUV hk)
  ·
    simp only [IsTI, not_forall] at hti
    obtain ⟨x, hx, y, hy, hxy⟩ := hti
    obtain ⟨u, hu, huF, rfl⟩ := hmemP x hx
    obtain ⟨v, hv, hvF, rfl⟩ := hmemP y hy
    set Γ := (u3ConjLin V (normalizer (V : Set G)) le_rfl).range
    have hle : Γ.map (linConj Φ).toMonoidHom ≤ N6L := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      obtain ⟨k, hk, hkn⟩ := hΦN n
      exact ⟨k, hk, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hkn]⟩
    have hprof := qtBinarySixProfile_of_map_linConj Φ b0 Γ (qtBinarySixProfile_of_le_N6L hle)
    have hCuv := hA G T L V z hH hU3 hF _ hprof.2.1 hprof.2.2.1
      (fun n x y => hprof.2.2.2.1 _ ⟨n, rfl⟩ x y) u v hu hv (by
        rw [LinearMap.compl₁₂_apply]
        exact hxy)
    intro c hc
    refine hTIF c (hCuv ?_) hc
    exact Subgroup.centralizer_le (by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact huF
      · exact hvF) hc

end CFSG.Quasithin.H13.U3
