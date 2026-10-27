module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCaseD
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSpecialEq

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

theorem exists_isOrthOvergroup_special_of_isOrthType (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) (horth : IsOrthType p (movedGroup B)) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨_, e₀, _, _, he0, _, _, heCB, _⟩ := exists_isOrthOn_root hp hD
  have hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g := by
    obtain ⟨Q₂, hQ₂, hoB₂, -⟩ := exists_isOrthOn_of_isOrthType_movedGroup hp
      hD.split.2.2.1 horth heCB he0 (c := 1) one_ne_zero
    exact ⟨Q₂, hQ₂, fun g hg => hoB₂.isIsom hg⟩
  have hcomp := exists_eq_mul_of_isCyclicRootTriple hp5 hD h4 hr hT hψ
  obtain ⟨Q, hQ, hoH, hBQ⟩ := exists_isOrthOn_of_lemmaTwoSevenData hp hD hcomp
  exact exists_isOrthOvergroup_of_isOrthType_of_isIsom hp hD (fun hp3 => by omega) horth hQ hoH hBQ

private theorem exists_isOrthOvergroup_of_mem_map_ne_of_transposition
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} {ζ : (ZMod p)ˣ}
    (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    (hcomp : ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q₁).Nondegenerate ∧ IsOrthOn p Q₁ H ∧
      (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v)
    {k m : Fin 3} {y : U}
    (hyV : centralizerSpace (reflStab p H h) ⊓
        HardMathSupport.Kantor79.commutatorSpace B ≤ Submodule.span (ZMod p) {y})
    (hy : y ∈ Submodule.span (ZMod p) {(f m : U)})
    (hk : (f k : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) :
    ∃ K, IsOrthOvergroup p G H K := by
  have hperm_gmmn : permMap p f (Equiv.swap k m) ∈ gmmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  have hperm_moved : permMap p f (Equiv.swap k m) ∈ movedGroup B := h1 hperm_gmmn
  obtain ⟨x, hx_eq⟩ := MonoidHom.mem_range.mp hperm_moved
  let xU : U ≃ₗ[ZMod p] U := x
  have hxB : xU ∈ B := x.2
  have hx_fk : xU (f k) = f m := by
    have h := congrArg (fun (g : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace B) => (g (f k) : U)) hx_eq
    simp only [restrictHom_apply, permMap_apply_basis, Equiv.swap_apply_left] at h
    exact h
  have hxV : centralizerSpace (reflStab p H h) ⊓
      HardMathSupport.Kantor79.commutatorSpace B ≤
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)).map (xU : U →ₗ[ZMod p] U) := by
    refine le_trans hyV ?_
    refine le_trans ((Submodule.span_singleton_le_iff_mem _ _).mpr hy) ?_
    have hmem : xU (f k) ∈
        (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)).map (xU : U →ₗ[ZMod p] U) :=
      Submodule.mem_map_of_mem (f := (xU : U →ₗ[ZMod p] U)) hk
    rw [hx_fk] at hmem
    exact ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
  exact exists_isOrthOvergroup_of_mem_map_ne hp hD hcomp hxB hxV

private theorem false_of_gmmn_smul_on_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B) (hζ : (ζ : ZMod p) * ζ ≠ 1)
    {e : Fin 3 → U} {l : Fin 3}
    {he₁ : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B}
    {he₂ : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B}
    (ha : f.repr ⟨e 1, he₁⟩ l = 0) (hb : f.repr ⟨e 2, he₂⟩ l = 0)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2}) : False := by
  obtain ⟨z, hz, hzv, -⟩ := exists_mem_gmmn_apply_eq_smul f hi ζ l
  obtain ⟨g, hgB, hgz⟩ := exists_mem_forall_apply_eq_of_mem_movedGroup (h1 hz)
  have hspanB : Submodule.span (ZMod p) ({e 1, e 2} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact he₁
    · exact he₂
  refine false_of_mem_smul hp hD hgB hζ ?_
  intro v hv
  have hvB : v ∈ HardMathSupport.Kantor79.commutatorSpace B := hspanB (hcomm ▸ hv)
  have hrepr : f.repr ⟨v, hvB⟩ l = 0 := by
    have hv' : v ∈ Submodule.span (ZMod p) ({e 1, e 2} : Set U) := hcomm ▸ hv
    rw [Submodule.mem_span_pair] at hv'
    obtain ⟨α, β, hαβ⟩ := hv'
    have hsub : (⟨v, hvB⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
        α • ⟨e 1, he₁⟩ + β • ⟨e 2, he₂⟩ := by
      ext
      simpa using hαβ.symm
    rw [hsub, map_add, map_smul, map_smul]
    simp [ha, hb]
  rw [hgz ⟨v, hvB⟩, hzv ⟨v, hvB⟩ hrepr]
  rfl

private theorem false_of_frame_smul_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B) (hζ : (ζ : ZMod p) * ζ ≠ 1)
    {Q₁ : QuadraticForm (ZMod p) U} (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hoH : IsOrthOn p Q₁ H) {l : Fin 3} {c : ZMod p} {i j : Fin 3}
    (hk0 : ∀ k, k ≠ i → k ≠ j → k = 0) (hQw : Q₁ (e j) ≠ 0)
    {he_i : e i ∈ HardMathSupport.Kantor79.commutatorSpace B}
    {he_j : e j ∈ HardMathSupport.Kantor79.commutatorSpace B}
    (hal : (⟨e i, he_i⟩ : HardMathSupport.Kantor79.commutatorSpace B) = c • f l)
    (hb : f.repr ⟨e j, he_j⟩ l = 0) : False := by
  obtain ⟨z, hz, hzv, hzl⟩ := exists_mem_gmmn_apply_eq_smul f hi ζ l
  obtain ⟨g, hgB, hgz⟩ := exists_mem_forall_apply_eq_of_mem_movedGroup (h1 hz)
  have hgi : g (e i) = ((ζ⁻¹ * ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • e i := by
    have hza : z (⟨e i, he_i⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
        ((ζ⁻¹ * ζ⁻¹ : (ZMod p)ˣ) : ZMod p) •
          (⟨e i, he_i⟩ : HardMathSupport.Kantor79.commutatorSpace B) := by
      rw [hal]
      calc z (c • f l) = c • z (f l) := map_smul z c (f l)
        _ = c • (((ζ⁻¹ * ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • f l) := by rw [hzl]
        _ = ((ζ⁻¹ * ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • (c • f l) := by
              rw [smul_smul, smul_smul, mul_comm]
    have h := hgz (⟨e i, he_i⟩ : HardMathSupport.Kantor79.commutatorSpace B)
    rw [hza] at h
    simpa only [Submodule.coe_smul] using h
  have hgj : g (e j) = (ζ : ZMod p) • e j := by
    have h := hgz (⟨e j, he_j⟩ : HardMathSupport.Kantor79.commutatorSpace B)
    rw [hzv (⟨e j, he_j⟩ : HardMathSupport.Kantor79.commutatorSpace B) hb] at h
    simpa only [Submodule.coe_smul] using h
  have hg0 : g (e 0) = e 0 := apply_eq_self_of_isCyclicRootTriple hp hD hr hT hgB
  have he0 := isCyclicRootTriple_root_mem_commutatorSpace hp hT 0
  have heiV := isCyclicRootTriple_root_mem_commutatorSpace hp hT i
  have hejV := isCyclicRootTriple_root_mem_commutatorSpace hp hT j
  have hV : (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H :=
    map_commutatorSpace_eq_of_isCyclicRootTriple hp hD h4 hT (g := g) (fun k => by
      by_cases hki : k = i
      · rw [hki, hgi]; exact Submodule.smul_mem _ _ heiV
      · by_cases hkj : k = j
        · rw [hkj, hgj]; exact Submodule.smul_mem _ _ hejV
        · rw [hk0 k hki hkj, hg0]; exact he0)
  exact false_of_map_commutatorSpace_eq_of_apply_eq_smul hp hD hQ₁ hoH hgB hV hejV hQw hζ hgj

private theorem false_of_le_g2mmn_of_mul_self_ne_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    (h2 : movedGroup B ≤ g2mmn p f i₀ i₁ ζ) (hζ : (ζ : ZMod p) * ζ ≠ 1) : False := by
  obtain ⟨Q₁, hQ₁, hoH, hQe0, hQe, -, -, hrmem, hcomm⟩ :=
    exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  obtain ⟨y, hy0, hyH, hyB⟩ := exists_mem_centralizerSpace_of_lemmaTwoSevenData hp hD
  have he₁ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 1) (by decide)
  have he₂ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 2) (by decide)
  obtain ⟨d₁, d₂, σ₁, σ₂, hK⟩ :=
    exists_isKleinFrame_of_le_g2mmn hp hD h4 hr hT hi h2 hy0 hyH hyB he₁ he₂
  obtain ⟨l, hl₁, hl₂⟩ := exists_fixed_of_diagMap_mul_permMap f hK.mul_self_left
    hK.symm.mul_self_left hK.commute
  have hQe2 : Q₁ (e 2) ≠ 0 := by rw [hQe 2]; exact hQe0
  have hQe1 : Q₁ (e 1) ≠ 0 := by rw [hQe 1]; exact hQe0
  rcases hK.basis_eq_smul hp hl₁ hl₂ with ⟨-, ha, hb⟩ | ⟨⟨c, hc, hal⟩, hb, hy⟩ |
    ⟨⟨c, hc, hbl⟩, ha, hy⟩
  · exact false_of_gmmn_smul_on_reflStab hp hD hi h1 hζ ha hb hcomm
  · exact false_of_frame_smul_root hp hD h4 hr hT hi h1 hζ hQ₁ hoH
      (i := 1) (j := 2) (by decide) hQe2 (he_i := he₁) (he_j := he₂) hal hb
  · exact false_of_frame_smul_root hp hD h4 hr hT hi h1 hζ hQ₁ hoH
      (i := 2) (j := 1) (by decide) hQe1 (he_i := he₂) (he_j := he₁) hbl ha

private theorem exists_isOrthOvergroup_or_false_of_frame_smul (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h) (hp5 : p = 5)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} {ζ : (ZMod p)ˣ} (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    (hcomp : ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q₁).Nondegenerate ∧ IsOrthOn p Q₁ H ∧
      (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v)
    {Q₂ : QuadraticForm (ZMod p) U}
    (hQ₂f : Q₂.comp (HardMathSupport.Kantor79.commutatorSpace B).subtype = basisSumSq f)
    {a b : HardMathSupport.Kantor79.commutatorSpace B} {y : U}
    {hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B}
    {t₁ : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace B}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b ⟨y, hyB⟩)
    (hQab : Q₂ (b : U) = Q₂ (a : U))
    (haV : (a : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h))
    (hyV : centralizerSpace (reflStab p H h) ⊓ HardMathSupport.Kantor79.commutatorSpace B ≤
      Submodule.span (ZMod p) {y})
    {l : Fin 3} (hl₂ : σ₂ l = l) {c : ZMod p} (hc : c ≠ 0) (hal : a = c • f l)
    (hb : f.repr b l = 0) (hy : f.repr ⟨y, hyB⟩ l = 0) :
    ∃ K, IsOrthOvergroup p G H K := by
  rcases hK.eq_smul_or_eq_smul_sub hp hl₂ hb hy with
    ⟨m, -, c', hc', hym⟩ | ⟨i, j, hij, hil, hjl, u, c', hu, hc', hbij⟩
  · have hfl : (f l : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
      have hval : (a : U) = c • (f l : U) := by simpa using congrArg Subtype.val hal
      have hfl' : (f l : U) = c⁻¹ • (a : U) := by
        rw [hval, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hfl']
      exact Submodule.smul_mem _ _ haV
    have hym' : y ∈ Submodule.span (ZMod p) {(f m : U)} := by
      have hym'' : y = c' • (f m : U) := by simpa using congrArg Subtype.val hym
      rw [hym'']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact exists_isOrthOvergroup_of_mem_map_ne_of_transposition hp hD h1 hcomp hyV hym' hfl
  · have hEq : basisSumSq f b = basisSumSq f a := by
      rw [← DFunLike.congr_fun hQ₂f b, ← DFunLike.congr_fun hQ₂f a]
      simpa using hQab
    rw [hbij, hal] at hEq
    exact absurd hEq (basisSumSq_smul_sub_ne hp5 f hij hil hjl hc hu hc')

private theorem exists_isOrthOvergroup_of_le_g2mmn_of_mul_self_eq_one (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    (h2 : movedGroup B ≤ g2mmn p f i₀ i₁ ζ) (hζ : ζ * ζ = 1) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨-, -, -, -, -, -, -, -, hcomm⟩ := exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  obtain ⟨y, hy0, hyH, hyB⟩ := exists_mem_centralizerSpace_of_lemmaTwoSevenData hp hD
  have he₁ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 1) (by decide)
  have he₂ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 2) (by decide)
  obtain ⟨d₁, d₂, σ₁, σ₂, hK⟩ :=
    exists_isKleinFrame_of_le_g2mmn hp hD h4 hr hT hi h2 hy0 hyH hyB he₁ he₂
  obtain ⟨l, hl₁, hl₂⟩ := exists_fixed_of_diagMap_mul_permMap f hK.mul_self_left
    hK.symm.mul_self_left hK.commute
  obtain ⟨Q₂, hQ₂, hQ₂f, hBQ⟩ := exists_isIsom_basisSumSq_of_le_g2mmn hp hD hi hζ h2
  have hcomp := exists_eq_mul_of_isCyclicRootTriple hp5 hD h4 hr hT ⟨Q₂, hQ₂, hBQ⟩
  have hQ : Q₂ (e 2) = Q₂ (e 1) :=
    eq_of_isIsom_of_isCyclicRootTriple hp5 hD h4 hr hT hQ₂ hBQ
  have hyV := centralizerSpace_inf_le_span_of_isCyclicRootTriple hp hD h4 hr hT hy0 hyH hyB
  have he1H : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [hcomm]; exact Submodule.subset_span (by simp)
  have he2H : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [hcomm]; exact Submodule.subset_span (by simp)
  rcases hK.basis_eq_smul hp hl₁ hl₂ with ⟨⟨c, hc, hyl⟩, ha, hb⟩ |
    ⟨⟨c, hc, hal⟩, hb, hy⟩ | ⟨⟨c, hc, hbl⟩, ha, hy⟩
  · obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ l := by
      fin_cases l
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨α, β, hαβ⟩ := hK.exists_eq_add_of_eq_smul hc hyl ha hb hk
    have hfk : (f k : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
      rw [hcomm]
      have hval : (f k : U) = α • e 1 + β • e 2 := by
        simpa using congrArg Subtype.val hαβ
      rw [hval]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hy' : y ∈ Submodule.span (ZMod p) {(f l : U)} := by
      have hyl' : y = c • (f l : U) := by simpa using congrArg Subtype.val hyl
      rw [hyl']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact exists_isOrthOvergroup_of_mem_map_ne_of_transposition hp hD h1 hcomp hyV hy' hfk
  · exact exists_isOrthOvergroup_or_false_of_frame_smul hp hD hp5 h1 hcomp hQ₂f hK hQ
      he1H hyV hl₂ hc hal hb hy
  · exact exists_isOrthOvergroup_or_false_of_frame_smul hp hD hp5 h1 hcomp hQ₂f hK.symm hQ.symm
      he2H hyV hl₁ hc hbl ha hy

private theorem exists_isOrthOvergroup_special_of_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (h1 : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    (h2 : movedGroup B ≤ g2mmn p f i₀ i₁ ζ) : ∃ K, IsOrthOvergroup p G H K := by
  by_cases hζ : ζ * ζ = 1
  · exact exists_isOrthOvergroup_of_le_g2mmn_of_mul_self_eq_one hp hD h4 hp5 hr hT hi h1 h2 hζ
  · refine (false_of_le_g2mmn_of_mul_self_ne_one hp hD h4 hr hT hi h1 h2 fun h' => hζ ?_).elim
    exact Units.ext (by simpa using h')

theorem exists_isOrthOvergroup_special_of_eq_gmmn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hB : movedGroup B = gmmn p f i₀ i₁ ζ) :
    ∃ K, IsOrthOvergroup p G H K :=
  exists_isOrthOvergroup_special_of_le hp hD h4 hp5 hr hT hi hB.ge
    (hB.le.trans (gmmn_le_g2mmn f i₀ i₁ ζ))

theorem exists_isOrthOvergroup_special_of_eq_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hB : movedGroup B = g2mmn p f i₀ i₁ ζ) :
    ∃ K, IsOrthOvergroup p G H K :=
  exists_isOrthOvergroup_special_of_le hp hD h4 hp5 hr hT hi
    ((gmmn_le_g2mmn f i₀ i₁ ζ).trans hB.ge) hB.le

end CFSG.StandardType.ZS

end
