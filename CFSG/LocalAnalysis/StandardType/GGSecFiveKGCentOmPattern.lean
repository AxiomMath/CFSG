module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmFixed
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.Triality

private theorem lv_add_lv_not_both : ∀ a b c d : Fin 4, ∀ s t u v : Bool, a ≠ b → c ≠ d →
    ∑ m, (lv a b s t + lv c d u v) m ^ 2 = 2 → (b ≠ c ∧ b ≠ d) ∨ (a ≠ c ∧ a ≠ d) := by
  decide +kernel

private theorem lv_add_lv_cases : ∀ a b c d : Fin 4, ∀ s t u v : Bool, a ≠ b → c ≠ d →
    ∑ m, (lv a b s t + lv c d u v) m ^ 2 = 2 → b ≠ c → b ≠ d →
      (c = a ∧ u = !s ∧ d ≠ b) ∨ (d = a ∧ v = !s ∧ c ≠ b) := by
  decide +kernel

private theorem sum_sq_lv : ∀ a b : Fin 4, ∀ s t : Bool, a ≠ b → ∑ m, lv a b s t m ^ 2 = 2 := by
  decide +kernel

private theorem ne_of_lv_apply_eq_zero : ∀ a b i : Fin 4, ∀ s t : Bool, a ≠ b →
    lv a b s t i = 0 → a ≠ i ∧ b ≠ i := by
  decide +kernel

private theorem exists_fourth_of_three : ∀ x y z : Fin 4, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, i ≠ x ∧ i ≠ y ∧ i ≠ z ∧ ∀ m, m = x ∨ m = y ∨ m = z ∨ m = i := by
  decide

private theorem tri_dot_check : ∀ e₀ e₁ e₂ e₃ : Bool, ∃ j : Fin 3, ∃ i₀ : Fin 4, ∀ a b : Fin 4,
    ∀ s t : Bool, a ≠ b → a ≠ i₀ → b ≠ i₀ →
      ∑ m, toStdD 4 ((⇑tri)^[j] (fromStd (lv a b s t))) m * boolSign (![e₀, e₁, e₂, e₃] m) =
        0 := by
  decide +kernel

private theorem sum_lv_mul (a b : Fin 4) (s t : Bool) (w : Fin 4 → ℤ) :
    ∑ m, lv a b s t m * w m = boolSign s * w a + boolSign t * w b := by
  simp [lv, Pi.single_apply, add_mul, Finset.sum_add_distrib]

private theorem kgcDiag_eq_zpow_of_cls {K : Type} [Field K] {σ : Sp8 K} {m : Fin 4} {e : Bool}
    {χ : K} (h₁ : kgcDiag σ (kgcIdx m e) = χ) (h₂ : kgcDiag σ (kgcIdx m (!e)) = χ⁻¹)
    (r : Bool) : kgcDiag σ (kgcIdx m r) = χ ^ (boolSign r * boolSign e) := by
  cases e <;> cases r <;> simp_all

private theorem kgcDiag_mul_eq_one_of_mem_centralizer {K : Type} [Field K] [CharP K 2]
    {G : Type*} [Group G] {p : ℕ} {D : Subgroup G} {ψ : Sp8 K →* G} (hψ : Function.Injective ψ)
    (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum 4 K three_le_four),
      ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹)) {a b : Fin 4} (hab : a ≠ b) {s t : Bool}
    (h : ψ ((plusFrame 4 K three_le_four).longRoot hab s t (.ofAdd 1)) ∈
      Subgroup.centralizer (D : Set G)) {σ : Sp8 K} (hσ : σ ∈ kgcLiftSet ψ D) :
    kgcDiag σ (kgcIdx a s) * kgcDiag σ (kgcIdx b t) = 1 := by
  have hσT := (kgcLiftSet_subset_kgcTorusSet three_le_four hψ hDp hlift hσ).1
  obtain ⟨d, hd, hσd⟩ := hσ
  have hc := hψ ((hσd _).symm.trans
    (mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp h d hd)))
  rw [StdPosD.conj_longRoot_of_smul _ hab s t
    (spinAction_vec_eq_kgcDiag_smul three_le_four hσT a s)
    (spinAction_vec_eq_kgcDiag_smul three_le_four hσT b t), mul_one] at hc
  exact Multiplicative.ofAdd.injective
    ((plusFrame 4 K three_le_four).longRoot_injective hab s t hc)

private theorem rootGroup_le_comap_of_kgcDiag {K : Type} [Field K] {G : Type*} [Group G]
    {D : Subgroup G} {ψ : Sp8 K →* G}
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum 4 K three_le_four),
      ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹)) {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4)
    (h : ∀ (a b : Fin 4) (s t : Bool), a ≠ b → toStdD 4 γ = lv a b s t →
      ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx a s) * kgcDiag σ (kgcIdx b t) = 1) :
    (plusDatum 4 K three_le_four).rootGroup γ ≤ (Subgroup.centralizer (D : Set G)).comap ψ := by
  obtain ⟨a, b, hab, s, t, hv, hR⟩ := exists_plusRootGroup_eq (K := K) three_le_four hγ
  intro x hx
  rw [show (plusDatum 4 K three_le_four).rootGroup γ = _ from hR] at hx
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
  exact mem_centralizer_longRoot_of_kgcDiag three_le_four hlift hab s t (h a b s t hab hv)
    (Multiplicative.toAdd c)

theorem exists_iterate_tri_le_comap {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type*}
    [Group G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} {ψ : Sp8 K →* G}
    (hψ : Function.Injective ψ) (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum 4 K three_le_four),
      ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC2' : Set.ncard (kgcTorusSet three_le_four ψ D p) ≤ p)
    (hKC2 : ∃ β ∈ {β | β ∈ rootsD4 ∧ (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ},
      ∃ β' ∈ {β | β ∈ rootsD4 ∧ (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ}, β + β' ∈ rootsD4) :
    ∃ (j : ℕ) (i₀ : Fin 4), ∀ δ ∈ rootsD4, toStdD 4 δ i₀ = 0 →
      (plusDatum 4 K three_le_four).rootGroup ((⇑tri)^[j] δ) ≤
        (Subgroup.centralizer (D : Set G)).comap ψ := by
  have hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum 4 K three_le_four) := fun σ hσ =>
    (kgcLiftSet_subset_kgcTorusSet three_le_four hψ hDp hlift hσ).1
  have hinv : ∀ σ ∈ kgcLiftSet ψ D, ∀ m r,
      kgcDiag σ (kgcIdx m (!r)) = (kgcDiag σ (kgcIdx m r))⁻¹ := fun σ hσ m r =>
    eq_inv_of_mul_eq_one_right (kgcDiag_mul_kgcDiag_not three_le_four (hLT hσ) m r)
  have hsymm : ∀ {m m' : Fin 4} {r r' : Bool}, (∀ σ ∈ kgcLiftSet ψ D,
      kgcDiag σ (kgcIdx m r) * kgcDiag σ (kgcIdx m' r') = 1) →
      ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx m' r') * kgcDiag σ (kgcIdx m r) = 1 :=
    fun h σ hσ => by rw [mul_comm]; exact h σ hσ
  have hfixC : ∀ {m m' : Fin 4} {r r' : Bool}, (∀ σ ∈ kgcLiftSet ψ D,
      kgcDiag σ (kgcIdx m r) * kgcDiag σ (kgcIdx m' r') = 1) →
      KGCFixedIdx three_le_four (kgcLiftSet ψ D) m →
        KGCFixedIdx three_le_four (kgcLiftSet ψ D) m' := fun {m m' r r'} h hm =>
    (kgcFixedIdx_iff three_le_four hLT m' r').2 fun σ hσ => by
      have h1 := h σ hσ
      rwa [(kgcFixedIdx_iff three_le_four hLT m r).1 hm σ hσ, one_mul] at h1
  have hC : ∀ γ ∈ rootsD4, (plusDatum 4 K three_le_four).rootGroup γ ≤
      (Subgroup.centralizer (D : Set G)).comap ψ → ∃ (a b : Fin 4) (s t : Bool), a ≠ b ∧
        toStdD 4 γ = lv a b s t ∧
          ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx a s) * kgcDiag σ (kgcIdx b t) = 1 := by
    intro γ hγ hγD
    obtain ⟨a, b, hab, s, t, hv, hR⟩ := exists_plusRootGroup_eq (K := K) three_le_four hγ
    refine ⟨a, b, s, t, hab, hv, fun σ hσ =>
      kgcDiag_mul_eq_one_of_mem_centralizer hψ hDp hlift hab (hγD ?_) hσ⟩
    rw [show (plusDatum 4 K three_le_four).rootGroup γ = _ from hR]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨β, ⟨hβ, hβD⟩, β', ⟨hβ', hβ'D⟩, hββ'⟩ := hKC2
  obtain ⟨a, b, s, t, hab, hv, hCβ⟩ := hC β hβ hβD
  obtain ⟨c, d, u, v, hcd, hv', hCβ'⟩ := hC β' hβ' hβ'D
  have hsq : ∑ m, (lv a b s t + lv c d u v) m ^ 2 = 2 := by
    obtain ⟨e, f, g, h, hef, hw, -⟩ := exists_eq_fromStd hββ'
    rw [← hv, ← hv', ← toStdD_add, hw]
    exact sum_sq_lv e f g h hef
  obtain ⟨x, y, z, p', q, r, hxy, hyz, hxz, h1, h2⟩ : ∃ (x y z : Fin 4) (p' q r : Bool),
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      (∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx x p') * kgcDiag σ (kgcIdx y q) = 1) ∧
      ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx y (!q)) * kgcDiag σ (kgcIdx z r) = 1 := by
    rcases lv_add_lv_not_both a b c d s t u v hab hcd hsq with ⟨hbc, hbd⟩ | ⟨hac, had⟩
    · rcases lv_add_lv_cases a b c d s t u v hab hcd hsq hbc hbd with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
      · exact ⟨b, _, d, t, s, v, hab.symm, hcd, h.symm, hsymm hCβ, hCβ'⟩
      · exact ⟨b, _, c, t, s, u, hab.symm, hcd.symm, h.symm, hsymm hCβ, hsymm hCβ'⟩
    · have hsq' : ∑ m, (lv b a t s + lv c d u v) m ^ 2 = 2 := by
        rwa [show lv b a t s = lv a b s t from add_comm _ _]
      rcases lv_add_lv_cases b a c d t s u v hab.symm hcd hsq' hac had with
        ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
      · exact ⟨a, _, d, s, t, v, hab, hcd, h.symm, hCβ, hCβ'⟩
      · exact ⟨a, _, c, s, t, u, hab, hcd.symm, h.symm, hCβ, hsymm hCβ'⟩
  obtain ⟨i₀, -, hi₀y, -, hcov⟩ := exists_fourth_of_three x y z hxy hyz hxz
  by_cases hy : KGCFixedIdx three_le_four (kgcLiftSet ψ D) y
  ·
    have hx := hfixC (hsymm h1) hy
    have hz := hfixC h2 hy
    refine ⟨0, i₀, fun δ hδ hδ0 => ?_⟩
    show (plusDatum 4 K three_le_four).rootGroup δ ≤ _
    refine rootGroup_le_comap_of_kgcDiag hlift hδ fun a b s t hab hv σ hσ => ?_
    have hfix : ∀ m, m ≠ i₀ → ∀ r', kgcDiag σ (kgcIdx m r') = 1 := fun m hm r' => by
      refine (kgcFixedIdx_iff three_le_four hLT m r').1 ?_ σ hσ
      rcases hcov m with rfl | rfl | rfl | rfl
      exacts [hx, hy, hz, absurd rfl hm]
    rw [hv] at hδ0
    obtain ⟨ha, hb⟩ := ne_of_lv_apply_eq_zero a b i₀ s t hab hδ0
    rw [hfix a ha, hfix b hb, one_mul]
  have hx : ¬ KGCFixedIdx three_le_four (kgcLiftSet ψ D) x := fun h => hy (hfixC h1 h)
  have hz : ¬ KGCFixedIdx three_le_four (kgcLiftSet ψ D) z := fun h => hy (hfixC (hsymm h2) h)
  have hi : ¬ KGCFixedIdx three_le_four (kgcLiftSet ψ D) i₀ := fun h =>
    not_existsUnique_fixed_index_of_ncard three_le_four hp hψ hDp hlift hKC2'
      ⟨i₀, h, fun m hm => by
        rcases hcov m with rfl | rfl | rfl | rfl
        exacts [absurd hm hx, absurd hm hy, absurd hm hz, rfl]⟩
  obtain ⟨s₀, t₀, h7⟩ := exists_longRoot_centralized_of_ncard three_le_four hp hψ hDp hlift
    hKC2' (Ne.symm hi₀y) hy hi
  have h3 : ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx y s₀) * kgcDiag σ (kgcIdx i₀ t₀) = 1 :=
    fun σ hσ => kgcDiag_mul_eq_one_of_mem_centralizer hψ hDp hlift _ (h7 1) hσ
  have hrel : ∀ {m m' : Fin 4} {r r' : Bool}, (∀ σ ∈ kgcLiftSet ψ D,
      kgcDiag σ (kgcIdx m r) * kgcDiag σ (kgcIdx m' r') = 1) →
      ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx m' r') = kgcDiag σ (kgcIdx m (!r)) :=
    fun h σ hσ => by rw [hinv σ hσ]; exact eq_inv_of_mul_eq_one_right (h σ hσ)
  have hcls : ∀ m, ∃ e, ∀ σ ∈ kgcLiftSet ψ D,
      kgcDiag σ (kgcIdx m e) = kgcDiag σ (kgcIdx y q) := by
    intro m
    rcases hcov m with rfl | rfl | rfl | rfl
    · exact ⟨!p', fun σ hσ => (hrel h1 σ hσ).symm⟩
    · exact ⟨q, fun _ _ => rfl⟩
    · exact ⟨r, fun σ hσ => by rw [hrel h2 σ hσ, Bool.not_not]⟩
    · by_cases hs : s₀ = q
      · refine ⟨!t₀, fun σ hσ => ?_⟩
        rw [hinv σ hσ, hrel h3 σ hσ, hs, ← hinv σ hσ, Bool.not_not]
      · refine ⟨t₀, fun σ hσ => ?_⟩
        rw [hrel h3 σ hσ, show (!s₀) = q by revert hs; cases s₀ <;> cases q <;> simp]
  choose ε hε using hcls
  have hrep : ∀ σ ∈ kgcLiftSet ψ D, ∀ m r, kgcDiag σ (kgcIdx m r) =
      kgcDiag σ (kgcIdx y q) ^ (boolSign r * boolSign (ε m)) := fun σ hσ m =>
    kgcDiag_eq_zpow_of_cls (hε m σ hσ) (by rw [hinv σ hσ, hε m σ hσ])
  obtain ⟨j, i₁, hj⟩ := tri_dot_check (ε 0) (ε 1) (ε 2) (ε 3)
  have hε4 : ![ε 0, ε 1, ε 2, ε 3] = ε := by
    funext m
    fin_cases m <;> rfl
  rw [hε4] at hj
  refine ⟨j, i₁, fun δ hδ hδ0 => rootGroup_le_comap_of_kgcDiag hlift
    (Set.MapsTo.iterate (fun _ => tri_mem_roots) j hδ) fun a b s t _ hv σ hσ => ?_⟩
  obtain ⟨a₁, b₁, s₁, t₁, hab₁, hv₁, rfl⟩ := exists_eq_fromStd hδ
  rw [hv₁] at hδ0
  obtain ⟨ha₁, hb₁⟩ := ne_of_lv_apply_eq_zero a₁ b₁ i₁ s₁ t₁ hab₁ hδ0
  have hdot := hj a₁ b₁ s₁ t₁ hab₁ ha₁ hb₁
  rw [hv, sum_lv_mul] at hdot
  have hχ : kgcDiag σ (kgcIdx y q) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (kgcDiag_mul_kgcDiag_not three_le_four (hLT hσ) y q)
  rw [hrep σ hσ a s, hrep σ hσ b t, ← zpow_add₀ hχ, hdot, zpow_zero]

end CFSG.StandardType.KGCentOm

end
