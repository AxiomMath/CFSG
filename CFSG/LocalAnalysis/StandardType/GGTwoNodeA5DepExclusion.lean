module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggDepA_h2_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h2
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hp_ge_2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp_eq_2 : p = 2 := by omega
  exact hp2 hp_eq_2

private lemma ggDepA_h_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Type} {h : ι → V}
    {α : ι → Module.Dual (ZMod p) V} (hdiag : ∀ i, α i (h i) = 2) (i : ι) : h i ≠ 0 := by
  intro h0
  have h_hi : α i (h i) = 2 := hdiag i
  rw [h0, map_zero] at h_hi
  exact ggDepA_h2_ne_zero hp2 h_hi.symm

private lemma ggDepA_r_mem_span_of_commute {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {r s : V ≃ₗ[ZMod p] V} {c : V}
    {β : Module.Dual (ZMod p) V} (hs : ∀ v, s v = v - β v • c) (hβc : β c = 2)
    (hcomm : s * r = r * s) : ∃ lam : ZMod p, r c = lam • c := by
  have h2unit : (2 : ZMod p) ≠ 0 := ggDepA_h2_ne_zero hp2
  have h_sc : s c = -c := by
    rw [hs c, hβc, two_smul]
    abel
  have h_eq : s (r c) = r (s c) := by
    have h := congrArg (fun f => f c) hcomm
    simpa only [LinearEquiv.mul_apply] using h
  have h2smul : (2 : ZMod p) • (r c) = β (r c) • c := by
    have h1 : s (r c) = r c - β (r c) • c := hs (r c)
    have h2 : s (r c) = -(r c) := by
      rw [h_eq, h_sc]
      simp
    rw [h2] at h1
    rw [two_smul]
    calc r c + r c = r c + (-(-r c)) := by simp
      _ = r c + (-(r c - β (r c) • c)) := by rw [h1]
      _ = β (r c) • c := by abel
  refine ⟨β (r c) * (2 : ZMod p)⁻¹, ?_⟩
  have h_inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2unit
  have h := congrArg (fun v => (2 : ZMod p)⁻¹ • v) h2smul
  simpa [smul_smul, h_inv, mul_comm, mul_left_comm, mul_assoc] using h

private lemma ggDepA_h_mem_span_of_ne_zero {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {c hk : V} {αk : Module.Dual (ZMod p) V}
    {lam : ZMod p} (hα : αk c ≠ 0) (h_eq : αk c • hk = (1 - lam) • c)
    (hk_ne_zero : hk ≠ 0) : hk ∈ Submodule.span (ZMod p) {c} := by
  by_cases hlam : 1 - lam = 0
  · rw [hlam, zero_smul] at h_eq
    rcases smul_eq_zero.mp h_eq with hα0 | hk0
    · exact absurd hα0 hα
    · exact absurd hk0 hk_ne_zero
  · refine Submodule.mem_span_singleton.mpr ?_
    use (αk c)⁻¹ * (1 - lam)
    have h1 := congrArg (fun v => (αk c)⁻¹ • v) h_eq
    simpa [smul_smul, inv_mul_cancel₀ hα] using h1.symm

theorem ggDep_mem_span_of_commute {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Type} {h : ι → V}
    {α : ι → Module.Dual (ZMod p) V} {x : V}
    (hfix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x})
    (hdiag : ∀ i, α i (h i) = 2) (hnbr : ∀ i, ∃ j, j ≠ i ∧ α j (h i) ≠ 0)
    (hh : ∀ j k : ι, j ≠ k → h j ∉ Submodule.span (ZMod p) {h k})
    (r : ι → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    {s : V ≃ₗ[ZMod p] V} {c : V} {β : Module.Dual (ZMod p) V} (hs : ∀ v, s v = v - β v • c)
    (hβc : β c = 2) (hcomm : ∀ i, s * r i = r i * s) : c ∈ Submodule.span (ZMod p) {x} := by
  apply hfix c
  intro i
  by_contra hαic
  obtain ⟨lami, h_lam_i⟩ := ggDepA_r_mem_span_of_commute hp2 hs hβc (hcomm i)
  have h_ric : r i c = c - α i c • h i := hr i c
  have h_eq2 : α i c • h i = (1 - lami) • c := by
    have h1 : c - α i c • h i = lami • c := by rw [← h_ric, h_lam_i]
    have h2 : α i c • h i = c - lami • c := by
      calc α i c • h i = c - (c - α i c • h i) := by abel
        _ = c - lami • c := by rw [h1]
    rw [h2, sub_smul, one_smul]
  have h_hi_ne_zero : h i ≠ 0 := ggDepA_h_ne_zero hp2 hdiag i
  have h_hi_span : h i ∈ Submodule.span (ZMod p) {c} :=
    ggDepA_h_mem_span_of_ne_zero hαic h_eq2 h_hi_ne_zero
  have h_c_span_hi : c ∈ Submodule.span (ZMod p) {h i} := by
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h_hi_span
    have hμ_ne_zero : μ ≠ 0 := by
      intro hμ0
      rw [hμ0, zero_smul] at hμ
      exact h_hi_ne_zero hμ.symm
    have hc : c = μ⁻¹ • h i := by
      rw [← hμ, smul_smul, inv_mul_cancel₀ hμ_ne_zero, one_smul]
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨j, hji, hαjhi⟩ := hnbr i
  have h_jc : α j c ≠ 0 := by
    intro h_jc_zero
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h_hi_span
    have h_jhi : α j (h i) = 0 := by
      rw [← hμ, map_smul, h_jc_zero, smul_zero]
    exact hαjhi h_jhi
  obtain ⟨lamj, h_lam_j⟩ := ggDepA_r_mem_span_of_commute hp2 hs hβc (hcomm j)
  have h_ric_j : r j c = c - α j c • h j := hr j c
  have h_eq2_j : α j c • h j = (1 - lamj) • c := by
    have h1 : c - α j c • h j = lamj • c := by rw [← h_ric_j, h_lam_j]
    have h2 : α j c • h j = c - lamj • c := by
      calc α j c • h j = c - (c - α j c • h j) := by abel
        _ = c - lamj • c := by rw [h1]
    rw [h2, sub_smul, one_smul]
  have h_j_ne_zero : h j ≠ 0 := ggDepA_h_ne_zero hp2 hdiag j
  have h_j_span : h j ∈ Submodule.span (ZMod p) {c} :=
    ggDepA_h_mem_span_of_ne_zero h_jc h_eq2_j h_j_ne_zero
  have h_j_hi : h j ∈ Submodule.span (ZMod p) {h i} := by
    have h_le : Submodule.span (ZMod p) {c} ≤ Submodule.span (ZMod p) {h i} := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact h_c_span_hi
    exact h_le h_j_span
  exact hh j i hji h_j_hi

theorem ggDepA_mem_span_of_commute {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {N : ℕ} (hN : 3 ≤ N) {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (hfr : GGDepAFrame p N h α x)
    (hh : ∀ j k : Fin (N - 1), j ≠ k → h j ∉ Submodule.span (ZMod p) {h k})
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    {s : V ≃ₗ[ZMod p] V} {c : V} {β : Module.Dual (ZMod p) V} (hs : ∀ v, s v = v - β v • c)
    (hβc : β c = 2) (hcomm : ∀ i, s * r i = r i * s) : c ∈ Submodule.span (ZMod p) {x} := by
  refine ggDep_mem_span_of_commute hp2 hfr.fix ?_ ?_ hh r hr hs hβc hcomm
  · intro i
    rw [hfr.pair i i]
    simp [CartanMatrix.A, Matrix.of_apply]
  · intro i
    have hN1 : 2 ≤ N - 1 := by omega
    let j : Fin (N - 1) := if h : (i : ℕ) + 1 < N - 1 then ⟨i + 1, h⟩ else ⟨i - 1, by omega⟩
    have hji : j ≠ i := by
      dsimp [j]
      split_ifs with h
      · intro heq
        have hval := congrArg (fun x : Fin (N - 1) => (x : ℕ)) heq
        simp at hval
      · intro heq
        have hval := congrArg (fun x : Fin (N - 1) => (x : ℕ)) heq
        simp at hval
        omega
    refine ⟨j, hji, ?_⟩
    have hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i := by
      dsimp [j]
      split_ifs with h
      · left; simp
      · right; simp; omega
    have h_int : CartanMatrix.A (N - 1) j i = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hji]
      rw [if_pos (Or.symm hadj)]
    rw [hfr.pair j i, h_int]
    norm_num

private lemma ggWeyl_key_lemma {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {H : Subgroup (V ≃ₗ[ZMod p] V)}
    {s s' : V ≃ₗ[ZMod p] V} {c c' : V} {β β' : Module.Dual (ZMod p) V}
    (hs : ∀ v, s v = v - β v • c) (hs' : ∀ v, s' v = v - β' v • c')
    (hβc : β c = 2) (hβ'c' : β' c' = 2)
    (hc' : c' ∈ Submodule.span (ZMod p) {c})
    (hnt : ∀ g ∈ H, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hsmem : s ∈ H) (hs'mem : s' ∈ H) :
    s = s' := by
  have h2unit : (2 : ZMod p) ≠ 0 := ggDepA_h2_ne_zero hp2
  have hc_ne_zero : c ≠ 0 := by
    intro hc0
    rw [hc0, map_zero] at hβc
    exact h2unit hβc.symm
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hc'
  let β'' : Module.Dual (ZMod p) V := lam • β'
  have hβ''c : β'' c = 2 := by
    dsimp [β'']
    rw [← hβ'c', ← hlam, map_smul, smul_eq_mul]
  have hs'' : ∀ v, s' v = v - β'' v • c := by
    intro v
    rw [hs' v, ← hlam]
    dsimp [β'']
    rw [smul_smul, mul_comm]
  let g : V ≃ₗ[ZMod p] V := s * s'
  have hgmem : g ∈ H := Subgroup.mul_mem _ hsmem hs'mem
  have hg_eq : ∀ v, g v = v - (β - β'') v • c := by
    intro v
    dsimp [g]
    rw [hs'' v]
    rw [map_sub, map_smul]
    rw [hs v]
    have h_sc : s c = -c := by
      rw [hs c, hβc, two_smul]
      abel
    rw [h_sc, smul_neg, sub_neg_eq_add]
    rw [sub_smul]
    abel
  have hgc : g c = c := by
    rw [hg_eq c]
    have hδc : (β - β'') c = 0 := by
      rw [LinearMap.sub_apply, hβc, hβ''c, sub_self]
    rw [hδc, zero_smul, sub_zero]
  have hgfix : ∀ w, g (g w - w) = g w - w := by
    intro w
    have h1 : g w - w = -((β - β'') w) • c := by
      rw [hg_eq w]
      simp only [LinearMap.sub_apply, sub_smul, one_smul]
      rw [sub_sub_cancel_left, neg_smul, sub_smul]
    rw [h1]
    simp [map_neg, map_smul, hgc]
  by_contra hne
  have hδne : β - β'' ≠ 0 := by
    intro hδ
    apply hne
    ext v
    rw [hs v, hs'' v]
    have hv : β v = β'' v := by
      have := congrArg (fun f => f v) hδ
      simp at this
      exact sub_eq_zero.mp this
    rw [hv]
  have htrans : Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w := by
    constructor
    · have hrange : ggLinMove g = Submodule.span (ZMod p) {c} := by
        apply le_antisymm
        · intro x hx
          rw [ggLinMove] at hx
          obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx
          have hx' : x = -((β - β'') v) • c := by
            rw [← hv]
            change g v - v = -((β - β'') v) • c
            rw [hg_eq v]
            simp only [LinearMap.sub_apply, sub_smul, one_smul]
            rw [sub_sub_cancel_left, neg_smul, sub_smul]
          rw [hx']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · intro x hx
          rw [Submodule.mem_span_singleton] at hx
          obtain ⟨μ, hμ⟩ := hx
          have h_exists : ∃ w, (β - β'') w ≠ 0 := by
            by_contra h
            simp only [not_exists, not_not] at h
            exact hδne (LinearMap.ext h)
          obtain ⟨w, hw⟩ := h_exists
          let v := (-μ * ((β - β'') w)⁻¹) • w
          have hv : g v - v = x := by
            rw [hg_eq v]
            have hδv : (β - β'') v = -μ := by
              show (β - β'') ((-μ * ((β - β'') w)⁻¹) • w) = -μ
              rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hw, mul_one]
            rw [hδv]
            simp [hμ]
          rw [ggLinMove]
          exact LinearMap.mem_range.mpr ⟨v, by change g v - v = x; exact hv⟩
      rw [hrange]
      exact finrank_span_singleton hc_ne_zero
    · exact hgfix
  exact hnt g hgmem htrans

theorem ggWeyl_rootLine_false {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {AA AK : Subgroup (MulAut ↥Bs)} (hKA : AK ≤ AA) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    [Nontrivial Λ] {M : CoxeterMatrix Λ} (hW : GGIsWeylMatrix M) {φ : Λ → MulAut ↥Bs}
    (hrefl : ∀ i, GGIsReflection p (φ i)) (f : M.Group ≃* ↥AK)
    (hf : ∀ i, ((f (M.simple i) : ↥AK) : MulAut ↥Bs) = φ i)
    (hcl : AK = Subgroup.closure (Set.range φ)) {z : ↥Bs} (hmove : ∃ t ∈ AK, t z ≠ z)
    (hnt : ∀ g ∈ AA.map (ggLin (p := p) ι),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hline : ∀ s ∈ AA.map (ggLin (p := p) ι), s (ι (Additive.ofMul z)) ≠ ι (Additive.ofMul z) →
      ∀ (c : V) (β : Module.Dual (ZMod p) V), (∀ v, s v = v - β v • c) → β c = 2 →
        c ∈ Submodule.span (ZMod p) {ι (Additive.ofMul z)}) : False := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, φ i z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨t', ht'K, ht'z⟩ := hmove
    apply ht'z
    have hle : AK ≤ MulAction.stabilizer (MulAut ↥Bs) z := by
      rw [hcl, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr (hcon j)
    exact MulAction.mem_stabilizer_iff.mp (hle ht'K)
  have hφK : ∀ j, φ j ∈ AK := fun j => by rw [hcl]; exact Subgroup.subset_closure ⟨j, rfl⟩
  have hψR : ∀ j, ggLin (p := p) ι (φ j) ∈ AA.map (ggLin (p := p) ι) := fun j =>
    Subgroup.mem_map.mpr ⟨φ j, hKA (hφK j), rfl⟩
  have hψi_refl : GGLinRefl (ggLin (p := p) ι (φ i)) :=
    (ggRC_isReflection_iff_linRefl (p := p) ι _).mp (hrefl i)
  obtain ⟨ci, βi, hβi_ci, hψi_form⟩ := (ggDepA_linRefl_iff hp2 _).mp hψi_refl
  have hψi_moves : ggLin (p := p) ι (φ i) (ι (Additive.ofMul z)) ≠ ι (Additive.ofMul z) := by
    intro h
    exact hi ((ggLin_fix_iff (p := p) ι (φ i) z).mpr h)
  have hci_span : ci ∈ Submodule.span (ZMod p) {ι (Additive.ofMul z)} :=
    hline (ggLin (p := p) ι (φ i)) (hψR i) hψi_moves ci βi hψi_form hβi_ci
  have hci_ne_zero : ci ≠ 0 := by
    intro hci0
    rw [hci0, map_zero] at hβi_ci
    exact ggDepA_h2_ne_zero hp2 hβi_ci.symm
  have hci_span_eq : Submodule.span (ZMod p) {ci} = Submodule.span (ZMod p) {ι (Additive.ofMul z)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hci_span
    · rw [Submodule.span_singleton_le_iff_mem]
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hci_span
      have hμ_ne_zero : μ ≠ 0 := by
        intro hμ0
        rw [hμ0, zero_smul] at hμ
        exact hci_ne_zero hμ.symm
      have hx : ι (Additive.ofMul z) = μ⁻¹ • ci := by
        rw [← hμ, smul_smul, inv_mul_cancel₀ hμ_ne_zero, one_smul]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨j, hji, hj3⟩ := ggWeyl_exists_bond hW i
  by_cases hfix : φ j z = z
  · have hψj_fix : ggLin (p := p) ι (φ j) (ι (Additive.ofMul z)) = ι (Additive.ofMul z) :=
      (ggLin_fix_iff (p := p) ι (φ j) z).mp hfix
    have hψj_ci : ggLin (p := p) ι (φ j) ci = ci := by
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hci_span
      rw [← hμ, map_smul, hψj_fix, hμ]
    let ψj : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ j)
    let s' : V ≃ₗ[ZMod p] V := ψj * ggLin (p := p) ι (φ i) * ψj⁻¹
    have hs'_form : ∀ v, s' v = v - βi (ψj.symm v) • ci := by
      intro v
      change ψj (ggLin (p := p) ι (φ i) (ψj.symm v)) = v - βi (ψj.symm v) • ci
      rw [hψi_form, map_sub, map_smul, hψj_ci]
      simp
    let β' : Module.Dual (ZMod p) V := βi.comp ψj.symm.toLinearMap
    have hs'_form' : ∀ v, s' v = v - β' v • ci := by
      intro v
      rw [hs'_form v]
      rfl
    have hβ'ci : β' ci = 2 := by
      change βi (ψj.symm ci) = 2
      have hψj_symm_ci : ψj.symm ci = ci := by
        rw [LinearEquiv.symm_apply_eq]
        exact hψj_ci.symm
      rw [hψj_symm_ci]
      exact hβi_ci
    have hs'mem : s' ∈ AA.map (ggLin (p := p) ι) := by
      dsimp [s', ψj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hψR j) (hψR i)) (Subgroup.inv_mem _ (hψR j))
    have h_eq : ggLin (p := p) ι (φ i) = s' := by
      apply ggWeyl_key_lemma hp2 hψi_form hs'_form' hβi_ci hβ'ci _ hnt (hψR i) hs'mem
      exact Submodule.subset_span (by simp)
    have hcomm_ψ : ggLin (p := p) ι (φ i) * ggLin (p := p) ι (φ j) = ggLin (p := p) ι (φ j) * ggLin (p := p) ι (φ i) := by
      have h_eq' : ggLin (p := p) ι (φ i) = ggLin (p := p) ι (φ j) * ggLin (p := p) ι (φ i) * (ggLin (p := p) ι (φ j))⁻¹ := by
        simpa [s', ψj] using h_eq
      conv_lhs => rw [h_eq']
      group
    have hcomm : φ i * φ j = φ j * φ i := by
      apply ggLin_injective (p := p) ι
      rw [map_mul, map_mul, hcomm_ψ]
    have hsc : M.simple i * M.simple j = M.simple j * M.simple i := by
      apply f.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hf, hf]
      exact hcomm
    have hii : M.simple i * M.simple i = 1 := CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem i
    have hjj : M.simple j * M.simple j = 1 := CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem j
    have hsq : (M.simple i * M.simple j) ^ 2 = 1 := by
      rw [pow_two]
      calc M.simple i * M.simple j * (M.simple i * M.simple j)
          = M.simple i * (M.simple j * M.simple i) * M.simple j := by group
        _ = M.simple i * (M.simple i * M.simple j) * M.simple j := by rw [hsc]
        _ = (M.simple i * M.simple i) * (M.simple j * M.simple j) := by group
        _ = 1 := by rw [hii, hjj, one_mul]
    have hord : orderOf (M.simple i * M.simple j) = M.M i j := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    have hdvd : M.M i j ∣ 2 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hsq
    have hle : M.M i j ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have hψj_moves : ggLin (p := p) ι (φ j) (ι (Additive.ofMul z)) ≠ ι (Additive.ofMul z) :=
      fun h => hfix ((ggLin_fix_iff (p := p) ι (φ j) z).mpr h)
    have hψj_refl : GGLinRefl (ggLin (p := p) ι (φ j)) :=
      (ggRC_isReflection_iff_linRefl (p := p) ι _).mp (hrefl j)
    obtain ⟨cj, βj, hβj_cj, hψj_form⟩ := (ggDepA_linRefl_iff hp2 _).mp hψj_refl
    have hcj_span : cj ∈ Submodule.span (ZMod p) {ι (Additive.ofMul z)} :=
      hline (ggLin (p := p) ι (φ j)) (hψR j) hψj_moves cj βj hψj_form hβj_cj
    have hcj_span_ci : cj ∈ Submodule.span (ZMod p) {ci} := by
      rw [hci_span_eq]
      exact hcj_span
    have h_eq : ggLin (p := p) ι (φ i) = ggLin (p := p) ι (φ j) := by
      apply ggWeyl_key_lemma hp2 hψi_form hψj_form hβi_ci hβj_cj hcj_span_ci hnt (hψR i) (hψR j)
    have hφ_eq : φ i = φ j := by
      apply ggLin_injective (p := p) ι
      rw [h_eq]
    have hsimple_eq : M.simple i = M.simple j := by
      apply f.injective
      apply Subtype.ext
      rw [hf, hf, hφ_eq]
    have hord : orderOf (M.simple i * M.simple j) = 1 := by
      rw [hsimple_eq]
      change orderOf (M.toCoxeterSystem.simple j * M.toCoxeterSystem.simple j) = 1
      rw [CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem j]
      simp
    have hordM : orderOf (M.simple i * M.simple j) = M.M i j := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    rw [hordM] at hord
    omega

end CFSG.StandardType

end
