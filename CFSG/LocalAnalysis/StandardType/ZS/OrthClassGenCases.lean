module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenRoot
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenTrans
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenTransThree
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenThreeMinus
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenRefl

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_finrank_perp_add_two [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (P : HypPair Q) :
    Module.finrank (ZMod p) P.perp + 2 = Module.finrank (ZMod p) U := by
  let φ : U →ₗ[ZMod p] (ZMod p × ZMod p) := (polarBilin Q P.e).prod (polarBilin Q P.f)
  have hker : LinearMap.ker φ = P.perp := by
    dsimp only [φ]
    rw [LinearMap.ker_prod, HypPair.perp]
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨s, t⟩
    refine ⟨s • P.f + t • P.e, Prod.ext ?_ ?_⟩
    · show polar Q P.e (s • P.f + t • P.e) = s
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ef, P.polar_ee]
      ring
    · show polar Q P.f (s • P.f + t • P.e) = t
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]
      ring
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at h
  omega

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_perp_eq_span [Module.Finite (ZMod p) U] (h3 : Module.finrank (ZMod p) U = 3)
    {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {a : U} (ha : a ∈ P.perp) (ha0 : a ≠ 0) :
    P.perp = Submodule.span (ZMod p) {a} := by
  have hdim : Module.finrank (ZMod p) P.perp = 1 := by
    have h := ocg_finrank_perp_add_two (p := p) P
    omega
  have hle : Submodule.span (ZMod p) {a} ≤ P.perp := by
    rw [Submodule.span_le]
    simpa using ha
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton ha0, hdim])).symm

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_norm_add {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {c : ZMod p} {a : U}
    (ha : a ∈ P.perp) (hQa : Q a = c) : Q (a + P.e) = c ∧ Q (a + P.f) = c := by
  obtain ⟨hae, haf⟩ := HypPair.mem_perp.mp ha
  have hpe : polar Q a P.e = 0 := by rw [polar_comm]; exact hae
  have hpf : polar Q a P.f = 0 := by rw [polar_comm]; exact haf
  constructor
  · rw [QuadraticMap.map_add Q, hQa, P.Q_e, hpe]; ring
  · rw [QuadraticMap.map_add Q, hQa, P.Q_f, hpf]; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_span_perp_e {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {a : U}
    {v : Empty → U} (hperp : P.perp = Submodule.span (ZMod p) {a}) {w : U}
    (hw : polar Q P.e w = 0) :
    w ∈ Submodule.span (ZMod p) (insert P.e (insert a (Set.range fun i => reflect Q (v i) a))) := by
  have hproj : P.proj w ∈ Submodule.span (ZMod p) {a} := by
    rw [← hperp]; exact P.proj_mem_perp w
  have hw_eq : w = polar Q w P.f • P.e + P.proj w := by
    have h := P.eq_add_proj w
    rw [polar_comm Q w P.e, hw, zero_smul, add_zero] at h
    exact h
  rw [hw_eq]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) ?_
  refine Submodule.span_mono ?_ hproj
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_span_perp_f {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {a : U}
    {v : Empty → U} (hperp : P.perp = Submodule.span (ZMod p) {a}) {w : U}
    (hw : polar Q P.f w = 0) :
    w ∈ Submodule.span (ZMod p) (insert P.f (insert a (Set.range fun i => reflect Q (v i) a))) := by
  have hproj : P.proj w ∈ Submodule.span (ZMod p) {a} := by
    rw [← hperp]; exact P.proj_mem_perp w
  have hw_eq : w = polar Q w P.e • P.f + P.proj w := by
    have h := P.eq_add_proj w
    rw [polar_comm Q w P.f, hw, zero_smul, zero_add] at h
    exact h
  rw [hw_eq]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) ?_
  refine Submodule.span_mono ?_ hproj
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp

private lemma ocg_list_prod_ofFn_apply {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (f : Fin n → V ≃ₗ[ZMod p] V) (b : Fin n → V)
    (hfix : ∀ i j, i ≠ j → f i (b j) = b j) (hneg : ∀ i, f i (b i) = - b i) :
    (∀ j, (List.ofFn f).prod (b j) = - b j) ∧
      (∀ v, (∀ i, f i v = v) → (List.ofFn f).prod v = v) := by
  induction n with
  | zero =>
    refine ⟨fun j => j.elim0, fun v _ => ?_⟩
    simp
  | succ n ih =>
    have hfix' : ∀ i j : Fin n, i ≠ j → (fun i => f i.succ) i (b j.succ) = b j.succ :=
      fun i j hij => hfix i.succ j.succ (fun h => hij (Fin.succ_injective n h))
    have hneg' : ∀ i : Fin n, (fun i => f i.succ) i (b i.succ) = - b i.succ :=
      fun i => hneg i.succ
    obtain ⟨ih1, ih2⟩ := ih (fun i => f i.succ) (fun i => b i.succ) hfix' hneg'
    constructor
    · intro j
      rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]
      refine Fin.cases ?_ ?_ j
      · have h0 : (List.ofFn fun i : Fin n => f i.succ).prod (b 0) = b 0 :=
          ih2 (b 0) (fun i => hfix i.succ 0 (Fin.succ_ne_zero i))
        rw [h0, hneg 0]
      · intro i
        rw [ih1 i, map_neg, hfix 0 i.succ (Fin.succ_ne_zero i).symm]
    · intro v hv
      rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]
      have hv' : (List.ofFn fun i : Fin n => f i.succ).prod v = v := ih2 v (fun i => hv i.succ)
      rw [hv', hv 0]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_closure_three_le_orthogonal {Q : QuadraticForm (ZMod p) U} (a₁ a₂ a₃ : U) :
    Subgroup.closure {reflect Q a₁, reflect Q a₂, reflect Q a₃} ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Subgroup.closure_le]
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact reflect_mem_orthogonalGroup Q a₁
  · exact reflect_mem_orthogonalGroup Q a₂
  · exact reflect_mem_orthogonalGroup Q a₃

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_closure_span_le_orthogonal {Q : QuadraticForm (ZMod p) U} (P : HypPair Q)
    {m : ℕ} (a : Fin (m + 1) → U) :
    Subgroup.closure (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
      (Set.range fun i => reflect Q (a i)))) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Subgroup.closure_le]
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_range] at ht
  rcases ht with rfl | rfl | ⟨i, rfl⟩
  · exact reflect_mem_orthogonalGroup Q (a 0 + P.e)
  · exact reflect_mem_orthogonalGroup Q (a 0 + P.f)
  · exact reflect_mem_orthogonalGroup Q (a i)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem closure_classRefl_le_of_forall_exists_apply [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {a : U}
    (hra : reflect Q a ∈ X) (htrans : ∀ b, Q b = c → ∃ g ∈ X, g a = b ∨ g a = -b) :
    Subgroup.closure (ClassRefl p Q c) ≤ X := by
  rw [Subgroup.closure_le]
  intro t ht
  obtain ⟨b, hQb, rfl⟩ := (mem_classRefl_iff hp hQ hc t).mp ht
  obtain ⟨g, hgX, hgab | hgab⟩ := htrans b hQb
  · have hconj : g * reflect Q a * g⁻¹ = reflect Q (g a) := reflect_conj (hX hgX) a
    rw [hgab] at hconj
    rw [← hconj]
    exact X.mul_mem (X.mul_mem hgX hra) (X.inv_mem hgX)
  · have hconj : g * reflect Q a * g⁻¹ = reflect Q (g a) := reflect_conj (hX hgX) a
    rw [hgab,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmSeven.reflect_neg_vec]
      at hconj
    rw [← hconj]
    exact X.mul_mem (X.mul_mem hgX hra) (X.inv_mem hgX)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem neg_mem_closure_classRefl_of_orthogonal [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {n : ℕ} (b : Fin n → U) (horth : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0)
    (hb : ∀ i, Q (b i) = c) (hspan : ⊤ ≤ Submodule.span (ZMod p) (Set.range b)) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ Subgroup.closure (ClassRefl p Q c) := by
  let f : Fin n → U ≃ₗ[ZMod p] U := fun i => reflect Q (b i)
  have hmem : ∀ i, f i ∈ Subgroup.closure (ClassRefl p Q c) := fun i =>
    Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨b i, hb i, rfl⟩)
  have hprod : (List.ofFn f).prod ∈ Subgroup.closure (ClassRefl p Q c) :=
    Subgroup.list_prod_mem (K := Subgroup.closure (ClassRefl p Q c)) fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hmem i
  have hfix : ∀ i j, i ≠ j → f i (b j) = b j := fun i j hij =>
    reflect_apply_of_polar_eq_zero (horth i j hij)
  have hneg : ∀ i, f i (b i) = - b i := fun i =>
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmSeven.reflect_apply_vec_self
      (by rw [hb i]; exact hc)
  obtain ⟨h1, _⟩ := ocg_list_prod_ofFn_apply f b hfix hneg
  have hspan' : Submodule.span (ZMod p) (Set.range b) = ⊤ := le_antisymm le_top hspan
  have hlin : ((List.ofFn f).prod : U →ₗ[ZMod p] U) =
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
    apply LinearMap.ext_on_range hspan'
    intro j
    exact h1 j
  have hEq : (List.ofFn f).prod = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
    refine LinearEquiv.ext fun x => ?_
    simpa using congrArg (fun (g : U →ₗ[ZMod p] U) => g x) hlin
  rw [← hEq]
  exact hprod

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem closure_classRefl_eq_of_isotropic [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) {a : U}
    (ha : a ∈ P.perp) (hQa : Q a = c) :
    Subgroup.closure (ClassRefl p Q c) =
      Subgroup.closure {reflect Q (a + P.e), reflect Q a, reflect Q (a + P.f)} := by
  have ha0 : a ≠ 0 := fun h => hc (by rw [← hQa, h, QuadraticMap.map_zero])
  have hperp : P.perp = Submodule.span (ZMod p) {a} := ocg_perp_eq_span h3 P ha ha0
  have hnorms := ocg_norm_add P ha hQa
  have hQane : Q a ≠ 0 := by rw [hQa]; exact hc
  let v : Empty → U := Empty.elim
  have hroot_e : IsRootCenter Q
      (Subgroup.closure {reflect Q (a + P.e), reflect Q a, reflect Q (a + P.f)}) P.e :=
    isRootCenter_of_reflect_mem P.e_ne_zero P.Q_e (HypPair.mem_perp.mp ha).1 hQane
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) v
      (fun i => Empty.elim i) (fun i => Empty.elim i) (fun w hw => ocg_span_perp_e P hperp hw)
  have hroot_f : IsRootCenter Q
      (Subgroup.closure {reflect Q (a + P.e), reflect Q a, reflect Q (a + P.f)}) P.f :=
    isRootCenter_of_reflect_mem P.f_ne_zero P.Q_f (HypPair.mem_perp.mp ha).2 hQane
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) v
      (fun i => Empty.elim i) (fun i => Empty.elim i) (fun w hw => ocg_span_perp_f P hperp hw)
  refine le_antisymm ?_ ?_
  · refine closure_classRefl_le_of_forall_exists_apply (a := a) hp hQ hc ?_ ?_ ?_
    · exact ocg_closure_three_le_orthogonal (a + P.e) a (a + P.f)
    · exact Subgroup.subset_closure (by simp)
    · intro b hb
      obtain ⟨g, hgX, hgab⟩ := exists_mem_apply_eq_or_neg_of_perp_le_span
        (ZMod.prime_ne_zero p 2 hp) P hroot_e hroot_f ha hQane (le_of_eq hperp) (by rw [hb, hQa])
      refine ⟨g⁻¹, Subgroup.inv_mem _ hgX, ?_⟩
      rcases hgab with h | h
      · left
        simpa using (congrArg (fun x => g⁻¹ x) h).symm
      · right
        have h2 : b = - g⁻¹ a := by simpa using congrArg (fun x => g⁻¹ x) h
        rw [h2, neg_neg]
  · rw [Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a + P.e, hnorms.1, rfl⟩)
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a, hQa, rfl⟩)
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a + P.f, hnorms.2, rfl⟩)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem closure_classRefl_eq_of_anisotropic [Module.Finite (ZMod p) U]
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (P : HypPair Q) {x : U} (hx : x ∈ P.perp)
    (hsq : ¬ IsSquare (c / Q x)) {lam t : ZMod p} (hlam : lam ≠ 0) (hlam4 : lam ^ 4 ≠ 1)
    (hκ : -(c / Q x) * (1 - lam ^ 2) = t ^ 2) :
    Subgroup.closure (ClassRefl p Q c) =
      Subgroup.closure {reflect Q (lam • P.e + (c / lam) • P.f), reflect Q (P.e + c • P.f),
        reflect Q (P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x)} := by
  have hp : p ≠ 2 := by
    rintro rfl
    exact hsq (isSquare_of_charTwo' (R := ZMod 2) (c / Q x))
  have hc : c ≠ 0 := by
    rintro rfl
    exact hsq ⟨0, by rw [zero_div]; ring⟩
  have hx0 : Q x ≠ 0 := by
    rintro h
    exact hsq ⟨0, by rw [h, div_zero]; ring⟩
  have hlam2 : lam ^ 2 ≠ 1 := fun h =>
    hlam4 (by rw [show lam ^ 4 = (lam ^ 2) ^ 2 by ring, h, one_pow])
  have hnorms := threeMinus_map_eq P hx hx0 hlam hlam2 hκ
  have hroot := isRootCenter_threeMinus h3 hQ P hx hx0 hc hlam hlam4 hκ
    (a₁ := lam • P.e + (c / lam) • P.f) (a₂ := P.e + c • P.f)
    (a₃ := P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x) rfl rfl rfl
  refine le_antisymm ?_ ?_
  · refine closure_classRefl_le_of_forall_exists_apply
      (a := lam • P.e + (c / lam) • P.f) hp hQ hc ?_ ?_ ?_
    · exact ocg_closure_three_le_orthogonal (lam • P.e + (c / lam) • P.f) (P.e + c • P.f)
        (P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x)
    · exact Subgroup.subset_closure (by simp)
    · intro b hb
      obtain ⟨g, hgX, hgab⟩ := exists_mem_apply_eq_of_not_isSquare_div P hroot.1 hroot.2 hx hsq
        hnorms.1 hb
      exact ⟨g, hgX, Or.inl hgab⟩
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.subset_closure
        ((mem_classRefl_iff hp hQ hc _).2 ⟨lam • P.e + (c / lam) • P.f, hnorms.1, rfl⟩)
    · exact Subgroup.subset_closure
        ((mem_classRefl_iff hp hQ hc _).2 ⟨P.e + c • P.f, hnorms.2.1, rfl⟩)
    · exact Subgroup.subset_closure
        ((mem_classRefl_iff hp hQ hc _).2
          ⟨P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x, hnorms.2.2, rfl⟩)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_a_mem_span_reflect {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {c : ZMod p}
    (hc : c ≠ 0) {m : ℕ} {a : Fin (m + 1) → U} (ha : ∀ i, a i ∈ P.perp ∧ Q (a i) = c)
    (hpol : ∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0) (i : Fin (m + 1)) :
    a i ∈ Submodule.span (ZMod p) (insert (a 0) (Set.range fun j => reflect Q (a j) (a 0))) := by
  by_cases hi : i = 0
  · subst hi
    exact Submodule.subset_span (by simp)
  · have hB : polar Q (a i) (a 0) ≠ 0 := by rw [polar_comm]; exact hpol i hi
    have hQi : Q (a i) = c := (ha i).2
    have hreflect : reflect Q (a i) (a 0) = a 0 - (polar Q (a i) (a 0) / c) • a i := by
      rw [reflect_apply (by rw [hQi]; exact hc), hQi]
    have hkey : a i = (c / polar Q (a i) (a 0)) • (a 0 - reflect Q (a i) (a 0)) := by
      rw [hreflect]
      have h1 : a 0 - (a 0 - (polar Q (a i) (a 0) / c) • a i) =
          (polar Q (a i) (a 0) / c) • a i := by abel
      rw [h1, smul_smul]
      have hcoef : c / polar Q (a i) (a 0) * (polar Q (a i) (a 0) / c) = 1 := by
        field_simp
      rw [hcoef, one_smul]
    rw [hkey]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span (by simp))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i))))

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_perp_le_span_e {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {c : ZMod p}
    (hc : c ≠ 0) {m : ℕ} {a : Fin (m + 1) → U} (ha : ∀ i, a i ∈ P.perp ∧ Q (a i) = c)
    (hpol : ∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0)
    (hspan : P.perp ≤ Submodule.span (ZMod p) (Set.range a)) :
    ∀ w, polar Q P.e w = 0 →
      w ∈ Submodule.span (ZMod p) (insert P.e (insert (a 0)
        (Set.range fun j => reflect Q (a j) (a 0)))) := by
  have hrange_le : Submodule.span (ZMod p) (Set.range a) ≤ Submodule.span (ZMod p)
      (insert P.e (insert (a 0) (Set.range fun j => reflect Q (a j) (a 0)))) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.span_mono (Set.subset_insert _ _) (ocg_a_mem_span_reflect P hc ha hpol i)
  intro w hw
  have hproj : P.proj w ∈ Submodule.span (ZMod p)
      (insert P.e (insert (a 0) (Set.range fun j => reflect Q (a j) (a 0)))) :=
    hrange_le (hspan (P.proj_mem_perp w))
  have hw_eq : w = polar Q w P.f • P.e + P.proj w := by
    have h := P.eq_add_proj w
    rw [polar_comm Q w P.e, hw, zero_smul, add_zero] at h
    exact h
  rw [hw_eq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) hproj

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_perp_le_span_f {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {c : ZMod p}
    (hc : c ≠ 0) {m : ℕ} {a : Fin (m + 1) → U} (ha : ∀ i, a i ∈ P.perp ∧ Q (a i) = c)
    (hpol : ∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0)
    (hspan : P.perp ≤ Submodule.span (ZMod p) (Set.range a)) :
    ∀ w, polar Q P.f w = 0 →
      w ∈ Submodule.span (ZMod p) (insert P.f (insert (a 0)
        (Set.range fun j => reflect Q (a j) (a 0)))) := by
  have hrange_le : Submodule.span (ZMod p) (Set.range a) ≤ Submodule.span (ZMod p)
      (insert P.f (insert (a 0) (Set.range fun j => reflect Q (a j) (a 0)))) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.span_mono (Set.subset_insert _ _) (ocg_a_mem_span_reflect P hc ha hpol i)
  intro w hw
  have hproj : P.proj w ∈ Submodule.span (ZMod p)
      (insert P.f (insert (a 0) (Set.range fun j => reflect Q (a j) (a 0)))) :=
    hrange_le (hspan (P.proj_mem_perp w))
  have hw_eq : w = polar Q w P.e • P.f + P.proj w := by
    have h := P.eq_add_proj w
    rw [polar_comm Q w P.f, hw, zero_smul, zero_add] at h
    exact h
  rw [hw_eq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) hproj

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem closure_classRefl_eq_of_four_le [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) {m : ℕ}
    (a : Fin (m + 1) → U) (ha : ∀ i, a i ∈ P.perp ∧ Q (a i) = c)
    (hpol : ∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0)
    (hspan : P.perp ≤ Submodule.span (ZMod p) (Set.range a)) :
    Subgroup.closure (ClassRefl p Q c) =
      Subgroup.closure (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
        (Set.range fun i => reflect Q (a i)))) := by
  have hQa0 : Q (a 0) = c := (ha 0).2
  have hQa0ne : Q (a 0) ≠ 0 := by rw [hQa0]; exact hc
  have hnorms := ocg_norm_add P (ha 0).1 hQa0
  have hdim : 2 ≤ Module.finrank (ZMod p) P.perp := by
    have h := ocg_finrank_perp_add_two (p := p) P
    omega
  have huniv : ∀ t : ZMod p, ∃ w ∈ P.perp, Q w = t := fun t =>
    exists_mem_map_eq_of_two_le_finrank hp (P.polarNondegOn_perp hQ) hdim t
  have hroot_e : IsRootCenter Q
      (Subgroup.closure (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
        (Set.range fun i => reflect Q (a i))))) P.e :=
    isRootCenter_of_reflect_mem P.e_ne_zero P.Q_e (HypPair.mem_perp.mp (ha 0).1).1 hQa0ne
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) a
      (fun i => (HypPair.mem_perp.mp (ha i).1).1)
      (fun i => Subgroup.subset_closure (by simp))
      (fun w hw => ocg_perp_le_span_e P hc ha hpol hspan w hw)
  have hroot_f : IsRootCenter Q
      (Subgroup.closure (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
        (Set.range fun i => reflect Q (a i))))) P.f :=
    isRootCenter_of_reflect_mem P.f_ne_zero P.Q_f (HypPair.mem_perp.mp (ha 0).1).2 hQa0ne
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) a
      (fun i => (HypPair.mem_perp.mp (ha i).1).2)
      (fun i => Subgroup.subset_closure (by simp))
      (fun w hw => ocg_perp_le_span_f P hc ha hpol hspan w hw)
  refine le_antisymm ?_ ?_
  · refine closure_classRefl_le_of_forall_exists_apply (a := a 0) hp hQ hc ?_ ?_ ?_
    · exact ocg_closure_span_le_orthogonal P a
    · exact Subgroup.subset_closure (by simp)
    · intro b hb
      obtain ⟨g, hgX, hgab⟩ := exists_mem_apply_eq_of_perp_represents
        (b := b) (ZMod.prime_ne_zero p 2 hp) P hroot_e hroot_f huniv hQa0ne (by rw [hQa0, hb])
      exact ⟨g, hgX, Or.inl hgab⟩
  · rw [Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_range] at ht
    rcases ht with rfl | rfl | ⟨i, rfl⟩
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a 0 + P.e, hnorms.1, rfl⟩)
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a 0 + P.f, hnorms.2, rfl⟩)
    · exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).2 ⟨a i, (ha i).2, rfl⟩)

end CFSG.StandardType.ZS
