module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp
import CFSG.LieType.SeitzGeneration.OuterLinearWide

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCSpFull CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SpSeitz

variable {r : ℕ} {K : Type} [Field K]

abbrev cGen (E : Subgroup (StatedProj (StatedSp r K))) : Subgroup (StatedSp r K) :=
  (⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _)).comap (proj r K)

theorem mem_cGen_of_commute {E : Subgroup (StatedProj (StatedSp r K))} {g h : StatedSp r K}
    (hg : proj r K g ∈ E) (hg1 : proj r K g ≠ 1) (hc : h * g = g * h) : h ∈ cGen E := by
  rw [mem_comap]
  have hsub : (⊤ : Subgroup _) ⊓ centralizer ({proj r K g} : Set _) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _) :=
    le_iSup₂_of_le (proj r K g) hg (le_iSup_of_le hg1 le_rfl)
  refine hsub ⟨mem_top _, ?_⟩
  exact mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hc])

theorem transCenter_of_eig {E : Subgroup (StatedProj (StatedSp r K))} {g : StatedSp r K}
    (hg : proj r K g ∈ E) (hg1 : proj r K g ≠ 1) {v : Fin r ⊕ Fin r → K}
    (hv : spEnd g v = v ∨ spEnd g v = -v) : TransCenter (cGen E) v := by
  intro t
  apply mem_cGen_of_commute hg hg1
  rcases hv with hv | hv
  · exact commute_spTransvection hv t
  · have h := spTransvection_conj g v t
    rw [hv, show -v = (-1 : K) • v by simp, spTransvection_smul] at h
    simp only [neg_mul, one_mul, neg_neg] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem spEnd_eq_of_mem_spScalars (hr : 1 ≤ r) {z : StatedSp r K}
    (hz : z ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K) :
    spEnd z = 1 ∨ spEnd z = -1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hc2 : c ^ 2 = 1 := (StatedAPI.scalar_mem_statedSp_iff hr c).mp (by rw [hc]; exact z.2)
  have hsp : ∀ v, spEnd z v = (c : K) • v := fun v => by
    rw [spEnd_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext x
    simp [Matrix.mulVec_diagonal]
  have hc' : (c : K) * c = 1 := by rw [← Units.val_mul, ← sq, hc2, Units.val_one]
  rcases mul_self_eq_one_iff.mp hc' with h | h
  · left
    exact LinearMap.ext fun v => by rw [hsp, h, one_smul]; rfl
  · right
    exact LinearMap.ext fun v => by rw [hsp, h, neg_one_smul]; rfl

theorem mem_spScalars_of_spEnd_eq {g : StatedSp r K} (c : Kˣ) (h : spEnd g = (c : K) • 1) :
    g ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
  rw [Subgroup.mem_subgroupOf]
  refine ⟨c, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  change _ = spEnd g v
  rw [h]
  simp [Matrix.smul_mulVec]

theorem proj_eq_one_of_spEnd_eq {g : StatedSp r K} (h : spEnd g = 1 ∨ spEnd g = -1) :
    proj r K g = 1 := by
  rw [← MonoidHom.mem_ker, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
  rcases h with h | h
  · exact mem_spScalars_of_spEnd_eq 1 (by rw [h]; simp)
  · exact mem_spScalars_of_spEnd_eq (-1) (by rw [h]; exact LinearMap.ext fun v => by simp)

theorem spEnd_sq_of_proj (hr : 1 ≤ r) {g : StatedSp r K} (hg : proj r K g ^ 2 = 1) :
    spEnd g * spEnd g = 1 ∨ spEnd g * spEnd g = -1 := by
  have h : g * g ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj, MonoidHom.mem_ker,
      map_mul, ← sq, hg]
  rw [← spEnd_mul]
  exact spEnd_eq_of_mem_spScalars hr h

theorem spEnd_comm_of_proj (hr : 1 ≤ r) {g h : StatedSp r K}
    (hc : proj r K g * proj r K h = proj r K h * proj r K g) :
    spEnd g * spEnd h = spEnd h * spEnd g ∨ spEnd g * spEnd h = -(spEnd h * spEnd g) := by
  have hm : g * h * (h * g)⁻¹ ∈
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj, MonoidHom.mem_ker,
      map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
  have hgh : g * h = (g * h * (h * g)⁻¹) * (h * g) := by group
  rcases spEnd_eq_of_mem_spScalars hr hm with h1 | h1
  · left
    rw [← spEnd_mul, ← spEnd_mul, hgh, spEnd_mul _ (h * g), h1, one_mul]
  · right
    rw [← spEnd_mul, ← spEnd_mul, hgh, spEnd_mul _ (h * g), h1]
    exact LinearMap.ext fun v => by simp

theorem spForm_eq_zero_of_eig (g : StatedSp r K) {u v : Fin r ⊕ Fin r → K} {c c' : K}
    (hu : spEnd g u = c • u) (hv : spEnd g v = c' • v) (hcc : c * c' ≠ 1) :
    spForm r K u v = 0 := by
  have h := spEnd_isometry g u v
  rw [hu, hv] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have h' : (c * c' - 1) * spForm r K u v = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hcc)

theorem restrict_nondegenerate_of_orth {ι : Type*} {Vs : ι → Submodule K (Fin r ⊕ Fin r → K)}
    (hspan : ⨆ i, Vs i = ⊤)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ Vs i, ∀ v ∈ Vs j, spForm r K u v = 0) (i : ι) :
    ((spForm r K).restrict (Vs i)).Nondegenerate := by
  classical
  have key : ∀ w ∈ Vs i, (∀ y ∈ Vs i, spForm r K w y = 0) → w = 0 := by
    intro w hw hy
    refine spForm_nondegenerate.1 w fun y => ?_
    have hle : ⨆ j, Vs j ≤ LinearMap.ker (spForm r K w) := iSup_le fun j z hz => by
      rw [LinearMap.mem_ker]
      by_cases hji : j = i
      · subst hji
        exact hy z hz
      · exact horth i j (Ne.symm hji) w hw z hz
    rw [hspan] at hle
    exact LinearMap.mem_ker.mp (hle Submodule.mem_top)
  refine ⟨fun w hw => Subtype.ext (key w w.2 fun y hy => hw ⟨y, hy⟩), fun w hw => ?_⟩
  refine Subtype.ext (key w w.2 fun y hy => ?_)
  have := hw ⟨y, hy⟩
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this
  rw [spForm_swap, this, neg_zero]

theorem eq_eig_sup_eig {W : Type*} [AddCommGroup W] [Module K W] (h2K : (2 : K) ≠ 0)
    {T : Module.End K W} (hT : T * T = 1) (X : Submodule K W) (hX : ∀ x ∈ X, T x ∈ X) :
    X = (X ⊓ T.eigenspace 1) ⊔ (X ⊓ T.eigenspace (-1)) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  have hTT : T (T x) = x := by rw [← Module.End.mul_apply, hT, Module.End.one_apply]
  have hx2 : x = (2 : K)⁻¹ • (x + T x) + (2 : K)⁻¹ • (x - T x) := by
    rw [← smul_add, show x + T x + (x - T x) = (2 : K) • x by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2K, one_smul]
  rw [hx2]
  refine Submodule.add_mem_sup ⟨X.smul_mem _ (X.add_mem hx (hX x hx)), ?_⟩
    ⟨X.smul_mem _ (X.sub_mem hx (hX x hx)), ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, map_smul, map_add, hTT, add_comm, one_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, map_smul, map_sub, hTT, neg_smul,
      one_smul, smul_sub, smul_sub, neg_sub]

theorem neg_one_ne_one_of_two (h2K : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := fun h =>
  h2K (by linear_combination -h)

theorem exists_sq_add_sq [Finite K] (h2K : (2 : K) ≠ 0) {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (γ : K) : ∃ s t : K, α * s ^ 2 + β * t ^ 2 + γ = 0 := by
  classical
  have := Fintype.ofFinite K
  have hch : ringChar K ≠ 2 := fun h => h2K (by
    have := ringChar.spec K 2
    exact_mod_cast this.2 (by rw [h]))
  obtain ⟨s, t, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C γ)
    (g := Polynomial.C β * Polynomial.X ^ 2) (by compute_degree!) (by compute_degree!)
    (FiniteField.odd_card_of_char_ne_two hch)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  exact ⟨s, t, by linear_combination h⟩

abbrev eigB (A : Module.End K (Fin r ⊕ Fin r → K)) (i : Bool) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  cond i (A.eigenspace 1) (A.eigenspace (-1))

theorem eigB_iSup (h2K : (2 : K) ≠ 0) {A : Module.End K (Fin r ⊕ Fin r → K)} (hA : A * A = 1) :
    ⨆ i, eigB A i = ⊤ := by
  rw [iSup_bool_eq]
  have := eq_eig_sup_eig h2K hA ⊤ fun _ _ => Submodule.mem_top
  simp only [top_inf_eq] at this
  exact this.symm

theorem eigB_orth (h2K : (2 : K) ≠ 0) (a : StatedSp r K) :
    ∀ i j, i ≠ j → ∀ u ∈ eigB (spEnd a) i, ∀ v ∈ eigB (spEnd a) j, spForm r K u v = 0 := by
  intro i j hij u hu v hv
  cases i <;> cases j
  · exact absurd rfl hij
  · exact spForm_eq_zero_of_eig a (Module.End.mem_eigenspace_iff.mp hu)
      (Module.End.mem_eigenspace_iff.mp hv) (by rw [neg_one_mul]; exact neg_one_ne_one_of_two h2K)
  · exact spForm_eq_zero_of_eig a (Module.End.mem_eigenspace_iff.mp hu)
      (Module.End.mem_eigenspace_iff.mp hv) (by rw [one_mul]; exact neg_one_ne_one_of_two h2K)
  · exact absurd rfl hij

theorem eig_of_eigB {A : Module.End K (Fin r ⊕ Fin r → K)} {i : Bool} {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ eigB A i) : A v = v ∨ A v = -v := by
  cases i
  · right
    rw [Module.End.mem_eigenspace_iff.mp hv, neg_one_smul]
  · left
    rw [Module.End.mem_eigenspace_iff.mp hv, one_smul]

theorem transCenter_of_mix (h2K : (2 : K) ≠ 0) {H : Subgroup (StatedSp r K)} {a : StatedSp r K}
    (haa : spEnd a * spEnd a = 1)
    (hpure : ∀ v, (spEnd a v = v ∨ spEnd a v = -v) → TransCenter H v)
    {p p' : Fin r ⊕ Fin r → K} (hp : spEnd a p = p) (hp' : spEnd a p' = -p') (hp0 : p ≠ 0)
    (hp'0 : p' ≠ 0) (hmix : TransCenter H (p + p')) : ∀ v, TransCenter H v := by
  have hspan := eigB_iSup h2K haa
  have horth := eigB_orth h2K a
  have hnd := restrict_nondegenerate_of_orth hspan horth
  have hpure' : ∀ i, ∀ c ∈ eigB (spEnd a) i, TransCenter H c := fun i c hc =>
    hpure c (eig_of_eigB hc)
  have hpm : p ∈ eigB (spEnd a) true := Module.End.mem_eigenspace_iff.mpr (by rw [hp, one_smul])
  have hpm' : p' ∈ eigB (spEnd a) false :=
    Module.End.mem_eigenspace_iff.mpr (by rw [hp', neg_one_smul])
  have main : ∀ y ∈ eigB (spEnd a) true, ∀ y' ∈ eigB (spEnd a) false, y ≠ 0 → y' ≠ 0 →
      TransCenter H (y + y') := by
    intro y hy y' hy' hy0 hy'0
    obtain ⟨g₁, hg₁, hg₁y, hg₁z⟩ := exists_mem_fixing_eq (hnd true) (hpure' true) hpm hy hp0 hy0
    obtain ⟨g₂, hg₂, hg₂y, hg₂z⟩ :=
      exists_mem_fixing_eq (hnd false) (hpure' false) hpm' hy' hp'0 hy'0
    have h1 : spEnd g₁ p' = p' := hg₁z p' fun c hc => horth false true (by simp) p' hpm' c hc
    have h2 : spEnd g₂ y = y := hg₂z y fun c hc => horth true false (by simp) y hy c hc
    have h := (hmix.map hg₁).map hg₂
    rwa [map_add, hg₁y, h1, map_add, h2, hg₂y] at h
  refine transCenter_of_pairs hspan horth hnd hpure' fun i j hij y hy y' hy' hy0 hy'0 => ?_
  cases i <;> cases j
  · exact absurd rfl hij
  · rw [add_comm]
    exact main y' hy' y hy hy'0 hy0
  · exact main y hy y' hy' hy0 hy'0
  · exact absurd rfl hij

theorem exists_eig_ne_zero {a : StatedSp r K}
    (haa : spEnd a * spEnd a = 1) (ha1 : proj r K a ≠ 1) :
    (∃ p, p ≠ 0 ∧ spEnd a p = p) ∧ ∃ p, p ≠ 0 ∧ spEnd a p = -p := by
  have hAA : ∀ v, spEnd a (spEnd a v) = v := fun v => by
    rw [← Module.End.mul_apply, haa, Module.End.one_apply]
  constructor
  · by_contra hcon
    push Not at hcon
    apply ha1
    refine proj_eq_one_of_spEnd_eq (Or.inr (LinearMap.ext fun v => ?_))
    have h := hcon (v + spEnd a v)
    rw [map_add, hAA] at h
    have h0 : v + spEnd a v = 0 := by_contra fun hne => h hne (add_comm _ _)
    change spEnd a v = -v
    linear_combination (norm := module) h0
  · by_contra hcon
    push Not at hcon
    apply ha1
    refine proj_eq_one_of_spEnd_eq (Or.inl (LinearMap.ext fun v => ?_))
    have h := hcon (v - spEnd a v)
    rw [map_sub, hAA, neg_sub] at h
    have h0 : v - spEnd a v = 0 := by_contra fun hne => h hne rfl
    change spEnd a v = v
    linear_combination (norm := module) -h0

theorem transCenter_of_comm_inv (h2K : (2 : K) ≠ 0) {E : Subgroup (StatedProj (StatedSp r K))}
    {a b : StatedSp r K} (ha : proj r K a ∈ E) (ha1 : proj r K a ≠ 1) (hb : proj r K b ∈ E)
    (hb1 : proj r K b ≠ 1) (hab : proj r K (a * b) ∈ E) (hab1 : proj r K (a * b) ≠ 1)
    (haa : spEnd a * spEnd a = 1) (hbb : spEnd b * spEnd b = 1)
    (hc : spEnd a * spEnd b = spEnd b * spEnd a) : ∀ v, TransCenter (cGen E) v := by
  classical
  set A := spEnd a with hA
  set B := spEnd b with hB
  let sg : Bool → K := fun i => cond i 1 (-1)
  have hsg : ∀ i, sg i = 1 ∨ sg i = -1 := fun i => by cases i <;> simp [sg]
  have hsg2 : ∀ i, sg i * sg i = 1 := fun i => by cases i <;> simp [sg]
  have hsgn : ∀ i j, i ≠ j → sg j = -sg i := fun i j hij => by
    cases i <;> cases j <;> first | exact absurd rfl hij | simp [sg]
  have hsgm : ∀ i j, i ≠ j → sg i * sg j ≠ 1 := fun i j hij => by
    rw [hsgn i j hij, mul_neg, hsg2]
    exact neg_one_ne_one_of_two h2K
  let Vs : Bool × Bool → Submodule K (Fin r ⊕ Fin r → K) := fun ij =>
    A.eigenspace (sg ij.1) ⊓ B.eigenspace (sg ij.2)
  have hBst : ∀ c : K, ∀ x ∈ A.eigenspace c, B x ∈ A.eigenspace c := fun c x hx => by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hx, map_smul]
  have hspan : ⨆ ij, Vs ij = ⊤ := by
    rw [iSup_prod, iSup_bool_eq, iSup_bool_eq, iSup_bool_eq]
    have h1 := eq_eig_sup_eig h2K hbb (A.eigenspace 1) (hBst 1)
    have h2 := eq_eig_sup_eig h2K hbb (A.eigenspace (-1)) (hBst (-1))
    have h3 := eigB_iSup h2K haa
    rw [iSup_bool_eq] at h3
    simp only [Vs, sg, cond_true, cond_false]
    rw [← h1, ← h2]
    exact h3
  have hpure : ∀ ij, ∀ c ∈ Vs ij, TransCenter (cGen E) c := by
    rintro ⟨i, j⟩ c hc
    refine transCenter_of_eig ha ha1 ?_
    have := Module.End.mem_eigenspace_iff.mp hc.1
    rcases hsg i with h | h <;> rw [h] at this
    · left; rwa [one_smul] at this
    · right; rwa [neg_one_smul] at this
  have horth : ∀ ij kl, ij ≠ kl → ∀ u ∈ Vs ij, ∀ v ∈ Vs kl, spForm r K u v = 0 := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne u hu v hv
    by_cases hik : i = k
    · have hjl : j ≠ l := fun h => hne (by rw [hik, h])
      exact spForm_eq_zero_of_eig b (Module.End.mem_eigenspace_iff.mp hu.2)
        (Module.End.mem_eigenspace_iff.mp hv.2) (hsgm j l hjl)
    · exact spForm_eq_zero_of_eig a (Module.End.mem_eigenspace_iff.mp hu.1)
        (Module.End.mem_eigenspace_iff.mp hv.1) (hsgm i k hik)
  have hnd := restrict_nondegenerate_of_orth hspan horth
  have heig : ∀ {g : StatedSp r K} {c : K} {y y' : Fin r ⊕ Fin r → K}, (c = 1 ∨ c = -1) →
      spEnd g y = c • y → spEnd g y' = c • y' → spEnd g (y + y') = y + y' ∨
        spEnd g (y + y') = -(y + y') := by
    intro g c y y' hc hy hy'
    rw [map_add, hy, hy', ← smul_add]
    rcases hc with rfl | rfl
    · left; rw [one_smul]
    · right; rw [neg_one_smul]
  refine transCenter_of_pairs hspan horth hnd hpure ?_
  rintro ⟨i, j⟩ ⟨k, l⟩ hne y hy y' hy' _ _
  by_cases hik : i = k
  · subst hik
    exact transCenter_of_eig ha ha1 (heig (hsg i) (Module.End.mem_eigenspace_iff.mp hy.1)
      (Module.End.mem_eigenspace_iff.mp hy'.1))
  by_cases hjl : j = l
  · subst hjl
    exact transCenter_of_eig hb hb1 (heig (hsg j) (Module.End.mem_eigenspace_iff.mp hy.2)
      (Module.End.mem_eigenspace_iff.mp hy'.2))
  · refine transCenter_of_eig hab hab1 (heig (c := sg i * sg j) ?_ ?_ ?_)
    · rcases hsg i with h | h <;> rcases hsg j with h' | h' <;> rw [h, h'] <;> simp
    · rw [spEnd_mul, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hy.2, map_smul,
        Module.End.mem_eigenspace_iff.mp hy.1, smul_smul, mul_comm]
    · rw [spEnd_mul, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hy'.2, map_smul,
        Module.End.mem_eigenspace_iff.mp hy'.1, smul_smul, hsgn i k hik, hsgn j l hjl]
      ring_nf

theorem transCenter_of_anti_inv (h2K : (2 : K) ≠ 0) {E : Subgroup (StatedProj (StatedSp r K))}
    {a b : StatedSp r K} (ha : proj r K a ∈ E) (ha1 : proj r K a ≠ 1) (hb : proj r K b ∈ E)
    (hb1 : proj r K b ≠ 1) (haa : spEnd a * spEnd a = 1) (hbb : spEnd b * spEnd b = 1)
    (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) : ∀ v, TransCenter (cGen E) v := by
  obtain ⟨⟨p, hp0, hp⟩, -⟩ := exists_eig_ne_zero haa ha1
  have hBB : ∀ v, spEnd b (spEnd b v) = v := fun v => by
    rw [← Module.End.mul_apply, hbb, Module.End.one_apply]
  have hBp : spEnd a (spEnd b p) = -spEnd b p := by
    rw [← Module.End.mul_apply, hc, LinearMap.neg_apply, Module.End.mul_apply, hp]
  have hBp0 : spEnd b p ≠ 0 := fun h => hp0 (by rw [← hBB p, h, map_zero])
  refine transCenter_of_mix h2K haa (fun v hv => transCenter_of_eig ha ha1 hv) hp hBp hp0 hBp0 ?_
  exact transCenter_of_eig hb hb1 (Or.inl (by rw [map_add, hBB, add_comm]))

theorem spForm_comb {T : Module.End K (Fin r ⊕ Fin r → K)} (hT : T * T = -1)
    (x : Fin r ⊕ Fin r → K) (s t : K) :
    spForm r K (s • x + t • T x) (T (s • x + t • T x)) =
      (s ^ 2 + t ^ 2) * spForm r K x (T x) := by
  have hTT : T (T x) = -x := by
    rw [← Module.End.mul_apply, hT, LinearMap.neg_apply, Module.End.one_apply]
  have h1 := spForm_isAlt.self_eq_zero x
  have h2 := spForm_isAlt.self_eq_zero (T x)
  have h3 := spForm_swap x (T x)
  have hTv : T (s • x + t • T x) = s • T x + t • (-x) := by rw [map_add, map_smul, map_smul, hTT]
  rw [hTv]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h1, h2, h3]
  ring

theorem exists_form_ne_zero_of_sq_neg_one (h2K : (2 : K) ≠ 0) {g : StatedSp r K}
    (hT : spEnd g * spEnd g = -1) {X : Submodule K (Fin r ⊕ Fin r → K)}
    (hX : ∀ x ∈ X, spEnd g x ∈ X) (hnd : ((spForm r K).restrict X).Nondegenerate)
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ X) (hw0 : w ≠ 0) :
    ∃ p ∈ X, spForm r K p (spEnd g p) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hTT : ∀ x, spEnd g (spEnd g x) = -x := fun x => by
    rw [← Module.End.mul_apply, hT, LinearMap.neg_apply, Module.End.one_apply]
  have hpol : ∀ p ∈ X, ∀ q ∈ X, spForm r K p (spEnd g q) = 0 := by
    intro p hp q hq
    have h1 := hcon (p + q) (X.add_mem hp hq)
    have h2 := hcon p hp
    have h3 := hcon q hq
    have h4 : spForm r K q (spEnd g p) = spForm r K p (spEnd g q) := by
      rw [← spEnd_isometry g q (spEnd g p), hTT, map_neg, spForm_swap (spEnd g q) p]
    simp only [map_add, LinearMap.add_apply] at h1
    have h5 : (2 : K) * spForm r K p (spEnd g q) = 0 := by linear_combination h1 - h2 - h3 - h4
    exact (mul_eq_zero.mp h5).resolve_left h2K
  apply hw0
  have h := hnd.1 ⟨w, hw⟩ fun z => by
    have hz : spEnd g (-spEnd g z) = z := by rw [map_neg, hTT, neg_neg]
    have := hpol w hw _ (X.neg_mem (hX _ z.2))
    rw [hz] at this
    exact this
  exact congrArg Subtype.val h

theorem mem_eigB_true {A : Module.End K (Fin r ⊕ Fin r → K)} {v : Fin r ⊕ Fin r → K} :
    v ∈ eigB A true ↔ A v = v := by
  rw [eigB, cond_true, Module.End.mem_eigenspace_iff, one_smul]

theorem mem_eigB_false {A : Module.End K (Fin r ⊕ Fin r → K)} {v : Fin r ⊕ Fin r → K} :
    v ∈ eigB A false ↔ A v = -v := by
  rw [eigB, cond_false, Module.End.mem_eigenspace_iff, neg_one_smul]

theorem transCenter_of_comm_neg [Finite K] (h2K : (2 : K) ≠ 0)
    {E : Subgroup (StatedProj (StatedSp r K))} {a b : StatedSp r K} (ha : proj r K a ∈ E)
    (ha1 : proj r K a ≠ 1) (hb : proj r K b ∈ E) (hb1 : proj r K b ≠ 1)
    (haa : spEnd a * spEnd a = 1) (hbb : spEnd b * spEnd b = -1)
    (hc : spEnd a * spEnd b = spEnd b * spEnd a) : ∀ v, TransCenter (cGen E) v := by
  have hspan := eigB_iSup h2K haa
  have horth := eigB_orth h2K a
  have hnd := restrict_nondegenerate_of_orth hspan horth
  have hBst : ∀ i, ∀ x ∈ eigB (spEnd a) i, spEnd b x ∈ eigB (spEnd a) i := by
    intro i x hx
    cases i
    · rw [mem_eigB_false] at hx ⊢
      rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hx, map_neg]
    · rw [mem_eigB_true] at hx ⊢
      rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hx]
  have hBB : ∀ x, spEnd b (spEnd b x) = -x := fun x => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  obtain ⟨⟨p₀, hp₀0, hp₀⟩, ⟨q₀, hq₀0, hq₀⟩⟩ := exists_eig_ne_zero haa ha1
  obtain ⟨p, hpX, hβ⟩ := exists_form_ne_zero_of_sq_neg_one h2K hbb (hBst true) (hnd true)
    (mem_eigB_true.mpr hp₀) hp₀0
  obtain ⟨p', hp'X, hβ'⟩ := exists_form_ne_zero_of_sq_neg_one h2K hbb (hBst false) (hnd false)
    (mem_eigB_false.mpr hq₀) hq₀0
  set β := spForm r K p (spEnd b p) with hβdef
  obtain ⟨s, t, hst⟩ := exists_sq_add_sq h2K hβ' hβ' β
  set p'' := s • p' + t • spEnd b p' with hp''
  have hp''X : p'' ∈ eigB (spEnd a) false :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hp'X) (Submodule.smul_mem _ _ (hBst false _ hp'X))
  have hQ : spForm r K p'' (spEnd b p'') = -β := by
    rw [hp'', spForm_comb hbb p' s t]
    linear_combination hst
  clear_value p''
  have hBpX := hBst true _ hpX
  have hBp''X := hBst false _ hp''X
  have o1 : spForm r K p (spEnd b p'') = 0 := horth true false (by simp) _ hpX _ hBp''X
  have o2 : spForm r K p'' (spEnd b p) = 0 := horth false true (by simp) _ hp''X _ hBpX
  have o3 : spForm r K p p'' = 0 := horth true false (by simp) _ hpX _ hp''X
  set w := p + p'' with hw
  clear_value w
  have hwBw : spForm r K w (spEnd b w) = 0 := by
    have e : spForm r K w (spEnd b w) = spForm r K p (spEnd b p) + spForm r K p (spEnd b p'') +
        (spForm r K p'' (spEnd b p) + spForm r K p'' (spEnd b p'')) := by
      rw [hw, map_add, map_add, LinearMap.add_apply, map_add, map_add]
    rw [e, o1, o2, hQ]
    ring
  have hcomm : spTransvection w 1 * spTransvection (spEnd b w) 1 =
      spTransvection (spEnd b w) 1 * spTransvection w 1 :=
    commute_spTransvection (by rw [spEnd_spTransvection, hwBw, mul_zero, zero_smul, add_zero]) 1
  set u := spTransvection w 1 * spTransvection (spEnd b w) 1 with hu
  have huC : u ∈ cGen E := by
    apply mem_cGen_of_commute hb hb1
    have hconj : b * u * b⁻¹ = u := by
      have e : b * u * b⁻¹ = (b * spTransvection w 1 * b⁻¹) *
          (b * spTransvection (spEnd b w) 1 * b⁻¹) := by rw [hu]; group
      rw [e, spTransvection_conj, spTransvection_conj, hBB, show -w = (-1 : K) • w by simp,
        spTransvection_smul]
      norm_num
      exact hcomm.symm
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hcen := (transCenter_of_eig ha ha1 (Or.inl (mem_eigB_true.mp hpX))).map huC
  have hBw : spForm r K p (spEnd b w) = β := by
    rw [hw, map_add, map_add, o1, add_zero]
  have hpw : spForm r K p w = 0 := by
    rw [hw, map_add, o3, spForm_isAlt.self_eq_zero, add_zero]
  have hwB : spForm r K (spEnd b w) w = 0 := by rw [spForm_swap, hwBw, neg_zero]
  have s1 : spEnd (spTransvection (spEnd b w) 1) p = p + β • spEnd b w := by
    rw [spEnd_spTransvection, hBw, one_mul]
  have s2 : spEnd (spTransvection w 1) (p + β • spEnd b w) = p + β • spEnd b w := by
    rw [spEnd_spTransvection, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpw,
      hwB, smul_zero, add_zero, mul_zero, zero_smul, add_zero]
  have hup : spEnd u p = (p + β • spEnd b p) + β • spEnd b p'' := by
    rw [hu, spEnd_mul, Module.End.mul_apply, s1, s2, hw, map_add, smul_add, add_assoc]
  rw [hup] at hcen
  have hAp : spEnd a (p + β • spEnd b p) = p + β • spEnd b p := by
    rw [map_add, map_smul, mem_eigB_true.mp hpX, mem_eigB_true.mp hBpX]
  have hAp' : spEnd a (β • spEnd b p'') = -(β • spEnd b p'') := by
    rw [map_smul, mem_eigB_false.mp hBp''X, smul_neg]
  have hn1 : p + β • spEnd b p ≠ 0 := by
    intro h0
    have hp_eq := eq_neg_of_add_eq_zero_left h0
    apply hβ
    calc spForm r K p (spEnd b p) = spForm r K (-(β • spEnd b p)) (spEnd b p) := by
          rw [← hp_eq]
      _ = 0 := by simp [spForm_isAlt.self_eq_zero]
  have hn2 : β • spEnd b p'' ≠ 0 := by
    refine smul_ne_zero hβ fun h0 => hβ ?_
    have h5 : spForm r K p'' (spEnd b p'') = 0 := by rw [h0, map_zero]
    rw [hQ] at h5
    exact neg_eq_zero.mp h5
  exact transCenter_of_mix h2K haa (fun v hv => transCenter_of_eig ha ha1 hv) hAp hAp' hn1 hn2 hcen

theorem transCenter_of_inv_lift [Finite K] (hr : 1 ≤ r) (h2K : (2 : K) ≠ 0)
    {E : Subgroup (StatedProj (StatedSp r K))} (hE : IsElemAbelian 2 E) {a b : StatedSp r K}
    (ha : proj r K a ∈ E) (ha1 : proj r K a ≠ 1) (hb : proj r K b ∈ E) (hb1 : proj r K b ≠ 1)
    (hab1 : proj r K (a * b) ≠ 1) (haa : spEnd a * spEnd a = 1) :
    ∀ v, TransCenter (cGen E) v := by
  have hab : proj r K (a * b) ∈ E := by rw [map_mul]; exact E.mul_mem ha hb
  have hcomm : proj r K a * proj r K b = proj r K b * proj r K a :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  rcases spEnd_sq_of_proj hr (hE.2 _ hb) with hbb | hbb <;>
    rcases spEnd_comm_of_proj hr hcomm with hc | hc
  · exact transCenter_of_comm_inv h2K ha ha1 hb hb1 hab hab1 haa hbb hc
  · exact transCenter_of_anti_inv h2K ha ha1 hb hb1 haa hbb hc
  · exact transCenter_of_comm_neg h2K ha ha1 hb hb1 haa hbb hc
  · have hBA : spEnd b * spEnd a = -(spEnd a * spEnd b) := by rw [hc, neg_neg]
    have hAA' : ∀ v, spEnd a (spEnd a v) = v := fun v => by
      rw [← Module.End.mul_apply, haa, Module.End.one_apply]
    have hBB' : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
      rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
    have hBA' : ∀ v, spEnd b (spEnd a v) = -(spEnd a (spEnd b v)) := fun v => by
      rw [← Module.End.mul_apply, hBA, LinearMap.neg_apply, Module.End.mul_apply]
    refine transCenter_of_anti_inv h2K ha ha1 hab hab1 haa ?_ ?_
    · rw [spEnd_mul]
      exact LinearMap.ext fun v => by
        simp only [Module.End.mul_apply, Module.End.one_apply, hBA', hBB', map_neg, neg_neg, hAA']
    · rw [spEnd_mul]
      exact LinearMap.ext fun v => by
        simp only [Module.End.mul_apply, LinearMap.neg_apply, hBA', map_neg, neg_neg, hAA']

theorem mem_four {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {x y z : G} (hx : x ∈ E) (hy : y ∈ E) (hz : z ∈ E) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) : z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hcon
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hxx : x * x = 1 := by rw [← sq]; exact hE.2 x hx
  have hxy1 : x * y ≠ 1 := fun h => hxy (mul_left_cancel (hxx.trans h.symm))
  have hxyx : x * y ≠ x := fun h => hy1 (mul_eq_left.mp h)
  have hxyy : x * y ≠ y := fun h => hx1 (mul_eq_right.mp h)
  set S : Finset G := {1, x, y, x * y, z} with hS
  have hcard : S.card = 5 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact Ne.symm hzxy
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hxyy, Ne.symm hzy⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hxyx, Ne.symm hzx⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1, Ne.symm hz1⟩
  have hsub : (S : Set G) ⊆ E := by
    intro w hw
    simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hx
    · exact hy
    · exact E.mul_mem hx hy
    · exact hz
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card E at hle
  omega

theorem spEnd_eq_or_neg_of_proj_eq (hr : 1 ≤ r) {g c : StatedSp r K}
    (h : proj r K g = proj r K c) : spEnd g = spEnd c ∨ spEnd g = -spEnd c := by
  have hm : g * c⁻¹ ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj, MonoidHom.mem_ker,
      map_mul, map_inv, h, mul_inv_cancel]
  have hg : g = g * c⁻¹ * c := by group
  rcases spEnd_eq_of_mem_spScalars hr hm with h1 | h1
  · left
    conv_lhs => rw [hg]
    rw [spEnd_mul, h1, one_mul]
  · right
    conv_lhs => rw [hg]
    rw [spEnd_mul, h1]
    exact LinearMap.ext fun v => by simp

theorem finrank_le_finrank_inf_ker_add_one (X : Submodule K (Fin r ⊕ Fin r → K))
    (f : (Fin r ⊕ Fin r → K) →ₗ[K] K) :
    Module.finrank K X ≤ Module.finrank K ↥(X ⊓ LinearMap.ker f) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : Module.finrank K (LinearMap.range f) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  have h4 := Submodule.finrank_le (X ⊔ LinearMap.ker f)
  omega

theorem exists_ne_zero_of_finrank_pos {X : Submodule K (Fin r ⊕ Fin r → K)}
    (h : 0 < Module.finrank K X) : ∃ u ∈ X, u ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot fun hb => by rw [hb, finrank_bot] at h; omega

theorem exists_isotropic_of_quat [Finite K] (hr : 3 ≤ r) (h2K : (2 : K) ≠ 0)
    {E : Subgroup (StatedProj (StatedSp r K))} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    {a b : StatedSp r K} (ha : proj r K a ∈ E) (hb : proj r K b ∈ E) (ha1 : proj r K a ≠ 1)
    (hb1 : proj r K b ≠ 1) (hab : proj r K a ≠ proj r K b)
    (haa : spEnd a * spEnd a = -1) (hbb : spEnd b * spEnd b = -1)
    (hc : spEnd a * spEnd b = -(spEnd b * spEnd a)) :
    ∃ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) ∧
      ∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W := by
  classical
  have hr1 : 1 ≤ r := by omega
  set A := spEnd a with hAdef
  set B := spEnd b with hBdef
  set C := spEnd (a * b) with hCdef
  have hCv : ∀ v, C v = A (B v) := fun v => by rw [hCdef, spEnd_mul, Module.End.mul_apply]
  have hAA : ∀ v, A (A v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, B (B v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  have hBA : ∀ v, B (A v) = -(A (B v)) := fun v => by
    rw [← Module.End.mul_apply, show B * A = -(A * B) by rw [hc, neg_neg],
      LinearMap.neg_apply, Module.End.mul_apply]
  have hCC : ∀ v, C (C v) = -v := fun v => by
    simp only [hCv, hBA, hBB, hAA, map_neg, neg_neg]
  obtain ⟨x₀, y₀, hxy⟩ := exists_sq_add_sq h2K one_ne_zero one_ne_zero (1 : K)
  set S : Module.End K (Fin r ⊕ Fin r → K) := x₀ • A + y₀ • B with hSdef
  have hSv : ∀ v, S v = x₀ • A v + y₀ • B v := fun v => by
    rw [hSdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  have hSS : S * S = 1 := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, Module.End.one_apply, hSv, hSv, map_add, map_add, map_smul,
      map_smul, map_smul, map_smul, hAA, hBB, hBA]
    linear_combination (norm := module) (-hxy) • v
  have hSC : ∀ v, S (C v) = -(C (S v)) := fun v => by
    simp only [hSv, hCv, map_add, map_smul, map_neg, hAA, hBA, hBB, neg_neg]
    module
  set U := eigB S true with hUdef
  set U' := eigB S false with hU'def
  have hAu : ∀ u ∈ U, A u = -x₀ • u + y₀ • C u := fun u hu => by
    have h := congrArg A (mem_eigB_true.mp hu)
    rw [hSv, map_add, map_smul, map_smul, hAA, ← hCv] at h
    rw [← h]
    module
  have hBu : ∀ u ∈ U, B u = -x₀ • C u - y₀ • u := fun u hu => by
    have h := congrArg B (mem_eigB_true.mp hu)
    rw [hSv, map_add, map_smul, map_smul, hBA, hBB, ← hCv] at h
    rw [← h]
    module
  have hACu : ∀ u ∈ U, A (C u) = x₀ • C u + y₀ • u := fun u hu => by
    conv_lhs => rw [hCv, hAA, hBu u hu]
    module
  have hBCu : ∀ u ∈ U, B (C u) = A u := fun u hu => by
    rw [hCv, hBA, hBB, map_neg, neg_neg]
  have hstab : ∀ u ∈ U, ∀ g : StatedSp r K, proj r K g ∈ E →
      ∀ w ∈ Submodule.span K {u, C u}, spEnd g w ∈ Submodule.span K {u, C u} := by
    intro u hu g hg w hw
    set W := Submodule.span K {u, C u} with hW
    have hu' : u ∈ W := Submodule.subset_span (by simp)
    have hCu' : C u ∈ W := Submodule.subset_span (by simp)
    have hT : ∀ T : Module.End K (Fin r ⊕ Fin r → K), T u ∈ W → T (C u) ∈ W →
        ∀ w ∈ W, T w ∈ W := by
      intro T h1 h2 w hw
      have hle : W ≤ W.comap T := by
        rw [hW, Submodule.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact h1
        · exact h2
      exact hle hw
    have hTn : ∀ T : Module.End K (Fin r ⊕ Fin r → K), (∀ w ∈ W, T w ∈ W) →
        (spEnd g = T ∨ spEnd g = -T) → spEnd g w ∈ W := by
      intro T hTW hgT
      rcases hgT with h | h
      · rw [h]; exact hTW w hw
      · rw [h, LinearMap.neg_apply]; exact W.neg_mem (hTW w hw)
    have hAW := hT A (by rw [hAu u hu]; exact W.add_mem (W.smul_mem _ hu') (W.smul_mem _ hCu'))
      (by rw [hACu u hu]; exact W.add_mem (W.smul_mem _ hCu') (W.smul_mem _ hu'))
    have hBW := hT B (by rw [hBu u hu]; exact W.sub_mem (W.smul_mem _ hCu') (W.smul_mem _ hu'))
      (by rw [hBCu u hu, hAu u hu]; exact W.add_mem (W.smul_mem _ hu') (W.smul_mem _ hCu'))
    have hCW := hT C hCu' (by rw [hCC]; exact W.neg_mem hu')
    have h1W := hT 1 hu' hCu'
    rcases mem_four hE h4 ha hb hg ha1 hb1 hab with h | h | h | h
    · have h1 := spEnd_eq_or_neg_of_proj_eq hr1 (c := 1) (by rw [h, map_one])
      rw [spEnd_one] at h1
      exact hTn 1 h1W h1
    · exact hTn A hAW (spEnd_eq_or_neg_of_proj_eq hr1 h)
    · exact hTn B hBW (spEnd_eq_or_neg_of_proj_eq hr1 h)
    · exact hTn C hCW (spEnd_eq_or_neg_of_proj_eq hr1 (c := a * b) (by rw [h, map_mul]))
  have hCiso : ∀ v w, spForm r K (C v) (C w) = spForm r K v w := spEnd_isometry (a * b)
  have hsymm : ∀ v w, spForm r K v (C w) = spForm r K w (C v) := fun v w => by
    rw [← hCiso w (C v), hCC, map_neg, spForm_swap (C w) v]
  by_contra hcon
  have haniso : ∀ u ∈ U, u ≠ 0 → spForm r K u (C u) ≠ 0 := by
    intro u hu hu0 h0
    refine hcon ⟨Submodule.span K {u, C u}, ?_, ?_, hstab u hu⟩
    · intro hbot
      apply hu0
      have : u ∈ Submodule.span K {u, C u} := Submodule.subset_span (by simp)
      rw [hbot] at this
      exact (Submodule.mem_bot K).mp this
    · intro x hx y hy
      obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨c₂, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
      have e1 := spForm_isAlt.self_eq_zero u
      have e2 := spForm_isAlt.self_eq_zero (C u)
      have e3 : spForm r K (C u) u = 0 := by rw [spForm_swap, h0, neg_zero]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1,
        e2, e3, h0]
      ring
  have hUU' : U ⊔ U' = ⊤ := by
    have := eigB_iSup h2K hSS
    rwa [iSup_bool_eq] at this
  have hdisj : U ⊓ U' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨h1, h2⟩
    rw [SetLike.mem_coe, mem_eigB_true] at h1
    rw [SetLike.mem_coe, mem_eigB_false] at h2
    have h3 : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [h2, neg_add_cancel]
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3).resolve_left h2K)
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq U U'
  rw [hUU', hdisj, finrank_top, finrank_bot, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin] at hfr
  have hCU : ∀ u ∈ U, C u ∈ U' := fun u hu => by
    rw [mem_eigB_false, hSC, mem_eigB_true.mp hu]
  have hCU' : ∀ u ∈ U', C u ∈ U := fun u hu => by
    rw [mem_eigB_true, hSC, mem_eigB_false.mp hu, map_neg, neg_neg]
  have hCinj : Function.Injective C := fun v w h => by
    have := congrArg C h
    rw [hCC, hCC] at this
    exact neg_inj.mp this
  have hle1 := LinearMap.finrank_le_finrank_of_injective (f := C.restrict hCU)
    fun v w h => Subtype.ext (hCinj (congrArg Subtype.val h))
  have hle2 := LinearMap.finrank_le_finrank_of_injective (f := C.restrict hCU')
    fun v w h => Subtype.ext (hCinj (congrArg Subtype.val h))
  have hdimU : Module.finrank K U = r := by omega
  set f : (Fin r ⊕ Fin r → K) → ((Fin r ⊕ Fin r → K) →ₗ[K] K) :=
    fun u => (spForm r K u).comp C with hf
  have hfv : ∀ u v, f u v = spForm r K u (C v) := fun u v => rfl
  obtain ⟨u₁, hu₁, hu₁0⟩ := exists_ne_zero_of_finrank_pos (X := U) (by omega)
  have hk1 := finrank_le_finrank_inf_ker_add_one U (f u₁)
  obtain ⟨u₂, hu₂, hu₂0⟩ := exists_ne_zero_of_finrank_pos (X := U ⊓ LinearMap.ker (f u₁))
    (by omega)
  have hk2 := finrank_le_finrank_inf_ker_add_one (U ⊓ LinearMap.ker (f u₁)) (f u₂)
  obtain ⟨u₃, hu₃, hu₃0⟩ := exists_ne_zero_of_finrank_pos
    (X := U ⊓ LinearMap.ker (f u₁) ⊓ LinearMap.ker (f u₂)) (by omega)
  have hu₂U : u₂ ∈ U := hu₂.1
  have hu₃U : u₃ ∈ U := hu₃.1.1
  have b12 : spForm r K u₁ (C u₂) = 0 := by rw [← hfv]; exact LinearMap.mem_ker.mp hu₂.2
  have b13 : spForm r K u₁ (C u₃) = 0 := by rw [← hfv]; exact LinearMap.mem_ker.mp hu₃.1.2
  have b23 : spForm r K u₂ (C u₃) = 0 := by rw [← hfv]; exact LinearMap.mem_ker.mp hu₃.2
  have b21 : spForm r K u₂ (C u₁) = 0 := by rw [hsymm, b12]
  have b31 : spForm r K u₃ (C u₁) = 0 := by rw [hsymm, b13]
  have b32 : spForm r K u₃ (C u₂) = 0 := by rw [hsymm, b23]
  have n1 := haniso u₁ hu₁ hu₁0
  have n2 := haniso u₂ hu₂U hu₂0
  have n3 := haniso u₃ hu₃U hu₃0
  obtain ⟨s, t, hst⟩ := exists_sq_add_sq h2K n1 n2 (spForm r K u₃ (C u₃))
  set u := s • u₁ + t • u₂ + u₃ with hu
  have huU : u ∈ U := U.add_mem (U.add_mem (U.smul_mem _ hu₁) (U.smul_mem _ hu₂U)) hu₃U
  have hu0 : u ≠ 0 := by
    intro h0
    have e1 : spForm r K u₁ (C u) = 0 := by rw [h0, map_zero, map_zero]
    have e2 : spForm r K u₂ (C u) = 0 := by rw [h0, map_zero, map_zero]
    rw [hu] at e1 e2
    simp only [map_add, map_smul, smul_eq_mul, b12, b13, b21, b23, mul_zero, add_zero,
      zero_add] at e1 e2
    have hs : s = 0 := (mul_eq_zero.mp e1).resolve_right n1
    have ht : t = 0 := (mul_eq_zero.mp e2).resolve_right n2
    apply hu₃0
    rw [← h0, hu, hs, ht, zero_smul, zero_smul, zero_add, zero_add]
  apply haniso u huU hu0
  rw [hu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, b12, b13,
    b21, b23, b31, b32]
  linear_combination hst

end SpSeitz

open SpSeitz

@[expose] def SeitzFourSp4Q8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) ≠ 0 → Nat.card K ≠ 3 →
    ∀ E : Subgroup (StatedProj (StatedSp 2 K)), IsElemAbelian 2 E → Nat.card E = 4 →
    (∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), (∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0) →
      (∀ g : StatedSp 2 K, proj 2 K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥) →
    ∀ a b : StatedSp 2 K, proj 2 K a ∈ E → proj 2 K b ∈ E → proj 2 K a ≠ 1 → proj 2 K b ≠ 1 →
      proj 2 K a ≠ proj 2 K b → spEnd a * spEnd a = -1 → spEnd b * spEnd b = -1 →
      spEnd a * spEnd b = -(spEnd b * spEnd a) →
    (⊤ : Subgroup (StatedProj (StatedSp 2 K))) ≤
      ⨆ x ∈ E, ⨆ (_ : x ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({x} : Set _)

theorem seitzFourSpAniso_of_sp4Q8 (hQ : SeitzFourSp4Q8) : SeitzFourSpAniso := by
  intro K _ _ r hr h2K hexc E hE h4 hA
  classical
  have hr1 : 1 ≤ r := by omega
  have hproj := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    (r := r) (K := K)
  have h4' : Nat.card E = 2 ^ 2 := h4
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    have hne : E ≠ ⊥ := by rintro h; rw [h, Subgroup.card_bot] at h4; norm_num at h4
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨y, hyE, hyx⟩ :=
    CFSG.LieType.SeitzGeneration.exists_notMem_zpowers_of_card_sq Nat.prime_two hE.2 h4' hxE hx1
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers _)
  have hxy1 : x * y ≠ 1 := fun h => hyx (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  have hcomm : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩)
  have hxx : x * x = 1 := by rw [← sq]; exact hE.2 x hxE
  have hyy : y * y = 1 := by rw [← sq]; exact hE.2 y hyE
  obtain ⟨a, rfl⟩ := hproj x
  obtain ⟨b, rfl⟩ := hproj y
  have key : (∀ v, TransCenter (cGen E) v) → (⊤ : Subgroup (StatedProj (StatedSp r K))) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _) := by
    intro hv k _
    obtain ⟨g, rfl⟩ := hproj k
    have htop := eq_top_of_transCenter hv
    have hg : g ∈ cGen E := htop ▸ mem_top g
    exact hg
  rcases spEnd_sq_of_proj hr1 (hE.2 _ hxE) with haa | haa
  · exact key (transCenter_of_inv_lift hr1 h2K hE hxE hx1 hyE hy1 (by rwa [map_mul]) haa)
  rcases spEnd_sq_of_proj hr1 (hE.2 _ hyE) with hbb | hbb
  · exact key (transCenter_of_inv_lift hr1 h2K hE hyE hy1 hxE hx1
      (by rw [map_mul, ← hcomm]; exact hxy1) hbb)
  have hAA : ∀ v, spEnd a (spEnd a v) = -v := fun v => by
    rw [← Module.End.mul_apply, haa, LinearMap.neg_apply, Module.End.one_apply]
  have hBB : ∀ v, spEnd b (spEnd b v) = -v := fun v => by
    rw [← Module.End.mul_apply, hbb, LinearMap.neg_apply, Module.End.one_apply]
  rcases spEnd_comm_of_proj hr1 hcomm with hc | hc
  · have hBA : ∀ v, spEnd b (spEnd a v) = spEnd a (spEnd b v) := fun v => by
      rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply]
    refine key (transCenter_of_inv_lift (a := a * b) (b := a) hr1 h2K hE
      (by rw [map_mul]; exact E.mul_mem hxE hyE) (by rwa [map_mul]) hxE hx1 ?_ ?_)
    · rw [map_mul, map_mul, mul_assoc, ← hcomm, ← mul_assoc, hxx, one_mul]
      exact hy1
    · rw [spEnd_mul]
      exact LinearMap.ext fun v => by
        simp only [Module.End.mul_apply, Module.End.one_apply, hBA, hAA, hBB, map_neg, neg_neg]
  · by_cases hr3 : 3 ≤ r
    · exfalso
      obtain ⟨W, hW0, hWi, hWs⟩ := exists_isotropic_of_quat hr3 h2K hE h4 hxE hyE hx1 hy1 hxy haa
        hbb hc
      exact hW0 (hA W hWi hWs)
    · obtain rfl : r = 2 := by omega
      exact hQ K h2K (fun h3 => hexc ⟨rfl, h3⟩) E hE h4 hA a b hxE hyE hx1 hy1 hxy haa hbb hc

theorem seitzFourInner_psp_of_sp4Q8 (hQ : SeitzFourSp4Q8) :
    SeitzFourInner fun X _ => ∃ n p f : ℕ, 2 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSp n p f :=
  seitzFourInner_psp_of_aniso (seitzFourSpAniso_of_sp4Q8 hQ)

end CFSG.LocalAnalysis.WeakClosure81
