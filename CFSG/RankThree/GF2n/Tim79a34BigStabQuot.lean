module

public import CFSG.LieType.SeitzGeneration.SpSubEmb
public import CFSG.Timmesfeld.Transvection.ModelSpRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

section SpFix

open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped Matrix

@[expose] def spFix {n : ℕ} {F : Type} [Field F] (a : Fin n ⊕ Fin n → F) :
    Subgroup (StatedSp n F) where
  carrier := {g | SpExtras.mat n F g *ᵥ a = a}
  mul_mem' := by
    intro g h hg hh
    show SpExtras.mat n F (g * h) *ᵥ a = a
    rw [map_mul, ← Matrix.mulVec_mulVec]
    have hh' : SpExtras.mat n F h *ᵥ a = a := hh
    have hg' : SpExtras.mat n F g *ᵥ a = a := hg
    rw [hh', hg']
  one_mem' := by
    show SpExtras.mat n F 1 *ᵥ a = a
    rw [map_one, Matrix.one_mulVec]
  inv_mem' := by
    intro g hg
    show SpExtras.mat n F g⁻¹ *ᵥ a = a
    have hg' : SpExtras.mat n F g *ᵥ a = a := hg
    have h1 : SpExtras.mat n F g⁻¹ *ᵥ (SpExtras.mat n F g *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rwa [hg'] at h1

theorem mem_spFix_iff {n : ℕ} {F : Type} [Field F] {a : Fin n ⊕ Fin n → F} {g : StatedSp n F} :
    g ∈ spFix a ↔ SpExtras.mat n F g *ᵥ a = a := Iff.rfl

end SpFix

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.SeitzGeneration
open CFSG.RankThree.Classical (spEnd spLin)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)
open CFSG.RankThree.PartOne.CTP (spEnd_isometry)
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup)

section Setup

variable {n m : ℕ} {F : Type} [Field F]

noncomputable abbrev spQuotB (n : ℕ) (F : Type) [Field F] :
    LinearMap.BilinForm F (Fin n ⊕ Fin n → F) :=
  CFSG.RankThree.Classical.spForm n F

theorem spQuotB_eq (u v : Fin n ⊕ Fin n → F) : spQuotB n F u v = CaseM.spForm u v := by
  rw [spQuotB, CFSG.RankThree.Classical.spForm_apply]
  rfl

theorem spQuotB_self (x : Fin n ⊕ Fin n → F) : spQuotB n F x x = 0 :=
  CFSG.RankThree.Classical.spForm_isAlt x

theorem spQuotB_comm (x y : Fin n ⊕ Fin n → F) : spQuotB n F y x = - spQuotB n F x y :=
  (CFSG.RankThree.Classical.spForm_isAlt.neg_eq x y).symm

structure SpQuotData (n m : ℕ) (F : Type) [Field F] where
  e : SpSubEmb n m F
  a : Fin n ⊕ Fin n → F
  b : Fin n ⊕ Fin n → F
  hab : spQuotB n F a b = 1
  mem_U : ∀ u, u ∈ e.U ↔ spQuotB n F a u = 0 ∧ spQuotB n F b u = 0

namespace SpQuotData

variable (Q : SpQuotData n m F)

theorem form_a_a : spQuotB n F Q.a Q.a = 0 := spQuotB_self _

theorem form_b_b : spQuotB n F Q.b Q.b = 0 := spQuotB_self _

theorem form_b_a : spQuotB n F Q.b Q.a = -1 := by
  rw [spQuotB_comm Q.a Q.b, Q.hab]

theorem form_a_of_mem {u : Fin n ⊕ Fin n → F} (hu : u ∈ Q.e.U) : spQuotB n F Q.a u = 0 :=
  ((Q.mem_U u).1 hu).1

theorem form_b_of_mem {u : Fin n ⊕ Fin n → F} (hu : u ∈ Q.e.U) : spQuotB n F Q.b u = 0 :=
  ((Q.mem_U u).1 hu).2

theorem form_of_mem_a {u : Fin n ⊕ Fin n → F} (hu : u ∈ Q.e.U) : spQuotB n F u Q.a = 0 := by
  rw [spQuotB_comm, Q.form_a_of_mem hu, neg_zero]

theorem form_of_mem_b {u : Fin n ⊕ Fin n → F} (hu : u ∈ Q.e.U) : spQuotB n F u Q.b = 0 := by
  rw [spQuotB_comm, Q.form_b_of_mem hu, neg_zero]

@[expose] noncomputable def pr : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) :=
  LinearMap.id - ((spQuotB n F).flip Q.b).smulRight Q.a - (spQuotB n F Q.a).smulRight Q.b

theorem pr_apply (v : Fin n ⊕ Fin n → F) :
    Q.pr v = v - spQuotB n F v Q.b • Q.a - spQuotB n F Q.a v • Q.b := by
  simp [pr]

theorem pr_mem (v : Fin n ⊕ Fin n → F) : Q.pr v ∈ Q.e.U := by
  rw [Q.mem_U, pr_apply]
  constructor
  · simp only [map_sub, map_smul, smul_eq_mul, Q.form_a_a, Q.hab]
    ring
  · simp only [map_sub, map_smul, smul_eq_mul, Q.form_b_b, Q.form_b_a, spQuotB_comm v Q.b]
    ring

theorem pr_of_mem {u : Fin n ⊕ Fin n → F} (hu : u ∈ Q.e.U) : Q.pr u = u := by
  rw [pr_apply, Q.form_of_mem_b hu, Q.form_a_of_mem hu]
  simp

theorem pr_a : Q.pr Q.a = 0 := by
  rw [pr_apply, Q.form_a_a, Q.hab]
  simp

theorem pr_of_form_eq_zero {v : Fin n ⊕ Fin n → F} (hv : spQuotB n F Q.a v = 0) :
    Q.pr v = v - spQuotB n F v Q.b • Q.a := by
  rw [pr_apply, hv]
  simp

theorem spEnd_a {g : StatedSp n F} (hg : g ∈ spFix Q.a) : spEnd g Q.a = Q.a := hg

theorem form_a_spEnd {g : StatedSp n F} (hg : g ∈ spFix Q.a) {v : Fin n ⊕ Fin n → F}
    (hv : spQuotB n F Q.a v = 0) : spQuotB n F Q.a (spEnd g v) = 0 := by
  have h := spEnd_isometry g Q.a v
  rwa [Q.spEnd_a hg, hv] at h

theorem pr_spEnd {g : StatedSp n F} (hg : g ∈ spFix Q.a) {v : Fin n ⊕ Fin n → F}
    (hv : spQuotB n F Q.a v = 0) :
    Q.pr (spEnd g v) = spEnd g v - spQuotB n F (spEnd g v) Q.b • Q.a :=
  Q.pr_of_form_eq_zero (Q.form_a_spEnd hg hv)

@[expose] noncomputable def qEnd (g : StatedSp n F) : Module.End F (Fin m ⊕ Fin m → F) :=
  Q.e.φ.symm.toLinearMap ∘ₗ
    (Q.pr ∘ₗ spEnd g ∘ₗ Q.e.U.subtype ∘ₗ Q.e.φ.toLinearMap).codRestrict Q.e.U
      (fun x => Q.pr_mem _)

theorem φ_qEnd (g : StatedSp n F) (x : Fin m ⊕ Fin m → F) :
    (Q.e.φ (Q.qEnd g x) : Fin n ⊕ Fin n → F) = Q.pr (spEnd g (Q.e.φ x)) := by
  simp [qEnd]

theorem qEnd_one : Q.qEnd (1 : StatedSp n F) = 1 := by
  refine LinearMap.ext fun x => ?_
  apply Q.e.φ.injective
  apply Subtype.ext
  rw [Q.φ_qEnd, spEnd_one, Module.End.one_apply, Q.pr_of_mem (Q.e.φ x).2]
  rfl

theorem qEnd_mul {g h : StatedSp n F} (hg : g ∈ spFix Q.a) (hh : h ∈ spFix Q.a) :
    Q.qEnd (g * h) = Q.qEnd g * Q.qEnd h := by
  refine LinearMap.ext fun x => ?_
  apply Q.e.φ.injective
  apply Subtype.ext
  rw [Module.End.mul_apply, Q.φ_qEnd, Q.φ_qEnd, Q.φ_qEnd, spEnd_mul, Module.End.mul_apply,
    Q.pr_spEnd hh (Q.form_a_of_mem (Q.e.φ x).2), map_sub, map_smul, Q.spEnd_a hg]
  simp [Q.pr_a]

theorem qEnd_isometry {g : StatedSp n F} (hg : g ∈ spFix Q.a) (x y : Fin m ⊕ Fin m → F) :
    spQuotB m F (Q.qEnd g x) (Q.qEnd g y) = spQuotB m F x y := by
  rw [← Q.e.form_φ, ← Q.e.form_φ x y, Q.φ_qEnd, Q.φ_qEnd]
  have hx := Q.form_a_spEnd hg (Q.form_a_of_mem (Q.e.φ x).2)
  have hy := Q.form_a_spEnd hg (Q.form_a_of_mem (Q.e.φ y).2)
  rw [Q.pr_spEnd hg (Q.form_a_of_mem (Q.e.φ x).2), Q.pr_spEnd hg (Q.form_a_of_mem (Q.e.φ y).2)]
  have hxa : spQuotB n F (spEnd g (Q.e.φ x)) Q.a = 0 := by
    rw [spQuotB_comm, hx, neg_zero]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hx, hy,
    hxa, Q.form_a_a, spEnd_isometry]
  ring

@[expose] noncomputable def qHomEnd : spFix Q.a →* Module.End F (Fin m ⊕ Fin m → F) where
  toFun g := Q.qEnd g.1
  map_one' := Q.qEnd_one
  map_mul' g h := Q.qEnd_mul g.2 h.2

theorem qHomEnd_mem (g : spFix Q.a) :
    Q.qHomEnd.toHomUnits g ∈ sesqUnitaryGroup (spQuotB m F) :=
  fun x y => Q.qEnd_isometry g.2 x y

@[expose] noncomputable def qHom : spFix Q.a →* StatedSp m F :=
  (spLinEquiv m F).symm.toMonoidHom.comp (Q.qHomEnd.toHomUnits.codRestrict _ Q.qHomEnd_mem)

theorem spEnd_qHom (g : spFix Q.a) (x : Fin m ⊕ Fin m → F) :
    spEnd (Q.qHom g) x = Q.qEnd g.1 x := by
  have h : spLin m F (Q.qHom g) = Q.qHomEnd.toHomUnits g :=
    spLin_spLinEquiv_symm (r := m) (K := F) _
  change ((spLin m F (Q.qHom g) : LinearMap.GeneralLinearGroup F (Fin m ⊕ Fin m → F)) :
    Module.End F (Fin m ⊕ Fin m → F)) x = _
  rw [h]
  rfl

theorem qHom_surjective : Function.Surjective Q.qHom := by
  intro h
  have hW : Q.a ∈ Q.e.W := fun u hu => Q.form_of_mem_a hu
  have hg : Q.e.ext h ∈ spFix Q.a := Q.e.spEnd_ext_of_mem_orth h hW
  refine ⟨⟨Q.e.ext h, hg⟩, ?_⟩
  rw [SpSubEmb.ext_eq_iff]
  refine LinearMap.ext fun x => ?_
  rw [Q.spEnd_qHom]
  apply Q.e.φ.injective
  apply Subtype.ext
  rw [Q.φ_qEnd, Q.e.spEnd_ext_of_mem, Q.pr_of_mem (Q.e.φ _).2]

theorem qHom_eq_one_iff (g : spFix Q.a) : Q.qHom g = 1 ↔ (g : StatedSp n F) ∈ spRad Q.a := by
  constructor
  · intro h
    have hker : ∀ u ∈ Q.e.U, Q.pr (spEnd (g : StatedSp n F) u) = u := by
      intro u hu
      obtain ⟨x, rfl⟩ : ∃ x, (Q.e.φ x : Fin n ⊕ Fin n → F) = u :=
        ⟨Q.e.φ.symm ⟨u, hu⟩, by simp⟩
      have h1 := Q.spEnd_qHom g x
      rw [h, spEnd_one, Module.End.one_apply] at h1
      rw [← Q.φ_qEnd, ← h1]
    refine ⟨g.2, fun v hv => ?_⟩
    have hv' : spQuotB n F Q.a v = 0 := by rw [spQuotB_eq]; exact hv
    have hu := Q.pr_mem v
    have h1 := hker _ hu
    rw [Q.pr_spEnd g.2 (Q.form_a_of_mem hu)] at h1
    have h2 : Q.pr v = v - spQuotB n F v Q.b • Q.a := Q.pr_of_form_eq_zero hv'
    have h3 : v = Q.pr v + spQuotB n F v Q.b • Q.a := by rw [h2]; abel
    have h4 : spEnd (g : StatedSp n F) v =
        spEnd (g : StatedSp n F) (Q.pr v) + spQuotB n F v Q.b • spEnd (g : StatedSp n F) Q.a := by
      conv_lhs => rw [h3]
      rw [map_add, map_smul]
    refine ⟨spQuotB n F (spEnd (g : StatedSp n F) (Q.pr v)) Q.b, ?_⟩
    show spEnd (g : StatedSp n F) v = _
    rw [h4, Q.spEnd_a g.2]
    linear_combination (norm := module) h1 + h2
  · intro hg
    rw [SpSubEmb.ext_eq_iff, spEnd_one]
    refine LinearMap.ext fun x => ?_
    rw [Q.spEnd_qHom]
    apply Q.e.φ.injective
    apply Subtype.ext
    rw [Q.φ_qEnd]
    obtain ⟨c, hc⟩ := hg.2 (Q.e.φ x) (by rw [← spQuotB_eq]; exact Q.form_a_of_mem (Q.e.φ x).2)
    change spEnd (g : StatedSp n F) (Q.e.φ x) = _ at hc
    rw [hc, map_add, map_smul, Q.pr_a, Q.pr_of_mem (Q.e.φ x).2]
    simp

theorem qHom_ker : (Q.qHom).ker = (spRad Q.a).subgroupOf (spFix Q.a) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact Q.qHom_eq_one_iff g

end SpQuotData

end Setup

section Existence

variable {n : ℕ} {F : Type} [Field F]

theorem spQuot_range_pair {V : Type} (a b : V) : Set.range ![a, b] = {a, b} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem spQuot_exists_data (hn : 2 ≤ n) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    ∃ Q : SpQuotData n (n - 1) F, Q.a = a := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have hab : spQuotB n F a b = 1 := by rw [spQuotB_eq]; exact hb
  have haa : spQuotB n F a a = 0 := spQuotB_self a
  have hbb : spQuotB n F b b = 0 := spQuotB_self b
  have hba : spQuotB n F b a = -1 := by rw [spQuotB_comm a b, hab]
  have hrefl : (spQuotB n F).IsRefl := CFSG.RankThree.Classical.spForm_isAlt.isRefl
  have hnd : (spQuotB n F).Nondegenerate := CFSG.RankThree.Classical.spForm_nondegenerate
  set Hy : Submodule F (Fin n ⊕ Fin n → F) := Submodule.span F (Set.range ![a, b]) with hHy
  have hmemHy : ∀ x, x ∈ Hy ↔ ∃ c d : F, c • a + d • b = x := by
    intro x
    rw [hHy, spQuot_range_pair, Submodule.mem_span_pair]
  set U : Submodule F (Fin n ⊕ Fin n → F) := (spQuotB n F).orthogonal Hy with hUdef
  have hmemU : ∀ u, u ∈ U ↔ spQuotB n F a u = 0 ∧ spQuotB n F b u = 0 := by
    intro u
    rw [hUdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h a ((hmemHy a).2 ⟨1, 0, by simp⟩), h b ((hmemHy b).2 ⟨0, 1, by simp⟩)⟩
    · rintro ⟨h1, h2⟩ x hx
      obtain ⟨c, d, rfl⟩ := (hmemHy x).1 hx
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
        h2]
      ring
  have hdisj : Disjoint Hy U := by
    rw [Submodule.disjoint_def]
    intro x hxH hxU
    obtain ⟨c, d, rfl⟩ := (hmemHy x).1 hxH
    obtain ⟨h1, h2⟩ := (hmemU _).1 hxU
    simp only [map_add, map_smul, smul_eq_mul, haa, hab, hba, hbb] at h1 h2
    have hd : d = 0 := by linear_combination h1
    have hc : c = 0 := by linear_combination -h2
    rw [hc, hd]
    simp
  have hcompl : IsCompl Hy U := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hdisj
  have horth : (spQuotB n F).orthogonal U = Hy :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl Hy
  have hcomplU : IsCompl U ((spQuotB n F).orthogonal U) := by
    rw [horth]
    exact hcompl.symm
  have hUnd : ((spQuotB n F).restrict U).Nondegenerate :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl).2 hcomplU
  obtain ⟨m, e, heU, hm⟩ := SpSubEmb.exists hUnd
  have hli : LinearIndependent F ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (spQuotB n F a) hst
    have h2 := congrArg (spQuotB n F b) hst
    simp only [map_add, map_smul, map_zero, smul_eq_mul, haa, hab, hba, hbb] at h1 h2
    exact ⟨by linear_combination -h2, by linear_combination h1⟩
  have hHyrank : Module.finrank F Hy = 2 := by
    rw [hHy, finrank_span_eq_card hli, Fintype.card_fin]
  have hVrank : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl.symm
  rw [hm, hHyrank, hVrank] at hsum
  obtain rfl : m = n - 1 := by omega
  exact ⟨⟨e, a, b, hab, fun u => by rw [heU]; exact hmemU u⟩, rfl⟩

end Existence

theorem spStabQuotStatement_holds :
    ∀ {n : ℕ}, 2 ≤ n → ∀ {F : Type} [Field F] (a : Fin n ⊕ Fin n → F), a ≠ 0 →
      ∃ π : ↥(spFix a) →* StatedSp (n - 1) F,
        Function.Surjective π ∧ π.ker = (spRad a).subgroupOf (spFix a) := by
  intro n hn F _ a ha
  obtain ⟨Q, rfl⟩ := spQuot_exists_data hn ha
  exact ⟨Q.qHom, Q.qHom_surjective, Q.qHom_ker⟩

end CFSG.RankThree.GF2n.Tim79a
