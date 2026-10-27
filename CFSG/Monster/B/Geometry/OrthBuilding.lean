module

public import CFSG.Monster.B.Geometry.OrthModel
public import CFSG.Monster.B.Geometry.PolarResidue
public import CFSG.Monster.B.Geometry.StandardPair

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (X Q)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def OData : PolarSpace (ZMod 2) OV where
  Iso v := oQ v = 0
  pair w := oPolarBilin.flip w
  pair_eq_zero_comm u v := by
    change oPolar v u = 0 ↔ oPolar u v = 0
    rw [oPolar_comm]
  pair_eq_zero_of_isTI _ hU _ hu _ hv := oPolar_eq_zero_of_isTSo hU hv hu
  isTI_sup _ hU _ hw hwU := isTSo_sup_span hU hw hwU
  finrank_le_three _ hU := finrank_le_three_of_isTSo hU

theorem oData_iso (v : OV) : OData.Iso v ↔ oQ v = 0 := Iff.rfl

theorem oData_pair (w v : OV) : OData.pair w v = oPolar v w := rfl

theorem oQ_eq_zero_of_mem_cspan {s : Finset (Fin 8)} (h6 : 6 ∉ s) (h7 : 7 ∉ s)
    (h0 : 0 ∉ s ∨ 3 ∉ s) (h1 : 1 ∉ s ∨ 4 ∉ s) (h2 : 2 ∉ s ∨ 5 ∉ s) {v : OV}
    (hv : v ∈ cspan (ZMod 2) s) : oQ v = 0 := by
  rw [mem_cspan] at hv
  rw [oQ_apply, hv 6 h6, hv 7 h7]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [hv _ h0, hv _ h1, hv _ h2]

abbrev oFlag (s₁ s₂ s₃ : Finset (Fin 8)) (h1 : s₁.card = 1 := by decide)
    (h2 : s₂.card = 2 := by decide) (h3 : s₃.card = 3 := by decide)
    (h12 : s₁ ⊆ s₂ := by decide) (h23 : s₂ ⊆ s₃ := by decide) (h6 : 6 ∉ s₃ := by decide)
    (h7 : 7 ∉ s₃ := by decide) (h0 : 0 ∉ s₃ ∨ 3 ∉ s₃ := by decide)
    (h1' : 1 ∉ s₃ ∨ 4 ∉ s₃ := by decide) (h2' : 2 ∉ s₃ ∨ 5 ∉ s₃ := by decide) :
    PFlag OData :=
  coordFlag OData s₁ s₂ s₃ h1 h2 h3 h12 h23 fun _ hv => oQ_eq_zero_of_mem_cspan h6 h7 h0 h1' h2' hv

@[expose] def oC0 : PFlag OData := oFlag {0} {0, 1} {0, 1, 2}

@[expose] def oD0 : PFlag OData := oFlag {3} {3, 4} {3, 4, 5}

structure OFrame where
  e : Fin 3 → OV
  f : Fin 3 → OV
  a : OV
  b : OV
  Qe : ∀ i, oQ (e i) = 0
  Qf : ∀ i, oQ (f i) = 0
  Qa : oQ a = 1
  Qb : oQ b = 1
  Bab : oPolar a b = 1
  Bee : ∀ i j, oPolar (e i) (e j) = 0
  Bff : ∀ i j, oPolar (f i) (f j) = 0
  Bef : ∀ i j, oPolar (e i) (f j) = if i = j then 1 else 0
  Bea : ∀ i, oPolar (e i) a = 0
  Beb : ∀ i, oPolar (e i) b = 0
  Bfa : ∀ i, oPolar (f i) a = 0
  Bfb : ∀ i, oPolar (f i) b = 0

namespace OFrame

variable (F : OFrame)

theorem Bfe (i j : Fin 3) : oPolar (F.f i) (F.e j) = if j = i then 1 else 0 := by
  rw [oPolar_comm, F.Bef]

theorem Bae (i : Fin 3) : oPolar F.a (F.e i) = 0 := by rw [oPolar_comm, F.Bea]

theorem Bbe (i : Fin 3) : oPolar F.b (F.e i) = 0 := by rw [oPolar_comm, F.Beb]

theorem Baf (i : Fin 3) : oPolar F.a (F.f i) = 0 := by rw [oPolar_comm, F.Bfa]

theorem Bbf (i : Fin 3) : oPolar F.b (F.f i) = 0 := by rw [oPolar_comm, F.Bfb]

theorem Bba : oPolar F.b F.a = 1 := by rw [oPolar_comm, F.Bab]

@[expose] def vec : Fin 8 → OV := ![F.e 0, F.e 1, F.e 2, F.f 0, F.f 1, F.f 2, F.a, F.b]

@[expose] def toLin : OV →ₗ[ZMod 2] OV where
  toFun x := ∑ k, x k • F.vec k
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem toLin_apply (x : OV) : F.toLin x = x 0 • F.e 0 + x 1 • F.e 1 + x 2 • F.e 2 +
    x 3 • F.f 0 + x 4 • F.f 1 + x 5 • F.f 2 + x 6 • F.a + x 7 • F.b := by
  simp [toLin, vec, Fin.sum_univ_eight]

theorem toLin_single (k : Fin 8) : F.toLin (Pi.single k 1) = F.vec k := by
  simp [toLin, Pi.single_apply, ite_smul]

theorem Q_toLin (x : OV) : oQ (F.toLin x) = oQ x := by
  have hmul : ∀ t : ZMod 2, t * t = t := by decide
  rw [toLin_apply, oQ_apply x]
  simp only [oQ_add, oQ_smul, oPolar_add_left, oPolar_smul_left, oPolar_smul_right, F.Qe, F.Qf,
    F.Qa, F.Qb, F.Bab, F.Bee, F.Bff, F.Bef, F.Bea, F.Beb, F.Bfa, F.Bfb]
  simp
  simp only [hmul]
  ring

theorem toLin_injective : Function.Injective F.toLin := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  have hB : ∀ w, oPolar (F.toLin x) w = 0 := fun w => by rw [hx, oPolar_zero_left]
  have key : ∀ w, oPolar (F.toLin x) w = x 0 * oPolar (F.e 0) w + x 1 * oPolar (F.e 1) w +
      x 2 * oPolar (F.e 2) w + x 3 * oPolar (F.f 0) w + x 4 * oPolar (F.f 1) w +
      x 5 * oPolar (F.f 2) w + x 6 * oPolar F.a w + x 7 * oPolar F.b w := fun w => by
    rw [toLin_apply]
    simp only [oPolar_add_left, oPolar_smul_left]
  have h0 := (key (F.f 0)).symm.trans (hB _)
  have h1 := (key (F.f 1)).symm.trans (hB _)
  have h2 := (key (F.f 2)).symm.trans (hB _)
  have h3 := (key (F.e 0)).symm.trans (hB _)
  have h4 := (key (F.e 1)).symm.trans (hB _)
  have h5 := (key (F.e 2)).symm.trans (hB _)
  have h6 := (key F.b).symm.trans (hB _)
  have h7 := (key F.a).symm.trans (hB _)
  simp [F.Bef, F.Bff, F.Baf, F.Bbf, F.Bee, F.Bfe, F.Bae, F.Bbe, F.Bea, F.Beb, F.Bfa, F.Bfb,
    F.Bab, F.Bba, oPolar_self] at h0 h1 h2 h3 h4 h5 h6 h7
  funext k
  fin_cases k <;> simpa

theorem toLin_bijective : Function.Bijective F.toLin :=
  ⟨F.toLin_injective, LinearMap.injective_iff_surjective.mp F.toLin_injective⟩

@[expose] noncomputable def flagPerm : Equiv.Perm (PFlag OData) :=
  polarFlagPerm F.toLin F.toLin_bijective fun v => by rw [oData_iso, oData_iso, F.Q_toLin]

theorem map_cspan_one : (cspan (ZMod 2) {0}).map F.toLin = (ZMod 2) ∙ F.e 0 := by
  rw [map_cspan_singleton, toLin_single]
  rfl

theorem map_cspan_two : (cspan (ZMod 2) {0, 1}).map F.toLin =
    (ZMod 2) ∙ F.e 0 ⊔ (ZMod 2) ∙ F.e 1 := by
  rw [map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single]
  rfl

theorem map_cspan_three : (cspan (ZMod 2) {0, 1, 2}).map F.toLin =
    (ZMod 2) ∙ F.e 0 ⊔ (ZMod 2) ∙ F.e 1 ⊔ (ZMod 2) ∙ F.e 2 := by
  rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single,
    toLin_single, sup_assoc]
  rfl

theorem map_cspan_four : (cspan (ZMod 2) {3}).map F.toLin = (ZMod 2) ∙ F.f 0 := by
  rw [map_cspan_singleton, toLin_single]
  rfl

theorem map_cspan_five : (cspan (ZMod 2) {3, 4}).map F.toLin =
    (ZMod 2) ∙ F.f 0 ⊔ (ZMod 2) ∙ F.f 1 := by
  rw [map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single]
  rfl

theorem map_cspan_six : (cspan (ZMod 2) {3, 4, 5}).map F.toLin =
    (ZMod 2) ∙ F.f 0 ⊔ (ZMod 2) ∙ F.f 1 ⊔ (ZMod 2) ∙ F.f 2 := by
  rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single,
    toLin_single, sup_assoc]
  rfl

end OFrame

theorem exists_oFrame {x y : PFlag OData} (h3 : x.V₃ ⊓ y.V₃ = ⊥)
    (h1 : ∀ u ∈ x.V₁, ∀ v ∈ y.V₁, u ≠ 0 → v ≠ 0 → OData.pair v u ≠ 0)
    (h2 : ∀ w ∈ x.V₂, (∀ v ∈ y.V₂, OData.pair v w = 0) → w = 0) :
    ∃ F : OFrame, F.flagPerm oC0 = x ∧ F.flagPerm oD0 = y := by
  obtain ⟨e, f, hef, hx1, hx2, hx3, hy1, hy2, hy3⟩ := exists_frame h3 h1 h2
  have hex : ∀ i, e i ∈ x.V₃ := fun i => by
    rw [hx3]
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hfy : ∀ i, f i ∈ y.V₃ := fun i => by
    rw [hy3]
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have Bef : ∀ i j, oPolar (e i) (f j) = if i = j then 1 else 0 := hef
  have Bee : ∀ i j, oPolar (e i) (e j) = 0 := fun i j =>
    oPolar_eq_zero_of_isTSo x.isTI (hex i) (hex j)
  have Bff : ∀ i j, oPolar (f i) (f j) = 0 := fun i j =>
    oPolar_eq_zero_of_isTSo y.isTI (hfy i) (hfy j)
  have Bfe : ∀ i j, oPolar (f i) (e j) = if j = i then 1 else 0 := fun i j => by
    rw [oPolar_comm, Bef]
  let w : Fin 6 → OV := ![e 0, e 1, e 2, f 0, f 1, f 2]
  let Φ : OV →ₗ[ZMod 2] (Fin 6 → ZMod 2) := LinearMap.pi fun k => oPolarBilin.flip (w k)
  have hΦ : ∀ v k, Φ v k = oPolar v (w k) := fun _ _ => rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    intro t _
    refine ⟨t 0 • f 0 + t 1 • f 1 + t 2 • f 2 + t 3 • e 0 + t 4 • e 1 + t 5 • e 2, ?_⟩
    funext k
    rw [hΦ]
    fin_cases k <;> simp [w, oPolar_add_left, oPolar_smul_left, Bef, Bee, Bff, Bfe]
  have hT : finrank (ZMod 2) (LinearMap.ker Φ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  have hmemT : ∀ {t : OV}, t ∈ LinearMap.ker Φ → ∀ k, oPolar t (w k) = 0 := fun ht k => by
    rw [← hΦ, LinearMap.mem_ker.mp ht]
    rfl
  have haniso : ∀ t ∈ LinearMap.ker Φ, t ≠ 0 → oQ t = 1 := by
    intro t ht ht0
    rcases C2E6Overlap.zmod_two_eq_zero_or_one (oQ t) with hQ | hQ
    · exfalso
      have hperp : ∀ u ∈ x.V₃, oPolar u t = 0 := by
        intro u hu
        rw [hx3] at hu
        obtain ⟨α, β, γ, rfl⟩ := mem_span_three.mp hu
        have h0 := hmemT ht 0
        have h1 := hmemT ht 1
        have h2 := hmemT ht 2
        simp only [w, Matrix.cons_val] at h0 h1 h2
        rw [oPolar_add_left, oPolar_add_left, oPolar_smul_left, oPolar_smul_left,
          oPolar_smul_left, oPolar_comm (e 0), oPolar_comm (e 1), oPolar_comm (e 2), h0, h1, h2]
        ring
      have hts := isTSo_sup_span x.isTI hQ hperp
      by_cases htx : t ∈ x.V₃
      · rw [hx3] at htx
        obtain ⟨α, β, γ, rfl⟩ := mem_span_three.mp htx
        have h3 := hmemT ht 3
        have h4 := hmemT ht 4
        have h5 := hmemT ht 5
        simp [w, oPolar_add_left, oPolar_smul_left, Bef] at h3 h4 h5
        exact ht0 (by rw [h3, h4, h5]; simp)
      · have := finrank_le_three_of_isTSo hts
        rw [finrank_sup_span_of_not_mem htx, x.finrank₃] at this
        omega
    · exact hQ
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := C2E6Overlap.exists_pair_of_finrank_eq_two hT
  have hab0 : a + b ≠ 0 := fun h => hab (by
    rw [← sub_eq_zero]
    rwa [sub_eq_add_neg, ZModModule.neg_eq_self])
  have hQa := haniso a ha ha0
  have hQb := haniso b hb hb0
  have hQab := haniso (a + b) (Submodule.add_mem _ ha hb) hab0
  have hBab : oPolar a b = 1 := by
    have := oQ_add a b
    rw [hQab, hQa, hQb] at this
    rcases C2E6Overlap.zmod_two_eq_zero_or_one (oPolar a b) with h | h
    · rw [h] at this
      exact absurd this (by decide)
    · exact h
  have hTa := hmemT ha
  have hTb := hmemT hb
  let F : OFrame :=
    { e := e, f := f, a := a, b := b
      Qe := fun i => x.isTI _ (hex i)
      Qf := fun i => y.isTI _ (hfy i)
      Qa := hQa, Qb := hQb, Bab := hBab, Bee := Bee, Bff := Bff, Bef := Bef
      Bea := fun i => by
        rw [oPolar_comm]
        fin_cases i
        · exact hTa 0
        · exact hTa 1
        · exact hTa 2
      Beb := fun i => by
        rw [oPolar_comm]
        fin_cases i
        · exact hTb 0
        · exact hTb 1
        · exact hTb 2
      Bfa := fun i => by
        rw [oPolar_comm]
        fin_cases i
        · exact hTa 3
        · exact hTa 4
        · exact hTa 5
      Bfb := fun i => by
        rw [oPolar_comm]
        fin_cases i
        · exact hTb 3
        · exact hTb 4
        · exact hTb 5 }
  refine ⟨F, PFlag.ext ?_ ?_ ?_, PFlag.ext ?_ ?_ ?_⟩
  · exact F.map_cspan_one.trans hx1.symm
  · exact F.map_cspan_two.trans hx2.symm
  · exact F.map_cspan_three.trans hx3.symm
  · exact F.map_cspan_four.trans hy1.symm
  · exact F.map_cspan_five.trans hy2.symm
  · exact F.map_cspan_six.trans hy3.symm

section Building

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  [Finite W] {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ) {p l π : ι}
  (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
  (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag OData}
  (hf : IsChamberModel cs δ (polarChamber OData p l π) f)
include hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf

theorem orth_transitive {c₀ d₀ : C} (hc₀ : f c₀ = oC0) (hd₀ : f d₀ = oD0) (c d : C)
    (hcd : δ c d = longest cs Set.univ) : ∃ g ∈ typeAut cs δ, g c₀ = c ∧ g d₀ = d := by
  obtain ⟨F, hFc, hFd⟩ := exists_oFrame
    (polar_opposite_plane hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd)
    (fun u hu v hv hu0 hv0 => polar_opposite_point hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd hu hv
      hu0 hv0)
    (fun w hw hperp => polar_opposite_line hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd hw hperp)
  refine ⟨hf.perm F.flagPerm, hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π),
    hf.1.1 ?_, hf.1.1 ?_⟩
  · rw [hf.apply_perm, hc₀, hFc]
  · rw [hf.apply_perm, hd₀, hFd]

theorem orth_standard_opposite {c₀ d₀ : C} (hc₀ : f c₀ = oC0) (hd₀ : f d₀ = oD0) :
    δ c₀ d₀ = longest cs Set.univ := by
  obtain ⟨d, hd⟩ := exists_dist hδ c₀ (longest cs Set.univ)
  obtain ⟨g, hg, hgc, hgd⟩ :=
    orth_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ c₀ d hd
  rw [← dist_typeAut hδ hg, hgc, hgd, hd]

end Building

end CFSG.Monster.B.Geometry
