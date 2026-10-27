module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchChartPath
public import CFSG.LocalAnalysis.StandardType.PhanEMatchChartProd
public import CFSG.LocalAnalysis.StandardType.PhanEMatchChartExch
public import CFSG.LocalAnalysis.StandardType.PhanEMatchSlice
public import CFSG.LocalAnalysis.StandardType.PhanEMatchPath

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.ClassicalInvolution.Phan.PhanE.Res

@[expose] def Matches {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : PhanCode)
    (σ : Fin c.rank → Fin n) (J I : Set (Fin n)) (π : Fin n → Fin n) : Prop :=
  Function.Injective σ ∧ Set.range σ = J ∧
    (∀ i j : Fin c.rank, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0) ∧
    (∀ i : Fin c.rank, σ i ∈ I ↔ c.coreN i = true) ∧
    ∀ i : Fin c.rank, σ i ∈ I → ∃ j : Fin c.rank, j.val = c.permN i ∧ σ j = π (σ i)

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}

@[expose] def HasCharts (M : ChevModel2 D n H Fld) : Prop :=
  ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
    (∀ k l : Fin m, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
    ∃ L : SLPath M m, L.e = e

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1) (hpanel : StdPanel hct F (nrep hct w₀))

private theorem plh_range_add {α : Type*} (m n : ℕ) (σ : Fin (m + n) → α) :
    Set.range σ = Set.range (fun k : Fin m => σ (Fin.castAdd n k)) ∪
      Set.range (fun k : Fin n => σ (Fin.natAdd m k)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases lt_or_ge i.val m with h | h
    · exact Or.inl ⟨⟨i.val, h⟩, congrArg σ (Fin.ext (by simp [Fin.val_castAdd]))⟩
    · exact Or.inr ⟨⟨i.val - m, by omega⟩,
        congrArg σ (Fin.ext (by simp only [Fin.val_natAdd]; omega))⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨Fin.castAdd n k, rfl⟩
    · exact ⟨Fin.natAdd m k, rfl⟩

private theorem plh_range_fin_one {α : Type*} (f : Fin 1 → α) : Set.range f = {f 0} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg f (Subsingleton.elim i 0))
  · rintro hx
    exact ⟨0, (Set.mem_singleton_iff.mp hx).symm⟩

private theorem plh_castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

include hext hw₀ hsq hpanel in
theorem residueModel_path (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M) {c : PhanCode}
    (hc : c.IsPath2 ∨ c.IsPath3) (σ : Fin c.rank → Fin D.rank) {J I : Set (Fin D.rank)}
    {π : Fin D.rank → Fin D.rank} (hm : Matches D.cartan c σ J I π) {a : K ⧸ borel D H} {g : K}
    {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a c := by
  obtain ⟨hinj, hrange, hadj, hcoreσ, hpermσ⟩ := hm
  have hfl : c.IsFlagCode := hc.elim (fun h => h.isFlagCode) (fun h => h.isFlagCode)
  have hdiag : ∀ i : Fin c.rank, D.cartan (σ i) (σ i) = 2 :=
    fun i => D.isFiniteType.apply_self (σ i)
  have hrk : 1 ≤ c.rank ∧ c.rank ≤ 3 := by
    rcases hc with h | h
    · rw [h.rank]; norm_num
    · rw [h.rank]; norm_num
  obtain ⟨L, hL⟩ := charts c.rank σ hrk.1 hrk.2 hinj
    (fun k l => path_cartan_of_match hfl σ hdiag hadj k l)
  have hJ : Set.range L.e = J := by rw [hL]; exact hrange
  have hcore' : ∀ k : Fin c.rank, L.e k ∈ I ↔ c.coreN k = true := by
    intro k
    rw [hL]
    exact hcoreσ k
  have hperm' : ∀ k : Fin c.rank, L.e k ∈ I →
      ∃ k' : Fin c.rank, k'.val = c.permN k ∧ L.e k' = π (L.e k) := by
    intro k hk
    rw [hL] at hk ⊢
    exact hpermσ k hk
  by_cases h22 : c = PhanCode.a3_22x
  · subst h22
    obtain ⟨Θ, hΘ⟩ := exists_chart_22x_of_frame hct hext F hw₀ hsq hpanel hK PC L hJ hfr hπ
      hcore' hperm'
    exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr
      PhanCode.a3_22x Θ hΘ
  · obtain ⟨Θ, hΘ⟩ := exists_chart_flagCode hct hext F hw₀ hsq hpanel hK PC hfl h22 L hJ hfr
      hπ hcore' hperm'
    rcases hc with h | h
    · rcases h with rfl | rfl | rfl | rfl <;>
        exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact absurd rfl h22
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ
      · exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ

include hext hw₀ hsq hpanel in
theorem residueModel_prod (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M) {c₁ c₂ : PhanCode}
    (hc₁ : c₁.IsNode ∨ c₁.IsPath2) (hc₂ : c₂.IsNode)
    (σ : Fin (PhanCode.prod c₁ c₂).rank → Fin D.rank) {J I : Set (Fin D.rank)}
    {π : Fin D.rank → Fin D.rank} (hm : Matches D.cartan (PhanCode.prod c₁ c₂) σ J I π)
    {a : K ⧸ borel D H} {g : K} {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a
      (PhanCode.prod c₁ c₂) := by
  have hc₂keep : c₂.IsNode := hc₂
  rcases hc₂ with rfl | rfl
  all_goals
    obtain ⟨hinj, hrange, hadj, hcoreσ, hpermσ⟩ := hm
    have hfl₁ : c₁.IsFlagCode := hc₁.elim (fun h => h.isFlagCode) (fun h => h.isFlagCode)
    let σ₁ : Fin c₁.rank → Fin D.rank := fun k => σ (Fin.castAdd 1 k)
    let σ₂ : Fin 1 → Fin D.rank := fun k => σ (Fin.natAdd c₁.rank k)
    have hinj₁ : Function.Injective σ₁ := hinj.comp (Fin.castAdd_injective c₁.rank 1)
    have hdiag₁ : ∀ i : Fin c₁.rank, D.cartan (σ₁ i) (σ₁ i) = 2 :=
      fun i => D.isFiniteType.apply_self _
    have hadj₁ : ∀ i j : Fin c₁.rank, i ≠ j →
        D.cartan (σ₁ i) (σ₁ j) = if c₁.coxN i j = 3 then -1 else 0 :=
      fun i j hij => slice_adj_left hadj i j hij
    have hrk₁ : 1 ≤ c₁.rank ∧ c₁.rank ≤ 3 := by
      rcases hc₁ with h | h
      · rw [h.rank]; norm_num
      · rw [h.rank]; norm_num
    obtain ⟨L₁, hL₁⟩ := charts c₁.rank σ₁ hrk₁.1 hrk₁.2 hinj₁
      (fun k l => path_cartan_of_match hfl₁ σ₁ hdiag₁ hadj₁ k l)
    have hinj₂ : Function.Injective σ₂ := fun i j _ => Subsingleton.elim i j
    have hcart₂ : ∀ k l : Fin 1, D.cartan (σ₂ k) (σ₂ l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0 := by
      intro k l
      have hkl : k = l := Subsingleton.elim k l
      rw [if_pos hkl, hkl]
      exact D.isFiniteType.apply_self _
    obtain ⟨L₂, hL₂⟩ := charts 1 σ₂ (by norm_num) (by norm_num) hinj₂ hcart₂
    have hrange_sum : Set.range σ = Set.range σ₁ ∪ Set.range σ₂ :=
      plh_range_add c₁.rank 1 σ
    have hrange₂ : Set.range σ₂ = ({σ₂ 0} : Set (Fin D.rank)) := plh_range_fin_one σ₂
    have hJ : insert (L₂.e 0) (Set.range L₁.e) = J := by
      rw [hL₁, hL₂, ← hrange, hrange_sum, hrange₂, Set.insert_eq]
      exact (Set.union_comm _ _).symm
    have hz : L₂.e 0 ∉ Set.range L₁.e := by
      rw [hL₁, hL₂]
      rintro ⟨k, hk⟩
      exact plh_castAdd_ne_natAdd k (0 : Fin 1) (hinj hk)
    have hcomm : ∀ i ∈ Set.range L₁.e, coxeterMatrix D.isFiniteType i (L₂.e 0) = 2 := by
      intro i hi
      rw [hL₁] at hi
      obtain ⟨k, rfl⟩ := hi
      rw [hL₂]
      exact coxeter_eq_two_of_cartan_eq_zero D.isFiniteType
        (fun h => plh_castAdd_ne_natAdd k (0 : Fin 1) (hinj h))
        (slice_adj_cross hadj k (0 : Fin 1))
    have hcore₁ : ∀ k : Fin c₁.rank, L₁.e k ∈ I ↔ c₁.coreN k = true := by
      intro k
      rw [hL₁]
      exact slice_core_left hcoreσ k
    have hperm₁ : ∀ k : Fin c₁.rank, L₁.e k ∈ I →
        ∃ k' : Fin c₁.rank, k'.val = c₁.permN k ∧ L₁.e k' = π (L₁.e k) := by
      intro k hk
      rw [hL₁] at hk ⊢
      exact slice_perm_left hpermσ k hk
    obtain ⟨Θ, hΘ⟩ := exists_chart_prod_of_frame hct hext F hw₀ hsq hpanel hK PC hc₁
      hc₂keep L₁ L₂
      (rfl : Set.range L₁.e = Set.range L₁.e) hJ hz hcomm hfr hπ hcore₁ hperm₁
      (by rw [hL₂]; exact slice_core_right hcoreσ (0 : Fin 1))
      (by intro hk; rw [hL₂] at hk ⊢; exact slice_perm_right hpermσ (0 : Fin 1) hk)
    rcases hc₁ with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
      exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
