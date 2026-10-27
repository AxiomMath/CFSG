module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchCases

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}

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

private theorem plh_range_fin2 {α : Type} (σ : Fin 2 → α) :
    Set.range σ = {σ 0, σ 1} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

private theorem plh_insert_comm {α : Type} (a b : α) :
    insert a ({b} : Set α) = ({b, a} : Set α) := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem plh_charts_single (charts : HasCharts M) (x : Fin D.rank) :
    ∃ L : SLPath M 1, L.e = fun _ : Fin 1 => x := by
  refine charts 1 (fun _ : Fin 1 => x) (by norm_num) (by norm_num) ?_ ?_
  · intro a b _
    exact Subsingleton.elim a b
  · intro k l
    rw [if_pos (Subsingleton.elim k l)]
    exact D.isFiniteType.apply_self x

include hext hw₀ hsq hpanel in
theorem residueModel_exchA1A1 (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M)
    (σ : Fin PhanCode.exchA1A1.rank → Fin D.rank) {J I : Set (Fin D.rank)}
    {π : Fin D.rank → Fin D.rank} (hm : Matches D.cartan PhanCode.exchA1A1 σ J I π)
    {a : K ⧸ borel D H} {g : K} {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a PhanCode.exchA1A1 := by
  haveI : NeZero PhanCode.exchA1A1.rank := ⟨by decide⟩
  obtain ⟨hinj, hrange, hadj, hcore, hperm⟩ := hm
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hcart01 : D.cartan (σ 0) (σ 1) = 0 := by
    rw [hadj 0 1 h01]
    rfl
  have hσ01 : σ 0 ≠ σ 1 := fun h => h01 (hinj h)
  have hcomm01 : coxeterMatrix D.isFiniteType (σ 0) (σ 1) = 2 :=
    coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hσ01 hcart01
  obtain ⟨L₁, hL₁⟩ := plh_charts_single charts (σ 0)
  obtain ⟨L₂, hL₂⟩ := plh_charts_single charts (σ 1)
  have hL₁0 : L₁.e 0 = σ 0 := congrFun hL₁ 0
  have hL₂0 : L₂.e 0 = σ 1 := congrFun hL₂ 0
  have hJ₁ : Set.range L₁.e = Set.range (fun _ : Fin 1 => σ 0) := by rw [hL₁]
  have hJ : insert (L₂.e 0) (Set.range (fun _ : Fin 1 => σ 0)) = J := by
    rw [← hrange, hL₂0, Set.range_const]
    rw [show insert (σ 1) ({σ 0} : Set (Fin D.rank)) = Set.range σ by
      rw [plh_insert_comm (σ 1) (σ 0)]
      exact (plh_range_fin2 σ).symm]
  have hz : L₂.e 0 ∉ Set.range (fun _ : Fin 1 => σ 0) := by
    rw [hL₂0, Set.range_const]
    intro h
    rw [Set.mem_singleton_iff] at h
    exact hσ01 h.symm
  have hcomm : ∀ i ∈ Set.range (fun _ : Fin 1 => σ 0),
      coxeterMatrix D.isFiniteType i (L₂.e 0) = 2 := by
    intro i hi
    rw [Set.range_const] at hi
    have hi' : i = σ 0 := by simpa using hi
    subst hi'
    rw [hL₂0]
    exact hcomm01
  have hI₁ : L₁.e 0 ∈ I := by
    rw [hL₁0]
    exact (hcore 0).mpr rfl
  have hI₂ : L₂.e 0 ∈ I := by
    rw [hL₂0]
    exact (hcore 1).mpr rfl
  have hπ₁ : π (L₁.e 0) = L₂.e 0 := by
    rw [hL₁0, hL₂0]
    obtain ⟨j, hjval, hjσ⟩ := hperm 0 ((hcore 0).mpr rfl)
    have hj : j = 1 := Fin.ext (by rw [hjval]; rfl)
    subst hj
    exact hjσ.symm
  have hπ₂ : π (L₂.e 0) = L₁.e 0 := by
    rw [hL₂0, hL₁0]
    obtain ⟨j, hjval, hjσ⟩ := hperm 1 ((hcore 1).mpr rfl)
    have hj : j = 0 := Fin.ext (by rw [hjval]; rfl)
    subst hj
    exact hjσ.symm
  obtain ⟨Θ, hΘ⟩ := exists_chart_exchA1A1_of_frame hct hext F hw₀ hsq hpanel hK PC L₁ L₂
    hJ₁ hJ hz hcomm hfr hπ hI₁ hI₂ hπ₁ hπ₂
  exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr PhanCode.exchA1A1 Θ hΘ

include hext hw₀ hsq hpanel in
theorem residueModel_exchA2A1 (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M)
    (σ : Fin PhanCode.exchA2A1.rank → Fin D.rank) {J I : Set (Fin D.rank)}
    {π : Fin D.rank → Fin D.rank} (hm : Matches D.cartan PhanCode.exchA2A1 σ J I π)
    {a : K ⧸ borel D H} {g : K} {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a PhanCode.exchA2A1 := by
  haveI : NeZero PhanCode.exchA2A1.rank := ⟨by decide⟩
  obtain ⟨hinj, hrange, hadj, hcore, hperm⟩ := hm
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hcart01 : D.cartan (σ 0) (σ 1) = -1 := by rw [hadj 0 1 h01]; rfl
  have hcart10 : D.cartan (σ 1) (σ 0) = -1 := by rw [hadj 1 0 h10]; rfl
  have hcart02 : D.cartan (σ 0) (σ 2) = 0 := by rw [hadj 0 2 h02]; rfl
  have hcart12 : D.cartan (σ 1) (σ 2) = 0 := by rw [hadj 1 2 h12]; rfl
  have hσ02 : σ 0 ≠ σ 2 := fun h => h02 (hinj h)
  have hσ12 : σ 1 ≠ σ 2 := fun h => h12 (hinj h)
  obtain ⟨L₁, hL₁⟩ : ∃ L : SLPath M 2,
      L.e = fun k : Fin 2 => σ (Fin.castAdd 1 k) :=
    charts 2 (fun k : Fin 2 => σ (Fin.castAdd 1 k)) (by norm_num) (by norm_num)
      (fun p q h => Fin.ext (by
        have h' := congrArg Fin.val (hinj h)
        simpa [Fin.val_castAdd] using h'))
      (fun k l => by
        have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
        have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
        rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
        · rw [if_pos rfl]; exact D.isFiniteType.apply_self _
        · rw [show Fin.castAdd 1 (0 : Fin 2) = (0 : Fin 3) from Fin.ext rfl,
              show Fin.castAdd 1 (1 : Fin 2) = (1 : Fin 3) from Fin.ext rfl,
              if_neg (by decide), if_pos (by decide)]
          exact hcart01
        · rw [show Fin.castAdd 1 (1 : Fin 2) = (1 : Fin 3) from Fin.ext rfl,
              show Fin.castAdd 1 (0 : Fin 2) = (0 : Fin 3) from Fin.ext rfl,
              if_neg (by decide), if_pos (by decide)]
          exact hcart10
        · rw [if_pos rfl]; exact D.isFiniteType.apply_self _)
  obtain ⟨L₂, hL₂⟩ := plh_charts_single charts (σ 2)
  have hL₂0 : L₂.e 0 = σ 2 := congrFun hL₂ 0
  have hL₁range : Set.range L₁.e = ({σ 0, σ 1} : Set (Fin D.rank)) := by
    rw [hL₁, plh_range_fin2 (fun k : Fin 2 => σ (Fin.castAdd 1 k))]
    rfl
  have hJ : insert (L₂.e 0) (Set.range L₁.e) = J := by
    rw [← hrange, hL₂0, hL₁range]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · right; left; exact congrArg σ (Fin.ext rfl)
      · right; right; exact congrArg σ (Fin.ext rfl)
      · left; exact congrArg σ (Fin.ext rfl)
  have hz : L₂.e 0 ∉ Set.range L₁.e := by
    rw [hL₁range, hL₂0]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact hσ02 h.symm
    · exact hσ12 h.symm
  have hcomm : ∀ i ∈ Set.range L₁.e,
      coxeterMatrix D.isFiniteType i (L₂.e 0) = 2 := by
    intro i hi
    rw [hL₁range] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi
    · subst hi
      rw [hL₂0]
      exact coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hσ02 hcart02
    · subst hi
      rw [hL₂0]
      exact coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hσ12 hcart12
  have hI₁ : ∀ k : Fin 2, L₁.e k ∈ I ↔ k = 1 := by
    intro k
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with rfl | rfl
    · rw [hL₁]
      dsimp only
      rw [show Fin.castAdd 1 (0 : Fin 2) = (0 : Fin PhanCode.exchA2A1.rank)
            from Fin.ext rfl, hcore 0]
      simp
      rfl
    · rw [hL₁]
      dsimp only
      rw [show Fin.castAdd 1 (1 : Fin 2) = (1 : Fin PhanCode.exchA2A1.rank)
            from Fin.ext rfl, hcore 1]
      simp
      rfl
  have hI₂ : L₂.e 0 ∈ I := by
    rw [hL₂0]
    exact (hcore 2).mpr rfl
  have hπ₁ : π (L₁.e 1) = L₂.e 0 := by
    rw [hL₁, hL₂0]
    dsimp only
    rw [show Fin.castAdd 1 (1 : Fin 2) = (1 : Fin PhanCode.exchA2A1.rank)
          from Fin.ext rfl]
    obtain ⟨j, hjval, hjσ⟩ := hperm 1 ((hcore 1).mpr rfl)
    have hj : j = 2 := Fin.ext (by rw [hjval]; rfl)
    subst hj
    exact hjσ.symm
  have hπ₂ : π (L₂.e 0) = L₁.e 1 := by
    rw [hL₂0, hL₁]
    dsimp only
    rw [show Fin.castAdd 1 (1 : Fin 2) = (1 : Fin PhanCode.exchA2A1.rank)
          from Fin.ext rfl]
    obtain ⟨j, hjval, hjσ⟩ := hperm 2 ((hcore 2).mpr rfl)
    have hj : j = 1 := Fin.ext (by rw [hjval]; rfl)
    subst hj
    exact hjσ.symm
  obtain ⟨Θ, hΘ⟩ := exists_chart_exchA2A1_of_frame hct hext F hw₀ hsq hpanel hK PC L₁ L₂
    rfl hJ hz hcomm hfr hπ hI₁ hI₂ hπ₁ hπ₂
  exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr PhanCode.exchA2A1 Θ hΘ

include hext hw₀ hsq hpanel in
theorem residueModel_prod3 (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M) {c₁ c₂ c₃ : PhanCode}
    (hc₁ : c₁.IsNode) (hc₂ : c₂.IsNode) (hc₃ : c₃.IsNode)
    (σ : Fin (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank → Fin D.rank)
    {J I : Set (Fin D.rank)} {π : Fin D.rank → Fin D.rank}
    (hm : Matches D.cartan (PhanCode.prod (PhanCode.prod c₁ c₂) c₃) σ J I π)
    {a : K ⧸ borel D H} {g : K} {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a
      (PhanCode.prod (PhanCode.prod c₁ c₂) c₃) := by
  have hrank : (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank = 3 := by
    show (c₁.rank + c₂.rank) + c₃.rank = 3
    rw [PhanCode.IsNode.rank hc₁, PhanCode.IsNode.rank hc₂, PhanCode.IsNode.rank hc₃]
  haveI : NeZero (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank :=
    ⟨by rw [hrank]; norm_num⟩
  let z0 : Fin (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank := ⟨0, by rw [hrank]; norm_num⟩
  let z1 : Fin (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank := ⟨1, by rw [hrank]; norm_num⟩
  let z2 : Fin (PhanCode.prod (PhanCode.prod c₁ c₂) c₃).rank := ⟨2, by rw [hrank]; norm_num⟩
  have hz01 : z0 ≠ z1 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z0.val = 0 from rfl, show z1.val = 1 from rfl] at h'
    omega
  have hz02 : z0 ≠ z2 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z0.val = 0 from rfl, show z2.val = 2 from rfl] at h'
    omega
  have hz12 : z1 ≠ z2 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z1.val = 1 from rfl, show z2.val = 2 from rfl] at h'
    omega
  have hc₁' := hc₁
  have hc₂' := hc₂
  have hc₃' := hc₃
  rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> rcases hc₃ with rfl | rfl
  all_goals
    obtain ⟨hinj, hrange, hadj, hcore, hperm⟩ := hm
    obtain ⟨Lx, hLx⟩ := plh_charts_single charts (σ z0)
    obtain ⟨Ly, hLy⟩ := plh_charts_single charts (σ z1)
    obtain ⟨Lz, hLz⟩ := plh_charts_single charts (σ z2)
    have hLx0 : Lx.e 0 = σ z0 := congrFun hLx 0
    have hLy0 : Ly.e 0 = σ z1 := congrFun hLy 0
    have hLz0 : Lz.e 0 = σ z2 := congrFun hLz 0
    have hxy : Lx.e 0 ≠ Ly.e 0 := by rw [hLx0, hLy0]; exact fun h => hz01 (hinj h)
    have hxz : Lx.e 0 ≠ Lz.e 0 := by rw [hLx0, hLz0]; exact fun h => hz02 (hinj h)
    have hyz : Ly.e 0 ≠ Lz.e 0 := by rw [hLy0, hLz0]; exact fun h => hz12 (hinj h)
    have hmxy : coxeterMatrix D.isFiniteType (Lx.e 0) (Ly.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hxy
        (by rw [hLx0, hLy0, hadj z0 z1 hz01]; rfl)
    have hmxz : coxeterMatrix D.isFiniteType (Lx.e 0) (Lz.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hxz
        (by rw [hLx0, hLz0, hadj z0 z2 hz02]; rfl)
    have hmyz : coxeterMatrix D.isFiniteType (Ly.e 0) (Lz.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hyz
        (by rw [hLy0, hLz0, hadj z1 z2 hz12]; rfl)
    obtain ⟨Θ, hΘ⟩ := exists_chart_prod3_of_frame hct hext F hw₀ hsq hpanel hK PC hc₁' hc₂' hc₃'
      Lx Ly Lz
      (by
        rw [← hrange, hLz0, hLy0, hLx0]
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨z2, rfl⟩
          · exact ⟨z1, rfl⟩
          · exact ⟨z0, rfl⟩
        · rintro ⟨i, rfl⟩
          fin_cases i
          · right; right; exact congrArg σ (Fin.ext rfl)
          · right; left; exact congrArg σ (Fin.ext rfl)
          · left; exact congrArg σ (Fin.ext rfl))
      hxy hxz hyz hmxy hmxz hmyz hfr hπ
      (by rw [hLx0]; exact hcore z0)
      (by
        intro hI
        rw [hLx0] at hI
        obtain ⟨j, hjval, hjσ⟩ := hperm z0 hI
        have hj : j = z0 := Fin.ext hjval
        refine ⟨⟨0, by norm_num⟩, rfl, ?_⟩
        subst hj
        simpa [hLx] using hjσ)
      (by rw [hLy0]; exact hcore z1)
      (by
        intro hI
        rw [hLy0] at hI
        obtain ⟨j, hjval, hjσ⟩ := hperm z1 hI
        have hj : j = z1 := Fin.ext hjval
        refine ⟨⟨0, by norm_num⟩, rfl, ?_⟩
        subst hj
        simpa [hLy] using hjσ)
      (by rw [hLz0]; exact hcore z2)
      (by
        intro hI
        rw [hLz0] at hI
        obtain ⟨j, hjval, hjσ⟩ := hperm z2 hI
        have hj : j = z2 := Fin.ext hjval
        refine ⟨⟨0, by norm_num⟩, rfl, ?_⟩
        subst hj
        simpa [hLz] using hjσ)
    exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ

include hext hw₀ hsq hpanel in
theorem residueModel_exch3 (hK : Nat.card Fld = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (charts : HasCharts M) {c₃ : PhanCode}
    (hc₃ : c₃.IsNode) (σ : Fin (PhanCode.prod PhanCode.exchA1A1 c₃).rank → Fin D.rank)
    {J I : Set (Fin D.rank)} {π : Fin D.rank → Fin D.rank}
    (hm : Matches D.cartan (PhanCode.prod PhanCode.exchA1A1 c₃) σ J I π)
    {a : K ⧸ borel D H} {g : K} {v : W} {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀)
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    PhanEResidueModel (cs) (stdδ hct) Fld f (stdFlip F (nrep hct w₀)) J a
      (PhanCode.prod PhanCode.exchA1A1 c₃) := by
  have hrank : (PhanCode.prod PhanCode.exchA1A1 c₃).rank = 3 := by
    show PhanCode.exchA1A1.rank + c₃.rank = 3
    rw [PhanCode.IsNode.rank hc₃]
    rfl
  haveI : NeZero (PhanCode.prod PhanCode.exchA1A1 c₃).rank :=
    ⟨by rw [hrank]; norm_num⟩
  let z0 : Fin (PhanCode.prod PhanCode.exchA1A1 c₃).rank := ⟨0, by rw [hrank]; norm_num⟩
  let z1 : Fin (PhanCode.prod PhanCode.exchA1A1 c₃).rank := ⟨1, by rw [hrank]; norm_num⟩
  let z2 : Fin (PhanCode.prod PhanCode.exchA1A1 c₃).rank := ⟨2, by rw [hrank]; norm_num⟩
  have hz01 : z0 ≠ z1 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z0.val = 0 from rfl, show z1.val = 1 from rfl] at h'
    omega
  have hz02 : z0 ≠ z2 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z0.val = 0 from rfl, show z2.val = 2 from rfl] at h'
    omega
  have hz12 : z1 ≠ z2 := fun h => by
    have h' := congrArg Fin.val h
    rw [show z1.val = 1 from rfl, show z2.val = 2 from rfl] at h'
    omega
  have hc₃' := hc₃
  rcases hc₃ with rfl | rfl
  all_goals
    obtain ⟨hinj, hrange, hadj, hcore, hperm⟩ := hm
    obtain ⟨Lx, hLx⟩ := plh_charts_single charts (σ z0)
    obtain ⟨Ly, hLy⟩ := plh_charts_single charts (σ z1)
    obtain ⟨Lz, hLz⟩ := plh_charts_single charts (σ z2)
    have hLx0 : Lx.e 0 = σ z0 := congrFun hLx 0
    have hLy0 : Ly.e 0 = σ z1 := congrFun hLy 0
    have hLz0 : Lz.e 0 = σ z2 := congrFun hLz 0
    have hxy : Lx.e 0 ≠ Ly.e 0 := by rw [hLx0, hLy0]; exact fun h => hz01 (hinj h)
    have hxz : Lx.e 0 ≠ Lz.e 0 := by rw [hLx0, hLz0]; exact fun h => hz02 (hinj h)
    have hyz : Ly.e 0 ≠ Lz.e 0 := by rw [hLy0, hLz0]; exact fun h => hz12 (hinj h)
    have hmxy : coxeterMatrix D.isFiniteType (Lx.e 0) (Ly.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hxy
        (by rw [hLx0, hLy0, hadj z0 z1 hz01]; rfl)
    have hmxz : coxeterMatrix D.isFiniteType (Lx.e 0) (Lz.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hxz
        (by rw [hLx0, hLz0, hadj z0 z2 hz02]; rfl)
    have hmyz : coxeterMatrix D.isFiniteType (Ly.e 0) (Lz.e 0) = 2 :=
      coxeter_eq_two_of_cartan_eq_zero D.isFiniteType hyz
        (by rw [hLy0, hLz0, hadj z1 z2 hz12]; rfl)
    have hIx : Lx.e 0 ∈ I := by
      rw [hLx0]
      exact (hcore z0).mpr rfl
    have hIy : Ly.e 0 ∈ I := by
      rw [hLy0]
      exact (hcore z1).mpr rfl
    have hπx : π (Lx.e 0) = Ly.e 0 := by
      rw [hLx0, hLy0]
      obtain ⟨j, hjval, hjσ⟩ := hperm z0 ((hcore z0).mpr rfl)
      have hj : j = z1 := Fin.ext (by rw [hjval]; rfl)
      subst hj
      exact hjσ.symm
    have hπy : π (Ly.e 0) = Lx.e 0 := by
      rw [hLy0, hLx0]
      obtain ⟨j, hjval, hjσ⟩ := hperm z1 ((hcore z1).mpr rfl)
      have hj : j = z0 := Fin.ext (by rw [hjval]; rfl)
      subst hj
      exact hjσ.symm
    obtain ⟨Θ, hΘ⟩ := exists_chart_exch3_of_frame hct hext F hw₀ hsq hpanel hK PC hc₃'
      Lx Ly Lz
      (by
        rw [← hrange, hLz0, hLy0, hLx0]
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨z2, rfl⟩
          · exact ⟨z1, rfl⟩
          · exact ⟨z0, rfl⟩
        · rintro ⟨i, rfl⟩
          fin_cases i
          · right; right; exact congrArg σ (Fin.ext rfl)
          · right; left; exact congrArg σ (Fin.ext rfl)
          · left; exact congrArg σ (Fin.ext rfl))
      hxy hxz hyz hmxy hmxz hmyz hfr hπ hIx hIy hπx hπy
      (by rw [hLz0]; exact hcore z2)
      (by
        intro hI
        rw [hLz0] at hI
        obtain ⟨j, hjval, hjσ⟩ := hperm z2 hI
        have hj : j = z2 := Fin.ext hjval
        refine ⟨⟨0, by norm_num⟩, rfl, ?_⟩
        subst hj
        simpa [hLz] using hjσ)
    exact phanEResidueModel_of_chartOf hct hext F hw₀ hsq hpanel hK hq hfr _ Θ hΘ

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
