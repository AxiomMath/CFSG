module

public import CFSG.RankThree.PartOne.CTP.Su4Det
public import CFSG.RankThree.PartOne.CTP.Su4Node
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.TitsSimplicity
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.RankThree.PartOne.CTP.Su4Plane
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} {ζ : K}

theorem commute_of_scalar_pair {g b : SUid σ 4} {L L' : Submodule K (Fin 4 → K)}
    (hc : IsCompl L L') {c c' : K} (hg : ∀ v ∈ L, g • v = c • v) (hg' : ∀ v ∈ L', g • v = c' • v)
    (hb : ∀ v ∈ L, b • v ∈ L) (hb' : ∀ v ∈ L', b • v ∈ L') : g * b = b * g := by
  refine ext_smul σ fun v => ?_
  have hv : v ∈ L ⊔ L' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [mul_smul, smul_add, hg x hx, hg' y hy, hg _ (hb x hx), hg' _ (hb' y hy),
    smul_comm b c x, smul_comm b c' y]

theorem finrank_inf_split [NeZero p] (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4} (hg : g ^ p = 1)
    {l : K}
    (hdisj : Disjoint (eigU g l) (eigU g l⁻¹))
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eigU g μ = ⊥) {S : Submodule K (Fin 4 → K)}
    (hS : ∀ v ∈ S, g • v ∈ S) :
    Module.finrank K ↥(S ⊓ eigU g l) + Module.finrank K ↥(S ⊓ eigU g l⁻¹) =
      Module.finrank K S := by
  have hsplit := le_iSup_inf_eigU hζ hg hS
  have hsup : (S ⊓ eigU g l) ⊔ (S ⊓ eigU g l⁻¹) = S := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun v hv => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mem_inf_add_of_stableU hzero hsplit hv
    exact Submodule.add_mem_sup ha hb
  have hd : Disjoint (S ⊓ eigU g l) (S ⊓ eigU g l⁻¹) :=
    hdisj.mono inf_le_right inf_le_right
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ eigU g l) (S ⊓ eigU g l⁻¹)
  rw [hd.eq_bot, finrank_bot, hsup] at h
  omega

section Lines

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem eq_smul_of_finrank_eq_one {S : Submodule K V} (hS : Module.finrank K S = 1) {v : V}
    (hv : v ∈ S) (hv0 : v ≠ 0) {w : V} (hw : w ∈ S) : ∃ c : K, w = c • v := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : S)
    (fun h => hv0 (congrArg Subtype.val h))).mp hS ⟨w, hw⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem exists_mem_ne_zero_of_finrank_pos {S : Submodule K V} (h : 0 < Module.finrank K S) :
    ∃ v ∈ S, v ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  exact ⟨x.1, x.2, fun h0 => hx (Subtype.ext h0)⟩

omit [FiniteDimensional K V] in
theorem not_mem_span_of_disjoint_of_ne_zero {M N : Submodule K V} (hd : Disjoint M N) {u e : V}
    (hu : u ∈ M) (he : e ∈ N) (he0 : e ≠ 0) : e ∉ Submodule.span K {u} := by
  intro h
  have h1 : e ∈ M := (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu)) h
  exact he0 (Submodule.disjoint_def.mp hd e h1 he)

theorem span_pair_eq_of_finrank {S : Submodule K V} (hS : Module.finrank K S = 2) {u e : V}
    (hu : u ∈ S) (he : e ∈ S) (hu0 : u ≠ 0) (hne : e ∉ Submodule.span K {u}) :
    Submodule.span K {u, e} = S := by
  have hle : Submodule.span K {u, e} ≤ S := Submodule.span_le.mpr (by
    rintro _ (rfl | rfl)
    · exact hu
    · exact he)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair_of_not_mem hu0 hne, hS])

omit [FiniteDimensional K V] in
theorem linearIndependent_pair_of_disjoint {M N : Submodule K V} (hd : Disjoint M N) {u v : V}
    (hu : u ∈ M) (hv : v ∈ N) (hu0 : u ≠ 0) (hv0 : v ≠ 0) : LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h2 : s • u = -(t • v) := eq_neg_of_add_eq_zero_left hst
  have h3 : s • u ∈ N := by rw [h2]; exact N.neg_mem (N.smul_mem t hv)
  have h4 : s • u = 0 := Submodule.disjoint_def.mp hd _ (M.smul_mem s hu) h3
  have hs : s = 0 := (smul_eq_zero.mp h4).resolve_right hu0
  rw [hs, zero_smul, zero_add] at hst
  exact ⟨hs, (smul_eq_zero.mp hst).resolve_right hv0⟩

end Lines

section Planes

variable {z : SUid σ 4} {P P' L L' : Submodule K (Fin 4 → K)}

theorem four_planes_lines (hσ : IsUnitaryInvolution σ) (hfix : ∀ l : K, l ^ p = 1 → σ l = l)
    (hzp : z ^ p = 1) (hPiso : ∀ x ∈ P, ∀ y ∈ P, herm σ x y = 0)
    (hLiso : ∀ x ∈ L, ∀ y ∈ L, herm σ x y = 0) (hL'iso : ∀ x ∈ L', ∀ y ∈ L', herm σ x y = 0)
    (hPc : IsCompl P P') (hLc : IsCompl L L') (hLd : Module.finrank K L = 2)
    (hL'd : Module.finrank K L' = 2) (h1 : Module.finrank K ↥(P ⊓ L) = 1)
    (h2 : Module.finrank K ↥(P ⊓ L') = 1) (h3 : Module.finrank K ↥(P' ⊓ L) = 1)
    (h4 : Module.finrank K ↥(P' ⊓ L') = 1) (hzP : ∀ v ∈ P, z • v ∈ P)
    (hzP' : ∀ v ∈ P', z • v ∈ P') (hzL : ∀ v ∈ L, z • v ∈ L) (hzL' : ∀ v ∈ L', z • v ∈ L')
    (hdet : ∀ a ∈ P, ∀ c ∈ P, ∀ α ν : K, z • a = α • a → z • c = ν • c →
      LinearIndependent K ![a, c] → α * ν = 1) :
    ∃ c c' : K, (∀ v ∈ L, z • v = c • v) ∧ ∀ v ∈ L', z • v = c' • v := by
  have hinv := hσ.invol
  obtain ⟨p₁, hp₁, hp₁0⟩ := exists_mem_ne_zero_of_finrank_pos (S := P ⊓ L) (by omega)
  obtain ⟨p₂, hp₂, hp₂0⟩ := exists_mem_ne_zero_of_finrank_pos (S := P ⊓ L') (by omega)
  obtain ⟨q₁, hq₁, hq₁0⟩ := exists_mem_ne_zero_of_finrank_pos (S := P' ⊓ L') (by omega)
  obtain ⟨q₂, hq₂, hq₂0⟩ := exists_mem_ne_zero_of_finrank_pos (S := P' ⊓ L) (by omega)
  obtain ⟨α, hα⟩ := eq_smul_of_finrank_eq_one h1 hp₁ hp₁0 (w := z • p₁)
    ⟨hzP _ hp₁.1, hzL _ hp₁.2⟩
  obtain ⟨ν, hν⟩ := eq_smul_of_finrank_eq_one h2 hp₂ hp₂0 (w := z • p₂)
    ⟨hzP _ hp₂.1, hzL' _ hp₂.2⟩
  obtain ⟨α', hα'⟩ := eq_smul_of_finrank_eq_one h4 hq₁ hq₁0 (w := z • q₁)
    ⟨hzP' _ hq₁.1, hzL' _ hq₁.2⟩
  obtain ⟨ν', hν'⟩ := eq_smul_of_finrank_eq_one h3 hq₂ hq₂0 (w := z • q₂)
    ⟨hzP' _ hq₂.1, hzL _ hq₂.2⟩
  have hαp : α ^ p = 1 := pow_eq_one_of_mem_eigU hzp (mem_eigU.mpr hα : p₁ ∈ eigU z α) hp₁0
  have hνp : ν ^ p = 1 := pow_eq_one_of_mem_eigU hzp (mem_eigU.mpr hν : p₂ ∈ eigU z ν) hp₂0
  have hσα := hfix α hαp
  have hσν := hfix ν hνp
  have hli : LinearIndependent K ![p₁, p₂] :=
    linearIndependent_pair_of_disjoint hLc.disjoint hp₁.2 hp₂.2 hp₁0 hp₂0
  have hαν : α * ν = 1 := hdet p₁ hp₁.1 p₂ hp₂.1 α ν hα hν hli
  have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hαν
  have hν0 : ν ≠ 0 := right_ne_zero_of_mul_eq_one hαν
  have hL'span : Submodule.span K {p₂, q₁} = L' :=
    span_pair_eq_of_finrank hL'd hp₂.2 hq₁.2 hp₂0
      (not_mem_span_of_disjoint_of_ne_zero hPc.disjoint hp₂.1 hq₁.1 hq₁0)
  have hLspan : Submodule.span K {p₁, q₂} = L :=
    span_pair_eq_of_finrank hLd hp₁.2 hq₂.2 hp₁0
      (not_mem_span_of_disjoint_of_ne_zero hPc.disjoint hp₁.1 hq₂.1 hq₂0)
  have hpq1 : herm σ p₁ q₁ ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := exists_herm_ne_zero_of_isCompl hLc hLiso hp₁.2 hp₁0
    rw [← hL'span] at hy
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [herm_add_right, herm_smul_right, herm_smul_right, hPiso p₁ hp₁.1 p₂ hp₂.1, mul_zero,
      zero_add] at hy0
    exact right_ne_zero_of_mul hy0
  have hpq2 : herm σ p₂ q₂ ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := exists_herm_ne_zero_of_isCompl hLc.symm hL'iso hp₂.2 hp₂0
    rw [← hLspan] at hy
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [herm_add_right, herm_smul_right, herm_smul_right, hPiso p₂ hp₂.1 p₁ hp₁.1, mul_zero,
      zero_add] at hy0
    exact right_ne_zero_of_mul hy0
  have hdual1 : α * α' = 1 := by
    have h := herm_smul_smul σ z p₁ q₁
    rw [hα, hα', herm_smul_left, herm_smul_right, ← mul_assoc, hσα] at h
    have h' : (α * α' - 1) * herm σ p₁ q₁ = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hpq1)
  have hdual2 : ν * ν' = 1 := by
    have h := herm_smul_smul σ z p₂ q₂
    rw [hν, hν', herm_smul_left, herm_smul_right, ← mul_assoc, hσν] at h
    have h' : (ν * ν' - 1) * herm σ p₂ q₂ = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hpq2)
  have hα'ν : α' = ν := mul_left_cancel₀ hα0 (hdual1.trans hαν.symm)
  have hν'α : ν' = α := mul_left_cancel₀ hν0 (hdual2.trans (by rw [mul_comm]; exact hαν.symm))
  refine ⟨α, ν, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← hLspan] at hv
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
    calc z • (s • p₁ + t • q₂) = s • (z • p₁) + t • (z • q₂) := by
          rw [smul_add, smul_comm z s p₁, smul_comm z t q₂]
      _ = s • (α • p₁) + t • (α • q₂) := by rw [hα, hν', hν'α]
      _ = α • (s • p₁ + t • q₂) := by rw [smul_add, smul_comm α s p₁, smul_comm α t q₂]
  · rw [← hL'span] at hv
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
    calc z • (s • p₂ + t • q₁) = s • (z • p₂) + t • (z • q₁) := by
          rw [smul_add, smul_comm z s p₂, smul_comm z t q₁]
      _ = s • (ν • p₂) + t • (ν • q₁) := by rw [hν, hα', hα'ν]
      _ = ν • (s • p₂ + t • q₁) := by rw [smul_add, smul_comm ν s p₂, smul_comm ν t q₁]

theorem eq_of_finrank_inf_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {S T : Submodule K V}
    {n : ℕ} (hS : Module.finrank K S = n) (hT : Module.finrank K T = n)
    (h : Module.finrank K ↥(S ⊓ T) = n) : S = T := by
  have h1 : S ⊓ T = S := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h, hS])
  have h2 : S ⊓ T = T := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h, hT])
  exact h1.symm.trans h2

theorem four_planes_cases (hσ : IsUnitaryInvolution σ) (hfix : ∀ l : K, l ^ p = 1 → σ l = l)
    (hzp : z ^ p = 1) (hPiso : ∀ x ∈ P, ∀ y ∈ P, herm σ x y = 0)
    (hLiso : ∀ x ∈ L, ∀ y ∈ L, herm σ x y = 0) (hL'iso : ∀ x ∈ L', ∀ y ∈ L', herm σ x y = 0)
    (hPc : IsCompl P P') (hLc : IsCompl L L') (hPd : Module.finrank K P = 2)
    (hP'd : Module.finrank K P' = 2) (hLd : Module.finrank K L = 2)
    (hL'd : Module.finrank K L' = 2)
    (hPL : Module.finrank K ↥(P ⊓ L) + Module.finrank K ↥(P ⊓ L') = 2)
    (hP'L : Module.finrank K ↥(P' ⊓ L) + Module.finrank K ↥(P' ⊓ L') = 2)
    (hLP : Module.finrank K ↥(L ⊓ P) + Module.finrank K ↥(L ⊓ P') = 2)
    (hzP : ∀ v ∈ P, z • v ∈ P) (hzP' : ∀ v ∈ P', z • v ∈ P') (hzL : ∀ v ∈ L, z • v ∈ L)
    (hzL' : ∀ v ∈ L', z • v ∈ L')
    (hdet : ∀ a ∈ P, ∀ c ∈ P, ∀ α ν : K, z • a = α • a → z • c = ν • c →
      LinearIndependent K ![a, c] → α * ν = 1) :
    (P = L ∧ P' = L') ∨ (P = L' ∧ P' = L) ∨
      ∃ c c' : K, (∀ v ∈ L, z • v = c • v) ∧ ∀ v ∈ L', z • v = c' • v := by
  rw [inf_comm L P, inf_comm L P'] at hLP
  have hcase : Module.finrank K ↥(P ⊓ L) = 2 ∨ Module.finrank K ↥(P ⊓ L) = 0 ∨
      Module.finrank K ↥(P ⊓ L) = 1 := by omega
  rcases hcase with h2 | h0 | h1
  · exact Or.inl ⟨eq_of_finrank_inf_eq hPd hLd h2, eq_of_finrank_inf_eq hP'd hL'd (by omega)⟩
  · exact Or.inr (Or.inl ⟨eq_of_finrank_inf_eq hPd hL'd (by omega),
      eq_of_finrank_inf_eq hP'd hLd (by omega)⟩)
  · exact Or.inr (Or.inr (four_planes_lines hσ hfix hzp hPiso hLiso hL'iso hPc hLc hLd hL'd h1
      (by omega) (by omega) (by omega) hzP hzP' hzL hzL' hdet))

end Planes

theorem su4_not_short_short [CharP K 2] [NeZero p] (hσ : IsUnitaryInvolution σ)
    (hζ : IsPrimitiveRoot ζ p) (hfix : ∀ l : K, l ^ p = 1 → σ l = l) {gA gB : SUid σ 4}
    (hgA : gA ^ p = 1)
    (hgB : gB ^ p = 1) (hcom : gA * gB = gB * gA) {A B : Subgroup (SUid σ 4)} [Group.IsPerfect A]
    (hcA : ∀ a ∈ A, a * gA = gA * a) (hcB : ∀ b ∈ B, b * gB = gB * b)
    (hmovB : ∃ b ∈ B, gA * b ≠ b * gA) {z : SUid σ 4} (hzA : z ∈ A) (hzp : z ^ p = 1)
    (hzg : z * gB = gB * z) (hzB : ¬ ∀ b ∈ B, z * b = b * z)
    {lA : K} (hlA : lA ≠ 1) (hlAp : lA ^ p = 1) (hPd : Module.finrank K (eigU gA lA) = 2)
    (hP'd : Module.finrank K (eigU gA lA⁻¹) = 2)
    (hcomplA : IsCompl (eigU gA lA) (eigU gA lA⁻¹))
    (hzeroA : ∀ μ, μ ≠ lA → μ ≠ lA⁻¹ → eigU gA μ = ⊥)
    {lB : K} (hlB : lB ≠ 1) (hlBp : lB ^ p = 1) (hLd : Module.finrank K (eigU gB lB) = 2)
    (hL'd : Module.finrank K (eigU gB lB⁻¹) = 2)
    (hcomplB : IsCompl (eigU gB lB) (eigU gB lB⁻¹))
    (hzeroB : ∀ μ, μ ≠ lB → μ ≠ lB⁻¹ → eigU gB μ = ⊥) : False := by
  have hlA' : lA⁻¹ ≠ 1 := inv_ne_one.mpr hlA
  have hlB' : lB⁻¹ ≠ 1 := inv_ne_one.mpr hlB
  have hlBp' : (lB⁻¹) ^ p = 1 := by rw [inv_pow, hlBp, inv_one]
  have hPiso : ∀ x ∈ eigU gA lA, ∀ y ∈ eigU gA lA, herm σ x y = 0 := fun x hx y hy =>
    herm_eigU_self_eq_zero gA hlA (hfix lA hlAp) hx hy
  have hLiso : ∀ x ∈ eigU gB lB, ∀ y ∈ eigU gB lB, herm σ x y = 0 := fun x hx y hy =>
    herm_eigU_self_eq_zero gB hlB (hfix lB hlBp) hx hy
  have hL'iso : ∀ x ∈ eigU gB lB⁻¹, ∀ y ∈ eigU gB lB⁻¹, herm σ x y = 0 := fun x hx y hy =>
    herm_eigU_self_eq_zero gB hlB' (hfix _ hlBp') hx hy
  have hPL := (finrank_inf_split hζ hgB hcomplB.disjoint hzeroB
    (S := eigU gA lA) fun v hv => smul_mem_eigU hcom.symm hv).trans hPd
  have hP'L := (finrank_inf_split hζ hgB hcomplB.disjoint hzeroB
    (S := eigU gA lA⁻¹) fun v hv => smul_mem_eigU hcom.symm hv).trans hP'd
  have hLP := (finrank_inf_split hζ hgA hcomplA.disjoint hzeroA
    (S := eigU gB lB) fun v hv => smul_mem_eigU hcom hv).trans hLd
  rcases four_planes_cases hσ hfix hzp hPiso hLiso hL'iso hcomplA hcomplB hPd hP'd hLd hL'd hPL
      hP'L hLP (fun v hv => smul_mem_eigU (hcA z hzA) hv)
      (fun v hv => smul_mem_eigU (hcA z hzA) hv) (fun v hv => smul_mem_eigU hzg hv)
      (fun v hv => smul_mem_eigU hzg hv)
      (fun a ha c hc α ν haz hcz hli => eigenvalue_mul_eq_one A (eigU gA lA) hPd
        (fun a ha v hv => smul_mem_eigU (hcA a ha) hv) hzA ha hc haz hcz hli) with
    ⟨hPL', hP'L'⟩ | ⟨hPL', hP'L'⟩ | ⟨c, c', hc, hc'⟩
  · obtain ⟨b, hb, hne⟩ := hmovB
    refine hne (commute_of_scalar_pair hcomplB (c := lA) (c' := lA⁻¹) (fun v hv => ?_)
      (fun v hv => ?_) (fun v hv => smul_mem_eigU (hcB b hb) hv)
      (fun v hv => smul_mem_eigU (hcB b hb) hv))
    · rw [← hPL'] at hv
      exact mem_eigU.mp hv
    · rw [← hP'L'] at hv
      exact mem_eigU.mp hv
  · obtain ⟨b, hb, hne⟩ := hmovB
    refine hne (commute_of_scalar_pair hcomplB (c := lA⁻¹) (c' := lA) (fun v hv => ?_)
      (fun v hv => ?_) (fun v hv => smul_mem_eigU (hcB b hb) hv)
      (fun v hv => smul_mem_eigU (hcB b hb) hv))
    · rw [← hP'L'] at hv
      exact mem_eigU.mp hv
    · rw [← hPL'] at hv
      exact mem_eigU.mp hv
  · exact hzB fun b hb => commute_of_scalar_pair hcomplB hc hc'
      (fun v hv => smul_mem_eigU (hcB b hb) hv) (fun v hv => smul_mem_eigU (hcB b hb) hv)

end CFSG.RankThree.PartOne.CTP
