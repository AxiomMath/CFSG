module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

open Matrix hiding ext
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (eω eω_injective eω_ne_zero eω_add eω_zero)
open CFSG.RankThree.PartTwo CFSG.RankThree CFSG.RankThree.LocalRank CFSG
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank

theorem idOutside_of_perfect {P : Subgroup Sp} (hP : Group.IsPerfect P)
    (S : Set (Fin 3 → ZMod 3)) (T : Set (Fin 3 ⊕ Fin 3))
    (hsing : ∀ x, x ∉ T → ∀ y, (∀ v ∈ S, ext v x = ext v y) → y = x)
    (hPC : ∀ g ∈ P, ∀ v ∈ S, g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) :
    ∀ g ∈ P, IsIdOutside T (mat g) := by
  have entry : ∀ g ∈ P, ∀ v ∈ S, ∀ x y, mat g x y ≠ 0 → ext v y = ext v x := by
    intro g hg v hv x y hxy
    have h1 := congrArg (fun z : Sp => mat z x y) (hPC g hg v hv)
    simp only [mat_mul, coe_δ, dg, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : eω (ext v y) = eω (ext v x) := mul_left_cancel₀ hxy (by rw [h1, mul_comm])
    exact eω_injective h2
  have hrow : ∀ g ∈ P, ∀ x, x ∉ T → ∀ y, y ≠ x → mat g x y = 0 := by
    intro g hg x hx y hyx
    by_contra h
    exact hyx (hsing x hx y fun v hv => (entry g hg v hv x y h).symm)
  have hcol : ∀ g ∈ P, ∀ x, x ∉ T → ∀ k, k ≠ x → mat g k x = 0 := by
    intro g hg x hx k hkx
    by_contra h
    exact hkx (hsing x hx k fun v hv => entry g hg v hv k x h)
  have hdiag : ∀ x, x ∉ T → ∀ g ∈ P, mat g x x = 1 := by
    intro x hx
    let f : P →* F4 :=
      { toFun := fun g => mat (g : Sp) x x
        map_one' := by simp [mat_one]
        map_mul' := fun g h => by
          change mat ((g : Sp) * (h : Sp)) x x = mat (g : Sp) x x * mat (h : Sp) x x
          rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single x]
          · intro z _ hz
            rw [hrow g.1 g.2 x hx z hz, zero_mul]
          · intro h
            exact absurd (Finset.mem_univ x) h }
    intro g hg
    exact perfect_hom_trivial hP f ⟨g, hg⟩
  intro g hg i j hij
  rcases hij with hi | hj
  · by_cases hji : j = i
    · subst hji
      rw [hdiag j hi g hg, Matrix.one_apply_eq]
    · rw [hrow g hg i hi j hji, Matrix.one_apply_ne (Ne.symm hji)]
  · by_cases hij' : i = j
    · subst hij'
      rw [hdiag i hj g hg, Matrix.one_apply_eq]
    · rw [hcol g hg j hj i hij', Matrix.one_apply_ne hij']

@[expose] def Good (D : Set (MulAut A0)) (Z : Subgroup Sp) : Prop :=
  ∃ ψ ∈ D, ∀ P : Subgroup Sp, P ≤ Subgroup.centralizer (fixedInG A0 ψ : Set Sp) →
    Group.IsPerfect P → P ≤ Z

theorem fixedInG_conj {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3)
    (ψ : MulAut A0) :
    fixedInG A0 (signedAut π hπ * ψ * (signedAut π hπ)⁻¹) =
      (fixedInG A0 ψ).map (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_fixedSubgroupOf] at ha
    refine Subgroup.mem_map.mpr ⟨(((signedAut π hπ)⁻¹ a : A0) : Sp), ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨(signedAut π hπ)⁻¹ a, ?_, rfl⟩
      rw [mem_fixedSubgroupOf]
      have h1 : signedAut π hπ (ψ ((signedAut π hπ)⁻¹ a)) = a := ha
      have h2 := congrArg (fun y => (signedAut π hπ)⁻¹ y) h1
      simpa using h2
    · change reindexSp π (Jm_submatrix_of_mem hπ) (((signedAut π hπ)⁻¹ a : A0) : Sp) = (a : Sp)
      rw [← signedAut_apply hπ, MulAut.apply_inv_self]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_fixedSubgroupOf] at ha
    refine Subgroup.mem_map.mpr ⟨signedAut π hπ a, ?_, ?_⟩
    · rw [mem_fixedSubgroupOf]
      change signedAut π hπ (ψ ((signedAut π hπ)⁻¹ (signedAut π hπ a))) = signedAut π hπ a
      rw [MulAut.inv_apply_self, ha]
    · change ((signedAut π hπ a : A0) : Sp) = reindexSp π (Jm_submatrix_of_mem hπ) (a : Sp)
      rw [signedAut_apply hπ]

theorem good_map {D : Set (MulAut A0)}
    (hconj : ∀ g ∈ starOf A0 (⊤ : Subgroup Sp), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) {Z : Subgroup Sp}
    (h : Good D Z) :
    Good D (Z.map (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom) := by
  obtain ⟨ψ, hψD, hψ⟩ := h
  set ρ := reindexSp π (Jm_submatrix_of_mem hπ) with hρ
  refine ⟨signedAut π hπ * ψ * (signedAut π hπ)⁻¹, hconj _ (signedAut_mem_starOf hπ) ψ hψD,
    fun P hPC hPperf => ?_⟩
  have hP0 : P.map ρ.symm.toMonoidHom ≤ Subgroup.centralizer (fixedInG A0 ψ : Set Sp) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hρz : ρ z ∈ fixedInG A0 (signedAut π hπ * ψ * (signedAut π hπ)⁻¹) := by
      rw [fixedInG_conj hπ ψ]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp (hPC hy) (ρ z) hρz
    have h2 := congrArg (fun w => ρ.symm w) h
    simpa using h2
  haveI : Group.IsPerfect P := hPperf
  have hP1 : Group.IsPerfect (P.map ρ.symm.toMonoidHom) := Group.IsPerfect.map _
  have hZ := hψ _ hP0 hP1
  intro x hx
  have hx' : ρ.symm x ∈ P.map ρ.symm.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact Subgroup.mem_map.mpr ⟨ρ.symm x, hZ hx', ρ.apply_symm_apply x⟩

theorem exists_component_map (φ : Sp ≃* Sp) (b : Sp)
    {Y : Subgroup (Subgroup.centralizer ({b} : Set Sp))} (hY : CFSG.IsComponent Y) :
    ∃ Y' : Subgroup (Subgroup.centralizer ({φ b} : Set Sp)), CFSG.IsComponent Y' ∧
      Y'.map (Subgroup.centralizer ({φ b} : Set Sp)).subtype =
        (Y.map (Subgroup.centralizer ({b} : Set Sp)).subtype).map φ.toMonoidHom := by
  have hC : (Subgroup.centralizer ({b} : Set Sp)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ b} : Set Sp) := by
    rw [map_centralizer_mulEquiv, Set.image_singleton]
  let e : Subgroup.centralizer ({b} : Set Sp) ≃* Subgroup.centralizer ({φ b} : Set Sp) :=
    (MulEquiv.subgroupMap φ _).trans (MulEquiv.subgroupCongr hC)
  refine ⟨Y.map e.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e hY, ?_⟩
  have h : (Subgroup.centralizer ({φ b} : Set Sp)).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp (Subgroup.centralizer ({b} : Set Sp)).subtype := by
    ext y
    rfl
  rw [Subgroup.map_map, Subgroup.map_map, h]

theorem hsing_s2 : ∀ x y : Fin 3 ⊕ Fin 3, x ≠ Sum.inl 2 → x ≠ Sum.inr 2 →
    (∀ v : Fin 3 → ZMod 3, wf 1 (scFlip 2) v = v → ext v x = ext v y) → y = x := by
  decide +kernel

theorem good_s2 {D : Set (MulAut A0)} (hs2 : sAut 1 (scFlip 2) ∈ D) {Z : Subgroup Sp}
    (hZ : ∀ g : Sp,
      IsIdOutside {x : Fin 3 ⊕ Fin 3 | x = Sum.inl 2 ∨ x = Sum.inr 2} (mat g) → g ∈ Z) :
    Good D Z := by
  refine ⟨_, hs2, fun P hPC hP g hg => hZ g ?_⟩
  refine idOutside_of_perfect hP {v | wf 1 (scFlip 2) v = v} _ ?_ ?_ g hg
  · intro x hx y hy
    exact hsing_s2 x y (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)) hy
  · intro g hg v hv
    have hmem : δ (Multiplicative.ofAdd v) ∈ fixedInG A0 (sAut 1 (scFlip 2)) :=
      Subgroup.mem_map.mpr ⟨⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩,
        (mem_fixed_sAut_iff 1 _ v).mpr hv, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hPC hg) _ hmem).symm

theorem wf_swap01_fix : ∀ v : Fin 3 → ZMod 3, v 0 = v 1 →
    wf (Equiv.swap 0 1) (fun _ => false) v = v := by
  decide

theorem good_rho01 {D : Set (MulAut A0)}
    (hρ : sAut (Equiv.swap 0 1) (fun _ => false) ∈ D) {Z : Subgroup Sp}
    (hZ : ∀ P : Subgroup Sp, Group.IsPerfect P →
      (∀ g ∈ P, ∀ v : Fin 3 → ZMod 3, v 0 = v 1 →
        g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) → P ≤ Z) :
    Good D Z := by
  refine ⟨_, hρ, fun P hPC hP => hZ P hP ?_⟩
  intro g hg v hv
  have hmem : δ (Multiplicative.ofAdd v) ∈ fixedInG A0 (sAut (Equiv.swap 0 1) (fun _ => false)) :=
    Subgroup.mem_map.mpr ⟨⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩,
      (mem_fixed_sAut_iff _ _ v).mpr (wf_swap01_fix v hv), rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (hPC hg) _ hmem).symm

theorem le_centralizer_of_iff {v : Fin 3 → ZMod 3} {κ : ZMod 3} {S : Subgroup Sp}
    (hS : ∀ x : Sp, x ∈ S ↔ IsIdOutside {i | ext v i = κ} (mat x)) :
    S ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) :=
  fun x hx => mem_centralizer_of_isBlockDiag ((hS x).mp hx).isBlockDiag

theorem normal_subgroupOf_of_iff {v : Fin 3 → ZMod 3} {κ : ZMod 3} {S : Subgroup Sp}
    (hS : ∀ x : Sp, x ∈ S ↔ IsIdOutside {i | ext v i = κ} (mat x)) :
    (S.subgroupOf (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_centralizer_of_iff hS)]
  have hSeq : S = idOutsideSp {i | ext v i = κ} := by
    ext x
    exact hS x
  rw [hSeq]
  exact centralizer_le_normalizer_idOutsideSp fun i j e => by simp only [Set.mem_ofPred_eq, e]

theorem hsing0 : ∀ x y : Fin 3 ⊕ Fin 3, ext (std 0) x ≠ 0 → ext (std 0) x = ext (std 0) y →
    y = x := by
  decide

theorem comm_of_perfect_cent {v : Fin 3 → ZMod 3}
    (P : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp))) :
    ∀ g ∈ P.map (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp)).subtype,
      ∀ w ∈ ({v} : Set (Fin 3 → ZMod 3)),
        g * δ (Multiplicative.ofAdd w) = δ (Multiplicative.ofAdd w) * g := by
  intro g hg w hw
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Set.mem_singleton_iff.mp hw]
  exact Subgroup.mem_centralizer_singleton_iff.mp y.2

theorem S4_le_C0 : S4 ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set Sp) :=
  le_centralizer_of_iff (κ := 0) mem_S4_iff

theorem components_std0 {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} :
    Set Sp))} (hY : CFSG.IsComponent Y) :
    Y.map (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set Sp)).subtype = S4 := by
  have key := components_eq_range_of_finite
    (fun _ : Unit => S4.subgroupOf (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} :
      Set Sp)))
    (fun _ => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe S4_le_C0).symm isQuasisimple_S4)
    (fun _ => normal_subgroupOf_of_iff (κ := 0) mem_S4_iff)
    (fun P hP => by
      refine le_trans ?_ (le_iSup _ ())
      intro g hg
      haveI : Group.IsPerfect P := hP
      have hQ : Group.IsPerfect (P.map (Subgroup.centralizer
          ({δ (Multiplicative.ofAdd (std 0))} : Set Sp)).subtype) := Group.IsPerfect.map _
      have h := idOutside_of_perfect hQ {std 0} {i | ext (std 0) i = 0}
        (fun x hx y hy => hsing0 x y hx (hy (std 0) rfl)) (comm_of_perfect_cent P) (g : Sp)
        ⟨g, hg, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ((mem_S4_iff _).mpr h))
  have hmem : Y ∈ {K : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} :
      Set Sp)) | CFSG.IsComponent K} := hY
  rw [key] at hmem
  obtain ⟨-, rfl⟩ := hmem
  exact Subgroup.map_subgroupOf_eq_of_le S4_le_C0

theorem good_S4 {D : Set (MulAut A0)} (hs2 : sAut 1 (scFlip 2) ∈ D) : Good D S4 :=
  good_s2 hs2 fun g hg => (mem_S4_iff g).mpr fun i j hij => hg i j (by
    rcases hij with h | h
    · left
      intro hx
      apply h
      rcases hx with rfl | rfl <;> decide
    · right
      intro hx
      apply h
      rcases hx with rfl | rfl <;> decide)

theorem S3_le_C3 : leviSL3.range ≤ C3 := by
  rw [range_leviSL3_eq]
  exact Subgroup.map_subtype_le _

theorem subgroupOf_S3 : leviSL3.range.subgroupOf C3 = d3.toHomUnits.ker := by
  rw [range_leviSL3_eq, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective C3.subtype_injective]

theorem d3_eq_one_of_perfect {P : Subgroup Sp} (hP : Group.IsPerfect P) (hPC : P ≤ C3) {g : Sp}
    (hg : g ∈ P) : d3.toHomUnits ⟨g, hPC hg⟩ = 1 := by
  have h := perfect_hom_trivial hP (d3.comp (Subgroup.inclusion hPC)) ⟨g, hg⟩
  apply Units.ext
  exact h

theorem components_std2 {Y : Subgroup C3} (hY : CFSG.IsComponent Y) :
    Y.map C3.subtype = leviSL3.range := by
  have key := components_eq_range_of_finite (fun _ : Unit => leviSL3.range.subgroupOf C3)
    (fun _ => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe S3_le_C3).symm isQuasisimple_S3)
    (fun _ => by rw [subgroupOf_S3]; exact MonoidHom.normal_ker _)
    (fun P hP => by
      refine le_trans ?_ (le_iSup _ ())
      rw [subgroupOf_S3]
      intro g hg
      rw [MonoidHom.mem_ker]
      apply Units.ext
      simpa using perfect_hom_trivial hP (d3.comp P.subtype) ⟨g, hg⟩)
  have hmem : Y ∈ {K : Subgroup C3 | CFSG.IsComponent K} := hY
  rw [key] at hmem
  obtain ⟨-, rfl⟩ := hmem
  exact Subgroup.map_subgroupOf_eq_of_le S3_le_C3

theorem good_S3 {D : Set (MulAut A0)} (hρ : sAut (Equiv.swap 0 1) (fun _ => false) ∈ D) :
    Good D leviSL3.range := by
  refine good_rho01 hρ fun P hP hPC => ?_
  have hPC3 : P ≤ C3 := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPC g hg (std 2) (by decide))
  intro g hg
  rw [range_leviSL3_eq]
  exact Subgroup.mem_map.mpr ⟨⟨g, hPC3 hg⟩, MonoidHom.mem_ker.mpr (d3_eq_one_of_perfect hP hPC3 hg),
    rfl⟩

end CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

end
