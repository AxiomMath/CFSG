module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesInvariant
public import CFSG.GroupTheory.SylowTwoOfConj
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CoverThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open scoped commutatorElement

@[expose] def IndexNinePackage (Γ : Type*) [Group Γ] : Prop :=
  ∃ U P Q : Subgroup Γ, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
    Nat.card P = 9 * Nat.card U ∧
    (∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
    Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1

@[expose] def InnerIndexNinePackage (Δ : Type*) [Group Δ] : Prop :=
  ∃ U P Q : Subgroup Δ, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
    Nat.card P = 9 * Nat.card U ∧
    Subgroup.normalizer (U : Set Δ) ≤ Subgroup.normalizer (P : Set Δ) ∧
    Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1

@[expose] def IndexThreePackage (Γ : Type*) [Group Γ] : Prop :=
  ∃ (U P : Subgroup Γ) (a g : Γ), CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
    Nat.card P = 3 * Nat.card U ∧
    (∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
    a ∈ P ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ g * a * g⁻¹ = a⁻¹

private lemma pspr_map_conjNormal_subtype {R : Type*} [Group R] {N : Subgroup R} [N.Normal]
    (r : R) (H : Subgroup ↥N) :
    (H.map (MulAut.conjNormal (H := N) r).toMonoidHom).map N.subtype =
      (H.map N.subtype).map (MulAut.conj r).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨-, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨(h : R), ⟨h, hh, rfl⟩, by simp [MulAut.conjNormal_apply, MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hy
    refine ⟨MulAut.conjNormal r h, ⟨h, hh, rfl⟩, ?_⟩
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem normalizer_le_stabilizer_of_unique_fixed {G X : Type*} [Group G] [MulAction G X]
    {U C : Subgroup G} {x₀ : X} (hNC : Subgroup.normalizer (U : Set G) ≤ C)
    (hfix : ∀ u ∈ U, u • x₀ = x₀)
    (huniq : ∀ c ∈ C, (∀ u ∈ U, u • (c • x₀) = c • x₀) → c • x₀ = x₀) :
    Subgroup.normalizer (U : Set G) ≤ MulAction.stabilizer G x₀ := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  refine huniq g (hNC hg) fun u hu => ?_
  have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
  rw [inv_inv] at hu'
  calc u • g • x₀ = g • (g⁻¹ * u * g) • x₀ := by
        simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = g • x₀ := by rw [hfix _ hu']

theorem map_eq_of_unique_fixed {R : Type*} [Group R] {N : Subgroup R} [N.Normal]
    {X : Type*} [MulAction R X] {U : Subgroup ↥N} {A C : Subgroup R} {x₀ : X}
    (hAut : ∀ α : MulAut ↥N, ∃ r ∈ A, ∀ n : ↥N, ((α n : ↥N) : R) = r * n * r⁻¹)
    (hNC : A ⊓ Subgroup.normalizer ((U.map N.subtype : Subgroup R) : Set R) ≤ C)
    (hfix : ∀ u ∈ U, (u : R) • x₀ = x₀)
    (huniq : ∀ c ∈ A ⊓ C, (∀ u ∈ U, (u : R) • (c • x₀) = c • x₀) → c • x₀ = x₀)
    (α : MulAut ↥N) (hα : U.map α.toMonoidHom = U) :
    ((C ⊓ MulAction.stabilizer R x₀).subgroupOf N).map α.toMonoidHom =
      (C ⊓ MulAction.stabilizer R x₀).subgroupOf N := by
  classical
  obtain ⟨r, hrA, hr⟩ := hAut α
  have hαeq : α = MulAut.conjNormal (H := N) r := by
    ext n
    rw [MulAut.conjNormal_apply]
    exact hr n
  have hrU : r ∈ Subgroup.normalizer ((U.map N.subtype : Subgroup R) : Set R) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : U.map (MulAut.conjNormal (H := N) r).toMonoidHom = U := by
      rw [← hαeq]
      exact hα
    have h := congrArg (fun H : Subgroup ↥N => H.map N.subtype) hmap
    rwa [pspr_map_conjNormal_subtype] at h
  have hrC : r ∈ C := hNC ⟨hrA, hrU⟩
  have hrinvC : r⁻¹ ∈ C := C.inv_mem hrC
  have hrinvA : r⁻¹ ∈ A := A.inv_mem hrA
  have hrinvU : r⁻¹ ∈ Subgroup.normalizer ((U.map N.subtype : Subgroup R) : Set R) :=
    Subgroup.inv_mem _ hrU
  have hfixrinv : r⁻¹ • x₀ = x₀ := by
    refine huniq r⁻¹ ⟨hrinvA, hNC ⟨hrinvA, hrinvU⟩⟩ ?_
    intro u hu
    have hu' : r * (u : R) * r⁻¹ ∈ U.map N.subtype :=
      (Subgroup.mem_normalizer_iff.mp hrU (u : R)).mp
        (Subgroup.mem_map_of_mem N.subtype hu)
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hu'
    calc (u : R) • (r⁻¹ • x₀) = ((u : R) * r⁻¹) • x₀ := by rw [smul_smul]
      _ = (r⁻¹ * (r * (u : R) * r⁻¹)) • x₀ := by
          rw [show (u : R) * r⁻¹ = r⁻¹ * (r * (u : R) * r⁻¹) from by group]
      _ = r⁻¹ • ((r * (u : R) * r⁻¹) • x₀) := by rw [smul_smul]
      _ = r⁻¹ • ((w : R) • x₀) := by rw [← hw']; rfl
      _ = r⁻¹ • x₀ := by rw [hfix w hw]
  have hfixr : r • x₀ = x₀ := by
    have h := congrArg (fun y => r • y) hfixrinv
    simpa [smul_smul] using h.symm
  let P : Subgroup ↥N := (C ⊓ MulAction.stabilizer R x₀).subgroupOf N
  have hPmem_iff : ∀ p : ↥N, p ∈ P ↔ (p : R) ∈ C ∧ (p : R) • x₀ = x₀ := by
    intro p
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  have hconj : ∀ t : R, t ∈ C → t⁻¹ • x₀ = x₀ → ∀ p : ↥N, p ∈ P →
      (⟨t * (p : R) * t⁻¹, Subgroup.Normal.conj_mem inferInstance (p : R) p.2 t⟩ : ↥N) ∈ P := by
    intro t ht htinv p hp
    rw [hPmem_iff] at hp ⊢
    refine ⟨C.mul_mem (C.mul_mem ht hp.1) (C.inv_mem ht), ?_⟩
    have htfix : t • x₀ = x₀ := by
      have h := congrArg (fun y => t • y) htinv
      simpa [smul_smul] using h.symm
    rw [show (t * (p : R) * t⁻¹) • x₀ = t • ((p : R) • (t⁻¹ • x₀)) by
      simp [mul_smul], htinv, hp.2, htfix]
  refine le_antisymm ?_ ?_
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hp
    have heq : (MulEquiv.toMonoidHom α) q = (⟨r * (q : R) * r⁻¹,
        Subgroup.Normal.conj_mem inferInstance (q : R) q.2 r⟩ : ↥N) := Subtype.ext (hr q)
    rw [← hqp, heq]
    exact hconj r hrC hfixrinv q hq
  · intro p hp
    have hq : (⟨r⁻¹ * (p : R) * r,
        by simpa using Subgroup.Normal.conj_mem inferInstance (p : R) p.2 r⁻¹⟩ : ↥N) ∈ P := by
      simpa using hconj r⁻¹ hrinvC (by simpa using hfixr) p hp
    have heq : α ⟨r⁻¹ * (p : R) * r,
        by simpa using Subgroup.Normal.conj_mem inferInstance (p : R) p.2 r⁻¹⟩ = p := by
      apply Subtype.ext
      rw [hr]
      group
    rw [← heq]
    exact Subgroup.mem_map.mpr ⟨_, hq, rfl⟩

theorem indexNinePackage_of_unique_fixed {R : Type*} [Group R] {N : Subgroup R} [N.Normal]
    {X : Type*} [MulAction R X] {U : Subgroup ↥N} {A C : Subgroup R} {x₀ : X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hAut : ∀ α : MulAut ↥N, ∃ r ∈ A, ∀ n : ↥N, ((α n : ↥N) : R) = r * n * r⁻¹)
    (hNC : A ⊓ Subgroup.normalizer ((U.map N.subtype : Subgroup R) : Set R) ≤ C)
    (hUC : U.map N.subtype ≤ C) (hfix : ∀ u ∈ U, (u : R) • x₀ = x₀)
    (huniq : ∀ c ∈ A ⊓ C, (∀ u ∈ U, (u : R) • (c • x₀) = c • x₀) → c • x₀ = x₀)
    (hcard : Nat.card ((C ⊓ MulAction.stabilizer R x₀).subgroupOf N) = 9 * Nat.card U)
    {x y : R} (hxN : x ∈ N) (hyN : y ∈ N) (hxC : x ∈ C) (hyC : y ∈ C)
    (hx₀ : x • x₀ = x₀) (hy₀ : y • x₀ = x₀) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    IndexNinePackage ↥N := by
  classical
  have hPinv : ∀ α : MulAut ↥N, U.map α.toMonoidHom = U →
      ((C ⊓ MulAction.stabilizer R x₀).subgroupOf N).map α.toMonoidHom =
        (C ⊓ MulAction.stabilizer R x₀).subgroupOf N :=
    fun α hα => map_eq_of_unique_fixed hAut hNC hfix huniq α hα
  have hUP : U ≤ (C ⊓ MulAction.stabilizer R x₀).subgroupOf N := by
    intro u hu
    change (u : R) ∈ C ⊓ MulAction.stabilizer R x₀
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨hUC (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩), hfix u hu⟩
  let xN : ↥N := ⟨x, hxN⟩
  let yN : ↥N := ⟨y, hyN⟩
  have hx3' : xN ^ 3 = 1 := Subtype.ext (by simpa [xN] using hx3)
  have hy3' : yN ^ 3 = 1 := Subtype.ext (by simpa [yN] using hy3)
  have hxy' : xN * yN = yN * xN := Subtype.ext (by simpa [xN, yN] using hxy)
  have hx1' : xN ≠ 1 := fun h => hx1 (by simpa [xN] using congrArg (Subtype.val) h)
  have hyx' : yN ∉ Subgroup.zpowers xN := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine hyx (Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩)
    simpa [xN, yN] using congrArg (Subtype.val) hk
  have hQ9 : Nat.card (Subgroup.closure ({xN, yN} : Set ↥N)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3' hy3' hxy' hx1' hyx'
  have hQP : Subgroup.closure ({xN, yN} : Set ↥N) ≤
      (C ⊓ MulAction.stabilizer R x₀).subgroupOf N := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · change (xN : R) ∈ C ⊓ MulAction.stabilizer R x₀
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨hxC, hx₀⟩
    · change (yN : R) ∈ C ⊓ MulAction.stabilizer R x₀
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨hyC, hy₀⟩
  have hQ3 : ∀ q ∈ Subgroup.closure ({xN, yN} : Set ↥N), q ^ 3 = 1 := by
    have hcomm : ⁅xN, yN⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hxy'
    intro q hq
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
      hx3' hy3' (by rw [hcomm]; exact Commute.one_left _)
      (by rw [hcomm]; exact Commute.one_left _) hq
  exact ⟨U, (C ⊓ MulAction.stabilizer R x₀).subgroupOf N, Subgroup.closure {xN, yN},
    hU, hUP, hcard, hPinv, hQP, hQ9, hQ3⟩

theorem indexThreePackage_of_unique_fixed {R : Type*} [Group R] {N : Subgroup R} [N.Normal]
    {X : Type*} [MulAction R X] {U : Subgroup ↥N} {A C : Subgroup R} {x₀ : X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hAut : ∀ α : MulAut ↥N, ∃ r ∈ A, ∀ n : ↥N, ((α n : ↥N) : R) = r * n * r⁻¹)
    (hNC : A ⊓ Subgroup.normalizer ((U.map N.subtype : Subgroup R) : Set R) ≤ C)
    (hUC : U.map N.subtype ≤ C) (hfix : ∀ u ∈ U, (u : R) • x₀ = x₀)
    (huniq : ∀ c ∈ A ⊓ C, (∀ u ∈ U, (u : R) • (c • x₀) = c • x₀) → c • x₀ = x₀)
    (hcard : Nat.card ((C ⊓ MulAction.stabilizer R x₀).subgroupOf N) = 3 * Nat.card U)
    {a g : R} (haN : a ∈ N) (hgN : g ∈ N) (haC : a ∈ C) (ha₀ : a • x₀ = x₀)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hg : g * a * g⁻¹ = a⁻¹) :
    IndexThreePackage ↥N := by
  classical
  have hPinv : ∀ α : MulAut ↥N, U.map α.toMonoidHom = U →
      ((C ⊓ MulAction.stabilizer R x₀).subgroupOf N).map α.toMonoidHom =
        (C ⊓ MulAction.stabilizer R x₀).subgroupOf N :=
    fun α hα => map_eq_of_unique_fixed hAut hNC hfix huniq α hα
  have hUP : U ≤ (C ⊓ MulAction.stabilizer R x₀).subgroupOf N := by
    intro u hu
    change (u : R) ∈ C ⊓ MulAction.stabilizer R x₀
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨hUC (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩), hfix u hu⟩
  let aN : ↥N := ⟨a, haN⟩
  let gN : ↥N := ⟨g, hgN⟩
  have haP : aN ∈ (C ⊓ MulAction.stabilizer R x₀).subgroupOf N := by
    change (aN : R) ∈ C ⊓ MulAction.stabilizer R x₀
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨haC, ha₀⟩
  have ha3' : aN ^ 3 = 1 := Subtype.ext (by simpa [aN] using ha3)
  have ha1' : aN ≠ 1 := fun h => ha1 (by simpa [aN] using congrArg (Subtype.val) h)
  have hg' : gN * aN * gN⁻¹ = aN⁻¹ :=
    Subtype.ext (by simpa [aN, gN] using hg)
  exact ⟨U, (C ⊓ MulAction.stabilizer R x₀).subgroupOf N, aN, gN, hU, hUP, hcard,
    hPinv, haP, ha1', ha3', hg'⟩

private lemma pspr_map_conj_subtype {R : Type*} [Group R] {C : Subgroup R} {g : R} (hg : g ∈ C)
    (H : Subgroup ↥C) :
    (H.map C.subtype).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj (⟨g, hg⟩ : ↥C)).toMonoidHom).map C.subtype := by
  ext x
  constructor
  · rintro ⟨-, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨MulAut.conj (⟨g, hg⟩ : ↥C) h, ⟨h, hh, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨-, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨C.subtype h, ⟨h, hh, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem indexNinePackage_of_quotient {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    (hAut : ∀ α : MulAut Γ, ∃ g : Γ, ∀ x : Γ, α x = g * x * g⁻¹)
    {U C : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hNC : Subgroup.normalizer (U : Set Γ) ≤ C)
    (π : ↥C →* Δ) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hΔ : InnerIndexNinePackage Δ) :
    IndexNinePackage Γ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ubar, Pbar, Qbar, hUbar, hUbarP, hPbar, hNbar, hQbarP, hQbar, hQbar3⟩ := hΔ
  have hUleC : U ≤ C := fun u hu => hNC (Subgroup.le_normalizer hu)
  let UC : Subgroup ↥C := U.subgroupOf C
  have hUCsyl : CFSG.QuasithinUnique.IsSylowTwoOf UC ⊤ := by
    refine ⟨le_top, hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUleC).symm, ?_⟩
    rw [show (UC.subgroupOf ⊤).index = UC.index from Subgroup.relIndex_top_right UC]
    have hUi : ¬ 2 ∣ U.index := by
      have h := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
    show ¬ 2 ∣ UC.index
    intro h2
    refine hUi ?_
    rw [← Subgroup.relIndex_mul_index hUleC]
    exact dvd_mul_of_dvd_left h2 C.index
  let Uπ : Subgroup Δ := UC.map π
  have hUCidx : ¬ 2 ∣ UC.index := by
    have h := hUCsyl.2.2
    rwa [show (UC.subgroupOf ⊤).index = UC.index from Subgroup.relIndex_top_right UC] at h
  have hUπsyl : CFSG.QuasithinUnique.IsSylowTwoOf Uπ ⊤ := by
    refine ⟨le_top, hUCsyl.2.1.map π, ?_⟩
    rw [show (Uπ.subgroupOf ⊤).index = Uπ.index from Subgroup.relIndex_top_right Uπ]
    exact fun h2 => hUCidx (dvd_trans h2 (Subgroup.index_map_dvd (f := π) UC hπ))
  have hkerU : π.ker ≤ UC := by
    have hsup : IsPGroup 2 ↥(UC ⊔ π.ker) := hUCsyl.2.1.to_sup_of_normal_right hker
    have hmax := CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le (P := UC) (Q := UC ⊔ π.ker)
      (H := ⊤) hUCsyl hsup le_top le_sup_left
    rw [← hmax]
    exact le_sup_right
  obtain ⟨δ, -, hδ⟩ :=
    CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf (L := (⊤ : Subgroup Δ)) hUbar hUπsyl
  let Pbar' : Subgroup Δ := Pbar.map (MulAut.conj δ).toMonoidHom
  let Qbar' : Subgroup Δ := Qbar.map (MulAut.conj δ).toMonoidHom
  have hUπP : Uπ ≤ Pbar' := by
    rw [hδ]
    exact Subgroup.map_mono hUbarP
  have hPbar'card : Nat.card Pbar' = 9 * Nat.card Uπ := by
    dsimp only [Pbar']
    rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hPbar]
    congr 1
    rw [hδ, show Quasithin.conjSub δ Ubar = Ubar.map (MulAut.conj δ).toMonoidHom from rfl]
    exact (Subgroup.card_map_of_injective (MulAut.conj δ).injective).symm
  have hNbar' : Subgroup.normalizer (Uπ : Set Δ) ≤ Subgroup.normalizer (Pbar' : Set Δ) := by
    have h1 : Subgroup.normalizer (Ubar.map (MulAut.conj δ).toMonoidHom : Set Δ) =
        (Subgroup.normalizer (Ubar : Set Δ)).map (MulAut.conj δ).toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq Ubar (MulAut.conj δ)).symm
    have h2 : Subgroup.normalizer (Pbar.map (MulAut.conj δ).toMonoidHom : Set Δ) =
        (Subgroup.normalizer (Pbar : Set Δ)).map (MulAut.conj δ).toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq Pbar (MulAut.conj δ)).symm
    dsimp only [Pbar']
    rw [hδ, show Quasithin.conjSub δ Ubar = Ubar.map (MulAut.conj δ).toMonoidHom from rfl, h1, h2]
    exact Subgroup.map_mono hNbar
  have hQbar'P : Qbar' ≤ Pbar' := Subgroup.map_mono hQbarP
  have hQbar'card : Nat.card Qbar' = 9 := by
    dsimp only [Qbar']
    rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hQbar]
  have hQbar'3 : ∀ q ∈ Qbar', q ^ 3 = 1 := by
    intro q hq
    dsimp only [Qbar'] at hq
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_pow, hQbar3 r hr, map_one]
  have hQbar'grp : IsPGroup 3 Qbar' := IsPGroup.of_card (n := 2) (by rw [hQbar'card]; norm_num)
  have h3ker : ¬ 3 ∣ Nat.card π.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
    rw [hk]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  obtain ⟨Q, hQp, hQle, hQmap, hQdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker π hπ h3ker hQbar'grp
  let Pc : Subgroup ↥C := Pbar'.comap π
  let P : Subgroup Γ := Pc.map C.subtype
  have hQc : Q ≤ Pc := hQle.trans (Subgroup.comap_mono hQbar'P)
  have hQcard : Nat.card Q = 9 := by
    let f : ↥Q →* Δ := π.comp Q.subtype
    have hfk : f.ker = ⊥ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro hx
        have hmem : (x : ↥C) ∈ Q ⊓ π.ker := ⟨x.2, hx⟩
        rw [hQdisj] at hmem
        exact Subtype.ext (by simpa using hmem)
      · intro hx
        rw [hx]
        simp
    have hfr : f.range = Q.map π := by
      ext y
      simp [f]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfk, hfr, Subgroup.card_bot, one_mul, hQmap, hQbar'card] at h
    exact h.symm
  have hQ3 : ∀ q ∈ Q, q ^ 3 = 1 := by
    intro q hq
    have hq' : π q ∈ Qbar' := by
      have hmem : π q ∈ Q.map π := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
      rwa [hQmap] at hmem
    have hmem : q ^ 3 ∈ Q ⊓ π.ker := by
      refine ⟨Q.pow_mem hq 3, ?_⟩
      change π (q ^ 3) = 1
      rw [map_pow]
      exact hQbar'3 (π q) hq'
    rw [hQdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hUP : U ≤ P := by
    intro u hu
    refine Subgroup.mem_map.mpr ⟨⟨u, hUleC hu⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hUπP (Subgroup.mem_map.mpr ⟨⟨u, hUleC hu⟩, hu, rfl⟩)
  have hPcard : Nat.card P = 9 * Nat.card U := by
    have hUcard : Nat.card U = Nat.card π.ker * Nat.card Uπ := by
      have h1 : Nat.card U = Nat.card UC :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleC).toEquiv).symm
      have h2 : Nat.card π.ker * Nat.card Uπ = Nat.card UC := by
        let f : ↥UC →* Δ := π.comp UC.subtype
        have hfker : f.ker = π.ker.subgroupOf UC := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
          rfl
        have hfrange : f.range = Uπ := by
          ext y
          simp [f, Uπ]
        have h := Subgroup.card_ker_mul_card_range f
        rw [hfker, hfrange] at h
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerU).toEquiv] at h
        exact h
      rw [h1, h2]
    dsimp only [P]
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      CFSG.GroupTheory.card_comap_eq_card_ker_mul_card π hπ Pbar', hPbar'card, hUcard]
    ring
  have hPinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P := by
    intro α hα
    obtain ⟨g, hg⟩ := hAut α
    have hgeq : α = MulAut.conj g := by
      ext x
      rw [hg x, MulAut.conj_apply]
    have hgN : g ∈ Subgroup.normalizer (U : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hgeq]
      exact hα
    have hgC : g ∈ C := hNC hgN
    have hgUC : (⟨g, hgC⟩ : ↥C) ∈ Subgroup.normalizer (UC : Set ↥C) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hUleC]
      exact hgN
    have hπg : π ⟨g, hgC⟩ ∈ Subgroup.normalizer (Uπ : Set Δ) :=
      Subgroup.le_normalizer_map π ⟨⟨g, hgC⟩, hgUC, rfl⟩
    have hπgP : π ⟨g, hgC⟩ ∈ Subgroup.normalizer (Pbar' : Set Δ) := hNbar' hπg
    have hσPc : Pc.map (MulAut.conj (⟨g, hgC⟩ : ↥C)).toMonoidHom = Pc := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_comap] at hy ⊢
        have h := (Subgroup.mem_normalizer_iff.mp hπgP (π y)).mp hy
        simpa [map_mul] using h
      · intro hx
        refine Subgroup.mem_map.mpr ⟨(⟨g, hgC⟩ : ↥C)⁻¹ * x * ⟨g, hgC⟩, ?_, ?_⟩
        · rw [Subgroup.mem_comap] at hx ⊢
          have hinv : (π ⟨g, hgC⟩)⁻¹ ∈ Subgroup.normalizer (Pbar' : Set Δ) :=
            (Subgroup.normalizer (Pbar' : Set Δ)).inv_mem hπgP
          have h := (Subgroup.mem_normalizer_iff.mp hinv (π x)).mp hx
          simpa [map_mul] using h
        · change (⟨g, hgC⟩ : ↥C) * ((⟨g, hgC⟩ : ↥C)⁻¹ * x * ⟨g, hgC⟩) * (⟨g, hgC⟩ : ↥C)⁻¹ = x
          group
    rw [hgeq]
    exact Eq.trans (pspr_map_conj_subtype hgC Pc) (by rw [hσPc])
  refine ⟨U, P, Q.map C.subtype, hU, hUP, hPcard, hPinv, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono hQc
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hQcard]
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hq
    simpa using congrArg (Subgroup.subtype C) (hQ3 c hc)

theorem IndexNinePackage.inner {Δ : Type*} [Group Δ] (h : IndexNinePackage Δ) :
    InnerIndexNinePackage Δ := by
  obtain ⟨U, P, Q, hU, hUP, hP, hinv, hQP, hQ, hQ3⟩ := h
  refine ⟨U, P, Q, hU, hUP, hP, fun g hg => ?_, hQP, hQ, hQ3⟩
  have hUg : U.map (MulAut.conj g).toMonoidHom = U := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
  have hPg := hinv (MulAut.conj g) hUg
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    have : g * p * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := ⟨p, hp, rfl⟩
    rwa [hPg] at this
  · intro hp
    rw [← hPg] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqp
    have : q = p := by
      have := congrArg (fun t => g⁻¹ * t * g) hqp
      simpa [mul_assoc] using this
    exact this ▸ hq

theorem card_orbit_apply_of_mem_normalizer {Ω : Type*} {U : Subgroup (Equiv.Perm Ω)}
    {r : Equiv.Perm Ω} (hr : r ∈ Subgroup.normalizer (U : Set (Equiv.Perm Ω))) (ω : Ω) :
    Nat.card (MulAction.orbit U (r ω)) = Nat.card (MulAction.orbit U ω) := by
  have key : ∀ x : Ω, x ∈ MulAction.orbit U ω ↔ r x ∈ MulAction.orbit U (r ω) := by
    intro x
    simp only [MulAction.mem_orbit_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨⟨r * u * r⁻¹, (Subgroup.mem_normalizer_iff.mp hr u).mp u.2⟩, ?_⟩
      simp [Equiv.Perm.mul_apply]
    · rintro ⟨u, hu⟩
      have hmem : r⁻¹ * (u : Equiv.Perm Ω) * r ∈ U := by
        have h := (Subgroup.mem_normalizer_iff.mp hr (r⁻¹ * u * r)).mpr
        simpa [mul_assoc] using h
      refine ⟨⟨_, hmem⟩, ?_⟩
      change (r⁻¹ * (u : Equiv.Perm Ω) * r) ω = x
      simp [Equiv.Perm.mul_apply, hu]
  exact (Nat.card_congr (Equiv.subtypeEquiv r key)).symm

theorem center_le_of_centralizer_le {G : Type*} [Group G] {U R₀ : Subgroup G} (hR : R₀ ≤ U)
    (hC : U ⊓ Subgroup.centralizer (R₀ : Set G) ≤ R₀) :
    ∀ x ∈ U, (∀ y ∈ U, x * y = y * x) → x ∈ R₀ ∧ ∀ y ∈ R₀, x * y = y * x := by
  intro x hx hc
  have hxc : x ∈ Subgroup.centralizer (R₀ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hc y (hR hy)).symm
  exact ⟨hC ⟨hx, hxc⟩, fun y hy => hc y (hR hy)⟩

private lemma pspr_exists_aut_quotient {Γ Δ : Type*} [Group Γ] [Group Δ] {C : Subgroup Γ}
    (π : ↥C →* Δ) (hπ : Function.Surjective π) (αC : MulAut ↥C)
    (hKc : (π.ker).map αC.toMonoidHom = π.ker) :
    ∃ β : MulAut Δ, ∀ y : ↥C, β (π y) = π (αC y) := by
  classical
  let qβ : MulAut (↥C ⧸ π.ker) := QuotientGroup.congr π.ker π.ker αC hKc
  let e : (↥C ⧸ π.ker) ≃* Δ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have he : ∀ c : ↥C, e (QuotientGroup.mk c) = π c := by
    intro c
    rfl
  refine ⟨e.symm.trans (qβ.trans e), ?_⟩
  intro y
  have h1 : e.symm (π y) = QuotientGroup.mk y := by
    rw [MulEquiv.symm_apply_eq]
    exact he y
  have h2 : qβ (QuotientGroup.mk y) = QuotientGroup.mk (αC y) := by
    rw [show qβ = QuotientGroup.congr π.ker π.ker αC hKc from rfl]
    exact QuotientGroup.congr_mk π.ker π.ker αC hKc y
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, h2, he]

theorem exists_permutes_of_invariant_cover {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] {Γ : Type} [Group Γ] [Finite Γ] {U P : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUP : U ≤ P)
    (hP : Nat.card P = 3 * Nat.card U)
    (hinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P)
    {a g : Γ} (ha : a ∈ P) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (hg : g * a * g⁻¹ = a⁻¹)
    (f : ↥K →* Γ) (hf : Function.Surjective f) (hker : f.ker = Subgroup.center ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 3) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  let T : Subgroup ↥K := (S ⊓ K).subgroupOf K
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    · rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T]
      exact hSK.2.2
  have hTindex : ¬ 2 ∣ T.index := hSK.2.2
  let P₂ : Sylow 2 ↥K := hT.2.1.toSylow hTindex
  let Q : Sylow 2 Γ := P₂.mapSurjective hf
  have hQ : (Q : Subgroup Γ) = T.map f := Sylow.coe_mapSurjective hf P₂
  have hUindex : ¬ 2 ∣ U.index := by
    have h := hU.2.2
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
    exact h
  let U' : Sylow 2 Γ := hU.2.1.toSylow hUindex
  have hU'coe : (U' : Subgroup Γ) = U := IsPGroup.toSylow_coe hU.2.1 hUindex
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Γ Q U'
  have hcQ : (Q : Subgroup Γ).map (MulAut.conj c).toMonoidHom = U := by
    have h1 := congrArg (fun X : Sylow 2 Γ => (X : Subgroup Γ)) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hU'coe] at h1
    exact h1
  let f' : ↥K →* Γ := (MulAut.conj c).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj c).surjective.comp hf
  have hker' : f'.ker = Subgroup.center ↥K := by
    dsimp only [f']
    rw [MonoidHom.ker_comp_of_injective f (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective, hker]
  have hTmap : T.map f' = U := by
    dsimp only [f']
    rw [← Subgroup.map_map, ← hQ, hcQ]
  let H' : Subgroup ↥K := Subgroup.comap f' P
  have hH'card : Nat.card H' = 9 * Nat.card U := by
    dsimp only [H']
    rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card f' hf', hker', hZ, hP]
    ring
  let H₀ : Subgroup Y := H'.map K.subtype
  have hH₀card : Nat.card H₀ = 9 * Nat.card U := by
    dsimp only [H₀]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hH'card]
  have hTcard : Nat.card ↥(S ⊓ K) = Nat.card U := by
    have hTdisj : T ⊓ f'.ker = ⊥ := by
      obtain ⟨n, hn⟩ := hT.2.1.exists_card_eq
      have hcop : Nat.Coprime (Nat.card T) (Nat.card f'.ker) := by
        rw [hker', hZ, hn]
        exact Nat.Coprime.pow_left _ (by norm_num)
      exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hTmapcard : Nat.card (T.map f') = Nat.card T := by
      have hkercomp : (f'.comp T.subtype).ker = ⊥ := by
        ext x
        rw [Subgroup.mem_bot, MonoidHom.mem_ker, MonoidHom.comp_apply]
        change f' (x : ↥K) = 1 ↔ x = 1
        constructor
        · intro hx
          have hmem : (x : ↥K) ∈ T ⊓ f'.ker := ⟨x.2, hx⟩
          rw [hTdisj] at hmem
          exact Subtype.ext hmem
        · intro hx
          rw [hx]
          simp
      have h := Subgroup.card_ker_mul_card_range (f'.comp T.subtype)
      rw [hkercomp, MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.card_bot] at h
      simpa using h
    have hTs : Nat.card T = Nat.card ↥(S ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hUT : Nat.card U = Nat.card T := by
      rw [← hTmap]
      exact hTmapcard
    exact hTs.symm.trans hUT.symm
  have hH₀card9 : Nat.card H₀ = 9 * Nat.card ↥(S ⊓ K) := by
    rw [hH₀card, hTcard]
  have hS₀leH₀ : S ⊓ K ≤ H₀ := by
    intro s hs
    refine Subgroup.mem_map.mpr ⟨⟨s, hs.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hmem : f' ⟨s, hs.2⟩ ∈ T.map f' :=
      Subgroup.mem_map.mpr ⟨⟨s, hs.2⟩, by rw [Subgroup.mem_subgroupOf]; exact hs, rfl⟩
    rw [hTmap] at hmem
    exact hUP hmem
  have hTconj : ∀ t ∈ S, T.map (MulAut.conjNormal (H := K) t).toMonoidHom = T := by
    intro t ht
    apply Subgroup.map_injective K.subtype_injective
    rw [pspr_map_conjNormal_subtype (N := K) t T]
    have hset : (S ⊓ K).map (MulAut.conj t).toMonoidHom = S ⊓ K := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyS, hyK⟩, rfl⟩
        exact ⟨S.mul_mem (S.mul_mem ht hyS) (S.inv_mem ht), hK.conj_mem _ hyK t⟩
      · intro hx
        refine ⟨t⁻¹ * x * t, ⟨S.mul_mem (S.mul_mem (S.inv_mem ht) hx.1) ht, ?_⟩, ?_⟩
        · simpa using hK.conj_mem _ hx.2 t⁻¹
        · change t * (t⁻¹ * x * t) * t⁻¹ = x
          group
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hset
  have hstep : ∀ t ∈ S, ∀ x ∈ H', (MulAut.conjNormal (H := K) t) x ∈ H' := by
    intro t ht x hx
    have hZchar : (Subgroup.center ↥K).map (MulAut.conjNormal (H := K) t).toMonoidHom =
        Subgroup.center ↥K :=
      Subgroup.characteristic_iff_map_eq.mp (Subgroup.centerCharacteristic (G := ↥K)) _
    obtain ⟨αt, hαt⟩ := pspr_exists_aut_quotient f' hf' (MulAut.conjNormal (H := K) t)
      (by rw [hker']; exact hZchar)
    have hcomp : αt.toMonoidHom.comp f' =
        f'.comp (MulAut.conjNormal (H := K) t).toMonoidHom := by
      ext y
      exact hαt y
    have hαtU : U.map αt.toMonoidHom = U := by
      calc U.map αt.toMonoidHom = (T.map f').map αt.toMonoidHom := by rw [hTmap]
        _ = T.map (αt.toMonoidHom.comp f') := by rw [Subgroup.map_map]
        _ = T.map (f'.comp (MulAut.conjNormal (H := K) t).toMonoidHom) := by rw [hcomp]
        _ = (T.map (MulAut.conjNormal (H := K) t).toMonoidHom).map f' := by
            rw [Subgroup.map_map]
        _ = U := by rw [hTconj t ht, hTmap]
    have hPmap : P.map αt.toMonoidHom = P := hinv αt hαtU
    rw [Subgroup.mem_comap] at hx ⊢
    rw [← hαt x, ← hPmap]
    exact Subgroup.mem_map.mpr ⟨f' x, hx, rfl⟩
  have hH'conj : ∀ t ∈ S, H'.map (MulAut.conjNormal (H := K) t).toMonoidHom = H' := by
    intro t ht
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hstep t ht y hy
    · intro hx
      have hx' : (MulAut.conjNormal (H := K) t).symm x ∈ H' := by
        have h := hstep t⁻¹ (S.inv_mem ht) x hx
        rwa [show MulAut.conjNormal (H := K) t⁻¹ = (MulAut.conjNormal (H := K) t).symm
          from map_inv _ _] at h
      exact Subgroup.mem_map.mpr ⟨_, hx', by simp⟩
  have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp only [H₀]
    change (H'.map K.subtype).map (MulAut.conj t).toMonoidHom = H'.map K.subtype
    rw [← pspr_map_conjNormal_subtype (N := K) t H', hH'conj t ht]
  have hH₀leK : H₀ ≤ K := Subgroup.map_subtype_le _
  have hSH : S ⊓ H₀ = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ hH₀leK) (le_inf inf_le_left hS₀leH₀)
  have hSHcard : Nat.card ↥(S ⊔ H₀) = 9 * Nat.card S := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := S) (K := H₀) hnorm
    rw [hSH, hH₀card9] at h
    have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card ↥(S ⊓ K) =
        (9 * Nat.card S) * Nat.card ↥(S ⊓ K) := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  letI : Fintype ↥(Subgroup.center ↥K) := Fintype.ofFinite _
  have hZnt : 1 < Fintype.card ↥(Subgroup.center ↥K) := by
    rw [← Nat.card_eq_fintype_card, hZ]
    norm_num
  obtain ⟨ζc, hζc⟩ := Fintype.exists_ne_of_one_lt_card hZnt (1 : ↥(Subgroup.center ↥K))
  let ζ : ↥K := (ζc : ↥K)
  have hζmem : ζ ∈ Subgroup.center ↥K := ζc.2
  have hζne : ζ ≠ 1 := by
    intro h
    exact hζc (Subtype.ext h)
  have hζ3 : ζ ^ 3 = 1 := by
    have h := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K))
      (pow_card_eq_one' (x := ζc))
    rw [hZ] at h
    simpa using h
  have hζker : ζ ∈ f'.ker := by rw [hker']; exact hζmem
  have hζf : f' ζ = 1 := MonoidHom.mem_ker.mp hζker
  obtain ⟨â, hâ⟩ := hf' a
  obtain ⟨ĝ, hĝ⟩ := hf' g
  have hâ3 : â ^ 3 = 1 := by
    refine CFSG.SectionRank.QTK.Insp443.CoverThree.pow_three_eq_one_of_inv
      (K := ↥K) (X := Γ) (f := f') (a := â) (g := ĝ) ?_ ?_ ?_ ?_
    · rw [hker']
    · intro z hz
      rw [hker'] at hz
      have h := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K))
        (pow_card_eq_one' (x := ⟨z, hz⟩))
      rw [hZ] at h
      simpa using h
    · rw [hâ, ha3]
    · rw [hâ, hĝ, hg]
  have hâne : â ≠ 1 := by
    intro h
    rw [h, map_one] at hâ
    exact ha1 hâ.symm
  have hζa : ζ ≠ â := by
    intro h
    have h1 := congrArg f' h
    rw [hζf, hâ] at h1
    exact ha1 h1.symm
  have hζa2 : ζ ≠ â ^ 2 := by
    intro h
    have h1 : a ^ 2 = 1 := by
      have h2 := congrArg f' h
      rw [hζf, map_pow, hâ] at h2
      exact h2.symm
    have h2 : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, h1]; simp
    exact ha1 h2
  have hcomm : Commute â ζ := Subgroup.mem_center_iff.mp hζmem â
  have hζnot : ζ ∉ Subgroup.zpowers â :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hâ3 hζne hζa hζa2
  have hcardcl : Nat.card (Subgroup.closure ({â, ζ} : Set ↥K)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hâ3 hζ3 hcomm hâne hζnot
  let E : Subgroup Y := (Subgroup.closure ({â, ζ} : Set ↥K)).map K.subtype
  have hEcard : Nat.card E = 9 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardcl]
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  have hE3pg : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hc : ⁅â, ζ⁆ = 1 := hcomm.commutator_eq
    have hzx : Commute ⁅â, ζ⁆ â := by rw [hc]; exact Commute.one_left _
    have hzy : Commute ⁅â, ζ⁆ ζ := by rw [hc]; exact Commute.one_left _
    have hy3 : y ^ 3 = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
        hâ3 hζ3 hzx hzy hy
    exact congrArg (fun z : ↥K => (z : Y)) hy3
  have hEnoncyc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hexpdvd : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE3 g g.2)
    rw [IsCyclic.exponent_eq_card, hEcard] at hexpdvd
    norm_num at hexpdvd
  have hâH' : â ∈ H' := by
    change f' â ∈ P
    rw [hâ]
    exact ha
  have hζH' : ζ ∈ H' := by
    change f' ζ ∈ P
    rw [hζf]
    exact P.one_mem
  have hEH' : Subgroup.closure ({â, ζ} : Set ↥K) ≤ H' := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hâH'
    · exact hζH'
  have hEH₀ : E ≤ H₀ := by
    dsimp only [E, H₀]
    exact Subgroup.map_mono hEH'
  have hEinfS : E ⊓ S = ⊥ := by
    have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
      obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
      rw [hEcard, hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hperm : CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hEinfS ?_
    calc Nat.card ↥(E ⊔ S) ≤ Nat.card ↥(S ⊔ H₀) :=
          Subgroup.card_le_of_le (sup_le (hEH₀.trans le_sup_right) le_sup_left)
      _ = 9 * Nat.card S := hSHcard
      _ = Nat.card E * Nat.card S := by rw [hEcard]
  exact ⟨E, Subgroup.map_subtype_le _, hEne, hE3pg, hE3, hEnoncyc, hperm⟩

theorem exists_permutes_of_indexThreePackage {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [K.Normal] {Γ : Type} [Group Γ] [Finite Γ] (hΓ : IndexThreePackage Γ)
    (hZ : Nat.card (Subgroup.center ↥K) = 3) (e : ↥K ⧸ Subgroup.center ↥K ≃* Γ)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  obtain ⟨U, P, a, g, hU, hUP, hP, hinv, ha, ha1, ha3, hg⟩ := hΓ
  refine exists_permutes_of_invariant_cover hU hUP hP hinv ha ha1 ha3 hg
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ hZ hS
  ext x
  simp [MonoidHom.mem_ker]

theorem exists_permutes_of_indexNinePackage {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [K.Normal] {Γ : Type} [Group Γ] [Finite Γ] (hΓ : IndexNinePackage Γ) (e : ↥K ≃* Γ)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  obtain ⟨U, P, Q, hU, hUP, hP, hinv, hQP, hQ, hQ3⟩ := hΓ
  exact exists_permutes_of_invariant_member hU hUP hP hinv hQP hQ hQ3 e hS

theorem innerIndexNinePackage_of_unique_fixed {Δ X : Type*} [Group Δ] [MulAction Δ X]
    {U : Subgroup Δ} {x₀ : X} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hfix : ∀ u ∈ U, u • x₀ = x₀)
    (huniq : ∀ d : Δ, (∀ u ∈ U, u • (d • x₀) = d • x₀) → d • x₀ = x₀)
    (hcard : Nat.card (MulAction.stabilizer Δ x₀) = 9 * Nat.card U)
    {x y : Δ} (hx₀ : x • x₀ = x₀) (hy₀ : y • x₀ = x₀) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    InnerIndexNinePackage Δ := by
  have hNP : Subgroup.normalizer (U : Set Δ) ≤ MulAction.stabilizer Δ x₀ :=
    normalizer_le_stabilizer_of_unique_fixed (C := ⊤) le_top hfix fun c _ h => huniq c h
  have hQ9 : Nat.card (Subgroup.closure ({x, y} : Set Δ)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3 hy3 hxy hx1 hyx
  refine ⟨U, MulAction.stabilizer Δ x₀, Subgroup.closure {x, y}, hU,
    fun u hu => hfix u hu, hcard, fun g hg => ?_, ?_, hQ9, fun q hq => ?_⟩
  · exact Subgroup.le_normalizer (hNP hg)
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hx₀
    · exact hy₀
  · have hcomm : ⁅x, y⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm]; exact hxy
    exact pow_three_eq_one_of_mem_closure_cubic hx3 hy3 (by rw [hcomm]; exact Commute.one_left x)
      (by rw [hcomm]; exact Commute.one_left y) hq

theorem IndexNinePackage.of_inner {Δ : Type*} [Group Δ]
    (hΔ : ∀ β : MulAut Δ, ∃ d : Δ, ∀ x : Δ, β x = d * x * d⁻¹) (h : InnerIndexNinePackage Δ) :
    IndexNinePackage Δ := by
  obtain ⟨U, P, Q, hU, hUP, hP, hN, hQP, hQ, hQ3⟩ := h
  refine ⟨U, P, Q, hU, hUP, hP, fun α hα => ?_, hQP, hQ, hQ3⟩
  obtain ⟨d, hd⟩ := hΔ α
  have hmap : ∀ H : Subgroup Δ, ∀ x : Δ, x ∈ H.map α.toMonoidHom ↔ d⁻¹ * x * d ∈ H := by
    intro H x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, hd]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨d⁻¹ * x * d, hx, by group⟩
  have hdU : d⁻¹ ∈ Subgroup.normalizer (U : Set Δ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [inv_inv, ← hmap U u, hα]
  have hdP := hN hdU
  ext x
  have h := Subgroup.mem_normalizer_iff.mp hdP x
  rw [inv_inv] at h
  rw [hmap]
  exact h.symm

private lemma pspr_map_subtype_map_aut {Γ : Type*} [Group Γ] {C : Subgroup Γ} (α : MulAut Γ)
    (αC : MulAut ↥C) (hαC : ∀ c : ↥C, ((αC c : ↥C) : Γ) = α c) (H : Subgroup ↥C) :
    (H.map C.subtype).map α.toMonoidHom = (H.map αC.toMonoidHom).map C.subtype := by
  ext x
  constructor
  · rintro ⟨-, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨αC h, ⟨h, hh, rfl⟩, by simpa using hαC h⟩
  · rintro ⟨-, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨C.subtype h, ⟨h, hh, rfl⟩, by simpa using (hαC h).symm⟩

private lemma pspr_invariance_conj {Δ : Type*} [Group Δ] {U P : Subgroup Δ} {δ : Δ}
    (hinv : ∀ γ : MulAut Δ, U.map γ.toMonoidHom = U → P.map γ.toMonoidHom = P)
    (γ : MulAut Δ)
    (hγ : (U.map (MulAut.conj δ).toMonoidHom).map γ.toMonoidHom =
      U.map (MulAut.conj δ).toMonoidHom) :
    (P.map (MulAut.conj δ).toMonoidHom).map γ.toMonoidHom =
      P.map (MulAut.conj δ).toMonoidHom := by
  let A : MulAut Δ := MulAut.conj δ
  have hid : A.symm.toMonoidHom.comp A.toMonoidHom = MonoidHom.id Δ := by
    ext x
    simp [A, MulAut.mul_apply]
  have hid' : A.toMonoidHom.comp A.symm.toMonoidHom = MonoidHom.id Δ := by
    ext x
    simp [A, MulAut.mul_apply]
  have hγ' : U.map (A.symm * γ * A).toMonoidHom = U := by
    have h := congrArg (Subgroup.map A.symm.toMonoidHom) hγ
    simp only [Subgroup.map_map] at h
    rw [hid, Subgroup.map_id] at h
    rwa [show A.symm.toMonoidHom.comp (γ.toMonoidHom.comp A.toMonoidHom) =
      (A.symm * γ * A).toMonoidHom from rfl] at h
  have hP' : P.map (A.symm * γ * A).toMonoidHom = P := hinv (A.symm * γ * A) hγ'
  have h := congrArg (Subgroup.map A.toMonoidHom) hP'
  simp only [Subgroup.map_map] at h
  rw [show A.toMonoidHom.comp ((A.symm * γ * A).toMonoidHom) =
      γ.toMonoidHom.comp A.toMonoidHom from by
    ext x
    simp [A, MulAut.mul_apply]
    group] at h
  dsimp only [A] at h ⊢
  rw [← Subgroup.map_map] at h
  exact h

private lemma pspr_indexNineSylow {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {U C : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUC : U ≤ C)
    (π : ↥C →* Δ) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((U.subgroupOf C).map π) ⊤ ∧
      Nat.card U = Nat.card π.ker * Nat.card ((U.subgroupOf C).map π) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUCsyl : CFSG.QuasithinUnique.IsSylowTwoOf (U.subgroupOf C) ⊤ := by
    refine ⟨le_top, hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUC).symm, ?_⟩
    rw [show ((U.subgroupOf C).subgroupOf ⊤).index = (U.subgroupOf C).index from
      Subgroup.relIndex_top_right _]
    have hUi : ¬ 2 ∣ U.index := by
      have h := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
    show ¬ 2 ∣ (U.subgroupOf C).index
    intro h2
    refine hUi ?_
    rw [← Subgroup.relIndex_mul_index hUC]
    exact dvd_mul_of_dvd_left h2 C.index
  have hUCidx : ¬ 2 ∣ (U.subgroupOf C).index := by
    have h := hUCsyl.2.2
    rwa [show ((U.subgroupOf C).subgroupOf ⊤).index = (U.subgroupOf C).index from
      Subgroup.relIndex_top_right _] at h
  have hkerU : π.ker ≤ U.subgroupOf C := by
    have hsup : IsPGroup 2 ↥((U.subgroupOf C) ⊔ π.ker) :=
      hUCsyl.2.1.to_sup_of_normal_right hker
    have hmax := CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le (P := U.subgroupOf C)
      (Q := (U.subgroupOf C) ⊔ π.ker) (H := ⊤) hUCsyl hsup le_top le_sup_left
    rw [← hmax]
    exact le_sup_right
  have hUπsyl : CFSG.QuasithinUnique.IsSylowTwoOf ((U.subgroupOf C).map π) ⊤ := by
    refine ⟨le_top, hUCsyl.2.1.map π, ?_⟩
    rw [show (((U.subgroupOf C).map π).subgroupOf ⊤).index =
      ((U.subgroupOf C).map π).index from Subgroup.relIndex_top_right _]
    exact fun h2 => hUCidx (dvd_trans h2
      (Subgroup.index_map_dvd (f := π) (U.subgroupOf C) hπ))
  have hUcard : Nat.card U = Nat.card π.ker * Nat.card ((U.subgroupOf C).map π) := by
    have h1 : Nat.card U = Nat.card (U.subgroupOf C) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv).symm
    have h2 : Nat.card π.ker * Nat.card ((U.subgroupOf C).map π) =
        Nat.card (U.subgroupOf C) := by
      let f : ↥(U.subgroupOf C) →* Δ := π.comp (U.subgroupOf C).subtype
      have hfker : f.ker = π.ker.subgroupOf (U.subgroupOf C) := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        rfl
      have hfrange : f.range = (U.subgroupOf C).map π := by
        ext y
        simp [f]
      have h := Subgroup.card_ker_mul_card_range f
      rw [hfker, hfrange] at h
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerU).toEquiv] at h
      exact h
    rw [h1, h2]
  exact ⟨hUπsyl, hUcard⟩

private lemma pspr_indexNineP {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {U C : Subgroup Γ} (hUC : U ≤ C) (π : ↥C →* Δ) (hπ : Function.Surjective π)
    {Pbar : Subgroup Δ}
    (hUπP : (U.subgroupOf C).map π ≤ Pbar)
    (hPbar : Nat.card Pbar = 9 * Nat.card ((U.subgroupOf C).map π))
    (hUcard : Nat.card U = Nat.card π.ker * Nat.card ((U.subgroupOf C).map π)) :
    U ≤ (Pbar.comap π).map C.subtype ∧
      Nat.card ((Pbar.comap π).map C.subtype) = 9 * Nat.card U := by
  constructor
  · intro u hu
    refine Subgroup.mem_map.mpr ⟨⟨u, hUC hu⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hUπP (Subgroup.mem_map.mpr ⟨⟨u, hUC hu⟩, hu, rfl⟩)
  · rw [Subgroup.card_map_of_injective C.subtype_injective,
      CFSG.GroupTheory.card_comap_eq_card_ker_mul_card π hπ Pbar, hPbar, hUcard]
    ring

private lemma pspr_indexNineInvariance {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {U C : Subgroup Γ} (hUC : U ≤ C) (π : ↥C →* Δ) (hπ : Function.Surjective π)
    (hα : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      C.map α.toMonoidHom = C ∧
        (π.ker.map C.subtype).map α.toMonoidHom = π.ker.map C.subtype)
    {Pbar : Subgroup Δ}
    (hinv : ∀ β : MulAut Δ, ((U.subgroupOf C).map π).map β.toMonoidHom =
      (U.subgroupOf C).map π → Pbar.map β.toMonoidHom = Pbar) :
    ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      ((Pbar.comap π).map C.subtype).map α.toMonoidHom = (Pbar.comap π).map C.subtype := by
  intro α hαU
  obtain ⟨hC, hK⟩ := hα α hαU
  let αC : MulAut ↥C := (α.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  have hαC : ∀ c : ↥C, ((αC c : ↥C) : Γ) = α c := by
    intro c
    rfl
  have hKc : (π.ker).map αC.toMonoidHom = π.ker := by
    apply Subgroup.map_injective C.subtype_injective
    rw [← pspr_map_subtype_map_aut α αC hαC π.ker, hK]
  obtain ⟨β, hβ⟩ := pspr_exists_aut_quotient π hπ αC hKc
  have hαC_UC : (U.subgroupOf C).map αC.toMonoidHom = U.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [← pspr_map_subtype_map_aut α αC hαC (U.subgroupOf C),
      Subgroup.map_subgroupOf_eq_of_le hUC, hαU]
  have hβUπ : ((U.subgroupOf C).map π).map β.toMonoidHom = (U.subgroupOf C).map π := by
    have hcomp : β.toMonoidHom.comp π = π.comp αC.toMonoidHom := by
      ext y
      exact hβ y
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hαC_UC]
  have hPbar : Pbar.map β.toMonoidHom = Pbar := hinv β hβUπ
  have hαC_Pc_le : (Pbar.comap π).map αC.toMonoidHom ≤ Pbar.comap π := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_comap] at hz ⊢
    have hmem : β (π z) ∈ Pbar.map β.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨π z, hz, rfl⟩
    rwa [hPbar, hβ z] at hmem
  have hαC_Pc : (Pbar.comap π).map αC.toMonoidHom = Pbar.comap π :=
    Subgroup.eq_of_le_of_card_ge hαC_Pc_le (by
      rw [Subgroup.card_map_of_injective αC.injective])
  rw [pspr_map_subtype_map_aut α αC hαC (Pbar.comap π), hαC_Pc]

private lemma pspr_indexNineQ {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {C : Subgroup Γ} (π : ↥C →* Δ) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    {Pbar Qbar : Subgroup Δ} (hQbarP : Qbar ≤ Pbar) (hQbar : Nat.card Qbar = 9)
    (hQbar3 : ∀ q ∈ Qbar, q ^ 3 = 1) :
    ∃ Q : Subgroup Γ, Q ≤ (Pbar.comap π).map C.subtype ∧ Nat.card Q = 9 ∧
      ∀ q ∈ Q, q ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQbar'grp : IsPGroup 3 Qbar := IsPGroup.of_card (n := 2) (by rw [hQbar]; norm_num)
  have h3ker : ¬ 3 ∣ Nat.card π.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
    rw [hk]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  obtain ⟨Q, -, hQle, hQmap, hQdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker π hπ h3ker hQbar'grp
  have hQc : Q ≤ Pbar.comap π := hQle.trans (Subgroup.comap_mono hQbarP)
  have hQcard : Nat.card Q = 9 := by
    let f : ↥Q →* Δ := π.comp Q.subtype
    have hfk : f.ker = ⊥ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro hx
        have hmem : (x : ↥C) ∈ Q ⊓ π.ker := ⟨x.2, hx⟩
        rw [hQdisj] at hmem
        exact Subtype.ext (by simpa using hmem)
      · intro hx
        rw [hx]
        simp
    have hfr : f.range = Q.map π := by
      ext y
      simp [f]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfk, hfr, Subgroup.card_bot, one_mul, hQmap, hQbar] at h
    exact h.symm
  have hQ3 : ∀ q ∈ Q, q ^ 3 = 1 := by
    intro q hq
    have hq' : π q ∈ Qbar := by
      have hmem : π q ∈ Q.map π := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
      rwa [hQmap] at hmem
    have hmem : q ^ 3 ∈ Q ⊓ π.ker := by
      refine ⟨Q.pow_mem hq 3, ?_⟩
      change π (q ^ 3) = 1
      rw [map_pow]
      exact hQbar3 (π q) hq'
    rw [hQdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine ⟨Q.map C.subtype, Subgroup.map_mono hQc, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hQcard]
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hq
    simpa using congrArg (Subgroup.subtype C) (hQ3 c hc)

private lemma pspr_indexThreeP {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {U C : Subgroup Γ} (hUC : U ≤ C) (π : ↥C →* Δ) (hπ : Function.Surjective π)
    {Pbar : Subgroup Δ}
    (hUπP : (U.subgroupOf C).map π ≤ Pbar)
    (hPbar : Nat.card Pbar = 3 * Nat.card ((U.subgroupOf C).map π))
    (hUcard : Nat.card U = Nat.card π.ker * Nat.card ((U.subgroupOf C).map π)) :
    U ≤ (Pbar.comap π).map C.subtype ∧
      Nat.card ((Pbar.comap π).map C.subtype) = 3 * Nat.card U := by
  constructor
  · intro u hu
    refine Subgroup.mem_map.mpr ⟨⟨u, hUC hu⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hUπP (Subgroup.mem_map.mpr ⟨⟨u, hUC hu⟩, hu, rfl⟩)
  · rw [Subgroup.card_map_of_injective C.subtype_injective,
      CFSG.GroupTheory.card_comap_eq_card_ker_mul_card π hπ Pbar, hPbar, hUcard]
    ring

theorem indexNinePackage_of_char_quotient {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ]
    [Finite Δ] {U C : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUC : U ≤ C)
    (π : ↥C →* Δ) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hα : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      C.map α.toMonoidHom = C ∧
        (π.ker.map C.subtype).map α.toMonoidHom = π.ker.map C.subtype)
    (hΔ : IndexNinePackage Δ) : IndexNinePackage Γ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', P', Q', hU', hU'P, hP', hinv', hQ'P, hQ', hQ'3⟩ := hΔ
  obtain ⟨hUπsyl, hUcard⟩ := pspr_indexNineSylow hU hUC π hπ hker
  obtain ⟨δ, -, hδ⟩ :=
    CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf (L := (⊤ : Subgroup Δ)) hU' hUπsyl
  have hδ' : (U.subgroupOf C).map π = U'.map (MulAut.conj δ).toMonoidHom := by
    simpa [Quasithin.conjSub] using hδ
  have hUπP : (U.subgroupOf C).map π ≤ P'.map (MulAut.conj δ).toMonoidHom := by
    rw [hδ']
    exact Subgroup.map_mono hU'P
  have hPcard : Nat.card (P'.map (MulAut.conj δ).toMonoidHom) =
      9 * Nat.card ((U.subgroupOf C).map π) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hP']
    congr 1
    rw [hδ', Subgroup.card_map_of_injective (MulAut.conj δ).injective]
  have hinvP : ∀ β : MulAut Δ,
      ((U.subgroupOf C).map π).map β.toMonoidHom = (U.subgroupOf C).map π →
        (P'.map (MulAut.conj δ).toMonoidHom).map β.toMonoidHom =
          P'.map (MulAut.conj δ).toMonoidHom := by
    intro β hβ
    have hβ' : (U'.map (MulAut.conj δ).toMonoidHom).map β.toMonoidHom =
        U'.map (MulAut.conj δ).toMonoidHom := by
      rwa [← hδ']
    exact pspr_invariance_conj hinv' β hβ'
  have hQ'P' : Q'.map (MulAut.conj δ).toMonoidHom ≤
      P'.map (MulAut.conj δ).toMonoidHom := Subgroup.map_mono hQ'P
  have hQ'card : Nat.card (Q'.map (MulAut.conj δ).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hQ']
  have hQ'3' : ∀ q ∈ Q'.map (MulAut.conj δ).toMonoidHom, q ^ 3 = 1 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_pow, hQ'3 r hr, map_one]
  obtain ⟨hUP, hPcard'⟩ := pspr_indexNineP hUC π hπ hUπP hPcard hUcard
  have hPinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      (((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype).map α.toMonoidHom =
        ((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype :=
    pspr_indexNineInvariance hUC π hπ hα hinvP
  obtain ⟨Q, hQle, hQcard', hQ3'⟩ := pspr_indexNineQ π hπ hker hQ'P' hQ'card hQ'3'
  exact ⟨U, ((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype, Q,
    hU, hUP, hPcard', hPinv, hQle, hQcard', hQ3'⟩

private lemma pspr_indexThreeElements {Γ Δ : Type*} [Group Γ] [Finite Γ]
    [Group Δ] [Finite Δ] {C : Subgroup Γ} (π : ↥C →* Δ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) {Pbar : Subgroup Δ} {abar gbar : Δ}
    (habarP : abar ∈ Pbar) (habar1 : abar ≠ 1) (habar3 : abar ^ 3 = 1)
    (hgbar : gbar * abar * gbar⁻¹ = abar⁻¹) :
    ∃ a g : Γ, a ∈ (Pbar.comap π).map C.subtype ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧
      g * a * g⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have habar_order : orderOf abar = 3 := orderOf_eq_prime habar3 habar1
  have hzp_card : Nat.card (Subgroup.zpowers abar) = 3 := by
    rw [Nat.card_zpowers, habar_order]
  let K₀ : Subgroup ↥C := Subgroup.comap π (Subgroup.zpowers abar)
  have hK₀card : Nat.card K₀ = 3 * Nat.card π.ker := by
    dsimp only [K₀]
    rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card π hπ (Subgroup.zpowers abar),
      hzp_card]
    ring
  obtain ⟨A⟩ := (inferInstance : Nonempty (Sylow 3 ↥K₀))
  let A_sub : Subgroup ↥C := (A : Subgroup ↥K₀).map K₀.subtype
  have hA_syl : CFSG.ABGLocalTools.IsSylowOf 3 A_sub K₀ := ⟨A, rfl⟩
  have hA_card : Nat.card A_sub = 3 := by
    have h := hA_syl.card_eq
    rw [hK₀card] at h
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
    rw [hn] at h
    have h2 : (2 ^ n).factorization 3 = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      intro h3
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
    have hfact : (3 * 2 ^ n).factorization 3 = 1 := by
      rw [Nat.factorization_mul (by norm_num) (pow_ne_zero n (by norm_num)),
        Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three, h2, add_zero]
    rw [hfact] at h
    simpa using h
  have hdisj : A_sub ⊓ π.ker = ⊥ := by
    have hcop : Nat.Coprime (Nat.card A_sub) (Nat.card π.ker) := by
      rw [hA_card]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hA_map_le : A_sub.map π ≤ Subgroup.zpowers abar := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ (Subgroup.zpowers abar)]
    exact Subgroup.map_mono hA_syl.le
  have hA_map_card : Nat.card (A_sub.map π) = 3 := by
    have hker' : (π.comp A_sub.subtype).ker = ⊥ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro hx
        have hmem : (x : ↥C) ∈ A_sub ⊓ π.ker := ⟨x.2, hx⟩
        rw [hdisj] at hmem
        exact Subtype.ext (by simpa using hmem)
      · intro hx
        rw [hx]
        simp
    have h := Subgroup.card_ker_mul_card_range (π.comp A_sub.subtype)
    rw [hker', Subgroup.card_bot, one_mul] at h
    have hrange : (π.comp A_sub.subtype).range = A_sub.map π := by
      ext y
      simp
    rw [hrange] at h
    rwa [hA_card] at h
  have hA_map_eq : A_sub.map π = Subgroup.zpowers abar :=
    Subgroup.eq_of_le_of_card_ge hA_map_le (by rw [hA_map_card, hzp_card])
  obtain ⟨aC, haC, hπaC⟩ : ∃ aC ∈ A_sub, π aC = abar := by
    have hmem : abar ∈ A_sub.map π := by
      rw [hA_map_eq]
      exact Subgroup.mem_zpowers abar
    obtain ⟨x, hx, hπx⟩ := Subgroup.mem_map.mp hmem
    exact ⟨x, hx, hπx⟩
  have haC1 : aC ≠ 1 := by
    intro h
    rw [h, map_one] at hπaC
    exact habar1 hπaC.symm
  have haC3 : aC ^ 3 = 1 := by
    have hmem : aC ^ 3 ∈ A_sub ⊓ π.ker := by
      refine ⟨A_sub.pow_mem haC 3, ?_⟩
      change π (aC ^ 3) = 1
      rw [map_pow, hπaC, habar3]
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have haC_P : aC ∈ Pbar.comap π := by
    rw [Subgroup.mem_comap, hπaC]
    exact Subgroup.zpowers_le.mpr habarP (Subgroup.mem_zpowers abar)
  obtain ⟨g₀, hg₀⟩ := hπ gbar
  have hzpow_conj : (Subgroup.zpowers abar).map (MulAut.conj gbar).toMonoidHom =
      Subgroup.zpowers abar := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj gbar) abar) = Subgroup.zpowers abar
    rw [MulAut.conj_apply, hgbar, Subgroup.zpowers_inv]
  have hzpow_conj_inv : (Subgroup.zpowers abar).map (MulAut.conj gbar⁻¹).toMonoidHom =
      Subgroup.zpowers abar := by
    have h := congrArg (Subgroup.map ((MulAut.conj gbar).symm).toMonoidHom) hzpow_conj
    simp only [Subgroup.map_map] at h
    have hcomp : ((MulAut.conj gbar).symm).toMonoidHom.comp (MulAut.conj gbar).toMonoidHom =
        MonoidHom.id Δ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id] at h
    have hsymm : ((MulAut.conj gbar).symm : MulAut Δ) = MulAut.conj gbar⁻¹ := by
      ext x
      simp [MulAut.conj_apply]
    rw [hsymm] at h
    exact h.symm
  have hK₀_map : K₀.map (MulAut.conj g₀).toMonoidHom = K₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp only [K₀] at hy ⊢
      have hy' : π y ∈ Subgroup.zpowers abar := Subgroup.mem_comap.mp hy
      have hmem : (MulAut.conj gbar) (π y) ∈ Subgroup.zpowers abar := by
        rw [← hzpow_conj]
        exact Subgroup.mem_map.mpr ⟨π y, hy', rfl⟩
      refine Subgroup.mem_comap.mpr ?_
      change π (g₀ * y * g₀⁻¹) ∈ Subgroup.zpowers abar
      rw [map_mul, map_mul, map_inv, hg₀]
      simpa [MulAut.conj_apply] using hmem
    · intro hx
      refine Subgroup.mem_map.mpr ⟨g₀⁻¹ * x * g₀, ?_, ?_⟩
      · dsimp only [K₀] at hx ⊢
        have hx' : π x ∈ Subgroup.zpowers abar := Subgroup.mem_comap.mp hx
        have hmem : (MulAut.conj gbar⁻¹) (π x) ∈ Subgroup.zpowers abar := by
          rw [← hzpow_conj_inv]
          exact Subgroup.mem_map.mpr ⟨π x, hx', rfl⟩
        refine Subgroup.mem_comap.mpr ?_
        change π (g₀⁻¹ * x * g₀) ∈ Subgroup.zpowers abar
        rw [map_mul, map_mul, map_inv, hg₀]
        simpa [MulAut.conj_apply] using hmem
      · change (MulAut.conj g₀) (g₀⁻¹ * x * g₀) = x
        rw [MulAut.conj_apply]
        group
  let A' : Subgroup ↥C := A_sub.map (MulAut.conj g₀).toMonoidHom
  have hA'_le : A' ≤ K₀ := by
    intro x hx
    dsimp only [A'] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← hK₀_map]
    exact Subgroup.mem_map.mpr ⟨y, hA_syl.le hy, rfl⟩
  have hA'_card : Nat.card A' = Nat.card A_sub := by
    dsimp only [A']
    exact Subgroup.card_map_of_injective (MulAut.conj g₀).injective
  have hA'_syl : CFSG.ABGLocalTools.IsSylowOf 3 A' K₀ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hA'_le ?_
    rw [hA'_card, hA_syl.card_eq]
  obtain ⟨k, hkK₀, hkconj⟩ := hA_syl.exists_mem_conj hA'_syl
  have hA'_eq : A' = A_sub.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨k⁻¹ * x * k, (hkconj x).mp hx, ?_⟩
      change (MulAut.conj k) (k⁻¹ * x * k) = x
      rw [MulAut.conj_apply]
      group
    · rintro ⟨y, hy, rfl⟩
      refine (hkconj (k * y * k⁻¹)).mpr ?_
      have h : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [h]
  have hπk_zpow : π k ∈ Subgroup.zpowers abar := by
    have h := Subgroup.mem_comap.mp hkK₀
    exact h
  obtain ⟨aC', haC', hπaC'⟩ : ∃ aC' ∈ A_sub, π aC' = π k := by
    have hmem : π k ∈ A_sub.map π := by
      rw [hA_map_eq]
      exact hπk_zpow
    obtain ⟨x, hx, hπx⟩ := Subgroup.mem_map.mp hmem
    exact ⟨x, hx, hπx⟩
  let n : ↥C := k * aC'⁻¹
  have hn_ker : n ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    change π (k * aC'⁻¹) = 1
    rw [map_mul, map_inv, hπaC']
    group
  have hk_eq : k = n * aC' := by
    dsimp only [n]
    group
  haveI : IsCyclic ↥A_sub := isCyclic_of_prime_card (p := 3) hA_card
  have hA_sub_comm : ∀ x ∈ A_sub, ∀ y ∈ A_sub, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA_sub_conj_le : A_sub.map (MulAut.conj aC').toMonoidHom ≤ A_sub := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change aC' * y * aC'⁻¹ ∈ A_sub
    rw [hA_sub_comm aC' haC' y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hA_sub_conj : A_sub.map (MulAut.conj aC').toMonoidHom = A_sub :=
    Subgroup.eq_of_le_of_card_ge hA_sub_conj_le (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj aC').toMonoidHom)
        (MulAut.conj aC').injective])
  have hA_sub_map_k : A_sub.map (MulAut.conj k).toMonoidHom =
      A_sub.map (MulAut.conj n).toMonoidHom := by
    rw [hk_eq]
    rw [show MulAut.conj (n * aC') = MulAut.conj n * MulAut.conj aC' from by
      ext x
      simp [MulAut.conj_apply, mul_assoc]]
    rw [show (MulAut.conj n * MulAut.conj aC').toMonoidHom =
        (MulAut.conj n).toMonoidHom.comp (MulAut.conj aC').toMonoidHom from rfl]
    rw [← Subgroup.map_map, hA_sub_conj]
  have hA'_eq_n : A' = A_sub.map (MulAut.conj n).toMonoidHom := by
    rw [hA'_eq, hA_sub_map_k]
  have hA'_inv : A'.map (MulAut.conj n⁻¹).toMonoidHom = A_sub := by
    rw [hA'_eq_n]
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      change (MulAut.conj n⁻¹) (n * z * n⁻¹) ∈ A_sub
      have h : (MulAut.conj n⁻¹) (n * z * n⁻¹) = z := by
        rw [MulAut.conj_apply]
        group
      rwa [h]
    · intro hx
      refine Subgroup.mem_map.mpr ⟨n * x * n⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · change (MulAut.conj n⁻¹) (n * x * n⁻¹) = x
        rw [MulAut.conj_apply]
        group
  have hg_norm : A_sub.map (MulAut.conj (n⁻¹ * g₀)).toMonoidHom = A_sub := by
    rw [show MulAut.conj (n⁻¹ * g₀) = MulAut.conj n⁻¹ * MulAut.conj g₀ from by
      ext x
      simp [MulAut.conj_apply, mul_assoc]]
    rw [show (MulAut.conj n⁻¹ * MulAut.conj g₀).toMonoidHom =
        (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom from rfl]
    rw [← Subgroup.map_map]
    change A'.map (MulAut.conj n⁻¹).toMonoidHom = A_sub
    exact hA'_inv
  let g : ↥C := n⁻¹ * g₀
  have hπg : π g = gbar := by
    dsimp only [g]
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn_ker, hg₀]
    simp
  have hconj_inv : ∀ x ∈ Subgroup.zpowers abar, gbar * x * gbar⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [show gbar * abar ^ m * gbar⁻¹ = (MulAut.conj gbar) (abar ^ m) from rfl]
    rw [map_zpow, show (MulAut.conj gbar) abar = abar⁻¹ from by
      rw [MulAut.conj_apply]; exact hgbar]
    rw [inv_zpow]
  have hga_mem : g * aC * g⁻¹ ∈ A_sub := by
    have hmem : g * aC * g⁻¹ ∈ A_sub.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨aC, haC, rfl⟩
    rwa [hg_norm] at hmem
  have hπaC_zpow : π aC ∈ Subgroup.zpowers abar := by
    have hmem : π aC ∈ A_sub.map π := Subgroup.mem_map.mpr ⟨aC, haC, rfl⟩
    rwa [hA_map_eq] at hmem
  have hga_π : π (g * aC * g⁻¹) = π (aC⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, hπg]
    exact hconj_inv (π aC) hπaC_zpow
  have hga : g * aC * g⁻¹ = aC⁻¹ := by
    have hmem : (g * aC * g⁻¹) * aC ∈ A_sub ⊓ π.ker := by
      refine ⟨A_sub.mul_mem hga_mem haC, ?_⟩
      change π ((g * aC * g⁻¹) * aC) = 1
      rw [map_mul, hga_π, map_inv, inv_mul_cancel]
    rw [hdisj] at hmem
    have h1 : (g * aC * g⁻¹) * aC = 1 := Subgroup.mem_bot.mp hmem
    calc g * aC * g⁻¹ = (g * aC * g⁻¹) * aC * aC⁻¹ := by group
      _ = 1 * aC⁻¹ := by rw [h1]
      _ = aC⁻¹ := one_mul _
  refine ⟨C.subtype aC, C.subtype g, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨aC, haC_P, rfl⟩
  · intro h
    exact haC1 (C.subtype_injective h)
  · simpa using congrArg (Subgroup.subtype C) haC3
  · have h := congrArg (Subgroup.subtype C) hga
    simpa using h

theorem indexThreePackage_of_char_quotient {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ]
    [Finite Δ] {U C : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUC : U ≤ C)
    (π : ↥C →* Δ) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hα : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      C.map α.toMonoidHom = C ∧
        (π.ker.map C.subtype).map α.toMonoidHom = π.ker.map C.subtype)
    (hΔ : IndexThreePackage Δ) : IndexThreePackage Γ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', P', a', g', hU', hU'P, hP', hinv', ha', ha1', ha3', hg'⟩ := hΔ
  obtain ⟨hUπsyl, hUcard⟩ := pspr_indexNineSylow hU hUC π hπ hker
  obtain ⟨δ, -, hδ⟩ :=
    CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf (L := (⊤ : Subgroup Δ)) hU' hUπsyl
  have hδ' : (U.subgroupOf C).map π = U'.map (MulAut.conj δ).toMonoidHom := by
    simpa [Quasithin.conjSub] using hδ
  have hUπP : (U.subgroupOf C).map π ≤ P'.map (MulAut.conj δ).toMonoidHom := by
    rw [hδ']
    exact Subgroup.map_mono hU'P
  have hPcard : Nat.card (P'.map (MulAut.conj δ).toMonoidHom) =
      3 * Nat.card ((U.subgroupOf C).map π) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hP']
    congr 1
    rw [hδ', Subgroup.card_map_of_injective (MulAut.conj δ).injective]
  have hinvP : ∀ β : MulAut Δ,
      ((U.subgroupOf C).map π).map β.toMonoidHom = (U.subgroupOf C).map π →
        (P'.map (MulAut.conj δ).toMonoidHom).map β.toMonoidHom =
          P'.map (MulAut.conj δ).toMonoidHom := by
    intro β hβ
    have hβ' : (U'.map (MulAut.conj δ).toMonoidHom).map β.toMonoidHom =
        U'.map (MulAut.conj δ).toMonoidHom := by
      rwa [← hδ']
    exact pspr_invariance_conj hinv' β hβ'
  have haP : (MulAut.conj δ) a' ∈ P'.map (MulAut.conj δ).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a', ha', rfl⟩
  have ha1 : (MulAut.conj δ) a' ≠ 1 := fun h =>
    ha1' ((MulEquiv.map_eq_one_iff (MulAut.conj δ)).mp h)
  have ha3 : ((MulAut.conj δ) a') ^ 3 = 1 := by
    rw [← map_pow, ha3', map_one]
  have hg : (MulAut.conj δ) g' * (MulAut.conj δ) a' * ((MulAut.conj δ) g')⁻¹ =
      ((MulAut.conj δ) a')⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, hg', map_inv]
  obtain ⟨hUP, hPcard'⟩ := pspr_indexThreeP hUC π hπ hUπP hPcard hUcard
  have hPinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      (((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype).map α.toMonoidHom =
        ((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype :=
    pspr_indexNineInvariance hUC π hπ hα hinvP
  obtain ⟨a, g, haP', ha1'', ha3'', hg''⟩ :=
    pspr_indexThreeElements π hπ hker haP ha1 ha3 hg
  exact ⟨U, ((P'.map (MulAut.conj δ).toMonoidHom).comap π).map C.subtype, a, g,
    hU, hUP, hPcard', hPinv, haP', ha1'', ha3'', hg''⟩

theorem map_eq_of_center {Γ : Type*} [Group Γ] {U : Subgroup Γ} {z : Γ}
    (hZ : ∀ x : Γ, (x ∈ U ∧ ∀ y ∈ U, x * y = y * x) ↔ x = 1 ∨ x = z) (hz1 : z ≠ 1)
    (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) : α z = z := by
  have hzU := (hZ z).2 (Or.inr rfl)
  have hmem : ∀ y ∈ U, ∃ w ∈ U, α w = y := fun y hy => by
    rw [← hα] at hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨w, hw, rfl⟩
  have h : α z ∈ U ∧ ∀ y ∈ U, α z * y = y * α z := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [← hα]
      exact Subgroup.mem_map.mpr ⟨z, hzU.1, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := hmem y hy
      rw [← map_mul, ← map_mul, hzU.2 w hw]
  rcases (hZ _).1 h with h1 | h2
  · exact absurd ((MulEquiv.map_eq_one_iff α).mp h1) hz1
  · exact h2

theorem char_of_centralizer {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] [Finite Δ]
    {U : Subgroup Γ} {z : Γ} (hz : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → α z = z)
    (π : ↥(Subgroup.centralizer {z}) →* Δ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) (hO2 : ∀ N : Subgroup Δ, N.Normal → IsPGroup 2 ↥N → N = ⊥)
    (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Subgroup.centralizer {z}).map α.toMonoidHom = Subgroup.centralizer {z} ∧
      (π.ker.map (Subgroup.centralizer {z}).subtype).map α.toMonoidHom =
        π.ker.map (Subgroup.centralizer {z}).subtype := by
  classical
  have hαz : α z = z := hz α hα
  let C : Subgroup Γ := Subgroup.centralizer ({z} : Set Γ)
  have hCmap : C.map α.toMonoidHom = C := by
    dsimp only [C]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * z = z * y := by
        simpa [Subgroup.mem_centralizer_singleton_iff] using hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc α y * z = α y * α z := by rw [hαz]
        _ = α (y * z) := by rw [map_mul]
        _ = α (z * y) := by rw [hy']
        _ = α z * α y := by rw [map_mul]
        _ = z * α y := by rw [hαz]
    · intro hx
      refine Subgroup.mem_map.mpr ⟨α.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      have hz' : α.symm z = z := by
        have h := congrArg (⇑α.symm) hαz
        simpa using h.symm
      have hxc := congrArg (⇑α.symm) hx
      simpa [map_mul, hz'] using hxc
  refine ⟨?_, ?_⟩
  · change C.map α.toMonoidHom = C
    exact hCmap
  change (π.ker.map C.subtype).map α.toMonoidHom = π.ker.map C.subtype
  let K : Subgroup Γ := π.ker.map C.subtype
  have hKC : K ≤ C := Subgroup.map_subtype_le _
  have hKiff : ∀ k : Γ, k ∈ K ↔ ∃ hkC : k ∈ C, (⟨k, hkC⟩ : ↥C) ∈ π.ker := by
    intro k
    constructor
    · intro hk
      obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp hk
      refine ⟨hck ▸ c.2, ?_⟩
      rwa [show (⟨k, hck ▸ c.2⟩ : ↥C) = c from Subtype.ext hck.symm]
    · rintro ⟨hkC, hkker⟩
      exact Subgroup.mem_map.mpr ⟨⟨k, hkC⟩, hkker, rfl⟩
  have hCiff : ∀ x : Γ, x ∈ C ↔ α x ∈ C := by
    intro x
    constructor
    · intro hx
      rw [← hCmap]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      rw [← hCmap] at hx
      obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
      rw [show c = x from α.injective hcx] at hc
      exact hc
  have hCα' : ∀ x : Γ, x ∈ C → α.symm x ∈ C := fun x hx =>
    (hCiff (α.symm x)).mpr (by simpa using hx)
  have hαKle : K.map α.toMonoidHom ≤ K := by
    intro y hy
    obtain ⟨x, hxK, rfl⟩ := Subgroup.mem_map.mp hy
    have hxC : x ∈ C := hKC hxK
    have hyC : α x ∈ C := (hCiff x).mp hxC
    let N' : Subgroup ↥C := (K.map α.toMonoidHom).subgroupOf C
    have hN'norm : N'.Normal := by
      refine Subgroup.Normal.mk fun m hm g => ?_
      have hmK : (m : Γ) ∈ K.map α.toMonoidHom := hm
      obtain ⟨k, hkK, hkm⟩ := Subgroup.mem_map.mp hmK
      have hkC : k ∈ C := hKC hkK
      have hkker : (⟨k, hkC⟩ : ↥C) ∈ π.ker := (hKiff k).mp hkK |>.2
      have hg' : α.symm (g : Γ) ∈ C := hCα' (g : Γ) g.2
      have hconjker := (inferInstance : π.ker.Normal).conj_mem
        (⟨k, hkC⟩ : ↥C) hkker (⟨α.symm (g : Γ), hg'⟩ : ↥C)
      have hconjK : α.symm (g : Γ) * k * (α.symm (g : Γ))⁻¹ ∈ K :=
        Subgroup.mem_map.mpr
          ⟨⟨α.symm (g : Γ) * k * (α.symm (g : Γ))⁻¹,
            C.mul_mem (C.mul_mem hg' hkC) (C.inv_mem hg')⟩, hconjker, rfl⟩
      have hgoal : (g : Γ) * (m : Γ) * (g : Γ)⁻¹
          = α (α.symm (g : Γ) * k * (α.symm (g : Γ))⁻¹) := by
        rw [← hkm]
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
        rfl
      show ((g * m * g⁻¹ : ↥C) : Γ) ∈ K.map α.toMonoidHom
      rw [show ((g * m * g⁻¹ : ↥C) : Γ) = (g : Γ) * (m : Γ) * (g : Γ)⁻¹ from rfl,
        hgoal]
      exact Subgroup.mem_map.mpr ⟨_, hconjK, rfl⟩
    have hN'2 : IsPGroup 2 ↥N' := by
      have h1 : IsPGroup 2 ↥(K.map α.toMonoidHom) :=
        (IsPGroup.map hker C.subtype).map α.toMonoidHom
      exact h1.comap_subtype
    have himgn : (N'.map π).Normal := Subgroup.Normal.map hN'norm π hπ
    have himg2 : IsPGroup 2 ↥(N'.map π) := hN'2.map π
    have hbot := hO2 (N'.map π) himgn himg2
    have hN'ker : N' ≤ π.ker := by
      intro c hc
      have hc' : π c ∈ N'.map π := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
      rw [hbot] at hc'
      simpa using hc'
    have hmN' : (⟨α x, hyC⟩ : ↥C) ∈ N' := by
      show ((⟨α x, hyC⟩ : ↥C) : Γ) ∈ K.map α.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨α x, hyC⟩, hN'ker hmN', rfl⟩
  have hcard : Nat.card (K.map α.toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective α.injective
  have hαKeq : K.map α.toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hαKle (le_of_eq hcard.symm)
  exact hαKeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
