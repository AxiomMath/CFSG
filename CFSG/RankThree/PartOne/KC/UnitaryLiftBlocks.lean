module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAction
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeTorus

public section

namespace CFSG.RankThree.PartOne.KCUnitaryLift

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryRegular CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

section Abstract

variable {Γ U : Type*} [Group Γ] [Group U]

theorem commute_core_image [Finite Γ] {p : ℕ} (hp : p.Prime) (ρ : U →* Γ)
    (hker : ∀ z ∈ ρ.ker, ∀ g : U, Commute z g) (B : Subgroup Γ) (t : Γ) (Hs M F : Subgroup U)
    (hHn : (Hs.map ρ).Normal) (hHB : Hs.map ρ ≤ B)
    (hMt : ∀ m ∈ M, ρ m * t = t * ρ m)
    (hMn : ∀ g : Γ, g * t = t * g → ∀ m ∈ M, ∃ m' ∈ M, g * ρ m * g⁻¹ = ρ m')
    (hFM : F ≤ M) (hFH : F ≤ Hs) (hFn : ∀ m ∈ M, ∀ g ∈ F, m * g * m⁻¹ ∈ F)
    (hFq : CFSG.IsQuasisimple F) {s : Γ}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set Γ))) {y : U} (hy : y ∈ F) : Commute (ρ y) s := by
  set CB := B ⊓ Subgroup.centralizer ({t} : Set Γ) with hCB
  set J := F.map ρ with hJ
  have hJB : J ≤ B := (Subgroup.map_mono hFH).trans hHB
  have hJcen : J ≤ Subgroup.centralizer ({t} : Set Γ) := by
    rintro _ ⟨y', hy', rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hMt y' (hFM hy'))
  have hJCB : J ≤ CB := le_inf hJB hJcen
  have hQ : CFSG.IsQuasisimple J := by
    let fF : F →* Γ := ρ.comp F.subtype
    have hkerF : fF.ker ≤ Subgroup.center F := by
      intro g hg
      rw [Subgroup.mem_center_iff]
      intro g'
      apply Subtype.ext
      exact (hker (g : U) hg (g' : U)).eq.symm
    have hrange : fF.range = J := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, g.2, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, rfl⟩
    have := isQuasisimple_range hFq fF hkerF
    rw [hrange] at this
    exact this
  set N₀ := M.map ρ ⊓ Hs.map ρ with hN₀
  have hJN₀ : J ≤ N₀ := le_inf (Subgroup.map_mono hFM) (Subgroup.map_mono hFH)
  have hN₀CB : N₀ ≤ CB := by
    refine le_inf (inf_le_right.trans hHB) ?_
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hx.1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hMt m hm)
  have hJnorm : (J.subgroupOf N₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnJ : ((n : N₀) : Γ) ∈ J := hn
    obtain ⟨m, hm, hmg⟩ := ((g : N₀).2).1
    obtain ⟨y', hy', hy'n⟩ := hnJ
    show ((g : N₀) : Γ) * ((n : N₀) : Γ) * ((g : N₀) : Γ)⁻¹ ∈ J
    rw [← hmg, ← hy'n]
    exact ⟨m * y' * m⁻¹, hFn m hm y' hy', by simp⟩
  have hN₀norm : (N₀.subgroupOf CB).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : CB) : Γ) ∈ N₀ := hn
    have hgt : ((g : CB) : Γ) * t = t * ((g : CB) : Γ) :=
      Subgroup.mem_centralizer_singleton_iff.mp g.2.2
    obtain ⟨m, hm, hmn⟩ := hn'.1
    obtain ⟨m', hm', hm'eq⟩ := hMn _ hgt m hm
    show ((g : CB) : Γ) * ((n : CB) : Γ) * ((g : CB) : Γ)⁻¹ ∈ N₀
    refine ⟨⟨m', hm', ?_⟩, hHn.conj_mem _ hn'.2 _⟩
    rw [← hmn]
    exact hm'eq.symm
  have hcomp : CFSG.IsComponent (J.subgroupOf CB) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJCB).symm hQ,
      isSubnormal_subgroupOf_of_normal_chain hJN₀ hJnorm hN₀norm⟩
  exact commute_of_isComponent_core hp hJCB hcomp ⟨y, hy, rfl⟩ hs

end Abstract

section Concrete

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem centralizer_eq_comap (u : primeFormUnitary h (idGram K n)) :
    Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n))) =
      (unitaryCentralizer (idForm h n) (toLinU h n u)).comap (toLinU h n) := by
  ext A
  rw [Subgroup.mem_comap, mem_unitaryCentralizer]
  refine ⟨fun hA => ⟨toLinU_mem A, ?_⟩, fun hA => ?_⟩
  · have hA' := Subgroup.mem_centralizer_singleton_iff.mp hA
    have := congrArg (toLinU h n) hA'
    rw [map_mul, map_mul] at this
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) this
    exact h2
  · have h1 : toLinU h n (A * u) = toLinU h n (u * A) := by
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hA.2.eq
    exact Subgroup.mem_centralizer_singleton_iff.mpr (toLinU_injective h1)

theorem specialBlock_le_range_toLinU (u : primeFormUnitary h (idGram K n)) (a : K[X]) :
    specialBlock (idForm h n) (toLinU h n u) a ≤ (toLinU h n).range := by
  rw [range_toLinU]
  exact specialBlock_le_unitaryCentralizer.trans (fun g hg => hg.1)

theorem map_toLinU_centralizer (u : primeFormUnitary h (idGram K n)) :
    (Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n)))).map (toLinU h n) =
      unitaryCentralizer (idForm h n) (toLinU h n u) := by
  rw [centralizer_eq_comap, Subgroup.map_comap_eq]
  refine inf_of_le_right ?_
  rw [range_toLinU]
  exact fun g hg => hg.1

theorem commute_of_mem_ker (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) {z : primeFormUnitary h (idGram K n)}
    (hz : primeFormConjHom h (idGram K n) z = 1) (g : primeFormUnitary h (idGram K n)) :
    Commute z g := by
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq z).mp hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (commute_scalar c (g : GL (Fin n) K)).symm.eq

theorem conj_mem_map_centralizer (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)
    (u : primeFormUnitary h (idGram K n)) {g : MulAut (primeFormP h (idGram K n))}
    (hg : g * primeFormConjHom h (idGram K n) u = primeFormConjHom h (idGram K n) u * g)
    {m : primeFormUnitary h (idGram K n)}
    (hm : m ∈ Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n)))) :
    ∃ m' ∈ Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n))),
      g * primeFormConjHom h (idGram K n) m * g⁻¹ = primeFormConjHom h (idGram K n) m' := by
  refine ⟨idActU h n hn hq g m, ?_, conj_primeFormConjHom hn hq g m⟩
  set c := idActU h n hn hq g with hc
  have hρ : primeFormConjHom h (idGram K n) (c u) = primeFormConjHom h (idGram K n) u := by
    rw [← conj_primeFormConjHom hn hq g u, hg, mul_inv_cancel_right]
  have hz : primeFormConjHom h (idGram K n) (u⁻¹ * c u) = 1 := by
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have hcen : ∀ g' : primeFormUnitary h (idGram K n), Commute (u⁻¹ * c u) g' :=
    fun g' => commute_of_mem_ker hn hq hz g'
  have h1 : c m * c u = c u * c m := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hm]
  have hw : c u = u * (u⁻¹ * c u) := by group
  set z := u⁻¹ * c u with hzdef
  rw [hw] at h1
  have h2 : (c m * u) * z = (u * c m) * z := by
    calc (c m * u) * z = c m * (u * z) := by group
      _ = u * z * c m := h1
      _ = u * (z * c m) := by group
      _ = u * (c m * z) := by rw [(hcen (c m)).eq]
      _ = (u * c m) * z := by group
  exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_right_cancel h2)

theorem isQuasisimple_comap_specialBlock (hq : 4 ≤ ℓ ^ f)
    {u : primeFormUnitary h (idGram K n)}
    (H : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n u))
    (a : primaryFactors ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : 2 ≤ primaryMultiplicity ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X])) :
    CFSG.IsQuasisimple ((specialBlock (idForm h n) (toLinU h n u) (a : K[X])).comap
      (toLinU h n)) := by
  have hQ := (specialBlockFacts H hq a).quasisimple ha
  have hinj := (toLinU_injective (h := h) (n := n))
  let e := ((specialBlock (idForm h n) (toLinU h n u) (a : K[X])).comap
    (toLinU h n)).equivMapOfInjective (toLinU h n) hinj
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (e.trans (MulEquiv.subgroupCongr ?_)).symm hQ
  rw [Subgroup.map_comap_eq]
  exact inf_of_le_right (specialBlock_le_range_toLinU u _)

theorem commute_core_specialBlock (hn : 3 ≤ n) (hq : 4 ≤ ℓ ^ f)
    {u : primeFormUnitary h (idGram K n)}
    (H : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n u))
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B) {p : ℕ} (hp : p.Prime)
    {s : MulAut (primeFormP h (idGram K n))}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K n) u} :
        Set (MulAut (primeFormP h (idGram K n))))))
    (a : primaryFactors ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : 2 ≤ primaryMultiplicity ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]))
    {y : primeFormUnitary h (idGram K n)}
    (hy : toLinU h n y ∈ specialBlock (idForm h n) (toLinU h n u) (a : K[X])) :
    Commute (primeFormConjHom h (idGram K n) y) s := by
  have hq3 : 3 < ℓ ^ f := by omega
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  refine commute_core_image hp (primeFormConjHom h (idGram K n))
    (fun z hz g' => commute_of_mem_ker hn hq3 (MonoidHom.mem_ker.mp hz) g') B
    (primeFormConjHom h (idGram K n) u)
    ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)))
    (Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n))))
    ((specialBlock (idForm h n) (toLinU h n u) (a : K[X])).comap (toLinU h n)) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ hs hy
  · rw [map_gramSU_eq_range_conj]
    exact CFSG.ComponentClassification.OuterAutomorphisms.innerNormal _
  · rw [map_gramSU_eq_range_conj]
    exact hB
  · intro m hm
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hm]
  · intro g hg m hm
    exact conj_mem_map_centralizer hn hq3 u hg hm
  · intro A hA
    rw [centralizer_eq_comap]
    exact specialBlock_le_unitaryCentralizer hA
  · intro A hA
    have h1 := specialBlock_le_sesqSpecialUnitaryGroup H hq a hA
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (A : GL (Fin n) K)).mp h1
  · intro m hm g hg
    rw [centralizer_eq_comap] at hm
    show toLinU h n (m * g * m⁻¹) ∈ specialBlock (idForm h n) (toLinU h n u) (a : K[X])
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_specialBlock hm hg
  · exact isQuasisimple_comap_specialBlock hq H a ha

theorem commute_core_commutator_centralizer (hn : 3 ≤ n) (hq : 4 ≤ ℓ ^ f)
    {u : primeFormUnitary h (idGram K n)}
    (H : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n u))
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B) {p : ℕ} (hp : p.Prime)
    {s : MulAut (primeFormP h (idGram K n))}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K n) u} :
        Set (MulAut (primeFormP h (idGram K n))))))
    {y : primeFormUnitary h (idGram K n)}
    (hy : y ∈ ⁅Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n))),
      Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n)))⁆) :
    Commute (primeFormConjHom h (idGram K n) y) s := by
  have hinj := toLinU_injective (h := h) (n := n)
  let G' : Subgroup (primeFormUnitary h (idGram K n)) :=
    (Subgroup.centralizer ({s} : Set (MulAut (primeFormP h (idGram K n))))).comap
      (primeFormConjHom h (idGram K n))
  have hle : ⁅Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n))),
      Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K n)))⁆ ≤ G' := by
    rw [← Subgroup.map_le_map_iff_of_injective hinj, Subgroup.map_commutator,
      map_toLinU_centralizer, commutator_unitaryCentralizer_eq_iSup_specialBlock H hq]
    refine iSup_le fun ⟨a, ha⟩ g hg => ?_
    obtain ⟨y', rfl⟩ := specialBlock_le_range_toLinU u _ hg
    refine ⟨y', ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_core_specialBlock hn hq H B hB hp hs a ha hg).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

end Concrete

end CFSG.RankThree.PartOne.KCUnitaryLift
