module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.LocalRank

@[expose] def NormalPrimeComplementsTrivial (p : ℕ) {T : Type*} [Group T] (a : MulAut T) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ S : Subgroup (MulAut T), S ≤ B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) →
      (S.subgroupOf (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)))).Normal →
        ¬ p ∣ Nat.card S → S = ⊥

namespace KCUnitaryDefining

theorem mulAutCongr_conj {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') (x : T) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

end KCUnitaryDefining

theorem NormalPrimeComplementsTrivial.map_mulEquiv {p : ℕ} {T T' : Type*} [Group T] [Group T']
    (e : T ≃* T') {a : MulAut T} (ha : NormalPrimeComplementsTrivial p a) :
    NormalPrimeComplementsTrivial p (MulAut.congr e a) := by
  intro B' hB' S' hS'C hS'n hS'p
  set φ : MulAut T ≃* MulAut T' := MulAut.congr e with hφ
  set B : Subgroup (MulAut T) := B'.map φ.symm.toMonoidHom with hB
  set S : Subgroup (MulAut T) := S'.map φ.symm.toMonoidHom with hS
  have hmemB : ∀ s : MulAut T, s ∈ B ↔ φ s ∈ B' := fun s => Subgroup.mem_map_equiv
  have hmemS : ∀ s : MulAut T, s ∈ S ↔ φ s ∈ S' := fun s => Subgroup.mem_map_equiv
  have hBinn : (MulAut.conj : T →* MulAut T).range ≤ B := by
    rintro _ ⟨x, rfl⟩
    refine (hmemB _).mpr (hB' ⟨e x, ?_⟩)
    exact (KCUnitaryDefining.mulAutCongr_conj e x).symm
  have hmemC : ∀ s : MulAut T, s ∈ B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) ↔
      φ s ∈ B' ⊓ Subgroup.centralizer ({φ a} : Set (MulAut T')) := by
    intro s
    simp only [Subgroup.mem_inf, hmemB, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := congrArg φ h2
      simpa using this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, φ.injective ?_⟩
      simpa using h2
  have hSC : S ≤ B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) := by
    intro s hs
    exact (hmemC s).mpr (hS'C ((hmemS s).mp hs))
  have hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSC]
    intro s y hs hy
    have h1 := (Subgroup.normal_subgroupOf_iff hS'C).mp hS'n (φ s) (φ y) ((hmemS s).mp hs)
      ((hmemC y).mp hy)
    rw [hmemS]
    simpa using h1
  have hSp : ¬ p ∣ Nat.card S := by
    have : Nat.card S = Nat.card S' := Subgroup.card_map_of_injective φ.symm.injective
    rwa [this]
  have hbot := ha B hBinn S hSC hSn hSp
  have : S' = S.map φ.toMonoidHom := by
    rw [hS, Subgroup.map_map]
    ext x
    simp
  rw [this, hbot, Subgroup.map_bot]

theorem theta_centralizer_eq_bot_of_normalPrimeComplementsTrivial {p : ℕ} (hp : p.Prime)
    {T : Type*} [Group T] [Finite T] {a : MulAut T} (ha : NormalPrimeComplementsTrivial p a)
    (B : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T))) = ⊥ := by
  set H : Subgroup (MulAut T) := B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) with hH
  have hθ := solvable_prime_complement_core_characterization (H := H) hp
  have hnorm : (aschbacherSolvableCore p H).Normal := inferInstance
  set S : Subgroup (MulAut T) := inSubgroup (aschbacherSolvableCore p) H with hS
  have hSH : S ≤ H := Subgroup.map_subtype_le _
  have hsub : S.subgroupOf H = aschbacherSolvableCore p H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hSn : (S.subgroupOf H).Normal := by
    rw [hsub]
    exact hnorm
  have hSp : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
    exact hθ.2.2.1
  exact ha B hB S hSH hSn hSp

end CFSG.RankThree.PartOne
