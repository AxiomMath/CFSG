module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOdd

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement

section Setting

variable {Γ U ι : Type*} [Group Γ] [Group U]

structure GoodSetting (ρ : U →* Γ) (B : Subgroup Γ) (t : Γ) (Hs M : Subgroup U)
    (F : ι → Subgroup U) : Prop where
  ker_central : ∀ u ∈ ρ.ker, ∀ g : U, Commute u g
  H_normal : (Hs.map ρ).Normal
  H_le_B : Hs.map ρ ≤ B
  C_eq : Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ) = (M ⊓ Hs).map ρ
  F_le_M : ∀ i, F i ≤ M
  F_le_Hs : ∀ i, F i ≤ Hs
  F_normal : ∀ i, ∀ m ∈ M ⊓ Hs, ∀ g ∈ F i, m * g * m⁻¹ ∈ F i
  F_quasi : ∀ i, CFSG.IsQuasisimple (F i)

variable {ρ : U →* Γ} {B : Subgroup Γ} {t : Γ} {Hs M : Subgroup U} {F : ι → Subgroup U}
  (S : GoodSetting ρ B t Hs M F)

namespace GoodSetting

include S in
theorem map_le_C (i : ι) :
    (F i).map ρ ≤ Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ) := by
  rw [S.C_eq]
  exact Subgroup.map_mono (le_inf (S.F_le_M i) (S.F_le_Hs i))

include S in
theorem map_le_H (i : ι) : (F i).map ρ ≤ Hs.map ρ := Subgroup.map_mono (S.F_le_Hs i)

include S in
theorem map_le_centralizerB (i : ι) :
    (F i).map ρ ≤ B ⊓ Subgroup.centralizer ({t} : Set Γ) :=
  le_inf ((S.map_le_H i).trans S.H_le_B) ((S.map_le_C i).trans inf_le_right)

include S in
theorem isQuasisimple_image (i : ι) : CFSG.IsQuasisimple ((F i).map ρ) := by
  have hQ := S.F_quasi i
  let f : F i →* Γ := ρ.comp (F i).subtype
  have hker : f.ker ≤ Subgroup.center (F i) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    apply Subtype.ext
    exact (S.ker_central (g : U) hg (g' : U)).eq.symm
  have := isQuasisimple_range hQ f hker
  have hrange : f.range = (F i).map ρ := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hrange] at this
  exact this

include S in
theorem conj_mem_image (i : ι) {y : Γ} (hy : y ∈ Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))
    {j : Γ} (hj : j ∈ (F i).map ρ) : y * j * y⁻¹ ∈ (F i).map ρ := by
  rw [S.C_eq] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  obtain ⟨g, hg, rfl⟩ := hj
  exact ⟨m * g * m⁻¹, S.F_normal i m hm g hg, by simp⟩

include S in
theorem image_normal_C (i : ι) :
    (((F i).map ρ).subgroupOf (Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnJ : ((n : ↥(Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) ∈ (F i).map ρ := hn
  exact S.conj_mem_image i g.2 hnJ

include S in
theorem C_normal_CB :
    ((Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ)).subgroupOf
      (B ⊓ Subgroup.centralizer ({t} : Set Γ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : ((n : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) ∈
      Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ) := hn
  have hgt : ((g : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) ∈
      Subgroup.centralizer ({t} : Set Γ) := g.2.2
  have hmem : ((g : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) *
      ((n : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) *
      ((g : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ)⁻¹ ∈
      Subgroup.centralizer ({t} : Set Γ) := mul_mem (mul_mem hgt hn'.2) (inv_mem hgt)
  show ((g : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) *
      ((n : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) *
      ((g : ↥(B ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ)⁻¹ ∈
      Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ)
  exact ⟨S.H_normal.conj_mem _ hn'.1 _, hmem⟩

include S in
theorem isComponent_image (i : ι) :
    CFSG.IsComponent (((F i).map ρ).subgroupOf (B ⊓ Subgroup.centralizer ({t} : Set Γ))) := by
  have hJCB : (F i).map ρ ≤ B ⊓ Subgroup.centralizer ({t} : Set Γ) := S.map_le_centralizerB i
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJCB).symm
    (S.isQuasisimple_image i), ?_⟩
  exact isSubnormal_subgroupOf_of_normal_chain (S.map_le_C i) (S.image_normal_C i) S.C_normal_CB

include S in
theorem conj_mem_iSup_image {y : Γ} (hy : y ∈ Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))
    {j : Γ} (hj : j ∈ ⨆ i, (F i).map ρ) : y * j * y⁻¹ ∈ ⨆ i, (F i).map ρ := by
  refine Subgroup.iSup_induction (fun i => (F i).map ρ) (C := fun j => y * j * y⁻¹ ∈
    ⨆ i, (F i).map ρ) hj ?_ ?_ ?_
  · intro i j hj
    exact Subgroup.mem_iSup_of_mem i (S.conj_mem_image i hy hj)
  · simp
  · intro u v hu hv
    have : y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
    rw [this]
    exact mul_mem hu hv

include S in
theorem iSup_image_normal :
    ((⨆ i, (F i).map ρ).subgroupOf (Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnJ : ((n : ↥(Hs.map ρ ⊓ Subgroup.centralizer ({t} : Set Γ))) : Γ) ∈
      ⨆ i, (F i).map ρ := hn
  exact S.conj_mem_iSup_image g.2 hnJ

include S in
theorem core_centralizes [Finite Γ] {p : ℕ} (hp : p.Prime) {s : Γ}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set Γ))) {j : Γ} (hj : j ∈ ⨆ i, (F i).map ρ) :
    Commute j s := by
  refine Subgroup.iSup_induction (fun i => (F i).map ρ) (C := fun j => Commute j s) hj ?_ ?_ ?_
  · intro i j hj
    exact commute_of_isComponent_core hp (S.map_le_centralizerB i) (S.isComponent_image i) hj hs
  · exact Commute.one_left s
  · intro a b ha hb
    exact ha.mul_left hb

include S in
theorem mem_centralizer_iff {Y : U} :
    ρ Y ∈ Subgroup.centralizer ((⨆ i, (F i).map ρ : Subgroup Γ) : Set Γ) ↔
      ∀ i, ∀ g ∈ F i, Commute Y g := by
  constructor
  · intro h i g hg
    have hρ : ρ g * ρ Y = ρ Y * ρ g :=
      Subgroup.mem_centralizer_iff.mp h _ (Subgroup.mem_iSup_of_mem i ⟨g, hg, rfl⟩)
    have hker : ∀ g' ∈ F i, ⁅Y, g'⁆ ∈ ρ.ker := by
      intro g' hg'
      have hρ' : ρ g' * ρ Y = ρ Y * ρ g' :=
        Subgroup.mem_centralizer_iff.mp h _ (Subgroup.mem_iSup_of_mem i ⟨g', hg', rfl⟩)
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hρ'.symm
    have h1 := commutator_eq_one_of_central (F := F i) (Z := ρ.ker) Y (S.F_quasi i).1
      S.ker_central hker g hg
    exact commutatorElement_eq_one_iff_commute.mp h1
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    refine Subgroup.iSup_induction (fun i => (F i).map ρ) (C := fun j => j * ρ Y = ρ Y * j) hj
      ?_ ?_ ?_
    · rintro i _ ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul, (h i g hg).symm.eq]
    · simp
    · intro a b ha hb
      rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

end GoodSetting

end Setting

section Plane

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem commutator_core_plane {p : ℕ} (hp : p.Prime) (B H J A : Subgroup Γ) (hHn : H.Normal)
    (hHB : H ≤ B) (hAH : A ≤ H) {a : Γ} (haA : a ∈ A)
    (hAcomm : ∀ b ∈ A, ∀ b' ∈ A, b * b' = b' * b) (hApow : ∀ b ∈ A, b ^ p = 1)
    (hSJ : ∀ s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set Γ)), ∀ j ∈ J, Commute s j)
    (hAJ : ∀ y ∈ H ⊓ Subgroup.centralizer ({a} : Set Γ), (∀ j ∈ J, Commute y j) →
      ∀ b ∈ A, Commute b y) :
    ⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set Γ)), A⁆ = ⊥ := by
  set CB := B ⊓ Subgroup.centralizer ({a} : Set Γ) with hCB
  set S := CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p) CB with hS
  have hcore := CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := CB) hp
  have hSord : ¬p ∣ Nat.card S := by
    have h1 : Nat.card S = Nat.card (CFSG.RankThree.LocalRank.aschbacherSolvableCore p CB) :=
      Subgroup.card_map_of_injective (Subtype.val_injective (p := (· ∈ CB)))
    rw [h1]
    exact hcore.2.2.1
  refine (Subgroup.commutator_le.mpr fun s hs b hb => ?_).antisymm bot_le
  have hbH : b ∈ H := hAH hb
  have hbCB : b ∈ CB :=
    ⟨hHB hbH, Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm b hb a haA)⟩
  have hsCB : s ∈ CB := inSubgroup_core_le p CB hs
  have hs' : b * s * b⁻¹ ∈ S := conj_mem_inSubgroup_core p CB hbCB hs
  have hs'CB : b * s * b⁻¹ ∈ CB := inSubgroup_core_le p CB hs'
  set c := s⁻¹ * (b * s * b⁻¹) with hc
  have hcS : c ∈ S := mul_mem (inv_mem hs) hs'
  have hcH : c ∈ H := by
    have h1 : s⁻¹ * b * s⁻¹⁻¹ ∈ H := hHn.conj_mem b hbH s⁻¹
    have h2 : c = (s⁻¹ * b * s⁻¹⁻¹) * b⁻¹ := by rw [hc]; group
    rw [h2]
    exact mul_mem h1 (inv_mem hbH)
  have hcC : c ∈ Subgroup.centralizer ({a} : Set Γ) :=
    mul_mem (inv_mem hsCB.2) hs'CB.2
  have hcJ : ∀ j ∈ J, Commute c j := fun j hj =>
    (hSJ _ (inv_mem hs) j hj).mul_left (hSJ _ hs' j hj)
  have hbc : Commute b c := hAJ c ⟨hcH, hcC⟩ hcJ b hb
  have hs'eq : b * s * b⁻¹ = s * c := by rw [hc]; group
  have hpow : ∀ k : ℕ, b ^ k * s * (b ^ k)⁻¹ = s * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b ^ (k + 1) * s * (b ^ (k + 1))⁻¹ = b * (b ^ k * s * (b ^ k)⁻¹) * b⁻¹ := by group
        _ = b * (s * c ^ k) * b⁻¹ := by rw [ih]
        _ = (b * s * b⁻¹) * (b * c ^ k * b⁻¹) := by group
        _ = (s * c) * c ^ k := by
          rw [hs'eq, (hbc.pow_right k).eq, mul_inv_cancel_right]
        _ = s * c ^ (k + 1) := by group
  have hcp : c ^ p = 1 := by
    have h1 := hpow p
    rw [hApow b hb, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_left.mp h1.symm)
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ Nat.card S := by
      have := orderOf_dvd_natCard (⟨c, hcS⟩ : S)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) hSord
  have hbs : b * s * b⁻¹ = s := by rw [hs'eq, hc1, mul_one]
  have hbs' : b * s = s * b := by
    calc b * s = (b * s * b⁻¹) * b := by group
      _ = s * b := by rw [hbs]
  rw [Subgroup.mem_bot, commutatorElement_def, ← hbs']
  group

end Plane

end CFSG.RankThree.PartOne.KCUnitary
