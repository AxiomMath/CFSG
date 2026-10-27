module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem mul_comm_of_isMulCommutative {M : Type} [Group M] {H : Subgroup M}
    (hH : IsMulCommutative ↥H) {a b : M} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a :=
  congrArg Subtype.val (hH.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isMulCommutative_of_comm' {M : Type} [Group M] {H : Subgroup M}
    (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : IsMulCommutative ↥H :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

namespace Setup521

variable (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem U_le_T (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)) ≤ T :=
  ((s.almostSpecialHyp_G₁ h5114 hF).G22_three).1

theorem tildeOf_U_le (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) ≤
      omegaOneCenterOf (tildeOf Z₁ (pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)))) :=
  ((s.almostSpecialHyp_G₁ h5114 hF).G22_one).2

theorem V₂_le_G₁ : conjClosure Z₁ D₃ ≤ Subgroup.centralizer (Z₁ : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  haveI := (s.isElemAbelian_V₂).1
  exact mul_comm_of_isMulCommutative this (le_conjClosure Z₁ D₃ (show z ∈ Z₁ from hz)) hy

theorem U_le_G₁ : conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)) ≤
    Subgroup.centralizer (Z₁ : Set G) :=
  conjClosure_le fun g hg y hy => (Subgroup.centralizer (Z₁ : Set G)).mul_mem
    ((Subgroup.centralizer (Z₁ : Set G)).mul_mem hg (s.V₂_le_G₁ hy))
    ((Subgroup.centralizer (Z₁ : Set G)).inv_mem hg)

theorem U_le_normalizer_Z₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)) ≤
      Subgroup.normalizer (Z₁ : Set G) :=
  (s.U_le_G₁).trans (Subgroup.centralizer_le_normalizer _)

theorem isElemAbelian_tildeOf_U (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))) := by
  have hle := s.tildeOf_U_le h5114 hF
  refine ⟨isMulCommutative_of_comm' fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact (mem_centralizer_of_mem_omegaOneCenterOf (hle hx)
      (omegaOneCenterOf_le _ (hle hy))).symm
  · exact sq_eq_one_of_mem_omegaOneCenterOf (hle hx)

theorem inv_mul_mem_Z₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) {x y : G}
    (hx : x ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))
    (hy : y ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
    (x * y)⁻¹ * (y * x) ∈ Z₁ := by
  set U := conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)) with hUdef
  have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := s.U_le_normalizer_Z₁ h5114 hF hx
  have hyN : y ∈ Subgroup.normalizer (Z₁ : Set G) := s.U_le_normalizer_Z₁ h5114 hF hy
  have hc := mul_comm_of_isMulCommutative (s.isElemAbelian_tildeOf_U h5114 hF).1
    (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (X := U)
      (x := ⟨x, hxN⟩) hx)
    (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (X := U)
      (x := ⟨y, hyN⟩) hy)
  have key : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (⟨x, hxN⟩ * ⟨y, hyN⟩) =
      secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (⟨y, hyN⟩ * ⟨x, hxN⟩) := by
    rw [map_mul, map_mul]
    exact hc
  rw [secMk_eq_secMk_iff] at key
  exact key

theorem comm_mem_Z₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) {a b : G}
    (ha : a ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))
    (hb : b ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
    a⁻¹ * b⁻¹ * a * b ∈ Z₁ := by
  have h := s.inv_mul_mem_Z₁ h5114 hF ha hb
  have : a⁻¹ * b⁻¹ * a * b = ((a * b)⁻¹ * (b * a))⁻¹ := by group
  rw [this]
  exact Z₁.inv_mem h

theorem commutator_V₂_U_le (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))⁆ ≤ Z₁ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have hU := s.comm_mem_Z₁ h5114 hF
    ((conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))).inv_mem
      (le_conjClosure _ _ ha)) ((conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))).inv_mem hb)
  have e : a⁻¹⁻¹ * b⁻¹⁻¹ * a⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e] at hU
  exact hU

theorem isMulCommutative_U_of_commutator_eq_bot (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (hb : ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))⁆ = ⊥) :
    IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) := by
  set U := conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)) with hUdef
  have hV : conjClosure Z₁ D₃ ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := by
    refine conjClosure_le fun g hg y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hgu : g⁻¹ * u * g ∈ U := by
      have hN : g⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        le_normalizer_conjClosure _ _ ((Subgroup.centralizer (Z₁ : Set G)).inv_mem hg)
      have h1 := (Subgroup.mem_normalizer_iff.mp hN u).mp hu
      rwa [inv_inv] at h1
    have h2 := Subgroup.mem_centralizer_iff.mp (hV hy) (g⁻¹ * u * g) hgu
    calc u * (g * y * g⁻¹) = g * (g⁻¹ * u * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * u := by group
  exact isMulCommutative_of_comm' fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hUC hx) y hy |>.symm

theorem commutator_V₂_U_eq (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))) :
    ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))⁆ = Z₁ := by
  have hle := s.commutator_V₂_U_le h5114 hF
  have hne : ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))⁆ ≠ ⊥ := fun hb =>
    hU (s.isMulCommutative_U_of_commutator_eq_bot h5114 hF hb)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzZ : z ∈ Z₁ := hle hz
  have hZ : Subgroup.zpowers z = Z₁ :=
    zpowers_eq_of_card_prime Nat.prime_two s.card_Z₁ hzZ hz1'
  apply le_antisymm hle
  have hzp : Subgroup.zpowers z ≤ ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))⁆ := Subgroup.zpowers_le.mpr hz
  rwa [hZ] at hzp

theorem sq_mem_Z₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) {x : G}
    (hx : x ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
    x ^ 2 ∈ Z₁ := by
  have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := s.U_le_normalizer_Z₁ h5114 hF hx
  have h := (s.isElemAbelian_tildeOf_U h5114 hF).2 _ (secMk_mem_secImg
    (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (X := conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))) (x := ⟨x, hxN⟩) hx)
  rw [← map_pow, secMk_eq_one_iff] at h
  simpa using h

end Setup521

end CFSG.Quasithin.H13
