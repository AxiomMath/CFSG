module

public import CFSG.Quasithin.MS93.S46I469
public import CFSG.Quasithin.MS93.S46X3Lin
public import CFSG.Quasithin.MS93.S46SL2Sec
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Quasithin.MS93.S46T
public import CFSG.Quasithin.Background.G13Core
public import CFSG.Quasithin.Background.G1Module
public import CFSG.Quasithin.MS93.S46I466a
public import CFSG.Quasithin.MS93.S46Last
public import CFSG.Quasithin.MS93.S4A431G
public import CFSG.Quasithin.MS93.S4A433
public import CFSG.Quasithin.MS93.S4ABridge
public import CFSG.Quasithin.MS93.S4AL1

public section

namespace CFSG.Quasithin.MS93.S468

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.I466b
open scoped commutatorElement Matrix MatrixGroups

section Block

variable {F : Type} [Field F]

@[expose] def stabX0 : Subgroup (SL3 F) where
  carrier := {A | ∀ v : Fin 3 → F, ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0}
  mul_mem' := by
    intro A B hA hB v
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hA, hB]
  one_mem' := by
    intro v
    simp
  inv_mem' := by
    intro A hA v
    have := hA (((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this
    exact this.symm

theorem row_zero_of_mem_stabX0 {A : SL3 F} (hA : A ∈ stabX0) (j : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 j = if j = 0 then 1 else 0 := by
  have := hA (Pi.single j 1)
  rw [show ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1) 0 = (A : Matrix (Fin 3) (Fin 3) F) 0 j
    from by simp [Matrix.mulVec, dotProduct, Pi.single_apply]] at this
  rw [this]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj, Ne.symm hj]

theorem rootGroup_sup_le_stabX0 :
    (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ≤ stabX0 :=
  fun _ hB v => X3.rootElt_mulVec_apply_zero_of_mem hB v

@[expose] noncomputable def blockHom : ↥(stabX0 : Subgroup (SL3 F)) →* SL(2, F) where
  toFun A := ⟨(A : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ, by
    have h0 := row_zero_of_mem_stabX0 A.2
    have hd := (A : SL3 F).2
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ] at hd
    simp only [h0, Fin.succ_ne_zero, ite_true, ite_false, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, pow_zero, one_mul, Fin.val_zero] at hd
    rw [show (Fin.succAbove (0 : Fin 3)) = Fin.succ from rfl] at hd
    exact hd⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [Matrix.one_apply, Fin.succ_inj]
  map_mul' A B := by
    apply Subtype.ext
    ext i j
    have hB := row_zero_of_mem_stabX0 B.2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, hB, Fin.succ_ne_zero, ite_false, mul_zero, zero_add]
    rfl

theorem blockHom_apply (A : ↥(stabX0 : Subgroup (SL3 F))) (i j : Fin 2) :
    ((blockHom A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) i.succ j.succ :=
  rfl

theorem mem_rootGroup_sup_of_blockHom_eq_one {A : ↥(stabX0 : Subgroup (SL3 F))}
    (hA : blockHom A = 1) :
    (A : SL3 F) ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
  have h0 := row_zero_of_mem_stabX0 A.2
  have hb : ∀ i j : Fin 2, ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) i.succ j.succ =
      if i = j then 1 else 0 := fun i j => by
    rw [← blockHom_apply, hA]
    simp [Matrix.one_apply]
  have e : (A : SL3 F) = rootElt 1 0 (((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0) *
      rootElt 2 0 (((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElt (show (1 : Fin 3) ≠ 0 by decide),
      coe_rootElt (show (2 : Fin 3) ≠ 0 by decide)]
    have h11 := hb 0 0
    have h12 := hb 0 1
    have h21 := hb 1 0
    have h22 := hb 1 1
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h11 h12 h21 h22
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply, h0,
        h11, h12, h21, h22]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 _))
    (Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 _))

theorem blockHom_rootElt_eq_one {i : Fin 3} (hi : i ≠ 0) (c : F) :
    blockHom ⟨rootElt i 0 c, rootGroup_sup_le_stabX0 (by
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 c)
      · exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 c))⟩ = 1 := by
  apply Subtype.ext
  ext a b
  rw [blockHom_apply, coe_rootElt hi]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj]
  have hb : (0 : Fin 3) ≠ b.succ := (Fin.succ_ne_zero b).symm
  simp [hb, Matrix.one_apply]

theorem rootGroup_sup_le_map_ker :
    (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ≤
      (blockHom (F := F)).ker.map (stabX0 : Subgroup (SL3 F)).subtype := by
  have key : ∀ i : Fin 3, i ≠ 0 → rootGroup i 0 ≤
      (blockHom (F := F)).ker.map (stabX0 : Subgroup (SL3 F)).subtype := by
    rintro i hi _ ⟨c, rfl⟩
    exact ⟨_, MonoidHom.mem_ker.mpr (blockHom_rootElt_eq_one hi c), rfl⟩
  exact sup_le (key 1 (by decide)) (key 2 (by decide))

theorem stabX0_le_normalizer :
    (stabX0 : Subgroup (SL3 F)) ≤
      Subgroup.normalizer ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) := by
  have key : ∀ A ∈ (stabX0 : Subgroup (SL3 F)), ∀ r ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 :
      Subgroup (SL3 F)), A * r * A⁻¹ ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
    intro A hA r hr
    obtain ⟨r', hr', rfl⟩ := rootGroup_sup_le_map_ker hr
    have hm : A * (r' : SL3 F) * A⁻¹ ∈ (stabX0 : Subgroup (SL3 F)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hA r'.2) (Subgroup.inv_mem _ hA)
    have e : (⟨A * (r' : SL3 F) * A⁻¹, hm⟩ : ↥(stabX0 : Subgroup (SL3 F))) =
        ⟨A, hA⟩ * r' * ⟨A, hA⟩⁻¹ := rfl
    refine mem_rootGroup_sup_of_blockHom_eq_one (A := ⟨_, hm⟩) ?_
    rw [e, map_mul, map_mul, MonoidHom.mem_ker.mp hr', mul_one, map_inv, mul_inv_cancel]
  intro A hA
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key A hA r, fun hr => ?_⟩
  have := key A⁻¹ (Subgroup.inv_mem _ hA) _ hr
  simpa [mul_assoc] using this

end Block

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
  {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
  (hψU : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
  (hψT : natImage ψ (Qv (puAmalgam h.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

include hφ hα hαβ hψU hψT in
theorem mem_qv_of_toSL3_mem {k : ↥(stab (puAmalgam h.le) α)}
    (hk : toSL3 ψ k ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) :
    (k : 𝔘) ∈ Qv (puAmalgam h.le) β := by
  rw [← hψT] at hk
  obtain ⟨t, ht, he⟩ := mem_natImage.mp hk
  have h1 : toSL3 ψ (t⁻¹ * k) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have h2 := (toSL3_eq_one_iff_mem_qv h hφ hα hψU _).mp h1
  have e : (k : 𝔘) = (t : 𝔘) * ((t⁻¹ * k : ↥(stab (puAmalgam h.le) α)) : 𝔘) := by simp
  rw [e]
  exact Subgroup.mul_mem _ ht (qv_le_qv _ h.hyp20 hα hαβ h2)

include hφ hα hαβ hψU hψT in
theorem mem_normalizer_qv_of_toSL3_mem {k : ↥(stab (puAmalgam h.le) α)}
    (hk : toSL3 ψ k ∈ (stabX0 : Subgroup (SL3 F))) :
    (k : 𝔘) ∈ Subgroup.normalizer (Qv (puAmalgam h.le) β : Set 𝔘) := by
  have key : ∀ k : ↥(stab (puAmalgam h.le) α), toSL3 ψ k ∈ (stabX0 : Subgroup (SL3 F)) →
      ∀ t ∈ Qv (puAmalgam h.le) β, (k : 𝔘) * t * (k : 𝔘)⁻¹ ∈ Qv (puAmalgam h.le) β := by
    intro k hk t ht
    have hts : t ∈ stab (puAmalgam h.le) α := qv_le_stab_of_adj _ hαβ.symm ht
    have hR : toSL3 ψ ⟨t, hts⟩ ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
      rw [← hψT]
      exact mem_natImage.mpr ⟨⟨t, hts⟩, ht, rfl⟩
    have := mem_qv_of_toSL3_mem h hφ hα hαβ hψU hψT (k := k * ⟨t, hts⟩ * k⁻¹) (by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (stabX0_le_normalizer hk) _).mp hR)
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key k hk t, fun ht => ?_⟩
  have := key k⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hk) _ ht
  simpa [mul_assoc] using this

omit [Fintype F] in
include hψU in
theorem commutator_mem_uloc (u : ↥(Uloc h.le L α)) (a : ↥(stab (puAmalgam h.le) α)) :
    ⁅(u : 𝔘), (a : 𝔘)⁆ ∈ Uloc h.le L α := by
  have hmem : (a : 𝔘) * u * (a : 𝔘)⁻¹ ∈ Uloc h.le L α :=
    (Subgroup.mem_normalizer_iff.mp (hψU.1 a.2) u).mp u.2
  rw [commutatorElement_def]
  have e : (u : 𝔘) * a * (u : 𝔘)⁻¹ * (a : 𝔘)⁻¹ = u * ((a : 𝔘) * u * (a : 𝔘)⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ u.2 (Subgroup.inv_mem _ hmem)

include hφ hα hαβ hψU hψT h464 in
theorem commutator_mem_zh_of_toSL3_mem {k : ↥(stab (puAmalgam h.le) α)}
    (hk : toSL3 ψ k ∈ (stabX0 : Subgroup (SL3 F))) :
    ∀ z ∈ ZM (puAmalgam h.le) α, ⁅z, (k : 𝔘)⁆ ∈ ZH (puAmalgam h.le) β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  intro z hz
  obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc h hfull hα hz
  have hζk : ζ * (k : 𝔘) = (k : 𝔘) * ζ :=
    (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hζ) k k.2).symm
  have e1 : ⁅u * ζ, (k : 𝔘)⁆ = ⁅u, (k : 𝔘)⁆ := by
    simp only [commutatorElement_def]
    calc u * ζ * (k : 𝔘) * (u * ζ)⁻¹ * (k : 𝔘)⁻¹
        = u * (ζ * (k : 𝔘)) * ζ⁻¹ * u⁻¹ * (k : 𝔘)⁻¹ := by group
      _ = u * ((k : 𝔘) * ζ) * ζ⁻¹ * u⁻¹ * (k : 𝔘)⁻¹ := by rw [hζk]
      _ = u * (k : 𝔘) * u⁻¹ * (k : 𝔘)⁻¹ := by group
  rw [e1]
  have hmem : ⁅u, (k : 𝔘)⁆ ∈ Uloc h.le L α := commutator_mem_uloc h hψU ⟨u, hu⟩ k
  have hnat := natVec_commutator hψU k ⟨u, hu⟩ ⟨_, hmem⟩ rfl
  have hc : natVec hψU ⟨_, hmem⟩ ∈ commN (natImage ψ (Qv (puAmalgam h.le) β)) := by
    rw [hψT]
    apply X3.mem_commN_of_apply_zero
    rw [hnat, Pi.sub_apply, hk (natVec hψU ⟨u, hu⟩), sub_self]
  have h1 := (mem_commutator_iff_natVec hψU (qv_le_stab_of_adj _ hαβ.symm) ⟨_, hmem⟩).mpr hc
  rw [← S4A.usup_eq_commutator_uloc h hfull hα hαβ] at h1
  exact h464 α β hα hαβ h1

include hφ hα hαβ hψU hψT h464 hsq in
theorem toSL3_mem_of_commutator_mem_zh {k : ↥(stab (puAmalgam h.le) α)}
    (hk : ∀ z ∈ ZM (puAmalgam h.le) α, ⁅z, (k : 𝔘)⁆ ∈ ZH (puAmalgam h.le) β) :
    toSL3 ψ k ∈ (stabX0 : Subgroup (SL3 F)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  intro v
  obtain ⟨u, rfl⟩ := natVec_surjective hψU v
  have hmem : ⁅(u : 𝔘), (k : 𝔘)⁆ ∈ Uloc h.le L α := commutator_mem_uloc h hψU u k
  have hZ : ⁅(u : 𝔘), (k : 𝔘)⁆ ∈ ZH 𝔛 β := hk u (uloc_le_zm h hfull hα u.2)
  have hU : ⁅(u : 𝔘), (k : 𝔘)⁆ ∈ Usup 𝔛 α β := by
    rw [zh_eq_usup_sup_zloc h hφ h464 hsq hα hαβ] at hZ
    obtain ⟨a, ha, ζ, hζ, he⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => commute_zh h (h464 α β hα hαβ ha) (zloc_le_zh h hfull hα hαβ hb)) hZ
    have haU : a ∈ Uloc h.le L α := usup_le_uloc' h hfull hα hαβ ha
    have hζU : ζ ∈ Uloc h.le L α := by
      have e : ζ = a⁻¹ * ⁅(u : 𝔘), (k : 𝔘)⁆ := by rw [he]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haU) hmem
    have hζ1 : ζ = 1 := by
      have h2 : ζ ∈ Uloc h.le L α ⊓ Zloc h.le L α := ⟨hζU, hζ⟩
      rw [uloc_inf_zloc h hfull α] at h2
      exact Subgroup.mem_bot.mp h2
    rw [he, hζ1, mul_one]
    exact ha
  rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ] at hU
  have hc := (mem_commutator_iff_natVec hψU (qv_le_stab_of_adj _ hαβ.symm) ⟨_, hmem⟩).mp hU
  rw [hψT] at hc
  have h0 := X3.apply_zero_of_mem_commN hc
  rw [natVec_commutator hψU k u ⟨_, hmem⟩ rfl, Pi.sub_apply, sub_eq_zero] at h0
  exact h0.symm

end Coord

section R4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (hq1 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (ZH (puAmalgam h.le) ρ).relIndex (ZM _ δ) = Fintype.card F)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

end R4

section R1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

end R1

section R2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

end R2

end CFSG.Quasithin.MS93.S468
