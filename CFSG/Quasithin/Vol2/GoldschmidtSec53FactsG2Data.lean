module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.Sec53F.BA
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

noncomputable def fieldAut (K : Type) [Field K] : (K ≃+* K) →* MulAut ↥(adjointGroup Tag.G2 K) where
  toFun σ := exactNormalAut Tag.G2 K 1 σ 0
  map_one' := exactNormalAut_one_one_zero
  map_mul' σ σ' := (exactNormalAut_one_zero_mul σ σ').symm

theorem fieldAut_apply (σ : K ≃+* K) (h : ↥(adjointGroup Tag.G2 K)) :
    ((fieldAut K σ h : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) := by
  show (exactNormalAut Tag.G2 K 1 σ 0 h : ModGL Tag.G2 K) = _
  rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]


theorem entrywise_mem_posUnipotent_iff (σ : K ≃+* K) (x : ModGL Tag.G2 K) :
    Units.map (entrywiseHom σ.toRingHom) x ∈ posUnipotent Tag.G2 K ↔
      x ∈ posUnipotent Tag.G2 K := by
  have h := map_exactEntrywiseAut (τ := Tag.G2) σ (H := posUnipotent Tag.G2 K)
    (Or.inr (Or.inl rfl))
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hzx' : z = x := (exactEntrywiseAut Tag.G2 σ).injective hzx
    rwa [hzx'] at hz
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩

theorem entrywise_rootDiagUnit (σ : K ≃+* K) (a : Fin Tag.G2.rank → Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.G2 a) =
      rootDiagUnit Tag.G2 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) := by
  refine Units.ext ?_
  have h := entrywise_rootDiag (τ := Tag.G2) σ.toRingHom a
  exact h

theorem entrywise_torusElt (σ : K ≃+* K) (i : Fin Tag.G2.rank) (t : Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (torusElt Tag.G2 K i t) =
      torusElt Tag.G2 K i (Units.map σ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, entrywise_rootDiagUnit]
  congr 1
  funext j
  simp [map_zpow]

theorem entrywise_mem_torusGroup (σ : K ≃+* K) {h : ModGL Tag.G2 K} (hh : h ∈ torusGroup Tag.G2 K) :
    Units.map (entrywiseHom σ.toRingHom) h ∈ torusGroup Tag.G2 K := by
  have : torusGroup Tag.G2 K ≤
      (torusGroup Tag.G2 K).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [entrywise_torusElt]
    exact torusElt_mem_torusGroup _ _
  exact this hh


section Struct

variable [Finite K] [CharP K 2]

theorem g2_center : ∀ y : ↥(adjointGroup Tag.G2 K), (∀ x, y * x = x * y) → y = 1 := by
  intro y hy
  have : y ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) :=
    Subgroup.mem_center_iff.mpr fun g => (hy g).symm
  rw [center_adjointGroup_eq_bot] at this
  exact Subgroup.mem_bot.mp this

theorem g2_sylow : IsSylowTwoOf (posUnipotentSub Tag.G2 K) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  exact isSylowTwoOf_subgroupOf_top
    (isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)

theorem g2_H_comm : ∀ a ∈ torusSub Tag.G2 K, ∀ b ∈ torusSub Tag.G2 K, a * b = b * a := by
  intro a ha b hb
  exact Subtype.ext ((triangular_borel_structure.{0, 0} Tag.G2 K).1 a.1 ha b.1 hb)

theorem g2_H_le : torusSub Tag.G2 K ≤ Subgroup.normalizer
    ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have := Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_posUnipotent hh) u.1
  exact this

theorem g2_U_inf_H : ∀ x ∈ posUnipotentSub Tag.G2 K, x ∈ torusSub Tag.G2 K → x = 1 := by
  intro x hx hxH
  have : x ∈ posUnipotentSub Tag.G2 K ⊓ torusSub Tag.G2 K := ⟨hx, hxH⟩
  rw [posUnipotentSub_inf_torusSub] at this
  exact Subgroup.mem_bot.mp this

theorem g2_B_eq : ∀ g ∈ Subgroup.normalizer
    ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)), ∃ u ∈ posUnipotentSub Tag.G2 K,
        ∃ h ∈ torusSub Tag.G2 K, g = u * h := by
  intro g hg
  rw [normalizer_subgroupOf_eq' posUnipotent_le_adjointGroup,
    (borel_self_normalizers Tag.G2 K).1] at hg
  have hg' : g ∈ (borelSub Tag.G2 K : Set ↥(adjointGroup Tag.G2 K)) := hg
  rw [borelSub_eq_mul, borelSub_inf_monomialSub] at hg'
  obtain ⟨u, hu, h, hh, rfl⟩ := hg'
  exact ⟨u, hu, h, hh, rfl⟩

end Struct


section Aut

variable [Finite K] [CharP K 2]

theorem g2_F_U : ∀ σ ∈ (fieldAut K).range, ∀ x : ↥(adjointGroup Tag.G2 K),
    σ x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K := by
  rintro _ ⟨σ, rfl⟩ x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, fieldAut_apply]
  exact entrywise_mem_posUnipotent_iff σ x.1

theorem g2_F_H : ∀ σ ∈ (fieldAut K).range, ∀ h ∈ torusSub Tag.G2 K,
    σ h ∈ torusSub Tag.G2 K := by
  rintro _ ⟨σ, rfl⟩ h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [fieldAut_apply]
  exact entrywise_mem_torusGroup σ hh

theorem g2_F_comm : ∀ σ ∈ (fieldAut K).range, ∀ τ ∈ (fieldAut K).range, σ * τ = τ * σ := by
  rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact RingEquiv.ext fun c => ringEquiv_comm_of_finite τ σ c

theorem g2_F_faithful : ∀ σ ∈ (fieldAut K).range, (∀ h ∈ torusSub Tag.G2 K, σ h = h) → σ = 1 := by
  rintro _ ⟨σ₀, rfl⟩ hfix
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
  have key : ∀ a : Fin Tag.G2.rank → Kˣ,
      (fun i => Units.map σ₀.toRingHom.toMonoidHom (a i)) = a := by
    intro a
    obtain ⟨-, hT, hC, -⟩ := hrest B hB a
    have hd : (⟨rootDiagUnit Tag.G2 a, hC⟩ : ↥(adjointGroup Tag.G2 K)) ∈ torusSub Tag.G2 K := hT
    have h1 := congrArg (fun x : ↥(adjointGroup Tag.G2 K) => (x : ModGL Tag.G2 K))
      (hfix _ hd)
    simp only [fieldAut_apply, entrywise_rootDiagUnit] at h1
    apply rootDiagAutHom_injective (τ := Tag.G2) (K := K)
    refine MulEquiv.ext fun g => Subtype.ext ?_
    show ((rootDiagAut Tag.G2 K _ g : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      ((rootDiagAut Tag.G2 K a g : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K)
    rw [coe_rootDiagAut, coe_rootDiagAut, h1]
  have hu : ∀ u : Kˣ, σ₀ (u : K) = u := by
    intro u
    have := congrFun (key fun _ => u) ⟨0, by decide⟩
    simpa using congrArg Units.val this
  have hσ : σ₀ = 1 := by
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · subst hc
      simp
    · exact hu (Units.mk0 c hc)
  rw [hσ, map_one]

theorem g2_normal_form {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut ↥(adjointGroup Tag.G2 K))
    (hα : ∀ x, α x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K) :
    ∃ g ∈ Subgroup.normalizer ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)), ∃ σ ∈ (fieldAut K).range, α = MulAut.conj g * σ := by
  obtain ⟨hex, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, σ₀⟩, hgσ, -⟩ := hex α
  have hα' : α = MulAut.conj g * fieldAut K σ₀ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hgσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, fieldAut_apply]
  refine ⟨g, ?_, fieldAut K σ₀, ⟨σ₀, rfl⟩, hα'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : (MulAut.conj g) y = α ((fieldAut K σ₀)⁻¹ y) := by
    rw [hα', MulAut.mul_apply, MulAut.apply_inv_self]
  have h1 := hα ((fieldAut K σ₀)⁻¹ y)
  have h2 := g2_F_U (fieldAut K σ₀) ⟨σ₀, rfl⟩ ((fieldAut K σ₀)⁻¹ y)
  rw [MulAut.apply_inv_self] at h2
  rw [← MulAut.conj_apply, e, h1]
  exact h2

end Aut

end CFSG.Quasithin.H13.Sec53F.G2
