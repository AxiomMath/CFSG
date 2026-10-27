module

public import CFSG.Sporadic.Recognition.J4MultiplierIota
public import CFSG.Monster.Schur.Restriction
public import CFSG.Sporadic.Co1.Cover.Rels
public import CFSG.Sporadic.Recognition.J4MultiplierFox

public section

namespace CFSG.Sporadic.Recognition.J4Multiplier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.Co1.Cover CFSG.Monster.Schur
  CFSG.Monster.Schur.M24 SemidirectProduct
open scoped commutatorElement

theorem closure_gen_pair :
    Subgroup.closure ({gen 0, gen 1} : Set PM24) = ⊤ := by
  have h : Set.range gen = ({gen 0, gen 1} : Set PM24) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    tauto
  rw [← h]
  exact closure_gen

theorem perfect_PM24 :
    Group.IsPerfect PM24 := by
  have := isSimpleGroup_PM24
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator PM24) with h | h
  · exfalso
    have hc : ∀ a b : PM24, a * b = b * a := fun a b => by
      have hmem : ⁅a, b⁆ ∈ commutator PM24 :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have : IsMulCommutative PM24 := ⟨⟨hc⟩⟩
    have hp := (Group.is_simple_iff_prime_card (α := PM24)).1 isSimpleGroup_PM24
    rw [natCard_PM24] at hp
    norm_num at hp
  · exact h


theorem noPerfectDoubleCover_J (hFox : J4FoxCert) (hForm : J4FormCert) :
    NoPerfectDoubleCover J := by
  apply noPerfectDoubleCover_of_odd_index_complement
  intro E _ π hπ hE h2
  obtain ⟨ζ, hζ1, hζc, hζ2, hker⟩ := exists_central_involution_of_card_ker_eq_two π h2
  have hζcomm : ∀ g : E, ζ * g = g * ζ := fun g => (Subgroup.mem_center_iff.1 hζc g).symm
  have hζker : ζ ∈ π.ker := by
    rw [hker]
    exact Subgroup.mem_zpowers ζ
  let X : Subgroup (SJ × E) :=
    (theta.comp (MonoidHom.fst SJ E)).eqLocus (π.comp (MonoidHom.snd SJ E))
  let ψ : X →* SJ := (MonoidHom.fst SJ E).comp X.subtype
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨y, hy⟩ := hπ (theta s)
    exact ⟨⟨(s, y), hy.symm⟩, rfl⟩
  let z : X := ⟨(1, ζ), by
    show theta 1 = π ζ
    rw [map_one, MonoidHom.mem_ker.1 hζker]⟩
  have hzc : ∀ x : X, z * x = x * z := fun x =>
    Subtype.ext (Prod.ext (by simp [z]) (hζcomm x.1.2))
  have hz2 : z * z = 1 := Subtype.ext (Prod.ext (one_mul 1) hζ2)
  have hzne : z ≠ 1 := fun h => hζ1 (congrArg (fun x : X => x.1.2) h)
  have hkerψ : ψ.ker = Subgroup.zpowers z := by
    ext x
    constructor
    · intro hx
      have hx1 : x.1.1 = 1 := hx
      have hmem : x.1.2 ∈ π.ker := by
        rw [MonoidHom.mem_ker, ← (show theta x.1.1 = π x.1.2 from x.2), hx1, map_one]
      rw [hker] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · simp [z, hx1]
      · simp [z, hk]
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      show ((z ^ k : X) : SJ × E).1 = 1
      simp [z]
  have := perfect_PM24
  obtain ⟨σ, hσ⟩ := exists_P_section rho ψ noPerfectDoubleCover_M24 hψ z hz2 hzne hkerψ
  obtain ⟨τ, hτ⟩ := exists_hom_section rho ψ noPerfectDoubleCover_M24 (gen 0) (gen 1)
    closure_gen_pair j4A j4B rho_gen0 rho_gen1 (hC_proof_j4 hForm) hl_proof_j4 0 (map_zero _)
    gen_sq (fun l hl _ => hfox_proof_j4 (gen 0) (gen 1) rho rho_gen0 rho_gen1 hFox hrel_M24 l hl)
    hψ hzc hz2 hzne hkerψ (σ (gen 0)) (by rw [← map_mul, gen_sq, map_one])
    (by rw [hσ, ofAdd_zero, map_one, one_mul])
  let τ' : SJ →* E := (MonoidHom.snd SJ E).comp (X.subtype.comp τ)
  have hτ' : ∀ s, π (τ' s) = theta s := by
    intro s
    have h1 : theta (τ s).1.1 = π (τ s).1.2 := (τ s).2
    have h2 : (τ s).1.1 = s := hτ s
    show π (τ s).1.2 = theta s
    rw [← h1, h2]
  refine ⟨theta.range.comap π, τ'.range, ?_, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ hπ]
    exact odd_index_theta
  · rw [eq_bot_iff]
    rintro y ⟨⟨s, rfl⟩, hyk⟩
    have h1 : π (τ' s) = 1 := hyk
    rw [hτ'] at h1
    have hs : s = 1 := theta_injective (h1.trans (map_one theta).symm)
    rw [hs, map_one]
    exact Subgroup.one_mem _
  · apply le_antisymm
    · apply sup_le
      · rintro _ ⟨s, rfl⟩
        show π (τ' s) ∈ theta.range
        rw [hτ']
        exact ⟨s, rfl⟩
      · intro y hy
        show π y ∈ theta.range
        rw [MonoidHom.mem_ker.1 hy]
        exact Subgroup.one_mem _
    · intro y hy
      obtain ⟨s, hs⟩ := (show π y ∈ theta.range from hy)
      have hyk : (τ' s)⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hτ', hs, inv_mul_cancel]
      have e : y = τ' s * ((τ' s)⁻¹ * y) := by group
      rw [e]
      exact Subgroup.mul_mem_sup ⟨s, rfl⟩ hyk

theorem noPerfectDoubleCover_J4 (hFox : J4FoxCert) (hForm : J4FormCert) :
    NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.J4 :=
  @NoPerfectDoubleCover.of_mulEquiv J CFSG.Blueprint.NativeSporadic.J4 (Subgroup.toGroup J) _
    (seedEquiv j4Facts.mat).symm (noPerfectDoubleCover_J hFox hForm)

end CFSG.Sporadic.Recognition.J4Multiplier
