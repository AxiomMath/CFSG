module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13.U3.S6Out Equiv

private theorem s1611e3_coreAct_eq_one :
    ∀ σ : Perm (Fin 6), coreAct 6 σ = 1 → σ = 1 := by
  decide +kernel

theorem sixRho_injective : Function.Injective sixRho := by
  intro σ τ h
  have h1 : coreAct 6 σ = coreAct 6 τ := by
    apply MulEquiv.ext
    intro x
    have hx := congrArg (fun f : MulAut (SixE6 × SixE6) => f (x, 1)) h
    have hy := congrArg (fun p : SixE6 × SixE6 => p.1) hx
    simpa [sixRho] using hy
  have h2 : coreAct 6 (σ * τ⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  exact mul_inv_eq_one.mp (s1611e3_coreAct_eq_one (σ * τ⁻¹) h2)

theorem sixS0_key : phi sixS0 * cc * sixS0 = 1 := by
  decide +kernel

theorem sixAlpha_sixAlpha (σ : Perm (Fin 6)) : sixAlpha (sixAlpha σ) = σ := by
  have h1 : phi sixS0 = sixS0⁻¹ * cc⁻¹ := by
    calc phi sixS0 = phi sixS0 * cc * sixS0 * sixS0⁻¹ * cc⁻¹ := by group
      _ = sixS0⁻¹ * cc⁻¹ := by rw [sixS0_key]; group
  calc sixAlpha (sixAlpha σ) = phi (sixS0 * phi (sixS0 * σ * sixS0⁻¹) * sixS0⁻¹) := rfl
    _ = phi sixS0 * phi (phi (sixS0 * σ * sixS0⁻¹)) * (phi sixS0)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    _ = σ := by rw [phi_phi, h1]; group

theorem sixSwap_mul_self : sixSwap * sixSwap = 1 := by
  apply MulEquiv.ext
  intro x
  rcases x with ⟨a, b⟩
  rfl

private theorem s1611e3_sixSwap_inv : sixSwap⁻¹ = sixSwap :=
  inv_eq_of_mul_eq_one_right sixSwap_mul_self

theorem sixSwap_conj_rho (σ : Perm (Fin 6)) :
    sixSwap * sixRho σ * sixSwap⁻¹ = sixRho (sixAlpha σ) := by
  rw [s1611e3_sixSwap_inv]
  apply MulEquiv.ext
  intro x
  rcases x with ⟨a, b⟩
  simp [sixSwap, sixRho, sixAlpha_sixAlpha]

private theorem s1611e3_swap_conj_rho_swap (σ : Perm (Fin 6)) :
    sixSwap * sixRho σ * sixSwap = sixRho (sixAlpha σ) :=
  calc sixSwap * sixRho σ * sixSwap
      = sixSwap * sixRho σ * sixSwap⁻¹ := by rw [s1611e3_sixSwap_inv]
    _ = sixRho (sixAlpha σ) := sixSwap_conj_rho σ

private theorem s1611e3_mem_closure_pair_union {G : Type*} [Group G] (H : Subgroup G) {y : G}
    (hy : y * y = 1) (hH : ∀ h ∈ H, y * h * y ∈ H) {g : G}
    (hg : g ∈ Subgroup.closure ((H : Set G) ∪ {y})) :
    g ∈ H ∨ ∃ h ∈ H, g = y * h := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hmid : ∀ a : G, y * (y * a * y) = a * y := by
    intro a
    rw [show y * (y * a * y) = (y * y) * (a * y) by group, hy, one_mul]
  let S : Subgroup G :=
    { carrier := (H : Set G) ∪ {x | ∃ h ∈ H, x = y * h}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
        · exact Or.inl (H.mul_mem ha hb)
        · refine Or.inr ⟨(y * a * y) * b', H.mul_mem (hH a ha) hb', ?_⟩
          rw [show a * (y * b') = (a * y) * b' by group, ← hmid a]
          group
        · exact Or.inr ⟨a' * b, H.mul_mem ha' hb, by group⟩
        · exact Or.inl (by
            rw [show (y * a') * (y * b') = (y * a' * y) * b' by group]
            exact H.mul_mem (hH a' ha') hb')
      inv_mem' := by
        rintro a (ha | ⟨a', ha', rfl⟩)
        · exact Or.inl (H.inv_mem ha)
        · refine Or.inr ⟨y * a'⁻¹ * y, hH a'⁻¹ (H.inv_mem ha'), ?_⟩
          rw [show (y * a')⁻¹ = a'⁻¹ * y by rw [mul_inv_rev, hyinv], ← hmid a'⁻¹] }
  have hle : Subgroup.closure ((H : Set G) ∪ {y}) ≤ S := by
    rw [Subgroup.closure_le]
    rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨1, H.one_mem, by rw [Set.mem_singleton_iff.mp hz, mul_one]⟩
  exact hle hg

private theorem s1611e3_mem_sixGhat {g : MulAut (SixE6 × SixE6)} (hg : g ∈ sixGhat) :
    (∃ σ : Perm (Fin 6), sixRho σ = g) ∨
      ∃ σ : Perm (Fin 6), sixSwap * sixRho σ = g := by
  have hghat : sixGhat =
      Subgroup.closure ((sixRho.range : Set (MulAut (SixE6 × SixE6))) ∪ {sixSwap}) := by
    rw [sixGhat, ← MonoidHom.coe_range]
  rw [hghat] at hg
  rcases s1611e3_mem_closure_pair_union sixRho.range sixSwap_mul_self
      (fun h hh => by
        obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
        exact ⟨sixAlpha σ, (s1611e3_swap_conj_rho_swap σ).symm⟩) hg with hg | ⟨h, hh, rfl⟩
  · obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hg
    exact Or.inl ⟨σ, rfl⟩
  · obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact Or.inr ⟨σ, rfl⟩

private theorem s1611e3_coreAct_sixZ (τ : Perm (Fin 6)) : coreAct 6 τ sixZ = sixZ := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  simp [sixZ, coreAct_coe, permAct_apply, allOnes]

private theorem s1611e3_centralizer_alt_trivial_aux :
    ∀ σ : Perm (Fin 6),
      (∀ a : Perm (Fin 6), Perm.sign a = 1 → σ * a = a * σ) → σ = 1 := by
  decide +kernel

private theorem s1611e3_centralizer_alt_trivial :
    ∀ σ : Perm (Fin 6), (∀ a ∈ alternatingGroup (Fin 6), σ * a = a * σ) → σ = 1 := by
  intro σ h
  exact s1611e3_centralizer_alt_trivial_aux σ
    (fun a ha => h a (Perm.mem_alternatingGroup.mpr ha))

private def s1611e3_c012 : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5, by
    rw [Perm.mem_alternatingGroup]; decide⟩

private theorem s1611e3_c012_support :
    (s1611e3_c012 : Perm (Fin 6)).support.card = 6 := by
  decide

private theorem s1611e3_sixAlpha_c012_support :
    (sixAlpha (s1611e3_c012 : Perm (Fin 6))).support.card = 3 := by
  decide +kernel

private theorem s1611e3_sixAlpha_not_inner :
    ¬ ∃ σ : Perm (Fin 6),
      sixAlpha (s1611e3_c012 : Perm (Fin 6)) =
        σ * (s1611e3_c012 : Perm (Fin 6)) * σ⁻¹ := by
  rintro ⟨σ, hσ⟩
  have hcard := congrArg (fun τ : Perm (Fin 6) => τ.support.card) hσ
  rw [s1611e3_sixAlpha_c012_support, Equiv.Perm.card_support_conj,
    s1611e3_c012_support] at hcard
  exact absurd hcard (by decide)

theorem sixGhat_normalizes : ∀ g ∈ sixGhat, ∀ l ∈ sixLhat, g * l * g⁻¹ ∈ sixLhat := by
  intro g hg l hl
  rw [sixLhat, Subgroup.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  rcases s1611e3_mem_sixGhat hg with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · have heq : sixRho σ * sixRho a * (sixRho σ)⁻¹ = sixRho (σ * a * σ⁻¹) := by
      simp only [map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map_of_mem sixRho (Subgroup.Normal.conj_mem inferInstance a ha σ)
  · have heq : (sixSwap * sixRho σ) * sixRho a * (sixSwap * sixRho σ)⁻¹ =
        sixRho (sixAlpha (σ * a * σ⁻¹)) := by
      calc (sixSwap * sixRho σ) * sixRho a * (sixSwap * sixRho σ)⁻¹
          = sixSwap * (sixRho σ * sixRho a * (sixRho σ)⁻¹) * sixSwap⁻¹ := by group
        _ = sixSwap * sixRho (σ * a * σ⁻¹) * sixSwap⁻¹ := by
              rw [show sixRho σ * sixRho a * (sixRho σ)⁻¹ = sixRho (σ * a * σ⁻¹) by
                simp only [map_mul, map_inv]]
        _ = sixRho (sixAlpha (σ * a * σ⁻¹)) := sixSwap_conj_rho _
    rw [heq]
    exact Subgroup.mem_map_of_mem sixRho
      (sixAlpha_mem_alt (Subgroup.Normal.conj_mem inferInstance a ha σ))

theorem sixGhat_cent_eq_one : ∀ g ∈ sixGhat, (∀ l ∈ sixLhat, g * l = l * g) → g = 1 := by
  intro g hg hc
  rcases s1611e3_mem_sixGhat hg with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · have hσ : σ = 1 := by
      apply s1611e3_centralizer_alt_trivial
      intro a ha
      have hmem : sixRho a ∈ sixLhat := by
        rw [sixLhat]
        exact Subgroup.mem_map_of_mem sixRho ha
      apply sixRho_injective
      rw [map_mul, map_mul]
      exact hc (sixRho a) hmem
    rw [hσ, map_one]
  · exfalso
    have hmem : (s1611e3_c012 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := s1611e3_c012.2
    have hmemL : sixRho (s1611e3_c012 : Perm (Fin 6)) ∈ sixLhat := by
      rw [sixLhat]
      exact Subgroup.mem_map_of_mem sixRho hmem
    have hconj : (sixSwap * sixRho σ) * sixRho (s1611e3_c012 : Perm (Fin 6)) *
        (sixSwap * sixRho σ)⁻¹ = sixRho (s1611e3_c012 : Perm (Fin 6)) := by
      rw [hc _ hmemL]
      group
    have h2 : sixRho (sixAlpha (σ * (s1611e3_c012 : Perm (Fin 6)) * σ⁻¹)) =
        sixRho (s1611e3_c012 : Perm (Fin 6)) := by
      calc sixRho (sixAlpha (σ * (s1611e3_c012 : Perm (Fin 6)) * σ⁻¹))
          = sixSwap * sixRho (σ * (s1611e3_c012 : Perm (Fin 6)) * σ⁻¹) * sixSwap⁻¹ :=
              (sixSwap_conj_rho _).symm
        _ = (sixSwap * sixRho σ) * sixRho (s1611e3_c012 : Perm (Fin 6)) *
              (sixSwap * sixRho σ)⁻¹ := by
                simp only [map_mul, map_inv]
                group
        _ = sixRho (s1611e3_c012 : Perm (Fin 6)) := hconj
    have hrel : sixAlpha (s1611e3_c012 : Perm (Fin 6)) =
        σ * (s1611e3_c012 : Perm (Fin 6)) * σ⁻¹ := by
      have hstep := congrArg sixAlpha (sixRho_injective h2)
      rw [sixAlpha_sixAlpha] at hstep
      exact hstep.symm
    exact s1611e3_sixAlpha_not_inner ⟨σ, hrel⟩

theorem sixDiag_invariant :
    ∀ g ∈ sixGhat, ∀ u ∈ sixDiag, (g : MulAut (SixE6 × SixE6)) u ∈ sixDiag := by
  intro g hg u hu
  have hfix : (g : MulAut (SixE6 × SixE6)) (sixZ, sixZ) = (sixZ, sixZ) := by
    rcases s1611e3_mem_sixGhat hg with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
    · show ((coreAct 6 σ) sixZ, (coreAct 6 (sixAlpha σ)) sixZ) = (sixZ, sixZ)
      rw [s1611e3_coreAct_sixZ, s1611e3_coreAct_sixZ]
    · show sixSwap ((sixRho σ) (sixZ, sixZ)) = (sixZ, sixZ)
      rw [show (sixRho σ) (sixZ, sixZ) = (sixZ, sixZ) from by
        show ((coreAct 6 σ) sixZ, (coreAct 6 (sixAlpha σ)) sixZ) = (sixZ, sixZ)
        rw [s1611e3_coreAct_sixZ, s1611e3_coreAct_sixZ]]
      rfl
  have hu' : u ∈ Subgroup.zpowers (sixZ, sixZ) := hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
  rw [map_zpow g (sixZ, sixZ) k, hfix]
  exact Subgroup.zpow_mem_zpowers (sixZ, sixZ) k

theorem sixLhat_isAlt : UC22.IsAlt ↥sixLhat 6 := by
  rw [sixLhat]
  exact ⟨(Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) sixRho
    sixRho_injective).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
