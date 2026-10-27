module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChain24
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChainGen

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.Code

private def offSet24 : Finset (Fin 24) := {8, 11, 13, 14, 17, 18, 20, 23}

private theorem isOctad_offSet24 : IsOctad offSet24 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · have hbvec : ∀ i : Fin 24, bvec 24 9857280 i = if i ∈ offSet24 then 1 else 0 := by
      intro i
      fin_cases i <;> decide +kernel
    rw [mem_golayC_iff']
    have h : Multiplicative.toAdd (eY offSet24) = bvec 24 9857280 := by
      funext i
      rw [toAdd_eY, hbvec i]
    rw [h]
    exact (bvec_mem_C_iff 9857280).2 (by decide +kernel)

private theorem mem_offPts24_iff (i : Fin 24) : (i : ℕ) ∈ offPts24 ↔ i ∈ offSet24 := by
  fin_cases i <;> decide +kernel

private theorem fixes_off_subprods :
    ∀ l : List T24s2.Elem,
      (∀ s ∈ l, ∀ y ∈ offSet24, ((phi24 s : ↥AutPerm) : S24) y = y) →
      ∀ t ∈ subprods l, ∀ y ∈ offSet24, ((phi24 t : ↥AutPerm) : S24) y = y := by
  intro l
  induction l with
  | nil =>
    intro _ t ht
    rw [subprods, List.mem_singleton] at ht
    rw [ht, map_one]
    intro y _
    rfl
  | cons b l ih =>
    intro h t ht y hy
    rw [mem_subprods_cons] at ht
    rcases ht with ht | ⟨w, hw, rfl⟩
    · exact ih (fun s hs => h s (List.mem_cons_of_mem b hs)) t ht y hy
    · simp only [map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]
      rw [ih (fun s hs => h s (List.mem_cons_of_mem b hs)) w hw y hy,
        h b List.mem_cons_self y hy]

theorem chain_octad24 {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) {V : Type}
    [CommGroup V] [Finite V] (ρ : ↥Γ →* MulAut V) (hρ : Function.Injective ρ) (e : V ≃* W11)
    (he : ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v)) {A : Subgroup (MulAut V)}
    (hAρ : A ≤ ρ.range) (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hF : rkIdx (fixV A) ≤ rk ↥A + 1) :
    ∃ O' : Finset (Fin 24), IsOctad O' ∧ octFix O' ≤ Γ ∧ A = rImg ρ (octFix O') := by
  have hcongr : ∀ γ : ↥Γ, congrHom e (ρ γ) = rho11 Γ hΓ γ := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    change e (ρ γ (e.symm w)) = rho11 Γ hΓ γ w
    rw [he γ (e.symm w), e.apply_symm_apply]
  have hAR : A.map (congrHom e) ≤ rhoM24.range := by
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨γ, hγ⟩ := hAρ ha
    refine ⟨⟨(γ : S24), hΓ γ.2⟩, ?_⟩
    rw [← hγ, hcongr γ]
    rfl
  obtain ⟨g, l, hind, hl4, hoff, hch⟩ := chain_shape24 e hAR hA2 hA1 hF
  have hcardA : Nat.card ↥A = 16 := by
    rw [card_of_chainSub hch (chainAut24_injective e g) hind, hl4]
    norm_num
  let O' : Finset (Fin 24) := ((g⁻¹ : ↥AutPerm) : S24) • offSet24
  have hO' : IsOctad O' := isOctad_smul (g⁻¹ : ↥AutPerm).2 isOctad_offSet24
  have hfix : ∀ a ∈ A, ∃ γ : ↥Γ, ρ γ = a ∧ ∀ x ∈ O', (γ : S24) x = x := by
    intro a ha
    obtain ⟨γ, hγ⟩ := hAρ ha
    obtain ⟨s, hs, rfl⟩ := (hch a).1 ha
    have hkey : congrHom e (chainAut e rhoM24 phi24 g s) = rhoM24 (g⁻¹ * phi24 s * g) := by
      refine MulEquiv.ext fun w => ?_
      have h1 : rhoM24 g (congrHom e (chainAut e rhoM24 phi24 g s) w) =
          rhoM24 ((phi24 s) * g) w := by
        calc rhoM24 g (congrHom e (chainAut e rhoM24 phi24 g s) w)
            = congrHom (twistEquiv e rhoM24 g) (chainAut e rhoM24 phi24 g s) (rhoM24 g w) := by
              rw [congrHom_twist_apply, MulEquiv.symm_apply_apply]
          _ = rhoM24 (phi24 s) (rhoM24 g w) :=
            congrArg (fun f : MulAut W11 => f (rhoM24 g w))
              (congrHom_chainAut e rhoM24 phi24 g s)
          _ = rhoM24 ((phi24 s) * g) w := by simp only [map_mul, MulAut.mul_apply]
      have h3 : rhoM24 ((phi24 s) * g) w =
          rhoM24 g (rhoM24 (g⁻¹ * phi24 s * g) w) := by
        rw [show (phi24 s) * g = g * (g⁻¹ * phi24 s * g) from by group, map_mul,
          MulAut.mul_apply]
      exact (rhoM24 g).injective (h1.trans h3)
    have h1 : rho11 Γ hΓ γ = rhoM24 (g⁻¹ * phi24 s * g) := by
      rw [← hcongr γ, hγ, hkey]
    have hperm : (γ : S24) = ((g⁻¹ * phi24 s * g : ↥AutPerm) : S24) := by
      have hA : (⟨(γ : S24), hΓ γ.2⟩ : ↥AutPerm) = g⁻¹ * phi24 s * g := by
        apply rho11_injective AutPerm le_rfl
        rw [show rho11 AutPerm le_rfl ⟨(γ : S24), hΓ γ.2⟩ = rho11 Γ hΓ γ from rfl, h1]
      exact congrArg Subtype.val hA
    have hphi : ∀ t ∈ subprods l, ∀ y ∈ offSet24, ((phi24 t : ↥AutPerm) : S24) y = y :=
      fixes_off_subprods l fun s hs y hy => by
        have hall := List.all_eq_true.1 (hoff s hs)
        have harr : HasArr (((phi24 s : ↥AutPerm) : S24)) (T24s2.arr s) :=
          T24s2.hasArr_toSub AutPerm _ s
        have hyl : (y : ℕ) ∈ offPts24 := (mem_offPts24_iff y).2 hy
        have h1 : (T24s2.arr s)[(y : ℕ)]! = (y : ℕ) :=
          beq_iff_eq.1 (hall (y : ℕ) hyl)
        exact Fin.ext (by rw [harr y, h1])
    refine ⟨γ, hγ, ?_⟩
    intro x hx
    rw [hperm]
    change x ∈ ((g⁻¹ : ↥AutPerm) : S24) • offSet24 at hx
    rw [smul_finset_eq_map, Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (((g⁻¹ * phi24 s * g : ↥AutPerm) : S24) (((g⁻¹ : ↥AutPerm) : S24) y)) =
      ((g⁻¹ : ↥AutPerm) : S24) y
    rw [show ((g⁻¹ * phi24 s * g : ↥AutPerm) : S24) =
        (g : S24)⁻¹ * (phi24 s : S24) * (g : S24) from by simp]
    simp only [Subgroup.coe_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    rw [Equiv.apply_symm_apply, hphi s hs y hy]
  obtain ⟨hle, hAeq⟩ := eq_rImg_octFix_of_fixing hΓ ρ hρ hcardA hO' hfix
  exact ⟨O', hO', hle, hAeq⟩

end CFSG.ASVolI.AppH

