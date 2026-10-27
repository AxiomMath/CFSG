module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChain22
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChainGen
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.Code

private def offSet22 : Finset (Fin 24) := Finset.univ.filter fun i => (i : ℕ) ∈ offPts22

private theorem mem_offSet22 (i : Fin 24) : i ∈ offSet22 ↔ (i : ℕ) ∈ offPts22 := by
  simp [offSet22]

private theorem isOctad_offSet22 : IsOctad offSet22 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · have hbvec : ∀ i : Fin 24, bvec 24 696467 i = if (i : ℕ) ∈ offPts22 then 1 else 0 := by
      decide +kernel
    rw [mem_golayC_iff']
    have h : Multiplicative.toAdd (eY offSet22) = bvec 24 696467 := by
      funext i
      rw [toAdd_eY, hbvec i]
      by_cases hi : (i : ℕ) ∈ offPts22 <;> simp [offSet22, hi]
    rw [h]
    exact (bvec_mem_C_iff 696467).2 (by decide +kernel)

private theorem phi22_fix_single {s : T22s2.Elem}
    (h : fixesOff22 s = true) :
    ∀ y : Fin 24, y ∈ offSet22 → (phi22 s : S24) y = y := by
  intro y hy
  have hoff : (y : ℕ) ∈ offPts22 := (mem_offSet22 y).1 hy
  have harr : ((phi22 s : S24) y : ℕ) = (T22s2.arr s)[(y : ℕ)]! :=
    T22s2.hasArr_toSub mog22plus (T22s2.mem_mog22plus T22s2_ok.2.2) s y
  have hall : (T22s2.arr s)[(y : ℕ)]! = (y : ℕ) := by
    have h1 := List.all_eq_true.1 h (y : ℕ) hoff
    simpa using h1
  apply Fin.ext
  rw [harr, hall]

private theorem phi22_fix_subprods {l : List T22s2.Elem}
    (hoff : ∀ s ∈ l, fixesOff22 s = true) :
    ∀ t ∈ subprods l, ∀ y : Fin 24, y ∈ offSet22 → (phi22 t : S24) y = y := by
  induction l with
  | nil =>
    intro t ht y hy
    simp only [subprods, List.mem_singleton] at ht
    rw [ht, map_one]
    simp
  | cons a l ih =>
    intro t ht y hy
    rw [mem_subprods_cons] at ht
    rcases ht with ht | ⟨w, hw, rfl⟩
    · exact ih (fun s hs => hoff s (List.mem_cons_of_mem a hs)) t ht y hy
    · rw [map_mul]
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
      rw [ih (fun s hs => hoff s (List.mem_cons_of_mem a hs)) w hw y hy]
      exact phi22_fix_single (hoff a List.mem_cons_self) y hy

theorem chain_octad22 {τ : S24} (hτ : τ ∈ AutPerm) {Γ : Subgroup S24}
    (hΓM : Γ ≤ M24g) {V : Type} [CommGroup V] [Finite V] (ρ : ↥Γ →* MulAut V)
    (hρ : Function.Injective ρ) (e : V ≃* W10)
    (hγ : ∀ γ : ↥Γ, τ⁻¹ * (γ : S24) * τ ∈ mog22plus)
    (he : ∀ (γ : ↥Γ) (v : V),
      e (ρ γ v) = rho10 mog22plus le_rfl ⟨τ⁻¹ * (γ : S24) * τ, hγ γ⟩ (e v))
    {A : Subgroup (MulAut V)} (hAρ : A ≤ ρ.range) (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hF : rkIdx (fixV A) ≤ rk ↥A + 1) :
    ∃ O' : Finset (Fin 24), IsOctad O' ∧ octFix O' ≤ Γ ∧ A = rImg ρ (octFix O') := by
  have hcongr : ∀ γ : ↥Γ, congrHom e (ρ γ) = psi22 ⟨τ⁻¹ * (γ : S24) * τ, hγ γ⟩ := by
    intro γ
    apply MulEquiv.ext
    intro w
    change e ((ρ γ) (e.symm w)) = psi22 ⟨τ⁻¹ * (γ : S24) * τ, hγ γ⟩ w
    rw [he γ (e.symm w), MulEquiv.apply_symm_apply]
  have hAR : A.map (congrHom e) ≤ psi22.range := by
    intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨γ, hγa⟩ := hAρ ha
    rw [← hγa, hcongr γ]
    exact ⟨⟨τ⁻¹ * (γ : S24) * τ, hγ γ⟩, rfl⟩
  obtain ⟨g, l, hind, hl4, hoff, hch⟩ := chain_shape22 e hAR hA2 hA1 hF
  have hcard : Nat.card ↥A = 16 := by
    rw [card_of_chainSub hch (chainAut22_injective e g) hind, hl4]
    norm_num
  have hgM : (g : S24) ∈ M24g := g.2.1
  have hτg : τ * (g : S24)⁻¹ ∈ M24g := M24g.mul_mem hτ (M24g.inv_mem hgM)
  set O' : Finset (Fin 24) := (τ * (g : S24)⁻¹) • offSet22 with hO'def
  have hO' : IsOctad O' := by
    rw [hO'def]
    exact isOctad_smul hτg isOctad_offSet22
  have hfix : ∀ a ∈ A, ∃ γ : ↥Γ, ρ γ = a ∧ ∀ x ∈ O', (γ : S24) x = x := by
    intro a ha
    obtain ⟨γ, hγa⟩ := hAρ ha
    obtain ⟨s, hs, hsa⟩ := (hch a).1 ha
    have hcc : congrHom e (chainAut e psi22 phi22 g s) = psi22 (g⁻¹ * phi22 s * g) := by
      refine MulEquiv.ext fun w => ?_
      have h1 : psi22 g (congrHom e (chainAut e psi22 phi22 g s) w) =
          psi22 ((phi22 s) * g) w := by
        calc psi22 g (congrHom e (chainAut e psi22 phi22 g s) w)
            = congrHom (twistEquiv e psi22 g) (chainAut e psi22 phi22 g s) (psi22 g w) := by
              rw [congrHom_twist_apply, MulEquiv.symm_apply_apply]
          _ = psi22 (phi22 s) (psi22 g w) :=
            congrArg (fun f : MulAut W10 => f (psi22 g w))
              (congrHom_chainAut e psi22 phi22 g s)
          _ = psi22 ((phi22 s) * g) w := by simp only [map_mul, MulAut.mul_apply]
      have h3 : psi22 ((phi22 s) * g) w =
          psi22 g (psi22 (g⁻¹ * phi22 s * g) w) := by
        rw [show (phi22 s) * g = g * (g⁻¹ * phi22 s * g) from by group, map_mul,
          MulAut.mul_apply]
      exact (psi22 g).injective (h1.trans h3)
    have hpsi : (⟨τ⁻¹ * (γ : S24) * τ, hγ γ⟩ : ↥mog22plus) = g⁻¹ * phi22 s * g := by
      apply rho10_mog22plus_injective
      rw [← hcongr γ, hγa, hsa]
      exact hcc
    have hperm : (γ : S24) = τ * (g : S24)⁻¹ * (phi22 s : S24) * (g : S24) * τ⁻¹ := by
      have hval : τ⁻¹ * (γ : S24) * τ = (g : S24)⁻¹ * (phi22 s : S24) * (g : S24) :=
        congrArg (fun x : ↥mog22plus => (x : S24)) hpsi
      calc (γ : S24) = τ * (τ⁻¹ * (γ : S24) * τ) * τ⁻¹ := by group
        _ = τ * ((g : S24)⁻¹ * (phi22 s : S24) * (g : S24)) * τ⁻¹ := by rw [hval]
        _ = τ * (g : S24)⁻¹ * (phi22 s : S24) * (g : S24) * τ⁻¹ := by group
    refine ⟨γ, hγa, ?_⟩
    intro x hx
    rw [hO'def, Finset.mem_smul_finset] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hfixs : (phi22 s : S24) y = y := phi22_fix_subprods hoff s hs y hy
    rw [← hxy, hperm]
    simp only [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, hfixs]
  obtain ⟨hle, hAeq⟩ := eq_rImg_octFix_of_fixing hΓM ρ hρ hcard hO' hfix
  exact ⟨O', hO', hle, hAeq⟩

end CFSG.ASVolI.AppH

