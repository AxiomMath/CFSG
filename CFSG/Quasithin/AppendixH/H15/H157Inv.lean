module

public import CFSG.Quasithin.AppendixH.H15.H157Core
public import CFSG.Quasithin.AppendixH.H15.H157Frat
public import CFSG.Quasithin.Background.H153Std

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code

theorem mem_fixV_img11_iff {Γ : Subgroup S24} {w : W11} :
    w ∈ fixV (img11 Γ) ↔ ∀ γ : ↥AutPerm, (γ : S24) ∈ Γ → rhoM24 γ w = w := by
  constructor
  · intro h γ hγ
    exact h (rhoM24 γ) (Subgroup.mem_map.2 ⟨γ, Subgroup.mem_subgroupOf.2 hγ, rfl⟩)
  · intro h x hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    exact h γ (Subgroup.mem_subgroupOf.1 hγ)


theorem eq_one_or_eY_of_inv {u : G6.PermMod 24} (hu : u ∈ evenSupp tFix)
    (hinv : ∀ n ∈ Nt, G6.permAct 24 n u = u) : u = 1 ∨ u = eY tFix := by
  obtain ⟨π, hsurj, -, hfix⟩ := exists_pi_Nt
  have hrel : ∀ n : ↥Nt, ∀ j : Fin 6,
      Multiplicative.toAdd u (fixPt ((π n)⁻¹ j)) = Multiplicative.toAdd u (fixPt j) := by
    intro n j
    have hfix' : (n : S24)⁻¹ (fixPt j) = fixPt ((π n)⁻¹ j) := by
      have h := hfix n⁻¹ j
      rwa [Subgroup.coe_inv, map_inv] at h
    have heq : Multiplicative.toAdd u ((n : S24)⁻¹ (fixPt j)) =
        Multiplicative.toAdd u (fixPt j) := by
      have h := congrArg (fun v : G6.PermMod 24 => Multiplicative.toAdd v (fixPt j))
        (hinv (n : S24) n.2)
      rwa [G6.permAct_apply] at h
    rw [← hfix', heq]
  have hconst : ∀ σ : Equiv.Perm (Fin 6), ∀ j : Fin 6,
      Multiplicative.toAdd u (fixPt (σ j)) = Multiplicative.toAdd u (fixPt j) := by
    intro σ j
    obtain ⟨n, rfl⟩ := hsurj σ
    have h := hrel n ((π n) j)
    have h2 : (π n)⁻¹ ((π n) j) = j := Equiv.symm_apply_apply (π n) j
    rw [h2] at h
    exact h.symm
  have hpair : ∀ i j : Fin 6,
      Multiplicative.toAdd u (fixPt i) = Multiplicative.toAdd u (fixPt j) := by
    intro i j
    have h := hconst (Equiv.swap i j) i
    rw [Equiv.swap_apply_left] at h
    exact h.symm
  have hsupp : ∀ i : Fin 24, i ∉ tFix → Multiplicative.toAdd u i = 0 := by
    intro i hi
    by_contra hne
    exact hi ((mem_evenSupp.1 hu).2 i hne)
  rcases h13_zmod2_cases (Multiplicative.toAdd u (fixPt (0 : Fin 6))) with h0 | h0
  · left
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_one]
    by_cases hi : i ∈ tFix
    · rw [eq_fixPt_colOf hi]
      exact (hpair (colOf i) 0).trans h0
    · exact hsupp i hi
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_eY]
    by_cases hi : i ∈ tFix
    · rw [if_pos hi, eq_fixPt_colOf hi]
      exact (hpair (colOf i) 0).trans h0
    · rw [if_neg hi]
      exact hsupp i hi

theorem fixV_img11_Nt : fixV (img11 Nt) = Subgroup.zpowers z0 := by
  have hfix_eY : ∀ n : S24, n ∈ Nt → G6.permAct 24 n (eY tFix) = eY tFix := by
    intro n hn
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply, toAdd_eY, toAdd_eY]
    have hiff : n⁻¹ i ∈ tFix ↔ i ∈ tFix := mem_tFix_iff_of_mem_Nt (Nt.inv_mem hn) i
    by_cases hi : i ∈ tFix
    · rw [if_pos (hiff.2 hi), if_pos hi]
    · rw [if_neg (fun h => hi (hiff.1 h)), if_neg hi]
  refine le_antisymm ?_ (Subgroup.zpowers_le.2 ?_)
  · intro w hw
    have hwt : w ∈ fixW tA := by
      rw [mem_fixW]
      exact mem_fixV_img11_iff.1 hw tA (zpowers_tP_le_Nt (Subgroup.mem_zpowers tP))
    obtain ⟨u, hu, hκu⟩ := (mem_fixW_tA_iff w).1 hwt
    have hinv : ∀ n ∈ Nt, G6.permAct 24 n u = u := by
      intro n hn
      have hnA : n ∈ AutPerm := Nt_le_M24g hn
      have hw' : rhoM24 ⟨n, hnA⟩ w = w := mem_fixV_img11_iff.1 hw ⟨n, hnA⟩ hn
      have hperm : G6.permAct 24 n u ∈ evenSupp tFix := by
        rw [mem_evenSupp]
        refine ⟨G6.permAct_mem_coreMod n hu.1, ?_⟩
        intro i hi
        exact (mem_tFix_iff_of_mem_Nt (Nt.inv_mem hn) i).1
          (hu.2 (n⁻¹ i) (by rwa [G6.permAct_apply] at hi))
      have hκeq : cocodeCoords.κ u = cocodeCoords.κ (G6.permAct 24 n u) := by
        rw [SecCoords.κ_permAct_rho cocodeCoords AutPerm (fun _ hσ => preserves_cocode hσ)
          ⟨n, hnA⟩ (mem_evenSupp.1 hu).1, hκu]
        exact hw'.symm
      exact (kappa_injOn_evenSupp (by rw [card_tFix]; norm_num) hu hperm hκeq).symm
    rcases eq_one_or_eY_of_inv hu hinv with h1 | h1
    · rw [← hκu, h1, map_one]
      exact Subgroup.one_mem _
    · rw [← hκu, h1, kappa_eY_tFix.2]
      exact Subgroup.mem_zpowers _
  · refine mem_fixV_img11_iff.2 ?_
    intro γ hγ
    calc rhoM24 γ z0 = rhoM24 γ (cocodeCoords.κ (eY tFix)) := by rw [kappa_eY_tFix.2]
      _ = cocodeCoords.κ (G6.permAct 24 (γ : S24) (eY tFix)) :=
          (SecCoords.κ_permAct_rho cocodeCoords AutPerm (fun _ hσ => preserves_cocode hσ) γ
            (mem_evenSupp.1 kappa_eY_tFix.1).1).symm
      _ = cocodeCoords.κ (eY tFix) := by rw [hfix_eY (γ : S24) hγ]
      _ = z0 := kappa_eY_tFix.2

theorem fixV_img11_KSp_eq_Nt : fixV (img11 KSp) = fixV (img11 Nt) := by
  rw [fixV_KS, fixV_img11_Nt]

end CFSG.ASVolI.AppH.H157
