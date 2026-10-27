module

public import CFSG.Quasithin.Background.SimsE214TwoSix
public import CFSG.Quasithin.Background.SimsE214TwoSp4
public import CFSG.Quasithin.Background.SimsE213M

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

open E214T in
theorem e214_two
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (_k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (hJI : JI = kerIn MI I) (hB : B = V ⊓ pCoreOf 2 I) (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I)
    (hP : P = A ⊔ B) (hZ' : Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (_k : ℕ∞)) :
    (P = JI ∧ E2.star MI I V = centerOf (E2.star MI I TI)) ∨
      (∃ (_ : (P.subgroupOf I).Normal), CFSG.IsQuasisimple (↥I ⧸ P.subgroupOf I) ∧
        IsSz 3 (E2.StarQuot MI I) ∧
        (∀ x : Γ, x ∈ JI ↔ x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ P) ∧
        V ⊔ P = ⁅Subgroup.closure {t : Γ | t ∈ TI ∧ t ^ 2 ∈ P}, MI⁆ ⊔ P ∧
        E2.IsBorelIn ⊤ (E2.star MI I MI) ∧ E2.star MI I V = centerOf (E2.star MI I TI)) ∨
      (∃ (_ : (P.subgroupOf I).Normal),
        Nonempty (↥I ⧸ P.subgroupOf I ≃* Equiv.Perm (Fin 6) × Multiplicative (ZMod 2)) ∧
        ∀ x : Γ, x ∈ JI ↔ x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ P) := by
  subst hMI hTI' hJI hB hA hP hZ'
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  obtain ⟨hp, hVZ, -, -, -, -, -, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  have hZ'' : V ⊓ B6.conjSub g⁻¹ V ≠ ⊥ := e ▸ hZ
  have hPeq : conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I = E2.Pair.PP (M ⊓ I) V I g⁻¹ := by
    show _ = (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V)
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm, e]
  have h1 : M ⊓ I = I ⊓ Subgroup.normalizer (V : Set Γ) :=
    E2.inf_eq_inf_normalizer_of_central hTI (hp.normalizer_le.trans inf_le_left) hZ''
      inf_le_left fun z hz x hx => hp.mem_center hz hx
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  rw [hPeq]
  obtain ⟨-, -, hsyl, -, k', -, hcase⟩ := hI
  rcases hcase with ⟨hk1, hY, hBor⟩ | ⟨-, p, a, hp', hp2, -, ⟨d⟩⟩ |
      ⟨-, -, hY, hBor, -, hroot⟩
  ·
    obtain ⟨hVeq, hcase⟩ := two_of_psl_sz E2.kgSz8CoverInvolutions_holds E2.kgI22One_holds hp
      hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBor (by omega : 2 ≤ k') hY
    rcases hcase with hPJ | hii
    · exact Or.inl ⟨hPJ, hVeq⟩
    · exact Or.inr (Or.inl hii)
  ·
    obtain ⟨hPJ, hV⟩ := E2.star_eq_center_of_dihedral hp hsyl hVZ (hp'.odd_of_ne_two hp2).pow d
    exact Or.inl ⟨hPJ, hV⟩
  ·
    rcases hY with hY | ⟨rfl, ⟨e6⟩⟩
    · exact Or.inl (two_of_sp4 hp hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBor hroot hY)
    · rcases two_of_six E2.kgI22One_holds hp hsyl (I.inv_mem hg) hgen hVZ e6 with hi | hiii
      · exact Or.inl hi
      · exact Or.inr (Or.inr hiii)

end CFSG.Quasithin.SimsE2
