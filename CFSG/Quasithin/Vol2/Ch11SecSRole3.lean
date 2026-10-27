module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4
public import CFSG.Quasithin.Vol2.Ch11SecSRole
public import CFSG.Quasithin.Vol2.Ch11SecSSym2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem isL24Sub_lOf (hN : NatFacts) (h1102 : Stmt11_0_2) {T J I' U : Subgroup G} {i : ℕ}
    (hJ : Hyp11 G T J I' 2) (hi : i = 1 ∨ i = 2) (hU : IsVi T J I' 2 i U) :
    IsL24Sub (modO2Image J (T ⊓ J)) (modO2Image J (LOf J U)) := by
  have hLJ : LOf J U ≤ J := (perfectCore_le _).trans inf_le_left
  have hp : ⁅LOf J U, LOf J U⁆ = LOf J U := perfectCore_perfect _
  have hne : LOf J U ≠ ⊥ := ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 hJ hU hi le_rfl)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 hJ hi hU
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hLJ
  exact ⟨modO2Image_ne_bot hLJ hp hne, modO2Image_perfect hLJ hp,
    modO2Image_le_normalizer (inf_le_left.trans (T_le_normalizer_lOf hJ.normal hU.2)),
    F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩

theorem natPoint_J (hNP : NatPointFacts) (h1102 : Stmt11_0_2) {T J I' U₁ X : Subgroup G}
    (hJ : Hyp11 G T J I' 2) (hU₁ : IsVi T J I' 2 1 U₁) (hcart : IsCartanX T J X)
    (hCV : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥) :
    (∀ w : ↥(fsuV T I'), w ≠ 1 → (∀ p ∈ autOn (T ⊓ J) (fsuV T I'), p w = w) →
      w ∈ U₁.subgroupOf (fsuV T I') ∧
        ∀ g ∈ autOn J (fsuV T I'), g w = w → g ∈ stabW (U₁.subgroupOf (fsuV T I'))) ∧
      ∃ d ∈ autOn X (fsuV T I'), ∀ u ∈ U₁.subgroupOf (fsuV T I'), u ≠ 1 → d u ≠ u := by
  have hZ0 : (Subgroup.centralizer (J : Set G)).subgroupOf (fsuV T I') = ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    have : (w : G) ∈ fsuV T I' ⊓ Subgroup.centralizer (J : Set G) := ⟨w.2, hw⟩
    rw [hCV, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hsq : ∀ w : ↥(fsuV T I'), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV hJ).2 w w.2)
  have hP := isSylowTwoOf_P hJ
  have hU₁f := isFlagW_of_isVi hJ hU₁
  rw [hZ0] at hU₁f
  have hD := isHall_autOn_cartan h1102 hJ hcart
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T J I' 2 hJ
  rcases hk with ⟨K', _, _, hK, -, π, hπ, -⟩ | ⟨K', _, _, hK, -, π, hπ, -⟩ | ⟨K', _, _, hK, -, hnat⟩
  · rw [hZ0] at hπ
    exact hNP.sl3 K' 2 le_rfl hK _ hsq _ π hπ _ hP _ hU₁f _ hD
  · rw [hZ0] at hπ
    exact hNP.sp4 K' 2 le_rfl hK _ hsq _ π hπ _ hP _ hU₁f _ hD
  · obtain ⟨K'', _, _, hK'', π, hπ⟩ := hnat
    rw [hZ0] at hπ
    exact hNP.g2 K'' 2 le_rfl hK'' _ hsq _ π hπ _ hP _ hU₁f _ hD

omit [Finite G] in
theorem fixed_of_omegaOneCenter {T J V : Subgroup G} {z : G} (hzV : z ∈ V)
    (hz : z ∈ quasithinOmegaOneCenter T) :
    ∀ p ∈ autOn (T ⊓ J) V, p ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
  rintro _ ⟨⟨t, ht⟩, htTJ, rfl⟩
  apply Subtype.ext
  change ((conjV V t ht ⟨z, hzV⟩ : ↥V) : G) = z
  rw [conjV_apply_coe]
  have hzC : z ∈ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr (fun y hy => hy.1.2) hz
  have htz := Subgroup.mem_centralizer_iff.mp hzC t (Subgroup.mem_inf.mp htTJ).1
  rw [htz, mul_assoc, mul_inv_cancel, mul_one]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem k0Of_le_lOf_J (hNP : NatPointFacts) (h1102 : Stmt11_0_2)
    {J I' U₁ : Subgroup G} (hJ : Hyp11 G T J I' 2)
    (hU₁ : IsVi T J I' 2 1 U₁) (hcart : IsCartanX T J X)
    (hCV : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥) (hK₀J : k0Of K P₂ ≤ J)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥) : k0Of K P₂ ≤ LOf J U₁ := by
  obtain ⟨ha, -⟩ := natPoint_J hNP h1102 hJ hU₁ hcart hCV
  obtain ⟨z, hz, hz1⟩ := exists_omegaOneCenter_fsuV hJ
  have hZC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK
  obtain ⟨-, hstab⟩ := ha ⟨z, hz.1⟩ (fun h1 => hz1 (congrArg Subtype.val h1))
    (fixed_of_omegaOneCenter hz.1 hz.2)
  have hK₀N : k0Of K P₂ ≤ Subgroup.normalizer (U₁ : Set G) := by
    intro k hk
    have hkV : k ∈ Subgroup.normalizer (fsuV T I' : Set G) := L_le_normalizer_fsuV hJ (hK₀J hk)
    have hfix : conjV (fsuV T I') k hkV ⟨z, hz.1⟩ = ⟨z, hz.1⟩ := by
      apply Subtype.ext
      rw [conjV_apply_coe]
      have hkz := Subgroup.mem_centralizer_iff.mp (hZC hz.2) k ((k0Of_le K P₂) hk)
      change k * z * k⁻¹ = z
      rw [hkz, mul_assoc, mul_inv_cancel, mul_one]
    exact (conjV_mem_stabW_iff (IsVi.le_fsuV hU₁) hkV).mp
      (hstab _ (conjV_mem_autOn (hK₀J hk) hkV) hfix)
  calc k0Of K P₂ = perfectCore (k0Of K P₂) :=
        (perfectCore_eq_self_of_perfect (k0Of_perfect K P₂)).symm
    _ ≤ perfectCore (J ⊓ Subgroup.normalizer (U₁ : Set G)) := perfectCore_mono (le_inf hK₀J hK₀N)

theorem lOf_one_eq_J (hPT : FactParabTwo) (hNP : NatPointFacts) (hLevi : FactL34Levi)
    (hT : FactPGL34Torus) (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) {J I' U₁ : Subgroup G}
    (hJ : Hyp11 G T J I' 2) (hU₁ : IsVi T J I' 2 1 U₁) (hcart : IsCartanX T J X)
    (hCV : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥) (hK₀J : k0Of K P₂ ≤ J)
    (hL₂J : LOf L V₂ ≤ J) (hXJ : X ≤ J) (hZK : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥) :
    LOf J U₁ = k0Of K P₂ := by
  have hle := k0Of_le_lOf_J hNP h1102 hJ hU₁ hcart hCV hK₀J hZK
  have hD := h.inspData_k0Of hLevi hT hN h1102 cL hP hJ.normal hK₀J hL₂J hXJ
  have hS₁ := isL24Sub_lOf hN h1102 hJ (Or.inl rfl) hU₁
  obtain ⟨h1, -⟩ := hPT _ hJ.shape _ hD.syl _ _ _ ⟨hD.ne₁, hD.p₁, hD.n₁, hD.sl₁⟩ hS₁ hS₁
  have hbar := h1 (Subgroup.map_mono fun x hx => hle hx)
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hJ.normal)
  have hOT : pCoreOf 2 J ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSI).trans inf_le_left
  exact (eq_of_modO2Image_eq_of_perfect hK₀J ((perfectCore_le _).trans inf_le_left)
    (k0Of_perfect K P₂) (perfectCore_perfect _) (hOT.trans (h.T_le_normalizer_k0Of hP))
    (hOT.trans (T_le_normalizer_lOf hJ.normal hU₁.2)) hbar).symm

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
