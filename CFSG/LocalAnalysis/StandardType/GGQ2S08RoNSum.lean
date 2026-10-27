module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CorePermsAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_roN_of_sum
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (hn : 6 ≤ n) (h3 : ¬ 3 ∣ n + 1)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (f : Fin (n + 1) → M.V)
    (hFrame : GGQ2S08ROFrame M f)
    (hperm : ∀ σ : Equiv.Perm (Fin (n + 1)), ∃ φ ∈ ggAutomizer
      (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs,
        ∀ i, ggLin (p := 3) M.model φ (f i) = f (σ i))
    {a b : Fin (n + 1)} (hab : a ≠ b)
    (hs : ∃ φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs,
      ggLin (p := 3) M.model φ (f a) = -f b ∧ ggLin (p := 3) M.model φ (f b) = -f a ∧
        ∀ k, k ≠ a → k ≠ b → ggLin (p := 3) M.model φ (f k) = f k)
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs)
    (hmono : GGQ2S08Mono f (ggLin (p := 3) M.model ψ)) :
    ψ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
  classical
  set AM := ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs with hAM
  set H : Subgroup (M.V ≃ₗ[ZMod 3] M.V) := AM.map (ggLin (p := 3) M.model) with hH
  set bf := ggQ2s08r4_basis M f hFrame with hbf
  have hbfa : ∀ i, bf i = f i := ggQ2s08r4_basis_apply M f hFrame
  have hpermH : ∀ σ, ggQ2s08k4_permM bf σ ∈ H := by
    intro σ
    obtain ⟨φ, hφ, hφf⟩ := hperm σ
    refine ⟨φ, hφ, ggQ2s08k4_eq_of_basis bf fun i => ?_⟩
    rw [ggQ2s08k4_permM_apply, hbfa, hbfa]
    exact hφf i
  obtain ⟨φs, hφs, hsa, hsb, hsk⟩ := hs
  have hpairab : ggQ2s08k4_pairDiag bf a b ∈ H := by
    have hmem : ggLin (p := 3) M.model φs * ggQ2s08k4_permM bf (Equiv.swap a b) ∈ H :=
      H.mul_mem ⟨φs, hφs, rfl⟩ (hpermH _)
    convert hmem using 1
    refine ggQ2s08k4_eq_of_basis bf fun k => ?_
    rw [ggQ2s08k4_pairDiag_apply, LinearEquiv.mul_apply, ggQ2s08k4_permM_apply, hbfa, hbfa]
    by_cases hka : k = a
    · rw [hka, if_pos rfl, Equiv.swap_apply_left, hsb]
      exact neg_one_smul _ _
    · by_cases hkb : k = b
      · rw [hkb, if_neg (Ne.symm hab), if_pos rfl, Equiv.swap_apply_right, hsa]
        exact neg_one_smul _ _
      · rw [if_neg hka, if_neg hkb, one_smul, Equiv.swap_apply_of_ne_of_ne hka hkb,
          hsk k hka hkb]
  have hpair : ∀ j, j ≠ a → ggQ2s08k4_pairDiag bf a j ∈ H := by
    intro j hja
    by_cases hjb : j = b
    · rw [hjb]; exact hpairab
    · have hmem : ggQ2s08k4_permM bf (Equiv.swap b j) * ggQ2s08k4_pairDiag bf a b *
          (ggQ2s08k4_permM bf (Equiv.swap b j))⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hpermH _) hpairab) (H.inv_mem (hpermH _))
      convert hmem using 1
      refine ggQ2s08k4_eq_of_basis bf fun k => ?_
      have hinv : (ggQ2s08k4_permM bf (Equiv.swap b j))⁻¹ (bf k) = bf (Equiv.swap b j k) := by
        rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, ggQ2s08k4_permM_apply,
          Equiv.swap_apply_self]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, ggQ2s08k4_pairDiag_apply,
        ggQ2s08k4_pairDiag_apply, map_smul, ggQ2s08k4_permM_apply, Equiv.swap_apply_self]
      have hab' : a ≠ j := fun h => hja h.symm
      congr 1
      by_cases hka : k = a
      · rw [hka, Equiv.swap_apply_of_ne_of_ne hab hab']
        simp
      · by_cases hkj : k = j
        · rw [hkj, Equiv.swap_apply_right]
          simp [hja, Ne.symm hab]
        · by_cases hkb : k = b
          · rw [hkb, Equiv.swap_apply_left]
            simp [Ne.symm hab, hja, hjb, Ne.symm hjb]
          · rw [Equiv.swap_apply_of_ne_of_ne hkb hkj]
            simp [hka, hkj, hkb]
  have hD : ∀ g : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧ ggLin (p := 3) M.model φ = g := by
    intro g hg
    have hg' : GGQ2S08MonoEven bf g := by
      obtain ⟨σ, ε, hε, hprod, hgε⟩ := hg
      exact ⟨σ, ε, hε, hprod, fun i => by rw [hbfa, hbfa]; exact hgε i⟩
    obtain ⟨φ, hφ, hφg⟩ := ggQ2s08k4_monoEven_mem bf H hpermH a hpair g hg'
    obtain ⟨k, hkN0, hkN, hk⟩ := mem_ggAutomizer_iff.mp hφ
    exact ⟨k, φ, ⟨hkN, hk⟩, hkN0, hφg⟩
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgG0 := ggQ2s08_roN hLB hP hRig hS hCav M hn h3 hMark hLab hWeyl f hFrame hD g ψ
    ⟨hgN, hg⟩ hmono
  exact mem_ggAutomizer_iff.mpr ⟨g, hgG0, hgN, hg⟩

end CFSG.StandardType

end
