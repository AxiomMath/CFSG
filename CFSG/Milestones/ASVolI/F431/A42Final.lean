module

public import CFSG.Milestones.ASVolI.F431.A42G2
public import CFSG.Milestones.ASVolI.F431.A42D4
public import CFSG.Milestones.ASVolI.F431.A42F4
public import CFSG.Milestones.ASVolI.F431.A42U5
public import CFSG.Milestones.ASVolI.F431.NonU2
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.Asm2
public import CFSG.Milestones.ASVolI.F431.L35

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F4Core

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

theorem burnsideF4m_A42_F4_oPPrime_le {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    oPPrime 2 (Pg K a ⟨1, by decide⟩) ≤ perfectCore (Pg K a ⟨1, by decide⟩) := by
  haveI : Finite (Gm K a) := finite_gm K a
  have hUle : Ug K a ≤ perfectCore (Pg K a ⟨1, by decide⟩) := fun u hu =>
    (CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma _) u).2
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeFixedPosUnipotent_le_perfectCore_one ha hK
        (Subgroup.mem_subgroupOf.1 hu))
  have YS : CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Gm K a) (Ug K a) (Pg K a ⟨0, by decide⟩)
      (Pg K a ⟨1, by decide⟩) := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyP, k, hk⟩
  have hy : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  exact CFSG.Quasithin.H13.U4Par.le_of_isPGroup_of_sylow_le (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)) hUle YS.sylow
    (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hy)
    ((Subgroup.zpowers_le (H := Pg K a ⟨1, by decide⟩)).mpr hyP) (Subgroup.mem_zpowers y)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_A42_core_F4 [Finite E] (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : 3 ≤ f)
    (hodd : Odd Gp.index) : burnsideF4m_Core1 Gp M₁ := by
  haveI := hyp.normal
  obtain ⟨chart, hm⟩ := hyp.lie_amalgam
  obtain ⟨K, fK, finK, charK, a, ha, hKsc, marking, h2, -, -, -⟩ :=
    burnsideF4gF4Inv_chart_data hf chart
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hKsc
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hK
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Inv_exists_iso ha hK marking
  have hGM1 : Gp ⊓ M₁ = (Pg K a ⟨1, by decide⟩).map (Gp.subtype.comp Φ.toMonoidHom) := by
    rw [hm.2.1, h2, hΦ _ _ (burnsideF4gF4Inv_mem_P₁_iff hK), burnsideF4gF4Inv_Pg_one_eq hK,
      Subgroup.map_map]
  have hinj : Function.Injective (Gp.subtype.comp Φ.toMonoidHom) :=
    Gp.subtype_injective.comp Φ.injective
  have hO : oPPrime 2 (Gp ⊓ M₁) ≤ perfectCore M₁ := by
    have h3 : oPPrime 2 (Gp ⊓ M₁) ≤ perfectCore (Gp ⊓ M₁) := by
      rw [hGM1, burnsideF4gD4Inv_map_oPPrime _ hinj, burnsideF4m_perfectCore_map _ hinj]
      exact Subgroup.map_mono (burnsideF4m_A42_F4_oPPrime_le ha hK)
    exact h3.trans (perfectCore_mono inf_le_right)
  intro x hx _ hx2
  have hx2' : x ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hx2
  have hxG : x ∈ Gp := burnsideF4m_core_mem_of_odd Gp hodd hx2'
  have hxM : x ∈ M₁ := perfectCore_le M₁ hx.1
  refine ⟨burnsideF4gU4Inv_mem_oPPrime ⟨hxG, hxM⟩ hx2',
    Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hx.2 g (hO hg)

end F4Core

@[expose] def burnsideF4m_A42Rest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ κ = .Tits ∨
      (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f ≠ 2)) →
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε

@[expose] def burnsideF4m_A35Rest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ κ = .Tits ∨
      (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f ≠ 2)) →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

section Final

set_option linter.unusedSectionVars false

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A42_kinds (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index)
    (hk : (κ = .G2 ∧ 2 ≤ f) ∨ (κ = .D4tw ∧ 2 ≤ f) ∨ (κ = .F4tw ∧ 3 ≤ f) ∨ (κ = .U4 ∧ 2 ≤ f) ∨
      (κ = .U5 ∧ f = 2)) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε) ∧
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  haveI := hyp.amalgam.finite
  rcases hk with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
  · exact burnsideF4m_A42_G2 hyp hf hodd (burnsideF4m_core12_G2 hyp.amalgam hf).1
  · exact burnsideF4m_A42_D4 hyp hf hodd (burnsideF4m_core12_D4 hyp.amalgam hf).1
  · exact burnsideF4m_A42_F4 hyp hf hodd (burnsideF4m_A42_core_F4 hyp.amalgam hf hodd)
  · exact burnsideF4m_A42_U4 hyp hf hodd (burnsideF4m_core12_U4 hyp.amalgam hf).1
  · exact burnsideF4m_A42_U5 hyp hodd (burnsideF4m_core12_U5 hyp.amalgam le_rfl).1

theorem burnsideF4m_F_4_42_odd_of_rest (hrest : burnsideF4m_A42Rest)
    (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL43 : ¬ IsL43 M) (hL3 : κ ≠ .L3)
    (hodd : Odd Gp.index) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  cases κ with
  | L3 => exact absurd rfl hL3
  | Sp4 => exact burnsideF4jb_F_4_42_Sp4 hyp
  | G2d => exact absurd rfl hyp.not_G2d
  | Tits =>
    exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | U5 =>
    by_cases hf : f = 2
    · exact (burnsideF4m_A42_kinds hyp hodd
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf⟩))))).1
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf⟩)))))
  | G2 =>
    by_cases hf : 2 ≤ f
    · exact (burnsideF4m_A42_kinds hyp hodd (Or.inl ⟨rfl, hf⟩)).1
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inl ⟨rfl, by omega⟩)
  | D4tw =>
    by_cases hf : 2 ≤ f
    · exact (burnsideF4m_A42_kinds hyp hodd (Or.inr (Or.inl ⟨rfl, hf⟩))).1
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inl ⟨rfl, by omega⟩))
  | F4tw =>
    by_cases hf : 3 ≤ f
    · exact (burnsideF4m_A42_kinds hyp hodd (Or.inr (Or.inr (Or.inl ⟨rfl, hf⟩)))).1
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd
        (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  | U4 =>
    by_cases hf : 2 ≤ f
    · exact (burnsideF4m_A42_kinds hyp hodd (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hf⟩))))).1
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))))

theorem burnsideF4m_F_4_42_of_rest (h38 : F_4_38) (hrest : burnsideF4m_A42Rest) : F_4_42 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hL3
  haveI := hyp.finite_M
  obtain ⟨T₀, hT₀⟩ := burnsideF4ja_exists_isSylowOf (MiOne β ε ⊓ MiTwo β ε)
  exact burnsideF4m_F_4_42_odd_of_rest hrest hyp hL43 hL3
    (h38 κ f E Gp M₁ M₂ Y β M ε z hyp hL43 T₀ hT₀).2.2

theorem burnsideF4m_F435Rest_of (hrest : burnsideF4m_A35Rest) : burnsideF4m_F435Rest := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL3 hSp i j hi hj hi1 hj1 hi2 hj2
  have key : ((κ = .G2 ∧ 2 ≤ f) ∨ (κ = .D4tw ∧ 2 ≤ f) ∨ (κ = .F4tw ∧ 3 ≤ f) ∨
      (κ = .U4 ∧ 2 ≤ f) ∨ (κ = .U5 ∧ f = 2)) →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
    intro hk
    have hU : ¬ ((κ = .U4 ∨ κ = .U5) ∧ f = 1) := by
      rintro ⟨hκ, hf1⟩
      rcases hk with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ <;> omega
    obtain ⟨-, K', _, _, θ, N1, N2, h1, h2, T, I, z₀', L, hnf⟩ :=
      burnsideF4m_A42_kinds hyp (burnsideF4m_odd_index_nonU2 hyp hU) hk
    exact burnsideF4m_F_4_35_of_lieK hyp hL3 hSp θ h1 h2 L hnf i j hi hj hi1 hi2 hj1 hj2
  cases κ with
  | L3 => exact absurd rfl hL3
  | Sp4 => exact absurd rfl hSp
  | G2d => exact absurd rfl hyp.not_G2d
  | Tits =>
    exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) i j hi hj
      hi1 hj1 hi2 hj2
  | U5 =>
    by_cases hf : f = 2
    · exact key (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf⟩))))
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf⟩)))))
        i j hi hj hi1 hj1 hi2 hj2
  | G2 =>
    by_cases hf : 2 ≤ f
    · exact key (Or.inl ⟨rfl, hf⟩)
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inl ⟨rfl, by omega⟩) i j hi hj hi1 hj1 hi2 hj2
  | D4tw =>
    by_cases hf : 2 ≤ f
    · exact key (Or.inr (Or.inl ⟨rfl, hf⟩))
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inl ⟨rfl, by omega⟩)) i j hi hj hi1 hj1
        hi2 hj2
  | F4tw =>
    by_cases hf : 3 ≤ f
    · exact key (Or.inr (Or.inr (Or.inl ⟨rfl, hf⟩)))
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))) i j hi
        hj hi1 hj1 hi2 hj2
  | U4 =>
    by_cases hf : 2 ≤ f
    · exact key (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hf⟩))))
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))) i j hi hj hi1 hj1 hi2 hj2

end Final

end CFSG.ASVolI
