module

public import CFSG.Quasithin.Background.E2TwoLieQuotDisj
public import CFSG.Quasithin.Background.E2TwoCCases
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace E2

theorem isSimpleGroup_of_isE22LieType {k : ℕ} {X : Type} [Group X] (h : IsE22LieType k X) :
    IsSimpleGroup X := by
  rcases h with ⟨-, h | h | h⟩ | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 k h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 k h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 2 k h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 k h).2
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 k h

theorem isSimpleGroup_of_isE22SmallType {X : Type} [Group X] (h : IsE22SmallType X) :
    IsSimpleGroup X := by
  rcases h with ⟨p, -, -, h⟩ | ⟨p, e, -, -, -, -, h⟩ | ⟨p, -, -, h | h⟩ | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p e h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 h).2
  · simp only [IsSp4Prime, ↓reduceIte] at h
    obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G]

theorem ker_eq_solvRad_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) {Y : Type} [Group Y]
    [IsSimpleGroup Y] (f : ↥L →* Y) (hf : Function.Surjective f) :
    f.ker = (solvRad L).subgroupOf L := by
  have hO : ((solvRad L).subgroupOf L).Normal := solvRad_normal L
  rcases normal_eq_top_or_map_le_solvRad hL f.ker with htop | hle
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hf y
    exact hy (f.mem_ker.mp (htop ▸ Subgroup.mem_top x))
  have hkO : f.ker ≤ (solvRad L).subgroupOf L :=
    fun x hx => hle (Subgroup.mem_map_of_mem L.subtype hx)
  have hOf : (((solvRad L).subgroupOf L).map f).Normal := hO.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((solvRad L).subgroupOf L).map f) with hb | ht
  · refine le_antisymm hkO fun x hx => ?_
    rw [MonoidHom.mem_ker]
    have : f x ∈ ((solvRad L).subgroupOf L).map f := Subgroup.mem_map_of_mem f hx
    rwa [hb, Subgroup.mem_bot] at this
  ·
    exfalso
    have htop' : (solvRad L).subgroupOf L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : f x ∈ ((solvRad L).subgroupOf L).map f := ht ▸ Subgroup.mem_top _
      obtain ⟨o, ho, hox⟩ := hx
      have hk : o⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hox, inv_mul_cancel]
      have := Subgroup.mul_mem _ ho (hkO hk)
      rwa [mul_inv_cancel_left] at this
    have hLs : solvRad L = L :=
      le_antisymm (solvRad_le L) (Subgroup.subgroupOf_eq_top.mp htop')
    exact not_isSolvable_of_mem_cComp hL ((solvRad_eq_self_iff L).mp hLs)

theorem nonempty_mulEquiv_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) {Y₁ Y₂ : Type}
    [Group Y₁] [Group Y₂] [IsSimpleGroup Y₁] [IsSimpleGroup Y₂] (f₁ : ↥L →* Y₁)
    (hf₁ : Function.Surjective f₁) (f₂ : ↥L →* Y₂) (hf₂ : Function.Surjective f₂) :
    Nonempty (Y₁ ≃* Y₂) := by
  have h1 := ker_eq_solvRad_of_mem_cComp hL f₁ hf₁
  have h2 := ker_eq_solvRad_of_mem_cComp hL f₂ hf₂
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (h1.trans h2.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂))⟩

omit [Finite G] in
theorem cjSub_mem_cComp {H K : Subgroup G} (hK : K ∈ cComp H) {h : G} (hh : h ∈ H) :
    cjSub h K ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj h) hK
  have h2 : cjSub h H = H := B2F.mem_normalizer_iff_cjSub_eq.mp (Subgroup.le_normalizer hh)
  rw [show H.map (MulAut.conj h).toMonoidHom = cjSub h H from rfl, h2] at h1
  exact h1

theorem exists_eq_cjSub_of_mem_cComp {H T K K' : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hK' : K' ∈ cComp H) : ∃ h ∈ H, K' = cjSub h K := by
  by_contra hne
  push Not at hne
  have hK'H : K' ≤ H := le_of_mem_cComp hK'
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hCN : H ≤ Subgroup.normalizer (solvRad H : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H)
  have hstep : ∀ h ∈ H, ⁅K', cjSub h K⁆ ≤ solvRad H := by
    intro h hh
    have hKh : cjSub h K ∈ cComp H := cjSub_mem_cComp hK hh
    rcases cComp_commutator_dichotomy_of_le hK' (le_of_mem_cComp hKh) with ⟨h1, -⟩ | h2
    · exact h1
    · exfalso
      have hn : K' ≤ Subgroup.normalizer (cjSub h K : Set G) := by
        obtain ⟨hle, hnor⟩ := cComp_normal_span_of_le hKh
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle] at hnor
        exact (le_cCompSpan hK').trans hnor
      have hle : K' ≤ cjSub h K := (le_conjClosure K' (cjSub h K)).trans
        (h2.symm.le.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp hn))
      exact not_subnormal_of_mem_cComp hKh (lt_of_le_of_ne hle (hne h hh))
        (ne_bot_of_mem_cComp hK') (perfect_of_mem_cComp hK') (subnormal_of_mem_cComp hK')
  let S : Subgroup G :=
    { carrier := {g | g ∈ H ∧ ∀ k ∈ K', ⁅k, g⁆ ∈ solvRad H}
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨H.mul_mem haH hbH, fun k hk => ?_⟩
        have e : ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (ha k hk)
          ((Subgroup.mem_normalizer_iff.mp (hCN haH) _).mp (hb k hk))
      one_mem' := ⟨H.one_mem, fun k _ => by
        rw [commutatorElement_one_right]
        exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨H.inv_mem haH, fun k hk => ?_⟩
        have e : ⁅k, a⁻¹⁆ = a⁻¹ * ⁅k, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCN (H.inv_mem haH)) _).mp
          (Subgroup.inv_mem _ (ha k hk)) }
  have hNS : conjClosure K H ≤ S := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨h, hh, z, hz, rfl⟩
    have hx : h * z * h⁻¹ ∈ cjSub h K := ⟨z, hz, by simp [MulAut.conj_apply]⟩
    refine ⟨le_of_mem_cComp (cjSub_mem_cComp hK hh) hx, fun k hk => ?_⟩
    exact hstep h hh (Subgroup.commutator_mem_commutator hk hx)
  have hNH : conjClosure K H ≤ H := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨h, hh, z, hz, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hKH hz)) (H.inv_mem hh)
  have hNn : ((conjClosure K H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hmap : (conjClosure K H).map (MulAut.conj g).toMonoidHom ≤ conjClosure K H := by
      rw [conjClosure, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨x, ⟨h, hh, z, hz, rfl⟩, rfl⟩
      exact ⟨g * h, H.mul_mem hg hh, z, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact hmap ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hHN : H = conjClosure K H ⊔ T :=
    le_antisymm (hHK.le.trans (sup_le_sup_right (le_conjClosure K H) T)) (sup_le hNH hTH)
  have hTs : Group.IsSolvable ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTn : Group.IsNilpotent ↥T := hT.isNilpotent
    infer_instance
  have hK'N : K' ≤ conjClosure K H :=
    (le_perfectCore_of_perfect hK'H (perfect_of_mem_cComp hK')).trans
      (perfectCore_le_of_sup_solvable hNH hNn hHN hTs)
  have hK'C : K' ≤ solvRad H := by
    rw [← perfect_of_mem_cComp hK']
    exact Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => (hNS (hK'N hk₂)).2 k₁ hk₁
  have := solvRad_isSolvable H
  exact not_isSolvable_of_mem_cComp hK' (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hK'C) (Subgroup.inclusion_injective hK'C))

theorem isE22LieType_star_of_lie {H T M K : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hlie : ∃ K' ∈ cComp H, HasE22LieQuot K')
    (hsimp : IsSimpleGroup ↥(star M H K)) : ∃ k : ℕ, 2 ≤ k ∧ IsE22LieType k ↥(star M H K) := by
  obtain ⟨K', hK', X, _, f, hf, k, hk, hX⟩ := hlie
  obtain ⟨h, -, rfl⟩ := exists_eq_cjSub_of_mem_cComp hTH hT hK hHK hK'
  have eK : ↥K ≃* ↥(cjSub h K) :=
    K.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective
  have := isSimpleGroup_of_isE22LieType hX
  obtain ⟨e⟩ := nonempty_mulEquiv_of_mem_cComp hK (f.comp eK.toMonoidHom) (hf.comp eK.surjective)
    (starRestrict M (le_of_mem_cComp hK)) (surjective_starRestrict M (le_of_mem_cComp hK))
  exact ⟨k, hk, isE22LieType_of_mulEquiv e.symm hX⟩

theorem not_isE22SmallType_star_of_lie {H T M K : Subgroup G}
    (hTH : T ≤ H) (hT : IsPGroup 2 T) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hlie : ∃ K' ∈ cComp H, HasE22LieQuot K') : ¬ IsE22SmallType ↥(star M H K) := by
  intro h
  obtain ⟨k, hk, hX⟩ :=
    isE22LieType_star_of_lie hTH hT hK hHK hlie (isSimpleGroup_of_isE22SmallType h)
  exact not_isE22SmallType_of_isE22LieType hk hX h

theorem exists_borel_of_e22CasesC_of_lie {H T X K : Subgroup G}
    (hTH : T ≤ H) (hT : IsPGroup 2 T) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hlie : ∃ K' ∈ cComp H, HasE22LieQuot K') (hcases : E22CasesC H T X K) :
    ∃ n : ℕ, 2 ≤ n ∧ (IsBenderOf n ↥(star X H K) ∨ IsPSL 3 2 n ↥(star X H K) ∨
        IsPSp4 2 n ↥(star X H K)) ∧
      IsBorelIn (star X H K) (star X H (X ⊓ K)) ∧ E1.nParam H ≤ n := by
  have hsmall := not_isE22SmallType_star_of_lie (M := X) hTH hT hK hHK hlie
  dsimp only [E22CasesC] at hcases
  rcases hcases with ⟨-, -, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, htype, hBor, hnH⟩ | ⟨p, hp, hp8, hKs, -, -, -⟩
    · exact ⟨n, hn, Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩, hBor, hnH⟩
    · exact absurd (Or.inl ⟨p, hp, hp8, hKs⟩) hsmall
  · rcases h2 with ⟨n, hBen, hBor, hnH, -⟩ | ⟨n, hn1, htype, -, hBor, hnH, -⟩ |
        ⟨p, e, hp, hp3, he, hpe, hKs, -, -, -⟩ | ⟨p, hp, hp2, hKs, -, -⟩
    · exact ⟨n, hBen.1, Or.inl hBen, hBor, hnH⟩
    · have hn2 : 2 ≤ n := by
        by_contra hlt
        have h1 : n = 1 := by omega
        subst h1
        rcases htype with h | h
        · exact hsmall (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact hsmall (Or.inr (Or.inr (Or.inr (Or.inr h))))
      refine ⟨n, hn2, ?_, hBor, hnH⟩
      rcases htype with h | h
      · exact Or.inr (Or.inl h)
      · right; right
        rw [IsSp4Prime] at h
        split_ifs at h with h1
        · omega
        · exact h
    · exact absurd (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hKs⟩)) hsmall
    · exfalso
      rcases hKs with ⟨-, hU⟩ | ⟨-, hL, -⟩
      · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl hU⟩)))
      · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr hL⟩)))

theorem exists_hasE22LieQuot_of_one_lt_nParam (hE22 : E22StatementC) {H T M : Subgroup G}
    (hmp : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hn : 1 < E1.nParam H) :
    ∃ K ∈ cComp H, HasE22LieQuot K := by
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd hn (not_lt.mpr (E1.solvable_nParam_le_one hs))
  obtain ⟨⟨K, hK, -, -, hc⟩, -⟩ := hE22.exists_cases hmp hsq hns
  obtain ⟨n, hn2, htype, -, -⟩ := exists_borel_of_e22CasesC hn hc
  exact ⟨K, hK, hasE22LieQuot_of_star (le_of_mem_cComp hK) hn2 htype⟩

end E2

end CFSG.Quasithin
