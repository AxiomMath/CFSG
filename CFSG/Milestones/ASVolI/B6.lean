module

public import CFSG.Milestones.ASVolI.B2
public import CFSG.Quasithin.Background.B610

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

@[expose] def B68ThreeStruct (X : Type) [Group X] (T M : Subgroup X) : Prop :=
  ∃ L : Subgroup (X ⧸ kerIn M ⊤), IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
    L ≤ (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
    (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) =
      ⨆ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), B6.conjSub t L ∧
    sSupIndep {S : Subgroup (X ⧸ kerIn M ⊤) |
      ∃ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), S = B6.conjSub t L} ∧
    (∀ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)),
      ((B6.conjSub t L).subgroupOf
        ((twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)))).Normal) ∧
    autOn ⊤ L ∈ uFamHat (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L) ∧
    IsUniqueMaxOver (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L)
      (autOn (M.map (QuotientGroup.mk' (kerIn M ⊤))) L)

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

section DirectSumMod

variable {M : Type*} [Group M]

@[expose] def IsIntDirSumMod {ι : Type*} (X C : Subgroup M) (Us : ι → Subgroup M) : Prop :=
  C ⊔ (⨆ i, Us i) = C ⊔ X ∧
    ∀ i, (C ⊔ Us i) ⊓ (C ⊔ (⨆ (j : ι) (_ : j ≠ i), Us j)) = C

end DirectSumMod

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X : Subgroup G), X < H → (⨆ U ∈ uFam H X, U) = H

section BurnsideB6a

private theorem burnsideB6a_conjClosure_eq_iSup {G : Type} [Group G] (X H : Subgroup G) :
    CFSG.Quasithin.conjClosure X H = ⨆ h ∈ H, X.map (MulAut.conj h).toMonoidHom := by
  apply le_antisymm
  · apply CFSG.Quasithin.conjClosure_le
    intro h hh z hz
    have hle : X.map (MulAut.conj h).toMonoidHom ≤
        ⨆ g ∈ H, X.map (MulAut.conj g).toMonoidHom :=
      le_iSup₂_of_le (f := fun g _ => X.map (MulAut.conj g).toMonoidHom) h hh le_rfl
    exact hle (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
  · refine iSup₂_le fun g hg => ?_
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact CFSG.Quasithin.mem_conjClosure hg hz

private theorem burnsideB6a_Jj_zero {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  unfold CFSG.ASVolI.ChB.Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

private theorem burnsideB6a_baumOf_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.baumOf H = CFSG.Quasithin.baum H := by
  unfold CFSG.ASVolI.ChB.baumOf CFSG.Quasithin.baum
  rw [burnsideB6a_Jj_zero]

private theorem burnsideB6a_isTwoReduced_top {X : Type} [Group X] {V : Subgroup X}
    (hV : V ∈ CFSG.Quasithin.primeReducedFamily X 2) :
    CFSG.Quasithin.IsTwoReducedIn ⊤ V := by
  obtain ⟨hVn, hVe, hD⟩ := (CFSG.Quasithin.isPrimeReduced_iff_forall 2).mp hV
  refine ⟨le_top, (Subgroup.normalizer_eq_top_iff.mpr hVn).ge,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hVe, ?_⟩
  intro D _ hDn hD2
  exact hD D (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDn)) hD2

private theorem burnsideB6a_pCore_quotient_eq_bot {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (h : CFSG.Quasithin.MinParabolic (⊤ : Subgroup X) T M)
    {C : Subgroup X} [C.Normal] (hQC : CFSG.Open.pCore 2 X ≤ C) (hCM : C ≤ M) :
    CFSG.Open.pCore 2 (X ⧸ C) = ⊥ := by
  have hPn : (CFSG.Open.pCore 2 (X ⧸ C)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hPp : IsPGroup 2 (CFSG.Open.pCore 2 (X ⧸ C)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ C) 2
  have hD2 : ∀ d ∈ (CFSG.Open.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C),
      ∃ k : ℕ, d ^ 2 ^ k ∈ C := fun d hd => by
    obtain ⟨k, hk⟩ := hPp ⟨QuotientGroup.mk' C d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk' C d) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hCD : C ≤ (CFSG.Open.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C) := fun c hc => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc]
    exact (CFSG.Open.pCore 2 (X ⧸ C)).one_mem
  have hDn : (CFSG.Open.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C) |>.Normal :=
    hPn.comap (QuotientGroup.mk' C)
  have hDle : (CFSG.Open.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C) ≤ C :=
    CFSG.Quasithin.MinParabolic.le_of_isTwoQuotient_of_pCoreOf_le h
      (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
      (by rw [CFSG.Quasithin.B6.pCoreOf_top]; exact hQC) hCM hCD le_top
      (Subgroup.normalizer_eq_top_iff.mpr hDn).ge hD2
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
  have hx : x ∈ (CFSG.Open.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C) := hy
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hDle hx

end BurnsideB6a

theorem as_B_6_3 : B_6_3 := by
  intro G _ _ H X hXH
  exact CFSG.Quasithin.mcBride hXH

@[expose] def B_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X : Subgroup G), X ≤ H →
    (uHat H X ≤ H ∧ ((uHat H X).subgroupOf H).Normal ∧
      (uHat H X : Set G) * ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) = (H : Set G)) ∧
    (X < H → (⨆ h ∈ H, X.map (MulAut.conj h).toMonoidHom) = H → uHat H X = H)

theorem as_B_6_4 : B_6_4 := by
  intro G _ _ H X hXH
  obtain ⟨_, hHn, hHeq⟩ := CFSG.Quasithin.uHat_normal_and_eq_sup hXH
  refine ⟨⟨CFSG.Quasithin.uHat_le H X, Subgroup.normal_subgroupOf_of_le_normalizer hHn, ?_⟩, ?_⟩
  · have hN : H ⊓ Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (CFSG.Quasithin.uHat H X : Set G) :=
      fun g hg => hHn hg.1
    exact (Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN).symm.trans
      (congrArg SetLike.coe hHeq.symm)
  · intro hlt hsup
    have hcl : CFSG.Quasithin.conjClosure X H = H := by
      rw [burnsideB6a_conjClosure_eq_iSup]
      exact hsup
    exact CFSG.Quasithin.uHat_eq_of_conjClosure_eq hXH (by rw [hcl]; exact hlt) hcl

@[expose] def B_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T : Subgroup G), IsSylowTwoOf T H →
    twoPrimeResidual H = H → T < H → uHat H T = H

theorem as_B_6_5 : B_6_5 := by
  intro G _ _ H T hT hH hTH
  exact CFSG.Quasithin.generated_by_uFamHat hT hTH hH

@[expose] def B_6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T : Subgroup G), IsSylowTwoOf T H →
    (H ⊓ Subgroup.normalizer (T : Set G)) ⊔ uHat H T = H

theorem as_B_6_6 : B_6_6 := by
  intro G _ _ H T hT
  rw [sup_comm]
  exact (CFSG.Quasithin.uHat_normal_and_eq_sup hT.1).2.2.symm

@[expose] def B_6_8 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T M : Subgroup X), MinParabolic (⊤ : Subgroup X) T M →
    (pCore 2 X = pCoreOf 2 (kerIn M ⊤) ∧ ¬ twoResidual (⊤ : Subgroup X) ≤ kerIn M ⊤) ∧
    (Group.IsSolvable X → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ O2p2 X p = ⊤ ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (pCore 2 X)) =
        (frattini (pCore p (X ⧸ pCore 2 X))).map (pCore p (X ⧸ pCore 2 X)).subtype ∧
      pCore p (X ⧸ kerIn M ⊤) ≠ ⊥ ∧
      ∀ S : Subgroup (X ⧸ kerIn M ⊤), S ≤ pCore p (X ⧸ kerIn M ⊤) →
        T.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ Subgroup.normalizer (S : Set (X ⧸ kerIn M ⊤)) →
        S = ⊥ ∨ S = pCore p (X ⧸ kerIn M ⊤)) ∧
    (¬ Group.IsSolvable X →
      kerIn M ⊤ = O2F X ∧ twoResidual (⊤ : Subgroup X) ⊔ T = ⊤ ∧ B68ThreeStruct X T M ∧
      ((kerIn M ⊤ = O2F X ∧ O2F X = O2Fstar X) ∨
        (kerIn M ⊤ = solvableRadical X ∧ O2E2 X = ⊤))) ∧
    (∀ Y : Subgroup X, Y.Normal → Y ≤ kerIn M ⊤ ∨ twoResidual (⊤ : Subgroup X) ≤ Y) ∧
    IsSylowTwoOf (pCore 2 X) (kerIn M ⊤) ∧
    (∀ (W : Type) [CommGroup W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : X →* MulAut W,
      (¬ twoResidual (⊤ : Subgroup X) ≤ ρ.ker → ρ.ker ≤ kerIn M ⊤) ∧
      (ρ.ker ≤ M → ρ.ker ≤ kerIn M ⊤ ∧ IsSylowTwoOf (pCore 2 X ⊓ ρ.ker) ρ.ker) ∧
      (pCore 2 X ≤ ρ.ker → ρ.ker ≤ M → pCore 2 (X ⧸ ρ.ker) = ⊥)) ∧
    (∀ V : Subgroup X, V ∈ primeReducedFamily X 2 → ⁅V, (⊤ : Subgroup X)⁆ ≠ ⊥ →
      ∀ N : Subgroup X, N ≤ T → (N.subgroupOf T).Normal →
        ((⁅twoResidual (⊤ : Subgroup X), N⁆ < twoResidual (⊤ : Subgroup X) ↔ N ≤ pCore 2 X) ∧
          (N ≤ pCore 2 X ↔ N ≤ T ⊓ Subgroup.centralizer (V : Set X))) ∧
        ((⁅V, Jj T 0⁆ = ⊥ ↔ Jj T 0 = Jj (pCore 2 X) 0) ∧
          (Jj T 0 = Jj (pCore 2 X) 0 ↔ baumOf T = baumOf (pCore 2 X))) ∧
        (⁅V, Jj T 0⁆ ≠ ⊥ → Jj ⊤ 0 = twoResidual (⊤ : Subgroup X) ⊔ Jj T 0 ∧
          ∃ hV : IsElemAbelian 2 V, IsFFModule (autI hV ⊤))) ∧
    (kerIn M ⊤).map (QuotientGroup.mk' (pCore 2 X)) = frattini (X ⧸ pCore 2 X)

theorem as_B_6_8 : B_6_8 := by
  intro X _ _ T M h
  have hpc : CFSG.Open.pCore 2 X = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
    (CFSG.Quasithin.B6.pCoreOf_top 2 X).symm
  have hn : ∀ C : Subgroup X, C.Normal → (⊤ : Subgroup X) ≤ Subgroup.normalizer (C : Set X) :=
    fun C hC => (Subgroup.normalizer_eq_top_iff.mpr hC).ge
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc]
    exact h.pCoreOf_eq_pCoreOf_kerIn
  · exact h.not_twoResidual_le_kerIn
  · intro hsolv
    exact h.solvable_structure hsolv
  · intro hns
    exact ⟨h.kerIn_eq_O2F hns, h.eq_twoResidual_sup.symm, h.nonsolvable_structure hns,
      h.O2F_dichotomy hns⟩
  · intro Y hY
    exact h.le_kerIn_or_twoResidual_le le_top (hn Y hY)
  · have key := h.isSylowTwoOf_pCoreOf_kerIn
    rw [CFSG.Quasithin.B6.pCoreOf_top] at key
    exact key
  · intro W _ _ ρ
    have hρ : (⊤ : Subgroup X) ≤ Subgroup.normalizer ((ρ.ker : Subgroup X) : Set X) :=
      hn _ inferInstance
    refine ⟨fun hK => h.le_kerIn_of_not_twoResidual_le le_top hρ hK, fun hC => ?_,
      fun hQC hCM => burnsideB6a_pCore_quotient_eq_bot h hQC hCM⟩
    have key := h.le_kerIn_and_isSylowTwoOf_of_le hρ hC
    rw [CFSG.Quasithin.B6.pCoreOf_top] at key
    exact key
  · intro V hVfam hJ0 N hNT hNn
    have hV2 : CFSG.Quasithin.IsTwoReducedIn ⊤ V := burnsideB6a_isTwoReduced_top hVfam
    have hHV : ¬ (⊤ : Subgroup X) ≤ Subgroup.centralizer (V : Set X) := fun hle =>
      hJ0 (by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hle)
    have hTN : T ≤ Subgroup.normalizer (N : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mp hNn
    have hT := h.tfae_thompsonJ hV2 hHV
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · have key := h.commutator_lt_iff_le_pCoreOf hNT hTN
      rw [CFSG.Quasithin.B6.pCoreOf_top] at key
      exact key
    · have key := h.le_pCoreOf_iff_le_centralizer hV2 hHV N
      rw [CFSG.Quasithin.B6.pCoreOf_top] at key
      exact key
    · have key := hT.out 1 2
      rw [CFSG.Quasithin.B6.pCoreOf_top] at key
      simp only [burnsideB6a_Jj_zero]
      exact key
    · have key := hT.out 2 3
      rw [CFSG.Quasithin.B6.pCoreOf_top] at key
      simp only [burnsideB6a_Jj_zero, burnsideB6a_baumOf_eq]
      exact key
    · intro hJ
      simp only [burnsideB6a_Jj_zero] at hJ ⊢
      exact ⟨h.thompsonJ_eq_sup hV2 hJ, hV2.2.2.1,
        h.isFFModule_autOn_of_not_commutator_eq_bot hV2 hJ⟩
  · exact h.map_kerIn_eq_frattini

@[expose] def B_6_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H T M : Subgroup (MulAut V), MinParabolic H T M → CFSG.SectionRank.IsKGroupCat ↥H →
      pCoreOf 2 H = ⊥ → IsFFModule H →
        (qOf H = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender H A) ∧
        ∃ (s : ℕ) (Hs : Fin s → Subgroup (MulAut V)),
          IsIntDirProd (ffJ H) Hs ∧
          IsIntDirSumMod (commV (ffJ H)) (fixV (ffJ H)) (fun i => commV (Hs i)) ∧
          (∀ i j, i ≠ j → commSub (commV (Hs i)) (Hs j) = ⊥) ∧
          ((∀ t ∈ T, ∀ i, ∃ j, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j) ∧
            (∀ i j, ∃ t ∈ T, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j)) ∧
          (((ffJ H : Subgroup (MulAut V)) : Set (MulAut V)) * (T : Set (MulAut V)) =
            (H : Set (MulAut V))) ∧
          ∀ i : Fin s,
            (∃ e : ℕ, 1 ≤ e ∧
              Nonempty (↥(Hs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
              M ⊓ Hs i = Hs i ⊓ Subgroup.normalizer ((T ⊓ Hs i : Subgroup (MulAut V)) : Set (MulAut V)) ∧
              BinaryNaturalSL (Hs i) (fixV (ffJ H) ⊔ commV (Hs i)) (fixV (ffJ H)) 2 e) ∨
            (∃ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))) ∧
              Nonempty (↥(M ⊓ Hs i) ≃* Equiv.Perm (Fin (2 ^ k))) ∧
              G6.IsSymCore (Hs i) (commV (Hs i)) (2 ^ k + 1))


@[expose] def B_6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V L : Subgroup G) (n : ℕ),
    MinParabolic H T M → quasithinGenFitting H = pCoreOf 2 H → IsTwoReducedIn H V →
    IsSubnormal L H → IsNaturalL2Prime n L V → ⁅V, Jj T 0⁆ ≠ ⊥ →
      (∀ s ∈ baumOf T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        conjAct V ⟨s, hs⟩ ∈ Subgroup.normalizer (autOn L V : Set (MulAut V))) ∧
      IsSylowTwoOf (baumOf T) (⨆ l ∈ L, (baumOf T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (Jj T 0) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (Jj T 0 : Set G)) ⊔
            (omegaOneCenterOf (Jj T 0) ⊓ Subgroup.centralizer (L : Set G)))

end CFSG.ASVolI
