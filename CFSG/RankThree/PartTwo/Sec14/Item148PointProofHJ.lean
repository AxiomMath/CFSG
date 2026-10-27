module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLE81
import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step148PointHJdON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        X ∈ thetaComponentsAt 3 b →
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] noncomputable def Step148PointHJdA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        X ∈ thetaComponentsAt 3 b →
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] noncomputable def Step148PointHJdA6A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X) →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] noncomputable def Step148PointHJdONPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        X ∈ thetaComponentsAt 3 b →
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ c' ∈ B ∧
            L' ∈ lA A c' ∧
            Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
            IsThreeCentralIn L' b) ∨
          ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] noncomputable def Step148PointHJdONGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        X ∈ thetaComponentsAt 3 b →
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        (∃ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)), K ≤ X ∧
            K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
              V = ⁅V, A⁆}) ∨
          ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

namespace Item148Point

variable {G : Type} [Group G] [Finite G]

theorem mem_of_eq_sSup148 {b : G} {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 b)
    (hne : 𝒳.Nonempty) {X : Subgroup G} (hX : X = sSup 𝒳) {T : Type*} [Group T]
    [hT : IsSimpleGroup T]
    (e : (↥X ⧸ aschbacherSolvableCore 3 ↥X) ⧸
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) ≃* T) :
    X ∈ 𝒳 := by
  classical
  set θX := aschbacherSolvableCore 3 ↥X with hθX
  set Z := Subgroup.center (↥X ⧸ θX) with hZ
  set τ : ↥X →* T := e.toMonoidHom.comp ((QuotientGroup.mk' Z).comp (QuotientGroup.mk' θX))
    with hτ
  have hτs : Function.Surjective τ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective Z).comp (QuotientGroup.mk'_surjective θX))
  have hLX : ∀ L ∈ 𝒳, L ≤ X := fun L hL => (le_sSup hL).trans hX.ge
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := hX.le.trans (sSup_le fun L hL =>
    le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL))
  have hcomm : ∀ L ∈ 𝒳, ∀ L' ∈ 𝒳, L ≠ L' → ∀ l ∈ L.subgroupOf X, ∀ l' ∈ L'.subgroupOf X,
      τ l * τ l' = τ l' * τ l := by
    intro L hL L' hL' hLL l hl l' hl'
    rw [Subgroup.mem_subgroupOf] at hl hl'
    have hc : ⁅(l : G), (l' : G)⁆ ∈
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) :=
      Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt (h𝒳 hL) (h𝒳 hL') hLL
        (Subgroup.commutator_mem_commutator hl hl')
    have hcX : ⁅(l : G), (l' : G)⁆ ∈ X := Subgroup.commutator_mem_commutator l.2 l'.2 |>
      fun h => Subgroup.commutator_le_self X h
    obtain ⟨t, ht, hteq⟩ := Sec12.Item125Diag.inf_le_inSubgroup_theta hXb ⟨hc, hcX⟩
    have hlt : ⁅l, l'⁆ = t := by
      apply Subtype.ext
      have e1 : ((⁅l, l'⁆ : ↥X) : G) = ⁅(l : G), (l' : G)⁆ := by
        simp [commutatorElement_def]
      rw [e1, ← hteq]
      rfl
    have h0 : QuotientGroup.mk' θX t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    have h1 : τ ⁅l, l'⁆ = 1 := by
      rw [hlt, hτ, MonoidHom.comp_apply, MonoidHom.comp_apply, h0, map_one, map_one]
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hnorm : ∀ L ∈ 𝒳, ((L.subgroupOf X).map τ).Normal := by
    intro L hL
    rw [← Subgroup.normalizer_eq_top_iff]
    set S := (Subgroup.normalizer (((L.subgroupOf X).map τ : Subgroup T) : Set T)).comap τ
      with hS
    have hSL : ∀ L' ∈ 𝒳, L' ≤ S.map X.subtype := by
      intro L' hL' x hx
      refine ⟨⟨x, hLX L' hL' hx⟩, ?_, rfl⟩
      show τ ⟨x, hLX L' hL' hx⟩ ∈ Subgroup.normalizer _
      by_cases hLL : L = L'
      · subst hLL
        exact Subgroup.le_normalizer ⟨⟨x, hLX L hL' hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      · rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨l, hl, rfl⟩
          have h := hcomm L hL L' hL' hLL l hl ⟨x, hLX L' hL' hx⟩
            (Subgroup.mem_subgroupOf.mpr hx)
          refine ⟨l, hl, ?_⟩
          rw [← h, mul_inv_cancel_right]
        · intro hy
          obtain ⟨l, hl, hly⟩ := hy
          have h := hcomm L hL L' hL' hLL l hl ⟨x, hLX L' hL' hx⟩
            (Subgroup.mem_subgroupOf.mpr hx)
          refine ⟨l, hl, ?_⟩
          have hy' : y = (τ ⟨x, hLX L' hL' hx⟩)⁻¹ * τ l * τ ⟨x, hLX L' hL' hx⟩ := by
            rw [hly]
            group
          rw [hy', mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    have hXS : X ≤ S.map X.subtype := hX.le.trans (sSup_le hSL)
    have hStop : S = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hXS x.2
      have : y = x := Subtype.ext hyx
      rwa [← this]
    rw [eq_top_iff]
    intro t _
    obtain ⟨x, rfl⟩ := hτs t
    have hx : x ∈ S := hStop ▸ Subgroup.mem_top x
    exact hx
  have hθs : Group.IsSolvable ↥θX :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have himg : ∀ L ∈ 𝒳, (L.subgroupOf X).map τ = ⊤ := by
    intro L hL
    have hLp : Group.IsPerfect ↥L := isPerfect_of_mem_thetaComponentsIn (h𝒳 hL)
    have hLp' : Group.IsPerfect ↥(L.subgroupOf X) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe (hLX L hL)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have := hnorm L hL
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L.subgroupOf X).map τ) with hb | ht
    · exfalso
      set P := (L.subgroupOf X).map (QuotientGroup.mk' θX) with hP
      have hPZ : P ≤ Z := by
        rintro _ ⟨l, hl, rfl⟩
        have h1 : τ l = 1 := by
          have : τ l ∈ (L.subgroupOf X).map τ := ⟨l, hl, rfl⟩
          rwa [hb, Subgroup.mem_bot] at this
        rw [hτ, MonoidHom.comp_apply, MonoidHom.comp_apply] at h1
        have h2 : QuotientGroup.mk' Z (QuotientGroup.mk' θX l) = 1 :=
          e.injective (h1.trans (map_one e).symm)
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hPp : Group.IsPerfect ↥P :=
        Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' θX).subgroupMap (L.subgroupOf X))
          ((QuotientGroup.mk' θX).subgroupMap_surjective _)
      have hPc : P = ⊥ := by
        rw [eq_bot_iff, ← (Subgroup.isPerfect_iff).mp hPp]
        rw [Subgroup.commutator_le]
        intro p hp q hq
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp (hPZ hp) q).symm]
        exact Subgroup.one_mem _
      have hLθ : L.subgroupOf X ≤ θX := by
        intro l hl
        have : QuotientGroup.mk' θX l ∈ P := ⟨l, hl, rfl⟩
        rw [hPc, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff _).mp this
      have hs : Group.IsSolvable ↥(L.subgroupOf X) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLθ)
          (Subgroup.inclusion_injective hLθ)
      have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt (h𝒳 hL)
      have hnt : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        CFSG.LocalCores.isQuasisimple_nontrivial hLq
      have hLnt : Nontrivial ↥(L.subgroupOf X) := by
        rw [← not_subsingleton_iff_nontrivial] at hnt ⊢
        intro hsub
        apply hnt
        have : Subsingleton ↥L :=
          (Subgroup.subgroupOfEquivOfLe (hLX L hL)).symm.injective.subsingleton
        infer_instance
      exact Group.IsPerfect.not_isSolvable ↥(L.subgroupOf X) hs
    · exact ht
  obtain ⟨L₀, hL₀⟩ := hne
  have huniq : ∀ L ∈ 𝒳, L = L₀ := by
    intro L hL
    by_contra hLL
    have hTp : Group.IsPerfect T := by
      have hLp : Group.IsPerfect ↥L := isPerfect_of_mem_thetaComponentsIn (h𝒳 hL)
      have hLp' : Group.IsPerfect ↥(L.subgroupOf X) :=
        Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe (hLX L hL)).symm.toMonoidHom)
          (MulEquiv.surjective _)
      have hsurj : Function.Surjective (τ.comp (L.subgroupOf X).subtype) := by
        intro t
        have : t ∈ (L.subgroupOf X).map τ := (himg L hL).symm ▸ Subgroup.mem_top t
        obtain ⟨l, hl, rfl⟩ := this
        exact ⟨⟨l, hl⟩, rfl⟩
      exact Group.IsPerfect.ofSurjective (f := τ.comp (L.subgroupOf X).subtype) hsurj
    have hTc : ∀ s t : T, s * t = t * s := by
      intro s t
      have hs : s ∈ (L.subgroupOf X).map τ := (himg L hL).symm ▸ Subgroup.mem_top s
      have ht : t ∈ (L₀.subgroupOf X).map τ := (himg L₀ hL₀).symm ▸ Subgroup.mem_top t
      obtain ⟨l, hl, rfl⟩ := hs
      obtain ⟨l', hl', rfl⟩ := ht
      exact hcomm L hL L₀ hL₀ hLL l hl l' hl'
    have hnt : Nontrivial T := hT.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative T ⟨⟨hTc⟩⟩
  have hX₀ : X = L₀ := hX.trans (le_antisymm (sSup_le fun L hL => (huniq L hL).le)
    (le_sSup hL₀))
  rwa [hX₀]

theorem step148PointHJdON_of (h143 : Concl143S14) (hPt : Step148PointHJdONPoint)
    (hGen : Step148PointHJdONGen) : Step148PointHJdON := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
    hdc hbbd hbd X hΔ hCX hX hT hQX
  rcases hPt G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
    hdc hbbd hbd X hΔ hCX hX hT hQX with ⟨c', L', hc'Ω, hc'B, hL'A, hJ2', hcent⟩ | hP
  · rcases hGen G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA
      hd1 hdc hbbd hbd X hΔ hCX hX hT hQX with ⟨K, hK, hKX, hKgen⟩ | hP
    · have hbA : b ∈ A := hB.1 hb
      have hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := hΔ ▸ le_sup_right
      have hKΔ : K = deltaZero A (lB A) K := by
        refine le_antisymm (hKgen.trans (sSup_le fun V hV => ?_)) (deltaZero_le K)
        obtain ⟨hVK, hVinv, hVA⟩ := hV
        obtain ⟨Qs, hQs, hVQs⟩ := exists_le_mem_maxInvariantPiSubgroups
          (⟨hVK.trans (hKX.trans hXΔ), hVinv.2.1, hVinv.2.2⟩ : V ∈ invariantPiSubgroups
            (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3))
        have hQs𝓠 := (h143 G A c L h b hbA hb1 hbΩ Qs hQs).1
        exact le_deltaZero ⟨mem_scriptQ_of_le hQs𝓠 hVQs hVinv.2.2, hVA⟩ hVK
      exact ⟨b, K, X, hB, hQ, hQY, hb, hb1, hK, hKΔ, hKX, hX,
        Or.inr ⟨c', L', hc'Ω, hc'B, hL'A, hJ2', hcent, hT⟩⟩
    · exact hP
  · exact hP

theorem step148PointHJd_of (hON : Step148PointHJdON)
    (hA6 : Step148PointHJdA6) (hA6A6 : Step148PointHJdA6A6) : Step148PointHJd := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
    hdc hbbd hbd X hΔ hCX h𝒳 htype hQX
  obtain ⟨𝒳, h𝒳b, h𝒳ne, hX𝒳⟩ := h𝒳
  rcases htype with hT | hT | hT
  · have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
    obtain ⟨hc3, ⟨e⟩⟩ := hT
    exact hON G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
      hdc hbbd hbd X hΔ hCX (h𝒳b (mem_of_eq_sSup148 h𝒳b h𝒳ne hX𝒳 e)) ⟨hc3, ⟨e⟩⟩ hQX
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨hc3, ⟨e⟩⟩ := hT
    exact hA6 G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
      hdc hbbd hbd X hΔ hCX (h𝒳b (mem_of_eq_sSup148 h𝒳b h𝒳ne hX𝒳 e)) ⟨hc3, ⟨e⟩⟩ hQX
  · exact hA6A6 G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA
      hd1 hdc hbbd hbd X hΔ hCX ⟨𝒳, h𝒳b, h𝒳ne, hX𝒳⟩ hT hQX

theorem step148PointHJ_of_types (hON : Step148PointHJdON)
    (hA6 : Step148PointHJdA6) (hA6A6 : Step148PointHJdA6A6) : Step148PointHJ :=
  Sec14.step148PointHJ_of (step148PointHJd_of hON hA6 hA6A6)

theorem step148PointHJ_of (h143 : Concl143S14)
    (hPt : Step148PointHJdONPoint) (hGen : Step148PointHJdONGen) (hA6 : Step148PointHJdA6)
    (hA6A6 : Step148PointHJdA6A6) : Step148PointHJ :=
  step148PointHJ_of_types (step148PointHJdON_of h143 hPt hGen) hA6 hA6A6

end Item148Point

end CFSG.RankThree.PartTwo.Sec14
