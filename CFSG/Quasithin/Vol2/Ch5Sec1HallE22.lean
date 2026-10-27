module

public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def E22BorelSolvableFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X B : Subgroup Y) (n : ℕ),
    (E2.IsBenderOf n ↥X ∨ (1 ≤ n ∧ (IsPSL 3 2 n ↥X ∨ E2.IsSp4Prime n ↥X))) →
    E2.IsBorelIn X B → Group.IsSolvable ↥B

section General

variable {G : Type*} [Group G]

theorem isSolvable_map_of_isSolvable {Q : Type*} [Group Q] (f : G →* Q) (X : Subgroup G)
    [Group.IsSolvable ↥X] : Group.IsSolvable ↥(X.map f) := by
  have hs : Function.Surjective ((f.comp X.subtype).codRestrict (X.map f)
      (fun x => ⟨x, x.2, rfl⟩)) := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Group.isSolvable_of_surjective hs

theorem isSolvable_of_map_of_isSolvable_ker {Q : Type*} [Group Q] (f : G →* Q)
    (X : Subgroup G) (hX : Group.IsSolvable ↥(X.map f)) (hK : Group.IsSolvable ↥f.ker) :
    Group.IsSolvable ↥X := by
  let g : ↥X →* ↥(X.map f) :=
    (f.comp X.subtype).codRestrict (X.map f) (fun x => ⟨x, x.2, rfl⟩)
  let e : ↥(f.ker.subgroupOf X) →* ↥f.ker :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun y : ↥f.ker => (y : G)) h))
  have : Group.IsSolvable ↥(f.ker.subgroupOf X) := Group.isSolvable_of_isSolvable_injective he
  refine Group.isSolvable_of_ker_le_range (f.ker.subgroupOf X).subtype g ?_
  intro x hx
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact congrArg Subtype.val hx

theorem isSolvable_of_commutator_le {X P : Subgroup G} (hc : ⁅X, X⁆ ≤ P)
    (hP : Group.IsSolvable ↥P) : Group.IsSolvable ↥X := by
  have hle : ∀ x ∈ commutator ↥X, ((x : ↥X) : G) ∈ P := by
    intro x hx
    apply hc
    have h1 : X.subtype x ∈ (commutator ↥X).map X.subtype := Subgroup.mem_map_of_mem _ hx
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  let e : ↥(commutator ↥X) →* ↥P :=
    { toFun := fun x => ⟨((x : ↥X) : G), hle x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun y : ↥P => (y : G)) h))
  have : Group.IsSolvable ↥(commutator ↥X) := Group.isSolvable_of_isSolvable_injective he
  exact Group.isSolvable_commutator_iff.mp inferInstance

theorem isSolvable_biSup_of_pairwise {ι : Type*} (s : Finset ι) (B : ι → Subgroup G)
    (hB : ∀ i ∈ s, Group.IsSolvable ↥(B i))
    (hP : ∀ i ∈ s, ∀ j ∈ s, B i = B j ∨ B i ≤ Subgroup.centralizer (B j : Set G)) :
    Group.IsSolvable ↥(⨆ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (⨆ i ∈ (∅ : Finset ι), B i) = ⊥ := by simp
    rw [h]
    infer_instance
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hP i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [Finset.iSup_insert]
    by_cases hex : ∃ j ∈ s, B a = B j
    · obtain ⟨j, hj, hEq⟩ := hex
      have hle : B a ≤ ⨆ i ∈ s, B i := by
        rw [hEq]
        exact le_iSup₂_of_le j hj le_rfl
      rw [sup_eq_right.mpr hle]
      exact ih'
    · push Not at hex
      have hc : ∀ j ∈ s, B j ≤ Subgroup.centralizer (B a : Set G) := by
        intro j hj
        rcases hP a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) with h | h
        · exact absurd h (hex j hj)
        · exact Subgroup.le_centralizer_iff.mp h
      have hN : B a ≤ Subgroup.normalizer ((⨆ i ∈ s, B i : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff.mp (iSup₂_le hc)).trans (Subgroup.centralizer_le_normalizer _)
      have := ih'
      have := hB a (Finset.mem_insert_self a s)
      rw [sup_comm]
      exact B1Red.isSolvable_sup_of_isSolvable_of_le_normalizer hN

theorem subgroupOf_iSup_of_le {ι : Sort*} {H : Subgroup G} (C : ι → Subgroup G)
    (hC : ∀ i, C i ≤ H) : (⨆ i, C i).subgroupOf H = ⨆ i, (C i).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le hC)]
  exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hC i)).symm

theorem cjSub_inf_of_mem {M K : Subgroup G} {g : G} (hg : g ∈ M) :
    cjSub g (M ⊓ K) = M ⊓ cjSub g K := by
  ext x
  simp only [mem_cjSub, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := M.mul_mem (M.mul_mem hg h1) (M.inv_mem hg)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨M.mul_mem (M.mul_mem (M.inv_mem hg) h1) hg, h2⟩

end General

namespace E22M

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

omit [Finite Γ] in
theorem isSolvable_of_star {X : Subgroup Γ} (hXH : X ≤ H) (hJH : kerIn M H ≤ H)
    (hJ : Group.IsSolvable ↥(kerIn M H)) (hX : Group.IsSolvable ↥(E2.star M H X)) :
    Group.IsSolvable ↥X := by
  set π : ↥H →* E2.StarQuot M H := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hker : Group.IsSolvable ↥π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    have := hJ
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hJH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJH).symm.surjective
  have h1 := isSolvable_of_map_of_isSolvable_ker π (X.subgroupOf H) hX hker
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXH).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hXH).surjective

end E22M

theorem e22MSolvableFact_of (hE22 : E2.E22StatementC)
    (hB : E22BorelSolvableFact) : E22MSolvableFact := by
  intro Γ _ _ H T M hmp hsq hns hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := hE22.exists_cases hmp hsq hns
  have hMH : M ≤ H := hmp.maximal.le
  have hTM : T ≤ M := hmp.le
  have hTH : T ≤ H := hTM.trans hMH
  have hsmall : ¬ E2.IsE22SmallType ↥(E2.star M H K) :=
    E2.not_isE22SmallType_star_of_lie hTH hmp.isSylow.2.1 hKc hHK hq
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hJH : kerIn M H ≤ H := hmp.kerIn_le_H
  have hTs : Group.IsSolvable ↥T := F1.isSolvable_of_isPGroup_two hmp.isSylow.2.1
  have hMKH : M ⊓ K ≤ H := inf_le_left.trans hMH
  unfold E2.E22CasesC at hcases
  rcases hcases with ⟨hJQ, t, htT, -, hMeq, h1⟩ | ⟨hTK, hJdesc, h2⟩
  ·
    have hJs : Group.IsSolvable ↥(kerIn M H) := by
      rw [hJQ]
      exact F1.isSolvable_of_isPGroup_two (pCoreOf_isPGroup 2 H)
    have hAs : Group.IsSolvable ↥(M ⊓ K) := by
      rcases h1 with ⟨n, hn2, hKs, hBor, -⟩ | ⟨p, hp, hp8, hKs, -, -, -⟩
      · refine E22M.isSolvable_of_star hMKH hJH hJs (hB _ _ _ n (Or.inl ⟨hn2, ?_⟩) hBor)
        rcases hKs with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact absurd (Or.inl ⟨p, hp, hp8, hKs⟩) hsmall
    set A := M ⊓ K with hAdef
    set N : Subgroup Γ := ⨆ y : ↥T, cjSub (y : Γ) A with hNdef
    have hCH : ∀ y : ↥T, cjSub (y : Γ) A ≤ H := fun y =>
      cjSub_le (hMH.trans Subgroup.le_normalizer (hTM y.2)) hMKH
    have hNH : N ≤ H := iSup_le hCH
    have hTN : T ≤ Subgroup.normalizer (N : Set Γ) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show N.map (MulAut.conj x).toMonoidHom = N
      rw [hNdef, Subgroup.map_iSup]
      have hre : ∀ y : ↥T, (cjSub (y : Γ) A).map (MulAut.conj x).toMonoidHom =
          cjSub (((⟨x, hx⟩ : ↥T) * y : ↥T) : Γ) A := by
        intro y
        rw [Subgroup.coe_mul, B2F.cjSub_mul]
        rfl
      simp only [hre]
      exact Equiv.iSup_comp (g := fun y : ↥T => cjSub (y : Γ) A) (Equiv.mulLeft (⟨x, hx⟩ : ↥T))
    have hMNT : M ≤ N ⊔ T := by
      rw [hMeq]
      have hA1 : A ≤ N := by
        have h1A : cjSub ((1 : ↥T) : Γ) A = A := by
          ext x
          simp [mem_cjSub]
        exact h1A ▸ le_iSup (fun y : ↥T => cjSub (y : Γ) A) 1
      have hAt : cjSub t A ≤ N := le_iSup (fun y : ↥T => cjSub (y : Γ) A) ⟨t, htT⟩
      exact sup_le (sup_le (hA1.trans le_sup_left) (hAt.trans le_sup_left)) le_sup_right
    have hNs : Group.IsSolvable ↥N := by
      have : Fintype ↥T := Fintype.ofFinite ↥T
      set R := CFSG.solvableRadical ↥H with hRdef
      set σ : ↥H →* ↥H ⧸ R := QuotientGroup.mk' R with hσ
      have hσs : Function.Surjective σ := QuotientGroup.mk'_surjective R
      have hker : Group.IsSolvable ↥σ.ker := by
        rw [hσ, QuotientGroup.ker_mk']
        exact A3.solvableRadical_isSolvable
      have hRb : CFSG.solvableRadical (↥H ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot ↥H
      have hKy : ∀ y : ↥T, (cjSub (y : Γ) K).subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) :=
        fun y => subgroupOf_mem_cComp (map_conj_mem_cComp hKc (hTH y.2))
      have hcompy : ∀ y : ↥T, CFSG.IsComponent (((cjSub (y : Γ) K).subgroupOf H).map σ) :=
        fun y => isComponent_of_mem_cComp_top hRb (map_mem_cComp_top σ hσs hker (hKy y))
      set Bf : ↥T → Subgroup (↥H ⧸ R) := fun y => ((cjSub (y : Γ) A).subgroupOf H).map σ
        with hBf
      have hBs : ∀ y ∈ (Finset.univ : Finset ↥T), Group.IsSolvable ↥(Bf y) := by
        intro y _
        have hCs : Group.IsSolvable ↥(cjSub (y : Γ) A) := by
          have := hAs
          exact isSolvable_map_of_isSolvable (MulAut.conj (y : Γ)).toMonoidHom A
        have hCs' : Group.IsSolvable ↥((cjSub (y : Γ) A).subgroupOf H) := by
          have := hCs
          exact Group.isSolvable_of_surjective
            (f := (Subgroup.subgroupOfEquivOfLe (hCH y)).symm.toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe (hCH y)).symm.surjective
        have := hCs'
        exact isSolvable_map_of_isSolvable σ _
      have hBle : ∀ y : ↥T, Bf y ≤ ((cjSub (y : Γ) K).subgroupOf H).map σ := fun y =>
        Subgroup.map_mono fun z hz => (cjSub_mono inf_le_right :
          cjSub (y : Γ) A ≤ cjSub (y : Γ) K) hz
      have hPair : ∀ y₁ ∈ (Finset.univ : Finset ↥T), ∀ y₂ ∈ (Finset.univ : Finset ↥T),
          Bf y₁ = Bf y₂ ∨ Bf y₁ ≤ Subgroup.centralizer (Bf y₂ : Set (↥H ⧸ R)) := by
        intro y₁ _ y₂ _
        by_cases hK12 : cjSub (y₁ : Γ) K = cjSub (y₂ : Γ) K
        · left
          have hA12 : cjSub (y₁ : Γ) A = cjSub (y₂ : Γ) A := by
            rw [hAdef, cjSub_inf_of_mem (hTM y₁.2), cjSub_inf_of_mem (hTM y₂.2), hK12]
          show ((cjSub (y₁ : Γ) A).subgroupOf H).map σ = ((cjSub (y₂ : Γ) A).subgroupOf H).map σ
          rw [hA12]
        · right
          have hne : ((cjSub (y₁ : Γ) K).subgroupOf H).map σ ≠
              ((cjSub (y₂ : Γ) K).subgroupOf H).map σ := by
            intro heq
            apply hK12
            have h12 := map_injOn_cComp_top σ hker (hKy y₁) (hKy y₂) heq
            have hle1 : cjSub (y₁ : Γ) K ≤ H :=
              le_of_mem_cComp (map_conj_mem_cComp hKc (hTH y₁.2))
            have hle2 : cjSub (y₂ : Γ) K ≤ H :=
              le_of_mem_cComp (map_conj_mem_cComp hKc (hTH y₂.2))
            rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hle1, inf_eq_left.mpr hle2] at h12
            exact h12
          rcases CFSG.LocalCores.distinct_components_commute (hcompy y₁) (hcompy y₂) with h | h
          · exact absurd h hne
          · have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
            exact (hBle y₁).trans (hc.trans (Subgroup.centralizer_le (hBle y₂)))
      have hsol := isSolvable_biSup_of_pairwise Finset.univ Bf hBs hPair
      have hmap : (N.subgroupOf H).map σ = ⨆ y ∈ (Finset.univ : Finset ↥T), Bf y := by
        rw [hNdef, subgroupOf_iSup_of_le _ hCH, Subgroup.map_iSup]
        simp only [Finset.mem_univ, iSup_true]
        rfl
      have h1 : Group.IsSolvable ↥(N.subgroupOf H) := by
        refine isSolvable_of_map_of_isSolvable_ker σ _ ?_ hker
        rw [hmap]
        exact hsol
      have := h1
      exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNH).surjective
    have := hNs
    have := hTs
    have hNTs : Group.IsSolvable ↥(N ⊔ T) := B1Red.isSolvable_sup_of_isSolvable_of_le_normalizer hTN
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMNT)
  ·
    have hJs : Group.IsSolvable ↥(kerIn M H) := by
      refine isSolvable_of_commutator_le (P := pCoreOf 2 H) ?_
        (F1.isSolvable_of_isPGroup_two (pCoreOf_isPGroup 2 H))
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact ((hJdesc x).mp hx).2 y ((hJdesc y).mp hy).1
    have hAs : Group.IsSolvable ↥(M ⊓ K) := by
      rcases h2 with ⟨n, hBen, hBor, -, -⟩ | ⟨n, hn1, hKs, -, hBor, -, -⟩ |
          ⟨p, e, hp, hp3, he, hpe, hKs, -, -, -⟩ | ⟨p, hp, hp2, hKs, -, -⟩
      · exact E22M.isSolvable_of_star hMKH hJH hJs (hB _ _ _ n (Or.inl hBen) hBor)
      · exact E22M.isSolvable_of_star hMKH hJH hJs (hB _ _ _ n (Or.inr ⟨hn1, hKs⟩) hBor)
      · exact absurd (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hKs⟩)) hsmall
      · exfalso
        rcases hKs with ⟨-, hU⟩ | ⟨-, hL, -⟩
        · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl hU⟩)))
        · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr hL⟩)))
    have hMeq : M = (M ⊓ K) ⊔ T := by
      apply le_antisymm
      · intro m hm
        have hmH : m ∈ K ⊔ T := by
          rw [← hHK]
          exact hMH hm
        obtain ⟨k, hk, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTK).mp hmH
        have hkM : k ∈ M := by
          have := M.mul_mem hm (M.inv_mem (hTM hs))
          simpa using this
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hkM, hk⟩))
          (Subgroup.mem_sup_right hs)
      · exact sup_le inf_le_left hTM
    have hTMK : T ≤ Subgroup.normalizer ((M ⊓ K : Subgroup Γ) : Set Γ) :=
      (le_inf (hTM.trans Subgroup.le_normalizer) hTK).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rw [hMeq]
    have := hAs
    have := hTs
    exact B1Red.isSolvable_sup_of_isSolvable_of_le_normalizer hTMK

end CFSG.Quasithin.H13
