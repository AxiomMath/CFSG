module

public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Prelim

variable {G : Type} [Group G]

theorem ggComponent_le_or_commute [Finite G] {L H U : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L H) (hU : (U.subgroupOf H).IsSubnormal) :
    L ≤ U ∨ ∀ l ∈ L, ∀ u ∈ H ⊓ U, l * u = u * l := by
  have hL' := (isComponentOf_iff_isComponent_subgroupOf hL.1).mp hL
  rcases CFSG.LocalCores.component_subnormal_subgroup hL' hU with hle | hc
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hL.1 hle)
  · refine Or.inr fun l hl u hu => ?_
    have hmem : ⁅(⟨l, hL.1 hl⟩ : H), (⟨u, hu.1⟩ : H)⁆ ∈ ⁅L.subgroupOf H, U.subgroupOf H⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hl)
        (Subgroup.mem_subgroupOf.mpr hu.2)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem

theorem ggComponent_perfect {L H : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L H) :
    ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL.2.2.1)

theorem ggComponent_ne_bot {L H : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L H) :
    L ≠ ⊥ := by
  have hq := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).mp
    hL.2.2
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

theorem ggComponent_not_le_of_isSolvable {L H A : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L H) (hA : Group.IsSolvable A) : ¬ L ≤ A := fun hle =>
  ggComponent_ne_bot hL (CFSG.SeitzReduction.perfect_eq_bot_of_le hA (ggComponent_perfect hL) hle)

theorem ggLe_centralizer_of_normal_le [Finite G] {L H U : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L H) (hUn : U.Normal) (hUH : U ≤ H) (hLU : ¬ L ≤ U) :
    L ≤ Subgroup.centralizer (U : Set G) := by
  rcases ggComponent_le_or_commute hL (hUn.subgroupOf H).isSubnormal with hle | hc
  · exact absurd hle hLU
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hc l hl u ⟨hUH hu, hu⟩).symm

theorem ggMem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hA, hB]

theorem ggMem_normalizer_centralizer {A : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA ⊢
  change conjSub g (Subgroup.centralizer (A : Set G)) = _
  rw [conjSub_centralizer]
  exact congrArg (fun B : Subgroup G => Subgroup.centralizer (B : Set G)) hA

end Prelim

section Fusion

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H E : Subgroup G}

namespace GGControlsStrongFusion

theorem inf_centralizer_le_of [hp : Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) {K : Subgroup G}
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ Subgroup.centralizer ((H ⊓ K : Subgroup G) : Set G) ≤ H := by
  obtain ⟨e, heE, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
  obtain ⟨R, hRY, hRp, hRidx⟩ := h.exists_sylow_le hE heE he1 (hEK heE)
  set Y := H ⊓ K with hY
  set C := K ⊓ Subgroup.centralizer (Y : Set G) with hC
  have hC1 : ∀ T : Subgroup G, T ≤ C → IsPGroup p T → T ≤ R := by
    intro T hTC hTp
    have hTR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRY) (hTC ht).2)
    have hTRp : IsPGroup p ↥(T ⊔ R) := IsPGroup.to_sup_of_normal_right' hTp hRp hTR
    have hTRK : T ⊔ R ≤ K := sup_le (hTC.trans inf_le_left) (hRY.trans inf_le_right)
    have hmul := Subgroup.relIndex_mul_relIndex R (T ⊔ R) K le_sup_right hTRK
    have hnd : ¬ p ∣ R.relIndex (T ⊔ R) := fun hd => hRidx (hmul ▸ dvd_mul_of_dvd_left hd _)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hTRp
    have hdvd : R.relIndex (T ⊔ R) ∣ p ^ m := hm ▸ Subgroup.relIndex_dvd_card R (T ⊔ R)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact hnd (hj ▸ dvd_pow_self p hj0)
    rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact le_sup_left.trans hj
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥C))
  have hPR : (P : Subgroup C).map C.subtype ≤ R :=
    hC1 _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _)
  have hPcen : (P : Subgroup C) ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxY : (x : G) ∈ Y := hRY (hPR ⟨x, hx, rfl⟩)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2.2 (x : G) hxY).symm
  have hNC : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_center_iff.mp (hPcen hx) g).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hQp := MonoidHom.not_dvd_card_ker_transferSylow P hNC
  have hQO : (MonoidHom.transferSylow P hNC).ker ≤ CFSG.pPrimeCore p C :=
    le_sSup ⟨MonoidHom.normal_ker _, (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQp⟩
  have hOH : (CFSG.pPrimeCore p ↥C).map C.subtype ≤ H := by
    refine h.le_of_coprime hp.out hE hEcard ?_ ?_
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact (hp.out.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
    · have hEC : E ≤ Subgroup.normalizer (C : Set G) := fun e he =>
        ggMem_normalizer_inf (hEK he) (ggMem_normalizer_centralizer
          (ggMem_normalizer_inf (Subgroup.le_normalizer (h.1 he)) (hEK he)))
      exact hEC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  intro x hx
  have htop : (⟨x, hx⟩ : C) ∈ (MonoidHom.transferSylow P hNC).ker ⊔ (P : Subgroup C) :=
    hcompl.sup_eq_top ▸ Subgroup.mem_top _
  have hle : (MonoidHom.transferSylow P hNC).ker ⊔ (P : Subgroup C) ≤ H.subgroupOf C := by
    refine sup_le (fun q hq => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_subgroupOf.mpr (hOH ⟨q, hQO hq, rfl⟩)
    · exact Subgroup.mem_subgroupOf.mpr ((hRY.trans inf_le_left) (hPR ⟨y, hy, rfl⟩))
  exact Subgroup.mem_subgroupOf.mp (hle htop)

theorem le_normalizer_of_component [Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) {e : G} (heE : e ∈ E) (he1 : e ≠ 1) {L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L H) {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hKp : p ∣ Nat.card K) (heK : e ∈ Subgroup.normalizer (K : Set G)) :
    L ≤ Subgroup.normalizer (K : Set G) := by
  have hUN : Subgroup.normalClosure (K : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    show Subgroup.closure (Group.conjugatesOfSet (K : Set G)) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have hmem : c * a * c⁻¹ ∈ conjSub c K := ggConj_mem_conjSub c ha
    by_cases hcK : conjSub c K = K
    · exact Subgroup.le_normalizer (hcK ▸ hmem)
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK c) hcK hmem hy).symm
  rcases ggComponent_le_or_commute hL
      ((Subgroup.normalClosure_normal (s := (K : Set G))).subgroupOf H).isSubnormal with
    hle | hc
  · exact hle.trans hUN
  · intro l hl
    by_contra hlK
    have hne : conjSub l K ≠ K := fun heq =>
      hlK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
    refine h.not_inf_le_centralizer hE heE he1 heK hK.1.1.commutator_eq_top hKp fun y hy => ?_
    have hly := hc l hl y ⟨hy.1, Subgroup.subset_normalClosure hy.2⟩
    have hy' : y ∈ conjSub l K := by
      have hyl : l * y * l⁻¹ = y := by rw [hly]; group
      rw [← hyl]
      exact ggConj_mem_conjSub l hy.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK l) hne hy' hx).symm

theorem le_or_le_centralizer [hp : Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) {L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L H) {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hKp : p ∣ Nat.card K) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hOut : Group.IsSolvable (Outer K)) :
    L ≤ K ∨ L ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨e, heE, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
  have hLN := h.le_normalizer_of_component hE heE he1 hL hK hKp (hEK heE)
  have hLperf := ggComponent_perfect hL
  have hLKC := CFSG.SeitzReduction.perfect_le_sup_centralizer hOut hLperf hLN
  rcases ggComponent_le_or_commute hL hK.2.subgroupOf with hle | hc
  · exact Or.inl hle
  right
  have hCH := h.inf_centralizer_le_of hE hEcard hEK
  have hact : ∀ l ∈ L, ∃ k ∈ H ⊓ K, k ∈ Subgroup.centralizer ((H ⊓ K : Subgroup G) : Set G) ∧
      ∀ x ∈ K, l * x * l⁻¹ = k * x * k⁻¹ ∧ l⁻¹ * x * l = k⁻¹ * x * k := by
    intro l hl
    obtain ⟨k, hk, c, hcC, rfl⟩ :=
      CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute
        (fun k hk c hc => (Subgroup.mem_centralizer_iff.mp hc) k hk) (hLKC hl)
    have hkY : k ∈ Subgroup.centralizer ((H ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hc (k * c) hl y hy
      have h2 := (Subgroup.mem_centralizer_iff.mp hcC) y hy.2
      calc y * k = y * (k * c) * c⁻¹ := by group
        _ = k * c * y * c⁻¹ := by rw [h1]
        _ = k * (c * y) * c⁻¹ := by group
        _ = k * (y * c) * c⁻¹ := by rw [h2]
        _ = k * y := by group
    refine ⟨k, ⟨hCH ⟨hk, hkY⟩, hk⟩, hkY, fun x hx => ⟨?_, ?_⟩⟩
    · have hxc := (Subgroup.mem_centralizer_iff.mp hcC) x hx
      calc k * c * x * (k * c)⁻¹ = k * (c * x) * c⁻¹ * k⁻¹ := by group
        _ = k * (x * c) * c⁻¹ * k⁻¹ := by rw [hxc]
        _ = k * x * k⁻¹ := by group
    · have hz : k⁻¹ * x * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
      have hzc := (Subgroup.mem_centralizer_iff.mp hcC) _ hz
      calc (k * c)⁻¹ * x * (k * c) = c⁻¹ * ((k⁻¹ * x * k) * c) := by group
        _ = c⁻¹ * (c * (k⁻¹ * x * k)) := by rw [hzc]
        _ = k⁻¹ * x * k := by group
  have hcomm : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ⁅l₁, l₂⁆ ∈ Subgroup.centralizer (K : Set G) := by
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨k₁, hk₁Y, -, hact₁⟩ := hact l₁ hl₁
    obtain ⟨k₂, hk₂Y, hk₂C, hact₂⟩ := hact l₂ hl₂
    have hk12 : k₁ * k₂ = k₂ * k₁ := Subgroup.mem_centralizer_iff.mp hk₂C k₁ hk₁Y
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hk₁K := hk₁Y.2
    have hk₂K := hk₂Y.2
    have hm1 : k₂⁻¹ * x * k₂ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk₂K) hx) hk₂K
    have hm2 : k₁⁻¹ * (k₂⁻¹ * x * k₂) * k₁ ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem hk₁K) hm1) hk₁K
    have hm3 : k₂ * (k₁⁻¹ * (k₂⁻¹ * x * k₂) * k₁) * k₂⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hk₂K hm2) (K.inv_mem hk₂K)
    have key : ⁅l₁, l₂⁆ * x * ⁅l₁, l₂⁆⁻¹ = ⁅k₁, k₂⁆ * x * ⁅k₁, k₂⁆⁻¹ := by
      calc ⁅l₁, l₂⁆ * x * ⁅l₁, l₂⁆⁻¹
          = l₁ * (l₂ * (l₁⁻¹ * (l₂⁻¹ * x * l₂) * l₁) * l₂⁻¹) * l₁⁻¹ := by
            rw [commutatorElement_def]; group
        _ = l₁ * (l₂ * (l₁⁻¹ * (k₂⁻¹ * x * k₂) * l₁) * l₂⁻¹) * l₁⁻¹ := by
            rw [(hact₂ x hx).2]
        _ = l₁ * (l₂ * (k₁⁻¹ * (k₂⁻¹ * x * k₂) * k₁) * l₂⁻¹) * l₁⁻¹ := by
            rw [(hact₁ _ hm1).2]
        _ = l₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * x * k₂) * k₁) * k₂⁻¹) * l₁⁻¹ := by
            rw [(hact₂ _ hm2).1]
        _ = k₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * x * k₂) * k₁) * k₂⁻¹) * k₁⁻¹ := by
            rw [(hact₁ _ hm3).1]
        _ = ⁅k₁, k₂⁆ * x * ⁅k₁, k₂⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hk12, one_mul, inv_one, mul_one] at key
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  have hLC : ⁅L, L⁆ ≤ Subgroup.centralizer (K : Set G) := Subgroup.commutator_le.mpr hcomm
  rwa [hLperf] at hLC

end GGControlsStrongFusion

end Fusion

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H E : Subgroup G}

theorem ggLemmaThreeFourteen_top [hp : Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hOut : ∀ K : Subgroup G, CFSG.IsComponent K → Group.IsSolvable (Outer K))
    {L : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L H)
    (hLO : ¬ L ≤ CFSG.pPrimeCore p G) :
    ∃ K : Subgroup G, CFSG.IsComponent K ∧ L ≤ K := by
  by_contra hcon
  push Not at hcon
  have hLOp : L ≤ Subgroup.centralizer (CFSG.pPrimeCore p G : Set G) :=
    ggLe_centralizer_of_normal_le hL CFSG.pPrimeCore_normal (h.pPrimeCore_le hp.out hE hEcard)
      hLO
  have hFH : CFSG.fittingSubgroup G ≤ H := by
    rw [CFSG.fitting_eq_sup_pCore]
    exact iSup_le fun q => h.pCore_le hp.out hE hEcard _
  have hLF : L ≤ Subgroup.centralizer (CFSG.fittingSubgroup G : Set G) :=
    ggLe_centralizer_of_normal_le hL CFSG.fittingSubgroup_normal hFH
      (ggComponent_not_le_of_isSolvable hL inferInstance)
  have hcomp : ∀ K : Subgroup G, CFSG.IsComponent K → L ≤ Subgroup.centralizer (K : Set G) := by
    intro K hK
    by_cases hKO : K ≤ CFSG.pPrimeCore p G
    · exact hLOp.trans (Subgroup.centralizer_le hKO)
    have hKp : p ∣ Nat.card K := by
      by_contra hnd
      exact hKO (ggLe_pPrimeCore_of_isSubnormal hK.2 hnd)
    by_cases hKH : K ≤ H
    · have hKc : CFSG.Assembly.IsComponentOf K H :=
        (isComponentOf_iff_isComponent_subgroupOf hKH).mpr
          (CFSG.LocalCores.component_overgroup hK hKH)
      rcases isComponentOf_eq_or_commute hL hKc with heq | hc
      · exact absurd (le_of_eq heq) (hcon K hK)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    · rcases h.le_or_le_centralizer hE hEcard hL hK hKp
          (ggLemmaThreeThirteen_top h hE hEcard hK hKp hKH) (hOut K hK) with hle | hc
      · exact absurd hle (hcon K hK)
      · exact hc
  have hLay : L ≤ Subgroup.centralizer (CFSG.layer G : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    show sSup {K : Subgroup G | CFSG.IsComponent K} ≤ _
    exact sSup_le fun K hK => Subgroup.le_centralizer_iff.mp (hcomp K hK)
  have hFs : L ≤ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    show CFSG.fittingSubgroup G ⊔ CFSG.layer G ≤ _
    exact sup_le (Subgroup.le_centralizer_iff.mp hLF) (Subgroup.le_centralizer_iff.mp hLay)
  have hLle : L ≤ CFSG.generalizedFitting G :=
    hFs.trans (CFSG.centralizer_generalizedFitting_le G)
  have hab : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hLle.trans (Subgroup.le_centralizer_iff.mp hFs))
  exact ggComponent_ne_bot hL (by rw [← ggComponent_perfect hL, hab])

end Main

end CFSG.StandardType
