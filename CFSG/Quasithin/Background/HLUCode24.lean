module

public import CFSG.Quasithin.Background.HLUCode24Gen
public import CFSG.Quasithin.Background.HLUBlocks
public import CFSG.Quasithin.Background.HZCoc24
public import CFSG.Quasithin.Background.HFCode24
public import Certificates.Certificate7260
public import CFSG.Quasithin.Background.HB82Base
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.SmithB42Alt6Mod

public section

namespace CFSG.Quasithin.H.LU24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU
open scoped commutatorElement

@[expose] def sxG1 : Equiv.Perm (Fin 24) := permOfArr 24 sxG1Arr sxG1Inv sx_ok.1

@[expose] def sxG2 : Equiv.Perm (Fin 24) := permOfArr 24 sxG2Arr sxG2Inv sx_ok.2.1

@[expose] def sxT : Equiv.Perm (Fin 24) := permOfArr 24 sxTArr sxTInv sx_ok.2.2.1

theorem hasArr_sxG1 : HasArr sxG1 sxG1Arr := hasArr_permOfArr _

theorem hasArr_sxG1inv : HasArr sxG1⁻¹ sxG1Inv := hasArr_permOfArr_inv _

theorem hasArr_sxG2 : HasArr sxG2 sxG2Arr := hasArr_permOfArr _

theorem hasArr_sxG2inv : HasArr sxG2⁻¹ sxG2Inv := hasArr_permOfArr_inv _

theorem hasArr_sxT : HasArr sxT sxTArr := hasArr_permOfArr _

theorem hasArr_sxTinv : HasArr sxT⁻¹ sxTInv := hasArr_permOfArr_inv _

theorem sxG1_mem : sxG1 ∈ AutPerm := mem_AutPerm_of_arr _ sx_ok.2.2.2.1

theorem sxG2_mem : sxG2 ∈ AutPerm := mem_AutPerm_of_arr _ sx_ok.2.2.2.2.1

theorem sxT_mem : sxT ∈ AutPerm := mem_AutPerm_of_arr _ sx_ok.2.2.2.2.2

@[expose] def sxP0 : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {sxG1, sxG2}

theorem sxG1_mem_P0 : sxG1 ∈ sxP0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem sxG2_mem_P0 : sxG2 ∈ sxP0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sxP0_le : sxP0 ≤ AutPerm := by
  rw [sxP0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact sxG1_mem
  · exact sxG2_mem

theorem hasArr_sxC0 : HasArr ⁅sxG1, sxG2⁆ sxC0Arr := by
  rw [commutatorElement_def, mul_assoc (sxG1 * sxG2)]
  exact hasArr_mul (hasArr_mul hasArr_sxG1 hasArr_sxG2) (hasArr_mul hasArr_sxG1inv hasArr_sxG2inv)

theorem hasArr_sxC1 : HasArr ⁅sxG1, sxG2 * (sxG2 * sxG2)⁆ sxC1Arr := by
  rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, mul_assoc (sxG1 * (sxG2 * (sxG2 * sxG2)))]
  exact hasArr_mul
    (hasArr_mul hasArr_sxG1 (hasArr_mul hasArr_sxG2 (hasArr_mul hasArr_sxG2 hasArr_sxG2)))
    (hasArr_mul hasArr_sxG1inv (hasArr_mul (hasArr_mul hasArr_sxG2inv hasArr_sxG2inv)
      hasArr_sxG2inv))

theorem commutator_sxP0 : ⁅sxP0, sxP0⁆ = sxP0 := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact sxP0.mul_mem (sxP0.mul_mem (sxP0.mul_mem hx hy) (sxP0.inv_mem hx))
      (sxP0.inv_mem hy)) ?_
  have hc : ∀ p ∈ [⁅sxG1, sxG2⁆, ⁅sxG1, sxG2 * (sxG2 * sxG2)⁆], p ∈ ⁅sxP0, sxP0⁆ := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Subgroup.commutator_mem_commutator sxG1_mem_P0 sxG2_mem_P0
    · exact Subgroup.commutator_mem_commutator sxG1_mem_P0
        (sxP0.mul_mem sxG2_mem_P0 (sxP0.mul_mem sxG2_mem_P0 sxG2_mem_P0))
  have hw := hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_sxC0 hasArr_sxC1)
  show Subgroup.closure ({sxG1, sxG2} : Set (Equiv.Perm (Fin 24))) ≤ ⁅sxP0, sxP0⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h := hw (sxPerfWord 0)
    rw [sx_perf.1] at h
    exact perm_eq_of_hasArr hasArr_sxG1 h ▸ wPerm_mem hc _
  · have h := hw (sxPerfWord 1)
    rw [sx_perf.2] at h
    exact perm_eq_of_hasArr hasArr_sxG2 h ▸ wPerm_mem hc _

@[expose] def sxGen : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {sxG1, sxG2, sxT}

theorem sxP0_le_gen : sxP0 ≤ sxGen := by
  rw [sxP0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem sxT_mem_gen : sxT ∈ sxGen := Subgroup.subset_closure (by simp)

abbrev sxEven : Subgroup (Equiv.Perm (Fin 24)) := blockEven lab6_rep6

theorem mem_blockP_lab6 {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ x y : Fin 24, (lab6L.getD a[(x : ℕ)]! 0 = lab6L.getD a[(y : ℕ)]! 0 ↔
      lab6L.getD x 0 = lab6L.getD y 0)) : σ ∈ blockP lab6 :=
  mem_blockP_of_arr lab6L lab6_val ha h

theorem blockHom_eq {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (hσ : σ ∈ blockP lab6) {π : Equiv.Perm (Fin 6)}
    (h : ∀ i : Fin 6, lab6L.getD a[((rep6 i : Fin 24) : ℕ)]! 0 = (π i : ℕ)) :
    blockHom lab6_rep6 ⟨σ, hσ⟩ = π := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [blockHom_apply, lab6_val, ha]
  exact h i

theorem sxG1_blockP : sxG1 ∈ blockP lab6 := mem_blockP_lab6 hasArr_sxG1 fun x y => (sx_lab x y).1

theorem sxG2_blockP : sxG2 ∈ blockP lab6 :=
  mem_blockP_lab6 hasArr_sxG2 fun x y => (sx_lab x y).2.1

theorem sxT_blockP : sxT ∈ blockP lab6 := mem_blockP_lab6 hasArr_sxT fun x y => (sx_lab x y).2.2

theorem sxP0_le_even : sxP0 ≤ sxEven := by
  rw [sxP0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · refine mem_blockEven lab6_rep6 sxG1_blockP ?_
    rw [blockHom_eq hasArr_sxG1 sxG1_blockP fun i => (sx_bp i).1]
    exact sign6.1
  · refine mem_blockEven lab6_rep6 sxG2_blockP ?_
    rw [blockHom_eq hasArr_sxG2 sxG2_blockP fun i => (sx_bp i).2.1]
    exact sign6.2.1

theorem sxT_not_even : sxT ∉ sxEven := by
  refine not_mem_blockEven lab6_rep6 sxT_blockP ?_
  rw [blockHom_eq hasArr_sxT sxT_blockP fun i => (sx_bp i).2.2]
  exact sign6.2.2.1

theorem two_mul_card_P0_le : 2 * Nat.card ↥sxP0 ≤ Nat.card ↥sxGen := by
  refine mul_card_le_of_cosets sxP0_le_gen ![1, sxT] (fun i => ?_) fun i j h => ?_
  · fin_cases i
    · exact sxGen.one_mem
    · exact sxT_mem_gen
  · fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply sxT_not_even
      have h' : (1 : Equiv.Perm (Fin 24))⁻¹ * sxT ∈ sxP0 := h
      rw [inv_one, one_mul] at h'
      exact sxP0_le_even h'
    · exfalso
      apply sxT_not_even
      have h' : sxT⁻¹ * 1 ∈ sxP0 := h
      rw [mul_one] at h'
      exact (sxEven).inv_mem_iff.1 (sxP0_le_even h')
    · rfl

@[expose] def ks6P (i : ℕ) : Equiv.Perm (Fin 24) := wPerm [sxG1, sxG2] (ksWord6 i)

theorem hasArr_ks6 (i : ℕ) : HasArr (ks6P i) (ks6Arr i) :=
  hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_sxG1 hasArr_sxG2) _

theorem mem_of_pair {K : Subgroup (Equiv.Perm (Fin 24))} (h1 : sxG1 ∈ K) (h2 : sxG2 ∈ K) :
    ∀ p ∈ [sxG1, sxG2], p ∈ K := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

theorem ks6_mem_P0 (i : ℕ) : ks6P i ∈ sxP0 := wPerm_mem (mem_of_pair sxG1_mem_P0 sxG2_mem_P0) _

@[expose] def sxKS : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure (Set.range fun i : Fin 6 => ks6P i)

theorem ks6_mem_KS (i : Fin 6) : ks6P i ∈ sxKS := Subgroup.subset_closure ⟨i, rfl⟩

theorem sxKS_le_P0 : sxKS ≤ sxP0 := by
  rw [sxKS, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ks6_mem_P0 i

@[expose] def ksList : List (Equiv.Perm (Fin 24)) := (List.range 6).map ks6P

theorem hasArr_ksList :
    ∀ i, HasArr (ksList.getD i 1) (((List.range 6).map ks6Arr).getD i idArr) := by
  refine hasArr_getD (by simp [ksList]) fun i hi => ?_
  simp only [ksList, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact hasArr_ks6 i

theorem wPerm_ksList_mem (w : List ℕ) : wPerm ksList w ∈ sxKS := by
  refine wPerm_mem (fun p hp => ?_) w
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  exact ks6_mem_KS ⟨i, List.mem_range.1 hi⟩

theorem conj_mem_KS {g : Equiv.Perm (Fin 24)} (hg : ∀ i < 6, g * ks6P i * g⁻¹ ∈ sxKS) :
    ∀ h ∈ sxKS, g * h * g⁻¹ ∈ sxKS := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hg i i.2
  | one => simp [sxKS.one_mem]
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact sxKS.mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact sxKS.inv_mem hx

theorem conj_ks6 {g : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hga : HasArr g a)
    (hgb : HasArr g⁻¹ b) {c : ℕ} (hc : ∀ i < 6, cArr (cArr a (ks6Arr i)) b =
      wArr ((List.range 6).map ks6Arr) (subW (ksConj c i))) :
    ∀ i < 6, g * ks6P i * g⁻¹ ∈ sxKS := by
  intro i hi
  have h1 : HasArr (g * ks6P i * g⁻¹) (cArr (cArr a (ks6Arr i)) b) :=
    hasArr_mul (hasArr_mul hga (hasArr_ks6 i)) hgb
  rw [hc i hi] at h1
  rw [perm_eq_of_hasArr h1 (hasArr_wPerm hasArr_ksList _)]
  exact wPerm_ksList_mem _

theorem mem_normalizer_KS {g : Equiv.Perm (Fin 24)} (h1 : ∀ i < 6, g * ks6P i * g⁻¹ ∈ sxKS)
    (h2 : ∀ i < 6, g⁻¹ * ks6P i * g⁻¹⁻¹ ∈ sxKS) :
    g ∈ Subgroup.normalizer (sxKS : Set (Equiv.Perm (Fin 24))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_KS h1 h, fun hh => ?_⟩
  have := conj_mem_KS h2 _ hh
  rwa [inv_inv, show g⁻¹ * (g * h * g⁻¹) * g = h by group] at this

theorem sxP0_le_normalizer : sxP0 ≤ Subgroup.normalizer (sxKS : Set (Equiv.Perm (Fin 24))) := by
  rw [sxP0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · refine mem_normalizer_KS
      (conj_ks6 hasArr_sxG1 hasArr_sxG1inv fun i hi => (ks6_conj i hi).1) ?_
    rw [inv_inv]
    exact conj_ks6 hasArr_sxG1inv hasArr_sxG1 fun i hi => (ks6_conj i hi).2.2.1
  · refine mem_normalizer_KS
      (conj_ks6 hasArr_sxG2 hasArr_sxG2inv fun i hi => (ks6_conj i hi).2.1) ?_
    rw [inv_inv]
    exact conj_ks6 hasArr_sxG2inv hasArr_sxG2 fun i hi => (ks6_conj i hi).2.2.2

theorem ks6_comm (i j : Fin 6) : ks6P i * ks6P j = ks6P j * ks6P i := by
  have h := (ks6_ok i i.2).2.2.2 j j.2
  exact perm_eq_of_hasArr (hasArr_mul (hasArr_ks6 i) (hasArr_ks6 j))
    (h ▸ hasArr_mul (hasArr_ks6 j) (hasArr_ks6 i))

theorem ks6_sq (i : Fin 6) : ks6P i * ks6P i = 1 := by
  have h := (ks6_ok i i.2).2.2.1
  exact perm_eq_of_hasArr (h ▸ hasArr_mul (hasArr_ks6 i) (hasArr_ks6 i)) hasArr_one

theorem sxKS_elem : ∀ x ∈ sxKS, x * x = 1 ∧ ∀ y ∈ sxKS, x * y = y * x := by
  have hc : ∀ x ∈ sxKS, ∀ i : Fin 6, x * ks6P i = ks6P i * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact fun i => ks6_comm j i
    | one => simp
    | mul x y _ _ hx hy => exact fun i => by rw [mul_assoc, hy i, ← mul_assoc, hx i, mul_assoc]
    | inv x _ hx =>
      intro i
      have h := hx i
      calc x⁻¹ * ks6P i = x⁻¹ * (ks6P i * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * ks6P i) * x⁻¹ := by rw [h]
        _ = ks6P i * x⁻¹ := by group
  have hc2 : ∀ x ∈ sxKS, ∀ y ∈ sxKS, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hc x hx j
    | one => simp
    | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    | inv y _ hy =>
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hy]
        _ = y⁻¹ * x := by group
  refine fun x hx => ⟨?_, hc2 x hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ks6_sq j
  | one => simp
  | mul x y hx' hy' hx hy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc2 y hy' x hx']
      _ = 1 := by rw [← mul_assoc, hx, one_mul, hy]
  | inv x _ hx => rw [← mul_inv_rev, hx, inv_one]

theorem isPGroup_KS : IsPGroup 2 ↥sxKS :=
  isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by rw [pow_two]; exact (sxKS_elem x x.2).1)

@[expose] def sxZ : Equiv.Perm (Fin 24) := wPerm [sxG1, sxG2] [1, 1, 1, 1, 1]

theorem hasArr_sxZ : HasArr sxZ sxZArr :=
  hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_sxG1 hasArr_sxG2) _

theorem sxZ_mem_P0 : sxZ ∈ sxP0 := wPerm_mem (mem_of_pair sxG1_mem_P0 sxG2_mem_P0) _

theorem sxZ_cube : sxZ ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  have h := sxZ_ok.1
  refine perm_eq_of_hasArr ?_ hasArr_one
  rw [← h, mul_assoc]
  exact hasArr_mul hasArr_sxZ (hasArr_mul hasArr_sxZ hasArr_sxZ)

theorem sxZ_ne_one : sxZ ≠ 1 := by
  intro h
  have h1 : ((sxZ 0 : Fin 24) : ℕ) = 12 := (hasArr_sxZ 0).trans sxZ_ok.2.1
  rw [h] at h1
  exact absurd h1 (by decide)

abbrev US : Subgroup W11 := maskSub 11 uSBasis

theorem uSBasis_lt : ∀ a ∈ uSBasis, a < 2 ^ 11 := by decide

theorem uSMasks_lt : ∀ m ∈ uSMasks, m < 2 ^ 11 := by decide

theorem toW_mem_US_iff {m : ℕ} (hm : m < 2 ^ 11) : (toW 11 m : W11) ∈ US ↔ m ∈ uSMasks := by
  rw [← uSMasks_combos m hm]
  constructor
  · rintro ⟨m', hm', he⟩
    rwa [← toW_inj (combos_lt uSBasis_lt _ hm') hm he]
  · intro h
    exact toW_mem_maskSub h

theorem maps_US {g : MulAut W11} {f : ℕ → ℕ} (hg : ∀ m, g (toW 11 m) = toW 11 (f m))
    (hlt : ∀ m, f m < 2 ^ 11) (hf : ∀ m ∈ uSMasks, f m ∈ uSMasks) : ∀ u ∈ US, g u ∈ US := by
  rintro _ ⟨m, hm, rfl⟩
  have hm' : m < 2 ^ 11 := combos_lt uSBasis_lt _ hm
  rw [hg m]
  exact (toW_mem_US_iff (hlt m)).2 (hf m ((uSMasks_combos m hm').1 hm))

@[expose] noncomputable def rhoCd {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) : MulAut W11 :=
  rhoC11 AutPerm le_rfl ⟨σ, hσ⟩

theorem rhoCd_toW {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {a : Array ℕ} (ha : HasArr σ a)
    (m : ℕ) : rhoCd hσ (toW 11 m) = toW 11 (actC11 a m) :=
  rhoC11_toW AutPerm le_rfl ⟨σ, hσ⟩ ha m

theorem rhoCd_mem_stabSub {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {a b : Array ℕ}
    (ha : HasArr σ a) (hb : HasArr σ⁻¹ b) (hpa : ∀ m ∈ uSMasks, actC11 a m ∈ uSMasks)
    (hpb : ∀ m ∈ uSMasks, actC11 b m ∈ uSMasks) : rhoCd hσ ∈ stabSub US := by
  refine mem_stabSub_of_maps (maps_US (rhoCd_toW hσ ha) (actC11_lt a) hpa)
    (maps_US (fun m => ?_) (actC11_lt b) hpb)
  have h := rhoC11_toW AutPerm le_rfl (⟨σ, hσ⟩⁻¹ : ↥AutPerm) hb m
  rw [map_inv] at h
  exact h

@[expose] noncomputable def stabUS : Subgroup ↥AutPerm := (stabSub US).comap (rhoC11 AutPerm le_rfl)

theorem map_stabUS :
    stabUS.map (rhoC11 AutPerm le_rfl) = (rhoC11 AutPerm le_rfl).range ⊓ stabSub US :=
  Subgroup.map_comap_eq (rhoC11 AutPerm le_rfl) (stabSub US)

@[expose] noncomputable def stabUSP : Subgroup (Equiv.Perm (Fin 24)) := stabUS.map AutPerm.subtype

theorem mem_stabUSP {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (h : rhoCd hσ ∈ stabSub US) :
    σ ∈ stabUSP :=
  ⟨⟨σ, hσ⟩, h, rfl⟩

theorem card_stabUSP :
    Nat.card ↥stabUSP = Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) := by
  rw [← map_stabUS, stabUSP, Subgroup.card_map_of_injective AutPerm.subtype_injective,
    Subgroup.card_map_of_injective (rhoC11_injective AutPerm le_rfl)]

theorem sxG1_stab : rhoCd sxG1_mem ∈ stabSub US :=
  rhoCd_mem_stabSub sxG1_mem hasArr_sxG1 hasArr_sxG1inv (fun m hm => (sx_pres m hm).1)
    (fun m hm => (sx_pres m hm).2.1)

theorem sxG2_stab : rhoCd sxG2_mem ∈ stabSub US :=
  rhoCd_mem_stabSub sxG2_mem hasArr_sxG2 hasArr_sxG2inv (fun m hm => (sx_pres m hm).2.2.1)
    (fun m hm => (sx_pres m hm).2.2.2.1)

theorem sxT_stab : rhoCd sxT_mem ∈ stabSub US :=
  rhoCd_mem_stabSub sxT_mem hasArr_sxT hasArr_sxTinv (fun m hm => (sx_pres m hm).2.2.2.2.1)
    (fun m hm => (sx_pres m hm).2.2.2.2.2)

theorem sxGen_le : sxGen ≤ stabUSP := by
  rw [sxGen, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact mem_stabUSP sxG1_mem sxG1_stab
  · exact mem_stabUSP sxG2_mem sxG2_stab
  · exact mem_stabUSP sxT_mem sxT_stab

theorem perfectCore_stabUSP (hS : Nat.card ↥stabUSP ≤ 138240) (hQ : 69120 ≤ Nat.card ↥sxP0) :
    perfectCore stabUSP = sxP0 ∧ Nat.card ↥sxP0 = 69120 := by
  have h1 := two_mul_card_P0_le
  have hle : sxP0 ≤ stabUSP := sxP0_le_gen.trans sxGen_le
  have h2 : Nat.card ↥sxGen ≤ Nat.card ↥stabUSP := Subgroup.card_le_of_le sxGen_le
  have hc : Nat.card ↥stabUSP = 2 * Nat.card ↥sxP0 := by omega
  refine ⟨le_antisymm ((perfectCore_le_derivedSeriesOf _ 1).trans ?_)
    (le_perfectCore_of_perfect hle commutator_sxP0), by omega⟩
  rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
  exact Coc24.commutator_le_of_card_two_mul hle hc

@[expose] noncomputable def imgCd (Γ : Subgroup (Equiv.Perm (Fin 24))) : Subgroup (MulAut W11) :=
  (Γ.subgroupOf AutPerm).map (rhoC11 AutPerm le_rfl)

theorem rhoCd_mem_imgCd {Γ : Subgroup (Equiv.Perm (Fin 24))} {σ : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ AutPerm) (hσΓ : σ ∈ Γ) : rhoCd hσ ∈ imgCd Γ :=
  ⟨⟨σ, hσ⟩, Subgroup.mem_subgroupOf.2 hσΓ, rfl⟩

theorem card_imgCd {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : Γ ≤ AutPerm) : Nat.card ↥(imgCd Γ) = Nat.card ↥Γ := by
  rw [imgCd, Subgroup.card_map_of_injective (rhoC11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv]

theorem imgCd_closure_le {S : Set (Equiv.Perm (Fin 24))} (hS : S ⊆ AutPerm)
    {T : Subgroup (MulAut W11)} (hT : ∀ σ (h : σ ∈ S), rhoCd (hS h) ∈ T) :
    imgCd (Subgroup.closure S) ≤ T := by
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' := Subgroup.mem_subgroupOf.1 hσ
  have key : ∀ τ ∈ Subgroup.closure S, ∀ h : τ ∈ AutPerm, rhoCd h ∈ T := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx => exact fun _ => hT x hx
    | one =>
      intro h
      have e : (⟨1, h⟩ : ↥AutPerm) = 1 := rfl
      show rhoC11 AutPerm le_rfl ⟨1, h⟩ ∈ T
      rw [e, map_one]
      exact T.one_mem
    | mul x y hx hy ihx ihy =>
      intro h
      have hx' : x ∈ AutPerm := (Subgroup.closure_le AutPerm).2 hS hx
      have hy' : y ∈ AutPerm := (Subgroup.closure_le AutPerm).2 hS hy
      have e : (⟨x * y, h⟩ : ↥AutPerm) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      show rhoC11 AutPerm le_rfl ⟨x * y, h⟩ ∈ T
      rw [e, map_mul]
      exact T.mul_mem (ihx hx') (ihy hy')
    | inv x hx ihx =>
      intro h
      have hx' : x ∈ AutPerm := (Subgroup.closure_le AutPerm).2 hS hx
      have e : (⟨x⁻¹, h⟩ : ↥AutPerm) = (⟨x, hx'⟩ : ↥AutPerm)⁻¹ := rfl
      show rhoC11 AutPerm le_rfl ⟨x⁻¹, h⟩ ∈ T
      rw [e, map_inv]
      exact T.inv_mem (ihx hx')
  exact key σ hσ' σ.2

theorem commutator_imgCd_P0 : ⁅imgCd sxP0, imgCd sxP0⁆ = imgCd sxP0 := by
  have h : ⁅sxP0.subgroupOf AutPerm, sxP0.subgroupOf AutPerm⁆ = sxP0.subgroupOf AutPerm := by
    apply Subgroup.map_injective AutPerm.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le sxP0_le, commutator_sxP0]
  rw [imgCd, ← Subgroup.map_commutator, h]

theorem imgCd_P0_le_stab : imgCd sxP0 ≤ stabSub US :=
  imgCd_closure_le (S := {sxG1, sxG2}) (by
    rintro _ (rfl | rfl)
    · exact sxG1_mem
    · exact sxG2_mem) (by
    rintro _ (rfl | rfl)
    · exact sxG1_stab
    · exact sxG2_stab)

theorem actsBy_sxG1 : ActsBy (rhoCd sxG1_mem) sxG1C := by
  rw [← sxCols_eq.1]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW sxG1_mem hasArr_sxG1)

theorem actsBy_sxG2 : ActsBy (rhoCd sxG2_mem) sxG2C := by
  rw [← sxCols_eq.2]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW sxG2_mem hasArr_sxG2)

theorem maskOf_mem_US {φ : MulAut W11} (hφ : φ ∈ stabSub US) {u : ℕ} (hu : u ∈ uSMasks) :
    Parab.maskOf 11 (φ (toW 11 u)) ∈ uSMasks := by
  have h1 : φ (toW 11 u) ∈ US := (hφ _).2 ((toW_mem_US_iff (uSMasks_lt u hu)).2 hu)
  rw [← (Parab.maskOf_spec (φ (toW 11 u))).2] at h1
  exact (toW_mem_US_iff (Parab.maskOf_spec _).1).1 h1

theorem card_centUS_mul_le [Finite (MulAut W11)] :
    360 * Nat.card ↥(imgCd sxP0 ⊓ centSub US) ≤ Nat.card ↥(imgCd sxP0) := by
  have hgen : ∀ g : ℕ, ∃ ρ ∈ imgCd sxP0, ActsBy ρ (if g = 0 then sxG1C else sxG2C) := by
    intro g
    by_cases hg : g = 0
    · rw [ite_eq_left hg]
      exact ⟨_, rhoCd_mem_imgCd sxG1_mem sxG1_mem_P0, actsBy_sxG1⟩
    · rw [ite_eq_right hg]
      exact ⟨_, rhoCd_mem_imgCd sxG2_mem sxG2_mem_P0, actsBy_sxG2⟩
  have hlt : ∀ g : ℕ, ∀ x ∈ (if g = 0 then sxG1C else sxG2C), x < 2 ^ 11 := by
    intro g x hx
    split_ifs at hx
    · exact sxCols_lt x (List.mem_append_left _ hx)
    · exact sxCols_lt x (List.mem_append_right _ hx)
  have hus : ∀ u ∈ uSBasis, u ∈ uSMasks := by decide
  have h := card_mul_le_of_tree (K := imgCd sxP0) (C := imgCd sxP0 ⊓ centSub US) inf_le_left
    (tupKey 11 4 usD uSBasis) (fun φ _ ψ hψ => tupKey_mul_fix uSBasis fun u hu =>
      hψ.2 _ ((toW_mem_US_iff (uSMasks_lt u (hus u hu))).2 (hus u hu)))
    usAct (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      obtain ⟨ρ, hρ, hρa⟩ := hgen g
      exact ⟨ρ * φ, Subgroup.mul_mem _ hρ hφ, tupKey_mul hρa (hlt g) (fun m hm => usD_ok m hm)
        uSBasis fun u hu => maskOf_mem_US (imgCd_P0_le_stab hφ) (hus u hu)⟩)
    ⟨1, Subgroup.one_mem _, by
      rw [tupKey_one uSBasis fun u hu => uSMasks_lt u (hus u hu), usStart]⟩ usTree_ok
  rwa [usTree_length] at h

theorem ks6_autPerm (i : ℕ) : ks6P i ∈ AutPerm := sxP0_le (ks6_mem_P0 i)

theorem sxZ_autPerm : sxZ ∈ AutPerm := sxP0_le sxZ_mem_P0

theorem ks6_cent {i : ℕ} (hi : i < 6) : rhoCd (ks6_autPerm i) ∈ centSub US := by
  rintro _ ⟨m, hm, rfl⟩
  exact (rhoCd_toW _ (hasArr_ks6 i) m).trans (congrArg (toW 11) ((ks6_ok i hi).2.1 m hm))

theorem sxZ_cent : rhoCd sxZ_autPerm ∈ centSub US := by
  rintro _ ⟨m, hm, rfl⟩
  exact (rhoCd_toW _ hasArr_sxZ m).trans (congrArg (toW 11) (sxZ_ok.2.2 m hm))

theorem actsBy_ks6 {i : ℕ} (hi : i < 6) : ActsBy (rhoCd (ks6_autPerm i)) (ksC6 i) := by
  rw [← (ks6_ok i hi).1]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW _ (hasArr_ks6 i))

theorem imgCd_KS_le : imgCd sxKS ≤ imgCd sxP0 ⊓ centSub US := by
  refine imgCd_closure_le (S := Set.range fun i : Fin 6 => ks6P i) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact ks6_autPerm i
  · rintro _ ⟨i, rfl⟩
    exact ⟨rhoCd_mem_imgCd _ (ks6_mem_P0 i), ks6_cent i.2⟩

theorem imgCd_KS_le_P0 : imgCd sxKS ≤ imgCd sxP0 := imgCd_KS_le.trans inf_le_left

theorem isPGroup_imgCd_KS : IsPGroup 2 ↥(imgCd sxKS) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : IsPGroup 2 ↥(sxKS.subgroupOf AutPerm) :=
    isPGroup_KS.of_equiv (Subgroup.subgroupOfEquivOfLe (sxKS_le_P0.trans sxP0_le)).symm
  exact h.map _

theorem le_card_imgCd_KS [Finite (MulAut W11)] : 64 ≤ Nat.card ↥(imgCd sxKS) := by
  have hgen : ∀ g : ℕ, rhoCd (ks6_autPerm (g % 6)) ∈ imgCd sxKS ∧
      ActsBy (rhoCd (ks6_autPerm (g % 6))) (ksC6 (g % 6)) := fun g =>
    ⟨rhoCd_mem_imgCd _ (ks6_mem_KS ⟨g % 6, Nat.mod_lt _ (by norm_num)⟩),
      actsBy_ks6 (Nat.mod_lt _ (by norm_num))⟩
  have h := le_card_of_tree (K := imgCd sxKS)
    (fun φ : MulAut W11 => Parab.maskOf 11 (φ (toW 11 8))) ks6Act (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      refine ⟨rhoCd (ks6_autPerm (g % 6)) * φ, Subgroup.mul_mem _ (hgen g).1 hφ, ?_⟩
      have hm := (Parab.maskOf_spec (φ (toW 11 8))).2
      calc Parab.maskOf 11 (rhoCd (ks6_autPerm (g % 6)) (φ (toW 11 8)))
          = Parab.maskOf 11 (rhoCd (ks6_autPerm (g % 6))
              (toW 11 (Parab.maskOf 11 (φ (toW 11 8))))) := by rw [hm]
        _ = ks6Act g (Parab.maskOf 11 (φ (toW 11 8))) := by
            rw [(hgen g).2, Parab.maskOf_toW (actM_lt
              (ksC6_lt _ (Nat.mod_lt _ (by norm_num))) _)]
            rfl)
    ⟨1, Subgroup.one_mem _, Parab.maskOf_toW (by norm_num)⟩ ksTree6_ok
  rwa [ksTree6_length] at h

theorem orderOf_rho_sxZ : orderOf (rhoCd sxZ_autPerm) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : rhoCd sxZ_autPerm ^ 3 = 1 := by
    have : (⟨sxZ, sxZ_autPerm⟩ : ↥AutPerm) ^ 3 = 1 := Subtype.ext (by simpa using sxZ_cube)
    show rhoC11 AutPerm le_rfl _ ^ 3 = 1
    rw [← map_pow, this, map_one]
  refine orderOf_eq_prime h3 fun h => sxZ_ne_one ?_
  have : (⟨sxZ, sxZ_autPerm⟩ : ↥AutPerm) = 1 :=
    rhoC11_injective AutPerm le_rfl (h.trans (map_one _).symm)
  exact congrArg Subtype.val this

theorem le_card_centUS [Finite (MulAut W11)] :
    192 ≤ Nat.card ↥(imgCd sxP0 ⊓ centSub US) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card ↥(imgCd sxP0 ⊓ centSub US) := Nat.card_pos
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 isPGroup_imgCd_KS
  have h64 : 64 ∣ Nat.card ↥(imgCd sxP0 ⊓ centSub US) := by
    have h1 : 2 ^ a ∣ Nat.card ↥(imgCd sxP0 ⊓ centSub US) :=
      ha ▸ Subgroup.card_dvd_of_le imgCd_KS_le
    have h2 : 64 ≤ 2 ^ a := ha ▸ le_card_imgCd_KS
    have h3 : 6 ≤ a := by
      by_contra h
      push Not at h
      have : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (Nat.pow_dvd_pow 2 h3).trans h1
  have h3 : 3 ∣ Nat.card ↥(imgCd sxP0 ⊓ centSub US) := by
    have hz : rhoCd sxZ_autPerm ∈ imgCd sxP0 ⊓ centSub US :=
      ⟨rhoCd_mem_imgCd _ sxZ_mem_P0, sxZ_cent⟩
    have := Subgroup.orderOf_dvd_natCard (imgCd sxP0 ⊓ centSub US) hz
    rwa [orderOf_rho_sxZ] at this
  have h192 : 192 ∣ Nat.card ↥(imgCd sxP0 ⊓ centSub US) :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h3 : 64 * 3 ∣ _)
  exact Nat.le_of_dvd hpos h192

noncomputable instance instCommGroupUS : CommGroup ↥US := Subgroup.toCommGroup (G := W11) US

theorem card_US : Nat.card ↥US = 16 := by
  rw [card_maskSub uSBasis_lt (by decide +kernel)]
  rfl

theorem th_mem : ∀ m ∈ combos uSBasis, toW 6 (actM thC m) ∈ S143.n6Sub := fun m hm =>
  S143.mem_n6Sub_iff.2 ⟨(th_ok m hm).2.2.1, (th_ok m hm).2.2.2.1⟩

@[expose] noncomputable def usTheta : ↥US ≃* S143.N6 :=
  maskEquiv 11 6 uSBasis S143.n6Sub thC uSBasis_lt th_mem
    (fun m hm => ⟨(th_ok m hm).1, (th_ok m hm).2.1⟩) (by rw [S143.n6_card, card_US])

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem s1_alt : s1P ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 sign6.2.2.2.1

theorem s2_alt : s2P ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 sign6.2.2.2.2

theorem rhoOf_eq {g : MulAut W11} (hgs : g ∈ stabSub US) {c : List ℕ} (hg : ActsBy g c)
    (hc : ∀ x ∈ c, x < 2 ^ 11) {s : Equiv.Perm (Fin 6)}
    (h : ∀ m ∈ combos uSBasis, ∀ i : Fin 6, bvec 6 (actM thC (actM c m)) i =
      bvec 6 (actM thC m) (s⁻¹ i) + bvec 6 (actM thC m) (s⁻¹ 5)) :
    B42Alt6.rhoOf usTheta s = resHom US ⟨g, hgs⟩ := by
  refine MulEquiv.ext fun u => usTheta.injective ((B42Alt6.rhoOf_apply usTheta s u).trans ?_)
  obtain ⟨m, hm, hmu⟩ := u.2
  have hgu : ((resHom US ⟨g, hgs⟩ u : ↥US) : W11) = toW 11 (actM c m) := by
    show g (u : W11) = _
    rw [← hmu]
    exact hg m
  have hcm : actM c m ∈ combos uSBasis := by
    have h1 : ((resHom US ⟨g, hgs⟩ u : ↥US) : W11) ∈ US := (resHom US ⟨g, hgs⟩ u).2
    rw [hgu] at h1
    obtain ⟨m', hm'c, he⟩ := h1
    rwa [← toW_inj (combos_lt uSBasis_lt _ hm'c) (actM_lt hc _) he]
  have e1 : ((usTheta (resHom US ⟨g, hgs⟩ u) : S143.N6) : Wn 6) = toW 6 (actM thC (actM c m)) :=
    maskEquiv_apply _ hcm hgu
  have e2 : ((usTheta u : S143.N6) : Wn 6) = toW 6 (actM thC m) := maskEquiv_apply u hm hmu.symm
  refine Subtype.ext (Multiplicative.toAdd.injective (funext fun i => ?_))
  have e3 := S143.n6Act_val s (usTheta u) i
  have e4 : Multiplicative.toAdd ((usTheta (resHom US ⟨g, hgs⟩ u) : S143.N6) :
      Multiplicative (Fin 6 → ZMod 2)) i = bvec 6 (actM thC (actM c m)) i :=
    congrArg (fun w : Wn 6 => Multiplicative.toAdd w i) e1
  have e5 : ∀ j, Multiplicative.toAdd ((usTheta u : S143.N6) : Multiplicative (Fin 6 → ZMod 2)) j =
      bvec 6 (actM thC m) j := fun j => congrArg (fun w : Wn 6 => Multiplicative.toAdd w j) e2
  exact e3.trans ((congrArg₂ (· + ·) (e5 _) (e5 _)).trans ((h m hm i).symm.trans e4.symm))

theorem autSub_le_alt6 :
    autSub (imgCd sxP0) US ≤ (alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta) := by
  set T := (((alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta)).comap (resHom US)).map
    (stabSub US).subtype
  have hT : imgCd sxP0 ≤ T := by
    refine imgCd_closure_le (S := {sxG1, sxG2}) (by
      rintro _ (rfl | rfl)
      · exact sxG1_mem
      · exact sxG2_mem) ?_
    rintro _ (rfl | rfl)
    · refine ⟨⟨rhoCd sxG1_mem, sxG1_stab⟩, ⟨s1P, s1_alt, ?_⟩, rfl⟩
      exact rhoOf_eq sxG1_stab actsBy_sxG1 (fun x hx => sxCols_lt x (List.mem_append_left _ hx))
        fun m hm i => ((th_ok m hm).2.2.2.2 i).1
    · refine ⟨⟨rhoCd sxG2_mem, sxG2_stab⟩, ⟨s2P, s2_alt, ?_⟩, rfl⟩
      exact rhoOf_eq sxG2_stab actsBy_sxG2 (fun x hx => sxCols_lt x (List.mem_append_right _ hx))
        fun m hm i => ((th_ok m hm).2.2.2.2 i).2
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  obtain ⟨g', hg', hgg'⟩ := hT hg
  rw [← show g' = g from Subtype.ext hgg']
  exact hg'

theorem imgCd_le_normalizer {Γ Δ : Subgroup (Equiv.Perm (Fin 24))}
    (h : Γ ≤ Subgroup.normalizer (Δ : Set (Equiv.Perm (Fin 24)))) :
    imgCd Γ ≤ Subgroup.normalizer (imgCd Δ : Set (MulAut W11)) := by
  rintro _ ⟨σ, hσ, rfl⟩
  apply Subgroup.le_normalizer_map
  refine ⟨σ, ?_, rfl⟩
  show σ ∈ Subgroup.normalizer _
  rw [Subgroup.mem_normalizer_iff]
  intro τ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hσ)) τ

theorem lu_code_std
    (hS : Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240) :
    perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) = imgCd sxP0 ∧
      (alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta) = autSub (imgCd sxP0) US ∧
      ⁅imgCd sxP0, imgCd sxP0⁆ = imgCd sxP0 ∧ imgCd sxKS ≤ imgCd sxP0 ∧
      imgCd sxP0 ≤ Subgroup.normalizer (imgCd sxKS : Set (MulAut W11)) ∧
      IsPGroup 2 ↥(imgCd sxKS) ∧ imgCd sxKS ≤ centSub US ∧
      Nat.card ↥(imgCd sxP0 ⊓ centSub US) = 3 * Nat.card ↥(imgCd sxKS) := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := le_card_centUS
  have hCK := card_centUS_mul_le
  have hP0 : Nat.card ↥(imgCd sxP0) = Nat.card ↥sxP0 := card_imgCd sxP0_le
  obtain ⟨hPS, hQc⟩ := perfectCore_stabUSP (card_stabUSP.trans_le hS) (by
    rw [← hP0]
    nlinarith)
  have hA : Nat.card ↥(autSub (imgCd sxP0) US) * Nat.card ↥(imgCd sxP0 ⊓ centSub US) = 69120 :=
    (card_autSub_mul imgCd_P0_le_stab).trans (hP0.trans hQc)
  replace hCK : 360 * Nat.card ↥(imgCd sxP0 ⊓ centSub US) ≤ 69120 := hCK.trans (hP0.trans hQc).le
  have hA360 : 360 ≤ Nat.card ↥(autSub (imgCd sxP0) US) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(autSub (imgCd sxP0) US) * Nat.card ↥(imgCd sxP0 ⊓ centSub US) <
        360 * Nat.card ↥(imgCd sxP0 ⊓ centSub US) :=
      Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  have hcardA : Nat.card ↥((alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta)) = 360 :=
    (Subgroup.card_map_of_injective (B42Alt6.rhoOf_injective usTheta)).trans card_alt6
  have hρ : (alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta) = autSub (imgCd sxP0) US :=
    (Subgroup.eq_of_le_of_card_ge autSub_le_alt6 ((le_of_eq hcardA).trans hA360)).symm
  have hA' : Nat.card ↥(autSub (imgCd sxP0) US) = 360 :=
    (congrArg (fun K : Subgroup (MulAut ↥US) => Nat.card ↥K) hρ).symm.trans hcardA
  rw [hA'] at hA
  have hC192 : Nat.card ↥(imgCd sxP0 ⊓ centSub US) = 192 := by omega
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 isPGroup_imgCd_KS
  have hK64 : Nat.card ↥(imgCd sxKS) = 64 := by
    have h1 : Nat.card ↥(imgCd sxKS) ∣ 192 := hC192 ▸ Subgroup.card_dvd_of_le imgCd_KS_le
    have h2 := le_card_imgCd_KS
    rw [ha] at h1 h2 ⊢
    have h3 : a ≤ 6 := by
      have h1' : 2 ^ a ∣ 2 ^ 6 * 3 := by simpa using h1
      have h4 : 2 ^ a ∣ 2 ^ 6 :=
        Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) h1'
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h4
    have h5 : 6 ≤ a := by
      by_contra h
      push Not at h
      have : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [show a = 6 by omega]
    norm_num
  refine ⟨?_, hρ, commutator_imgCd_P0, imgCd_KS_le_P0,
    imgCd_le_normalizer (sxP0_le_normalizer), isPGroup_imgCd_KS, imgCd_KS_le.trans inf_le_right,
    by rw [hC192, hK64]⟩
  rw [← map_stabUS, ← map_perfectCore]
  have h1 : (perfectCore stabUS).map AutPerm.subtype =
      (sxP0.subgroupOf AutPerm).map AutPerm.subtype := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le sxP0_le]
    exact hPS
  rw [Subgroup.map_injective AutPerm.subtype_injective h1]
  rfl

theorem codCols_eq :
    matOf 11 (actC11 Coc24.pAArr) = codColsA ∧ matOf 11 (actC11 Coc24.pBArr) = codColsB := by
  decide +kernel

theorem card_range_rhoC11 :
    Nat.card ↥(rhoC11 AutPerm le_rfl).range = 244823040 :=
  (Nat.card_congr (MonoidHom.ofInjective (rhoC11_injective AutPerm le_rfl)).toEquiv).symm.trans
    card_AutPerm

theorem card_stab_US_le :
    Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  obtain ⟨hst, hlt, hnd, hlen⟩ := orbCheck_spec Certificates.certificate7260.2.1
  have hmem : ∀ i < [rhoCd bridgePA_mem, rhoCd bridgePB_mem].length,
      [rhoCd bridgePA_mem, rhoCd bridgePB_mem].getD i 1 ∈ (rhoC11 AutPerm le_rfl).range := by
    intro i hi
    rcases i with _ | _ | i
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp at hi
  have hact : ∀ i < [rhoCd bridgePA_mem, rhoCd bridgePB_mem].length,
      ActsBy ([rhoCd bridgePA_mem, rhoCd bridgePB_mem].getD i 1)
        ([codColsA, codColsB].getD i []) := by
    intro i hi
    rcases i with _ | _ | i
    · rw [← codCols_eq.1]
      exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW bridgePA_mem Coc24.hasArr_pA)
    · rw [← codCols_eq.2]
      exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW bridgePB_mem Coc24.hasArr_pB)
    · simp at hi
  have h := card_stab_le_of_orb hmem hact hst hlt hnd
  rw [hlen] at h
  have h' : 1771 * Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 244823040 :=
    h.trans card_range_rhoC11.le
  omega

theorem greedyKS :
    forallGreedy T24s2.invols predKS 6 [] = true :=
  (forallGreedyP_eq pos24s2_eq predKS 6 []).symm.trans
    (forallGreedyAll_le 6 [] Certificates.certificate7260.1 6 le_rfl)

theorem fixV_eq_US
    {V : Type} [CommGroup V]
    [Finite V] {H X : Subgroup (MulAut V)} {e : V ≃* W11}
    (he : H.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) (hX : Nat.card ↥X = 2 ^ 6)
    (hfX : Nat.card ↥(fixV X) = 2 ^ 4) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) :
    ∃ g : ↥AutPerm, fixV (X.map (congrHom (twistEquiv e psiC24 g))) = US := by
  have hXR : X.map (congrHom e) ≤ psiC24.range := by
    have h2 := Subgroup.le_normalizer_map (H := H) (congrHom e)
    have h3 : Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W11)) :
        Set (MulAut W11)) = psiC24.range :=
      (congrArg (fun K : Subgroup (MulAut W11) => Subgroup.normalizer (K : Set (MulAut W11)))
        he).trans normalizer_rhoC11_autPerm
    exact (Subgroup.map_mono hXN).trans (h2.trans h3.le)
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2) greedyKS e
    hXR (isElemAbelian2_iff.2 hXe) hX
  have hact := chainActC24 e g
  have hlen : l.length = 6 := by
    have h := card_of_chainSub hchain (chainAutC24_injective e g) hind
    rw [hX] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfm : (fixMasks 11 codeAct24 l).length = 16 := by
    rw [← card_fixV hact hchain, hfX]
    norm_num
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hU : fixMasks 11 codeAct24 l = uSMasks := by
    have h := hpred
    unfold predKS at h
    rw [codeFixMasks24_eq hinv, hlen, hfm] at h
    simpa using h
  refine ⟨g, ?_⟩
  ext w
  refine (mem_fixV_map_congrHom _ X w).trans ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hv := vm_mem_fixV_iff hact hchain hm
  rw [MaskCoords.ofEquiv_vm] at hv
  refine hv.trans (Iff.trans ?_ (toW_mem_US_iff hm).symm)
  rw [← hU, fixMasks, List.mem_filter, List.mem_range]
  exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩

end CFSG.Quasithin.H.LU24
