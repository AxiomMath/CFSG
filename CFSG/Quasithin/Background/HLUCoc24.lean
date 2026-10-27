module

public import CFSG.Quasithin.Background.HLUCoc24Gen
public import CFSG.Quasithin.Background.HB82Coc24
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.HLUBlocks
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Certificates.Certificate7260
public import CFSG.Quasithin.Background.HMathieuO2Data

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.LU
open scoped commutatorElement

@[expose] def autAdd (φ : MulAut (Wn 3)) : (Fin 3 → ZMod 2) ≃+ (Fin 3 → ZMod 2) where
  toFun v := Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
  invFun v := Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd v))
  left_inv v := by simp
  right_inv v := by simp
  map_add' a b := by
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) = _
    rw [map_mul, toAdd_mul]

@[expose] noncomputable def autLin (φ : MulAut (Wn 3)) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (autAdd φ).toLinearEquiv fun c v => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem autLin_injective : Function.Injective autLin := by
  intro a b h
  refine MulEquiv.ext fun v => ?_
  have h1 : Multiplicative.toAdd (a (Multiplicative.ofAdd (Multiplicative.toAdd v))) =
      Multiplicative.toAdd (b (Multiplicative.ofAdd (Multiplicative.toAdd v))) :=
    congrArg (fun f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) => f (Multiplicative.toAdd v)) h
  exact Multiplicative.toAdd.injective h1

@[expose] noncomputable def autLinHom :
    MulAut (Wn 3) →* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) where
  toFun := autLin
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem card_linEquiv3 : Nat.card ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) = 168 := by
  rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Fin 3 → ZMod 2)).toEquiv,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).toEquiv,
    Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

instance : Finite ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  Finite.of_injective (fun f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) =>
    (f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective

theorem card_mulAut_le : Nat.card (MulAut (Wn 3)) ≤ 168 := by
  rw [← card_linEquiv3]
  exact Nat.card_le_card_of_injective _ autLin_injective

theorem isSimpleGroup_GL32 : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem isSimpleGroup_mulAut (h : 168 ≤ Nat.card (MulAut (Wn 3))) :
    IsSimpleGroup (MulAut (Wn 3)) := by
  have hbij : Function.Bijective autLinHom :=
    (Function.Injective.bijective_of_nat_card_le autLin_injective (card_linEquiv3 ▸ h))
  let e : MulAut (Wn 3) ≃* GL (Fin 3) (ZMod 2) :=
    ((MulEquiv.ofBijective autLinHom hbij).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm).trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).symm
  have := isSimpleGroup_GL32
  exact e.isSimpleGroup

theorem lab_val (x : Fin 24) : ((lab x : Fin 3) : ℕ) = labL.getD x 0 :=
  Nat.mod_eq_of_lt (labL_lt x)

abbrev trioP : Subgroup (Equiv.Perm (Fin 24)) := blockP lab

abbrev trioP0 : Subgroup (Equiv.Perm (Fin 24)) := block0 lab

@[expose] def trRep : Fin 3 → Fin 24 := ![0, 3, 8]

theorem lab_trRep : ∀ i, lab (trRep i) = i := by decide

theorem perfectCore_trioP_le : perfectCore trioP ≤ trioP0 :=
  perfectCore_blockP_le lab_trRep (by norm_num)

theorem mem_trioP_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ x y : Fin 24, (labL.getD a[(x : ℕ)]! 0 = labL.getD a[(y : ℕ)]! 0 ↔
      labL.getD x 0 = labL.getD y 0)) : σ ∈ trioP :=
  mem_blockP_of_arr labL lab_val ha h

theorem mem_trioP0_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ x : Fin 24, labL.getD a[(x : ℕ)]! 0 = labL.getD x 0) : σ ∈ trioP0 :=
  mem_block0_of_arr labL lab_val ha h

@[expose] def t3P : Equiv.Perm (Fin 24) := permOfArr 24 t3Arr t3Inv t_ok.1

@[expose] def t2P : Equiv.Perm (Fin 24) := permOfArr 24 t2Arr t2Inv t_ok.2.1

theorem hasArr_t3 : HasArr t3P t3Arr := hasArr_permOfArr _

theorem hasArr_t3inv : HasArr t3P⁻¹ t3Inv := hasArr_permOfArr_inv _

theorem hasArr_t2 : HasArr t2P t2Arr := hasArr_permOfArr _

theorem hasArr_t2inv : HasArr t2P⁻¹ t2Inv := hasArr_permOfArr_inv _

theorem t3_mem : t3P ∈ AutPerm := mem_AutPerm_of_arr _ t_ok.2.2.1

theorem t2_mem : t2P ∈ AutPerm := mem_AutPerm_of_arr _ t_ok.2.2.2

theorem trA_mem_trioP0 : trA ∈ trioP0 := mem_trioP0_of_arr hasArr_trA fun x => (tr_lab x).1

theorem trB_mem_trioP0 : trB ∈ trioP0 := mem_trioP0_of_arr hasArr_trB fun x => (tr_lab x).2

theorem trQ_le_trioP0 : trQ ≤ trioP0 := by
  rw [trQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact trA_mem_trioP0
  · exact trB_mem_trioP0

theorem t3_mem_trioP : t3P ∈ trioP := mem_trioP_of_arr hasArr_t3 fun x y => (t_lab x y).1

theorem t2_mem_trioP : t2P ∈ trioP := mem_trioP_of_arr hasArr_t2 fun x y => (t_lab x y).2

theorem rho_t3_mem_stabSub : rho11 AutPerm le_rfl ⟨t3P, t3_mem⟩ ∈ stabSub UT := by
  refine mem_stabSub_UT (maps_UT (f := act11 t3Arr)
    (fun m _ => rho11_toW AutPerm le_rfl _ hasArr_t3 m) (fun m _ => act11_lt _ _)
    (fun m hm => (t_pres m (by simp [uTMasks] at hm; omega) hm).1))
    (maps_UT (f := act11 t3Inv) (fun m _ => ?_) (fun m _ => act11_lt _ _)
    (fun m hm => (t_pres m (by simp [uTMasks] at hm; omega) hm).2.1))
  rw [← map_inv]
  exact rho11_toW AutPerm le_rfl (⟨t3P, t3_mem⟩⁻¹ : ↥AutPerm) hasArr_t3inv m

theorem rho_t2_mem_stabSub : rho11 AutPerm le_rfl ⟨t2P, t2_mem⟩ ∈ stabSub UT := by
  refine mem_stabSub_UT (maps_UT (f := act11 t2Arr)
    (fun m _ => rho11_toW AutPerm le_rfl _ hasArr_t2 m) (fun m _ => act11_lt _ _)
    (fun m hm => (t_pres m (by simp [uTMasks] at hm; omega) hm).2.2.1))
    (maps_UT (f := act11 t2Inv) (fun m _ => ?_) (fun m _ => act11_lt _ _)
    (fun m hm => (t_pres m (by simp [uTMasks] at hm; omega) hm).2.2.2))
  rw [← map_inv]
  exact rho11_toW AutPerm le_rfl (⟨t2P, t2_mem⟩⁻¹ : ↥AutPerm) hasArr_t2inv m

@[expose] def twP (i : Fin 6) : Equiv.Perm (Fin 24) := wPerm [t3P, t2P] (twWord i)

theorem hasArr_tw (i : Fin 6) : HasArr (twP i) (wArr [t3Arr, t2Arr] (twWord i)) :=
  hasArr_wPerm (hasArr_getD₂ hasArr_t3 hasArr_t2) _

theorem tw_mem {K : Subgroup (Equiv.Perm (Fin 24))} (h3 : t3P ∈ K) (h2 : t2P ∈ K) (i : Fin 6) :
    twP i ∈ K := by
  refine wPerm_mem (fun p hp => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h3
  · exact h2

theorem tw_distinct (i j : Fin 6) (h : (twP i)⁻¹ * twP j ∈ trioP0) : i = j := by
  apply tw_lab i j
  intro x
  have h2 := eq_of_inv_mul_mem_block0 labL lab_val (tw_mem t3_mem_trioP t2_mem_trioP i) h x
  rw [hasArr_tw, hasArr_tw] at h2
  exact h2.symm

@[expose] def ktP (i : ℕ) : Equiv.Perm (Fin 24) := wPerm [trA, trB] (ktWord i)

theorem hasArr_kt (i : ℕ) : HasArr (ktP i) (wArr [trAArr, trBArr] (ktWord i)) :=
  hasArr_wPerm (hasArr_getD₂ hasArr_trA hasArr_trB) _

theorem kt_mem_Q (i : ℕ) : ktP i ∈ trQ := by
  refine wPerm_mem (fun p hp => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact trA_mem_Q
  · exact trB_mem_Q

@[expose] noncomputable def ktRho (i : ℕ) : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨ktP i, trQ_le (kt_mem_Q i)⟩

theorem ktRho_mem_img (i : ℕ) : ktRho i ∈ img11 trQ :=
  ⟨⟨ktP i, trQ_le (kt_mem_Q i)⟩, Subgroup.mem_subgroupOf.2 (kt_mem_Q i), rfl⟩

theorem ktRho_toW (i m : ℕ) :
    ktRho i (toW 11 m) = toW 11 (act11 (wArr [trAArr, trBArr] (ktWord i)) m) :=
  rho11_toW AutPerm le_rfl _ (hasArr_kt i) m

theorem ktRho_mem_cent {i : ℕ} (hi : i < 6) : ktRho i ∈ centSub UT := by
  rintro _ ⟨m, hm, rfl⟩
  exact (ktRho_toW i m).trans (congrArg (toW 11) ((kt_ok i hi).2 m hm))

theorem actsBy_ktRho {i : ℕ} (hi : i < 6) : ActsBy (ktRho i) (ktCols i) := by
  rw [← (kt_ok i hi).1]
  exact actsBy_of_xorLin (xorLin_act11 _) (ktRho_toW i)

theorem le_card_cent [Finite (MulAut W11)] : 64 ≤ Nat.card ↥(img11 trQ ⊓ centSub UT) := by
  have hgen : ∀ g : ℕ, ktRho (g % 6) ∈ img11 trQ ⊓ centSub UT ∧ ActsBy (ktRho (g % 6))
      (ktCols (g % 6)) := fun g =>
    ⟨⟨ktRho_mem_img _, ktRho_mem_cent (Nat.mod_lt _ (by norm_num))⟩,
      actsBy_ktRho (Nat.mod_lt _ (by norm_num))⟩
  have h := le_card_of_tree (K := img11 trQ ⊓ centSub UT)
    (fun φ : MulAut W11 => Parab.maskOf 11 (φ (toW 11 1))) ktAct (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      refine ⟨ktRho (g % 6) * φ, Subgroup.mul_mem _ (hgen g).1 hφ, ?_⟩
      have hm := (Parab.maskOf_spec (φ (toW 11 1))).2
      calc Parab.maskOf 11 (ktRho (g % 6) (φ (toW 11 1)))
          = Parab.maskOf 11 (ktRho (g % 6) (toW 11 (Parab.maskOf 11 (φ (toW 11 1))))) := by
            rw [hm]
        _ = ktAct g (Parab.maskOf 11 (φ (toW 11 1))) := by
            rw [(hgen g).2, Parab.maskOf_toW (actM_lt
              (ktCols_lt _ (Nat.mod_lt _ (by norm_num))) _)]
            rfl)
    ⟨1, Subgroup.one_mem _, Parab.maskOf_toW (by norm_num)⟩ ktTree_ok
  rwa [ktTree_length] at h

@[expose] noncomputable def rhoTrA : MulAut W11 := rho11 AutPerm le_rfl ⟨trA, trA_mem⟩

@[expose] noncomputable def rhoTrB : MulAut W11 := rho11 AutPerm le_rfl ⟨trB, trB_mem⟩

theorem rhoTrA_mem : rhoTrA ∈ img11 trQ :=
  ⟨⟨trA, trA_mem⟩, Subgroup.mem_subgroupOf.2 trA_mem_Q, rfl⟩

theorem rhoTrB_mem : rhoTrB ∈ img11 trQ :=
  ⟨⟨trB, trB_mem⟩, Subgroup.mem_subgroupOf.2 trB_mem_Q, rfl⟩

theorem actsBy_rhoTrA : ActsBy rhoTrA trACols := by
  rw [← trCols_eq.1]
  exact actsBy_of_xorLin (xorLin_act11 _) (rho11_toW AutPerm le_rfl _ hasArr_trA)

theorem actsBy_rhoTrB : ActsBy rhoTrB trBCols := by
  rw [← trCols_eq.2]
  exact actsBy_of_xorLin (xorLin_act11 _) (rho11_toW AutPerm le_rfl _ hasArr_trB)

theorem uTMasks_lt : ∀ m ∈ uTMasks, m < 2 ^ 11 := by decide

theorem maskOf_mem_UT {φ : MulAut W11} (hφ : φ ∈ stabSub UT) {u : ℕ} (hu : u ∈ uTMasks) :
    Parab.maskOf 11 (φ (toW 11 u)) ∈ uTMasks := by
  have h1 : φ (toW 11 u) ∈ UT := (hφ _).2 ((toW_mem_UT_iff (uTMasks_lt u hu)).2 hu)
  rw [← (Parab.maskOf_spec (φ (toW 11 u))).2] at h1
  exact (toW_mem_UT_iff (Parab.maskOf_spec _).1).1 h1

theorem card_cent_mul_le [Finite (MulAut W11)] :
    168 * Nat.card ↥(img11 trQ ⊓ centSub UT) ≤ Nat.card ↥(img11 trQ) := by
  have hstab : img11 trQ ≤ stabSub UT := img11_trQ_le.trans inf_le_right
  have hgen : ∀ g : ℕ, ∃ ρ ∈ img11 trQ, ActsBy ρ (if g = 0 then trACols else trBCols) := by
    intro g
    by_cases hg : g = 0
    · rw [ite_eq_left hg]
      exact ⟨_, rhoTrA_mem, actsBy_rhoTrA⟩
    · rw [ite_eq_right hg]
      exact ⟨_, rhoTrB_mem, actsBy_rhoTrB⟩
  have hlt : ∀ g : ℕ, ∀ x ∈ (if g = 0 then trACols else trBCols), x < 2 ^ 11 := by
    intro g x hx
    split_ifs at hx
    · exact trCols_lt x (List.mem_append_left _ hx)
    · exact trCols_lt x (List.mem_append_right _ hx)
  have hus : ∀ u ∈ uTBasis, u ∈ uTMasks := by decide
  have h := card_mul_le_of_tree (K := img11 trQ) (C := img11 trQ ⊓ centSub UT) inf_le_left
    (tupKey 11 3 trD uTBasis) (fun φ _ ψ hψ => tupKey_mul_fix uTBasis fun u hu =>
      hψ.2 _ ((toW_mem_UT_iff (uTMasks_lt u (hus u hu))).2 (hus u hu)))
    trAct (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      obtain ⟨ρ, hρ, hρa⟩ := hgen g
      exact ⟨ρ * φ, Subgroup.mul_mem _ hρ hφ, tupKey_mul hρa (hlt g) (fun m hm => trD_ok m hm)
        uTBasis fun u hu => maskOf_mem_UT (hstab hφ) (hus u hu)⟩)
    ⟨1, Subgroup.one_mem _, by
      rw [tupKey_one uTBasis fun u hu => uTMasks_lt u (hus u hu), trStart]⟩ trTree_ok
  rwa [trTree_length] at h

theorem uT_h0 : ∀ m ∈ combos uTBasis, actM trD m < 2 ^ 3 ∧ (actM trD m = 0 → m = 0) := by
  decide +kernel

theorem card_UT : Nat.card ↥UT = 8 := by
  rw [card_maskSub uTBasis_lt (by decide +kernel)]
  rfl

@[expose] noncomputable def utEquiv : ↥UT ≃* Wn 3 :=
  (maskEquiv 11 3 uTBasis ⊤ trD uTBasis_lt (fun _ _ => Subgroup.mem_top _) uT_h0
    (by rw [Subgroup.card_top, natCard_Wn, card_UT]; norm_num)).trans Subgroup.topEquiv

theorem card_mulAut_UT : Nat.card (MulAut ↥UT) = Nat.card (MulAut (Wn 3)) :=
  Nat.card_congr (MulAut.congr utEquiv).toEquiv

@[expose] noncomputable def stabUT : Subgroup ↥AutPerm :=
  (stabSub UT).comap (rho11 AutPerm le_rfl)

theorem map_stabUT : stabUT.map (rho11 AutPerm le_rfl) = img11 AutPerm ⊓ stabSub UT :=
  (Subgroup.map_comap_eq (rho11 AutPerm le_rfl) (stabSub UT)).trans
    (congrArg (· ⊓ stabSub UT) (range_rho11_eq_img11 AutPerm le_rfl))

@[expose] noncomputable def stabUTP : Subgroup (Equiv.Perm (Fin 24)) := stabUT.map AutPerm.subtype

theorem mem_stabUTP {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    (h : rho11 AutPerm le_rfl ⟨σ, hσ⟩ ∈ stabSub UT) : σ ∈ stabUTP :=
  ⟨⟨σ, hσ⟩, h, rfl⟩

theorem card_stabUTP :
    Nat.card ↥stabUTP = Nat.card ↥(img11 AutPerm ⊓ stabSub UT) := by
  rw [← map_stabUT, stabUTP, Subgroup.card_map_of_injective AutPerm.subtype_injective,
    Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl)]

theorem trQ_le_stabUTP : trQ ≤ stabUTP := by
  rw [trQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_stabUTP trA_mem rho_trA_mem_stabSub
  · exact mem_stabUTP trB_mem rho_trB_mem_stabSub

@[expose] def genT : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {trA, trB, t3P, t2P}

theorem genT_le : genT ≤ stabUTP ⊓ trioP := by
  rw [genT, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact ⟨mem_stabUTP trA_mem rho_trA_mem_stabSub, block0_le lab trA_mem_trioP0⟩
  · exact ⟨mem_stabUTP trB_mem rho_trB_mem_stabSub, block0_le lab trB_mem_trioP0⟩
  · exact ⟨mem_stabUTP t3_mem rho_t3_mem_stabSub, t3_mem_trioP⟩
  · exact ⟨mem_stabUTP t2_mem rho_t2_mem_stabSub, t2_mem_trioP⟩

theorem trQ_le_genT : trQ ≤ genT := by
  rw [trQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem tw_mem_genT (i : Fin 6) : twP i ∈ genT :=
  tw_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) i

theorem perfectCore_stabUTP (hS : Nat.card ↥stabUTP ≤ 64512) (hQ : 10752 ≤ Nat.card ↥trQ) :
    perfectCore stabUTP = trQ ∧ Nat.card ↥trQ = 10752 := by
  have h1 : 6 * Nat.card ↥trQ ≤ Nat.card ↥genT :=
    mul_card_le_of_cosets trQ_le_genT twP tw_mem_genT
      fun i j h => tw_distinct i j (trQ_le_trioP0 h)
  have heq : genT = stabUTP :=
    Subgroup.eq_of_le_of_card_ge (genT_le.trans inf_le_left) (by omega)
  have hΩ : stabUTP ≤ trioP := heq ▸ genT_le.trans inf_le_right
  have hP : perfectCore stabUTP ≤ trioP0 := (perfectCore_mono hΩ).trans perfectCore_trioP_le
  have h2 : 6 * Nat.card ↥(trioP0 ⊓ stabUTP) ≤ Nat.card ↥stabUTP :=
    mul_card_le_of_cosets inf_le_right twP (fun i => heq ▸ tw_mem_genT i)
      fun i j h => tw_distinct i j h.1
  have hQle : trQ ≤ trioP0 ⊓ stabUTP := le_inf trQ_le_trioP0 trQ_le_stabUTP
  have hQeq : trQ = trioP0 ⊓ stabUTP := Subgroup.eq_of_le_of_card_ge hQle (by omega)
  refine ⟨le_antisymm ?_ (le_perfectCore_of_perfect trQ_le_stabUTP commutator_trQ), ?_⟩
  · rw [hQeq]
    exact le_inf hP (perfectCore_le _)
  · have := congrArg (fun K : Subgroup (Equiv.Perm (Fin 24)) => Nat.card ↥K) hQeq
    omega

theorem card_img11_trQ :
    Nat.card ↥(img11 trQ) = Nat.card ↥trQ := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe trQ_le).toEquiv]

theorem not_comm_autSub {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)} {U : Subgroup V}
    {g h : MulAut V} (hg : g ∈ X) (hh : h ∈ X) (hgs : g ∈ stabSub U) (hhs : h ∈ stabSub U)
    {u : V} (hu : u ∈ U) (hne : g (h u) ≠ h (g u)) : ∃ a b : ↥(autSub X U), a * b ≠ b * a := by
  refine ⟨⟨resHom U ⟨g, hgs⟩, mem_autSub.2 ⟨_, hg, rfl⟩⟩,
    ⟨resHom U ⟨h, hhs⟩, mem_autSub.2 ⟨_, hh, rfl⟩⟩, fun hc => hne ?_⟩
  have h1 := congrArg (fun φ : ↥(autSub X U) => ((φ.1 ⟨u, hu⟩ : ↥U) : V)) hc
  exact h1

theorem rho_ab_39 :
    actM trACols (actM trBCols 39) = 1192 ∧ actM trBCols (actM trACols 39) = 1167 := by
  decide +kernel

theorem lu_coc_std
    (hS : Nat.card ↥(img11 AutPerm ⊓ stabSub UT) ≤ 64512) :
    perfectCore (img11 AutPerm ⊓ stabSub UT) = img11 trQ ∧ autSub (img11 trQ) UT = ⊤ ∧
      IsSimpleGroup ↥(autSub (img11 trQ) UT) ∧
      (∃ a b : ↥(autSub (img11 trQ) UT), a * b ≠ b * a) ∧
      IsPGroup 2 ↥(img11 trQ ⊓ centSub UT) := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have : Finite (MulAut ↥UT) :=
    Finite.of_injective (fun f : MulAut ↥UT => (f : ↥UT → ↥UT)) DFunLike.coe_injective
  have hC64 := le_card_cent
  have hCK := card_cent_mul_le
  have hQ : 10752 ≤ Nat.card ↥trQ := by
    rw [← card_img11_trQ]
    omega
  obtain ⟨hPS, hQc⟩ := perfectCore_stabUTP (card_stabUTP.trans_le hS) hQ
  have hstab : img11 trQ ≤ stabSub UT := img11_trQ_le.trans inf_le_right
  have hA : Nat.card ↥(autSub (img11 trQ) UT) * Nat.card ↥(img11 trQ ⊓ centSub UT) = 10752 :=
    (card_autSub_mul hstab).trans (card_img11_trQ.trans hQc)
  replace hCK : 168 * Nat.card ↥(img11 trQ ⊓ centSub UT) ≤ 10752 :=
    hCK.trans (card_img11_trQ.trans hQc).le
  have hA168 : 168 ≤ Nat.card ↥(autSub (img11 trQ) UT) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(autSub (img11 trQ) UT) * Nat.card ↥(img11 trQ ⊓ centSub UT) <
        168 * Nat.card ↥(img11 trQ ⊓ centSub UT) :=
      Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  have hAut : Nat.card (MulAut ↥UT) ≤ 168 := card_mulAut_UT ▸ card_mulAut_le
  have htop : autSub (img11 trQ) UT = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).1 (le_antisymm (Subgroup.card_le_card_group _)
      (hAut.trans hA168))
  have hA' : Nat.card ↥(autSub (img11 trQ) UT) = 168 :=
    le_antisymm ((Subgroup.card_le_card_group _).trans hAut) hA168
  refine ⟨?_, htop, ?_, ?_, ?_⟩
  · rw [← map_stabUT, ← map_perfectCore]
    have h1 : (perfectCore stabUT).map AutPerm.subtype = (trQ.subgroupOf AutPerm).map
        AutPerm.subtype := by
      rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le trQ_le]
      exact hPS
    rw [Subgroup.map_injective AutPerm.subtype_injective h1]
    rfl
  · have h168 : 168 ≤ Nat.card (MulAut (Wn 3)) := card_mulAut_UT ▸ hA'.symm.le.trans
      (Subgroup.card_le_card_group _)
    have := isSimpleGroup_mulAut h168
    let e : ↥(autSub (img11 trQ) UT) ≃* MulAut (Wn 3) :=
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans (MulAut.congr utEquiv)
    exact e.isSimpleGroup
  · refine not_comm_autSub rhoTrA_mem rhoTrB_mem (hstab rhoTrA_mem) (hstab rhoTrB_mem)
      ((toW_mem_UT_iff (m := 39) (by norm_num)).2 (by decide)) fun h => ?_
    have h2 : toW 11 (actM trACols (actM trBCols 39)) = toW 11 (actM trBCols (actM trACols 39)) :=
      (actsBy_rhoTrA _).symm.trans ((congrArg rhoTrA (actsBy_rhoTrB 39)).symm.trans
        (h.trans ((congrArg rhoTrB (actsBy_rhoTrA 39)).trans (actsBy_rhoTrB _))))
    rw [rho_ab_39.1, rho_ab_39.2] at h2
    exact absurd (toW_inj (by norm_num) (by norm_num) h2) (by norm_num)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hA'] at hA
    exact IsPGroup.of_card (n := 6) (by omega)

theorem cocCols_eq : matOf 11 (act11 pAArr) = CFSG.Quasithin.H.LU24.cocColsA ∧
    matOf 11 (act11 pBArr) = CFSG.Quasithin.H.LU24.cocColsB := by
  decide +kernel

theorem card_stab_UT_le :
    Nat.card ↥(img11 AutPerm ⊓ stabSub UT) ≤ 64512 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  obtain ⟨hst, hlt, hnd, hlen⟩ :=
    CFSG.Quasithin.H.LU24.orbCheck_spec Certificates.certificate7260.2.2
  set rA : MulAut W11 := rho11 AutPerm le_rfl ⟨bridgePA, bridgePA_mem⟩
  set rB : MulAut W11 := rho11 AutPerm le_rfl ⟨bridgePB, bridgePB_mem⟩
  have hmem : ∀ i < [rA, rB].length, [rA, rB].getD i 1 ∈ img11 AutPerm := by
    intro i hi
    rcases i with _ | _ | i
    · exact rho11_mem_img11 _
    · exact rho11_mem_img11 _
    · simp at hi
  have hact : ∀ i < [rA, rB].length, ActsBy ([rA, rB].getD i 1)
      ([CFSG.Quasithin.H.LU24.cocColsA, CFSG.Quasithin.H.LU24.cocColsB].getD i []) := by
    intro i hi
    rcases i with _ | _ | i
    · rw [← cocCols_eq.1]
      exact actsBy_of_xorLin (xorLin_act11 pAArr) (rho11_toW AutPerm le_rfl _ hasArr_pA)
    · rw [← cocCols_eq.2]
      exact actsBy_of_xorLin (xorLin_act11 pBArr) (rho11_toW AutPerm le_rfl _ hasArr_pB)
    · simp at hi
  have h := card_stab_le_of_orb hmem hact hst hlt hnd
  rw [hlen] at h
  have h' : 3795 * Nat.card ↥(img11 AutPerm ⊓ stabSub UT) ≤ 244823040 :=
    h.trans card_img11_autPerm.le
  omega

end CFSG.Quasithin.H.Coc24
