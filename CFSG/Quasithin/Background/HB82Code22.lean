module

public import CFSG.Quasithin.Background.HB82Code22Gen
public import CFSG.Quasithin.Background.HB82Base
public import CFSG.Quasithin.Background.HZCode22B

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu.H16Pf
open scoped commutatorElement

abbrev UC : Subgroup W10 := maskSub 10 hbU0Basis

theorem toW_mem_UC_iff {m : ℕ} (hm : m < 2 ^ 10) : (toW 10 m : W10) ∈ UC ↔ m ∈ hbU0Masks := by
  rw [← hb_combos m hm]
  constructor
  · rintro ⟨m', hm', he⟩
    rwa [← toW_inj (combos_lt hbU0Basis_lt _ hm') hm he]
  · intro h
    exact toW_mem_maskSub h

theorem maps_UC {g : MulAut W10} {f : ℕ → ℕ} (hg : ∀ m < 2 ^ 10, g (toW 10 m) = toW 10 (f m))
    (hlt : ∀ m < 2 ^ 10, f m < 2 ^ 10) (hf : ∀ m ∈ hbU0Masks, f m ∈ hbU0Masks) :
    ∀ u ∈ UC, g u ∈ UC := by
  rintro _ ⟨m, hm, rfl⟩
  have hm' : m < 2 ^ 10 := combos_lt hbU0Basis_lt _ hm
  rw [hg m hm']
  exact toW_mem_maskSub ((hb_combos _ (hlt m hm')).2 (hf m ((hb_combos m hm').1 hm)))

@[expose] def hbA : Equiv.Perm (Fin 24) := permOfArr 24 hbAArr hbAInv hb_ok.1

@[expose] def hbB : Equiv.Perm (Fin 24) := permOfArr 24 hbBArr hbBInv hb_ok.2.1

@[expose] def hbH : Equiv.Perm (Fin 24) := permOfArr 24 hbHArr hbHInv hb_ok.2.2.1

theorem hasArr_hbA : HasArr hbA hbAArr := hasArr_permOfArr _

theorem hasArr_hbAinv : HasArr hbA⁻¹ hbAInv := hasArr_permOfArr_inv _

theorem hasArr_hbB : HasArr hbB hbBArr := hasArr_permOfArr _

theorem hasArr_hbBinv : HasArr hbB⁻¹ hbBInv := hasArr_permOfArr_inv _

theorem hasArr_hbH : HasArr hbH hbHArr := hasArr_permOfArr _

theorem hasArr_hbHinv : HasArr hbH⁻¹ hbHInv := hasArr_permOfArr_inv _

theorem hbA_mem : hbA ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ hb_ok.2.2.2.1) hasArr_hbA hb_ok.2.2.2.2.2.2.1
    hb_ok.2.2.2.2.2.2.2.1

theorem hbB_mem : hbB ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ hb_ok.2.2.2.2.1) hasArr_hbB hb_ok.2.2.2.2.2.2.2.2.1
    hb_ok.2.2.2.2.2.2.2.2.2.1

theorem hbH_mem : hbH ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr _ hb_ok.2.2.2.2.2.1) hasArr_hbH
    hb_ok.2.2.2.2.2.2.2.2.2.2.1 hb_ok.2.2.2.2.2.2.2.2.2.2.2

@[expose] def hbQ : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {hbA, hbB}

theorem hbA_mem_Q : hbA ∈ hbQ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem hbB_mem_Q : hbB ∈ hbQ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem hbQ_le : hbQ ≤ mog22 := by
  rw [hbQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact hbA_mem
  · exact hbB_mem

theorem hasArr_hbC0 : HasArr ⁅hbA, hbB⁆ hbC0Arr := by
  rw [commutatorElement_def, mul_assoc (hbA * hbB)]
  exact hasArr_mul (hasArr_mul hasArr_hbA hasArr_hbB) (hasArr_mul hasArr_hbAinv hasArr_hbBinv)

theorem hasArr_hbC1 : HasArr ⁅hbA, hbA * hbB⁆ hbC1Arr := by
  rw [commutatorElement_def, mul_inv_rev, mul_assoc (hbA * (hbA * hbB))]
  exact hasArr_mul (hasArr_mul hasArr_hbA (hasArr_mul hasArr_hbA hasArr_hbB))
    (hasArr_mul hasArr_hbAinv (hasArr_mul hasArr_hbBinv hasArr_hbAinv))

theorem commutator_hbQ : ⁅hbQ, hbQ⁆ = hbQ := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact hbQ.mul_mem (hbQ.mul_mem (hbQ.mul_mem hx hy) (hbQ.inv_mem hx)) (hbQ.inv_mem hy)) ?_
  have hc : ∀ p ∈ [⁅hbA, hbB⁆, ⁅hbA, hbA * hbB⁆], p ∈ ⁅hbQ, hbQ⁆ := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Subgroup.commutator_mem_commutator hbA_mem_Q hbB_mem_Q
    · exact Subgroup.commutator_mem_commutator hbA_mem_Q (hbQ.mul_mem hbA_mem_Q hbB_mem_Q)
  have hw := hasArr_wPerm (Coc24.hasArr_getD₂ hasArr_hbC0 hasArr_hbC1)
  show Subgroup.closure ({hbA, hbB} : Set (Equiv.Perm (Fin 24))) ≤ ⁅hbQ, hbQ⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h := hw hbAWord
    rw [hb_perfect.1] at h
    have hx := perm_eq_of_hasArr hasArr_hbA h
    exact hx ▸ wPerm_mem hc _
  · have h := hw hbBWord
    rw [hb_perfect.2] at h
    have hy := perm_eq_of_hasArr hasArr_hbB h
    exact hy ▸ wPerm_mem hc _

theorem commutator_imgC_hbQ : ⁅imgC hbQ, imgC hbQ⁆ = imgC hbQ := by
  have h : ⁅hbQ.subgroupOf mog22, hbQ.subgroupOf mog22⁆ = hbQ.subgroupOf mog22 := by
    apply Subgroup.map_injective mog22.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hbQ_le, commutator_hbQ]
  rw [imgC, ← Subgroup.map_commutator, h]

theorem rho_hbA_mem_stabSub : rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ ∈ stabSub UC := by
  have hinv : ∀ m < 2 ^ 10, (rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩)⁻¹ (toW 10 m) =
      toW 10 (actC10 hbAInv m) := fun m _ => by
    rw [← map_inv]
    exact rhoC10_toW mog22 mog22_le_mog22plus (⟨hbA, hbA_mem⟩⁻¹ : ↥mog22) hasArr_hbAinv m
  exact mem_stabSub_of_maps (maps_UC (f := actC10 hbAArr)
    (fun m _ => rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_hbA m) (fun m _ => actC10_lt _ _)
    (fun m hm => (hb_pres m hm).1)) (maps_UC hinv (fun m _ => actC10_lt _ _)
    (fun m hm => (hb_pres m hm).2.2.1))

theorem rho_hbB_mem_stabSub : rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ ∈ stabSub UC := by
  have hinv : ∀ m < 2 ^ 10, (rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩)⁻¹ (toW 10 m) =
      toW 10 (actC10 hbBInv m) := fun m _ => by
    rw [← map_inv]
    exact rhoC10_toW mog22 mog22_le_mog22plus (⟨hbB, hbB_mem⟩⁻¹ : ↥mog22) hasArr_hbBinv m
  exact mem_stabSub_of_maps (maps_UC (f := actC10 hbBArr)
    (fun m _ => rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_hbB m) (fun m _ => actC10_lt _ _)
    (fun m hm => (hb_pres m hm).2.1)) (maps_UC hinv (fun m _ => actC10_lt _ _)
    (fun m hm => (hb_pres m hm).2.2.2))

theorem imgC_hbQ_le : imgC hbQ ≤ imgC mog22 ⊓ stabSub UC := by
  refine le_inf (Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2) ?_
  have hQ : hbQ ≤ ((stabSub UC).comap (rhoC10 mog22 mog22_le_mog22plus)).map mog22.subtype := by
    rw [hbQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨hbA, hbA_mem⟩, rho_hbA_mem_stabSub, rfl⟩
    · exact ⟨⟨hbB, hbB_mem⟩, rho_hbB_mem_stabSub, rfl⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := hQ (Subgroup.mem_subgroupOf.1 hσ)
  rw [show σ = τ from Subtype.ext hτσ.symm]
  exact hτ

@[expose] noncomputable def rhoH : MulAut W10 :=
  rhoC10 mog22 mog22_le_mog22plus ⟨hbH, hbH_mem⟩

theorem rhoH_mem : rhoH ∈ imgC mog22 := rhoC10_mem_imgC _

theorem rhoH_toW (m : ℕ) : rhoH (toW 10 m) = toW 10 (actC10 hbHArr m) :=
  rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_hbH m

@[expose] noncomputable def KOh : Subgroup (MulAut W10) := (imgC fixO).map (congrHom rhoH)

theorem conj_koRho_toW (t : Fin 16) (m : ℕ) :
    (rhoH * koRho t * rhoH⁻¹) (toW 10 m) =
      toW 10 (actC10 (cArr hbHArr (cArr (koArr t) hbHInv)) m) := by
  have hc : HasArr (hbH * koPerm t * hbH⁻¹) (cArr hbHArr (cArr (koArr t) hbHInv)) := by
    rw [mul_assoc]
    exact hasArr_mul hasArr_hbH (hasArr_mul (hasArr_koPerm t) hasArr_hbHinv)
  have hm : hbH * koPerm t * hbH⁻¹ ∈ mog22 :=
    mog22.mul_mem (mog22.mul_mem hbH_mem (koPerm_mem_mog22 t)) (mog22.inv_mem hbH_mem)
  have e : rhoH * koRho t * rhoH⁻¹ =
      rhoC10 mog22 mog22_le_mog22plus ⟨hbH * koPerm t * hbH⁻¹, hm⟩ := by
    rw [rhoH, koRho, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact rhoC10_toW mog22 mog22_le_mog22plus _ hc m

theorem KOh_le : KOh ≤ imgC mog22 ⊓ stabSub UC := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨t, rfl⟩ := mem_imgC_fixO.1 hφ
  show rhoH * koRho t * rhoH⁻¹ ∈ imgC mog22 ⊓ stabSub UC
  refine ⟨(imgC mog22).mul_mem ((imgC mog22).mul_mem rhoH_mem
    (imgC_fixO_le (koRho_mem_imgC_fixO t))) ((imgC mog22).inv_mem rhoH_mem), ?_⟩
  have hinv : ∀ m < 2 ^ 10, (rhoH * koRho t * rhoH⁻¹)⁻¹ (toW 10 m) =
      toW 10 (actC10 (cArr hbHArr (cArr (koArr t) hbHInv)) m) := fun m _ => by
    have h2 : koRho t * koRho t = 1 := by
      rw [koRho_mul, show (⟨(t : ℕ) ^^^ (t : ℕ), Nat.xor_lt_two_pow (n := 4) t.2 t.2⟩ : Fin 16)
        = 0 from Fin.ext (Nat.xor_self _), koRho_zero]
    have hk : (koRho t)⁻¹ = koRho t := inv_eq_of_mul_eq_one_right h2
    have e : (rhoH * koRho t * rhoH⁻¹)⁻¹ = rhoH * koRho t * rhoH⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hk, mul_assoc]
    rw [e]
    exact conj_koRho_toW t m
  exact mem_stabSub_of_maps (maps_UC (f := actC10 (cArr hbHArr (cArr (koArr t) hbHInv)))
    (fun m _ => conj_koRho_toW t m) (fun m _ => actC10_lt _ _) (hb_ko_pres t t.2))
    (maps_UC hinv (fun m _ => actC10_lt _ _) (hb_ko_pres t t.2))

theorem isPGroup_KOh : IsPGroup 2 ↥KOh := isPGroup_imgC_fixO.map _

theorem fix_KOh (w : W10) (hw : w ∈ fixV KOh) : w = 1 ∨ w = toW 10 209 := by
  have h1 : rhoH⁻¹ w ∈ fixV (imgC fixO) := by
    intro φ hφ
    have h2 : rhoH (φ ((rhoH⁻¹ : MulAut W10) w)) = w := hw _ ⟨φ, hφ, rfl⟩
    have h3 := congrArg (rhoH⁻¹ : MulAut W10) h2
    rwa [MulAut.inv_apply_self] at h3
  have hz : rhoH z0 = toW 10 209 := by
    rw [rhoH_toW, hbH_z]
  rcases fix_imgC_fixO _ h1 with h | h
  · left
    have := congrArg rhoH h
    rwa [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, map_one] at this
  · right
    have := congrArg rhoH h
    rwa [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, hz] at this

theorem vZ_z2 :
    vZ (imgC mog22) (toW 10 209) = W0.map rhoH.toMonoidHom := by
  have h1 := vZ_map rhoH (imgC mog22) z0
  have hH : (imgC mog22).map (congrHom rhoH) = imgC mog22 := map_congrHom_self rhoH_mem
  have hz : rhoH z0 = toW 10 209 := by
    rw [rhoH_toW, hbH_z]
  have key : ∀ (A : Subgroup (MulAut W10)) (w : W10), A = imgC mog22 → w = toW 10 209 →
      vZ A w = vZ (imgC mog22) (toW 10 209) := by
    rintro A w rfl rfl
    rfl
  exact (key _ _ hH hz).symm.trans (h1.symm.trans (congrArg (·.map rhoH.toMonoidHom) vZ_std))

theorem toW_mem_commV_hbQ {m : ℕ}
    (hm : m ∈ combos (hbCvData.map fun e => hbLAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2)) :
    toW 10 m ∈ commV (imgC hbQ) := by
  refine mem_of_combos (fun m => toW 10 m ∈ commV (imgC hbQ)) ?_ ?_ _ ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    obtain ⟨⟨g, j⟩, -, rfl⟩ := List.mem_map.1 ha
    by_cases hg : g = 0
    · have hx : rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ ∈ imgC hbQ :=
        ⟨⟨hbA, hbA_mem⟩, Subgroup.mem_subgroupOf.2 hbA_mem_Q, rfl⟩
      have h := mem_commV hx (toW 10 (2 ^ j))
      have e1 : toW 10 (hbLAct g (2 ^ j) ^^^ 2 ^ j) =
          rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ (toW 10 (2 ^ j)) *
            (toW 10 (2 ^ j))⁻¹ := by
        rw [rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_hbA, toW_inv, toW_xor, hbLAct,
          ite_eq_left hg]
      show toW 10 (hbLAct g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h
    · have hx : rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ ∈ imgC hbQ :=
        ⟨⟨hbB, hbB_mem⟩, Subgroup.mem_subgroupOf.2 hbB_mem_Q, rfl⟩
      have h := mem_commV hx (toW 10 (2 ^ j))
      have e1 : toW 10 (hbLAct g (2 ^ j) ^^^ 2 ^ j) =
          rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ (toW 10 (2 ^ j)) *
            (toW 10 (2 ^ j))⁻¹ := by
        rw [rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_hbB, toW_inv, toW_xor, hbLAct,
          ite_eq_right hg]
      show toW 10 (hbLAct g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h

theorem vZ_z2_le :
    vZ (imgC mog22) (toW 10 209) ≤ commV (imgC hbQ) := by
  rw [vZ_z2]
  rintro _ ⟨w, ⟨m, hm, rfl⟩, rfl⟩
  show rhoH (toW 10 m) ∈ _
  refine mem_of_combos (fun m => rhoH (toW 10 m) ∈ commV (imgC hbQ)) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero, map_one]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor, map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    show rhoH (toW 10 a) ∈ _
    rw [rhoH_toW]
    refine toW_mem_commV_hbQ (hb_w1_mem _ ?_)
    rw [← hbW1_eq]
    exact List.mem_map_of_mem ha

theorem not_vZ_z2_le :
    ¬ vZ (imgC mog22) (toW 10 209) ≤ UC := by
  rw [vZ_z2]
  intro h
  have hm := h ⟨toW 10 _, toW_mem_maskSub hb_notin.1, rfl⟩
  have e : rhoH.toMonoidHom (toW 10 7) = toW 10 (actC10 hbHArr 7) := rhoH_toW _
  have hm2 : (toW 10 (actC10 hbHArr 7) : W10) ∈ UC := (congrArg (· ∈ UC) e).mp hm
  exact hb_notin.2 ((toW_mem_UC_iff (actC10_lt _ _)).1 hm2)

theorem hbConcl_std
    {X : Subgroup (MulAut W10)} (hX : fixV X = UC) {z : W10} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut W10)} (hSH : S ≤ imgC mog22 ⊓ stabSub UC)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥(imgC mog22)).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl (imgC mog22) X z :=
  hbConcl_of_std KOh_le isPGroup_KOh fix_KOh imgC_hbQ_le commutator_imgC_hbQ vZ_z2_le
    not_vZ_z2_le hX hz1 hSH hS hzS

end CFSG.Quasithin.H.Code22
