module

public import CFSG.Quasithin.Background.HB82Coc24Gen
public import CFSG.Quasithin.Background.HB82Base
public import CFSG.Quasithin.Background.HZCoc24C
public import Certificates.Certificate7247

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

abbrev UT : Subgroup W11 := maskSub 11 uTBasis

theorem toW_mem_UT_iff {m : ℕ} (hm : m < 2 ^ 11) : (toW 11 m : W11) ∈ UT ↔ m ∈ uTMasks := by
  rw [← uT_combos m hm]
  constructor
  · rintro ⟨m', hm', he⟩
    rwa [← toW_inj (combos_lt uTBasis_lt _ hm') hm he]
  · intro h
    exact toW_mem_maskSub h

theorem mem_stabSub_UT {g : MulAut W11} (hg : ∀ u ∈ UT, g u ∈ UT) (hg' : ∀ u ∈ UT, g⁻¹ u ∈ UT) :
    g ∈ stabSub UT := by
  intro u
  constructor
  · intro h
    have h2 := hg' (g u) h
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h2
  · exact hg u

theorem maps_UT {g : MulAut W11} {f : ℕ → ℕ} (hg : ∀ m < 2 ^ 11, g (toW 11 m) = toW 11 (f m))
    (hlt : ∀ m < 2 ^ 11, f m < 2 ^ 11) (hf : ∀ m ∈ uTMasks, f m ∈ uTMasks) :
    ∀ u ∈ UT, g u ∈ UT := by
  rintro _ ⟨m, hm, rfl⟩
  have hm' : m < 2 ^ 11 := combos_lt uTBasis_lt _ hm
  rw [hg m hm']
  exact toW_mem_maskSub ((uT_combos _ (hlt m hm')).2 (hf m ((uT_combos m hm').1 hm)))

@[expose] def trA : Equiv.Perm (Fin 24) := permOfArr 24 trAArr trAInv tr_ok.1

@[expose] def trB : Equiv.Perm (Fin 24) := permOfArr 24 trBArr trBInv tr_ok.2.1

@[expose] def trH : Equiv.Perm (Fin 24) := permOfArr 24 trHArr trHInv tr_ok.2.2.1

theorem hasArr_trA : HasArr trA trAArr := hasArr_permOfArr _

theorem hasArr_trAinv : HasArr trA⁻¹ trAInv := hasArr_permOfArr_inv _

theorem hasArr_trB : HasArr trB trBArr := hasArr_permOfArr _

theorem hasArr_trBinv : HasArr trB⁻¹ trBInv := hasArr_permOfArr_inv _

theorem hasArr_trH : HasArr trH trHArr := hasArr_permOfArr _

theorem trA_mem : trA ∈ AutPerm := mem_AutPerm_of_arr _ tr_ok.2.2.2.1

theorem trB_mem : trB ∈ AutPerm := mem_AutPerm_of_arr _ tr_ok.2.2.2.2.1

theorem trH_mem : trH ∈ AutPerm := mem_AutPerm_of_arr _ tr_ok.2.2.2.2.2

@[expose] def trQ : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {trA, trB}

theorem trA_mem_Q : trA ∈ trQ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem trB_mem_Q : trB ∈ trQ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem trQ_le : trQ ≤ AutPerm := by
  rw [trQ, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact trA_mem
  · exact trB_mem

theorem hasArr_trC0 : HasArr ⁅trA, trB⁆ trC0Arr := by
  rw [commutatorElement_def, mul_assoc (trA * trB)]
  exact hasArr_mul (hasArr_mul hasArr_trA hasArr_trB) (hasArr_mul hasArr_trAinv hasArr_trBinv)

theorem hasArr_trC1 : HasArr ⁅trA, trA * (trB * trB)⁆ trC1Arr := by
  rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, mul_assoc (trA * (trA * (trB * trB)))]
  exact hasArr_mul
    (hasArr_mul hasArr_trA (hasArr_mul hasArr_trA (hasArr_mul hasArr_trB hasArr_trB)))
    (hasArr_mul hasArr_trAinv (hasArr_mul (hasArr_mul hasArr_trBinv hasArr_trBinv) hasArr_trAinv))

theorem commutator_trQ : ⁅trQ, trQ⁆ = trQ := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact trQ.mul_mem (trQ.mul_mem (trQ.mul_mem hx hy) (trQ.inv_mem hx)) (trQ.inv_mem hy)) ?_
  have hc : ∀ p ∈ [⁅trA, trB⁆, ⁅trA, trA * (trB * trB)⁆], p ∈ ⁅trQ, trQ⁆ := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Subgroup.commutator_mem_commutator trA_mem_Q trB_mem_Q
    · exact Subgroup.commutator_mem_commutator trA_mem_Q
        (trQ.mul_mem trA_mem_Q (trQ.mul_mem trB_mem_Q trB_mem_Q))
  have hw := hasArr_wPerm (hasArr_getD₂ hasArr_trC0 hasArr_trC1)
  show Subgroup.closure ({trA, trB} : Set (Equiv.Perm (Fin 24))) ≤ ⁅trQ, trQ⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h := hw trAWord
    rw [tr_perfect.1] at h
    have hx := perm_eq_of_hasArr hasArr_trA h
    exact hx ▸ wPerm_mem hc _
  · have h := hw trBWord
    rw [tr_perfect.2] at h
    have hy := perm_eq_of_hasArr hasArr_trB h
    exact hy ▸ wPerm_mem hc _

theorem commutator_img11_trQ : ⁅img11 trQ, img11 trQ⁆ = img11 trQ := by
  have h : ⁅trQ.subgroupOf AutPerm, trQ.subgroupOf AutPerm⁆ = trQ.subgroupOf AutPerm := by
    apply Subgroup.map_injective AutPerm.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le trQ_le, commutator_trQ]
  rw [img11, ← Subgroup.map_commutator, h]

theorem rho_trA_mem_stabSub : rho11 AutPerm le_rfl ⟨trA, trA_mem⟩ ∈ stabSub UT := by
  refine mem_stabSub_UT (maps_UT (f := act11 trAArr)
    (fun m _ => rho11_toW AutPerm le_rfl _ hasArr_trA m) (fun m _ => act11_lt _ _)
    (fun m hm => (tr_pres m hm).1)) (maps_UT (f := act11 trAInv) (fun m _ => ?_)
    (fun m _ => act11_lt _ _) (fun m hm => (tr_pres m hm).2.2.1))
  rw [← map_inv]
  exact rho11_toW AutPerm le_rfl (⟨trA, trA_mem⟩⁻¹ : ↥AutPerm) hasArr_trAinv m

theorem rho_trB_mem_stabSub : rho11 AutPerm le_rfl ⟨trB, trB_mem⟩ ∈ stabSub UT := by
  refine mem_stabSub_UT (maps_UT (f := act11 trBArr)
    (fun m _ => rho11_toW AutPerm le_rfl _ hasArr_trB m) (fun m _ => act11_lt _ _)
    (fun m hm => (tr_pres m hm).2.1)) (maps_UT (f := act11 trBInv) (fun m _ => ?_)
    (fun m _ => act11_lt _ _) (fun m hm => (tr_pres m hm).2.2.2))
  rw [← map_inv]
  exact rho11_toW AutPerm le_rfl (⟨trB, trB_mem⟩⁻¹ : ↥AutPerm) hasArr_trBinv m

theorem img11_trQ_le : img11 trQ ≤ img11 AutPerm ⊓ stabSub UT := by
  refine le_inf (Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2) ?_
  have hQ : trQ ≤ ((stabSub UT).comap (rho11 AutPerm le_rfl)).map AutPerm.subtype := by
    rw [trQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨trA, trA_mem⟩, rho_trA_mem_stabSub, rfl⟩
    · exact ⟨⟨trB, trB_mem⟩, rho_trB_mem_stabSub, rfl⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := hQ (Subgroup.mem_subgroupOf.1 hσ)
  rw [show σ = τ from Subtype.ext hτσ.symm]
  exact hτ

@[expose] noncomputable def K24 : Subgroup (MulAut W11) :=
  phi24.range.map rhoM24

theorem act24s2_lt (s : T24s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    act24s2 s m < 2 ^ 11 := by
  rw [act24s2_spec s hm]
  exact act11_lt _ _

theorem presUT (s : T24s2.Elem) :
    ∀ m ∈ uTMasks, act24s2 s m ∈ uTMasks := by
  intro m hm
  have h := Certificates.certificate7247.2.1
  unfold t24PresUT at h
  rw [List.all_eq_true] at h
  have h1 := h (T24s2.elemEquiv s) (List.mem_finRange _)
  rw [List.all_eq_true] at h1
  have h2 := h1 m hm
  rw [Equiv.symm_apply_apply] at h2
  exact List.contains_iff_mem.1 h2

theorem K24_le :
    K24 ≤ img11 AutPerm ⊓ stabSub UT := by
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  refine ⟨(range_rho11_eq_img11 AutPerm le_rfl) ▸ ⟨phi24 s, rfl⟩, ?_⟩
  refine mem_stabSub_UT (maps_UT (f := act24s2 s) (fun m hm => rhoM24_phi24 s hm)
    (fun m hm => act24s2_lt s hm) (presUT s)) (maps_UT (f := act24s2 s⁻¹) (fun m hm => ?_)
    (fun m hm => act24s2_lt s⁻¹ hm) (presUT s⁻¹))
  rw [← map_inv, ← map_inv]
  exact rhoM24_phi24 s⁻¹ hm

theorem isPGroup_K24 :
    IsPGroup 2 ↥K24 := by
  have hT : IsPGroup 2 T24s2.Elem := IsPGroup.of_card card_T24s2
  rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩⟩
  obtain ⟨k, hk⟩ := hT s
  refine ⟨k, Subtype.ext ?_⟩
  show (rhoM24 (phi24 s)) ^ 2 ^ k = 1
  rw [← map_pow, ← map_pow, hk, map_one, map_one]

theorem fix_K24 (w : W11)
    (hw : w ∈ fixV K24) : w = 1 ∨ w = toW 11 1192 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have key : ∀ s : T24s2.Elem, act24s2 s m = m := fun s =>
    toW_inj (act24s2_lt s hm) hm ((rhoM24_phi24 s hm).symm.trans
      (hw _ ⟨phi24 s, ⟨s, rfl⟩, rfl⟩))
  have h := Certificates.certificate7247.2.2
  unfold t24Fix at h
  rw [beq_iff_eq] at h
  have hmem : m ∈ (List.range (2 ^ 11)).filter fun m =>
      (List.finRange T24s2.n).all fun i => act24s2 (T24s2.elemEquiv.symm i) m == m := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨hm, List.all_eq_true.2 fun i _ => ?_⟩
    rw [beq_iff_eq]
    exact key _
  rw [h] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl (toW_zero 11)
  · exact Or.inr rfl

@[expose] noncomputable def rhoH : MulAut W11 := rho11 AutPerm le_rfl ⟨trH, trH_mem⟩

theorem rhoH_mem : rhoH ∈ img11 AutPerm := rho11_mem_img11 _

theorem rhoH_toW (m : ℕ) : rhoH (toW 11 m) = toW 11 (act11 trHArr m) :=
  rho11_toW AutPerm le_rfl _ hasArr_trH m

theorem vZ_z1 :
    vZ (img11 AutPerm) (toW 11 1192) = W0.map rhoH.toMonoidHom := by
  have h1 := vZ_map rhoH (img11 AutPerm) z0
  have hH : (img11 AutPerm).map (congrHom rhoH) = img11 AutPerm := map_congrHom_self rhoH_mem
  have hz : rhoH z0 = toW 11 1192 := by
    rw [rhoH_toW, trH_z]
  have key : ∀ (A : Subgroup (MulAut W11)) (w : W11), A = img11 AutPerm → w = toW 11 1192 →
      vZ A w = vZ (img11 AutPerm) (toW 11 1192) := by
    rintro A w rfl rfl
    rfl
  exact (key _ _ hH hz).symm.trans (h1.symm.trans (congrArg (·.map rhoH.toMonoidHom) vZ_std))

theorem toW_mem_commV_trQ {m : ℕ}
    (hm : m ∈ combos (trCvData.map fun e => trLAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2)) :
    toW 11 m ∈ commV (img11 trQ) := by
  refine mem_of_combos (fun m => toW 11 m ∈ commV (img11 trQ)) ?_ ?_ _ ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    obtain ⟨⟨g, j⟩, -, rfl⟩ := List.mem_map.1 ha
    by_cases hg : g = 0
    · have hx : rho11 AutPerm le_rfl ⟨trA, trA_mem⟩ ∈ img11 trQ :=
        ⟨⟨trA, trA_mem⟩, Subgroup.mem_subgroupOf.2 trA_mem_Q, rfl⟩
      have h := mem_commV hx (toW 11 (2 ^ j))
      have e1 : toW 11 (trLAct g (2 ^ j) ^^^ 2 ^ j) =
          rho11 AutPerm le_rfl ⟨trA, trA_mem⟩ (toW 11 (2 ^ j)) * (toW 11 (2 ^ j))⁻¹ := by
        rw [rho11_toW AutPerm le_rfl _ hasArr_trA, toW_inv, toW_xor, trLAct, ite_eq_left hg]
      show toW 11 (trLAct g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h
    · have hx : rho11 AutPerm le_rfl ⟨trB, trB_mem⟩ ∈ img11 trQ :=
        ⟨⟨trB, trB_mem⟩, Subgroup.mem_subgroupOf.2 trB_mem_Q, rfl⟩
      have h := mem_commV hx (toW 11 (2 ^ j))
      have e1 : toW 11 (trLAct g (2 ^ j) ^^^ 2 ^ j) =
          rho11 AutPerm le_rfl ⟨trB, trB_mem⟩ (toW 11 (2 ^ j)) * (toW 11 (2 ^ j))⁻¹ := by
        rw [rho11_toW AutPerm le_rfl _ hasArr_trB, toW_inv, toW_xor, trLAct, ite_eq_right hg]
      show toW 11 (trLAct g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h

theorem vZ_z1_le :
    vZ (img11 AutPerm) (toW 11 1192) ≤ commV (img11 trQ) := by
  rw [vZ_z1]
  rintro _ ⟨w, ⟨m, hm, rfl⟩, rfl⟩
  show rhoH (toW 11 m) ∈ _
  refine mem_of_combos (fun m => rhoH (toW 11 m) ∈ commV (img11 trQ)) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero, map_one]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor, map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    show rhoH (toW 11 a) ∈ _
    rw [rhoH_toW]
    refine toW_mem_commV_trQ (tr_w1_mem _ ?_)
    rw [← trW1_eq]
    exact List.mem_map_of_mem ha

theorem w0Basis_head_mem : w0Basis.getD 0 0 ∈ combos w0Basis := by
  decide +kernel

theorem not_vZ_z1_le :
    ¬ vZ (img11 AutPerm) (toW 11 1192) ≤ UT := by
  rw [vZ_z1]
  intro h
  have hm := h ⟨toW 11 (w0Basis.getD 0 0), toW_mem_maskSub w0Basis_head_mem, rfl⟩
  have e : rhoH.toMonoidHom (toW 11 (w0Basis.getD 0 0)) =
      toW 11 (act11 trHArr (w0Basis.getD 0 0)) := rhoH_toW _
  have hm2 : (toW 11 (act11 trHArr (w0Basis.getD 0 0)) : W11) ∈ UT :=
    (congrArg (· ∈ UT) e).mp hm
  exact tr_notin ((toW_mem_UT_iff (act11_lt _ _)).1 hm2)

theorem hbConcl_std
    {X : Subgroup (MulAut W11)} (hX : fixV X = UT) {z : W11} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut W11)} (hSH : S ≤ img11 AutPerm ⊓ stabSub UT)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥(img11 AutPerm)).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl (img11 AutPerm) X z :=
  hbConcl_of_std K24_le isPGroup_K24 fix_K24 img11_trQ_le commutator_img11_trQ vZ_z1_le
    not_vZ_z1_le hX hz1 hSH hS hzS

theorem greedyKT :
    forallGreedy T24s2.invols predKT 6 [] = true :=
  (forallGreedyP_eq pos24s2_eq predKT 6 []).symm.trans
    (forallGreedyAll_le 6 [] Certificates.certificate7247.1 6 le_rfl)

theorem fixV_eq_UT
    {V : Type} [CommGroup V]
    [Finite V] {H X : Subgroup (MulAut V)} {e : V ≃* W11}
    (he : H.map (congrHom e) = (rho11 AutPerm le_rfl).range) (hX : Nat.card ↥X = 2 ^ 6)
    (hfX : Nat.card ↥(fixV X) = 2 ^ 3) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) :
    ∃ g : ↥AutPerm, fixV (X.map (congrHom (twistEquiv e rhoM24 g))) = UT := by
  have hXR : X.map (congrHom e) ≤ rhoM24.range := by
    have h2 := Subgroup.le_normalizer_map (H := H) (congrHom e)
    have h3 : Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W11)) :
        Set (MulAut W11)) = rhoM24.range :=
      (congrArg (fun K : Subgroup (MulAut W11) => Subgroup.normalizer (K : Set (MulAut W11)))
        he).trans normalizer_rho11_autPerm
    exact (Subgroup.map_mono hXN).trans (h2.trans h3.le)
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2) greedyKT e
    hXR (isElemAbelian2_iff.2 hXe) hX
  have hact := chainAct24 e g
  have hlen : l.length = 6 := by
    have h := card_of_chainSub hchain (chainAut24_injective e g) hind
    rw [hX] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfm : (fixMasks 11 act24s2 l).length = 8 := by
    rw [← card_fixV hact hchain, hfX]
    norm_num
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hU : fixMasks 11 act24s2 l = uTMasks := by
    have h := hpred
    unfold predKT at h
    rw [fixMasks24_eq hinv, hlen, hfm] at h
    simpa using h
  refine ⟨g, ?_⟩
  ext w
  refine (mem_fixV_map_congrHom _ X w).trans ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hv := vm_mem_fixV_iff hact hchain hm
  rw [MaskCoords.ofEquiv_vm] at hv
  refine hv.trans (Iff.trans ?_ (toW_mem_UT_iff hm).symm)
  rw [← hU, fixMasks, List.mem_filter, List.mem_range]
  exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩

theorem hbConcl_of_cocode24
    {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥)
    (hX : Nat.card ↥X = 2 ^ 6) (hfX : Nat.card ↥(fixV X) = 2 ^ 3)
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian 2 X) {z : V}
    (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H ⊓ stabSub (fixV X))
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl H X z := by
  obtain ⟨e, he⟩ := cocode24_std h
  obtain ⟨g, hXU⟩ := fixV_eq_UT he hX hfX hXN hXe
  have hR : (rho11 AutPerm le_rfl).range.map (congrHom (rhoM24 g)) = img11 AutPerm :=
    (map_congrHom_self (⟨g, rfl⟩ : rhoM24 g ∈ (rho11 AutPerm le_rfl).range)).trans
      (range_rho11_eq_img11 AutPerm le_rfl)
  have hH : H.map (congrHom (twistEquiv e rhoM24 g)) = img11 AutPerm :=
    (map_congrHom_trans e (rhoM24 g) H).trans
      ((congrArg (fun K => K.map (congrHom (rhoM24 g))) he).trans hR)
  exact hbConcl_of_equiv (twistEquiv e rhoM24 g) hH hXU
    (fun hX' _ hz1' _ hSH' hS' hz' => hbConcl_std hX' hz1' hSH' hS' hz') hz1 hSH hS hzS

end CFSG.Quasithin.H.Coc24
