module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheck
public import CFSG.Sporadic.Schreier.ONTwoCentralizer
public import CFSG.Sporadic.ONOddCore.LiftBasics
public import CFSG.Sporadic.ONOddCore.SylowEight
public import CFSG.Monster.Existence.Compat.Orbits

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure conj_orbit
  card_set_of_tabs invsOK_spec)
open scoped commutatorElement

section General

variable {G G' : Type*} [Group G] [Group G']

@[expose] def sqSub (H : Subgroup G) : Subgroup G := Subgroup.closure {x | ∃ t ∈ H, t ^ 2 = x}

@[expose] def omSub (K : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ K ∧ x ^ 2 = 1}

@[expose] def vSub (H : Subgroup G) : Subgroup G := ⁅omSub (sqSub H), H⁆

theorem sqSub_map (f : G →* G') (H : Subgroup G) : (sqSub H).map f = sqSub (H.map f) := by
  rw [sqSub, sqSub, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨f t, ⟨t, ht, rfl⟩, (map_pow f t 2).symm⟩
  · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t ^ 2, ⟨t, ht, rfl⟩, map_pow f t 2⟩

theorem omSub_map (f : G →* G') (hf : Function.Injective f) (K : Subgroup G) :
    (omSub K).map f = omSub (K.map f) := by
  rw [omSub, omSub, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxK, hx2⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxK, hf ?_⟩, rfl⟩
    rw [map_pow, hy2, map_one]

theorem vSub_map (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    (vSub H).map f = vSub (H.map f) := by
  rw [vSub, vSub, Subgroup.map_commutator, omSub_map f hf, sqSub_map]

theorem card_comap_surj [Finite G] {f : G →* G'} (hf : Function.Surjective f)
    (H : Subgroup G') : Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := (H.comap f).card_mul_index
  rw [H.index_comap_of_surjective hf] at h1
  have h2 := H.card_mul_index
  have h3 : Nat.card G = Nat.card G' * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (H.comap f) * H.index = (Nat.card f.ker * Nat.card H) * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h4

theorem card_le_of_conj_mem (H : Subgroup G) (γ : G) (S : Finset G)
    (hS : ∀ h ∈ H, h * γ * h⁻¹ ∈ S) :
    Nat.card H ≤ S.card * Nat.card ↥(H ⊓ Subgroup.centralizer ({γ} : Set G)) := by
  have h := CFSG.Monster.Existence.Compat.card_conj_orbit_mul_card_inf_centralizer H γ
  have hle : Nat.card {x : G | ∃ h ∈ H, h * γ * h⁻¹ = x} ≤ S.card := by
    calc Nat.card {x : G | ∃ h ∈ H, h * γ * h⁻¹ = x} ≤ Nat.card (S : Set G) :=
          Nat.card_mono S.finite_toSet (by rintro _ ⟨h, hh, rfl⟩; exact hS h hh)
      _ = S.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [← h]
  exact Nat.mul_le_mul_right _ hle

end General

section Model

abbrev onpV :
    Equiv.Perm (Fin N) := evalS onpVWord

abbrev onpX :
    Equiv.Perm (Fin N) := evalS onpXWord

abbrev onpM :
    Equiv.Perm (Fin N) := evalS onpMWord

abbrev onpN :
    Equiv.Perm (Fin N) := evalS onpNWord

theorem prep_onpV :
    PRep N onpVArr onpV := prep_wordArr (by decide)

theorem prep_onpX :
    PRep N onpXArr onpX := prep_wordArr (by decide)

theorem prep_onpM :
    PRep N onpMArr onpM := prep_wordArr (by decide)

theorem prep_onpN :
    PRep N onpNArr onpN := prep_wordArr (by decide)

theorem onpV_mem_T :
    onpV ∈ onT := by
  have h := tFacts.mem prep_onpV (evalS_mem _) onp_v_cert.1
  rwa [onTChain_sub] at h

theorem onpM_mem_M :
    onpM ∈ onM := by
  have h := mFacts.mem prep_onpM (evalS_mem _) onp_mn_cert.1
  rwa [onMChain_sub] at h

theorem onpN_mem_M :
    onpN ∈ onM := by
  have h := mFacts.mem prep_onpN (evalS_mem _) onp_mn_cert.2.1
  rwa [onMChain_sub] at h

theorem onpX_z :
    onpX * onz = onpV * onz * onpX :=
  eq_of_peq (prep_pcomp prep_onpX prep_z) (prep_pcomp (prep_pcomp prep_onpV prep_z) prep_onpX)
    onp_x_cert.1

theorem onpX_v :
    onpX * onpV = onz * onpX :=
  eq_of_peq (prep_pcomp prep_onpX prep_onpV) (prep_pcomp prep_z prep_onpX) onp_x_cert.2.1

theorem onpX_cube :
    onpX * (onpX * onpX) = 1 :=
  eq_of_peq (prep_pcomp prep_onpX (prep_pcomp prep_onpX prep_onpX)) prep_pid onp_x_cert.2.2

theorem onpG_z :
    onpN * (onpX * (onpM * onpX)) * onz = ont * (onpN * (onpX * (onpM * onpX))) :=
  eq_of_peq (prep_pcomp (prep_pcomp prep_onpN (prep_pcomp prep_onpX (prep_pcomp prep_onpM
    prep_onpX))) prep_z) (prep_pcomp prep_t (prep_pcomp prep_onpN (prep_pcomp prep_onpX
    (prep_pcomp prep_onpM prep_onpX)))) onp_mn_cert.2.2

theorem onq_mul_self :
    onq * onq = onz :=
  eq_of_peq (prep_pcomp prep_q prep_q) prep_z onp_q_cert

theorem onT_le_M :
    onT ≤ onM := by
  rw [onM_eq_centralizer_z]
  intro t ht
  refine ⟨onT_le ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hz : onz ∈ CFSG.centerIn onT := by
    rw [onT_centerIn]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht)

theorem onz_onpV :
    onz * onpV = onpV * onz := by
  have h := onT_le_M onpV_mem_T
  rw [onM_eq_centralizer_z] at h
  exact (Subgroup.mem_centralizer_singleton_iff.1 h.2).symm

abbrev vT :
    onT := ⟨onpV, onpV_mem_T⟩

theorem tab_v32 :
    TabRep onpV32 (rhoT vT) :=
  tabRep_of_prep (by decide) (prep_rhoT (G := vT) prep_onpV onp_v_cert.2.1)

theorem tab_z32 :
    TabRep Data.T32z (rhoT zT) := by
  rw [rhoT_z]
  exact tabRep_of_prep t32_cert.2.2.1 prep_z32

theorem onpCommGens_size :
    onpCommGens.size = omegaEnum.tabs.size * t32Enum.tabs.size := Array.size_ofFn

theorem onpCommGens_get {k : ℕ} (hk : k < omegaEnum.tabs.size * t32Enum.tabs.size) :
    onpCommGens[k]! = CFSG.PSL3Four.Native.commTab 32 omegaEnum.tabs[k / t32Enum.tabs.size]!
      t32Enum.tabs[k % t32Enum.tabs.size]! onpOmInv[k / t32Enum.tabs.size]!
      onpTInv[k % t32Enum.tabs.size]! := by
  rw [getElem!_pos onpCommGens k (by rw [onpCommGens_size]; exact hk)]
  simp only [onpCommGens, Array.getElem_ofFn]

theorem comm32_enumerates :
    Enumerates ⁅omega32, onT32Chain.originalSubgroup⁆ onpCommEnum.tabs.toList := by
  obtain ⟨hOm, hT, hE, -⟩ := onp_comm_cert
  have hs : 0 < t32Enum.tabs.size := by rw [t32_cert.2.2.2.2.1]; norm_num
  rw [Subgroup.commutator_def]
  refine enumerates_closure ?_ ?_ hE
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨i, hi, hra⟩ := omega32_enumerates.exists_pos ha
    obtain ⟨j, hj, hrb⟩ := t32_enumerates.exists_pos hb
    have hk : i * t32Enum.tabs.size + j < omegaEnum.tabs.size * t32Enum.tabs.size :=
      calc i * t32Enum.tabs.size + j < i * t32Enum.tabs.size + t32Enum.tabs.size := by omega
        _ = (i + 1) * t32Enum.tabs.size := by ring
        _ ≤ omegaEnum.tabs.size * t32Enum.tabs.size := Nat.mul_le_mul_right _ hi
    refine ⟨i * t32Enum.tabs.size + j, by rw [onpCommGens_size]; exact hk, ?_⟩
    have h1 : (i * t32Enum.tabs.size + j) / t32Enum.tabs.size = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hj, zero_add]
    have h2 : (i * t32Enum.tabs.size + j) % t32Enum.tabs.size = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [onpCommGens_get hk, h1, h2]
    exact TabRep.commTab hra hrb (invsOK_spec hOm hi hra) (invsOK_spec hT hj hrb)
  · intro k hk
    rw [onpCommGens_size] at hk
    have hi : k / t32Enum.tabs.size < omegaEnum.tabs.size :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
    have hj : k % t32Enum.tabs.size < t32Enum.tabs.size := Nat.mod_lt _ hs
    obtain ⟨a, ha, hra⟩ := omega32_enumerates.exists_elt hi
    obtain ⟨b, hb, hrb⟩ := t32_enumerates.exists_elt hj
    refine ⟨⁅a, b⁆, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    rw [onpCommGens_get hk]
    exact TabRep.commTab hra hrb (invsOK_spec hOm hi hra) (invsOK_spec hT hj hrb)

theorem commEnum_tab_cases
    {t : CFSG.PSL3Four.Native.Tab} (ht : t ∈ onpCommEnum.tabs) :
    t = CFSG.PSL3Four.Native.idTab 32 ∨ t = Data.T32z ∨ t = onpV32 ∨
      t = CFSG.PSL3Four.Native.comp 32 Data.T32z onpV32 := by
  have h := Array.all_eq_true'.1 onp_comm_cert.2.2.2.1 t ht
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  tauto

theorem mem_comm32
    {y : Equiv.Perm (Fin 32)}
    (hy : y ∈ ⁅omega32, onT32Chain.originalSubgroup⁆) :
    y = 1 ∨ y = rhoT zT ∨ y = rhoT vT ∨ y = rhoT zT * rhoT vT := by
  obtain ⟨t, ht, hr⟩ := comm32_enumerates.complete y hy
  rcases commEnum_tab_cases (Array.mem_toList_iff.1 ht) with rfl | rfl | rfl | rfl
  · exact Or.inl (hr.perm_eq TabRep.idTab)
  · exact Or.inr (Or.inl (hr.perm_eq tab_z32))
  · exact Or.inr (Or.inr (Or.inl (hr.perm_eq tab_v32)))
  · exact Or.inr (Or.inr (Or.inr (hr.perm_eq (tab_z32.comp tab_v32))))

theorem z32_mem_comm :
    rhoT zT ∈ ⁅omega32, onT32Chain.originalSubgroup⁆ := by
  obtain ⟨t, ht, he⟩ := Array.any_eq_true'.1 onp_comm_cert.2.2.2.2.1
  rw [beq_iff_eq] at he
  subst he
  obtain ⟨g, hg, hr⟩ := comm32_enumerates.sound _ (Array.mem_toList_iff.2 ht)
  rwa [tab_z32.perm_eq hr]

theorem v32_mem_comm :
    rhoT vT ∈ ⁅omega32, onT32Chain.originalSubgroup⁆ := by
  obtain ⟨t, ht, he⟩ := Array.any_eq_true'.1 onp_comm_cert.2.2.2.2.2
  rw [beq_iff_eq] at he
  subst he
  obtain ⟨g, hg, hr⟩ := comm32_enumerates.sound _ (Array.mem_toList_iff.2 ht)
  rwa [tab_v32.perm_eq hr]

abbrev VT : Subgroup onT := vSub ⊤

theorem VT_map_rhoT :
    VT.map rhoT = ⁅omega32, onT32Chain.originalSubgroup⁆ := by
  rw [vSub_map rhoT rhoT_injective, ← MonoidHom.range_eq_map, rhoT_range]
  rfl

theorem mem_VT
    {y : onT} : y ∈ VT ↔ y = 1 ∨ y = zT ∨ y = vT ∨ y = zT * vT := by
  rw [← Subgroup.mem_map_iff_mem rhoT_injective, VT_map_rhoT]
  constructor
  · intro h
    rcases mem_comm32 h with h | h | h | h
    · exact Or.inl (rhoT_injective (by rw [h, map_one]))
    · exact Or.inr (Or.inl (rhoT_injective h))
    · exact Or.inr (Or.inr (Or.inl (rhoT_injective h)))
    · exact Or.inr (Or.inr (Or.inr (rhoT_injective (by rw [h, map_mul]))))
  · rintro (rfl | rfl | rfl | rfl)
    · rw [map_one]
      exact one_mem _
    · exact z32_mem_comm
    · exact v32_mem_comm
    · rw [map_mul]
      exact mul_mem z32_mem_comm v32_mem_comm

abbrev Tp :
    Subgroup Pv := onT.subgroupOf Pv

abbrev iotaT :
    onT →* Pv := Subgroup.inclusion onT_le

abbrev Vp : Subgroup Pv := vSub Tp

abbrev vP : Pv := ⟨onpV, evalS_mem _⟩

abbrev xP : Pv := ⟨onpX, evalS_mem _⟩

abbrev mP : Pv := ⟨onpM, evalS_mem _⟩

abbrev nP : Pv := ⟨onpN, evalS_mem _⟩

abbrev cP : Pv := ⟨onc, onc_mem_P⟩

theorem Tp_eq :
    Tp = (⊤ : Subgroup onT).map iotaT := by
  rw [← MonoidHom.range_eq_map, Subgroup.inclusion_range]

theorem Vp_eq :
    Vp = VT.map iotaT := by
  rw [Vp, Tp_eq, vSub_map iotaT (Subgroup.inclusion_injective onT_le)]

theorem mem_Vp
    {y : Pv} : y ∈ Vp ↔ y = 1 ∨ y = zP ∨ y = vP ∨ y = zP * vP := by
  rw [Vp_eq]
  constructor
  · rintro ⟨y₀, hy₀, rfl⟩
    rcases mem_VT.1 hy₀ with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact ⟨zT, mem_VT.2 (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨vT, mem_VT.2 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨zT * vT, mem_VT.2 (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

theorem zP_ne_one :
    zP ≠ 1 := fun h => onz_ne_one (congrArg Subtype.val h)

theorem vT_ne_one :
    vT ≠ 1 := by
  intro h
  have h1 := tab_v32
  rw [h, map_one] at h1
  have h2 := congrArg (fun t : CFSG.PSL3Four.Native.Tab => t[5]!) (h1.tab_eq TabRep.idTab)
  exact absurd h2 (by decide)

theorem vT_ne_zT :
    vT ≠ zT := by
  intro h
  have h1 := tab_v32
  rw [h] at h1
  have h2 := congrArg (fun t : CFSG.PSL3Four.Native.Tab => t[0]!) (h1.tab_eq tab_z32)
  exact absurd h2 (by decide)

theorem vP_ne_one :
    vP ≠ 1 := by
  intro h
  apply vT_ne_one
  apply Subtype.ext
  exact congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) h

theorem vP_ne_zP :
    vP ≠ zP := by
  intro h
  apply vT_ne_zT
  apply Subtype.ext
  exact congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) h

theorem xP_zP :
    xP * zP * xP⁻¹ = vP * zP := by
  have h : xP * zP = vP * zP * xP := Subtype.ext onpX_z
  rw [h, mul_inv_cancel_right]

theorem xP_vP :
    xP * vP * xP⁻¹ = zP := by
  have h : xP * vP = zP * xP := Subtype.ext onpX_v
  rw [h, mul_inv_cancel_right]

theorem xP_cube :
    xP * (xP * xP) = 1 := Subtype.ext onpX_cube

theorem zP_vP :
    zP * vP = vP * zP := Subtype.ext onz_onpV

theorem zP_sq :
    zP * zP = 1 := Subtype.ext onz_sq

abbrev parP :
    Subgroup Pv := Subgroup.normalizer (Vp : Set Pv)

theorem conj_xP_mem
    {h : Pv} (hh : h ∈ Vp) : xP * h * xP⁻¹ ∈ Vp := by
  rw [mem_Vp] at hh ⊢
  rcases hh with rfl | rfl | rfl | rfl
  · left
    group
  · right; right; right
    rw [xP_zP, zP_vP]
  · right; left
    exact xP_vP
  · right; right; left
    calc xP * (zP * vP) * xP⁻¹ = (xP * zP * xP⁻¹) * (xP * vP * xP⁻¹) := by group
      _ = vP * (zP * zP) := by rw [xP_zP, xP_vP, mul_assoc]
      _ = vP := by rw [zP_sq, mul_one]

theorem xP_mem_parP :
    xP ∈ parP := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_xP_mem, fun hh => ?_⟩
  have h3 : xP * xP * xP = 1 := by rw [mul_assoc]; exact xP_cube
  have e : h = xP * (xP * (xP * h * xP⁻¹) * xP⁻¹) * xP⁻¹ := by
    calc h = (xP * xP * xP) * h * (xP * xP * xP)⁻¹ := by rw [h3, one_mul, inv_one, mul_one]
      _ = _ := by group
  rw [e]
  exact conj_xP_mem (conj_xP_mem hh)

theorem orderOf_xP :
    orderOf xP = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [pow_three]; exact xP_cube) fun h => vP_ne_one ?_
  have e := xP_zP
  rw [h, one_mul, inv_one, mul_one] at e
  calc vP = vP * zP * zP⁻¹ := by group
    _ = 1 := by rw [← e, mul_inv_cancel]

theorem Vp_map
    {α : MulAut Pv} (hα : Tp.map α.toMonoidHom = Tp) :
    Vp.map α.toMonoidHom = Vp := by
  rw [Vp, vSub_map _ α.injective, hα]

theorem parP_map
    {α : MulAut Pv} (hα : Tp.map α.toMonoidHom = Tp) :
    parP.map α.toMonoidHom = parP := by
  rw [parP, Subgroup.map_equiv_normalizer_eq, Vp_map hα]

theorem Tp_le_parP : Tp ≤ parP := by
  intro t ht
  have hα : Tp.map (MulAut.conj t).toMonoidHom = Tp := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hy
      have := mul_mem (mul_mem ht hy) (inv_mem ht)
      rwa [show t * (t⁻¹ * y * t) * t⁻¹ = y by group] at this
    · intro hy
      exact mul_mem (mul_mem (inv_mem ht) hy) ht
  have hV := Vp_map hα
  rw [Subgroup.mem_normalizer_iff]
  intro h
  conv_rhs => rw [← hV]
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    show t⁻¹ * (t * h * t⁻¹) * t = h by group]

theorem conj_zP_mem
    {g : Pv} (hg : g ∈ parP) :
    g * zP * g⁻¹ ∈ ({zP, vP, zP * vP} : Finset Pv) := by
  have hz : zP ∈ Vp := mem_Vp.2 (Or.inr (Or.inl rfl))
  have h := (Subgroup.mem_normalizer_iff.1 hg zP).1 hz
  rw [mem_Vp] at h
  rcases h with h | h | h | h
  · exfalso
    apply zP_ne_one
    calc zP = g⁻¹ * (g * zP * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp

abbrev vM :
    onM := ⟨onpV, onT_le_M onpV_mem_T⟩

abbrev zM :
    onM := ⟨onz, onT_le_M onz_mem_T⟩

theorem piR_zM :
    piR zM = 1 := by
  have h : zM ∈ piR.ker := by
    rw [ker_piR, Subgroup.mem_subgroupOf]
    show onz ∈ onQ
    rw [← onq_mul_self]
    exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  exact h

abbrev CR :
    Subgroup RM := Subgroup.centralizer {piR vM}

theorem mem_M_of_comm
    {g : Pv} (hg : g * zP = zP * g) : (g : Equiv.Perm (Fin N)) ∈ onM := by
  rw [onM_eq_centralizer_z]
  exact ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)⟩

theorem piR_mem_CR
    {g : Pv} (hgP : g ∈ parP) (hgz : g * zP = zP * g) :
    piR ⟨g, mem_M_of_comm hgz⟩ ∈ CR := by
  have hv : vP ∈ Vp := mem_Vp.2 (Or.inr (Or.inr (Or.inl rfl)))
  have h := (Subgroup.mem_normalizer_iff.1 hgP vP).1 hv
  rw [mem_Vp] at h
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  rcases h with h | h | h | h
  · exfalso
    apply vP_ne_one
    calc vP = g⁻¹ * (g * vP * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply vP_ne_zP
    calc vP = g⁻¹ * (g * vP * g⁻¹) * g := by group
      _ = g⁻¹ * (zP * g) := by rw [h, mul_assoc]
      _ = g⁻¹ * (g * zP) := by rw [hgz]
      _ = zP := by group
  · congr 1
    apply Subtype.ext
    have e : g * vP = vP * g := by
      calc g * vP = g * vP * g⁻¹ * g := by group
        _ = vP * g := by rw [h]
    exact congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) e
  · have e : g * vP = zP * vP * g := by
      calc g * vP = g * vP * g⁻¹ * g := by group
        _ = zP * vP * g := by rw [h]
    have e' : (⟨g, mem_M_of_comm hgz⟩ : onM) * vM = zM * vM * ⟨g, mem_M_of_comm hgz⟩ :=
      Subtype.ext (congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) e)
    rw [e', map_mul, map_mul, piR_zM, one_mul, map_mul]

theorem pinvCand_size' (n : ℕ) (t : Array ℕ) : (pinvCand n t).size = n := by
  have heq : pinvCand n t =
      (List.range' 0 n).foldl (fun p i => p.set! t[i]! i) (Array.replicate n 0) := by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq]
  have : ∀ (l : List ℕ) (p : Array ℕ), (l.foldl (fun p i => p.set! t[i]! i) p).size = p.size := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons a l ih => intro p; rw [List.foldl_cons, ih]; simp
  rw [this]
  simp

theorem tab_u :
    TabRep Data.quotientConjugator onu := tabRep_of_prep (by decide) prep_u

theorem tab_uinv :
    TabRep (pinvCand 120 Data.quotientConjugator) onu⁻¹ :=
  tabRep_of_prep (pinvCand_size' _ _) prep_u_inv

theorem bTab_size (g : Array ℕ) : (bTab g).size = 120 := by
  simp [bTab, blockTab, qblocks_size]

theorem piM_apply
    (m : onM) : piM m = onu * rhoM m * onu⁻¹ := rfl

theorem tab_rgen
    {j : ℕ} (hj : j < 3) : TabRep onpRGens[j]! (piM (mGen j)) := by
  have hjs : j < (wordArrs Data.MWords).size := by
    rw [wordArrs_size]
    exact lt_of_lt_of_eq hj onMgens_length.symm
  have hb := prep_rhoM_gen j (by rw [Array.size_map]; exact hjs)
  rw [getElem!_map' _ _ hjs] at hb
  rw [onpRGens, getElem!_map' _ _ hjs, piM_apply]
  exact tab_u.conjTab (tabRep_of_prep (bTab_size _) hb) tab_uinv

theorem onpRGens_size :
    onpRGens.size = 3 := by
  rw [onpRGens, Array.size_map, wordArrs_size]
  exact onMgens_length

theorem tab_vbar :
    TabRep onpVBar (piM vM) := by
  rw [onpVBar, piM_apply]
  exact tab_u.conjTab (tabRep_of_prep (by decide)
    (prep_rhoM (g := vM) prep_onpV onp_v_cert.2.2)) tab_uinv

theorem RM_eq_closure :
    RM = Subgroup.closure (piM '' (mGen '' {j | j < 3})) := by
  rw [RM, MonoidHom.range_eq_map, onM_top, MonoidHom.map_closure]

theorem card_class_vbar :
    Nat.card {x : Equiv.Perm (Fin 120) | ∃ h ∈ RM, h * piM vM * h⁻¹ = x} = 315 := by
  obtain ⟨hs, hc, hn⟩ := conj_orbit (A := piM '' (mGen '' {j | j < 3})) (ginv := onpRGensInv)
    (fun a ha => by
      obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := ha
      exact ⟨j, by rw [onpRGens_size]; exact hj, tab_rgen hj⟩)
    (fun j hj => ⟨_, ⟨mGen j, ⟨j, by rwa [onpRGens_size] at hj, rfl⟩, rfl⟩,
      tab_rgen (by rwa [onpRGens_size] at hj)⟩)
    tab_vbar onp_orbit_cert.1
  rw [← RM_eq_closure] at hs hc
  rw [card_set_of_tabs (L := onpROrbit.tabs.toList) (fun t ht => ?_) (fun g hg => ?_) hn,
    Array.length_toList, onp_orbit_cert.2]
  · obtain ⟨c, hc', hr⟩ := hs t ht
    exact ⟨_, ⟨c, hc', rfl⟩, hr⟩
  · obtain ⟨c, hc', rfl⟩ := hg
    exact hc c hc'

theorem card_CR :
    Nat.card CR = 128 := by
  have h1 : CR = (Subgroup.centralizer {(piM vM : Equiv.Perm (Fin 120))}).subgroupOf RM := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  rw [h1, card_subgroupOf]
  have h2 := CFSG.Monster.Existence.Compat.card_conj_orbit_mul_card_inf_centralizer RM (piM vM)
  rw [card_RM, card_class_vbar] at h2
  omega

theorem card_parP_inf_le :
    Nat.card ↥(parP ⊓ Subgroup.centralizer ({zP} : Set Pv)) ≤ 512 := by
  have hK : Nat.card (CR.comap piR) = 512 := by
    rw [card_comap_surj piR_surjective, ker_piR, card_onQ_subgroupOf_M, card_CR]
  rw [← hK]
  have hz : ∀ g : ↥(parP ⊓ Subgroup.centralizer ({zP} : Set Pv)), (g : Pv) * zP = zP * g :=
    fun g => Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
  refine Nat.card_le_card_of_injective
    (fun g => ⟨⟨g, mem_M_of_comm (hz g)⟩, piR_mem_CR (Subgroup.mem_inf.1 g.2).1 (hz g)⟩) ?_
  intro a b hab
  have := congrArg (fun y : ↥(CR.comap piR) => ((y : onM) : Equiv.Perm (Fin N))) hab
  exact Subtype.ext (Subtype.ext this)

theorem card_parP :
    Nat.card parP = 1536 := by
  have hup : Nat.card parP ≤ 1536 := by
    have h1 := card_le_of_conj_mem parP zP {zP, vP, zP * vP} (fun g hg => conj_zP_mem hg)
    have h2 : ({zP, vP, zP * vP} : Finset Pv).card ≤ 3 := Finset.card_le_three
    calc Nat.card parP ≤ _ := h1
      _ ≤ 3 * 512 := Nat.mul_le_mul h2 card_parP_inf_le
  have h512 : 512 ∣ Nat.card parP := by
    rw [← card_onT_subgroupOf]
    exact Subgroup.card_dvd_of_le Tp_le_parP
  have h3 : 3 ∣ Nat.card parP := by
    have := orderOf_dvd_natCard (⟨xP, xP_mem_parP⟩ : parP)
    rwa [Subgroup.orderOf_mk, orderOf_xP] at this
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h512 h3
  have hpos : 0 < Nat.card parP := Nat.card_pos
  omega

theorem cP_val :
    ((cP : Pv) : Equiv.Perm (Fin N)) = onc := rfl

theorem onc_inv_g_mem_M :
    onc⁻¹ * (onpN * (onpX * (onpM * onpX))) ∈ onM := by
  rw [onM_eq_centralizer_z]
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem onc_mem_P) (mul_mem (evalS_mem _)
    (mul_mem (evalS_mem _) (mul_mem (evalS_mem _) (evalS_mem _)))), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, onpG_z, ont_eq]
  group

theorem cP_mem_sup :
    cP ∈ parP ⊔ onM.subgroupOf Pv := by
  have hMH : onM.subgroupOf Pv ≤ parP ⊔ onM.subgroupOf Pv := le_sup_right
  have hxH : xP ∈ parP ⊔ onM.subgroupOf Pv := le_sup_left (a := parP) xP_mem_parP
  have hmH : mP ∈ parP ⊔ onM.subgroupOf Pv := hMH (Subgroup.mem_subgroupOf.2 onpM_mem_M)
  have hnH : nP ∈ parP ⊔ onM.subgroupOf Pv := hMH (Subgroup.mem_subgroupOf.2 onpN_mem_M)
  have hgH : nP * (xP * (mP * xP)) ∈ parP ⊔ onM.subgroupOf Pv :=
    mul_mem hnH (mul_mem hxH (mul_mem hmH hxH))
  have hcg : cP⁻¹ * (nP * (xP * (mP * xP))) ∈ onM.subgroupOf Pv := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_mul]
    exact onc_inv_g_mem_M
  have e : nP * (xP * (mP * xP)) * (cP⁻¹ * (nP * (xP * (mP * xP))))⁻¹ = cP := by
    rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  rw [← e]
  exact mul_mem hgH (inv_mem (hMH hcg))

theorem onM1_le_sup :
    onM1 ≤ (parP ⊔ onM.subgroupOf Pv).map Pv.subtype := by
  intro y hy
  rw [onM1, Subgroup.mem_map] at hy
  obtain ⟨m, hm, hmy⟩ := hy
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmy
  have hmP : (⟨m, onM_le hm⟩ : Pv) ∈ parP ⊔ onM.subgroupOf Pv :=
    le_sup_right (a := parP) (Subgroup.mem_subgroupOf.2 hm)
  refine ⟨cP * ⟨m, onM_le hm⟩ * cP⁻¹, mul_mem (mul_mem cP_mem_sup hmP) (inv_mem cP_mem_sup), ?_⟩
  rw [← hmy, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, cP_val]

theorem onM_le_sup :
    onM ≤ (parP ⊔ onM.subgroupOf Pv).map Pv.subtype := by
  intro m hm
  exact ⟨⟨m, onM_le hm⟩, le_sup_right (a := parP) (Subgroup.mem_subgroupOf.2 hm), rfl⟩

theorem parP_sup_M :
    parP ⊔ onM.subgroupOf Pv = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : (y : Equiv.Perm (Fin N)) ∈ onM ⊔ onM1 := by
    rw [onM_sup_M1]
    exact y.2
  obtain ⟨y', hy', hyy⟩ := sup_le onM_le_sup onM1_le_sup hy
  have e : y' = y := Subtype.ext hyy
  rwa [e] at hy'

theorem onl_parFact_holds :
    ∃ P : Subgroup Pv, onT.subgroupOf Pv ≤ P ∧ Nat.card P = 3 * Nat.card (onT.subgroupOf Pv) ∧
      P ⊔ onM.subgroupOf Pv = ⊤ ∧
      ∀ α : MulAut Pv, (onT.subgroupOf Pv).map α.toMonoidHom = onT.subgroupOf Pv →
        P.map α.toMonoidHom = P :=
  ⟨parP, Tp_le_parP, by rw [card_parP, card_onT_subgroupOf], parP_sup_M,
    fun _ hα => parP_map hα⟩

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
