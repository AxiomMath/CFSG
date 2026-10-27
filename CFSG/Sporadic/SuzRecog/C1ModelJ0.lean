module

public import CFSG.Sporadic.SuzRecog.C1ModelBase

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

theorem card_mul_card_le_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {A B K : Subgroup G}
    (hAB : A ⊓ B = ⊥) (hmul : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ K) :
    Nat.card A * Nat.card B ≤ Nat.card K := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => ⟨p.1 * p.2, hmul _ p.1.2 _ p.2.2⟩) ?_
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
  have h' : x * y = x' * y' := congrArg Subtype.val h
  have hm : x'⁻¹ * x = y' * y⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h'
  have hmem : x'⁻¹ * x ∈ A ⊓ B :=
    mem_inf.mpr ⟨mul_mem (inv_mem hx') hx, hm ▸ mul_mem hy' (inv_mem hy)⟩
  rw [hAB, mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  have hyy : y = y' := mul_left_cancel h'
  subst hyy
  rfl

theorem two_mul_card_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    {x : G} (hxK : x ∈ K) (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hK : 0 < Nat.card K := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hxH (by rw [Subgroup.eq_of_le_of_card_ge hle hm.le]; exact hxK)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

theorem card_map_le {G N : Type*} [Group G] [Group N] [Finite G] (f : G →* N) (H : Subgroup G) :
    Nat.card (H.map f) ≤ Nat.card H := by
  refine Nat.card_le_card_of_surjective (fun h => ⟨f h, mem_map_of_mem f h.2⟩) ?_
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] noncomputable def J0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ⊓ centralizer {Model.rho1} ⊓ suzM

section J0

theorem mem_centralizer_R0_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ↔
      g * Model.w0 = Model.w0 * g ∧ g * r1 = r1 * g := by
  rw [R0_eq, centralizer_closure, mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem mem_J0_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ J0 ↔ g * Model.w0 = Model.w0 * g ∧ g * r1 = r1 * g ∧
      g * Model.rho1 = Model.rho1 * g ∧ g ∈ suzM := by
  rw [J0, mem_inf, mem_inf, mem_centralizer_R0_iff, mem_centralizer_singleton_iff, and_assoc,
    and_assoc]

theorem J0_le_suzM : J0 ≤ suzM := fun _ hg => (mem_J0_iff.mp hg).2.2.2

theorem J0_le_centralizer_rho1 : J0 ≤ centralizer {Model.rho1} := fun _ hg =>
  mem_centralizer_singleton_iff.mpr (mem_J0_iff.mp hg).2.2.1

theorem J0_le_centralizer_R0 : J0 ≤ centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) :=
  fun _ hg => mem_centralizer_R0_iff.mpr ⟨(mem_J0_iff.mp hg).1, (mem_J0_iff.mp hg).2.1⟩

theorem J0_le_centralizer_w0 : J0 ≤ centralizer {Model.w0} := fun _ hg =>
  mem_centralizer_singleton_iff.mpr (mem_J0_iff.mp hg).1

theorem suzInv_one_mem_J0 : suzInv 1 ∈ J0 := by
  have hc : ∀ {g : Equiv.Perm (Fin 1782)}, g ∈ invE 1 → suzInv 1 * g = g * suzInv 1 :=
    fun hg => (mem_invE_iff.mp hg).1.symm
  exact mem_J0_iff.mpr ⟨hc w0_mem_invE, hc r1_mem_invE, hc rho1_mem_invE,
    invE_le_suzM suzInv_mem_invE⟩

theorem zJ0_mem_J0 : zJ0 ∈ J0 :=
  mem_J0_iff.mpr ⟨zJ0_comm.1, zJ0_comm.2.1, zJ0_comm.2.2, zJ0_mem_suzM⟩

theorem closure_le_J0 : closure ({suzInv 1, zJ0} : Set (Equiv.Perm (Fin 1782))) ≤ J0 := by
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact suzInv_one_mem_J0
  · exact zJ0_mem_J0

theorem not_comm_rho1_of_mem_R0 {r : Equiv.Perm (Fin 1782)} (hr : r ∈ Model.R0) (hr1 : r ≠ 1) :
    r * Model.rho1 ≠ Model.rho1 * r := by
  intro h
  have hc : Model.rho1 * r * Model.rho1⁻¹ = r := by rw [← h, mul_inv_cancel_right]
  rcases mem_R0_iff.mp hr with rfl | rfl | rfl | rfl
  · exact hr1 rfl
  · exact r1_ne_w0 hc
  · exact r2_ne_r1 hc
  · exact r2_ne_w0 (hc.symm.trans rho1_conj_r2)

theorem J0_inf_R0 : J0 ⊓ Model.R0 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  by_contra h1
  exact not_comm_rho1_of_mem_R0 (mem_inf.mp hg).2 h1 (mem_J0_iff.mp (mem_inf.mp hg).1).2.2.1

theorem R0_le_centralizer_R0 : Model.R0 ≤ centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) :=
  fun _ hx => mem_centralizer_iff.mpr fun _ hy => R0_comm hy hx

theorem R0_le_suzM : Model.R0 ≤ suzM := R0_le_invE.trans invE_le_suzM

theorem card_J0_le : Nat.card J0 ≤ 20160 := by
  have h1 : Nat.card J0 * Nat.card Model.R0 ≤
      Nat.card ↥(centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) :=
    card_mul_card_le_of_inf_eq_bot J0_inf_R0 fun a ha b hb =>
      mem_inf.mpr ⟨mul_mem (J0_le_centralizer_R0 ha) (R0_le_centralizer_R0 hb),
        mul_mem (J0_le_suzM ha) (R0_le_suzM hb)⟩
  have h2 : 2 * Nat.card ↥(centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) ≤
      Nat.card ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) :=
    two_mul_card_le (inf_le_inf_right _ (centralizer_le (Set.singleton_subset_iff.mpr w0_mem_R0)))
      (x := tau0) (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr tau0_comm_w0,
        invE_le_suzM tau0_mem_invE⟩)
      (fun h => tau0_not_comm_r1 (mem_centralizer_R0_iff.mp (mem_inf.mp h).1).2)
  rw [card_R0] at h1
  rw [card_centralizer_w0] at h2
  omega

theorem res_parts : labArr.size = 42 ∧
    (∀ i < 42, labArr[i]! < 1782 ∧ w0T[labArr[i]!]! = labArr[i]! ∧ labInv[labArr[i]!]! = i) ∧
    (∀ x < 1782, w0T[x]! = x → labInv[x]! < 42 ∧ labArr[labInv[x]!]! = x) ∧
    resTab tTab = wordTab 42 gensS C1ModelData.resT1Word ∧
    resTab zT = wordTab 42 gensS C1ModelData.resZWord ∧
    (∀ k < 3, gensS[k]! = wordTab 42 #[resTab tTab, resTab zT] (C1ModelData.gensSWords.getD k [])) ∧
    resTab tauT = comp 42 (wordTab 42 gensS C1ModelData.tauSWord) r₄T := by
  have h := c1Res_check
  unfold resCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨beq_iff_eq.mp h1, fun i hi => ?_, fun x hx hfix => ?_, beq_iff_eq.mp h4,
    beq_iff_eq.mp h5, fun k hk => beq_iff_eq.mp (allBelow_eq_true.mp h6 k hk), beq_iff_eq.mp h7⟩
  · have := allBelow_eq_true.mp h2 i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allBelow_eq_true.mp h3 x hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at this
    exact this.resolve_left (not_not.mpr hfix)

abbrev FixW0 : Type := {x : Fin 1782 // Model.w0 x = x}

theorem w0_apply_eq_iff {x : Fin 1782} : Model.w0 x = x ↔ w0T[x.val]! = x.val := by
  rw [tabRep_w0.apply x]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

@[expose] noncomputable def labEquiv : Fin 42 ≃ FixW0 where
  toFun i := ⟨⟨labArr[i.val]!, (res_parts.2.1 i i.2).1⟩,
    w0_apply_eq_iff.mpr (res_parts.2.1 i i.2).2.1⟩
  invFun x := ⟨labInv[x.1.val]!, (res_parts.2.2.1 x.1 x.1.2 (w0_apply_eq_iff.mp x.2)).1⟩
  left_inv i := Fin.ext (res_parts.2.1 i i.2).2.2
  right_inv x := Subtype.ext (Fin.ext (res_parts.2.2.1 x.1 x.1.2 (w0_apply_eq_iff.mp x.2)).2)

theorem fix_iff_of_comm {g : Equiv.Perm (Fin 1782)} (hg : g * Model.w0 = Model.w0 * g)
    (x : Fin 1782) : Model.w0 x = x ↔ Model.w0 (g x) = g x := by
  have e : Model.w0 (g x) = g (Model.w0 x) := by
    rw [← Equiv.Perm.mul_apply, ← hg, Equiv.Perm.mul_apply]
  rw [e]
  exact ⟨fun h => by rw [h], fun h => g.injective h⟩

@[expose] noncomputable def resW0 :
    ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))) →* Equiv.Perm (Fin 42) where
  toFun g := labEquiv.symm.permCongr
    ((g : Equiv.Perm (Fin 1782)).subtypePerm fun x =>
      (fix_iff_of_comm (mem_centralizer_singleton_iff.mp g.2) x).symm)
  map_one' := by
    ext i
    simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext i
    simp [Equiv.permCongr_apply, Equiv.Perm.subtypePerm_apply]

theorem tabRep_resTab {t : Tab} {g : ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782))))}
    (ht : Rep 1782 t (g : Equiv.Perm (Fin 1782))) : TabRep (resTab t) (resW0 g) := by
  refine ⟨Array.size_ofFn, fun i => ?_⟩
  rw [show (resTab t)[i.val]! = labInv[t[labArr[i.val]!]!]! from getElem!_ofFn' _ i.2,
    ht ⟨labArr[i.val]!, (res_parts.2.1 i i.2).1⟩]
  rfl

@[expose] def sGen (k : ℕ) : Equiv.Perm (Fin 42) := if k = 0 then g₁ else if k = 1 then g₂ else g₃

theorem rep_sGen {k : ℕ} (hk : k < gensS.size) : Rep 42 gensS[k]! (sGen k) := by
  have hk' : k < 3 := hk
  interval_cases k
  · exact tabRep_g₁.2
  · exact tabRep_g₂.2
  · exact tabRep_g₃.2

theorem sGen_mem_S (k : ℕ) : sGen k ∈ ComponentClassification.PSL3Four.S := by
  unfold sGen
  split_ifs
  exacts [g₁_mem_S, g₂_mem_S, g₃_mem_S]

@[expose] noncomputable def t1C : ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))) :=
  ⟨suzInv 1, mem_centralizer_singleton_iff.mpr (mem_invE_iff.mp w0_mem_invE).1.symm⟩

@[expose] noncomputable def zC : ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))) :=
  ⟨zJ0, mem_centralizer_singleton_iff.mpr zJ0_comm.1⟩

theorem resW0_t1C : resW0 t1C = (C1ModelData.resT1Word.map sGen).prod :=
  (tabRep_resTab (t := tTab) (g := t1C) rep_tTab).perm_eq
    (res_parts.2.2.2.1 ▸ tabRep_wordTab (fun k hk => rep_sGen hk) _ (by decide))

theorem resW0_zC : resW0 zC = (C1ModelData.resZWord.map sGen).prod :=
  (tabRep_resTab (t := zT) (g := zC) tabRep_zJ0.2).perm_eq
    (res_parts.2.2.2.2.1 ▸ tabRep_wordTab (fun k hk => rep_sGen hk) _ (by decide))

@[expose] noncomputable def resGen (k : ℕ) : Equiv.Perm (Fin 42) :=
  if k = 0 then resW0 t1C else resW0 zC

theorem rep_resGen {k : ℕ} (hk : k < (#[resTab tTab, resTab zT] : Array Tab).size) :
    Rep 42 (#[resTab tTab, resTab zT] : Array Tab)[k]! (resGen k) := by
  have hk' : k < 2 := hk
  interval_cases k
  · rw [getElem!_pair_zero, show resGen 0 = resW0 t1C from rfl]
    exact (tabRep_resTab (t := tTab) (g := t1C) rep_tTab).2
  · rw [getElem!_pair_one, show resGen 1 = resW0 zC from rfl]
    exact (tabRep_resTab (t := zT) (g := zC) tabRep_zJ0.2).2

theorem sGen_eq {k : ℕ} (hk : k < 3) :
    sGen k = ((C1ModelData.gensSWords.getD k []).map resGen).prod := by
  refine (rep_sGen (k := k) hk).unique ?_
  rw [res_parts.2.2.2.2.2.1 k hk]
  refine (tabRep_wordTab (fun k hk => rep_resGen hk) _ ?_).2
  interval_cases k <;> decide

theorem closure_res_eq_S :
    closure ({resW0 t1C, resW0 zC} : Set (Equiv.Perm (Fin 42))) =
      ComponentClassification.PSL3Four.S := by
  refine le_antisymm ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)
  · rintro g (rfl | rfl)
    · rw [resW0_t1C]
      exact wordProd_mem sGen_mem_S _
    · rw [resW0_zC]
      exact wordProd_mem sGen_mem_S _
  · have hres : ∀ k, resGen k ∈ closure ({resW0 t1C, resW0 zC} : Set (Equiv.Perm (Fin 42))) :=
      fun k => by
        unfold resGen
        split_ifs
        · exact subset_closure (Set.mem_insert _ _)
        · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    rintro g (rfl | rfl | rfl)
    · rw [show g₁ = sGen 0 from rfl, sGen_eq (by norm_num)]
      exact wordProd_mem hres _
    · rw [show g₂ = sGen 1 from rfl, sGen_eq (by norm_num)]
      exact wordProd_mem hres _
    · rw [show g₃ = sGen 2 from rfl, sGen_eq (by norm_num)]
      exact wordProd_mem hres _

theorem map_closure_subtype :
    (closure ({t1C, zC} : Set ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))))).map
      (centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))).subtype =
        closure ({suzInv 1, zJ0} : Set (Equiv.Perm (Fin 1782))) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_closure_resW0 :
    (closure ({t1C, zC} : Set ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))))).map
      resW0 = ComponentClassification.PSL3Four.S := by
  rw [MonoidHom.map_closure, Set.image_pair, closure_res_eq_S]

theorem card_S_le_closure :
    20160 ≤ Nat.card (closure ({suzInv 1, zJ0} : Set (Equiv.Perm (Fin 1782)))) := by
  rw [← card_S, ← map_closure_resW0, ← map_closure_subtype,
    card_map_of_injective (centralizer _).subtype_injective]
  exact card_map_le _ _

theorem card_J0 : Nat.card J0 = 20160 :=
  le_antisymm card_J0_le (card_S_le_closure.trans (card_le_of_le closure_le_J0))

theorem J0_eq :
    J0 = closure ({suzInv 1, zJ0} : Set (Equiv.Perm (Fin 1782))) :=
  (eq_of_le_of_card_ge closure_le_J0 (by rw [card_J0]; exact card_S_le_closure)).symm

noncomputable abbrev J0C : Subgroup ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))) :=
  J0.subgroupOf (centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782))))

theorem J0C_eq :
    J0C = closure ({t1C, zC} : Set ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782))))) := by
  apply map_injective (centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))).subtype_injective
  rw [map_closure_subtype, subgroupOf_map_subtype, inf_of_le_left J0_le_centralizer_w0, J0_eq]

theorem range_resJ0 :
    (resW0.domRestrict J0C).range = ComponentClassification.PSL3Four.S := by
  rw [MonoidHom.domRestrict_range, J0C_eq, map_closure_resW0]

theorem bijective_resJ0 :
    Function.Bijective (resW0.domRestrict J0C).rangeRestrict := by
  refine (MonoidHom.rangeRestrict_surjective _).bijective_of_nat_card_le ?_
  rw [range_resJ0, card_S, Nat.card_congr (subgroupOfEquivOfLe J0_le_centralizer_w0).toEquiv,
    card_J0]

@[expose] noncomputable def j0Equiv :
    J0 ≃* ComponentClassification.PSL3Four.S :=
  ((subgroupOfEquivOfLe J0_le_centralizer_w0).symm.trans
    (MulEquiv.ofBijective _ bijective_resJ0)).trans (MulEquiv.subgroupCongr range_resJ0)

theorem j0Equiv_apply (g : J0) :
    (j0Equiv g : Equiv.Perm (Fin 42)) = resW0 ⟨g, J0_le_centralizer_w0 g.2⟩ :=
  rfl

end J0

end CFSG.Sporadic.SuzRecog.C1Model
