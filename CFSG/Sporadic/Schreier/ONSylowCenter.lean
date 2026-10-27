module

public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.Schreier.ONSmallChains
public import CFSG.Sporadic.Schreier.ONRestrict
public import CFSG.Sporadic.Schreier.ONCheckAux
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

theorem prep_z :
    PRep N zArr onz := prep_wordArr words_ok.2.2.2.2.1

theorem onz_mem_T :
    onz ∈ onT := by
  have h := tFacts.mem prep_z (evalS_mem _) z_cert.2.2.1
  rwa [onTChain_sub] at h

theorem onz_sq :
    onz * onz = 1 := eq_of_peq (prep_pcomp prep_z prep_z) prep_pid z_cert.1

theorem onz_ne_one :
    onz ≠ 1 := by
  intro h
  have h1 : peq nPts zArr (pid nPts) = true := (peq_iff prep_z prep_pid).2 h
  rw [z_cert.2.1] at h1
  exact absurd h1 (by decide)

theorem orderOf_onz :
    orderOf onz = 2 :=
  orderOf_eq_prime (by rw [sq]; exact onz_sq) onz_ne_one

theorem tpoints_size : Data.TPoints.size = 32 := by decide

theorem onR_length : onR.length = 32 := by simp [onR, tpoints_size]

theorem tpoints_lt
    {k : ℕ} (hk : k < Data.TPoints.size) : Data.TPoints[k]! < N := by
  have := allBelowN_spec (by
    have h := r_cert.1
    simp only [pointsOK, Bool.and_eq_true] at h
    exact h.2) hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem tpoints_pos
    {k : ℕ} (hk : k < Data.TPoints.size) : rPos[Data.TPoints[k]!]! = k := by
  have := allBelowN_spec (by
    have h := r_cert.1
    simp only [pointsOK, Bool.and_eq_true] at h
    exact h.2) hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this.2

theorem onR_get {k : ℕ} (hk : k < onR.length) :
    ((onR[k] : Fin N) : ℕ) = Data.TPoints[k]! := by
  have hk' : k < Data.TPoints.size := by simpa [onR] using hk
  have e := List.getElem_of_eq (show onR = Data.TPoints.toList.map ptN from rfl) hk
  rw [e, List.getElem_map, Array.getElem_toList, ptN]
  show Data.TPoints[k] % N = _
  rw [Nat.mod_eq_of_lt (by rw [← getElem!_pos Data.TPoints k hk']; exact tpoints_lt hk'),
    getElem!_pos Data.TPoints k hk']

theorem onR_nodup : onR.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  have h1 := congrArg (fun x : Fin N => (x : ℕ)) hab
  simp only [List.get_eq_getElem] at h1
  rw [onR_get, onR_get] at h1
  have ha : a.val < Data.TPoints.size := by have := a.isLt; simpa [onR] using this
  have hb : b.val < Data.TPoints.size := by have := b.isLt; simpa [onR] using this
  have : rPos[Data.TPoints[a.val]!]! = rPos[Data.TPoints[b.val]!]! := by rw [h1]
  rw [tpoints_pos ha, tpoints_pos hb] at this
  exact Fin.ext this

theorem restrict_get
    {g : Array ℕ} {G : Equiv.Perm (Fin N)} (hg : PRep N g G) {t : Array ℕ}
    (h : restrictOK g Data.TPoints t = true) {k : ℕ} (hk : k < onR.length) :
    ∃ hk' : t[k]! < onR.length, G onR[k] = onR[t[k]!] := by
  have hk1 : k < Data.TPoints.size := by simpa [onR] using hk
  obtain ⟨ht, he⟩ := restrictOK_spec h hk1
  have ht' : t[k]! < onR.length := by simpa [onR] using ht
  refine ⟨ht', Fin.ext ?_⟩
  rw [onR_get ht', he, ← onR_get hk]
  exact (hg _).symm

theorem prep_onTgens :
    ∀ j (hj : j < onTgens.length), PRep N (wordArrs Data.TWords)[j]! onTgens[j] :=
  prep_wordArrs words_ok.1

theorem onTgens_preserve :
    ∀ g ∈ onTgens, ∀ p ∈ onR, g • p ∈ onR := by
  intro g hg p hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hj6 : j < 6 := by rw [onTgens_length] at hj; exact hj
  obtain ⟨hk', he⟩ := restrict_get (prep_onTgens j hj) (allBelowN_spec r_cert.2.1 hj6) hk
  rw [Equiv.Perm.smul_def, he]
  exact List.getElem_mem hk'

theorem onT_preserve :
    ∀ g ∈ onT, ∀ p ∈ onR, g • p ∈ onR :=
  listInvariant onR onTgens_preserve

@[expose] def rhoT :
    onT →* Equiv.Perm (Fin 32) :=
  (finCongr onR_length).permCongrHom.toMonoidHom.comp
    (listRestrict onR onT onT_preserve onR_nodup)

theorem rhoT_spec
    (g : onT) (k : Fin 32) :
    onR.get (Fin.cast onR_length.symm (rhoT g k)) = (g : Equiv.Perm (Fin N))
      (onR.get (Fin.cast onR_length.symm k)) := by
  have := get_listRestrict onR onT onT_preserve onR_nodup g (Fin.cast onR_length.symm k)
  rw [Equiv.Perm.smul_def] at this
  rw [← this]
  congr 1

theorem prep_rhoT
    {g : Array ℕ} {G : onT} (hg : PRep N g (G : Equiv.Perm (Fin N))) {t : Array ℕ}
    (h : restrictOK g Data.TPoints t = true) : PRep 32 t (rhoT G) := by
  intro k
  have hk : k.val < onR.length := by rw [onR_length]; exact k.isLt
  obtain ⟨hk', he⟩ := restrict_get hg h hk
  have hr := rhoT_spec G k
  simp only [List.get_eq_getElem, Fin.val_cast] at hr
  rw [he] at hr
  exact ((List.Nodup.getElem_inj_iff onR_nodup).1 hr).symm

@[expose] def tGen (j : ℕ) : onT :=
  if h : j < onTgens.length then ⟨onTgens[j], Subgroup.subset_closure (List.getElem_mem h)⟩
  else 1

theorem tGen_val
    {j : ℕ} (h : j < onTgens.length) : (tGen j : Equiv.Perm (Fin N)) = onTgens[j] := by
  rw [tGen, dite_eq_left h]

theorem onT_top :
    (⊤ : Subgroup onT) = Subgroup.closure (tGen '' {j | j < 6}) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj6 : j < 6 := by rw [onTgens_length] at hj; exact hj
    refine Subgroup.subset_closure ⟨j, hj6, Subtype.ext ?_⟩
    exact tGen_val hj
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx => exact Subgroup.inv_mem _ ihx

theorem prep_rhoT_gen :
    ∀ j < ((wordArrs Data.TWords).map rTab).size,
    PRep 32 ((wordArrs Data.TWords).map rTab)[j]! (rhoT (tGen j)) := by
  intro j hj
  have h6 : (evalList Data.TWords).length = 6 := onTgens_length
  have hj6 : j < 6 := by simp only [Array.size_map, wordArrs_size] at hj; omega
  have hjl : j < onTgens.length := by rw [onTgens_length]; exact hj6
  have hjs : j < (wordArrs Data.TWords).size := by rw [wordArrs_size]; exact hjl
  rw [getElem!_map' _ _ hjs]
  apply prep_rhoT (G := tGen j) _ (allBelowN_spec r_cert.2.1 hj6)
  rw [tGen_val hjl]
  exact prep_onTgens j hjl

theorem t32_gens_inv : ∀ j < Data.T32Chain.generators.size,
    pisInv 32 Data.T32Chain.generators[j]! (pinvCand 32 Data.T32Chain.generators[j]!) = true := by
  intro j hj
  have h := small_chain_certs.1
  simp only [smallChainOK, Bool.and_eq_true] at h
  exact (Bool.and_eq_true _ _ ▸ allBelowN_spec h.1.2 hj).2

theorem prep_t32_gens : ∀ j < Data.T32Chain.generators.size,
    PRep 32 Data.T32Chain.generators[j]! (permOfArr 32 Data.T32Chain.generators[j]!) :=
  fun j hj => (prep_permOfArr (t32_gens_inv j hj)).1

theorem t32_gens_size : Data.T32Chain.generators.size = 6 := by decide

theorem onT32_sub : onT32Chain.originalSubgroup = Subgroup.closure
    ((fun j => permOfArr 32 Data.T32Chain.generators[j]!) '' {j | j < 6}) := by
  rw [onT32Chain, smallChain, ofArrays_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, by simpa [t32_gens_size] using j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by rw [t32_gens_size]; exact hj⟩, rfl⟩

theorem rhoT_range :
    rhoT.range = onT32Chain.originalSubgroup := by
  rw [MonoidHom.range_eq_map, onT_top, MonoidHom.map_closure, ← Set.image_comp, onT32_sub]
  have h6 : ((wordArrs Data.TWords).map rTab).size = 6 := by
    rw [Array.size_map, wordArrs_size]; exact onTgens_length
  have := closure_eq_of_coversOK prep_rhoT_gen prep_t32_gens r_cert.2.2.2.1 r_cert.2.2.2.2
  rw [h6, t32_gens_size] at this
  exact this

theorem card_rhoT_range :
    Nat.card rhoT.range = 512 := by
  rw [rhoT_range, card_onT32]

theorem rhoT_injective :
    Function.Injective rhoT := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup rhoT.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rhoT).toEquiv, card_rhoT_range,
    card_onT] at h
  have hk : Nat.card rhoT.ker = 1 := by omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hk

@[expose] def zT :
    onT := ⟨onz, onz_mem_T⟩

theorem prep_z32 :
    PRep 32 Data.T32z onz32 := (prep_permOfArr t32_cert.2.1).1

theorem rhoT_z :
    rhoT zT = onz32 :=
  (prep_rhoT (G := zT) prep_z r_cert.2.2.1).unique prep_z32

theorem tabRep_of_prep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (hs : t.size = n)
    (h : PRep n t g) : TabRep t g := ⟨hs, fun i => h i⟩

theorem t32_gen_size
    {j : ℕ} (hj : j < Data.T32Chain.generators.size) :
    Data.T32Chain.generators[j]!.size = 32 := by
  have := t32_cert.1
  rw [Array.all_eq_true] at this
  have h := this j hj
  rw [beq_iff_eq] at h
  rwa [getElem!_pos _ j hj]

theorem t32_enumerates :
    Enumerates onT32Chain.originalSubgroup t32Enum.tabs.toList := by
  rw [onT32_sub]
  refine enumerates_closure ?_ ?_ t32_cert.2.2.2.1
  · rintro _ ⟨j, hj, rfl⟩
    have hj' : j < Data.T32Chain.generators.size := by rw [t32_gens_size]; exact hj
    exact ⟨j, hj', tabRep_of_prep (t32_gen_size hj') (prep_t32_gens j hj')⟩
  · intro j hj
    exact ⟨_, ⟨j, by rw [t32_gens_size] at hj; exact hj, rfl⟩,
      tabRep_of_prep (t32_gen_size hj) (prep_t32_gens j hj)⟩

theorem t32_center
    {y : Equiv.Perm (Fin 32)} (hy : y ∈ onT32Chain.originalSubgroup)
    (hc : ∀ j < 6, y * permOfArr 32 Data.T32Chain.generators[j]! =
      permOfArr 32 Data.T32Chain.generators[j]! * y) : y = 1 ∨ y = onz32 := by
  obtain ⟨t, ht, hr⟩ := t32_enumerates.complete y hy
  have hmem : t ∈ (t32Enum.tabs.filter fun x => Data.T32Chain.generators.all fun g =>
      CFSG.PSL3Four.Native.comp 32 x g == CFSG.PSL3Four.Native.comp 32 g x).toList := by
    rw [Array.toList_filter, List.mem_filter]
    refine ⟨ht, ?_⟩
    rw [Array.all_eq_true]
    intro j hj
    have hj6 : j < 6 := by rw [t32_gens_size] at hj; exact hj
    have hg := tabRep_of_prep (t32_gen_size hj) (prep_t32_gens j hj)
    rw [← getElem!_pos _ j hj, beq_iff_eq]
    exact (hr.comp hg).tab_eq (by rw [hc j hj6]; exact hg.comp hr)
  rw [t32_cert.2.2.2.2.2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl (hr.perm_eq CFSG.ComponentClassification.PSL3Four.TabRep.idTab)
  · exact Or.inr (hr.perm_eq (tabRep_of_prep t32_cert.2.2.1 prep_z32))

theorem z32_comm
    {j : ℕ} (hj : j < 6) :
    onz32 * permOfArr 32 Data.T32Chain.generators[j]! =
      permOfArr 32 Data.T32Chain.generators[j]! * onz32 := by
  have hmem : Data.T32z ∈ (t32Enum.tabs.filter fun x => Data.T32Chain.generators.all fun g =>
      CFSG.PSL3Four.Native.comp 32 x g == CFSG.PSL3Four.Native.comp 32 g x).toList := by
    rw [t32_cert.2.2.2.2.2]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  rw [Array.toList_filter, List.mem_filter, Array.all_eq_true] at hmem
  have hj' : j < Data.T32Chain.generators.size := by rw [t32_gens_size]; exact hj
  have h := hmem.2 j hj'
  rw [← getElem!_pos _ j hj', beq_iff_eq] at h
  have hz := tabRep_of_prep t32_cert.2.2.1 prep_z32
  have hg := tabRep_of_prep (t32_gen_size hj') (prep_t32_gens j hj')
  have h2 : TabRep (CFSG.PSL3Four.Native.comp 32 Data.T32z Data.T32Chain.generators[j]!)
      (permOfArr 32 Data.T32Chain.generators[j]! * onz32) := by
    rw [h]
    exact hg.comp hz
  exact (hz.comp hg).perm_eq h2

theorem z32_mem_centralizer :
    onT32Chain.originalSubgroup ≤ Subgroup.centralizer {onz32} := by
  rw [onT32_sub, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (z32_comm hj).symm

theorem gen_mem_range
    {j : ℕ} (hj : j < 6) :
    permOfArr 32 Data.T32Chain.generators[j]! ∈ rhoT.range := by
  rw [rhoT_range, onT32_sub]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem onT_centerIn :
    CFSG.centerIn onT = Subgroup.zpowers onz := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxc⟩ := Subgroup.mem_inf.1 hx
    have hcomm : ∀ j < 6, rhoT ⟨x, hxT⟩ * permOfArr 32 Data.T32Chain.generators[j]! =
        permOfArr 32 Data.T32Chain.generators[j]! * rhoT ⟨x, hxT⟩ := by
      intro j hj
      obtain ⟨y, hy⟩ := gen_mem_range hj
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hxc y y.2).symm
    have hmem : rhoT ⟨x, hxT⟩ ∈ onT32Chain.originalSubgroup := by
      rw [← rhoT_range]; exact ⟨_, rfl⟩
    rcases t32_center hmem hcomm with h1 | h2
    · have : (⟨x, hxT⟩ : onT) = 1 := rhoT_injective (by rw [h1, map_one])
      rw [show x = 1 from congrArg Subtype.val this]
      exact one_mem _
    · have : (⟨x, hxT⟩ : onT) = zT := rhoT_injective (by rw [h2, rhoT_z])
      rw [show x = onz from congrArg Subtype.val this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨onz_mem_T, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h1 : rhoT ⟨y, hy⟩ ∈ onT32Chain.originalSubgroup := by
      rw [← rhoT_range]; exact ⟨_, rfl⟩
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (z32_mem_centralizer h1)
    have : (⟨y, hy⟩ : onT) * zT = zT * ⟨y, hy⟩ :=
      rhoT_injective (by rw [map_mul, map_mul, rhoT_z]; exact h2)
    exact congrArg Subtype.val this


theorem at_on_sylow_center :
    onz ∈ onT ∧ onz ≠ 1 ∧ orderOf onz = 2 ∧ CFSG.centerIn onT = Subgroup.zpowers onz ∧
      onR.Nodup ∧ onR.length = 32 ∧ (∀ g ∈ onT, ∀ p ∈ onR, g p ∈ onR) ∧
      (∀ (g : onT) (k : Fin 32), onR.get (Fin.cast onR_length.symm (rhoT g k)) =
        (g : Equiv.Perm (Fin N)) (onR.get (Fin.cast onR_length.symm k))) ∧
      Function.Injective rhoT ∧ rhoT.range = onT32Chain.originalSubgroup ∧ rhoT zT = onz32 :=
  ⟨onz_mem_T, onz_ne_one, orderOf_onz, onT_centerIn, onR_nodup, onR_length,
    fun g hg p hp => onT_preserve g hg p hp, rhoT_spec, rhoT_injective, rhoT_range, rhoT_z⟩

end CFSG.ONSchreier
