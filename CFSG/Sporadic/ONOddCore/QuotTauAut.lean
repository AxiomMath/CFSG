module

public import CFSG.Sporadic.ONOddCore.QuotTau
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.Sporadic.ONOddCore.GraphEnum
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Quasithin.Recognition.CertChain

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates)

@[expose] def recK (k : ℕ) : QuotRecord := localCert.records.getD k default

theorem records_length :
    localCert.records.length = 12 := by
  have h := r3e_on_local_automorphism_certificate_data.2.2.1
  have := congrArg List.length h
  simpa [tripleList] using this

theorem recK_mem
    {k : ℕ} (hk : k < 12) : recK k ∈ localCert.records :=
  getD_mem (by rw [records_length]; exact hk) _

theorem recK_triple
    {k : ℕ} (hk : k < 12) :
    ((recK k).diag, (recK k).field, (recK k).graph) = tripleList.getD k (0, 0, 0) := by
  have h := r3e_on_local_automorphism_certificate_data.2.2.1
  have hk' : k < localCert.records.length := by rw [records_length]; exact hk
  have := congrArg (fun l => l.getD k (0, 0, 0)) h
  rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map] at this
  rw [← this, recK, List.getD_eq_getElem _ _ hk']

theorem recK_bounds
    {k : ℕ} (hk : k < 12) :
    (recK k).diag < 3 ∧ (recK k).field < 2 ∧ (recK k).graph < 2 := by
  have h := recK_triple hk
  interval_cases k <;> simp only [tripleList, List.getD_cons_succ, List.getD_cons_zero,
    Prod.mk.injEq] at h <;> omega

@[expose] def pairPerm (r : QuotRecord) (j : ℕ) : Equiv.Perm (Fin 120) × Equiv.Perm (Fin 120) :=
  (qGenPerm j, qImgPerm r j)

@[expose] def pairEmbOf (n : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + n)) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin n) (Fin n))

theorem pairEmbOf_injective (n : ℕ) : Function.Injective (pairEmbOf n) :=
  (finSumFinEquiv.permCongrHom).injective.comp Equiv.Perm.sumCongrHom_injective

theorem pairEmbOf_apply {n : ℕ} (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) (x : Fin (n + n)) :
    pairEmbOf n g x = finSumFinEquiv (Sum.map g.1 g.2 (finSumFinEquiv.symm x)) := rfl

theorem prep_dbl_of {n : ℕ} {A B : Array ℕ} {a b : Equiv.Perm (Fin n)} (hA : PRep n A a)
    (hB : PRep n B b) (hs : A.size = n) (hs' : B.size = n) :
    PRep (n + n) (dbl n A B) (pairEmbOf n (a, b)) := by
  intro x
  rw [pairEmbOf_apply]
  rcases Nat.lt_or_ge x.val n with h | h
  · have e : (finSumFinEquiv (m := n) (n := n)).symm x = Sum.inl ⟨x.val, h⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
    rw [e]
    simp only [Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
    unfold dbl
    rw [getElem!_pos _ x.val (by simp only [Array.size_append, Array.size_map, hs, hs']; omega),
      Array.getElem_append_left (by omega), ← getElem!_pos A x.val (by omega)]
    exact hA ⟨x.val, h⟩
  · have hx : x.val - n < n := by omega
    have e : (finSumFinEquiv (m := n) (n := n)).symm x = Sum.inr ⟨x.val - n, hx⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
      omega
    rw [e]
    simp only [Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
    unfold dbl
    rw [getElem!_pos _ x.val (by simp only [Array.size_append, Array.size_map, hs, hs']; omega),
      Array.getElem_append_right (by omega)]
    simp only [Array.getElem_map, hs]
    rw [← getElem!_pos B (x.val - n) (by omega), hB ⟨x.val - n, hx⟩]
    omega

theorem permOfArr_pairGens
    {r : QuotRecord} (hr : r ∈ localCert.records) {k : ℕ} (hk : k < 2) :
    CFSG.Monster.B.Co2.permOfArr 240 (pairGens r)[k]! = pairEmbOf 120 (pairPerm r k) := by
  have hp := prep_dbl_of (prep_qgArr hk).1 (prep_qiArr hr hk).1 (prep_qgArr hk).2
    (prep_qiArr hr hk).2
  rw [pairGens_get r hk]
  have hv : ∀ i (hi : i < 240), (dbl 120 (qgArr k) (qiArr r k))[i]! =
      ((pairEmbOf 120 (pairPerm r k)) ⟨i, hi⟩ : ℕ) := fun i hi => hp ⟨i, hi⟩
  have hc : (∀ i < 240, (dbl 120 (qgArr k) (qiArr r k))[i]! < 240) ∧ ∀ i < 240, ∀ j < 240,
      (dbl 120 (qgArr k) (qiArr r k))[i]! = (dbl 120 (qgArr k) (qiArr r k))[j]! → i = j :=
    ⟨fun i hi => by
      rw [hv i hi]
      exact Fin.isLt _, fun i hi j hj hij => by
      rw [hv i hi, hv j hj] at hij
      exact Fin.mk.inj ((pairEmbOf 120 (pairPerm r k)).injective (Fin.ext hij))⟩
  ext x
  rw [CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
  exact hp x

theorem card_closure_pairGens
    {r : QuotRecord} (hr : r ∈ localCert.records) :
    Nat.card (Subgroup.closure {g | ∃ k < (pairGens r).size,
      CFSG.Monster.B.Co2.permOfArr 240 (pairGens r)[k]! = g} :
        Subgroup (Equiv.Perm (Fin 240))) =
      Nat.card (Subgroup.closure (pairPerm r '' {j | j < 2})) := by
  have he : {g | ∃ k < (pairGens r).size, CFSG.Monster.B.Co2.permOfArr 240 (pairGens r)[k]! = g} =
      ⇑(pairEmbOf 120) '' (pairPerm r '' {j | j < 2}) := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [pairGens_size] at hk
      exact ⟨pairPerm r k, ⟨k, hk, rfl⟩, (permOfArr_pairGens hr hk).symm⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, by rw [pairGens_size]; exact hk, permOfArr_pairGens hr hk⟩
  have h := Subgroup.card_map_of_injective (K := Subgroup.closure (pairPerm r '' {j | j < 2}))
    (pairEmbOf_injective 120)
  rw [MonoidHom.map_closure] at h
  rw [he]
  exact h

theorem card_pair_closure
    {r : QuotRecord} (hr : r ∈ localCert.records) :
    Nat.card (Subgroup.closure (pairPerm r '' {j | j < 2})) = 40320 := by
  rw [← card_closure_pairGens hr, ← (record_facts hr).2.2.1]
  exact CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (O := pairGens r)
    (base := pairChainBaseL) (by norm_num) (by decide) Nat.one_pos
    (by rw [pairGens_size, pairStrongs_size]; norm_num) (pairStrongs_get r) (record_facts hr).2.1

theorem fst_pairPerm_image (r : QuotRecord) :
    Prod.fst '' (pairPerm r '' {j | j < 2}) = {g | g ∈ [qGenPerm 0, qGenPerm 1]} := by
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
    pairPerm]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, by norm_num, rfl⟩, rfl⟩
    · exact ⟨_, ⟨1, by norm_num, rfl⟩, rfl⟩

theorem card_qGroup :
    Nat.card qGroup = 40320 := by rw [qGroup_eq_RM, card_RM]

theorem exists_quotHom
    {r : QuotRecord} (hr : r ∈ localCert.records) :
    ∃ φ : qGroup →* Equiv.Perm (Fin 120),
      ∀ j (hj : j < 2), φ ⟨qGenPerm j, qGenPerm_mem j hj⟩ = qImgPerm r j := by
  have hcl : Subgroup.closure (Prod.fst '' (pairPerm r '' {j | j < 2})) = qGroup := by
    rw [fst_pairPerm_image]
    rfl
  obtain ⟨φ, hφ⟩ := exists_hom_of_graph (pairPerm r '' {j | j < 2}) (by
    rw [card_pair_closure hr, hcl, card_qGroup])
  let e : qGroup ≃* Subgroup.closure (Prod.fst '' (pairPerm r '' {j | j < 2})) :=
    MulEquiv.subgroupCongr hcl.symm
  refine ⟨φ.comp e.toMonoidHom, fun j hj => ?_⟩
  have := hφ (pairPerm r j) ⟨j, hj, rfl⟩
  exact this

@[expose] def quotHom
    (k : ℕ) : qGroup →* Equiv.Perm (Fin 120) :=
  if hk : k < 12 then Classical.choose (exists_quotHom (recK_mem hk)) else 1

theorem quotHom_gen
    {k : ℕ} (hk : k < 12) {j : ℕ} (hj : j < 2) :
    quotHom k ⟨qGenPerm j, qGenPerm_mem j hj⟩ = qImgPerm (recK k) j := by
  rw [quotHom, dite_eq_left hk]
  exact Classical.choose_spec (exists_quotHom (recK_mem hk)) j hj

theorem qGroup_closure_top : Subgroup.closure {g : qGroup | g ∈ qGens} = ⊤ := by
  apply Subgroup.map_injective qGroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [qGroup]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, qGens, List.mem_cons, List.not_mem_nil,
    or_false, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem qGens_map
    (k : ℕ) (hk : k < 12) :
    qGens.map (quotHom k) = [qImgPerm (recK k) 0, qImgPerm (recK k) 1] := by
  simp only [qGens, List.map_cons, List.map_nil]
  rw [quotHom_gen hk (by norm_num), quotHom_gen hk (by norm_num)]

theorem quotHom_eq_quotFun
    {k : ℕ} (hk : k < 12) (x : qGroup) :
    quotHom k x = quotFun (recK k) x := by
  rw [quotFun, ← qGens_map k hk, substFun_eq_of_hom qGens qGroup_closure_top]

theorem onX_le_qGroup :
    onX ≤ qGroup := qGroup_eq_RM ▸ onX_le_RM

theorem xGen_mem_qGroup
    {m : ℕ} (hm : m < 12) : xGen m ∈ qGroup :=
  onX_le_qGroup (xGenX m hm).2

theorem quotHom_xGen
    {k : ℕ} (hk : k < 12) {m : ℕ} (hm : m < 12) :
    quotHom k ⟨xGen m, xGen_mem_qGroup hm⟩ =
      ((sigmaX (recK k).diag (recK k).field (recK k).graph (xGenX m hm) : onX) :
        Equiv.Perm (Fin 120)) := by
  have hr := recK_mem hk
  have hw : ∀ l ∈ xWords[m]!, 1 ≤ l ∧ l ≤ 2 := quot_facts.2.2.1 _ (by
    rw [getElem!_pos xWords m (by simpa [xWords] using hm)]; exact Array.getElem_mem _)
  have e1 : (⟨xGen m, xGen_mem_qGroup hm⟩ : qGroup) = evalPos qGens xWords[m]! := by
    apply Subtype.ext
    show xGen m = qGroup.subtype (evalPos qGens xWords[m]!)
    rw [map_evalPos, xGen_eq hm]
    rfl
  rw [e1, map_evalPos, qGens_map k hk, sigmaX_xGen _ _ _ hm]
  have hrep1 := prep_posArr (n := 120) (gs := #[qiArr (recK k) 0, qiArr (recK k) 1])
    (G := [qImgPerm (recK k) 0, qImgPerm (recK k) 1]) (fun l h1 h2 => by
      simp only [List.length_cons, List.length_nil] at h2
      interval_cases l
      · exact (prep_qiArr hr (by norm_num)).1
      · exact (prep_qiArr hr (by norm_num)).1) _ (fun l hl => by simpa using hw l hl)
  have hsig : ∀ l ∈ sigWord (recK k).diag (recK k).field (recK k).graph m,
      1 ≤ l ∧ l ≤ xGens.length := by
    obtain ⟨hd, hf, hg⟩ := recK_bounds hk
    have : ∀ d < 3, ∀ f < 2, ∀ g < 2, ∀ m < 12, ∀ l ∈ sigWord d f g m, 1 ≤ l ∧ l ≤ 12 := by
      decide
    simpa [xGens] using this _ hd _ hf _ hg m hm
  have hrep2 := prep_posArr (n := 120) (gs := Data.PSL120Chain.generators) (G := xGens)
    (fun l h1 h2 => by
      have hl : l - 1 < 12 := by simp [xGens] at h2; omega
      rw [Array.getD_eq_getD_getElem?, getElem?_pos _ _ (by rw [psl120_size]; exact hl),
        Option.getD_some, List.getD_eq_getElem _ _ (by simpa [xGens] using hl)]
      simp only [xGens, List.getElem_map, List.getElem_range]
      rw [← getElem!_pos _ _ (by rw [psl120_size]; exact hl)]
      exact prep_smallGen small_chain_certs.2.2.2.2.1 _ (by rw [psl120_size]; exact hl)) _ hsig
  exact eq_of_peq hrep1 hrep2 ((record_facts hr).2.2.2 m hm)

theorem onX_eq_closure :
    onX = Subgroup.closure (xGen '' {m | m < 12}) := by
  rw [onX, onPSL120Chain, smallChain_sub, psl120_size]
  rfl

theorem closure_xGenX_top :
    Subgroup.closure {x : onX | ∃ m, ∃ hm : m < 12, x = xGenX m hm} = ⊤ := by
  apply Subgroup.map_injective onX.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [onX_eq_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, rfl⟩

theorem quotHom_eq_sigma
    {k : ℕ} (hk : k < 12) (x : onX) :
    quotHom k ⟨x, onX_le_qGroup x.2⟩ =
      ((sigmaX (recK k).diag (recK k).field (recK k).graph x : onX) : Equiv.Perm (Fin 120)) := by
  let f₁ : onX →* Equiv.Perm (Fin 120) :=
    (quotHom k).comp (Subgroup.inclusion onX_le_qGroup)
  let f₂ : onX →* Equiv.Perm (Fin 120) :=
    onX.subtype.comp (sigmaX (recK k).diag (recK k).field (recK k).graph).toMonoidHom
  have h : f₁ = f₂ := by
    apply MonoidHom.eq_of_eqOn_dense closure_xGenX_top
    rintro _ ⟨m, hm, rfl⟩
    exact quotHom_xGen hk hm
  exact DFunLike.congr_fun h x

end CFSG.Sporadic.ONOddCore
