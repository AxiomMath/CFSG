module

public import CFSG.Sporadic.ONOddCore.QuotTau
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.Sporadic.ONOddCore.GraphEnum

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

theorem pairGens_size (r : QuotRecord) : (pairGens r).size = 2 := rfl

theorem pairGens_get (r : QuotRecord) {j : ℕ} (hj : j < 2) :
    (pairGens r)[j]! = dbl 120 (qgArr j) (qiArr r j) := by
  interval_cases j <;> rfl

theorem finRange_length : (List.finRange 120).length = 120 := List.length_finRange

theorem pairRel_full_inj
    {t : Tab} {g g' : Equiv.Perm (Fin 120) × Equiv.Perm (Fin 120)}
    (h : pairRel 120 (List.finRange 120) t g) (h' : pairRel 120 (List.finRange 120) t g') :
    g = g' := by
  obtain ⟨-, hk⟩ := h
  obtain ⟨-, hk'⟩ := h'
  have key : ∀ x : Fin 120, g.1 x = g'.1 x ∧ g.2 x = g'.2 x := by
    intro x
    have hx : x.val < (List.finRange 120).length := by rw [finRange_length]; exact x.2
    have e : (List.finRange 120)[x.val] = x := List.getElem_finRange _
    obtain ⟨a1, a2⟩ := hk x.val hx
    obtain ⟨b1, b2⟩ := hk' x.val hx
    rw [e] at a1 a2 b1 b2
    exact ⟨Fin.ext (a1.symm.trans b1), Fin.ext (by omega)⟩
  exact Prod.ext (Equiv.ext fun x => (key x).1) (Equiv.ext fun x => (key x).2)

theorem pairRoot_rel : pairRel 120 (List.finRange 120) pairRoot 1 := by
  have h := pairRel_root (n := 120) (List.finRange 120)
  have e : ((List.finRange 120).map Fin.val).toArray = Array.range 120 :=
    Array.ext (by simp) fun i h1 h2 => by simp
  rwa [e] at h

theorem pair_step
    {r : QuotRecord} (hr : r ∈ localCert.records) :
    ∀ j < (pairGens r).size, ∀ t g, pairRel 120 (List.finRange 120) t g →
      pairRel 120 (List.finRange 120) (leftStep 240 (pairGens r) j t) (pairPerm r j * g) := by
  intro j hj t g ht
  rw [pairGens_size] at hj
  have h := pairRel_step (prep_qgArr hj).1 (prep_qiArr hr hj).1 (prep_qgArr hj).2
    (prep_qiArr hr hj).2 ht
  rw [finRange_length] at h
  rw [leftStep, pairGens_get r hj]
  exact h

theorem card_pair_closure
    {r : QuotRecord} (hr : r ∈ localCert.records) :
    Nat.card (Subgroup.closure (pairPerm r '' {j | j < 2})) = 40320 := by
  have h := rel_card (record_facts hr).2.1 (pair_step hr) pairRoot_rel
    (fun _ _ _ h h' => pairRel_full_inj h h') (fun _ _ _ h h' => pairRel_fun h h')
  rw [pairGens_size, (record_facts hr).2.2.1] at h
  exact h

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
