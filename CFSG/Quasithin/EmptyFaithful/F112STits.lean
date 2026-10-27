module

public import CFSG.Quasithin.EmptyFaithful.F112SSearch
public import CFSG.Sporadic.Schreier.TitsCentral
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.F112S

open CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem isElemAbelian_map' {G' : Type*} [Group G'] (f : G →* G') {A : Subgroup G}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map h _

theorem isPGroup_subgroupOf {D F : Subgroup G} (h : IsElemAbelian 2 F) :
    IsPGroup 2 (F.subgroupOf D) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := h.2 (x : G) x.2
  simpa using this

theorem exists_conj_le_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) {F : Subgroup X}
    (hF : IsPGroup 2 F) : ∃ g : X, ∀ x ∈ F, g * x * g⁻¹ ∈ (P : Subgroup X) := by
  obtain ⟨Q, hQ⟩ := hF.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, fun x hx => ?_⟩
  have h1 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (Q : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hx)
  have h2 : (MulAut.conj g) • (Q : Subgroup X) = (P : Subgroup X) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [h2] at h1
  simpa [MulAut.smul_def] using h1

theorem isElemAbelian_conj (g : G) {A : Subgroup G} (h : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) :=
  isElemAbelian_map' _ h

theorem card_conj (g : G) (A : Subgroup G) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Generic

section Tits

theorem exists_rep_of_all5
    {p : Array ℕ → Bool} (hp : all5 1755 titsSLevels p = true)
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsS) : ∃ a, Rep 1755 a g ∧ p a = true := by
  have hgQ : g ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hg
  exact all5_spec titsS_chainArrays (by norm_num : 0 < 4) titsLocalChains_check.2.1
    (by show (finList 1755 titsSBase).length = 5; simp [finList, titsSBase]) hp hgQ

@[expose] noncomputable def invPerm (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 invs[i]!

theorem prodAt_eq {i j : ℕ} (hi : i < numInvs) (hj : j < numInvs) : prodAt i j = prodIdx i j := by
  unfold prodAt prodTab
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem invs_ok (h : TitsRankCheck) {i : ℕ} (hi : i < numInvs) :
    isInvA 1755 invs[i]! (invCand 1755 invs[i]!) = true ∧ isInv invs[i]! = true := by
  have := h.1
  rw [invsOK, Array.all_eq_true] at this
  have h2 := this i hi
  rw [getElem!_pos invs i hi]
  simpa [Bool.and_eq_true] using h2

theorem invs_rep (h : TitsRankCheck) {i : ℕ} (hi : i < numInvs) :
    Rep 1755 invs[i]! (invPerm i) :=
  (rep_permOfArr (invs_ok h hi).1).1

theorem invPerm_sq (h : TitsRankCheck) {i : ℕ} (hi : i < numInvs) :
    invPerm i * invPerm i = 1 := by
  have hr := invs_rep h hi
  have h2 := (invs_ok h hi).2
  simp only [isInv, Bool.and_eq_true, Bool.not_eq_true'] at h2
  exact eq_of_eqA (rep_compA hr hr) rep_idA h2.1

theorem invPerm_ne_one (h : TitsRankCheck) {i : ℕ} (hi : i < numInvs) : invPerm i ≠ 1 := by
  have hr := invs_rep h hi
  have h2 := (invs_ok h hi).2
  simp only [isInv, Bool.and_eq_true, Bool.not_eq_true'] at h2
  intro h1
  have := (eqA_iff hr rep_idA).2 h1
  rw [h2.2] at this
  exact Bool.false_ne_true this

theorem invPerm_inj (h : TitsRankCheck) {i j : ℕ} (hi : i < numInvs) (hj : j < numInvs)
    (hij : invPerm i = invPerm j) : i = j := by
  have := h.2.1
  rw [invsDistinct, allLt_iff] at this
  have h2 := this i hi
  rw [allLt_iff] at h2
  have h3 := h2 j hj
  by_contra hne
  have h4 : eqA 1755 invs[i]! invs[j]! = true := (eqA_iff (invs_rep h hi) (invs_rep h hj)).2 hij
  simp [hne, h4] at h3

theorem invPerm_complete
    (h : TitsRankCheck) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsS) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∃ i < numInvs, invPerm i = x := by
  obtain ⟨a, ha, hp⟩ := exists_rep_of_all5 (p := fun a =>
    !(isInv a) || (List.range numInvs).any fun i => eqA 1755 a invs[i]!) h.2.2.1 hx
  have hinv : isInv a = true := by
    simp only [isInv, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(eqA_iff (rep_compA ha ha) rep_idA).2 hx2, ?_⟩
    by_contra hne
    have : eqA 1755 a (idA 1755) = true := by simpa using hne
    exact hx1 ((eqA_iff ha rep_idA).1 this)
  simp only [hinv, Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range] at hp
  obtain ⟨i, hi, hai⟩ := hp
  exact ⟨i, hi, ((eqA_iff ha (invs_rep h hi)).1 hai).symm⟩

theorem prodAt_spec (h : TitsRankCheck) {i j : ℕ} (hi : i < numInvs) (hj : j < numInvs)
    (hk : ∃ k < numInvs, invPerm k = invPerm i * invPerm j) :
    prodAt i j < numInvs ∧ invPerm (prodAt i j) = invPerm i * invPerm j := by
  rw [prodAt_eq hi hj]
  obtain ⟨k, hkN, hk⟩ := hk
  have hp : Rep 1755 (compA 1755 invs[i]! invs[j]!) (invPerm i * invPerm j) :=
    rep_compA (invs_rep h hi) (invs_rep h hj)
  have hex : ((List.range numInvs).find? fun k' =>
      eqA 1755 (compA 1755 invs[i]! invs[j]!) invs[k']!).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.2 hkN, (eqA_iff hp (invs_rep h hkN)).2 hk.symm⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 hex
  have hk'N : k' < numInvs := List.mem_range.1 (List.mem_of_find?_eq_some hk')
  have hk'eq := List.find?_some hk'
  have hperm : invPerm k' = invPerm i * invPerm j :=
    ((eqA_iff hp (invs_rep h hk'N)).1 hk'eq).symm
  have hidx : prodIdx i j = k' := by
    unfold prodIdx
    simp only [hk', Option.getD_some]
  rw [hidx]
  exact ⟨hk'N, hperm⟩

theorem invList_titsS
    (h : TitsRankCheck) : InvList titsS numInvs invPerm prodAt where
  ne_one _ hi := invPerm_ne_one h hi
  inj _ hi _ hj hij := invPerm_inj h hi hj hij
  complete _ hx hx2 hx1 := invPerm_complete h hx hx2 hx1
  mul _ hi _ hj hk := prodAt_spec h hi hj hk

theorem card_le_titsS
    (h : TitsRankCheck) {E : Subgroup (Equiv.Perm (Fin 1755))} (hES : E ≤ titsS)
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 32 :=
  card_le_of_search (invList_titsS h) h.2.2.2.1 hES hE

theorem card_le_titsD
    (h : TitsRankCheck) {F : Subgroup (Equiv.Perm (Fin 1755))} (hF : F ≤ titsD)
    (hE : IsElemAbelian 2 F) : Nat.card F ≤ 32 := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow titsSylow (isPGroup_subgroupOf (D := titsD) hE)
  have hle : F.map (MulAut.conj (g : Equiv.Perm (Fin 1755))).toMonoidHom ≤ titsS := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hg ⟨x, hF hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx)
    rw [coe_titsSylow, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have := card_le_titsS h hle (isElemAbelian_conj _ hE)
  rwa [card_conj] at this

end Tits

end CFSG.Quasithin.F112S
