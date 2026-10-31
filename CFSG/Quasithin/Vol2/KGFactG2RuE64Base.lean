
module

public import CFSG.Quasithin.Vol2.KGFactG2RuBasic
public import CFSG.Sporadic.Schreier.RuSEnum

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

theorem isInvA_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    isInvA n t (invCand n t) = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  have hr := rep_invCand' ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem permOfArr_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    permOfArr n t = g :=
  Rep.unique (rep_permOfArr (isInvA_of_rep ht)).1 ht

theorem mul_comm_of_sq' {G : Type*} [Group G] {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have hab := hsq _ (E.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  rw [← inv_eq_of_mul_eq_one_right hab, mul_inv_rev, ha', hb']

theorem countP_range_eq_card (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter fun k => p k = true).card := by
  have h := Nat.count_eq_card_filter_range (fun k => p k = true) n
  rw [Nat.count] at h
  rw [← h]
  simp only [Bool.decide_eq_true]

theorem mem_g2Inv_toList {t : Array ℕ} : t ∈ g2Inv.toList ↔
    ∃ a < ruLevS[0]!.pts.size, ∃ b < ruLevS[1]!.pts.size,
      ruIsInvolA (prod2A 4060 ruLevS a b) = true ∧ prod2A 4060 ruLevS a b = t := by
  simp only [g2Inv, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq]

theorem ruChainS4060_baseCount : ruChainS4060.baseCount = 2 := rfl

section Inv

theorem ruChainS4060_arrays : ChainArrays ruChainS4060 ((ruField4060 4).extract 0 4)
    (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) (ruWordsArr 4 6 ruS4060ChainDerivations) :=
  ruChain_arrays ruInv_check.1

theorem g2Inv_spec {k : ℕ} (hk : k < g2Inv.size) :
    ∃ g ∈ ruS, orderOf g = 2 ∧ Rep 4060 g2Inv[k]! g := by
  have h := ruInv_check.1
  have hA := ruChainS4060_arrays
  have hmem : g2Inv[k]! ∈ g2Inv.toList := by
    rw [getElem!_pos g2Inv k hk]
    exact Array.getElem_mem_toList hk
  obtain ⟨a, ha, b, hb, hinv, he⟩ := mem_g2Inv_toList.1 hmem
  have hrep := chain_rep_prod2A hA h (by rw [ruChainS4060_baseCount]) ha hb
  refine ⟨_, ?_, (ruIsInvolA_iff hrep).1 hinv, he ▸ hrep⟩
  rw [← ruChainS4060_sub]
  exact Subgroup.mul_mem _ (chain_levT_mem_original hA (by norm_num) h (by decide) ha)
    (chain_levT_mem_original hA (by norm_num) h (by decide) hb)

theorem exists_g2Inv {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruS) (h2 : orderOf g = 2) :
    ∃ k < g2Inv.size, Rep 4060 g2Inv[k]! g := by
  have h := ruInv_check.1
  have hA := ruChainS4060_arrays
  rw [← ruChainS4060_sub] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := chain_exists_prod2 hA (by norm_num) h
    (by rw [ruChainS4060_baseCount]) (fun i hi hi' => by rw [ruChainS4060_baseCount] at hi'; omega)
    hg
  have hrep := chain_rep_prod2A hA h (by rw [ruChainS4060_baseCount]) ha hb
  have hmem : prod2A 4060 ruLevS a b ∈ g2Inv.toList :=
    mem_g2Inv_toList.2 ⟨a, ha, b, hb, (ruIsInvolA_iff hrep).2 h2, rfl⟩
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
  refine ⟨k, by simpa using hk, ?_⟩
  rw [getElem!_pos g2Inv k (by simpa using hk)]
  simp only [Array.getElem_toList] at hke
  rw [hke]
  exact hrep

def g2InvElt (k : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 g2Inv[k]!

theorem rep_g2InvElt {k : ℕ} (hk : k < g2Inv.size) : Rep 4060 g2Inv[k]! (g2InvElt k) := by
  obtain ⟨g, -, -, hg⟩ := g2Inv_spec hk
  rw [g2InvElt, permOfArr_of_rep hg]
  exact hg

end Inv

theorem g2ComM_get {i j : ℕ} (hi : i < g2Inv.size) (hj : j < g2Inv.size) :
    (g2ComM[i]!)[j]! = g2Com g2Inv[i]! g2Inv[j]! := by
  rw [g2ComM, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem g2KeepM_get {i j : ℕ} (hi : i < g2Inv.size) (hj : j < g2Inv.size) :
    (g2KeepM[i]!)[j]! = ((i != j) && (g2ComM[i]!)[j]! && decide (63 ≤ g2Cn i j)) := by
  rw [g2KeepM, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem g2DegA_get {i : ℕ} (hi : i < g2Inv.size) :
    g2DegA[i]! = (List.range g2Inv.size).countP fun j => (g2KeepM[i]!)[j]! := by
  rw [g2DegA, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem g2InWM_get {r j : ℕ} (hr : r < 4) (hj : j < g2Inv.size) :
    (g2InWM[r]!)[j]! = (g2WrArr[r]!).any fun u => eqA 4060 g2Inv[j]! u := by
  rw [g2InWM, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_map, ← getElem!_pos g2Inv j hj]

theorem g2Com_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hu : Rep 4060 u h) : g2Com t u = true ↔ g * h = h * g := by
  rw [g2Com, Bool.and_eq_true, eqA_iff (rep_compA ht hu) (rep_compA hu ht)]
  refine ⟨fun h => h.2, fun hgh => ⟨allLt_iff.2 fun x hx => ?_, hgh⟩⟩
  have h1 := (rep_compA ht hu).apply (by omega : x < 4060)
  have h2 := (rep_compA hu ht).apply (by omega : x < 4060)
  rw [compA_get (by omega : x < 4060)] at h1
  rw [compA_get (by omega : x < 4060)] at h2
  rw [beq_iff_eq, h1, h2, hgh]

open scoped Classical in
def g2Idx (E : Subgroup (Equiv.Perm (Fin 4060))) : Finset ℕ :=
  (Finset.range g2Inv.size).filter fun k => g2InvElt k ∈ E

theorem mem_g2Idx {E : Subgroup (Equiv.Perm (Fin 4060))} {k : ℕ} :
    k ∈ g2Idx E ↔ k < g2Inv.size ∧ g2InvElt k ∈ E := by
  classical
  unfold g2Idx
  rw [Finset.mem_filter, Finset.mem_range]

theorem lt_of_mem_g2Idx {E : Subgroup (Equiv.Perm (Fin 4060))} {k : ℕ} (hk : k ∈ g2Idx E) :
    k < g2Inv.size :=
  (mem_g2Idx.1 hk).1

theorem mem_of_mem_g2Idx {E : Subgroup (Equiv.Perm (Fin 4060))} {k : ℕ} (hk : k ∈ g2Idx E) :
    g2InvElt k ∈ E :=
  (mem_g2Idx.1 hk).2

section Idx

variable
  {E : Subgroup (Equiv.Perm (Fin 4060))}

theorem exists_mem_g2Idx (hES : E ≤ ruS) (hE : ∀ x ∈ E, x * x = 1) {x : Equiv.Perm (Fin 4060)}
    (hx : x ∈ E) (hx1 : x ≠ 1) : ∃ k ∈ g2Idx E, g2InvElt k = x := by
  have h2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hE x hx) hx1
  obtain ⟨k, hk, hrep⟩ := exists_g2Inv (hES hx) h2
  have he : g2InvElt k = x := Rep.unique (rep_g2InvElt hk) hrep
  exact ⟨k, mem_g2Idx.2 ⟨hk, he ▸ hx⟩, he⟩

theorem card_g2Idx (hES : E ≤ ruS) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E - 1 ≤ (g2Idx E).card := by
  classical
  have hsub : (E : Set (Equiv.Perm (Fin 4060))) ⊆
      ↑(insert 1 ((g2Idx E).image g2InvElt)) := by
    intro x hx
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · obtain ⟨k, hk, he⟩ := exists_mem_g2Idx hES hE hx hx1
      exact Or.inr (Finset.mem_image.2 ⟨k, hk, he⟩)
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h0 : Nat.card E = (E : Set (Equiv.Perm (Fin 4060))).ncard := Nat.card_coe_set_eq _
  have h2 := Finset.card_insert_le (1 : Equiv.Perm (Fin 4060)) ((g2Idx E).image g2InvElt)
  have h3 : ((g2Idx E).image g2InvElt).card ≤ (g2Idx E).card := Finset.card_image_le
  omega

theorem comM_of_mem_g2Idx (hE : ∀ x ∈ E, x * x = 1) {i j : ℕ} (hi : i ∈ g2Idx E)
    (hj : j ∈ g2Idx E) : (g2ComM[i]!)[j]! = true := by
  rw [g2ComM_get (lt_of_mem_g2Idx hi) (lt_of_mem_g2Idx hj),
    g2Com_iff (rep_g2InvElt (lt_of_mem_g2Idx hi)) (rep_g2InvElt (lt_of_mem_g2Idx hj))]
  exact mul_comm_of_sq' hE (mem_of_mem_g2Idx hi) (mem_of_mem_g2Idx hj)

theorem keepM_of_mem_g2Idx (hE : ∀ x ∈ E, x * x = 1) (h63 : 63 ≤ (g2Idx E).card) {i j : ℕ}
    (hi : i ∈ g2Idx E) (hj : j ∈ g2Idx E) (hij : i ≠ j) : (g2KeepM[i]!)[j]! = true := by
  rw [g2KeepM_get (lt_of_mem_g2Idx hi) (lt_of_mem_g2Idx hj)]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  refine ⟨⟨hij, comM_of_mem_g2Idx hE hi hj⟩, ?_⟩
  rw [g2Cn, countP_range_eq_card]
  refine le_trans h63 (Finset.card_le_card fun k hk => ?_)
  rw [Finset.mem_filter, Bool.and_eq_true]
  exact ⟨Finset.mem_range.2 (lt_of_mem_g2Idx hk), comM_of_mem_g2Idx hE hi hk,
    comM_of_mem_g2Idx hE hj hk⟩

theorem deg_of_mem_g2Idx (hE : ∀ x ∈ E, x * x = 1) (h63 : 63 ≤ (g2Idx E).card) {i : ℕ}
    (hi : i ∈ g2Idx E) : 62 ≤ g2DegA[i]! := by
  rw [g2DegA_get (lt_of_mem_g2Idx hi), countP_range_eq_card]
  have h1 : ((g2Idx E).erase i).card ≤
      ((Finset.range g2Inv.size).filter fun j => (g2KeepM[i]!)[j]! = true).card :=
    Finset.card_le_card fun j hj => by
      rw [Finset.mem_erase] at hj
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_mem_g2Idx hj.2),
        keepM_of_mem_g2Idx hE h63 hi hj.2 (Ne.symm hj.1)⟩
  rw [Finset.card_erase_of_mem hi] at h1
  omega

end Idx

end CFSG.Quasithin.H13.Ch4.G2Ru
