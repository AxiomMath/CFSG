module

public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.YGroups.Exact.Model
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {n : ℕ}

theorem base_zero_mem_take (Q : RawSchreierDatum n) (hb : 1 ≤ Q.baseCount) :
    Q.base.get ⟨0, by omega⟩ ∈ Q.base.toList.take 1 := by
  rw [List.mem_take_iff_getElem]
  refine ⟨0, by simp; omega, ?_⟩
  simp [Vector.get]

theorem base_get_ne (Q : RawSchreierDatum n) (hb : 2 ≤ Q.baseCount) :
    Q.base.get ⟨0, by omega⟩ ≠ Q.base.get ⟨1, by omega⟩ := by
  intro h
  have hnd := Q.base_distinct
  have hl : Q.base.toList.length = Q.baseCount := by simp
  have h' : Q.base.toList[0]'(by omega) = Q.base.toList[1]'(by omega) := by
    simpa [Vector.get] using h
  have := (List.Nodup.getElem_inj_iff hnd).1 h'
  omega

theorem chain_twoTransitive (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (hb2 : 2 ≤ Q.baseCount)
    (h0 : Q.orbitSize ⟨0, by omega⟩ = n) (h1 : Q.orbitSize ⟨1, by omega⟩ = n - 1) :
    ∀ a b a' b' : Fin n, a ≠ b → a' ≠ b' → ∃ g ∈ Q.originalSubgroup, g a = a' ∧ g b = b' := by
  set i0 : Fin Q.baseCount := ⟨0, by omega⟩ with hi0
  set i1 : Fin Q.baseCount := ⟨1, by omega⟩ with hi1
  set b0 := Q.base.get i0 with hb0
  set b1 := Q.base.get i1 with hb1
  have hne : b0 ≠ b1 := base_get_ne Q hb2
  have hO0 : ∀ p : Fin n, ∃ g ∈ Q.originalSubgroup, g b0 = p := by
    have hcard : Nat.card (Q.orbitPoints i0) = n := by rw [← Q.orbitSize_eq_card, h0]
    have huniv : Q.orbitPoints i0 = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
    intro p
    have hp : p ∈ Q.orbitPoints i0 := by rw [huniv]; trivial
    rw [Q.orbitPoints_eq_orbit i0] at hp
    obtain ⟨⟨g, hg⟩, hgp⟩ := hp
    have hg' : g ∈ Q.originalSubgroup := by
      rw [← Q.levelSubgroup_zero_eq_original hQ]
      exact hg
    exact ⟨g, hg', hgp⟩
  have hO1 : ∀ p : Fin n, p ≠ b0 → ∃ g ∈ Q.originalSubgroup, g b0 = b0 ∧ g b1 = p := by
    have hcard : Nat.card (Q.orbitPoints i1) = n - 1 := by rw [← Q.orbitSize_eq_card, h1]
    have hsub : Q.orbitPoints i1 ⊆ {p | p ≠ b0} := by
      intro p hp
      rw [Q.orbitPoints_eq_orbit i1] at hp
      obtain ⟨⟨g, hg⟩, hgp⟩ := hp
      rw [Q.levelSubgroup_eq_pointwise_stabilizer hQ 1 (by omega)] at hg
      obtain ⟨hgO, hgfix⟩ := Subgroup.mem_inf.1 hg
      have hmem : b0 ∈ {b | b ∈ Q.base.toList.take 1} := base_zero_mem_take Q (by omega)
      have hfix : g b0 = b0 := (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).1 hgfix b0 hmem
      intro hpb
      have hgp' : g b1 = p := hgp
      apply hne
      apply g.injective
      rw [hfix, hgp', hpb]
    have hsize : ({p | p ≠ b0} : Set (Fin n)).ncard = n - 1 := by
      have : ({p | p ≠ b0} : Set (Fin n)) = ({b0}ᶜ : Set (Fin n)) := rfl
      rw [this, Set.ncard_compl, Set.ncard_singleton, Nat.card_fin]
    have heq : Q.orbitPoints i1 = {p | p ≠ b0} := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [hsize, ← Nat.card_coe_set_eq, hcard]
    intro p hp
    have hp' : p ∈ Q.orbitPoints i1 := by rw [heq]; exact hp
    rw [Q.orbitPoints_eq_orbit i1] at hp'
    obtain ⟨⟨g, hg⟩, hgp⟩ := hp'
    rw [Q.levelSubgroup_eq_pointwise_stabilizer hQ 1 (by omega)] at hg
    obtain ⟨hgO, hgfix⟩ := Subgroup.mem_inf.1 hg
    have hmem : b0 ∈ {b | b ∈ Q.base.toList.take 1} := base_zero_mem_take Q (by omega)
    exact ⟨g, hgO, (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).1 hgfix b0 hmem, hgp⟩
  have key : ∀ a b : Fin n, a ≠ b → ∃ g ∈ Q.originalSubgroup, g b0 = a ∧ g b1 = b := by
    intro a b hab
    obtain ⟨g1, hg1, hg1a⟩ := hO0 a
    have hne' : g1⁻¹ b ≠ b0 := by
      intro h
      apply hab
      have h2 : b = g1 b0 := by
        rw [← h]; simp
      rw [h2, hg1a]
    obtain ⟨h, hh, hhb0, hhb1⟩ := hO1 (g1⁻¹ b) hne'
    refine ⟨g1 * h, Q.originalSubgroup.mul_mem hg1 hh, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hhb0, hg1a]
    · rw [Equiv.Perm.mul_apply, hhb1]; simp
  intro a b a' b' hab hab'
  obtain ⟨s, hs, hsa, hsb⟩ := key a b hab
  obtain ⟨s', hs', hsa', hsb'⟩ := key a' b' hab'
  refine ⟨s' * s⁻¹, Q.originalSubgroup.mul_mem hs' (Q.originalSubgroup.inv_mem hs), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, ← hsa]; simp [hsa']
  · rw [Equiv.Perm.mul_apply, ← hsb]; simp [hsb']

theorem orderOf_eq_of_pow_checks {t : Array ℕ} (ht : validA n t = true) {m : ℕ}
    (h1 : eqA n (CFSG.Monster.B.Mathieu.powArr n t m) (idA n) = true) {p : ℕ} (hp : p.Prime)
    {e : ℕ} (hm : m = p ^ e) (he : 0 < e)
    (h2 : eqA n (CFSG.Monster.B.Mathieu.powArr n t (p ^ (e - 1))) (idA n) = false) :
    orderOf (permOfArr n t) = m := by
  have hrep := rep_of_validA ht
  have e1 : permOfArr n t ^ m = 1 :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep m) rep_idA).1 h1
  have e2 : permOfArr n t ^ (p ^ (e - 1)) ≠ 1 := fun h => by
    have := (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep (p ^ (e - 1))) rep_idA).2 h
    rw [this] at h2
    exact absurd h2 (by simp)
  have hdvd : orderOf (permOfArr n t) ∣ p ^ e := hm ▸ orderOf_dvd_of_pow_eq_one e1
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hje : j = e := by
    by_contra hne
    have hjle : j ≤ e - 1 := by omega
    have : permOfArr n t ^ (p ^ (e - 1)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hjo]
      exact pow_dvd_pow p hjle
    exact e2 this
  rw [hjo, hje, hm]

open CFSG.YGroups in
theorem originalSubgroup_ofArrays_eq_arrClosure {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ}
    {hk : k ≤ S.size} {bs : List (Fin n)} {hb : bs.Nodup} {W : Array (List ℤ)}
    {O : Array (Array ℕ)} (hOk : O.size = k) (hSO : ∀ i < k, S[i]! = O[i]!) :
    (RawSchreierDatum.ofArrays n hn S k hk bs hb W).originalSubgroup = arrClosure n O := by
  unfold RawSchreierDatum.originalSubgroup arrClosure
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, by rw [hSO i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, by rw [hSO i (by omega)]⟩

theorem centralizer_card_of_centOKP {p : ℕ} {S : Array (Array ℕ)} {k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ S.size) {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)}
    (hchain : rawChainOK n (S.extract 0 k) S (bs.map Fin.val).toArray W 1 = true)
    {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (hcent : centOKP p n S (bs.map Fin.val).toArray x rels gs ps c N = true) :
    Subgroup.closure (permsA n gs) = Subgroup.centralizer {X} ⊓
        (RawSchreierDatum.ofArrays n hn S k hk bs hb W).originalSubgroup ∧
      Nat.card (Subgroup.closure (permsA n gs)) = N := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S k hk bs hb W) (S.extract 0 k) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hchain).strong_inv
  exact ⟨centralizer_eq_of_ptailOKP hA hchain hx hrels hps hC hcomm hsift htail,
    (enumOK_spec hps hC).2.1.trans hsize⟩

theorem map_val_finRange' (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem <;> simp

theorem card_fixedPoints_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Nat.card {p : Fin n // g p = p} = ((List.range n).filter fun p => t[p]! == p).length := by
  have h1 : Nat.card {p : Fin n // g p = p} = (Finset.univ.filter fun p : Fin n => g p = p).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1]
  have h2 : (List.range n) = (List.finRange n).map Fin.val := (map_val_finRange' n).symm
  rw [h2, List.filter_map, List.length_map]
  have h3 : ((List.finRange n).filter ((fun p : ℕ => t[p]! == p) ∘ Fin.val)) =
      (List.finRange n).filter (fun p : Fin n => decide (g p = p)) := by
    apply List.filter_congr
    intro p _
    simp only [Function.comp_apply]
    rw [ht p]
    by_cases h : g p = p
    · simp [h]
    · have : ¬ ((g p : Fin n) : ℕ) = (p : ℕ) := fun e => h (Fin.ext e)
      simp [h, this]
  rw [h3]
  rw [Finset.card_def]
  simp [Finset.filter, Fin.univ_def]

theorem levels_size_get {L : Array Level} {B : List ℕ}
    (h : (L.toList.map fun l => l.pts.size) = B) {i : ℕ} (hi : i < B.length) :
    (L[i]!).pts.size = B[i] := by
  subst h
  rw [getElem!_pos L i (by simpa using hi)]
  simp [List.getElem_map]

end CFSG.RankThree.PartTwo.Sec4.Item434U38
