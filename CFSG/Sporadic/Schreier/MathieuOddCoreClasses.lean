module

public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Schreier.MathieuOddCoreWitness
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Mathlib

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

section Group

variable {M : Type*} [Group M]

@[expose] def centralizerIn (H : Subgroup M) (u : M) : Subgroup M :=
  H ⊓ Subgroup.centralizer {u}

@[expose] def conjClass (H : Subgroup M) (u : M) : Set M := {x | ∃ c ∈ H, x = c * u * c⁻¹}

theorem mem_centralizerIn {H : Subgroup M} {u x : M} :
    x ∈ centralizerIn H u ↔ x ∈ H ∧ x * u = u * x := by
  rw [centralizerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem conjClass_finite (H : Subgroup M) [Finite H] (u : M) : (conjClass H u).Finite := by
  have : conjClass H u = Set.range fun c : H => (c : M) * u * (c : M)⁻¹ := by
    ext x
    exact ⟨fun ⟨c, hc, hx⟩ => ⟨⟨c, hc⟩, hx.symm⟩, fun ⟨c, hx⟩ => ⟨c, c.2, hx.symm⟩⟩
  rw [this]
  exact Set.finite_range _

theorem ncard_conjClass_mul_card (H : Subgroup M) [Finite H] (u : M) :
    (conjClass H u).ncard * Nat.card (centralizerIn H u) = Nat.card H := by
  let : MulAction H M := MulAction.compHom M ((MulAut.conj : M →* MulAut M).comp H.subtype)
  have hsmul : ∀ (h : H) (x : M), h • x = (h : M) * x * (h : M)⁻¹ := fun _ _ => rfl
  have horbit : MulAction.orbit H u = conjClass H u := by
    ext x
    simp only [MulAction.mem_orbit_iff, hsmul, conjClass, Set.mem_ofPred_eq]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, c.2, hc.symm⟩, fun ⟨c, hc, hx⟩ => ⟨⟨c, hc⟩, hx.symm⟩⟩
  have hstab : (MulAction.stabilizer H u).map H.subtype = centralizerIn H u := by
    ext x
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, hsmul, Subgroup.coe_subtype,
      mem_centralizerIn]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      calc (c : M) * u = (c : M) * u * (c : M)⁻¹ * c := by group
        _ = u * c := by rw [hc]
    · rintro ⟨hx, hxu⟩
      exact ⟨⟨x, hx⟩, by simp [hxu], rfl⟩
  have hidx := MulAction.index_stabilizer (G := H) (x := u)
  have hmul := (MulAction.stabilizer H u).card_mul_index
  rw [← hstab, Subgroup.card_map_of_injective H.subtype_injective, ← horbit, ← hidx, mul_comm]
  exact hmul

theorem centralizerIn_eq_of_le (H : Subgroup M) [Finite H] (u : M) {K : Subgroup M}
    (hK : K ≤ centralizerIn H u) {c : ℕ} (hc : c ≤ (conjClass H u).ncard)
    (hcard : c * Nat.card K = Nat.card H) : centralizerIn H u = K := by
  have hos := ncard_conjClass_mul_card H u
  have hfin : Finite (centralizerIn H u) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hKC : Nat.card K ≤ Nat.card (centralizerIn H u) := Subgroup.card_le_of_le hK
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hle : Nat.card (centralizerIn H u) ≤ Nat.card K := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : c * Nat.card K < c * Nat.card (centralizerIn H u) :=
      Nat.mul_lt_mul_of_pos_left hlt hc0
    have h2 : c * Nat.card (centralizerIn H u) ≤
        (conjClass H u).ncard * Nat.card (centralizerIn H u) := Nat.mul_le_mul_right _ hc
    omega
  exact (Subgroup.eq_of_le_of_card_ge hK hle).symm

theorem centralizerIn_conj (H : Subgroup M) {c : M} (hc : c ∈ H) (u : M) :
    centralizerIn H (c * u * c⁻¹) = (centralizerIn H u).map (MulAut.conj c).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, mem_centralizerIn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hx, hxu⟩
    refine ⟨c⁻¹ * x * c, ⟨H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩, by group⟩
    calc c⁻¹ * x * c * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [hxu]
      _ = u * (c⁻¹ * x * c) := by group
  · rintro ⟨y, ⟨hy, hyu⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hc hy) (H.inv_mem hc), ?_⟩
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hyu]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group

end Group

variable {n : ℕ}

@[expose] def cosetOrderTables (Q : RawSchreierDatum n) (g₀ : Equiv.Perm (Fin n)) (m : ℕ) :
    List Table :=
  filterProducts n (ordTest n m) (levelTables Q) (toTable g₀) []

theorem forall₂_cosetOrderTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (g₀ : Equiv.Perm (Fin n)) {m : ℕ} (hm : 0 < m) :
    List.Forall₂ (Rep n) (cosetOrderTables Q g₀ m)
      (((enumeration Q).map (g₀ * ·)).filter fun h => decide (orderOf h = m)).reverse := by
  have h := filterProducts_spec (P := fun h : Equiv.Perm (Fin n) => orderOf h = m)
    (fun T g hT => ordTest_iff perm_faithful hT hm) (forall₂_levelTables hn Q)
    (rep_toTable hn g₀) (acc := []) (accG := []) List.Forall₂.nil
  simp only [List.append_nil] at h
  exact h

theorem exists_conj_of_repsOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup) {m : ℕ} (hm : 0 < m)
    (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, g₀⁻¹ * r ∈ Q.originalSubgroup ∧ orderOf r = m) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ m) (reps.map toTable) cap = true) :
    (∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = m →
      ∃ r ∈ reps, ∃ c ∈ Q.originalSubgroup, u = c * r * c⁻¹) ∧
    (∀ r ∈ reps, (conjClosure n gens gensInv (toTable r) cap).1.size ≤
      (conjClass Q.originalSubgroup r).ncard) := by
  set H := Q.originalSubgroup
  set L := enumeration Q
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_enumeration_iff Q hQ
  set XG := (L.map (g₀ * ·)).filter fun h => decide (orderOf h = m)
  have hX := forall₂_cosetOrderTables hn Q g₀ hm
  have hXG : ∀ u, u ∈ XG ↔ g₀⁻¹ * u ∈ H ∧ orderOf u = m := by
    intro u
    simp only [XG, List.mem_filter, List.mem_map, hmem, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h, hh, rfl⟩, ho⟩
      exact ⟨by simpa using hh, ho⟩
    · rintro ⟨hu, ho⟩
      exact ⟨⟨g₀⁻¹ * u, hu, by group⟩, ho⟩
  have hclosed : ∀ c ∈ H, ∀ u, g₀⁻¹ * u ∈ H → orderOf u = m →
      g₀⁻¹ * (c * u * c⁻¹) ∈ H ∧ orderOf (c * u * c⁻¹) = m := by
    intro c hc u hu ho
    refine ⟨?_, (MulEquiv.orderOf_eq (MulAut.conj c) u).trans ho⟩
    have : g₀⁻¹ * (c * u * c⁻¹) = (g₀⁻¹ * c * g₀) * (g₀⁻¹ * u) * c⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (hg₀ c hc) hu) (H.inv_mem hc)
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, hsum⟩ := hok
  set cl := (reps.map toTable).map fun r => (r, conjClosure n gens gensInv r cap)
  have hcl : ∀ c ∈ cl, ∃ r ∈ reps, c.1 = toTable r ∧
      c.2 = conjClosure n gens gensInv (toTable r) cap := by
    intro c hc
    simp only [cl, List.map_map, List.mem_map, Function.comp] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    exact ⟨r, hr, rfl, rfl⟩
  have hentries : ∀ c ∈ cl, ∀ T ∈ c.2.1.toList, ∃ r ∈ reps, Rep n c.1 r ∧
      ∃ d ∈ H, Rep n T (d * r * d⁻¹) := by
    intro c hc T hT
    obtain ⟨r, hr, h1, -⟩ := hcl c hc
    have hrep : Rep n c.1 r := h1 ▸ rep_toTable hn r
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec H hg hrep (htree c hc) k hk
    refine ⟨r, hr, hrep, d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.2.1 k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList
  have hU : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, -, -, d, -, hrep⟩ := hentries c hc T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hU hdist
  have hUmem : ∀ T ∈ U, ∃ r ∈ reps, ∃ d ∈ H, tablePerm n T = d * r * d⁻¹ := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, hr, -, d, hd, hrep⟩ := hentries c hc T hT
    exact ⟨r, hr, d, hd, tablePerm_eq hrep⟩
  have hsub : U.map (tablePerm n) ⊆ XG := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨r, hr, d, hd, heq⟩ := hUmem T hT
    rw [heq, hXG]
    exact hclosed d hd r (hreps r hr).1 (hreps r hr).2
  have hlen : XG.length ≤ (U.map (tablePerm n)).length := by
    rw [List.length_map, List.length_flatMap, ← List.length_reverse, ← hX.length_eq, ← hsum]
    simp
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  refine ⟨fun u hu ho => ?_, fun r hr => ?_⟩
  · have huU : u ∈ U.map (tablePerm n) := hperm.symm.subset ((hXG u).2 ⟨hu, ho⟩)
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 huU
    obtain ⟨r, hr, d, hd, heq⟩ := hUmem T hT
    exact ⟨r, hr, d, hd, heq⟩
  · set c : Table × Array Table × Array ℕ × Array ℕ :=
      (toTable r, conjClosure n gens gensInv (toTable r) cap)
    have hc : c ∈ cl := by
      simp only [cl, List.map_map, List.mem_map, Function.comp]
      exact ⟨r, hr, rfl⟩
    set E := c.2.1.toList.map (tablePerm n)
    have hEsub : E ⊆ U.map (tablePerm n) := by
      intro y hy
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
      exact List.mem_map.2 ⟨T, List.mem_flatMap.2 ⟨c, hc, hT⟩, rfl⟩
    have hEnodup : E.Nodup := by
      have := (List.nodup_flatMap.1 (by
        have h' : (U.map (tablePerm n)).Nodup := hnodup
        rwa [List.map_flatMap] at h')).1
      exact this c hc
    have hEcls : ∀ y ∈ E, y ∈ conjClass H r := by
      intro y hy
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
      obtain ⟨r', hr', hrep', d, hd, hrep⟩ := hentries c hc T hT
      have hrr : r' = r := (tablePerm_eq hrep').symm.trans (tablePerm_eq (rep_toTable hn r))
      subst hrr
      exact ⟨d, hd, tablePerm_eq hrep⟩
    have hlenE : E.length = (conjClosure n gens gensInv (toTable r) cap).1.size := by
      simp [E, c]
    rw [← hlenE, ← List.toFinset_card_of_nodup hEnodup, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun y hy => hEcls y (List.mem_toFinset.1 hy))
      (conjClass_finite H r)

end CFSG.Sporadic.Schreier
