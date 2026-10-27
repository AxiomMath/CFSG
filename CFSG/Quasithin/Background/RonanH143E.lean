module

public import CFSG.Quasithin.Background.RonanH143PG
public import CFSG.Quasithin.Background.RonanH143Data2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.QuasithinUnique.Setup.X1

@[expose] def PG.all : List PG :=
  (List.finRange 16).flatMap fun t => (List.finRange 8).map fun j => ⟨t, j⟩

theorem PG.mem_all (x : PG) : x ∈ PG.all := by
  simp only [PG.all, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨x.t, x.j, by cases x; rfl⟩

@[expose] def PG.invs : List PG := PG.all.filter fun x => decide (x ≠ 1) && decide (x * x = 1)

theorem PG.mem_invs {x : PG} (h1 : x ≠ 1) (h2 : x * x = 1) : x ∈ PG.invs := by
  simp only [PG.invs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨PG.mem_all x, h1, h2⟩

@[expose] def koL : List PG := (List.finRange 16).map fun t => ⟨t, 0⟩

@[expose] def nqL : List PG := (List.finRange 16).map fun u => ⟨nqKF u, nqJF u⟩

@[expose] def pred4 (l : List PG) : Bool :=
  (subprods l).all (fun x => koL.contains x) || (subprods l).all (fun x => nqL.contains x)

@[expose] def pred5 (_ : List PG) : Bool := false

theorem greedy4 : forallGreedy PG.invs pred4 4 [] = true := by decide +kernel

theorem greedy5 : forallGreedy PG.invs pred5 5 [] = true := by decide +kernel

theorem koPerm_comm (s t : Fin 16) : koPerm s * koPerm t = koPerm t * koPerm s := by
  rw [koPerm_mul, koPerm_mul]
  congr 1
  simp only [xorF, Nat.xor_comm]

theorem isElemAbelian_fixO : IsElemAbelian 2 fixO := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := (mem_fixO_iff _).1 a.2
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 b.2
    apply Subtype.ext
    show (a : P24) * b = b * a
    rw [hs, ht, koPerm_comm]
  · obtain ⟨t, rfl⟩ := (mem_fixO_iff _).1 hx
    rw [pow_two, koPerm_mul_self]

theorem isE2k_fixO : IsE2k 4 fixO := ⟨isElemAbelian_fixO, by rw [card_fixO']; norm_num⟩

theorem isElemAbelian_NQ : IsElemAbelian 2 NQ := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    exact NQ_comm _ _ a.2 b.2
  · obtain ⟨t, rfl⟩ := hx
    rw [pow_two, nqPerm_sq]

theorem isE2k_NQ : IsE2k 4 NQ := ⟨isElemAbelian_NQ, by rw [card_NQ]; norm_num⟩

theorem fixO_normal_PO : ∀ y ∈ PO, ∀ k ∈ fixO, y * k * y⁻¹ ∈ fixO := by
  rintro _ ⟨t, j, rfl⟩ k hk
  obtain ⟨s, rfl⟩ := (mem_fixO_iff _).1 hk
  have h : koPerm t * dPerm j * koPerm s * (koPerm t * dPerm j)⁻¹ =
      koPerm t * (dPerm j * koPerm s * (dPerm j)⁻¹) * (koPerm t)⁻¹ := by group
  rw [h]
  have hd : dPerm j * koPerm s * (dPerm j)⁻¹ = koPerm (ctF j s) := by
    have := dPerm_mul_koPerm j s
    rw [this]
    group
  rw [hd]
  have hc := koPerm_comm t (ctF j s)
  have : koPerm t * koPerm (ctF j s) * (koPerm t)⁻¹ = koPerm (ctF j s) := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact (mem_fixO_iff _).2 ⟨_, rfl⟩

theorem NQ_conj_gens :
    (∀ (t u : Fin 16), ∃ u' : Fin 16, koPerm t * nqPerm u * (koPerm t)⁻¹ = nqPerm u') ∧
      (∀ (j : Fin 8) (u : Fin 16), ∃ u' : Fin 16, dPerm j * nqPerm u * (dPerm j)⁻¹ = nqPerm u') := by
  decide +kernel

theorem NQ_normal_PO : ∀ y ∈ PO, ∀ k ∈ NQ, y * k * y⁻¹ ∈ NQ := by
  rintro _ ⟨t, j, rfl⟩ k hk
  obtain ⟨u, rfl⟩ := hk
  obtain ⟨u1, h1⟩ := NQ_conj_gens.2 j u
  obtain ⟨u2, h2⟩ := NQ_conj_gens.1 t u1
  have h : koPerm t * dPerm j * nqPerm u * (koPerm t * dPerm j)⁻¹ =
      koPerm t * (dPerm j * nqPerm u * (dPerm j)⁻¹) * (koPerm t)⁻¹ := by group
  rw [h, h1, h2]
  exact ⟨u2, rfl⟩

theorem card_PG_sylow : Nat.card PG = 2 ^ (Nat.card PG).factorization 2 := by
  rw [PG.card_PG]
  have h : (128 : ℕ) = 2 ^ 7 := by norm_num
  rw [h, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem chain_of_E {k : ℕ} {pred : List PG → Bool} (hg : forallGreedy PG.invs pred k [] = true)
    (A : Subgroup P24) (hA : A ≤ PO) (hE : IsElemAbelian 2 A) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : PG, ∃ l : List PG, IndepList l ∧ pred l = true ∧
      ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, PG.toPerm g * x * (PG.toPerm g)⁻¹ = PG.toPerm s := by
  obtain ⟨hc, hsq⟩ := hE
  have hEc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := hc.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hE2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact hsq a ha
  have := exists_conj_chain (P := PG) (K := PG) (X := P24) (MonoidHom.id PG) Function.injective_id
    PG.toPermHom PG.toPerm_injective card_PG_sylow (Rinv := PG.invs)
    (fun x h1 h2 => PG.mem_invs h1 h2) hg A (by rw [PG.range_toPermHom]; exact hA) hEc hE2 hcard
  obtain ⟨g, l, hl, hp, hx⟩ := this
  exact ⟨g, l, hl, hp, hx⟩

theorem koL_mem {s : PG} (hs : s ∈ koL) : PG.toPerm s ∈ fixO := by
  simp only [koL, List.mem_map, List.mem_finRange, true_and] at hs
  obtain ⟨t, rfl⟩ := hs
  refine (mem_fixO_iff _).2 ⟨t, ?_⟩
  show koPerm t * dPerm 0 = koPerm t
  rw [dPerm_zero, mul_one]

theorem nqL_mem {s : PG} (hs : s ∈ nqL) : PG.toPerm s ∈ NQ := by
  simp only [nqL, List.mem_map, List.mem_finRange, true_and] at hs
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, rfl⟩

theorem not_isE2k_five_PO (A : Subgroup P24) (hA : A ≤ PO) : ¬ IsE2k 5 A := by
  rintro ⟨hE, hc⟩
  obtain ⟨g, l, -, hp, -⟩ := chain_of_E greedy5 A hA hE hc
  exact absurd hp (by simp [pred5])

theorem eq_NQ_or_fixO_of_isE2k_four (A : Subgroup P24) (hA : A ≤ PO) (hE : IsE2k 4 A) :
    A = NQ ∨ A = fixO := by
  obtain ⟨g, l, -, hp, hx⟩ := chain_of_E greedy4 A hA hE.1 hE.2
  have hgPO : PG.toPerm g ∈ PO := PG.toPerm_mem_PO g
  have hginv : (PG.toPerm g)⁻¹ ∈ PO := PO.inv_mem hgPO
  simp only [pred4, Bool.or_eq_true, List.all_eq_true] at hp
  rcases hp with hp | hp
  · right
    have hle : A ≤ fixO := by
      intro x hxA
      obtain ⟨s, hs, hsx⟩ := (hx x).1 hxA
      have hxeq : x = (PG.toPerm g)⁻¹ * PG.toPerm s * ((PG.toPerm g)⁻¹)⁻¹ := by
        rw [← hsx]
        group
      rw [hxeq]
      exact fixO_normal_PO _ hginv _ (koL_mem (by simpa using hp s hs))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hE.2, card_fixO']; norm_num)
  · left
    have hle : A ≤ NQ := by
      intro x hxA
      obtain ⟨s, hs, hsx⟩ := (hx x).1 hxA
      have hxeq : x = (PG.toPerm g)⁻¹ * PG.toPerm s * ((PG.toPerm g)⁻¹)⁻¹ := by
        rw [← hsx]
        group
      rw [hxeq]
      exact NQ_normal_PO _ hginv _ (nqL_mem (by simpa using hp s hs))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hE.2, card_NQ]; norm_num)

theorem isE2k_four_PO_iff (A : Subgroup P24) :
    (A ≤ PO ∧ IsE2k 4 A) ↔ (A = NQ ∨ A = fixO) := by
  constructor
  · rintro ⟨hA, hE⟩
    exact eq_NQ_or_fixO_of_isE2k_four A hA hE
  · rintro (rfl | rfl)
    · exact ⟨NQ_le_PO, isE2k_NQ⟩
    · exact ⟨fun g hg => by
        obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
        exact koPerm_mem_PO t, isE2k_fixO⟩

end CFSG.Quasithin.RonanH143
