module

public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.Quasithin.S152W

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native

theorem hs_class_card :
    ∀ t ∈ hsP, orderOf t = 2 →
    Nat.card ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) = 7680 ∨
      Nat.card ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) = 2880 := by
  intro t ht ho
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := hs_involution_centralizers
  have htR : t ∈ hsR := (le_sup_left : hsP ≤ hsP ⊔ Subgroup.zpowers hsU) ht
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover t htR ho
  obtain ⟨-, -, hout, -, hcard, -⟩ := hrows r hr
  have hnot : r.outer = false := by
    by_contra hne
    have hT : r.outer = true := by simpa using hne
    apply hout.1 hT
    have : tp 3850 r.rep = g⁻¹ * (g * tp 3850 r.rep * g⁻¹) * g := by group
    rw [this]
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) ht) hg
  rw [card_inf_centralizer_conj hg, hcard]
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      hsRows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
  rw [hmap] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
  · exact Or.inl h3
  · exact Or.inr h3
  · rw [hnot] at h1
    exact absurd h1 (by decide)
  · rw [hnot] at h1
    exact absurd h1 (by decide)

theorem atlasClauses_hsP :
    AtlasClauses hsP := by
  have hcard : Nat.card hsP = 44352000 := card_hsP
  have h2part : (Nat.card hsP).factorization 2 = 9 :=
    factorization_two_of_eq (b := 86625) (by rw [hcard]; norm_num) (by norm_num)
  refine atlasClauses_of_data hs_outer_card_le [7680, 2880] ?_ ?_
  · intro t ht
    rw [card_centralizer_subtype]
    have := hs_class_card (t : Equiv.Perm (Fin 3850)) t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact this
  · intro c hc h9
    rw [h2part]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> revert h9 <;> decide

theorem atlasClauses_HS :
    AtlasClauses NativeSporadic.HS :=
  AtlasClauses.of_equiv hsPermEquiv atlasClauses_hsP

end CFSG.Quasithin.S152W
