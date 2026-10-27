module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem same_action (F : FanTree Γ G) {v b c : V} (hvb : Γ.Adj v b) {g h : G} (hg2 : g * g = 1)
    (hh2 : h * h = 1) (hgv : g • v = v) (hgb : g • b = b) (hhv : h • v = v) (hhb : h • b = b)
    (hvc : Γ.Adj v c) (hgc : g • c ≠ c) (hhc : h • c ≠ c) :
    ∀ w, Γ.Adj v w → g • w = h • w := by
  have hmem : g * h ∈ nbrStab Γ G v := F.mul_mem_nbrStab_of_sq_eq_one hvb
    ⟨MulAction.mem_stabilizer_iff.2 hgv, MulAction.mem_stabilizer_iff.2 hgb⟩
    ⟨MulAction.mem_stabilizer_iff.2 hhv, MulAction.mem_stabilizer_iff.2 hhb⟩ hg2 hh2
    (fun hn => hgc (mem_nbrStab.1 hn c hvc)) (fun hn => hhc (mem_nbrStab.1 hn c hvc))
  intro w hw
  have h1 : (g * h) • w = w := mem_nbrStab.1 hmem w hw
  rw [mul_smul] at h1
  have h2 : g • h • w = g • g • w := by
    rw [h1, ← mul_smul, hg2, one_smul]
  exact (MulAction.injective g h2).symm

theorem exists_third (F : FanTree Γ G) {ξ p q : V} (hξ : valence Γ ξ = 3) (hp : Γ.Adj ξ p)
    (hq : Γ.Adj ξ q) (hpq : p ≠ q) :
    ∃ r, Γ.neighborSet ξ = {p, q, r} ∧ r ≠ p ∧ r ≠ q := by
  have hν : (Γ.neighborSet ξ).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hξ
  have hfin : (Γ.neighborSet ξ).Finite := (F.ncard_neighborSet_le ξ).2
  have hsub : ({p, q} : Set V) ⊆ Γ.neighborSet ξ := by
    rintro x (rfl | rfl)
    · exact hp
    · exact hq
  obtain ⟨r, hr, hn⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({p, q} : Set V)) (t := Γ.neighborSet ξ) (by rw [Set.ncard_pair hpq, hν]; omega)
  have hrp : r ≠ p := fun e => hn (Or.inl e)
  have hrq : r ≠ q := fun e => hn (Or.inr e)
  refine ⟨r, ?_, hrp, hrq⟩
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro x (rfl | rfl | rfl)
    · exact hp
    · exact hq
    · exact hr
  · rw [hν, Set.ncard_insert_of_notMem (by simp [hpq, hrp.symm]), Set.ncard_pair hrq.symm]

theorem lab_pair_of_three (F : FanTree Γ G) {L : ZLab Γ G} (H : LabHyp L) {ξ x p q : V}
    (hξ : valence Γ ξ = 3) (hx : Γ.Adj ξ x) (hp : Γ.Adj ξ p) (hq : Γ.Adj ξ q) (hxp : x ≠ p)
    (hxq : x ≠ q) : L.z p * L.z q = 1 ∨ L.z p * L.z q = L.z x := by
  by_cases hpq : p = q
  · left
    subst hpq
    exact z_sq (F.val5_of_adj_val3 hp hξ)
  · right
    obtain ⟨r, hset, -, -⟩ := exists_third F hξ hx hp hxp
    have hq' : q = r := by
      have hmem : q ∈ Γ.neighborSet ξ := hq
      rw [hset] at hmem
      rcases hmem with e | e | e
      · exact absurd e.symm hxq
      · exact absurd e (Ne.symm hpq)
      · exact e
    subst hq'
    have hprod := H.prod ξ x p q hξ hset hxp hxq hpq
    have h1 : L.z x * (L.z p * L.z q) = 1 := by rw [← mul_assoc]; exact hprod
    rw [eq_inv_of_mul_eq_one_right h1, z_inv (F.val5_of_adj_val3 hx hξ)]

end P518

end CFSG.Quasithin.Fan86
