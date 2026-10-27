module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin Equiv

@[expose] def cyc7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 0 1 * swap 0 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def inv7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 0 1 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem cyc7_facts : cyc7 ^ 3 = 1 ∧ cyc7 ≠ 1 ∧ inv7 * cyc7 * inv7⁻¹ = cyc7⁻¹ := by
  refine ⟨Subtype.ext ?_, fun h => ?_, Subtype.ext ?_⟩
  · show (swap (0 : Fin 7) 1 * swap 0 2) ^ 3 = 1
    decide
  · have := congrArg (fun σ : ↥(alternatingGroup (Fin 7)) => (σ : Perm (Fin 7)) 0) h
    revert this
    decide
  · show swap (0 : Fin 7) 1 * swap 3 4 * (swap 0 1 * swap 0 2) * (swap 0 1 * swap 3 4)⁻¹ =
      (swap 0 1 * swap 0 2)⁻¹
    decide

theorem center_alt7' : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ := by
  have := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(alternatingGroup (Fin 7))) with h | h
  · exact h
  · exfalso
    have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top inv7 :
      inv7 ∈ Subgroup.center ↥(alternatingGroup (Fin 7))) cyc7
    have := congrArg (fun σ : ↥(alternatingGroup (Fin 7)) => (σ : Perm (Fin 7)) 0) hc
    revert this
    decide

theorem two_le_pRank_hat7 {Y : Type} [Group Y] [Finite Y]
    (h : IsHat Y ↥(alternatingGroup (Fin 7))) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hc3, ⟨e⟩⟩ := h
  obtain ⟨hσ3, hσ1, hτσ⟩ := cyc7_facts
  set π : Y →* ↥(alternatingGroup (Fin 7)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hπ
  have hπk : ∀ y : Y, π y = 1 ↔ y ∈ Subgroup.center Y := fun y => by
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨x, hx⟩ := hπs cyc7
  obtain ⟨g, hg⟩ := hπs inv7
  have hcub : ∀ c ∈ Subgroup.center Y, c ^ 3 = 1 := fun c hc => by
    have := pow_card_eq_one' (G := ↥(Subgroup.center Y)) (x := ⟨c, hc⟩)
    rw [hc3] at this
    simpa using congrArg Subtype.val this
  have hx3c : x ^ 3 ∈ Subgroup.center Y := (hπk _).mp (by rw [map_pow, hx, hσ3])
  set c := x * (g * x * g⁻¹) with hcdef
  have hcc : c ∈ Subgroup.center Y := (hπk _).mp (by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, hx, hg, hτσ, mul_inv_cancel])
  have hgx : g * x * g⁻¹ = x⁻¹ * c := by rw [hcdef]; group
  have h1 : (g * x * g⁻¹) ^ 3 = x ^ 3 := by
    rw [conj_pow, Subgroup.mem_center_iff.mp hx3c g, mul_inv_cancel_right]
  have hcx : Commute x⁻¹ c := Subgroup.mem_center_iff.mp hcc x⁻¹
  rw [hgx, hcx.mul_pow, hcub c hcc, mul_one, inv_pow] at h1
  have hx6 : (x ^ 3) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel _
  have hx3 : x ^ 3 = 1 := by
    have h3' := hcub _ hx3c
    calc x ^ 3 = (x ^ 3) ^ 3 * ((x ^ 3) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', hx6, inv_one, mul_one]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Y)) 3
    (by rw [hc3])
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := (z : Y)) (y := x)
    (hcub _ z.2) hx3 (Subgroup.mem_center_iff.mp z.2 x).symm ?_ ?_
  · intro h1'
    have : z = 1 := Subtype.ext h1'
    rw [this, orderOf_one] at hz
    omega
  · intro n hn
    have hxc : x ∈ Subgroup.center Y := hn ▸ Subgroup.pow_mem _ z.2 n
    have := (hπk x).mpr hxc
    rw [hx] at this
    exact hσ1 this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
