module

public import CFSG.Quasithin.Vol2.Ch10SecV1SF
public import CFSG.Quasithin.Background.A3Structure319Defs

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} {K : Type} [Field K] [Finite K]
  {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {V : Subgroup H}

omit [Finite H] [Finite K] in
theorem mem_normalizer_of_normal (hVn : V.Normal) (h : H) :
    h ∈ Subgroup.normalizer (V : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hVn.conj_mem v hv h, fun hv => ?_⟩
  have := hVn.conj_mem _ hv h⁻¹
  rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at this

namespace SumTwo

variable {W₀ W₁ : Subgroup H}

theorem exists_inv (S : SumTwo φ V W₀ W₁) (hVn : V.Normal) (hq : ¬ 3 ∣ Nat.card K + 1)
    {h : H} {k : ℕ} (hk : orderOf h = 3 ^ k) (hhL : h ∈ Subgroup.normalizer (L : Set H)) :
    ∃ J : Subgroup H, Nonempty (NatCoord φ J) ∧ h ∈ Subgroup.normalizer (J : Set H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := conjPerm (Nat.card W₀) (mem_normalizer_of_normal hVn h) hhL with hσdef
  have hσ : σ ^ (3 ^ k) = 1 := by
    refine Equiv.ext fun J => Subtype.ext ?_
    rw [hσdef, conjPerm_pow, ← hk, pow_orderOf_eq_one, map_conj_one]
    rfl
  have hP : IsPGroup 3 (Subgroup.zpowers σ) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hσ)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨J, hJ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card
    ↥(invSubs L V (Nat.card W₀)) (by rwa [S.card_invSubs])
  have hJσ : σ J = J := hJ ⟨σ, Subgroup.mem_zpowers σ⟩
  refine ⟨J.1, ?_, ?_⟩
  · rcases S.eq_or_eq_graph J.2.1 J.2.2.1 J.2.2.2 with h1 | ⟨a, ha⟩
    · rw [h1]
      exact ⟨S.c₁⟩
    · rw [ha]
      exact ⟨S.graphCoord a⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact congrArg Subtype.val hJσ

end SumTwo

theorem exists_natCoord_inv (hV : IsElemAbelian 2 V) (hVn : V.Normal) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s ≤ 2) (hnat : IsNaturalSum s K L V φ) (hq : ¬ 3 ∣ Nat.card K + 1) {h : H} {k : ℕ}
    (hk : orderOf h = 3 ^ k) (hhL : h ∈ Subgroup.normalizer (L : Set H)) :
    ∃ I : Subgroup H, Nonempty (NatCoord φ I) ∧ h ∈ Subgroup.normalizer (I : Set H) := by
  obtain ⟨W, hWV, hVW, hind, hθ⟩ := hnat
  have hc : ∀ i, Nonempty (NatCoord φ (W i)) := fun i => by
    obtain ⟨θ, hθi⟩ := hθ i
    exact ⟨⟨θ, hθi⟩⟩
  interval_cases s
  ·
    have hV0 : V = W 0 := hVW.trans (iSup_unique W)
    exact ⟨W 0, hc 0, hV0 ▸ mem_normalizer_of_normal hVn h⟩
  ·
    obtain ⟨c₀⟩ := hc 0
    obtain ⟨c₁⟩ := hc 1
    have hsup : W 0 ⊔ W 1 = V := by
      rw [hVW]
      refine le_antisymm (sup_le (le_iSup W 0) (le_iSup W 1)) (iSup_le fun i => ?_)
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    exact SumTwo.exists_inv
      { c₀ := c₀
        c₁ := c₁
        le₀ := hWV 0
        le₁ := hWV 1
        sup := hsup
        inf := (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)).eq_bot
        comm := fun x hx y hy => congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩) }
      hVn hq hk hhL

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
