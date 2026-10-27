module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBInv
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBWeak

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem false_of_index_two (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S T₀ : Subgroup G} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hQS : T₀ ≤ S)
    (hQidx : T₀.relIndex S = 2) {u : G} (hu : orderOf u = 2)
    (hQu : ∀ g : G, g⁻¹ * u * g ∉ T₀) : False := by
  obtain ⟨N, -, hNn, hsq, huN⟩ := thompson_transfer_exists_normal_subgroup (X := ⊤) le_top hS2
    (by rw [Subgroup.relIndex_top_right]; exact hSi) hQS hQidx (Subgroup.mem_top u) hu
    (fun x _ => hQu x)
  have hN : N.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hNn))
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · obtain ⟨g, h, hgh⟩ := hnab
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by
      have := hsq x (Subgroup.mem_top x)
      rwa [hbot, Subgroup.mem_bot, pow_two] at this)
    apply hgh
    calc g * h = (g * h)⁻¹ := (hinv _).symm
      _ = h * g := by rw [mul_inv_rev, hinv, hinv]
  · exact huN (htop ▸ Subgroup.mem_top u)

namespace BCtx

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx T M L V g D)

include c in
theorem caseB_two (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrQ, hrV, hr2, hQ⟩ := c.exists_r h2
  obtain ⟨a, haV1, haN, has, ha2⟩ := c.exists_a₁
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hr1 : r ≠ 1 := fun h => hrV (h ▸ V.one_mem)
  refine false_of_index_two c.h.simple c.h.nonabelian c.h.sylow.1 c.h.sylow.2
    (inf_le_left : T ⊓ (L ⊔ Subgroup.zpowers a) ≤ T)
    (c.relIndex_T0 haN has haa hrQ hr2 hQ hrV)
    (orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1) ?_
  intro g' hconj
  obtain ⟨-, hNB⟩ := Subgroup.mem_inf.mp hconj
  have hx2 : (g'⁻¹ * r * g') * (g'⁻¹ * r * g') = 1 := by
    calc g'⁻¹ * r * g' * (g'⁻¹ * r * g') = g'⁻¹ * (r * r) * g' := by group
      _ = 1 := by rw [hr2]; group
  have hx1 : g'⁻¹ * r * g' ≠ 1 := fun h => hr1 (by
    calc r = g' * (g'⁻¹ * r * g') * g'⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h, v, hv, -, hhx⟩ := c.conj_into_V haV1 haN has haa hNB hx2 hx1
  refine c.not_conj_V h2 hrQ hrV (g' * h⁻¹) v hv ?_
  rw [← hhx]
  group

end BCtx

theorem m22CaseBTwo_holds : M22CaseBTwo := by
  intro G _ _ T M L V g D hl h hk _ h2
  obtain ⟨c⟩ := nonempty_bCtx hl h hk
  exact c.caseB_two h2

end CFSG.Quasithin.H13.GM22
