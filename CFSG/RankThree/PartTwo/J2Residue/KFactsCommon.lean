module

public import CFSG.GroupTheory.PCentralElement
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.J2Residue.KG1Holds
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic

theorem card_sylow_inf_centralizer_J2
    (S : Sylow 3 J2) :
    Nat.card ↥((S : Subgroup J2) ⊓ Subgroup.centralizer (S : Set J2)) = 3 := by
  have h := Sec4.Sporadic.J2.forall_sylow_of_P3 (fun _ _ P => Sec4.Sporadic.J2.Pt123 P)
    (fun _ _ _ _ φ _ hP => hP.map φ) Sec4.Sporadic.J2.pt123_P3 J2 ⟨MulEquiv.refl _⟩ S
  exact card_inf_centralizer_eq_three h.1.1

theorem orderOf_eq_three_J2
    {a : J2} (ha : a ≠ 1)
    (haS : ∃ S : Sylow 3 J2, a ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {a}) :
    orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, haS', hSa⟩ := haS
  rw [← Nat.card_zpowers,
    zpowers_eq_inf_centralizer_of_card (card_sylow_inf_centralizer_J2 S) ha haS' hSa]
  exact card_sylow_inf_centralizer_J2 S

theorem exists_map_conj_zpowers_eq_J2
    {a b : J2} (ha : a ≠ 1)
    (haS : ∃ S : Sylow 3 J2, a ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {a})
    (hb : b ≠ 1)
    (hbS : ∃ S : Sylow 3 J2, b ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {b}) :
    ∃ g : J2, (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_map_conj_zpowers_eq card_sylow_inf_centralizer_J2 ha haS hb hbS

theorem exists_conj_eq_or_eq_inv_J2
    {a b : J2} (ha : a ≠ 1)
    (haS : ∃ S : Sylow 3 J2, a ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {a})
    (hb : b ≠ 1)
    (hbS : ∃ S : Sylow 3 J2, b ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {b}) :
    ∃ g : J2, g * a * g⁻¹ = b ∨ g * a * g⁻¹ = b⁻¹ := by
  obtain ⟨g, hg⟩ := exists_map_conj_zpowers_eq_J2 ha haS hb hbS
  refine ⟨g, eq_or_eq_inv_of_mem_zpowers_of_pow_three ?_ ?_ fun h => ha (by simpa using h)⟩
  · rw [← orderOf_eq_three_J2 hb hbS]
    exact pow_orderOf_eq_one b
  · rw [← hg]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers a)

variable {L : Type*} [Group L]

theorem orderOf_mk_eq_three {R : Subgroup L} [R.Normal] (hR : IsPGroup 2 R) (ψ : L ⧸ R ≃* J2)
    {d : L} (hd : orderOf d = 3) : orderOf (ψ (d : L ⧸ R)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_map_eq_of_isPGroup_ker (Q := L ⧸ R) (p := 3) (q := 2) (by norm_num)
    (QuotientGroup.mk' R) (by rw [QuotientGroup.ker_mk']; exact hR) hd
  rw [MulEquiv.orderOf_eq]
  simpa only [QuotientGroup.mk'_apply] using h

theorem exists_sylow_mk [Finite L] {R : Subgroup L} [R.Normal] (ψ : L ⧸ R ≃* J2) {d : L}
    (hdS : ∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) :
    ∃ S : Sylow 3 J2, ψ (d : L ⧸ R) ∈ (S : Subgroup J2) ∧
      (S : Subgroup J2) ≤ Subgroup.centralizer {ψ (d : L ⧸ R)} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_sylow_mem_le_centralizer_map (ψ.toMonoidHom.comp (QuotientGroup.mk' R))
    (ψ.surjective.comp (QuotientGroup.mk'_surjective R)) hdS

theorem exists_conj_mk_eq_or_eq_inv
    [Finite L] {R : Subgroup L}
    [R.Normal] (hR : IsPGroup 2 R) (ψ : L ⧸ R ≃* J2) {d : L} (hd : orderOf d = 3)
    (hdS : ∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d})
    {x₀ : J2} (hx₀ : x₀ ≠ 1)
    (hx₀S : ∃ S : Sylow 3 J2, x₀ ∈ (S : Subgroup J2) ∧
      (S : Subgroup J2) ≤ Subgroup.centralizer {x₀}) :
    ∃ g : L, ψ ((g * d * g⁻¹ : L) : L ⧸ R) = x₀ ∨ ψ ((g * d * g⁻¹ : L) : L ⧸ R) = x₀⁻¹ := by
  have hd1 : ψ (d : L ⧸ R) ≠ 1 := by
    intro h
    have h3 := orderOf_mk_eq_three hR ψ hd
    rw [h, orderOf_one] at h3
    norm_num at h3
  obtain ⟨h, hh⟩ := exists_conj_eq_or_eq_inv_J2 hd1 (exists_sylow_mk ψ hdS) hx₀ hx₀S
  obtain ⟨g, rfl⟩ : ∃ g : L, ψ (g : L ⧸ R) = h := by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ψ.symm h)
    exact ⟨q, by rw [hq, MulEquiv.apply_symm_apply]⟩
  refine ⟨g, ?_⟩
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv] using hh

end CFSG.RankThree.PartTwo.J2Residue
