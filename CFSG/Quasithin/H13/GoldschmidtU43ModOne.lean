module

public import CFSG.Quasithin.H13.GoldschmidtU43ModSyl

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.LieType.Multipliers.U43

@[expose] def X0OneClass : Prop :=
  ∀ u v : X₀, orderOf u = 2 → orderOf v = 2 → IsConj u v

theorem x0OneClass_of_checks (ho : orbCheck 820 tabA tabB = true)
    (hs : sylCheck 820 tabA tabB = true) : X0OneClass := by
  obtain ⟨hcard, hinv⟩ := syl_sound ho hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card X₀).factorization 2 = 7 := by
    rw [card_X₀, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  let P : Sylow 2 X₀ := Sylow.ofCard Ssub (by rw [hcard, hfac]; norm_num)
  have key : ∀ u : X₀, orderOf u = 2 → IsConj u xElt := by
    intro u hu
    have hp : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X₀ P Q
    have huQ : u ∈ (Q : Subgroup X₀) := hQ (Subgroup.mem_zpowers u)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at huQ
    obtain ⟨s, hsP, hsu⟩ := huQ
    have hsu' : g * s * g⁻¹ = u := by simpa using hsu
    have hso : orderOf s = 2 := by
      rw [← hu, ← hsu']
      exact ((MulAut.conj g).orderOf_eq s).symm
    obtain ⟨c, hc⟩ := hinv s hsP hso
    exact isConj_iff.2 ⟨(g * c)⁻¹, by rw [← hsu', ← hc]; group⟩
  intro u v hu hv
  exact (key u hu).trans (key v hv).symm

end CFSG.Quasithin.H13.U43
