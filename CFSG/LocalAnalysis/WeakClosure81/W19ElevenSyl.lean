module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_isCyclic_sup_of_ne {P₁ P₂ : Subgroup G} {p : ℕ}
    (h₁ : Nat.card P₁ = p) (h₂ : Nat.card P₂ = p) (hne : P₁ ≠ P₂) :
    ¬ IsCyclic ↥(P₁ ⊔ P₂) := by
  intro hcyc
  apply hne
  have e1 : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have e2 : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  have hc1 : Nat.card (P₁.subgroupOf (P₁ ⊔ P₂)) = p := by
    rw [← h₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe e1).toEquiv
  have hc2 : Nat.card (P₂.subgroupOf (P₁ ⊔ P₂)) = p := by
    rw [← h₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe e2).toEquiv
  have heq := (IsCyclic.subgroup_eq_iff_card_eq (H := P₁.subgroupOf (P₁ ⊔ P₂))
    (K := P₂.subgroupOf (P₁ ⊔ P₂))).2 (hc1.trans hc2.symm)
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 e1, inf_eq_left.2 e2] at heq
  exact heq

private theorem card_conjSubgroup_aux (R : Subgroup G) (g : G) :
    Nat.card (conjSubgroup R g) = Nat.card R :=
  (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem disjoint_of_card_prime_of_isPGroup_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P Q : Subgroup G} (hP : Nat.card P = p) (hQ : IsPGroup 2 Q) : Disjoint Q P := by
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hQ
  rw [Subgroup.disjoint_def]
  intro y hyQ hyP
  have h1 : orderOf y ∣ 2 ^ b := hb ▸ Subgroup.orderOf_dvd_natCard Q hyQ
  have h2 : orderOf y ∣ p := hP ▸ Subgroup.orderOf_dvd_natCard P hyP
  have hcop : Nat.Coprime (2 ^ b) p :=
    Nat.Coprime.pow_left b ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_conj_zpowers_eq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P Q : Subgroup G}
    (hP : Nat.card P = p) (hQ : IsPGroup 2 Q) (hPQ : P ≤ normalizer (Q : Set G)) {x : G}
    (hxo : orderOf x = p) (hx : x ∈ P ⊔ Q) :
    ∃ q ∈ Q, Subgroup.zpowers x = conjSubgroup P q := by
  classical
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hQ
  have hdis : Disjoint Q P := disjoint_of_card_prime_of_isPGroup_two hp2 hP hQ
  set S : Subgroup G := P ⊔ Q with hSdef
  have hS : Nat.card S = 2 ^ b * p := by
    rw [hSdef, sup_comm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q P hPQ hdis, hb, hP]
  have hfac : (Nat.card S).factorization p = 1 := by
    rw [hS, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hp.out.ne_zero]
    have h1 : (2 ^ b).factorization p = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      exact Finsupp.single_eq_of_ne hp2
    rw [Finsupp.add_apply, h1, hp.out.factorization_self, zero_add]
  have hPS : P ≤ S := le_sup_left
  have hZS : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.2 hx
  have hcP : Nat.card (P.subgroupOf S) = p ^ (Nat.card S).factorization p := by
    rw [hfac, pow_one, ← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
  have hcZ : Nat.card ((Subgroup.zpowers x).subgroupOf S) = p ^ (Nat.card S).factorization p := by
    rw [hfac, pow_one, ← hxo, ← Nat.card_zpowers]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv
  haveI : Fact p.Prime := hp
  let SP : Sylow p ↥S := Sylow.ofCard (P.subgroupOf S) hcP
  let SR : Sylow p ↥S := Sylow.ofCard ((Subgroup.zpowers x).subgroupOf S) hcZ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S SP SR
  have hle : Subgroup.zpowers x ≤ conjSubgroup P (g : G)⁻¹ := by
    intro z hz
    rw [mem_conjSubgroup_iff]
    have hzS : z ∈ S := hZS hz
    have hmem : (⟨z, hzS⟩ : ↥S) ∈ (SR : Subgroup ↥S) := by
      change (⟨z, hzS⟩ : ↥S) ∈ (Subgroup.zpowers x).subgroupOf S
      exact hz
    rw [← hg, Sylow.coe_subgroup_smul] at hmem
    obtain ⟨s, hs, hsz⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hmem
    have hsP : (s : G) ∈ P := by
      change s ∈ P.subgroupOf S at hs
      exact hs
    have hz' : z = (g : G) * (s : G) * (g : G)⁻¹ := by
      have := congrArg Subtype.val hsz
      simpa [MulAut.smul_def, MulAut.conj_apply] using this.symm
    have e : (g : G)⁻¹ * z * ((g : G)⁻¹)⁻¹ = (s : G) := by rw [hz']; group
    rw [e]
    exact hsP
  have hcard : Nat.card (conjSubgroup P (g : G)⁻¹) ≤ Nat.card (Subgroup.zpowers x) := by
    rw [card_conjSubgroup_aux, hP, Nat.card_zpowers, hxo]
  have heq : Subgroup.zpowers x = conjSubgroup P (g : G)⁻¹ :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hgS : (g : G)⁻¹ ∈ P ⊔ Q := S.inv_mem g.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ] at hgS
  obtain ⟨y, hy, q, hq, hyq⟩ := hgS
  refine ⟨q, hq, ?_⟩
  have hyq' : y * q = (g : G)⁻¹ := hyq
  rw [heq, ← hyq', ← conjSubgroup_conjSubgroup,
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hy)]

end CFSG.LocalAnalysis.WeakClosure81

end
