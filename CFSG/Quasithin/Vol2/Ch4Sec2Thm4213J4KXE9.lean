module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsKS
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open

theorem exists_e9_of_isSporadic_M22 {X : Type} [Group X] (h : CFSG.Quasithin.IsSporadic .M22 X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨e⟩ := h
  exact CFSG.RankThree.PartTwo.Sec15.exists_e9_of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec15.exists_e9_of_e9Basis CFSG.RankThree.Asc83Table.M22.E)

theorem exists_e9_of_quotient {Q : Type} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (E0 : Subgroup (Q ⧸ N)) (hE0 : IsElemAbelian 3 E0) (hE0c : Nat.card E0 = 9) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : Q →* Q ⧸ N := QuotientGroup.mk' N with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set P : Subgroup Q := E0.comap π with hPdef
  have hPcard : Nat.card P = Nat.card E0 * Nat.card N := by
    have h1 : Nat.card P * P.index = Nat.card Q := Subgroup.card_mul_index P
    have h2 : Nat.card E0 * E0.index = Nat.card (Q ⧸ N) := Subgroup.card_mul_index E0
    have h3 : Nat.card Q = Nat.card (Q ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h4 : P.index = E0.index := Subgroup.index_comap_of_surjective E0 hπs
    have hidx : E0.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx)
    rw [h4] at h1
    calc Nat.card P * E0.index = Nat.card Q := h1
      _ = Nat.card (Q ⧸ N) * Nat.card N := h3
      _ = Nat.card E0 * E0.index * Nat.card N := by rw [h2]
      _ = Nat.card E0 * Nat.card N * E0.index := by ring
  obtain ⟨v, m, hm, hNv⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := N)).ne' 3 (by norm_num)
  have hPdvd : 3 ^ (v + 2) ∣ Nat.card P := by
    rw [hPcard, hE0c, hNv]
    exact ⟨m, by ring⟩
  obtain ⟨T', hT'⟩ := Sylow.exists_subgroup_card_pow_prime 3 hPdvd
  set T : Subgroup Q := T'.map P.subtype with hTdef
  have hTcard : Nat.card T = 3 ^ (v + 2) := by
    rw [hTdef, Subgroup.card_map_of_injective P.subtype_injective, hT']
  have hTP : T ≤ P := Subgroup.map_subtype_le T'
  set ψ : T →* Q ⧸ N := π.comp T.subtype with hψdef
  have hψE : ∀ t : T, ψ t ∈ E0 := fun t => hTP t.2
  have hrange : ψ.range ≤ E0 := by
    rintro _ ⟨t, rfl⟩
    exact hψE t
  have hcount : Nat.card T = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hker_dvd : Nat.card ψ.ker ∣ Nat.card N := by
    have hK' : ψ.ker.map T.subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
      exact QuotientGroup.eq_one_iff _ |>.mp hx1
    have hc : Nat.card (ψ.ker.map T.subtype) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective T.subtype_injective
    rw [← hc]
    exact Subgroup.card_dvd_of_le hK'
  obtain ⟨a, ha, hka⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hTcard ▸ Subgroup.card_subgroup_dvd_card ψ.ker)
  have hav : a ≤ v := by
    have hcop : Nat.Coprime (3 ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
    have h1 : 3 ^ a ∣ 3 ^ v * m := hNv ▸ (hka ▸ hker_dvd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h1)
  have hkerle : Nat.card ψ.ker ≤ 3 ^ v := by
    rw [hka]
    exact Nat.pow_le_pow_right (by norm_num) hav
  have hrange_card : 9 ≤ Nat.card ψ.range := by
    have h1 : 3 ^ (v + 2) = 9 * 3 ^ v := by ring
    have h2 : Nat.card ψ.range * Nat.card ψ.ker ≤ Nat.card ψ.range * 3 ^ v :=
      Nat.mul_le_mul_left _ hkerle
    have h3 : 9 * 3 ^ v ≤ Nat.card ψ.range * 3 ^ v := by
      rw [← hcount, hTcard] at h2
      omega
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hreq : ψ.range = E0 :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hE0c]; exact hrange_card)
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := v + 2) hTcard
  have hnc : ¬ IsCyclic T := by
    intro hcyc
    have hψE' : ∀ t : T, ψ t ∈ E0 := hψE
    let φ : T →* E0 := ψ.codRestrict E0 hψE'
    have hφs : Function.Surjective φ := by
      intro e
      have hmem : (e : Q ⧸ N) ∈ ψ.range := by
        rw [hreq]
        exact e.2
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, Subtype.ext ht⟩
    have hcycE : IsCyclic E0 := isCyclic_of_surjective φ hφs
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E0)
    have hg3 : g ^ 3 = 1 := Subtype.ext (by
      have := hE0.2 (g : Q ⧸ N) g.2
      simpa using this)
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rw [hg, hE0c] at hdvd
    norm_num at hdvd
  obtain ⟨E, hE, hEc⟩ := CFSG.AGLEmbedding.BlockCyc.hasE9_of_not_isCyclic hTp hnc
  exact ⟨E, hE, by rw [hEc]; norm_num⟩

end CFSG.Quasithin.H13.Ch4.J4KX

end
