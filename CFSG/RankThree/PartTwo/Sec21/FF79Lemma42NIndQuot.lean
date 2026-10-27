module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NIndAux
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem nhyp_quotient {Q L : Subgroup G} {b : G} (h : NHyp Q L b) (R : Subgroup G) [R.Normal]
    (hRQ : R ≤ Q) :
    NHyp (Q.map (QuotientGroup.mk' R)) (L.map (QuotientGroup.mk' R)) (QuotientGroup.mk' R b) := by
  have hRL : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R := fun l _ r hr =>
    Subgroup.Normal.conj_mem inferInstance r hr l
  have hbR := not_mem_of_hyp h hRQ
  have hRcard : Nat.Coprime 3 (Nat.card R) :=
    h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRQ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact KCore.KGroupNonab.of_surjective CFSG.Assembly.inCatalog_isoInvariant h.kgroup _
      ((QuotientGroup.mk' R).subgroupMap_surjective Q)
  · obtain ⟨e⟩ := h.iso
    have hinj : Function.Injective ((QuotientGroup.mk' R).subgroupMap L) := by
      rw [injective_iff_map_eq_one]
      intro l hl
      have hl' : (l : G) ∈ R := by
        have := congrArg Subtype.val hl
        simpa [QuotientGroup.eq_one_iff] using this
      exact Subtype.ext (eq_one_of_mem_inf h hRQ hRL l.2 hl')
    exact ⟨(MulEquiv.ofBijective _
      ⟨hinj, (QuotientGroup.mk' R).subgroupMap_surjective L⟩).symm.trans e⟩
  · exact (Subgroup.map_mono h.normalizes).trans (Subgroup.le_normalizer_map _)
  · exact h.coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
  · exact Subgroup.mem_map_of_mem _ h.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← h.order, pow_orderOf_eq_one, map_one]
    · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hbR
  · rintro z ⟨⟨x, hxQ, rfl⟩, hz⟩
    have hb3 : IsPGroup 3 (Subgroup.zpowers b) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order]; rfl)
    have hx : x ∈ (Subgroup.centralizer (((Subgroup.zpowers b).map (QuotientGroup.mk' R) :
        Subgroup (G ⧸ R)) : Set (G ⧸ R))).comap (QuotientGroup.mk' R) := by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [MonoidHom.map_zpowers] at hy
      obtain ⟨k, rfl⟩ := hy
      have hc : Commute (QuotientGroup.mk' R b) (QuotientGroup.mk' R x) := by
        have := Subgroup.mem_centralizer_iff.mp hz (QuotientGroup.mk' R b) (by simp)
        exact this
      exact ((hc.zpow_left k).eq)
    obtain ⟨u, hu, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_left.mp
      (CFSG.AGLEmbedding.comap_centralizer_map_le_sup Nat.prime_three R
        hRcard hb3 hx)
    have hyQ : y ∈ Q := by
      have : y = u⁻¹ * x := by rw [← hxy, inv_mul_cancel_left]
      rw [this]
      exact Q.mul_mem (Q.inv_mem (hRQ hu)) hxQ
    have hyb : y ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (Subgroup.mem_centralizer_iff.mp hy) g (Subgroup.mem_zpowers g)
    have hyL := h.cent ⟨hyQ, hyb⟩
    have hu1 : QuotientGroup.mk' R u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    have hπ : QuotientGroup.mk' R x = QuotientGroup.mk' R y := by
      rw [← hxy, map_mul, hu1, one_mul]
    rw [hπ, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hyL l hl]

theorem card_map_lt {Q : Subgroup G} (R : Subgroup G) [R.Normal] (hRQ : R ≤ Q) (hR : R ≠ ⊥) :
    Nat.card (Q.map (QuotientGroup.mk' R)) < Nat.card Q := by
  have hdvd := Subgroup.card_map_dvd Q (QuotientGroup.mk' R)
  have hpos : 0 < Nat.card Q := Nat.card_pos
  refine lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) fun heq => ?_
  set ψ := (QuotientGroup.mk' R).subgroupMap Q with hψ
  have hsurj : Function.Surjective ψ := (QuotientGroup.mk' R).subgroupMap_surjective Q
  have h1 := Subgroup.card_mul_index ψ.ker
  have h2 := Subgroup.index_ker ψ
  rw [MonoidHom.range_eq_top_of_surjective ψ hsurj, Subgroup.card_top] at h2
  rw [h2, heq] at h1
  have hker : Nat.card ψ.ker = 1 := by
    have : Nat.card ψ.ker * Nat.card Q = 1 * Nat.card Q := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [Subgroup.card_eq_one] at hker
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
  have hmem : (⟨r, hRQ hr⟩ : Q) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simpa [hψ, QuotientGroup.eq_one_iff] using hr
  rw [hker, Subgroup.mem_bot] at hmem
  exact hr1 (Subtype.ext (congrArg Subtype.val hmem : r = 1))

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
