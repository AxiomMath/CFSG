module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutElemK

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

theorem conj_pow_succ_out {G : Type*} [Group G] (y : G) (n : ℕ) (δ : G) :
    y ^ (n + 1) * δ * (y ^ (n + 1))⁻¹ = y * (y ^ n * δ * (y ^ n)⁻¹) * y⁻¹ := by
  rw [pow_succ']; group

theorem comm_of_conj_eq_out {G : Type*} [Group G] {g δ : G} (h : g * δ * g⁻¹ = δ) :
    δ * g = g * δ := (mul_inv_eq_iff_eq_mul.1 h).symm

section Elem


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217OutElements_of (h45 : Sec4.Item4_5) : Sec217OutElements := by
  intro G _ _ A E U c L a U₀ K hS
  have h : CoverOut A E U c L := hS.base
  have hfr := hS.frame
  have hEA : E ≤ A := h.pair.mem_E.2
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  obtain ⟨u, huL, huA, huD, huC, huord, huc, huI, huAI, hu4⟩ := h.exists_u h45 hfr
  obtain ⟨v, hvK, hvA, hvD, hvC, hvord, hva, hvI, hvAI, hv4⟩ := hS.exists_v h45
  obtain ⟨⟨eI⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  have hu8 : u ^ 8 = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
  have hv8 : v ^ 8 = 1 := by rw [← hvord]; exact pow_orderOf_eq_one v
  obtain ⟨x, hxE, k, hk, hmatch⟩ := exists_match_pgl (G := G) (I := iCore L a)
    (E := A ⊓ iCore L a) inf_le_right hcardAI ⟨eI⟩ huI huAI hvI hvAI hu8 hu4 hv8 hv4
  have hxA : x ∈ A := hxE.1
  have hxI : x ∈ iCore L a := hxE.2
  have hDA : dGroup a c ≤ A :=
    sup_le (Subgroup.zpowers_le.2 (hEA hfr.mem)) (Subgroup.zpowers_le.2 h.c_mem_A)
  have hxD : x ∈ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro δ hδ
    exact hab.1 δ (hDA hδ) x hxA
  have hxcomm : ∀ δ ∈ dGroup a c, x * δ * x⁻¹ = δ := by
    intro δ hδ
    have := Subgroup.mem_centralizer_iff.1 hxD δ hδ
    rw [← this]; group
  have hwN : v ^ k ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ hvD k
  have hv'N : x * v ^ k ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (centralizer_le_normalizer' _ hxD) hwN
  have hconj1 : ∀ δ ∈ dGroup a c, (x * v ^ k) * δ * (x * v ^ k)⁻¹ = v ^ k * δ * (v ^ k)⁻¹ := by
    intro δ hδ
    have hwδ : v ^ k * δ * (v ^ k)⁻¹ ∈ dGroup a c := (Subgroup.mem_normalizer_iff.1 hwN δ).1 hδ
    calc (x * v ^ k) * δ * (x * v ^ k)⁻¹ = x * (v ^ k * δ * (v ^ k)⁻¹) * x⁻¹ := by group
      _ = v ^ k * δ * (v ^ k)⁻¹ := hxcomm _ hwδ
  have hconjn : ∀ n : ℕ, ∀ δ ∈ dGroup a c,
      (x * v ^ k) ^ n * δ * ((x * v ^ k) ^ n)⁻¹ = (v ^ k) ^ n * δ * ((v ^ k) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro δ hδ; simp
    | succ n ih =>
      intro δ hδ
      have hwnδ : (v ^ k) ^ n * δ * ((v ^ k) ^ n)⁻¹ ∈ dGroup a c :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hwN n) δ).1 hδ
      calc (x * v ^ k) ^ (n + 1) * δ * ((x * v ^ k) ^ (n + 1))⁻¹
          = (x * v ^ k) * ((x * v ^ k) ^ n * δ * ((x * v ^ k) ^ n)⁻¹) * (x * v ^ k)⁻¹ :=
            conj_pow_succ_out _ _ _
        _ = (x * v ^ k) * ((v ^ k) ^ n * δ * ((v ^ k) ^ n)⁻¹) * (x * v ^ k)⁻¹ := by rw [ih δ hδ]
        _ = v ^ k * ((v ^ k) ^ n * δ * ((v ^ k) ^ n)⁻¹) * (v ^ k)⁻¹ := hconj1 _ hwnδ
        _ = (v ^ k) ^ (n + 1) * δ * ((v ^ k) ^ (n + 1))⁻¹ := (conj_pow_succ_out _ _ _).symm
  have hv'8 : (x * v ^ k) ^ 8 ∈ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro δ hδ
    have h1 := hconjn 8 δ hδ
    have hw8 : (v ^ k) ^ 8 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hv8, one_pow]
    rw [hw8] at h1
    have h2 : (x * v ^ k) ^ 8 * δ * ((x * v ^ k) ^ 8)⁻¹ = δ := by rw [h1]; group
    exact comm_of_conj_eq_out h2
  have hv'C : x * v ^ k ∉ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
    intro hc'
    apply hvC
    have hwC : v ^ k ∈ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxD) hc'
      simpa using this
    have hk2 : k * k % 8 = 1 := by
      obtain ⟨r, hr⟩ := hk
      subst hr
      have : (2 * r + 1) * (2 * r + 1) = 8 * (r * (r + 1) / 2) + 1 := by
        have h2 : r * (r + 1) % 2 = 0 := by
          rcases Nat.even_or_odd r with ⟨s, hs⟩ | ⟨s, hs⟩ <;> subst hs <;> ring_nf <;> omega
        have h3 : r * (r + 1) = 2 * (r * (r + 1) / 2) := by omega
        nlinarith
      omega
    have hvv : (v ^ k) ^ k = v := by
      rw [← pow_mul]
      have hm : k * k = 8 * (k * k / 8) + 1 := by omega
      rw [hm, pow_add, pow_mul, hv8, one_pow, one_mul, pow_one]
    rw [← hvv]
    exact Subgroup.pow_mem _ hwC k
  refine ⟨u, x * v ^ k, ⟨huL, huA⟩, ⟨?_, ?_⟩, ?_, hv'8, huD, hv'N, huC, hv'C, hmatch⟩
  · exact Subgroup.mul_mem _ (hS.I_le_K hxI) (Subgroup.pow_mem _ hvK k)
  · exact Subgroup.mul_mem _ (Subgroup.le_normalizer hxA) (Subgroup.pow_mem _ hvA k)
  · have : u ^ 8 = 1 := hu8
    rw [this]; exact Subgroup.one_mem _

end Elem

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
