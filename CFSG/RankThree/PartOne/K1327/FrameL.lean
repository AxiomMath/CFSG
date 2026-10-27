module

public import CFSG.RankThree.PartOne.K1327.ModelL
public import CFSG.RankThree.PartOne.K1320.L4CT

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.RankThree.PartOne.K1320

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem q8_surjective : Function.Surjective (q8 K) := (KFOUT3.m8Iso (K := K)).surjective

theorem exists_ne_one_mem_Rr {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) :
    ∃ a : Kˣ, a ≠ 1 ∧ Tl K a ∈ Rr K r := by
  have hcard : Nat.card (Rr K r) = r := rootsOfUnity_card hr hrq
  rcases Subgroup.bot_or_exists_ne_one (Rr K r) with h | ⟨x, hx, hx1⟩
  · exfalso
    rw [h, Subgroup.card_bot] at hcard
    exact hr.one_lt.ne hcard
  · obtain ⟨a, ha, hax⟩ := hx
    refine ⟨a, fun h => hx1 ?_, ?_⟩
    · rw [← hax, h, map_one]
    · exact ⟨a, ha, rfl⟩

omit [Finite G] in
theorem model_comm_Tl (fr : Row8Frame p A L E f K) {a : Kˣ} {r : ℕ} (haR : Tl K a ∈ Rr K r)
    {n : G} (hn : n ∈ L) {m : ↥(M8 K)} (hm : q8 K m = fr.ε ⟨n, hn⟩)
    (hnR : ∀ x ∈ fr.lft (Rr K r), n * x = x * n) : m * Tl K a = Tl K a * m := by
  obtain ⟨l, hl⟩ := fr.surj (q8 K (Tl K a))
  have hlR : (l : G) ∈ fr.lft (Rr K r) := by
    refine mem_liftM.2 ⟨l.2, Tl K a, haR, ?_⟩
    rw [← hl]
  have h1 : n * (l : G) = (l : G) * n := hnR _ hlR
  have h2 : (⟨n, hn⟩ : ↥L) * l = l * ⟨n, hn⟩ := Subtype.ext h1
  have h3 := congrArg fr.ε h2
  rw [map_mul, map_mul, hl, ← hm, ← map_mul, ← map_mul] at h3
  exact (Row8Frame.q8_inj (K := K)) h3

omit [Finite G] in
theorem conj_normalizes (fr : Row8Frame p A L E f K) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K - 1) {n : G} (hn : n ∈ L)
    (hnR : ∀ x ∈ fr.lft (Rr K r), n * x = x * n) :
    (∀ k ∈ fr.lft (slB K 0 1), n * k * n⁻¹ ∈ fr.lft (slB K 0 1)) ∧
      (∀ k ∈ fr.lft (slB K 2 3), n * k * n⁻¹ ∈ fr.lft (slB K 2 3)) := by
  obtain ⟨a, ha1, haR⟩ := exists_ne_one_mem_Rr (K := K) hr hrq
  obtain ⟨m, hm⟩ := q8_surjective (K := K) (fr.ε ⟨n, hn⟩)
  have hmc := model_comm_Tl fr haR hn hm hnR
  obtain ⟨hc1, hc2⟩ := conj_slB ha1 hmc
  have hconj : ∀ (S : Subgroup ↥(M8 K)), (∀ g ∈ S, m * g * m⁻¹ ∈ S) →
      ∀ k ∈ fr.lft S, n * k * n⁻¹ ∈ fr.lft S := by
    intro S hS k hk
    have h1 := conjBy_liftM (ε := fr.ε) (ψ := q8 K) S m ⟨n, hn⟩ hm.symm
    have h2 : S.map (MulAut.conj m).toMonoidHom ≤ S := by
      rintro _ ⟨g, hg, rfl⟩
      exact hS g hg
    have h3 : conjBy n (fr.lft S) ≤ fr.lft S := by
      show conjBy n (liftM fr.ε (q8 K) S) ≤ liftM fr.ε (q8 K) S
      rw [h1]
      exact liftM_mono h2
    apply h3
    rw [Equivariance.mem_conjBy]
    have : n⁻¹ * (n * k * n⁻¹) * n = k := by group
    rw [this]
    exact hk
  exact ⟨hconj _ hc1, hconj _ hc2⟩

omit [Finite G] in
theorem commute_of_centralizes_blocks (fr : Row8Frame p A L E f K) (hZ : Subgroup.center L = ⊥)
    {n : G} (hn : n ∈ L)
    (h1 : ∀ k ∈ fr.lft (slB K 0 1), n * k = k * n)
    (h2 : ∀ k ∈ fr.lft (slB K 2 3), n * k = k * n) : ∀ e ∈ A ⊓ L, n * e = e * n := by
  obtain ⟨m, hm⟩ := q8_surjective (K := K) (fr.ε ⟨n, hn⟩)
  have hgen : ∀ (S : Subgroup ↥(M8 K)), (∀ k ∈ fr.lft S, n * k = k * n) →
      ∀ s ∈ S, m * s = s * m := by
    intro S hS s hs
    obtain ⟨l, hl⟩ := fr.surj (q8 K s)
    have hlS : (l : G) ∈ fr.lft S := by
      refine mem_liftM.2 ⟨l.2, s, hs, ?_⟩
      rw [← hl]
    have h3 : (⟨n, hn⟩ : ↥L) * l = l * ⟨n, hn⟩ := Subtype.ext (hS _ hlS)
    have h4 := congrArg fr.ε h3
    rw [map_mul, map_mul, hl, ← hm, ← map_mul, ← map_mul] at h4
    exact (Row8Frame.q8_inj (K := K)) h4
  have hmc : m ∈ Subgroup.centralizer ((slB K 0 1 ⊔ slB K 2 3 : Subgroup ↥(M8 K)) : Set ↥(M8 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hle : slB K 0 1 ⊔ slB K 2 3 ≤ Subgroup.centralizer ({m} : Set ↥(M8 K)) := by
      refine sup_le (fun s hs => ?_) (fun s hs => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hgen _ h1 s hs).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hgen _ h2 s hs).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hs)
  rw [centralizer_slB_blocks] at hmc
  obtain ⟨a, rfl⟩ := hmc
  intro e he
  have hAT := fr.hAT
  have hmem : fr.ε ⟨e, he.2⟩ ∈ (T8 p K).map (q8 K) := by
    rw [← hAT]
    exact Subgroup.mem_map_of_mem fr.ε (Subgroup.mem_subgroupOf.2 he)
  obtain ⟨t, ht, hte⟩ := hmem
  have h5 := Tl_comm_T8 ht a
  have h6 : fr.ε (⟨n, hn⟩ * ⟨e, he.2⟩) = fr.ε (⟨e, he.2⟩ * ⟨n, hn⟩) := by
    rw [map_mul, map_mul, ← hm, ← hte, ← map_mul, ← map_mul, h5]
  exact congrArg Subtype.val (fr.inj hZ h6)

end CFSG.RankThree.PartOne.K1327
