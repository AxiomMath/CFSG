module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenTen
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBPair
public import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

structure Eleven11Data (M V Q U L X : Subgroup G) : Prop where
  setting : Setting11 M V Q
  two_lt_m : 2 < mBar M ⊥ V setting.isElemAbelian
  one_lt_r : 1 < rMV M V
  r_lt_m : rMV M V < (mBar M ⊥ V setting.isElemAbelian : ℕ∞)
  mem_delta : U ∈ deltaEleven M V
  mem_blocks : L ∈ elevenBlocksB M Q U
  isHall : IsHallTwoPrimeOf X (L ⊓ M)

theorem exists_eleven11Data {M V Q : Subgroup G}
    (hset : Setting11 M V Q) (h2 : 2 < mBar M ⊥ V hset.isElemAbelian)
    (hlt : rMV M V < (mBar M ⊥ V hset.isElemAbelian : ℕ∞)) :
    ∃ U L X : Subgroup G, Eleven11Data M V Q U L X := by
  have h116 := eleven_six_B hset
  obtain ⟨hr, hm⟩ := one_lt_rMV_and_one_lt_mBar hset.isElemAbelian h116 h2
  obtain ⟨U, hU⟩ := eleven_f hset.isElemAbelian hset.normal hlt
  have hUΓ := deltaEleven_subset_gammaEleven M V hU
  obtain ⟨L, hL⟩ := exists_mem_elevenBlocksB hset hUΓ
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hset hUΓ hL
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hL).2
  obtain ⟨n, -, -, -, -, -, -, ⟨X, hX⟩, -⟩ :=
    eleven_ten_of_one_lt hset hr hm hU hLb hLM
  exact ⟨U, L, X, ⟨hset, h2, hr, hlt, hU, hL, hX⟩⟩


theorem Eleven11Data.ten {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∃ n : ℕ, 1 < n ∧ IsLTwoBlockType L n ∧ rMV M V = (n : ℕ∞) ∧
      (∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
        L' = L) ∧
      ∀ D : Subgroup G, IsHallTwoPrimeOf D (L ⊓ M) → IsCyclic ↥D ∧ Nat.card D = 2 ^ n - 1 ∧
        V ⊓ Subgroup.centralizer (D : Set G) = U ∧ ActsRegularlyOn D (nonIdentity ⁅V, D⁆) := by
  have hset := hd.setting
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hm : 1 < mBar M ⊥ V hset.isElemAbelian := by
    have := hd.two_lt_m
    omega
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hset hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : ∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' →
      ¬ L' ≤ M → ∃ n : ℕ, IsLTwoBlockType L' n := by
    intro L' hL' hL'M
    obtain ⟨n, hn, hnat⟩ := eleven_eight hset hd.one_lt_r hm hUΓ hL' hL'M
    exact ⟨n, hn, hnat, eleven_seven hset hd.one_lt_r hm hUΓ hL' hL'M⟩
  obtain ⟨n, hn, hnat, hr, -, huniq, -, -, hD⟩ := eleven_ten hset hd.mem_delta h78 hLb hLM
  exact ⟨n, hn, ⟨hn, hnat, eleven_seven hset hd.one_lt_r hm hUΓ hLb hLM⟩, hr, huniq, hD⟩


theorem isHallTwoPrimeOf_conjSubgroup {D K : Subgroup G} (h : IsHallTwoPrimeOf D K) (g : G) :
    IsHallTwoPrimeOf (conjSubgroup D g) (conjSubgroup K g) := by
  obtain ⟨hDK, hodd, k, hk⟩ := h
  refine ⟨conjSubgroup_mono_left g hDK, ?_, k, ?_⟩
  · rw [E3.card_conjSubgroup]; exact hodd
  · rw [E3.relIndex_conjSubgroup]; exact hk


theorem eleven_ten_sylow_normal {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    IsSylowOf 2 (L ⊓ Q) (L ⊓ M) ∧
      L ⊓ M ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) ∧
      L ⊓ Q ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨n, -, h78, -⟩ := hd.ten
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  obtain ⟨⟨hS, hLMeq⟩, -⟩ := eleven_nine_one hd.setting hUΓ hLb hLM h78
  have hQle : Q ≤ M ⊓ Subgroup.centralizer (V : Set G) := hd.setting.sylowQ.1
  have hSM : L ⊓ Q ≤ L ⊓ M := inf_le_inf_left L (hQle.trans inf_le_left)
  refine ⟨⟨hSM, hS.2.1, ?_⟩, hLMeq.le.trans inf_le_right,
    inf_le_right.trans (hQle.trans inf_le_right)⟩
  intro h2
  apply hS.2.2
  have hmul := Subgroup.relIndex_mul_relIndex (L ⊓ Q) (L ⊓ M) L hSM inf_le_left
  exact h2.trans (Dvd.intro _ hmul)


private theorem hall_compl {S H D : Subgroup G} (hS : IsSylowOf 2 S H)
    (hD : IsHallTwoPrimeOf D H) : S ⊓ D = ⊥ ∧ S ⊔ D = H := by
  obtain ⟨hSH, hS2, hSi⟩ := hS
  obtain ⟨hDH, hDodd, k, hk⟩ := hD
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS2
  have h1 : S.relIndex H * Nat.card S = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := S) (K := H)
    rwa [inf_eq_left.2 hSH] at this
  have h2 : D.relIndex H * Nat.card D = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := D) (K := H)
    rwa [inf_eq_left.2 hDH] at this
  rw [hk] at h2
  rw [hn] at h1
  have hcn : Nat.Coprime (2 ^ n) (Nat.card D) :=
    (Nat.coprime_two_left.2 hDodd).pow_left n
  have hSodd : Odd (S.relIndex H) := by
    rcases Nat.even_or_odd (S.relIndex H) with he | ho
    · exact absurd (even_iff_two_dvd.1 he) hSi
    · exact ho
  have hck : Nat.Coprime (2 ^ k) (S.relIndex H) :=
    (Nat.coprime_two_left.2 hSodd).pow_left k
  have hd1 : 2 ^ n ∣ 2 ^ k := by
    refine hcn.dvd_of_dvd_mul_right ?_
    rw [h2, ← h1]
    exact Dvd.intro_left _ rfl
  have hd2 : 2 ^ k ∣ 2 ^ n := by
    refine hck.dvd_of_dvd_mul_left ?_
    rw [h1, ← h2]
    exact Dvd.intro _ rfl
  have hnk : 2 ^ n = 2 ^ k := Nat.dvd_antisymm hd1 hd2
  have hSD : Nat.card S * Nat.card D = Nat.card H := by
    rw [hn, hnk]; exact h2
  have hcop : Nat.Coprime (Nat.card S) (Nat.card D) := by rw [hn]; exact hcn
  have hdvd : Nat.card S * Nat.card D ∣ Nat.card ↥(S ⊔ D) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hle : S ⊔ D ≤ H := sup_le hSH hDH
  have hge : Nat.card H ≤ Nat.card ↥(S ⊔ D) := by
    rw [← hSD]; exact Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨?_, Subgroup.eq_of_le_of_card_ge hle hge⟩
  have hdi : Nat.card ↥(S ⊓ D) ∣ 1 := by
    have := Nat.dvd_gcd (Subgroup.card_dvd_of_le (inf_le_left : S ⊓ D ≤ S))
      (Subgroup.card_dvd_of_le (inf_le_right : S ⊓ D ≤ D))
    rwa [hcop] at this
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdi)

theorem exists_conj_of_isHallTwoPrimeOf {S H D D' : Subgroup G} (hS : IsSylowOf 2 S H)
    (hSn : H ≤ Subgroup.normalizer (S : Set G)) (hD : IsHallTwoPrimeOf D H)
    (hD' : IsHallTwoPrimeOf D' H) : ∃ c ∈ S, D' = CFSG.Walter.W67.Sec6.cj c D := by
  obtain ⟨hi₁, hs₁⟩ := hall_compl hS hD
  obtain ⟨hi₂, hs₂⟩ := hall_compl hS hD'
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS.2.1
  have hSodd : Odd (S.relIndex H) := by
    rcases Nat.even_or_odd (S.relIndex H) with he | ho
    · exact absurd (even_iff_two_dvd.1 he) hS.2.2
    · exact ho
  have hcop : Nat.Coprime (Nat.card S) (S.relIndex H) := by
    rw [hn]; exact (Nat.coprime_two_left.2 hSodd).pow_left n
  exact CFSG.Walter.W67.Sec6.exists_conj_complement_in (C := S) (N := H) (W₁ := D) (W₂ := D')
    hS.1 hSn hcop hD.1 hD'.1 hi₁ hs₁ hi₂ hs₂


theorem eleven_ten_hall_mod {M V Q U L X D D' : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (hD : IsHallTwoPrimeOf D (L ⊓ M))
    (hD' : IsHallTwoPrimeOf D' (L ⊓ M)) :
    ∀ x ∈ D, ∃ y ∈ D', x * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hS, hSn, hSC⟩ := eleven_ten_sylow_normal hd
  obtain ⟨c, hcS, hc⟩ := exists_conj_of_isHallTwoPrimeOf hS hSn hD hD'
  intro x hx
  have hxM : x ∈ M := (Subgroup.mem_inf.1 (hD.1 hx)).2
  have hcC : c ∈ Subgroup.centralizer (V : Set G) := hSC (hcS)
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hd.setting.normal hxM
  refine ⟨c * x * c⁻¹, ?_, ?_⟩
  · rw [hc]
    exact CFSG.Walter.W67.Sec6.conj_mem_cj hx
  ·
    have e : x * (c * x * c⁻¹)⁻¹ = (x * c * x⁻¹) * c⁻¹ := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hcC)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : x⁻¹ * v * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hv'
    calc v * (x * c * x⁻¹) = x * ((x⁻¹ * v * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * v * x)) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * v := by group


theorem eleven_ten_hnorm {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x ∈ X, ∃ y ∈ X, g * x * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  intro g hg hgU x hx
  obtain ⟨hgM, -⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨n, -, -, -, huniq, -⟩ := hd.ten
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hgU' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := (Subgroup.normalizer (U : Set G)).inv_mem hgU
  have hU' : conjSubgroup U g⁻¹ = U := conjSubgroup_eq_iff_mem_normalizer.2 hgU'
  have hM' : conjSubgroup M g⁻¹ = M :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgM')
  have hCg : conjSubgroup (Subgroup.centralizer (U : Set G)) g⁻¹ =
      Subgroup.centralizer (U : Set G) := by
    rw [E3.conjSubgroup_centralizer, hU']
  have hLg : IsBlockOfInX (Subgroup.centralizer (U : Set G)) (conjSubgroup L g⁻¹) := by
    have := isBlockOfInX_conjSubgroup g⁻¹ hLb
    rwa [hCg] at this
  have hLgM : ¬ conjSubgroup L g⁻¹ ≤ M := by
    intro hle
    apply hLM
    have h1 := (E3.conjSubgroup_le_iff_le_inv g⁻¹).1 hle
    rw [inv_inv, conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgM)] at h1
    exact h1
  have hLeq : conjSubgroup L g⁻¹ = L := huniq _ hLg hLgM
  have hKeq : conjSubgroup (L ⊓ M) g⁻¹ = L ⊓ M := by
    rw [E3.conjSubgroup_inf, hLeq, hM']
  have hX' : IsHallTwoPrimeOf (conjSubgroup X g⁻¹) (L ⊓ M) := by
    have := isHallTwoPrimeOf_conjSubgroup hd.isHall g⁻¹
    rwa [hKeq] at this
  have hmem : g * x * g⁻¹ ∈ conjSubgroup X g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  exact eleven_ten_hall_mod hd hX' hd.isHall _ hmem


end CFSG.LocalAnalysis.WeakClosure81
