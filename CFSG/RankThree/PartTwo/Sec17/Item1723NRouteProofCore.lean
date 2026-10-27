module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProof1723
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.RankThree.PartTwo.Late.Cores17
public import CFSG.RankThree.PartTwo.Sec17.Item1726Proof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof1723N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem map_conj_not_le_M (h : Sec17Y1 G A c L Y₀ Y₁ S p P) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    ¬ Y₁.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro hle
  apply h.not_le_M
  have hgM : g ∈ Subgroup.normalizer (Y₀ : Set G) := h.normalizer_le hg
  intro y hy
  have h1 : g * y * g⁻¹ ∈ Subgroup.normalizer (Y₀ : Set G) := hle ⟨y, hy, rfl⟩
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hgM) h1) hgM

theorem exists_conj_eq_pow (h1723 : Item1723N) (h : Sec17W G A c L Y₀ Y₁ S p P w Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    ∃ j : ℕ, Y₁.map (MulAut.conj g).toMonoidHom = Y₁.map (MulAut.conj (w ^ j)).toMonoidHom := by
  have hY : Y₁.map (MulAut.conj g).toMonoidHom ∈
      ({yI Y₁ w 1, yI Y₁ w 2, yI Y₁ w 3} : Set (Subgroup G)) := by
    rw [← (h1723 G A c L Y₀ Y₁ S p P w Q h).1]
    exact ⟨HeadProof.map_conj_mem_scriptY1Star hg h.mem_y1Star,
      map_conj_not_le_M h.toSec17Y1 hg⟩
  rcases hY with h1 | h1 | h1
  · exact ⟨0, h1⟩
  · exact ⟨1, h1⟩
  · exact ⟨2, h1⟩

theorem yI_mem (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (i : ℕ) :
    yI Y₁ w i ∈ scriptY1Star A (lB A) :=
  HeadProof.map_conj_mem_scriptY1Star (pow_mem (Subgroup.mem_inf.mp h.w_mem).1 _) h.mem_y1Star

theorem yI_ne (h1723 : Item1723N) (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    yI Y₁ w 1 ≠ yI Y₁ w 2 ∧ yI Y₁ w 1 ≠ yI Y₁ w 3 ∧ yI Y₁ w 2 ≠ yI Y₁ w 3 := by
  obtain ⟨hset, h3⟩ := h1723 G A c L Y₀ Y₁ S p P w Q h
  rw [hset] at h3
  exact ne_of_ncard_eq_three h3

theorem exists_le_yI (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h1723 : Item1723N) (h1724 : Item1724Three)
    (h : Sec17WQ G A c L Y₀ Y₁ S p P w Q) {K : Subgroup G} (hKQ : K ≤ Q)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {b : G}
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (hb : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ∈ scriptY3 A (lB A)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ K ≤ yI Y₁ w i := by
  by_cases hK : K = ⊥
  · exact ⟨1, le_rfl, by norm_num, hK ▸ bot_le⟩
  have hKQ' : K ∈ scriptQ A (lB A) := mem_scriptQ_of_le h.mem_qStar_G.prop.1.1 hKQ hAK
  have hKD : K ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hKQ' hKb
  have hDM : ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) := fun hle =>
    hK (le_bot_iff.mp ((le_inf hKQ (hKD.trans hle)).trans
      (h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W).le))
  have hD1 := h.toSec17Std.mem_scriptY1_of_not_le h166 hbot hb hDM
  obtain ⟨Y, hDY, hY⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY1 A (lB A))) hD1
  have hYmem : Y ∈ ({yI Y₁ w 1, yI Y₁ w 2, yI Y₁ w 3} : Set (Subgroup G)) := by
    rw [← (h1723 G A c L Y₀ Y₁ S p P w Q h.toSec17W).1]
    exact ⟨hY, fun hle => hDM (hDY.trans hle)⟩
  rcases hYmem with h1 | h1 | h1
  · exact ⟨1, le_rfl, by norm_num, h1 ▸ hKD.trans hDY⟩
  · exact ⟨2, by norm_num, by norm_num, h1 ▸ hKD.trans hDY⟩
  · exact ⟨3, by norm_num, le_rfl, h1 ▸ hKD.trans hDY⟩

end Proof1723N

theorem item1725_of_1723N
    (h1710 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1710 A (lB A))
    (h1712 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1712 A (lB A))
    (h166 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item166 A (lB A))
    (hbot : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h1723 : Item1723N) (h1724 : Item1724Three) : Item1725 := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h X hX
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXQ, hXp, hXN⟩ := hX
  have hwX : w ∈ Subgroup.normalizer (X : Set G) :=
    hXN (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans hXN
  have h166' := h166 G A c L Y₀ h.toSec17Std
  have hbot' := hbot G A c L h.toSec14Std
  have h1710' := h1710 G A c L Y₀ h.toSec17Std
  obtain ⟨B, hB, hBY, -⟩ := h1712 G A c L Y₀ h.toSec17Std
  have hBA : B ≤ A := hB.1
  have hB9 : Nat.card B = 9 := by
    have h2 := hB.2
    rw [h.isE27.2] at h2
    omega
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le h.isE27.1 hBA
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hAX
  have hXp' : IsPGroup p X := (isPiSubgroup_piOf_iff h.p_prime X).mp hXp
  have hcop : ∀ K : Subgroup G, K ≤ X → Nat.Coprime 3 (Nat.card K) := by
    intro K hK
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hXp'.to_le hK)
    rw [hn]
    exact Nat.Coprime.pow_right n
      ((Nat.coprime_primes Nat.prime_three h.p_prime).mpr h.three_lt_p.ne)
  have hmem : ∀ i, 1 ≤ i → i ≤ 3 → yI Y₁ w i ∈ scriptY1Star A (lB A) :=
    fun i _ _ => Proof1723N.yI_mem h.toSec17W i
  have hAY : ∀ i, 1 ≤ i → i ≤ 3 → A ≤ Subgroup.normalizer (yI Y₁ w i : Set G) :=
    fun i hi1 hi3 => (hmem i hi1 hi3).prop.1.1.1.2
  obtain ⟨h12, h13, h23⟩ := Proof1723N.yI_ne h1723 h.toSec17W
  have hne : ∀ i j, 1 ≤ i → i ≤ 3 → 1 ≤ j → j ≤ 3 → i ≠ j → yI Y₁ w i ≠ yI Y₁ w j := by
    intro i j hi1 hi3 hj1 hj3 hij
    interval_cases i <;> interval_cases j
    all_goals first | exact absurd rfl hij | exact h12 | exact h13 | exact h23 |
      exact h12.symm | exact h13.symm | exact h23.symm
  have hdisj : ∀ i j, 1 ≤ i → i ≤ 3 → 1 ≤ j → j ≤ 3 → i ≠ j →
      (X ⊓ yI Y₁ w i) ⊓ (X ⊓ yI Y₁ w j) = ⊥ := by
    intro i j hi1 hi3 hj1 hj3 hij
    exact h.eq_bot_of_le_inf h1710' h166' hbot' h1724
      (inf_le_left.trans (inf_le_left.trans hXQ))
      (le_normalizer_inf (le_normalizer_inf hAX (hAY i hi1 hi3))
        (le_normalizer_inf hAX (hAY j hj1 hj3)))
      (hmem i hi1 hi3) (hmem j hj1 hj3) (hne i j hi1 hi3 hj1 hj3 hij)
      (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hD : ∀ D ∈ CFSG.Open.signalizerFunctorEk 3 1 B, ∃ b ∈ B, b ≠ 1 ∧
      Subgroup.centralizer (D : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rintro D ⟨hDB, hD3⟩
    have hD1 : D ≠ ⊥ := by
      intro hbot0
      rw [hbot0, Subgroup.card_bot] at hD3
      norm_num at hD3
    obtain ⟨⟨b, hbD⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    have hb1' : b ≠ 1 := fun h' => hb1 (Subtype.ext h')
    have hb3 : b ^ 3 = 1 := hBe.2 b (hDB hbD)
    have hzb : Subgroup.zpowers b = D := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hbD)
      (le_of_eq (by rw [hD3, Nat.card_zpowers, orderOf_eq_prime hb3 hb1', pow_one]))
    refine ⟨b, hDB hbD, hb1', ?_⟩
    rw [← hzb, KFacts.KS14.centralizer_zpowers_eq]
  have hcover : ∀ D ∈ CFSG.Open.signalizerFunctorEk 3 1 B, ∃ i, 1 ≤ i ∧ i ≤ 3 ∧
      X ⊓ Subgroup.centralizer (D : Set G) ≤ X ⊓ yI Y₁ w i := by
    intro D hDmem
    obtain ⟨b, hbB, hb1, hCD⟩ := hD D hDmem
    have hAb : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := fun a ha =>
      Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem ha (hBA hbB)))
    obtain ⟨i, hi1, hi3, hle⟩ := Proof1723N.exists_le_yI h166' hbot' h1723 h1724 h
      (K := X ⊓ Subgroup.centralizer ({b} : Set G)) (inf_le_left.trans hXQ)
      (le_normalizer_inf hAX hAb) inf_le_right (hBY b hbB hb1)
    exact ⟨i, hi1, hi3, by rw [hCD]; exact le_inf inf_le_left hle⟩
  have hgenX := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three B X hBe (by rw [hB9]; norm_num) hBX (hcop X le_rfl)
  have hclause1 : X = (X ⊓ yI Y₁ w 1) ⊔ (X ⊓ yI Y₁ w 2) ⊔ (X ⊓ yI Y₁ w 3) := by
    apply le_antisymm
    · conv_lhs => rw [← hgenX]
      refine iSup₂_le fun D hDmem => ?_
      obtain ⟨i, hi1, hi3, hle⟩ := hcover D hDmem
      interval_cases i
      · exact hle.trans (le_sup_left.trans le_sup_left)
      · exact hle.trans (le_sup_right.trans le_sup_left)
      · exact hle.trans le_sup_right
    · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hcard : ∀ k, 1 ≤ k → k ≤ 3 → Nat.card (X ⊓ yI Y₁ w k : Subgroup G) =
      Nat.card (X ⊓ yI Y₁ w 3 : Subgroup G) := fun k hk1 _ => by
    rw [inf_yI_eq_map_conj h.w_pow_three hwX hk1,
      Subgroup.card_map_of_injective (MulAut.conj _).injective]
  refine ⟨hclause1, fun i hi1 _ => inf_yI_eq_map_conj h.w_pow_three hwX hi1, fun hXab => ?_⟩
  choose! idx hidx1 hidx3 hidxle using hcover
  obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ ∈ CFSG.Open.signalizerFunctorEk 3 1 B := by
    obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 3 (n := 1)
      (by rw [hB9]; norm_num)
    exact ⟨E.map B.subtype, Subgroup.map_subtype_le E,
      by rw [Subgroup.card_map_of_injective B.subtype_injective, hE]⟩
  have hXB : X ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
    have hKD : ∀ D ∈ CFSG.Open.signalizerFunctorEk 3 1 B,
        X ⊓ Subgroup.centralizer (B : Set G) ≤ X ⊓ yI Y₁ w (idx D) := fun D hDmem =>
      (inf_le_inf_left X (Subgroup.centralizer_le hDmem.1)).trans (hidxle D hDmem)
    by_cases hall : ∀ D ∈ CFSG.Open.signalizerFunctorEk 3 1 B, idx D = idx D₀
    · have hXi₀ : X ⊓ yI Y₁ w (idx D₀) = X := by
        apply le_antisymm inf_le_left
        conv_lhs => rw [← hgenX]
        refine iSup₂_le fun D hDmem => ?_
        have h1 := hidxle D hDmem
        rw [hall D hDmem] at h1
        exact h1
      have hXk : ∀ k, 1 ≤ k → k ≤ 3 → X ⊓ yI Y₁ w k = X := fun k hk1 hk3 =>
        Subgroup.eq_of_le_of_card_ge inf_le_left (by
          rw [hcard k hk1 hk3, ← hcard (idx D₀) (hidx1 D₀ hD₀) (hidx3 D₀ hD₀), hXi₀])
      have hX1 : X = ⊥ := by
        have h1 := hdisj 1 2 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        rwa [hXk 1 le_rfl (by norm_num), hXk 2 (by norm_num) (by norm_num), inf_idem] at h1
      rw [hX1, bot_inf_eq]
    · simp only [not_forall] at hall
      obtain ⟨D, hDmem, hDne⟩ := hall
      have h1 := hdisj (idx D) (idx D₀) (hidx1 D hDmem) (hidx3 D hDmem) (hidx1 D₀ hD₀)
        (hidx3 D₀ hD₀) hDne
      rw [eq_bot_iff, ← h1]
      exact le_inf (hKD D hDmem) (hKD D₀ hD₀)
  obtain ⟨-, hind⟩ := Late.iSup_inf_centralizer_eq_and_iSupIndep Nat.prime_three hBe
    (by rw [hB9]; norm_num) hBX hXab (hcop X le_rfl) hXB
  classical
  let : Fintype {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} := Fintype.ofFinite _
  have hblock : ∀ k, 1 ≤ k → k ≤ 3 → ∀ s : Finset {D : Subgroup G // D ≤ B ∧ Nat.card D = 3},
      (∀ D : {D : Subgroup G // D ≤ B ∧ Nat.card D = 3}, idx D.1 = k → D ∈ s) →
      X ⊓ yI Y₁ w k ≤ s.sup (fun D : {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} =>
        X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G)) := by
    intro k hk1 hk3 s hs
    have hBk : B ≤ Subgroup.normalizer ((X ⊓ yI Y₁ w k : Subgroup G) : Set G) :=
      hBA.trans (le_normalizer_inf hAX (hAY k hk1 hk3))
    have hgenk := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
      Nat.prime_three B (X ⊓ yI Y₁ w k) hBe (by rw [hB9]; norm_num) hBk (hcop _ inf_le_left)
    conv_lhs => rw [← hgenk]
    refine iSup₂_le fun D hDmem => ?_
    by_cases hDk : idx D = k
    · have hD' : (⟨D, hDmem.1, by rw [hDmem.2, pow_one]⟩ :
          {D : Subgroup G // D ≤ B ∧ Nat.card D = 3}) ∈ s := hs _ hDk
      calc X ⊓ yI Y₁ w k ⊓ Subgroup.centralizer (D : Set G) ≤
            X ⊓ Subgroup.centralizer (D : Set G) :=
            le_inf (inf_le_left.trans inf_le_left) inf_le_right
        _ ≤ _ := Finset.le_sup (f := fun D : {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} =>
            X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G)) hD'
    · have hbot0 := hdisj k (idx D) hk1 hk3 (hidx1 D hDmem) (hidx3 D hDmem) (Ne.symm hDk)
      have h1 : X ⊓ yI Y₁ w k ⊓ Subgroup.centralizer (D : Set G) ≤ ⊥ := by
        rw [← hbot0]
        exact le_inf inf_le_left
          ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans (hidxle D hDmem))
      exact h1.trans bot_le
  set t : Finset {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} :=
    Finset.univ.filter (fun D => idx D.1 = 1) with ht
  set u : Finset {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} :=
    Finset.univ.filter (fun D => ¬ idx D.1 = 1) with hu
  have hX1t := hblock 1 le_rfl (by norm_num) t
    (fun D hD1 => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD1⟩)
  have hX2u := hblock 2 (by norm_num) (by norm_num) u
    (fun D hD1 => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hD1]; norm_num⟩)
  have hX3u := hblock 3 (by norm_num) le_rfl u
    (fun D hD1 => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hD1]; norm_num⟩)
  have htu : Disjoint t u := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hdisjtu := disjoint_sup_sup_of_isMulCommutative hXab
    (fun D : {D : Subgroup G // D ≤ B ∧ Nat.card D = 3} =>
      X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G)) (fun _ => inf_le_left) hind htu
  have hdisj1 : Disjoint (X ⊓ yI Y₁ w 1) ((X ⊓ yI Y₁ w 2) ⊔ (X ⊓ yI Y₁ w 3)) :=
    hdisjtu.mono hX1t (sup_le hX2u hX3u)
  have hn23 : X ⊓ yI Y₁ w 3 ≤ Subgroup.normalizer ((X ⊓ yI Y₁ w 2 : Subgroup G) : Set G) :=
    le_normalizer_of_le_of_isMulCommutative hXab inf_le_left inf_le_left
  have hn1 : (X ⊓ yI Y₁ w 2) ⊔ (X ⊓ yI Y₁ w 3) ≤
      Subgroup.normalizer ((X ⊓ yI Y₁ w 1 : Subgroup G) : Set G) :=
    le_normalizer_of_le_of_isMulCommutative hXab inf_le_left (sup_le inf_le_left inf_le_left)
  have hcard23 : Nat.card ((X ⊓ yI Y₁ w 2) ⊔ (X ⊓ yI Y₁ w 3) : Subgroup G) =
      Nat.card (X ⊓ yI Y₁ w 2 : Subgroup G) * Nat.card (X ⊓ yI Y₁ w 3 : Subgroup G) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn23
      (disjoint_iff.mpr (hdisj 2 3 (by norm_num) (by norm_num) (by norm_num) le_rfl
        (by norm_num)))
  have hcardX : Nat.card X = Nat.card (X ⊓ yI Y₁ w 1 : Subgroup G) *
      (Nat.card (X ⊓ yI Y₁ w 2 : Subgroup G) * Nat.card (X ⊓ yI Y₁ w 3 : Subgroup G)) := by
    conv_lhs => rw [hclause1, sup_assoc]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn1 hdisj1,
      hcard23]
  rw [hcardX, hcard 1 le_rfl (by norm_num), hcard 2 (by norm_num) (by norm_num)]
  ring

theorem item1725_of_named_1723N (h1710 : Item1710S17) (h1712 : Item1712S17)
    (h166 : Item166S17) (hbot : Item145BotS14) (h1723 : Item1723N) (h1724 : Item1724Three) :
    Item1725 :=
  item1725_of_1723N h1710 h1712 h166 hbot h1723 h1724

end CFSG.RankThree.PartTwo.Sec17
