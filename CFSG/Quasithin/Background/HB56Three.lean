module

public import CFSG.Quasithin.EmptyFaithful.SzN17Dig

public section

namespace CFSG.Quasithin.H.B56N3

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Quasithin.SzN17
  CFSG.Quasithin.S153L

variable {V : Type} [CommGroup V] [Finite V]

structure Digest3 (H P Z₁ Z₂ : Subgroup (MulAut V)) : Prop where
  normal₁ : Z₁ = ⊥ ∨ IsNormalThree H Z₁
  normal₂ : Z₂ = ⊥ ∨ IsNormalThree H Z₂
  decomp : H ≤ perfectCore H ⊔ (Z₁ ⊔ Z₂) ⊔ P
  unique : ∀ Q : Subgroup (MulAut V), IsNormalThree H Q → Q = Z₁ ∨ Q = Z₂

omit [Finite V] in
theorem digest3_of_good_self {H P Z : Subgroup (MulAut V)} (hZ : GoodFactor H P H Z) :
    Digest3 H P Z Z := by
  refine ⟨hZ.normal, hZ.normal, ?_, fun Q hQ => Or.inl (hZ.unique Q hQ)⟩
  rw [sup_idem]
  exact hZ.decomp

omit [Finite V] in
theorem digest3_of_product {H P A B ZA ZB : Subgroup (MulAut V)} (hH : A ⊔ B = H)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hcen : CenterTrivial A ∨ CenterTrivial B) (hA : GoodFactor H P A ZA)
    (hB : GoodFactor H P B ZB) : Digest3 H P ZA ZB := by
  have hAH : A ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hH ▸ le_sup_right
  have hc' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hinf' : B ⊓ A = ⊥ := by rw [inf_comm]; exact hinf
  refine ⟨hA.normal, hB.normal, (digest_of_product hH hc hinf hcen hA hB).1, ?_⟩
  intro Q hQ
  have hQ' : IsNormalThree (A ⊔ B) Q := hH ▸ hQ
  have hle : Q ≤ A ∨ Q ≤ B := by
    rcases hcen with h | h
    · exact normalThree_le_factor hc hinf h hQ'
    · have hQ'' : IsNormalThree (B ⊔ A) Q := by rw [sup_comm]; exact hQ'
      rcases normalThree_le_factor hc' hinf' h hQ'' with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
  rcases hle with h | h
  · exact Or.inl (hA.unique Q ⟨h, fun x hx q hq => hQ.2.1 x (hAH hx) q hq, hQ.2.2⟩)
  · exact Or.inr (hB.unique Q ⟨h, fun x hx q hq => hQ.2.1 x (hBH hx) q hq, hQ.2.2⟩)

theorem digest3_case1 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case1 H) :
    H ≤ perfectCore H ⊔ P := by
  obtain ⟨hq, ⟨⟨-, hcase⟩, -⟩, -⟩ := h
  have hE : quasithinGenFitting H ≤ H := quasithinGenFitting_le H
  have hper : ⁅quasithinGenFitting H, quasithinGenFitting H⁆ = quasithinGenFitting H :=
    comp_perfect_of_isQuasisimple hq
  have hEc : quasithinGenFitting H ≤ perfectCore H := le_perfectCore_of_perfect hE hper
  have hHE : H ≤ quasithinGenFitting H ⊔ P := by
    rcases hcase with ⟨-, -, hT⟩ | ⟨hGL, -⟩ | ⟨n, hGL, -⟩ | ⟨hGL, -⟩
    · rcases hT P hP with h1 | ⟨h1, -⟩
      · exact h1.le.trans le_sup_left
      · exact h1.le
    · exact hGL.le.trans le_sup_left
    · exact hGL.le.trans le_sup_left
    · exact hGL.le.trans le_sup_left
  exact hHE.trans (sup_le (hEc.trans le_sup_left) le_sup_right)

theorem digest3_case2 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case2 H) :
    ∃ Z₁ Z₂, Digest3 H P Z₁ Z₂ := by
  obtain ⟨⟨e⟩, -, -⟩ := h
  have h6 : Nat.card ↥H = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨Z, hZ⟩ := goodFactor_of_small hP le_rfl
    (fun h hh g hg => H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)) (by rw [h6])
  exact ⟨Z, Z, digest3_of_good_self hZ⟩

theorem digest3_case3 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case3 H) :
    ∃ Z₁ Z₂, Digest3 H P Z₁ Z₂ := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ := h
  have hG₁H : G₁ ≤ H := hsup ▸ le_sup_left
  have hG₂H : G₂ ≤ H := hsup ▸ le_sup_right
  obtain ⟨hn₁, hn₂⟩ := normal_of_commuting hsup hc
  obtain ⟨⟨Z₁, hZ₁⟩, hc₁⟩ := goodFactor_of_factorList hP hG₁H hn₁ hf₁
  obtain ⟨⟨Z₂, hZ₂⟩, -⟩ := goodFactor_of_factorList hP hG₂H hn₂ hf₂
  exact ⟨Z₁, Z₂, digest3_of_product hsup hc hinf (Or.inl hc₁) hZ₁ hZ₂⟩

theorem digest3_case5 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case5 H) :
    ∃ Z₁ Z₂, Digest3 H P Z₁ Z₂ := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, h₂⟩ := h
  have hG₁H : G₁ ≤ H := hsup ▸ le_sup_left
  have hG₂H : G₂ ≤ H := hsup ▸ le_sup_right
  obtain ⟨hn₁, hn₂⟩ := normal_of_commuting hsup hc
  obtain ⟨⟨Z₁, hZ₁⟩, hc₁⟩ := goodFactor_of_sl3 (G := G₁) (P := P) (H := H) (m := 1) (F := ZMod 2)
    le_rfl odd_one (by simp) e₁
  have hG₂ : ∃ Z₂, GoodFactor H P G₂ Z₂ := by
    rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
    · exact (goodFactor_of_sl3 (G := G₂) (P := P) (H := H) (m := 1) (F := ZMod 2)
        le_rfl odd_one (by simp) e₂).1
    · exact goodFactor_of_image_sl2 hP hG₂H hn₂ hF π hR.1
  obtain ⟨Z₂, hZ₂⟩ := hG₂
  exact ⟨Z₁, Z₂, digest3_of_product hsup hc hinf (Or.inl hc₁) hZ₁ hZ₂⟩

theorem digest3_case4 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (hffJ : H = ffJ H)
    (h : B56Case4 H) : ∃ Z₁ Z₂, Digest3 H P Z₁ Z₂ := by
  obtain ⟨G₁, G₂, t, hJt, hinf, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ := h
  have htK₀ : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    InternalSec.mem_normalizer_sup ht₁ ht₂
  have hK₀H : G₁ ⊔ G₂ ≤ H := by rw [hJt]; exact le_sup_left
  have hG₁H : G₁ ≤ H := le_sup_left.trans hK₀H
  have hG₂H : G₂ ≤ H := le_sup_right.trans hK₀H
  have hPH : P ≤ H := hP.1
  have hnormH' := normal_sup_of_zpowers hJt htK₀ hPH
  have hH2 : H ≤ (G₁ ⊔ G₂) ⊔ P := by
    calc H = ffJ H := hffJ
      _ ≤ (G₁ ⊔ G₂) ⊔ P := iSup₂_le fun A hA =>
        le_of_isPGroup_of_normal hP le_sup_right hnormH' hA.1
          (B6.isPGroup_two_of_isElemAbelian2 hA.2.2.1)
  have hs₁ : IsSimpleGroup ↥G₁ := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e₁.isSimpleGroup
  have hnp₁ : ¬ (Nat.card ↥G₁).Prime := by
    rw [Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    norm_num [Nat.factorial]
  obtain ⟨hgood₁, hcen₁⟩ := goodFactor_of_simple (H := H) (P := P) hs₁ hnp₁
  have hq₁ : CFSG.IsQuasisimple ↥G₁ := comp_quasisimple_of_simple hs₁ hnp₁
  have hperf₁ : ⁅G₁, G₁⁆ = G₁ := comp_perfect_of_isQuasisimple hq₁
  have hG₁core : G₁ ≤ perfectCore H := le_perfectCore_of_perfect hG₁H hperf₁
  have hHN₂ : H ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [hJt]
    refine sup_le (sup_le (fun a ha => ?_) Subgroup.le_normalizer) (Subgroup.zpowers_le.2 ht₂)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm)
  have hG₂n : ∀ h ∈ H, ∀ g ∈ G₂, h * g * h⁻¹ ∈ G₂ := fun h hh g hg =>
    (Subgroup.mem_normalizer_iff.1 (hHN₂ hh) g).1 hg
  have hG₂N : IsNormalThree H G₂ := ⟨hG₂H, hG₂n, hc₂⟩
  have hHN : H ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [hJt]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 htK₀)
  have hPN : P ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    hPH.trans hHN
  have hΞ : ∀ Q : Subgroup (MulAut V), IsNormalThree H Q → Q = G₂ ∨ Q = G₂ := by
    intro Q hQ
    left
    obtain ⟨hQH, hQn, hQc⟩ := hQ
    have hQK : Q ≤ G₁ ⊔ G₂ := by
      intro q hq
      obtain ⟨k, hk, p, hp, hkp⟩ := (mem_sup_iff_of_right_le_normalizer hPN).1 (hH2 (hQH hq))
      obtain ⟨m, hm⟩ := hP.2.1 ⟨p, hp⟩
      have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      obtain ⟨k', hk', hpow⟩ := pow_mul_mem hk (hPN hp) (2 ^ m)
      have hq2 : q ^ 2 ^ m ∈ G₁ ⊔ G₂ := by
        rw [← hkp, hpow, hpm, mul_one]; exact hk'
      have hq3 : q ^ 3 = 1 := by
        have h1 : (⟨q, hq⟩ : ↥Q) ^ Nat.card ↥Q = 1 := pow_card_eq_one'
        rw [hQc] at h1
        simpa using congrArg Subtype.val h1
      exact mem_of_pow_mem_of_coprime' (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2))
        (by rw [hq3]; exact one_mem _) hq2
    have hQ' : IsNormalThree (G₁ ⊔ G₂) Q :=
      ⟨hQK, fun x hx q hq => hQn x (hK₀H hx) q hq, hQc⟩
    rcases normalThree_le_factor hc hinf hcen₁ hQ' with hQG₁ | hQG₂
    · exfalso
      have hQbot := hgood₁.unique Q
        ⟨hQG₁, fun x hx q hq => hQn x (hG₁H hx) q hq, hQc⟩
      rw [hQbot, Subgroup.card_bot] at hQc
      omega
    · exact Subgroup.eq_of_le_of_card_ge hQG₂ (by rw [hc₂, hQc])
  refine ⟨G₂, G₂, Or.inr hG₂N, Or.inr hG₂N, ?_, hΞ⟩
  have hK₀core : G₁ ⊔ G₂ ≤ perfectCore H ⊔ (G₂ ⊔ G₂) := by
    rw [sup_idem]
    exact sup_le (hG₁core.trans le_sup_left) le_sup_right
  exact hH2.trans (sup_le (hK₀core.trans le_sup_left) le_sup_right)

theorem digest3_of_b56 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (hffJ : H = ffJ H)
    (hcases : B56Case1 H ∨ B56Case2 H ∨ B56Case3 H ∨ B56Case4 H ∨ B56Case5 H) :
    H ≤ perfectCore H ⊔ P ∨ ∃ Z₁ Z₂, Digest3 H P Z₁ Z₂ := by
  rcases hcases with h | h | h | h | h
  · exact Or.inl (digest3_case1 hP h)
  · exact Or.inr (digest3_case2 hP h)
  · exact Or.inr (digest3_case3 hP h)
  · exact Or.inr (digest3_case4 hP hffJ h)
  · exact Or.inr (digest3_case5 hP h)

end CFSG.Quasithin.H.B56N3
