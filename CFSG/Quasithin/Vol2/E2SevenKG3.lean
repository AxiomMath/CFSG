module

public import CFSG.Quasithin.Vol2.E2SevenPairN
public import CFSG.Holt.Bender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem eq_top_of_sylow_le {X : Type}
    [Group X] [Finite X] {n k : ℕ} (hn : 2 ≤ n) (hB : fusionBenderBorel X (2 ^ n) k)
    (hs : IsSimpleGroup X) (P : Sylow 2 X) {Y : Subgroup X} (hPY : (P : Subgroup X) ≤ Y)
    (hYN : ¬ Y ≤ Subgroup.normalizer ((P : Subgroup X) : Set X)) : Y = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSE, -, hsq, hcard, -⟩ := hB P
  set N := Subgroup.normalizer ((P : Subgroup X) : Set X) with hN
  have hdvd4 : 2 ^ 2 ∣ Nat.card (Subgroup.center ↥(P : Subgroup X)) := hcard ▸ pow_dvd_pow 2 hn
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd4
  set V := (W.map (Subgroup.center ↥(P : Subgroup X)).subtype).map (P : Subgroup X).subtype
    with hVdef
  have hV : Nat.card V = 4 := by
    rw [hVdef, Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.center _).subtype_injective, hW]
    norm_num
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
    rintro _ ⟨y, ⟨w, -, rfl⟩, rfl⟩
    have := hsq w w.2
    simpa using congrArg Subtype.val this
  have heven : Even (Nat.card X) := by
    have h1 : 2 ∣ Nat.card V := by rw [hV]; norm_num
    exact even_iff_two_dvd.mpr (h1.trans (Subgroup.card_subgroup_dvd_card V))
  have hO : ∀ R : Subgroup X, R.Normal → Odd (Nat.card R) → R = ⊥ := by
    intro R hR hodd
    rcases hs.eq_bot_or_eq_top_of_normal R with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨N₀, q, i, hBN⟩ := CFSG.Holt.exists_isBenderNormal_quotient hSE hO hV hV2
  have hcardSyl : Nat.card (Sylow 2 X) = Nat.card (P : Subgroup X) + 1 := by
    rw [Sylow.card_eq_card_quotient_normalizer P]
    exact hBN.card_eq_card_sylow_add_one P
  have hconj : ∀ g : X, ((g • P : Sylow 2 X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := fun g => by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hTI : ∀ y : X, y ∉ N → ∀ x ∈ (P : Subgroup X),
      x ∈ ((y • P : Sylow 2 X) : Subgroup X) → x = 1 := by
    intro y hy x hxP hxyP
    have hy' : y⁻¹ ∉ N := fun h => hy (by simpa using N.inv_mem h)
    have hodd := hSE.2.2 y⁻¹ hy'
    rw [inv_inv] at hodd
    have hle : (P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X) ≤
        N ⊓ N.map (MulAut.conj y).toMonoidHom := by
      refine inf_le_inf Subgroup.le_normalizer ?_
      rw [hconj, hN, Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.le_normalizer
    have h2 : IsPGroup 2 ↥((P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X)) :=
      P.isPGroup'.to_le inf_le_left
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    have hodd' := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    rw [hm] at hodd'
    have hm0 : m = 0 := by
      by_contra hm0
      exact (Nat.not_even_iff_odd.mpr hodd') ((Nat.even_pow.mpr ⟨even_two, hm0⟩))
    rw [hm0, pow_zero, Subgroup.card_eq_one] at hm
    have : x ∈ (P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X) := ⟨hxP, hxyP⟩
    rw [hm] at this
    exact (Subgroup.mem_bot).mp this
  obtain ⟨y, hyY, hyN⟩ : ∃ y ∈ Y, y ∉ N := by
    by_contra hall
    push Not at hall
    exact hYN hall
  set P₁ := y • P with hP₁
  have hP₁P : P₁ ≠ P := fun h => hyN (Sylow.smul_eq_iff_mem_normalizer.mp h)
  have hstab : MulAction.stabilizer ↥(P : Subgroup X) P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have hg' : (g : X) • P₁ = P₁ := hg
    have hgN : (g : X) ∈ Subgroup.normalizer ((P₁ : Subgroup X) : Set X) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hg'
    have hgP₁ : (g : X) ∈ (P₁ : Subgroup X) := by
      have h2 : IsPGroup 2 ↥(Subgroup.zpowers (g : X) ⊔ (P₁ : Subgroup X)) :=
        IsPGroup.to_sup_of_normal_right' (P.isPGroup'.to_le (Subgroup.zpowers_le.mpr g.2))
          P₁.isPGroup' (Subgroup.zpowers_le.mpr hgN)
      have := P₁.is_maximal' h2 le_sup_right
      rw [← this]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hTI y hyN g g.2 hgP₁))
  have horb : Set.ncard (MulAction.orbit ↥(P : Subgroup X) P₁) = Nat.card (P : Subgroup X) := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ P₁)]
    show (MulAction.stabilizer ↥(P : Subgroup X) P₁).index = _
    rw [hstab, Subgroup.index_bot]
  set sylY : Set (Sylow 2 X) := {Q | (Q : Subgroup X) ≤ Y} with hsyldef
  have hsmul_le : ∀ g ∈ Y, ∀ Q : Sylow 2 X, (Q : Subgroup X) ≤ Y →
      ((g • Q : Sylow 2 X) : Subgroup X) ≤ Y := by
    intro g hg Q hQ
    rw [Sylow.coe_subgroup_smul]
    change (Q : Subgroup X).map (MulAut.conj g).toMonoidHom ≤ Y
    rintro _ ⟨x, hx, rfl⟩
    exact Y.mul_mem (Y.mul_mem hg (hQ hx)) (Y.inv_mem hg)
  have hOsyl : MulAction.orbit ↥(P : Subgroup X) P₁ ⊆ sylY \ {P} := by
    rintro _ ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · have e : (g • P₁ : Sylow 2 X) = ((g : X) * y) • P := by
        rw [hP₁, mul_smul]
        rfl
      show ((g • P₁ : Sylow 2 X) : Subgroup X) ≤ Y
      rw [e]
      exact hsmul_le _ (Y.mul_mem (hPY g.2) hyY) P hPY
    · intro h
      apply hP₁P
      have h' : (g : X) • P₁ = P := h
      calc P₁ = (g : X)⁻¹ • ((g : X) • P₁) := by rw [inv_smul_smul]
        _ = (g : X)⁻¹ • P := by rw [h']
        _ = P := Sylow.smul_eq_iff_mem_normalizer.mpr
          (Subgroup.le_normalizer ((P : Subgroup X).inv_mem g.2))
  have hcardsyl : Nat.card (Sylow 2 X) ≤ Set.ncard sylY := by
    have h1 : Set.ncard (insert P (MulAction.orbit ↥(P : Subgroup X) P₁)) =
        Set.ncard (MulAction.orbit ↥(P : Subgroup X) P₁) + 1 :=
      Set.ncard_insert_of_notMem (fun h => (hOsyl h).2 rfl) (Set.toFinite _)
    have h2 : insert P (MulAction.orbit ↥(P : Subgroup X) P₁) ⊆ sylY :=
      Set.insert_subset hPY (hOsyl.trans Set.sdiff_subset)
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
    rw [h1, horb] at h3
    rw [hcardSyl]
    exact h3
  have hsylu : sylY = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; exact hcardsyl)
      (Set.toFinite _)
  have hcl : Subgroup.normalClosure ((P : Subgroup X) : Set X) ≤ Y := by
    refine (Subgroup.closure_le Y).mpr fun x hx => ?_
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have hQ : (c • P : Sylow 2 X) ∈ sylY := by rw [hsylu]; trivial
    apply hQ
    rw [hconj c]
    exact ⟨a, ha, rfl⟩
  have hP1 : (P : Subgroup X) ≠ ⊥ := by
    intro h0
    have h1 := Subgroup.card_le_card_group (Subgroup.center ↥(P : Subgroup X))
    rw [hcard, h0, Subgroup.card_bot] at h1
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ((P : Subgroup X) : Set X))
    with h | h
  · exfalso
    apply hP1
    exact le_bot_iff.mp (h ▸ Subgroup.le_normalClosure)
  · exact top_le_iff.mp (h ▸ hcl)

theorem kgBenderMax_holds :
    KGBenderMax := by
  intro G _ _ K S Y n hn2 hK hS hSY hYK
  obtain ⟨k, hB⟩ := exists_fusionBenderBorel_of_psl_or_sz hn2 hK
  have hs := isSimpleGroup_of_psl_or_sz hK
  by_cases hYN : Y ≤ Subgroup.normalizer (S : Set G)
  · exact Or.inl hYN
  right
  set P := toSylow2 hS
  have hPc : (P : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  have hPY : (P : Subgroup ↥K) ≤ Y.subgroupOf K := by
    rw [hPc]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hSY (Subgroup.mem_subgroupOf.mp hx))
  have hYN' : ¬ Y.subgroupOf K ≤ Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) := by
    intro hle
    apply hYN
    intro y hy
    have hyK := hYK hy
    have h1 := hle (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hyK⟩ : ↥K) ∈ Y.subgroupOf K)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro z
    constructor
    · intro hz
      have h2 := (h1 ⟨z, hS.1 hz⟩).mp (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h2
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hz
      have hzK : z ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hyK) (hS.1 hz)) hyK
        simpa [mul_assoc] using this
      have h2 := (h1 ⟨z, hzK⟩).mpr (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h2
      exact Subgroup.mem_subgroupOf.mp h2
  have htop := eq_top_of_sylow_le hn2 hB hs P hPY hYN'
  refine le_antisymm hYK fun x hx => ?_
  have : (⟨x, hx⟩ : ↥K) ∈ Y.subgroupOf K := by rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

end E2

end CFSG.Quasithin
