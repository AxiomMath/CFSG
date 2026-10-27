module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHMain
public import CFSG.RankThree.PartOne.S11c.HNCoverAbstract
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem lemmaH_holds : LemmaH := by
  intro G _ _ K T N x hK60 hKs hT3 hKT hNT hKN hNnorm hxK hx3 hfpf
  haveI := hKs
  set W : Subgroup G := Nor T ⊓ Nor N with hW
  have hKW : K ≤ W := le_inf hKT hKN
  have hTNor : T ≤ Nor N := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hNnorm.conj_mem ⟨n, hNT hn⟩ hn ⟨t, ht⟩
    · intro hn
      have := hNnorm.conj_mem ⟨t * n * t⁻¹, hNT hn⟩ hn ⟨t⁻¹, inv_mem ht⟩
      have h2 : t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n := by group
      rw [← h2]
      exact this
  have hTW : T ≤ W := le_inf Subgroup.le_normalizer hTNor
  have hNW : N ≤ W := hNT.trans hTW
  have hN1 : (N.subgroupOf W).Normal := by
    refine ⟨fun n hn w => ?_⟩
    have hw : (w : G) ∈ Nor N := w.2.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 hw n).1 hn
  have hT1 : (T.subgroupOf W).Normal := by
    refine ⟨fun n hn w => ?_⟩
    have hw : (w : G) ∈ Nor T := w.2.1
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 hw n).1 hn
  let π : ↥W →* ↥W ⧸ N.subgroupOf W := QuotientGroup.mk' (N.subgroupOf W)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : ∀ w : ↥W, π w = 1 ↔ (w : G) ∈ N := fun w => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set Q : Subgroup (↥W ⧸ N.subgroupOf W) := (T.subgroupOf W).map π with hQdef
  haveI hQn : Q.Normal := Subgroup.Normal.map hT1 π hπ
  have hker : (π.domRestrict (T.subgroupOf W)).ker =
      (N.subgroupOf W).subgroupOf (T.subgroupOf W) := by
    ext t
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, hπker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
  have hN'T' : N.subgroupOf W ≤ T.subgroupOf W := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact hNT hw
  have hcardT' : Nat.card (T.subgroupOf W) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv
  have hcardN' : Nat.card ((N.subgroupOf W).subgroupOf (T.subgroupOf W)) = Nat.card N := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'T').toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  have hcardTNQ : Nat.card T = Nat.card N * Nat.card Q := by
    have h1 := Subgroup.card_mul_index (π.domRestrict (T.subgroupOf W)).ker
    rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hker, hcardN', hcardT'] at h1
    exact h1.symm
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h => hT3 (by rw [hcardTNQ]; exact Dvd.dvd.mul_left h _)
  let x' : ↥K := ⟨x, hxK⟩
  let φ : ↥K →* MulAut ↥Q := MulAut.conjNormal.comp (π.comp (Subgroup.inclusion hKW))
  have hsm : ∀ (j : ↥K) (e : ↥Q), ((φ j e : ↥Q) : ↥W ⧸ N.subgroupOf W) =
      π (Subgroup.inclusion hKW j) * e * (π (Subgroup.inclusion hKW j))⁻¹ := by
    intro j e
    have h0 : (φ j e : ↥Q) = MulAut.conjNormal (π (Subgroup.inclusion hKW j)) e := rfl
    rw [h0, MulAut.conjNormal_apply]
  have hxfpf : ∀ v : ↥Q, φ x' v = v → v = 1 := by
    intro v hv
    have he' := congrArg Subtype.val hv
    rw [hsm] at he'
    obtain ⟨w, hwT, hwe⟩ := Subgroup.mem_map.1 v.2
    have h3 : π w = π (Subgroup.inclusion hKW x' * w * (Subgroup.inclusion hKW x')⁻¹) := by
      rw [map_mul, map_mul, map_inv, hwe]
      exact he'.symm
    have hn := QuotientGroup.eq.1 h3
    rw [Subgroup.mem_subgroupOf] at hn hwT
    have hwN : (w : G) ∈ N := by
      refine hfpf (w : G) hwT ⟨(w : G)⁻¹ * (x * (w : G) * x⁻¹), ?_, by group⟩
      simpa using hn
    apply Subtype.ext
    rw [← hwe]
    exact (hπker w).2 hwN
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [x'] using (hx3 ▸ pow_orderOf_eq_one x)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx'1 : x' ≠ 1 := by
    intro h
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx3
    omega
  have hx'o : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have h9 : ¬ 3 ^ 2 ∣ Nat.card ↥K := by rw [hK60]; norm_num
  have hFpf : LemmaH.Fpf φ := by
    intro y hy3 hy1 u hu
    obtain ⟨g, k, hg⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime h9 hx'o
      (orderOf_eq_prime hy3 hy1)
    have hfixk : φ (x' ^ k) (φ g u) = φ g u := by
      rw [← hg]
      calc φ (g * y * g⁻¹) (φ g u) = φ g (φ y (φ (g⁻¹ * g) u)) := by
            simp only [map_mul, MulAut.mul_apply]
        _ = φ g u := by simp [hu]
    have hk : x' ^ k = 1 ∨ x' ^ k = x' ∨ x' ^ k = x' ^ 2 := by
      have hkk : x' ^ k = x' ^ (k % 3) := by
        conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hx'3, one_pow, one_mul]
      have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hm : k % 3
      · left; rw [hkk]; simp
      · right; left; rw [hkk]; simp
      · right; right; rw [hkk]
    have hu' : φ g u = 1 := by
      apply hxfpf
      rcases hk with h | h | h
      · exfalso
        apply hy1
        have : g * y * g⁻¹ = 1 := hg.trans h
        simpa [mul_inv_eq_one] using this
      · rw [h] at hfixk; exact hfixk
      · rw [h] at hfixk
        have hxx : x' = x' ^ 2 * x' ^ 2 := by
          calc x' = x' ^ 3 * x' := by rw [hx'3, one_mul]
            _ = x' ^ 2 * x' ^ 2 := by group
        rw [hxx, map_mul, MulAut.mul_apply, hfixk, hfixk]
    have : u = φ g⁻¹ (φ g u) := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this, hu', map_one]
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := ↥K) hK60
  obtain ⟨hcomm, hsq, r, hr⟩ := LemmaH.higman_abstract e φ hQ3 hFpf
  have hmem : ∀ (u : G) (hu : u ∈ T), ∃ q : ↥Q,
      (q : ↥W ⧸ N.subgroupOf W) = π ⟨u, hTW hu⟩ := by
    intro u hu
    exact ⟨⟨_, Subgroup.mem_map_of_mem _ (show (⟨u, hTW hu⟩ : ↥W) ∈ T.subgroupOf W from hu)⟩, rfl⟩
  refine ⟨?_, ?_, r, ?_⟩
  · intro u hu v hv
    obtain ⟨qu, hqu⟩ := hmem u hu
    obtain ⟨qv, hqv⟩ := hmem v hv
    have hc := congrArg Subtype.val (hcomm qu qv)
    simp only [Subgroup.coe_mul] at hc
    rw [hqu, hqv] at hc
    have h1 : π (⟨u, hTW hu⟩ * ⟨v, hTW hv⟩ * ⟨u, hTW hu⟩⁻¹ * ⟨v, hTW hv⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    exact (hπker _).1 h1
  · intro u hu
    obtain ⟨qu, hqu⟩ := hmem u hu
    have hc := congrArg Subtype.val (hsq qu)
    simp only [Subgroup.coe_mul] at hc
    rw [hqu] at hc
    have h1 : π (⟨u, hTW hu⟩ * ⟨u, hTW hu⟩) = 1 := by
      rw [map_mul]; exact hc
    have := (hπker _).1 h1
    rw [pow_two]
    exact this
  · rw [hcardTNQ, hr]

end CFSG.RankThree.PartTwo.Sec21.FF84
