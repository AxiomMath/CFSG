module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLCenter
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLCyc
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Facts
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLInnerHom

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian evenRank)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem ffHypA5Sp6_holds : FFHypA5Sp6 := by
  intro G _ _ A a X hpt h6 hXq hN hW B hBC hBab hT₀ hBcard
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : IsL4L5Sp6 X := Or.inr (Or.inr h6)
  have hG : evenRank G = 3 := hpt.standing.evenRank_eq
  have hAab := hpt.mem_S.1.1
  have ha3 : a ^ 3 = 1 := hAab.2 a hpt.mem
  have ha1 : a ≠ 1 := hpt.ne_one
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBC.trans hN
  have hXa : ∀ y ∈ X, y * a = a * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXC hy)
  have hXm : StatedClassicalModel ↥X .PSp 3 2 1 := ffCenterSp6_holds G A a X hpt h6 hXq hN hW
  have hZ : Subgroup.center ↥X = ⊥ := center_eq_bot_of_sp6Model hXm
  obtain ⟨φ, hφ⟩ := exists_inner_hom hZ (exists_eq_conj_of_sp6Model hXm)
  have hrk : localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({a} : Set G)) :=
    ffLocalRankC_of_kE9 fFKE9_holds G A a X hpt hX hXq hN
  have h3 : localRank 3 G = 3 := hpt.standing.toTheoremFourHyp.localRank_three
  have hB27 : Nat.card B = 3 ^ 3 := by rw [hBcard, ← hrk, h3]
  have hcyc : ∀ P : Sylow 3 ↥(Subgroup.centralizer (X : Set G)),
      IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (X : Set G))) :=
    ffCentCyclic_of_kE9 fFKE9_holds G A a X hpt hX hXq hN
  obtain ⟨T₀, hT₀C, hT₀2, hT₀1, hBT₀⟩ := hT₀
  have hT₀N : T₀ ≤ Subgroup.normalizer (X : Set G) := hT₀C.trans hN
  have hcent : ∀ g : ↥(Subgroup.normalizer (X : Set G)), φ g = 1 →
      ∀ x ∈ X, (g : G) * x = x * (g : G) := by
    intro g hg x hx
    have h := hφ g x hx
    rw [hg] at h
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hconj : ∀ b : ↥(Subgroup.normalizer (X : Set G)), (b : G) ∈ B →
      ∀ t : ↥(Subgroup.normalizer (X : Set G)), (t : G) ∈ T₀ →
        ((b * t * b⁻¹ : ↥(Subgroup.normalizer (X : Set G))) : G) ∈ T₀ := by
    intro b hb t ht
    exact (Subgroup.mem_set_normalizer_iff.mp (hBT₀ hb) (t : G)).mp ht
  have hB3K : ∀ K : Subgroup G, ∀ g : ↥(B.subgroupOf K), g ^ 3 = 1 := by
    intro K g
    apply Subtype.ext
    apply Subtype.ext
    simpa using hBab.2 _ (Subgroup.mem_subgroupOf.mp g.2)
  set B' : Subgroup ↥(Subgroup.normalizer (X : Set G)) := B.subgroupOf _
  set T₀' : Subgroup ↥(Subgroup.normalizer (X : Set G)) := T₀.subgroupOf _
  set F : Subgroup ↥X := B'.map φ
  set T₁ : Subgroup ↥X := T₀'.map φ
  have hT₁ne : T₁ ≠ ⊥ := by
    intro h1
    have hT₀X : ∀ t ∈ T₀, ∀ x ∈ X, t * x = x * t := by
      intro t ht x hx
      have htN : t ∈ Subgroup.normalizer (X : Set G) := hT₀N ht
      have hmem : (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) ∈ T₀' :=
        Subgroup.mem_subgroupOf.mpr ht
      have hφt : φ ⟨t, htN⟩ = 1 := by
        have h' : φ ⟨t, htN⟩ ∈ T₁ := Subgroup.mem_map_of_mem φ hmem
        rw [h1, Subgroup.mem_bot] at h'
        exact h'
      exact hcent ⟨t, htN⟩ hφt x hx
    obtain ⟨E, hEab, hEcard⟩ := exists_e27_of_sp6Model hXm
    have hPab : IsElemAbelian 3 (E.map X.subtype) :=
      CFSG.Open.IsElemAbelian.map hEab X.subtype
    have hPcard : Nat.card (E.map X.subtype) = 27 := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact hEcard
    have hPX : E.map X.subtype ≤ X := Subgroup.map_subtype_le E
    have hQab : IsElemAbelian 3 (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha3
    have hQcard : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    have hcenX : ∀ x : G, x ∈ X → (∀ y ∈ X, y * x = x * y) → x = 1 := by
      intro x hx hxc
      have hz : (⟨x, hx⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hxc y.1 y.2)
      rw [hZ, Subgroup.mem_bot] at hz
      simpa using congrArg Subtype.val hz
    have hdisj : ∀ x ∈ E.map X.subtype, x ∈ Subgroup.zpowers a → x = 1 := by
      intro x hx hxa
      apply hcenX x (hPX hx)
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
      exact ((show Commute y a from hXa y hy).zpow_right k).eq
    have hcomm : ∀ x ∈ E.map X.subtype, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((show Commute x a from hXa x (hPX hx)).zpow_right k).eq
    have hPN : E.map X.subtype ≤ Subgroup.normalizer (T₀ : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer (T₀ : Set G)
        (Subgroup.mem_centralizer_iff.mpr fun t ht => hT₀X t ht x (hPX hx))
    have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (T₀ : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (T₀ : Set G)
        (Subgroup.mem_centralizer_iff.mpr fun t ht =>
          Subgroup.mem_centralizer_singleton_iff.mp (hT₀C ht)))
    obtain ⟨K, hKN, hKab, hKcard⟩ := exists_elemAbelian_card_mul
      (N := Subgroup.normalizer (T₀ : Set G)) hPab hQab hPN haN hcomm hdisj
    rw [hPcard, hQcard] at hKcard
    have hK := ff_card_le_of_normalizes hT₀1 hT₀2 hKab hKN
    rw [hG, hKcard] at hK
    norm_num at hK
  have hFne : F ≠ ⊥ := by
    intro h1
    have hBX : ∀ b ∈ B, ∀ x ∈ X, b * x = x * b := by
      intro b hb x hx
      have hbN : b ∈ Subgroup.normalizer (X : Set G) := hBN hb
      have hmem : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set G))) ∈ B' :=
        Subgroup.mem_subgroupOf.mpr hb
      have h' : φ ⟨b, hbN⟩ ∈ F := Subgroup.mem_map_of_mem φ hmem
      rw [h1, Subgroup.mem_bot] at h'
      exact hcent ⟨b, hbN⟩ h' x hx
    have hBC' : B ≤ Subgroup.centralizer (X : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => (hBX b hb x hx).symm
    have hB1 : IsPGroup 3 (B.subgroupOf (Subgroup.centralizer (X : Set G))) :=
      fun g => ⟨1, by simpa using hB3K _ g⟩
    obtain ⟨Q, hQ⟩ := hB1.exists_le_sylow
    haveI := hcyc Q
    haveI : IsCyclic ↥(B.subgroupOf (Subgroup.centralizer (X : Set G))) :=
      Subgroup.isCyclic_of_le hQ
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
      (α := ↥(B.subgroupOf (Subgroup.centralizer (X : Set G))))
    have hcard : Nat.card ↥(B.subgroupOf (Subgroup.centralizer (X : Set G))) = 3 ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC').toEquiv, hB27]
    rw [hcard] at hg
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hB3K _ g)
    rw [hg] at hdvd
    norm_num at hdvd
  have hF3 : IsPGroup 3 F :=
    (show IsPGroup 3 (B.subgroupOf (Subgroup.normalizer (X : Set G))) from
      fun g => ⟨1, by simpa using hB3K _ g⟩).map φ
  have hT₀'2 : IsPGroup 2 T₀' :=
    hT₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀N).symm
  have hT₁2 : IsPGroup 2 T₁ := hT₀'2.map φ
  have hnormT : ∀ b ∈ B', ∀ h ∈ T₁, φ b * h * (φ b)⁻¹ ∈ T₁ := by
    rintro b hb _ ⟨t, ht, rfl⟩
    have hbt : b * t * b⁻¹ ∈ T₀' := by
      apply Subgroup.mem_subgroupOf.mpr
      exact hconj b (Subgroup.mem_subgroupOf.mp hb) t (Subgroup.mem_subgroupOf.mp ht)
    have h2 := Subgroup.mem_map_of_mem φ hbt
    rw [map_mul, map_mul, map_inv] at h2
    exact h2
  have hFT : F ≤ Subgroup.normalizer (T₁ : Set ↥X) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    refine ⟨fun hh => hnormT b hb h hh, fun hh => ?_⟩
    have h' := hnormT b⁻¹ (B'.inv_mem hb) (φ b * h * (φ b)⁻¹) hh
    rw [map_inv] at h'
    simpa [mul_assoc] using h'
  obtain ⟨T, hT2, hFTn, hnot⟩ := exists_moved_two_of_sp6Model hXm hF3 hFne hT₁2 hT₁ne hFT
  have hTG : ∀ b ∈ B, ∀ h ∈ T.map X.subtype, b * h * b⁻¹ ∈ T.map X.subtype := by
    intro b hb h hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
    have hbN : b ∈ Subgroup.normalizer (X : Set G) := hBN hb
    have hbF : φ ⟨b, hbN⟩ ∈ F :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hb)
    have hnt : φ ⟨b, hbN⟩ * t * (φ ⟨b, hbN⟩)⁻¹ ∈ T :=
      (Subgroup.mem_set_normalizer_iff.mp (hFTn hbF) t).mp ht
    exact Subgroup.mem_map.mpr ⟨_, hnt, (hφ ⟨b, hbN⟩ (t : G) t.2).symm⟩
  have hBnorm : B ≤ Subgroup.normalizer ((T.map X.subtype : Subgroup G) : Set G) := by
    intro b hb
    refine Subgroup.mem_set_normalizer_iff.mpr fun h => ⟨fun hh => hTG b hb h hh, fun hh => ?_⟩
    have h' := hTG b⁻¹ (B.inv_mem hb) (b * h * b⁻¹) hh
    simpa [mul_assoc] using h'
  have hBnc : ¬ B ≤ Subgroup.centralizer ((T.map X.subtype : Subgroup G) : Set G) := by
    intro hle
    obtain ⟨f, hfF, hfT⟩ : ∃ f ∈ F, f ∉ Subgroup.centralizer (T : Set ↥X) := by
      by_contra hc
      push Not at hc
      exact hnot fun f hf => hc f hf
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hfF
    obtain ⟨t, ht, htf⟩ : ∃ t ∈ T, t * φ b ≠ φ b * t := by
      by_contra hc
      push Not at hc
      exact hfT (Subgroup.mem_centralizer_iff.mpr fun t ht => hc t ht)
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have htT : (t : G) ∈ T.map X.subtype := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have hc1 : (t : G) * (b : G) = (b : G) * (t : G) :=
      Subgroup.mem_centralizer_iff.mp (hle hbB) _ htT
    have hbt : (b : G) * (t : G) * (b : G)⁻¹ = (t : G) := by
      rw [← hc1]
      simp
    have hf3 : (φ b : G) * (t : G) * (φ b : G)⁻¹ = (t : G) := by
      rw [← hφ b (t : G) t.2]
      exact hbt
    apply htf
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hf3).symm
  exact ⟨T.map X.subtype, (Subgroup.map_subtype_le T).trans hXC, hT2.map X.subtype, hBnorm,
    hBnc⟩

end CFSG.RankThree.PartTwo.Sec21
