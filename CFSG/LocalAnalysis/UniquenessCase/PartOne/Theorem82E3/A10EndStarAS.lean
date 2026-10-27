module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarOne

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Loc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

@[expose] def KFactE27SignalizerAlmostSimple : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ L : Subgroup X, CFSG.IsComponent L → Subgroup.centralizer (L : Set X) = ⊥ →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W = ⊥

namespace A10Gen

variable {X : Type} [Group X] [Finite X]

private lemma eq_of_ne_one_of_card_le_two {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ≤ 2) {x y : H} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  by_contra hxy
  have h1 : (1 : H) ∉ ({x, y} : Finset H) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hx h'.symm, fun h' => hy h'.symm⟩
  have h2 : x ∉ ({y} : Finset H) := by
    simp only [Finset.mem_singleton]
    exact fun h' => hxy h'
  have hc : ({1, x, y} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hle := Finset.card_le_univ ({1, x, y} : Finset H)
  rw [hc, Fintype.card_eq_nat_card] at hle
  omega

private lemma eq_or_eq_inv_of_mem_zpowers_of_orderOf_three {z y : X} (hz : orderOf z = 3)
    (hy : y ∈ Subgroup.zpowers z) (hy1 : y ≠ 1) : y = z ∨ y = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]; exact pow_orderOf_eq_one z
  have hz2 : z ^ 2 = z⁻¹ := by
    have h : z * z ^ 2 = 1 := by rw [← pow_succ', hz3]
    exact eq_inv_of_mul_eq_one_right h
  have hmod : z ^ (k % (3 : ℤ)) = z ^ k := by
    have h3 : (orderOf z : ℤ) = 3 := by rw [hz]; norm_num
    rw [← h3]
    exact zpow_mod_orderOf z k
  rw [← hmod] at hy1 ⊢
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have h1 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h2 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hcases with h | h | h
  · rw [h] at hy1; simp at hy1
  · left; rw [h]; simp
  · right; rw [h]; simpa using hz2

private lemma subgroupOf_inf_centralizer_eq_center (P : Subgroup X) :
    (P ⊓ Subgroup.centralizer (P : Set X)).subgroupOf P = Subgroup.center ↥P := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hc⟩ g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (g : X) g.2)
  · intro h
    refine ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (h ⟨g, hg⟩)

private lemma card_inf_centralizer_of_zwr {P : Subgroup X}
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set X)) = 3 := by
  obtain ⟨e⟩ := hPZ
  obtain ⟨-, -, hcent⟩ := UC22.InS3.UC326.zwr_card_center (n := 1) le_rfl e
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : P ⊓ Subgroup.centralizer (P : Set X) ≤ P)).toEquiv,
    subgroupOf_inf_centralizer_eq_center P]
  simpa using hcent

private lemma normal_of_layer_eq {L : Subgroup X} (hlay : CFSG.layer X = L) : L.Normal := by
  haveI hchar : L.Characteristic := hlay ▸ (CFSG.LocalCores.layer_characteristic (G := X))
  exact Subgroup.normal_of_characteristic L

private lemma inf_centralizer_normal_of_layer {L : Subgroup X} (hlay : CFSG.layer X = L) :
    (L ⊓ Subgroup.centralizer (L : Set X)).Normal := by
  haveI : L.Normal := normal_of_layer_eq hlay
  infer_instance

private lemma isPGroup_inf_centralizer {L : Subgroup X} (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hL : CFSG.IsComponent L) :
    IsPGroup 3 ↥(L ⊓ Subgroup.centralizer (L : Set X)) := by
  have hc : IsPGroup 3 ↥(Subgroup.center ↥L) :=
    UC22.InS3.UC326.comp_center_isPGroup h3' ((CFSG.isComponent_iff_open L).mp hL)
  rw [← subgroupOf_inf_centralizer_eq_center L] at hc
  exact hc.of_equiv (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : L ⊓ Subgroup.centralizer (L : Set X) ≤ L))

private lemma le_of_isPGroup_normal_of_isSylow {N P : Subgroup X} (hNn : N.Normal)
    (hN3 : IsPGroup 3 ↥N) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) : N ≤ P := by
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ N) N :=
    hP.inf_of_le_normalizer le_top (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hNn).symm)
  have hEq : N = P ⊓ N := hSyl.eq_of_le inf_le_right le_rfl hN3
  rw [hEq]
  exact inf_le_left

private lemma inf_centralizer_le_of_isComponent {P L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hlay : CFSG.layer X = L) :
    P ⊓ Subgroup.centralizer (P : Set X) ≤ L := by
  obtain ⟨e⟩ := hPZ
  obtain ⟨x, hxPL, hxc⟩ := exists_mem_inf_not_mem_centralizer_of_isComponent hP h3' hL
  have hx1 : x ≠ 1 := by rintro rfl; exact hxc (Subgroup.one_mem _)
  have hNnorm : ((P ⊓ L).subgroupOf P).Normal := by
    have h : (P ⊓ L).subgroupOf P = L.subgroupOf P := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    rw [h]
    exact (normal_of_layer_eq hlay).subgroupOf P
  have hNne : (P ⊓ L).subgroupOf P ≠ ⊥ := by
    intro hbot
    have hmem : (⟨x, hxPL.1⟩ : ↥P) ∈ (P ⊓ L).subgroupOf P := hxPL
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  intro z hz
  obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P :=
    Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (y : X) y.2)
  have hz3 : (⟨z, hzP⟩ : ↥P) ^ 3 = 1 := by
    obtain ⟨-, -, hcent⟩ := UC22.InS3.UC326.zwr_card_center (n := 1) le_rfl e
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥P) hzcenter
    rw [hcent] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hmem := UC22.InS3.UC326.zwr_normal_contains_omega_center (n := 1) le_rfl e
    hNnorm hNne ⟨z, hzP⟩ hzcenter hz3
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2

private lemma inf_centralizer_le_of_eq_jOf {P A : Subgroup X}
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (hA : A = UC22.InS3.UC326.jOf P) (hAcard : Nat.card A = 27) :
    P ⊓ Subgroup.centralizer (P : Set X) ≤ A := by
  obtain ⟨e⟩ := hPZ
  have hAle : A ≤ P := hA ▸ Subgroup.map_subtype_le _
  have hAnorm : (A.subgroupOf P).Normal := by
    haveI hchar : (A.subgroupOf P).Characteristic := by
      have h : A.subgroupOf P = CFSG.elemThompson ↥P 3 := by
        rw [hA, UC22.InS3.UC326.jOf]
        exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
      rw [h]
      exact CFSG.Quasithin.BlueprintB2.elemThompson_characteristic ↥P 3
    exact Subgroup.normal_of_characteristic _
  have hAne : A.subgroupOf P ≠ ⊥ := by
    intro hbot
    have hc : Nat.card ↥(A.subgroupOf P) = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hAcard]
    rw [hbot, Subgroup.card_bot] at hc
    omega
  intro z hz
  obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P :=
    Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (y : X) y.2)
  have hz3 : (⟨z, hzP⟩ : ↥P) ^ 3 = 1 := by
    obtain ⟨-, -, hcent⟩ := UC22.InS3.UC326.zwr_card_center (n := 1) le_rfl e
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥P) hzcenter
    rw [hcent] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  exact Subgroup.mem_subgroupOf.mp (UC22.InS3.UC326.zwr_normal_contains_omega_center (n := 1)
    le_rfl e hAnorm hAne ⟨z, hzP⟩ hzcenter hz3)

private lemma conj_eq_or_eq_inv_of_mem_normal {Z : Subgroup X} (hZn : Z.Normal)
    (hZcard : Nat.card ↥Z = 3) {z : X} (hz : z ∈ Z) (hz1 : z ≠ 1) (g : X) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z⁻¹ := by
  have hzord : orderOf z = 3 := by
    have h : orderOf z ∣ Nat.card ↥Z := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzp : Subgroup.zpowers z = Z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    rw [hZcard, Nat.card_zpowers, hzord]
  have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    rw [hzp]
    exact hZn.conj_mem z hz g
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have hh := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using hh
  exact eq_or_eq_inv_of_mem_zpowers_of_orderOf_three hzord hmem hne

private lemma centralizer_singleton_normal {Z : Subgroup X} (hZn : Z.Normal)
    (hZcard : Nat.card ↥Z = 3) {z : X} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    (Subgroup.centralizer ({z} : Set X)).Normal := by
  refine ⟨fun y hy g => ?_⟩
  set w : X := g⁻¹ * z * g with hwdef
  have hwz : z = g * w * g⁻¹ := by rw [hwdef]; simp [mul_assoc]
  have hconj : w = z ∨ w = z⁻¹ := by
    rw [hwdef]
    simpa using conj_eq_or_eq_inv_of_mem_normal hZn hZcard hz hz1 g⁻¹
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  have hy' : y * w = w * y := by
    rcases hconj with h | h
    · rw [h]; exact hy
    · rw [h]
      have hyc : Commute y z := hy
      exact hyc.inv_right
  rw [hwz]
  calc (g * y * g⁻¹) * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by simp [mul_assoc]
    _ = g * (w * y) * g⁻¹ := by rw [hy']
    _ = (g * w * g⁻¹) * (g * y * g⁻¹) := by simp [mul_assoc]

private lemma inf_centralizer_eq_of_ne_bot {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hL : CFSG.IsComponent L) (hlay : CFSG.layer X = L)
    (hcent : P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X))
    (hZ : L ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥) :
    L ⊓ Subgroup.centralizer (L : Set X) = P ⊓ Subgroup.centralizer (P : Set X) := by
  have hZLn : (L ⊓ Subgroup.centralizer (L : Set X)).Normal :=
    inf_centralizer_normal_of_layer hlay
  have hZLleP : L ⊓ Subgroup.centralizer (L : Set X) ≤ P :=
    le_of_isPGroup_normal_of_isSylow hZLn (isPGroup_inf_centralizer h3' hL) hX.sylow
  have hZLleZP : L ⊓ Subgroup.centralizer (L : Set X) ≤
      P ⊓ Subgroup.centralizer (P : Set X) := by
    refine le_inf hZLleP ?_
    exact ((le_inf hZLleP inf_le_right :
      L ⊓ Subgroup.centralizer (L : Set X) ≤ P ⊓ Subgroup.centralizer (L : Set X))).trans hcent
  have hZPcard : Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set X)) = 3 :=
    card_inf_centralizer_of_zwr hPZ
  have hZLne : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) ≠ 1 := by
    intro h
    apply hZ
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    haveI : Subsingleton ↥(L ⊓ Subgroup.centralizer (L : Set X)) :=
      (Nat.card_eq_one_iff_unique.mp h).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥(L ⊓ _)) 1)
  have hZLcard : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = 3 := by
    have hdvd : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) ∣
        Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set X)) := Subgroup.card_dvd_of_le hZLleZP
    rw [hZPcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hZLne
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hZLleZP (by rw [hZPcard, hZLcard])

private lemma exists_mem_inf_centralizer_of_ne_bot {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hL : CFSG.IsComponent L) (hlay : CFSG.layer X = L)
    (hcent : P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X))
    (hZ : L ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥) :
    ∃ z ∈ L ⊓ Subgroup.centralizer (L : Set X), z ≠ 1 ∧ z ∈ A := by
  have hZLeq := inf_centralizer_eq_of_ne_bot hX hPZ h3' hL hlay hcent hZ
  have hZPleA : P ⊓ Subgroup.centralizer (P : Set X) ≤ A :=
    inf_centralizer_le_of_eq_jOf hPZ hX.jA hX.card
  obtain ⟨z, hzZL, hz1⟩ : ∃ z ∈ L ⊓ Subgroup.centralizer (L : Set X), z ≠ 1 := by
    by_contra h
    push Not at h
    exact hZ (Subgroup.eq_bot_iff_forall _ |>.mpr h)
  exact ⟨z, hzZL, hz1, hZPleA (hZLeq ▸ hzZL)⟩

private lemma relPPrimeCore_centralizer_singleton_eq_bot {z : X}
    (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hYn : (Subgroup.centralizer ({z} : Set X)).Normal) :
    CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  have hreln : (CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({z} : Set X))).Normal := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three (Subgroup.centralizer ({z} : Set X))]
    exact ConjAct.normal_of_characteristic_of_normal
      (H := Subgroup.centralizer ({z} : Set X))
      (K := CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({z} : Set X)))
  have hrelcop : Nat.Coprime 3 (Nat.card ↥(CFSG.Open.relPPrimeCore 3
      (Subgroup.centralizer ({z} : Set X)))) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three (Subgroup.centralizer ({z} : Set X))
  exact (CFSG.pPrimeCore_eq_bot_iff.mp h3') _ hreln hrelcop

private lemma inf_centralizer_eq_bot_of_balance {A W : Subgroup X} {z : X}
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    (hzA : z ∈ A) (hz1 : z ≠ 1) (hAreY : A ≤ Subgroup.centralizer ({z} : Set X))
    (hW : A ≤ Subgroup.normalizer (W : Set X)) (hcop : Nat.Coprime (Nat.card W) 3)
    (hcore : CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({z} : Set X)) = ⊥) :
    W ⊓ Subgroup.centralizer ({z} : Set X) = ⊥ := by
  have h := hbal z hzA hz1 (W ⊓ Subgroup.centralizer ({z} : Set X)) inf_le_right
    ((le_inf hW (hAreY.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop.symm).symm
  have h' : W ⊓ Subgroup.centralizer ({z} : Set X) ≤ ⊥ := by rwa [hcore] at h
  exact le_bot_iff.mp h'

private lemma eq_of_conj_eq_of_inf_centralizer_eq_bot {W : Subgroup X} {z : X}
    (hWY : W ⊓ Subgroup.centralizer ({z} : Set X) = ⊥)
    {w₁ w₂ : ↥W} (h : (w₁ : X) * z * (w₁ : X)⁻¹ = (w₂ : X) * z * (w₂ : X)⁻¹) : w₁ = w₂ := by
  have hmemC : (w₂ : X)⁻¹ * (w₁ : X) ∈ Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((w₂ : X)⁻¹ * (w₁ : X)) * z =
        (w₂ : X)⁻¹ * ((w₁ : X) * z * (w₁ : X)⁻¹) * (w₁ : X) * (w₂ : X)⁻¹ * (w₂ : X) := by
          simp [mul_assoc]
      _ = (w₂ : X)⁻¹ * ((w₂ : X) * z * (w₂ : X)⁻¹) * (w₁ : X) * (w₂ : X)⁻¹ * (w₂ : X) := by
          rw [h]
      _ = z * ((w₂ : X)⁻¹ * (w₁ : X)) := by simp [mul_assoc]
  have hmemW : (w₂ : X)⁻¹ * (w₁ : X) ∈ W := W.mul_mem (W.inv_mem w₂.2) w₁.2
  have hmem := Subgroup.mem_inf.mpr ⟨hmemW, hmemC⟩
  have hbot : (w₂ : X)⁻¹ * (w₁ : X) ∈ (⊥ : Subgroup X) := by rwa [hWY] at hmem
  rw [Subgroup.mem_bot] at hbot
  refine Subtype.ext ?_
  calc (w₁ : X) = (w₂ : X) * ((w₂ : X)⁻¹ * (w₁ : X)) := by simp [mul_assoc]
    _ = (w₂ : X) := by rw [hbot]; simp

private lemma card_le_two_of_inf_centralizer_eq_bot {W : Subgroup X} {z : X}
    (hWY : W ⊓ Subgroup.centralizer ({z} : Set X) = ⊥)
    (hconj : ∀ w : ↥W, (w : X) * z * (w : X)⁻¹ = z ∨ (w : X) * z * (w : X)⁻¹ = z⁻¹) :
    Nat.card ↥W ≤ 2 := by
  classical
  have hinj : Function.Injective
      (fun w : ↥W => if (w : X) * z * (w : X)⁻¹ = z then (0 : Fin 2) else 1) := by
    intro w₁ w₂ heq
    have heq' : (if (w₁ : X) * z * (w₁ : X)⁻¹ = z then (0 : Fin 2) else 1) =
        (if (w₂ : X) * z * (w₂ : X)⁻¹ = z then (0 : Fin 2) else 1) := heq
    apply eq_of_conj_eq_of_inf_centralizer_eq_bot hWY
    by_cases h1 : (w₁ : X) * z * (w₁ : X)⁻¹ = z
    · have h2 : (w₂ : X) * z * (w₂ : X)⁻¹ = z := by
        by_contra h2
        rw [if_pos h1, if_neg h2] at heq'
        exact absurd heq' (by decide)
      rw [h1, h2]
    · have h2 : (w₂ : X) * z * (w₂ : X)⁻¹ ≠ z := by
        intro h2
        rw [if_neg h1, if_pos h2] at heq'
        exact absurd heq' (by decide)
      rcases hconj w₁ with h1' | h1' <;> rcases hconj w₂ with h2' | h2'
      · exact absurd h1' h1
      · exact absurd h1' h1
      · exact absurd h2' h2
      · rw [h1', h2']
  have h := Nat.card_le_card_of_injective _ hinj
  simpa using h

private lemma eq_bot_of_card_le_two {W : Subgroup X} {z : X} (hWcard : Nat.card ↥W ≤ 2)
    (hWY : W ⊓ Subgroup.centralizer ({z} : Set X) = ⊥)
    (hzN : z ∈ Subgroup.normalizer (W : Set X)) : W = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  by_contra hw1
  have hzw : z * w * z⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hzN w).mp hw
  have hzw1 : z * w * z⁻¹ ≠ 1 := by
    intro h
    apply hw1
    have hh := congrArg (fun t => z⁻¹ * t * z) h
    simpa [mul_assoc] using hh
  have heq : z * w * z⁻¹ = w := by
    have h := eq_of_ne_one_of_card_le_two hWcard
      (x := (⟨z * w * z⁻¹, hzw⟩ : ↥W)) (y := ⟨w, hw⟩)
      (fun h' => hzw1 (congrArg Subtype.val h'))
      (fun h' => hw1 (congrArg Subtype.val h'))
    exact congrArg Subtype.val h
  have hcomm : w * z = z * w := by
    have h := congrArg (fun t => t * z) heq
    have h' : z * w = w * z := by simpa [mul_assoc] using h
    exact h'.symm
  have hwY : w ∈ Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hmem : w ∈ W ⊓ Subgroup.centralizer ({z} : Set X) := ⟨hw, hwY⟩
  rw [hWY, Subgroup.mem_bot] at hmem
  exact hw1 hmem

theorem eq_bot_of_inf_centralizer_ne_bot {P A L : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A) (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    (hL : CFSG.IsComponent L) (hlay : CFSG.layer X = L)
    (hcent : P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X))
    (hZ : L ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥)
    {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) : W = ⊥ := by
  obtain ⟨z, hzZL, hz1, hzA⟩ :=
    exists_mem_inf_centralizer_of_ne_bot hX hPZ h3' hL hlay hcent hZ
  have hZLn : (L ⊓ Subgroup.centralizer (L : Set X)).Normal :=
    inf_centralizer_normal_of_layer hlay
  have hZLcard : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = 3 := by
    rw [inf_centralizer_eq_of_ne_bot hX hPZ h3' hL hlay hcent hZ]
    exact card_inf_centralizer_of_zwr hPZ
  have hYnorm : (Subgroup.centralizer ({z} : Set X)).Normal :=
    centralizer_singleton_normal hZLn hZLcard hzZL hz1
  have hAreY : A ≤ Subgroup.centralizer ({z} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hX.elem.1.is_comm.comm ⟨a, ha⟩ ⟨z, hzA⟩)
  have hWY := inf_centralizer_eq_bot_of_balance hbal hzA hz1 hAreY hW hcop
    (relPPrimeCore_centralizer_singleton_eq_bot h3' hYnorm)
  refine eq_bot_of_card_le_two
    (card_le_two_of_inf_centralizer_eq_bot hWY ?_) hWY (hW hzA)
  intro w
  exact conj_eq_or_eq_inv_of_mem_normal hZLn hZLcard hzZL hz1 (w : X)

theorem centralizer_eq_bot_of_inf_centralizer_eq_bot {P L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L) (hlay : CFSG.layer X = L)
    (hcent : P ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (P : Set X))
    (hZ : L ⊓ Subgroup.centralizer (L : Set X) = ⊥) :
    Subgroup.centralizer (L : Set X) = ⊥ := by
  have hZPleL : P ⊓ Subgroup.centralizer (P : Set X) ≤ L :=
    inf_centralizer_le_of_isComponent hP hPZ h3' hL hlay
  have hPCL : P ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ L := hZPleL ⟨hxP, hcent hx⟩
    have hxZL : x ∈ L ⊓ Subgroup.centralizer (L : Set X) := ⟨hxL, hxC⟩
    rw [hZ, Subgroup.mem_bot] at hxZL
    exact hxZL
  have hCn : (Subgroup.centralizer (L : Set X)).Normal := by
    haveI : L.Normal := normal_of_layer_eq hlay
    exact Subgroup.normal_centralizer
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ Subgroup.centralizer (L : Set X))
      (Subgroup.centralizer (L : Set X)) :=
    hP.inf_of_le_normalizer le_top (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hCn).symm)
  have hcard := CFSG.ABGLocalTools.IsSylowOf.card_eq hSyl
  rw [hPCL, Subgroup.card_bot] at hcard
  have hk : (Nat.card ↥(Subgroup.centralizer (L : Set X))).factorization 3 = 0 := by
    rcases Nat.pow_eq_one.mp hcard.symm with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer (L : Set X))) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    have hpos : 0 < (Nat.card ↥(Subgroup.centralizer (L : Set X))).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos.ne') hdvd
    omega
  exact (CFSG.pPrimeCore_eq_bot_iff.mp h3') _ hCn hcop

end A10Gen

theorem kFactE27SignalizerOne_of_almostSimple (h : KFactE27SignalizerAlmostSimple) :
    KFactE27SignalizerOne := by
  intro X _ _ P A hK hX hPZ h3' hbal L hL hlay hcent W hW hcop
  by_cases hZ : L ⊓ Subgroup.centralizer (L : Set X) = ⊥
  · have hC : Subgroup.centralizer (L : Set X) = ⊥ :=
      A10Gen.centralizer_eq_bot_of_inf_centralizer_eq_bot hX.sylow hPZ h3' hL hlay hcent hZ
    rw [h X P A hK hX hPZ h3' hbal L hL hC W hW hcop]
    exact bot_le
  · rw [A10Gen.eq_bot_of_inf_centralizer_ne_bot hX hPZ h3' hbal hL hlay hcent hZ hW hcop]
    exact bot_le

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
