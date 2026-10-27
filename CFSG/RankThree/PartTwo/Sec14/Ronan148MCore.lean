module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Adapters.WholeGroupLayer
import CFSG.ClassicalInvolution.Sp62Rec.Balance

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Quot

variable {A Y : Subgroup G}

theorem ker148_eq_pPrimeCore_sup (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    letI := ker148_normal hAY
    ker148 A Y = CFSG.pPrimeCore 3 ↥(Y ⊔ A) := by
  letI := ker148_normal hAY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · refine le_sSup ⟨inferInstance, ?_⟩
    have h1 : Nat.card ↥(ker148 A Y) = Nat.card ↥(pPrimeCoreOf 3 Y) := by
      rw [ker148]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((pPrimeCoreOf_le 3 Y).trans le_sup_left)).toEquiv
    rw [h1]
    exact coprime_card_pPrimeCoreOf 3 Y
  ·
    set P : Subgroup G := (CFSG.pPrimeCore 3 ↥(Y ⊔ A)).map (Y ⊔ A).subtype with hP
    have hPcop : Nat.Coprime 3 (Nat.card P) := by
      rw [hP, Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hPY : P ≤ Y := by
      rintro _ ⟨g, hg, rfl⟩
      refine Main148.mem_of_coprime_three_of_mem_sup hAY hA3 g.2 ?_
      change Nat.Coprime 3 (orderOf (g : G))
      rw [Subgroup.orderOf_coe]
      have h2 : orderOf g ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(Y ⊔ A)) := by
        have := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 ↥(Y ⊔ A)) hg
        exact this
      exact Nat.Coprime.coprime_dvd_right h2 CFSG.pPrimeCore_coprime_card
    have hYP : Y ≤ Subgroup.normalizer (P : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
        refine ⟨⟨y, hyM⟩ * g * ⟨y, hyM⟩⁻¹, ?_, by simp⟩
        exact (CFSG.pPrimeCore_normal (p := 3) (G := ↥(Y ⊔ A))).conj_mem g hg _
      · rintro ⟨g, hg, hgx⟩
        have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
        refine ⟨⟨y, hyM⟩⁻¹ * g * (⟨y, hyM⟩⁻¹)⁻¹, ?_, ?_⟩
        · exact (CFSG.pPrimeCore_normal (p := 3) (G := ↥(Y ⊔ A))).conj_mem g hg _
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hgx ⊢
          rw [hgx]
          group
    have hPle : P ≤ pPrimeCoreOf 3 Y := le_pPrimeCoreOf hPY hYP hPcop
    intro g hg
    rw [ker148, Subgroup.mem_subgroupOf]
    exact hPle ⟨g, hg, rfl⟩

theorem pPrimeCore_quot148_eq_bot (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    letI := ker148_normal hAY
    CFSG.pPrimeCore 3 (↥(Y ⊔ A) ⧸ ker148 A Y) = ⊥ := by
  letI := ker148_normal hAY
  have key : ∀ (K : Subgroup ↥(Y ⊔ A)) [K.Normal], K = CFSG.pPrimeCore 3 ↥(Y ⊔ A) →
      CFSG.pPrimeCore 3 (↥(Y ⊔ A) ⧸ K) = ⊥ := by
    intro K _ hK
    subst hK
    exact CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  exact key _ (ker148_eq_pPrimeCore_sup hAY hA3)

theorem fittingSubgroup_quot148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    letI := ker148_normal hAY
    CFSG.fittingSubgroup (↥(Y ⊔ A) ⧸ ker148 A Y) = CFSG.pCore 3 (↥(Y ⊔ A) ⧸ ker148 A Y) := by
  letI := ker148_normal hAY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.Fitting_eq_pcore _ 3 (pPrimeCore_quot148_eq_bot hAY hA3)

end Quot

section ATimesB

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem coprime_card_img148 {X : Subgroup G} (hXM : X ≤ Y ⊔ A)
    (hX : Nat.Coprime 3 (Nat.card X)) :
    Nat.Coprime 3 (Nat.card (img148 A Y X)) := by
  refine Nat.Coprime.coprime_dvd_right ?_ hX
  have h1 := Subgroup.card_map_dvd (X.subgroupOf (Y ⊔ A)) (QuotientGroup.mk' (ker148 A Y))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at h1

theorem exists_lift_centralizer148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA : IsMulCommutative A) {b : G} (hb : b ∈ A) (hb3 : b ^ 3 = 1)
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hx : alpha148 A Y b hb * x = x * alpha148 A Y b hb) :
    ∃ (y a : G) (hya : y * a ∈ Y ⊔ A), y ∈ Y ⊓ Subgroup.centralizer ({b} : Set G) ∧ a ∈ A ∧
      QuotientGroup.mk' (ker148 A Y) ⟨y * a, hya⟩ = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) x
  have hgC : (g : G) ∈ (Y : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY]
    exact g.2
  obtain ⟨y₀, hy₀, a, ha, hya⟩ := hgC
  have hy₀M : y₀ ∈ Y ⊔ A := Subgroup.mem_sup_left hy₀
  have haM : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
  have hg : g = ⟨y₀, hy₀M⟩ * ⟨a, haM⟩ := Subtype.ext hya.symm
  set u := QuotientGroup.mk' (ker148 A Y) (⟨y₀, hy₀M⟩ : ↥(Y ⊔ A)) with hu
  set v := QuotientGroup.mk' (ker148 A Y) (⟨a, haM⟩ : ↥(Y ⊔ A)) with hv
  set β := alpha148 A Y b hb with hβ
  have hxuv : QuotientGroup.mk' (ker148 A Y) g = u * v := by rw [hg, map_mul]
  have hbv : β * v = v * β := by
    have hv' : v = alpha148 A Y a ha := rfl
    rw [hv', hβ, ← alpha148_mul, ← alpha148_mul]
    congr 1
    exact congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hbv' : β * v⁻¹ = v⁻¹ * β := by
    calc β * v⁻¹ = v⁻¹ * (v * β) * v⁻¹ := by group
      _ = v⁻¹ * (β * v) * v⁻¹ := by rw [hbv]
      _ = v⁻¹ * β := by group
  have hy₀c : β * u = u * β := by
    have hux : u = QuotientGroup.mk' (ker148 A Y) g * v⁻¹ := by rw [hxuv]; group
    rw [hux]
    calc β * (QuotientGroup.mk' (ker148 A Y) g * v⁻¹)
        = (β * QuotientGroup.mk' (ker148 A Y) g) * v⁻¹ := by group
      _ = (QuotientGroup.mk' (ker148 A Y) g * β) * v⁻¹ := by rw [hx]
      _ = QuotientGroup.mk' (ker148 A Y) g * (β * v⁻¹) := by group
      _ = QuotientGroup.mk' (ker148 A Y) g * (v⁻¹ * β) := by rw [hbv']
      _ = QuotientGroup.mk' (ker148 A Y) g * v⁻¹ * β := by group
  have hy₀img : u ∈ img148 A Y Y := mem_img148_iff.mpr ⟨y₀, hy₀M, hy₀, rfl⟩
  have hmem := Item148Rank.mem_img148_centralizer_of_commute148 hAY hb hb3 le_rfl hy₀img hy₀c
  obtain ⟨y, hyM, hyC, hyeq⟩ := mem_img148_iff.mp hmem
  refine ⟨y, a, (Y ⊔ A).mul_mem hyM haM, hyC, ha, ?_⟩
  rw [hxuv]
  have e1 : QuotientGroup.mk' (ker148 A Y) (⟨y * a, (Y ⊔ A).mul_mem hyM haM⟩ : ↥(Y ⊔ A)) =
      QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ * v := by
    rw [hv, ← map_mul]
    rfl
  rw [e1, hyeq]

theorem pCore_le_centralizer_img148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA : IsMulCommutative A) {b : G} (hb : b ∈ A) (hb3 : b ^ 3 = 1) {Q : Subgroup G}
    (hQb : Q ≤ Subgroup.centralizer ({b} : Set G))
    (hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    CFSG.pCore 3 (↥(Y ⊔ A) ⧸ ker148 A Y) ≤
      Subgroup.centralizer (img148 A Y Q : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := ↥(Y ⊔ A) ⧸ ker148 A Y
  set P : Subgroup M := CFSG.pCore 3 M with hPdef
  set R : Subgroup G := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) with hRdef
  set Rb := img148 A Y R with hRb
  set Qb := img148 A Y Q with hQb'
  set Bb : Subgroup M := Subgroup.zpowers (alpha148 A Y b hb) with hBb
  have hPp : IsPGroup 3 P := CFSG.pCore_isPGroup
  have hPn : P.Normal := CFSG.pCore_normal
  have hRcop : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 _
  have hQRb : Qb ≤ Rb := img148_mono hQR
  have hRbcop : Nat.Coprime 3 (Nat.card Rb) :=
    coprime_card_img148 ((pPrimeCoreOf_le 3 _).trans (inf_le_left.trans le_sup_left)) hRcop
  have hQbcop : Nat.Coprime (Nat.card Qb) 3 :=
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hQRb) hRbcop).symm
  have hα3 : alpha148 A Y b hb ^ 3 = 1 := by
    rw [← alpha148_pow, alpha148_eq_mk', mk'_ker148_eq_one_iff]
    change b ^ 3 ∈ pPrimeCoreOf 3 Y
    rw [hb3]
    exact Subgroup.one_mem _
  have hBbp : IsPGroup 3 Bb := by
    refine isPGroup_three_of_pow148 fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3, one_zpow]
  have hQB : ⁅Qb, Bb⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [hBb, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨g, hgM, hgQ, rfl⟩ := mem_img148_iff.mp hx
    have hcomm : alpha148 A Y b hb * QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩ * alpha148 A Y b hb := by
      rw [alpha148_eq_mk', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hQb hgQ)).symm
    exact (Commute.zpow_left hcomm k).eq
  have hfix : P ⊓ Subgroup.centralizer (Bb : Set M) ≤ Subgroup.centralizer (Qb : Set M) := by
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxb : alpha148 A Y b hb * x = x * alpha148 A Y b hb :=
      (Subgroup.mem_centralizer_iff.mp hxC _ (Subgroup.mem_zpowers _))
    obtain ⟨y, a, hya, hyC, ha, rfl⟩ := exists_lift_centralizer148 hAY hA hb hb3 hxb
    have hyN : y ∈ Subgroup.normalizer (R : Set G) :=
      le_normalizer_pPrimeCoreOf 3 _ hyC
    have haN : a ∈ Subgroup.normalizer (R : Set G) := by
      refine normalizer_le_normalizer_pPrimeCoreOf 3 _ ?_
      have haY := Subgroup.mem_normalizer_iff.mp (hAY ha)
      have haC : a ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)).symm
      have hCn := Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer haC : a ∈ Subgroup.normalizer
          (Subgroup.centralizer ({b} : Set G) : Set G))
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_inf]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(haY z).mp h1, (hCn z).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨(haY z).mpr h1, (hCn z).mpr h2⟩⟩
    have hgN : y * a ∈ Subgroup.normalizer (R : Set G) := Subgroup.mul_mem _ hyN haN
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqR : q ∈ Rb := hQRb hq
    obtain ⟨r, hrM, hrR, rfl⟩ := mem_img148_iff.mp hqR
    set xx := QuotientGroup.mk' (ker148 A Y) (⟨y * a, hya⟩ : ↥(Y ⊔ A))
    set qq := QuotientGroup.mk' (ker148 A Y) (⟨r, hrM⟩ : ↥(Y ⊔ A))
    have hconj : xx * qq * xx⁻¹ ∈ Rb := by
      have hr' : (y * a) * r * (y * a)⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgN r).mp hrR
      have hr'M : (y * a) * r * (y * a)⁻¹ ∈ Y ⊔ A :=
        (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hya hrM) ((Y ⊔ A).inv_mem hya)
      refine mem_img148_iff.mpr ⟨_, hr'M, hr', ?_⟩
      simp only [xx, qq, ← map_inv, ← map_mul]
      rfl
    have h1 : xx * qq * xx⁻¹ * qq⁻¹ ∈ Rb := Rb.mul_mem hconj (Rb.inv_mem (hQRb hq))
    have h2 : xx * qq * xx⁻¹ * qq⁻¹ ∈ P := by
      have hxP' : xx ∈ P := hxP
      have e : xx * qq * xx⁻¹ * qq⁻¹ = xx * (qq * xx⁻¹ * qq⁻¹) := by group
      rw [e]
      exact P.mul_mem hxP' (hPn.conj_mem _ (P.inv_mem hxP') qq)
    have h3 : xx * qq * xx⁻¹ * qq⁻¹ = 1 := by
      have hdisj : P ⊓ Rb = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        obtain ⟨n, hn⟩ := hPp.exists_card_eq
        rw [hn]
        exact Nat.Coprime.pow_left _ hRbcop
      have := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact this
    calc qq * xx = (xx * qq * xx⁻¹ * qq⁻¹)⁻¹ * (xx * qq) := by group
      _ = xx * qq := by rw [h3, inv_one, one_mul]
  have hnorm : ∀ x : M, x ∈ Subgroup.normalizer (P : Set M) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun z => ⟨fun hz => hPn.conj_mem z hz x,
      fun hz => by simpa [mul_assoc] using hPn.conj_mem _ hz x⁻¹⟩
  have hRB : Bb ≤ Subgroup.normalizer (P : Set M) := fun x _ => hnorm x
  have hQN : Qb ≤ Subgroup.normalizer (P : Set M) := fun x _ => hnorm x
  exact CFSG.ClassicalInvolution.Sp62Rec.centralizes_of_thompson_AxB hPp hQbcop hBbp hQN hRB hQB
    hfix

end ATimesB

section Core


@[expose] def Core148Layer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
        (∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) →
        letI := ker148_normal hY.2
        CFSG.layer (↥(Y ⊔ A) ⧸ ker148 A Y) ≤
          Subgroup.centralizer (img148 A Y Q : Set (↥(Y ⊔ A) ⧸ ker148 A Y))

theorem step148Core_of_layer (hLay : Core148Layer) : Step148Core := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY hQb
  letI := ker148_normal hY.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : IsMulCommutative A := hA.1.1
  set M := ↥(Y ⊔ A) ⧸ ker148 A Y
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hB1 : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    have := hB.2
    rw [hB1, Subgroup.card_bot, hA.2] at this
    omega
  have hbA : b ∈ A := hB.1 hbB
  have hQC : Q ≤ Subgroup.centralizer ({b} : Set G) := by
    intro q hq
    have hqB := (hQY hq).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hqB b hbB).symm
  have hPcent := pCore_le_centralizer_img148 hY.2 hAc hbA (hA3 b hbA) hQC (hQb b hbB hb1)
  have hLcent := hLay G A c L h Y hY hs hYB B hB Q hQ hQY hQb
  have hFstar : CFSG.generalizedFitting M ≤
      Subgroup.centralizer (img148 A Y Q : Set M) := by
    rw [CFSG.generalizedFitting.eq_sup, fittingSubgroup_quot148 hY.2 hA3]
    exact sup_le hPcent hLcent
  have hQF : img148 A Y Q ≤ CFSG.pCore 3 M := by
    rw [← fittingSubgroup_quot148 hY.2 hA3]
    refine le_trans ?_ (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup M)
    exact Subgroup.le_centralizer_iff.mp hFstar
  have hQcop : Nat.Coprime 3 (Nat.card (img148 A Y Q)) :=
    coprime_card_img148 (fun q hq => Subgroup.mem_sup_left (hQY hq).1)
      (Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (hQb b hbB hb1)) (coprime_card_pPrimeCoreOf 3 _))
  have hQbot : img148 A Y Q = ⊥ := by
    have hp : IsPGroup 3 (img148 A Y Q) := CFSG.pCore_isPGroup.to_le hQF
    rcases hp.card_eq_or_dvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (Nat.Coprime.eq_one_of_dvd hQcop h3) (by norm_num)
  intro q hq
  have hqM : q ∈ Y ⊔ A := Subgroup.mem_sup_left (hQY hq).1
  have h1 : QuotientGroup.mk' (ker148 A Y) ⟨q, hqM⟩ ∈ img148 A Y Q :=
    mem_img148_iff.mpr ⟨q, hqM, hq, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at h1
  exact mk'_ker148_eq_one_iff.mp h1

end Core

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
