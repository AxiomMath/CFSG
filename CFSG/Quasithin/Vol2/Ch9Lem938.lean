module

public import CFSG.Quasithin.Vol2.Ch9Sec3VU
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsLie
public import CFSG.Quasithin.Vol2.Ch9Lem936
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3Conj
public import CFSG.Quasithin.Vol2.Ch9Sec3Field

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem not_commutator_le_of_card_three {G : Type} [Group G] [Finite G] {K B : Subgroup G}
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) (hBK : B ≤ K)
    (hB3 : Nat.card B = 3) : ¬ ⁅K, B⁆ ≤ pCoreOf 2 K := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := hKA
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eA.isSimpleGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set B' := B.subgroupOf K with hB'
  set P := B'.map π with hP
  have hcent : ∀ x ∈ P, ∀ g, g * x * g⁻¹ = x := by
    rintro _ ⟨⟨b, hbK⟩, hb, rfl⟩ g
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) g
    have h1 : k * b * k⁻¹ * b⁻¹ ∈ pCoreOf 2 K :=
      hle (Subgroup.commutator_mem_commutator hk (Subgroup.mem_subgroupOf.mp hb))
    obtain ⟨y, hy, hye⟩ := h1
    have h2 : (⟨k, hk⟩ : ↥K) * ⟨b, hbK⟩ * (⟨k, hk⟩ : ↥K)⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹ = y :=
      Subtype.ext hye.symm
    have h3 : π ((⟨k, hk⟩ : ↥K) * ⟨b, hbK⟩ * (⟨k, hk⟩ : ↥K)⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹) = 1 := by
      rw [h2]
      exact (QuotientGroup.eq_one_iff y).mpr (hy)
    simp only [map_mul, map_inv] at h3
    calc π ⟨k, hk⟩ * π ⟨b, hbK⟩ * (π ⟨k, hk⟩)⁻¹
        = (π ⟨k, hk⟩ * π ⟨b, hbK⟩ * (π ⟨k, hk⟩)⁻¹ * (π ⟨b, hbK⟩)⁻¹) * π ⟨b, hbK⟩ := by group
      _ = π ⟨b, hbK⟩ := by rw [h3, one_mul]
  have hnorm : P.Normal := ⟨fun x hx g => by rw [hcent x hx g]; exact hx⟩
  rcases hs.eq_bot_or_eq_top_of_normal P with hbot | htop
  ·
    have hBO : B ≤ pCoreOf 2 K := by
      intro b hb
      have h1 : π ⟨b, hBK hb⟩ ∈ P := ⟨⟨b, hBK hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact ⟨⟨b, hBK hb⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hBO)
    rw [hB3] at hk
    have h2 : 2 ∣ 3 := by
      rcases k with _ | k
      · norm_num at hk
      · exact ⟨2 ^ k, by rw [hk]; ring⟩
    omega
  ·
    have h1 : Nat.card P ≤ Nat.card B' :=
      Nat.card_le_card_of_surjective (fun b : ↥B' => (⟨π b, b, b.2, rfl⟩ : ↥P))
        (by rintro ⟨_, b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩)
    have h2 : Nat.card B' = 3 := by
      rw [hB', ← hB3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
    have h3 : Nat.card P = 60 := by
      rw [htop, Subgroup.card_top, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup, Fintype.card_fin]
      decide
    omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem commutator_le_pCoreOf_of_psi
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) {x : G}
    (hxL₀ : x ∈ fsuL0 T L) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hψ : ∀ l (hl : l ∈ L), ψ ⟨l, S.L_le_L0 hl⟩ * ψ ⟨x, hxL₀⟩ = ψ ⟨x, hxL₀⟩ * ψ ⟨l, S.L_le_L0 hl⟩) :
    ⁅L, Subgroup.zpowers x⁆ ≤ pCoreOf 2 L := by
  rw [Subgroup.commutator_le]
  intro l hl y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hlx : l * x ^ k * l⁻¹ * (x ^ k)⁻¹ ∈ L := by
    have h1 : x ^ k * l⁻¹ * (x ^ k)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).zpow_mem hxN k) _).mp
        (L.inv_mem hl)
    have e' : l * x ^ k * l⁻¹ * (x ^ k)⁻¹ = l * (x ^ k * l⁻¹ * (x ^ k)⁻¹) := by group
    rw [e']
    exact L.mul_mem hl h1
  have hcomm : ψ ⟨l, S.L_le_L0 hl⟩ * ψ ⟨x, hxL₀⟩ ^ k = ψ ⟨x, hxL₀⟩ ^ k * ψ ⟨l, S.L_le_L0 hl⟩ :=
    ((Commute.zpow_right (hψ l hl) k))
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c
    (⟨l, S.L_le_L0 hl⟩ * ⟨x, hxL₀⟩ ^ k * ⟨l, S.L_le_L0 hl⟩⁻¹ * (⟨x, hxL₀⟩ ^ k)⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, hcomm]
      group)
  rw [commutatorElement_def]
  exact S.inf_centralizer_L_le h37c h38c ⟨hlx, hq.2⟩

end IsCoord

variable (S : Setup T L I n)
include S

theorem lem938' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hFE : SL3FourTorusFact) (h2 : n = 2) {K B D K₀ : Subgroup G}
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hKperf : ⁅K, K⁆ = K) (hKM : ¬ K ≤ fsuM T L)
    (hT₁K : T ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hd' : ∃ d' ∈ D ⊓ L, d' ≠ 1 ∧ ⁅K, Subgroup.zpowers d'⁆ ≤ pCoreOf 2 K)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hSL : IsSL3 4 (O2Q K₀)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hK4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hK4]
  have : Nontrivial Fˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Fˣ)
  have hDL0 : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hL0N := hc.L0_le_normalizer_L h37 h38 h37c h38c
  have hK₀M₀ : K₀ ≤ M₀ := le_of_mem_cComp hK₀
  have hDT : ∀ x ∈ D, x ∈ T → x = 1 := fun x hx hxT =>
    eq_one_of_odd_of_mem hfsu.sylow.1 hxT (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx))
  have hψinj : ∀ x (hx : x ∈ D), ψ ⟨x, hDL0 hx⟩ = 1 → x = 1 := fun x hx hψx =>
    hc.eq_one_of_odd h37c h38c ⟨x, hDL0 hx⟩
      (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx)) hψx
  obtain ⟨d', ⟨hd'D, hd'Lm⟩, hd'1, hd'C⟩ := hd'
  have hd'L : d' ∈ fsuL0 T L := hDL0 hd'D
  have key : ∃ d ∈ D, ∃ hdL : d ∈ fsuL0 T L, d ≠ 1 ∧ ⁅L, Subgroup.zpowers d⁆ ≤ pCoreOf 2 L ∧
      ∀ x ∈ D, ∃ i j : ℤ, x = d' ^ i * d ^ j := by
    have hgen : ∀ (a b : Fˣ), a ≠ 1 → b ≠ 1 → ∀ (x d d' : G), x ∈ D → d ∈ D → d' ∈ D →
        ∀ (hd : d ∈ fsuL0 T L) (hd' : d' ∈ fsuL0 T L),
        ((ψ ⟨d, hd⟩ = (diagOf 1, diagOf b) ∧ ψ ⟨d', hd'⟩ = (diagOf a, diagOf 1)) ∨
          (ψ ⟨d, hd⟩ = (diagOf b, diagOf 1) ∧ ψ ⟨d', hd'⟩ = (diagOf 1, diagOf a))) →
        ∃ i j : ℤ, x = d' ^ i * d ^ j := by
      intro a b ha hb x d d' hx hdD hd'D hd hd' hψ
      obtain ⟨u, v, huv⟩ := IsCoord.exists_diag_of_mem hdiag hx (hDL0 hx)
      have hdH : ∀ (c : Fˣ) (i : ℕ), diagOf (c ^ i) = (diagOf c) ^ i := fun c i => by
        rw [← diagHom_apply, ← diagHom_apply, map_pow]
      have hd1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
      have hfin : ∀ i j : ℕ, ψ ⟨x, hDL0 hx⟩ = ψ ⟨d', hd'⟩ ^ i * ψ ⟨d, hd⟩ ^ j →
          ∃ i j : ℤ, x = d' ^ i * d ^ j := by
        intro i j hij
        refine ⟨i, j, ?_⟩
        have hmem : x * (d' ^ i * d ^ j)⁻¹ ∈ D :=
          D.mul_mem hx (D.inv_mem (D.mul_mem (D.pow_mem hd'D i) (D.pow_mem hdD j)))
        have h1 := hψinj _ hmem (by
          have e' : (⟨x * (d' ^ i * d ^ j)⁻¹, hDL0 hmem⟩ : ↥(fsuL0 T L)) =
              ⟨x, hDL0 hx⟩ * (⟨d', hd'⟩ ^ i * ⟨d, hd⟩ ^ j)⁻¹ := rfl
          rw [e', map_mul, map_inv, map_mul, map_pow, map_pow, hij, mul_inv_cancel])
        simpa using mul_inv_eq_one.mp h1
      rcases hψ with ⟨hψd, hψd'⟩ | ⟨hψd, hψd'⟩
      · obtain ⟨i, hi⟩ := mem_powers_of_prime_card hU3 ha (g' := u)
        obtain ⟨j, hj⟩ := mem_powers_of_prime_card hU3 hb (g' := v)
        have hi : a ^ i = u := hi
        have hj : b ^ j = v := hj
        refine hfin i j ?_
        rw [huv, hψd, hψd', Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk, ← hdH, ← hdH, ← hdH, ← hdH,
          one_pow, one_pow, hd1, mul_one, one_mul, hi, hj]
      · obtain ⟨i, hi⟩ := mem_powers_of_prime_card hU3 ha (g' := v)
        obtain ⟨j, hj⟩ := mem_powers_of_prime_card hU3 hb (g' := u)
        have hi : a ^ i = v := hi
        have hj : b ^ j = u := hj
        refine hfin i j ?_
        rw [huv, hψd, hψd', Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk, ← hdH, ← hdH, ← hdH, ← hdH,
          one_pow, one_pow, hd1, mul_one, one_mul, hi, hj]
    obtain ⟨u, v, huv⟩ := IsCoord.exists_diag_of_mem hdiag hd'D hd'L
    have hdg1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
    have hψd'L : ψ ⟨d', hd'L⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
      ⟨⟨d', hd'L⟩, Subgroup.mem_subgroupOf.mpr hd'Lm, rfl⟩
    rcases hc.map_L h37c h38c with hL | hL
    · obtain ⟨d, hdD, hdL, hψd⟩ := IsCoord.exists_mem_of_diag hdiag 1 ω
      have hv : v = 1 := by
        rw [hL] at hψd'L
        have h1 : (ψ ⟨d', hd'L⟩).2 = 1 := hψd'L
        rw [huv] at h1
        have h3 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
          ((g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h1
        simp only [coe_diagOf] at h3
        exact Units.ext (by simpa using h3)
      have hu : u ≠ 1 := by
        rintro rfl
        apply hd'1
        refine hψinj d' hd'D ?_
        rw [huv, hv, hdg1, Prod.mk_one_one]
      have hd1 : d ≠ 1 := by
        intro h1
        have h0 : (⟨d, hdL⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd
        have h3 := congrArg (fun p : SpecialLinearGroup (Fin 2) F × _ =>
          ((p.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hψd
        simp only [coe_diagOf] at h3
        exact hω (Units.ext (by simpa using h3.symm))
      refine ⟨d, hdD, hdL, hd1, ?_, fun x hx =>
        hgen u ω hu hω x d d' hx hdD hd'D hdL hd'L (Or.inl ⟨hψd, by rw [huv, hv]⟩)⟩
      refine hc.commutator_le_pCoreOf_of_psi h37c h38c hdL (hL0N hdL) fun l hl => ?_
      have hl2 : (ψ ⟨l, S.L_le_L0 hl⟩).2 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      rw [hψd, hdg1]
      apply Prod.ext
      · simp
      · simp [hl2]
    · obtain ⟨d, hdD, hdL, hψd⟩ := IsCoord.exists_mem_of_diag hdiag ω 1
      have hu : u = 1 := by
        rw [hL] at hψd'L
        have h1 : (ψ ⟨d', hd'L⟩).1 = 1 := hψd'L
        rw [huv] at h1
        have h3 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
          ((g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h1
        simp only [coe_diagOf] at h3
        exact Units.ext (by simpa using h3)
      have hv : v ≠ 1 := by
        rintro rfl
        apply hd'1
        refine hψinj d' hd'D ?_
        rw [huv, hu, hdg1, Prod.mk_one_one]
      have hd1 : d ≠ 1 := by
        intro h1
        have h0 : (⟨d, hdL⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd
        have h3 := congrArg (fun p : SpecialLinearGroup (Fin 2) F × _ =>
          ((p.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hψd
        simp only [coe_diagOf] at h3
        exact hω (Units.ext (by simpa using h3.symm))
      refine ⟨d, hdD, hdL, hd1, ?_, fun x hx =>
        hgen v ω hv hω x d d' hx hdD hd'D hdL hd'L (Or.inr ⟨hψd, by rw [huv, hu]⟩)⟩
      refine hc.commutator_le_pCoreOf_of_psi h37c h38c hdL (hL0N hdL) fun l hl => ?_
      have hl1 : (ψ ⟨l, S.L_le_L0 hl⟩).1 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      rw [hψd, hdg1]
      apply Prod.ext
      · simp [hl1]
      · simp
  obtain ⟨d, hdD, hdL, hd1, hdC, hgenD⟩ := key
  have hDK₀ : D ≤ K₀ := (hc.le_sup_L h37 h38 h37c h38c hD hdiag).trans
    (sup_le ((hBD ▸ hBK).trans hKK₀) hLK₀)
  have hd3 : orderOf d = 3 :=
    orderOf_eq_prime (hc.pow_three_eq_one h37c h38c h2 hD hdiag hdD) hd1
  have hO₂K₀ : pCoreOf 2 K₀ ≤ fsuM T L := by
    refine (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀M₀)
      (hK₀n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)).trans ?_
    exact (F7.isSylowTwoOf_pCoreOf_le hsyl).trans (inf_le_left.trans Setup.T_le_fsuM)
  have hKnot : ¬ K ≤ L ⊔ pCoreOf 2 K₀ := fun h => hKM (h.trans (sup_le S.L_le_fsuM hO₂K₀))
  have hdK := hFE G K₀ (T₁ ⊓ K₀) L K d hSL (A4.isSylowTwoOf_inf_normal hsyl hK₀M₀ hK₀n) hLK₀
    hKK₀ (inf_le_left.trans inf_le_right) (inf_le_left.trans hT₁K)
    (perfect_of_mem_cComp hfsu.maximal.1.2.1) hKperf
    (S.oTwoQuot_L_facts h37c h38c h2) hKA hKnot (hDK₀ hdD) hd3 (hL0N (hDL0 hdD)) (hDK hdD) hdC
  have hON : ∀ x ∈ D, x ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hDK hx)
  have hcd : ∀ k ∈ K, ∀ j : ℤ, k * d ^ j * k⁻¹ * (d ^ j)⁻¹ ∈ pCoreOf 2 K := fun k hk j =>
    hdK (Subgroup.commutator_mem_commutator hk (Subgroup.zpow_mem_zpowers d j))
  have hcd' : ∀ k ∈ K, ∀ i : ℤ, k * d' ^ i * k⁻¹ * (d' ^ i)⁻¹ ∈ pCoreOf 2 K := fun k hk i =>
    hd'C (Subgroup.commutator_mem_commutator hk (Subgroup.zpow_mem_zpowers d' i))
  have hKD : ⁅K, D⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro k hk x hx
    obtain ⟨i, j, rfl⟩ := hgenD x hx
    rw [commutatorElement_def]
    have h1 := hcd' k hk i
    have h2 := (Subgroup.mem_normalizer_iff.mp (hON _ (D.zpow_mem hd'D i)) _).mp (hcd k hk j)
    have e' : k * (d' ^ i * d ^ j) * k⁻¹ * (d' ^ i * d ^ j)⁻¹ =
        (k * d' ^ i * k⁻¹ * (d' ^ i)⁻¹) *
          (d' ^ i * (k * d ^ j * k⁻¹ * (d ^ j)⁻¹) * (d' ^ i)⁻¹) := by group
    rw [e']
    exact mul_mem h1 h2
  exact not_commutator_le_of_card_three hKA hBK hB3
    ((Subgroup.commutator_mono le_rfl (hBD ▸ inf_le_left)).trans hKD)

theorem lem938 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hFE : SL3FourTorusFact) (h2 : n = 2) {H K B D K₀ : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hSL : IsSL3 4 (O2Q K₀)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hK4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hK4]
  have : Nontrivial Fˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Fˣ)
  have hDL0 : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hL0N := hc.L0_le_normalizer_L h37 h38 h37c h38c
  have hKM : ¬ K ≤ fsuM T L := fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM)
  have hK₀M₀ : K₀ ≤ M₀ := le_of_mem_cComp hK₀
  obtain ⟨t₀, ht₀, ht₀n⟩ := S.exists_not_mem_normalizer
  obtain ⟨m, hm, hmt⟩ := S.exists_mul_mem_normalizer_hall hD ht₀
  set t := m * t₀ with ht
  have htT : t ∈ T := T.mul_mem hm.1 ht₀
  have htn : t ∉ Subgroup.normalizer (L : Set G) := fun h => ht₀n (by
    have e' : t₀ = m⁻¹ * t := by rw [ht]; group
    rw [e']
    exact (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem (hL0N hm.2)) h)
  obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut htT
  have hswap : bar e ⟨t, S.hMN (Setup.T_le_fsuM htT)⟩ = Om4.lr A B' * Om4.frM τ * Om4.trM := by
    rcases hform with hf | hf
    · exact absurd (hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.T_le_fsuM htT) hf) htn
    · exact hf
  have hDT : ∀ x ∈ D, x ∈ T → x = 1 := fun x hx hxT =>
    eq_one_of_odd_of_mem hfsu.sylow.1 hxT (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx))
  have hψinj : ∀ x (hx : x ∈ D), ψ ⟨x, hDL0 hx⟩ = 1 → x = 1 := fun x hx hψx =>
    hc.eq_one_of_odd h37c h38c ⟨x, hDL0 hx⟩
      (hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hx)) hψx
  have key : ∃ d ∈ D, ∃ hdL : d ∈ fsuL0 T L, ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L,
      d' ∈ L ∧ d ≠ 1 ∧ t * d * t⁻¹ = d' ∧ ⁅L, Subgroup.zpowers d⁆ ≤ pCoreOf 2 L ∧
      ∀ x ∈ D, ∃ i j : ℤ, x = d' ^ i * d ^ j := by
    have hgen : ∀ (a b : Fˣ), a ≠ 1 → b ≠ 1 → ∀ (x d d' : G), x ∈ D → d ∈ D → d' ∈ D →
        ∀ (hd : d ∈ fsuL0 T L) (hd' : d' ∈ fsuL0 T L),
        ((ψ ⟨d, hd⟩ = (diagOf 1, diagOf b) ∧ ψ ⟨d', hd'⟩ = (diagOf a, diagOf 1)) ∨
          (ψ ⟨d, hd⟩ = (diagOf b, diagOf 1) ∧ ψ ⟨d', hd'⟩ = (diagOf 1, diagOf a))) →
        ∃ i j : ℤ, x = d' ^ i * d ^ j := by
      intro a b ha hb x d d' hx hdD hd'D hd hd' hψ
      obtain ⟨u, v, huv⟩ := IsCoord.exists_diag_of_mem hdiag hx (hDL0 hx)
      have hdH : ∀ (c : Fˣ) (i : ℕ), diagOf (c ^ i) = (diagOf c) ^ i := fun c i => by
        rw [← diagHom_apply, ← diagHom_apply, map_pow]
      have hd1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
      have hfin : ∀ i j : ℕ, ψ ⟨x, hDL0 hx⟩ = ψ ⟨d', hd'⟩ ^ i * ψ ⟨d, hd⟩ ^ j →
          ∃ i j : ℤ, x = d' ^ i * d ^ j := by
        intro i j hij
        refine ⟨i, j, ?_⟩
        have hmem : x * (d' ^ i * d ^ j)⁻¹ ∈ D :=
          D.mul_mem hx (D.inv_mem (D.mul_mem (D.pow_mem hd'D i) (D.pow_mem hdD j)))
        have h1 := hψinj _ hmem (by
          have e' : (⟨x * (d' ^ i * d ^ j)⁻¹, hDL0 hmem⟩ : ↥(fsuL0 T L)) =
              ⟨x, hDL0 hx⟩ * (⟨d', hd'⟩ ^ i * ⟨d, hd⟩ ^ j)⁻¹ := rfl
          rw [e', map_mul, map_inv, map_mul, map_pow, map_pow, hij, mul_inv_cancel])
        simpa using mul_inv_eq_one.mp h1
      rcases hψ with ⟨hψd, hψd'⟩ | ⟨hψd, hψd'⟩
      · obtain ⟨i, hi⟩ := mem_powers_of_prime_card hU3 ha (g' := u)
        obtain ⟨j, hj⟩ := mem_powers_of_prime_card hU3 hb (g' := v)
        have hi : a ^ i = u := hi
        have hj : b ^ j = v := hj
        refine hfin i j ?_
        rw [huv, hψd, hψd', Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk, ← hdH, ← hdH, ← hdH, ← hdH,
          one_pow, one_pow, hd1, mul_one, one_mul, hi, hj]
      · obtain ⟨i, hi⟩ := mem_powers_of_prime_card hU3 ha (g' := v)
        obtain ⟨j, hj⟩ := mem_powers_of_prime_card hU3 hb (g' := u)
        have hi : a ^ i = v := hi
        have hj : b ^ j = u := hj
        refine hfin i j ?_
        rw [huv, hψd, hψd', Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk, ← hdH, ← hdH, ← hdH, ← hdH,
          one_pow, one_pow, hd1, mul_one, one_mul, hi, hj]
    have hτω : Units.map τ.toMonoidHom ω ≠ 1 := fun h1 => hω (by
      have h2 := congrArg Units.val h1
      rw [Units.coe_map, Units.val_one] at h2
      exact Units.ext (by simpa using τ.injective (h2.trans (map_one τ).symm)))
    rcases hc.map_L h37c h38c with hL | hL
    · obtain ⟨d, hdD, hdL, hψd⟩ := IsCoord.exists_mem_of_diag hdiag 1 ω
      obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ :=
        hc.conj_diag_swap h37c h38c hdiag htT hA hB' hswap hdL hψd
      have htd : t * d * t⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp hmt d).mp hdD
      have heq : t * d * t⁻¹ = d' := mul_inv_eq_one.mp (hDT _ (D.mul_mem htd (D.inv_mem hd'D)) hmem)
      rw [map_one] at hψd'
      have hd1 : d ≠ 1 := by
        intro h1
        have h0 : (⟨d, hdL⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd
        have h3 := congrArg (fun p : SpecialLinearGroup (Fin 2) F × _ =>
          ((p.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hψd
        simp only [coe_diagOf] at h3
        exact hω (Units.ext (by simpa using h3.symm))
      have hd'Lm : d' ∈ L := hc.mem_L_of_mem_D h37 h38 h37c h38c hD hd'D (by
        rw [hL, hψd']
        exact MonoidHom.mem_ker.mpr (show diagOf (1 : Fˣ) = 1 by rw [← diagHom_apply, map_one]))
      refine ⟨d, hdD, hdL, d', hd'D, hd'L, hd'Lm, hd1, heq, ?_, fun x hx =>
        hgen _ ω hτω hω x d d' hx hdD hd'D hdL hd'L (Or.inl ⟨hψd, hψd'⟩)⟩
      refine hc.commutator_le_pCoreOf_of_psi h37c h38c hdL (hL0N hdL) fun l hl => ?_
      have hl2 : (ψ ⟨l, S.L_le_L0 hl⟩).2 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      have hdg1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
      rw [hψd, hdg1]
      apply Prod.ext
      · simp
      · simp [hl2]
    · obtain ⟨d, hdD, hdL, hψd⟩ := IsCoord.exists_mem_of_diag hdiag ω 1
      obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ :=
        hc.conj_diag_swap h37c h38c hdiag htT hA hB' hswap hdL hψd
      have htd : t * d * t⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp hmt d).mp hdD
      have heq : t * d * t⁻¹ = d' := mul_inv_eq_one.mp (hDT _ (D.mul_mem htd (D.inv_mem hd'D)) hmem)
      rw [map_one] at hψd'
      have hd1 : d ≠ 1 := by
        intro h1
        have h0 : (⟨d, hdL⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
        rw [h0, map_one] at hψd
        have h3 := congrArg (fun p : SpecialLinearGroup (Fin 2) F × _ =>
          ((p.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hψd
        simp only [coe_diagOf] at h3
        exact hω (Units.ext (by simpa using h3.symm))
      have hd'Lm : d' ∈ L := hc.mem_L_of_mem_D h37 h38 h37c h38c hD hd'D (by
        rw [hL, hψd']
        exact MonoidHom.mem_ker.mpr (show diagOf (1 : Fˣ) = 1 by rw [← diagHom_apply, map_one]))
      refine ⟨d, hdD, hdL, d', hd'D, hd'L, hd'Lm, hd1, heq, ?_, fun x hx =>
        hgen _ ω hτω hω x d d' hx hdD hd'D hdL hd'L (Or.inr ⟨hψd, hψd'⟩)⟩
      refine hc.commutator_le_pCoreOf_of_psi h37c h38c hdL (hL0N hdL) fun l hl => ?_
      have hl1 : (ψ ⟨l, S.L_le_L0 hl⟩).1 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      have hdg1 : diagOf (1 : Fˣ) = 1 := by rw [← diagHom_apply, map_one]
      rw [hψd, hdg1]
      apply Prod.ext
      · simp [hl1]
      · simp
  obtain ⟨d, hdD, hdL, d', hd'D, hd'L, hd'Lm, hd1, heq, hdC, hgenD⟩ := key
  have hDK₀ : D ≤ K₀ := (hc.le_sup_L h37 h38 h37c h38c hD hdiag).trans
    (sup_le ((hBD ▸ hBK).trans hKK₀) hLK₀)
  have hd3 : orderOf d = 3 :=
    orderOf_eq_prime (hc.pow_three_eq_one h37c h38c h2 hD hdiag hdD) hd1
  have hO₂K₀ : pCoreOf 2 K₀ ≤ fsuM T L := by
    refine (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀M₀)
      (hK₀n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)).trans ?_
    exact (F7.isSylowTwoOf_pCoreOf_le hsyl).trans (inf_le_left.trans Setup.T_le_fsuM)
  have hKnot : ¬ K ≤ L ⊔ pCoreOf 2 K₀ := fun h => hKM (h.trans (sup_le S.L_le_fsuM hO₂K₀))
  have hdK := hFE G K₀ (T₁ ⊓ K₀) L K d hSL (A4.isSylowTwoOf_inf_normal hsyl hK₀M₀ hK₀n) hLK₀
    hKK₀ (inf_le_left.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans hTK))
    (perfect_of_mem_cComp hfsu.maximal.1.2.1) (perfect_of_mem_cComp hKc)
    (S.oTwoQuot_L_facts h37c h38c h2) hKA hKnot (hDK₀ hdD) hd3 (hL0N (hDL0 hdD)) (hDK hdD) hdC
  have htO : t ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hTK htT)
  have hcd : ∀ k ∈ K, ∀ j : ℤ, k * d ^ j * k⁻¹ * (d ^ j)⁻¹ ∈ pCoreOf 2 K := fun k hk j =>
    hdK (Subgroup.commutator_mem_commutator hk (Subgroup.zpow_mem_zpowers d j))
  have hcd' : ∀ k ∈ K, ∀ i : ℤ, k * d' ^ i * k⁻¹ * (d' ^ i)⁻¹ ∈ pCoreOf 2 K := by
    intro k hk i
    have hk' : t⁻¹ * k * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem htT)) k).mp hk
      simpa using this
    have h1 := hcd _ hk' i
    have h2 := (Subgroup.mem_normalizer_iff.mp htO _).mp h1
    have e' : t * (t⁻¹ * k * t * d ^ i * (t⁻¹ * k * t)⁻¹ * (d ^ i)⁻¹) * t⁻¹ =
        k * d' ^ i * k⁻¹ * (d' ^ i)⁻¹ := by
      rw [← heq, conj_zpow]
      group
    rwa [e'] at h2
  have hd'1 : d' ≠ 1 := by
    intro h1
    apply hd1
    have h3 : t * d * t⁻¹ = 1 := heq.trans h1
    calc d = t⁻¹ * (t * d * t⁻¹) * t := by group
      _ = 1 := by rw [h3]; group
  refine S.lem938' h37 h38 h37c h38c hFE h2 hKA (perfect_of_mem_cComp hKc) hKM
    (inf_le_left.trans hTK) hBK hB3 hD hBD hDK ⟨d', ⟨hd'D, hd'Lm⟩, hd'1, ?_⟩ hsyl hK₀ hLK₀ hKK₀
    hK₀n hSL
  rw [Subgroup.commutator_le]
  intro k hk y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [commutatorElement_def]
  exact hcd' k hk i

end Setup

end CFSG.Quasithin.H13.Ch9
