module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5StepC1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem ne_top_of_fstar (h : Hyp141 D L₁ L₂ X) {H : Subgroup G} (hXH : X ≤ H)
    (hF : Fstar H = pCoreOf 2 H) : H ≠ ⊤ := by
  have hX9 : Nat.card X = 9 := card_X h
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ := le_bot_iff.1 (hbot ▸ hXH)
    rw [hXbot, Subgroup.card_bot] at hX9
    norm_num at hX9
  obtain ⟨N, hN, hHN⟩ := exists_isMaxTwoLocal_ge_of_fstar hF hHne
  haveI : IsSimpleGroup G := D.standing.simple
  intro hHtop
  have hNtop : N = ⊤ := top_le_iff.1 (hHtop ▸ hHN)
  exact (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1) hNtop

theorem le_of_eq_sup_pCoreOf (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D) {L : Subgroup G}
    (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) {H : Subgroup G} (hH : H ≠ ⊤)
    (hLH : L = (H ⊓ L) ⊔ pCoreOf 2 L) : H ≤ D.M := by
  have hcal : calNOf (H ⊓ L) = {D.M} :=
    h1422 L₁ L₂ X h L hL (H ⊓ L) inf_le_right hLH
  rcases eq_top_or_exists_le_coatom H with hHt | ⟨A, hA, hHA⟩
  · exact absurd hHt hH
  · have hA_mem : A ∈ calNOf (H ⊓ L) := ⟨hA, (inf_le_left.trans hHA)⟩
    have hA_eq : A = D.M := by
      rw [hcal] at hA_mem
      exact Set.mem_singleton_iff.mp hA_mem
    exact hHA.trans (le_of_eq hA_eq)

private theorem barImage_conj_eq_of_acts_trivially {L : Subgroup G} {g v : G}
    (hgN : g ∈ normalizer (L : Set G)) (hvL : v ∈ L)
    (hact : ∀ l ∈ L, (v⁻¹ * g) * l * (v⁻¹ * g)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) (l : ↥L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨v, hvL⟩ * l * ⟨v, hvL⟩⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.normalizerMonoidHom L ⟨g, hgN⟩ l) := by
  change QuotientGroup.mk (⟨v, hvL⟩ * l * ⟨v, hvL⟩⁻¹) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨g, hgN⟩ l)
  rw [QuotientGroup.eq_iff_div_mem]
  apply (CFSG.mem_openPCoreOf_iff _).mp
  have hcoe : (((⟨v, hvL⟩ * l * ⟨v, hvL⟩⁻¹) /
      (Subgroup.normalizerMonoidHom L ⟨g, hgN⟩ l) : ↥L) : G) =
      v * ((v⁻¹ * g) * (l : G) * (v⁻¹ * g)⁻¹ * (l : G)⁻¹)⁻¹ * v⁻¹ := by
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, UC6S846.rhoL_mk_coe]
    rw [div_eq_mul_inv]
    group
  rw [hcoe]
  exact (Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hvL) _).1
    ((pCoreOf 2 L).inv_mem (hact (l : G) l.2))

private theorem mem_normalizer_barImage_of_acts_trivially {L H : Subgroup G} {g v : G}
    (hgH : g ∈ H) (hgN : g ∈ normalizer (L : Set G)) (hvL : v ∈ L)
    (hact : ∀ l ∈ L, (v⁻¹ * g) * l * (v⁻¹ * g)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨v, hvL⟩ ∈
      normalizer (((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
        Set (Bar2 L)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    have hgkL : g * (k : G) * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hgN (k : G)).1 k.2
    have hgkH : g * (k : G) * g⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hgH (Subgroup.mem_subgroupOf.mp hk)) (H.inv_mem hgH)
    have hmemK : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g * (k : G) * g⁻¹, hgkL⟩ ∈
        (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hgkH)
    convert hmemK using 1
    have hconj : MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨v, hvL⟩)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) k) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨v, hvL⟩ * k * ⟨v, hvL⟩⁻¹) := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
    change MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨v, hvL⟩)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) k) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g * (k : G) * g⁻¹, hgkL⟩
    rw [hconj, barImage_conj_eq_of_acts_trivially hgN hvL hact k]
    apply congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    apply Subtype.ext
    rw [UC6S846.rhoL_mk_coe]
  · set Kb : Subgroup (Bar2 L) := (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      with hKb
    set ab : Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨v, hvL⟩ with hab
    let φ : Bar2 L →* Bar2 L := MulAut.conj ab
    have hφ : Function.Injective φ := (MulAut.conj ab).injective
    have hc : Nat.card Kb = Nat.card (Kb.map φ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective Kb φ hφ).toEquiv
    exact le_of_eq hc

theorem acts_trivially_of_not_le (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D)
    (hperm : PermutesPair D.M L₁ L₂) {H : Subgroup G} (hH : H ≠ ⊤) (hXH : X ≤ H)
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹)
    (hHM : ¬ H ≤ D.M) {L : Subgroup G} (hL : L ∈ ({L₁, L₂} : Set (Subgroup G)))
    {W : Subgroup G} (hW : IsPGroup 7 W) (hWH : W ≤ H ⊓ D.M) :
    ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  have hL' : L = L₁ ∨ L = L₂ := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hL
  have hcardX : Nat.card (X ⊓ L : Subgroup G) = 3 := by
    rcases hL' with rfl | rfl
    · exact card_inf_left h
    · exact card_inf_right h
  have hshape : IsL3 (Bar2 L) 1 := (mem_isL3 h hL).2
  have hX3 : IsPGroup 3 X := h.sylow.isPGroup
  have hdisjXQ : X ⊓ pCoreOf 2 L = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 L) hX3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))
  have hcardA : Nat.card (X.subgroupOf L) = 3 := by
    have hmap := Subgroup.card_map_of_injective (K := X.subgroupOf L) L.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype X L] at hmap
    rw [← hmap, hcardX]
  intro w hw l hl
  by_contra hwl
  have hwH : w ∈ H := (Subgroup.mem_inf.1 (hWH hw)).1
  have hWnorm : W ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) :=
    le_normalizer_of_isPGroup h hperm Nat.prime_seven (by norm_num) hW (hWH.trans inf_le_right)
  have hwn : w ∈ normalizer (L : Set G) := by
    have hw' := hWnorm hw
    rcases hL' with rfl | rfl
    · exact (Subgroup.mem_inf.1 hw').1
    · exact (Subgroup.mem_inf.1 hw').2
  obtain ⟨k7, hk7⟩ := hW ⟨w, hw⟩
  have hk7' : w ^ (7 ^ k7) = 1 := by simpa using hk7
  have hodd : Odd (orderOf w) :=
    ((Nat.prime_seven.odd_of_ne_two (by norm_num)).pow).of_dvd_nat
      (orderOf_dvd_of_pow_eq_one hk7')
  obtain ⟨v, hvord, hvact⟩ := exists_acts_eq_of_odd hshape hwn hodd
  let a : Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) v
  have ha_ne : a ≠ 1 := by
    intro ha1
    have ha1' : QuotientGroup.mk v = (1 : Bar2 L) := ha1
    have hvP : v ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff v).1 ha1'
    have hvQ : (v : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff v).2 hvP
    have hlvl : l * (v : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) (v : G)⁻¹).1
        ((pCoreOf 2 L).inv_mem hvQ)
    have hwq : w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
      have h1 := hvact l hl
      have h2 := (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).mul_mem hvQ h1) hlvl
      convert h2 using 1
      group
    exact hwl hwq
  have ha7 : 7 ∣ orderOf a := by
    have hdvd : orderOf a ∣ 7 ^ k7 :=
      hvord.trans (orderOf_dvd_of_pow_eq_one hk7')
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_seven).1 hdvd
    have hj0 : j ≠ 0 := by
      intro hj0
      have h1 : orderOf a = 1 := by rw [hj, hj0, pow_zero]
      exact ha_ne (orderOf_eq_one_iff.mp h1)
    have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
    rw [hj]
    calc 7 = 7 ^ 1 := by norm_num
      _ ∣ 7 ^ j := pow_dvd_pow 7 hj1
  have hP_ne_bot : (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊥ := by
    have hsub_ne : X.subgroupOf L ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card (X.subgroupOf L) = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hcardA] at h1
      norm_num at h1
    haveI : Nontrivial ↥(X.subgroupOf L) :=
      (Subgroup.nontrivial_iff_ne_bot (X.subgroupOf L)).mpr hsub_ne
    obtain ⟨k, hk, hk1⟩ :=
      (Subgroup.nontrivial_iff_exists_ne_one (X.subgroupOf L)).mp inferInstance
    have hkQ : (k : G) ∉ pCoreOf 2 L := by
      intro hkQ
      have hmem : (k : G) ∈ X ⊓ pCoreOf 2 L :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hk, hkQ⟩
      rw [hdisjXQ] at hmem
      have hkone : (k : G) = 1 := Subgroup.mem_bot.mp hmem
      exact hk1 (Subtype.ext hkone)
    intro hbot
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) k ∈ (⊥ : Subgroup (Bar2 L)) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem _ hk
    have hkπ : QuotientGroup.mk' (CFSG.pCore 2 ↥L) k = 1 := Subgroup.mem_bot.mp hmem
    exact hkQ ((CFSG.mem_openPCoreOf_iff k).2 ((QuotientGroup.eq_one_iff k).1 hkπ))
  have hP : Nat.card ((X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 3 := by
    have hdvd : Nat.card ((X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∣ 3 := by
      have h := Subgroup.card_map_dvd (H := X.subgroupOf L)
        (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      rwa [hcardA] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_le _ (le_of_eq h1)) hP_ne_bot
    · exact h3
  have hPK : (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono L hXH)
  obtain ⟨n, hn, hninv1, hninv2⟩ := exists_inversion h true true
  obtain ⟨m, hm, hmconj⟩ := hAut n hn
  have hmH : m ∈ H := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hm).1).1
  have hmL : m ∈ L₁ ⊔ L₂ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hm).1).2
  have hsupNorm : L₁ ⊔ L₂ ≤ normalizer (L : Set G) := by
    rcases hL' with rfl | rfl
    · exact sup_le Subgroup.le_normalizer (le_normalizer_left h)
    · exact sup_le (le_normalizer_right h) Subgroup.le_normalizer
  have hmN : m ∈ normalizer (L : Set G) := hsupNorm hmL
  obtain ⟨c, hcL, hcact⟩ := exists_acts_eq_of_mem_sup h hL hmL
  have hbN : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨c, hcL⟩ ∈
      normalizer (((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
        Set (Bar2 L)) :=
    mem_normalizer_barImage_of_acts_trivially hmH hmN hcL hcact
  have hbP : ∀ x ∈ (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨c, hcL⟩ * x *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨c, hcL⟩)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    have hkX : (k : G) ∈ X := Subgroup.mem_subgroupOf.mp hk
    have hnk : n * (k : G) * n⁻¹ = (k : G)⁻¹ := by
      rcases hL' with rfl | rfl
      · simpa using hninv1 (k : G) (Subgroup.mem_inf.mpr ⟨hkX, k.2⟩)
      · simpa using hninv2 (k : G) (Subgroup.mem_inf.mpr ⟨hkX, k.2⟩)
    have hmk : m * (k : G) * m⁻¹ = (k : G)⁻¹ := (hmconj (k : G) hkX).trans hnk
    have heq := barImage_conj_eq_of_acts_trivially hmN hcL hcact k
    have hLHS : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨c, hcL⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) k *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨c, hcL⟩)⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨c, hcL⟩ * k * ⟨c, hcL⟩⁻¹) := by
      rw [← map_mul, ← map_inv, ← map_mul]
    rw [hLHS, heq]
    have hk_inv : (Subgroup.normalizerMonoidHom L ⟨m, hmN⟩ k : ↥L) = k⁻¹ := by
      apply Subtype.ext
      rw [UC6S846.rhoL_mk_coe, Subgroup.coe_inv]
      simpa using hmk
    rw [hk_inv, map_inv]
  have ha : a ∈ normalizer (((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
      Set (Bar2 L)) :=
    mem_normalizer_barImage_of_acts_trivially hwH hwn v.2 hvact
  have hKtop : (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ :=
    eq_top_of_isL3_of_mem_normalizer hshape hPK hP ha ha7 hbN hbP
  have hLH : L = (H ⊓ L) ⊔ pCoreOf 2 L := by
    apply le_antisymm
    · intro x hxL
      have hmemTop : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈
          (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [hKtop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.1 hmemTop
      have hdiv : (⟨x, hxL⟩ / k : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (QuotientGroup.eq_iff_div_mem).1 hkπ.symm
      have hdivQ : ((⟨x, hxL⟩ / k : ↥L) : G) ∈ pCoreOf 2 L :=
        (CFSG.mem_openPCoreOf_iff (⟨x, hxL⟩ / k)).2 hdiv
      have hmem : ((⟨x, hxL⟩ / k : ↥L) : G) * (k : G) ∈ (H ⊓ L) ⊔ pCoreOf 2 L := by
        rw [sup_comm]
        exact Subgroup.mul_mem_sup hdivQ
          (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hk, k.2⟩)
      have hxeq : x = ((⟨x, hxL⟩ / k : ↥L) : G) * (k : G) := by
        rw [Subgroup.coe_div]
        simp only [Subtype.coe_mk]
        rw [div_eq_mul_inv]
        group
      rw [hxeq]
      exact hmem
    · exact sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  exact hHM (le_of_eq_sup_pCoreOf h h1422 hL hH hLH)

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
