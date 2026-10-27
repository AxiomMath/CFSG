module

public import CFSG.Quasithin.Background.G64Case1Pre
public import CFSG.Quasithin.Background.G64Case3Piece
public import CFSG.Quasithin.Background.G64Alt
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}

theorem conclusion_of_natSL (h : Hyp61 G a) {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥(conjClosure (Subgroup.zpowers a) G)}
    (hπ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia (conjClosure (Subgroup.zpowers a) G)
      ⊤ ⊥ π) : Conclusion G a := by
  have hnat : BinaryNaturalSL (conjClosure (Subgroup.zpowers a) G) ⊤ ⊥ n 1 :=
    ⟨ZMod 2, inferInstance, inferInstance, by simp, π, hπ⟩
  have hKtop : conjClosure (Subgroup.zpowers a) G = ⊤ := BinaryNaturalSL.eq_top hnat
  have hGK : G = conjClosure (Subgroup.zpowers a) G :=
    le_antisymm (by rw [hKtop]; exact le_top) (classK_le h)
  refine conclusion_of_single h hGK (Or.inl ⟨n, hn2, hn5, hnat⟩) fun _ => ?_
  refine Or.inl ⟨n, hn2, hn5, ⟨?_⟩⟩
  rw [hGK]
  exact (MulEquiv.ofBijective π ⟨natSL_injective hπ, hπ.1⟩).symm

theorem eq_bot_of_natSL [Finite V] {n : ℕ} (hn : 2 ≤ n) {H : Subgroup (MulAut V)} {C : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (hπ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H ⊤ C π) (hHV : commV H = ⊤)
    {x : MulAut V} (hx : x ∈ H) (hx1 : x ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers x)) = 2) :
    C = ⊥ := by
  have h1 := card_commV_le_of_natSL hn hπ hx hx1 htr
  have h2 := RealizesVia.card_eq hπ
  rw [card_natMod, Nat.card_zmod, Subgroup.card_top] at h2
  rw [hHV, Subgroup.card_top, h2] at h1
  have hC : Nat.card C ≤ 1 := by
    have : 2 ^ n * Nat.card C ≤ 2 ^ n * 1 := by rw [mul_one]; exact h1
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  exact Subgroup.card_eq_one.1 (le_antisymm hC Nat.card_pos)

theorem false_of_two_summands {D₀ D₁ : FFModel} (hD₀ : D₀.Faithful) (hD₁ : D₁.Faithful)
    {H : Subgroup (MulAut V)} {I₀ I₁ Z : Subgroup V}
    {π₀ : D₀.Gam →* ↥H} {π₁ : D₁.Gam →* ↥H} (h₀ : D₀.RealizesVia H I₀ Z π₀)
    (h₁ : D₁.RealizesVia H I₁ Z π₁) (hI : I₀ ⊓ I₁ ≤ Z) {x : MulAut V} (hx : x ∈ H)
    (hx1 : x ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers x)) = 2) : False := by
  obtain ⟨γ₀, hγ₀⟩ := exists_preimage h₀ hx
  obtain ⟨γ₁, hγ₁⟩ := exists_preimage h₁ hx
  have hγ₀1 : γ₀ ≠ 1 := by rintro rfl; rw [map_one] at hγ₀; exact hx1 hγ₀.symm
  have hγ₁1 : γ₁ ≠ 1 := by rintro rfl; rw [map_one] at hγ₁; exact hx1 hγ₁.symm
  obtain ⟨u₀, hu₀, hm₀⟩ := RealizesVia.exists_moved hD₀ h₀ hγ₀1
  obtain ⟨u₁, hu₁, hm₁⟩ := RealizesVia.exists_moved hD₁ h₁ hγ₁1
  rw [hγ₀] at hm₀
  rw [hγ₁] at hm₁
  exact false_of_two_moved htr (fun u hu => hγ₀ ▸ h₀.2.2.2.1 (π₀ γ₀) u hu)
    (fun u hu => hγ₁ ▸ h₁.2.2.2.1 (π₁ γ₁) u hu) hI hu₀ hu₁ hm₀ hm₁

theorem conclusion_of_b42 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) (hG2 : G2NoTransvection)
    (hq : CFSG.IsQuasisimple ↥(conjClosure (Subgroup.zpowers a) G))
    (hts : IsTransvecSec a ⊤ (fixV (conjClosure (Subgroup.zpowers a) G)))
    (hB : B42ModulePair (conjClosure (Subgroup.zpowers a) G) ⊤
      (fixV (conjClosure (Subgroup.zpowers a) G))) : Conclusion G a := by
  classical
  set K := conjClosure (Subgroup.zpowers a) G with hK
  set C := fixV K with hC
  have hKV : commV K = ⊤ := commV_classK h
  have haK : a ∈ K := mem_classK
  have ha1 : a ≠ 1 := h.ne_one
  have ha2 : a ^ 2 = 1 := h.sq_eq_one
  rcases hB with ⟨n, F, _, _, -, π, hπ⟩ | h3 | ⟨n, F, _, _, -, π, hπ⟩ | ⟨n, F, _, _, -, π, hπ⟩ |
    ⟨F, _, _, hF, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨F, _, _, Γ₀, hF4, -, -, -, π, hπ⟩ | h4 | h5 | h4' | h5'
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
    have hF2 : Nat.card F ≤ 2 := card_le_two_of_rankOne hV2 hπ (hγ ▸ hts.1) (hγ ▸ hts.2)
    have hF : Nat.card F = 2 := le_antisymm hF2 (two_le_card_field F)
    have e := MulEquiv.ofBijective π ⟨RealizesVia.injective_of_faithful'
      (FFModel.nat_faithful _) hπ, hπ.1⟩
    have h6 : Nat.card ↥(conjClosure (Subgroup.zpowers a) G) = 6 := by
      rw [← Nat.card_congr e.toEquiv]
      exact card_statedSL_two hF
    exact not_isQuasisimple_of_card_six h6 hq
  ·
    obtain ⟨π, hπ⟩ := exists_zmod_of_transvection hV2 h3.choose_spec haK ha1 htr
    have hC0 := eq_bot_of_natSL (by norm_num) hπ hKV haK ha1 htr
    rw [hC0] at hπ
    exact conclusion_of_natSL h (by norm_num) (by norm_num) hπ
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
    have hF2 : Nat.card F ≤ 2 := card_le_two_of_rankOne hV2 hπ (hγ ▸ hts.1) (hγ ▸ hts.2)
    have hF : Nat.card F = 2 := le_antisymm hF2 (two_le_card_field F)
    have hsp : BinaryNaturalSp4 K ⊤ C 1 := ⟨F, inferInstance, inferInstance, by simp [hF], π, hπ⟩
    obtain ⟨π', hπ'⟩ := asSp4S6 V K ⊤ C hsp
    have e := MulEquiv.ofBijective π' ⟨RealizesVia.injective_of_faithful'
      (symDn_faithful (by norm_num)) hπ', hπ'.1⟩
    exact not_isQuasisimple_of_perm (by norm_num) e.symm hq
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
    have ht := RealizesVia.isTransvecOn hV2 hπ (hγ ▸ hts)
    have hF : Nat.card F = 2 := le_antisymm (card_le_two_of_zornQ ht) (two_le_card_field F)
    exact hG2 F hF γ ht
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
    have ht := RealizesVia.isTransvecOn hV2 hπ (hγ ▸ hts)
    exact hG2 F (by simpa using hF) _ (modelTransvec_zornQ_of_derived ht)
  ·
    exfalso
    exact false_of_alt_transvection hV2 (Or.inl rfl) (MulEquiv.ofBijective π
      ⟨RealizesVia.injective_of_faithful' (altDn_faithful le_rfl) hπ, hπ.1⟩) haK ha2 ha1 htr
  ·
    exfalso
    exact false_of_alt_transvection hV2 (Or.inr (Or.inl rfl)) (MulEquiv.ofBijective π
      ⟨RealizesVia.injective_of_faithful' (altDn_faithful (by norm_num)) hπ, hπ.1⟩) haK ha2 ha1
      htr
  ·
    exfalso
    exact false_of_alt_transvection hV2 (Or.inr (Or.inr rfl)) (MulEquiv.ofBijective π
      ⟨RealizesVia.injective_of_faithful' (altDn_faithful (by norm_num)) hπ, hπ.1⟩) haK ha2 ha1
      htr
  ·
    exfalso
    exact false_of_alt_transvection hV2 (Or.inr (Or.inr rfl)) (MulEquiv.ofBijective π
      ⟨RealizesVia.injective_of_faithful' (a7Four_faithful α) hπ, hπ.1⟩) haK ha2 ha1 htr
  ·
    exfalso
    obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
    have hF2 : Nat.card F ≤ 2 := card_le_two_of_rankOne hV2 hπ (hγ ▸ hts.1) (hγ ▸ hts.2)
    omega
  ·
    obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h4
    have hC0 := eq_bot_of_natSL (by norm_num) hπ hKV haK ha1 htr
    rw [hC0] at hπ
    exact conclusion_of_natSL h (by norm_num) (by norm_num) hπ
  ·
    obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h5
    have hC0 := eq_bot_of_natSL (by norm_num) hπ hKV haK ha1 htr
    rw [hC0] at hπ
    exact conclusion_of_natSL h (by norm_num) le_rfl hπ
  · exact absurd (false_of_extSq_transvection hV2 (Or.inl rfl) h4' haK ha1 ha2 htr) not_false
  · exact absurd (false_of_extSq_transvection hV2 (Or.inr rfl) h5' haK ha1 ha2 htr) not_false

theorem conclusion_of_case1 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) (hG2 : G2NoTransvection)
    (hC : B56Case1 (conjClosure (Subgroup.zpowers a) G)) : Conclusion G a := by
  classical
  set K := conjClosure (Subgroup.zpowers a) G with hK
  obtain ⟨hq, ⟨⟨-, hcases⟩, -⟩, -⟩ := hC
  set L := quasithinGenFitting K with hL
  have hUV : commV L = ⊤ := commV_eq_top_of_fstar h htr hq
  obtain ⟨v, hv⟩ := exists_moved_of_fstar h hq
  have hts : IsTransvecSec a ⊤ (fixV L) := isTransvecSec_of_card_two htr ⟨v, trivial, hv⟩
  have hKV : commV K = ⊤ := commV_classK h
  have haK : a ∈ K := mem_classK
  have ha1 : a ≠ 1 := h.ne_one
  rcases hcases with ⟨-, hB42, hT⟩ | ⟨hKL, n, F, _, _, -, I, π, hind, -, hreal, -⟩ |
    ⟨n, hKL, -, π, U₁, U₂, ⟨-, hU⟩, h₁, h₂⟩ | ⟨hKL, n, hn, k, hk1, hkn, I, π, -, hind, hsup, hreal⟩
  ·
    rw [hUV, inf_top_eq] at hB42
    simp only [hUV, inf_top_eq] at hT
    obtain ⟨T, hTsyl⟩ := exists_isSylowTwoOf K
    rcases hT T hTsyl with hKL | ⟨-, ⟨n, hn5, hn8, hs⟩ | hg2⟩
    ·
      have hq' : CFSG.IsQuasisimple ↥K := by rw [hKL]; exact hq
      rw [← hKL] at hB42 hts
      exact conclusion_of_b42 hV2 h htr hG2 hq' hts hB42
    · exact conclusion_of_sym hV2 h htr hn5 hn8 hs
    ·
      exfalso
      obtain ⟨F, _, _, hF, π, hπ⟩ := hg2
      obtain ⟨γ, hγ⟩ := exists_preimage hπ haK
      exact hG2 F (by simpa using hF) γ (RealizesVia.isTransvecOn hV2 hπ (hγ ▸ hts))
  ·
    exfalso
    have haL : a ∈ L := hKL ▸ haK
    have hI : I 0 ⊓ I 1 ≤ ⊥ := (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)).le_bot
    exact false_of_two_summands (FFModel.nat_faithful _) (FFModel.nat_faithful _) (hreal 0)
      (hreal 1) hI haL ha1 htr
  ·
    exfalso
    have haL : a ∈ L := hKL ▸ haK
    exact false_of_two_summands (FFModel.nat_faithful _) (dualNat_faithful _) h₁ h₂ hU.le
      haL ha1 htr
  ·
    have haL : a ∈ L := hKL ▸ haK
    by_cases hk : k = 1
    · subst hk
      have hI0 : I 0 = ⊤ := by
        rw [← hUV, ← hsup, bot_sup_eq]
        exact (iSup_unique (f := I)).symm
      have hπ := hreal 0
      rw [hI0] at hπ
      have hR : (FFModel.nat (StatedSL n (ZMod 2))).Realizes L ⊤ ⊥ := ⟨π, hπ⟩
      rw [← hKL] at hR
      obtain ⟨π', hπ'⟩ := hR
      rcases hn with rfl | rfl
      · exact conclusion_of_natSL h (by norm_num) (by norm_num) hπ'
      · exact conclusion_of_natSL h (by norm_num) le_rfl hπ'
    · exfalso
      set i₀ : Fin k := ⟨0, by omega⟩
      set i₁ : Fin k := ⟨1, by omega⟩
      have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
      have hI : I i₀ ⊓ I i₁ ≤ ⊥ := by
        rw [← hind i₀]
        refine inf_le_inf_left _ (le_sup_of_le_right ?_)
        exact le_iSup₂_of_le (f := fun (j : Fin k) (_ : j ≠ i₀) => I j) i₁ h01 le_rfl
      exact false_of_two_summands (FFModel.nat_faithful _) (FFModel.nat_faithful _)
        (hreal i₀) (hreal i₁) hI haL ha1 htr

end CFSG.Quasithin.G64
