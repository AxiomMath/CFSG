module

public import CFSG.Quasithin.EmptyFaithful.S1421QA26Img
public import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.Quasithin.EmptyFaithful.R3cSL2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.QA26

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

section Basic

variable {V : Type} [CommGroup V]

@[expose] def IsA7Cover (K : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7))

theorem false_of_epi {K : Subgroup (MulAut V)} (hA7 : IsA7Cover K) {Γ : Type} [Group Γ]
    (hN : NoA7Image Γ) (π : Γ →* ↥K) (hπ : Function.Surjective π) : False :=
  hN _ ((QuotientGroup.mk' (Subgroup.center ↥K)).comp π)
    ((QuotientGroup.mk'_surjective _).comp hπ) hA7

theorem false_of_realizes {K : Subgroup (MulAut V)} {U Z : Subgroup V} (hA7 : IsA7Cover K)
    {D : FFModel} (hN : NoA7Image D.Gam) (h : D.Realizes K U Z) : False := by
  obtain ⟨π, hπ⟩ := h
  exact false_of_epi hA7 hN π hπ.1

theorem noA7Image_slTwoField {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = 2) : NoA7Image ↥(StatedSL d F) := by
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let σ : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hcard
  let m : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin d) F :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
      (Matrix.SpecialLinearGroup.map σ.symm.toRingHom) (by ext A i j; simp) (by ext A i j; simp)
  let e : ↥(StatedSL d F) ≃* ↥(StatedSL d (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL d F).symm.trans
      (m.symm.trans (specialLinearGroupEquivStatedSL d (ZMod 2)))
  exact noA7Image_of_mulEquiv e (noA7Image_slTwo hd)

theorem false_of_binarySL {K : Subgroup (MulAut V)} {U Z : Subgroup V} (hA7 : IsA7Cover K)
    {d a : ℕ} (hN : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ a →
      NoA7Image ↥(StatedSL d F)) (h : BinaryNaturalSL K U Z d a) : False := by
  obtain ⟨F, _, _, hc, hr⟩ := h
  exact false_of_realizes hA7 (hN F hc) hr

theorem false_of_list2 {K : Subgroup (MulAut V)} {U Z : Subgroup V} (hA7 : IsA7Cover K)
    (h : B51NaturalList2 K U Z) : False := by
  rcases h with ⟨n, h⟩ | ⟨n, F, _, _, hc, hr⟩ | ⟨n, F, _, _, hc, hr⟩ | hr | hr |
    ⟨F, _, _, hc, hr⟩ | ⟨F, _, _, hc, hr⟩
  · exact false_of_binarySL hA7 (fun F _ _ hc => noA7Image_sl2 F ⟨n, hc⟩) h
  · exact false_of_realizes hA7 (noA7Image_sp4 F ⟨n, hc⟩) hr
  · exact false_of_realizes hA7 (noA7Image_g2 F ⟨n, hc⟩) hr
  · exact false_of_realizes hA7 (noA7Image_alt (m := 6) (by norm_num)) hr
  · exact false_of_realizes hA7 (noA7Image_alt (m := 8) (by norm_num)) hr
  · exact false_of_realizes hA7 (noA7Image_g2derived F (by simpa using hc)) hr
  · exact false_of_realizes hA7 (noA7Image_sl3 F ⟨1, hc⟩) hr

theorem module_pair_a7 {K : Subgroup (MulAut V)} {U Z : Subgroup V} (hA7 : IsA7Cover K)
    (h : B42ModulePair K U Z) : AlternatingNatural K U Z 7 ∨ A7Four K U Z := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, F, _, _, hc, hr⟩ | ⟨n, F, _, _, hc, hr⟩ |
    ⟨F, _, _, hc, hr⟩ | hr | hr | hr | hr | ⟨F, _, _, Γ₀, hc, -, hHat, -, hr⟩ | h | h | hr | hr
  · exact (false_of_binarySL hA7 (fun F _ _ hc => noA7Image_sl2 F ⟨n, hc⟩) h).elim
  · exact (false_of_binarySL hA7 (fun F _ _ hc => noA7Image_sl3 F ⟨n, hc⟩) h).elim
  · exact (false_of_realizes hA7 (noA7Image_sp4 F ⟨n, hc⟩) hr).elim
  · exact (false_of_realizes hA7 (noA7Image_g2 F ⟨n, hc⟩) hr).elim
  · exact (false_of_realizes hA7 (noA7Image_g2derived F (by simpa using hc)) hr).elim
  · exact (false_of_realizes hA7 (noA7Image_alt (m := 5) (by norm_num)) hr).elim
  · exact (false_of_realizes hA7 (noA7Image_alt (m := 6) (by norm_num)) hr).elim
  · exact Or.inl hr
  · exact Or.inr hr
  · exact (false_of_realizes hA7 (noA7Image_hat hHat) hr).elim
  · exact (false_of_binarySL hA7 (d := 4) (a := 1)
      (fun F _ _ hc => noA7Image_slTwoField (Or.inr (Or.inl rfl)) F (by simpa using hc)) h).elim
  · exact (false_of_binarySL hA7 (d := 5) (a := 1)
      (fun F _ _ hc => noA7Image_slTwoField (Or.inr (Or.inr rfl)) F (by simpa using hc)) h).elim
  · exact (false_of_realizes hA7 (noA7Image_slTwo (d := 4) (Or.inr (Or.inl rfl))) hr).elim
  · exact (false_of_realizes hA7 (noA7Image_slTwo (d := 5) (Or.inr (Or.inr rfl))) hr).elim

end Basic

section Factor

variable {V : Type} [CommGroup V] [Finite V]

open CFSG.Quasithin.InternalSec

omit [Finite V] in
theorem ne_bot_of_quasisimple {K : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K) :
    K ≠ ⊥ := by
  rintro rfl
  exact not_commute_of_isQuasisimple hK fun a ha b hb => by
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

omit [Finite V] in
theorem eq_of_normal_of_simple {K X : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hn : (K.subgroupOf X).Normal) (hK : K ≠ ⊥) [IsSimpleGroup ↥X] : K = X := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf X) with h | h
  · exfalso
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have h1 : (⟨k, hKX hk⟩ : ↥X) ∈ K.subgroupOf X := hk
    rw [h, Subgroup.mem_bot] at h1
    simpa using congrArg Subtype.val h1
  · exact le_antisymm hKX (Subgroup.subgroupOf_eq_top.1 h)

theorem false_of_card_lt {K : Subgroup (MulAut V)} (hA7 : IsA7Cover K)
    (h : Nat.card ↥K < 2520) : False :=
  false_of_epi hA7 (noA7Image_of_not_dvd (Nat.not_dvd_of_pos_of_lt Nat.card_pos h))
    (MonoidHom.id ↥K) Function.surjective_id

theorem notB56Factor_of_a7Cover {K : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K)
    (hA7 : IsA7Cover K) : NotB56Factor K := by
  intro X hKX hXN h
  have hKne : K ≠ ⊥ := ne_bot_of_quasisimple hK
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXN
  have hsmall : Nat.card ↥X < 2520 → False := fun hlt =>
    false_of_card_lt hA7 (lt_of_le_of_lt (Subgroup.card_le_of_le hKX) hlt)
  have hsimple : ∀ {Γ : Type} [Group Γ], IsSimpleGroup Γ → NoA7Image Γ →
      (↥X ≃* Γ) → False := by
    intro Γ _ hS hN e
    have : IsSimpleGroup ↥X := e.isSimpleGroup
    have hKeq : K = X := eq_of_normal_of_simple hKX hKn hKne
    let e' : ↥K ≃* Γ := (MulEquiv.subgroupCongr hKeq).trans e
    exact false_of_epi hA7 hN e'.symm.toMonoidHom e'.symm.surjective
  rcases h with (⟨n, F, _, _, hn1, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, -, hm, hF, ⟨e⟩⟩) | ⟨⟨e⟩⟩ |
    ⟨⟨e⟩⟩ | ⟨n, F, _, _, hF, π, hπ⟩
  · by_cases hn : n = 1
    · subst hn
      refine hsmall ?_
      rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.R3c.card_statedSL_two_pow hF]
      norm_num
    · have hn2 : 2 ≤ n := by omega
      have hchar : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      exact hsimple inferInstance (noA7Image_sl2 F ⟨n, hF⟩) e
  · refine hsmall ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · have : IsSimpleGroup ↥(StatedSL 3 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hm
    exact hsimple inferInstance (noA7Image_sl3 F ⟨m, hF⟩) e
  · refine hsmall ?_
    rw [Nat.card_congr e.toEquiv, card_alt_six]
    norm_num
  · refine hsmall ?_
    have hK2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    have : Finite ↥(StatedSL 3 (ZMod 2)) :=
      Finite.of_equiv _ (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr
      (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv, Alt57.card_sl3_field (ZMod 2), hK2]
    norm_num
  ·
    have hn1 : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial F)
      simp [hF] at this
    by_cases hn : n = 1
    · subst hn
      refine hsmall ?_
      have h6 : Nat.card ↥(StatedSL 2 F) = 6 := by
        rw [CFSG.Quasithin.R3c.card_statedSL_two_pow hF]
        norm_num
      have := Subgroup.card_dvd_of_surjective hπ
      rw [h6] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have hn2 : 2 ≤ n := by omega
      have hchar : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      have : Nontrivial ↥X := by
        have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
        obtain ⟨k, hk⟩ := exists_ne (1 : ↥K)
        exact ⟨⟨⟨k, hKX k.2⟩, 1, fun h =>
          hk (Subtype.ext (congrArg (fun z : ↥X => (z : MulAut V)) h))⟩⟩
      have hinj : Function.Injective π := injective_of_surjective_of_simple π hπ
      exact hsimple inferInstance (noA7Image_sl2 F ⟨n, hF⟩)
        (MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm

end Factor

section Main

variable {V : Type} [CommGroup V] [Finite V]

open CFSG.Quasithin.InternalSec

theorem b56Case1_of_notFactor {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hfac : NotB56Factor K)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56Case1 J := by
  have hJn : J ≤ Subgroup.normalizer (K : Set (MulAut V)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hn x hx k hk, fun hk => by
        have := hn x⁻¹ (J.inv_mem hx) _ hk
        simpa [mul_assoc] using this⟩
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  · exact h1
  · exact (not_le_perm_three hK hKJ e).elim
  · exfalso
    have h₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inl hf₁)
    · exact hfac G₂ h (h₂J.trans hJn) (Or.inl hf₂)
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inr (Or.inl ⟨e₁⟩))
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    have h₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · exact hfac G₁ h (h₁J.trans hJn) (Or.inr (Or.inr (Or.inl ⟨e₁⟩)))
    · refine hfac G₂ h (h₂J.trans hJn) ?_
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hcF, π, hR⟩
      · exact Or.inr (Or.inr (Or.inl ⟨e₂⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, hcF, π, hR.1⟩))

theorem moduleData_of_b51 {J K : Subgroup (MulAut V)} (hB : B51Conclusion J K)
    (hA7 : IsA7Cover K) :
    IsIntDirect (commV K) (fixV K) ⊤ ∧
      (AlternatingNatural K (commV K) ⊥ 7 ∨ A7Four K (commV K) ⊥) := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hB
  have hdir : IsIntDirect (commV K) (fixV K) ⊤ := by
    by_contra hnd
    exact false_of_list2 hA7 (h2.2 hnd).2
  refine ⟨hdir, ?_⟩
  have hZ : fixV K ⊓ commV K = ⊥ := by rw [inf_comm]; exact hdir.2
  obtain ⟨-, hcases⟩ := h1
  rcases hcases with ⟨-, hpair, -⟩ | ⟨-, n, F, _, _, hc, I, π, -, -, hR, -⟩ |
    ⟨n, -, hsum⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hR⟩
  · rw [hZ] at hpair
    exact module_pair_a7 hA7 hpair
  · exact (false_of_epi hA7 (noA7Image_sl3 F ⟨n, hc⟩) π (hR 0).1).elim
  · obtain ⟨hn, π, U₁, U₂, -, hR, -⟩ := hsum
    exact (false_of_epi hA7 (noA7Image_slTwo (d := n) (by omega)) π hR.1).elim
  · exact (false_of_epi hA7 (noA7Image_slTwo (d := n) (by omega)) π (hR ⟨0, hk1⟩).1).elim

theorem a7ModData_of_b56 (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1) {J K : Subgroup (MulAut V)}
    (hJ : J ≠ ⊥) (hb : B53Hyp J) (hKJ : K ≤ J) (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hK : CFSG.IsQuasisimple ↥K) (hA7 : IsA7Cover K) :
    IsIntDirect (commV K) (fixV K) ⊤ ∧
      (AlternatingNatural K (commV K) ⊥ 7 ∨ A7Four K (commV K) ⊥) := by
  have hcases := h56 V hV J hJ hb
  obtain ⟨hE, hB51, -⟩ :=
    b56Case1_of_notFactor hKJ hn hK (notB56Factor_of_a7Cover hK hA7) hcases
  have hF : CFSG.Open.quasithinGenFitting J = K := eq_of_le_quasisimple hKJ hn hK hE
  rw [hF] at hB51
  exact moduleData_of_b51 hB51 hA7

end Main

end CFSG.Quasithin.QA26
