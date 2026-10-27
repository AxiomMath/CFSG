module

public import CFSG.Quasithin.Vol2.Ch8Sec2InspA
public import CFSG.Quasithin.H13.KGFactA314J4
public import CFSG.RankThree.Co2.GoldVariant
import CFSG.Quasithin.Vol2.Ch4Sec3L4314Row
import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
import CFSG.Quasithin.Background.GoldschmidtS146RArith
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.H13.Insp82

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.A5.G3

@[expose] def J4LFamilyCharTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L → B ∈ lFamily T →
    B ≤ L → B ≠ L → IsSporadic .J4 ↥L → CharTwo B

section J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem j4LFamilyCharTwo_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    J4LFamilyCharTwo := by
  intro G _ _ L T B hT hB hBL hBne hL
  have hF : J4Facts := j4Facts
  obtain ⟨e₀⟩ := hL
  obtain ⟨ψ⟩ : Nonempty (↥L ≃* J) := ⟨e₀.trans (seedEquiv hF.mat)⟩
  have hBc : B ∈ cComp (B ⊔ T) := hB
  obtain ⟨hB1, -, hBsub, -⟩ := hBc
  have hXL : B ⊔ T ≤ L := sup_le hBL hT.1
  have hXne : B ⊔ T ≠ L := by
    intro hXL'
    have hsub : IsSubnormal (B.subgroupOf L) ⊤ := by
      have := CFSG.Quasithin.A4.subnormal_subgroupOf L hBsub
      rwa [hXL', Subgroup.subgroupOf_self] at this
    have hJs : IsSimpleGroup J := CFSG.Sporadic.J4.isSimpleGroup_J hF
    have : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ hJs ψ
    rcases KGA314J4.eq_bot_or_top_of_isSubnormal hsub (Or.inr rfl) with h | h
    · apply hB1
      rw [← Subgroup.map_subgroupOf_eq_of_le hBL, h, Subgroup.map_bot]
    · apply hBne
      refine le_antisymm hBL fun l hl => ?_
      have : (⟨l, hl⟩ : ↥L) ∈ B.subgroupOf L := by rw [h]; trivial
      exact this
  have hns : ¬ Group.IsSolvable ↥(B ⊔ T) := CFSG.Quasithin.A312S.not_isSolvable_sup hB
  set Y : Subgroup ↥L := (B ⊔ T).subgroupOf L with hYdef
  let eY : ↥Y ≃* ↥(B ⊔ T) := Subgroup.subgroupOfEquivOfLe hXL
  have hTY : T.subgroupOf L ≤ Y := fun x hx => (le_sup_right : T ≤ B ⊔ T) hx
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hXne
    refine le_antisymm hXL fun l hl => ?_
    have : (⟨l, hl⟩ : ↥L) ∈ Y := by rw [htop]; trivial
    exact this
  have hYns : ¬ Group.IsSolvable ↥Y := fun hs =>
    hns (Group.isSolvable_of_surjective (f := eY.toMonoidHom) eY.surjective)
  have hYc : CharTwo Y := KGA314J4.charTwo_transport (Γ := J) (P := P0)
    (CFSG.Quasithin.J4Loc.isSylowTwoOf_P0 : IsSylowTwoOf P0 ⊤)
    (fun Y' hP hY' hns' => KGA314J4.charTwo_of_overgroup hP hY' hns') ψ
    (KGA314J4.isSylowTwoOf_subgroupOf_top hT) hTY hYne hYns
  have hXc : CharTwo (B ⊔ T) := charTwo_iff_internal.mpr
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2 eY
      (charTwo_iff_internal.mp hYc))
  exact CFSG.Quasithin.A4.charTwo_of_subnormal hBsub hXc

end J4

section Aut

variable {Q : Type} [Group Q] [Finite Q]

theorem card_psl42_dvd :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∣ 20160 := by
  have h1 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∣
      Nat.card (GL (Fin 4) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective _ Matrix.SpecialLinearGroup.toGL_injective
  have h3 : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
    norm_num
  exact h1.trans (h3 ▸ h2)

theorem card_mulAut_dvd {P : Type} [Group P] (hP : IsE2 4 P) : Nat.card (MulAut P) ∣ 20160 := by
  obtain ⟨e⟩ := hP
  set E := Multiplicative (Fin 4 → ZMod 2)
  have hE2 : ∀ v : E, v * v = 1 := fun v => by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    generalize Multiplicative.toAdd v i = x
    revert x
    decide
  have hE : Nat.card E = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  obtain ⟨κ, hκ⟩ := CFSG.RankThree.Co2.GoldVariant.exists_injective_mulAut_psl hE2 hE
  have h1 : Nat.card (MulAut P) = Nat.card (MulAut E) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [h1]
  exact (Subgroup.card_dvd_of_injective κ hκ).trans card_psl42_dvd

omit [Finite Q] in
theorem card_modO2_dvd_of_charTwo {B : Subgroup Q} (hB : CharTwo B)
    (hE : IsE2 4 ↥(CFSG.pCore 2 ↥B)) : Nat.card (ModO2 B) ∣ 20160 := by
  set P : Subgroup ↥B := CFSG.pCore 2 ↥B with hPdef
  have hcomm : ∀ a b : ↥P, a * b = b * a := by
    obtain ⟨e⟩ := hE
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  let φ : ↥B →* MulAut ↥P := MulAut.conjNormal
  have hker : φ.ker = P := by
    apply le_antisymm
    · intro x hx
      have hc : x ∈ Subgroup.centralizer (P : Set ↥B) := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have h1 : φ x ⟨p, hp⟩ = ⟨p, hp⟩ := by
          rw [MonoidHom.mem_ker.mp hx]
          rfl
        have h2 : (φ x ⟨p, hp⟩ : ↥B) = x * p * x⁻¹ := MulAut.conjNormal_apply x ⟨p, hp⟩
        rw [h1] at h2
        have h3 : p * x = x * p * x⁻¹ * x := by rw [← h2]
        rw [h3, inv_mul_cancel_right]
      have hint := charTwo_iff_internal.mp hB
      exact hint hc
    · intro x hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro q
      apply Subtype.ext
      have h2 : (φ x q : ↥B) = x * q * x⁻¹ := MulAut.conjNormal_apply x q
      rw [h2]
      have h4 : x * (q : ↥B) = q * x := congrArg Subtype.val (hcomm ⟨x, hx⟩ q)
      rw [h4, mul_inv_cancel_right]
      rfl
  have h1 : Nat.card (ModO2 B) = Nat.card φ.range :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).toEquiv
  rw [h1]
  exact (Subgroup.card_subgroup_dvd_card φ.range).trans (card_mulAut_dvd hE)

end Aut

section Cocode24

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem isHat_of_a312Case_cocode24 (hM : A314ModelFacts)
    (hJ4 : IsSporadic .J4 ↥L → IsHat (ModO2 B) (alternatingGroup (Fin 6)) → False)
    (hmod : Nat.card (ModO2 B) = 1080) (hO : Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ 4)
    (hcase : A312Case B L) : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  have hcard : Nat.card ↥B = 17280 := by
    rw [card_eq_modO2_mul, hmod, hO]
    norm_num
  have hnotS : IsSimpleGroup ↥B → (∃ a b : ↥B, a * b ≠ b * a) → False := by
    intro _ hnc
    have h1 := pCore_two_eq_bot_of_simple hnc
    rw [h1, Subgroup.card_bot] at hO
    norm_num at hO
  unfold A312Case at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, -⟩ := h
    have h1 := GoldS146R.card_isPSL_two_two hn
    exact (false_of_psl2_two hn.1.2.1 (Or.inr rfl) (h1.symm.trans hmod)).elim
  ·
    obtain ⟨f, hf, -⟩ := h
    have h1 := S146zX.not_three_dvd_card_isSz hf
    rw [hmod] at h1
    exact (h1 (by norm_num)).elim
  ·
    have h1 := Ch4.L4314Row.card_L32 h.1
    omega
  ·
    have h1 := Ch4.L4314Row.card_L42 h.1
    omega
  ·
    rcases h.1 with h1 | h1
    · have := Ch4.L4314Row.card_alt5 h1
      omega
    · have := Ch4.L4314Row.card_L32 h1
      omega
  ·
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := Ch4.L4314Row.card_alt6 h1
      omega
    · have := Ch4.L4314Row.card_hat6 h1
      omega
  ·
    rcases h with ⟨p, hp, hp3, h1, -⟩ | ⟨h1, -⟩
    · have h2 := Ch4.L4314Row.two_mul_card_of_isPSL_two hp (by omega) h1
      rw [hcard] at h2
      exact (false_of_sl2_mul hp (by omega) odd_one (n := 34560) (by omega) (by omega)).elim
    · have := Ch4.L4314Row.card_alt5 h1
      omega
  ·
    rcases h with ⟨s, p, hp, hp3, h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · have h2 := A313.IsSL2.card_eq hp h1
      exact (false_of_sl2_mul hp (by omega) odd_one (n := 17280) (by omega)
        (by rw [mul_one, ← h2, hcard])).elim
    · have := Ch4.L4314Row.card_alt6 h1
      omega
    · have := Ch4.L4314Row.card_hat6 h1
      omega
  ·
    obtain ⟨p, hp, hp3, hext, -⟩ := h
    obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt hext
    rw [card_of_isElemAbelianOfRank hV, A313.IsSL2.card_eq hp hYq, hcard] at hc
    have hp5 : 5 ≤ p := by
      rcases (by omega : p = 4 ∨ 5 ≤ p) with rfl | h5
      · norm_num at hp
      · exact h5
    have h8 : p < 8 := by
      by_contra h7
      have h7' : 8 ≤ p := by omega
      have : 63 ≤ p ^ 2 - 1 := by
        have : 64 ≤ p ^ 2 := by nlinarith
        omega
      have : 8 * 63 * 64 ≤ p * (p ^ 2 - 1) * p ^ 2 := by
        have h1 : 8 * 63 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul h7' this
        have h2 : 64 ≤ p ^ 2 := by nlinarith
        exact Nat.mul_le_mul h1 h2
      omega
    interval_cases p <;> norm_num at hc
  ·
    have := Ch4.L4314Row.card_alt6 h.1
    omega
  ·
    rcases h with ⟨h1 | h1, -⟩ | ⟨-, hL⟩
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt5 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt6 hYq] at hc
      omega
    · exact hL
  ·
    obtain ⟨h1 | h1 | h1 | h1 | h1 | h1 | h1, -⟩ := h
    · obtain ⟨hs, hnc, -⟩ := hM.1 ↥B (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      exact (hnotS hs hnc).elim
    · obtain ⟨hs, hnc, -⟩ := hM.1 ↥B (Or.inr (Or.inr (Or.inl h1)))
      exact (hnotS hs hnc).elim
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt7 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt6 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt5 hYq] at hc
      omega
  ·
    obtain ⟨h1 | h1 | h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L42 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [hV.2, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_hat6 hYq] at hc
      omega
  ·
    have := Ch4.L4314Row.card_alt5 h.1
    omega
  ·
    obtain ⟨h1, -⟩ := h
    obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
    rw [hV.2, Ch4.L4314Row.card_alt5 hYq] at hc
    omega
  ·
    obtain ⟨hL, h1 | h1 | h1 | h1 | h1 | h1⟩ := h
    · obtain ⟨V, _, hV, -, -⟩ := exists_card_of_isExt h1
      have h2 : Nat.card ↥V ∣ Nat.card ↥B := Subgroup.card_subgroup_dvd_card V
      rw [hV.2, hcard] at h2
      norm_num at h2
    · obtain ⟨V, _, hV, -, -⟩ := exists_card_of_isExt h1
      have h2 : Nat.card ↥V ∣ Nat.card ↥B := Subgroup.card_subgroup_dvd_card V
      rw [Ch4.L4314Row.card_isE2 hV, hcard] at h2
      norm_num at h2
    · have := Ch4.L4314Row.card_alt5 h1
      omega
    · exact (hJ4 hL h1).elim
    · have := Ch4.L4314Row.card_L42 h1
      omega
    · have := Ch4.L4314Row.card_L32 h1
      omega
  ·
    obtain ⟨h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      obtain ⟨k, hk⟩ := Ch4.L4314Row.card_isZ4StarExtra2 hV
      rw [hk, Ch4.L4314Row.card_alt5 hYq, hcard] at hc
      have h2 : 2 ^ 2 * 15 * 2 ^ k = 2 ^ (k + 2) * 15 := by ring
      have h3 : (17280 : ℕ) = 2 ^ 7 * 135 := by norm_num
      rw [h2, h3] at hc
      have := Ch4.L4314Row.eq_of_two_pow_mul_eq (by decide) (by decide) hc.symm
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isZ4Cubed hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
  ·
    obtain ⟨h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [hV.2, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_hat6 hYq] at hc
      omega
  ·
    obtain ⟨-, h1, -⟩ := h
    omega

theorem open_isQuasisimple_of {X : Type} [Group X] (h : CFSG.IsQuasisimple X) :
    CFSG.Open.IsQuasisimple X :=
  ⟨h.1.1, h.2.1⟩

end Cocode24

theorem inspCocode24_of (h312 : A312ForSQTKCat) (hM : A314ModelFacts)
    (hJ : J4LFamilyCharTwo) : InspCocode24 := by
  intro Y _ hY T hT K hK B hB hBK hmod hE
  have := hY.finite
  have hO : Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ 4 := Ch4.L4314Row.card_isE2 hE
  obtain ⟨L, hL, hBL, huniq, hcase⟩ := h312 Y hY T hT B hB
  have hLK : K = L := huniq K hK hBK
  subst hLK
  have hBne : B ≠ K := by
    rintro rfl
    rw [pCore_two_eq_bot_of_mem_cComp hY hL, Subgroup.card_bot] at hO
    norm_num at hO
  rcases hcase with h | hc | hc
  · exact (hBne h).elim
  · have hJ4 : IsSporadic .J4 ↥K → IsHat (ModO2 B) (alternatingGroup (Fin 6)) → False := by
      intro hJK _
      have hTK : IsSylowTwoOf (T ⊓ K) K :=
        L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp hL) hT
      have hB' : B ∈ lFamily (T ⊓ K) :=
        cComp_mem_of_le hB le_sup_left (sup_le_sup_left inf_le_left B)
      have hc2 := hJ Y K (T ⊓ K) B hTK hB' hBK hBne hJK
      have hdvd := card_modO2_dvd_of_charTwo hc2 hE
      rw [hmod] at hdvd
      norm_num at hdvd
    obtain ⟨hq, hZ, ⟨e⟩⟩ := isHat_of_a312Case_cocode24 hM hJ4 hmod hO hc
    exact ⟨open_isQuasisimple_of hq, hZ, ⟨e⟩⟩
  · exact (false_of_a312Nonquasi hBK hc (Or.inr (Or.inr (by
      rw [card_eq_modO2_mul, hmod, hO]
      norm_num)))).elim

end CFSG.Quasithin.H13.Insp82
