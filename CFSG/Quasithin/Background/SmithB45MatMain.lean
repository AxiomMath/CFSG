module

public import CFSG.Quasithin.Background.SmithB45MatIrr
public import CFSG.Quasithin.Background.SmithB45MatQ
public import CFSG.Quasithin.Background.SmithB45MatGen
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.Family

namespace B45Mat

variable {V : Type} [CommGroup V] [Finite V]

theorem b4Hyp_facts {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) :
    Nontrivial V ∧ (∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      L ≤ G ∧ G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  refine ⟨?_, Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2, (FFC.b4hyp_data hHyp).1,
    B42L2.le_normalizer_of_b4Hyp hHyp⟩
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
  exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩

noncomputable def cqEquiv {L : Subgroup (MulAut V)} (hZ : Subgroup.center ↥L = ⊥) {S : Type}
    [Group S] (θ : ↥L ≃* S) : CQ L ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans θ)

theorem card_le_of_offender_mem {L : Subgroup (MulAut V)} {S : Type} [Group S] (θ : ↥L ≃* S)
    (hS : ∀ x : S, x * x = 1 → x ≠ 1 →
      ∃ cs : List S, cs.length = 3 ∧
        Subgroup.closure (CFSG.QuasithinUnique.Setup.X1.conjSet cs {x}) = ⊤)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {A : Subgroup (MulAut V)} (hAe : IsElemAbelian2 A)
    (hAV : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A)) {r : ℕ}
    (hr : Nat.card A ≤ 2 ^ r) {b : MulAut V} (hbA : b ∈ A) (hbL : b ∈ L) (hb1 : b ≠ 1) :
    Nat.card V ≤ 2 ^ (6 * r) := by
  have hb2 : b * b = 1 := by simpa [sq] using hAe.2 b hbA
  have h3 := card_le_index_pow_three θ hS hirr hbL hb2 hb1
  have h1 : (fixV (Subgroup.zpowers b)).index ≤ (fixV A).index :=
    Subgroup.index_antitone (CFSG.QuasithinUnique.Setup.X1.fixV_anti
      ((Subgroup.zpowers_le).2 hbA))
  have h2 := B45Exc.index_le_sq_of_offender2 A hAV
  calc Nat.card V ≤ (fixV (Subgroup.zpowers b)).index ^ 3 := h3
    _ ≤ (Nat.card A ^ 2) ^ 3 := Nat.pow_le_pow_left (h1.trans h2) 3
    _ ≤ ((2 ^ r) ^ 2) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hr 2) 3
    _ = 2 ^ (6 * r) := by rw [← pow_mul, ← pow_mul]; ring_nf

theorem exists_ne_one_of_two_le {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (h : 2 ≤ Nat.card H) : ∃ x ∈ H, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hcon
  rw [this, Subgroup.card_bot] at h
  omega

end B45Mat

open B45Mat

theorem asB45M24_of_smallIrr
    (hIrr : MathieuSmallIrr24) : AsB45M24 := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S24 := θ
  obtain ⟨hnt, hirr, hLG, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have e := cqEquiv hZ θ'
  have hAL : A ≤ L := le_of_autInner hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
    (autInner_of_card_le m24_center_eq_bot' m24_mulAut_card)
  have hcardA : Nat.card A ≤ 2 ^ 6 :=
    card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m24_rank_le
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
  have hV36 : Nat.card V ≤ 2 ^ 36 := card_le_of_offender_mem θ' m24_gen3 hirr
    hA.isElemAbelian2 hAV hcardA hbA (hAL hbA) (fun h => hb1 (Subtype.ext h))
  have hLG' : IsOver L G := ⟨hLG, hGN⟩
  left
  iterate 10 right
  rcases hIrr V hW L ⟨θ⟩ hirr hV36 with hc | hc
  · exact ⟨Or.inr (Or.inr (Or.inr hc)), two_lt_qOf_code24 hLG' hc⟩
  · exact ⟨Or.inr (Or.inr (Or.inl hc)), two_lt_qOf_cocode24 hLG' hc⟩

theorem asB45M23_of_smallIrr
    (hIrr : MathieuSmallIrr23) : AsB45M23 := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S23 := θ
  obtain ⟨hnt, hirr, hLG, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have e := cqEquiv hZ θ'
  have hAL : A ≤ L := le_of_autInner hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
    m23_autInner
  have hcardA : Nat.card A ≤ 2 ^ 4 :=
    card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m23_rank_le
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
  have hV24 : Nat.card V ≤ 2 ^ 24 := card_le_of_offender_mem θ' m23_gen3 hirr
    hA.isElemAbelian2 hAV hcardA hbA (hAL hbA) (fun h => hb1 (Subtype.ext h))
  have hLG' : IsOver L G := ⟨hLG, hGN⟩
  left
  iterate 10 right
  rcases hIrr V hW L ⟨θ⟩ hirr hV24 with hc | hc
  · exact ⟨Or.inr (Or.inl hc), two_lt_qOf_code23 hLG' hc⟩
  · exact ⟨Or.inl hc, two_lt_qOf_cocode23 hLG' hc⟩

theorem asB45M22_of_smallIrr
    (hIrr : MathieuSmallIrr22) : AsB45M22 := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S22 := θ
  obtain ⟨hnt, hirr, hLG, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have e := cqEquiv hZ θ'
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hV30 : Nat.card V ≤ 2 ^ 30 := by
    rcases out2_dichotomy_gen hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
      m22_center_eq_bot' m22_mulAut_card (k := 3 + 1) (p := 11) (by norm_num)
      (fun ψ hψ hψ2 => m22_outer_gen ψ hψ2 hψ) with hAL | ⟨hdisp, hcardE⟩
    · have hcardA : Nat.card A ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m22_rank_le
      obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
      have := card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hbA
        (hAL hbA) (fun h => hb1 (Subtype.ext h))
      calc Nat.card V ≤ 2 ^ (6 * 4) := this
        _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [orderOf_two_zmod_11] at hdisp
      have hE0el : IsElemAbelian2 (A ⊓ L) :=
        ⟨fun a ha b hb => hA.isElemAbelian2.1 a ha.1 b hb.1, fun a ha => hA.isElemAbelian2.2 a ha.1⟩
      have hE0card : Nat.card ↥(A ⊓ L) ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' inf_le_right hE0el e m22_rank_le
      have hA4 : 4 ≤ Nat.card A := by
        by_contra hlt
        push Not at hlt
        have hc := B45Mat.card_eq_two_pow_rk hA.isElemAbelian2
        have hA2 : Nat.card A ≤ 2 := by
          rw [hc] at hlt ⊢
          have : rk ↥A < 2 := by
            by_contra h
            push Not at h
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
            omega
          calc 2 ^ rk ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        have h1 : (fixV A).index ≤ 2 ^ 2 := hAidx.trans (Nat.pow_le_pow_left hA2 2)
        have h2 : (fixV A).index ^ (3 + 1) ≤ (2 ^ 2) ^ (3 + 1) := Nat.pow_le_pow_left h1 _
        have h3 := hdisp.trans h2
        norm_num at h3
      have hE02 : 2 ≤ Nat.card ↥(A ⊓ L) := by omega
      obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_two_le hE02
      have hcardA : Nat.card A ≤ 2 ^ 5 := by
        calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hcardE
          _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul le_rfl hE0card
          _ = 2 ^ 5 := by norm_num
      exact card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hb.1 hb.2 hb1
  have hLG' : IsOver L G := ⟨hLG, hGN⟩
  left
  iterate 8 right
  rcases hIrr V hW L ⟨θ⟩ hirr hV30 with hc | hc
  · exact Or.inr (Or.inl ⟨hc, two_le_qOf_code22 hLG' hc⟩)
  · exact Or.inl ⟨hc, two_lt_qOf_cocode22 hLG' hc⟩

theorem asB45M12_of_smallIrr
    (hIrr : MathieuSmallIrr12) : AsB45M12 := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S12 := θ
  obtain ⟨hnt, hirr, hLG, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have e := cqEquiv hZ θ'
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hV24 : Nat.card V ≤ 2 ^ 24 := by
    rcases out2_dichotomy hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
      m12_center_eq_bot' m12_mulAut_card (r := 3) (p := 11) (by norm_num) m12_rank_le
      m12_outer_dihedral with hAL | ⟨hdisp, hcardA⟩
    · have hcardA : Nat.card A ≤ 2 ^ 3 :=
        card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m12_rank_le
      obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
      have := card_le_of_offender_mem θ' m12_gen3 hirr hA.isElemAbelian2 hAV hcardA hbA
        (hAL hbA) (fun h => hb1 (Subtype.ext h))
      calc Nat.card V ≤ 2 ^ (6 * 3) := this
        _ ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [orderOf_two_zmod_11] at hdisp
      have hE0el : IsElemAbelian2 (A ⊓ L) :=
        ⟨fun a ha b hb => hA.isElemAbelian2.1 a ha.1 b hb.1, fun a ha => hA.isElemAbelian2.2 a ha.1⟩
      have hA4 : 4 ≤ Nat.card A := by
        by_contra hlt
        push Not at hlt
        have h1 : (fixV A).index ≤ 3 ^ 2 :=
          hAidx.trans (Nat.pow_le_pow_left (by omega) 2)
        have h2 : (fixV A).index ^ 2 ≤ (3 ^ 2) ^ 2 := Nat.pow_le_pow_left h1 _
        have h3 := hdisp.trans h2
        norm_num at h3
      have hcardE := card_le_two_mul_inf hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2
        e m12_center_eq_bot' m12_mulAut_card
      have hE02 : 2 ≤ Nat.card ↥(A ⊓ L) := by omega
      obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_two_le hE02
      exact card_le_of_offender_mem θ' m12_gen3 hirr hA.isElemAbelian2 hAV hcardA hb.1 hb.2 hb1
  have hLG' : IsOver L G := ⟨hLG, hGN⟩
  left
  iterate 6 right
  exact Or.inl ⟨hIrr V hW L ⟨θ⟩ hirr hV24, two_lt_qOf_m12Ten hLG' (hIrr V hW L ⟨θ⟩ hirr hV24)⟩

end CFSG.Quasithin
