module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def AsB42Half : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → qhatOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ) →
      (∃ n, BinaryNaturalSL L ⊤ ⊥ 3 n ∧ qhatOf G = ((1 / 2 : ℚ) : WithTop ℚ)) ∨
        BinaryNaturalSL L ⊤ ⊥ 4 1 ∨ BinaryNaturalSL L ⊤ ⊥ 5 1

section C1

variable {V : Type} [CommGroup V] [Finite V]

theorem weight_le_iff (hV : ∀ v : V, v ^ 2 = 1) {A B : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) (hB : IsElemAbelian2 B) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B) ↔
      rk A + rkIdx (fixV B) ≤ rk B + rkIdx (fixV A) := by
  rw [B1.card_elemAbelian hA, B1.card_elemAbelian hB, card_eq_two_pow hV (fixV A),
    card_eq_two_pow hV (fixV B), ← pow_add, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  have h1 := rk_add_rkIdx (fixV A)
  have h2 := rk_add_rkIdx (fixV B)
  omega

theorem ratio_aux {a b xA xB : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) (hxA : xA ≤ a)
    (hw : a + xB ≤ b + xA) : (xB : ℚ) / b ≤ (xA : ℚ) / a := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have ha' : (0 : ℚ) < a := by exact_mod_cast (hb.trans hba)
  rw [div_le_div_iff₀ hb' ha']
  have h1 : (a : ℚ) + xB ≤ b + xA := by exact_mod_cast hw
  have h2 : (b : ℚ) ≤ a := by exact_mod_cast hba
  have h3 : (xA : ℚ) ≤ a := by exact_mod_cast hxA
  have h4 : (0 : ℚ) ≤ xB := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem exists_quadratic_below_ratio (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : IsA2 G A) (h1 : rAV A ≤ 1) :
    ∃ F : Subgroup (MulAut V), F ≤ A ∧ IsFFStarOffender G F ∧ IsQuadratic F ∧ rAV F ≤ rAV A := by
  have h0 : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := (rAV_le_one_iff hV hA).1 h1
  obtain ⟨B, hBA, hB, hBw⟩ := B1.exists_offender_below hA (Nat.card A * Nat.card (fixV A) -
    Nat.card V) (by omega)
  have hBw' : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B) := by omega
  obtain ⟨F, hFB, hF, hFq, hFw, -, -⟩ := exists_quadratic_offender_le hV hB
  have hFA : F ≤ A := hFB.trans hBA
  refine ⟨F, hFA, hF, hFq, ?_⟩
  have hF2 : IsA2 G F := hF.isA2
  have hw : rk A + rkIdx (fixV F) ≤ rk F + rkIdx (fixV A) :=
    (weight_le_iff hV hA.2.2 hF2.2.2).1 (by rw [hFw]; exact hBw')
  have hxA : rkIdx (fixV A) ≤ rk A := (B1.card_le_iff hV hA.2.2).1 h0
  unfold rAV
  exact ratio_aux hF2.rk_pos (rk_mono hFA) hxA hw

theorem qOf_le_qhatOf_of_le_one (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (h : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)) : qOf G ≤ qhatOf G := by
  have hne : qhatOf G ≠ ⊤ := fun h' => by rw [h'] at h; exact absurd h (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr]
  have hr1 : r ≤ 1 := by
    rw [← hr] at h
    exact_mod_cast h
  obtain ⟨A₀, hA₀, -, hA₀r⟩ := kq_le_iff.1 (show kq G 3 ≤ (r : WithTop ℚ) from hr ▸ le_rfl)
  obtain ⟨F, -, hF, hFq, hFr⟩ := exists_quadratic_below_ratio hV hA₀ (hA₀r.trans hr1)
  exact (qOf_le_iff).2 ⟨F, hF.isA2, hFq, hFr.trans hA₀r⟩

theorem qhatOf_eq_qOf_of_le_one (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (h : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)) : qhatOf G = qOf G :=
  le_antisymm (qhatOf_le_qOf G) (qOf_le_qhatOf_of_le_one hV h)

theorem asB42Half_of_asB42 (hB42 : AsB42) : AsB42Half := by
  intro V _ _ hV G L hHyp hq
  have hq1 : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := hq.trans (by exact_mod_cast (by norm_num))
  obtain ⟨A₀, hA₀, -, hr⟩ := kq_le_iff.1 hq
  obtain ⟨F, -, hF, hFq, hrF⟩ := exists_quadratic_below_ratio hV hA₀ (hr.trans (by norm_num))
  have hqF : qOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ) := qOf_le_iff.2 ⟨F, hF.isA2, hFq, hrF.trans hr⟩
  have hnot : ∀ c : ℚ, 1 / 2 < c → qOf G = (c : WithTop ℚ) → False := fun c hc h => by
    rw [h] at hqF
    exact absurd (WithTop.coe_le_coe.1 hqF) (not_le.2 hc)
  have heq := qhatOf_eq_qOf_of_le_one hV hq1
  rcases hB42 V hV G L hHyp F hF with h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2.2 (fun h' => hnot 1 (by norm_num) h')
  · exact Or.inl (by
      obtain ⟨-, ⟨n, hn⟩, hq2⟩ := h
      exact ⟨n, hn, heq.trans hq2⟩)
  · exact absurd h.2 (fun h' => hnot (2 / 3) (by norm_num) h')
  · exact absurd h.2 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · obtain ⟨-, n, hn, hnat, -⟩ := h
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hnat)
    · exact Or.inr (Or.inr hnat)
  · rcases h.2 with h' | h'
    · exact absurd h'.2.2.2 (fun h'' => hnot 1 (by norm_num) h'')
    · exact absurd h'.2.2 (fun h'' => hnot (3 / 4) (by norm_num) h'')
  · exact absurd h.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')

end C1

end CFSG.Quasithin
