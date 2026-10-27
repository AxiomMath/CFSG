module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2TwoL52
public import CFSG.Sporadic.Schreier.TitsInner
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin.He4 (NoInvCommNine)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem exists_E9_tits :
    ∃ E : Subgroup titsD, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := titsD_nontrivial
  obtain ⟨E, Γ, -, hΓ, hY⟩ := CFSG.AGLEmbeddingD2.coreGenerationOf_tits
  obtain ⟨g, hg⟩ : Γ.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [Subgroup.closure_empty] at hΓ
    exact bot_ne_top hΓ
  obtain ⟨Y, -, hY2, -⟩ := hY g hg
  obtain ⟨F, -, hF, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hY2
  exact ⟨F, hF, hcard⟩


theorem mem_inner_of_pow_three_tits {α : MulAut titsD} (hα : α ^ 3 = 1) : α ∈ inner titsD := by
  have h3 : orderOf (QuotientGroup.mk α : Outer titsD) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk α : Outer titsD) ∣ 2 :=
    card_outer_titsD ▸ orderOf_dvd_natCard _
  have h1 : orderOf (QuotientGroup.mk α : Outer titsD) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num) h3 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem noInvCommNine_tits : NoInvCommNine titsD := by
  intro P hP t ht hc
  by_contra hne
  have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) hne
  have hle : P ≤ Subgroup.centralizer {t} := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc p hp)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hP] at hdvd
  have hconj : ∀ c : titsD, IsConj c t →
      Nat.card (Subgroup.centralizer {t}) = Nat.card (Subgroup.centralizer {c}) := by
    intro c h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg, ← map_conj_centralizer g c, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rcases titsD_involution_conj t h2 with h | h
  · rw [hconj _ h, card_centralizer_titsZD] at hdvd
    norm_num at hdvd
  · rw [hconj _ h, titsD_centralizer_t.2.1] at hdvd
    norm_num at hdvd

theorem false_of_autConf_tits {ν : MulAut titsD} {Lb Pb : Subgroup (MulAut titsD)}
    (h : AutConf titsD ν Lb Pb) (hP : Nat.card Pb = 9) : False :=
  false_of_autConf_of_noInvCommNine titsD_center noInvCommNine_tits h
    (titsD_mem_inner_of_sq_eq_one h.sq) (fun p hp => mem_inner_of_pow_three_tits (h.elem.2 p hp))
    hP

theorem not_tits {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) : ¬ ReeTitsModel ↥K .Tits 2 1 :=
  fun hK => by
    have := hQ.finite
    obtain ⟨e⟩ := titsModelEquiv ↥K 2 1 hK
    obtain ⟨E, hE, hE9⟩ := exists_E9_tits
    exact false_of_autConf_tits (h.autConf.map e) (h.card_map_rhoP_eq_nine hQ e
      (fun z hz => by rwa [titsD_center, Subgroup.mem_bot] at hz) hE hE9)

end CFSG.Quasithin.H13.S126C
