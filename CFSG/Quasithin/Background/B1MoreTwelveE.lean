module

public import CFSG.Quasithin.Background.B1MoreTwelveD
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B1MoreTen
public import CFSG.Quasithin.Background.B1MoreTwelveC
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section Blocks

variable {V : Type*} [CommGroup V] [Finite V] {T K : Subgroup (MulAut V)}

local notation "𝐔" => fixV (pCoreOf 2 (T ⊔ K))

theorem TwelveHyp.autSub_ffJ_le (h : TwelveHyp T K) :
    autSub (ffJ T) 𝐔 ≤ ffJ (autSub (T ⊔ K) 𝐔) := by
  refine autSub_le_of_le_preimageAut (H₀ := T ⊔ K) ?_
  unfold ffJ
  refine iSup₂_le fun A hA g hgA => ?_
  have hAH : A ≤ T ⊔ K := hA.1.trans le_sup_left
  have hgst : g ∈ stabSub 𝐔 := h.le_stabSub (hAH hgA)
  refine mem_preimageAut.2 ⟨hAH hgA, hgst, ?_⟩
  by_cases hnt : A ≤ centSub 𝐔
  · have : resHom 𝐔 ⟨g, hgst⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_resHom, Subgroup.mem_subgroupOf]
      exact hnt hgA
    rw [this]
    exact Subgroup.one_mem _
  · have hAU : ∀ a ∈ A, ∀ w ∈ 𝐔, a w ∈ 𝐔 := fun a ha w hw =>
      (mem_stabSub.1 (h.le_stabSub (hAH ha)) w).2 hw
    have hoff := isFFStarOffender_autSub (H := T ⊔ K) (A := A) (U := 𝐔)
      ⟨hAH, hA.2.1, hA.2.2.1, hA.2.2.2⟩ hAU hnt
    exact B6.le_ffJ hoff (mem_autSub.2 ⟨⟨g, hgst⟩, hgA, rfl⟩)

theorem TwelveHyp.autSub_le_ffJ (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ∈ conjSetUnder T K) : autSub K' 𝐔 ≤ ffJ (autSub (T ⊔ K) 𝐔) := by
  have hK'0 := le_conjClosure_of_mem_conjSetUnder hK'
  have hK'U : K' ≤ stabSub 𝐔 := hK'0.trans (conjClosure_le_sup.trans h.le_stabSub)
  have hJU : ffJ T ≤ stabSub 𝐔 := (B6.ffJ_le T).trans (le_sup_left.trans h.le_stabSub)
  have hcomm : ⁅autSub K' 𝐔, autSub (ffJ T) 𝐔⁆ = autSub K' 𝐔 :=
    commutator_autSub_eq hK'U hJU (h.comm_of_mem hK')
  calc autSub K' 𝐔 = ⁅autSub K' 𝐔, autSub (ffJ T) 𝐔⁆ := hcomm.symm
    _ ≤ ffJ (autSub (T ⊔ K) 𝐔) := by
      rw [Subgroup.commutator_le]
      intro a ha j hj
      have haX : a ∈ autSub (T ⊔ K) 𝐔 := autSub_mono (hK'0.trans conjClosure_le_sup) 𝐔 ha
      have hjJ : j ∈ ffJ (autSub (T ⊔ K) 𝐔) := h.autSub_ffJ_le hj
      have h1 : a * j * a⁻¹ ∈ ffJ (autSub (T ⊔ K) 𝐔) :=
        (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ haX) j).mp hjJ
      exact (ffJ _).mul_mem h1 ((ffJ _).inv_mem hjJ)

theorem TwelveHyp.noncomm_resHom (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ∈ conjSetUnder T K) {a k : MulAut V} (ha : a ∈ ffJ T) (hk : k ∈ K')
    (has : a ∈ stabSub 𝐔) (hks : k ∈ stabSub 𝐔) (hne : a * k ≠ k * a) :
    resHom 𝐔 ⟨a, has⟩ * resHom 𝐔 ⟨k, hks⟩ ≠ resHom 𝐔 ⟨k, hks⟩ * resHom 𝐔 ⟨a, has⟩ := by
  intro heq
  apply hne
  have hn : a * k * a⁻¹ ∈ K' := conj_mem_of_commutator_eq (h.comm_of_mem hK') ha hk
  have hc : ⁅a, k⁆ ∈ conjClosure K T := by
    have e : ⁅a, k⁆ = (a * k * a⁻¹) * k⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (conjClosure K T).mul_mem (le_conjClosure_of_mem_conjSetUnder hK' hn)
      ((conjClosure K T).inv_mem (le_conjClosure_of_mem_conjSetUnder hK' hk))
  have hcs : ⁅a, k⁆ ∈ stabSub 𝐔 :=
    (stabSub 𝐔).mul_mem ((stabSub 𝐔).mul_mem ((stabSub 𝐔).mul_mem has hks)
      ((stabSub 𝐔).inv_mem has)) ((stabSub 𝐔).inv_mem hks)
  have h1 : resHom 𝐔 ⟨⁅a, k⁆, hcs⟩ = 1 := by
    have e : resHom 𝐔 ⟨⁅a, k⁆, hcs⟩ = ⁅resHom 𝐔 ⟨a, has⟩, resHom 𝐔 ⟨k, hks⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [e, commutatorElement_eq_one_iff_mul_comm]
    exact heq
  have h2 : ⁅a, k⁆ ∈ centSub 𝐔 := by
    have : (⟨⁅a, k⁆, hcs⟩ : stabSub 𝐔) ∈ (resHom 𝐔).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at this
    exact this
  have h3 := h.eq_one_of_mem_centSub hc h2
  have h4 : a * k = k * a := (commutatorElement_eq_one_iff_mul_comm.1 h3)
  exact h4


theorem TwelveHyp.exists_block (h : TwelveHyp T K)
    {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hb : IsTransvectionBlocks (ffJ (autSub (T ⊔ K) 𝐔)) 𝓗)
    (hoff : ∀ A : Subgroup (MulAut ↥𝐔), IsFFStarOffender (autSub (T ⊔ K) 𝐔) A →
      ∃ a : Subgroup (MulAut ↥𝐔) → Subgroup (MulAut ↥𝐔),
        (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
          (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H)
    {K' : Subgroup (MulAut V)} (hK' : K' ∈ conjSetUnder T K) :
    ∃ G ∈ 𝓗, autSub K' 𝐔 = oddCoreOfSub G ∧
      ∃ s ∈ G, s ∈ autSub (ffJ T) 𝐔 ∧ s ∉ oddCoreOfSub G := by
  classical
  have hK'0 := le_conjClosure_of_mem_conjSetUnder hK'
  have hK'3 := h.card_of_mem hK'
  have hcommK' := h.comm_of_mem hK'
  have hHst := h.le_stabSub
  have hK'H : K' ≤ T ⊔ K := hK'0.trans conjClosure_le_sup
  obtain ⟨A, hA, a, haA, k, hkK, hak⟩ :
      ∃ A, IsFFStarOffender T A ∧ ∃ a ∈ A, ∃ k ∈ K', a * k ≠ k * a := by
    by_contra hcon
    push Not at hcon
    have hle : ffJ T ≤ Subgroup.centralizer (K' : Set (MulAut V)) := by
      unfold ffJ
      refine iSup₂_le fun A hA a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcon A hA a ha k hk).symm
    have hbot : ⁅K', ffJ T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    rw [hcommK'] at hbot
    rw [hbot, Subgroup.card_bot] at hK'3
    omega
  have hAH : A ≤ T ⊔ K := hA.1.trans le_sup_left
  have hAU : ∀ b ∈ A, ∀ w ∈ 𝐔, b w ∈ 𝐔 := fun b hb w hw =>
    (mem_stabSub.1 (hHst (hAH hb)) w).2 hw
  have hnt : ¬ A ≤ centSub 𝐔 := by
    intro hle
    have hAQ : a ∈ pCoreOf 2 (T ⊔ K) := by
      rw [← h.ker_eq]
      exact ⟨hAH haA, hle haA⟩
    exact hak (commute_conjClosure_pCoreOf h.card h.sub k (hK'0 hkK) a hAQ).symm
  have hAoff : IsFFStarOffender (autSub (T ⊔ K) 𝐔) (autSub A 𝐔) :=
    isFFStarOffender_autSub ⟨hAH, hA.2.1, hA.2.2.1, hA.2.2.2⟩ hAU hnt
  obtain ⟨af, haf, -, hAeq⟩ := hoff _ hAoff
  have hex : ∃ G ∈ 𝓗, ∃ s ∈ af G, ∃ k' ∈ autSub K' 𝐔, s * k' ≠ k' * s := by
    by_contra hcon
    push Not at hcon
    have hle : autSub A 𝐔 ≤ Subgroup.centralizer (autSub K' 𝐔 : Set (MulAut ↥𝐔)) := by
      rw [hAeq]
      refine iSup₂_le fun G hG s hs => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      exact (hcon G hG s hs k' hk').symm
    have has : a ∈ stabSub 𝐔 := hHst (hAH haA)
    have hks : k ∈ stabSub 𝐔 := hHst (hK'H hkK)
    have haA' : resHom 𝐔 ⟨a, has⟩ ∈ autSub A 𝐔 := mem_autSub.2 ⟨⟨a, has⟩, haA, rfl⟩
    have hkK' : resHom 𝐔 ⟨k, hks⟩ ∈ autSub K' 𝐔 := mem_autSub.2 ⟨⟨k, hks⟩, hkK, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hle haA') _ hkK'
    exact h.noncomm_resHom hK' (B6.le_ffJ hA haA) hkK has hks hak this.symm
  obtain ⟨G₀, hG₀, s, hsa, k', hk', hsk'⟩ := hex
  have hsG₀ : s ∈ G₀ := by
    rcases haf G₀ hG₀ with h0 | hsyl
    · rw [h0, Subgroup.mem_bot] at hsa
      subst hsa
      exact absurd (by simp) hsk'
    · exact hsyl.1 hsa
  have hsA : s ∈ autSub A 𝐔 := by
    rw [hAeq]
    exact Subgroup.mem_iSup_of_mem G₀ (Subgroup.mem_iSup_of_mem hG₀ hsa)
  have hsJ : s ∈ autSub (ffJ T) 𝐔 := autSub_mono (B6.le_ffJ hA) 𝐔 hsA
  have hnorm : ∀ x ∈ autSub K' 𝐔, s * x * s⁻¹ ∈ autSub K' 𝐔 := fun x hx =>
    autSub_conj_mem (X := ffJ T) (Y := K')
      (fun y hy z hz => conj_mem_of_commutator_eq hcommK' hy hz) hsJ hx
  have hKeq : autSub K' 𝐔 = oddCoreOfSub G₀ :=
    hb.eq_oddCoreOfSub_of_inverted hG₀ (by rw [h.card_autSub hK'0, hK'3])
      (h.autSub_le_ffJ hK') hsG₀ hnorm ⟨k', hk', hsk'⟩
  refine ⟨G₀, hG₀, hKeq, s, hsG₀, hsJ, fun hsO => ?_⟩
  obtain ⟨-, hs3⟩ := (hb.mem_oddCoreOfSub_iff_of_mem hG₀).1 hsO
  have hs2 : s ^ 2 = 1 := hAoff.2.2.1.2 s hsA
  have hs1 : s = 1 := by
    calc s = s ^ 3 * (s ^ 2)⁻¹ := by group
      _ = 1 := by rw [hs3, hs2]; group
  subst hs1
  exact hsk' (by simp)

theorem TwelveHyp.exists_blockOf (h : TwelveHyp T K)
    {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hb : IsTransvectionBlocks (ffJ (autSub (T ⊔ K) 𝐔)) 𝓗)
    (hoff : ∀ A : Subgroup (MulAut ↥𝐔), IsFFStarOffender (autSub (T ⊔ K) 𝐔) A →
      ∃ a : Subgroup (MulAut ↥𝐔) → Subgroup (MulAut ↥𝐔),
        (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
          (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H)
    {K' : Subgroup (MulAut V)} (hK' : K' ∈ conjSetUnder T K) :
    blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ∈ 𝓗 ∧
      autSub K' 𝐔 = oddCoreOfSub (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔)) ∧
      blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ≤ autSub (twelveM T K) 𝐔 := by
  obtain ⟨G, hG, hKeq, s, hsG, hsJ, hsO⟩ := h.exists_block hb hoff hK'
  have hV' : ∀ w : ↥𝐔, w ^ 2 = 1 := B1.sq_eq_one_sub h.sq 𝐔
  have hblk : blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) = G := by
    rw [hKeq]
    exact hb.blockOf_oddCoreOfSub hV' hG
  rw [hblk]
  refine ⟨hG, hKeq, ?_⟩
  have hsup : oddCoreOfSub G ⊔ Subgroup.zpowers s = G :=
    sup_zpowers_eq_of_card_six (hb.card_eq G hG) (oddCoreOfSub_le G)
      (hb.card_oddCoreOfSub_of_mem hG) hsG hsO
  rw [← hsup]
  refine sup_le ?_ (Subgroup.zpowers_le.2 (autSub_mono (le_sup_left : ffJ T ≤ twelveM T K) 𝐔 hsJ))
  rw [← hKeq]
  exact autSub_mono ((le_conjClosure_of_mem_conjSetUnder hK').trans
    (le_sup_right : conjClosure K T ≤ twelveM T K)) 𝐔

end Blocks

end B1Red

end CFSG.Quasithin
