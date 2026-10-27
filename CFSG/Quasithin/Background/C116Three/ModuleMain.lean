module

public import CFSG.Quasithin.Background.C116Three.CasesFalse
public import CFSG.Quasithin.Background.C116Three.Case3Shape
public import CFSG.Quasithin.Background.C116Three.Case5Shape
public import CFSG.Quasithin.Background.C116Three.L3Branch
public import CFSG.Quasithin.EmptyFaithful.R3c23NatSL2
public import CFSG.Quasithin.EmptyFaithful.R3c23NatSym
public import CFSG.Quasithin.EmptyFaithful.R3c23PairB2

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem l2Branch (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ Q : Subgroup (MulAut V)} {τ : MulAut V}
    (P : PairHyp X L₁ L₂ τ) (h : TypeTwo X L₁ L₂) (𝒜 : Set (Subgroup (MulAut V)))
    (hQ2 : IsPGroup 2 Q) (hQJ : Q ≤ ffJ X) (hA : ∀ A ∈ 𝒜, IsFFStarOffender X A)
    (hAQ : ∀ A ∈ 𝒜, A ≤ Q) : ∃ w : V, w ∉ fixV L₁ ∧ w ∈ fixV L₂ ∧ ∀ A ∈ 𝒜, w ∈ fixV A := by
  obtain ⟨h2, hK⟩ := h
  have hPO := pairOutput_of_twoB56Gen sl2PieceFacts sym5PieceFacts P.conj P.q₁ hK h2
  obtain ⟨G₁, G₂, W₁, W₂, C, PD, N₁, N₂, hX, hL₁, hL₂, hne, hfree⟩ := hPO
  obtain ⟨w, -, hwL₁, hwL₂, hwA⟩ :=
    exists_fixed_vector hV PD N₁ N₂ hX hL₂ hne hfree 𝒜 hA hQ2 hAQ (hQJ.trans hX)
  exact ⟨w, hwL₁, hwL₂, hwA⟩

theorem case5Branch (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ Q : Subgroup (MulAut V)}
    (h : Case5Out X L₁ L₂) (𝒜 : Set (Subgroup (MulAut V))) (hQ2 : IsPGroup 2 Q) (hQJ : Q ≤ ffJ X)
    (hAQ : ∀ A ∈ 𝒜, A ≤ Q) : ∃ w : V, w ∉ fixV L₁ ∧ w ∈ fixV L₂ ∧ ∀ A ∈ 𝒜, w ∈ fixV A := by
  obtain ⟨G₁, G₂, hJ, -, hcomm, rfl, rfl, -, -, htriv, hcard, hfree⟩ := h
  have hne : ∃ w ∈ commV L₁, w ∉ (⊥ : Subgroup V) := by
    by_contra hcon
    push Not at hcon
    have hb : commV L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun w hw => by simpa using hcon w hw
    rw [hb, Subgroup.card_bot] at hcard
    omega
  have hinv : ∀ q ∈ Q, ∀ w ∈ commV L₁, q w ∈ commV L₁ := by
    intro q hq w hw
    have hqJ : q ∈ L₁ ⊔ L₂ := hJ ▸ hQJ hq
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hcomm hqJ
    rw [MulAut.mul_apply, htriv b hb w hw]
    exact CFSG.Quasithin.commV_apply_mem_of_mem ha hw
  obtain ⟨w, hw, hwC, hwQ⟩ := exists_fixMod_ne hV hQ2 bot_le hne hinv
    (fun q _ c hc => by rw [Subgroup.mem_bot.mp hc]; exact map_one q)
  have hfix : ∀ q ∈ Q, q w = w := by
    intro q hq
    have := hwQ q hq
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  refine ⟨w, fun hfixL => hwC ?_, mem_fixV.mpr fun b hb => htriv b hb w hw, fun A hA => ?_⟩
  · exact Subgroup.mem_bot.mpr (hfree w hw fun g hg => (mem_fixV.mp hfixL) g hg)
  · exact mem_fixV.mpr fun a ha => hfix a (hAQ A hA ha)

theorem genB56 (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) : TypeTwo X L₁ L₂ ∨ TypeThree X L₁ L₂ ∨ TypeFive X L₁ L₂ := by
  have hne : ffJ X ≠ ⊥ := by
    intro hbot
    have hL : L₁ = ⊥ := le_bot_iff.mp (hbot ▸ P.L₁J)
    have : Nontrivial ↥L₁ := CFSG.LocalCores.isQuasisimple_nontrivial P.q₁
    have : Subsingleton ↥L₁ := by rw [hL]; infer_instance
    exact not_subsingleton ↥L₁ ‹_›
  rcases h56 V hV (ffJ X) hne P.b53 with h1 | h2 | h3 | h4 | h5
  · exact (case1_false hV P h1).elim
  · exact (case2_false hV P h2).elim
  · rcases case3_shape hV P h3 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact (case4_false hV P h4).elim
  · exact Or.inr (Or.inr (case5_shape hV P h5))

theorem modulePairFV (h56 : AsB56) : ModulePairFV := by
  intro V _ _ hV X L₁ L₂ τ P hO2 hFF hB53 hL₁J hJn hno 𝒜 Q hQ2 hQJ hA hAQ
  have PJ : JPair X L₁ L₂ τ := ⟨P, hB53, hL₁J, hJn⟩
  rcases genB56 h56 hV PJ with h | h | h
  · exact l2Branch hV P h 𝒜 hQ2 hQJ hA hAQ
  · obtain ⟨h3, m, K, hF, hFin, hm1, hmodd, hcard, hiso⟩ := h
    by_cases hm : m = 1
    · subst hm
      exact l3Branch hV PJ h3 ⟨K, hF, hFin, by simpa using hcard, hiso⟩ hFF hO2 𝒜 hQ2 hQJ hA hAQ
    · exfalso
      obtain ⟨k, hk⟩ := hmodd
      exact hno ⟨m, K, hF, hFin, by omega, ⟨k, hk⟩, hcard, hiso⟩
  · exact case5Branch hV h 𝒜 hQ2 hQJ hAQ

end CFSG.Quasithin.C116Three
