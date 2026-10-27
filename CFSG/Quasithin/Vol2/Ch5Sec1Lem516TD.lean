module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] def IsTDMod (T X W : Subgroup G) : Prop :=
  IsTwoReducedIn (T ⊔ X) W ∧ pCoreOf 2 (T ⊔ X) = T ⊓ Subgroup.centralizer (W : Set G)

variable {T M L H X W : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem inM : InM T M := ⟨h.maxTwoLocal, h.T_le⟩

theorem sup_le_M_of_le_borel (hX : X ≤ borelL T L) : T ⊔ X ≤ M :=
  sup_le h.T_le (hX.trans (inf_le_left.trans h.L_le))

omit h in
theorem hyp315_sup (h : Hyp5_0_1 G T M L n) (hH : IsHStar T M H) (hX : X ≤ borelL T L)
    (hW : IsTDMod T X W) (hI : H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ X) : Set G)) :
    Hyp315 T M (T ⊔ X) H W where
  T_le := le_sup_left
  le_M := h.sup_le_M_of_le_borel hX
  hStar := hH
  reduced := hW.1
  centralizer := hW.2
  case := Or.inl hI

theorem pCoreOf_ne_bot_of_normal (hH : IsHStar T M H) {R₀ : Subgroup G} (hR₀ : R₀ ≠ ⊥)
    (hR₀O : R₀ ≤ pCoreOf 2 (T ⊔ X)) (hR₀n : T ⊔ X ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) :
    pCoreOf 2 (X ⊔ H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : T ⊔ X ⊔ H = X ⊔ H := by
    rw [sup_comm T X, sup_assoc, sup_eq_right.mpr hH.1.1]
  rw [hsup] at hR₀n
  have hR₀T : R₀ ≤ T := hR₀O.trans (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_left))
  have hR₀le : R₀ ≤ X ⊔ H := hR₀T.trans (hH.1.1.trans le_sup_right)
  intro hb
  have := le_pCoreOf_of_le_normalizer 2 hR₀le hR₀n (h.sylow.1.to_le hR₀T)
  rw [hb] at this
  exact hR₀ (le_bot_iff.mp this)

theorem pCoreOf_ne_bot_or_center (hC58 : TheoremC58) (h317 : AS317Sylow) (hH : IsHStar T M H)
    (hX : X ≤ borelL T L) (hW : IsTDMod T X W)
    (hI : H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ X) : Set G))
    (hJ : thompsonJ T ≤ Subgroup.centralizer (W : Set G)) :
    pCoreOf 2 (X ⊔ H) ≠ ⊥ ∨
      (quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf (T ⊔ X) = ⊥) := by
  have h315 := h.hyp315_sup hH hX hW hI
  have hJ' : thompsonJ T ≤ pCoreOf 2 (T ⊔ X) := by
    rw [hW.2]
    exact le_inf (thompsonJ_le_self T) hJ
  rcases lemma317 hC58 h317 h.simple h.nonabelian h.qtke h.sylow h.inM h315 hJ' with h1 |
    ⟨R₀, h1, h2, h3⟩
  · exact Or.inr h1
  · exact Or.inl (h.pCoreOf_ne_bot_of_normal hH h1 h2 h3)

theorem caseI_D (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hH : IsHStar T M H) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ D) : Set G) := by
  rw [sup_comm]
  exact (h.lemma_5_1_5_one h331 hR hH hD).2

theorem caseI_of_normalizes
    (hT : T ≤ Subgroup.normalizer (((T ⊓ L) ⊔ X : Subgroup G) : Set G))
    (hHM : H ⊓ M ≤ Subgroup.normalizer (((T ⊓ L) ⊔ X : Subgroup G) : Set G)) :
    H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ X) : Set G) := by
  have heq : T ⊔ X = ((T ⊓ L) ⊔ X) ⊔ T := by
    apply le_antisymm
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le (inf_le_left.trans le_sup_left) le_sup_right) le_sup_left
  rw [heq, oTwoUpper_sup_eq_of_isPGroup h.sylow.1 hT]
  exact hHM.trans (normalizer_le_normalizer_oTwoUpper _)

theorem centerOf_eq_bot (hH : IsHStar T M H) (hO : pCoreOf 2 (X ⊔ H) = ⊥)
    (hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : centerOf H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hCT : CharTwo H := charTwo_of_inH' h.qtke h.sylow hH.1
  have hZH : centerOf H ≤ pCoreOf 2 H := fun x hx =>
    hCT ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_iff.mp hx.2 g ((pCoreOf_le 2 H) hg)⟩
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hH.1.1)
  obtain ⟨y, hyZ, hy⟩ := exists_mem_orderOf_two_of_isPGroup
    ((pCoreOf_isPGroup 2 H).to_le hZH) hne
  have hyY : y ∈ omegaOneCenterOf H :=
    Subgroup.subset_closure ⟨hyZ, by rw [← hy]; exact pow_orderOf_eq_one y⟩
  have hYne : omegaOneCenterOf H ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hyY
    rw [hyY, orderOf_one] at hy
    omega
  have hYC : omegaOneCenterOf H ≤ centerOf H := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hYZ : omegaOneCenterOf H ≤ quasithinOmegaOneCenter T := by
    refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure ?_
    exact ⟨⟨hOT (hZH hx.1), Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_iff.mp hx.1.2 t (hH.1.1 ht)⟩, hx.2⟩
  have hYO : omegaOneCenterOf H ≤ pCoreOf 2 (X ⊔ H) := by
    refine le_pCoreOf_of_le_normalizer 2 ((hYC.trans inf_le_left).trans le_sup_right)
      (sup_le (le_normalizer_of_le_centralizer ?_) (le_normalizer_of_le_centralizer ?_))
      ((pCoreOf_isPGroup 2 H).to_le (hYC.trans hZH))
    · exact hYZ.trans (Subgroup.le_centralizer_iff.mp hXZ)
    · exact hYC.trans inf_le_right
  rw [hO] at hYO
  exact hYne (le_bot_iff.mp hYO)

theorem commutator_ne_bot_of_centerOf_eq_bot (hH : IsHStar T M H) (hZ : centerOf H = ⊥) :
    ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
  intro hb
  apply quasithinOmegaOneCenter_ne_bot h.sylow.1 h.T_ne_bot
  rw [eq_bot_iff, ← hZ]
  exact le_inf ((quasithinOmegaOneCenter_le_self T).trans hH.1.1)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb)

theorem pCoreOf_ne_bot_of_le_normalizer (hH : IsHStar T M H)
    (hXZ : X ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) : pCoreOf 2 (X ⊔ H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hb
  have hle : quasithinOmegaOneCenter T ≤ pCoreOf 2 (X ⊔ H) :=
    le_pCoreOf_of_le_normalizer 2
      ((quasithinOmegaOneCenter_le_self T).trans (hH.1.1.trans le_sup_right))
      (sup_le hXZ (le_normalizer_of_le_centralizer
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH)))
      (h.sylow.1.to_le (quasithinOmegaOneCenter_le_self T))
  rw [hb] at hle
  exact quasithinOmegaOneCenter_ne_bot h.sylow.1 h.T_ne_bot (le_bot_iff.mp hle)

omit h in
theorem inf_centralizer_eq_bot_of_center (hT : IsPGroup 2 T) (hXL : X ≤ L) {R : Subgroup G}
    (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hZ : centerOf (T ⊔ X) = ⊥) :
    R ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hTC : T ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    have h2 : t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      F7.normalizer_le_normalizer_centralizer L (hTL ht)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxR, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTR ht) x).mp hxR,
        (Subgroup.mem_normalizer_iff.mp h2 x).mp hxC⟩
    · rintro ⟨hxR, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTR ht) x).mpr hxR,
        (Subgroup.mem_normalizer_iff.mp h2 x).mpr hxC⟩
  have hfix := inf_centralizer_ne_bot_of_two hT (hT.to_le (inf_le_left.trans hRT)) hTC hne
  apply hfix
  rw [eq_bot_iff, ← hZ]
  intro c hc
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hc
  obtain ⟨⟨hcR, hcL⟩, hcT⟩ := hc
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (hRT hcR), ?_⟩
  have hle : T ⊔ X ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun t ht => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp hcT t ht).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp hcL x (hXL hx)).symm
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) c rfl).symm

end Hyp5_0_1

end CFSG.Quasithin.H13
