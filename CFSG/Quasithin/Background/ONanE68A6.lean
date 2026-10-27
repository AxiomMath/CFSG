module

public import CFSG.Quasithin.Background.ONanE68Cases
public import CFSG.Quasithin.Background.GoldschmidtTDE68Six
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Quasithin.Background.E6TwentyA
public import CFSG.Quasithin.Background.ONanE68Small

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique

section A6Lattice

variable {G : Type} [Group G]

theorem isPGroup_two_ker_of_injective {A B : Type*} [Group A] [Group B] (π : A →* B)
    (h : Function.Injective π) : IsPGroup 2 π.ker := by
  intro x
  refine ⟨0, ?_⟩
  have hx : (x : A) = 1 := h (by rw [map_one]; exact MonoidHom.mem_ker.mp x.2)
  apply Subtype.ext
  simpa using hx

theorem center_eq_bot_of_alt_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Subgroup.center X = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have hc := Subgroup.mem_center_iff.1 hg
  apply e.injective
  rw [map_one]
  refine Borel252.A6.center_trivial_M6 (e g) fun y => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, hc x]

variable {L P : Subgroup G}

theorem isSylowTwoOf_of_le_of_le_left {X : Subgroup G} (hS : IsSylowTwoOf P L) (hPX : P ≤ X)
    (hXL : X ≤ L) : IsSylowTwoOf P X := by
  refine ⟨hPX, hS.2.1, fun hd => hS.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P X L hPX hXL
  have h2 : 2 ∣ P.relIndex L := by
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  exact h2

variable [Finite G]

theorem a6_borel (hq : CFSG.IsQuasisimple ↥L) (hS : IsSylowTwoOf P L)
    (e : ↥L ≃* alternatingGroup (Fin 6)) :
    L ⊓ Subgroup.normalizer (P : Set G) = P ∧
      ∀ X : Subgroup G, P < X → X < L → IsMaxSubgroupIn L X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Nontrivial Borel252.A6.M6 := e.injective.nontrivial
  have hker : IsPGroup 2 e.toMonoidHom.ker := isPGroup_two_ker_of_injective _ e.injective
  obtain ⟨π, hπ⟩ := Borel252.reduceB hq Borel252.A6.center_trivial_M6 Borel252.A6.sylow_U6
    e.toMonoidHom e.surjective hker hS
  have hB : L ⊓ Subgroup.normalizer (P : Set G) = P := by
    have h1 := Fin257.pre_normalizer hπ.surj Borel252.A6.U6
    rw [Borel252.A6.normalizer_U6, ← hπ.hP] at h1
    exact h1.symm
  refine ⟨hB, fun X hPX hXL => ⟨hXL, fun K hXK hKL => ?_⟩⟩
  obtain ⟨-, P₁, P₂, -, -, -, -, -, hsup, honly, -, -⟩ :=
    Borel252.borelFacts_of_data hq hS Borel252.A6.borelData_A6 e.toMonoidHom e.surjective hker
  rw [hB] at honly
  by_contra hKL'
  have hKlt : K < L := lt_of_le_of_ne hKL hKL'
  have hPK : P < K := hPX.trans hXK
  rcases honly X hPX hXL with hX | hX <;> rcases honly K hPK hKlt with hK | hK
  · exact hXK.ne (hX.trans hK.symm)
  · have h12 : P₁ ≤ P₂ := by
      rw [← hX, ← hK]
      exact hXK.le
    rw [sup_eq_right.2 h12] at hsup
    exact hKlt.ne (hK.trans hsup)
  · have h21 : P₂ ≤ P₁ := by
      rw [← hX, ← hK]
      exact hXK.le
    rw [sup_eq_left.2 h21] at hsup
    exact hKlt.ne (hK.trans hsup)
  · exact hXK.ne (hX.trans hK.symm)

theorem twoPrimeResidual_eq_self_of_ne (hS : IsSylowTwoOf P L)
    (hN : L ⊓ Subgroup.normalizer (P : Set G) = P)
    (hmax : ∀ X : Subgroup G, P < X → X < L → IsMaxSubgroupIn L X) {X : Subgroup G}
    (hPX : P ≤ X) (hXL : X < L) (hXP : X ≠ P) : twoPrimeResidual X = X := by
  have hSX := isSylowTwoOf_of_le_of_le_left hS hPX hXL.le
  have hcl := conjClosure_eq_twoPrimeResidual hSX
  have hPY : P ≤ twoPrimeResidual X := hcl ▸ le_conjClosure P X
  have hXN : X ≤ Subgroup.normalizer (twoPrimeResidual X : Set G) :=
    hcl ▸ le_normalizer_conjClosure P X
  have hYX : twoPrimeResidual X ≤ X := twoPrimeResidual_le_self X
  by_cases hYP : twoPrimeResidual X = P
  · exfalso
    apply hXP
    refine le_antisymm ?_ hPX
    rw [hYP] at hXN
    have : X ≤ L ⊓ Subgroup.normalizer (P : Set G) := le_inf hXL.le hXN
    rwa [hN] at this
  · by_contra hYX'
    have hPY' : P < twoPrimeResidual X := lt_of_le_of_ne hPY (Ne.symm hYP)
    have hYL : twoPrimeResidual X < L := lt_of_le_of_lt hYX hXL
    have hXY : twoPrimeResidual X < X := lt_of_le_of_ne hYX hYX'
    exact hXL.ne ((hmax _ hPY' hYL).2 X hXY hXL.le)

end A6Lattice

section Case

theorem e68A6Case : E68A6Case := by
  intro G _ _ T M V U L _ h hU hL ⟨e⟩
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hS : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  obtain ⟨hN, hmax⟩ := a6_borel hq hS e
  obtain ⟨-, hres, -⟩ := sandwich h hU hL
  have hPX : (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
  have hXL : L ⊓ M < L := lt_of_le_of_ne inf_le_left fun hh => hLM (hh ▸ inf_le_right)
  have hZ0 : Subgroup.center ↥L = ⊥ := center_eq_bot_of_alt_six e
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  let φ : CFSG.Quasithin.E6.Bar.Qbar L ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hZ0).trans (QuotientGroup.quotientBot.trans e)
  obtain ⟨hle4, hgen⟩ := CFSG.Quasithin.E6.Alt.altRank_of_iso CFSG.Quasithin.E6.Alt.altModel_six
    CFSG.QuasithinUnique.Unc25A6.card_Dsub (by decide) CFSG.Quasithin.E6.Alt.card_X0_eq
    (φ.trans ψ.symm) (Or.inl (by rw [hZ0]; exact Subgroup.card_bot)) (baseHyp h hU hL)
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hpow := E3.relIndex_eq_two_pow h.isPGroup_V C
  have hne0 : E3.mQuot V C ≠ 0 := mQuot_ne_zero_of_not_le h hLM
  have hm2 : E3.mQuot V C ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h8 : 2 ^ 3 ≤ 2 ^ E3.mQuot V C := Nat.pow_le_pow_right (by norm_num) hlt
    rw [← hpow] at h8
    omega
  have hUC : U ≤ C := le_inf_centralizer_component hU.1 hL
  have hLC : L ≤ Subgroup.centralizer (C : Set G) := le_centralizer_inf_centralizer V L
  refine ⟨1, le_rfl, Or.inr ⟨rfl, ⟨e⟩⟩, E3.mQuot_mono hUC, fun h1 => absurd h1 (lt_irrefl 1), ?_⟩
  by_cases hXP : L ⊓ M = (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L
  ·
    left
    refine ⟨hXP.trans hN.symm, ?_⟩
    rcases (show E3.mQuot V C = 1 ∨ E3.mQuot V C = 2 by omega) with h1 | h2
    · exact Or.inr ⟨rfl, h1⟩
    · left
      refine ⟨by omega, ?_⟩
      have hrel : C.relIndex V = 4 := by rw [hpow, h2]; norm_num
      have hgen' := hgen hrel
      by_contra hno
      push Not at hno
      apply hLM
      refine hgen'.trans (iSup₂_le fun a ha => ?_)
      obtain ⟨haV, haC⟩ := ha
      have haC' : a ∉ C := fun hac => haC hac.2
      have hmA : E3.mQuot V (C ⊔ Subgroup.zpowers a) + 1 = E3.mQuot V C :=
        mQuot_sup_zpowers_add h.isElemAbelian (inf_le_left : C ≤ V) haV haC'
      have hle : L ⊓ Subgroup.centralizer ({a} : Set G) ≤
          L ⊓ Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
        rw [centralizer_sup_eq, centralizer_zpowers_eq]
        exact le_inf inf_le_left (le_inf (inf_le_left.trans hLC) inf_le_right)
      have hCA : C < C ⊔ Subgroup.zpowers a := lt_of_le_of_ne le_sup_left fun hh =>
        haC' (by rw [hh]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      have hAV : C ⊔ Subgroup.zpowers a < V := by
        refine lt_of_le_of_ne (sup_le inf_le_left (Subgroup.zpowers_le.2 haV)) fun hh => ?_
        rw [hh, E3.mQuot_self] at hmA
        omega
      exact hle.trans (hno (C ⊔ Subgroup.zpowers a) (lt_of_le_of_lt hUC hCA) hAV (by omega))
  ·
    right
    have hPX' : (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L < L ⊓ M :=
      lt_of_le_of_ne hPX fun hh => hXP hh.symm
    have hmaxX := hmax _ hPX' hXL
    have hresX := twoPrimeResidual_eq_self_of_ne hS hN hmax hPX hXL hXP
    have hXC : L ⊓ M ≤ L ⊓ Subgroup.centralizer (V : Set G) := hresX.ge.trans hres
    have hm1 : E3.mQuot V C = 1 := by
      by_contra hne1
      have h2 : E3.mQuot V C = 2 := by omega
      have hrel : C.relIndex V = 4 := by rw [hpow, h2]; norm_num
      apply hXL.ne
      refine le_antisymm inf_le_left ((hgen hrel).trans (iSup₂_le fun a ha => ?_))
      obtain ⟨haV, haC⟩ := ha
      have hXa : L ⊓ M ≤ L ⊓ Subgroup.centralizer ({a} : Set G) :=
        hXC.trans (inf_le_inf_left L (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haV)))
      by_contra hnle
      have hlt : L ⊓ M < L ⊓ Subgroup.centralizer ({a} : Set G) :=
        lt_of_le_of_ne hXa fun hh => hnle hh.ge
      have hLa : L ⊓ Subgroup.centralizer ({a} : Set G) = L :=
        hmaxX.2 _ hlt inf_le_left
      refine haC (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
      have : l ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := hLa.ge hl
      exact (Subgroup.mem_centralizer_iff.1 this.2 a rfl).symm
    refine ⟨by rw [hN]; exact hPX, hXL, fun K hXK hKL => ?_, hm1,
      fun h1 => absurd h1 (lt_irrefl 1)⟩
    by_cases hKX : K = L ⊓ M
    · exact Or.inl hKX
    · exact Or.inr (hmaxX.2 K (lt_of_le_of_ne hXK fun hh => hKX hh.symm) hKL)

end Case

end E68Proof

end E6

end CFSG.Quasithin
