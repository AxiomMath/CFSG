module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

section Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem ggDichotomy_refined_of_dvd (hL : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hpJ : p ∣ Nat.card J) {t : MulAut ↥Bs}
    {Jt : Subgroup G} (hr : GGIsReflection p t) (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G)))) :
    Jt ≤ L ∨ (∃ (d : G) (K : Subgroup G), GGNbr p B x D J d K ∧ J ≤ K ∧ Jt ≤ K) ∨
      ∀ a ∈ ggInduced J Bs, t * a = a * t := by
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  have hsimple : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBsabel : IsElemAbelian p Bs := hBsB.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hxBs : x ∈ Bs := hBsB.1 hS.2.1
  have hJJ : ⁅J, J⁆ = J :=
    commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn.1
  have hBsJ : Bs ≤ normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKGroup : ∀ d : G, d ≠ 1 →
      CFSG.Open.lBalanceIsKGroup ↥(centralizer ({d} : Set G)) := fun d hd =>
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hd)
  have step : ∀ (d : G) (X : Subgroup G), d ≠ 1 → d ∈ ggFixG Bs t →
      LargeEvenPComponent p (centralizer ({d} : Set G)) X → J ≤ X →
      Jt ≤ X ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t := by
    intro d X hd1 hdE hX hJX
    have hBsd : Bs ≤ centralizer ({d} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb d (hEBs hdE))
    have hBsX := GGDichotomy.le_normalizer_of_pComponent hBsd hX hJX hJJ hpJ hBsJ
    rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hdE (hKGroup d hd1) hBsX
        ((largeEvenPComponent_iff_lBalance p _ X).1 hX).2 hT with h | h
    · exact Or.inl h
    · exact Or.inr (GGDichotomy.aut_commute_of_commutator_le hBsd hexp hind hJX h)
  by_cases hxE : x ∈ ggFixG Bs t
  ·
    obtain ⟨hJL, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
    rcases step x L hx1 hxE hLpc hJL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    obtain ⟨d, hdD, hdE, hdx⟩ := GGDichotomy.exists_mem_not_mem_zpowers hp
      ((hDJ.1.1).trans hBsB.1) hDJ.1.2.2.1 (hexp x hxBs) (GGDichotomy.relIndex_ggFixG hr) hxE
    have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
    have hD : D = Subgroup.closure {x, d} := eq_closure_pair_of_mem hI hDJ hdD hdx
    obtain ⟨hKpc, hJK, -, hN | hV⟩ :=
      pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) hI hDJ hpJ hD
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      · exact Or.inr (Or.inl ⟨d, _, hN, hJK, h⟩)
      · exact Or.inr (Or.inr h)
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      ·
        exfalso
        obtain ⟨n, hnJt, hnN, hn⟩ := hind
        have hsub : IsSubnormal (ggLayerClosure p (centralizer ({d} : Set G)) J)
            (centralizer ({d} : Set G)) :=
          (AssemblyBPredicates.isSubnormal_iff_open _ _).2
            ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2.1
        have hO : n * x * n⁻¹ * x⁻¹ ∈
            CFSG.Open.lBalancePrimeCore p (centralizer ({d} : Set G)) :=
          largeEvenPPrimeCoreOf_le_of_isSubnormal hsub
            (hV (Subgroup.commutator_mem_commutator (h hnJt) (Subgroup.mem_zpowers x)))
        have hBs' : n * x * n⁻¹ * x⁻¹ ∈ Bs := by
          have h1 : n * x * n⁻¹ ∈ Bs := (mem_normalizer_iff.mp hnN x).mp hxBs
          exact Bs.mul_mem h1 (Bs.inv_mem hxBs)
        have hnx : n * x * n⁻¹ * x⁻¹ = 1 :=
          GGDichotomy.eq_one_of_mem_of_coprime (LBalance.primeCore_coprime p _) hO
            (hexp _ hBs')
        exact hxE (GGDichotomy.mem_ggFixG_of_induced hxBs hn (mul_inv_eq_one.mp hnx))
      · exact Or.inr (Or.inr h)

end Dichotomy

theorem swap_mul_swap_pow_two_or_three {α : Type*} [DecidableEq α] [Fintype α]
    {σ τ : Equiv.Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap) :
    (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      left
      rw [Equiv.swap_mul_self]
      simp
    · right
      have h3 : (Equiv.swap a b * Equiv.swap a d).IsThreeCycle :=
        Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := a) (b := b) (c := d) hab hcd hbd
      simpa [h3.orderOf] using pow_orderOf_eq_one (Equiv.swap a b * Equiv.swap a d)
  · by_cases had : a = d
    · subst had
      rw [Equiv.swap_comm c a]
      by_cases hbc : b = c
      · subst hbc
        left
        rw [Equiv.swap_mul_self]
        simp
      · right
        have h3 : (Equiv.swap a b * Equiv.swap a c).IsThreeCycle :=
          Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := a) (b := b) (c := c) hab hac hbc
        simpa [h3.orderOf] using pow_orderOf_eq_one (Equiv.swap a b * Equiv.swap a c)
    · by_cases hbc : b = c
      · subst hbc
        rw [Equiv.swap_comm a b]
        by_cases hbd : b = d
        · exact absurd hbd hcd
        · right
          have h3 : (Equiv.swap b a * Equiv.swap b d).IsThreeCycle :=
            Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b) (b := a) (c := d)
              (Ne.symm hab) hbd had
          simpa [h3.orderOf] using pow_orderOf_eq_one (Equiv.swap b a * Equiv.swap b d)
      · by_cases hbd : b = d
        · subst hbd
          rw [Equiv.swap_comm a b, Equiv.swap_comm c b]
          right
          have h3 : (Equiv.swap b a * Equiv.swap b c).IsThreeCycle :=
            Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b) (b := a) (c := c)
              (Ne.symm hab) hbc hac
          simpa [h3.orderOf] using pow_orderOf_eq_one (Equiv.swap b a * Equiv.swap b c)
        · left
          have hcomm := swap_commute_of_disjoint hac had hbc hbd
          calc (Equiv.swap a b * Equiv.swap c d) ^ 2
              = (Equiv.swap a b) ^ 2 * (Equiv.swap c d) ^ 2 := hcomm.mul_pow 2
            _ = 1 := by
              rw [pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]

section WeylA

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}

theorem ggWeylOfType_A_mul_pow_eq_one [Fact p.Prime] [Finite ↥Bs] (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    (h : GGWeylOfType p (CoxeterMatrix.A m) A) {c₁ c₂ : MulAut ↥Bs} (h₁ : c₁ ∈ A)
    (h₂ : c₂ ∈ A) (r₁ : GGIsReflection p c₁) (r₂ : GGIsReflection p c₂) :
    (c₁ * c₂) ^ 2 = 1 ∨ (c₁ * c₂) ^ 3 = 1 := by
  obtain ⟨Ê, hÊ⟩ := exists_permEquiv_of_ggWeylOfType_A h
  let E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs := A.subtype.comp Ê.toMonoidHom
  have hinj : Function.Injective E := Subtype.val_injective.comp Ê.injective
  by_cases hm : 1 ≤ m
  · have hsw : ∀ x y : Fin (m + 1), x ≠ y → GGIsReflection p (E (Equiv.swap x y)) := by
      intro x y hxy
      refine ggIsReflection_swap_of_swap E (a := ((⟨0, hm⟩ : Fin m).castSucc))
        (b := ((⟨0, hm⟩ : Fin m).succ)) ?_ (hÊ ⟨0, hm⟩) hxy
      exact (Fin.castSucc_lt_succ).ne
    obtain ⟨π₁, hπ₁⟩ : ∃ π, E π = c₁ := ⟨Ê.symm ⟨c₁, h₁⟩, by
      show ((Ê (Ê.symm ⟨c₁, h₁⟩) : ↥A) : MulAut ↥Bs) = c₁
      rw [Ê.apply_symm_apply]⟩
    obtain ⟨π₂, hπ₂⟩ : ∃ π, E π = c₂ := ⟨Ê.symm ⟨c₂, h₂⟩, by
      show ((Ê (Ê.symm ⟨c₂, h₂⟩) : ↥A) : MulAut ↥Bs) = c₂
      rw [Ê.apply_symm_apply]⟩
    subst hπ₁ hπ₂
    have hperm : (π₁ * π₂) ^ 2 = 1 ∨ (π₁ * π₂) ^ 3 = 1 :=
      swap_mul_swap_pow_two_or_three
        (isSwap_of_ggIsReflection hp2 hBs E hinj hsw r₁)
        (isSwap_of_ggIsReflection hp2 hBs E hinj hsw r₂)
    have hmain : (E (π₁ * π₂)) ^ 2 = 1 ∨ (E (π₁ * π₂)) ^ 3 = 1 := by
      rcases hperm with h2 | h3
      · left
        rw [← map_pow, h2, map_one]
      · right
        rw [← map_pow, h3, map_one]
    simpa only [map_mul] using hmain
  · have hm0 : m = 0 := by omega
    subst hm0
    have hcard : Nat.card ↥A = 1 := by
      simpa using ggWeylOfType_A_card h
    haveI : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp hcard).1
    have hc₁ : c₁ = 1 := by
      have h1 : (⟨c₁, h₁⟩ : ↥A) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h1
    have hc₂ : c₂ = 1 := by
      have h2 : (⟨c₂, h₂⟩ : ↥A) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h2
    rw [hc₁, hc₂]
    simp

end WeylA

section Pair

variable {G : Type} [Group G]

theorem ggRealizedRefl_mul_pow_eq_one [Finite G] (hL : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hpJ : p ∣ Nat.card J)
    (hAJ : GGSecFiveAllAJoin p B Bs x L D J) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) {s : MulAut ↥Bs} {Js : Subgroup G}
    (hs : GGIsReflection p s) (hind : s ∈ ggInduced Js Bs)
    (hJC : Js ≤ Subgroup.centralizer (ggFixG Bs s : Set G))
    (hpc : IsPComponent p (Js.subgroupOf (Subgroup.centralizer (ggFixG Bs s : Set G))))
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) (htJ : t ∈ ggInduced J Bs) :
    (s * t) ^ 2 = 1 ∨ (s * t) ^ 3 = 1 := by
  have hI : GGThmIHyp p B x L := hcfg.1
  have hBsB : GGBstar p B Bs := hcfg.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hBsB.2.1
  have hJL : J ≤ L := (eq_of_le_of_stdSub hI hDJ hpJ).1
  rcases ggDichotomy_refined_of_dvd hL hcfg hInn hpJ hs hind hJC hpc with hJsL |
    ⟨d, K', hK', hJK', hJsK'⟩ | hcomm
  · obtain ⟨m, -, e, he⟩ := hAJ y K hK
    exact ggWeylOfType_A_mul_pow_eq_one (m := m) hp2 hBs ⟨e, he⟩
      ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        (ggAutomizer_mono Bs hJsL (Subgroup.subset_closure hind)))
      ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        (ggAutomizer_mono Bs hJL (Subgroup.subset_closure htJ))) hs ht
  · obtain ⟨m, -, e, he⟩ := hAJ d K' hK'
    exact ggWeylOfType_A_mul_pow_eq_one (m := m) hp2 hBs ⟨e, he⟩
      ((le_sup_right : ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K' Bs)
        (ggAutomizer_mono Bs hJsK' (Subgroup.subset_closure hind)))
      ((le_sup_right : ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K' Bs)
        (ggAutomizer_mono Bs hJK' (Subgroup.subset_closure htJ))) hs ht
  · left
    have hst : Commute s t := (commute_iff_eq s t).mpr (hcomm t htJ)
    rw [hst.mul_pow, hs.1, ht.1, mul_one]

end Pair

end CFSG.StandardType

end
