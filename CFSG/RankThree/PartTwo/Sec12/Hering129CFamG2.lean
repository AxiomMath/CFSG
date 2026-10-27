module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0
public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFacts
import CFSG.RankThree.PartTwo.Sec12.Hering129LFix
import CFSG.RankThree.PartTwo.Sec12.Hering129KRes
import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Positive


variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem census_concl_of_isG2D4 (hD : Census129 c a I X f) (r : TauCeti.PrimePower) (δ : ℕ)
    (hQ : IsG2D4 Q r δ) (h4 : 4 ≤ r.card) (hp3 : r.p ≠ 3) (hδ3 : δ = 3 → r.p = 2) :
    CensusConcl Q Lb := by
  obtain ⟨h0, -, -, -⟩ := Hering129L.ks129ThreeLocalFix_holds Q r δ hQ h4 hp3 hδ3
  have hIE : I ≤ resCent (⊤ : Subgroup Q) c :=
    le_inSubgroup_perfectResidual_of_isPerfect (le_inf le_top hD.le_centralizer) hD.isPerfect
  have hEC : resCent (⊤ : Subgroup Q) c ≤ Subgroup.centralizer ({c} : Set Q) :=
    (resCent_le ⊤ c).trans inf_le_right
  rcases h0 c hD.orderOf_c with hA | hB
  ·
    obtain ⟨-, -, hsl⟩ := hA
    have hEq : CFSG.IsQuasisimple ↥(resCent (⊤ : Subgroup Q) c) :=
      Hering129KRes.isQuasisimple_of_isSLThreePiAt hsl (by omega)
    have hZ3 : Nat.card (Subgroup.center ↥(resCent (⊤ : Subgroup Q) c)) = 3 :=
      card_center_eq_three_of_isSLThreePi ⟨_, hsl⟩
    have hsub : (I.subgroupOf (resCent (⊤ : Subgroup Q) c)).IsSubnormal :=
      isSubnormal_subgroupOf_of_le hEC hD.isSubnormal
    have hnt : Nontrivial ↥I := ⟨⟨⟨c, hD.c_mem⟩, 1, fun h => c_ne_one hD (congrArg Subtype.val h)⟩⟩
    have hIeq : I = resCent (⊤ : Subgroup Q) c :=
      Sec4.Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hIE hEq hD.isPerfect hnt hsub
    subst hIeq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hEq f.normal_ker with hk | hk
    ·
      exfalso
      have hL1 : ∀ y : Lb, y = 1 := fun y => by
        obtain ⟨x, rfl⟩ := hD.surjective y
        have : x ∈ f.ker := hk ▸ Subgroup.mem_top x
        exact this
      obtain ⟨a', b', hab⟩ := hD.quasisimple_Lb.2.2
      induction a' using QuotientGroup.induction_on with
      | H x =>
        induction b' using QuotientGroup.induction_on with
        | H y => exact hab (by rw [hL1 x, hL1 y])
    · have hdvd : Nat.card f.ker ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hk
      have h1 : Nat.card f.ker = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact h
        · exact absurd (h ▸ dvd_refl _) hD.ker_three
      have hinj : Function.Injective f := by
        rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_card]
        exact h1
      let e : ↥(resCent (⊤ : Subgroup Q) c) ≃* Lb := MulEquiv.ofBijective f ⟨hinj, hD.surjective⟩
      have hLb : Sec4.IsSLThreePiAt Lb r.card := isSLThreePiAt_congr e hsl
      rcases hQ with ⟨-, h⟩ | ⟨-, hr, h⟩
      · exact Or.inr ⟨r, hLb, Or.inl h⟩
      · exact Or.inr ⟨r, hLb, Or.inr ⟨hr, h⟩⟩
  ·
    exfalso
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hB
    have hcE : c ∈ resCent (⊤ : Subgroup Q) c := hIE hD.c_mem
    have hcen : (⟨c, hcE⟩ : ↥(resCent (⊤ : Subgroup Q) c)) ∈
        Subgroup.center ↥(resCent (⊤ : Subgroup Q) c) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hEC g.2))
    have hcen' : e ⟨c, hcE⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.mp hcen (e.symm g)
      have h2 := congrArg e this
      simpa using h2
    obtain ⟨u, hu, hue⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen'
    have hu2 : u ^ 2 = 1 := by simpa using hu
    have hsq : (e ⟨c, hcE⟩) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hue, ← map_pow, hu2, map_one]
      rfl
    have hc2 : c ^ 2 = 1 := by
      have h3 : (⟨c, hcE⟩ : ↥(resCent (⊤ : Subgroup Q) c)) ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, hsq, map_one]
      simpa using congrArg Subtype.val h3
    have hc3 : c ^ 3 = 1 := c_pow_three hD
    have hc1 : c = 1 := by
      have : c = c ^ 3 * (c ^ 2)⁻¹ := by group
      rw [this, hc3, hc2]
      simp
    exact c_ne_one hD hc1

end Positive

section Models


theorem isG2D4_of_chevalley_G2 {Q : Type} [Group Q] {p f : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel Q .G2 p f) :
    ∃ r : TauCeti.PrimePower, r.card = p ^ f ∧ r.p = p ∧ 3 ≤ r.card ∧ IsG2D4 Q r 1 := by
  obtain ⟨⟨hpp, hf1, -, hstd⟩, K, hF, hFin, hK, ⟨e⟩⟩ := h
  let r : TauCeti.PrimePower := ⟨p, f, hpp, hf1⟩
  have hrc : r.card = p ^ f := TauCeti.PrimePower.card_def r
  have h3 : 3 ≤ r.card := by rw [hrc]; exact hstd
  have hv : (TauCeti.LieTypeIndex.G2 r).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 h3, by simp⟩
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 r hv K (hK.trans hrc.symm)
  exact ⟨r, hrc, rfl, h3, Or.inl ⟨rfl, hv, ⟨e.trans φ⟩⟩⟩

theorem isG2D4_of_chevalley_D4 {Q : Type} [Group Q] {p f : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel Q .trialityD4 p f) :
    ∃ r : TauCeti.PrimePower, r.card = p ^ f ∧ r.p = p ∧ IsG2D4 Q r 3 := by
  obtain ⟨⟨hpp, hf1, -⟩, K, hF, hFin, hK, σ, hσ, ⟨e⟩⟩ := h
  let r : TauCeti.PrimePower := ⟨p, f, hpp, hf1⟩
  have hrc : r.card = p ^ f := TauCeti.PrimePower.card_def r
  have hv : (TauCeti.LieTypeIndex.trialityD4 r).Valid := TauCeti.LieTypeIndex.valid_trialityD4 r
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 r hv K
    (by rw [hrc]; exact hK) σ (by intro x; rw [hrc]; exact hσ x)
  exact ⟨r, hrc, rfl, Or.inr ⟨rfl, hv, ⟨e.trans φ⟩⟩⟩

end Models

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
