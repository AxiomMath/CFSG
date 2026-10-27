module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus

private abbrev E6c3nV : Type := Fin Tag.E6.rank → ZMod 3

private abbrev E6c3nE : Type := Multiplicative E6c3nV

theorem e6Three_rank_ge_three {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (cd : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hrange : cd.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ cd.range ↔ x ∈ NoOffRest.hypE6)
    (Ψ : Set (Fin Tag.E6.rank → ℤ))
    (hU : ∀ b : ↥Bs, (∀ γ ∈ Ψ, ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (cd b) j = 0) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (bX : ↥Bs) (hbX1 : bX ≠ 1) (hbXker : cd bX = 1)
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3) :
    3 ≤ compRank Ψ := by
  classical
  let Wsub : Submodule (ZMod 3) E6c3nV := ggRootAnn 3 Ψ
  let W : Subgroup E6c3nE :=
    { carrier := {x : E6c3nE | ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd x j = 0}
      mul_mem' := by
        intro x y hx hy γ hγ
        rw [toAdd_mul]
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx γ hγ, hy γ hγ, add_zero]
      one_mem' := by
        intro γ hγ
        rw [toAdd_one]
        simp
      inv_mem' := by
        intro x hx γ hγ
        rw [toAdd_inv]
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, hx γ hγ, neg_zero] }
  let U : Subgroup ↥Bs := W.comap cd
  have hWmem : ∀ x : E6c3nE, x ∈ W ↔
      ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd x j = 0 := fun _ => Iff.rfl
  have hWsub_mem : ∀ t : E6c3nV, t ∈ Wsub ↔
      ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod 3) * t j = 0 := by
    intro t
    change t ∈ ggRootAnn 3 Ψ ↔ ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod 3) * t j = 0
    rfl
  have hWeq : Nat.card ↥W = Nat.card ↥Wsub := by
    refine Nat.card_congr (α := ↥W) (β := ↥Wsub) ?_
    exact
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, (hWsub_mem _).mpr ((hWmem x.1).mp x.2)⟩
        invFun := fun t => ⟨Multiplicative.ofAdd t.1, (hWmem _).mpr (by
          rw [toAdd_ofAdd]
          exact (hWsub_mem t.1).mp t.2)⟩
        left_inv := fun x => Subtype.ext (ofAdd_toAdd x.1)
        right_inv := fun t => Subtype.ext (toAdd_ofAdd t.1) }
  have hUcard : Nat.card ↥U ≤ 27 := by
    let f : ↥U → ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
      fun u => ⟨(u.1 : G), u.1.2, hU u.1 u.2⟩
    have hinj : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (x : G)) huv
    calc Nat.card ↥U ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
          Nat.card_le_card_of_injective f hinj
      _ ≤ 3 ^ 3 := hcardJ
      _ = 27 := by norm_num
  let cdU : ↥U →* E6c3nE := cd.comp U.subtype
  have hbXU : bX ∈ U := by
    change cd bX ∈ W
    rw [hbXker]
    exact W.one_mem
  have hbXkerU : cdU ⟨bX, hbXU⟩ = 1 := by
    change cd bX = 1
    exact hbXker
  have hnt : Nontrivial ↥cdU.ker :=
    ⟨⟨⟨⟨bX, hbXU⟩, hbXkerU⟩, ⟨1, by simp⟩, by
      intro h
      exact hbX1 (by
        have h' := congrArg (fun x : ↥cdU.ker => ((x.1 : ↥U) : ↥Bs)) h
        simpa using h')⟩⟩
  have hker_two : 2 ≤ Nat.card ↥cdU.ker := by
    have := Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega
  have hcdUcard : Nat.card ↥cdU.ker * Nat.card ↥cdU.range = Nat.card ↥U :=
    Subgroup.card_ker_mul_card_range cdU
  have hrange_le : Nat.card ↥cdU.range ≤ 13 := by
    have h2 : 2 * Nat.card ↥cdU.range ≤ 27 := by
      calc 2 * Nat.card ↥cdU.range ≤ Nat.card ↥cdU.ker * Nat.card ↥cdU.range :=
            Nat.mul_le_mul_right _ hker_two
        _ = Nat.card ↥U := hcdUcard
        _ ≤ 27 := hUcard
    omega
  let R : Subgroup E6c3nE := cd.range
  have hindex : R.index ≤ 3 := by
    rcases hrange with htop | hker
    · have hRtop : R = ⊤ := htop
      rw [hRtop, Subgroup.index_top]
      norm_num
    · let κ : E6c3nE →* Multiplicative (ZMod 3) :=
        { toFun := fun x => Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd x))
          map_one' := by
            show Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd (1 : E6c3nE))) = 1
            rw [toAdd_one, NoOffRest.kDotP_zero, ofAdd_zero]
          map_mul' := by
            intro x y
            show Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd (x * y))) =
              Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd x)) *
              Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd y))
            rw [toAdd_mul, NoOffRest.kDotP_add, ofAdd_add] }
      have hmem : ∀ x : E6c3nE, x ∈ κ.ker ↔
          NoOffRest.kDotP 3 (Multiplicative.toAdd x) = 0 := by
        intro x
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd (NoOffRest.kDotP 3 (Multiplicative.toAdd x)) = 1 ↔
          NoOffRest.kDotP 3 (Multiplicative.toAdd x) = 0
        rw [ofAdd_eq_one]
      have hRker : R = κ.ker := by
        ext x
        change x ∈ cd.range ↔ x ∈ κ.ker
        rw [hmem]
        have h := hker (Multiplicative.toAdd x)
        rw [NoOffRest.mem_hypE6, ofAdd_toAdd] at h
        exact h
      rw [hRker, Subgroup.index_ker]
      have h1 : Nat.card ↥κ.range ≤ Nat.card (Multiplicative (ZMod 3)) :=
        Nat.card_le_card_of_injective (Subtype.val : ↥κ.range → Multiplicative (ZMod 3))
          Subtype.val_injective
      have h2 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
        exact ZMod.card 3
      omega
  letI : R.Normal := Subgroup.normal_of_comm R
  let q : ↥W →* E6c3nE ⧸ R := (QuotientGroup.mk' R).comp W.subtype
  have hqcard : Nat.card ↥q.ker * Nat.card ↥q.range = Nat.card ↥W :=
    Subgroup.card_ker_mul_card_range q
  have hqrange : Nat.card ↥q.range ≤ 3 := by
    have h1 : Nat.card ↥q.range ≤ Nat.card (E6c3nE ⧸ R) :=
      Nat.card_le_card_of_injective (Subtype.val : ↥q.range → E6c3nE ⧸ R) Subtype.val_injective
    have h2 : Nat.card (E6c3nE ⧸ R) = R.index := (Subgroup.index_eq_card R).symm
    omega
  have hqker : Nat.card ↥q.ker ≤ Nat.card ↥cdU.range := by
    let f : ↥q.ker → ↥cdU.range := fun z =>
      ⟨(z.1 : E6c3nE), by
        have hz : (QuotientGroup.mk' R) (z.1 : E6c3nE) = 1 :=
          MonoidHom.mem_ker.mp z.2
        have hzR : (z.1 : E6c3nE) ∈ R := by
          have hmem : (z.1 : E6c3nE) ∈ MonoidHom.ker (QuotientGroup.mk' R : E6c3nE →* E6c3nE ⧸ R) :=
            MonoidHom.mem_ker.mpr hz
          rwa [QuotientGroup.ker_mk'] at hmem
        have hzR' : (z.1 : E6c3nE) ∈ cd.range := hzR
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hzR'
        have hbU : b ∈ U := by
          change cd b ∈ W
          rw [hb]
          exact z.1.2
        exact MonoidHom.mem_range.mpr ⟨⟨b, hbU⟩, by
          show cdU ⟨b, hbU⟩ = (z.1 : E6c3nE)
          change cd b = (z.1 : E6c3nE)
          exact hb⟩⟩
    have hfinj : Function.Injective f := by
      intro z1 z2 h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥cdU.range => (y : E6c3nE)) h
    exact Nat.card_le_card_of_injective f hfinj
  have hWcard : Nat.card ↥W ≤ 3 * Nat.card ↥cdU.range := by
    calc Nat.card ↥W = Nat.card ↥q.ker * Nat.card ↥q.range := hqcard.symm
      _ ≤ Nat.card ↥cdU.range * 3 := Nat.mul_le_mul hqker hqrange
      _ = 3 * Nat.card ↥cdU.range := Nat.mul_comm _ _
  have hWpow : Nat.card ↥Wsub = 3 ^ Module.finrank (ZMod 3) Wsub :=
    (FiniteField.pow_finrank_eq_natCard 3 ↥Wsub).symm
  have hfin_le : Module.finrank (ZMod 3) Wsub ≤ 3 := by
    have h39 : 3 ^ Module.finrank (ZMod 3) Wsub ≤ 39 := by
      calc 3 ^ Module.finrank (ZMod 3) Wsub = Nat.card ↥Wsub := hWpow.symm
        _ = Nat.card ↥W := hWeq.symm
        _ ≤ 3 * Nat.card ↥cdU.range := hWcard
        _ ≤ 3 * 13 := Nat.mul_le_mul_left 3 hrange_le
        _ = 39 := by norm_num
    by_contra h
    have h : 3 < Module.finrank (ZMod 3) Wsub := not_le.mp h
    have h4 : 4 ≤ Module.finrank (ZMod 3) Wsub := by omega
    have h81 : 81 ≤ 3 ^ Module.finrank (ZMod 3) Wsub := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ Module.finrank (ZMod 3) Wsub := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have hmain := le_compRank_of_finrank_ggRootAnn (τ := Tag.E6) (p := 3) Ψ hfin_le
  have hrank : Tag.E6.rank = 6 := rfl
  rw [hrank] at hmain
  omega

end CFSG.StandardType

end
