module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Lin
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

@[expose] noncomputable def xbarHToXbar (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] :
    ↥(XbarH M Q Z B) →* ↥(Xbar M Q Z B) :=
  ((QuotientGroup.mk' (Q.subgroupOf M)).comp
    (Subgroup.inclusion (inf_le_left : H0 M Z ≤ M))).subgroupComap (Xbar M Q Z B)

theorem coe_xbarHToXbar [(Q.subgroupOf M).Normal] (s : ↥(XbarH M Q Z B)) :
    ((xbarHToXbar M Q Z B s : ↥(Xbar M Q Z B)) : Mbar M Q) =
      QuotientGroup.mk (⟨((s : ↥(H0 M Z)) : G), ((s : ↥(H0 M Z)).2).1⟩ : ↥M) := rfl

theorem xbarHToXbar_surjective [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) : Function.Surjective (xbarHToXbar M Q Z B) := by
  rintro ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
  have htX : (t : G) ∈ XbarPre M Q Z B := (mem_XbarPre_iff hc t.2).mpr hy
  obtain ⟨n, hn⟩ := exists_XbarH_of_mem_XbarPre hc htX
  refine ⟨n, Subtype.ext ?_⟩
  rw [coe_xbarHToXbar]
  exact congrArg QuotientGroup.mk (Subtype.ext hn)

theorem xbarHToXbar_eq_one_iff [(Q.subgroupOf M).Normal] (s : ↥(XbarH M Q Z B)) :
    xbarHToXbar M Q Z B s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := by
  rw [← Subtype.coe_inj, coe_xbarHToXbar]
  exact (QuotientGroup.eq_one_iff _).trans Subgroup.mem_subgroupOf


theorem Ctx.exists_hom_statedSp_of_transvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)} (hT : CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x) :
    ∃ Θ : ↥(XbarH M Q Z B) →* StatedSp m K, Function.Surjective Θ ∧
      (∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
      ∃ s : ↥(XbarH M Q Z B), ((s : ↥(H0 M Z)) : G) = (a : G) ∧
        Matrix.rank (((Θ s : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) = 1 := by
  classical
  obtain ⟨K'', hK'', hfin'', hcard'', φ', g, hg, hφg⟩ := hT
  have hx1 : 1 ≤ x := (hLm.admissible).2.1
  have : CharP K'' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hx1
      hcard''
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_psp hLm
  let hquot : XbarMod M Q Z B ≃* ↥(Xbar M Q Z B) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have := Fintype.ofFinite K''
  have := Fintype.ofFinite K
  have hcard : Fintype.card K'' = Fintype.card K := by
    have h1 := hcard''
    have h2 := hK
    rw [Nat.card_eq_fintype_card] at h1 h2
    exact h1.trans h2.symm
  let τ : K'' ≃+* K := FiniteField.ringEquivOfCardEq hcard
  let θ : ↥(Xbar M Q Z B) ≃* StatedSp m K :=
    hquot.symm.trans (φ'.trans
      (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.statedProjEquivSp.trans
        (statedSpMapEquiv τ)))
  have haX : (a : G) ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc a.2).mpr (mk_mem_Xbar_of_LB M Q Z B a h.1 h.2)
  refine ⟨θ.toMonoidHom.comp (xbarHToXbar M Q Z B),
    θ.surjective.comp (xbarHToXbar_surjective hc), fun s => ?_,
    ⟨⟨(a : G), XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩, rfl, ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one θ, θ.injective.eq_iff]
    exact xbarHToXbar_eq_one_iff s
  · have h1 : θ (xbarHToXbar M Q Z B
        ⟨⟨(a : G), XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩) =
        statedSpMapEquiv τ g := by
      show statedSpMapEquiv τ
        (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.statedProjEquivSp
          (φ' (a2Class M Q Z B a h))) = statedSpMapEquiv τ g
      rw [hφg]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, coe_statedSpMapEquiv]
    have h2 : (((g : GL (Fin m ⊕ Fin m) K'') : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K'').map τ
        - 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        ((((g : GL (Fin m ⊕ Fin m) K'') : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K'') -
          1).map τ) := by
      rw [Matrix.map_sub _ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [h2, rank_map_ringEquiv]
    exact hg

end CFSG.RankThree.GF2n.Stroth80
