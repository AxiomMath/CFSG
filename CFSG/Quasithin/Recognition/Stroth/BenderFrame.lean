module

public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Vol2.Ch11SecD557B
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

theorem sup_inf_inf_left (L1 L2 S : Subgroup G) :
    ((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L1 = S ⊓ L1 := by
  refine le_antisymm ?_ (le_inf le_sup_left inf_le_right)
  exact inf_le_inf_right L1 (sup_le inf_le_left inf_le_left)

theorem sup_inf_inf_right (L1 L2 S : Subgroup G) :
    ((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L2 = S ⊓ L2 := by
  refine le_antisymm ?_ (le_inf le_sup_right inf_le_right)
  exact inf_le_inf_right L2 (sup_le inf_le_left inf_le_left)

private theorem borelOf_congr_inf {Lj S T : Subgroup G} (h : T ⊓ Lj = S ⊓ Lj) :
    borelOf Lj T = borelOf Lj S := by
  unfold borelOf
  rw [h]

private theorem charTwo_sup_inf [Finite G] {L S B T : Subgroup G}
    (hK : CharTwo (L ⊔ S ⊔ B))
    (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hTS : T ≤ S) (hST : S ≤ Subgroup.normalizer (T : Set G)) :
    CharTwo (L ⊔ T ⊔ B) := by
  have hHK : L ⊔ T ⊔ B ≤ L ⊔ S ⊔ B :=
    sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hTS.trans (le_sup_right.trans le_sup_left))) le_sup_right
  have hLiN : L ≤ Subgroup.normalizer ((L ⊔ T ⊔ B : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
  have hSN : S ≤ Subgroup.normalizer ((L ⊔ T ⊔ B : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup hSL hST) hSB
  have hBN : B ≤ Subgroup.normalizer ((L ⊔ T ⊔ B : Subgroup G) : Set G) :=
    le_sup_right.trans Subgroup.le_normalizer
  have hKN : L ⊔ S ⊔ B ≤ Subgroup.normalizer ((L ⊔ T ⊔ B : Subgroup G) : Set G) :=
    sup_le (sup_le hLiN hSN) hBN
  exact CharTwo.of_normal hK hHK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr hKN)

private theorem hyp111_sup_inf [Finite G] (hF : Hyp111 L1 L2 S) :
    Hyp111 L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) := by
  set T : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hT
  have hTS : T ≤ S := sup_le inf_le_left inf_le_left
  have hT1 : T ⊓ L1 = S ⊓ L1 := sup_inf_inf_left L1 L2 S
  have hT2 : T ⊓ L2 = S ⊓ L2 := sup_inf_inf_right L1 L2 S
  have hB1 : borelOf L1 T = borelOf L1 S := borelOf_congr_inf hT1
  have hB2 : borelOf L2 T = borelOf L2 S := borelOf_congr_inf hT2
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_inf_of_le hF.h1.normalizes)
      (F1.le_normalizer_inf_of_le hF.h2.normalizes)
  have hSB2 : S ≤ Subgroup.normalizer ((borelOf L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hF.h2.normalizes
  have hSB1 : S ≤ Subgroup.normalizer ((borelOf L1 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hF.h1.normalizes
  have hA1 : Hyp111At L1 L2 T :=
    { finite := inferInstance
      pgroup := hF.h1.pgroup.to_le hTS
      normalizes := hTS.trans hF.h1.normalizes
      sylow := by rw [hT1]; exact hF.h1.sylow
      listed := hF.h1.listed
      borel_le := by rw [hB2]; exact hF.h1.borel_le
      charTwo := by
        rw [hB2]
        exact charTwo_sup_inf hF.h1.charTwo hF.h1.normalizes hSB2 hTS hST }
  have hA2 : Hyp111At L2 L1 T :=
    { finite := inferInstance
      pgroup := hF.h1.pgroup.to_le hTS
      normalizes := hTS.trans hF.h2.normalizes
      sylow := by rw [hT2]; exact hF.h2.sylow
      listed := hF.h2.listed
      borel_le := by rw [hB1]; exact hF.h2.borel_le
      charTwo := by
        rw [hB1]
        exact charTwo_sup_inf hF.h2.charTwo hF.h2.normalizes hSB1 hTS hST }
  refine ⟨hA1, hA2, ?_⟩
  have hsub : L1 ⊔ L2 ⊔ T ≤ L1 ⊔ L2 ⊔ S := sup_le_sup_left hTS _
  have hL1 : L1 ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ L2 ⊔ T))
  have hL2 : L2 ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ L2 ⊔ T))
  have hSG : S ≤ Subgroup.normalizer ((L1 ⊔ L2 ⊔ T : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup hF.h1.normalizes hF.h2.normalizes) hST
  have hS' : S ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_pCoreOf_of_le_normalizer hSG
  have hN : L1 ⊔ L2 ⊔ S ≤
      Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
    sup_le (sup_le hL1 hL2) hS'
  have hle : pCoreOf 2 (L1 ⊔ L2 ⊔ T) ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ L2 ⊔ T)).trans hsub) hN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L1 ⊔ L2 ⊔ T))
  rw [hF.o2] at hle
  exact le_bot_iff.mp hle

theorem f112HypW_sup_inf [Finite G] (hF : F112HypW L1 L2 S) :
    F112HypW L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) := by
  set T : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hT
  have hT1 : T ⊓ L1 = S ⊓ L1 := sup_inf_inf_left L1 L2 S
  have hT2 : T ⊓ L2 = S ⊓ L2 := sup_inf_inf_right L1 L2 S
  have hB1 : borelOf L1 T = borelOf L1 S := borelOf_congr_inf hT1
  have hB2 : borelOf L2 T = borelOf L2 S := borelOf_congr_inf hT2
  have hnorm : ((T.subgroupOf (T ⊔ borelOf L1 T)).Normal ∨
      (T.subgroupOf (T ⊔ borelOf L2 T)).Normal) := by
    rw [hB1, hB2]
    rcases hF.2 with h | h
    · left
      have hB1S : borelOf L1 S ≤ Subgroup.normalizer (S : Set G) :=
        (le_sup_right : borelOf L1 S ≤ S ⊔ borelOf L1 S).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (le_sup_left : S ≤ S ⊔ borelOf L1 S)).mp h)
      have hB1S2 : borelOf L1 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
        fun b hb => CFSG.ABGLocalTools.mem_normalizer_inf (hB1S hb) (hF.1.h2.borel_le hb)
      have hB1T : borelOf L1 S ≤ Subgroup.normalizer (T : Set G) :=
        F1.le_normalizer_sup (F1.borelOf_le_normalizer L1 S) hB1S2
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : T ≤ T ⊔ borelOf L1 S)).mpr ?_
      exact sup_le Subgroup.le_normalizer hB1T
    · right
      have hB2S : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) :=
        (le_sup_right : borelOf L2 S ≤ S ⊔ borelOf L2 S).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (le_sup_left : S ≤ S ⊔ borelOf L2 S)).mp h)
      have hB2S1 : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
        fun b hb => CFSG.ABGLocalTools.mem_normalizer_inf (hB2S hb) (hF.1.h1.borel_le hb)
      have hB2T : borelOf L2 S ≤ Subgroup.normalizer (T : Set G) :=
        F1.le_normalizer_sup hB2S1 (F1.borelOf_le_normalizer L2 S)
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : T ≤ T ⊔ borelOf L2 S)).mpr ?_
      exact sup_le Subgroup.le_normalizer hB2T
  exact ⟨hyp111_sup_inf hF.1, hnorm⟩

theorem f112Hyp_sup_inf [Finite G] (hF : F112Hyp L1 L2 S) :
    F112Hyp L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) := by
  have hW := f112HypW_sup_inf hF.toW
  refine ⟨hW.1, ?_, hW.2⟩
  set T : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hT
  have hTS : T ≤ S := sup_le inf_le_left inf_le_left
  have hsub : L1 ⊔ L2 ⊔ T ≤ L1 ⊔ L2 ⊔ S := sup_le_sup_left hTS _
  intro p hp hp2 R hR hRne hR2
  refine (CFSG.SectionRank.pRank_mono hp.one_lt
    (inf_le_inf_right (Subgroup.normalizer (R : Set G)) hsub)).trans
    (hF.2.1 p hp hp2 R ?_ hRne hR2)
  exact hR.trans hsub

theorem bigB_le_normalizer_of_sup_inf_eq [Finite G]
    (hF : Hyp111 L1 L2 S) (hS : (S ⊓ L1) ⊔ (S ⊓ L2) = S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have h1 := (F1.bigB_le_normalizer_sylow hR).1
  have h2 := (F1.bigB_le_normalizer_sylow hR).2
  have h := F1.le_normalizer_sup h1 h2
  rwa [hS] at h

noncomputable def oTwoQuotConj (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (oTwoQuot ↥L) :=
  let ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥L := Subgroup.normalizerMonoidHom L
  let hmap : ∀ g, Subgroup.map (ρ g) (pCore 2 ↥L) = pCore 2 ↥L := fun g => by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      have hgN : (g : G) ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L g.2
      refine (F1.mem_pCore_iff_coe ((ρ g) w)).mpr ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hgN (w : G)).mp ((F1.mem_pCore_iff_coe w).mp hw)
    · intro z hz
      refine ⟨ρ g⁻¹ z, ?_, ?_⟩
      · have hgN : (g⁻¹ : G) ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
          CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
            ((Subgroup.normalizer _).inv_mem g.2)
        refine (F1.mem_pCore_iff_coe ((ρ g⁻¹) z)).mpr ?_
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp hgN (z : G)).mp ((F1.mem_pCore_iff_coe z).mp hz)
      · have h1 : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        simpa using congrArg (fun f : MulAut ↥L => f z) h1
  MonoidHom.mk' (fun g =>
      QuotientGroup.congr (pCore 2 ↥L) (pCore 2 ↥L) (ρ g) (hmap g))
    (by
      intro g h
      apply MulEquiv.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hgh : ρ (g * h) = ρ g * ρ h := map_mul ρ g h
      simp only [hgh, MulAut.mul_apply, QuotientGroup.congr_mk])

theorem oTwoQuotConj_mk (L : Subgroup G) (g : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    oTwoQuotConj L g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨(g : G) * (x : G) * (g : G)⁻¹, by
        have h := (Subgroup.normalizerMonoidHom L g x).2
        rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h⟩ : ↥L) := by
  rw [oTwoQuotConj, MonoidHom.mk'_apply, QuotientGroup.congr_mk]
  congr 1

private theorem commutator_mem_swap_iff {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g * x⁻¹ * g⁻¹ * x ∈ pCoreOf 2 L ↔ g⁻¹ * x⁻¹ * g * x ∈ pCoreOf 2 L := by
  have hgQ : g ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg
  have hgQinv : g⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    (Subgroup.normalizer _).inv_mem hgQ
  constructor
  · intro h
    have h1 : (g * x⁻¹ * g⁻¹ * x)⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem h
    have e : g⁻¹ * x⁻¹ * g * x = g⁻¹ * (g * x⁻¹ * g⁻¹ * x)⁻¹ * g := by group
    rw [e]
    simpa using (Subgroup.mem_normalizer_iff.mp hgQinv _).mp h1
  · intro h
    have h1 : (g⁻¹ * x⁻¹ * g * x)⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem h
    have e : g * x⁻¹ * g⁻¹ * x = (g * (g⁻¹ * x⁻¹ * g * x) * g⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 L).inv_mem
      ((Subgroup.mem_normalizer_iff.mp hgQ (g⁻¹ * x⁻¹ * g * x)).mp h)

theorem oTwoQuotConj_eq_one_iff (L : Subgroup G)
    (g : ↥(Subgroup.normalizer (L : Set G))) :
    oTwoQuotConj L g = 1 ↔ ∀ l ∈ L, (g : G) * l⁻¹ * (g : G)⁻¹ * l ∈ pCoreOf 2 L := by
  constructor
  · intro hσ x hx
    let a : ↥L := ⟨(g : G) * x * (g : G)⁻¹, by
      have h := (Subgroup.normalizerMonoidHom L g (⟨x, hx⟩ : ↥L)).2
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h⟩
    have hfix : oTwoQuotConj L g (QuotientGroup.mk (⟨x, hx⟩ : ↥L)) =
        QuotientGroup.mk (⟨x, hx⟩ : ↥L) := by rw [hσ]; rfl
    rw [oTwoQuotConj_mk] at hfix
    have hfix' : QuotientGroup.mk a = QuotientGroup.mk (⟨x, hx⟩ : ↥L) := hfix
    have hmem : a⁻¹ * (⟨x, hx⟩ : ↥L) ∈ pCore 2 ↥L := QuotientGroup.eq.mp hfix'
    have hmem' := (F1.mem_pCore_iff_coe (a⁻¹ * (⟨x, hx⟩ : ↥L))).mp hmem
    have ha : (a : G) = (g : G) * x * (g : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L g (⟨x, hx⟩ : ↥L)
    simpa [ha, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hmem'
  · intro h
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rw [oTwoQuotConj_mk, MulAut.one_apply]
    apply QuotientGroup.eq.mpr
    rw [F1.mem_pCore_iff_coe]
    have hnat : (g : G) * (x : G)⁻¹ * (g : G)⁻¹ * (x : G) ∈ pCoreOf 2 L := h (x : G) x.2
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hnat

private def modCentralizer (P L Q : Subgroup G)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) : Subgroup G where
  carrier := {x : G | x ∈ P ∧ ∀ l ∈ L, x⁻¹ * l⁻¹ * x * l ∈ Q}
  one_mem' := by
    refine ⟨P.one_mem, fun l _ => ?_⟩
    simpa using Q.one_mem
  mul_mem' := by
    rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
    refine ⟨P.mul_mem hxP hyP, fun l hl => ?_⟩
    have h1 : y⁻¹ * (x⁻¹ * l⁻¹ * x * l) * y ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hPQ (P.inv_mem hyP))
        (x⁻¹ * l⁻¹ * x * l)).mp (hx l hl)
    have h2 : y⁻¹ * l⁻¹ * y * l ∈ Q := hy l hl
    have e : (x * y)⁻¹ * l⁻¹ * (x * y) * l =
        (y⁻¹ * (x⁻¹ * l⁻¹ * x * l) * y) * (y⁻¹ * l⁻¹ * y * l) := by group
    rw [e]
    exact Q.mul_mem h1 h2
  inv_mem' := by
    rintro x ⟨hxP, hx⟩
    refine ⟨P.inv_mem hxP, fun l hl => ?_⟩
    have h1 : x * (x⁻¹ * l⁻¹ * x * l)⁻¹ * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPQ hxP) _).mp (Q.inv_mem (hx l hl))
    have e : (x⁻¹)⁻¹ * l⁻¹ * x⁻¹ * l = x * (x⁻¹ * l⁻¹ * x * l)⁻¹ * x⁻¹ := by group
    rw [e]
    exact h1

private theorem mem_modCentralizer {P L Q : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) {x : G} :
    x ∈ modCentralizer P L Q hPQ ↔ x ∈ P ∧ ∀ l ∈ L, x⁻¹ * l⁻¹ * x * l ∈ Q :=
  Iff.rfl

private theorem modCentralizer_le (P L Q : Subgroup G)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) :
    modCentralizer P L Q hPQ ≤ P :=
  fun x hx => ((mem_modCentralizer hPQ).mp hx).1

private theorem le_normalizer_modCentralizer {P L Q : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) :
    P ≤ Subgroup.normalizer (modCentralizer P L Q hPQ : Set G) := by
  have key : ∀ p ∈ P, ∀ x ∈ modCentralizer P L Q hPQ,
      p * x * p⁻¹ ∈ modCentralizer P L Q hPQ := by
    intro p hp x hx
    rw [mem_modCentralizer] at hx ⊢
    refine ⟨P.mul_mem (P.mul_mem hp hx.1) (P.inv_mem hp), fun l hl => ?_⟩
    have hpl : p⁻¹ * l * p ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem (hPL hp)) l).mp hl
    have hq : x⁻¹ * (p⁻¹ * l * p)⁻¹ * x * (p⁻¹ * l * p) ∈ Q := hx.2 _ hpl
    have h1 : p * (x⁻¹ * (p⁻¹ * l * p)⁻¹ * x * (p⁻¹ * l * p)) * p⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPQ hp) _).mp hq
    have e : (p * x * p⁻¹)⁻¹ * l⁻¹ * (p * x * p⁻¹) * l =
        p * (x⁻¹ * (p⁻¹ * l * p)⁻¹ * x * (p⁻¹ * l * p)) * p⁻¹ := by group
    rwa [e]
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key p hp x
  · intro hx
    have h1 := key p⁻¹ (P.inv_mem hp) (p * x * p⁻¹) hx
    simpa [mul_assoc] using h1

private theorem mem_pCoreOf_of_commutator_mem_of_eq_pCoreOf [Finite G] {S L B Q : Subgroup G}
    (hS2 : IsPGroup 2 S)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hSP : S ≤ L ⊔ B) (hQ2 : IsPGroup 2 Q) (hQle : Q ≤ L ⊔ B)
    (hNQ : L ⊔ B ≤ Subgroup.normalizer (Q : Set G))
    (hQeq : Q = pCoreOf 2 (L ⊔ B))
    {s : G} (hs : s ∈ S)
    (hc : ∀ l ∈ L, s⁻¹ * l⁻¹ * s * l ∈ Q) : s ∈ Q := by
  set P : Subgroup G := L ⊔ B with hPdef
  set C : Subgroup G := modCentralizer P L Q hNQ with hCdef
  have hLP : P ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBL
  have hPn : P ≤ Subgroup.normalizer (C : Set G) := le_normalizer_modCentralizer hLP hNQ
  have hCP : C ≤ P := by rw [hCdef]; exact modCentralizer_le P L Q hNQ
  set R : Subgroup G := S ⊓ C with hRdef
  set RQ : Subgroup G := R ⊔ Q with hRQdef
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := by
    intro b hb
    exact CFSG.ABGLocalTools.mem_normalizer_inf (hBS hb)
      ((le_sup_right : B ≤ P).trans hPn hb)
  have hRQN : ∀ l ∈ L, ∀ y ∈ RQ, l * y * l⁻¹ ∈ RQ := by
    intro l hl y hy
    have hLP' : L ≤ P := by rw [hPdef]; exact le_sup_left
    have hlQ : l ∈ Subgroup.normalizer (Q : Set G) := hNQ (hLP' hl)
    have hRN : R ≤ Subgroup.normalizer (Q : Set G) :=
      ((inf_le_right : S ⊓ C ≤ C).trans hCP).trans hNQ
    rw [hRQdef, sup_comm] at hy
    obtain ⟨q, hq, r, hr, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (H := Q) (K := R) hRN).mp hy
    have hq' : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hlQ q).mp hq
    have hrC : r ∈ C := hr.2
    have hrP : r ∈ P := (inf_le_right : S ⊓ C ≤ C).trans hCP hr
    have hq2 : r⁻¹ * l * r * l⁻¹ ∈ Q := by
      simpa using (mem_modCentralizer hNQ).mp (hCdef ▸ hrC) |>.2 l⁻¹ (L.inv_mem hl)
    have hq3 : l * r * l⁻¹ * r⁻¹ ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (hNQ hrP) (r⁻¹ * l * r * l⁻¹)).mp hq2
      have e : r * (r⁻¹ * l * r * l⁻¹) * r⁻¹ = l * r * l⁻¹ * r⁻¹ := by group
      rwa [e] at h
    have hr2 : l * r * l⁻¹ ∈ RQ := by
      have e : l * r * l⁻¹ = (l * r * l⁻¹ * r⁻¹) * r := by group
      rw [e]
      exact (hRQdef.symm ▸ (R ⊔ Q).mul_mem (Subgroup.mem_sup_right hq3)
        (Subgroup.mem_sup_left hr))
    rw [show l * (q * r) * l⁻¹ = (l * q * l⁻¹) * (l * r * l⁻¹) by group]
    exact (hRQdef.symm ▸ (R ⊔ Q).mul_mem (Subgroup.mem_sup_right hq') hr2)
  have hL1N : L ≤ Subgroup.normalizer (RQ : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hRQN l hl y
    · intro hy
      have h1 := hRQN l⁻¹ (L.inv_mem hl) (l * y * l⁻¹) hy
      simpa [mul_assoc] using h1
  have hBN : B ≤ Subgroup.normalizer (RQ : Set G) :=
    F1.le_normalizer_sup hBR ((le_sup_right : B ≤ P).trans hNQ)
  have hPN : P ≤ Subgroup.normalizer (RQ : Set G) := sup_le hL1N hBN
  have hSPP : S ≤ P := by rw [hPdef]; exact hSP
  have hQPP : Q ≤ P := by rw [hPdef]; exact hQle
  have hRP : RQ ≤ P := by
    rw [hRQdef, hRdef]
    exact sup_le ((inf_le_left : S ⊓ C ≤ S).trans hSPP) hQPP
  have hRQ2 : IsPGroup 2 RQ := by
    have h := IsPGroup.to_sup_of_normal_right' (H := S ⊓ C) (K := Q)
      (hS2.to_le (inf_le_left : S ⊓ C ≤ S)) hQ2
      (((inf_le_right : S ⊓ C ≤ C).trans hCP).trans hNQ)
    exact hRQdef.symm ▸ hRdef.symm ▸ h
  have hRQle : RQ ≤ Q := by
    rw [hQeq]
    exact le_pCoreOf_of_le_normalizer 2 hRP hPN hRQ2
  have hsR : s ∈ R := by
    rw [hRdef]
    refine ⟨hs, ?_⟩
    rw [hCdef]
    exact ⟨hSPP hs, hc⟩
  exact hRQle (hRQdef.symm ▸ Subgroup.mem_sup_left hsR)

theorem mem_pCoreOf_of_commutator_mem [Finite G] (hF : Hyp111 L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S)
    (hc : ∀ l ∈ L1, s⁻¹ * l⁻¹ * s * l ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) :
    s ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
  mem_pCoreOf_of_commutator_mem_of_eq_pCoreOf hF.h1.pgroup
    (bigB_le_normalizer_of_hyp111 hF) hSB
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    (pCoreOf_isPGroup 2 (L1 ⊔ bigB L1 L2 S)) (pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S))
    (le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) rfl hs hc

theorem eq_sup_inf_centralizer_of_odd [Finite G] {S L D : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSD : D ≤ Subgroup.normalizer (S : Set G)) (hDL : D ≤ L)
    (hDodd : Odd (Nat.card D)) :
    S = (S ⊓ L) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) := by
  have hsolv : Group.IsSolvable ↥S := by
    have := hS2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) := by
    obtain ⟨b, hb⟩ := hS2.exists_card_eq
    rw [hb]
    exact (Nat.coprime_two_left.mpr hDodd).symm.pow_right b
  have hdec : S ≤ ⁅S, D⁆ ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.Quasithin.Vol2.Ch11.SecD.le_commutator_sup_centralizer hSD hsolv hcop
  have hcomm : ⁅S, D⁆ ≤ S ⊓ L := by
    refine le_inf ((Subgroup.le_normalizer_iff_commutator_le_left).mp hSD) ?_
    have hSL' : ⁅S, L⁆ ≤ L := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hSL
    exact (Subgroup.commutator_mono le_rfl hDL).trans hSL'
  refine le_antisymm ?_ (sup_le (inf_le_left : S ⊓ L ≤ S)
    (inf_le_left : S ⊓ Subgroup.centralizer (D : Set G) ≤ S))
  exact hdec.trans (sup_le (hcomm.trans le_sup_left) le_sup_right)

theorem exists_complement_eq_sup_centralizer [Finite G] (hF : Hyp111 L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    ∃ D : Subgroup G, D ≤ borelOf L1 S ∧ Odd (Nat.card D) ∧
      (S ⊓ L1) ⊔ D = borelOf L1 S ∧
      S = (S ⊓ L1) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) := by
  obtain ⟨D, hCart, -, hsup⟩ := F1.exists_cartan hF.h1.sylow
  have hD : D ≤ borelOf L1 S := hCart.1
  have hDL : D ≤ L1 := hD.trans (F1.borelOf_le L1 S)
  have hSD : D ≤ Subgroup.normalizer (S : Set G) :=
    hD.trans ((le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S).trans hSB)
  have hSdec : S = (S ⊓ L1) ⊔ (S ⊓ Subgroup.centralizer (D : Set G)) :=
    eq_sup_inf_centralizer_of_odd hF.h1.pgroup hF.h1.normalizes hSD hDL hCart.2.1
  exact ⟨D, hD, hCart.2.1, hsup, hSdec⟩

theorem isSylow_map_inf [Finite G] (h : Hyp111At L1 L2 S) :
    ∃ T : Sylow 2 (oTwoQuot ↥L1),
      (T : Subgroup (oTwoQuot ↥L1)) =
        ((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)) := by
  obtain ⟨hgroup, hidx, -⟩ := F1.map_borelOf_eq_normalizer h.sylow
  exact ⟨hgroup.toSylow hidx, IsPGroup.toSylow_coe hgroup hidx⟩

private theorem odd_card_map_subgroupOf [Finite G] {D L : Subgroup G} (hD : D ≤ L)
    (hodd : Odd (Nat.card D)) :
    Odd (Nat.card ((D.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)))) := by
  refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv]
  exact hodd

private theorem sup_map_inf_map_borelOf [Finite G] (hF : Hyp111 L1 L2 S) {D : Subgroup G}
    (hD : D ≤ borelOf L1 S) (hsup : (S ⊓ L1) ⊔ D = borelOf L1 S) :
    (((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))) ⊔
        ((D.subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))) =
      Subgroup.normalizer
        (((((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)) :
          Subgroup (oTwoQuot ↥L1))) : Set (oTwoQuot ↥L1)) := by
  have hN := (F1.map_borelOf_eq_normalizer hF.h1.sylow).2.2
  have hsub : (S ⊓ L1).subgroupOf L1 ⊔ D.subgroupOf L1 = (borelOf L1 S).subgroupOf L1 := by
    rw [← Subgroup.subgroupOf_sup (inf_le_right : S ⊓ L1 ≤ L1)
      (hD.trans (F1.borelOf_le L1 S)), hsup]
  rw [← Subgroup.map_sup, hsub, hN]

private theorem oTwoQuotConj_maps_map_inf [Finite G] (hF : Hyp111 L1 L2 S) {s : G}
    (hs : s ∈ S) :
    ∀ x ∈ (((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)) :
      Subgroup (oTwoQuot ↥L1)),
      oTwoQuotConj L1 ⟨s, hF.h1.normalizes hs⟩ x ∈
        (((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change oTwoQuotConj L1 ⟨s, hF.h1.normalizes hs⟩ (QuotientGroup.mk y) ∈
    Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L1)) ((S ⊓ L1).subgroupOf L1)
  rw [oTwoQuotConj_mk]
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩)
  · exact S.mul_mem (S.mul_mem hs (Subgroup.mem_subgroupOf.mp hy).1) (S.inv_mem hs)
  · exact (Subgroup.mem_normalizer_iff.mp (hF.h1.normalizes hs) _).mp
      (Subgroup.mem_subgroupOf.mp hy).2

private theorem oTwoQuotConj_fixes_map_subgroupOf [Finite G] (hF : Hyp111 L1 L2 S)
    {D : Subgroup G} {s : G} (hs : s ∈ S)
    (hsC : s ∈ Subgroup.centralizer (D : Set G)) :
    ∀ x ∈ (D.subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)),
      oTwoQuotConj L1 ⟨s, hF.h1.normalizes hs⟩ x = x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change oTwoQuotConj L1 ⟨s, hF.h1.normalizes hs⟩ (QuotientGroup.mk y) = QuotientGroup.mk y
  rw [oTwoQuotConj_mk]
  congr 1
  apply Subtype.ext
  change s * (y : G) * s⁻¹ = (y : G)
  have hyD : (y : G) ∈ D := hy
  have hcomm : s * (y : G) = (y : G) * s :=
    (Subgroup.mem_centralizer_iff.mp hsC (y : G) hyD).symm
  rw [hcomm]
  group

theorem oTwoQuotConj_eq_one_of_autFact [Finite G]
    (hF : Hyp111 L1 L2 S)
    (hAut : ∀ (T : Sylow 2 (CFSG.Quasithin.oTwoQuot ↥L1))
      (H : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)),
      H ≤ Subgroup.normalizer ((T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) : Set _) →
      Odd (Nat.card H) →
      (T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) ⊔ H =
        Subgroup.normalizer ((T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) : Set _) →
      ∀ σ : MulAut (CFSG.Quasithin.oTwoQuot ↥L1), (∃ k : ℕ, σ ^ (2 ^ k) = 1) →
        (∀ x ∈ (T : Subgroup _), σ x ∈ (T : Subgroup _)) → (∀ h ∈ H, σ h = h) → σ = 1)
    {D : Subgroup G} (hD : D ≤ borelOf L1 S)
    (hDsup : (S ⊓ L1) ⊔ D = borelOf L1 S) (hDodd : Odd (Nat.card D))
    {b : G} (hbS : b ∈ S) (hbC : b ∈ Subgroup.centralizer (D : Set G)) :
    oTwoQuotConj L1 ⟨b, hF.h1.normalizes hbS⟩ = 1 := by
  obtain ⟨T, hT⟩ := isSylow_map_inf hF.h1
  let π : ↥L1 →* oTwoQuot ↥L1 := QuotientGroup.mk' (pCore 2 ↥L1)
  let Dbar : Subgroup (oTwoQuot ↥L1) := (D.subgroupOf L1).map π
  have hTbar : (T : Subgroup (oTwoQuot ↥L1)) =
      ((S ⊓ L1).subgroupOf L1).map π := by simpa [π] using hT
  have hDbarOdd : Odd (Nat.card Dbar) := by
    simpa [Dbar, π] using odd_card_map_subgroupOf (L := L1)
      (hD.trans (F1.borelOf_le L1 S)) hDodd
  have hDbarSup : (T : Subgroup (oTwoQuot ↥L1)) ⊔ Dbar =
      Subgroup.normalizer ((T : Subgroup (oTwoQuot ↥L1)) : Set _) := by
    simpa [π, Dbar, hTbar] using sup_map_inf_map_borelOf hF hD hDsup
  have hDbarN : Dbar ≤ Subgroup.normalizer
      ((T : Subgroup (oTwoQuot ↥L1)) : Set _) :=
    (le_sup_right : Dbar ≤
      (T : Subgroup (oTwoQuot ↥L1)) ⊔ Dbar).trans hDbarSup.le
  apply hAut T Dbar hDbarN hDbarOdd hDbarSup
  · obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hF.h1.pgroup) ⟨b, hbS⟩
    refine ⟨k, ?_⟩
    have hbk : (⟨b, hF.h1.normalizes hbS⟩ :
        ↥(Subgroup.normalizer (L1 : Set G))) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    rw [← map_pow, hbk, map_one]
  · intro x hx
    rw [hTbar] at hx ⊢
    exact oTwoQuotConj_maps_map_inf hF hbS x hx
  · intro h hh
    exact oTwoQuotConj_fixes_map_subgroupOf hF hbS hbC h hh

theorem eq_sup_pCoreOf_of_autFact [Finite G]
    (hF : Hyp111 L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hAut : ∀ (T : Sylow 2 (CFSG.Quasithin.oTwoQuot ↥L1))
      (H : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)),
      H ≤ Subgroup.normalizer ((T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) : Set _) →
      Odd (Nat.card H) →
      (T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) ⊔ H =
        Subgroup.normalizer ((T : Subgroup (CFSG.Quasithin.oTwoQuot ↥L1)) : Set _) →
      ∀ σ : MulAut (CFSG.Quasithin.oTwoQuot ↥L1), (∃ k : ℕ, σ ^ (2 ^ k) = 1) →
        (∀ x ∈ (T : Subgroup _), σ x ∈ (T : Subgroup _)) → (∀ h ∈ H, σ h = h) → σ = 1) :
    S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
  obtain ⟨D, hD, hDodd, hDsup, hSdec⟩ := exists_complement_eq_sup_centralizer hF hSB
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  let Q : Subgroup G := pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  have hB : S ⊓ Subgroup.centralizer (D : Set G) ≤ Q := by
    intro b hb
    have hbS : b ∈ S := hb.1
    have hbC : b ∈ Subgroup.centralizer (D : Set G) := hb.2
    have hσ1 : oTwoQuotConj L1 ⟨b, hF.h1.normalizes hbS⟩ = 1 :=
      oTwoQuotConj_eq_one_of_autFact hF hAut hD hDsup hDodd hbS hbC
    have hcomm : ∀ l ∈ L1, b⁻¹ * l⁻¹ * b * l ∈ Q := by
      intro l hl
      have hker := (oTwoQuotConj_eq_one_iff L1 ⟨b, hF.h1.normalizes hbS⟩).mp hσ1
      exact Hyp111.pCoreOf_le_pCoreOf_vertex hF
        ((commutator_mem_swap_iff (L := L1) (g := b) (hF.h1.normalizes hbS)).mp (hker l hl))
    exact mem_pCoreOf_of_commutator_mem hF hSB hbS hcomm
  have hQS : Q ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  have hmain : S ≤ (S ⊓ L1) ⊔ Q :=
    hSdec.le.trans (sup_le_sup_left hB (S ⊓ L1))
  exact le_antisymm hmain (sup_le (inf_le_left : S ⊓ L1 ≤ S) hQS)

end CFSG.Quasithin.Stroth

end
