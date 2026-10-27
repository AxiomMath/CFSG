module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4k
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.Vol2.Ch10SecC9S5f
public import CFSG.Quasithin.Vol2.Ch10SecKIK4b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem autOn_conj_mem {H J W : Subgroup G} (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    ∀ y ∈ autOn H W, ∀ k ∈ autOn J W, y * k * y⁻¹ ∈ autOn J W := by
  intro y hy k hk
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hy
  obtain ⟨l, hl, rfl⟩ := Setup.mem_autOn_iff.1 hk
  have hgl : (g : G) * l * (g : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hHJ hg) l).mp hl
  rw [← map_inv, ← map_mul, ← map_mul]
  exact Setup.mem_autOn_iff.2 ⟨g * l * g⁻¹, hgl, rfl⟩

theorem autOn_two_pow {H J W : Subgroup G} (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) :
    ∀ y ∈ autOn H W, ∃ e : ℕ, y ^ 2 ^ e ∈ autOn J W := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hy
  obtain ⟨e, he⟩ := h2 g hg
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact Setup.mem_autOn_iff.2 ⟨g ^ 2 ^ e, by simpa using he, rfl⟩

variable [Finite G] {H R J W : Subgroup G} [IsMulCommutative ↥W]

theorem b4Hyp_autOn (hred : IsTwoReducedIn H W) (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J)
    (hSQ : SQTKGroup ↥J) (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J)
    (hq : CFSG.IsQuasisimple ↥(autOn J W))
    (hirr : ∀ X : Subgroup G, X ≤ W → J ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W)
    (hnt : Nontrivial ↥W) : B4Hyp (autOn H W) (autOn J W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := hJH.trans hred.2.1
  have hn := autOn_conj_mem (W := W) hHJ
  have h2' := autOn_two_pow (W := W) h2
  have hle : autOn J W ≤ autOn H W := A4.autOn_mono hJH
  have hker : IsPGroup 2 ↥(J ⊓ Subgroup.centralizer (W : Set G)) := by
    rw [hCJ]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hSQJ := InternalSec.sqtkGroup_autOn hJN hSQ hker
  refine ⟨InternalSec.sqtkGroup_of_two_pow hle hn h2' hSQJ,
    (InternalSec.quasithinGenFitting_eq_of_two_pow hle hn (B1Red.isQuasisimple_to_open hq) h2'
      (Setup.pCoreOf_autOn_eq_bot hred)).symm, hq, ⟨bot_lt_top, fun J' hJ' _ _ => ?_⟩⟩
  have h := InternalSec.irr_autOn (U := W) (L := J) (Cg := ⊥) hJN
    (fun X h1 h2 h3 => by
      rw [inf_bot_eq] at h1 ⊢
      exact hirr X h2 h3) J' (by simp) (fun k hk w hw => hJ' ⟨k, hk⟩ w hw)
  simpa using h

omit [Finite G] [IsMulCommutative ↥W] in
theorem card_evenWeight_seven : Nat.card (evenWeight 7) = 64 := by
  have hs : Function.Surjective (AddMonoidHom.mk' (fun x : Fin 7 → ZMod 2 => ∑ i, x i)
      (fun _ _ => Finset.sum_add_distrib)) := by
    intro z
    refine ⟨Pi.single 0 z, ?_⟩
    simp
  have h := AddSubgroup.card_ker_mul_card_of_surjective hs
  rw [Nat.card_zmod, Nat.card_pi] at h
  simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  unfold evenWeight
  omega

omit [Finite G] [IsMulCommutative ↥W] in
theorem index_of_altType (h : IsAltType J 7) :
    ((blockZ J).subgroupOf (blockU J)).index = 2 ^ 6 := by
  obtain ⟨-, -, -, β, hβs, hβk, -⟩ := h
  rw [← hβk, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 7) ≃ evenWeight 7),
    card_evenWeight_seven]
  norm_num

theorem exists_swap (h42 : AsB42) (hW : IsElemAbelian 2 W) (hred : IsTwoReducedIn H W)
    (hS : IsSylowTwoOf R H) (hJH : J ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) (hSQ : SQTKGroup ↥J)
    (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J)
    (α : ↥J →* ↥(alternatingGroup (Fin 7))) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥J) (hJ : J = ⁅J, thompsonJ R⁆)
    (hJW : ¬ J ≤ Subgroup.centralizer (W : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ W → J ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W)
    (hcard : Nat.card ↥W = 2 ^ 6) :
    ∃ π : Equiv.Perm (Fin 7) →* ↥(ffJ (autOn H W)),
      (FFModel.symDn 7).RealizesVia (ffJ (autOn H W)) ⊤ ⊥ π ∧ Function.Injective π ∧
      autOn J W ≤ ffJ (autOn H W) ∧ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧
        ∃ g : Subgroup.normalizer (W : Set G), (g : G) ∈ R ∧
          ((π t : ↥(ffJ (autOn H W))) : MulAut ↥W) = conjAct W g := by
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := hJH.trans hred.2.1
  obtain ⟨e⟩ := nonempty_autI_equiv hW hJN hCJ α hαs hαk
  have e' : ↥(autOn J W) ≃* ↥(alternatingGroup (Fin 7)) := e
  have hX : Nat.card ↥(autOn J W) = 2520 := (Nat.card_congr e'.toEquiv).trans card_alt7
  have hq : CFSG.IsQuasisimple ↥(autOn J W) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm isQuasisimple_alt7
  have hnt : Nontrivial ↥W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hW.2 v v.2)
  have hB4 := b4Hyp_autOn hred hJH hHJ h2 hSQ hCJ hq hirr hnt
  obtain ⟨A, hAmax, hoff, -⟩ := exists_offender1527d hW hred hS hJH hHJ hq hJ hJW
  obtain ⟨π, hR, T, hT, hAT⟩ := b42_case5 hV2 hB4 hoff (h42 ↥W hV2 _ _ hB4 _ hoff) hX
    hq.1.commutator_eq_top hcard
  have hinj : Function.Injective π :=
    hR.injective_of_faithful (InternalSec.symDn_faithful (by norm_num))
  refine ⟨π, hR, hinj, SecA.le_ffJ_of_two_dvd hV2 hB4 (SecA.two_dvd_card_ffJ hoff), ?_⟩
  obtain ⟨t, ht⟩ : T.Nonempty := by
    by_contra hT0
    rw [Set.not_nonempty_iff_eq_empty] at hT0
    rw [hT0, Subgroup.closure_empty, Subgroup.map_bot] at hAT
    apply hoff.2.1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, B6.le_ffJ hoff hx⟩ : ↥(ffJ (autOn H W))) ∈ (autOn A W).subgroupOf _ :=
      Subgroup.mem_subgroupOf.2 hx
    rw [hAT, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  have hmem : π t ∈ (autOn A W).subgroupOf (ffJ (autOn H W)) := by
    rw [hAT]
    exact Subgroup.mem_map_of_mem π (Subgroup.subset_closure ht)
  obtain ⟨g, hgA, hg⟩ := Setup.mem_autOn_iff.1 (Subgroup.mem_subgroupOf.1 hmem)
  exact ⟨t, hT t ht, g, hAmax.1 hgA, hg.symm⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
