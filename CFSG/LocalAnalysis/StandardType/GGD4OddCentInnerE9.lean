module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerToralFrame
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerComp
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Classify
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.RankTwo
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Basic
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldReplace
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LieType.SeitzGeneration.OuterSUCat
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNoInner
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (sc scal mem_sc_iff scal_mem_sc
  coe_scal sc_mem_center scal_pow scal_one diagGL monomGL torusThree)

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fixedInCenter_or_toralOn {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {A : Subgroup (MulAut (Om8 K))} {s : Om8 K} {J : Subgroup (Om8 K)}
    (hloc : GGKLocal A (MulAut.conj s) J) (hA : Nat.card A = 3 ^ 3)
    (hd : D4Rank.omFixDim s = 2) (hinn : InnDiagOn A s J) :
    GGAutsFixedInCenter A J ∨ ToralOn A s J := by
  classical
  obtain ⟨⟨hEA, hσA, hσ1, hcomp, hnorm⟩, hker⟩ := hloc
  have hs3 : s ^ 3 = 1 := NbrGraphD4.conj_injective (by rw [map_pow, hEA.2 _ hσA, map_one])
  obtain rfl := eq_centDer_of_isComponentOf hK hn hn3 hs3 hd hcomp
  obtain ⟨E, _, hU, R, _, Ψ, ω, hRc, -, hR3, hω, hJ, hs1, hs2⟩ := exists_d2Model hK hn hn3 hs3 hd
  have h3 : 3 ∣ 2 ^ n + 1 := hK ▸ three_dvd_card_add_one hK hn
  have hCJ := mem_centralizer_centDer_iff_of_model hn3 Ψ hJ
  have hJC : centDer s ≤ Subgroup.centralizer ({s} : Set (Om8 K)) := centDer_le_centralizer s
  have hRmul : ∀ a ∈ A, ∀ a' ∈ A, ∀ u u' : Om8 K, (∀ j ∈ centDer s, a j = u * j * u⁻¹) →
      (∀ j ∈ centDer s, a' j = u' * j * u'⁻¹) →
        ∀ j ∈ centDer s, (a * a') j = (u * u') * j * (u * u')⁻¹ := by
    intro a ha a' ha' u u' hu hu' j hj
    have hj' : u' * j * u'⁻¹ ∈ centDer s := hu' j hj ▸ hnorm a' ha' j hj
    rw [MulAut.mul_apply, hu' j hj, hu _ hj', mul_inv_rev]
    group
  have hRinv : ∀ a ∈ A, ∀ u : Om8 K, (∀ j ∈ centDer s, a j = u * j * u⁻¹) →
      ∀ j ∈ centDer s, a⁻¹ j = u⁻¹ * j * u⁻¹⁻¹ := by
    intro a ha u hu j hj
    have h1 : a⁻¹ j ∈ centDer s := hnorm a⁻¹ (inv_mem ha) j hj
    have h2 : a (a⁻¹ j) = j := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [hu _ h1] at h2
    calc a⁻¹ j = u⁻¹ * (u * a⁻¹ j * u⁻¹) * u := by group
      _ = u⁻¹ * j * u⁻¹⁻¹ := by rw [h2, inv_inv]
  have hRpow : ∀ a ∈ A, ∀ u : Om8 K, (∀ j ∈ centDer s, a j = u * j * u⁻¹) →
      ∀ k : ℕ, ∀ j ∈ centDer s, (a ^ k) j = u ^ k * j * (u ^ k)⁻¹ := by
    intro a ha u hu k
    induction k with
    | zero => intro j _; simp
    | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ]
      exact hRmul _ (pow_mem ha k) a ha _ _ ih hu j hj
  have hR1 : ∀ u : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      (∀ j ∈ centDer s, (1 : MulAut (Om8 K)) j = u * j * (u : Om8 K)⁻¹) →
        ((Ψ u).2 : GL (Fin 3) E) ∈ sc E := by
    intro u hu
    rw [← hCJ u, Subgroup.mem_centralizer_iff]
    intro j hj
    have h : (u : Om8 K) * j * (u : Om8 K)⁻¹ = j :=
      ((MulAut.one_apply _ j).symm.trans (hu j hj)).symm
    calc j * (u : Om8 K) = ((u : Om8 K) * j * (u : Om8 K)⁻¹) * u := by rw [h]
      _ = u * j := by group
  have hRsame : ∀ a ∈ A, ∀ u w : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      (∀ j ∈ centDer s, a j = u * j * (u : Om8 K)⁻¹) →
        (∀ j ∈ centDer s, a j = w * j * (w : Om8 K)⁻¹) →
          ((Ψ (u⁻¹ * w)).2 : GL (Fin 3) E) ∈ sc E := by
    intro a ha u w hu hw
    refine hR1 _ fun j hj => ?_
    have h := (hu j hj).symm.trans (hw j hj)
    rw [MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    calc j = (u : Om8 K)⁻¹ * ((u : Om8 K) * j * (u : Om8 K)⁻¹) * u := by group
      _ = (u : Om8 K)⁻¹ * ((w : Om8 K) * j * (w : Om8 K)⁻¹) * u := by rw [h]
      _ = ((u : Om8 K)⁻¹ * w) * j * ((u : Om8 K)⁻¹ * w)⁻¹ := by group
  obtain ⟨Ahat, hAhat⟩ : ∃ Ahat : Subgroup (GL (Fin 3) E), ∀ M, M ∈ Ahat ↔
      ∃ u : ↥(Subgroup.centralizer ({s} : Set (Om8 K))), ((Ψ u).2 : GL (Fin 3) E) = M ∧
        ∃ a ∈ A, ∀ j ∈ centDer s, a j = u * j * (u : Om8 K)⁻¹ :=
    ⟨{ carrier := {M | ∃ u : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
          ((Ψ u).2 : GL (Fin 3) E) = M ∧ ∃ a ∈ A, ∀ j ∈ centDer s, a j = u * j * (u : Om8 K)⁻¹}
       mul_mem' := by
          rintro _ _ ⟨u, rfl, a, ha, hu⟩ ⟨u', rfl, a', ha', hu'⟩
          exact ⟨u * u', by rw [map_mul, Prod.snd_mul, Subgroup.coe_mul], a * a', mul_mem ha ha',
            fun j hj => by rw [Subgroup.coe_mul]; exact hRmul a ha a' ha' u u' hu hu' j hj⟩
       one_mem' := ⟨1, by rw [map_one, Prod.snd_one, OneMemClass.coe_one], 1, one_mem _,
          fun j _ => by simp⟩
       inv_mem' := by
          rintro _ ⟨u, rfl, a, ha, hu⟩
          exact ⟨u⁻¹, by rw [map_inv, Prod.snd_inv, Subgroup.coe_inv], a⁻¹, inv_mem ha,
            fun j hj => by rw [Subgroup.coe_inv]; exact hRinv a ha u hu j hj⟩ },
      fun M => Iff.rfl⟩
  have hAU : Ahat ≤ unitaryIsom3 hU := by
    intro M hM
    obtain ⟨u, rfl, -⟩ := (hAhat M).mp hM
    exact (Ψ u).2.2
  have hscA : sc E ⊓ unitaryIsom3 hU ≤ Ahat := by
    intro M hM
    obtain ⟨hMsc, hMU⟩ := Subgroup.mem_inf.mp hM
    set u := Ψ.symm (1, ⟨M, hMU⟩) with hu
    have hΨu : Ψ u = (1, ⟨M, hMU⟩) := MulEquiv.apply_symm_apply _ _
    have huJ : (u : Om8 K) ∈ Subgroup.centralizer (centDer s : Set (Om8 K)) :=
      (hCJ u).mpr (by rw [hΨu]; exact hMsc)
    refine (hAhat M).mpr ⟨u, by rw [hΨu], 1, one_mem _, fun j hj => ?_⟩
    rw [MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp huJ j hj
    calc j = j * u * (u : Om8 K)⁻¹ := by group
      _ = u * j * (u : Om8 K)⁻¹ := by rw [this]
  have hcube : ∀ M ∈ Ahat, M ^ 3 ∈ sc E := by
    intro M hM
    obtain ⟨u, rfl, a, ha, hu⟩ := (hAhat M).mp hM
    have h1 := hRpow a ha u hu 3
    rw [hEA.2 a ha] at h1
    have h2 := hR1 (u ^ 3) fun j hj => by rw [SubgroupClass.coe_pow]; exact h1 j hj
    rwa [map_pow, Prod.pow_snd, SubgroupClass.coe_pow] at h2
  have hcomm : ∀ M ∈ Ahat, ∀ N ∈ Ahat, M * N * M⁻¹ * N⁻¹ ∈ sc E := by
    intro M hM N hN
    obtain ⟨u, rfl, a, ha, hu⟩ := (hAhat M).mp hM
    obtain ⟨w, rfl, b, hb, hw⟩ := (hAhat N).mp hN
    have hab : a * b * a⁻¹ * b⁻¹ = 1 := by
      have := congrArg Subtype.val (hEA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simp only [Subgroup.coe_mul] at this
      rw [this]
      group
    have h1 := hRmul _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb) _ _
      (hRmul _ (mul_mem ha hb) _ (inv_mem ha) _ _ (hRmul a ha b hb u w hu hw) (hRinv a ha u hu))
      (hRinv b hb w hw)
    rw [hab] at h1
    have h2 := hR1 (u * w * u⁻¹ * w⁻¹) fun j hj => by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact h1 j hj
    simpa only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] using h2
  have hscn : (sc E).Normal := ⟨fun x hx g => by
    rw [(Subgroup.mem_center_iff.mp (sc_mem_center hx) g), mul_assoc, mul_inv_cancel, mul_one]
    exact hx⟩
  have : ((sc E).subgroupOf Ahat).Normal := inferInstance
  choose uA huAC huA using fun a : ↥A => hinn a a.2
  have hmemA : ∀ a : ↥A, ((Ψ ⟨uA a, huAC a⟩).2 : GL (Fin 3) E) ∈ Ahat := fun a =>
    (hAhat _).mpr ⟨⟨uA a, huAC a⟩, rfl, a, a.2, huA a⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥A →* ↥Ahat ⧸ (sc E).subgroupOf Ahat,
      ∀ a, ψ a = QuotientGroup.mk (⟨_, hmemA a⟩ : ↥Ahat) :=
    ⟨{ toFun := fun a => QuotientGroup.mk (⟨_, hmemA a⟩ : ↥Ahat)
       map_one' := by
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hR1 _ (huA 1)
       map_mul' := fun a b => by
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have h := hRsame (a * b) (a * b).2 ⟨uA (a * b), huAC (a * b)⟩
            (⟨uA a, huAC a⟩ * ⟨uA b, huAC b⟩) (huA (a * b))
            (fun j hj => by
              rw [Subgroup.coe_mul]
              exact hRmul a a.2 b b.2 _ _ (huA a) (huA b) j hj)
          simpa only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul,
            Subgroup.coe_inv] using h },
      fun a => rfl⟩
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨M, hM⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w, rfl, a, ha, hw⟩ := (hAhat M).mp hM
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hψ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hRsame a ha ⟨uA ⟨a, ha⟩, huAC ⟨a, ha⟩⟩ w (huA ⟨a, ha⟩) hw
    simpa only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] using h
  have hkerψ : ∀ a : ↥A, a ∈ ψ.ker ↔ (a : MulAut (Om8 K)) ∈ Subgroup.zpowers (MulAut.conj s) := by
    intro a
    rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine hker a a.2 fun j hj => ?_
      have hc := Subgroup.mem_centralizer_iff.mp ((hCJ ⟨uA a, huAC a⟩).mpr h) j hj
      rw [huA a j hj]
      calc uA a * j * (uA a)⁻¹ = (j * uA a) * (uA a)⁻¹ := by rw [← hc]
        _ = j := by group
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have htriv : ∀ j ∈ centDer s, (a : MulAut (Om8 K)) j =
          ((1 : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) : Om8 K) * j *
            ((1 : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) : Om8 K)⁻¹ := by
        intro j hj
        have hjs : Commute j s := Subgroup.mem_centralizer_singleton_iff.mp (hJC hj)
        rw [← hk, ← map_zpow, MulAut.conj_apply, ((hjs.zpow_right k).eq).symm, mul_assoc,
          mul_inv_cancel, mul_one, OneMemClass.coe_one, one_mul, inv_one, mul_one]
      have h' := hRsame a a.2 1 ⟨uA a, huAC a⟩ htriv (huA a)
      rwa [inv_one, one_mul] at h'
  have hcs3 : orderOf (MulAut.conj s) = 3 := orderOf_eq_prime (hEA.2 _ hσA) hσ1
  have hkercard : Nat.card ψ.ker = 3 := by
    refine (Nat.card_congr
      { toFun := fun a => ⟨a.1.1, (hkerψ a.1).mp a.2⟩
        invFun := fun z => ⟨⟨z.1, Subgroup.zpowers_le.mpr hσA z.2⟩, (hkerψ _).mpr z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } :
      Nat.card ψ.ker = Nat.card (Subgroup.zpowers (MulAut.conj s))).trans ?_
    rw [Nat.card_zpowers, hcs3]
  have hrank : Nat.card (↥Ahat ⧸ (sc E).subgroupOf Ahat) = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hkercard,
      hA] at h1
    omega
  rcases CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF.pgu3_rank_two_classify_any
      hU h3 Ahat hAU hscA hcube hcomm hrank with
    ⟨g, hg, hgT⟩ | ⟨g, hg, lam, ω', hω', -, -, hgH⟩
  ·
    right
    obtain ⟨D, V, hDJ, habel, hV, hVc, hVD, hVJ, hzp, hreal⟩ :=
      exists_toral_of_model hn3 h3 hs3 Ψ hRc hR3 hω hJ hs1 hs2 hg
    refine ⟨D, V, hDJ, habel, hV, hVc, hVD, hVJ, hzp, fun a ha => ?_⟩
    obtain ⟨u, huC, hu⟩ := hinn a ha
    have hM : ((Ψ ⟨u, huC⟩).2 : GL (Fin 3) E) ∈ Ahat :=
      (hAhat _).mpr ⟨⟨u, huC⟩, rfl, a, ha, hu⟩
    have hT : g * ((Ψ ⟨u, huC⟩).2 : GL (Fin 3) E) * g⁻¹ ∈ torusThree E := hgT ⟨_, hM, rfl⟩
    obtain ⟨v, hvV, hv⟩ := hreal ⟨u, huC⟩ hT
    exact ⟨v, hvV, fun j hj => (hu j hj).trans (hv j hj)⟩
  ·
    left
    intro j hjfix
    set jC : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) := ⟨j.1, hJC j.2⟩ with hjC
    have hN : ∀ M ∈ Ahat, M * ((Ψ jC).2 : GL (Fin 3) E) = ((Ψ jC).2 : GL (Fin 3) E) * M := by
      intro M hM
      obtain ⟨w, rfl, a, ha, hw⟩ := (hAhat M).mp hM
      have h1 : (w : Om8 K) * j * (w : Om8 K)⁻¹ = j := (hw j.1 j.2).symm.trans (hjfix a ha)
      have h2 : w * jC = jC * w := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc (w : Om8 K) * j = ((w : Om8 K) * j * (w : Om8 K)⁻¹) * w := by group
          _ = j * w := by rw [h1])
      have h3 := congrArg (fun z => ((Ψ z).2 : GL (Fin 3) E)) h2
      simpa only [map_mul, Prod.snd_mul, Subgroup.coe_mul] using h3
    have hX : monomGL E lam ∈ Ahat.map (MulAut.conj g).toMonoidHom := by
      rw [hgH]
      exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hD : diagGL E 1 ω' (ω' ^ 2) ∈ Ahat.map (MulAut.conj g).toMonoidHom := by
      rw [hgH]
      exact Subgroup.subset_closure (Or.inl (Or.inr rfl))
    obtain ⟨MX, hMX, hMXe⟩ := hX
    obtain ⟨MD, hMD, hMDe⟩ := hD
    have hMXe' : g * MX * g⁻¹ = monomGL E lam := hMXe
    have hMDe' : g * MD * g⁻¹ = diagGL E 1 ω' (ω' ^ 2) := hMDe
    have hconj : ∀ M ∈ Ahat, (g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹) * (g * M * g⁻¹) =
        (g * M * g⁻¹) * (g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹) := fun M hM => by
      have := hN M hM
      calc (g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹) * (g * M * g⁻¹) =
          g * (((Ψ jC).2 : GL (Fin 3) E) * M) * g⁻¹ := by group
        _ = g * (M * ((Ψ jC).2 : GL (Fin 3) E)) * g⁻¹ := by rw [this]
        _ = (g * M * g⁻¹) * (g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹) := by group
    have hsc : g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹ ∈ sc E := by
      have hcD := hconj MD hMD
      have hcX := hconj MX hMX
      rw [hMDe'] at hcD
      rw [hMXe'] at hcX
      exact mem_sc_of_commute_heis hω' hcD hcX
    have hsc' : ((Ψ jC).2 : GL (Fin 3) E) ∈ sc E := by
      obtain ⟨c, hc⟩ := mem_sc_iff.mp hsc
      have e : ((Ψ jC).2 : GL (Fin 3) E) =
          g⁻¹ * (g * ((Ψ jC).2 : GL (Fin 3) E) * g⁻¹) * g := by group
      rw [e, hc, (Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc c)) g⁻¹), mul_assoc,
        inv_mul_cancel, mul_one]
      exact scal_mem_sc c
    rw [Subgroup.mem_center_iff]
    intro j'
    set j'C : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) := ⟨j'.1, hJC j'.2⟩ with hj'C
    have : j'C * jC = jC * j'C := by
      apply Ψ.injective
      rw [map_mul, map_mul]
      refine Prod.ext (hRc _ _) (Subtype.ext ?_)
      rw [Prod.snd_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp (sc_mem_center hsc') _
    have h := congrArg (fun z : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) => (z : Om8 K)) this
    exact Subtype.ext h

end D4Inner

end CFSG.StandardType

end
