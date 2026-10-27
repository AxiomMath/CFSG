module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNineteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1919Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltIndexThirtyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Perm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918ThreeA6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEighteenLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLieA
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Sz
public import CFSG.GroupTheory.OddOrderClosureIdempotent
public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  (normalizer_le_normalizer_oUpperTwo)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_r6_1 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    {Y N Dsub H S : Subgroup G} (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    {J : Subgroup G} (hJM : J ≤ D.M) (hJN : J ≤ N) :
    CFSG.Open.pRank p J ≤ 1 := by
  classical
  have hp := D.sig_prime p h.ctx.hyp.hp
  have : Fact p.Prime := ⟨hp.1⟩
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank p J := by omega
  obtain ⟨E, hEJ, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (H := J) (k := 2) h2
  have hEM : E ≤ D.M := hEJ.trans hJM
  have hEN : E ≤ N := hEJ.trans hJN
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 2) hEcard
  have : IsElementaryAbelian p E :=
    { toIsMulCommutative := hEel.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (hEel.2 x x.2)) }
  have hEnc : ¬ IsCyclic E :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEcard
  have huniq := h61 p h.ctx.hyp.hp E hEM hEp hEnc
  have hmem : N ∈ calMOf E := ⟨h.hN.1.1, hEN⟩
  rw [huniq] at hmem
  simp only [Set.mem_singleton_iff] at hmem
  exact h.hN.2 hmem

theorem isMulCommutative_bar2_of_subset_pCore_mul {X : Type} [Group X] [Finite X]
    {A J : Subgroup X} (hA : IsMulCommutative ↥A)
    (h : (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X)) :
    IsMulCommutative (Bar2 J) := by
  classical
  let Q : Subgroup ↥J := CFSG.pCore 2 ↥J
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨jx, rfl⟩ := QuotientGroup.mk'_surjective Q x
  obtain ⟨jy, rfl⟩ := QuotientGroup.mk'_surjective Q y
  obtain ⟨z, hz, a, ha, hza⟩ := Set.mem_mul.mp (h jx.2)
  have hzJ : z ∈ J := (CFSG.LieType.BorelTits.pCoreOf_le 2 J) hz
  have hzQ : (⟨z, hzJ⟩ : ↥J) ∈ Q :=
    (CFSG.mem_openPCoreOf_iff (H := J) (⟨z, hzJ⟩ : ↥J)).mp hz
  have haJ : a ∈ J := by
    have haz : a = z⁻¹ * (jx : X) := by
      rw [← hza]
      group
    rw [haz]
    exact J.mul_mem (J.inv_mem hzJ) jx.2
  have hxj : jx = (⟨z, hzJ⟩ : ↥J) * ⟨a, haJ⟩ :=
    Subtype.ext (by rw [Subgroup.coe_mul]; exact hza.symm)
  have hxeq : QuotientGroup.mk' Q jx = QuotientGroup.mk' Q (⟨a, haJ⟩ : ↥J) := by
    calc QuotientGroup.mk' Q jx
        = QuotientGroup.mk' Q ((⟨z, hzJ⟩ : ↥J) * ⟨a, haJ⟩) := by rw [hxj]
      _ = QuotientGroup.mk' Q (⟨z, hzJ⟩ : ↥J) * QuotientGroup.mk' Q (⟨a, haJ⟩ : ↥J) :=
          map_mul _ _ _
      _ = 1 * QuotientGroup.mk' Q (⟨a, haJ⟩ : ↥J) := by
          rw [show QuotientGroup.mk' Q (⟨z, hzJ⟩ : ↥J) = 1 from
            (QuotientGroup.eq_one_iff (N := Q) (⟨z, hzJ⟩ : ↥J)).mpr hzQ]
      _ = QuotientGroup.mk' Q (⟨a, haJ⟩ : ↥J) := one_mul _
  obtain ⟨w, hw, b, hb, hwb⟩ := Set.mem_mul.mp (h jy.2)
  have hwJ : w ∈ J := (CFSG.LieType.BorelTits.pCoreOf_le 2 J) hw
  have hwQ : (⟨w, hwJ⟩ : ↥J) ∈ Q :=
    (CFSG.mem_openPCoreOf_iff (H := J) (⟨w, hwJ⟩ : ↥J)).mp hw
  have hbJ : b ∈ J := by
    have hbw : b = w⁻¹ * (jy : X) := by
      rw [← hwb]
      group
    rw [hbw]
    exact J.mul_mem (J.inv_mem hwJ) jy.2
  have hyj : jy = (⟨w, hwJ⟩ : ↥J) * ⟨b, hbJ⟩ :=
    Subtype.ext (by rw [Subgroup.coe_mul]; exact hwb.symm)
  have hyeq : QuotientGroup.mk' Q jy = QuotientGroup.mk' Q (⟨b, hbJ⟩ : ↥J) := by
    calc QuotientGroup.mk' Q jy
        = QuotientGroup.mk' Q ((⟨w, hwJ⟩ : ↥J) * ⟨b, hbJ⟩) := by rw [hyj]
      _ = QuotientGroup.mk' Q (⟨w, hwJ⟩ : ↥J) * QuotientGroup.mk' Q (⟨b, hbJ⟩ : ↥J) :=
          map_mul _ _ _
      _ = 1 * QuotientGroup.mk' Q (⟨b, hbJ⟩ : ↥J) := by
          rw [show QuotientGroup.mk' Q (⟨w, hwJ⟩ : ↥J) = 1 from
            (QuotientGroup.eq_one_iff (N := Q) (⟨w, hwJ⟩ : ↥J)).mpr hwQ]
      _ = QuotientGroup.mk' Q (⟨b, hbJ⟩ : ↥J) := one_mul _
  rw [hxeq, hyeq, ← map_mul, ← map_mul]
  congr 1
  have hcommJ : (⟨a, haJ⟩ : ↥J) * ⟨b, hbJ⟩ = ⟨b, hbJ⟩ * ⟨a, haJ⟩ := by
    apply Subtype.ext
    change a * b = b * a
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  exact hcommJ

theorem nonempty_bar2_oUpperTwo_equiv_of_quot {X : Type} [Group X] [Finite X]
    {S : Type} [Group S] [Finite S] (Y : Subgroup X) (φ : ↥Y →* S)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥Y) :
    Nonempty (Bar2 (S17.oUpperTwo Y) ≃* S17.oUpperTwo (⊤ : Subgroup S)) := by
  let J₀ : Subgroup X := S17.oUpperTwo Y
  have hJle : J₀ ≤ Y := S17.oUpperTwo_le Y
  set ψ : ↥J₀ →* S := φ.comp (Subgroup.inclusion hJle) with hψdef
  have hJnormal : (J₀.subgroupOf Y).Normal :=
    CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf Y
  have hsub : CFSG.Open.IsSubnormal J₀ Y :=
    CFSG.Assembly.isSubnormal_iff_open.1
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hJle).2 hJnormal.isSubnormal)
  have hcore : CFSG.Open.pCoreOf 2 J₀ = J₀ ⊓ CFSG.Open.pCoreOf 2 Y :=
    CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub
  have hψrange : ψ.range = (J₀.subgroupOf Y).map φ := by
    rw [MonoidHom.range_eq_map, hψdef]
    rw [← Subgroup.map_map (g := φ) (f := Subgroup.inclusion hJle)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      change (Subgroup.inclusion hJle x : X) ∈ J₀
      rw [Subgroup.coe_inclusion]
      exact x.2
    · intro hy
      exact ⟨⟨(y : X), hy⟩, Subgroup.mem_top _, Subtype.ext (Subgroup.coe_inclusion hJle _)⟩
  have hrange_le : ψ.range ≤ S17.oUpperTwo (⊤ : Subgroup S) := by
    rw [hψrange]
    have hJ : J₀.subgroupOf Y = CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup ↥Y) := by
      have h := CFSG.Quasithin.A4.oTwoUpper_subgroupOf (le_refl Y)
      rw [Subgroup.subgroupOf_self] at h
      exact h.symm
    rw [hJ]
    have hmap := CFSG.GroupTheory.map_oddOrderClosure_le φ (⊤ : Subgroup ↥Y)
    rw [Subgroup.map_top_of_surjective φ hφ] at hmap
    exact hmap.trans (le_of_eq (CFSG.GroupTheory.oddOrderClosure_eq_closure (⊤ : Subgroup S)))
  have hrange_ge : S17.oUpperTwo (⊤ : Subgroup S) ≤ ψ.range := by
    rw [S17.oUpperTwo_eq_closure, Subgroup.closure_le]
    rintro s ⟨-, hodd⟩
    obtain ⟨y, hφy⟩ := hφ s
    obtain ⟨k, hk⟩ :=
      CFSG.GroupTheory.pow_two_pow_mem_oddOrderClosure Y (g := (y : X)) y.2
    have hwJ : ((y ^ 2 ^ k : ↥Y) : X) ∈ J₀ := by
      rw [Subgroup.coe_pow]
      change (y : X) ^ 2 ^ k ∈ CFSG.GroupTheory.oddOrderClosure Y
      exact hk
    have hpow : s ^ 2 ^ k ∈ ψ.range := by
      refine ⟨⟨((y ^ 2 ^ k : ↥Y) : X), hwJ⟩, ?_⟩
      rw [hψdef]
      change φ (Subgroup.inclusion hJle ⟨((y ^ 2 ^ k : ↥Y) : X), hwJ⟩) = s ^ 2 ^ k
      have hincl : (Subgroup.inclusion hJle
          ⟨((y ^ 2 ^ k : ↥Y) : X), hwJ⟩ : ↥Y) = y ^ 2 ^ k :=
        Subtype.ext rfl
      rw [hincl, map_pow, hφy]
    exact CFSG.Quasithin.B2F.mem_of_odd_orderOf_of_pow_mem hodd hpow
  have hrange_eq : ψ.range = S17.oUpperTwo (⊤ : Subgroup S) :=
    le_antisymm hrange_le hrange_ge
  have hkerψ : ψ.ker = CFSG.pCore 2 ↥J₀ := by
    have h1 : ψ.ker = (CFSG.pCore 2 ↥Y).comap (Subgroup.inclusion hJle) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, ← hker]
      rfl
    have hPY : CFSG.pCore 2 ↥Y = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y := by
      unfold CFSG.Open.pCoreOf
      exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _).symm
    have hcomap : (CFSG.pCore 2 ↥Y).comap (Subgroup.inclusion hJle) =
        CFSG.pCore 2 ↥J₀ := by
      rw [hPY, Subgroup.comap_inclusion_subgroupOf hJle (CFSG.Open.pCoreOf 2 Y)]
      rw [show (CFSG.Open.pCoreOf 2 Y).subgroupOf J₀ =
          (J₀ ⊓ CFSG.Open.pCoreOf 2 Y).subgroupOf J₀ from by
        rw [inf_comm]
        exact (Subgroup.inf_subgroupOf_right _ _).symm]
      rw [← hcore]
      unfold CFSG.Open.pCoreOf
      exact Subgroup.comap_map_eq_self_of_injective J₀.subtype_injective _
    exact h1.trans hcomap
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange_eq))⟩

theorem bar2_oUpperTwo_opp_equiv_alt_of_perm_quot {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {k : ℕ} (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin k)) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃* alternatingGroup (Fin k)) := by
  let φ : ↥Y →* Equiv.Perm (Fin k) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
  have hφ : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = CFSG.pCore 2 ↥Y :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
      (QuotientGroup.ker_mk' _)
  have hYopp : Opp 2 Y = Y :=
    opp_eq_self_of_quot Y φ hφ (by rw [hker]; exact CFSG.pCore_isPGroup) (opp_top_perm k)
  obtain ⟨eiso⟩ := nonempty_bar2_oUpperTwo_equiv_of_quot Y φ hφ hker
  rw [hYopp]
  rw [oUpperTwo_top_perm k] at eiso
  exact ⟨eiso⟩

theorem bar2_oUpperTwo_opp_equiv_alt_of_perm {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {k : ℕ} (hk : k = 3 ∨ 5 ≤ k) (e : ↥Y ≃* Equiv.Perm (Fin k)) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃* alternatingGroup (Fin k)) := by
  have hperm : CFSG.pCore 2 (Equiv.Perm (Fin k)) = ⊥ := by
    rcases hk with rfl | hk
    · exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
        (Or.inr (Or.inl rfl))
    · exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
        (Or.inr (Or.inr hk))
  have hp : CFSG.pCore 2 ↥Y = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 e
    rw [hperm] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  let φ : ↥Y →* Equiv.Perm (Fin k) := e.toMonoidHom
  have hφ : Function.Surjective φ := e.surjective
  have hker : φ.ker = CFSG.pCore 2 ↥Y :=
    (MonoidHom.ker_eq_bot_iff φ).mpr e.injective |>.trans hp.symm
  have hYopp : Opp 2 Y = Y :=
    opp_eq_self_of_quot Y φ hφ (by rw [hker]; exact CFSG.pCore_isPGroup) (opp_top_perm k)
  obtain ⟨eiso⟩ := nonempty_bar2_oUpperTwo_equiv_of_quot Y φ hφ hker
  rw [hYopp]
  rw [oUpperTwo_top_perm k] at eiso
  exact ⟨eiso⟩

theorem bar2_oUpperTwo_opp_equiv_alt_of_swap {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {n : ℕ} (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hY : Y.map e.toMonoidHom =
      (Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))).comap
        (alternatingGroup (Fin n)).subtype) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃* alternatingGroup (Fin (n - 2))) := by
  let C : Subgroup (Equiv.Perm (Fin n)) :=
    Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))
  let A : Subgroup (Equiv.Perm (Fin n)) := alternatingGroup (Fin n)
  have hmap : (C.comap A.subtype).map A.subtype = C ⊓ A := by
    rw [Subgroup.comap_subtype C A, Subgroup.subgroupOf_map_subtype C A]
  let e1 : ↥Y ≃* ↥(Y.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective
  let e2 : ↥(Y.map e.toMonoidHom) ≃* ↥(C.comap A.subtype) := MulEquiv.subgroupCongr hY
  let e3 : ↥(C.comap A.subtype) ≃* ↥(C ⊓ A) :=
    (Subgroup.equivMapOfInjective (C.comap A.subtype) A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e4 : ↥(C ⊓ A) ≃* Equiv.Perm (Fin (n - 2)) :=
    (CFSG.HardMathSupport.RichardWeiss.Proving.PLType.altCentSwapEquiv (m := n) hab).symm
  let φ : ↥Y ≃* Equiv.Perm (Fin (n - 2)) := ((e1.trans e2).trans e3).trans e4
  exact bar2_oUpperTwo_opp_equiv_alt_of_perm Y (Or.inr (by omega)) φ

theorem nonempty_bar2_oUpperTwo_opp_equiv_of_isSimpleGroup {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) (hY : IsSimpleGroup ↥Y) (h2 : 2 ∣ Nat.card Y)
    (hY2 : ¬ IsPGroup 2 ↥Y) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 Y)) ≃* ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOpp : Opp 2 Y = Y := by
    refine le_antisymm ?_ ?_
    · unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      exact (closure_le _).mpr fun x hx => hx.1
    · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 h2
      have hz1 : z ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hz
        omega
      have hzOpp : (z : X) ∈ Opp 2 Y := by
        unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
        refine Subgroup.subset_closure ⟨z.2, 1, ?_⟩
        rw [Subgroup.orderOf_coe, hz, pow_one]
      have : ((Opp 2 Y).subgroupOf Y).Normal := S17.normal_Opp 2 Y
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Opp 2 Y).subgroupOf Y) with h | h
      · exfalso
        have hmem : z ∈ (Opp 2 Y).subgroupOf Y := Subgroup.mem_subgroupOf.mpr hzOpp
        rw [h, Subgroup.mem_bot] at hmem
        exact hz1 hmem
      · exact Subgroup.subgroupOf_eq_top.mp h
  have hp : CFSG.pCore 2 ↥Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥Y) with h | h
    · exact h
    · exfalso
      apply hY2
      have hp2 : IsPGroup 2 (CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
      rw [h] at hp2
      exact hp2.of_equiv Subgroup.topEquiv
  have ho : S17.oUpperTwo Y = Y := by
    refine le_antisymm (S17.oUpperTwo_le Y) ?_
    have hOddPrime : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card Y := by
      by_contra hcon
      apply hY2
      rw [IsPGroup.iff_card]
      refine ⟨(Nat.card Y).primeFactorsList.length, ?_⟩
      exact Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥Y)).ne'
        (fun {d} hd hdn => by
          by_contra hd2
          exact hcon ⟨d, hd, hd2, hdn⟩)
    obtain ⟨p, hpp, hp2, hpdvd⟩ := hOddPrime
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpdvd
    have hpodd : Odd p := hpp.odd_of_ne_two hp2
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw
      exact hpp.ne_one hw.symm
    have hwodd : Odd (orderOf (w : X)) := by
      rw [Subgroup.orderOf_coe, hw]
      exact hpodd
    have hwmem : (w : X) ∈ S17.oUpperTwo Y := by
      rw [S17.oUpperTwo_eq_closure]
      exact Subgroup.subset_closure ⟨w.2, hwodd⟩
    have : ((S17.oUpperTwo Y).subgroupOf Y).Normal :=
      CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf Y
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S17.oUpperTwo Y).subgroupOf Y) with h | h
    · exfalso
      have hmem : w ∈ (S17.oUpperTwo Y).subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr hwmem
      rw [h, Subgroup.mem_bot] at hmem
      exact hw1 hmem
    · exact Subgroup.subgroupOf_eq_top.mp h
  rw [hOpp, ho]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot⟩

abbrev Jzero (D : Data G) (Dsub : Subgroup G) : Type :=
  Bar2 (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))

theorem jzero_type_of_p19_16_1 (D : Data G) {Dsub : Subgroup G} (h1 : P19_16_1 D Dsub) :
    ∃ k : ℕ, (k = 3 ∨ k = 5 ∨ k = 6) ∧
      Nonempty (Jzero D Dsub ≃* alternatingGroup (Fin k)) := by
  obtain ⟨-, hq⟩ := h1
  obtain ⟨e0⟩ := nonempty_bar2_jzero_equiv D.M Dsub
  rcases hq with h3 | h5 | h6
  · obtain ⟨e3⟩ := h3
    obtain ⟨eY⟩ :=
      bar2_oUpperTwo_opp_equiv_alt_of_perm_quot (barOfInter D.M Dsub) (k := 3) e3
    exact ⟨3, Or.inl rfl, ⟨e0.trans eY⟩⟩
  · obtain ⟨e5⟩ := h5
    obtain ⟨eY⟩ :=
      bar2_oUpperTwo_opp_equiv_alt_of_perm_quot (barOfInter D.M Dsub) (k := 5) e5
    exact ⟨5, Or.inr (Or.inl rfl), ⟨e0.trans eY⟩⟩
  · obtain ⟨e6⟩ := h6
    obtain ⟨eY⟩ :=
      bar2_oUpperTwo_opp_equiv_alt_of_perm_quot (barOfInter D.M Dsub) (k := 6) e6
    exact ⟨6, Or.inr (Or.inr rfl), ⟨e0.trans eY⟩⟩

theorem jzero_equiv_zmod_three_of_p19_16_2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) (h2 : P19_16_2 D Dsub) :
    Nonempty (Jzero D Dsub ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨hA6, hidx⟩ := h2
  have hidx' : (barOfInter D.M Dsub).index = 15 := by
    rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
    exact hidx
  have hk := kFacts1918_of_isA6ModZ3 hA6 (barOfInter D.M Dsub) hidx'
  obtain ⟨e0⟩ := nonempty_bar2_jzero_equiv D.M Dsub
  have hcard : Nat.card (Jzero D Dsub) = 3 := by
    rw [Nat.card_congr e0.toEquiv]
    exact hk.2
  exact ⟨mulEquivOfPrimeCardEq (p := 3) hcard (by simp)⟩

theorem jzero_equiv_zmod_three_sq_of_p19_16_3 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) (h3 : P19_16_3 D Dsub) :
    Nonempty (Jzero D Dsub ≃* Multiplicative (ZMod 3 × ZMod 3)) := by
  obtain ⟨hAlt, hidx⟩ := h3
  have hidx' : (barOfInter D.M Dsub).index = 35 := by
    rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
    exact hidx
  obtain ⟨eY⟩ := a7_index35_jzero hAlt (barOfInter D.M Dsub) hidx'
  obtain ⟨e0⟩ := nonempty_bar2_jzero_equiv D.M Dsub
  exact ⟨e0.trans eY⟩

theorem jzero_props_of_equiv_simple {D : Data G} {Dsub : Subgroup G} {X : Type} [Group X]
    [Finite X] (e : Jzero D Dsub ≃* X) (hX : IsSimpleGroup X)
    (hnc : ¬ IsMulCommutative X) (c : ℕ) (hcard : Nat.card X = c) :
    IsSimpleGroup (Jzero D Dsub) ∧ ¬ IsMulCommutative (Jzero D Dsub) ∧
      Nat.card (Jzero D Dsub) = c := by
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr hX, ?_, ?_⟩
  · exact CFSG.Quasithin.H13.not_isMulCommutative_of_mulEquiv e.symm hnc
  · rw [Nat.card_congr e.toEquiv, hcard]

theorem jzero_simple_of_p19_16_4 (D : Data G) {Dsub : Subgroup G} (h4 : P19_16_4 D Dsub) :
    IsSimpleGroup (Jzero D Dsub) ∧ ¬ IsMulCommutative (Jzero D Dsub) ∧
      (Nat.card (Jzero D Dsub) = 360 ∨ Nat.card (Jzero D Dsub) = 20160 ∨
        Nat.card (Jzero D Dsub) = 1451520) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc6 : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    norm_num
  have hnc8 : ¬ IsMulCommutative (alternatingGroup (Fin 8)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    norm_num
  have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hsimple8 : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hcard6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcard8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  obtain ⟨e0⟩ := nonempty_bar2_jzero_equiv D.M Dsub
  obtain ⟨m, hm, hdata⟩ := h4
  rcases hm with rfl | rfl
  · rcases hdata with ⟨ε, hΩ, hCent⟩ | ⟨hAlt, e, a, b, hab, hmap⟩
    · cases ε
      ·
        obtain ⟨eSp⟩ := nonempty_mulEquiv_statedSp_of_isOmegaEps2
          (X := Bar2 Dsub) (Y := barOfInter D.M Dsub) (Or.inl ⟨rfl, rfl⟩) hΩ hCent
        obtain ⟨eS6⟩ :=
          nonempty_statedSp_two_mulEquiv_perm_six
        obtain ⟨eY⟩ := bar2_oUpperTwo_opp_equiv_alt_of_perm (barOfInter D.M Dsub)
          (k := 6) (Or.inr (by norm_num)) (eSp.trans eS6)
        obtain ⟨hJsimple, hJnc, hJcard⟩ :=
          jzero_props_of_equiv_simple (e0.trans eY) hsimple6 hnc6 360 hcard6
        exact ⟨hJsimple, hJnc, Or.inl hJcard⟩
      ·
        have hΩ' : IsOmegaPlus (Bar2 Dsub) 6 1 := by simpa [IsOmegaEps2] using hΩ
        obtain ⟨e, a, b, hab, hmap⟩ := exists_swap_of_isOmegaPlus_six hΩ' hCent
        obtain ⟨eY⟩ := bar2_oUpperTwo_opp_equiv_alt_of_swap (barOfInter D.M Dsub)
          (n := 8) (by norm_num) e hab hmap
        obtain ⟨hJsimple, hJnc, hJcard⟩ :=
          jzero_props_of_equiv_simple (e0.trans eY) hsimple6 hnc6 360 hcard6
        exact ⟨hJsimple, hJnc, Or.inl hJcard⟩
    ·
      obtain ⟨eY⟩ := bar2_oUpperTwo_opp_equiv_alt_of_swap (barOfInter D.M Dsub)
        (n := 8) (by norm_num) e hab hmap
      obtain ⟨hJsimple, hJnc, hJcard⟩ :=
        jzero_props_of_equiv_simple (e0.trans eY) hsimple6 hnc6 360 hcard6
      exact ⟨hJsimple, hJnc, Or.inl hJcard⟩
  · rcases hdata with ⟨ε, hΩ, hCent⟩ | ⟨hAlt, e, a, b, hab, hmap⟩
    ·
      obtain ⟨eSp⟩ := nonempty_mulEquiv_statedSp_of_isOmegaEps2
        (X := Bar2 Dsub) (Y := barOfInter D.M Dsub) (Or.inr rfl) hΩ hCent
      have hSpSimple : IsSimpleGroup ↥(StatedSp 3 (ZMod 2)) :=
        isSimpleGroup_statedSp_zmod_two
          (by norm_num)
      have hYsimple : IsSimpleGroup ↥(barOfInter D.M Dsub) :=
        (MulEquiv.isSimpleGroup_congr eSp).mpr hSpSimple
      have hYcard : Nat.card ↥(barOfInter D.M Dsub) = 1451520 := by
        rw [Nat.card_congr eSp.toEquiv,
          card_statedSp_zmod_two]
        decide +kernel
      have h2 : 2 ∣ Nat.card ↥(barOfInter D.M Dsub) := by rw [hYcard]; norm_num
      have hY2 : ¬ IsPGroup 2 ↥(barOfInter D.M Dsub) := by
        intro hp
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
        have h3 : 3 ∣ Nat.card ↥(barOfInter D.M Dsub) := by rw [hYcard]; norm_num
        rw [hn] at h3
        exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      obtain ⟨eY⟩ := nonempty_bar2_oUpperTwo_opp_equiv_of_isSimpleGroup
        (barOfInter D.M Dsub) hYsimple h2 hY2
      obtain ⟨hJsimple, hJnc, hJcard⟩ := jzero_props_of_equiv_simple (e0.trans eY) hYsimple
        (by
          intro hcomm
          letI : CommGroup ↥(barOfInter D.M Dsub) :=
            { (inferInstance : Group ↥(barOfInter D.M Dsub)) with
              mul_comm := hcomm.is_comm.comm }
          have hprime : (Nat.card ↥(barOfInter D.M Dsub)).Prime :=
            (CommGroup.is_simple_iff_prime_card (α := ↥(barOfInter D.M Dsub))).1 inferInstance
          rw [hYcard] at hprime
          norm_num at hprime)
        1451520 hYcard
      exact ⟨hJsimple, hJnc, Or.inr (Or.inr hJcard)⟩
    ·
      obtain ⟨eY⟩ := bar2_oUpperTwo_opp_equiv_alt_of_swap (barOfInter D.M Dsub)
        (n := 10) (by norm_num) e hab hmap
      obtain ⟨hJsimple, hJnc, hJcard⟩ :=
        jzero_props_of_equiv_simple (e0.trans eY) hsimple8 hnc8 20160 hcard8
      exact ⟨hJsimple, hJnc, Or.inr (Or.inl hJcard)⟩

section Certificates


theorem shape_of_ctx19_10_for_gap (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) :
    ((IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) ∨
      (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)])) := by
  have h1910 := h.h1910
  simp only [Setting1910] at h1910
  obtain ⟨-, h1 | h2 | h3⟩ := h1910
  · exact Or.inl ⟨h1.1, h1.2.1, h1.2.2.2⟩
  · rcases h2.2.2.2 with ⟨hL2, hcong⟩ | ⟨hSz, hcong⟩
    · have hL : L ∈ calC D.M := h.hyp.hL.1
      obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ :=
        S17.p42_alt2_of_ne h42 h.hyp.hp hL h2.2.1
      have hsq := isL2Square_bar2_conjClosure hL hxM hXsup hne hL2
      rw [← h2.1] at hsq
      exact Or.inr (Or.inl ⟨hsq, hcong⟩)
    · have hL : L ∈ calC D.M := h.hyp.hL.1
      obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ :=
        S17.p42_alt2_of_ne h42 h.hyp.hp hL h2.2.1
      have hsq := isSzSquare_bar2_conjClosure hL hxM hXsup hne hSz
      rw [← h2.1] at hsq
      exact Or.inr (Or.inr (Or.inl hsq))
  · rcases h3 with ⟨hshape, -, hpow, hcong⟩
    rcases hshape with hU3 | hL2sq
    · exact Or.inr (Or.inr (Or.inr ⟨hU3, hpow, hcong⟩))
    · exact Or.inr (Or.inl ⟨hL2sq, hcong⟩)

end Certificates

theorem not_isL2_of_jzero_card {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (hL2 : IsL2 X n)
    (hcard : Nat.card X ∈ ({3, 9, 60, 360, 20160, 1451520} : Finset ℕ)) : False := by
  have hcard_eq : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_L2_card hL2
  rw [hcard_eq] at hcard
  have hn1 : 1 ≤ n := by omega
  have hn2 : n ≠ 2 := by omega
  have hnot := l2_card_not_mem_jzeroShape hn1 hn2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  have hmem : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∈ ({3, 60, 360, 20160, 1451520} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcard ⊢
    rcases hcard with h | h | h | h | h | h
    · exact Or.inl h
    · exfalso
      have hq : 8 ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ n)
      have hq' : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 * 8 := by norm_num
          _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hq hq
          _ = (2 ^ n) ^ 2 := by ring
      have hq2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
      have hge : 504 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
        calc 504 = 8 * 63 := by norm_num
          _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul hq hq2
      omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  exact hnot hmem

section Certificates


theorem gap19_19_first (D : Data G) (h61 : UC6.R6_1 D) (hT : K_19_19_torusQS) :
    ∀ (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h → S17.R17_42At D V₀ V →
      ((P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub ∨ P19_16_4 D Dsub) →
        S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L →
        A ≤ normalizer ((S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) : Subgroup G) : Set G) →
        P19_19 D p L A Dsub (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h42 hc hJ hA_norm
  let J0 : Subgroup G := S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M))
  have hOpple : Opp 2 (Dsub ⊓ D.M) ≤ Dsub ⊓ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 _
  have hJ0le : J0 ≤ Dsub ⊓ D.M := (S17.oUpperTwo_le _).trans hOpple
  have hJ0M : J0 ≤ D.M := hJ0le.trans inf_le_right
  have hJ0N : J0 ≤ N := (hJ0le.trans inf_le_left).trans h.hD.1.1.le
  have hr : CFSG.Open.pRank p J0 ≤ 1 := pRank_le_one_of_r6_1 D h61 h hJ0M hJ0N
  have hr' : CFSG.pRank p ↥J0 ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hr
  have hn3 : 3 ≤ S17.nOf L := three_le_nOf_of_setting1910 h.ctx.h1910
  have hp : p.Prime := (D.sig_prime p h.ctx.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.ctx.hyp.hp).2
  have hO : S17.oUpperTwo J0 = J0 :=
    CFSG.GroupTheory.oddOrderClosure_oddOrderClosure (Opp 2 (Dsub ⊓ D.M))
  have hA2 : IsZModSq A (S17.nOf L) := h.ctx.hAcard
  have hshapeStrong := shape_of_ctx19_10_for_gap D h.ctx h42
  have hshape : ((IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) ∨
      (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)])) := by
    rcases hshapeStrong with hSp | hL2sq | hSz | hU3
    · exact Or.inl hSp
    · exact Or.inr (Or.inl hL2sq.1)
    · exact Or.inr (Or.inr (Or.inl hSz))
    · exact Or.inr (Or.inr (Or.inr hU3))
  have hT' := Inputs1719.k_19_19_torusInv_of_qs hT
  rcases hc with h1 | h2 | h3 | h4
  · obtain ⟨k, hk, hEk⟩ := jzero_type_of_p19_16_1 D h1
    rcases hk with rfl | rfl | rfl
    · obtain ⟨eJ⟩ := hEk
      have hcard : Nat.card (Bar2 J0) = 3 := by
        change Nat.card (Jzero D Dsub) = 3
        rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have hZ : Nonempty (Bar2 J0 ≃* Multiplicative (ZMod 3)) := by
        have hcardAlt : Nat.card (alternatingGroup (Fin 3)) = 3 := by
          rw [nat_card_alternatingGroup, Nat.card_fin]
          norm_num
        let eAltZ : alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3) :=
          mulEquivOfPrimeCardEq hcardAlt (by simp)
        exact ⟨eJ.trans eAltZ⟩
      have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
          IsQuasisimple (Bar2 J0) := by
        left
        exact ⟨IsPGroup.of_card (n := 1) (by norm_num [hcard]),
          by norm_num [hcard]⟩
      have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by norm_num [hcard]
      rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
        hJ hA_norm hO hr' hgroup h3dvd with hi | hii
      · exact Or.inr ⟨hi, Or.inl hZ, Or.inr (Or.inl h1)⟩
      · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 (by norm_num [hcard]))
    · obtain ⟨eJ⟩ := hEk
      have hcard : Nat.card (Bar2 J0) = 60 := by
        change Nat.card (Jzero D Dsub) = 60
        rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have hsimpleAlt : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by norm_num)
      have hncAlt : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three]
        norm_num
      have hsimple : IsSimpleGroup (Bar2 J0) :=
        (MulEquiv.isSimpleGroup_congr eJ).mpr hsimpleAlt
      have hnc : ¬ IsMulCommutative (Bar2 J0) :=
        CFSG.Quasithin.H13.not_isMulCommutative_of_mulEquiv eJ.symm hncAlt
      have hqs : IsQuasisimple (Bar2 J0) := by
        have hnab : ∃ a b : Bar2 J0, a * b ≠ b * a := by
          by_contra hcon
          push Not at hcon
          exact hnc ⟨⟨hcon⟩⟩
        exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
      have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
          IsQuasisimple (Bar2 J0) := Or.inr hqs
      have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by norm_num [hcard]
      rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
        hJ hA_norm hO hr' hgroup h3dvd with hi | hii
      · have hcomm : IsMulCommutative (Bar2 J0) :=
          isMulCommutative_bar2_of_subset_pCore_mul
            (isMulCommutative_of_isZModSq hA2) hi
        exact False.elim (hnc hcomm)
      · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 (by norm_num [hcard]))
    · obtain ⟨eJ⟩ := hEk
      have hcard : Nat.card (Bar2 J0) = 360 := by
        change Nat.card (Jzero D Dsub) = 360
        rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have hsimpleAlt : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by norm_num)
      have hncAlt : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three]
        norm_num
      have hsimple : IsSimpleGroup (Bar2 J0) :=
        (MulEquiv.isSimpleGroup_congr eJ).mpr hsimpleAlt
      have hnc : ¬ IsMulCommutative (Bar2 J0) :=
        CFSG.Quasithin.H13.not_isMulCommutative_of_mulEquiv eJ.symm hncAlt
      have hqs : IsQuasisimple (Bar2 J0) := by
        have hnab : ∃ a b : Bar2 J0, a * b ≠ b * a := by
          by_contra hcon
          push Not at hcon
          exact hnc ⟨⟨hcon⟩⟩
        exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
      have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
          IsQuasisimple (Bar2 J0) := Or.inr hqs
      have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by norm_num [hcard]
      rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
        hJ hA_norm hO hr' hgroup h3dvd with hi | hii
      · have hcomm : IsMulCommutative (Bar2 J0) :=
          isMulCommutative_bar2_of_subset_pCore_mul
            (isMulCommutative_of_isZModSq hA2) hi
        exact False.elim (hnc hcomm)
      · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 (by norm_num [hcard]))
  · obtain ⟨eZ⟩ := jzero_equiv_zmod_three_of_p19_16_2 D h h2
    have hcard : Nat.card (Bar2 J0) = 3 := by
      rw [Nat.card_congr eZ.toEquiv]
      simp
    have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
        IsQuasisimple (Bar2 J0) := by
      left
      exact ⟨IsPGroup.of_card (n := 1) (by norm_num [hcard]),
        by norm_num [hcard]⟩
    have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by norm_num [hcard]
    rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
      hJ hA_norm hO hr' hgroup h3dvd with hi | hii
    · exact Or.inr ⟨hi, Or.inl ⟨eZ⟩, Or.inr (Or.inr (Or.inl h2))⟩
    · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 (by norm_num [hcard]))
  · obtain ⟨eZ2⟩ := jzero_equiv_zmod_three_sq_of_p19_16_3 D h h3
    have hcard : Nat.card (Bar2 J0) = 9 := by
      rw [Nat.card_congr eZ2.toEquiv]
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod,
        ZMod.card]
    have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
        IsQuasisimple (Bar2 J0) := by
      left
      exact ⟨IsPGroup.of_card (n := 2) (by norm_num [hcard]),
        by norm_num [hcard]⟩
    have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by norm_num [hcard]
    rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
      hJ hA_norm hO hr' hgroup h3dvd with hi | hii
    · exact Or.inr ⟨hi, Or.inr ⟨eZ2⟩, Or.inr (Or.inr (Or.inr h3))⟩
    · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 (by norm_num [hcard]))
  · obtain ⟨hsimple, hnc, hcardcase⟩ := jzero_simple_of_p19_16_4 D h4
    have hqs : IsQuasisimple (Bar2 J0) := by
      have hnab : ∃ a b : Bar2 J0, a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨⟨hcon⟩⟩
      exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
    have hgroup : (IsPGroup 3 (Bar2 J0) ∧ Nat.card (Bar2 J0) ∣ 9) ∨
        IsQuasisimple (Bar2 J0) := Or.inr hqs
    have h3dvd : 3 ∣ Nat.card (Bar2 J0) := by
      rcases hcardcase with h | h | h <;> rw [h] <;> norm_num
    have hmem : Nat.card (Bar2 J0) ∈ ({3, 9, 60, 360, 20160, 1451520} : Finset ℕ) := by
      rcases hcardcase with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · rw [h]; norm_num
    rcases hT' G (IOf D p L) A J0 (S17.nOf L) p hn3 hp hp2 hshape h.ctx.hA hA2
      hJ hA_norm hO hr' hgroup h3dvd with hi | hii
    · have hcomm : IsMulCommutative (Bar2 J0) :=
        isMulCommutative_bar2_of_subset_pCore_mul
          (isMulCommutative_of_isZModSq hA2) hi
      exact False.elim (hnc hcomm)
    · exact False.elim (not_isL2_of_jzero_card hn3 hii.1 hmem)

theorem gap19_19_second (D : Data G) (h61 : UC6.R6_1 D) (hT : K_19_19_torusQS)
    (hLv : K_19_19_leviInv) (hL21 : K_19_21_levi) :
    ∀ (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h → S17.R17_42At D V₀ V →
      (P19_16_5 D Dsub →
        ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinComponentFamily D Dsub d K J →
          ∀ i : Fin d, J i ≤ IOf D p L → P19_19 D p L A Dsub (J i)) := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h42 h5 d K J hfam i hJi
  have hqOpen : CFSG.Open.IsQuasisimple (Bar2 Dsub) := h.hD.1.2.2
  have hq : CFSG.IsQuasisimple (Bar2 Dsub) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hqOpen)
  have hlist : List19_16_5 (BarInf Dsub) := h5.1
  have hpar : IsNontrivialParabolic (Bar2 Dsub) (barOfInter D.M Dsub) := h5.2
  have hfamIn : IsDynkinFamilyIn D.M Dsub d K J :=
    (isDynkinComponentFamily_iff D Dsub d K J).mp hfam
  have hK4 := hLv G D.M Dsub hq hlist hpar h.hO2 d K J hfamIn
  have hK4_2 := hK4.2 i
  have hJKi : J i ≤ K i := by
    rw [hfam.2.2.2.2 i]
    exact S17.oUpperTwo_le (K i)
  have hJiM : J i ≤ D.M := (hJKi.trans (hfam.1 i).2.1).trans inf_le_right
  have hJiN : J i ≤ N :=
    (hJKi.trans (hfam.1 i).2.1).trans inf_le_left |>.trans h.hD.1.1.le
  have hr : CFSG.Open.pRank p (J i) ≤ 1 := pRank_le_one_of_r6_1 D h61 h hJiM hJiN
  have hr' : CFSG.pRank p ↥(J i) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hr
  have hO : S17.oUpperTwo (J i) = J i := by
    rw [hfam.2.2.2.2 i]
    exact CFSG.GroupTheory.oddOrderClosure_oddOrderClosure (K i)
  have hA2 : IsZModSq A (S17.nOf L) := h.ctx.hAcard
  have hp : p.Prime := (D.sig_prime p h.ctx.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.ctx.hyp.hp).2
  have hn3 : 3 ≤ S17.nOf L := three_le_nOf_of_setting1910 h.ctx.h1910
  have hgroup : (IsPGroup 3 (Bar2 (J i)) ∧ Nat.card (Bar2 (J i)) ∣ 9) ∨
      IsQuasisimple (Bar2 (J i)) := by
    rcases hK4_2.2 with hqs | ⟨⟨eZ⟩, -⟩
    · exact Or.inr hqs
    · left
      have hcard : Nat.card (Bar2 (J i)) = 3 := by
        rw [Nat.card_congr eZ.toEquiv]
        simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      exact ⟨IsPGroup.of_card (n := 1) (by norm_num [hcard]),
        by norm_num [hcard]⟩
  have h3dvd : 3 ∣ Nat.card (Bar2 (J i)) := hK4_2.1
  have hAinf : A ≤ normalizer ((Dsub ⊓ D.M : Subgroup G) : Set G) :=
    le_normalizer_inf_of_ctx D h.ctx h17
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx
  have hA_K : A ≤ normalizer (K i) := by
    by_cases hL2exists : ∃ (k : Fin d) (n' : ℕ), 3 ≤ n' ∧ IsL2 (Bar2 (J k)) n'
    · obtain ⟨k, n', hn', hL2k⟩ := hL2exists
      have hL21' := hL21 G D.M Dsub hqOpen hlist hpar h.hO2 d K J hfamIn k n' hn' hL2k
      intro a ha
      exact hL21'.2.2 a (hAinf ha)
        (Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)) i
    · have hno : ∀ (k : Fin d) (n' : ℕ), 3 ≤ n' → ¬ IsL2 (Bar2 (J k)) n' := by
        intro k n' hn' hL2k
        exact hL2exists ⟨k, n', hn', hL2k⟩
      exact hK4.1 hno A h17 hAinf hAodd i
  have hA_J : A ≤ normalizer (J i) := by
    rw [hfam.2.2.2.2 i]
    exact fun a ha => normalizer_le_normalizer_oUpperTwo (K i) (hA_K ha)
  have hT' := Inputs1719.k_19_19_torusInv_of_qs hT
  have finish : ∀ (hs : ((IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) ∨
      (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]))),
      (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)] → P19_19 D p L A Dsub (J i) := by
    intro hs hcong
    have hres := hT' G (IOf D p L) A (J i) (S17.nOf L) p hn3 hp hp2 hs h.ctx.hA hA2
      hJi hA_J hO hr' hgroup h3dvd
    rcases hres with hi | hii
    · rcases hK4_2.2 with hqs | ⟨⟨eZ⟩, hLie⟩
      · have hqsOpen : CFSG.Open.IsQuasisimple (Bar2 (J i)) :=
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
            ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
              hqs)
        have hncq : ¬ IsMulCommutative (Bar2 (J i)) :=
          s16h_not_isMulCommutative_of_isQuasisimple hqsOpen
        have hcomm : IsMulCommutative (Bar2 (J i)) :=
          isMulCommutative_bar2_of_subset_pCore_mul
            (isMulCommutative_of_isZModSq hA2) hi
        exact False.elim (hncq hcomm)
      · exact Or.inr ⟨hi, Or.inl ⟨eZ⟩, Or.inl hLie⟩
    · obtain ⟨hL2, Kc, hKle, hKnorm, hKperf, hKqs, hJK, hKshape⟩ := hii
      have hsnI : (Kc.subgroupOf (IOf D p L)).IsSubnormal := hKnorm.isSubnormal
      have hsubI : CFSG.Open.IsSubnormal Kc (IOf D p L) :=
        (CFSG.Open.IsSubnormal.iff_subgroupOf hKle).mpr hsnI
      have hIOfN : ((IOf D p L).subgroupOf D.M).Normal :=
        IOf_normal D p h.ctx.hyp.hL.1
      have hsubM : CFSG.Open.IsSubnormal (IOf D p L) D.M :=
        (CFSG.Open.IsSubnormal.iff_subgroupOf (IOf_le_M D p h.ctx.hyp.hL.1.1.le)).mpr
          hIOfN.isSubnormal
      have hKqs' : CFSG.Open.IsQuasisimple (Bar2 Kc) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
            hKqs)
      have hcal : Kc ∈ calC D.M :=
        ⟨CFSG.Open.IsSubnormal.trans hsubI hsubM, hKperf, hKqs'⟩
      have hpBar : p ∣ Nat.card (Bar2 (J i)) := by
        have hcard : Nat.card (Bar2 (J i)) =
            2 ^ S17.nOf L * ((2 ^ S17.nOf L) ^ 2 - 1) :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_L2_card hL2
        have hdvd : p ∣ 2 ^ S17.nOf L + 1 :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_dvd_succ hcong
        rw [hcard]
        have h2 : (2 ^ S17.nOf L) ^ 2 - 1 =
            (2 ^ S17.nOf L + 1) * (2 ^ S17.nOf L - 1) := by
          rw [← Nat.sq_sub_sq, one_pow]
        rw [h2]
        exact (hdvd.mul_right _).mul_left _
      have hpJi : p ∣ Nat.card ↥(J i) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(J i))]
        exact dvd_mul_of_dvd_left hpBar _
      have hpK : p ∣ Nat.card ↥Kc := hpJi.trans (Subgroup.card_dvd_of_le hJK)
      have hpiset : p ∈ piSet Kc := ⟨hp, hpK⟩
      exact Or.inl ⟨Kc, ⟨hcal, hpiset⟩, hJK, hL2, hKshape⟩
  rcases shape_of_ctx19_10_for_gap D h.ctx h42 with hSp | hL2sq | hSz | hU3
  · exact finish (Or.inl hSp) hSp.2.2
  · exact finish (Or.inr (Or.inl hL2sq.1)) hL2sq.2
  · exact False.elim (false_of_isSzSquare_of_three_dvd_bar2 hSz hJi h3dvd)
  · exact finish (Or.inr (Or.inr (Or.inr hU3))) hU3.2.2

theorem gap19_19_holds (D : Data G) (h61 : UC6.R6_1 D) (hT : Inputs1719.K_19_19_torusQS)
    (hLv : Inputs1719.K_19_19_leviInv) (hL21 : Inputs1719.K_19_21_levi) : Gap19_19 D := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h42
  exact ⟨gap19_19_first D h61 hT V₀ V p L A t B r Y N Dsub H S h h17 h42,
    gap19_19_second D h61 hT hLv hL21 V₀ V p L A t B r Y N Dsub H S h h17 h42⟩

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
