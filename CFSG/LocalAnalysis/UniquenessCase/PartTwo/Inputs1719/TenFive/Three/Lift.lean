module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Bounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics
import CFSG.Quasithin.Background.E6TwentyTwoA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem four_le_rkIdx_of_quot_genGood (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hZ : ∃ k : ℕ, Nat.card (center ↥L) = 3 ^ k) {t : MulAut W}
    (σ : MulAut ↥L) (σ' : MulAut (↥L ⧸ center ↥L))
    (hσ : ∀ l : ↥L, ((σ l : ↥L) : MulAut W) = t * l * t⁻¹)
    (hσ' : ∀ l : ↥L, σ' (l : ↥L ⧸ center ↥L) = ((σ l : ↥L) : ↥L ⧸ center ↥L))
    (hgen : IsGenGood σ') : 4 ≤ rkIdx (fixV (zpowers t)) := by
  classical
  obtain ⟨k, g, y, r, hr, hy, hyD, hd⟩ := hgen
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h0 : dParam 2 = 0 := by
      rw [dParam]
      rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero]
    rw [h0] at hd
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    rw [SevenFour.dParam_eq_of_small.1] at hd
    omega
  let gL : Fin k → ↥L := fun i => (QuotientGroup.mk'_surjective (center ↥L) (g i)).choose
  have hgL : ∀ i, (QuotientGroup.mk' (center ↥L)) (gL i) = g i :=
    fun i => (QuotientGroup.mk'_surjective (center ↥L) (g i)).choose_spec
  have hgLq : ∀ i, ((gL i : ↥L) : ↥L ⧸ center ↥L) = g i := by
    intro i
    rw [← QuotientGroup.mk'_apply]
    exact hgL i
  let C : Subgroup ↥L := closure (Set.range fun i => (gL i)⁻¹ * σ (gL i))
  have hterm : ∀ i, (QuotientGroup.mk' (center ↥L)) ((gL i)⁻¹ * σ (gL i)) =
      (g i)⁻¹ * σ' (g i) := by
    intro i
    rw [map_mul, map_inv, hgL i]
    rw [show (QuotientGroup.mk' (center ↥L)) (σ (gL i)) = σ' (g i) by
      rw [QuotientGroup.mk'_apply, ← hσ' (gL i), hgLq i]]
  have hCmap : C.map (QuotientGroup.mk' (center ↥L)) =
      closure (Set.range fun i => (g i)⁻¹ * σ' (g i)) := by
    rw [show C = closure (Set.range fun i => (gL i)⁻¹ * σ (gL i)) from rfl,
      MonoidHom.map_closure, ← Set.range_comp']
    exact congrArg Subgroup.closure (congrArg Set.range (funext hterm))
  have hy_mem : y ∈ C.map (QuotientGroup.mk' (center ↥L)) := by
    rw [hCmap]
    exact hyD
  obtain ⟨yl, hylC, hylval⟩ := Subgroup.mem_map.mp hy_mem
  obtain ⟨m, hm⟩ := hZ
  have hcop : Nat.Coprime (Nat.card (center ↥L)) r := by
    rw [hm]
    simpa using Nat.coprime_pow_primes m 1 Nat.prime_three hr (Ne.symm hr3)
  set n := Nat.card (center ↥L) with hn
  set yh : ↥L := yl ^ n with hyhdef
  have hyhC : yh ∈ C := C.pow_mem hylC n
  have hyhmk : (QuotientGroup.mk' (center ↥L)) yh = y ^ n := by
    rw [hyhdef, map_pow, hylval]
  have hyhimgord : orderOf ((QuotientGroup.mk' (center ↥L)) yh) = r := by
    rw [hyhmk, Nat.Coprime.orderOf_pow (h := by rw [hy]; exact hcop.symm), hy]
  have hylrZ : yl ^ r ∈ center ↥L := by
    have h : (QuotientGroup.mk' (center ↥L)) (yl ^ r) = 1 := by
      rw [map_pow, hylval, ← hy, pow_orderOf_eq_one]
    have hmem := MonoidHom.mem_ker.mpr h
    rwa [QuotientGroup.ker_mk'] at hmem
  have hzpow : ((⟨yl ^ r, hylrZ⟩ : ↥(center ↥L)) ^ n) = 1 := by
    simp [n]
  have hylrn : (yl ^ r) ^ n = 1 := by
    simpa using congrArg (Subtype.val) hzpow
  have hyhpow : yh ^ r = 1 := by
    rw [hyhdef]
    calc (yl ^ n) ^ r = yl ^ (n * r) := (pow_mul yl n r).symm
      _ = yl ^ (r * n) := by rw [Nat.mul_comm]
      _ = (yl ^ r) ^ n := pow_mul yl r n
      _ = 1 := hylrn
  have hyhne : yh ≠ 1 := by
    intro h1
    have h : (QuotientGroup.mk' (center ↥L)) yh = 1 := by rw [h1, map_one]
    have h2 := hyhimgord
    rw [h, orderOf_one] at h2
    exact hr.ne_one h2.symm
  have : Fact r.Prime := ⟨hr⟩
  have hyhord : orderOf yh = r := orderOf_eq_prime hyhpow hyhne
  let yA : MulAut W := (yh : MulAut W)
  have hyAord : orderOf yA = r := (Subgroup.orderOf_coe yh).trans hyhord
  have hCsub : C.map L.subtype = closure (Set.range fun i =>
      (((gL i : ↥L) : MulAut W))⁻¹ * (t * ((gL i : ↥L) : MulAut W) * t⁻¹)) := by
    rw [show C = closure (Set.range fun i => (gL i)⁻¹ * σ (gL i)) from rfl,
      MonoidHom.map_closure, ← Set.range_comp']
    exact congrArg Subgroup.closure (congrArg Set.range (funext fun i => by
      change L.subtype ((gL i)⁻¹ * σ (gL i)) =
        ((gL i : ↥L) : MulAut W)⁻¹ * (t * ((gL i : ↥L) : MulAut W) * t⁻¹)
      rw [map_mul, map_inv]
      simp only [Subgroup.coe_subtype]
      rw [hσ (gL i)]))
  have hyD' : yA ∈ closure (Set.range fun i =>
      (((gL i : ↥L) : MulAut W))⁻¹ * (t * ((gL i : ↥L) : MulAut W) * t⁻¹)) := by
    rw [← hCsub]
    exact Subgroup.mem_map_of_mem L.subtype hyhC
  exact four_le_rkIdx_of_gen hW (fun i => ((gL i : ↥L) : MulAut W)) hr hyAord hyD' hd

private noncomputable def quotCenterEquivBot {L : Subgroup (MulAut W)}
    (hZ : center ↥L = ⊥) : (↥L ⧸ center ↥L) ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

omit [Finite W] in
private theorem quotCenterEquivBot_mk {L : Subgroup (MulAut W)} (hZ : center ↥L = ⊥)
    (l : ↥L) : quotCenterEquivBot hZ (l : ↥L ⧸ center ↥L) = l := by
  change ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    (QuotientGroup.mk' (center ↥L) l) = l
  rw [QuotientGroup.mk'_apply, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [← QuotientGroup.quotientBot_symm_apply l]
  exact QuotientGroup.quotientBot.apply_symm_apply l

omit [Finite W] in
private theorem mk_quotCenterEquivBot {L : Subgroup (MulAut W)} (hZ : center ↥L = ⊥)
    (q : ↥L ⧸ center ↥L) :
    (QuotientGroup.mk' (center ↥L)) (quotCenterEquivBot hZ q) = q := by
  apply (quotCenterEquivBot hZ).injective
  rw [QuotientGroup.mk'_apply, quotCenterEquivBot_mk]

private theorem four_le_mParam_of_quot_aut {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L)
    (h : ∀ (t : MulAut W) (_htY : t ∈ Y) (_ht : orderOf t = 2)
      (σ : MulAut ↥L) (σ' : MulAut (↥L ⧸ center ↥L))
      (_hσ : ∀ l : ↥L, ((σ l : ↥L) : MulAut W) = t * l * t⁻¹)
      (_hσ' : ∀ l : ↥L, σ' (l : ↥L ⧸ center ↥L) = ((σ l : ↥L) : ↥L ⧸ center ↥L))
      (_hord : orderOf σ' = 2), 4 ≤ rkIdx (fixV (zpowers t))) :
    4 ≤ E3.mParam Y := by
  have hY : ∃ t ∈ Y, orderOf t = 2 := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
      ((E6.two_dvd_card_of_isQuasisimple hLq).trans (Subgroup.card_dvd_of_le hLY))
    exact ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩
  refine SevenFour.le_mParam_of_forall hY ?_
  intro t htY ht
  obtain ⟨σ, σ', hσ, hσ', hord⟩ := exists_quotAut_of_involution hLY hLn hF hLq hO2 htY ht
  exact h t htY ht σ σ' hσ hσ' hord

theorem four_le_mParam_of_involGood (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L) (hZ : center ↥L = ⊥)
    (hI : InvolGood (↥L ⧸ center ↥L)) : 4 ≤ E3.mParam Y := by
  classical
  refine four_le_mParam_of_quot_aut hLY hLn hF hLq hO2 ?_
  intro t htY ht σ σ' hσ hσ' hord
  rcases hI σ' hord with ⟨xb, hxb, hinv, hgood⟩ | hgen
  · let e := quotCenterEquivBot hZ
    let x : ↥L := e xb
    have hxq : (x : ↥L ⧸ center ↥L) = xb := mk_quotCenterEquivBot hZ xb
    have hxgood : IsExtraGood x := IsExtraGood.map (f := e.toMonoidHom) e.injective hgood
    have hxord : orderOf x = 3 := (MulEquiv.orderOf_eq e xb).trans hxb
    have hσx : σ x = x⁻¹ := by
      apply (show Function.Injective (QuotientGroup.mk' (center ↥L)) from
        (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hZ]))
      calc (QuotientGroup.mk' (center ↥L)) (σ x)
          = σ' ((QuotientGroup.mk' (center ↥L)) x) := (hσ' x).symm
        _ = σ' xb := by rw [QuotientGroup.mk'_apply, hxq]
        _ = xb⁻¹ := hinv
        _ = (QuotientGroup.mk' (center ↥L)) (x⁻¹) := by
          rw [map_inv, QuotientGroup.mk'_apply, hxq]
    have hxW : orderOf ((x : ↥L) : MulAut W) = 3 :=
      (Subgroup.orderOf_coe x).trans hxord
    have hinvW : t * ((x : ↥L) : MulAut W) * t⁻¹ = ((x : ↥L) : MulAut W)⁻¹ := by
      rw [← hσ x, hσx]
      simp
    have hgoodW : IsExtraGood ((x : ↥L) : MulAut W) :=
      IsExtraGood.map (f := L.subtype) L.subtype_injective hxgood
    exact (by norm_num : 4 ≤ 6).trans
      (six_le_rkIdx_of_inverts_extraGood hW ht hxW hinvW hgoodW)
  · exact four_le_rkIdx_of_quot_genGood hW
      ⟨0, by rw [hZ, Subgroup.card_bot, pow_zero]⟩ σ σ' hσ hσ' hgen

theorem four_le_mParam_of_involGen (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L)
    (hZ : ∃ k : ℕ, Nat.card (center ↥L) = 3 ^ k) (hI : InvolGen (↥L ⧸ center ↥L)) :
    4 ≤ E3.mParam Y := by
  classical
  refine four_le_mParam_of_quot_aut hLY hLn hF hLq hO2 ?_
  intro t htY ht σ σ' hσ hσ' hord
  exact four_le_rkIdx_of_quot_genGood hW hZ σ σ' hσ hσ' (hI σ' hord)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
