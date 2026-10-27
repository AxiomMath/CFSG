module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.Quasithin.Background.JonesParshallG2Two
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953

public section

namespace CFSG.Quasithin.G11.P3G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open scoped commutatorElement

section

variable {K : Type} [Field K] [CharP K 2]

theorem cayleyMul_eq (x y : quasithinZorn K) : cayleyMul x y = quasithinZornMul x y := by
  simp only [cayleyMul, quasithinZornMul]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    simp [CharTwo.sub_eq_add]
  · funext i
    simp

theorem zorn_sq (x : quasithinZorn K) :
    quasithinZornMul x x = cayleyTr x • x + cayleyNorm x • (zornOne : quasithinZorn K) := by
  rw [zornMul_self]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨r, u, v, s⟩ := x
  simp only [cayleyTr, cayleyNorm, zornOne]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul, mul_one]
    linear_combination (-(r * s)) * h2
  · funext i
    simp
  · funext i
    simp
  · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul, mul_one]
    have : ∑ i, v i * u i = ∑ i, u i * v i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    linear_combination (-(r * s)) * h2

theorem zornAuto_tr_eq {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g)
    (x : quasithinZorn K) : cayleyTr (g x) = cayleyTr x ∧ cayleyNorm (g x) = cayleyNorm x := by
  have h1 : quasithinZornMul (g x) (g x) =
      cayleyTr x • g x + cayleyNorm x • (zornOne : quasithinZorn K) := by
    rw [← hg, zorn_sq, map_add, map_smul, map_smul, hg.map_one]
  have h2 := zorn_sq (g x)
  rw [h1] at h2
  have e1 := congrArg Prod.fst h2
  have e2 := congrArg (fun z => z.2.1) h2
  have e3 := congrArg (fun z => z.2.2.1) h2
  have e4 := congrArg (fun z => z.2.2.2) h2
  simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul, zornOne,
    mul_one, smul_zero, add_zero] at e1 e2 e3 e4
  set y := g x with hy
  have htr : cayleyTr y = cayleyTr x := by
    by_contra hne
    have hne' : cayleyTr x - cayleyTr y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hu : y.2.1 = 0 := by
      funext i
      have := congrFun e2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      have h3 : (cayleyTr x - cayleyTr y) * y.2.1 i = 0 := by linear_combination this
      exact (mul_eq_zero.mp h3).resolve_left hne'
    have hv : y.2.2.1 = 0 := by
      funext i
      have := congrFun e3 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      have h3 : (cayleyTr x - cayleyTr y) * y.2.2.1 i = 0 := by linear_combination this
      exact (mul_eq_zero.mp h3).resolve_left hne'
    have hs : y.2.2.2 = y.1 := by
      have h3 : (cayleyTr x - cayleyTr y) * (y.1 - y.2.2.2) = 0 := by
        linear_combination e1 - e4
      have := (mul_eq_zero.mp h3).resolve_left hne'
      linear_combination -this
    have hyc : y = (y.1, 0, 0, y.1) := by
      refine Prod.ext rfl (Prod.ext hu (Prod.ext hv hs))
    have hxc : x = (y.1, 0, 0, y.1) := by
      apply g.injective
      rw [← hy, hg.map_smul_one, ← hyc]
    apply hne
    have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have htx : cayleyTr x = 0 := by
      rw [hxc]
      simp only [cayleyTr]
      linear_combination y.1 * h2'
    have hty : cayleyTr y = 0 := by
      simp only [cayleyTr]
      rw [hs]
      linear_combination y.1 * h2'
    rw [htx, hty]
  refine ⟨htr, ?_⟩
  rw [htr] at e1
  exact (add_left_cancel e1).symm

theorem quasithinG2_eq_cayleyGroup : quasithinG2 K = cayleyGroup K := by
  apply le_antisymm
  · intro g hg
    have hz : IsZornAuto g := mem_quasithinG2_isZornAuto hg
    refine ⟨hz.map_one, fun x y => ?_, fun x => (zornAuto_tr_eq hz x).1,
      fun x => (zornAuto_tr_eq hz x).2⟩
    rw [cayleyMul_eq, cayleyMul_eq]
    exact hz x y
  · intro g hg
    obtain ⟨-, hm, -, -⟩ := hg
    refine Subgroup.subset_closure fun x y => ?_
    rw [← cayleyMul_eq, ← cayleyMul_eq]
    exact hm x y

end

noncomputable def commutatorG2Equiv :
    ↥⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆ ≃* ↥subG2 :=
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  haveI hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 1 (by norm_num)]
    norm_num
  let e : GaloisField 2 1 ≃+* ZMod 2 :=
    (ZMod.ringEquivOfPrime (GaloisField 2 1) Nat.prime_two hcard).symm
  (MulEquiv.subgroupCongr (by rw [quasithinG2_eq_cayleyGroup])).trans
    (((zornConj e).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator e).trans g2Two_commutator_eq)))

end CFSG.Quasithin.G11.P3G2
