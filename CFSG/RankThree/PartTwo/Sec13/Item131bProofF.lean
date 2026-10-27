module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section CentralProduct

variable {X : Type*} [Group X]

theorem commutator_eq_mul_of_commute {U V : Subgroup X} (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    {u u' v v' : X} (hu : u ∈ U) (hu' : u' ∈ U) (hv : v ∈ V) (hv' : v' ∈ V) :
    u * v * (u' * v') * (u * v)⁻¹ * (u' * v')⁻¹ =
      (u * u' * u⁻¹ * u'⁻¹) * (v * v' * v⁻¹ * v'⁻¹) := by
  let φ : U × V →* X := MonoidHom.noncommCoprod U.subtype V.subtype fun a b => hUV a a.2 b b.2
  have hφ : ∀ p : U × V, φ p = (p.1 : X) * p.2 := fun p => rfl
  have h := map_commutatorElement φ ((⟨u, hu⟩ : U), (⟨v, hv⟩ : V))
    ((⟨u', hu'⟩ : U), (⟨v', hv'⟩ : V))
  simp only [commutatorElement_def, Prod.mk_mul_mk, Prod.inv_mk, hφ, Subgroup.coe_mul,
    Subgroup.coe_inv] at h
  rw [← h]

end CentralProduct

section Factor

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_U_facts (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hcL : c ∈ L)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    ∃ U : Subgroup (lBarA c L A), (∀ u ∈ U, u ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * v = v * u) ∧
      (∀ x : lBarA c L A, ∃ u ∈ U, ∃ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), x = u * v) ∧
      U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) = Subgroup.zpowers (mkC (L := L) hD.mem_A) ∧
      ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ Subgroup.zpowers (mkC (L := L) hD.mem_A) := by
  obtain ⟨U, hU, hUΛ, hUV, hZU⟩ := isHeisCentral_facts hD hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set z := mkC (L := L) hD.mem_A with hz
  have hzΛ : z ∈ Λ := mkC_mem_lBar hD hcL
  set ZΛ := (Subgroup.center Λ).map Λ.subtype with hZΛ
  have hZΛcard : Nat.card ZΛ = 3 := by
    rw [hZΛ, Subgroup.card_map_of_injective Λ.subtype_injective, card_center_lBar hD, hZ3]
  have hUΛZ : U ⊓ Λ ≤ ZΛ := by
    rintro x ⟨hxU, hxΛ⟩
    refine ⟨⟨x, hxΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (hUΛ x hxU y y.2).symm
  have hUΛcard : Nat.card (U ⊓ Λ : Subgroup _) = 3 := by
    rw [← hZU, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  have hUΛeq : U ⊓ Λ = ZΛ := Subgroup.eq_of_le_of_card_ge hUΛZ (by rw [hZΛcard, hUΛcard])
  have hzZ : z ∈ U ⊓ Λ := by
    rw [hUΛeq]
    refine ⟨⟨z, hzΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_center_iff.mp (mkC_mem_center hD) y
  have hzpow : U ⊓ Λ = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [hUΛcard, Nat.card_zpowers, orderOf_mkC hD]
  refine ⟨U, fun u hu => ?_, hUΛ, fun x => ?_, hzpow, fun u hu u' hu' => ?_⟩
  · have h1 := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : U)
    rw [hU.2.2] at h1
    simpa using congrArg Subtype.val h1
  · have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U Λ hUΛ).2
    have hx : x ∈ ((U ⊔ Λ : Subgroup _) : Set _) := by
      rw [hUV]
      exact Subgroup.mem_top x
    rw [hcoe] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx
    exact ⟨u, hu, v, hv, rfl⟩
  · have h2 : (⁅(⟨u, hu⟩ : U), ⟨u', hu'⟩⁆ : U) ∈ commutator U :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at h2
    have h3 : ((⁅(⟨u, hu⟩ : U), ⟨u', hu'⟩⁆ : U) : lBarA c L A) ∈
        (Subgroup.center U).map U.subtype := ⟨_, h2, rfl⟩
    rw [hZU, hzpow] at h3
    simpa [commutatorElement_def] using h3

theorem card_sup_eq_nine {X : Type} [Group X] [Finite X] {x y : X} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 9 := by
  have hN1 : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [((Commute.zpow_left (hxy : Commute x y) k).symm).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers x k
  have h := Sec6.card_sup_mul_card_inf hN1
  have hbot : Subgroup.zpowers y ⊓ Subgroup.zpowers x = ⊥ := by
    rw [inf_comm]
    exact Sec12.inf_zpowers_eq_bot_of_not_mem hy hyx
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx, hy,
    sup_comm] at h
  exact h

theorem card_sup_sup_eq_27 {X : Type} [Group X] [Finite X] {x y w : X}
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hw : orderOf w = 3) (hxy : x * y = y * x)
    (hxw : x * w = w * x) (hyw : y * w = w * y) (hyx : y ∉ Subgroup.zpowers x)
    (hwxy : w ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers w : Subgroup X) = 27 ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 9 := by
  have hN1 : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [((Commute.zpow_left (hxy : Commute x y) k).symm).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers x k
  have h9 : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 9 := by
    have h := Sec6.card_sup_mul_card_inf hN1
    have hbot : Subgroup.zpowers y ⊓ Subgroup.zpowers x = ⊥ := by
      rw [inf_comm]
      exact Sec12.inf_zpowers_eq_bot_of_not_mem hy hyx
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx, hy,
      sup_comm] at h
    exact h
  refine ⟨?_, h9⟩
  have hN2 : Subgroup.zpowers w ≤
      Subgroup.normalizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    have hcomm : ∀ g ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X), w * g = g * w := by
      intro g hg
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
          Subgroup.centralizer ({w} : Set X) := by
        refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact hxw
        · exact hyw
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
    rw [hcomm g hg, mul_inv_cancel_right]
    exact hg
  have h := Sec6.card_sup_mul_card_inf hN2
  have hbot : Subgroup.zpowers w ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥ := by
    rw [inf_comm]
    exact Sec12.inf_zpowers_eq_bot_of_not_mem hw hwxy
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hw, h9, sup_comm] at h
  exact h

end Factor

section Construction

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_F_of_heis (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) {E : Subgroup G}
    (hEle : E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G))
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) {a : G} (haA : a ∈ A)
    (hac : a ∉ Subgroup.zpowers c) :
    ∃ F : Subgroup G, F ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      ¬ IsCyclic (F ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∧
      ¬ IsCyclic (F ⊓ L : Subgroup G) ∧ F ≤ Subgroup.centralizer ({a} : Set G) ∧
      E ≤ Subgroup.normalizer (F : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcL := mem_of_isHeisCentral hD hH
  have hZ3 := card_center_eq_three hty
  obtain ⟨hcE, -, -, -⟩ := e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  obtain ⟨U, hU3, hUΛ, hdec, hUΛz, hUU⟩ := exists_U_facts hD hH hcL hZ3
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHom hD).range with hAb
  set z := mkC (L := L) hD.mem_A with hz
  have hAbΛ : Ab ⊓ Λ = Subgroup.zpowers z := range_aBarHom_inf_lBar hD hH hcL hZ3
  have hzΛ : z ∈ Λ := mkC_mem_lBar hD hcL
  have hzU : z ∈ U := (hUΛz ▸ Subgroup.mem_zpowers z : z ∈ U ⊓ Λ).1
  have hzc : ∀ x : lBarA c L A, x * z = z * x := fun x =>
    (Subgroup.mem_center_iff.mp (mkC_mem_center hD) x)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [orderOf_mkC hD] at h
  set ab : lBarA c L A := aBarHom hD ⟨a, haA⟩ with hab
  obtain ⟨ua, hua, va, hva, habuv⟩ := hdec ab
  have hua3 := hU3 ua hua
  have huv : ua * va = va * ua := hUΛ ua hua va hva
  have hab3 : ab ^ 3 = 1 := by
    rw [hab, ← map_pow]
    have : (⟨a, haA⟩ : A) ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 a haA)
    rw [this, map_one]
  have hva3 : va ^ 3 = 1 := by
    have h := hab3
    rw [habuv, (Commute.mul_pow huv), hua3, one_mul] at h
    exact h
  have hmemc : ∀ b : A, aBarHom hD b ∈ Subgroup.zpowers z → (b : G) ∈ Subgroup.zpowers c := by
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hk' : aBarHom hD ((⟨c, hD.mem_A⟩ : A) ^ k) = aBarHom hD b := by
      rw [map_zpow, ← mkC_eq_aBarHom hD, hk]
    have heq := aBarHom_injective hD hk'
    rw [← heq]
    simp only [SubgroupClass.coe_zpow]
    exact Subgroup.zpow_mem_zpowers c k
  have hua_z : ua ∉ Subgroup.zpowers z := by
    intro h
    have habΛ : ab ∈ Λ := habuv ▸ mul_mem ((Subgroup.zpowers_le.mpr hzΛ) h) hva
    exact hac (hmemc ⟨a, haA⟩ (hAbΛ ▸ ⟨⟨_, rfl⟩, habΛ⟩))
  have hva_U : va ∉ U := by
    intro h
    have hvz : va ∈ Subgroup.zpowers z := hUΛz ▸ ⟨h, hva⟩
    have habU : ab ∈ U := habuv ▸ mul_mem hua ((Subgroup.zpowers_le.mpr hzU) hvz)
    exact hac (mem_zpowers_of_aBarHom_commute hD ⟨a, haA⟩ fun y hy => hUΛ ab habU y hy)
  have hua1 : ua ≠ 1 := fun h => hua_z (h ▸ Subgroup.one_mem _)
  have hva1 : va ≠ 1 := fun h => hva_U (h ▸ Subgroup.one_mem _)
  have hzo : orderOf z = 3 := orderOf_mkC hD
  have huao : orderOf ua = 3 := orderOf_eq_prime hua3 hua1
  have hvao : orderOf va = 3 := orderOf_eq_prime hva3 hva1
  have hzUa : Subgroup.zpowers z ⊔ Subgroup.zpowers ua ≤ U :=
    sup_le (Subgroup.zpowers_le.mpr hzU) (Subgroup.zpowers_le.mpr hua)
  obtain ⟨hF27, hF9⟩ := card_sup_sup_eq_27 hzo huao hvao (hzc ua).symm (hzc va).symm huv
    (fun h => hua_z h) (fun h => hva_U (hzUa h))
  set Fb := Subgroup.zpowers z ⊔ Subgroup.zpowers ua ⊔ Subgroup.zpowers va with hFb
  have hFbe : CFSG.Assembly.IsElemAbelian 3 Fb := by
    refine Sec15.isElemAbelian_sup_zpowers (Sec15.isElemAbelian_sup_zpowers
      (isElemAbelian_zpowers hz3) hua3 fun e he => ?_) hva3 fun e he => ?_
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact (Commute.zpow_left ((hzc ua).symm : Commute z ua) k).eq
    · have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers ua ≤
          Subgroup.centralizer ({va} : Set (lBarA c L A)) := by
        refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact (hzc va).symm
        · exact huv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have habF : ab ∈ Fb := habuv ▸ mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers ua))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers va))
  have hzF : z ∈ Fb := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hzpF : Subgroup.zpowers z ≤ Fb := Subgroup.zpowers_le.mpr hzF
  have hFbc : ∀ x ∈ Fb, ∀ y ∈ Fb, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFbe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcu : ∀ x : lBarA c L A, x * ua * x⁻¹ * ua⁻¹ ∈ Subgroup.zpowers z := by
    intro x
    obtain ⟨ux, hux, vx, hvx, rfl⟩ := hdec x
    have h := commutator_eq_mul_of_commute hUΛ hux hua hvx (Subgroup.one_mem Λ)
    rw [mul_one, mul_one, inv_one, mul_one, mul_inv_cancel, mul_one] at h
    rw [h]
    exact hUU ux hux ua hua
  have hcv : ∀ x : lBarA c L A, x * ab * x⁻¹ * ab⁻¹ ∈ Ab →
      x * va * x⁻¹ * va⁻¹ ∈ Subgroup.zpowers z := by
    intro x hx
    obtain ⟨ux, hux, vx, hvx, rfl⟩ := hdec x
    have h1 := commutator_eq_mul_of_commute hUΛ hux hua hvx hva
    have h2 := commutator_eq_mul_of_commute hUΛ hux (Subgroup.one_mem U) hvx hva
    simp only [one_mul, mul_one, inv_one, mul_inv_cancel] at h2
    rw [← habuv] at h1
    have hzAb : Subgroup.zpowers z ≤ Ab := Subgroup.zpowers_le.mpr ⟨⟨c, hD.mem_A⟩, rfl⟩
    have hmemAb : ux * vx * va * (ux * vx)⁻¹ * va⁻¹ ∈ Ab := by
      rw [h2]
      have h3 : vx * va * vx⁻¹ * va⁻¹ =
          (ux * ua * ux⁻¹ * ua⁻¹)⁻¹ * (ux * vx * ab * (ux * vx)⁻¹ * ab⁻¹) := by
        rw [h1]
        group
      rw [h3]
      exact mul_mem (inv_mem (hzAb (hUU ux hux ua hua))) hx
    have hmemΛ : ux * vx * va * (ux * vx)⁻¹ * va⁻¹ ∈ Λ := by
      rw [h2]
      exact mul_mem (mul_mem (mul_mem hvx hva) (inv_mem hvx)) (inv_mem hva)
    rw [← hAbΛ]
    exact ⟨hmemAb, hmemΛ⟩
  have hnorm : ∀ x : lBarA c L A, x * ua * x⁻¹ * ua⁻¹ ∈ Subgroup.zpowers z →
      x * va * x⁻¹ * va⁻¹ ∈ Subgroup.zpowers z →
      x ∈ Subgroup.normalizer (Fb : Set (lBarA c L A)) := by
    intro x hxu hxv
    have hle : Fb ≤ Fb.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap] <;>
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      · rw [hzc x, mul_inv_cancel_right]
        exact hzF
      · have h : x * ua * x⁻¹ = (x * ua * x⁻¹ * ua⁻¹) * ua := by group
        rw [h]
        exact mul_mem (hzpF hxu) (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers ua)))
      · have h : x * va * x⁻¹ = (x * va * x⁻¹ * va⁻¹) * va := by group
        rw [h]
        exact mul_mem (hzpF hxv) (Subgroup.mem_sup_right (Subgroup.mem_zpowers va))
    exact Subgroup.mem_normalizer_fintype fun y hy => by
      simpa [MulAut.conj_apply] using hle hy
  have hAbF : ∀ b : A, aBarHom hD b ∈ Subgroup.normalizer (Fb : Set (lBarA c L A)) := by
    intro b
    refine hnorm _ (hcu _) (hcv _ ?_)
    have hcomm : aBarHom hD b * ab = ab * aBarHom hD b := by
      rw [hab, ← map_mul, ← map_mul, hD.isElemAbelian.1.is_comm.comm b ⟨a, haA⟩]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hFAb : Fb ≤ Subgroup.normalizer (Ab : Set (lBarA c L A)) := by
    have hzAb : z ∈ Ab := ⟨⟨c, hD.mem_A⟩, (mkC_eq_aBarHom hD).symm⟩
    have hua' : ua ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have h1 := hcu y
      have h2 : ua * y * ua⁻¹ = (y * ua * y⁻¹ * ua⁻¹)⁻¹ * y := by group
      rw [h2]
      exact mul_mem (inv_mem ((Subgroup.zpowers_le.mpr hzAb) h1)) hy
    have habN : ab ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) :=
      Subgroup.le_normalizer ⟨_, rfl⟩
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact Subgroup.le_normalizer hzAb
    · exact hua'
    · have hv : va = ua⁻¹ * ab := by rw [habuv]; group
      rw [hv]
      exact mul_mem (inv_mem hua') habN
  have hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hD.A_le_normalizer_zpowers
  have hLAH : L ⊔ A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt) hAH
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (hEle.trans inf_le_left).trans hLAH
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := hEle.trans inf_le_right
  set Fb' := Fb.map (lBarA c L A).subtype with hFb'
  have hAbmap : Ab.map (lBarA c L A).subtype = Sec12.lBar c A := by
    ext y
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨⟨b, hAH b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, (aBarHom_apply hD b).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨aBarHom hD ⟨x, Subgroup.mem_subgroupOf.mp hx⟩, ⟨_, rfl⟩, aBarHom_apply hD _⟩
  have hEbar : ∀ (e : G) (he : e ∈ E), QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ⟨e, hEH he⟩ ∈ lBarA c L A :=
    fun e he => ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.mpr ((hEle.trans inf_le_left) he), rfl⟩
  have hEF : ∀ (e : G) (he : e ∈ E), (⟨_, hEbar e he⟩ : lBarA c L A) ∈
      Subgroup.normalizer (Fb : Set (lBarA c L A)) := by
    intro e he
    refine hnorm _ (hcu _) (hcv _ ?_)
    have hxA : e * a * e⁻¹ * a⁻¹ ∈ A :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hEA he) a).mp haA) (inv_mem haA)
    refine ⟨⟨_, hxA⟩, Subtype.ext ?_⟩
    rw [aBarHom_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hab, aBarHom_apply, ← map_mul, ← map_inv]
    rfl
  have hAbFb' : Sec12.lBar c A ≤ Subgroup.normalizer (Fb' : Set (HBar c)) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := Subgroup.le_normalizer_map (lBarA c L A).subtype
      ⟨aBarHom hD ⟨x, Subgroup.mem_subgroupOf.mp hx⟩,
        hAbF ⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    rwa [Subgroup.coe_subtype, aBarHom_apply] at h
  have hEbFb' : Sec12.lBar c E ≤ Subgroup.normalizer (Fb' : Set (HBar c)) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := Subgroup.le_normalizer_map (lBarA c L A).subtype
      ⟨⟨_, hEbar x (Subgroup.mem_subgroupOf.mp hx)⟩, hEF x (Subgroup.mem_subgroupOf.mp hx), rfl⟩
    exact h
  have hEbAb' : Sec12.lBar c E ≤ Subgroup.normalizer (Sec12.lBar c A : Set (HBar c)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_lBar (hEA (Subgroup.mem_subgroupOf.mp hx))
  have hFbAb' : Fb' ≤ Subgroup.normalizer (Sec12.lBar c A : Set (HBar c)) := by
    rw [← hAbmap]
    exact (Subgroup.map_mono hFAb).trans (Subgroup.le_normalizer_map _)
  have hA3 : IsPGroup 3 (A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    fun g => ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  have hE3 : IsPGroup 3 (E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    fun g => ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hEe.2 _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  have hFb3 : IsPGroup 3 Fb := fun g => ⟨1, Subtype.ext (by simpa using hFbe.2 _ g.2)⟩
  have hB3 : IsPGroup 3 ((Sec12.lBar c A ⊔ Sec12.lBar c E ⊔ Fb' : Subgroup (HBar c))) :=
    ((hA3.map _).to_sup_of_normal_left' (hE3.map _) hEbAb').to_sup_of_normal_right'
      (hFb3.map _) (sup_le hAbFb' hEbFb')
  have hBM : Sec12.lBar c A ⊔ Sec12.lBar c E ⊔ Fb' ≤
      ((L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) :=
    sup_le (sup_le (Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_right))
      (Subgroup.map_mono (Subgroup.subgroupOf_mono _ (hEle.trans inf_le_left))))
      (Subgroup.map_subtype_le _)
  have hEA' : E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.normalizer ((A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    show e * y * e⁻¹ ∈ A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))
    rw [Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hEA (Subgroup.mem_subgroupOf.mp he)) _).mp hy'
  have hE₀3 := hA3.to_sup_of_normal_left' hE3 hEA'
  obtain ⟨S, hE₀S, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hB3 hBM hE₀3
    (sup_le (Subgroup.subgroupOf_mono _ le_sup_right)
      (Subgroup.subgroupOf_mono _ (hEle.trans inf_le_left)))
    (by rw [Subgroup.map_sup]; exact le_sup_left)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  set F₁ := S ⊓ Fb'.comap (QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) with hF₁
  have hF₁S : F₁ ≤ S := inf_le_left
  have hinjF := hinj.mono hF₁S
  have hFbB : Fb' ≤ Sec12.lBar c A ⊔ Sec12.lBar c E ⊔ Fb' := le_sup_right
  have hF₁map : F₁.map (QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) = Fb' := by
    rw [hF₁, map_inf_comap_eq, hSB]
    exact inf_eq_right.mpr hFbB
  have hF₁card : Nat.card F₁ = 27 := by
    rw [← card_map_eq_of_injOn _ hinjF, hF₁map, hFb',
      Subgroup.card_map_of_injective (lBarA c L A).subtype_injective, hF27]
  have hF₁e : CFSG.Assembly.IsElemAbelian 3 F₁ :=
    isElemAbelian_of_injOn _ hinjF (by rw [hF₁map]; exact isElemAbelian_map hFbe _)
  have hAS : A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤ S :=
    le_sup_left.trans hE₀S
  have hES : E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤ S :=
    le_sup_right.trans hE₀S
  have hmemF : ∀ f ∈ F₁, QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) f ∈ Fb' := fun f hf => hf.2
  have hFbc' : ∀ x ∈ Fb', ∀ y ∈ Fb', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hFbc x hx y hy)
  have habF' : ((ab : lBarA c L A) : HBar c) ∈ Fb' := ⟨ab, habF, rfl⟩
  refine ⟨F₁.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype, le_inf ?_ ?_,
    isElemAbelian_map hF₁e _, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨f, hf, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hSM (hF₁S hf))
  ·
    rintro _ ⟨f, hf, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    set x' : Subgroup.normalizer (Subgroup.zpowers c : Set G) := ⟨x, hAH hx⟩
    have hx'S : x' ∈ S := hAS (Subgroup.mem_subgroupOf.mpr hx)
    have hconjS : f * x' * f⁻¹ ∈ S := mul_mem (mul_mem (hF₁S hf) hx'S) (inv_mem (hF₁S hf))
    have himg : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) (f * x' * f⁻¹) ∈ Sec12.lBar c A := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hFbAb' (hmemF f hf)) _).mp
        ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := himg
    have := hinj (hAS hy) hconjS hyeq
    have h2 : ((f * x' * f⁻¹ : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G) ∈ A :=
      this ▸ Subgroup.mem_subgroupOf.mp hy
    simpa using h2
  · rw [Subgroup.card_map_of_injective Subtype.coe_injective, hF₁card]
  ·
    set T := (Subgroup.zpowers z ⊔ Subgroup.zpowers ua).map (lBarA c L A).subtype with hT
    have hTFb : T ≤ Fb' := Subgroup.map_mono le_sup_left
    have hTcard : Nat.card T = 9 := by
      rw [hT, Subgroup.card_map_of_injective (lBarA c L A).subtype_injective, hF9]
    have hFTcard : Nat.card ((F₁ ⊓ T.comap (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))))).map
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective Subtype.coe_injective,
        ← card_map_eq_of_injOn _ (hinjF.mono inf_le_left), map_inf_comap_eq, hF₁map,
        inf_eq_right.mpr hTFb, hTcard]
    refine not_isCyclic_of_nine_le (fun x hx => (isElemAbelian_map hF₁e _).2 x hx.1)
      (hFTcard ▸ Subgroup.card_le_of_le ?_)
    rintro _ ⟨f, ⟨hf, hfT⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, mem_thetaQuotCentralizer_of_mk_commute hD.mem_thetaComponentsAt
      (g := f) ?_ fun l hl => ?_⟩
    · exact (sup_le Subgroup.le_normalizer hD.le_normalizer)
        (Subgroup.mem_subgroupOf.mp (hSM (hF₁S hf)))
    · obtain ⟨t, ht, hteq⟩ := Subgroup.mem_comap.mp hfT
      have hlΛ : (⟨QuotientGroup.mk' _ l, lBar_le_lBarA ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩⟩ :
          lBarA c L A) ∈ Λ :=
        Subgroup.mem_subgroupOf.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have h := hUΛ t (hzUa ht) _ hlΛ
      rw [← hteq]
      exact congrArg Subtype.val h
  ·
    have hva_z : va ∉ Subgroup.zpowers z := fun h => hva_U ((Subgroup.zpowers_le.mpr hzU) h)
    set T := (Subgroup.zpowers z ⊔ Subgroup.zpowers va).map (lBarA c L A).subtype with hT
    have hTFb : T ≤ Fb' := Subgroup.map_mono (sup_le hzpF (Subgroup.zpowers_le.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers va))))
    have hTcard : Nat.card T = 9 := by
      rw [hT, Subgroup.card_map_of_injective (lBarA c L A).subtype_injective,
        card_sup_eq_nine hzo hvao (hzc va).symm hva_z]
    have hTΛ : T ≤ Sec12.lBar c L := by
      rintro _ ⟨v, hv, rfl⟩
      have hvΛ : v ∈ Λ := (sup_le (Subgroup.zpowers_le.mpr hzΛ) (Subgroup.zpowers_le.mpr hva)) hv
      exact Subgroup.mem_subgroupOf.mp hvΛ
    have hFTcard : Nat.card ((F₁ ⊓ T.comap (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))))).map
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective Subtype.coe_injective,
        ← card_map_eq_of_injOn _ (hinjF.mono inf_le_left), map_inf_comap_eq, hF₁map,
        inf_eq_right.mpr hTFb, hTcard]
    refine not_isCyclic_of_nine_le (fun x hx => (isElemAbelian_map hF₁e _).2 x hx.1)
      (hFTcard ▸ Subgroup.card_le_of_le ?_)
    rintro _ ⟨f, ⟨hf, hfT⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, mem_of_mk_mem_lBar hD.mem_thetaComponentsAt (k := 1) ?_
      (hTΛ (Subgroup.mem_comap.mp hfT))⟩
    rw [pow_one]
    exact hF₁e.2 f hf
  ·
    rintro _ ⟨f, hf, rfl⟩
    set a' : Subgroup.normalizer (Subgroup.zpowers c : Set G) := ⟨a, hAH haA⟩
    have ha'S : a' ∈ S := hAS (Subgroup.mem_subgroupOf.mpr haA)
    have hcS : f * a' * f⁻¹ * a'⁻¹ ∈ S :=
      mul_mem (mul_mem (mul_mem (hF₁S hf) ha'S) (inv_mem (hF₁S hf))) (inv_mem ha'S)
    have hπa : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) a' = ((ab : lBarA c L A) : HBar c) := by
      rw [hab, aBarHom_apply]
    have himg : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) (f * a' * f⁻¹ * a'⁻¹) =
        QuotientGroup.mk' _ 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπa, hFbc' _ (hmemF f hf) _ habF',
        map_one]
      group
    have h1 := hinj hcS (Subgroup.one_mem S) himg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : f * a' = a' * f := by
      calc f * a' = f * a' * f⁻¹ * a'⁻¹ * (a' * f) := by group
        _ = a' * f := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  ·
    intro e he
    set e' : Subgroup.normalizer (Subgroup.zpowers c : Set G) := ⟨e, hEH he⟩
    have he'S : e' ∈ S := hES (Subgroup.mem_subgroupOf.mpr he)
    have he'N : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) e' ∈
        Subgroup.normalizer (Fb' : Set (HBar c)) :=
      hEbFb' ⟨e', Subgroup.mem_subgroupOf.mpr he, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨f, hf, rfl⟩ := hy
    refine ⟨e' * f * e'⁻¹, Subgroup.mem_inf.mpr
      ⟨S.mul_mem (S.mul_mem he'S (hF₁S hf)) (S.inv_mem he'S), ?_⟩, rfl⟩
    show QuotientGroup.mk' _ (e' * f * e'⁻¹) ∈ Fb'
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp he'N _).mp (hmemF f hf)

end Construction

end CFSG.RankThree.PartTwo.Sec13.Item131bProof
