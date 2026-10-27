module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux2
public import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux4
public import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux5

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

theorem lup8f_f2_commute (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame1 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    ∀ b b' : ↥(lup8f_E' L Bs), F.mat b * F.mat b' = F.mat b' * F.mat b := by
  subst hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card K = 4 := M.card_K
  have hn3 : 3 ≤ n := by omega
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hSS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hNT : GGNoTransvection 3 Bs := hS.1.2.2.2.1
  have hxo : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxBs) hSS.2.2.1
  set x' : lup8f_HT L Bs := ⟨x, Subgroup.mem_sup_left hxL⟩ with hx'
  have hxL' : x' ∈ lup8f_L' L Bs := Subgroup.mem_subgroupOf.mpr hxL
  have hxE' : x' ∈ lup8f_E' L Bs := Subgroup.mem_subgroupOf.mpr hxBs
  have hxN : x' ∉ C.N := by
    intro hxN
    have h1 : orderOf x' ∣ Nat.card C.N := Subgroup.orderOf_dvd_natCard C.N hxN
    have h2 : orderOf x' = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hxo
    rw [h2] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd C.coprime h1) (by norm_num)
  have hxc : ∀ l ∈ lup8f_L' L Bs, l * x' = x' * l := fun l hl =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx (Subgroup.mem_subgroupOf.mp hl)))
  have hEp : IsPGroup 3 (lup8f_E' L Bs) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hBs.2 _ (Subgroup.mem_subgroupOf.mp g.2)
  have hEc : ∀ e e' : ↥(lup8f_E' L Bs), e * e' = e' * e := by
    intro e e'
    have h := hBs.1.is_comm.comm
      (⟨((e : lup8f_HT L Bs) : G), Subgroup.mem_subgroupOf.mp e.2⟩ : ↥Bs)
      ⟨((e' : lup8f_HT L Bs) : G), Subgroup.mem_subgroupOf.mp e'.2⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hNT' : ∀ a ∈ lup8f_L' L Bs ⊓ Subgroup.normalizer (lup8f_E' L Bs : Set (lup8f_HT L Bs)),
      (∀ e ∈ lup8f_E' L Bs, e * a * e⁻¹ * a⁻¹ ∈ Subgroup.zpowers x') →
        ∀ e ∈ lup8f_E' L Bs, a * e = e * a := by
    rintro a ⟨haL, haN⟩ hdisp e he
    have haG : (a : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mem_subgroupOf.mp
        ((Subgroup.subgroupOf_normalizer_eq (le_sup_right : Bs ≤ L ⊔ Bs)).ge haN)
    have hax : (a : G) * x = x * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx (Subgroup.mem_subgroupOf.mp haL))
    have hdispG : ∀ b ∈ Bs, b * (a : G) * b⁻¹ * (a : G)⁻¹ ∈ Subgroup.zpowers x := by
      intro b hb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (hdisp ⟨b, Subgroup.mem_sup_right hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact Subtype.ext (lup8f_f2_commute_of_noTransvection Nat.prime_three hBs hNT hxBs haG hax
      hdispG (e : G) (Subgroup.mem_subgroupOf.mp he))
  have hZ : LargeEvenScalars (Fin n) K ≤ Subgroup.center (GL (Fin n) K) :=
    (largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm).le
  have hproj := lup8f_f2_mat_mul_mem_scalars F.tolup8f_UFrame0 hK hn3
  let χ : ↥(lup8f_E' L Bs) →* Kˣ :=
    MonoidHom.mk' (fun b => Matrix.GeneralLinearGroup.det (F.mat b)) fun b b' => by
      have hd : Matrix.GeneralLinearGroup.det ((F.mat b * F.mat b')⁻¹ * F.mat (b * b')) = 1 :=
        Units.ext (by
          rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
          exact lup8f_f2_det_eq_one_of_mem_scalars hK hdvd (hproj b b'))
      rw [map_mul, map_inv, map_mul] at hd
      exact (inv_mul_eq_one.mp hd).symm
  have hC : (Nat.card Kˣ).Prime := by
    rw [Nat.card_units, hK]
    norm_num
  intro b b'
  refine lup8f_f2_commute_of_ker hC hZ hproj χ (fun c hc e => ?_) b b'
  have hdet : (F.mat c : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val hc
  exact lup8f_f2_commute_of_det_eq_one F.tolup8f_UFrame0 hK hn3 hEp hEc C.coprime hxL' hxE' hxN
    hxc hNT' hdet e

noncomputable def lup8f_frame2 (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame1 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K :=
  { F with commute := lup8f_f2_commute hS hxL M C F hp hdvd hn }

end CFSG.StandardType.GGXInL

end
