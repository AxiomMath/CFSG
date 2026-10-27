module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.RankThree.Classical.SteinbergCFBinaryQuadraticFour
import CFSG.Assembly.OrderReductions.FrattiniElementary
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hom_zmod_ext {n : ℕ} [NeZero n] {A : Type*} [Group A]
    {f g : Multiplicative (ZMod n) →* A}
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  refine MonoidHom.ext fun x => ?_
  induction x using Multiplicative.rec with | ofAdd k =>
  have hk : Multiplicative.ofAdd k = (Multiplicative.ofAdd (1 : ZMod n)) ^ ZMod.val k := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  rw [hk, map_pow, map_pow, h]

theorem zmodHom_ofAdd {A : Type*} [Group A] {n : ℕ} [NeZero n] (c : A) (hc : c ^ n = 1)
    (k : ZMod n) : zmodHom n c hc (Multiplicative.ofAdd k) = c ^ ZMod.val k := by
  have hk : Multiplicative.ofAdd k = (Multiplicative.ofAdd (1 : ZMod n)) ^ ZMod.val k := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  rw [hk, map_pow, zmodHom_ofAdd_one]

theorem exists_qd32_mulEquiv {S : Type*} [Group S] [Finite S] (hcard : Nat.card S = 32)
    {x y u v z : S} (hzc : z ∈ center S) (hzz : z * z = 1) (hx2 : x * x = z) (hy2 : y * y = z)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hxy : ⁅x, y⁆ = z) (huv : ⁅u, v⁆ = z)
    (hxu : ⁅x, u⁆ = 1) (hxv : ⁅x, v⁆ = 1) (hyu : ⁅y, u⁆ = 1) (hyv : ⁅y, v⁆ = 1)
    (hgen : closure ({x, y, u, v} : Set S) = ⊤) :
    ∃ e : QD32 ≃* S, e qd32I = x ∧ e qd32J = y ∧ e qd32U = u * v ∧ e qd32V = u := by
  have cxu : Commute x u := commutatorElement_eq_one_iff_mul_comm.mp hxu
  have cxv : Commute x v := commutatorElement_eq_one_iff_mul_comm.mp hxv
  have cyu : Commute y u := commutatorElement_eq_one_iff_mul_comm.mp hyu
  have cyv : Commute y v := commutatorElement_eq_one_iff_mul_comm.mp hyv
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hx4 : x ^ (2 * 2) = 1 := by
    rw [show 2 * 2 = 2 + 2 from rfl, pow_add, pow_two, hx2, hzz]
  have hyx2 : y ^ 2 = x ^ 2 := by rw [pow_two, pow_two, hx2, hy2]
  have hyx : y * x * y⁻¹ = x⁻¹ := by
    have hyx' : ⁅y, x⁆ = z := by rw [← commutatorElement_inv, hxy, hzinv]
    calc y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
      _ = z * x := by rw [hyx']
      _ = x * z := (mem_center_iff.mp hzc x).symm
      _ = x⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx2, hzz])).symm
  let φQ : QuaternionGroup 2 →* S := CFSG.Semidihedral.Local.normalFormHom hx4 hyx2 hyx
  have hφQa : ∀ i, φQ (QuaternionGroup.a i) = x ^ i.val := fun _ => rfl
  have hφQxa : ∀ i, φQ (QuaternionGroup.xa i) = y * x ^ i.val := fun _ => rfl
  have hr2 : u * v * (u * v) = z := by
    calc u * v * (u * v) = ⁅u, v⁆ * (v * u) * (u * v) := by rw [commutatorElement_def]; group
      _ = z * (v * (u * u) * v) := by rw [huv]; group
      _ = z := by rw [hu2, mul_one, hv2, mul_one]
  have hr4 : (u * v) ^ 4 = 1 := by
    rw [show 4 = 2 + 2 from rfl, pow_add, pow_two, hr2, hzz]
  have hs2 : u ^ 2 = 1 := by rw [pow_two, hu2]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hsr : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    calc u * (u * v) * u⁻¹ = (u * u) * v * u⁻¹ := by group
      _ = v * u := by rw [hu2, one_mul, huinv]
      _ = (u * v)⁻¹ := by rw [mul_inv_rev, huinv, hvinv]
  let f₁ : Multiplicative (ZMod 4) →* S := zmodHom 4 (u * v) hr4
  let f₂ : Multiplicative (ZMod 2) →* S := zmodHom 2 u hs2
  have hcompat : ∀ g, f₁.comp (quaternionDihedralNegation g).toMonoidHom =
      (MulAut.conj (f₂ g)).toMonoidHom.comp f₁ := by
    intro g
    induction g using Multiplicative.rec with | ofAdd e =>
    apply hom_zmod_ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [quaternionDihedralNegation_apply, mul_one]
    change zmodHom 4 (u * v) hr4 _ = zmodHom 2 u hs2 _ * zmodHom 4 (u * v) hr4 _ *
      (zmodHom 2 u hs2 _)⁻¹
    rw [zmodHom_ofAdd, zmodHom_ofAdd, zmodHom_ofAdd]
    rcases zmod_two_eq_zero_or_eq_one e with rfl | rfl
    · simp
    · have h3 : ((-1 : ZMod 4) ^ (1 : ZMod 2).val).val = 3 := by decide
      have h1 : (1 : ZMod 4).val = 1 := rfl
      have h1' : (1 : ZMod 2).val = 1 := rfl
      rw [h3, h1, h1', pow_one, pow_one, hsr, eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hr4
  let φD : QuaternionDihedralD →* S := SemidirectProduct.lift f₁ f₂ hcompat
  have hφD : ∀ (i : ZMod 4) (e : ZMod 2),
      φD ⟨Multiplicative.ofAdd i, Multiplicative.ofAdd e⟩ = (u * v) ^ i.val * u ^ e.val := by
    intro i e
    change f₁ (Multiplicative.ofAdd i) * f₂ (Multiplicative.ofAdd e) = _
    rw [zmodHom_ofAdd, zmodHom_ofAdd]
  have hxr : Commute x (u * v) := cxu.mul_right cxv
  have hyr : Commute y (u * v) := cyu.mul_right cyv
  have hcomm : ∀ q d, Commute (φQ q) (φD d) := by
    intro q d
    obtain ⟨n, g⟩ := d
    induction n using Multiplicative.rec with | ofAdd i =>
    induction g using Multiplicative.rec with | ofAdd e =>
    rw [hφD]
    rcases q with k | k
    · rw [hφQa]
      exact (hxr.pow_pow _ _).mul_right (cxu.pow_pow _ _)
    · rw [hφQxa]
      exact ((hyr.pow_right _).mul_right (cyu.pow_right _)).mul_left
        ((hxr.pow_pow _ _).mul_right (cxu.pow_pow _ _))
  let F : QuaternionGroup 2 × QuaternionDihedralD →* S := MonoidHom.noncommCoprod φQ φD hcomm
  have hF : ∀ q d, F (q, d) = φQ q * φD d := fun _ _ => rfl
  have hdiag : quaternionDihedralDiagonal ≤ F.ker := by
    refine zpowers_le.mpr (MonoidHom.mem_ker.mpr ?_)
    rw [hF, quaternionDihedralZQ, quaternionDihedralZD, hφQa, hφD,
      show (2 : ZMod (2 * 2)).val = 2 from rfl, ZMod.val_zero, pow_zero, mul_one, pow_two,
      pow_two, hx2, hr2, hzz]
  let Fbar : QD32 →* S := QuotientGroup.lift quaternionDihedralDiagonal F hdiag
  have hFbar : ∀ g : QuaternionGroup 2 × QuaternionDihedralD,
      Fbar (QuotientGroup.mk g) = F g := fun _ => rfl
  have hI : Fbar qd32I = x := by
    rw [qd32I, hFbar, hF, hφQa, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one, map_one,
      mul_one]
  have hJ : Fbar qd32J = y := by
    rw [qd32J, hFbar, hF, hφQxa, ZMod.val_zero, pow_zero, mul_one, map_one, mul_one]
  have hU : Fbar qd32U = u * v := by
    rw [qd32U, hFbar, hF, map_one, one_mul, hφD, ZMod.val_zero, pow_zero, mul_one,
      show (1 : ZMod 4).val = 1 from rfl, pow_one]
  have hV : Fbar qd32V = u := by
    rw [qd32V, hFbar, hF, map_one, one_mul, hφD, ZMod.val_zero, pow_zero, one_mul,
      ZMod.val_one, pow_one]
  have hsurj : Function.Surjective Fbar := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨_, hI⟩
    · exact ⟨_, hJ⟩
    · exact ⟨_, hV⟩
    · refine ⟨qd32V⁻¹ * qd32U, ?_⟩
      rw [map_mul, map_inv, hV, hU, inv_mul_cancel_left]
  have : Finite QD32 := Nat.finite_of_card_ne_zero (by rw [card_QD32]; norm_num)
  have hbij : Function.Bijective Fbar := hsurj.bijective_of_nat_card_le (by rw [card_QD32, hcard])
  exact ⟨MulEquiv.ofBijective Fbar hbij, hI, hJ, hU, hV⟩

theorem zmod_two_add_add_add_add (a b c : ZMod 2) : a + b + c + b + c = a := by
  revert a b c
  decide

theorem zmod_two_eq_one_of_add_one_add_one {c : ZMod 2} (h : c + 1 + 1 = 1) : c = 1 := by
  revert c h
  decide

theorem zmod_two_eq_one_of_add_zero_add_zero {c : ZMod 2} (h : c + 0 + 0 = 1) : c = 1 := by
  revert c h
  decide

theorem zmod_two_eq_zero_of_add_one_add_zero {c : ZMod 2} (h : c + 1 + 0 = 1) : c = 0 := by
  revert c h
  decide

theorem exists_qd32_basis_of_order_five_automorphism {S : Type*} [Group S] [Finite S]
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 32) {z : S}
    (hz : center S = zpowers z) (α : MulAut S) (hα : orderOf α = 5)
    (hfix : ∀ s : S, ((α s : S) : S ⧸ center S) = (s : S ⧸ center S) → s ∈ center S) :
    ∃ x y u v : S,
      Function.Bijective (fun c : Fin 4 → ZMod 2 =>
        ((x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val : S) : S ⧸ center S)) ∧
      x * x = z ∧ y * y = z ∧ u * u = 1 ∧ v * v = 1 ∧ ⁅x, y⁆ = z ∧ ⁅u, v⁆ = z ∧
      ⁅x, u⁆ = 1 ∧ ⁅x, v⁆ = 1 ∧ ⁅y, u⁆ = 1 ∧ ⁅y, v⁆ = 1 := by
  obtain ⟨hz2, hcomm⟩ := extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzc : z ∈ center S := hz ▸ mem_zpowers z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hZ : ∀ w ∈ center S, w = 1 ∨ w = z := fun w hw =>
    (mem_zpowers_of_orderOf_eq_two hz2).mp (hz ▸ hw)
  have hcen : ∀ s t : S, ⁅s, t⁆ ∈ center S := fun s t => by
    rcases hcomm s t with h | h <;> rw [h]
    · exact one_mem _
    · exact hzc
  have hsq : ∀ g : S, g * g ∈ center S := fun g => by
    rw [← hS.2.2.1, ← pow_two]
    exact CFSG.OrderReductions.FrattiniElementary.pow_mem_frattini 2 hS.1 g
  have hww : ∀ w ∈ center S, w * w = 1 := fun w hw => by
    rcases hZ w hw with rfl | rfl
    · exact mul_one 1
    · exact hzz
  let ι : center S ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hS.2.2.2 (by rw [Nat.card_eq_fintype_card]; rfl)
  let sq : S → ZMod 2 := fun s => Multiplicative.toAdd (ι ⟨s * s, hsq s⟩)
  let cm : S → S → ZMod 2 := fun s t => Multiplicative.toAdd (ι ⟨⁅s, t⁆, hcen s t⟩)
  have hι0 : ∀ (w : S) (hw : w ∈ center S), Multiplicative.toAdd (ι ⟨w, hw⟩) = 0 ↔ w = 1 :=
    fun w hw => by rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff, mk_eq_one]
  have hsq0 : ∀ s, sq s = 0 ↔ s * s = 1 := fun s => hι0 _ _
  have hcm0 : ∀ s t, cm s t = 0 ↔ ⁅s, t⁆ = 1 := fun s t => hι0 _ _
  have hsq1 : ∀ s, sq s = 1 → s * s = z := fun s h =>
    (hZ _ (hsq s)).resolve_left fun h' => by rw [(hsq0 s).mpr h'] at h; exact zero_ne_one h
  have hcm1 : ∀ s t, cm s t = 1 → ⁅s, t⁆ = z := fun s t h =>
    (hZ _ (hcen s t)).resolve_left fun h' => by rw [(hcm0 s t).mpr h'] at h; exact zero_ne_one h
  have hP1 : ∀ s t, sq (s * t) = cm t s + sq s + sq t := by
    intro s t
    have e1 : t * s = ⁅t, s⁆ * (s * t) := by rw [commutatorElement_def]; group
    have e : (⟨s * t * (s * t), hsq (s * t)⟩ : center S) =
        ⟨⁅t, s⁆, hcen t s⟩ * ⟨s * s, hsq s⟩ * ⟨t * t, hsq t⟩ := by
      apply Subtype.ext
      change s * t * (s * t) = ⁅t, s⁆ * (s * s) * (t * t)
      calc s * t * (s * t) = s * (t * s) * t := by group
        _ = s * (⁅t, s⁆ * (s * t)) * t := by rw [e1]
        _ = (s * ⁅t, s⁆) * s * t * t := by group
        _ = (⁅t, s⁆ * s) * s * t * t := by rw [mem_center_iff.mp (hcen t s) s]
        _ = ⁅t, s⁆ * (s * s) * (t * t) := by group
    change Multiplicative.toAdd (ι ⟨s * t * (s * t), _⟩) = _
    rw [e, map_mul ι, map_mul ι, toAdd_mul, toAdd_mul]
  have hP2 : ∀ s s' t, cm (s * s') t = cm s t + cm s' t := by
    intro s s' t
    have e : (⟨⁅s * s', t⁆, hcen (s * s') t⟩ : center S) =
        ⟨⁅s', t⁆, hcen s' t⟩ * ⟨⁅s, t⁆, hcen s t⟩ := by
      apply Subtype.ext
      change ⁅s * s', t⁆ = ⁅s', t⁆ * ⁅s, t⁆
      calc ⁅s * s', t⁆ = s * ⁅s', t⁆ * (t * s⁻¹ * t⁻¹) := by
            simp only [commutatorElement_def]
            group
        _ = ⁅s', t⁆ * s * (t * s⁻¹ * t⁻¹) := by rw [mem_center_iff.mp (hcen s' t) s]
        _ = ⁅s', t⁆ * ⁅s, t⁆ := by rw [commutatorElement_def s t]; group
    change Multiplicative.toAdd (ι ⟨⁅s * s', t⁆, _⟩) = _
    rw [e, map_mul ι, toAdd_mul, add_comm]
  have hP3 : ∀ s t, cm t s = cm s t := by
    intro s t
    have e : (⟨⁅t, s⁆, hcen t s⟩ : center S) = (⟨⁅s, t⁆, hcen s t⟩)⁻¹ :=
      Subtype.ext (commutatorElement_inv s t).symm
    change Multiplicative.toAdd (ι ⟨⁅t, s⁆, _⟩) = _
    rw [e, map_inv ι, toAdd_inv]
    exact ZMod.neg_eq_self_mod_two _
  have hcmz : ∀ w ∈ center S, ∀ t, cm w t = 0 := fun w hw t =>
    (hcm0 w t).mpr (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hw t).symm)
  have hsqz : ∀ w ∈ center S, sq w = 0 := fun w hw => (hsq0 w).mpr (hww w hw)
  have hP5 : ∀ s, ∀ w ∈ center S, sq (s * w) = sq s := fun s w hw => by
    rw [hP1, hcmz w hw, hsqz w hw, zero_add, add_zero]
  have hP5' : ∀ s t, ∀ w ∈ center S, cm (s * w) t = cm s t := fun s t w hw => by
    rw [hP2, hcmz w hw, add_zero]
  have hautz : ∀ β : MulAut S, ∀ w ∈ center S, β w = w := by
    intro β w hw
    have hβz : β z ∈ center S := by
      have h := characteristic_iff_map_eq.mp (inferInstance : (center S).Characteristic) β
      rw [← h]
      exact mem_map_of_mem _ hzc
    have hβz' : β z = z := (hZ _ hβz).resolve_left fun h =>
      hz1 (β.injective (h.trans (map_one β).symm))
    rcases hZ w hw with rfl | rfl
    · exact map_one β
    · exact hβz'
  have hP6 : ∀ β : MulAut S, ∀ s, sq (β s) = sq s := by
    intro β s
    have e : (⟨β s * β s, hsq (β s)⟩ : center S) = ⟨s * s, hsq s⟩ :=
      Subtype.ext (show β s * β s = s * s by rw [← map_mul]; exact hautz β _ (hsq s))
    exact congrArg (fun w => Multiplicative.toAdd (ι w)) e
  have hVcomm : ∀ a b : S ⧸ center S, a * b = b * a := by
    intro a b
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (s * t)⁻¹ * (t * s) = ⁅t⁻¹, s⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [this]
    exact hcen _ _
  let : CommGroup (S ⧸ center S) := { (inferInstance : Group (S ⧸ center S)) with
    mul_comm := hVcomm }
  have h2V : ∀ w : Additive (S ⧸ center S), 2 • w = 0 := by
    intro w
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hw : w = Additive.ofMul (s : S ⧸ center S) := by rw [hs]; rfl
    rw [hw, ← ofMul_pow, ← QuotientGroup.mk_pow, pow_two, (QuotientGroup.eq_one_iff _).mpr (hsq s)]
    rfl
  let : Module (ZMod 2) (Additive (S ⧸ center S)) := AddCommGroup.zmodModule h2V
  have hsmul_def : ∀ (c : ZMod 2) (w : Additive (S ⧸ center S)), c • w = c.val • w :=
    fun _ _ => rfl
  let qbar : S ⧸ center S → ZMod 2 := Quotient.lift sq (fun a b hab => by
    have hw : a⁻¹ * b ∈ center S := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, hP5 a _ hw])
  have hqbar : ∀ s : S, qbar (s : S ⧸ center S) = sq s := fun _ => rfl
  let f : Additive (S ⧸ center S) → ZMod 2 := fun w => qbar (Additive.toMul w)
  have hf : ∀ s : S, f (Additive.ofMul (s : S ⧸ center S)) = sq s := fun _ => rfl
  have hlift : ∀ w : Additive (S ⧸ center S), ∃ s : S, w = Additive.ofMul (s : S ⧸ center S) := by
    intro w
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    exact ⟨s, by rw [hs]; rfl⟩
  have hadd : ∀ s t : S, Additive.ofMul (s : S ⧸ center S) + Additive.ofMul (t : S ⧸ center S) =
      Additive.ofMul ((s * t : S) : S ⧸ center S) := fun _ _ => rfl
  have hf0 : f 0 = 0 := by
    change sq 1 = 0
    exact (hsq0 1).mpr (mul_one 1)
  have hP2r : ∀ s s' t, cm t (s * s') = cm t s + cm t s' := fun s s' t => by
    rw [hP3 (s * s') t, hP3 s t, hP3 s' t, hP2]
  have hpolar : ∀ s t : S, QuadraticMap.polar f (Additive.ofMul (s : S ⧸ center S))
      (Additive.ofMul (t : S ⧸ center S)) = cm t s := by
    intro s t
    rw [QuadraticMap.polar, hadd, hf, hf, hf, hP1]
    ring
  have hsmulf : ∀ (a : ZMod 2) (w : Additive (S ⧸ center S)), f (a • w) = (a * a) • f w := by
    intro a w
    rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul, hf0, zero_mul, zero_smul]
    · rw [one_smul, one_mul, one_smul]
  have hpadd : ∀ w w' w'' : Additive (S ⧸ center S), QuadraticMap.polar f (w + w') w'' =
      QuadraticMap.polar f w w'' + QuadraticMap.polar f w' w'' := by
    intro w w' w''
    obtain ⟨s, rfl⟩ := hlift w
    obtain ⟨s', rfl⟩ := hlift w'
    obtain ⟨t, rfl⟩ := hlift w''
    rw [hadd, hpolar, hpolar, hpolar, hP2r]
  have hpsmul : ∀ (a : ZMod 2) (w w' : Additive (S ⧸ center S)),
      QuadraticMap.polar f (a • w) w' = a • QuadraticMap.polar f w w' := by
    intro a w w'
    rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul, zero_smul, QuadraticMap.polar, zero_add, hf0, sub_zero, sub_self]
    · rw [one_smul, one_smul]
  let Q : QuadraticForm (ZMod 2) (Additive (S ⧸ center S)) :=
    QuadraticMap.ofPolar f hsmulf hpadd hpsmul
  have hQ : ∀ w, Q w = f w := fun _ => rfl
  have hnd : ∀ w : Additive (S ⧸ center S), (∀ w', Q (w + w') + Q w + Q w' = 0) → w = 0 := by
    intro w hw
    obtain ⟨s, rfl⟩ := hlift w
    have hsc : s ∈ center S := by
      rw [mem_center_iff]
      intro t
      have h := hw (Additive.ofMul (t : S ⧸ center S))
      rw [hQ, hQ, hQ, hadd, hf, hf, hf, hP1] at h
      have h' : cm t s = 0 := by rw [← zmod_two_add_add_add_add (cm t s) (sq s) (sq t)]; exact h
      exact commutatorElement_eq_one_iff_mul_comm.mp ((hcm0 t s).mp h')
    change Additive.ofMul (s : S ⧸ center S) = Additive.ofMul 1
    rw [(QuotientGroup.eq_one_iff s).mpr hsc]
  have hcardV : Nat.card (S ⧸ center S) = 16 := by
    have h := card_eq_card_quotient_mul_card_subgroup (center S)
    rw [hcard, hS.2.2.2] at h
    omega
  have : Finite (Additive (S ⧸ center S)) := inferInstanceAs (Finite (S ⧸ center S))
  have : FiniteDimensional (ZMod 2) (Additive (S ⧸ center S)) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive (S ⧸ center S)) = 4 := by
    have : Fintype (Additive (S ⧸ center S)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (S ⧸ center S))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    have h16 : Nat.card (Additive (S ⧸ center S)) = 16 := hcardV
    rw [h16, show (16 : ℕ) = 2 ^ 4 by norm_num] at hpow
    exact (Nat.pow_right_injective le_rfl hpow).symm
  have hnf := CFSG.RankThree.Classical.binary_quadratic_four_normal_forms hfin Q hnd
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set G := zpowers α with hG
  have hGp : IsPGroup 5 G := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hα, pow_one])
  have hN : ∀ a : G, ∀ n ∈ center S, (G.subtype a) n ∈ center S := fun a n hn => by
    rw [show (G.subtype a) n = n from hautz (a : MulAut S) n hn]
    exact hn
  let act : G →* MulAut (S ⧸ center S) :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction G.subtype (center S) hN
  have hact : ∀ (a : G) (s : S), act a (s : S ⧸ center S) = ((a : MulAut S) s : S ⧸ center S) :=
    fun _ _ => rfl
  let : MulAction G (S ⧸ center S) := MulAction.compHom _ act
  let X : SubMulAction G (S ⧸ center S) :=
    { carrier := {q | qbar q = 0}
      smul_mem' := fun a q hq => by
        obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
        change qbar (act a (s : S ⧸ center S)) = 0
        rw [hact, hqbar, hP6]
        exact hq }
  have hcong := hGp.card_modEq_card_fixedPoints X
  have h1X : (1 : S ⧸ center S) ∈ X := by
    change sq 1 = 0
    exact (hsq0 1).mpr (mul_one 1)
  have hfixX : Nat.card (MulAction.fixedPoints G X) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨1, h1X⟩, fun a => Subtype.ext (map_one (act a))⟩, fun q => ?_⟩
    obtain ⟨⟨q, hq⟩, hqfix⟩ := q
    apply Subtype.ext
    apply Subtype.ext
    change q = 1
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have h := congrArg Subtype.val (hqfix ⟨α, mem_zpowers α⟩)
    change act ⟨α, mem_zpowers α⟩ (s : S ⧸ center S) = (s : S ⧸ center S) at h
    rw [hact] at h
    exact (QuotientGroup.eq_one_iff s).mpr (hfix s h)
  have hcountX : Nat.card {w : Additive (S ⧸ center S) // Q w = 0} = Nat.card X :=
    Nat.card_congr
      { toFun := fun w => ⟨Additive.toMul w.1, w.2⟩
        invFun := fun q => ⟨Additive.ofMul q.1, q.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hmod : Nat.card {w : Additive (S ⧸ center S) // Q w = 0} ≡ 1 [MOD 5] := by
    rw [hcountX, ← hfixX]
    exact hcong
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 4) (ZMod 2) (Additive (S ⧸ center S)),
      ∀ c : Fin 4 → ZMod 2, Q (∑ i, c i • b i) = c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2 + c 2 * c 3 := by
    rcases hnf with ⟨⟨-, h10⟩, -⟩ | ⟨⟨h, -⟩, -⟩
    · rw [h10] at hmod
      exact absurd hmod (by decide)
    · exact h
  have hval : ∀ a₀ a₁ a₂ a₃ : ZMod 2, Q (a₀ • b 0 + a₁ • b 1 + a₂ • b 2 + a₃ • b 3) =
      a₀ ^ 2 + a₀ * a₁ + a₁ ^ 2 + a₂ * a₃ := by
    intro a₀ a₁ a₂ a₃
    have h := hb ![a₀, a₁, a₂, a₃]
    rw [Fin.sum_univ_four] at h
    simpa using h
  obtain ⟨x, hbx⟩ := hlift (b 0)
  obtain ⟨y, hby⟩ := hlift (b 1)
  obtain ⟨u, hbu⟩ := hlift (b 2)
  obtain ⟨v, hbv⟩ := hlift (b 3)
  have hQ1 : ∀ (a₀ a₁ a₂ a₃ : ZMod 2) (w : Additive (S ⧸ center S)),
      w = a₀ • b 0 + a₁ • b 1 + a₂ • b 2 + a₃ • b 3 → Q w = a₀ ^ 2 + a₀ * a₁ + a₁ ^ 2 + a₂ * a₃ :=
    fun a₀ a₁ a₂ a₃ w hw => hw ▸ hval a₀ a₁ a₂ a₃
  have ex : sq x = 1 := by
    have h := hQ1 1 0 0 0 (b 0) (by simp)
    rw [hbx] at h
    exact h
  have ey : sq y = 1 := by
    have h := hQ1 0 1 0 0 (b 1) (by simp)
    rw [hby] at h
    exact h
  have eu : sq u = 0 := by
    have h := hQ1 0 0 1 0 (b 2) (by simp)
    rw [hbu] at h
    exact h
  have ev : sq v = 0 := by
    have h := hQ1 0 0 0 1 (b 3) (by simp)
    rw [hbv] at h
    exact h
  have exy : sq (x * y) = 1 := by
    have h := hQ1 1 1 0 0 (b 0 + b 1) (by simp)
    rw [hbx, hby, hadd] at h
    exact h.trans (by decide)
  have euv : sq (u * v) = 1 := by
    have h := hQ1 0 0 1 1 (b 2 + b 3) (by simp)
    rw [hbu, hbv, hadd] at h
    exact h.trans (by decide)
  have exu : sq (x * u) = 1 := by
    have h := hQ1 1 0 1 0 (b 0 + b 2) (by simp)
    rw [hbx, hbu, hadd] at h
    exact h.trans (by decide)
  have exv : sq (x * v) = 1 := by
    have h := hQ1 1 0 0 1 (b 0 + b 3) (by simp)
    rw [hbx, hbv, hadd] at h
    exact h.trans (by decide)
  have eyu : sq (y * u) = 1 := by
    have h := hQ1 0 1 1 0 (b 1 + b 2) (by simp)
    rw [hby, hbu, hadd] at h
    exact h.trans (by decide)
  have eyv : sq (y * v) = 1 := by
    have h := hQ1 0 1 0 1 (b 1 + b 3) (by simp)
    rw [hby, hbv, hadd] at h
    exact h.trans (by decide)
  rw [hP1, ex, ey] at exy
  rw [hP1, eu, ev] at euv
  rw [hP1, ex, eu] at exu
  rw [hP1, ex, ev] at exv
  rw [hP1, ey, eu] at eyu
  rw [hP1, ey, ev] at eyv
  have hxy : ⁅x, y⁆ = z := hcm1 x y (by rw [← hP3]; exact zmod_two_eq_one_of_add_one_add_one exy)
  have huv : ⁅u, v⁆ = z := hcm1 u v (by rw [← hP3]; exact zmod_two_eq_one_of_add_zero_add_zero euv)
  have hxu : ⁅x, u⁆ = 1 :=
    (hcm0 x u).mp (by rw [← hP3]; exact zmod_two_eq_zero_of_add_one_add_zero exu)
  have hxv : ⁅x, v⁆ = 1 :=
    (hcm0 x v).mp (by rw [← hP3]; exact zmod_two_eq_zero_of_add_one_add_zero exv)
  have hyu : ⁅y, u⁆ = 1 :=
    (hcm0 y u).mp (by rw [← hP3]; exact zmod_two_eq_zero_of_add_one_add_zero eyu)
  have hyv : ⁅y, v⁆ = 1 :=
    (hcm0 y v).mp (by rw [← hP3]; exact zmod_two_eq_zero_of_add_one_add_zero eyv)
  have hcoord : (fun c : Fin 4 → ZMod 2 =>
      ((x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val : S) : S ⧸ center S)) =
      Additive.toMul ∘ b.equivFun.symm := by
    funext c
    rw [Function.comp_apply, Module.Basis.equivFun_symm_apply, Fin.sum_univ_four, hbx, hby, hbu,
      hbv]
    simp only [hsmul_def, toMul_add, toMul_nsmul, toMul_ofMul, QuotientGroup.mk_mul,
      QuotientGroup.mk_pow]
  refine ⟨x, y, u, v, ?_, hsq1 x ex, hsq1 y ey, (hsq0 u).mp eu, (hsq0 v).mp ev, hxy, huv, hxu,
    hxv, hyu, hyv⟩
  rw [hcoord]
  exact Additive.toMul.bijective.comp b.equivFun.symm.bijective

theorem extraspecial_thirty_two_five_recognition {S : Type*} [Group S]
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 32) {z : S}
    (hz : center S = zpowers z) (α : MulAut S) (hα : orderOf α = 5)
    (hfix : ∀ s : S, ((α s : S) : S ⧸ center S) = (s : S ⧸ center S) → s ∈ center S) :
    Nonempty (S ≃* QD32) ∧
      ∃ x y u v : S,
        Function.Bijective (fun c : Fin 4 → ZMod 2 =>
          ((x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val : S) :
            S ⧸ center S)) ∧
        x ^ 2 = z ∧ y ^ 2 = z ∧ u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ ⁅x, y⁆ = z ∧ ⁅u, v⁆ = z ∧
        ⁅x, u⁆ = 1 ∧ ⁅x, v⁆ = 1 ∧ ⁅y, u⁆ = 1 ∧ ⁅y, v⁆ = 1 ∧
        ∃ e : QD32 ≃* S, e qd32I = x ∧ e qd32J = y ∧ e qd32U = u * v ∧ e qd32V = u := by
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨x, y, u, v, hbij, hxx, hyy, huu, hvv, hxy, huv, hxu, hxv, hyu, hyv⟩ :=
    exists_qd32_basis_of_order_five_automorphism hS hcard hz α hα hfix
  obtain ⟨hz2, -⟩ := extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzc : z ∈ center S := hz ▸ mem_zpowers z
  have hgen : closure ({x, y, u, v} : Set S) = ⊤ := by
    set K := closure ({x, y, u, v} : Set S) with hK
    have hxK : x ∈ K := subset_closure (by simp)
    have hyK : y ∈ K := subset_closure (by simp)
    have huK : u ∈ K := subset_closure (by simp)
    have hvK : v ∈ K := subset_closure (by simp)
    have hzK : z ∈ K := hxx ▸ mul_mem hxK hxK
    rw [eq_top_iff]
    intro s _
    obtain ⟨c, hc⟩ := hbij.2 (s : S ⧸ center S)
    set p := x ^ (c 0).val * y ^ (c 1).val * u ^ (c 2).val * v ^ (c 3).val with hp
    have hpK : p ∈ K := mul_mem (mul_mem (mul_mem (pow_mem hxK _) (pow_mem hyK _))
      (pow_mem huK _)) (pow_mem hvK _)
    have hw : p⁻¹ * s ∈ center S := QuotientGroup.eq.mp hc
    have hs : s = p * (p⁻¹ * s) := by group
    rw [hs]
    refine mul_mem hpK ?_
    rcases (mem_zpowers_of_orderOf_eq_two hz2).mp (hz ▸ hw) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact hzK
  obtain ⟨e, he⟩ :=
    exists_qd32_mulEquiv hcard hzc hzz hxx hyy huu hvv hxy huv hxu hxv hyu hyv hgen
  exact ⟨⟨e.symm⟩, x, y, u, v, hbij, by rw [pow_two, hxx], by rw [pow_two, hyy],
    by rw [pow_two, huu], by rw [pow_two, hvv], hxy, huv, hxu, hxv, hyu, hyv, e, he⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
