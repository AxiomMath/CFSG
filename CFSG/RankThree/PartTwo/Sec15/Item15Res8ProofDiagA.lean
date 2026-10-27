module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

open CFSG CFSG.ComponentClassification
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem commutator_self_eq {K : Subgroup Γ} (hK : Group.IsPerfect K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) hK.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem mem_normalizer_of_conj_mem [Finite Γ] {H : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set Γ) := by
  let φ : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hφ : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : Γ) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφs := Finite.surjective_of_injective hφ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := hφs ⟨g * y * g⁻¹, hy⟩
  have hxy : (x : Γ) = y := by
    have h1 : g * (x : Γ) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hx
    exact mul_left_cancel (mul_right_cancel h1)
  exact hxy ▸ x.2

theorem commutatorElement_mul_right {a b c : Γ} (h : c * a = a * c) : ⁅a, b * c⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have h' : c * a⁻¹ = a⁻¹ * c := by
    calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
      _ = a⁻¹ * (c * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * c := by group
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [h']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem isElemAbelian_of_le {E F : Subgroup Γ} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hFE : F ≤ E) : CFSG.Assembly.IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem conj_injective {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut X => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem card_mul_le_of_comm [Finite Γ]
    (hrank : ∀ F : Subgroup Γ, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27)
    {E₀ F : Subgroup Γ} (hE₀ : CFSG.Assembly.IsElemAbelian 3 E₀)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hc : ∀ x ∈ E₀, ∀ y ∈ F, x * y = y * x) :
    Nat.card E₀ * Nat.card F ≤ 27 * Nat.card (E₀ ⊓ F : Subgroup Γ) := by
  rw [← (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₀ F hc).1]
  exact Nat.mul_le_mul_right _ (hrank _ (Sec13.isElemAbelian_sup hE₀ hF hc))

theorem mem_centralizer_of_displacement {Y : Subgroup Γ} (hYp : Group.IsPerfect Y) {e : Γ}
    (heY : e ∈ Subgroup.normalizer (Y : Set Γ))
    (h : ∀ y ∈ Y, ∀ y' ∈ Y, y' * (y⁻¹ * (e * y * e⁻¹)) = (y⁻¹ * (e * y * e⁻¹)) * y') :
    e ∈ Subgroup.centralizer (Y : Set Γ) := by
  have := hYp
  set σ := Y.normalizerMonoidHom ⟨e, heY⟩ with hσ
  have hcen : ∀ y : ↥Y, y⁻¹ * σ.toMonoidHom y ∈ Subgroup.center ↥Y := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro y'
    exact Subtype.ext (h y y.2 y' y'.2)
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement σ.toMonoidHom hcen
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : e * y * e⁻¹ = y :=
    congrArg (fun f : ↥Y →* ↥Y => ((f ⟨y, hy⟩ : ↥Y) : Γ)) hid
  calc y * e = e * y * e⁻¹ * e := by rw [h1]
    _ = e * y := by group

section Pair

variable {W W' : Subgroup Γ}

theorem le_centralizer_of_comm (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    W' ≤ Subgroup.centralizer (W : Set Γ) := fun w' hw' =>
  Subgroup.mem_centralizer_iff.mpr fun w hw => hc w hw w' hw'

theorem sup_le_normalizer_of_comm (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    W ⊔ W' ≤ Subgroup.normalizer (W : Set Γ) :=
  sup_le Subgroup.le_normalizer
    ((le_centralizer_of_comm hc).trans (Subgroup.centralizer_le_normalizer _))

theorem exists_mul_eq_of_mem_sup (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {x : Γ}
    (hx : x ∈ W ⊔ W') : ∃ w ∈ W, ∃ w' ∈ W', x = w * w' := by
  have hx' : x ∈ ((W ⊔ W' : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W W'
    ((le_centralizer_of_comm hc).trans (Subgroup.centralizer_le_normalizer _))] at hx'
  obtain ⟨w, hw, w', hw', rfl⟩ := hx'
  exact ⟨w, hw, w', hw', rfl⟩

@[expose] noncomputable def mulHom (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    ↥W × ↥W' →* ↥(W ⊔ W') :=
  (MonoidHom.noncommCoprod W.subtype W'.subtype fun a b => hc a a.2 b b.2).codRestrict (W ⊔ W')
    fun p => mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)

theorem mulHom_surjective (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    Function.Surjective (mulHom hc) := by
  rintro ⟨x, hx⟩
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_eq_of_mem_sup hc hx
  exact ⟨(⟨w, hw⟩, ⟨w', hw'⟩), Subtype.ext rfl⟩

theorem ker_mulHom_le (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    (mulHom hc).ker ≤
      ((QuotientGroup.mk' (Subgroup.center ↥W)).comp (MonoidHom.fst ↥W ↥W')).ker := by
  intro p hp
  rw [MonoidHom.mem_ker] at hp ⊢
  have h1 : (p.1 : Γ) * p.2 = 1 := congrArg Subtype.val hp
  have hp1 : (p.1 : Γ) = (p.2 : Γ)⁻¹ := eq_inv_of_mul_eq_one_left h1
  change QuotientGroup.mk' (Subgroup.center ↥W) p.1 = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  show (w : Γ) * p.1 = p.1 * w
  rw [hp1]
  exact hc w w.2 _ (inv_mem p.2.2)

@[expose] noncomputable def projQ (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) :
    ↥(W ⊔ W') →* ↥W ⧸ Subgroup.center ↥W :=
  (mulHom hc).liftOfSurjective (mulHom_surjective hc)
    ⟨(QuotientGroup.mk' (Subgroup.center ↥W)).comp (MonoidHom.fst ↥W ↥W'), ker_mulHom_le hc⟩

theorem projQ_eq (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {x : ↥(W ⊔ W')} {w w' : Γ}
    (hw : w ∈ W) (hw' : w' ∈ W') (hx : (x : Γ) = w * w') :
    projQ hc x = QuotientGroup.mk' (Subgroup.center ↥W) ⟨w, hw⟩ := by
  have hx' : x = mulHom hc (⟨w, hw⟩, ⟨w', hw'⟩) := Subtype.ext hx
  rw [hx']
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem exists_of_projQ_eq_one (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {x : ↥(W ⊔ W')}
    (hx : projQ hc x = 1) :
    ∃ z ∈ W, (∀ w ∈ W, w * z = z * w) ∧ ∃ w' ∈ W', (x : Γ) = z * w' := by
  obtain ⟨w, hw, w', hw', hxw⟩ := exists_mul_eq_of_mem_sup hc x.2
  rw [projQ_eq hc hw hw' hxw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_center_iff] at hx
  exact ⟨w, hw, fun u hu => congrArg Subtype.val (hx ⟨u, hu⟩), w', hw', hxw⟩

theorem mk_conj_eq (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) (x : ↥(W ⊔ W')) {s : Γ}
    (hs : s ∈ W) (hxs : (x : Γ) * s * (x : Γ)⁻¹ ∈ W) :
    QuotientGroup.mk' (Subgroup.center ↥W) ⟨x * s * x⁻¹, hxs⟩ =
      projQ hc x * QuotientGroup.mk' (Subgroup.center ↥W) ⟨s, hs⟩ * (projQ hc x)⁻¹ := by
  obtain ⟨w, hw, w', hw', hxw⟩ := exists_mul_eq_of_mem_sup hc x.2
  rw [projQ_eq hc hw hw' hxw, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (x : Γ) * s * (x : Γ)⁻¹ = w * s * w⁻¹
  rw [hxw]
  have h1 : w' * s = s * w' := (hc s hs w' hw').symm
  calc w * w' * s * (w * w')⁻¹ = w * (w' * s) * w'⁻¹ * w⁻¹ := by group
    _ = w * (s * w') * w'⁻¹ * w⁻¹ := by rw [h1]
    _ = w * s * w⁻¹ := by group

@[expose] noncomputable def actQ (W : Subgroup Γ) :
    ↥(Subgroup.normalizer (W : Set Γ)) →* MulAut (↥W ⧸ Subgroup.center ↥W) :=
  (PerfectAutomorphisms.centerQuotientHom ↥W).comp W.normalizerMonoidHom

theorem actQ_mk (g : ↥(Subgroup.normalizer (W : Set Γ))) (w : ↥W) :
    actQ W g (QuotientGroup.mk' (Subgroup.center ↥W) w) =
      QuotientGroup.mk' (Subgroup.center ↥W) (W.normalizerMonoidHom g w) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ w

theorem projQ_conj (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {g : Γ}
    (hgW : g ∈ Subgroup.normalizer (W : Set Γ)) (hgW' : g ∈ Subgroup.normalizer (W' : Set Γ))
    (x : ↥(W ⊔ W')) (hx : g * x * g⁻¹ ∈ W ⊔ W') :
    projQ hc ⟨g * x * g⁻¹, hx⟩ = actQ W ⟨g, hgW⟩ (projQ hc x) := by
  obtain ⟨w, hw, w', hw', hxw⟩ := exists_mul_eq_of_mem_sup hc x.2
  have hgw : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgW w).mp hw
  have hgw' : g * w' * g⁻¹ ∈ W' := (Subgroup.mem_normalizer_iff.mp hgW' w').mp hw'
  rw [projQ_eq hc hw hw' hxw, actQ_mk,
    projQ_eq hc hgw hgw' (show g * (x : Γ) * g⁻¹ = g * w * g⁻¹ * (g * w' * g⁻¹) by
      rw [hxw]; group)]
  rfl

theorem mem_centralizer_of_actQ_eq_one (hWp : Group.IsPerfect W)
    {g : ↥(Subgroup.normalizer (W : Set Γ))} (hg : actQ W g = 1) :
    (g : Γ) ∈ Subgroup.centralizer (W : Set Γ) := by
  have := hWp
  have h1 : W.normalizerMonoidHom g = 1 :=
    PerfectAutomorphisms.centerQuotientHom_injective ↥W (hg.trans (map_one _).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h2 : (g : Γ) * w * (g : Γ)⁻¹ = w :=
    congrArg (fun σ : MulAut ↥W => ((σ ⟨w, hw⟩ : ↥W) : Γ)) h1
  calc w * g = (g : Γ) * w * (g : Γ)⁻¹ * g := by rw [h2]
    _ = g * w := by group

theorem actQ_eq_one_of_mem_centralizer {g : ↥(Subgroup.normalizer (W : Set Γ))}
    (hg : (g : Γ) ∈ Subgroup.centralizer (W : Set Γ)) : actQ W g = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥W) x
  rw [actQ_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show (g : Γ) * w * (g : Γ)⁻¹ = w
  rw [(Subgroup.mem_centralizer_iff.mp hg w w.2).symm]
  group

theorem isPerfect_map_projQ (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {K : Subgroup Γ}
    (hK : K ≤ W ⊔ W') (hKp : Group.IsPerfect K) :
    Group.IsPerfect ((K.subgroupOf (W ⊔ W')).map (projQ hc)) := by
  have := hKp
  have : Group.IsPerfect (K.subgroupOf (W ⊔ W')) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.IsPerfect.ofSurjective (f := (projQ hc).subgroupMap _)
    ((projQ hc).subgroupMap_surjective _)

theorem le_of_map_projQ_eq_bot (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {K : Subgroup Γ}
    (hK : K ≤ W ⊔ W') (hKp : Group.IsPerfect K)
    (hb : (K.subgroupOf (W ⊔ W')).map (projQ hc) = ⊥) : K ≤ W' := by
  have hdec : ∀ k ∈ K, ∃ z ∈ W, (∀ w ∈ W, w * z = z * w) ∧ ∃ w' ∈ W', k = z * w' := by
    intro k hk
    have h1 : projQ hc ⟨k, hK hk⟩ = 1 := by
      have h2 : projQ hc ⟨k, hK hk⟩ ∈ (K.subgroupOf (W ⊔ W')).map (projQ hc) :=
        ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [hb, Subgroup.mem_bot] at h2
      exact h2
    exact exists_of_projQ_eq_one hc h1
  rw [← commutator_self_eq hKp, Subgroup.commutator_le]
  intro a ha b hb'
  obtain ⟨z₁, hz₁, -, w₁, hw₁, rfl⟩ := hdec a ha
  obtain ⟨z₂, hz₂, hz₂c, w₂, hw₂, rfl⟩ := hdec b hb'
  have e1 : z₁ * w₁ = w₁ * z₁ := hc z₁ hz₁ w₁ hw₁
  have e2 : z₂ * w₂ = w₂ * z₂ := hc z₂ hz₂ w₂ hw₂
  have e3 : z₁ * (w₂ * z₂) = w₂ * z₂ * z₁ := by
    rw [← mul_assoc, hc z₁ hz₁ w₂ hw₂, mul_assoc, (hz₂c z₁ hz₁), mul_assoc]
  have e4 : z₂ * w₁ = w₁ * z₂ := hc z₂ hz₂ w₁ hw₁
  rw [e1, e2, Sec14.Item148PtRes.commutatorElement_mul_of_commute e3,
    commutatorElement_mul_right e4]
  rw [commutatorElement_def]
  exact W'.mul_mem (W'.mul_mem (W'.mul_mem hw₁ hw₂) (W'.inv_mem hw₁)) (W'.inv_mem hw₂)

theorem displacement_mem (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {Y : Subgroup Γ}
    (hYD : Y ≤ W ⊔ W') {e : Γ} (heY : e ∈ Subgroup.normalizer (Y : Set Γ))
    (heW : e ∈ Subgroup.normalizer (W : Set Γ)) (heW' : e ∈ Subgroup.centralizer (W' : Set Γ))
    {y : Γ} (hy : y ∈ Y) : y⁻¹ * (e * y * e⁻¹) ∈ Y ⊓ W := by
  refine ⟨Y.mul_mem (Y.inv_mem hy) ((Subgroup.mem_normalizer_iff.mp heY y).mp hy), ?_⟩
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_eq_of_mem_sup hc (hYD hy)
  have h1 : w' * e = e * w' := Subgroup.mem_centralizer_iff.mp heW' w' hw'
  have hew : e * w * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp heW w).mp hw
  have hu : w⁻¹ * (e * w * e⁻¹) ∈ W := W.mul_mem (W.inv_mem hw) hew
  have h2 : e * w' * e⁻¹ = w' := by rw [← h1]; group
  have h3 : (w * w')⁻¹ * (e * (w * w') * e⁻¹) = w⁻¹ * (e * w * e⁻¹) := by
    calc (w * w')⁻¹ * (e * (w * w') * e⁻¹)
        = w'⁻¹ * (w⁻¹ * (e * w * e⁻¹)) * (e * w' * e⁻¹) := by group
      _ = w'⁻¹ * (w⁻¹ * (e * w * e⁻¹)) * w' := by rw [h2]
      _ = w⁻¹ * (e * w * e⁻¹) := by
        rw [mul_assoc, hc _ hu w' hw', ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h3]
  exact hu

end Pair

theorem eq_bot_of_isSolvable_five {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 5)) {T S : Subgroup X} (hT : Group.IsPerfect T)
    (hT1 : T ≠ ⊥) (hS : Group.IsSolvable S) (hTS : T ≤ Subgroup.normalizer (S : Set X)) :
    S = ⊥ := by
  have hTt := eq_top_of_isPerfect_five e hT hT1
  rw [hTt] at hTS hT1
  have hSn : S.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hTS)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup X := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
  · exact h
  · exfalso
    subst h
    rw [hTt] at hT
    have : Nontrivial (⊤ : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hT1
    exact Group.IsPerfect.not_isSolvable (⊤ : Subgroup X) hS

theorem eq_one_of_fix_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    {σ : MulAut X} {T : Subgroup X} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥)
    (hσT : ∀ t ∈ T, σ t = t) : σ = 1 := by
  have hTt := eq_top_of_isPerfect_five e hT hT1
  exact MulEquiv.ext fun x => hσT x (hTt ▸ Subgroup.mem_top x)

theorem eq_one_of_fix_six {X : Type*} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 6))
    {σ : MulAut X} {k : ℕ} (hσ : σ ^ (3 ^ k) = 1) {T : Subgroup X} (hT : Group.IsPerfect T)
    (hT1 : T ≠ ⊥) (hσT : ∀ t ∈ T, σ t = t) : σ = 1 := by
  obtain ⟨a, ha⟩ := mem_inner_of_pow_eq_one_six e hσ
  have hac : a ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := hσT t ht
    rw [← ha, MulAut.conj_apply] at h1
    calc t * a = a * t * a⁻¹ * a := by rw [h1]
      _ = a * t := by group
  rw [centralizer_eq_bot_six e hT hT1, Subgroup.mem_bot] at hac
  rw [← ha, hac, map_one]

theorem eq_bot_of_le_mulAut_six {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) {F : Subgroup (MulAut X)} (hF : IsPGroup 3 F)
    (hF9 : Nat.card F = 9) {Q : Subgroup X} (hQ : ¬ 3 ∣ Nat.card Q)
    (hFQ : ∀ σ ∈ F, ∀ q ∈ Q, σ q ∈ Q) : Q = ⊥ := by
  have hinj := conj_injective (center_eq_bot_six e)
  have hFle : F ≤ (MulAut.conj : X →* MulAut X).range := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hF ⟨σ, hσ⟩
    have hk' : σ ^ (3 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact mem_inner_of_pow_eq_one_six e hk'
  set P := F.comap (MulAut.conj : X →* MulAut X) with hP
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hP, Subgroup.map_comap_eq_self hFle, hF9]
  have hPQ : P ≤ Subgroup.normalizer (Q : Set X) := fun g hg =>
    mem_normalizer_of_conj_mem fun q hq => by
      have h1 := hFQ _ hg q hq
      rwa [MulAut.conj_apply] at h1
  exact eq_bot_of_le_normalizer_six e hP9 hQ hPQ

end CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag
