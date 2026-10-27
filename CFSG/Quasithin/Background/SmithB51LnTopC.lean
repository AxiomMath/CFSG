module

public import CFSG.Quasithin.Background.SmithB51LnTopB
public import CFSG.Quasithin.Background.SmithB51LnInputs
public import CFSG.Quasithin.Background.SmithB51LnSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix
open scoped Matrix

section Real

variable {V : Type} [CommGroup V] {n : ℕ} {L : Subgroup (MulAut V)} {W Y Z U X : Subgroup V}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem secImg_self (W Z : Subgroup V) : secImg W Z Z = ⊥ := by
  rw [eq_bot_iff]
  rintro s ⟨w, hw, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hw

theorem secPre_secImg (hZU : Z ≤ U) (hUW : U ≤ W) : secPre W Z (secImg W Z U) = U := by
  ext u
  rw [mem_secPre]
  constructor
  · rintro ⟨hu, h⟩
    exact (mk_mem_secImg hZU ⟨u, hu⟩).1 h
  · intro hu
    exact ⟨hUW hu, (mk_mem_secImg hZU ⟨u, hUW hu⟩).2 hu⟩

theorem RealM.toSecSub (h : RealM L U Y π M) (hZY : Z ≤ Y) (hUW : U ≤ W) (hLW : L ≤ stabSub W)
    (hLZ : L ≤ stabSub Z) :
    RealM (autSec L W Z) (secImg W Z U) (secImg W Z Y) ((secHomL L hLW hLZ).comp π) M := by
  obtain ⟨hπ, hYU, hLU, hLY, β, hβs, hβk, hβe⟩ := h
  let p : ↥U →* ↥(secImg W Z U) :=
    { toFun := fun u => ⟨QuotientGroup.mk ⟨u, hUW u.2⟩, ⟨⟨u, hUW u.2⟩, u.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpu : ∀ u : ↥U, ((p u : ↥(secImg W Z U)) : Sec W Z) = QuotientGroup.mk ⟨u, hUW u.2⟩ :=
    fun _ => rfl
  have hp : Function.Surjective p := by
    rintro ⟨s, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hle : p.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 : (QuotientGroup.mk ⟨u, hUW u.2⟩ : Sec W Z) = 1 := by
      rw [← hpu, hu]
      rfl
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact (hβk u).2 (hZY h1)
  set e := QuotientGroup.quotientKerEquivOfSurjective p hp with he
  let β' : ↥(secImg W Z U) →* Multiplicative (Fin n → ZMod 2) :=
    (QuotientGroup.lift p.ker β hle).comp e.symm.toMonoidHom
  have hβ' : ∀ u : ↥U, β' (p u) = β u := by
    intro u
    have : e.symm (p u) = (QuotientGroup.mk u : ↥U ⧸ p.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift p.ker β hle (e.symm (p u)) = β u
    rw [this, QuotientGroup.lift_mk]
  refine ⟨(secHomL_surjective hLW hLZ).comp hπ, ?_, ?_, ?_, β', ?_, ?_, ?_⟩
  · rintro s ⟨w, hw, rfl⟩
    exact ⟨w, hYU hw, rfl⟩
  · intro l s hs
    obtain ⟨w, hw, rfl⟩ := hs
    obtain ⟨g, hg⟩ := secHomL_surjective hLW hLZ l
    rw [← hg]
    show B5.secHom L hLW hLZ g (QuotientGroup.mk w) ∈ _
    rw [B5.secHom_mk]
    refine ⟨_, ?_, rfl⟩
    have hw : (w : V) ∈ U := hw
    exact hLU g _ hw
  · intro l s hs
    obtain ⟨w, hw, rfl⟩ := hs
    obtain ⟨g, hg⟩ := secHomL_surjective hLW hLZ l
    rw [← hg]
    show B5.secHom L hLW hLZ g (QuotientGroup.mk w) ∈ _
    rw [B5.secHom_mk]
    refine ⟨_, ?_, rfl⟩
    have hw : (w : V) ∈ Y := hw
    exact hLY g _ hw
  · intro x
    obtain ⟨u, hu⟩ := hβs x
    exact ⟨p u, by rw [hβ', hu]⟩
  · intro s
    obtain ⟨u, rfl⟩ := hp s
    rw [hβ', hβk, hpu, mk_mem_secImg hZY]
  · intro γ s hs
    obtain ⟨u, rfl⟩ := hp s
    have hU' : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hLU (π γ) u u.2
    have heq : (⟨_, hs⟩ : ↥(secImg W Z U)) = p ⟨_, hU'⟩ := by
      apply Subtype.ext
      show B5.secHom L hLW hLZ (π γ) (QuotientGroup.mk ⟨u, hUW u.2⟩) = _
      rw [B5.secHom_mk]
      rfl
    rw [heq, hβ', hβ']
    exact hβe γ u hU'

theorem RealM.restrict (h : RealM L W Y π M) (hXW : X ≤ W) (hXY : X ⊔ Y = W)
    (hX : ∀ l : ↥L, ∀ x ∈ X, (l : MulAut V) x ∈ X) : RealM L X (X ⊓ Y) π M := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  refine ⟨hπ, inf_le_left, hX, fun l y hy => ⟨hX l y hy.1, hLY l y hy.2⟩,
    β.comp (Subgroup.inclusion hXW), fun y => ?_, fun x => ?_, fun γ x hx => ?_⟩
  · obtain ⟨w, rfl⟩ := hβs y
    have hw : (w : V) ∈ X ⊔ Y := by rw [hXY]; exact w.2
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hw
    refine ⟨⟨a, ha⟩, ?_⟩
    have h1 : β ⟨b, hYW hb⟩ = 1 := (hβk _).2 hb
    have h2 : w = Subgroup.inclusion hXW ⟨a, ha⟩ * ⟨b, hYW hb⟩ := Subtype.ext hab.symm
    rw [MonoidHom.comp_apply, h2, map_mul, h1, mul_one]
  · rw [MonoidHom.comp_apply, hβk]
    exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
  · have := hβe γ (Subgroup.inclusion hXW x) (hLW (π γ) _ (hXW x.2))
    exact this

theorem RealM.sup_bot (h : RealM L X ⊥ π M) (hY : ∀ l : ↥L, ∀ y ∈ Y, (l : MulAut V) y ∈ Y)
    (hXY : X ⊓ Y = ⊥) : RealM L (X ⊔ Y) Y π M := by
  obtain ⟨hπ, -, hLX, -, β, hβs, hβk, hβe⟩ := h
  let q : ↥X →* ↥(X ⊔ Y) ⧸ Y.subgroupOf (X ⊔ Y) :=
    (QuotientGroup.mk' (Y.subgroupOf (X ⊔ Y))).comp (Subgroup.inclusion le_sup_left)
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : (Subgroup.inclusion le_sup_left x : ↥(X ⊔ Y)) ∈ Y.subgroupOf (X ⊔ Y) :=
        (QuotientGroup.eq_one_iff _).1 hx
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : (x : V) ∈ X ⊓ Y := ⟨x.2, h1⟩
      rw [hXY, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    · intro s
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective s
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 z.2
      refine ⟨⟨a, ha⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨a, ha⟩) : _) = QuotientGroup.mk z
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (a : V)⁻¹ * (z : V) ∈ Y
      rw [← hab]
      simpa using hb
  set eq := MulEquiv.ofBijective q hq with heq
  let β' : ↥(X ⊔ Y) →* Multiplicative (Fin n → ZMod 2) :=
    (β.comp eq.symm.toMonoidHom).comp (QuotientGroup.mk' (Y.subgroupOf (X ⊔ Y)))
  have hβ' : ∀ (x : ↥X) (y : V), y ∈ Y → ∀ z : ↥(X ⊔ Y), (z : V) = x * y → β' z = β x := by
    intro x y hy z hz
    have h1 : QuotientGroup.mk' (Y.subgroupOf (X ⊔ Y)) z = q x := by
      show (QuotientGroup.mk z : _) = QuotientGroup.mk (Subgroup.inclusion le_sup_left x)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (z : V)⁻¹ * (x : V) ∈ Y
      rw [hz, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact Y.inv_mem hy
    show β (eq.symm (QuotientGroup.mk' (Y.subgroupOf (X ⊔ Y)) z)) = β x
    rw [h1]
    congr 1
    exact eq.symm_apply_apply x
  refine ⟨hπ, le_sup_right, fun l w hw => CFSG.Quasithin.isInv_sup
    (fun l hl x hx => hLX ⟨l, hl⟩ x hx) (fun l hl y hy => hY ⟨l, hl⟩ y hy) l l.2 w hw, hY, β',
    fun t => ?_, fun z => ?_, fun γ z hz => ?_⟩
  · obtain ⟨x, hx⟩ := hβs t
    refine ⟨⟨x, Subgroup.mem_sup_left x.2⟩, ?_⟩
    rw [hβ' x 1 Y.one_mem _ (by simp), hx]
  · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 z.2
    rw [hβ' ⟨a, ha⟩ b hb z hab.symm, hβk]
    constructor
    · intro h1
      rw [Subgroup.mem_bot] at h1
      rw [← hab]
      have h1' : a = 1 := h1
      rw [h1', one_mul]
      exact hb
    · intro h1
      have h2 : (a : V) ∈ X ⊓ Y := ⟨ha, by
        have := Y.mul_mem h1 (Y.inv_mem hb)
        rwa [← hab, mul_inv_cancel_right] at this⟩
      rwa [hXY] at h2
  · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 z.2
    have hXa : ((π γ : ↥L) : MulAut V) a ∈ X := hLX (π γ) a ha
    have hYb : ((π γ : ↥L) : MulAut V) b ∈ Y := hY (π γ) b hb
    rw [hβ' ⟨a, ha⟩ b hb z hab.symm, hβ' ⟨_, hXa⟩ _ hYb ⟨_, hz⟩ (by
      show ((π γ : ↥L) : MulAut V) (z : V) = _
      rw [← hab, map_mul])]
    exact hβe γ ⟨a, ha⟩ hXa

end Real

section Split

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem rAV_sec_le_one (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {W Y : Subgroup V}
    (c : SecCtx G L A W Y) (hA : IsFFStarOffender G A) : rAV (autSec A W Y) ≤ 1 := by
  have hAW : A ≤ stabSub W := le_sup_right.trans c.hMW
  have hAY : A ≤ stabSub Y := le_sup_right.trans c.hMU
  have e1 := rkSub_ge_sec hV c.hUW hAW
  have e2 := rkSub_mono (A := A) (le_top : W ≤ ⊤)
  have e3 := rkSub_top A
  have e4 := rkIdx_fixV_le_rk hV hA
  have hrk := rk_autSec_eq hAW hAY (sec_A_inf_centSec h c)
  have hpos : 0 < rk A := hA.isA2.rk_pos
  unfold rAV
  rw [hrk, div_le_one (by exact_mod_cast hpos)]
  exact_mod_cast (by omega : rkIdx (fixV (autSec A W Y)) ≤ rk A)

theorem split_sec (hB492 : AsB492Split) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hA : IsFFStarOffender G A) (hAL : A ≤ L) (hquad : IsQuadratic A)
    {W Y U : Subgroup V} (c : SecCtx G L A W Y) {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (h1 : RealM L U Y π mat) (h2 : RealM L W U π mat ∨ RealM L W U π dmat) :
    ∃ X : Subgroup V, (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) ∧ Y ≤ X ∧ X ≤ W ∧ X ⊓ U = Y ∧ X ⊔ U = W := by
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hLW : L ≤ stabSub W := le_sup_left.trans c.hMW
  have hLY : L ≤ stabSub Y := le_sup_left.trans c.hMU
  have hUW : U ≤ W := h2.elim (fun h => h.2.1) (fun h => h.2.1)
  have hYU : Y ≤ U := h1.2.1
  have h1' := (h1.toSecSub le_rfl hUW hLW hLY).congr_sub rfl (secImg_self W Y)
  have h2' : RealM (autSec L W Y) ⊤ (secImg W Y U) ((secHomL L hLW hLY).comp π) mat ∨
      RealM (autSec L W Y) ⊤ (secImg W Y U) ((secHomL L hLW hLY).comp π) dmat :=
    h2.elim (fun h => Or.inl (h.toSec hYU hLY)) (fun h => Or.inr (h.toSec hYU hLY))
  obtain ⟨B, hBA, hB, -⟩ := exists_offender_max (CFSG.Quasithin.sq_eq_one_sec hV W Y)
    (isA2_secA h c) (rAV_sec_le_one hV h c hA)
  rw [hLA] at hB
  have hBq : IsQuadratic B := isQuadratic_of_le (isQuadratic_secA c hquad) hBA
  obtain ⟨X', hX'inv, hX'U, hX'U'⟩ := hB492 (Sec W Y) (CFSG.Quasithin.sq_eq_one_sec hV W Y) n hn
    (autSec L W Y) (secImg W Y U) ((secHomL L hLW hLY).comp π) (realM_mat_iff.1 h1')
    (h2'.elim (fun h => Or.inl (realM_mat_iff.1 h)) (fun h => Or.inr (realM_dmat_iff.1 h)))
    ⟨B, hB, hBq⟩
  refine ⟨secPre W Y X', fun x hx w hw => ?_, le_secPre c.hUW X', secPre_le X', ?_, ?_⟩
  · obtain ⟨hw', hs⟩ := mem_secPre.1 hw
    refine mem_secPre.2 ⟨(hLW hx w).2 hw', ?_⟩
    have := hX'inv _ (secHomL L hLW hLY ⟨x, hx⟩).2 _ hs
    rw [show ((secHomL L hLW hLY ⟨x, hx⟩ : ↥(autSec L W Y)) : MulAut (Sec W Y)) =
      B5.secHom L hLW hLY ⟨x, hx⟩ from rfl, B5.secHom_mk] at this
    exact this
  · calc secPre W Y X' ⊓ U = secPre W Y X' ⊓ secPre W Y (secImg W Y U) := by
          rw [secPre_secImg hYU hUW]
      _ = secPre W Y (X' ⊓ secImg W Y U) := (secPre_inf _ _).symm
      _ = Y := by rw [inf_comm, hX'U', secPre_bot c.hUW]
  · calc secPre W Y X' ⊔ U = secPre W Y X' ⊔ secPre W Y (secImg W Y U) := by
          rw [secPre_secImg hYU hUW]
      _ = secPre W Y (X' ⊔ secImg W Y U) := (secPre_sup _ _).symm
      _ = W := by rw [sup_comm, hX'U, secPre_top]

theorem split_copies (hB492 : AsB492Split) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hA : IsFFStarOffender G A) (hAL : A ≤ L) (hquad : IsQuadratic A)
    {k : ℕ} {I : Fin k → Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hI : ∀ i, RealM L (I i) ⊥ π mat) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    ∀ (s : Finset (Fin k)) (W : Subgroup V), RealM L W (⨆ i ∈ s, I i) π mat →
      ∃ X : Subgroup V, (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) ∧ X ≤ W ∧ X ⊓ (⨆ i ∈ s, I i) = ⊥ ∧
        X ⊔ (⨆ i ∈ s, I i) = W := by
  classical
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro W hW
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot] at hW ⊢
    exact ⟨W, fun l hl x hx => hW.2.2.1 ⟨l, hl⟩ x hx, le_rfl, inf_bot_eq W, sup_bot_eq W⟩
  | insert a s ha ih =>
    intro W hW
    rw [Finset.iSup_insert] at hW ⊢
    set Us := ⨆ i ∈ s, I i with hUs
    have hdisj : I a ⊓ Us = ⊥ := by
      rw [eq_bot_iff, ← hind a]
      refine inf_le_inf_left _ (iSup₂_le fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      exact le_iSup₂_of_le (f := fun (j : Fin k) (_ : j ≠ a) => I j) i hia le_rfl
    have hUsinv : ∀ l ∈ L, ∀ y ∈ Us, l y ∈ Us :=
      inv_iSup (fun i => ⨆ (_ : i ∈ s), I i) fun i =>
        inv_iSup (fun _ : i ∈ s => I i) fun _ l hl x hx => (hI i).2.2.1 ⟨l, hl⟩ x hx
    have hR1 : RealM L (I a ⊔ Us) Us π mat :=
      (hI a).sup_bot (fun l y hy => hUsinv l l.2 y hy) hdisj
    have hnc : ¬ commSub W L ≤ Us := by
      intro hle
      have h1 := hW.commSub_sup (Or.inl rfl) hn2
      have h2 : commSub W L ≤ I a ⊔ Us := hle.trans le_sup_right
      rw [sup_eq_right.2 h2] at h1
      have h3 := hW.card_sec
      have h4 : Nat.card (Sec W (I a ⊔ Us)) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, h1]
        exact W.mul_mem (W.inv_mem x.2) y.2
      rw [h4] at h3
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hLW : L ≤ stabSub W := hW.hLW
    have hLUs : L ≤ stabSub Us := le_stabSub_of_inv hUsinv
    have c : SecCtx G L A W Us := ⟨hA.1, hA.2.2.1, hA.2.1, le_sup_right.trans hW.2.1,
      by rw [hLA]; exact hLW, by rw [hLA]; exact hLUs, hnc⟩
    obtain ⟨X₁, hX₁inv, -, hX₁W, hX₁U, hX₁U'⟩ :=
      split_sec hB492 hV h hn hA hAL hquad c hR1 (Or.inl hW)
    have hR2 : RealM L X₁ Us π mat :=
      (hW.restrict hX₁W hX₁U' (fun l x hx => hX₁inv l l.2 x hx)).congr_sub rfl hX₁U
    obtain ⟨X, hXinv, hXX₁, hXUs, hXUs'⟩ := ih X₁ hR2
    refine ⟨X, hXinv, hXX₁.trans hX₁W, ?_, ?_⟩
    · rw [eq_bot_iff, ← hXUs]
      calc X ⊓ (I a ⊔ Us) = X ⊓ (X₁ ⊓ (I a ⊔ Us)) := by rw [← inf_assoc, inf_eq_left.2 hXX₁]
        _ = X ⊓ Us := by rw [hX₁U]
        _ ≤ X ⊓ Us := le_rfl
    · rw [← hX₁U', ← hXUs', sup_assoc, sup_eq_right.2 (le_sup_right : Us ≤ I a ⊔ Us)]

end Split

end CFSG.Quasithin.B5.Ln
