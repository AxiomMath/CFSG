module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.Quasithin.Background.CommVBasics
import CFSG.Quasithin.Background.FixVZPowersMem
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGroup
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix MatrixGroups

section Disjoint

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {t : MulAut W}

private theorem w4s_comm_conj (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    {x y : MulAut W} (hx : x ∈ L) (hy : y ∈ L) : x * (t * y * t⁻¹) = t * y * t⁻¹ * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx)
    (t * y * t⁻¹) ⟨y, hy, rfl⟩).symm

private theorem w4s_mem_centralizer {c : MulAut W} (h1 : ∀ x ∈ L, x * c = c * x)
    (h2 : ∀ y ∈ L, t * y * t⁻¹ * c = c * (t * y * t⁻¹)) :
    c ∈ Subgroup.centralizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)) := by
  have hle : L ⊔ L.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer {c} := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h1 x hx)) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h2 y hy)
  exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hb)

private theorem w4s_mem_centralizer_of_central
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) {c : MulAut W} (hcL : c ∈ L)
    (hc : ∀ x ∈ L, c * x = x * c) :
    c ∈ Subgroup.centralizer
        ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)) ∧
      t * c * t⁻¹ ∈ Subgroup.centralizer
        ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)) := by
  refine ⟨w4s_mem_centralizer (fun x hx => (hc x hx).symm)
    (fun y hy => (w4s_comm_conj hcomm hcL hy).symm), w4s_mem_centralizer
    (fun x hx => w4s_comm_conj hcomm hx hcL) fun y hy => ?_⟩
  calc t * y * t⁻¹ * (t * c * t⁻¹) = t * (y * c) * t⁻¹ := by group
    _ = t * (c * y) * t⁻¹ := by rw [hc y hy]
    _ = t * c * t⁻¹ * (t * y * t⁻¹) := by group

private theorem w4s_eq_bot_or_eq_top
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥) {U : Subgroup W}
    (hU : StableUnder (L ⊔ L.map (MulAut.conj t).toMonoidHom) U) : U = ⊥ ∨ U = ⊤ :=
  hirr.2.2.2 U hU bot_le le_top

private theorem w4s_eq_one_of_mem_centralizer
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥) {c : MulAut W}
    (hc : c ∈ Subgroup.centralizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)))
    (hne : fixV (Subgroup.zpowers c) ≠ ⊥) : c = 1 := by
  have hU : StableUnder (L ⊔ L.map (MulAut.conj t).toMonoidHom) (fixV (Subgroup.zpowers c)) := by
    intro b hb w hw
    rw [mem_fixV_zpowers_iff_apply] at hw ⊢
    rw [← MulAut.mul_apply, ← Subgroup.mem_centralizer_iff.mp hc b hb, MulAut.mul_apply, hw]
  rcases w4s_eq_bot_or_eq_top hirr hU with h | h
  · exact absurd h hne
  · refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    exact mem_fixV_zpowers_iff_apply.mp (h ▸ Subgroup.mem_top w)

private theorem w4s_inv_eq (hW : ∀ w : W, w ^ 2 = 1) (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW w)

private theorem w4s_eq_one_of_sq (hW : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥) {c : MulAut W}
    (hc : c ∈ Subgroup.centralizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)))
    (hc2 : c ^ 2 = 1) : c = 1 := by
  refine w4s_eq_one_of_mem_centralizer hirr hc fun hbot => ?_
  have hcc : ∀ w : W, c (c w) = w := fun w => by
    rw [← MulAut.mul_apply, ← pow_two, hc2, MulAut.one_apply]
  have hall : ∀ w : W, w = 1 := by
    intro w
    have h1 : c w * w ∈ fixV (Subgroup.zpowers c) := by
      rw [mem_fixV_zpowers_iff_apply, map_mul, hcc, mul_comm]
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : w ∈ fixV (Subgroup.zpowers c) := by
      rw [mem_fixV_zpowers_iff_apply, eq_inv_of_mul_eq_one_left h1, w4s_inv_eq hW]
    rw [hbot, Subgroup.mem_bot] at h2
    exact h2
  exact hirr.1.ne ((Subgroup.eq_bot_iff_forall ⊤).mpr fun w _ => hall w).symm

private theorem w4s_fixV_eq_bot (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥) :
    fixV (L ⊔ L.map (MulAut.conj t).toMonoidHom) = ⊥ := by
  have hU : StableUnder (L ⊔ L.map (MulAut.conj t).toMonoidHom)
      (fixV (L ⊔ L.map (MulAut.conj t).toMonoidHom)) := by
    intro b hb w hw x hx
    rw [hw b hb]
    exact hw x hx
  rcases w4s_eq_bot_or_eq_top hirr hU with h | h
  · exact h
  · exfalso
    have h1 : ∀ x : ↥L, x = 1 := fun x => by
      refine Subtype.ext (MulEquiv.ext fun w => ?_)
      have hw : w ∈ fixV (L ⊔ L.map (MulAut.conj t).toMonoidHom) := h ▸ Subgroup.mem_top w
      rw [Subgroup.coe_one, MulAut.one_apply]
      exact hw x (Subgroup.mem_sup_left x.2)
    obtain ⟨a, b, hab⟩ := (CFSG.ComponentClassification.Quasisimple.nontrivial hLq).exists_pair_ne
    exact hab ((h1 a).trans (h1 b).symm)

private theorem w4s_le_of_normalized (hLq : CFSG.Open.IsQuasisimple ↥L)
    {N : Subgroup (MulAut W)} (hNL : N ≤ L) (hNn : ∀ y ∈ L, ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hNZ : ∃ n ∈ N, ∃ x ∈ L, n * x ≠ x * n) : L ≤ N := by
  have hnorm : (N.subgroupOf L).Normal :=
    ⟨fun n hn y => Subgroup.mem_subgroupOf.mpr (hNn y y.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLq
      (N.subgroupOf L) with h | h
  · exfalso
    obtain ⟨n, hn, x, hx, hne⟩ := hNZ
    have hmem : (⟨n, hNL hn⟩ : ↥L) ∈ Subgroup.center ↥L := h (Subgroup.mem_subgroupOf.mpr hn)
    exact hne (congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩)).symm
  · intro y hy
    have hy' : (⟨y, hy⟩ : ↥L) ∈ N.subgroupOf L := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hy'

private theorem w4s_comm_apply {x a g : MulAut W} {w : W} (h1 : (x * a) w = w)
    (h2 : (x * a) (g w) = g w) (hc : a * g = g * a) : (g⁻¹ * x * g * x⁻¹) w = w := by
  have ha : x⁻¹ w = a w := by
    calc x⁻¹ w = x⁻¹ ((x * a) w) := by rw [h1]
      _ = a w := by rw [MulAut.mul_apply, MulAut.inv_apply_self]
  calc (g⁻¹ * x * g * x⁻¹) w = g⁻¹ (x (g (x⁻¹ w))) := by simp only [MulAut.mul_apply]
    _ = g⁻¹ ((x * a) (g w)) := by
        rw [ha, ← MulAut.mul_apply _ g a w, ← hc, MulAut.mul_apply _ a g w,
          MulAut.mul_apply _ x a (g w)]
    _ = w := by rw [h2, MulAut.inv_apply_self]

theorem inf_commV_conj_eq_bot (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w)
    {g : MulAut W} (hg : g ∈ L) (hgZ : ∃ x ∈ L, g * x ≠ x * g) :
    commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers (g⁻¹ * t * g)) = ⊥ := by
  have hgI : ∀ w ∈ commV (Subgroup.zpowers (g⁻¹ * t * g)),
      g w ∈ commV (Subgroup.zpowers t) := by
    intro w hw
    rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], commV_zpowers_conj_eq] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    simpa using hu
  have hs : ∀ x ∈ L, g⁻¹ * x * g * x⁻¹ ∈
      centSub (commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers (g⁻¹ * t * g))) := by
    intro x hx
    rw [mem_centSub]
    intro w hw
    exact w4s_comm_apply (hdiag x hx w hw.1) (hdiag x hx (g w) (hgI w hw.2))
      (w4s_comm_conj hcomm hg hx).symm
  let S : Set (MulAut W) := {s | ∃ x ∈ L, g⁻¹ * x * g * x⁻¹ = s}
  have hNL : Subgroup.closure S ≤ L := by
    refine (Subgroup.closure_le L).mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hg) hx) hg) (L.inv_mem hx)
  have hNK : Subgroup.closure S ≤
      centSub (commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers (g⁻¹ * t * g))) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hs x hx
  have hNn : ∀ y ∈ L, ∀ n ∈ Subgroup.closure S, y * n * y⁻¹ ∈ Subgroup.closure S := by
    intro y hy n hn
    induction hn using Subgroup.closure_induction with
    | mem n hn =>
      obtain ⟨x, hx, rfl⟩ := hn
      have e : y * (g⁻¹ * x * g * x⁻¹) * y⁻¹ =
          (g⁻¹ * y * g * y⁻¹)⁻¹ * (g⁻¹ * (y * x) * g * (y * x)⁻¹) := by group
      rw [e]
      exact (Subgroup.closure S).mul_mem
        ((Subgroup.closure S).inv_mem (Subgroup.subset_closure ⟨y, hy, rfl⟩))
        (Subgroup.subset_closure ⟨y * x, L.mul_mem hy hx, rfl⟩)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : y * (a * b) * y⁻¹ = y * a * y⁻¹ * (y * b * y⁻¹) := by group
      rw [e]
      exact (Subgroup.closure S).mul_mem ha hb
    | inv a _ ha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact (Subgroup.closure S).inv_mem ha
  have hNZ : ∃ n ∈ Subgroup.closure S, ∃ x ∈ L, n * x ≠ x * n := by
    by_contra hcon
    push Not at hcon
    have hcen : (⟨g⁻¹, L.inv_mem hg⟩ : ↥L) ∈ Subgroup.center ↥L := by
      refine CFSG.LocalAnalysis.GLTheoremA.HSubT.mem_center_of_commutator_mem_center hLq
        fun y => Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_
      have h := hcon (g⁻¹ * y * g * (y : MulAut W)⁻¹) (Subgroup.subset_closure ⟨y, y.2, rfl⟩) x x.2
      simpa [commutatorElement_def] using h.symm
    obtain ⟨x, hx, hne⟩ := hgZ
    apply hne
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨x, hx⟩)
    simp only [Subgroup.coe_mul] at h
    calc g * x = g * (x * g⁻¹) * g := by group
      _ = g * (g⁻¹ * x) * g := by rw [h]
      _ = x * g := by group
  have hLK : L ≤ centSub (commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers (g⁻¹ * t * g))) :=
    (w4s_le_of_normalized hLq hNL hNn hNZ).trans hNK
  have hLtK : L.map (MulAut.conj t).toMonoidHom ≤
      centSub (commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers (g⁻¹ * t * g))) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centSub]
    intro w hw
    have h2 : y⁻¹ w = w := (mem_centSub.mp (hLK (L.inv_mem hy))) w hw
    show (t * y * t⁻¹) w = w
    calc (t * y * t⁻¹) w = y⁻¹ ((y * (t * y * t⁻¹)) w) := by
          rw [MulAut.mul_apply _ y (t * y * t⁻¹) w, MulAut.inv_apply_self]
      _ = w := by rw [hdiag y hy w hw.1, h2]
  rw [eq_bot_iff, ← w4s_fixV_eq_bot hLq hirr]
  intro w hw b hb
  exact (mem_centSub.mp (sup_le hLK hLtK hb)) w hw

private theorem w4s_commV_ne_bot (ht2 : orderOf t = 2) : commV (Subgroup.zpowers t) ≠ ⊥ := by
  intro h
  have ht1 : t = 1 := MulEquiv.ext fun v => by
    have hv : t v * v⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hv
    rw [MulAut.one_apply]
    exact hv
  rw [ht1, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

private theorem w4s_sq_eq_one (hW : ∀ w : W, w ^ 2 = 1) {r z : MulAut W} (hz2 : z ^ 2 = 1)
    (hrz : r * z = z * r) (hrU : ∀ u : W, z u = u → r u = u) : r ^ 2 = 1 := by
  have hzz : ∀ w : W, z (z w) = w := fun w => by
    rw [← MulAut.mul_apply, ← pow_two, hz2, MulAut.one_apply]
  refine MulEquiv.ext fun w => ?_
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  have E1 : r (z w) * r w = z w * w := by
    have h := hrU (z w * w) (by rw [map_mul, hzz, mul_comm])
    rwa [map_mul] at h
  have hx : z (r w * w) = r w * w := by
    have h3 : r (z w) = z w * w * (r w)⁻¹ := eq_mul_inv_of_mul_eq E1
    have hzw : z w * z w = 1 := by rw [← pow_two]; exact hW _
    rw [map_mul, ← MulAut.mul_apply, ← hrz, MulAut.mul_apply, h3, w4s_inv_eq hW]
    calc z w * w * r w * z w = z w * z w * (r w * w) := by ac_rfl
      _ = r w * w := by rw [hzw, one_mul]
  have E2 := hrU _ hx
  rw [map_mul] at E2
  calc r (r w) = r (r w) * r w * (r w)⁻¹ := by rw [mul_inv_cancel_right]
    _ = r w * w * (r w)⁻¹ := by rw [E2]
    _ = w := by rw [mul_comm (r w) w, mul_inv_cancel_right]

end Disjoint

section Orders

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

theorem orderOf_mul_conj_dvd_two_or_odd (hW : ∀ w : W, w ^ 2 = 1)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (ht2 : orderOf t = 2)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w)
    {g : MulAut W} (hg : g ∈ L) :
    orderOf (t * (g⁻¹ * t * g)) ∣ 2 ∨ Odd (orderOf (t * (g⁻¹ * t * g))) := by
  rcases Nat.even_or_odd (orderOf (t * (g⁻¹ * t * g))) with ⟨m, hm⟩ | hodd
  · left
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have hag : Commute (t * g⁻¹ * t⁻¹) g := (w4s_comm_conj hcomm hg (L.inv_mem hg)).symm
    have hr : t * (g⁻¹ * t * g) = t * g⁻¹ * t⁻¹ * g := by
      rw [inv_eq_of_mul_eq_one_right htt]; group
    rw [hr] at hm ⊢
    have hpos : 0 < orderOf (t * g⁻¹ * t⁻¹ * g) := orderOf_pos _
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hz : (t * g⁻¹ * t⁻¹ * g) ^ m = t * (g ^ m)⁻¹ * t⁻¹ * g ^ m := by
      rw [hag.mul_pow, conj_pow, inv_pow]
    have hz2 : (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) ^ 2 = 1 := by
      rw [← hz, ← pow_mul, mul_comm m 2, two_mul, ← hm, pow_orderOf_eq_one]
    have hz1 : t * (g ^ m)⁻¹ * t⁻¹ * g ^ m ≠ 1 := by
      rw [← hz]
      exact pow_ne_one_of_lt_orderOf hm0 (by omega)
    have hcL : g ^ m ∈ L := L.pow_mem hg m
    have hcZ : ∃ x ∈ L, g ^ m * x ≠ x * g ^ m := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := w4s_mem_centralizer_of_central hcomm hcL hcon
      refine hz1 (w4s_eq_one_of_sq hW hirr ?_ hz2)
      have e : t * (g ^ m)⁻¹ * t⁻¹ * g ^ m = (t * g ^ m * t⁻¹)⁻¹ * g ^ m := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    have hD := inf_commV_conj_eq_bot hLq hcomm hirr hdiag hcL hcZ
    have htz : t * (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) = (g ^ m)⁻¹ * t * g ^ m := by
      calc t * (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) = t * t * (g ^ m)⁻¹ * t⁻¹ * g ^ m := by group
        _ = (g ^ m)⁻¹ * t * g ^ m := by rw [htt, inv_eq_of_mul_eq_one_right htt]; group
    have htU : ∀ u : W, (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) u = u → t u = u := by
      intro u hu
      have hmem : t u * u⁻¹ ∈
          commV (Subgroup.zpowers t) ⊓ commV (Subgroup.zpowers ((g ^ m)⁻¹ * t * g ^ m)) := by
        refine ⟨Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, rfl⟩, ?_⟩
        have e : t u = ((g ^ m)⁻¹ * t * g ^ m) u := by
          rw [← htz, MulAut.mul_apply, hu]
        rw [e]
        exact Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, u, rfl⟩
      rw [hD, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    have hgz : g * (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) = t * (g ^ m)⁻¹ * t⁻¹ * g ^ m * g := by
      have h1 : g * (t * (g ^ m)⁻¹ * t⁻¹) = t * (g ^ m)⁻¹ * t⁻¹ * g :=
        w4s_comm_conj hcomm hg (L.inv_mem hcL)
      have h2 : g * g ^ m = g ^ m * g := (Commute.self_pow g m).eq
      calc g * (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) = g * (t * (g ^ m)⁻¹ * t⁻¹) * g ^ m := by group
        _ = t * (g ^ m)⁻¹ * t⁻¹ * (g * g ^ m) := by rw [h1]; group
        _ = t * (g ^ m)⁻¹ * t⁻¹ * g ^ m * g := by rw [h2]; group
    have hrU : ∀ u : W, (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) u = u → (t * g⁻¹ * t⁻¹ * g) u = u := by
      intro u hu
      have hgu : (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) (g u) = g u := by
        rw [← MulAut.mul_apply, ← hgz, MulAut.mul_apply, hu]
      rw [← hr]
      simp only [MulAut.mul_apply]
      rw [htU _ hgu, MulAut.inv_apply_self, htU u hu]
    have hrz : t * g⁻¹ * t⁻¹ * g * (t * (g ^ m)⁻¹ * t⁻¹ * g ^ m) =
        t * (g ^ m)⁻¹ * t⁻¹ * g ^ m * (t * g⁻¹ * t⁻¹ * g) := by
      rw [← hz]
      exact (Commute.self_pow _ m).eq
    exact orderOf_dvd_of_pow_eq_one (w4s_sq_eq_one hW hz2 hrz hrU)
  · exact Or.inr hodd

private theorem w4s_exists_involution (hLq : CFSG.Open.IsQuasisimple ↥L) :
    ∃ s ∈ L, s ^ 2 = 1 ∧ s ≠ 1 := by
  have h2 : 2 ∣ Nat.card ↥L := by
    by_contra hodd
    have hsolv : Group.IsSolvable ↥L :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
    have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥L)).ne hLq.1
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2
  refine ⟨s, s.2, ?_, fun h1 => ?_⟩
  · rw [← Subgroup.orderOf_coe] at hs
    rw [← hs]
    exact pow_orderOf_eq_one _
  · rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hs
    exact absurd hs (by norm_num)

theorem eq_one_of_mem_center (hW : ∀ w : W, w ^ 2 = 1)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (ht2 : orderOf t = 2)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w)
    {z : MulAut W} (hz : z ∈ L) (hzc : ∀ x ∈ L, z * x = x * z) : z = 1 := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  obtain ⟨hzB, hztB⟩ := w4s_mem_centralizer_of_central hcomm hz hzc
  have hzt : z * (t * z * t⁻¹) = 1 := by
    refine w4s_eq_one_of_mem_centralizer hirr (Subgroup.mul_mem _ hzB hztB) fun hbot => ?_
    refine w4s_commV_ne_bot ht2 (eq_bot_iff.mpr ?_)
    rw [← hbot]
    intro w hw
    exact mem_fixV_zpowers_iff_apply.mpr (hdiag z hz w hw)
  have hzt' : t * z⁻¹ * t⁻¹ = z := by
    calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
      _ = z := by rw [eq_inv_of_mul_eq_one_right hzt, inv_inv]
  obtain ⟨s, hsL, hs2, hs1⟩ := w4s_exists_involution hLq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs2)
  have hss : Commute (t * s * t⁻¹) s := (w4s_comm_conj hcomm hsL hsL).symm
  have hu2 : (t * s * t⁻¹ * s) ^ 2 = 1 := by
    rw [hss.mul_pow, conj_pow, hs2]
    group
  have hu1 : t * s * t⁻¹ * s ≠ 1 := by
    intro h
    have hst : t * s * t⁻¹ = s := by
      calc t * s * t⁻¹ = t * s * t⁻¹ * s * s⁻¹ := by group
        _ = s := by rw [h, one_mul, hsinv]
    refine hs1 (w4s_eq_one_of_sq hW hirr (w4s_mem_centralizer (fun x hx => ?_) fun y hy => ?_) hs2)
    · have h1 := w4s_comm_conj hcomm hx hsL
      rwa [hst] at h1
    · exact (w4s_comm_conj hcomm hsL hy).symm
  have huB : t * s * t⁻¹ * s ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨s, hsL, rfl⟩) (Subgroup.mem_sup_left hsL)
  have hzu : t * s * t⁻¹ * s * z = z * (t * s * t⁻¹ * s) :=
    Subgroup.mem_centralizer_iff.mp hzB _ huB
  have hr : t * ((s * z)⁻¹ * t * (s * z)) = t * s * t⁻¹ * s * (z * z) := by
    calc t * ((s * z)⁻¹ * t * (s * z)) =
          t * z⁻¹ * t⁻¹ * (t * s⁻¹ * t⁻¹) * (t * t) * s * z := by group
      _ = z * (t * s * t⁻¹ * s) * z := by rw [hzt', hsinv, htt]; group
      _ = t * s * t⁻¹ * s * (z * z) := by rw [← hzu]; group
  have hyB : z * z ∈ Subgroup.centralizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)) :=
    Subgroup.mul_mem _ hzB hzB
  have huy : Commute (t * s * t⁻¹ * s) (z * z) := Subgroup.mem_centralizer_iff.mp hyB _ huB
  rcases orderOf_mul_conj_dvd_two_or_odd hW hLq ht2 hcomm hirr hdiag (L.mul_mem hsL hz) with
    h | h
  · rw [hr] at h
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [huy.mul_pow, hu2, one_mul] at h2
    have hy1 : z * z = 1 := w4s_eq_one_of_sq hW hirr hyB h2
    exact w4s_eq_one_of_sq hW hirr hzB (by rw [pow_two]; exact hy1)
  · exfalso
    rw [hr] at h
    obtain ⟨k, hk⟩ := h
    have h1 := pow_orderOf_eq_one (t * s * t⁻¹ * s * (z * z))
    rw [hk, huy.mul_pow, pow_succ (t * s * t⁻¹ * s), pow_mul, hu2, one_pow, one_mul] at h1
    refine hu1 (w4s_eq_one_of_sq hW hirr ?_ hu2)
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hyB _)

theorem orderOf_dvd_two_or_odd (hW : ∀ w : W, w ^ 2 = 1)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (ht2 : orderOf t = 2)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w)
    {g : MulAut W} (hg : g ∈ L) : orderOf g ∣ 2 ∨ Odd (orderOf g) := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hag : Commute (t * g⁻¹ * t⁻¹) g := (w4s_comm_conj hcomm hg (L.inv_mem hg)).symm
  have hr : t * (g⁻¹ * t * g) = t * g⁻¹ * t⁻¹ * g := by
    rw [inv_eq_of_mul_eq_one_right htt]; group
  have hpow : ∀ k : ℕ, (t * g⁻¹ * t⁻¹ * g) ^ k = t * (g ^ k)⁻¹ * t⁻¹ * g ^ k := fun k => by
    rw [hag.mul_pow, conj_pow, inv_pow]
  have heq : orderOf (t * (g⁻¹ * t * g)) = orderOf g := by
    rw [hr]
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
    · rw [hpow, pow_orderOf_eq_one]
      group
    · have h1 := pow_orderOf_eq_one (t * g⁻¹ * t⁻¹ * g)
      rw [hpow] at h1
      have h2 : g ^ orderOf (t * g⁻¹ * t⁻¹ * g) = t * g ^ orderOf (t * g⁻¹ * t⁻¹ * g) * t⁻¹ := by
        calc g ^ orderOf (t * g⁻¹ * t⁻¹ * g) =
              (t * (g ^ orderOf (t * g⁻¹ * t⁻¹ * g))⁻¹ * t⁻¹)⁻¹ :=
            eq_inv_of_mul_eq_one_right h1
          _ = t * g ^ orderOf (t * g⁻¹ * t⁻¹ * g) * t⁻¹ := by group
      refine eq_one_of_mem_center hW hLq ht2 hcomm hirr hdiag (L.pow_mem hg _) fun x hx => ?_
      rw [h2]
      exact (w4s_comm_conj hcomm hx (L.pow_mem hg _)).symm
  rw [← heq]
  exact orderOf_mul_conj_dvd_two_or_odd hW hLq ht2 hcomm hirr hdiag hg

end Orders

end CFSG.LocalAnalysis.WeakClosure81
