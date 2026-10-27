module

public import CFSG.Quasithin.H13.A6S13821zi
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.H13.L32AC47n
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.Quasithin.H13.L32A.C
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem map_le_sup_of_d310Two {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hMp : Mp = L)
    (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V) (hLs : L ≤ stabSub V)
    (hTL : ∀ s ∈ T, ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) (hTL' : ∀ s ∈ T, ∀ γ ∈ L, s⁻¹ * γ * s ∈ L)
    (h3 : D310Two T L V) {y : MulAut W} (hyL : ∀ γ ∈ L, γ * y = y * γ) :
    ∀ v ∈ V, y v ∈ V ⊔ fixV L := by
  classical
  obtain ⟨-, ⟨s, hsT, hsV⟩, hall⟩ := h3
  obtain ⟨⟨hsum1, hsum2⟩, hniso⟩ := hall s hsT hsV
  have hyL' : ∀ γ ∈ L, γ * y⁻¹ = y⁻¹ * γ := fun γ hγ => by
    have h1 := hyL γ hγ
    calc γ * y⁻¹ = y⁻¹ * (y * γ) * y⁻¹ := by group
      _ = y⁻¹ * (γ * y) * y⁻¹ := by rw [h1]
      _ = y⁻¹ * γ := by group
  have hyC : ∀ c ∈ fixV L, y c ∈ fixV L := fun c hc γ hγ => by
    rw [← MulAut.mul_apply, hyL γ hγ, MulAut.mul_apply, hc γ hγ]
  have hLA : ∀ γ ∈ L, ∀ a ∈ V ⊔ fixV L, γ a ∈ V ⊔ fixV L := by
    intro γ hγ a ha
    obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp ha
    rw [map_mul, hc γ hγ]
    exact (V ⊔ fixV L).mul_mem (Subgroup.mem_sup_left ((hLs hγ v).mpr hv))
      (Subgroup.mem_sup_right hc)
  have hyγ : ∀ γ ∈ L, ∀ w, y (γ w) = γ (y w) := fun γ hγ w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hyL γ hγ]
  let J : Subgroup W :=
    { carrier := {u | u ∈ V ∧ y u ∈ V ⊔ fixV L}
      one_mem' := ⟨V.one_mem, by rw [map_one]; exact (V ⊔ fixV L).one_mem⟩
      mul_mem' := fun ha hb => ⟨V.mul_mem ha.1 hb.1, by
        rw [map_mul]; exact (V ⊔ fixV L).mul_mem ha.2 hb.2⟩
      inv_mem' := fun ha => ⟨V.inv_mem ha.1, by
        rw [map_inv]; exact (V ⊔ fixV L).inv_mem ha.2⟩ }
  have hfixC : ∀ u, u ∈ XMod.fixed ↥Mp V ↔ u ∈ V ⊓ fixV L := fun u => by
    constructor
    · rintro ⟨hu, hf⟩
      exact ⟨hu, fun γ hγ => hf ⟨γ, hMp ▸ hγ⟩⟩
    · rintro ⟨hu, hc⟩
      exact ⟨hu, fun a => hc a (hMp ▸ a.2)⟩
  have hJinv : XMod.IsInv ↥Mp J := by
    intro a u hu
    have ha : (a : MulAut W) ∈ L := hMp ▸ a.2
    refine ⟨(hLs ha u).mpr hu.1, ?_⟩
    show y ((a : MulAut W) u) ∈ V ⊔ fixV L
    rw [hyγ _ ha]
    exact hLA _ ha _ hu.2
  have hfJ : XMod.fixed ↥Mp V ≤ J := fun u hu => by
    obtain ⟨hu1, hu2⟩ := (hfixC u).mp hu
    exact ⟨hu1, Subgroup.mem_sup_right (hyC u hu2)⟩
  rcases hirr.2 J hJinv hfJ (fun u hu => hu.1) with hJ | hJ
  ·
    exfalso
    apply hniso
    rw [B5.secIsoL_iff]
    have hsC : s ∈ stabSub (fixV L) := mem_stabSub_fixV_of_conj (hTL s hsT) (hTL' s hsT)
    have hLB : ∀ γ ∈ L, ∀ m ∈ V.map s.toMonoidHom, γ m ∈ V.map s.toMonoidHom := by
      rintro γ hγ _ ⟨v, hv, rfl⟩
      refine ⟨(s⁻¹ * γ * s) v, (hLs (hTL' s hsT γ hγ) v).mpr hv, ?_⟩
      show s ((s⁻¹ * γ * s) v) = γ (s v)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    refine ⟨inf_le_left, inf_le_left, fun h u hu => (hLs h.2 u).mpr hu,
      fun h z hz => ⟨(hLs h.2 z).mpr hz.1, by rw [hz.2 h h.2]; exact hz.2⟩,
      fun γ m hm => hLB _ γ.2 m hm,
      fun γ m hm => ⟨hLB _ γ.2 m hm.1, by rw [hm.2 γ γ.2]; exact hm.2⟩, ?_⟩
    let qB : ↥(V.map s.toMonoidHom) →* W ⧸ (V ⊔ fixV L) :=
      (QuotientGroup.mk' (V ⊔ fixV L)).comp (V.map s.toMonoidHom).subtype
    have hqB : Function.Surjective qB := by
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (V ⊔ fixV L) z
      have hw : w ∈ V ⊔ V.map s.toMonoidHom ⊔ fixV L := hsum1 ▸ Subgroup.mem_top w
      obtain ⟨y₁, hy₁, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
      obtain ⟨v, hv, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy₁
      refine ⟨⟨b, hb⟩, ?_⟩
      show (QuotientGroup.mk' (V ⊔ fixV L)) b = (QuotientGroup.mk' (V ⊔ fixV L)) (v * b * c)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        show v * b * c = b * (v * c) by rw [mul_comm v b, mul_assoc], inv_mul_cancel_left]
      exact (V ⊔ fixV L).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hc)
    have hkerB : qB.ker = (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom) := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (QuotientGroup.mk' (V ⊔ fixV L)) (b : W) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro hbA
        exact ⟨b.2, hsum2 ⟨hbA, Subgroup.mem_sup_left b.2⟩⟩
      · intro hbC
        exact Subgroup.mem_sup_right hbC.2
    let eB := (QuotientGroup.quotientMulEquivOfEq hkerB.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qB hqB)
    have heB : ∀ m : ↥(V.map s.toMonoidHom), eB (QuotientGroup.mk m) =
        QuotientGroup.mk (m : W) := fun m => rfl
    let β : ↥V →* ↥(V.map s.toMonoidHom) ⧸
        (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom) :=
      eB.symm.toMonoidHom.comp
        ((QuotientGroup.mk' (V ⊔ fixV L)).comp (y.toMonoidHom.comp V.subtype))
    have hβ : ∀ u : ↥V, eB (β u) = QuotientGroup.mk (y u) := fun u => by
      show eB (eB.symm _) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hβ1 : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ V ⊓ fixV L := by
      intro u
      rw [← (hfixC u).trans Iff.rfl, ← hJ]
      constructor
      · intro h1
        have h2 := hβ u
        rw [h1, map_one] at h2
        exact ⟨u.2, (QuotientGroup.eq_one_iff _).mp h2.symm⟩
      · intro h1
        apply eB.injective
        rw [hβ, map_one]
        exact (QuotientGroup.eq_one_iff _).mpr h1.2
    refine ⟨β, ?_, hβ1, ?_⟩
    ·
      have hker : β.ker = (V ⊓ fixV L).subgroupOf V := by
        ext u
        rw [MonoidHom.mem_ker, hβ1, Subgroup.mem_subgroupOf]
      have hr : Nat.card β.range = (V ⊓ fixV L).relIndex V := by
        rw [← Subgroup.index_ker, hker]
        rfl
      have hcod : Nat.card (↥(V.map s.toMonoidHom) ⧸
          (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom)) =
          (V ⊓ fixV L).relIndex V := by
        rw [← Subgroup.index_eq_card]
        show (V.map s.toMonoidHom ⊓ fixV L).relIndex (V.map s.toMonoidHom) = _
        have hC' : fixV L = (fixV L).map s.toMonoidHom := (map_eq_of_mem_stabSub hsC).symm
        have h1 : (V.map s.toMonoidHom ⊓ (fixV L).map s.toMonoidHom).relIndex
            (V.map s.toMonoidHom) = (V ⊓ fixV L).relIndex V := by
          rw [← Subgroup.map_inf_eq _ _ s.toMonoidHom s.injective,
            Subgroup.relIndex_map_map_of_injective _ _ s.injective]
        rw [← hC'] at h1
        exact h1
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ (hr.trans hcod.symm)
    ·
      intro γ u m hu hm hum
      apply eB.injective
      rw [hβ, heB]
      have h1 := hβ u
      rw [hum, heB] at h1
      have h2 := (QuotientGroup.eq.mp h1)
      show QuotientGroup.mk (y ((γ : MulAut W) u)) = QuotientGroup.mk ((γ : MulAut W) m)
      rw [QuotientGroup.eq, hyγ _ γ.2, ← map_inv, ← map_mul]
      exact hLA _ γ.2 _ (by simpa using (V ⊔ fixV L).inv_mem h2)
  · intro v hv
    have hvJ : v ∈ J := hJ ▸ hv
    exact hvJ.2

theorem nonabelian_autSec {L : Subgroup (MulAut W)} {A C : Subgroup W}
    (hLA : L ≤ stabSub A ⊓ stabSub C) (hperf : ⁅L, L⁆ = L)
    (hnt : ∃ γ ∈ L, ∃ a ∈ A, γ a * a⁻¹ ∉ C) :
    ∃ a b : ↥(autSec L A C), a * b ≠ b * a := by
  classical
  set Y : Subgroup (MulAut W) := stabSub A ⊓ stabSub C with hY
  have hYW : Y ≤ stabSub A := inf_le_left
  have hYU : Y ≤ stabSub C := inf_le_right
  set φ := B5.secHom Y hYW hYU with hφ
  have hBmap : (L.subgroupOf Y).map φ = autSec L A C := B5.map_secHom_eq_autSec Y hYW hYU hLA
  by_contra hcon
  push Not at hcon
  have hcomm : ⁅L, L⁆ ≤ (φ.ker).map Y.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hm₁ : φ ⟨g₁, hLA hg₁⟩ ∈ autSec L A C := by
      rw [← hBmap]
      exact ⟨⟨g₁, hLA hg₁⟩, Subgroup.mem_subgroupOf.mpr hg₁, rfl⟩
    have hm₂ : φ ⟨g₂, hLA hg₂⟩ ∈ autSec L A C := by
      rw [← hBmap]
      exact ⟨⟨g₂, hLA hg₂⟩, Subgroup.mem_subgroupOf.mpr hg₂, rfl⟩
    have hc := hcon ⟨_, hm₁⟩ ⟨_, hm₂⟩
    have hc' : φ ⟨g₁, hLA hg₁⟩ * φ ⟨g₂, hLA hg₂⟩ = φ ⟨g₂, hLA hg₂⟩ * φ ⟨g₁, hLA hg₁⟩ :=
      congrArg Subtype.val hc
    refine ⟨⁅(⟨g₁, hLA hg₁⟩ : ↥Y), ⟨g₂, hLA hg₂⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hc'
  obtain ⟨γ, hγ, a, ha, hγa⟩ := hnt
  rw [hperf] at hcomm
  obtain ⟨g, hg, hgγ⟩ := hcomm hγ
  have h1 := ((B5.mem_ker_secHom Y hYW hYU g).1 hg).2 a ha
  have hg' : (g : MulAut W) = γ := hgγ
  rw [hg'] at h1
  exact hγa h1

theorem false_of_d310Two_cube (hW : ∀ w : W, w * w = 1) {Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} (hMp : Mp = L) (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V)
    (hLs : L ≤ stabSub V) (hperf : ⁅L, L⁆ = L)
    (hTL : ∀ s ∈ T, ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) (hTL' : ∀ s ∈ T, ∀ γ ∈ L, s⁻¹ * γ * s ∈ L)
    (h3 : D310Two T L V) {y r : MulAut W} (hy3 : y ^ 3 = 1) (hcube : ∀ w, w * y w * y (y w) = 1)
    (hyL : ∀ γ ∈ L, γ * y = y * γ) (hrL : ∀ γ ∈ L, γ * r = r * γ) {e : ℕ} (hr2 : r ^ 2 ^ e = 1)
    (hry : r * y * r⁻¹ = y⁻¹) (hnt : ∃ γ ∈ L, ∃ v ∈ V, γ v * v⁻¹ ∉ fixV L) : False := by
  classical
  set A := V ⊔ fixV L with hA
  set C := fixV L with hC
  have hfixC : ∀ u, u ∈ XMod.fixed ↥Mp V ↔ u ∈ V ⊓ fixV L := fun u => by
    constructor
    · rintro ⟨hu, hf⟩
      exact ⟨hu, fun γ hγ => hf ⟨γ, hMp ▸ hγ⟩⟩
    · rintro ⟨hu, hc⟩
      exact ⟨hu, fun a => hc a (hMp ▸ a.2)⟩
  have hstab : ∀ g : MulAut W, (∀ γ ∈ L, γ * g = g * γ) → g ∈ stabSub A ⊓ stabSub C := by
    intro g hg
    have hg' : ∀ γ ∈ L, γ * g⁻¹ = g⁻¹ * γ := fun γ hγ => by
      have h1 := hg γ hγ
      calc γ * g⁻¹ = g⁻¹ * (g * γ) * g⁻¹ := by group
        _ = g⁻¹ * (γ * g) * g⁻¹ := by rw [h1]
        _ = g⁻¹ * γ := by group
    have hgC : g ∈ stabSub C := mem_stabSub_fixV_of_conj
      (fun m hm => by rw [← hg m hm, mul_inv_cancel_right]; exact hm)
      (fun m hm => by rw [← hg' m hm, inv_mul_cancel_right]; exact hm)
    have hmap : ∀ g' : MulAut W, (∀ γ ∈ L, γ * g' = g' * γ) → ∀ a ∈ A, g' a ∈ A := by
      intro g' hg'' a ha
      have hg'C : ∀ c ∈ C, g' c ∈ C := fun c hc γ hγ => by
        rw [← MulAut.mul_apply, hg'' γ hγ, MulAut.mul_apply, hc γ hγ]
      obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp ha
      rw [map_mul]
      exact A.mul_mem (map_le_sup_of_d310Two hMp hirr hLs hTL hTL' h3 hg'' v hv)
        (Subgroup.mem_sup_right (hg'C c hc))
    refine ⟨fun a => ⟨fun ha => ?_, fun ha => hmap g hg a ha⟩, hgC⟩
    have h1 := hmap g⁻¹ hg' _ ha
    rwa [MulAut.inv_apply_self] at h1
  have hLA : L ≤ stabSub A ⊓ stabSub C := by
    have hmapL : ∀ γ ∈ L, ∀ a ∈ A, γ a ∈ A := by
      intro γ hγ a ha
      obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp ha
      rw [map_mul, hc γ hγ]
      exact A.mul_mem (Subgroup.mem_sup_left ((hLs hγ v).mpr hv)) (Subgroup.mem_sup_right hc)
    intro γ hγ
    refine ⟨fun a => ⟨fun ha => ?_, fun ha => hmapL γ hγ a ha⟩,
      mem_stabSub_fixV_of_conj (fun m hm => L.mul_mem (L.mul_mem hγ hm) (L.inv_mem hγ))
        (fun m hm => L.mul_mem (L.mul_mem (L.inv_mem hγ) hm) hγ)⟩
    have h1 := hmapL γ⁻¹ (L.inv_mem hγ) _ ha
    rwa [MulAut.inv_apply_self] at h1
  have hCV : V ⊓ C < V := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    apply hirr.1.ne
    ext u
    rw [hfixC]
    exact ⟨fun hu => hu.1, fun hu => h.symm ▸ hu⟩
  have hCA : C < A := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    apply hCV.ne
    refine le_antisymm inf_le_left fun v hv => ⟨hv, ?_⟩
    rw [h]
    exact Subgroup.mem_sup_left hv
  have hirrA : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → C ≤ J → J ≤ A →
      J = C ∨ J = A := by
    intro J hJ hCJ hJA
    have hJinv : XMod.IsInv ↥Mp (J ⊓ V) := by
      intro a u hu
      have ha : (a : MulAut W) ∈ L := hMp ▸ a.2
      exact ⟨hJ _ ha u hu.1, (hLs ha u).mpr hu.2⟩
    have hfJ : XMod.fixed ↥Mp V ≤ J ⊓ V := fun u hu => by
      obtain ⟨hu1, hu2⟩ := (hfixC u).mp hu
      exact ⟨hCJ hu2, hu1⟩
    rcases hirr.2 (J ⊓ V) hJinv hfJ inf_le_right with h | h
    · left
      refine le_antisymm (fun j hj => ?_) hCJ
      obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp (hJA hj)
      have hvJ : v ∈ J := by
        have := J.mul_mem hj (J.inv_mem (hCJ hc))
        rwa [mul_inv_cancel_right] at this
      have hvf : v ∈ XMod.fixed ↥Mp V := by
        rw [← h]
        exact ⟨hvJ, hv⟩
      exact C.mul_mem ((hfixC v).mp hvf).2 hc
    · right
      refine le_antisymm hJA (sup_le (fun v hv => ?_) hCJ)
      have h2 : v ∈ J ⊓ V := by
        rw [h]
        exact hv
      exact h2.1
  have hirrS := B5.isIrrSec_autSec hCA hirrA (fun γ hγ => (hLA hγ).1) (fun γ hγ => (hLA hγ).2)
  have hnc := nonabelian_autSec hLA hperf (by
    obtain ⟨γ, hγ, v, hv, hγv⟩ := hnt
    exact ⟨γ, hγ, v, Subgroup.mem_sup_left hv, hγv⟩)
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [sq]; exact hW w
  exact false_of_sec_cube hW2 hLA hirrS hnc hy3 (fun w _ => hcube w) hyL hrL hr2 hry
    (hstab y hyL) (hstab r hrL)

end CFSG.Quasithin.H13.A6.A6S20
