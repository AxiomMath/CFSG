module

public import CFSG.LocalAnalysis.WeakClosure81.W16QExcL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Gen1616

variable {M V₀ V U S H : Subgroup G} {k : G}

theorem conjSubgroup_le_iSub16 (g : Gen1616 M V₀ V U S H k) :
    conjSubgroup V₀ k ≤ iSub16 V H := by
  intro x hx
  have hxV : k * x * k⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hx
  have hkH : k ∈ H := g.cfg.conjClosure_le_H g.mem
  have hI : k * x * k⁻¹ ∈ iSub16 V H := g.cfg.le_iSub16 (Subgroup.mem_sup_right hxV)
  have hnorm : k⁻¹ ∈ normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H (H.inv_mem hkH)
  have h := (Subgroup.mem_normalizer_iff.1 hnorm (k * x * k⁻¹)).1 hI
  rwa [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x by group] at h

theorem le_normalizer_sup_conj (g : Gen1616 M V₀ V U S H k) :
    conjClosure V H ≤ normalizer ((V₀ ⊔ conjSubgroup V₀ k : Subgroup G) : Set G) := by
  have c := g.cfg
  have hIab := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hWI : conjSubgroup V₀ k ≤ iSub16 V H := conjSubgroup_le_iSub16 g
  have hXI : (V₀ ⊔ conjSubgroup V₀ k : Subgroup G) ≤ iSub16 V H :=
    sup_le (le_sup_right.trans c.le_iSub16) hWI
  have hI : iSub16 V H ≤ normalizer ((V₀ ⊔ conjSubgroup V₀ k : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hIab.1).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXI)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hV : V ≤ normalizer ((V₀ ⊔ conjSubgroup V₀ k : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun v hv x hx => ?_
    have hxI : x ∈ iSub16 V H := hXI hx
    have hxS : x ∈ S := Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16
      (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16 hxI)
    have hcomm : v * x * v⁻¹ * x⁻¹ ∈ V₀ := by
      have h := V₀.inv_mem (c.cex.comm_mem_V₀ hxS hv)
      rwa [show (x * v * x⁻¹ * v⁻¹)⁻¹ = v * x * v⁻¹ * x⁻¹ by group] at h
    rw [show v * x * v⁻¹ = (v * x * v⁻¹ * x⁻¹) * x by group]
    exact (V₀ ⊔ conjSubgroup V₀ k).mul_mem (Subgroup.mem_sup_left hcomm) hx
  have hVk : conjSubgroup V k ≤
      normalizer ((V₀ ⊔ conjSubgroup V₀ k : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun u hu x hx => ?_
    have hu' : k * u * k⁻¹ ∈ V := mem_conjSubgroup_iff.1 hu
    have hnormI : k ∈ normalizer (iSub16 V H : Set G) :=
      le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H (c.conjClosure_le_H g.mem)
    have key : (V₀ ⊔ conjSubgroup V₀ k : Subgroup G) ≤
        (V₀ ⊔ conjSubgroup V₀ k : Subgroup G).comap (MulAut.conj u).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro w hw
        refine Subgroup.mem_comap.2 ?_
        show u * w * u⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ k
        have hwI : w ∈ iSub16 V H := c.le_iSub16 (Subgroup.mem_sup_right hw)
        have hkw : k * w * k⁻¹ ∈ iSub16 V H :=
          (Subgroup.mem_normalizer_iff.1 hnormI w).1 hwI
        have hkwS : k * w * k⁻¹ ∈ S := Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16
          (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16 hkw)
        let cc : G := (k * u * k⁻¹) * (k * w * k⁻¹) * (k * u * k⁻¹)⁻¹ *
          (k * w * k⁻¹)⁻¹
        have hcv : cc ∈ V₀ := by
          dsimp only [cc]
          have h := V₀.inv_mem (c.cex.comm_mem_V₀ hkwS hu')
          rwa [show ((k * w * k⁻¹) * (k * u * k⁻¹) * (k * w * k⁻¹)⁻¹ *
              (k * u * k⁻¹)⁻¹)⁻¹ =
            (k * u * k⁻¹) * (k * w * k⁻¹) * (k * u * k⁻¹)⁻¹ * (k * w * k⁻¹)⁻¹
            by group] at h
        have hmemW : k⁻¹ * cc * k ∈ conjSubgroup V₀ k := by
          rw [mem_conjSubgroup_iff]
          show k * (k⁻¹ * cc * k) * k⁻¹ ∈ V₀
          rwa [show k * (k⁻¹ * cc * k) * k⁻¹ = cc by group]
        have hmain : u * w * u⁻¹ = (k⁻¹ * cc * k) * w := by
          have hu_eq : u = k⁻¹ * (k * u * k⁻¹) * k := by group
          have hw_eq : w = k⁻¹ * (k * w * k⁻¹) * k := by group
          rw [hu_eq, hw_eq]
          dsimp only [cc]
          group
        rw [hmain]
        exact (V₀ ⊔ conjSubgroup V₀ k).mul_mem (Subgroup.mem_sup_right hmemW)
          (Subgroup.mem_sup_left hw)
      · intro w hw
        refine Subgroup.mem_comap.2 ?_
        show u * w * u⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ k
        have hw₀ : k * w * k⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hw
        have huw : u * w * u⁻¹ = w := by
          have hu_eq : u = k⁻¹ * (k * u * k⁻¹) * k := by group
          have hw_eq : w = k⁻¹ * (k * w * k⁻¹) * k := by group
          have hcomm := B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hu'
            (c.cex.hyp.h6.le hw₀)
          calc u * w * u⁻¹
              = k⁻¹ * ((k * u * k⁻¹) * (k * w * k⁻¹) * (k * u * k⁻¹)⁻¹) * k := by
                conv_lhs => rw [hu_eq]
                group
            _ = k⁻¹ * (k * w * k⁻¹) * k := by rw [hcomm]; group
            _ = w := by rw [← hw_eq]
        rw [huw]
        exact Subgroup.mem_sup_right hw
    have h := Subgroup.mem_comap.1 (key hx)
    simpa [MulAut.conj_apply] using h
  exact g.gen.trans (sup_le (sup_le hV hVk) hI)

theorem iSub16_le_sup (g : Gen1616 M V₀ V U S H k) :
    iSub16 V H ≤ U ⊔ V₀ ⊔ conjSubgroup V₀ k := by
  have c := g.cfg
  have hSK : S ≤ normalizer (conjClosure V H : Set G) :=
    c.min.fam16.1.trans (le_normalizer_conjClosure V H)
  have hKS : (↑H : Set G) = (conjClosure V H : Set G) * (S : Set G) := by
    conv_lhs => rw [← c.sup_eq]
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure V H) S hSK
  rw [c.iSub16_eq]
  refine conjClosure_le fun h hh z hz => ?_
  have hh' : h ∈ ((conjClosure V H : Set G) * (S : Set G)) := by
    rw [← hKS]
    exact hh
  obtain ⟨k', hk', s, hs, rfl⟩ := Set.mem_mul.1 hh'
  obtain ⟨u, hu, w, hw, rfl⟩ := c.cex.exists_mul_of_mem_sup hz
  have hsN : s ∈ normalizer (V₀ : Set G) := c.cex.hyp.h6.le_normalizer₀ (c.cex.S_le_M hs)
  have hsu : s * u * s⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 (c.cex.S_le_centralizer hs) u hu).symm
  have hsw : s * w * s⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hsN w).1 hw
  have hk'u : k' * u * k'⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 (c.conjClosure_le_centralizer hk') u hu).symm
  have hk'w : k' * (s * w * s⁻¹) * k'⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ k :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_sup_conj g hk') (s * w * s⁻¹)).1
      (Subgroup.mem_sup_left hsw)
  rw [show (k' * s) * (u * w) * (k' * s)⁻¹ = u * (k' * (s * w * s⁻¹) * k'⁻¹) by
    calc (k' * s) * (u * w) * (k' * s)⁻¹
        = k' * ((s * u * s⁻¹) * (s * w * s⁻¹)) * k'⁻¹ := by group
      _ = k' * (u * (s * w * s⁻¹)) * k'⁻¹ := by rw [hsu]
      _ = (k' * u * k'⁻¹) * (k' * (s * w * s⁻¹) * k'⁻¹) := by group
      _ = u * (k' * (s * w * s⁻¹) * k'⁻¹) := by rw [hk'u]]
  rw [sup_assoc]
  exact (U ⊔ (V₀ ⊔ conjSubgroup V₀ k)).mul_mem (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right hk'w)

theorem eq_one_of_mem_conjSubgroup (g : Gen1616 M V₀ V U S H k) {b v : G}
    (hb : b ∈ conjSubgroup V₀ k) (hv : v ∈ V) (hvZ : v ∉ U ⊔ V₀) (hc : v * b = b * v) :
    b = 1 := by
  by_contra hb1
  have c := g.cfg
  have hk : k ∈ centralizer (U : Set G) := c.conjClosure_le_centralizer g.mem
  have hC : conjSubgroup V₀ k ≤ F11.CTilde M V₀ V :=
    (conjSubgroup_le_iSub16 g).trans
      ((Cex16.iSub16_le_pCoreOf c.cex c.min.fam16).trans
        ((Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16).trans c.cex.S_le_cTilde))
  have hinf := Cex16.inf_centralizer_eq c.one c.five c.fifteen c.std c.cex hk g.not_mem hC hb hb1
  apply hvZ
  rw [← hinf]
  exact ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 hc⟩

theorem mem_sup_of_comm (g : Gen1616 M V₀ V U S H k) {v w : G} (hv : v ∈ V)
    (hvZ : v ∉ U ⊔ V₀) (hw : w ∈ iSub16 V H) (hc : v * w = w * v) : w ∈ U ⊔ V₀ := by
  have c := g.cfg
  have hIab := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hZI : U ⊔ V₀ ≤ iSub16 V H := c.le_iSub16
  have hWI : conjSubgroup V₀ k ≤ iSub16 V H := conjSubgroup_le_iSub16 g
  have hle : conjSubgroup V₀ k ≤ normalizer ((U ⊔ V₀ : Subgroup G) : Set G) :=
    hWI.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hIab.1).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZI)).trans
        (Subgroup.centralizer_le_normalizer _)))
  have hZW : (↑(U ⊔ V₀ ⊔ conjSubgroup V₀ k) : Set G) =
      ((U ⊔ V₀ : Subgroup G) : Set G) * (conjSubgroup V₀ k : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (U ⊔ V₀) (conjSubgroup V₀ k) hle
  have hw' : w ∈ (↑(U ⊔ V₀ ⊔ conjSubgroup V₀ k) : Set G) := iSub16_le_sup g hw
  rw [hZW] at hw'
  obtain ⟨z, hz, b, hb, hzb⟩ := Set.mem_mul.1 hw'
  have hzV : z ∈ V := (sup_le c.cex.le c.cex.hyp.h6.le) hz
  have hzv : z * v = v * z := B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hzV hv
  have hvb : v * b = b * v := by
    apply mul_left_cancel (a := z)
    calc z * (v * b) = (z * v) * b := by group
      _ = (v * z) * b := by rw [hzv]
      _ = v * (z * b) := by group
      _ = v * w := by rw [hzb]
      _ = w * v := hc
      _ = (z * b) * v := by rw [hzb]
      _ = z * (b * v) := by group
  have hb1 : b = 1 := eq_one_of_mem_conjSubgroup g hb hv hvZ hvb
  rw [← hzb, hb1, mul_one]
  exact hz

theorem card_iSub16_eq (g : Gen1616 M V₀ V U S H k) :
    Nat.card ↥(iSub16 V H) = Nat.card ↥V := by
  have c := g.cfg
  have hIab := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hWI : conjSubgroup V₀ k ≤ iSub16 V H := conjSubgroup_le_iSub16 g
  have hZI : U ⊔ V₀ ≤ iSub16 V H := c.le_iSub16
  have hsup : iSub16 V H = U ⊔ V₀ ⊔ conjSubgroup V₀ k :=
    le_antisymm (iSub16_le_sup g) (sup_le hZI hWI)
  have hVI : V ⊓ iSub16 V H = U ⊔ V₀ :=
    Cex16.inf_iSub16_eq c.one c.five c.std c.cex c.min.fam16 c.not_le
  have hPC : V ⊓ pCoreOf 2 H = U ⊔ V₀ :=
    Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le
  have hVnZ : ¬ V ≤ U ⊔ V₀ := by
    intro hle
    exact c.not_le (hle.trans (hPC ▸ inf_le_right))
  obtain ⟨v', hv'V, hv'Z⟩ := Set.not_subset.1 hVnZ
  have hZW : (U ⊔ V₀) ⊓ conjSubgroup V₀ k = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbZ, hbW⟩ := Subgroup.mem_inf.1 hb
    have hbV : b ∈ V := (sup_le c.cex.le c.cex.hyp.h6.le) hbZ
    have hcomm : v' * b = b * v' :=
      B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hv'V hbV
    have hb1 : b = 1 := eq_one_of_mem_conjSubgroup g hbW hv'V hv'Z hcomm
    rw [hb1, Subgroup.mem_bot]
  have hcardZW : Nat.card ↥(U ⊔ V₀ ⊔ conjSubgroup V₀ k) =
      Nat.card ↥(U ⊔ V₀) * Nat.card ↥(conjSubgroup V₀ k) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (U ⊔ V₀)
      (conjSubgroup V₀ k)
      (fun x hx y hy => B2F.isElemAbelian_comm hIab (hZI hx) (hWI hy))).1
    rw [hZW, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardW : Nat.card ↥(conjSubgroup V₀ k) = Nat.card ↥V₀ := card_conjSubgroup' k V₀
  have hV₀2 : IsPGroup 2 V₀ := c.cex.hyp.isPGroup.to_le c.cex.hyp.h6.le
  have hcardV0 : Nat.card ↥V₀ = 2 ^ E3.mQuot V (iSub16 V H) := by
    rw [card_eq_two_pow_mSub hV₀2, g.rank]
  have hcardV : Nat.card ↥V = Nat.card ↥(U ⊔ V₀) * 2 ^ E3.mQuot V (iSub16 V H) := by
    have h := E3.card_eq_two_pow_mul c.cex.hyp.isPGroup (sup_le c.cex.le c.cex.hyp.h6.le)
    have hmq : E3.mQuot V (U ⊔ V₀) = E3.mQuot V (iSub16 V H) := by
      rw [← hVI]
      show padicValNat 2 ((V ⊓ iSub16 V H).relIndex V) =
        padicValNat 2 ((iSub16 V H).relIndex V)
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [hmq] at h
    rw [h, mul_comm]
  rw [hsup, hcardZW, hcardW, hcardV0, hcardV]

private theorem w16q_commutator_mul (g : Gen1616 M V₀ V U S H k) {v x y : G}
    (hv : v ∈ V) (hx : x ∈ conjSubgroup V₀ k) (hy : y ∈ conjSubgroup V₀ k) :
    ⁅v, x * y⁆ = ⁅v, x⁆ * ⁅v, y⁆ := by
  have c := g.cfg
  have hxI : x ∈ iSub16 V H := conjSubgroup_le_iSub16 g hx
  have hyI : y ∈ iSub16 V H := conjSubgroup_le_iSub16 g hy
  have hIab := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hyS : y ∈ S := Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16
    (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16 hyI)
  have hvy : ⁅v, y⁆ ∈ iSub16 V H := by
    rw [commutatorElement_def]
    refine c.le_iSub16 (Subgroup.mem_sup_right ?_)
    have h := V₀.inv_mem (c.cex.comm_mem_V₀ hyS hv)
    rwa [show (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ by group] at h
  have hcomm : x * ⁅v, y⁆ * x⁻¹ = ⁅v, y⁆ := by
    rw [B2F.isElemAbelian_comm hIab hxI hvy]
    group
  calc ⁅v, x * y⁆ = ⁅v, x⁆ * x * ⁅v, y⁆ * x⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj v x y
    _ = ⁅v, x⁆ * (x * ⁅v, y⁆ * x⁻¹) := by group
    _ = ⁅v, x⁆ * ⁅v, y⁆ := by rw [hcomm]

private theorem w16q_eq_of_commutator_eq (g : Gen1616 M V₀ V U S H k) {v : G}
    (hv : v ∈ V) (hvZ : v ∉ U ⊔ V₀) {x y : G}
    (hx : x ∈ conjSubgroup V₀ k) (hy : y ∈ conjSubgroup V₀ k)
    (h : ⁅v, x⁆ = ⁅v, y⁆) : x = y := by
  have hyi : y⁻¹ ∈ conjSubgroup V₀ k := (conjSubgroup V₀ k).inv_mem hy
  have hxy : x * y⁻¹ ∈ conjSubgroup V₀ k := (conjSubgroup V₀ k).mul_mem hx hyi
  have hmul := w16q_commutator_mul g hv hx hyi
  have hinv := w16q_commutator_mul g hv hy hyi
  have h1 : ⁅v, y * y⁻¹⁆ = (1 : G) := by simp
  rw [h1] at hinv
  have hyinv : ⁅v, y⁻¹⁆ = ⁅v, y⁆⁻¹ := eq_inv_of_mul_eq_one_right hinv.symm
  have hgoal : ⁅v, x * y⁻¹⁆ = 1 := by
    rw [hmul, h, hyinv, mul_inv_cancel]
  have hcomm : v * (x * y⁻¹) = (x * y⁻¹) * v :=
    commutatorElement_eq_one_iff_mul_comm.1 hgoal
  have hx1 : x * y⁻¹ = 1 := eq_one_of_mem_conjSubgroup g hxy hv hvZ hcomm
  exact mul_inv_eq_one.1 hx1

theorem mem_centralizer_of_mem_normalizer_conj (g : Gen1616 M V₀ V U S H k) {y : G}
    (hy : y ∈ tSub16 V₀ S)
    (hyN : y ∈ normalizer ((conjSubgroup V₀ k : Subgroup G) : Set G)) :
    y ∈ centralizer ((conjSubgroup V₀ k : Subgroup G) : Set G) := by
  have c := g.cfg
  have hIab := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hWI : conjSubgroup V₀ k ≤ iSub16 V H := conjSubgroup_le_iSub16 g
  have hZI : U ⊔ V₀ ≤ iSub16 V H := c.le_iSub16
  have hPC : V ⊓ pCoreOf 2 H = U ⊔ V₀ :=
    Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le
  have hVnZ : ¬ V ≤ U ⊔ V₀ := by
    intro hle
    exact c.not_le (hle.trans (hPC ▸ inf_le_right))
  obtain ⟨v', hv'V, hv'Z⟩ := Set.not_subset.1 hVnZ
  have hyS : y ∈ S := hy.1
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  have hw' : y * w * y⁻¹ ∈ conjSubgroup V₀ k := (Subgroup.mem_normalizer_iff.1 hyN w).1 hw
  have hwI : w ∈ iSub16 V H := hWI hw
  have hw'I : y * w * y⁻¹ ∈ iSub16 V H := hWI hw'
  have hwS : w ∈ S := Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16
    (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16 hwI)
  have hw'S : y * w * y⁻¹ ∈ S := Cex16.pCoreOf_le_S c.one c.std c.cex c.min.fam16
    (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16 hw'I)
  have hcv0 : y * v' * y⁻¹ * v'⁻¹ ∈ V₀ := c.cex.comm_mem_V₀ hyS hv'V
  have hvw : ⁅v', w⁆ ∈ V₀ := by
    rw [commutatorElement_def]
    have h := V₀.inv_mem (c.cex.comm_mem_V₀ hwS hv'V)
    rwa [show (w * v' * w⁻¹ * v'⁻¹)⁻¹ = v' * w * v'⁻¹ * w⁻¹ by group] at h
  have hvwy : ⁅v', y * w * y⁻¹⁆ ∈ V₀ := by
    rw [commutatorElement_def]
    have h := V₀.inv_mem (c.cex.comm_mem_V₀ hw'S hv'V)
    rwa [show ((y * w * y⁻¹) * v' * (y * w * y⁻¹)⁻¹ * v'⁻¹)⁻¹ =
      v' * (y * w * y⁻¹) * v'⁻¹ * (y * w * y⁻¹)⁻¹ by group] at h
  have hyc : y * ⁅v', w⁆ * y⁻¹ = ⁅v', w⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hy.2 ⁅v', w⁆ hvw).symm
  have hc'v : (y * v' * y⁻¹ * v'⁻¹) * v' = v' * (y * v' * y⁻¹ * v'⁻¹) :=
    B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.hyp.h6.le hcv0) hv'V
  have hc'w : (y * v' * y⁻¹ * v'⁻¹) * (y * w * y⁻¹) =
      (y * w * y⁻¹) * (y * v' * y⁻¹ * v'⁻¹) :=
    B2F.isElemAbelian_comm hIab (hZI (Subgroup.mem_sup_right hcv0)) hw'I
  have hcv : ⁅y * v' * y⁻¹, y * w * y⁻¹⁆ = ⁅v', y * w * y⁻¹⁆ := by
    rw [show y * v' * y⁻¹ = (y * v' * y⁻¹ * v'⁻¹) * v' by group]
    rw [commutatorElement_mul_left_eq_conj_mul,
      (commutatorElement_eq_one_iff_mul_comm.2 hc'w), mul_one]
    rw [show (y * v' * y⁻¹ * v'⁻¹) * ⁅v', y * w * y⁻¹⁆ * (y * v' * y⁻¹ * v'⁻¹)⁻¹ =
      ⁅v', y * w * y⁻¹⁆ by
        rw [B2F.isElemAbelian_comm hIab (hZI (Subgroup.mem_sup_right hcv0))
          (hZI (Subgroup.mem_sup_right hvwy))]
        group]
  have hkey : ⁅v', y * w * y⁻¹⁆ = ⁅v', w⁆ := by
    rw [← hcv, ← conjugate_commutatorElement v' w y, hyc]
  have hEq : y * w * y⁻¹ = w := w16q_eq_of_commutator_eq g hv'V hv'Z hw' hw hkey
  exact (mul_inv_eq_iff_eq_mul.1 hEq).symm

end Gen1616

end CFSG.LocalAnalysis.WeakClosure81

end
