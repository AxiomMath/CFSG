module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveModel
public import CFSG.LocalAnalysis.WeakClosure81.W16QDOff
public import CFSG.LocalAnalysis.WeakClosure81.W16QDQT
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveFaith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

private theorem w16q_map_fusionOddCore_le (X : Type) [Group X] (σ : MulAut X) :
    (fusionOddCore X).map σ.toMonoidHom ≤ fusionOddCore X := by
  rw [Subgroup.map_le_iff_le_comap]
  rw [fusionOddCore]
  refine sSup_le ?_
  rintro N ⟨hN, hodd⟩
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup ⟨hN.map σ.toMonoidHom σ.surjective, by
    rw [Subgroup.card_map_of_injective σ.injective]
    exact hodd⟩

private theorem w16q_eq_one_or_eq_of_card_two {X : Type} [Group X] {Y : Subgroup X}
    (hY : Nat.card Y = 2) {v y : X} (hv : v ∈ Y) (hv1 : v ≠ 1) (hy : y ∈ Y) :
    y = 1 ∨ y = v := by
  obtain ⟨y₀, -, hy₀uniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).1 hY
  have hv_eq : (⟨v, hv⟩ : Y) = y₀ := hy₀uniq _ (fun h => hv1 (congrArg Subtype.val h))
  rcases eq_or_ne y 1 with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have hy_eq : (⟨y, hy⟩ : Y) = y₀ := hy₀uniq _ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (hy_eq.trans hv_eq.symm)

theorem comm_mem_iSub16_of_mem_oddCoreCenter [Finite X] (d : DichCfg M V₀ V U S H φ) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p)
    (hfp : ∀ z : ↥(conjClosure V H), φ z ∈ oddCoreCenter X → φ z ≠ 1 →
      conjClosure V₀ H ⊓ centralizer ({(z : G)} : Set G) = ⊥)
    {t : G} (ht : t ∈ tSub16 V₀ S) {k : ↥(conjClosure V H)} (hk : φ k ∈ oddCoreCenter X) :
    t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ iSub16 V H := by
  have hHnormI : H ≤ Subgroup.normalizer (iSub16 V H : Set G) := by
    simpa only [iSub16] using le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hTK : tSub16 V₀ S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hS : t ∈ S := (inf_le_left : tSub16 V₀ S ≤ S) ht
  have htH : t ∈ H := d.cfg.min.fam16.1 hS
  by_cases hk1 : φ k = 1
  · have hkI : (k : G) ∈ iSub16 V H := (d.bar.ker_iff k).1 hk1
    have htkI : t * (k : G) * t⁻¹ ∈ iSub16 V H :=
      (Subgroup.mem_normalizer_iff.mp (hHnormI htH) (k : G)).1 hkI
    exact (iSub16 V H).mul_mem htkI ((iSub16 V H).inv_mem hkI)
  · have hYcard : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := h.card_Y
    have hYne : SevenK.barSub (conjClosure V H) φ V ≠ ⊥ := by
      intro hbot
      have h1 := hYcard
      rw [hbot, Subgroup.card_bot] at h1
      norm_num at h1
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
    have hvY : (v : X) ∈ SevenK.barSub (conjClosure V H) φ V := v.2
    have hvX1 : (v : X) ≠ 1 := fun hh => hv1 (Subtype.ext hh)
    obtain ⟨-, hvcent⟩ := h.inv_center hvY hvX1
    have hcent : φ k ∈ Subgroup.centralizer
        ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases w16q_eq_one_or_eq_of_card_two hYcard hvY hvX1 hy with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hvcent (φ k) hk
    have hnorm : φ k ∈ Subgroup.normalizer
        ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) :=
      Subgroup.centralizer_le_normalizer _ hcent
    have hkM : (k : G) ∈ M := d.mem_M_of_map_mem_normalizer hnorm
    obtain ⟨ρ, hρ⟩ := d.exists_actAut
    let α : MulAut X := ρ ⟨t, ht⟩
    have hNmap_le : (fusionOddCore X).map α.toMonoidHom ≤ fusionOddCore X :=
      w16q_map_fusionOddCore_le X α
    have hcardN : Nat.card ↥((fusionOddCore X).map α.toMonoidHom) =
        Nat.card ↥(fusionOddCore X) :=
      Subgroup.card_map_of_injective α.injective
    have hNmap : (fusionOddCore X).map α.toMonoidHom = fusionOddCore X :=
      le_antisymm hNmap_le
        (Subgroup.eq_of_le_of_card_ge hNmap_le (le_of_eq hcardN.symm)).ge
    have hαN : ∀ n ∈ fusionOddCore X, α n ∈ fusionOddCore X :=
      fun n hn => hNmap_le (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
    have hαinvN : ∀ n ∈ fusionOddCore X, α.symm n ∈ fusionOddCore X := by
      intro n hn
      have hmem : n ∈ (fusionOddCore X).map α.toMonoidHom := hNmap.symm ▸ hn
      obtain ⟨m, hm, hm_eq⟩ := Subgroup.mem_map.mp hmem
      rw [← hm_eq]
      simpa using hm
    let β : ↥(fusionOddCore X) ≃* ↥(fusionOddCore X) :=
      { toFun := fun n => ⟨α (n : X), hαN n n.2⟩
        invFun := fun n => ⟨α.symm (n : X), hαinvN n n.2⟩
        left_inv := fun n => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    have hβcenter : ∀ w ∈ Subgroup.center ↥(fusionOddCore X),
        (⟨α (w : X), hαN w w.2⟩ : ↥(fusionOddCore X)) ∈
          Subgroup.center ↥(fusionOddCore X) := by
      intro w hw
      have hmap := Subgroup.map_center_eq β
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨w, hw, Subtype.ext rfl⟩
    have hαZ : α (φ k) ∈ oddCoreCenter X := by
      obtain ⟨w, hw, hwφ⟩ := Subgroup.mem_map.mp hk
      refine Subgroup.mem_map.mpr ⟨⟨α (w : X), hαN w w.2⟩, hβcenter w hw, ?_⟩
      exact congrArg α hwφ
    have hZcard : Nat.card (oddCoreCenter X) = p := by
      rw [oddCoreCenter, Subgroup.card_map_of_injective (fusionOddCore X).subtype_injective]
      exact h.ext.center_order_p
    have hord : orderOf (φ k) = p := by
      have hdvd : orderOf (φ k) ∣ p := by
        rw [← hZcard]
        exact Subgroup.orderOf_dvd_natCard (oddCoreCenter X) hk
      rcases h.prime.eq_one_or_self_of_dvd _ hdvd with h1 | hp
      · exact absurd h1 (fun hh => hk1 (orderOf_eq_one_iff.mp hh))
      · exact hp
    have hZgen : oddCoreCenter X = Subgroup.zpowers (φ k) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk)
        (by rw [Nat.card_zpowers, hord, hZcard])).symm
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hZgen ▸ hαZ)
    let k' : ↥(conjClosure V H) :=
      ⟨t * (k : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK ht) (k : G)).1 k.2⟩
    have hk'_eq : φ k' = (φ k) ^ m := by
      rw [hm]
      exact (hρ ⟨t, ht⟩ k k' rfl).symm
    have hker : φ (k' * (k ^ m)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk'_eq, hm]
      exact mul_inv_cancel _
    have hi : t * (k : G) * t⁻¹ * ((k : G) ^ m)⁻¹ ∈ iSub16 V H := by
      have hmem := (d.bar.ker_iff (k' * (k ^ m)⁻¹)).1 hker
      simpa only [k', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using hmem
    let i : G := t * (k : G) * t⁻¹ * ((k : G) ^ m)⁻¹
    have hiI : i ∈ iSub16 V H := hi
    have hdecomp : t * (k : G) * t⁻¹ = i * (k : G) ^ m := by
      show t * (k : G) * t⁻¹ = (t * (k : G) * t⁻¹ * ((k : G) ^ m)⁻¹) * (k : G) ^ m
      group
    have hzMnorm : (k : G) ∈ Subgroup.normalizer (V₀ : Set G) := by
      rw [d.cfg.cex.hyp.normalizer₀]
      exact hkM
    have htconj : ∀ u ∈ V₀, t * u * t⁻¹ = u := by
      intro u hu
      have h1 : u * t = t * u := Subgroup.mem_centralizer_iff.mp ht.2 u hu
      rw [← h1]
      group
    have hIab : IsElemAbelian 2 (iSub16 V H) :=
      Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
    have hkey : ∀ w ∈ V₀, (k : G) ^ m * w * ((k : G) ^ m)⁻¹ =
        (k : G) * w * (k : G)⁻¹ := by
      intro w hw
      have hzwV : (k : G) * w * (k : G)⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.mp hzMnorm w).1 hw
      have hxV : (k : G) ^ m * w * ((k : G) ^ m)⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (V₀ : Set G)).zpow_mem hzMnorm m) w).1 hw
      have hxI : (k : G) ^ m * w * ((k : G) ^ m)⁻¹ ∈ iSub16 V H :=
        d.cfg.le_iSub16 (Subgroup.mem_sup_right hxV)
      have hL1 : (t * (k : G) * t⁻¹) * w * (t * (k : G) * t⁻¹)⁻¹ =
          (k : G) ^ m * w * ((k : G) ^ m)⁻¹ := by
        rw [hdecomp]
        calc (i * (k : G) ^ m) * w * (i * (k : G) ^ m)⁻¹
            = i * ((k : G) ^ m * w * ((k : G) ^ m)⁻¹) * i⁻¹ := by group
          _ = (k : G) ^ m * w * ((k : G) ^ m)⁻¹ := by
              rw [B2F.isElemAbelian_comm hIab hiI hxI]
              group
      have hL2 : (t * (k : G) * t⁻¹) * w * (t * (k : G) * t⁻¹)⁻¹ =
          (k : G) * w * (k : G)⁻¹ := by
        have htinv : t⁻¹ * w * t = w := by
          have h := congrArg (fun u => t⁻¹ * u * t) (htconj w hw)
          simpa [mul_assoc] using h.symm
        calc (t * (k : G) * t⁻¹) * w * (t * (k : G) * t⁻¹)⁻¹
            = t * (k : G) * (t⁻¹ * w * t) * (k : G)⁻¹ * t⁻¹ := by group
          _ = t * (k : G) * w * (k : G)⁻¹ * t⁻¹ := by rw [htinv]
          _ = (k : G) * w * (k : G)⁻¹ := by
              rw [show t * (k : G) * w * (k : G)⁻¹ * t⁻¹ =
                t * ((k : G) * w * (k : G)⁻¹) * t⁻¹ from by group]
              exact htconj ((k : G) * w * (k : G)⁻¹) hzwV
      exact hL1.symm.trans hL2
    have hyconj : ∀ w ∈ V₀, ((k : G) ^ m * (k : G)⁻¹) * w *
        ((k : G) ^ m * (k : G)⁻¹)⁻¹ = w := by
      intro w hw
      have hw' : (k : G)⁻¹ * w * (k : G) ∈ V₀ := by
        have h := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (V₀ : Set G)).inv_mem hzMnorm) w).1 hw
        simpa using h
      calc ((k : G) ^ m * (k : G)⁻¹) * w * ((k : G) ^ m * (k : G)⁻¹)⁻¹
          = (k : G) ^ m * ((k : G)⁻¹ * w * (k : G)) * ((k : G) ^ m)⁻¹ := by group
        _ = (k : G) * ((k : G)⁻¹ * w * (k : G)) * (k : G)⁻¹ := hkey _ hw'
        _ = w := by group
    have hcent_y : ((k : G) ^ m * (k : G)⁻¹) ∈ Subgroup.centralizer (V₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun u => u * ((k : G) ^ m * (k : G)⁻¹)) (hyconj w hw)
      have h : ((k : G) ^ m * (k : G)⁻¹) * w = w * ((k : G) ^ m * (k : G)⁻¹) := by
        simpa [mul_assoc] using h2
      exact h.symm
    let yK : ↥(conjClosure V H) := k ^ m * k⁻¹
    have hyKval : (yK : G) = (k : G) ^ m * (k : G)⁻¹ := by
      simp only [yK, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    have hφyK : φ yK = (φ k) ^ m * (φ k)⁻¹ := by
      simp only [yK]
      rw [map_mul, map_zpow, map_inv]
    have hφyKZ : φ yK ∈ oddCoreCenter X := by
      rw [hφyK]
      exact (oddCoreCenter X).mul_mem ((oddCoreCenter X).zpow_mem hk m)
        ((oddCoreCenter X).inv_mem hk)
    have hφyK1 : φ yK = 1 := by
      by_contra hne
      have hbot := hfp yK hφyKZ hne
      have hV₀cent : V₀ ≤ Subgroup.centralizer ({(yK : G)} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm := Subgroup.mem_centralizer_iff.mp hcent_y w hw
        rw [hyKval]
        exact hcomm
      have hle : V₀ ≤ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact le_inf (le_conjClosure V₀ H) hV₀cent
      exact d.cfg.cex.hyp.ne_bot (le_bot_iff.mp hle)
    have hpow_eq : (φ k) ^ m = φ k := by
      have h1 := hφyK1
      rw [hφyK] at h1
      exact mul_inv_eq_one.mp h1
    have hφk'_eq : φ k' = φ k := by
      rw [hk'_eq, hpow_eq]
    have hker2 : φ (k' * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hφk'_eq, mul_inv_cancel]
    have hmem2 := (d.bar.ker_iff (k' * k⁻¹)).1 hker2
    simpa only [k', Subgroup.coe_mul, Subgroup.coe_inv] using hmem2

theorem card_le_two_mul_of_heis [Finite X] (d : DichCfg M V₀ V U S H φ) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p)
    (hfix : ∀ t ∈ tSub16 V₀ S, ∀ k : ↥(conjClosure V H), φ k ∈ oddCoreCenter X →
      t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ iSub16 V H)
    {A : Subgroup G} (hAT : A ≤ tSub16 V₀ S) (hA2 : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ qSub16 V₀ V S H) := by
  obtain ⟨E, hE2, hEc, hEact, hEcard⟩ := d.exists_subgroup_aut hAT hA2
  have hTK : tSub16 V₀ S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hEZ : ∀ α ∈ E, ∀ z ∈ oddCoreCenter X, α z = z := by
    intro α hα z hz
    obtain ⟨a, ha, hact⟩ := hEact α hα
    obtain ⟨k, rfl⟩ := d.bar.surjective z
    have haT : a ∈ tSub16 V₀ S := hAT ha
    have haK : a ∈ Subgroup.normalizer (conjClosure V H : Set G) := hTK haT
    let k' : ↥(conjClosure V H) :=
      ⟨a * (k : G) * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK (k : G)).1 k.2⟩
    have hk' : (k' : G) = a * (k : G) * a⁻¹ := rfl
    have hαz : α (φ k) = φ k' := hact k k' hk'
    have hφk' : φ k' = φ k := by
      have hker : φ (k' * k⁻¹) = 1 := by
        apply (d.bar.ker_iff _).2
        simpa only [k', Subgroup.coe_mul, Subgroup.coe_inv] using hfix a haT k hz
      have h1 := hker
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [hαz, hφk']
  have hcardE : Nat.card E ≤ 2 := h.card_le_two E hE2 hEc hEZ
  calc Nat.card A = Nat.card E * Nat.card ↥(A ⊓ qSub16 V₀ V S H) := hEcard.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ qSub16 V₀ V S H) := Nat.mul_le_mul_right _ hcardE

theorem two_le_of_fixedPointFree [Finite X] (d : DichCfg M V₀ V U S H φ) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p) {k : ℕ}
    (hI₀ : Nat.card ↥(conjClosure V₀ H) = 2 ^ (p * k))
    (hfp : ∀ z : ↥(conjClosure V H), φ z ∈ oddCoreCenter X → φ z ≠ 1 →
      conjClosure V₀ H ⊓ centralizer ({(z : G)} : Set G) = ⊥) : 2 ≤ k := by
  have hHnormI : H ≤ Subgroup.normalizer (iSub16 V H : Set G) := by
    simpa only [iSub16] using le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hI₀_le_I : conjClosure V₀ H ≤ iSub16 V H :=
    conjClosure_le fun hh hhh v hv =>
      (Subgroup.mem_normalizer_iff.mp (hHnormI hhh) v).1
        (d.cfg.le_iSub16 (Subgroup.mem_sup_right hv))
  have hIab : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hZcard : Nat.card (oddCoreCenter X) = p := by
    rw [oddCoreCenter, Subgroup.card_map_of_injective (fusionOddCore X).subtype_injective]
    exact h.ext.center_order_p
  have hZne : oddCoreCenter X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (oddCoreCenter X) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hZcard] at h1
    exact h.prime.ne_one h1
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  obtain ⟨k₀, hk₀⟩ := d.bar.surjective (z₀ : X)
  have hφk₀Z : φ k₀ ∈ oddCoreCenter X := by rw [hk₀]; exact z₀.2
  have hφk₀1 : φ k₀ ≠ 1 := by rw [hk₀]; exact fun hh => hz₀1 (Subtype.ext hh)
  have hord : orderOf (φ k₀) = p := by
    have hdvd : orderOf (φ k₀) ∣ p := by
      rw [← hZcard]
      exact Subgroup.orderOf_dvd_natCard (oddCoreCenter X) hφk₀Z
    rcases h.prime.eq_one_or_self_of_dvd _ hdvd with h1 | hp
    · exact absurd h1 (fun hh => hφk₀1 (orderOf_eq_one_iff.mp hh))
    · exact hp
  have hφk₀p : φ (k₀ ^ p) = 1 := by
    rw [map_pow, ← hord, pow_orderOf_eq_one]
  have hzpI : (k₀ : G) ^ p ∈ iSub16 V H := by
    have h1 := (d.bar.ker_iff (k₀ ^ p)).1 hφk₀p
    simpa using h1
  have hk₀H : (k₀ : G) ∈ H := d.cfg.conjClosure_le_H k₀.2
  have hk₀Norm : (k₀ : G) ∈ Subgroup.normalizer (conjClosure V₀ H : Set G) :=
    le_normalizer_conjClosure V₀ H hk₀H
  let g : ↥(Subgroup.normalizer (conjClosure V₀ H : Set G)) := ⟨(k₀ : G), hk₀Norm⟩
  let σ : MulAut ↥(conjClosure V₀ H) := Subgroup.normalizerMonoidHom (conjClosure V₀ H) g
  have hσ_apply : ∀ i : ↥(conjClosure V₀ H),
      ((σ i : ↥(conjClosure V₀ H)) : G) = (k₀ : G) * (i : G) * (k₀ : G)⁻¹ :=
    fun i => Subgroup.normalizerMonoidHom_apply_apply_coe (conjClosure V₀ H) g i
  have hσp : σ ^ p = 1 := by
    rw [show σ = Subgroup.normalizerMonoidHom (conjClosure V₀ H) g from rfl, ← map_pow]
    ext i
    rw [MulAut.one_apply]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hgp : ((g ^ p : ↥(Subgroup.normalizer (conjClosure V₀ H : Set G))) : G) =
        (k₀ : G) ^ p := by
      rw [Subgroup.coe_pow]
    rw [hgp]
    have hiI : (i : G) ∈ iSub16 V H := hI₀_le_I i.2
    rw [B2F.isElemAbelian_comm hIab hzpI hiI, mul_inv_cancel_right]
  have hfixeq : ∀ a : {x : ↥(conjClosure V₀ H) // σ x = x}, (a.1 : G) = 1 := by
    intro a
    by_contra hne
    have hcomm : (a.1 : G) ∈ Subgroup.centralizer ({(k₀ : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ((σ a.1 : ↥(conjClosure V₀ H)) : G) = (a.1 : G) := congrArg Subtype.val a.2
      rw [hσ_apply a.1] at h1
      have h2 := congrArg (fun u => u * (k₀ : G)) h1
      simpa [mul_assoc] using h2.symm
    have hmem : (a.1 : G) ∈ conjClosure V₀ H ⊓ Subgroup.centralizer ({(k₀ : G)} : Set G) :=
      ⟨a.1.2, hcomm⟩
    rw [hfp k₀ hφk₀Z hφk₀1] at hmem
    exact hne (Subgroup.mem_bot.mp hmem)
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hmod :=
    CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime σ hσp
  have hfixcard : Nat.card {x : ↥(conjClosure V₀ H) // σ x = x} = 1 :=
    Nat.card_eq_one_iff_exists.mpr
      ⟨⟨1, map_one σ⟩, fun y => Subtype.ext (Subtype.ext (hfixeq y))⟩
  have hk0 : k ≠ 0 := by
    intro hk0
    have h1 : Nat.card ↥(conjClosure V₀ H) = 1 := by rw [hI₀, hk0, mul_zero, pow_zero]
    have hbot : conjClosure V₀ H = ⊥ := Subgroup.eq_bot_of_card_eq (conjClosure V₀ H) h1
    exact d.cfg.cex.hyp.ne_bot (le_bot_iff.mp ((le_conjClosure V₀ H).trans (le_of_eq hbot)))
  have hmod2 : 2 ^ (p * k) ≡ 1 [MOD p] := by
    have hh := hmod
    rw [hfixcard] at hh
    rw [hI₀] at hh
    exact hh
  exact w16q_two_le_of_pow_modEq_one h.prime hk0 hmod2

section Certified


theorem le_qSub16_of_heis [Finite X] (d : DichCfg M V₀ V U S H φ)
    (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p) :
    ∀ A ∈ elemFamilyIn 2 (tSub16 V₀ S), A ≤ qSub16 V₀ V S H := by
  intro A hA
  by_contra hAQ
  obtain ⟨k, hk1, hk2, hfp⟩ := d.exists_card_of_heis h h.exponent_eq
    (d.inf_centralizer_iSub16_le h)
  have hk : 2 ≤ k := d.two_le_of_fixedPointFree h hk1 hfp
  have hfix : ∀ t ∈ tSub16 V₀ S, ∀ k : ↥(conjClosure V H), φ k ∈ oddCoreCenter X →
      t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ iSub16 V H := fun t ht k hk =>
    d.comm_mem_iSub16_of_mem_oddCoreCenter h hfp ht hk
  have hNN := fun α hα hN => eq_one_of_forall_normalizes_of_card_two h.card_Y h.gen α hα hN
  obtain ⟨hAT, hAe, -⟩ := mem_elemFamilyIn.1 hA
  have hA2 : IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAe
  have h1 := d.card_mul_le_of_not_le hQT hNN hA hAQ
  have h2 := d.card_le_two_mul_of_heis h hfix hAT hA2
  have hp3 : 3 ≤ p := by
    have := h.prime.two_le
    have := h.ne_two
    omega
  have h4 : 4 ≤ Nat.card ↥V₀ := by
    rw [hk2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ((p - 1) * k / 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have : 4 ≤ (p - 1) * k := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
        omega
  have hpos : 0 < Nat.card ↥(A ⊓ qSub16 V₀ V S H) := Nat.card_pos
  nlinarith

end Certified

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end

