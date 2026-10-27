module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45T

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem quaternionGroup_two_not_isMulCommutative :
    ¬ IsMulCommutative (QuaternionGroup 2) := by
  intro h
  have hc := h.is_comm.comm (QuaternionGroup.a 1 : QuaternionGroup 2)
    (QuaternionGroup.xa 0 : QuaternionGroup 2)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hc
  exact absurd (QuaternionGroup.xa.inj hc) (by decide)

theorem uc45_T_le_ZX_of_le_wker (c : Pre45 p G D) (hle : D ≤ Wker G) :
    Tof G D ≤ ZXof G := by
  show ⁅Xof G, D⁆ ≤ ZXof G
  refine Subgroup.commutator_le.mpr fun x hx d hd => ?_
  have hdmem : ⁅d, x⁆ ∈ ZXof G := (mem_wker.mp (hle hd)) x hx
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ hdmem

theorem uc45_D_inf_wker (c : Pre45 p G D) : D ⊓ Wker G = ⊥ := by
  have hdvd : Nat.card ↥(D ⊓ Wker G) ∣ 3 := by
    rw [← c.card_three]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq (D ⊓ Wker G) h1
  · exfalso
    have hEq : D ⊓ Wker G = D :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [c.card_three, h3])
    have hle : D ≤ Wker G := hEq ▸ inf_le_right
    have hTZ : Tof G D ≤ ZXof G := uc45_T_le_ZX_of_le_wker c hle
    have hcommT : IsMulCommutative ↥(Tof G D) :=
      IsMulCommutative.of_comm fun a b => by
        apply Subtype.ext
        simpa using (Subgroup.mem_center_iff.mp (c.ZX_le (hTZ a.2)) (b : G)).symm
    obtain ⟨eQ⟩ := c.Q8
    refine quaternionGroup_two_not_isMulCommutative ?_
    refine IsMulCommutative.of_comm fun u v => ?_
    have h := hcommT.is_comm.comm (eQ.symm u) (eQ.symm v)
    have h2 := congrArg (fun t : ↥(Tof G D) => eQ t) h
    simpa using h2

theorem uc45_T_inf_ZX_eq_center (c : Pre45 p G D) :
    Tof G D ⊓ ZXof G = (Subgroup.center ↥(Tof G D)).map (Tof G D).subtype := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzT, hzZ⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hzT⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (c.ZX_le hzZ) (y : G)
  · intro z hz
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.map_subtype_le _ hz, uc45_ZT_le_ZX c.toBase45 c.class_two.1 c.ZX_le hz⟩

theorem uc45_card_center_T (c : Pre45 p G D) :
    Nat.card ↥(Subgroup.center ↥(Tof G D)) = 2 := by
  obtain ⟨eQ⟩ := c.Q8
  have hmap : (Subgroup.center ↥(Tof G D)).map eQ.toMonoidHom =
      Subgroup.center (QuaternionGroup 2) := Subgroup.map_center_eq eQ
  have h := Subgroup.card_map_of_injective (K := Subgroup.center ↥(Tof G D))
    (f := eQ.toMonoidHom) eQ.injective
  rw [hmap] at h
  rw [← h, Nat.card_eq_fintype_card]
  decide

theorem uc45_card_TZ (c : Pre45 p G D) :
    Nat.card ↥(Tof G D ⊔ ZXof G) = 4 * Nat.card ↥(ZXof G) := by
  obtain ⟨eQ⟩ := c.Q8
  have hcardT : Nat.card ↥(Tof G D) = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardZT : Nat.card ↥(Subgroup.center ↥(Tof G D)) = 2 := uc45_card_center_T c
  have hcard_inf : Nat.card ↥(Tof G D ⊓ ZXof G) = 2 := by
    rw [uc45_T_inf_ZX_eq_center c,
      Subgroup.card_map_of_injective (Tof G D).subtype_injective, hcardZT]
  have h1 : (Tof G D).relIndex (Tof G D ⊔ ZXof G) * Nat.card ↥(Tof G D) =
      Nat.card ↥(Tof G D ⊔ ZXof G) := by
    rw [← Subgroup.relIndex_mul_card (Tof G D) (Tof G D ⊔ ZXof G),
      inf_eq_left.mpr le_sup_left]
  have h2 : (Tof G D).relIndex (Tof G D ⊔ ZXof G) = (Tof G D).relIndex (ZXof G) := by
    rw [sup_comm]
    exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (ZXof G) (Tof G D)
  have h3 : (Tof G D).relIndex (ZXof G) * Nat.card ↥(Tof G D ⊓ ZXof G) =
      Nat.card ↥(ZXof G) := Subgroup.relIndex_mul_card (Tof G D) (ZXof G)
  rw [hcardT] at h1
  rw [hcard_inf] at h3
  rw [h2] at h1
  rw [← h1, ← h3]
  ring

theorem uc45_card_D_map (c : Pre45 p G D) :
    Nat.card ↥(D.map (QuotientGroup.mk' (Wker G))) = 3 := by
  let f : G →* G ⧸ Wker G := QuotientGroup.mk' (Wker G)
  have hdvd : Nat.card ↥(D.map f) ∣ 3 := by
    rw [← c.card_three]
    exact Subgroup.card_map_dvd D f
  rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exfalso
    have hbot : D.map f = ⊥ := Subgroup.eq_bot_of_card_eq (D.map f) h1
    have hDle : D ≤ Wker G := by
      intro d hd
      have hd1 : f d = 1 := by
        have hmem : f d ∈ (⊥ : Subgroup (G ⧸ Wker G)) :=
          hbot ▸ Subgroup.mem_map_of_mem f hd
        simpa using hmem
      have hker : d ∈ f.ker := MonoidHom.mem_ker.mpr hd1
      rwa [QuotientGroup.ker_mk'] at hker
    have hDlebot : D ≤ (⊥ : Subgroup G) := by
      rw [← uc45_D_inf_wker c]
      exact le_inf le_rfl hDle
    have hDbot : D = ⊥ := le_bot_iff.mp hDlebot
    have hc3 : Nat.card ↥D = 3 := c.card_three
    rw [hDbot, Subgroup.card_bot] at hc3
    exact (by decide : (1 : ℕ) ≠ 3) hc3
  · exact h3

theorem uc45_map_conj_zpowers (d g : G) :
    (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * d * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem uc45_center_Xof_isCyclic (c : Pre45 p G D) :
    IsCyclic ↥(Subgroup.center ↥(Xof G)) := by
  have hcycZX : IsCyclic ↥(ZXof G) := by
    haveI : IsCyclic ↥(Subgroup.center G) := c.center_cyclic
    exact Subgroup.isCyclic_of_le c.ZX_le
  exact ((Subgroup.equivMapOfInjective (Subgroup.center ↥(Xof G)) (Xof G).subtype
    (Xof G).subtype_injective).isCyclic).mpr hcycZX

theorem uc45_orderOf_mk_of_zpowers (c : Pre45 p G D) {d : G}
    (hd : Subgroup.zpowers d = D) :
    orderOf (QuotientGroup.mk d : G ⧸ Wker G) = 3 := by
  have hdmap : D.map (QuotientGroup.mk' (Wker G)) =
      Subgroup.zpowers (QuotientGroup.mk d : G ⧸ Wker G) := by
    rw [← hd, MonoidHom.map_zpowers]
    rfl
  rw [← Nat.card_zpowers, ← hdmap, uc45_card_D_map c]

theorem uc45_orderOf_mk_conj {x : G} (g : G)
    (hx : orderOf (QuotientGroup.mk x : G ⧸ Wker G) = 3) :
    orderOf (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ Wker G) = 3 := by
  have hsemiconj : SemiconjBy (QuotientGroup.mk g : G ⧸ Wker G)
      (QuotientGroup.mk x : G ⧸ Wker G)
      (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ Wker G) := by
    unfold SemiconjBy
    rw [show (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ Wker G) =
        QuotientGroup.mk g * QuotientGroup.mk x * (QuotientGroup.mk g)⁻¹ from by
      simp]
    group
  rw [← SemiconjBy.orderOf_eq (QuotientGroup.mk g : G ⧸ Wker G) hsemiconj, hx]

theorem uc45_card_commutator_zpowers (c : Pre45 p G D) {d : G}
    (hd : Subgroup.zpowers d = D) :
    Nat.card ↥(⁅Xof G, Subgroup.zpowers d⁆ ⊔ ZXof G) = 4 * Nat.card ↥(ZXof G) := by
  rw [hd]
  exact uc45_card_TZ c

theorem uc45_card_commutator_zpowers_conj (c : Pre45 p G D) {d : G}
    (hd : Subgroup.zpowers d = D) (g : G) :
    Nat.card ↥(⁅Xof G, Subgroup.zpowers (g * d * g⁻¹)⁆ ⊔ ZXof G) =
      4 * Nat.card ↥(ZXof G) := by
  have hXmap : (Xof G).map (MulAut.conj g).toMonoidHom = Xof G :=
    Subgroup.Normal.map_conj_eq (H := Xof G) g
  have hZXmap : (ZXof G).map (MulAut.conj g).toMonoidHom = ZXof G :=
    Subgroup.Normal.map_conj_eq (H := ZXof G) g
  have hφd : (MulAut.conj g).toMonoidHom d = g * d * g⁻¹ := by
    simp [MulAut.conj_apply]
  have hbT : ⁅Xof G, Subgroup.zpowers (g * d * g⁻¹)⁆ =
      (Tof G D).map (MulAut.conj g).toMonoidHom := by
    have hmap := Subgroup.map_commutator (MulAut.conj g).toMonoidHom (H₁ := Xof G)
      (H₂ := Subgroup.zpowers d)
    rw [hXmap, MonoidHom.map_zpowers, hφd] at hmap
    rw [← hmap, ← hd]
  rw [hbT]
  have hsup : (Tof G D).map (MulAut.conj g).toMonoidHom ⊔ ZXof G =
      (Tof G D ⊔ ZXof G).map (MulAut.conj g).toMonoidHom := by
    simp only [Subgroup.map_sup, hZXmap]
  rw [hsup, Subgroup.card_map_of_injective (MulAut.conj g).injective, uc45_card_TZ c]

theorem uc45_sup_map_conj (c : Pre45 p G D) {d : G} (hd : Subgroup.zpowers d = D) (g : G) :
    D ⊔ D.map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({d, g * d * g⁻¹} : Set G) := by
  rw [← hd, uc45_map_conj_zpowers d g, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1

theorem uc45_pair_shape (hPair : PairX) (c : Pre45 p G D) (N : Subgroup G) [N.Normal]
    (hN : N = Wker G) (g : G) :
    Z3E9A5Mod2 ((D ⊔ D.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N)) := by
  subst hN
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨d, hd⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top D).mp (isCyclic_of_prime_card c.card_three)
  have hdtri : orderOf (QuotientGroup.mk d : G ⧸ Wker G) = 3 :=
    uc45_orderOf_mk_of_zpowers c hd
  have hbtri : orderOf (QuotientGroup.mk (g * d * g⁻¹) : G ⧸ Wker G) = 3 :=
    uc45_orderOf_mk_conj g hdtri
  have hcardd := uc45_card_commutator_zpowers c hd
  have hcardb := uc45_card_commutator_zpowers_conj c hd g
  have hpair := hPair G (Xof G) (Wker G) (xof_isPGroup (G := G)) c.class_two.1 c.class_two.2
    (uc45_center_Xof_isCyclic c) (fun g => mem_wker (G := G) (g := g)) d (g * d * g⁻¹)
    hdtri hbtri hcardd hcardb
  have hsup : D ⊔ D.map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({d, g * d * g⁻¹} : Set G) := uc45_sup_map_conj c hd g
  rw [hsup]
  exact hpair

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
