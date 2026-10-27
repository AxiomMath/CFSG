module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecC9B
public import CFSG.Quasithin.Vol2.Ch10SecC9Out

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_act_eq : ∀ a b : L3.Vec, a ≠ 0 → b ≠ 0 → ∃ γ : L3.Γ, L3.act γ a = b := by
  decide +kernel

omit [Finite G] in
theorem exists_conj_mod_V1 (h3 : Case10_1_1Three T L I) {x y : G} (hx : x ∈ fsuUL T L I)
    (hy : y ∈ fsuUL T L I) (hxC : x ∉ Subgroup.centralizer (fsuL0 T L : Set G))
    (hyC : y ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    ∃ l ∈ L, l * x * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D⟩ := hnat.toL3Coord
  have hx0 : coordOf D ⟨x, hx⟩ ≠ 0 := fun h =>
    hxC (Subgroup.mem_subgroupOf.mp ((coordOf_eq_zero_iff D _).mp h))
  have hy0 : coordOf D ⟨y, hy⟩ ≠ 0 := fun h =>
    hyC (Subgroup.mem_subgroupOf.mp ((coordOf_eq_zero_iff D _).mp h))
  obtain ⟨γ, hγ⟩ := exists_act_eq _ _ hx0 hy0
  obtain ⟨⟨l, hlN⟩, hl, hlγ⟩ := SecB.mem_autOn_iff.mp (D.π γ).2
  have hlx : l * x * l⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp hlN x).mp hx
  have hc1 := coord_conj (K := L) D hlN hlγ hx hlx
  rw [hγ] at hc1
  have hm : l * x * l⁻¹ * y⁻¹ ∈ fsuUL T L I := Subgroup.mul_mem _ hlx (Subgroup.inv_mem _ hy)
  have h0 : coordOf D ⟨_, hm⟩ = 0 := by
    have e : (⟨l * x * l⁻¹ * y⁻¹, hm⟩ : ↥(fsuUL T L I)) = ⟨_, hlx⟩ * (⟨y, hy⟩)⁻¹ := rfl
    rw [e, coordOf_mul, coordOf_inv, hc1]
    exact add_neg_cancel _
  exact ⟨l, hl, Subgroup.mem_subgroupOf.mp ((coordOf_eq_zero_iff D _).mp h0)⟩

omit [Finite G] in
theorem exists_conj_mod_V2 (h3 : Case10_1_1Three T L I) {t : G} (ht : t ∈ T) {x y : G}
    (hx : x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hy : y ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hxC : x ∉ Subgroup.centralizer (fsuL0 T L : Set G))
    (hyC : y ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    ∃ k ∈ CFSG.conjugate L t, k * x * k⁻¹ * y⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  have htM := SecA.le_fsuM T L ht
  have key : ∀ z, z ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔ t * z * t⁻¹ ∈ fsuUL T L I := fun z => by
    rw [← SecA.conjugate_commutator_fsuVM (I := I) htM, SecA.mem_conjugate_iff]
  have hMC := SecA.le_normalizer_centralizer (V := fsuL0 T L) (X := fsuM T L) le_rfl
  have hCt : ∀ g ∈ fsuM T L, ∀ z, z ∈ Subgroup.centralizer (fsuL0 T L : Set G) ↔
      g * z * g⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := fun g hg z =>
    Subgroup.mem_normalizer_iff.mp (hMC hg) z
  obtain ⟨l, hl, hlC⟩ := exists_conj_mod_V1 h3 ((key x).mp hx) ((key y).mp hy)
    (fun h => hxC ((hCt t htM x).mpr h)) (fun h => hyC ((hCt t htM y).mpr h))
  refine ⟨t⁻¹ * l * t, ?_, ?_⟩
  · rw [SecA.mem_conjugate_iff, show t * (t⁻¹ * l * t) * t⁻¹ = l by group]
    exact hl
  · rw [hCt t htM]
    have e : t * (t⁻¹ * l * t * x * (t⁻¹ * l * t)⁻¹ * y⁻¹) * t⁻¹ =
        l * (t * x * t⁻¹) * l⁻¹ * (t * y * t⁻¹)⁻¹ := by group
    rw [e]
    exact hlC

theorem T1_le_normalizer_V2 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    T1 T L ≤ Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
  intro s hs
  have hLt : s ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
    rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate]
    refine SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn (T.mul_mem ht hs.1) fun h => htn ?_
    have := (Subgroup.normalizer (L : Set G)).mul_mem h ((Subgroup.normalizer _).inv_mem hs.2)
    rwa [mul_inv_cancel_right] at this
  exact SecA.le_normalizer_commutator (X := Subgroup.zpowers s)
    (Subgroup.zpowers_le.mpr (SecA.le_normalizer_fsuVM T L I hs.1))
    (Subgroup.zpowers_le.mpr hLt) (Subgroup.mem_zpowers s)

theorem claim_case3_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1025 : Stmt10_2_5) (h3 : Case10_1_1Three T L I)
    (hcv : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {v : G} (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hbot : ∀ x ∈ fsuCVM T L I, x = 1 := fun x hx => by
    rw [hcv] at hx
    exact Subgroup.mem_bot.mp hx
  have hnotC : ∀ x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, x ≠ 1 →
      x ∉ Subgroup.centralizer (fsuL0 T L : Set G) := fun x hx hx1 hxC =>
    hx1 (hbot x ⟨hV2V hx, hxC⟩)
  have hV2ne : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≠ ⊥ := fun h => hv1 (by
    rw [h] at hv
    exact Subgroup.mem_bot.mp hv)
  obtain ⟨u, hu, hu1, huc⟩ := exists_mem_centralizer_ne_one hyp.fsu.sylow.1
    (hV2V.trans (SecA.fsuVM_le_T hyp)) inf_le_left (T1_le_normalizer_V2 h37 h38 hyp ht htn) hV2ne
  obtain ⟨k, hk, hkC⟩ := exists_conj_mod_V2 h3 ht hv hu (hnotC v hv hv1) (hnotC u hu hu1)
  have hkM : k ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.conjugate_le_fsuL0 ht hk)
  have hkv : k * v * k⁻¹ = u := by
    have hkvW : k * v * k⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
        Subgroup.le_normalizer hk) v).mp hv
    have h1 := hbot _ ⟨hV2V (Subgroup.mul_mem _ hkvW (Subgroup.inv_mem _ hu)), hkC⟩
    exact mul_inv_eq_one.mp h1
  have huM : ¬ Subgroup.centralizer ({u} : Set G) ≤ fsuM T L := by
    rw [← hkv, centralizer_conj_le_iff hkM]
    exact hvM
  have huV1 : u ∉ fsuUL T L I := fun h => hu1 (hbot u (inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h, hu⟩))
  have hfix : ∀ {x : G}, x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ → x ≠ 1 →
      T ⊓ Subgroup.centralizer ({x} : Set G) ≤ T1 T L := fun hx hx1 s hs =>
    mem_T1_of_fix h37 h38 hyp h1011 ht htn hx (hnotC _ hx hx1) hs.1
      (mul_conj_eq_of_mem_centralizer hs.2)
  have hTu : T ⊓ Subgroup.centralizer ({u} : Set G) = T1 T L := by
    refine le_antisymm (hfix hu hu1) fun s hs => ⟨hs.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huc s hs)
  obtain ⟨m, hm, hwW, hwV1, hSyl, hcon⟩ := exists_conj_in_V2 h37 h38 hyp ht htn hu huV1
  have hw1 : m * u * m⁻¹ ≠ 1 := fun h => hwV1 (h ▸ Subgroup.one_mem _)
  have hTw : T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) = T1 T L := by
    refine Subgroup.eq_of_le_of_card_ge (hfix hwW hw1) ?_
    have h1 : B6.conjSub m (T ⊓ Subgroup.centralizer ({u} : Set G)) ≤
        T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := fun y hy => by
      rw [B6.mem_conjSub] at hy
      have := hcon _ hy
      rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at this
    rw [← hTu, ← B6.card_conjSub _ m]
    exact Subgroup.card_le_of_le h1
  have hN : Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) : Subgroup G) : Set G) ≤ fsuM T L := by
    rw [hTw]
    exact h1025 G T L I hyp
  refine ⟨m * u * m⁻¹, hwW, hwV1, ?_, isSylowTwoOf_of_normalizer_le hSyl (inf_le_right.trans hN),
    ?_, fun _ s hs => ?_⟩
  · rw [centralizer_conj_le_iff hm]
    exact huM
  · exact (h1012 G T L I hyp).2.1.trans (hTw.symm.le.trans inf_le_right)
  · have hs' : s ∈ T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := hTw ▸ hs
    rw [mul_conj_eq_of_mem_centralizer hs'.2, mul_inv_cancel]
    exact Subgroup.one_mem _

end CFSG.Quasithin.Vol2.Ch10.SecC
