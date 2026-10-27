module

public import CFSG.Quasithin.Vol2.Ch10SecD31E
public import CFSG.Quasithin.Background.E3Gen

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_subgroupOf_eq (H K : Subgroup G) : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_inf_normalizer_V1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    {g : G} (hidx : (Subgroup.centralizer ({g} : Set G)).relIndex (fsuVM T L I) ≤ 2) :
    g ∈ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      (Subgroup.centralizer ({g} : Set G)).relIndex (fsuUL T L I) ≤ 2 := by
  obtain ⟨hc16, hc2⟩ := card_V1_eq h37 h38 hI16 h h3 hV1
  have hidx1 : (Subgroup.centralizer ({g} : Set G)).relIndex (fsuUL T L I) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right V1_le_V Subgroup.index_ne_zero_of_finite).trans hidx
  refine ⟨?_, hidx1⟩
  obtain ⟨v, hvV1, hvg, hvL0⟩ : ∃ v ∈ fsuUL T L I, v ∈ Subgroup.centralizer ({g} : Set G) ∧
      v ∉ Subgroup.centralizer (fsuL0 T L : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.centralizer ({g} : Set G) ⊓ fsuUL T L I ≤
        Subgroup.centralizer (fsuL0 T L : Set G) ⊓ fsuUL T L I :=
      fun x hx => ⟨hcon x hx.2 hx.1, hx.2⟩
    have h1 := Subgroup.card_le_of_le hle
    have hc2' : Nat.card ↥((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
        (fsuUL T L I)) = 2 := hc2
    rw [← card_subgroupOf_eq (Subgroup.centralizer (fsuL0 T L : Set G)) (fsuUL T L I), hc2']
      at h1
    have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({g} : Set G)) (fsuUL T L I)
    rw [hc16] at h2
    have := Nat.mul_le_mul hidx1 h1
    omega
  have hgv : g ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hvg).symm
  exact (h1029 G T L I h L (Or.inl rfl)).2.2 v hvV1 hvL0 hgv

theorem mem_centralizer_V1_of (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    {g : G} (hidx : (Subgroup.centralizer ({g} : Set G)).relIndex (fsuVM T L I) ≤ 2) :
    g ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨⟨hgM, hgV1⟩, hidx1⟩ := mem_inf_normalizer_V1 h37 h38 hI16 h1029 h h3 hV1 hidx
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
    rcases SecA.conjugate_eq_or h37 h38 h ht htn hgM with hL | hL
    · exact SecA.conjugate_eq_self_iff.mp hL
    · exfalso
      have hV12 : fsuUL T L I = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
        rw [← hL, ← SecA.conjugate_commutator_fsuVM hgM, SecA.conjugate_eq_self_iff.mpr hgV1]
      have hVC : fsuUL T L I ≤ Subgroup.centralizer (L : Set G) :=
        hV12 ▸ V2_le_centralizer_L h37 h38 h ht htn
      obtain ⟨hc16, hc2⟩ := card_V1_eq h37 h38 hI16 h h3 hV1
      obtain ⟨-, hcomm, -⟩ := h3
      have htop : cV1 T L I = ⊤ := by
        rw [← fixV_autOn_V1 h37 h38 h, eq_top_iff]
        intro v _
        exact (mem_centralizer_iff_autOn L_le_normalizer_V1 v).mp (hVC v.2)
      rw [htop, Subgroup.card_top, hc16] at hc2
      exact absurd hc2 (by norm_num)
  exact mem_centralizer_V1 h37 h38 hI16 h h3 hV1 hgL hgV1 hidx1

omit [Finite G] in
theorem centralizer_conj_eq_map (g t : G) :
    Subgroup.centralizer ({t * g * t⁻¹} : Set G) =
      (Subgroup.centralizer ({g} : Set G)).map (MulAut.conj t).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    refine ⟨t⁻¹ * x * t, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t⁻¹ * x * t * g = t⁻¹ * (x * (t * g * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * g * t⁻¹) * x) * t := by rw [hx]
      _ = g * (t⁻¹ * x * t) := by group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * y * t⁻¹ * (t * g * t⁻¹) = t * (y * g) * t⁻¹ := by group
      _ = t * (g * y) * t⁻¹ := by rw [hy]
      _ = t * g * t⁻¹ * (t * y * t⁻¹) := by group

theorem mem_centralizer_V (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    {g : G} (hidx : (Subgroup.centralizer ({g} : Set G)).relIndex (fsuVM T L I) ≤ 2) :
    g ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have htV : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I htM
  have hg1 := mem_centralizer_V1_of h37 h38 hI16 h1029 h h3 hV1 hidx
  have hidx' : (Subgroup.centralizer ({t * g * t⁻¹} : Set G)).relIndex (fsuVM T L I) ≤ 2 := by
    have hV : (fsuVM T L I).map (MulAut.conj t).toMonoidHom = fsuVM T L I := by
      have := SecA.conjugate_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem htV)
      rw [SecA.conjugate_eq_map, inv_inv] at this
      exact this
    rw [centralizer_conj_eq_map, ← hV,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hidx
  have hg2 := mem_centralizer_V1_of h37 h38 hI16 h1029 h h3 hV1 hidx'
  have hgV2 : ∀ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, w * g = g * w := by
    intro w hw
    rw [← SecA.conjugate_commutator_fsuVM htM, SecA.mem_conjugate_iff] at hw
    have h1 := Subgroup.mem_centralizer_iff.mp hg2 _ hw
    have e1 : t * (w * g) * t⁻¹ = t * (g * w) * t⁻¹ := by
      calc t * (w * g) * t⁻¹ = (t * w * t⁻¹) * (t * g * t⁻¹) := by group
        _ = (t * g * t⁻¹) * (t * w * t⁻¹) := h1
        _ = t * (g * w) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e1)
  have hle : fsuVM T L I ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hg1 w hw)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hgV2 w hw)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem index_fixV_convI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : Subgroup.normalizer (V : Set G)) :
    (fixV (Subgroup.zpowers (convI hV g))).index =
      (Subgroup.centralizer ({(g : G)} : Set G)).relIndex V := by
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers (convI hV g))) =
      Nat.card ↥(Subgroup.centralizer ({(g : G)} : Set G) ⊓ V) := by
    have hmem : ∀ w : IntMod V hV, w ∈ fixV (Subgroup.zpowers (convI hV g)) ↔
        w.val ∈ Subgroup.centralizer ({(g : G)} : Set G) := by
      intro w
      rw [mem_fixV_zpowers_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hw
        have h1 : (g : G) * w.val * (g : G)⁻¹ = w.val := by
          rw [← convI_apply_val hV g w, hw]
        calc w.val * (g : G) = (g : G) * w.val * (g : G)⁻¹ * g := by rw [h1]
          _ = g * w.val := by group
      · intro hw
        apply IntMod.val_injective
        rw [convI_apply_val, ← hw]
        group
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.val, (hmem w.1).mp w.2, w.1.val_mem⟩
        invFun := fun x => ⟨IntMod.mk hV ⟨x.1, x.2.2⟩, (hmem _).mpr x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers (convI hV g)))
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({(g : G)} : Set G)) V
  have h3 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h3, hcard] at h1
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({(g : G)} : Set G) ⊓ V) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, mul_comm, h2]

theorem two_le_sParam (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    2 ≤ E3.sParam (SecA.isElemAbelian_fsuVM h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hV := SecA.isElemAbelian_fsuVM h with hhV
  obtain ⟨hc16, -⟩ := card_V1_eq h37 h38 hI16 h h3 hV1
  have hr : ((1 : ℕ) : ℕ∞) < E3.rParam (fsuVM T L I) := by
    have h1 := (h1029 G T L I h L (Or.inl rfl)).2.1
    have h4 : E3.mQuot ⁅fsuVM T L I, L⁆ ⊥ = 4 := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left]
      show padicValNat 2 (Nat.card ↥(fsuUL T L I)) = 4
      rw [hc16, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
    rw [h4] at h1
    exact lt_of_lt_of_le (by norm_num) h1
  have hm : 1 < E3.mParam (autI hV ⊤) := by
    unfold E3.mParam
    split_ifs with hev
    · have hne : {n : ℕ | ∃ t ∈ autI hV ⊤, orderOf t = 2 ∧
          n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hV ⊤)) 2
          (even_iff_two_dvd.mp hev)
        exact ⟨_, (x : MulAut (IntMod (fsuVM T L I) hV)), x.2,
          by rw [Subgroup.orderOf_coe]; exact hx, rfl⟩
      refine lt_of_lt_of_le (by norm_num : 1 < 2) (le_csInf hne ?_)
      rintro n ⟨τ, hτ, hτ2, rfl⟩
      obtain ⟨g, -, rfl⟩ := (mem_autI hV).mp hτ
      by_contra hlt
      push Not at hlt
      have hidx : (Subgroup.centralizer ({(g : G)} : Set G)).relIndex (fsuVM T L I) ≤ 2 := by
        rw [← index_fixV_convI hV g]
        have hp : IsPGroup 2 (IntMod (fsuVM T L I) hV) := fun w =>
          ⟨1, by simpa using IntMod.sq_eq_one w⟩
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
        have hdvd : (fixV (Subgroup.zpowers (convI hV g))).index ∣ 2 ^ k :=
          hk ▸ Subgroup.index_dvd_card _
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        unfold rkIdx at hlt
        rw [hj, padicValNat.prime_pow] at hlt
        rw [hj]
        interval_cases j <;> norm_num
      have hgC := mem_centralizer_V h37 h38 hI16 h1029 h h3 hV1 hidx
      rw [(convI_eq_one_iff hV g).mpr hgC, orderOf_one] at hτ2
      exact absurd hτ2 (by norm_num)
    ·
      have hp : IsPGroup 2 (fsuVM T L I) := SecA.isPGroup_fsuVM h
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
      have h16 : 16 ≤ Nat.card ↥(fsuVM T L I) := hc16 ▸ Subgroup.card_le_of_le V1_le_V
      have hrk : rk (IntMod (fsuVM T L I) hV) = k := by
        unfold rk
        show padicValNat 2 (Nat.card ↥(fsuVM T L I)) = k
        rw [hk, padicValNat.prime_pow]
      rw [hrk]
      by_contra hk1
      push Not at hk1
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      omega
  have := E3.lt_sParam_of_lt hV hr hm
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
