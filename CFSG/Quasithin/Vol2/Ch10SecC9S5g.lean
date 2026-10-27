module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5f

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_case_three_of_A5 (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) :
    ¬ Case10_1_1Three T L I := by
  rintro ⟨⟨e3⟩, -⟩
  have hc := (Nat.card_congr eL.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  have h5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]; decide
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [h5, h3] at hc
  omega

omit [Finite G] in
theorem inf_centralizer_le_pCoreOf {V₁ : Subgroup G}
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set G))
    (hLN : L ≤ Subgroup.normalizer (V₁ : Set G)) (hV1 : ⁅V₁, L⁆ = V₁) (hne : V₁ ≠ ⊥) :
    L ⊓ Subgroup.centralizer (V₁ : Set G) ≤ pCoreOf 2 L := by
  set N : Subgroup ↥L := (Subgroup.centralizer (V₁ : Set G)).subgroupOf L with hNdef
  have hNn : N.Normal := ⟨fun x hx g => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer' (hLN g.2)) _).mp hx⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hmk
  have hNm : (N.map mk).Normal := hNn.map mk (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map mk) with h | h
  · rintro x ⟨hxL, hxC⟩
    have hx : mk ⟨x, hxL⟩ ∈ N.map mk := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxC, rfl⟩
    rw [h, Subgroup.mem_bot, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact (C1Pack.coe_mem_pCoreOf_iff L _).mpr hx
  · exfalso
    apply hne
    have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro x hx
      have hx' : mk ⟨x, hx⟩ ∈ N.map mk := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx'
      have h1 : n⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := by
        rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
        exact hnx
      have h2 := hO ((C1Pack.coe_mem_pCoreOf_iff L _).mpr h1)
      have e1 : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hn) h2
    rw [← hV1]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hLC)

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem false_of_b1 (h1026 : Stmt10_2_6) (hV1 : fsuUL T L I ≤ VI T L I J w)
    (hIrr : IrrG L (VI T L I J w)) : False := by
  have hne : fsuUL T L I ≠ ⊥ := SecA.commutator_fsuVM_ne_bot c.hyp.fsu
  rcases hIrr.2 _ hV1 (le_normalizer_fsuUL T L I) with h | h
  · exact hne h
  · apply c.not_le
    intro j hj
    have hjN : j ∈ Subgroup.normalizer (VI T L I J w : Set G) :=
      le_normalizer_VI T L I J w (Subgroup.mem_sup_left hj)
    rw [← h] at hjN
    exact (h1026 G T L I c.hyp).2.1 L (Or.inl rfl) hjN

theorem false_of_b2 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo)
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥(alternatingGroup (Fin 7)))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (hV1 : fsuUL T L I ≤ VI T L I J w)
    (h3v : ∀ v ∈ ⁅VI T L I J w, L⁆, ∃ l ∈ L, orderOf l = 3 ∧ l * v = v * l)
    (h3N : ∀ y ∈ J ⊓ Subgroup.normalizer (L : Set G), orderOf y = 3 →
      y ∈ L ⊔ (J ⊓ Subgroup.centralizer (VI T L I J w : Set G))) : False := by
  have hyp := c.hyp
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1C, -, -⟩ := hdec t c.ht c.htn
  have hwt : t * w * t⁻¹ ∈ ⁅VI T L I J w, L⁆ := by
    have h1 := c.claim.1
    rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L c.ht),
      SecA.mem_conjugate_iff] at h1
    have h2 : fsuUL T L I ≤ ⁅VI T L I J w, L⁆ :=
      calc fsuUL T L I = ⁅fsuUL T L I, L⁆ := (commutator_fsuUL_eq hyp).symm
        _ ≤ ⁅VI T L I J w, L⁆ := Subgroup.commutator_mono hV1 le_rfl
    exact h2 h1
  obtain ⟨l, hl, hl3, hlc⟩ := h3v _ hwt
  set y := t⁻¹ * l * t with hy
  have hyLt : y ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff, hy]
    simpa [mul_assoc] using hl
  have hy3 : orderOf y = 3 := by
    have := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective l
    rw [← hl3, ← this]
    simp [hy]
  have hyw : y ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * w = t⁻¹ * (l * (t * w * t⁻¹)) * t := by rw [hy]; group
      _ = t⁻¹ * ((t * w * t⁻¹) * l) * t := by rw [hlc]
      _ = w * y := by rw [hy]; group
  have hyJ := c.mem_J_of_orderOf_three h38 h318 h36' hK7 hE eJ hyw hy3
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := conjugate_le_normalizer hyp c.ht hyLt
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  have hKN : L ≤ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer (VI T L I J w : Set G) : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf' (Subgroup.le_normalizer (c.le hx))
      (mem_normalizer_centralizer' (hJN (c.le hx)))
  have hyLC := h3N y ⟨hyJ, hyN⟩ hy3
  rw [sup_comm] at hyLC
  have hyLC' : y ∈ (↑((J ⊓ Subgroup.centralizer (VI T L I J w : Set G)) ⊔ L) : Set G) := hyLC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN] at hyLC'
  obtain ⟨d, hd, l', hl', hdl⟩ := hyLC'
  have hdl' : d * l' = y := hdl
  have hl'C : l' ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : y * v = v * y := Subgroup.mem_centralizer_iff.mp (hV1C hv) y hyLt
    have h2 : v * d = d * v := Subgroup.mem_centralizer_iff.mp hd.2 v (hV1 hv)
    have e1 : l' = d⁻¹ * y := by rw [← hdl']; group
    rw [e1]
    calc v * (d⁻¹ * y) = d⁻¹ * (d * v) * d⁻¹ * y := by group
      _ = d⁻¹ * (v * d) * d⁻¹ * y := by rw [h2]
      _ = d⁻¹ * (v * y) := by group
      _ = d⁻¹ * (y * v) := by rw [h1]
      _ = d⁻¹ * y * v := by group
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuUL T L I : Set G) :=
    (pCoreOf_L_le_centralizer hyp h1011).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V))
  have hl'O : l' ∈ pCoreOf 2 L :=
    inf_centralizer_le_pCoreOf hsimp hOC (le_normalizer_fsuUL T L I) (commutator_fsuUL_eq hyp)
      (SecA.commutator_fsuVM_ne_bot hyp.fsu) ⟨hl', hl'C⟩
  have hdO : d ∈ pCoreOf 2 J := hCJ ▸ hd
  have h2 : IsPGroup 2 ↥(pCoreOf 2 J ⊔ pCoreOf 2 L) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans c.le).trans ((Subgroup.le_normalizer).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)))
  have hy2 : y ∈ pCoreOf 2 J ⊔ pCoreOf 2 L :=
    hdl' ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_left hdO) (Subgroup.mem_sup_right hl'O)
  obtain ⟨k, hk⟩ := h2 ⟨y, hy2⟩
  have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [hy3] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
