module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DMat
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

namespace U2DFrame

variable {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]

theorem orderOf_eq {E : Subgroup G} {b : Fin 2 → G} (hF : U2DFrame r E b) (i : Fin 2) :
    orderOf (b i) = r := by
  have hr := (Fact.out : r.Prime)
  have : NeZero r := ⟨hr.ne_zero⟩
  have : Fact (1 < r) := ⟨hr.one_lt⟩
  rcases hr.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hF.pow_eq_one i)) with h | h
  · rw [orderOf_eq_one_iff] at h
    have h0 := congrFun (hF.indep (Pi.single i 1) (by rw [hF.coord_single_one, h])) i
    rw [Pi.single_eq_same, Pi.zero_apply] at h0
    exact absurd h0 one_ne_zero
  · exact h

theorem of_pair [Finite G] {z₀ z₁ : G} (h₀ : orderOf z₀ = r) (h₁ : orderOf z₁ = r)
    (hc : z₀ * z₁ = z₁ * z₀) (hn : z₁ ∉ zpowers z₀) :
    U2DFrame r (zpowers z₀ ⊔ zpowers z₁) ![z₀, z₁] := by
  have hr := (Fact.out : r.Prime)
  have : NeZero r := ⟨hr.ne_zero⟩
  have : Fact (1 < r) := ⟨hr.one_lt⟩
  obtain ⟨hE, -⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card h₀ h₁
      hc hn
  refine ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).1 hE, fun i => ?_,
    fun a ha => ?_, fun x hx => ?_⟩
  · fin_cases i
    exacts [mem_sup_left (mem_zpowers z₀), mem_sup_right (mem_zpowers z₁)]
  · have ha' : z₀ ^ (a 0).val * z₁ ^ (a 1).val = 1 := ha
    have ha1 : a 1 = 0 := by
      by_contra h
      have hval : (a 1).val * ((a 1)⁻¹).val % r = 1 := by
        rw [← ZMod.val_mul, mul_inv_cancel₀ h, ZMod.val_one]
      have e : z₁ = (z₁ ^ (a 1).val) ^ ((a 1)⁻¹).val := by
        rw [← pow_mul, ← pow_mod_orderOf, h₁, hval, pow_one]
      apply hn
      rw [e, eq_inv_of_mul_eq_one_right ha']
      exact pow_mem (inv_mem (pow_mem (mem_zpowers z₀) _)) _
    have ha0 : a 0 = 0 := by
      rw [ha1, ZMod.val_zero, pow_zero, mul_one] at ha'
      have h := orderOf_dvd_of_pow_eq_one ha'
      rw [h₀] at h
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt _))
    funext i
    fin_cases i
    exacts [ha0, ha1]
  · have hc' : Commute z₀ z₁ := hc
    have hle : zpowers z₀ ≤ normalizer (zpowers z₁ : Set G) :=
      zpowers_le.2 (mem_normalizer_fintype fun y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        rw [(hc'.zpow_right k).eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers z₁) k)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hle] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, z₀ ^ i = y :=
      (isOfFinOrder_of_finite z₀).mem_powers_iff_mem_zpowers.2 hy
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, z₁ ^ j = z :=
      (isOfFinOrder_of_finite z₁).mem_powers_iff_mem_zpowers.2 hz
    have e₀ : z₀ ^ (i % r) = z₀ ^ i := by rw [← h₀, pow_mod_orderOf]
    have e₁ : z₁ ^ (j % r) = z₁ ^ j := by rw [← h₁, pow_mod_orderOf]
    refine ⟨![(i : ZMod r), (j : ZMod r)], ?_⟩
    show z₀ ^ (i : ZMod r).val * z₁ ^ (j : ZMod r).val = z₀ ^ i * z₁ ^ j
    rw [ZMod.val_natCast, ZMod.val_natCast, e₀, e₁]

end U2DFrame

variable {G : Type} [Group G] [Finite G]

theorem uc22r8u2d_conj_cases {M L K : Subgroup G} (hne : K ≠ L)
    (hset : conjSetOf M L = {L, K}) {t : G} (ht : t ∈ M) :
    (t ∈ normalizer (L : Set G) ∧ t ∈ normalizer (K : Set G)) ∨
      (L.map (MulAut.conj t).toMonoidHom = K ∧ K.map (MulAut.conj t).toMonoidHom = L) := by
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  have hL' : L.map (MulAut.conj t).toMonoidHom ∈ conjSetOf M L := ⟨t, ht, rfl⟩
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ conjSetOf M K := ⟨t, ht, rfl⟩
  rw [hset] at hL'
  rw [uc22p2214_conjSetOf_eq hKmem, hset] at hK'
  have hinj := Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL' hK'
  rcases hL' with hL' | hL' <;> rcases hK' with hK' | hK'
  · exact absurd (hinj (hL'.trans hK'.symm)).symm hne
  · exact Or.inl ⟨mem_normalizer_iff_map_conj_eq.2 hL', mem_normalizer_iff_map_conj_eq.2 hK'⟩
  · exact Or.inr ⟨hL', hK'⟩
  · exact absurd (hinj (hL'.trans hK'.symm)).symm hne

theorem uc22r8u2d_le_normalizer {M L : Subgroup G} (hc2 : (conjSetOf M L).ncard = 2) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    R ≤ normalizer (L : Set G) := fun g hg => by
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨g, hg⟩
  have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
  exact uc22p2214_mem_normalizer_of_odd hc2 (hR.le hg)
    ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hg3))

theorem uc22r8u2d_exists_swap {M L K : Subgroup G} (hne : K ≠ L)
    (hset : conjSetOf M L = {L, K}) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    ∃ s ∈ M, s ∈ normalizer (R : Set G) ∧ (∀ x ∈ L, s * x * s⁻¹ ∈ K) ∧
      ∀ x ∈ K, s * x * s⁻¹ ∈ L := by
  have : Fact r.Prime := ⟨hr⟩
  have hc2 : (conjSetOf M L).ncard = 2 := by
    rw [hset]
    exact Set.ncard_pair hne.symm
  have hR0 : CFSG.ABGLocalTools.IsSylowOf r R (normalizer (L : Set G) ⊓ M) :=
    hR.of_le (le_inf (uc22r8u2d_le_normalizer hc2 hr hr2 hR) hR.le) inf_le_right
  have hLK : ∀ m ∈ normalizer (L : Set G) ⊓ M, m ∈ normalizer (K : Set G) := by
    intro m hm
    rcases uc22r8u2d_conj_cases hne hset (mem_inf.1 hm).2 with h | ⟨h, -⟩
    · exact h.2
    · exact absurd (h.symm.trans (mem_normalizer_iff_map_conj_eq.1 (mem_inf.1 hm).1)) hne
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  obtain ⟨g, hgM, hgK⟩ := hKmem
  have hgL : K.map (MulAut.conj g).toMonoidHom = L := by
    rcases uc22r8u2d_conj_cases hne hset hgM with h | ⟨-, h⟩
    · exact absurd (hgK.trans (mem_normalizer_iff_map_conj_eq.1 h.1)) hne
    · exact h
  have hgLK : ∀ x ∈ L, g * x * g⁻¹ ∈ K := fun x hx => by
    rw [hgK]
    exact mem_map.2 ⟨x, hx, rfl⟩
  have hgKL : ∀ x ∈ K, g * x * g⁻¹ ∈ L := fun x hx => by
    rw [← hgL]
    exact mem_map.2 ⟨x, hx, rfl⟩
  have hgN : g ∈ normalizer ((normalizer (L : Set G) ⊓ M : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun m hm => mem_inf.2 ⟨?_, M.mul_mem (M.mul_mem hgM
      (mem_inf.1 hm).2) (M.inv_mem hgM)⟩
    have hmK : K.map (MulAut.conj m).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.1 (hLK m hm)
    refine mem_normalizer_iff_map_conj_eq.2 ?_
    calc L.map (MulAut.conj (g * m * g⁻¹)).toMonoidHom
        = (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * m * g⁻¹)).toMonoidHom := by
          rw [hgL]
      _ = (K.map (MulAut.conj m).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [uc22p22d_map_conj_map_conj, uc22p22d_map_conj_map_conj, inv_mul_cancel_right]
      _ = L := by rw [hmK, hgL]
  obtain ⟨k, hk, hkN⟩ := uc22r8100b_frattini hR0 hgN
  have hkL : k⁻¹ ∈ normalizer (L : Set G) := inv_mem (mem_inf.1 hk).1
  have hkK : k⁻¹ ∈ normalizer (K : Set G) := hLK _ (inv_mem hk)
  have e : ∀ x, k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k⁻¹⁻¹ := fun x => by group
  refine ⟨k⁻¹ * g, M.mul_mem (M.inv_mem (mem_inf.1 hk).2) hgM, hkN, fun x hx => ?_,
    fun x hx => ?_⟩
  · rw [e]
    exact (mem_normalizer_iff.1 hkK _).1 (hgLK x hx)
  · rw [e]
    exact (mem_normalizer_iff.1 hkL _).1 (hgKL x hx)

structure U2DBasis (M L K : Subgroup G) (r : ℕ) (R E : Subgroup G) (b : Fin 2 → G) : Prop where
  sylow : CFSG.ABGLocalTools.IsSylowOf r R M
  le_R : E ≤ R
  le_centralizer : R ≤ centralizer (E : Set G)
  omega : ∀ x ∈ R, x ^ r = 1 → x ∈ E
  le_sup : E ≤ L ⊔ K
  frame : U2DFrame r E b
  mem_L : b 0 ∈ L
  mem_K : b 1 ∈ K
  inf_L : E ⊓ L ≤ zpowers (b 0)
  inf_K : E ⊓ K ≤ zpowers (b 1)

theorem uc22r8u2d_exists_basis {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h2 : CFSG.Open.pRank r M ≤ 2) {A : Subgroup G} (hAL : A ≤ L) (hAr : Nat.card A = r) :
    ∃ (R E : Subgroup G) (b : Fin 2 → G), U2DBasis M L K r R E b ∧ A = zpowers (b 0) := by
  have : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ M := uc22p22a_le_of_isSubnormal hL.1
  have hLmem : L ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert L _
  have hc2 : (conjSetOf M L).ncard = 2 := by
    rw [hset]
    exact Set.ncard_pair hne.symm
  have hZL : center (Bar2 L) = ⊥ := uc22s21r899_center_bot hL hLmem hLS
  have hrL : CFSG.Open.pRank r L ≤ 1 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) hr hr2]
    exact pRank_le_one_of_isL2_or_isSz hLS hr hr2
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])
  obtain ⟨Q, hQ⟩ := (hAp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf r R M := ⟨Q, rfl⟩
  have hAR : A ≤ R := fun x hx => ⟨⟨x, hLM (hAL hx)⟩, hQ hx, rfl⟩
  have hRM : R ≤ M := hR.le
  obtain ⟨z₀, ⟨hz₀R, hz₀L⟩, hz₀o, hz₀c⟩ :=
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hR.isPGroup
      inf_le_left ((le_inf Subgroup.le_normalizer (uc22r8u2d_le_normalizer hc2 hr hr2 hR)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) fun h => hA1 (le_bot_iff.1 (h ▸ le_inf hAR hAL))
  have hAz : A ≤ zpowers z₀ := by
    intro a ha
    by_contra haz
    have ha1 : a ≠ 1 := fun h => haz (h ▸ (zpowers z₀).one_mem)
    have hdvd : orderOf a ∣ r := by
      rw [← hAr, ← Subgroup.orderOf_mk a ha]
      exact orderOf_dvd_natCard _
    have hao : orderOf a = r :=
      (hr.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h => ha1 (orderOf_eq_one_iff.1 h)
    obtain ⟨hP, hPc⟩ :=
      CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card
        hz₀o hao (mem_centralizer_iff.1 hz₀c a (hAR ha)).symm haz
    have h := CFSG.SectionRank.le_pRank hr.one_lt
      (sup_le (zpowers_le.2 hz₀L) (zpowers_le.2 (hAL ha)))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).1 hP) hPc
    omega
  obtain ⟨s, -, hsR, hsL, -⟩ := uc22r8u2d_exists_swap hne hset hr hr2 hR
  obtain ⟨z₁, hz₁R, hz₁K, hz₁o, hz₁c⟩ : ∃ z₁ ∈ R, z₁ ∈ K ∧ orderOf z₁ = r ∧
      z₁ ∈ centralizer (R : Set G) := by
    refine ⟨s * z₀ * s⁻¹, (mem_normalizer_iff.1 hsR z₀).1 hz₀R, hsL z₀ hz₀L,
      (MulEquiv.orderOf_eq (MulAut.conj s) z₀).trans hz₀o, mem_centralizer_iff.2 fun h hh => ?_⟩
    have e := mem_centralizer_iff.1 hz₀c _ ((mem_normalizer_iff.1 (inv_mem hsR) h).1 hh)
    calc h * (s * z₀ * s⁻¹) = s * (s⁻¹ * h * s⁻¹⁻¹ * z₀) * s⁻¹ := by group
      _ = s * (z₀ * (s⁻¹ * h * s⁻¹⁻¹)) * s⁻¹ := by rw [e]
      _ = s * z₀ * s⁻¹ * h := by group
  have hz₀r : z₀ ^ r = 1 := by
    rw [← hz₀o]
    exact pow_orderOf_eq_one z₀
  have hz₁r : z₁ ^ r = 1 := by
    rw [← hz₁o]
    exact pow_orderOf_eq_one z₁
  have hz₁n : z₁ ∉ zpowers z₀ := by
    intro h
    have h1 := uc22p2213e_eq_one_of_mem_inf hL hK hne.symm hZL hr hr2 (zpowers_le.2 hz₀L h) hz₁K
      hz₁r
    rw [h1, orderOf_one] at hz₁o
    exact hr.one_lt.ne hz₁o
  have hc : z₀ * z₁ = z₁ * z₀ := mem_centralizer_iff.1 hz₁c z₀ hz₀R
  obtain ⟨-, hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hz₀o
      hz₁o hc hz₁n
  have hF := U2DFrame.of_pair hz₀o hz₁o hc hz₁n
  have hEZ : zpowers z₀ ⊔ zpowers z₁ ≤ centralizer (R : Set G) :=
    sup_le (zpowers_le.2 hz₀c) (zpowers_le.2 hz₁c)
  have hER : zpowers z₀ ⊔ zpowers z₁ ≤ R := sup_le (zpowers_le.2 hz₀R) (zpowers_le.2 hz₁R)
  refine ⟨R, zpowers z₀ ⊔ zpowers z₁, ![z₀, z₁], ⟨hR, hER, le_centralizer_iff.1 hEZ,
    fun x hx hxr => ?_, sup_le_sup (zpowers_le.2 hz₀L) (zpowers_le.2 hz₁K), hF, hz₀L, hz₁K,
    ?_, ?_⟩, ?_⟩
  ·
    by_contra hxE
    have hx1 : x ≠ 1 := fun h => hxE (h ▸ one_mem _)
    have h3 := CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hr
      hF.elem hEc (orderOf_eq_prime hxr hx1) hxE
      (mem_centralizer_iff.2 fun e he => (mem_centralizer_iff.1 (hEZ he) x hx).symm)
      (hER.trans hRM) (hRM hx)
    omega
  ·
    rintro x ⟨hxE, hxL⟩
    obtain ⟨a, rfl⟩ := hF.span x hxE
    have hxL' : z₀ ^ (a 0).val * z₁ ^ (a 1).val ∈ L := hxL
    have h1 : z₁ ^ (a 1).val = 1 := by
      refine uc22p2213e_eq_one_of_mem_inf hL hK hne.symm hZL hr hr2 ?_ (pow_mem hz₁K _)
        (by rw [pow_right_comm, hz₁r, one_pow])
      have h := L.mul_mem (L.inv_mem (L.pow_mem hz₀L (a 0).val)) hxL'
      rwa [inv_mul_cancel_left] at h
    show z₀ ^ (a 0).val * z₁ ^ (a 1).val ∈ zpowers z₀
    rw [h1, mul_one]
    exact pow_mem (mem_zpowers z₀) _
  ·
    rintro x ⟨hxE, hxK⟩
    obtain ⟨a, rfl⟩ := hF.span x hxE
    have hxK' : z₀ ^ (a 0).val * z₁ ^ (a 1).val ∈ K := hxK
    have h0 : z₀ ^ (a 0).val = 1 := by
      refine uc22p2213e_eq_one_of_mem_inf hL hK hne.symm hZL hr hr2 (pow_mem hz₀L _) ?_
        (by rw [pow_right_comm, hz₀r, one_pow])
      have h := K.mul_mem hxK' (K.inv_mem (K.pow_mem hz₁K (a 1).val))
      rwa [mul_inv_cancel_right] at h
    show z₀ ^ (a 0).val * z₁ ^ (a 1).val ∈ zpowers z₁
    rw [h0, one_mul]
    exact pow_mem (mem_zpowers z₁) _
  · show A = zpowers z₀
    exact eq_of_le_of_card_ge hAz (le_of_eq (by rw [Nat.card_zpowers, hz₀o, hAr]))

namespace U2DBasis

variable {M L K R E : Subgroup G} {r : ℕ} {b : Fin 2 → G}

theorem exists_swap (hb : U2DBasis M L K r R E b) (hne : K ≠ L)
    (hset : conjSetOf M L = {L, K}) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ s ∈ normalizer (E : Set G) ⊓ M,
      s * b 0 * s⁻¹ ∈ zpowers (b 1) ∧ s * b 1 * s⁻¹ ∈ zpowers (b 0) := by
  obtain ⟨s, hsM, hsR, hsL, hsK⟩ := uc22r8u2d_exists_swap hne hset hr hr2 hb.sylow
  have hsE : s ∈ normalizer (E : Set G) := mem_normalizer_fintype fun x hx =>
    hb.omega _ ((mem_normalizer_iff.1 hsR x).1 (hb.le_R hx))
      (by rw [conj_pow, hb.frame.elem.2 x hx, mul_one, mul_inv_cancel])
  have hbE : ∀ i, s * b i * s⁻¹ ∈ E := fun i => (mem_normalizer_iff.1 hsE _).1 (hb.frame.mem i)
  exact ⟨s, mem_inf.2 ⟨hsE, hsM⟩, hb.inf_K (mem_inf.2 ⟨hbE 0, hsL _ hb.mem_L⟩),
    hb.inf_L (mem_inf.2 ⟨hbE 1, hsK _ hb.mem_K⟩)⟩

theorem conj_mem_zpowers (hb : U2DBasis M L K r R E b) (hne : K ≠ L)
    (hset : conjSetOf M L = {L, K}) {x : G} (hxM : x ∈ M) (hxE : x ∈ normalizer (E : Set G))
    (hodd : Odd (orderOf x)) (i : Fin 2) : x * b i * x⁻¹ ∈ zpowers (b i) := by
  have hc2 : (conjSetOf M L).ncard = 2 := by
    rw [hset]
    exact Set.ncard_pair hne.symm
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  have hc2K : (conjSetOf M K).ncard = 2 := by
    rw [uc22p2214_conjSetOf_eq hKmem]
    exact hc2
  have hxL := uc22p2214_mem_normalizer_of_odd hc2 hxM hodd
  have hxK := uc22p2214_mem_normalizer_of_odd hc2K hxM hodd
  have hbE : ∀ j, x * b j * x⁻¹ ∈ E := fun j => (mem_normalizer_iff.1 hxE _).1 (hb.frame.mem j)
  fin_cases i
  · exact hb.inf_L (mem_inf.2 ⟨hbE 0, (mem_normalizer_iff.1 hxL _).1 hb.mem_L⟩)
  · exact hb.inf_K (mem_inf.2 ⟨hbE 1, (mem_normalizer_iff.1 hxK _).1 hb.mem_K⟩)

end U2DBasis

end CFSG.LocalAnalysis.UniquenessCase.UC22
