module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZF
public import CFSG.Quasithin.Vol2.Ch10SecC8FF
public import CFSG.Quasithin.Vol2.Ch10SecQ3CS
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem cV1_eq_bot : cV1 T L I = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_subgroupOf] at hu
  have h : (u : G) ∈ fsuCVM T L I := ⟨SecA.fsuUL_le_fsuVM T L I u.2, hu⟩
  rw [c.fsuCVM_eq_bot, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

theorem normalizes_of_mem {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) :
    y ∈ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  ⟨SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer c.hyp.fsu.maximal.1) hyL0,
    SecA.mem_normalizer_inf_of_mem (SecA.le_fsuL0 T L)
      (SecA.fsuL0_le_normalizer c.hyp.fsu.maximal.1) hyL0 hyN⟩

theorem fix_V₁ {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) (hyo : Odd (orderOf y)) {u : G}
    (hu : u ∈ fsuUL T L I) (hu1 : u ≠ 1) (hyu : y * u * y⁻¹ = u) :
    ∀ v ∈ fsuUL T L I, y * v * y⁻¹ = v := by
  obtain ⟨-, -, hUab, hB⟩ := c.h1
  rw [c.cV1_eq_bot] at hB
  obtain ⟨hyU, hyT⟩ := c.normalizes_of_mem hyL0 hyN
  set d := conjAct (fsuUL T L I) ⟨y, hyU⟩ with hd
  have hdL : d ∈ autOn L (fsuUL T L I) :=
    SecA.conjAct_mem_autOn_of_mem_fsuL0 c.h37 c.h38 c.hyp hyL0 hyU
  have hdN := SecA.conjAct_mem_normalizer_autOn hyU hyT
  have hdo := SecA.odd_orderOf_conjAct hyU hyo
  have hdu : d ⟨u, hu⟩ = ⟨u, hu⟩ := Subtype.ext (by rw [hd, SecA.coe_conjAct_apply']; exact hyu)
  by_cases hd1 : d = 1
  · intro v hv
    have h := congrArg (fun φ : MulAut ↥(fsuUL T L I) => ((φ ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hd1
    simp only [hd, SecA.coe_conjAct_apply', MulAut.one_apply] at h
    exact h
  · exfalso
    have h0 := (factNatBorelFix_holds ↥(fsuUL T L I) (autOn L (fsuUL T L I)) n hB
      (autOn (T ⊓ L) (fsuUL T L I)) (SecA.isSylowTwoOf_autOn_inf c.hyp)).2 d ⟨hdL, hdN⟩ hd1 hdo
    have hst : Subgroup.zpowers d ≤ MulAction.stabilizer (MulAut ↥(fsuUL T L I))
        (⟨u, hu⟩ : ↥(fsuUL T L I)) := Subgroup.zpowers_le.mpr hdu
    have hmem : (⟨u, hu⟩ : ↥(fsuUL T L I)) ∈ fixV (Subgroup.zpowers d) := fun x hx =>
      MulAction.mem_stabilizer_iff.mp (hst hx)
    rw [h0, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)

theorem pow_fix_V₁ {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) (hyo : Odd (orderOf y)) :
    ∀ v ∈ fsuUL T L I, y ^ (2 ^ n - 1) * v * (y ^ (2 ^ n - 1))⁻¹ = v := by
  obtain ⟨hUab, F, _, _, _, -, hF, ⟨nc⟩⟩ := SecA.exists_natCoord c.hyp c.h1
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨hyU, hyT⟩ := c.normalizes_of_mem hyL0 hyN
  set d := conjAct (fsuUL T L I) ⟨y, hyU⟩ with hd
  have hdL : d ∈ autOn L (fsuUL T L I) :=
    SecA.conjAct_mem_autOn_of_mem_fsuL0 c.h37 c.h38 c.hyp hyL0 hyU
  have hdN := SecA.conjAct_mem_normalizer_autOn hyU hyT
  set γ := nc.eρ.symm ⟨d, hdL⟩ with hγ
  have hγd : ((nc.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) = d := by
    rw [hγ, MulEquiv.apply_symm_apply]
  have hc : ∃ c' : F, (nc.g * γ * nc.g⁻¹) * SecA.unipSL 1 * (nc.g * γ * nc.g⁻¹)⁻¹ =
      SecA.unipSL c' := by
    have h1 : ((nc.eρ (nc.g⁻¹ * SecA.unipSL 1 * nc.g) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) :=
      (nc.unip _).mpr ⟨1, by group⟩
    have h2 : ((nc.eρ (γ * (nc.g⁻¹ * SecA.unipSL 1 * nc.g) * γ⁻¹) :
        ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγd]
      exact (Subgroup.mem_normalizer_iff.mp hdN _).mp h1
    obtain ⟨c', hc'⟩ := (nc.unip _).mp h2
    exact ⟨c', by rw [← hc']; group⟩
  have hγo : Odd (orderOf γ) := by
    have h1 : orderOf γ = orderOf d := by
      rw [← MulEquiv.orderOf_eq nc.eρ γ, ← Subgroup.orderOf_coe, hγd]
    rw [h1]
    exact SecA.odd_orderOf_conjAct hyU hyo
  have hp := pow_card_sub_one_eq_one hc hγo
  rw [hFc] at hp
  have hdp : d ^ (2 ^ n - 1) = 1 := by
    rw [← hγd, ← Subgroup.coe_pow, ← map_pow, hp, map_one, Subgroup.coe_one]
  intro v hv
  have h := congrArg (fun φ : MulAut ↥(fsuUL T L I) => ((φ ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hdp
  simp only [hd, ← map_pow, SecA.coe_conjAct_apply', MulAut.one_apply,
    Subgroup.coe_pow] at h
  exact h

theorem exists_t : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
  by_contra h
  push Not at h
  exact c.hyp.not_normal h

omit [Finite G] c in
theorem conj_mem_of_mem {y t : G} (ht : t ∈ T) (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) :
    t * y * t⁻¹ ∈ fsuL0 T L ∧ t * y * t⁻¹ ∈ Subgroup.normalizer (T0 T L : Set G) :=
  ⟨(Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L ht) y).mp hyL0,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (SecA.le_normalizer_T0 T L ht) hyN)
      (Subgroup.inv_mem _ (SecA.le_normalizer_T0 T L ht))⟩

theorem fix_V₂ {t : G} (ht : t ∈ T) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) (hyo : Odd (orderOf y)) {u : G}
    (hu : u ∈ CFSG.conjugate (fsuUL T L I) t) (hu1 : u ≠ 1) (hyu : y * u * y⁻¹ = u) :
    ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, y * v * y⁻¹ = v := by
  obtain ⟨h2L0, h2N⟩ := conj_mem_of_mem ht hyL0 hyN
  have h2o : Odd (orderOf (t * y * t⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hyo
  have hu' : t * u * t⁻¹ ∈ fsuUL T L I := SecA.mem_conjugate_iff.mp hu
  have hu1' : t * u * t⁻¹ ≠ 1 := fun h => hu1 (by
    have := congrArg (fun x => t⁻¹ * x * t) h
    simpa [mul_assoc] using this)
  have hyu' : t * y * t⁻¹ * (t * u * t⁻¹) * (t * y * t⁻¹)⁻¹ = t * u * t⁻¹ := by
    calc t * y * t⁻¹ * (t * u * t⁻¹) * (t * y * t⁻¹)⁻¹ = t * (y * u * y⁻¹) * t⁻¹ := by group
      _ = t * u * t⁻¹ := by rw [hyu]
  exact SecA.forall_conj_eq_of_conj (c.fix_V₁ h2L0 h2N h2o hu' hu1' hyu')

theorem pow_eq_one {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) (hyo : Odd (orderOf y)) :
    y ^ (2 ^ n - 1) = 1 := by
  obtain ⟨t, ht, htn⟩ := c.exists_t
  obtain ⟨h2L0, h2N⟩ := conj_mem_of_mem ht hyL0 hyN
  have h2o : Odd (orderOf (t * y * t⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hyo
  have h2 := c.pow_fix_V₁ h2L0 h2N h2o
  have h2' : ∀ u ∈ fsuUL T L I,
      t * y ^ (2 ^ n - 1) * t⁻¹ * u * (t * y ^ (2 ^ n - 1) * t⁻¹)⁻¹ = u := by
    intro u hu
    have := h2 u hu
    rwa [conj_pow] at this
  exact SecA.eq_one_of_forall_conj_eq c.h37 c.h38 c.hyp ht htn ((fsuL0 T L).pow_mem hyL0 _)
    (Odd.of_dvd_nat hyo (orderOf_pow_dvd _)) (c.pow_fix_V₁ hyL0 hyN hyo)
    (SecA.forall_conj_eq_of_conj h2')

theorem k_le_n : k ≤ n := by
  have hp := c.pow_eq_one (oTwoUpper_le _ c.hbB0).1 (oTwoUpper_le _ c.hbB0).2 c.hbo
  have h2 : 2 ^ k - 1 ∣ 2 ^ n - 1 := c.hbk.trans (orderOf_dvd_of_pow_eq_one hp)
  have hn : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := c.h1.1; omega)
  have h3 := Nat.le_of_dvd (by omega) h2
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4 : 2 ^ k ≤ 2 ^ n := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4

theorem card_E₁ :
    Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) = 2 ^ n := by
  obtain ⟨-, -, hUab, hB⟩ := c.h1
  rw [c.cV1_eq_bot] at hB
  have h := (factNatBorelFix_holds ↥(fsuUL T L I) (autOn L (fsuUL T L I)) n hB
    (autOn (T ⊓ L) (fsuUL T L I)) (SecA.isSylowTwoOf_autOn_inf c.hyp)).1
  rwa [SecC.card_fixV_autOn_eq (fun x (hx : x ∈ T ⊓ L) => le_normalizer_fsuUL T L I hx.2)] at h

theorem E₁_le_E :
    fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ≤
      omegaOneCenterOf (thompsonJ T) := by
  obtain ⟨t, ht, htn⟩ := c.exists_t
  obtain ⟨_, -, -, ha, -⟩ := c.hyp.three
  have hV₁ : fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (ha t ht htn).2.2
  intro v hv
  have hvV : v ∈ fsuVM T L I := SecA.fsuUL_le_fsuVM T L I hv.1
  have hvT0 := SecA.mem_centralizer_T0 c.h37 c.h38 c.h322 c.hyp ht htn hvV hv.2
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right) (hV₁ hv.1))
  have hJ : thompsonJ T ≤ Subgroup.centralizer ({v} : Set G) := by
    refine c.thompsonJ_le_T0.trans (sup_le (fun x hx => ?_) (fun x hx => ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hvT0 x hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 v hvV).symm
  refine inf_centralizer_thompsonJ_le (SecA.isElemAbelian_fsuVM c.hyp) (SecA.fsuVM_le_T c.hyp)
    ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hJ hx)

theorem card_E :
    2 ^ (2 * n) ≤ Nat.card ↥(omegaOneCenterOf (thompsonJ T)) := by
  obtain ⟨t, ht, htn⟩ := c.exists_t
  set E₁ := fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hE₁
  set E₂ := CFSG.conjugate E₁ t with hE₂
  have hE₁E := c.E₁_le_E
  have hE₂E : E₂ ≤ omegaOneCenterOf (thompsonJ T) := fun x hx => by
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_E T (T.inv_mem ht)) _).mp
      (hE₁E (SecA.mem_conjugate_iff.mp hx))
    simpa [mul_assoc] using h
  have hcard₂ : Nat.card E₂ = Nat.card E₁ := Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ CFSG.conjugate (fsuUL T L I) t :=
      SecA.mem_conjugate_iff.mpr (SecA.mem_conjugate_iff.mp hx.2).1
    have h2 := SecA.inf_conjugate_le_fsuCVM c.hyp ht htn ⟨hx.1.1, h1⟩
    rwa [c.fsuCVM_eq_bot] at h2
  have hN : E₁ ≤ Subgroup.normalizer (E₂ : Set G) := SecE.le_normalizer_of_commute
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf (hE₁E ha) (hE₂E hb)
  have h := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, hcard₂, c.card_E₁] at h
  calc 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by ring
    _ = Nat.card ↥(E₁ ⊔ E₂) := h.symm
    _ ≤ _ := Subgroup.card_le_of_le (sup_le hE₁E hE₂E)

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
