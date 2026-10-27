module

public import CFSG.Quasithin.Vol2.Ch10SecD32D
public import CFSG.Quasithin.Vol2.Ch10SecD32C
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem card_le_two_mul_card_inf {A N : Subgroup G}
    (h2 : ∀ a ∈ A, ∀ b ∈ A, a ∉ N → b ∉ N → a * b⁻¹ ∈ N) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ N) := by
  classical
  by_cases hA : A ≤ N
  · rw [inf_eq_left.mpr hA]
    omega
  obtain ⟨a₀, ha₀, ha₀N⟩ := Set.not_subset.mp hA
  let f : ↥A → ↥(A ⊓ N) × Bool := fun a =>
    if h : (a : G) ∈ N then (⟨a, a.2, h⟩, false)
    else (⟨a * a₀⁻¹, A.mul_mem a.2 (A.inv_mem ha₀), h2 a a.2 a₀ ha₀ h ha₀N⟩, true)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    split_ifs at hab with ha hb hb
    · exact Subtype.ext (congrArg (fun p : ↥(A ⊓ N) × Bool => (p.1 : G)) hab)
    · simp at hab
    · simp at hab
    · exact Subtype.ext
        (mul_right_cancel (congrArg (fun p : ↥(A ⊓ N) × Bool => (p.1 : G)) hab))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem sixty_four_le_card_V (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) : 64 ≤ Nat.card (fsuVM T L I) := by
  have hV1 := card_V1 h3 hc
  have hinj : Function.Injective (MulAut.conj t⁻¹).toMonoidHom := (MulAut.conj t⁻¹).injective
  have hV2 : Nat.card (⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) = 8 := by
    rw [V2_eq_conjugate ht, SecA.conjugate_eq_map, Subgroup.card_map_of_injective hinj, hV1]
  have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  let f : ↥(fsuUL T L I) × ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) →
      ↥(fsuVM T L I) :=
    fun p => ⟨p.1 * p.2, (fsuVM T L I).mul_mem (V1_le_V p.1.2) (hle2 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (V1_inf_V2 h37 h38 h hc ht htn) a.2 a'.2
      b.2 b'.2 (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hV1, hV2] at this

theorem card_le_four_of_inf_centralizer_eq_bot (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) (hV1 : IsElemAbelian 2 (fsuUL T L I)) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (hEN : E ≤ Subgroup.normalizer (fsuUL T L I : Set G))
    (hEC : E ⊓ Subgroup.centralizer (fsuUL T L I : Set G) = ⊥) : Nat.card E ≤ 4 := by
  have hcard := card_autOn_eq_relIndex hEN
  rw [hEC, Subgroup.relIndex_bot_left] at hcard
  have hel := isElemAbelian2_autOn hV1 hE hEN
  have : IsMulCommutative ↥(fsuUL T L I) := hV1.1
  rw [← hcard]
  exact card_le_four_of_isElemAbelian2 h3 hc hel

theorem false_of_offender (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥)
    (hNV : Subgroup.normalizer (fsuVM T L I : Set G) = fsuM T L)
    (hTI : fusionIsTI (fsuVM T L I)) {g : G}
    (hcomm : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥)
    (hA2 : E3.mQuot (conjSubgroup (fsuVM T L I) g)
      (conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G)) = 2)
    (hAC : conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G) ⊓
      Subgroup.centralizer (fsuVM T L I : Set G) = ⊥) : False := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hV := SecA.isElemAbelian_fsuVM h
  have hV2g : IsPGroup 2 (conjSubgroup (fsuVM T L I) g) :=
    E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hcardVg : Nat.card (conjSubgroup (fsuVM T L I) g) = Nat.card (fsuVM T L I) :=
    Subgroup.card_map_of_injective hinj
  have hcardA : 16 ≤ Nat.card ↥(conjSubgroup (fsuVM T L I) g ⊓
      Subgroup.normalizer (fsuVM T L I : Set G)) := by
    have h1 := E3.card_eq_two_pow_mul hV2g (inf_le_left : conjSubgroup (fsuVM T L I) g ⊓
      Subgroup.normalizer (fsuVM T L I : Set G) ≤ conjSubgroup (fsuVM T L I) g)
    rw [hA2, hcardVg] at h1
    have h2 := sixty_four_le_card_V h37 h38 h h3 hc ht htn
    omega
  have hAM : conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G) ≤
      fsuM T L := inf_le_right.trans hNV.le
  have hcardA0 : 8 ≤ Nat.card ↥(conjSubgroup (fsuVM T L I) g ⊓
      Subgroup.normalizer (fsuVM T L I : Set G) ⊓ Subgroup.normalizer (L : Set G)) := by
    have := card_le_two_mul_card_inf (N := Subgroup.normalizer (L : Set G))
      fun a ha b hb han hbn => by
        have h1 := (SecA.conjugate_eq_or h37 h38 h ht htn (hAM ha)).resolve_left
          fun h' => han (SecA.conjugate_eq_self_iff.mp h')
        have h2 := (SecA.conjugate_eq_or h37 h38 h ht htn (hAM hb)).resolve_left
          fun h' => hbn (SecA.conjugate_eq_self_iff.mp h')
        exact SecA.mul_inv_mem_normalizer_of_conjugate_eq (h1.trans h2.symm)
    omega
  set A0 := conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G) ⊓
    Subgroup.normalizer (L : Set G) with hA0
  have hA0V : A0 ≤ Subgroup.normalizer (fsuVM T L I : Set G) := inf_le_left.trans inf_le_right
  have hA0V1 : A0 ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator hA0V inf_le_right
  have hA0Lt : A0 ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
    intro a ha
    rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate]
    refine (SecA.conjugate_eq_or h37 h38 h ht htn ((fsuM T L).mul_mem (SecA.le_fsuM T L ht)
      (hAM ha.1))).resolve_left fun h' => htn ?_
    have h1 := SecA.conjugate_eq_self_iff.mp h'
    have e : t = t * a * a⁻¹ := by group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem h1 ((Subgroup.normalizer _).inv_mem ha.2)
  have hA0V2 : A0 ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator hA0V hA0Lt
  have hA0el : IsElemAbelian 2 A0 :=
    B2F.isElemAbelian_mono (inf_le_left.trans inf_le_left) (E3.isElemAbelian_conjSubgroup hV g)
  have hV1el : IsElemAbelian 2 (fsuUL T L I) := B2F.isElemAbelian_mono V1_le_V hV
  by_cases hK1 : A0 ⊓ Subgroup.centralizer (fsuUL T L I : Set G) = ⊥
  · have := card_le_four_of_inf_centralizer_eq_bot h3 hc hV1el hA0el hA0V1 hK1
    omega
  by_cases hK2 : A0 ⊓
      Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) = ⊥
  · have hinjt : Function.Injective (MulAut.conj t⁻¹⁻¹).toMonoidHom :=
      (MulAut.conj t⁻¹⁻¹).injective
    have hEcard : Nat.card (conjSubgroup A0 t⁻¹) = Nat.card A0 :=
      Subgroup.card_map_of_injective hinjt
    have hEN : conjSubgroup A0 t⁻¹ ≤ Subgroup.normalizer (fsuUL T L I : Set G) := by
      intro e he
      have he' := mem_conjSubgroup_iff.mp he
      rw [inv_inv] at he'
      have h1 := hA0V2 he'
      rw [V2_eq_conjugate ht] at h1
      have h2 : t⁻¹ * e * t ∈ conjSubgroup (Subgroup.normalizer (fsuUL T L I : Set G)) t := by
        rw [E3.conjSubgroup_normalizer]
        exact h1
      rw [mem_conjSubgroup_iff] at h2
      have e' : t * (t⁻¹ * e * t) * t⁻¹ = e := by group
      rwa [e'] at h2
    have hEC : conjSubgroup A0 t⁻¹ ⊓ Subgroup.centralizer (fsuUL T L I : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro e ⟨he0, heC⟩
      have he := mem_conjSubgroup_iff.mp he0
      rw [inv_inv] at he
      have h1 : t⁻¹ * e * t ∈
          Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
        rw [V2_eq_conjugate ht]
        have h2 : t⁻¹ * e * t ∈
            conjSubgroup (Subgroup.centralizer (fsuUL T L I : Set G)) t := by
          rw [mem_conjSubgroup_iff]
          have e' : t * (t⁻¹ * e * t) * t⁻¹ = e := by group
          rw [e']
          exact heC
        rw [E3.conjSubgroup_centralizer] at h2
        exact h2
      have h2 : t⁻¹ * e * t ∈ A0 ⊓
          Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
        ⟨he, h1⟩
      rw [hK2, Subgroup.mem_bot] at h2
      rw [Subgroup.mem_bot]
      calc e = t * (t⁻¹ * e * t) * t⁻¹ := by group
        _ = 1 := by rw [h2]; group
    have := card_le_four_of_inf_centralizer_eq_bot h3 hc hV1el
      (E3.isElemAbelian_conjSubgroup hA0el t⁻¹) hEN hEC
    omega
  obtain ⟨⟨a, haK⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
  obtain ⟨⟨b, hbK⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK2
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have hb1' : b ≠ 1 := fun h' => hb1 (Subtype.ext h')
  have hVne : fsuVM T L I ≠ conjSubgroup (fsuVM T L I) g := by
    intro heq
    apply hcomm
    rw [← heq]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => B2F.isElemAbelian_comm hV hy hx
  have hVVg := inf_conjSubgroup_eq_bot hTI hVne
  have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have haV2 : ∀ v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, v * a = a * v := by
    intro v hv
    have hvV : v ∈ fsuVM T L I := hle2 hv
    have hvb : v * b = b * v := (Subgroup.mem_centralizer_iff.mp hbK.2) v hv
    have hvN := mem_normalizer_conjSubgroup hTI hbK.1.1.1 hb1' hvb
    have h1 : v * a * v⁻¹ * a⁻¹ ∈ conjSubgroup (fsuVM T L I) g :=
      (conjSubgroup (fsuVM T L I) g).mul_mem ((Subgroup.mem_normalizer_iff.mp hvN a).mp
        haK.1.1.1) ((conjSubgroup (fsuVM T L I) g).inv_mem haK.1.1.1)
    have h2 : v * a * v⁻¹ * a⁻¹ ∈ fsuVM T L I := by
      have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
      rw [e]
      exact (fsuVM T L I).mul_mem hvV ((Subgroup.mem_normalizer_iff.mp haK.1.1.2 v⁻¹).mp
        ((fsuVM T L I).inv_mem hvV))
    have h3 : v * a * v⁻¹ * a⁻¹ ∈ fsuVM T L I ⊓ conjSubgroup (fsuVM T L I) g := ⟨h2, h1⟩
    rw [hVVg, Subgroup.mem_bot] at h3
    calc v * a = v * a * v⁻¹ * a⁻¹ * (a * v) := by group
      _ = a * v := by rw [h3, one_mul]
  have hVa : fsuVM T L I ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [SecA.fsuVM_eq_sup h37 h38 h ht htn]
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp haK.2) v hv)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (haV2 v hv)
  have haV : a ∈ conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G) ⊓
      Subgroup.centralizer (fsuVM T L I : Set G) :=
    ⟨haK.1.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hVa hv)⟩
  rw [hAC, Subgroup.mem_bot] at haV
  exact ha1' haV

theorem stmt10_3_2_of (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9) (h10213 : Stmt10_2_13)
    (h1031 : Stmt10_3_1) : Stmt10_3_2 := by
  intro G _ _ T L I h z hz hz1 hzM
  obtain ⟨h3, hw, -⟩ := h10213 G T L I h
  have hc := (h1031 G T L I h).1
  have hzT : T ≤ Subgroup.centralizer ({z} : Set G) := by
    have hzC : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).mpr (fun x hx => hx.1) hz.1
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzC.2) s hs
  have hTI := fusionIsTI_V h331 h37 h38 h1029 h h3 hc hz.2 hz1 hzT hzM
  have hV := SecA.isElemAbelian_fsuVM h
  have hT322 : E3.HypE322 T (fsuVM T L I) :=
    ⟨⟨le_top, h.fsu.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.fsu.sylow.2⟩,
      SecA.fsuVM_le_T h, SecA.le_normalizer_fsuVM T L I⟩
  have hw' : E3.wParam T (fsuVM T L I) = ((2 : ℕ) : ℕ∞) := by rw [hw]; rfl
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT322 hw'
  have h24 : E3.HypE324 T (fsuVM T L I) hV := Or.inl (by rw [hw]; norm_num)
  have hAC := inf_centralizer_eq_bot_of_fusionIsTI hV hT322 h24 hTI hw' hg
  have hA2 : E3.mQuot (conjSubgroup (fsuVM T L I) g)
      (conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G)) = 2 := by
    have := hg.2
    rw [hw'] at this
    exact_mod_cast this.symm
  exact false_of_offender h37 h38 h h3 hc
    (SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h)) hTI hg.1 hA2 hAC

end CFSG.Quasithin.Vol2.Ch10.SecD
