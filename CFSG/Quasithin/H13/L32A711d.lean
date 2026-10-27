module

public import CFSG.Quasithin.H13.L32A711c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def s3Vec : Fin 2 → Fin 3 → ZMod 2 := ![![1, 0, 1], ![0, 1, 1]]

@[expose] def s3Mat (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => s3Vec j (σ⁻¹ (Fin.castSucc i))

theorem s3Mat_det : ∀ σ : Equiv.Perm (Fin 3), (s3Mat σ).det = 1 := by decide

theorem s3Mat_one : s3Mat 1 = 1 := by decide

theorem s3Mat_mul : ∀ σ τ : Equiv.Perm (Fin 3), s3Mat (σ * τ) = s3Mat σ * s3Mat τ := by decide

theorem s3Mat_injective : ∀ σ τ : Equiv.Perm (Fin 3), s3Mat σ = s3Mat τ → σ = τ := by decide

theorem s3Mat_surjective : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∃ σ : Equiv.Perm (Fin 3), s3Mat σ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by decide

@[expose] def s3SL2Hom : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun σ := ⟨s3Mat σ, s3Mat_det σ⟩
  map_one' := Subtype.ext s3Mat_one
  map_mul' σ τ := Subtype.ext (s3Mat_mul σ τ)

@[expose] noncomputable def s3SL2Equiv :
    Equiv.Perm (Fin 3) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective s3SL2Hom ⟨fun σ τ h => s3Mat_injective σ τ (congrArg Subtype.val h),
    fun A => by
      obtain ⟨σ, hσ⟩ := s3Mat_surjective A
      exact ⟨σ, Subtype.ext hσ⟩⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quasithinO2QuotientIso_trans {X : Subgroup G} {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂]
    (h : quasithinO2QuotientIso X Q₁) (e : Q₁ ≃* Q₂) : quasithinO2QuotientIso X Q₂ := by
  obtain ⟨φ, hφ, hker⟩ := h
  refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hφ, ?_⟩
  rw [← hker]
  ext x
  simp

omit [Finite G] in
theorem dvd_relIndex_of_pow_mem {K B : Subgroup G} (hKB : K ≤ B)
    (hB : B ≤ Subgroup.normalizer (K : Set G)) {b : G} (hb : b ∈ B) {q : ℕ} (hq : q.Prime)
    (hbq : b ^ q ∈ K) (hbK : b ∉ K) : q ∣ K.relIndex B := by
  have : Fact q.Prime := ⟨hq⟩
  have : (K.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKB).mpr hB
  set x := QuotientGroup.mk' (K.subgroupOf B) ⟨b, hb⟩ with hx
  have hx1 : x ^ q = 1 := by
    rw [hx, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hbq
  have hx2 : x ≠ 1 := by
    rw [hx, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hbK
  have hord : orderOf x = q := orderOf_eq_prime hx1 hx2
  rw [← hord]
  exact orderOf_dvd_natCard x

namespace Ctx711

variable {T L V H V₂ H₂ : Subgroup G} {z a l p : G} (C : Ctx711 T L V H V₂ H₂ z a l p)
include C

theorem bD_le : bD T L V H₂ V₂ ≤ d1 T L H₂ V₂ := sup_le C.I2_le_d1 (pCoreOf_le 2 _)

theorem d1_le_NbD : d1 T L H₂ V₂ ≤ Subgroup.normalizer (bD T L V H₂ V₂ : Set G) := fun _ hg =>
  F6.mem_normalizer_sup (C.d1_le_NI2 hg) (le_normalizer_pCoreOf 2 _ hg)

theorem O2d1_le_O2b : pCoreOf 2 (d1 T L H₂ V₂) ≤ pCoreOf 2 (bD T L V H₂ V₂) :=
  le_pCoreOf_of_le_normalizer 2 le_sup_right (C.bD_le.trans (le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

theorem pB : pCoreOf 2 (bD T L V H₂ V₂) = pCoreOf 2 (d1 T L H₂ V₂) :=
  le_antisymm (U3.pCoreOf_le_pCoreOf C.bD_le C.d1_le_NbD) C.O2d1_le_O2b

theorem bD_S3 : quasithinO2QuotientIso (bD T L V H₂ V₂) (Equiv.Perm (Fin 3)) :=
  U3.quasithinO2QuotientIso_of_sup le_sup_left (C.bD_le.trans C.d1_le_NI2)
    (le_antisymm (sup_le_sup_left C.O2d1_le_O2b _) (sup_le le_sup_left (pCoreOf_le 2 _)))
    C.I2_S3

theorem O2d1_le_T : pCoreOf 2 (d1 T L H₂ V₂) ≤ T := pCoreOf_le_of_le C.S.hyp (T_le_d1 T L H₂ V₂)

theorem O2d1_cent : pCoreOf 2 (d1 T L H₂ V₂) ≤ Subgroup.centralizer (V₂ : Set G) := by
  intro q hq
  have hl : l ∈ d1 T L H₂ V₂ := L2_le_d1 T L H₂ V₂ C.hl
  have hq' : l⁻¹ * q * l ∈ pCoreOf 2 (d1 T L H₂ V₂) := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hl)) q).mp hq
    simpa using this
  have h1 := C.T_fix_z (C.O2d1_le_T hq')
  refine C.mem_cent (C.T_fix_z (C.O2d1_le_T hq)) ?_
  rw [← C.hlz]
  calc q * (l * z * l⁻¹) * q⁻¹ = l * ((l⁻¹ * q * l) * z * (l⁻¹ * q * l)⁻¹) * l⁻¹ := by group
    _ = l * z * l⁻¹ := by rw [h1]

theorem l_mem_bD : l ∈ bD T L V H₂ V₂ := Subgroup.mem_sup_left (C.L2_le_I2 C.hl)

theorem p_mem_bD : p ∈ bD T L V H₂ V₂ := by
  refine Subgroup.mem_sup_left ?_
  rw [C.I2_eq]
  exact Subgroup.mem_sup_right C.hp

theorem p_not_cent : p ∉ Subgroup.centralizer (V₂ : Set G) := fun h =>
  C.hpa (by rw [← Subgroup.mem_centralizer_iff.mp h a C.ha]; group)

theorem l_not_cent : l ∉ Subgroup.centralizer (V₂ : Set G) := fun h =>
  C.l_moves (by rw [← Subgroup.mem_centralizer_iff.mp h z C.V2_facts.2.2.2.2]; group)

theorem bD_cent :
    bD T L V H₂ V₂ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 (d1 T L H₂ V₂) := by
  set K := bD T L V H₂ V₂ ⊓ Subgroup.centralizer (V₂ : Set G) with hK
  have hOK : pCoreOf 2 (d1 T L H₂ V₂) ≤ K := le_inf le_sup_right C.O2d1_cent
  refine le_antisymm ?_ hOK
  have hKB : K ≤ bD T L V H₂ V₂ := inf_le_left
  have hBN : bD T L V H₂ V₂ ≤ Subgroup.normalizer (K : Set G) := fun _ hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      mem_normalizer_centralizer' (C.d1_le_NV2 (C.bD_le hg))⟩
  have h3 : 3 ∣ K.relIndex (bD T L V H₂ V₂) :=
    dvd_relIndex_of_pow_mem hKB hBN C.l_mem_bD Nat.prime_three
      (by rw [C.hl3]; exact one_mem _) (fun h => C.l_not_cent h.2)
  have h2 : 2 ∣ K.relIndex (bD T L V H₂ V₂) :=
    dvd_relIndex_of_pow_mem hKB hBN C.p_mem_bD Nat.prime_two
      ⟨by rw [sq]; exact mul_mem C.p_mem_bD C.p_mem_bD,
        by rw [sq]; exact C.sq_mem_cent (C.TV₂ C.pT) (C.T_fix_z C.pT)⟩
      (fun h => C.p_not_cent h.2)
  have h6 : 6 ∣ K.relIndex (bD T L V H₂ V₂) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hO6 : (pCoreOf 2 (d1 T L H₂ V₂)).relIndex (bD T L V H₂ V₂) = 6 := by
    rw [← C.pB, U3.relIndex_pCoreOf_of_quot C.bD_S3, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ hOK hKB
  rw [hO6] at hm
  have hpos : K.relIndex (bD T L V H₂ V₂) ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨c, hc⟩ := h6
  rw [hc] at hm hpos
  have h1 : (pCoreOf 2 (d1 T L H₂ V₂)).relIndex K = 1 := by
    have hc0 : c ≠ 0 := by rintro rfl; simp at hpos
    have : (pCoreOf 2 (d1 T L H₂ V₂)).relIndex K * c = 1 := by
      have := hm
      nlinarith
    exact Nat.eq_one_of_mul_eq_one_right this
  exact Subgroup.relIndex_eq_one.mp h1

theorem aD_inf_bD : aD T L H₂ V₂ ⊓ bD T L V H₂ V₂ ≤ pCoreOf 2 (d1 T L H₂ V₂) := fun _ hx => by
  rw [← C.bD_cent]
  exact ⟨hx.2, hx.1.2⟩

theorem d1_eq : d1 T L H₂ V₂ = aD T L H₂ V₂ ⊔ bD T L V H₂ V₂ := by
  refine le_antisymm (fun d hd => ?_) (sup_le inf_le_left C.bD_le)
  obtain ⟨l', hl', y, hy, t, ht, rfl⟩ := C.mem_d1 hd
  have htd : t ∈ d1 T L H₂ V₂ := T_le_d1 T L H₂ V₂ ht
  have ht' : t ∈ aD T L H₂ V₂ ⊔ bD T L V H₂ V₂ := by
    by_cases htC : t ∈ Subgroup.centralizer (V₂ : Set G)
    · exact Subgroup.mem_sup_left ⟨htd, htC⟩
    · have hpt : p⁻¹ * t ∈ Subgroup.centralizer (V₂ : Set G) :=
        C.inv_mul_mem_cent (C.TV₂ C.pT) (C.TV₂ ht) (C.T_fix_z C.pT) (C.T_fix_z ht) C.hpa
          (fun h => htC (C.mem_cent (C.T_fix_z ht) h))
      rw [show t = p * (p⁻¹ * t) by group]
      exact mul_mem (Subgroup.mem_sup_right C.p_mem_bD)
        (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨(d1 T L H₂ V₂).mul_mem
          ((d1 T L H₂ V₂).inv_mem (T_le_d1 T L H₂ V₂ C.pT)) htd, hpt⟩))
  exact mul_mem (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left (C.L2_le_I2 hl')))
    (Subgroup.mem_sup_left (C.Y_le_aD hy))) ht'

theorem aD_S3 : quasithinO2QuotientIso (aD T L H₂ V₂) (Equiv.Perm (Fin 3)) :=
  U3.quot_S3_of_index_three C.aD_syl C.aD_idx C.aD_nn

theorem pA : pCoreOf 2 (aD T L H₂ V₂) = aD T L H₂ V₂ ⊓ pCoreOf 2 (d1 T L H₂ V₂) :=
  le_antisymm (le_inf (pCoreOf_le 2 _) (U3.pCoreOf_le_pCoreOf inf_le_left C.d1_le_NaD))
    (U3.inf_pCoreOf_le_pCoreOf_of_le inf_le_left)

theorem d1_S3S3 :
    quasithinO2QuotientIso (d1 T L H₂ V₂) (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have hBN : bD T L V H₂ V₂ ≤ Subgroup.normalizer (aD T L H₂ V₂ : Set G) :=
    C.bD_le.trans C.d1_le_NaD
  refine U3.quasithinO2QuotientIso_prod inf_le_left C.bD_le C.d1_le_NaD C.d1_le_NbD
    (fun h hh => ?_) C.aD_inf_bD C.aD_S3 C.bD_S3 C.pA C.pB
  rw [C.d1_eq] at hh
  exact (F1.mem_sup_iff_exists_mul_of_normalizes hBN).mp hh

theorem d1_SL22 : quasithinO2QuotientIso (d1 T L H₂ V₂)
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
  quasithinO2QuotientIso_trans C.d1_S3S3 (s3SL2Equiv.prodCongr s3SL2Equiv)

end Ctx711

end CFSG.Quasithin.H13.L32A
