module

public import CFSG.Quasithin.MS93.S32Nat
public import CFSG.Quasithin.MS93.S32X

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Case1ii

variable {V : Type} [CommGroup V] [Finite V] {G' L' : Subgroup (MulAut V)}

theorem exists_two_ne_zero (F : Type) [Field F] :
    ∃ x y : Fin 3 → F, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  refine ⟨Pi.single 0 1, Pi.single 1 1, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simpa using congrFun h 0
  · simpa using congrFun h 1
  · simpa using congrFun h 0

theorem fixV_inf_commV_of_case1ii (hii : B51Case1ii G' L') : fixV L' ⊓ commV L' = ⊥ := by
  obtain ⟨-, n, K, iK, fK, -, I, π, hind, hsup, hreal, -, -⟩ := hii
  rw [eq_bot_iff]
  rintro x ⟨hxf, hxc⟩
  have h01 : (⨆ i, I i) = I 0 ⊔ I 1 := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup I 0) (le_iSup I 1)
  rw [← hsup, h01] at hxc
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Subgroup.mem_sup.mp hxc
  have hdisj : I 0 ⊓ I 1 = ⊥ := by
    have := (hind 0).eq_bot
    rw [eq_bot_iff] at this ⊢
    refine le_trans (inf_le_inf_left _ ?_) this
    exact le_iSup₂_of_le (f := fun j (_ : j ≠ (0 : Fin 2)) => I j) 1 (by decide) le_rfl
  have hfix0 : ∀ g ∈ L', g x₀ = x₀ := by
    intro g hg
    have hg0 : g x₀ ∈ I 0 := (hreal 0).2.2.2.1 ⟨g, hg⟩ x₀ hx₀
    have hg1 : g x₁ ∈ I 1 := (hreal 1).2.2.2.1 ⟨g, hg⟩ x₁ hx₁
    have he : g x₀ * g x₁ = x₀ * x₁ := by rw [← map_mul]; exact hxf g hg
    have hm : g x₀ * x₀⁻¹ ∈ I 0 ⊓ I 1 := by
      refine ⟨(I 0).mul_mem hg0 ((I 0).inv_mem hx₀), ?_⟩
      have e : g x₀ * x₀⁻¹ = x₁ * (g x₁)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul, mul_comm, ← mul_assoc, eq_mul_inv_iff_mul_eq, he]
      rw [e]
      exact (I 1).mul_mem hx₁ ((I 1).inv_mem hg1)
    rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  have hfix1 : ∀ g ∈ L', g x₁ = x₁ := by
    intro g hg
    have he : g x₀ * g x₁ = x₀ * x₁ := by rw [← map_mul]; exact hxf g hg
    rw [hfix0 g hg] at he
    exact mul_left_cancel he
  have h0 := natReal_fixed isTransNZ_statedSL3 (exists_two_ne_zero K) (hreal 0) hx₀ hfix0
  have h1 := natReal_fixed isTransNZ_statedSL3 (exists_two_ne_zero K) (hreal 1) hx₁ hfix1
  rw [Subgroup.mem_bot] at h0 h1
  rw [h0, h1, one_mul]
  exact Subgroup.one_mem _

theorem not_isIrrSec_of_case1ii (hii : B51Case1ii G' L')
    (hirr : XMod.IsIrrSec ↥L' (XMod.fixed ↥L' (commV L')) (commV L')) : False := by
  have hfix : XMod.fixed ↥L' (commV L') = ⊥ := by
    rw [eq_bot_iff, ← fixV_inf_commV_of_case1ii hii]
    intro x hx
    exact ⟨fun g hg => hx.2 ⟨g, hg⟩, hx.1⟩
  rw [hfix] at hirr
  obtain ⟨-, n, K, iK, fK, -, I, π, hind, hsup, hreal, -, -⟩ := hii
  have hle : ∀ i, I i ≤ commV L' := fun i => hsup ▸ le_iSup I i
  have hinv : ∀ i, XMod.IsInv ↥L' (I i) := fun i a w hw => (hreal i).2.2.2.1 a w hw
  rcases hirr.2 (I 0) (hinv 0) bot_le (hle 0) with h0 | h0
  · exact natReal_ne (hreal 0) h0
  · apply natReal_ne (hreal 1)
    have hdisj := (hind 1).eq_bot
    rw [eq_bot_iff] at hdisj ⊢
    refine le_trans (le_inf le_rfl ?_) hdisj
    refine le_trans (hle 1) (h0.symm.le.trans ?_)
    exact le_iSup₂_of_le (f := fun j (_ : j ≠ (1 : Fin 2)) => I j) 0 (by decide) le_rfl

end Case1ii

section XCases

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem b51_Xq (h : PUHyp M T L) (h51 : AsB51) (hSQ : SQTKQuot) :
    B51Conclusion (ffJ (autI h.isElemAbelian_Xq M)) (autI h.isElemAbelian_Xq L) :=
  (isSecW_Xq h).b51 h h51 hSQ (h.isFFModule_of_le_Xq (isSecW_Xq h))

theorem commXq_inf_centralizer (h : PUHyp M T L) :
    ⁅Xq M, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⁅Xq M, L⁆ ⊓ Zq M L := by
  rw [Zq, ← inf_assoc, inf_eq_left.2 (commutator_Xq_le M L h.L_le)]

theorem isIntDirect_Xq_iff (h : PUHyp M T L) :
    IsIntDirect (commV (autI h.isElemAbelian_Xq L)) (fixV (autI h.isElemAbelian_Xq L)) ⊤ ↔
      (⁅Xq M, L⁆ ⊔ Zq M L = Xq M ∧ ⁅Xq M, L⁆ ⊓ Zq M L = ⊥) := by
  have hX := h.isElemAbelian_Xq
  unfold IsIntDirect
  rw [← C124.toG_inj hX, ← C124.toG_inj hX (W := _ ⊓ _), toG_top]
  have hsup : C124.toG hX (commV (autI hX L) ⊔ fixV (autI hX L)) = ⁅Xq M, L⁆ ⊔ Zq M L := by
    rw [C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, (toG_commV_Xq h), (toG_fixV_Xq h)]
  have hinf : C124.toG hX (commV (autI hX L) ⊓ fixV (autI hX L)) = ⁅Xq M, L⁆ ⊓ Zq M L := by
    rw [C124.toG, Subgroup.map_inf _ _ _ (C124.valHom_injective hX), ← C124.toG, ← C124.toG,
      (toG_commV_Xq h), (toG_fixV_Xq h)]
  rw [hsup, hinf, C124.toG, Subgroup.map_bot]

theorem x_cases (h : PUHyp M T L) (h51 : AsB51) (hSQ : SQTKQuot) (h45 : NoSL45) :
    (IrrSecG L (⁅Xq M, L⁆ ⊓ Zq M L) ⁅Xq M, L⁆ ∧ ⁅Xq M, L⁆ = Uq M T L) ∨
    (B51Case1ii (ffJ (autI h.isElemAbelian_Xq M)) (autI h.isElemAbelian_Xq L) ∧
      ⁅Xq M, L⁆ ⊔ Zq M L = Xq M ∧ ⁅Xq M, L⁆ ⊓ Zq M L = ⊥) := by
  have hX := h.isElemAbelian_Xq
  have hs := (isSecW_Xq h)
  obtain ⟨⟨-, hcases⟩, ⟨-, hP2⟩, -, -, -, -⟩ := (b51_Xq h) h51 hSQ
  rcases hcases with hi | hii | ⟨n, -, hm, π, U₁, U₂, -, h1, -⟩ | ⟨-, n, hn, k, hk1, hkn, I, π, -,
      -, -, hreal⟩
  · have hirr := irrSecG_toG hX (hs.L_le_normalizer h) hi.1.2.2.2
    rw [C124.toG_fixed hX (hs.L_le_normalizer h), (toG_commV_Xq h),
      (commXq_inf_centralizer h)] at hirr
    exact Or.inl ⟨hirr, (commutator_Xq_eq_of_irrSecG h) hirr⟩
  · refine Or.inr ⟨hii, ((isIntDirect_Xq_iff h)).mp ?_⟩
    by_contra hnd
    exact not_isIrrSec_of_case1ii hii (hP2 hnd).1.2.2.2
  · exact (h45 _ (hs.rankTwo h) _ hm (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)).elim
  · exact (h45 _ (hs.rankTwo h) _ hn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))).elim

end XCases

end CFSG.Quasithin.MS93.S32
