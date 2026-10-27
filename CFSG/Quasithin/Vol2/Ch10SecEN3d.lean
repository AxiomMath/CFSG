module

public import CFSG.Quasithin.Vol2.Ch10SecECoordV
public import CFSG.Quasithin.Vol2.Ch10SecEN3c
public import CFSG.Quasithin.Vol2.Ch10SecEE3Data

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven pact_mul)

@[expose] def wTwo : Fin 5 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1

@[expose] def wFour : Fin 5 → ZMod 2 :=
  Pi.single 0 1 + Pi.single 1 1 + (Pi.single 2 1 + Pi.single 3 1)

theorem isEven_wTwo : isEven wTwo := by decide

theorem isEven_wFour : isEven wFour := by decide

theorem orbit_model : ∀ m : Fin 5 → ZMod 2, isEven m → m ≠ 0 →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ (pact σ m = wTwo ∨ pact σ m = wFour) := by
  decide +kernel

theorem fix_eFour_w : ∀ σ ∈ eFour, pact σ wTwo = wTwo ∧ pact σ wFour = wFour := by
  decide +kernel

theorem pact_wTwo_ne : ∀ σ : Perm (Fin 5), pact σ wTwo ≠ wFour := by
  decide +kernel

theorem wTwo_ne_zero : wTwo ≠ 0 := by decide

theorem wFour_ne_zero : wFour ≠ 0 := by decide

section Coord

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem fix_of_coord (hβ : A5Equivariant θ β) (k : ↥K) (u : ↥(commV K))
    (h : pact (θ k) ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)) :
    (k : MulAut W) (u : W) = u := by
  rw [← coord_apply θ β hβ k u] at h
  have h2 := β.injective (Multiplicative.toAdd.injective (Subtype.ext h))
  exact congrArg Subtype.val h2

theorem symm_mem_oTwoUpper (θ : ↥K ≃* Perm (Fin 5)) {σ : Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) : ((θ.symm σ : ↥K) : MulAut W) ∈ oTwoUpper K := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hσ
  induction hσ using Subgroup.closure_induction with
  | mem c hc =>
    refine mem_oTwoUpper_of_odd (θ.symm c).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc.orderOf]
    decide
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul, Subgroup.coe_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv, Subgroup.coe_inv]; exact Subgroup.inv_mem _ ha

end Coord

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fix_pair_orbit_case2
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    ∃ x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, ∃ y ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆,
      x ≠ 1 ∧ y ≠ 1 ∧ thompsonJ T ≤ Subgroup.centralizer ({x} : Set G) ∧
      thompsonJ T ≤ Subgroup.centralizer ({y} : Set G) ∧
      baum T ≤ Subgroup.centralizer ({x} : Set G) ∧ baum T ≤ Subgroup.centralizer ({y} : Set G) ∧
      (∀ k ∈ CFSG.conjugate L t, k * x * k⁻¹ ≠ y) ∧
      ∀ v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, v ≠ 1 →
        ∃ k ∈ CFSG.conjugate L t, k * v * k⁻¹ = x ∨ k * v * k⁻¹ = y := by
  obtain ⟨D⟩ := exists_case2Data he23 h37 h38 h322 hshape h3228 hyp h2 ht htn hJ
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLtN
  set u₂ : ↥(commV D.K₂) := D.β₂.symm (Multiplicative.ofAdd ⟨wTwo, isEven_wTwo⟩) with hu₂
  set u₄ : ↥(commV D.K₂) := D.β₂.symm (Multiplicative.ofAdd ⟨wFour, isEven_wFour⟩) with hu₄
  have hc₂ : ((Multiplicative.toAdd (D.β₂ u₂) : evenWeight 5) : Fin 5 → ZMod 2) = wTwo := by
    simp [u₂]
  have hc₄ : ((Multiplicative.toAdd (D.β₂ u₄) : evenWeight 5) : Fin 5 → ZMod 2) = wFour := by
    simp [u₄]
  have hJfix : ∀ φ ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T),
      φ (u₂ : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) = u₂ ∧
        φ (u₄ : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) = u₄ := by
    intro φ hφ
    rw [D.thompsonJ_eq] at hφ
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (A := D.P₁) (B := D.P₂)
      (fun a ha b hb => D.comm a ha.1 b hb.1) hφ
    obtain ⟨f2, f4⟩ := fix_eFour_w _ ((D.memP₂ b hb.1).mp hb)
    refine ⟨?_, ?_⟩
    · rw [MulAut.mul_apply, fix_of_coord D.equiv₂ ⟨b, hb.1⟩ u₂ (by rw [hc₂]; exact f2),
        D.triv₁ ha.1 u₂.2]
    · rw [MulAut.mul_apply, fix_of_coord D.equiv₂ ⟨b, hb.1⟩ u₄ (by rw [hc₄]; exact f4),
        D.triv₁ ha.1 u₄.2]
  have hJN : thompsonJ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T).trans (SecA.le_normalizer_fsuVM T L I)
  have hcent : ∀ w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp),
      (∀ φ ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T), φ w = w) →
      thompsonJ T ≤ Subgroup.centralizer ({IntMod.val w} : Set G) := by
    intro w hw j hj
    have h1 := (convI_fix_iff _ ⟨j, hJN hj⟩ w).mp (hw _ (convI_mem_autI _ hj (hJN hj)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc j * IntMod.val w = (j * IntMod.val w * j⁻¹) * j := by group
      _ = IntMod.val w * j := by rw [h1]
  have hS := baum_le_case2 he23 h37 h38 h322 hshape h3228 hyp h2 hJ
  have hSc : ∀ z ∈ fsuVM T L I, thompsonJ T ≤ Subgroup.centralizer ({z} : Set G) →
      baum T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro z hz hJz
    refine hS.trans (sup_le hJz fun c hc => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc.2 z hz).symm
  have hx := (D.mem_commV₂_iff ht _).mp u₂.2
  have hy := (D.mem_commV₂_iff ht _).mp u₄.2
  have hne1 : ∀ (u : ↥(commV D.K₂)) (m : Fin 5 → ZMod 2),
      ((Multiplicative.toAdd (D.β₂ u) : evenWeight 5) : Fin 5 → ZMod 2) = m → m ≠ 0 →
      IntMod.val (u : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) ≠ 1 := by
    intro u m hum hm h1
    apply hm
    have hu1 : u = 1 := Subtype.ext (IntMod.val_injective (h1.trans IntMod.val_one.symm))
    rw [← hum, hu1, map_one, toAdd_one]
    rfl
  have hact : ∀ k (hk : k ∈ CFSG.conjugate L t), ∀ u : ↥(commV D.K₂),
      ∃ (hkK : convI (SecA.isElemAbelian_fsuVM hyp) ⟨k, hLtN hk⟩ ∈ D.K₂),
        ((Multiplicative.toAdd (D.β₂ ⟨convI (SecA.isElemAbelian_fsuVM hyp) ⟨k, hLtN hk⟩ u,
          commV_invariant D.K₂ _ hkK _ u.2⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
          pact (D.θ₂ ⟨_, hkK⟩)
            ((Multiplicative.toAdd (D.β₂ u) : evenWeight 5) : Fin 5 → ZMod 2) := by
    intro k hk u
    have hkK : convI (SecA.isElemAbelian_fsuVM hyp) ⟨k, hLtN hk⟩ ∈ D.K₂ := by
      have h1 := convI_mem_autI (SecA.isElemAbelian_fsuVM hyp) hk (hLtN hk)
      rw [← D.oTwo₂] at h1
      exact oTwoUpper_le _ h1
    exact ⟨hkK, coord_apply D.θ₂ D.β₂ D.equiv₂ ⟨_, hkK⟩ u⟩
  refine ⟨_, hx, _, hy, hne1 u₂ wTwo hc₂ wTwo_ne_zero, hne1 u₄ wFour hc₄ wFour_ne_zero,
    hcent _ fun φ hφ => (hJfix φ hφ).1, hcent _ fun φ hφ => (hJfix φ hφ).2,
    hSc _ (hV2 hx) (hcent _ fun φ hφ => (hJfix φ hφ).1),
    hSc _ (hV2 hy) (hcent _ fun φ hφ => (hJfix φ hφ).2), ?_, ?_⟩
  · intro k hk heq
    obtain ⟨hkK, hk2⟩ := hact k hk u₂
    apply pact_wTwo_ne (D.θ₂ ⟨_, hkK⟩)
    rw [← hc₂, ← hk2, ← hc₄]
    congr 3
    apply Subtype.ext
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact heq
  · intro v hv hv1
    set w : ↥(commV D.K₂) := ⟨IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨v, hV2 hv⟩,
      (D.mem_commV₂_iff ht _).mpr hv⟩
    set m := ((Multiplicative.toAdd (D.β₂ w) : evenWeight 5) : Fin 5 → ZMod 2)
    have hm : m ≠ 0 := fun h0 => hv1 (by
      have h1 : D.β₂ w = 1 := Multiplicative.toAdd.injective (Subtype.ext h0)
      have h2 : w = 1 := D.β₂.injective (h1.trans (map_one _).symm)
      exact congrArg (fun u : ↥(commV D.K₂) =>
        IntMod.val (u : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) h2)
    obtain ⟨σ, hσ, hσm⟩ := orbit_model m (Multiplicative.toAdd (D.β₂ w)).2 hm
    have hk0 := symm_mem_oTwoUpper D.θ₂ (Perm.mem_alternatingGroup.mpr hσ)
    rw [D.oTwo₂] at hk0
    obtain ⟨g, hgL, hg⟩ := (mem_autI _).mp hk0
    refine ⟨g, hgL, ?_⟩
    have hgK : convI (SecA.isElemAbelian_fsuVM hyp) g ∈ D.K₂ := hg ▸ (D.θ₂.symm σ).2
    have hcoord := coord_apply D.θ₂ D.β₂ D.equiv₂ ⟨_, hgK⟩ w
    have hθ : D.θ₂ ⟨_, hgK⟩ = σ := by
      rw [show (⟨_, hgK⟩ : ↥D.K₂) = D.θ₂.symm σ from Subtype.ext hg, MulEquiv.apply_symm_apply]
    rw [hθ] at hcoord
    have hval : ∀ u : ↥(commV D.K₂),
        D.β₂ ⟨convI (SecA.isElemAbelian_fsuVM hyp) g w, commV_invariant D.K₂ _ hgK _ w.2⟩ =
          D.β₂ u → (g : G) * v * (g : G)⁻¹ =
            IntMod.val (u : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) := by
      intro u hu
      have h1 := congrArg (fun z : ↥(commV D.K₂) =>
        IntMod.val (z : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))
        (D.β₂.injective hu)
      simp only at h1
      rw [← h1, convI_apply_val]
      rfl
    rcases hσm with h | h
    · left
      refine hval u₂ (Multiplicative.toAdd.injective (Subtype.ext ?_))
      rw [hcoord, h, hc₂]
    · right
      refine hval u₄ (Multiplicative.toAdd.injective (Subtype.ext ?_))
      rw [hcoord, h, hc₄]

end CFSG.Quasithin.Vol2.Ch10.SecE
