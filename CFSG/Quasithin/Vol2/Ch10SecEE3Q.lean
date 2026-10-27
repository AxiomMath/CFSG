module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Comm2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem sA_sB_sA_sB : sA * sB * sA * sB = 1 := by decide

theorem mem_fsuVM_of_lifts (hyp : Hyp10 G T L I) {K : Subgroup (MulAut (IntMod (fsuVM T L I)
      (SecA.isElemAbelian_fsuVM hyp)))} (θ : ↥K ≃* Perm (Fin 5))
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {x y : Subgroup.normalizer (fsuVM T L I : Set G)} (hxT : (x : G) ∈ T) (hyT : (y : G) ∈ T)
    (hx : convI (SecA.isElemAbelian_fsuVM hyp) x = ((θ.symm sA : ↥K) : MulAut _))
    (hy : convI (SecA.isElemAbelian_fsuVM hyp) y = ((θ.symm sB : ↥K) : MulAut _)) :
    (x : G) * y * x * y ∈ fsuVM T L I := by
  have h1 : convI (SecA.isElemAbelian_fsuVM hyp) (x * y * x * y) = 1 := by
    rw [map_mul, map_mul, map_mul, hx, hy, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← map_mul, sA_sB_sA_sB, map_one,
      Subgroup.coe_one]
  exact hCV ⟨T.mul_mem (T.mul_mem (T.mul_mem hxT hyT) hxT) hyT,
    (convI_eq_one_iff _ _).mp h1⟩

theorem mem_commV_of_centralizer (hyp : Hyp10 G T L I) {X : Subgroup G}
    {K K' : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))}
    {θ' : ↥K' ≃* Perm (Fin 5)}
    {β' : ↥(commV K') ≃* Multiplicative (evenWeight 5)} (hβ' : A5Equivariant θ' β')
    (htop : commV K ⊔ commV K' = ⊤) (htriv : ∀ φ ∈ K', ∀ u ∈ commV K, φ u = u)
    (hX : oTwoUpper K' = autI (SecA.isElemAbelian_fsuVM hyp) X) {u : G}
    (hu : u ∈ fsuVM T L I) (huX : u ∈ Subgroup.centralizer (X : Set G)) :
    IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨u, hu⟩ ∈ commV K := by
  refine mem_commV_of_fix hβ' htop htriv fun φ hφ => ?_
  rw [hX] at hφ
  obtain ⟨g, hgX, rfl⟩ := (mem_autI _).mp hφ
  refine (convI_fix_iff _ g _).mpr ?_
  have h1 := Subgroup.mem_centralizer_iff.mp huX g hgX
  calc (g : G) * u * (g : G)⁻¹ = u * g * (g : G)⁻¹ := by rw [h1]
    _ = u := by group

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

@[expose] noncomputable def tau (i : Fin 4) :
    MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :=
  ![((D.θ₁.symm sA : ↥D.K₁) : MulAut _), ((D.θ₁.symm sB : ↥D.K₁) : MulAut _),
    ((D.θ₂.symm sA : ↥D.K₂) : MulAut _), ((D.θ₂.symm sB : ↥D.K₂) : MulAut _)] i

theorem tau_zero : D.tau 0 = ((D.θ₁.symm sA : ↥D.K₁) : MulAut _) := rfl

theorem tau_one : D.tau 1 = ((D.θ₁.symm sB : ↥D.K₁) : MulAut _) := rfl

theorem tau_two : D.tau 2 = ((D.θ₂.symm sA : ↥D.K₂) : MulAut _) := rfl

include D

theorem exists_Q
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I) :
    ∃ q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G), (∀ i, (q i : G) ∈ T) ∧
      (∀ i, (q i : G) ^ 2 = 1) ∧ (∀ i j, (q i : G) * q j = q j * q i) ∧
      ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hVab := hV.1
  have hVT := SecA.fsuVM_le_T hyp
  have htop := D.commV_sup_eq_top hC0
  obtain ⟨a₁, ha₁, ha₁2, ha₁θ⟩ :=
    D.exists_lift₁ h113 h37 h38 ht htn h2 hb hC0 hCV (σ := sA) (Or.inl rfl)
  obtain ⟨b₁, hb₁, hb₁2, hb₁θ⟩ :=
    D.exists_lift₁ h113 h37 h38 ht htn h2 hb hC0 hCV (σ := sB) (Or.inr rfl)
  obtain ⟨a₂, ha₂, ha₂2, ha₂θ⟩ :=
    D.exists_lift₂ h113 h37 h38 ht htn h2 hb hC0 hCV (σ := sA) (Or.inl rfl)
  obtain ⟨b₂, hb₂, hb₂2, hb₂θ⟩ :=
    D.exists_lift₂ h113 h37 h38 ht htn h2 hb hC0 hCV (σ := sB) (Or.inr rfl)
  have hc₁ := mem_fsuVM_of_lifts hyp D.θ₁ hCV ha₁.1.1 hb₁.1.1 ha₁θ hb₁θ
  have hc₂ := mem_fsuVM_of_lifts hyp D.θ₂ hCV ha₂.1.1 hb₂.1.1 ha₂θ hb₂θ
  have hcK₁ := mem_commV_of_centralizer hyp D.equiv₂ htop (fun φ hφ u hu => D.triv₂ hφ hu) D.oTwo₂
    hc₁ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₁.2 hb₁.2) ha₁.2) hb₁.2)
  have hcK₂ := mem_commV_of_centralizer hyp D.equiv₁ (by rwa [sup_comm] at htop)
    (fun φ hφ u hu => D.triv₁ hφ hu) D.oTwo₁
    hc₂ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₂.2 hb₂.2) ha₂.2) hb₂.2)
  obtain ⟨v₁, w₁, hw₁, hv₁, hc1⟩ := exists_commuting_pair hV D.equiv₁ ha₁2 hb₁2 ha₁θ hb₁θ hc₁ hcK₁
  obtain ⟨v₂, w₂, hw₂, hv₂, hc2⟩ := exists_commuting_pair hV D.equiv₂ ha₂2 hb₂2 ha₂θ hb₂θ hc₂ hcK₂
  let nv : IntMod (fsuVM T L I) hV → Subgroup.normalizer (fsuVM T L I : Set G) := fun u =>
    ⟨u.val, Subgroup.le_normalizer u.val_mem⟩
  have hnv : ∀ u, convI hV (nv u) = 1 := fun u => (convI_eq_one_iff _ _).mpr
    (Subgroup.mem_centralizer_iff.mpr fun v hv => setLike_mul_comm hv u.val_mem)
  have hfixc : ∀ {x : Subgroup.normalizer (fsuVM T L I : Set G)} {u : IntMod (fsuVM T L I) hV},
      convI hV x u = u → Commute (x : G) u.val := by
    intro x u h
    have h1 := (convI_fix_iff _ x u).mp h
    show (x : G) * u.val = u.val * x
    calc (x : G) * u.val = ((x : G) * u.val * (x : G)⁻¹) * x := by group
      _ = u.val * x := by rw [h1]
  have hcross : ∀ {x y : Subgroup.normalizer (fsuVM T L I : Set G)} {u : ↥(commV D.K₁)}
      {z : ↥(commV D.K₂)},
      (x : G) ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (CFSG.conjugate L t : Set G) →
      convI hV x ∈ D.K₁ → (y : G) ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) →
      convI hV y ∈ D.K₂ → Commute ((x : G) * IntMod.val (u : IntMod (fsuVM T L I) hV))
        ((y : G) * IntMod.val (z : IntMod (fsuVM T L I) hV)) := by
    intro x y u z hx hxK hy hyK
    have hxy : Commute (x : G) y := commute_of_mem_centralizer h37 h38 hyp ht htn hC0 hx hy
    have hxz : Commute (x : G) (IntMod.val (z : IntMod (fsuVM T L I) hV)) :=
      hfixc (D.triv₁ hxK z.2)
    have huy : Commute (IntMod.val (u : IntMod (fsuVM T L I) hV)) y :=
      (hfixc (D.triv₂ hyK u.2)).symm
    have huz : Commute (IntMod.val (u : IntMod (fsuVM T L I) hV))
        (IntMod.val (z : IntMod (fsuVM T L I) hV)) :=
      setLike_mul_comm (IntMod.val_mem _) (IntMod.val_mem _)
    exact (hxy.mul_right hxz).mul_left (huy.mul_right huz)
  have ha₁K : convI hV a₁ ∈ D.K₁ := ha₁θ ▸ (D.θ₁.symm sA).2
  have hb₁K : convI hV b₁ ∈ D.K₁ := hb₁θ ▸ (D.θ₁.symm sB).2
  have ha₂K : convI hV a₂ ∈ D.K₂ := ha₂θ ▸ (D.θ₂.symm sA).2
  have hb₂K : convI hV b₂ ∈ D.K₂ := hb₂θ ▸ (D.θ₂.symm sB).2
  have c02 := hcross (u := w₁) (z := w₂) ha₁ ha₁K ha₂ ha₂K
  have c03 := hcross (u := w₁) (z := v₂) ha₁ ha₁K hb₂ hb₂K
  have c12 := hcross (u := v₁) (z := w₂) hb₁ hb₁K ha₂ ha₂K
  have c13 := hcross (u := v₁) (z := v₂) hb₁ hb₁K hb₂ hb₂K
  have hT : ∀ (x : Subgroup.normalizer (fsuVM T L I : Set G)) (u : IntMod (fsuVM T L I) hV),
      (x : G) ∈ T → ((x * nv u : Subgroup.normalizer (fsuVM T L I : Set G)) : G) ∈ T :=
    fun x u hx => T.mul_mem hx (hVT u.val_mem)
  have hc : ∀ (x : Subgroup.normalizer (fsuVM T L I : Set G)) (u : IntMod (fsuVM T L I) hV),
      convI hV (x * nv u) = convI hV x := fun x u => by rw [map_mul, hnv, mul_one]
  refine ⟨![a₁ * nv w₁, b₁ * nv v₁, a₂ * nv w₂, b₂ * nv v₂], fun i => ?_, fun i => ?_,
    fun i j => ?_, fun i => ?_⟩
  · fin_cases i
    exacts [hT _ _ ha₁.1.1, hT _ _ hb₁.1.1, hT _ _ ha₂.1.1, hT _ _ hb₂.1.1]
  · fin_cases i
    exacts [hw₁, hv₁, hw₂, hv₂]
  · fin_cases i <;> fin_cases j
    exacts [rfl, hc1, c02, c03, hc1.symm, rfl, c12, c13, c02.symm, c12.symm, rfl, hc2,
      c03.symm, c13.symm, hc2.symm, rfl]
  · fin_cases i
    exacts [(hc _ _).trans ha₁θ, (hc _ _).trans hb₁θ, (hc _ _).trans ha₂θ, (hc _ _).trans hb₂θ]

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
