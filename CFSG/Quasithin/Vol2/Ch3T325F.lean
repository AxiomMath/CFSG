module

public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

section IsoBack

variable {A₁ A₂ : Type*} [Group A₁] [Group A₂] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]
  [MulDistribMulAction A₁ Q₁] [MulDistribMulAction A₂ Q₂]

theorem iso_of_map_injOn (θ : Q₁ →* Q₂) (hθ : ∀ a₁ : A₁, ∃ a₂ : A₂, ∀ x, θ (a₁ • x) = a₂ • θ x)
    {S : Subgroup Q₁} (hS : XMod.IsInv A₁ S) (hinj : ∀ x ∈ S, θ x = 1 → x = 1)
    {L₁ L₂ : Subgroup Q₁} (h₁ : L₁ ≤ S) (h₂ : L₂ ≤ S)
    (h : XMod.Iso A₂ (L₁.map θ) (L₂.map θ)) : XMod.Iso A₁ L₁ L₂ := by
  obtain ⟨φ, hφ⟩ := h
  have hinj' : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := hinj _ (S.mul_mem hx (S.inv_mem hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θ hinj' h₁
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θ hinj' h₂
  refine ⟨e₁.trans (φ.trans e₂.symm), fun a l l' hll' => ?_⟩
  obtain ⟨a₂, ha₂⟩ := hθ a
  have hθl : θ ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q₁) = ((φ (e₁ l) : ↥(L₂.map θ)) : Q₂) := by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have hθl' : θ ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q₁) = ((φ (e₁ l') : ↥(L₂.map θ)) : Q₂) := by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have h1 : a₂ • ((e₁ l : ↥(L₁.map θ)) : Q₂) = ((e₁ l' : ↥(L₁.map θ)) : Q₂) := by
    rw [he₁, he₁, ← ha₂, hll']
  have h2 := hφ a₂ (e₁ l) (e₁ l') h1
  show a • ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q₁) = ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q₁)
  apply hinj' _ (hS a _ (h₂ (e₂.symm (φ (e₁ l))).2)) _ (h₂ (e₂.symm (φ (e₁ l'))).2)
  rw [ha₂, hθl, hθl', h2]

end IsoBack

section IrrPlusUp

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {P Q : Type*} [CommGroup P] [CommGroup Q]
  [MulDistribMulAction G₁ P] [MulDistribMulAction G₂ Q]
  {ι : P →* Q} {X₁ : Subgroup G₁} {X₂ : Subgroup G₂} {W : Subgroup P}

theorem iso_tilde_of_map (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂)
    (hWinv : IsModInv X₁ W) {J₁ J₂ : Subgroup P} (h₁ : J₁ ≤ W) (h₂ : J₂ ≤ W)
    (h : XMod.Iso ↥X₂ (tilde X₂ (W.map ι) (J₁.map ι)) (tilde X₂ (W.map ι) (J₂.map ι))) :
    XMod.Iso ↥X₁ (tilde X₁ W J₁) (tilde X₁ W J₂) := by
  have hle : modFix X₁ W ≤ (modFix X₂ (W.map ι)).comap ι := by
    intro c hc
    rw [Subgroup.mem_comap]
    refine ⟨Subgroup.mem_map_of_mem _ hc.1, fun a => ?_⟩
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    have h1 : a • ι c = ι ((⟨b, hb⟩ : ↥X₁) • c) := (hba c).symm
    rw [h1, hc.2 ⟨b, hb⟩]
  let θ : (P ⧸ modFix X₁ W) →* (Q ⧸ modFix X₂ (W.map ι)) := QuotientGroup.map _ _ ι hle
  have hθmk : ∀ p : P, θ (QuotientGroup.mk p) = QuotientGroup.mk (ι p) := fun p => rfl
  have hθact : ∀ a₁ : ↥X₁, ∃ a₂ : ↥X₂, ∀ x, θ (a₁ • x) = a₂ • θ x := by
    intro b
    obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
    refine ⟨⟨a, ha⟩, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H p =>
      rw [XMod.smul_quotMk, hθmk, hθmk, XMod.smul_quotMk]
      exact congrArg QuotientGroup.mk (hab p)
  have hS : XMod.IsInv ↥X₁ (tilde X₁ W W) := isInv_tilde hWinv
  have hinj : ∀ x ∈ tilde X₁ W W, θ x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.1 hx
    rw [hθmk, QuotientGroup.eq_one_iff] at h1
    have : w ∈ modFix X₁ W := by
      refine ⟨hw, fun b => ?_⟩
      obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
      apply hι
      have h2 : ι (b • w) = ι w := (hab w).trans (h1.2 ⟨a, ha⟩)
      exact h2
    exact (QuotientGroup.eq_one_iff w).2 this
  have hmap : ∀ J : Subgroup P, tilde X₂ (W.map ι) (J.map ι) = (tilde X₁ W J).map θ := by
    intro J
    ext q
    constructor
    · intro hq
      obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hv
      exact ⟨QuotientGroup.mk j, mem_tilde_iff.2 ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, rfl⟩ := mem_tilde_iff.1 hx
      exact mem_tilde_iff.2 ⟨ι j, Subgroup.mem_map_of_mem _ hj, rfl⟩
  rw [hmap, hmap] at h
  exact iso_of_map_injOn θ hθact hS hinj (tilde_mono h₁) (tilde_mono h₂) h

theorem map_mem_irrPlusOn (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂)
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (hT : ActCompat ι T₁ T₂)
    (hTX₁ : T₁ ≤ Subgroup.normalizer (X₁ : Set G₁))
    (hTX₂ : T₂ ≤ Subgroup.normalizer (X₂ : Set G₂))
    (hW : ∀ t ∈ T₁, ∀ w ∈ W, t • w ∈ W) (hWinv : IsModInv X₁ W) {I : Subgroup P}
    (hI : I ∈ IrrPlusOn X₁ W T₁) : I.map ι ∈ IrrPlusOn X₂ (W.map ι) T₂ := by
  have hWq : ∀ t ∈ T₂, ∀ w ∈ W.map ι, t • w ∈ W.map ι := by
    intro t ht w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨b, hb, hbt⟩ := hT.bwd t ht
    rw [← hbt w']
    exact Subgroup.mem_map_of_mem _ (hW b hb w' hw')
  have hIirr : I.map ι ∈ IrrPlus X₂ (W.map ι) :=
    ⟨Subgroup.map_mono hI.1.1, (hX.isIrrPlus_map_iff hι I).2 hI.1.2⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX₂ hWq hIirr).1 ?_
  rintro t ⟨ht, hiso⟩
  obtain ⟨b, hb, hcompat⟩ := hT.bwd t ht
  have e : t • I.map ι = (b • I).map ι := by
    ext q
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hs
      exact ⟨b • i, Subgroup.smul_mem_pointwise_smul i b I hi, hcompat i⟩
    · intro hq
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
      obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x b I).1 hx
      exact ⟨ι i, Subgroup.mem_map_of_mem _ hi, (hcompat i).symm⟩
  have hbI : b • I ≤ W := by
    rintro _ ⟨i, hi, rfl⟩
    exact hW b hb i (hI.1.1 hi)
  rw [e] at hiso
  have hiso' := iso_tilde_of_map hι hX hWinv hbI hI.1.1 hiso
  have hclass := (forall_smul_eq_iff_mem_irrPlusOn hTX₁ hW hI.1).2 hI
  rw [e, hclass b ⟨hb, hiso'⟩]

end IrrPlusUp

end CFSG.Quasithin.H13.T325
