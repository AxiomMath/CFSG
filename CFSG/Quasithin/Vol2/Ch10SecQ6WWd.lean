module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WWc
public import CFSG.Quasithin.Vol2.Ch10SecQ6L2b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open CFSG.Open

theorem card_eq_mul_centralizer {W : Type*} [Group W] {Λ : Subgroup (MulAut W)} {S : Type*}
    [Group S] (πs : S ≃* Λ) {E : Subgroup (MulAut W)}
    (hEN : E ≤ Subgroup.normalizer (Λ : Set (MulAut W))) (hEab : IsElemAbelian 2 E) :
    ∃ A : Subgroup (MulAut S), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
      Nat.card E = Nat.card A * Nat.card ↥(E ⊓ Subgroup.centralizer (Λ : Set (MulAut W))) := by
  have hφ : ∀ (e : E) (M : S), (πs ((πs.trans ((conjOn (hEN e.2)).trans πs.symm)) M) :
      MulAut W) = e * πs M * (e : MulAut W)⁻¹ := fun e M => by
    change (πs (πs.symm (conjOn (hEN e.2) (πs M))) : MulAut W) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  let φ : E →* MulAut S :=
    { toFun := fun e => πs.trans ((conjOn (hEN e.2)).trans πs.symm)
      map_one' := MulEquiv.ext fun M => πs.injective (Subtype.ext (by
        rw [hφ]
        simp))
      map_mul' := fun e f => MulEquiv.ext fun M => πs.injective (Subtype.ext (by
        rw [hφ, MulAut.mul_apply, hφ, hφ]
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group)) }
  have hφ' : ∀ (e : E) (M : S), (πs (φ e M) : MulAut W) = e * πs M * (e : MulAut W)⁻¹ := hφ
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩ _ ⟨f, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (hEab.1.is_comm.comm e f)
  · rintro _ ⟨e, rfl⟩
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hEab.2 _ e.2)
  · rw [← Subgroup.card_ker_mul_card_range φ, mul_comm]
    congr 1
    have hker : φ.ker.map E.subtype = E ⊓ Subgroup.centralizer (Λ : Set (MulAut W)) := by
      ext x
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨e.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
        obtain ⟨M, hM⟩ := πs.surjective ⟨l, hl⟩
        have h1 := hφ' e M
        rw [MonoidHom.mem_ker.mp he, MulAut.one_apply, hM] at h1
        change l * e = e * l
        calc l * e = e * l * (e : MulAut W)⁻¹ * e := by rw [← h1]
          _ = e * l := by group
      · rintro ⟨hxE, hxC⟩
        refine ⟨⟨x, hxE⟩, MonoidHom.mem_ker.mpr (MulEquiv.ext fun M =>
          πs.injective (Subtype.ext ?_)), rfl⟩
        rw [hφ', MulAut.one_apply]
        change x * πs M * x⁻¹ = πs M
        rw [← Subgroup.mem_centralizer_iff.mp hxC _ (πs M).2, mul_inv_cancel_right]
    rw [← hker, Subgroup.card_map_of_injective E.subtype_injective]

end C10P06

open C10P06 in
theorem fact12WW : Fact12WW := by
  intro W W₁ _ _ _ _ hW ι hι Λ Λ₁ hnat hres hlift hfaith s hs hsup hinf E hEN hEab
  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hnat
  have hex : ∀ x : Λ, ∃ y : Λ₁, ∀ w, (x : MulAut W) (ι w) = ι ((y : MulAut W₁) w) := fun x => by
    obtain ⟨y, hy, h⟩ := hres x x.2
    exact ⟨⟨y, hy⟩, h⟩
  choose r hr using hex
  have huniq : ∀ (x : Λ) (y : Λ₁), (∀ w, (x : MulAut W) (ι w) = ι ((y : MulAut W₁) w)) →
      r x = y := fun x y hy =>
    Subtype.ext (MulEquiv.ext fun w => hι (by rw [← hr x w, hy w]))
  let rh : Λ →* Λ₁ :=
    { toFun := r
      map_one' := huniq 1 1 fun w => rfl
      map_mul' := fun x x' => huniq _ _ fun w => by
        change (x : MulAut W) ((x' : MulAut W) (ι w)) =
          ι ((r x : MulAut W₁) ((r x' : MulAut W₁) w))
        rw [hr x', hr x] }
  have hrh : Function.Bijective rh := by
    refine ⟨(injective_iff_map_eq_one rh).mpr fun x hx => Subtype.ext (hfaith x x.2 fun w => ?_),
      fun y => ?_⟩
    · rw [hr x w, show r x = 1 from hx]
      rfl
    · obtain ⟨x, hx, h⟩ := hlift y y.2
      exact ⟨⟨x, hx⟩, huniq _ _ h⟩
  let ρ : L3.Γ ≃* Λ :=
    (MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).trans (MulEquiv.ofBijective rh hrh).symm
  let b : W₁ → L3.Vec := fun w => Multiplicative.toAdd (D.β ⟨w, Subgroup.mem_top w⟩)
  have hbadd : ∀ w w', b (w * w') = b w + b w' := fun w w' =>
    congrArg Multiplicative.toAdd (map_mul D.β ⟨w, Subgroup.mem_top w⟩ ⟨w', Subgroup.mem_top w'⟩)
  have hbinj : Function.Injective b := by
    intro w w' h
    have h1 : D.β (⟨w, Subgroup.mem_top w⟩ * (⟨w', Subgroup.mem_top w'⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, show D.β ⟨w, Subgroup.mem_top w⟩ = D.β ⟨w', Subgroup.mem_top w'⟩ from
        Multiplicative.toAdd.injective h]
      exact mul_inv_cancel _
    have h2 := (D.ker_β _).mp h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  have hbij : Function.Bijective b := ⟨hbinj, fun v => by
    obtain ⟨⟨w, hw⟩, h⟩ := D.β_surj (Multiplicative.ofAdd v)
    exact ⟨w, congrArg Multiplicative.toAdd h⟩⟩
  have hequi : ∀ (γ : L3.Γ) (w : W₁), b ((D.π γ : MulAut W₁) w) = L3.act γ (b w) := fun γ w =>
    congrArg Multiplicative.toAdd (D.equi γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _))
  have hlift' : ∀ γ : L3.Γ, ∃ x ∈ Λ, ∀ w w', b w' = L3.act γ (b w) →
      x (ι w) = ι w' := fun γ => by
    obtain ⟨x, hx, h⟩ := hlift (D.π γ) (D.π γ).2
    refine ⟨x, hx, fun w w' hw' => ?_⟩
    rw [h, hbinj (hw'.trans (hequi γ w).symm)]
  have h₁ : L3Emb Λ ι b := ⟨hι, hbadd, hbij, hlift'⟩
  have h₂ : L3Emb Λ ((s : MulAut W).toMonoidHom.comp ι) b := by
    refine ⟨(s : MulAut W).injective.comp hι, hbadd, hbij, fun γ => ?_⟩
    obtain ⟨x, hx, h⟩ := hlift' γ
    refine ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs x).mp hx, fun w w' hw' => ?_⟩
    change (s * x * s⁻¹) (s (ι w)) = s (ι w')
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h w w' hw']
  have hsup' : ι.range ⊔ ((s : MulAut W).toMonoidHom.comp ι).range = ⊤ := by
    rw [MonoidHom.range_comp]
    exact hsup
  have hinf' : ι.range ⊓ ((s : MulAut W).toMonoidHom.comp ι).range = ⊥ := by
    rw [MonoidHom.range_comp]
    exact hinf
  obtain ⟨A, hAc, hA2, hEA⟩ := card_eq_mul_centralizer ρ hEN hEab
  have hC : Nat.card ↥(E ⊓ Subgroup.centralizer (Λ : Set (MulAut W))) ≤ 2 := by
    refine card_le_two_of fun c hc c' hc' hc1 hc'1 => ?_
    obtain ⟨hcE, hcC⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hc'E, hc'C⟩ := Subgroup.mem_inf.mp hc'
    exact eq_of_centralizes_L3 hW h₁ h₂ hsup' hinf'
      (fun x hx => (Subgroup.mem_centralizer_iff.mp hcC x hx).symm)
      (fun x hx => (Subgroup.mem_centralizer_iff.mp hc'C x hx).symm)
      (congrArg Subtype.val (hEab.1.is_comm.comm ⟨c, hcE⟩ ⟨c', hc'E⟩))
      (by rw [← sq]; exact hEab.2 c hcE) (by rw [← sq]; exact hEab.2 c' hc'E) hc1 hc'1
  calc Nat.card E = Nat.card A * Nat.card ↥(E ⊓ Subgroup.centralizer (Λ : Set (MulAut W))) := hEA
    _ ≤ 4 * 2 := Nat.mul_le_mul (card_le_four_aut hAc hA2) hC
    _ = 2 ^ 3 := by norm_num

end CFSG.Quasithin.Vol2.Ch10.SecD
