module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NatSum

open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem zmod_two_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
  · left; exact (ZMod.val_eq_zero a).mp (by omega)
  · right; exact (ZMod.val_eq_one (by norm_num) a).mp h

private theorem addMonoidHom_eq_zero_of_equivariant {X W M : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup M] (ρ : X →* LGL 2 W)
    {Z : Submodule (ZMod 2) W}
    (hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤) (x : X) {z₁ : W}
    (hspan : Submodule.span (ZMod 2) ({z₁, ρ x z₁} : Set W) = Z)
    (Λ : W →+ M) (A : X → M → M) (hA : ∀ g, A g 0 = 0)
    (heq : ∀ g w, Λ (ρ g w) = A g (Λ w)) (hz : Λ z₁ = 0) : Λ = 0 := by
  classical
  have hy : Λ (ρ x z₁) = 0 := by rw [heq x z₁, hz, hA x]
  let K : Submodule (ZMod 2) W :=
    { carrier := {w | Λ w = 0}
      add_mem' := by
        intro a b ha hb
        have ha' : Λ a = 0 := ha
        have hb' : Λ b = 0 := hb
        change Λ (a + b) = 0
        rw [map_add, ha', hb', add_zero]
      zero_mem' := by
        change Λ 0 = 0
        rw [map_zero]
      smul_mem' := by
        intro c w hw
        have hw' : Λ w = 0 := hw
        change Λ (c • w) = 0
        rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul, map_zero]
        · rw [one_smul]; exact hw' }
  have hzK : z₁ ∈ K := hz
  have hyK : ρ x z₁ ∈ K := hy
  have hZleK : Z ≤ K := by
    rw [← hspan, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzK, hyK⟩
  have hle : (⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W)) ≤ K := by
    apply iSup_le
    intro g
    rw [Submodule.map_le_iff_le_comap]
    intro z hzZ
    have hz0 : Λ z = 0 := hZleK hzZ
    show Λ (ρ g z) = 0
    rw [heq g z, hz0, hA g]
  have htop : (⊤ : Submodule (ZMod 2) W) ≤ K := by rw [← hgen]; exact hle
  exact AddMonoidHom.ext fun w => htop trivial

theorem false_of_two_projections {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : X →* LGL 2 W)
    {B F : Subgroup X} {Z : Submodule (ZMod 2) W} (hB : B.index = 5)
    (hstab : ∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z) (hFc : Nat.card F = 4)
    (hFZ : ∀ f ∈ F, ∀ z ∈ Z, ρ f z = z) (hZ : Module.finrank (ZMod 2) Z = 2)
    (hreg : ∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0)
    (hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤)
    {K₁ K₂ : Type} [Field K₁] [Field K₂]
    {φ₁ : X →* Matrix.SpecialLinearGroup (Fin 2) K₁}
    {φ₂ : X →* Matrix.SpecialLinearGroup (Fin 2) K₂} (hφ₁ : Function.Injective φ₁)
    (Ψ₁ : W →+ (Fin 2 → K₁)) (Ψ₂ : W →+ (Fin 2 → K₂)) (hΨ₁ : Function.Surjective Ψ₁)
    (heq₁ : ∀ (g : X) (w : W), Ψ₁ (ρ g w) = (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (Ψ₁ w))
    (heq₂ : ∀ (g : X) (w : W), Ψ₂ (ρ g w) = (φ₂ g : Matrix (Fin 2) (Fin 2) K₂).mulVec (Ψ₂ w))
    (T : (Fin 2 → K₂) ≃+ (Fin 2 → K₁))
    (hT : ∀ (g : X) (v : Fin 2 → K₂), T ((φ₂ g : Matrix (Fin 2) (Fin 2) K₂).mulVec v) =
      (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (T v))
    (hne : ∃ w : W, Ψ₁ w = 0 ∧ Ψ₂ w ≠ 0) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXcard : Nat.card X = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hX
  haveI hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  have hBcard : Nat.card B = 12 := by
    have h := Subgroup.card_mul_index (H := B)
    rw [hB, hXcard] at h
    omega
  have h3 : 3 ∣ Nat.card B := by rw [hBcard]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
  have hx3' : orderOf (x : X) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  have hxodd : Odd (orderOf (x : X)) := by rw [hx3']; norm_num
  have hxne : (x : X) ≠ 1 := by
    intro h1
    have h1' : orderOf (x : X) = 1 := by rw [h1, orderOf_one]
    omega
  have hxmem : (x : X) ∈ B := x.2
  have hZpos : 0 < Module.finrank (ZMod 2) Z := by rw [hZ]; norm_num
  obtain ⟨z₁Z, hz₁Zne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hZpos
  set z₁ : W := (z₁Z : W) with hz₁def
  have hz₁ : z₁ ∈ Z := z₁Z.2
  have hz₁0 : z₁ ≠ 0 := by
    intro h
    exact hz₁Zne (Subtype.ext (by simpa [hz₁def] using h))
  set y : W := ρ (x : X) z₁ with hydef
  have hyZ : y ∈ Z := (hstab (x : X)).mp hxmem z₁ hz₁
  have hyne : y ≠ z₁ := by
    intro h
    have hfix : ρ (x : X) z₁ = z₁ := by rw [← hydef]; exact h
    exact hz₁0 (hreg (x : X) hxmem hxodd hxne z₁ hz₁ hfix)
  have hy0 : y ≠ 0 := by
    intro h
    apply hz₁0
    apply (ρ (x : X)).injective
    rw [← hydef, h, map_zero]
  have hli : LinearIndependent (ZMod 2) ![z₁, y] := by
    rw [LinearIndependent.pair_iff' hz₁0]
    intro a
    rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
    · simpa using hy0.symm
    · simpa using hyne.symm
  have hspan : Submodule.span (ZMod 2) ({z₁, ρ (x : X) z₁} : Set W) = Z := by
    have hfin : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({z₁, ρ (x : X) z₁} : Set W)) = 2 := by
      have hrange : Set.range ![z₁, y] = ({z₁, ρ (x : X) z₁} : Set W) := by
        ext v
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp [hydef]
        · rintro (rfl | rfl)
          · exact ⟨0, by simp⟩
          · exact ⟨1, by simp [hydef]⟩
      have hcard := finrank_span_eq_card hli
      rw [hrange] at hcard
      simpa using hcard
    have hle : Submodule.span (ZMod 2) ({z₁, ρ (x : X) z₁} : Set W) ≤ Z := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hz₁, (hstab (x : X)).mp hxmem z₁ hz₁⟩
    apply Submodule.eq_of_le_of_finrank_le hle
    simp [hZ, hfin]
  have hc₀ne : Ψ₁ z₁ ≠ 0 := by
    intro hc0
    have hΨ₁zero : Ψ₁ = 0 :=
      addMonoidHom_eq_zero_of_equivariant (M := Fin 2 → K₁) ρ hgen (x : X) hspan Ψ₁
        (fun g v => (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec v)
        (fun g => Matrix.mulVec_zero _) heq₁ hc0
    have hsingle : (fun i : Fin 2 => if i = 0 then (1 : K₁) else 0) = 0 := by
      obtain ⟨w, hw⟩ := hΨ₁ (fun i : Fin 2 => if i = 0 then (1 : K₁) else 0)
      rw [← hw, hΨ₁zero]
      simp
    have h10 : (1 : K₁) = 0 := by
      have h := congrFun hsingle 0
      simpa using h
    exact one_ne_zero h10
  let Ψ₂' : W →+ (Fin 2 → K₁) := (T : (Fin 2 → K₂) →+ (Fin 2 → K₁)).comp Ψ₂
  have hΨ₂'apply : ∀ w, Ψ₂' w = T (Ψ₂ w) := fun w => rfl
  have hΨ₂'eq : ∀ g w, Ψ₂' (ρ g w) =
      (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (Ψ₂' w) := by
    intro g w
    rw [hΨ₂'apply, hΨ₂'apply, heq₂ g w, hT g (Ψ₂ w)]
  let C : Submodule K₁ (Fin 2 → K₁) :=
    { carrier := {v | ∀ f ∈ F, (φ₁ f : Matrix (Fin 2) (Fin 2) K₁).mulVec v = v}
      add_mem' := by
        intro a b ha hb f hf
        rw [Matrix.mulVec_add, ha f hf, hb f hf]
      zero_mem' := by
        intro f _
        rw [Matrix.mulVec_zero]
      smul_mem' := by
        intro c v hv f hf
        rw [Matrix.mulVec_smul, hv f hf] }
  have hc₀C : Ψ₁ z₁ ∈ C := by
    intro f hf
    have h1 : ρ f z₁ = z₁ := hFZ f hf z₁ hz₁
    calc (φ₁ f : Matrix (Fin 2) (Fin 2) K₁).mulVec (Ψ₁ z₁)
        = Ψ₁ (ρ f z₁) := (heq₁ f z₁).symm
      _ = Ψ₁ z₁ := by rw [h1]
  have hdC : Ψ₂' z₁ ∈ C := by
    intro f hf
    have h1 : ρ f z₁ = z₁ := hFZ f hf z₁ hz₁
    calc (φ₁ f : Matrix (Fin 2) (Fin 2) K₁).mulVec (Ψ₂' z₁)
        = Ψ₂' (ρ f z₁) := (hΨ₂'eq f z₁).symm
      _ = Ψ₂' z₁ := by rw [h1]
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have hFall : ∀ f ∈ F, f = 1 := by
      intro f hf
      have hmat : (φ₁ f : Matrix (Fin 2) (Fin 2) K₁) = 1 := by
        apply Matrix.ext_of_mulVec_single
        intro i
        have hmem : (Pi.single i (1 : K₁)) ∈ C := by rw [hCtop]; trivial
        have hfix := hmem f hf
        rw [hfix, Matrix.one_mulVec]
      have hphi : φ₁ f = φ₁ 1 := by
        rw [map_one]
        exact Subtype.ext hmat
      exact hφ₁ hphi
    have hFbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hFall
    have hcard : Nat.card F = 1 := by rw [hFbot, Subgroup.card_bot]
    omega
  have hCfin : Module.finrank K₁ C ≤ 1 := by
    have hlt : C < ⊤ := lt_top_iff_ne_top.mpr hCne
    have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_top, Module.finrank_fin_fun] at hlt'
    omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hCfin
  obtain ⟨a, ha⟩ := hv ⟨Ψ₁ z₁, hc₀C⟩
  obtain ⟨b, hb⟩ := hv ⟨Ψ₂' z₁, hdC⟩
  have ha0 : a ≠ 0 := by
    intro ha0
    have hval : a • (v : Fin 2 → K₁) = Ψ₁ z₁ := by
      have h := congrArg Subtype.val ha
      simpa using h
    rw [ha0, zero_smul] at hval
    exact hc₀ne hval.symm
  set lam : K₁ := b * a⁻¹ with hlamdef
  have hd_eq : Ψ₂' z₁ = lam • Ψ₁ z₁ := by
    have hbval : b • (v : Fin 2 → K₁) = Ψ₂' z₁ := by
      have h := congrArg Subtype.val hb
      simpa using h
    have hav : a • (v : Fin 2 → K₁) = Ψ₁ z₁ := by
      have h := congrArg Subtype.val ha
      simpa using h
    have hv_eq : (v : Fin 2 → K₁) = a⁻¹ • Ψ₁ z₁ := by
      rw [← hav, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [← hbval, hv_eq, smul_smul, ← hlamdef]
  let Λ : W →+ (Fin 2 → K₁) :=
    AddMonoidHom.mk' (fun w => Ψ₂' w - lam • Ψ₁ w) (by
      intro p q
      simp only [map_add, smul_add]
      abel)
  have hΛapply : ∀ w, Λ w = Ψ₂' w - lam • Ψ₁ w := fun w => rfl
  have hΛeq : ∀ g w, Λ (ρ g w) = (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (Λ w) := by
    intro g w
    rw [hΛapply, hΛapply, hΨ₂'eq g w, heq₁ g w, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hΛz₁ : Λ z₁ = 0 := by
    rw [hΛapply, hd_eq, sub_self]
  have hΛzero : Λ = 0 :=
    addMonoidHom_eq_zero_of_equivariant (M := Fin 2 → K₁) ρ hgen (x : X) hspan Λ
      (fun g v => (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec v)
      (fun g => Matrix.mulVec_zero _) hΛeq hΛz₁
  obtain ⟨w, hw₁, hw₂⟩ := hne
  have hΛw : Λ w = 0 := by rw [hΛzero, AddMonoidHom.zero_apply]
  have hΨ₂'w : Ψ₂' w = 0 := by
    have h := hΛapply w
    rw [hΛw, hw₁, smul_zero, sub_zero] at h
    exact h.symm
  have hTΨ₂ : T (Ψ₂ w) = 0 := by
    rw [← hΨ₂'apply w]
    exact hΨ₂'w
  exact hw₂ (T.injective (by rw [hTΨ₂, map_zero]))

end CFSG.LocalAnalysis.WeakClosure81.NatSum

end
