module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_iso_of_xSectionIso {L W₁ W₂ : Subgroup G}
    (hL₁ : L ≤ Subgroup.normalizer (W₁ : Set G)) (hL₂ : L ≤ Subgroup.normalizer (W₂ : Set G))
    (h : IsXSectionIso₂ L W₁ ⊥ W₂ ⊥) :
    ∃ j : ↥W₁ ≃* ↥W₂, ∀ l ∈ L, ∀ w w' : ↥W₁, (w' : G) = l * w * l⁻¹ →
      ((j w' : ↥W₂) : G) = l * (j w : G) * l⁻¹ := by
  obtain ⟨hn₁, hn₂, e, he⟩ := h
  let q₁ : ↥W₁ ⧸ (⊥ : Subgroup G).subgroupOf W₁ ≃* ↥W₁ :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := W₁))).trans
      QuotientGroup.quotientBot
  let q₂ : ↥W₂ ⧸ (⊥ : Subgroup G).subgroupOf W₂ ≃* ↥W₂ :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := W₂))).trans
      QuotientGroup.quotientBot
  have hq₁ : ∀ w : ↥W₁, q₁.symm w = (w : ↥W₁ ⧸ (⊥ : Subgroup G).subgroupOf W₁) := fun w =>
    (MulEquiv.symm_apply_eq q₁).mpr rfl
  have hq₂ : ∀ k : ↥W₂, q₂.symm k = (k : ↥W₂ ⧸ (⊥ : Subgroup G).subgroupOf W₂) := fun k =>
    (MulEquiv.symm_apply_eq q₂).mpr rfl
  refine ⟨q₁.symm.trans (e.trans q₂), fun l hl w w' hw' => ?_⟩
  set k : ↥W₂ := q₂ (e (q₁.symm w)) with hk
  have hek : e (w : ↥W₁ ⧸ (⊥ : Subgroup G).subgroupOf W₁) =
      (k : ↥W₂ ⧸ (⊥ : Subgroup G).subgroupOf W₂) := by
    rw [← hq₂, hk, MulEquiv.symm_apply_apply, hq₁]
  have hj : l * (w : G) * l⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hl) w).mp w.2
  have hkm : l * (k : G) * l⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hl) k).mp k.2
  have h1 := he l hl w k hj hkm hek
  have hw'' : w' = ⟨l * w * l⁻¹, hj⟩ := Subtype.ext hw'
  change ((q₂ (e (q₁.symm w')) : ↥W₂) : G) = l * (k : G) * l⁻¹
  rw [hq₁, hw'', h1]
  rfl

variable {K : Type} [Field K]

@[expose] def pr₁ : W6 K →* StdMod (Fin 3) K where
  toFun v := Multiplicative.ofAdd (Multiplicative.toAdd v ∘ Sum.inl)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def pr₂ : W6 K →* StdMod (Fin 3) K where
  toFun v := Multiplicative.ofAdd (Multiplicative.toAdd v ∘ Sum.inr)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem le_normalizer_of_le {W W₁ W₂ : Subgroup G} (hW : IsMulCommutative ↥W) (h₁ : W₁ ≤ W)
    (h₂ : W₂ ≤ W) : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [setLike_mul_comm (h₂ hy) (h₁ hg), mul_inv_cancel_right]
    exact hg
  · have h3 : (y * g * y⁻¹) * y = y * (y * g * y⁻¹) := setLike_mul_comm (h₁ hg) (h₂ hy)
    have e : g = y * g * y⁻¹ := by
      calc g = y⁻¹ * ((y * g * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * g * y⁻¹)) := by rw [h3]
        _ = y * g * y⁻¹ := by group
    rw [e]
    exact hg

theorem exists_sumEquiv {W W₁ W₂ : Subgroup G} (hW : IsElemAbelian 2 W) (h₁ : W₁ ≤ W)
    (h₂ : W₂ ≤ W) (hinf : W₁ ⊓ W₂ = ⊥) (hsup : W₁ ⊔ W₂ = W)
    (e₁ : ↥W₁ ≃* StdMod (Fin 3) K) (j : ↥W₁ ≃* ↥W₂) :
    ∃ Φ : IntMod W hW ≃* W6 K, ∀ v : W6 K,
      (Φ.symm v).val = ((e₁.symm (pr₁ v) : ↥W₁) : G) * ((j (e₁.symm (pr₂ v)) : ↥W₂) : G) := by
  have hc := hW.1
  let a : W6 K → G := fun v => ((e₁.symm (pr₁ v) : ↥W₁) : G)
  let b : W6 K → G := fun v => ((j (e₁.symm (pr₂ v)) : ↥W₂) : G)
  have ha : ∀ v, a v ∈ W := fun v => h₁ (e₁.symm (pr₁ v)).2
  have hb : ∀ v, b v ∈ W := fun v => h₂ (j (e₁.symm (pr₂ v))).2
  have ham : ∀ v v', a (v * v') = a v * a v' := fun v v' => by
    simp only [a, map_mul, Subgroup.coe_mul]
  have hbm : ∀ v v', b (v * v') = b v * b v' := fun v v' => by
    simp only [b, map_mul, Subgroup.coe_mul]
  have hmem : ∀ v, a v * b v ∈ W := fun v => W.mul_mem (ha v) (hb v)
  let f : W6 K →* IntMod W hW :=
    { toFun := fun v => IntMod.mk hW ⟨a v * b v, hmem v⟩
      map_one' := IntMod.val_injective (by
        change a 1 * b 1 = 1
        simp [a, b])
      map_mul' := fun v v' => IntMod.val_injective (by
        change a (v * v') * b (v * v') = (a v * b v) * (a v' * b v')
        rw [ham, hbm]
        calc a v * a v' * (b v * b v') = a v * (a v' * b v) * b v' := by group
          _ = a v * (b v * a v') * b v' := by rw [setLike_mul_comm (ha v') (hb v)]
          _ = a v * b v * (a v' * b v') := by group) }
  have hf : ∀ v, (f v).val = a v * b v := fun v => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h0 : a v * b v = 1 := by
      have := congrArg IntMod.val hv
      rwa [hf] at this
    have hab : a v = (b v)⁻¹ := eq_inv_of_mul_eq_one_left h0
    have hai : a v ∈ W₁ ⊓ W₂ :=
      ⟨(e₁.symm (pr₁ v)).2, hab ▸ W₂.inv_mem (j (e₁.symm (pr₂ v))).2⟩
    rw [hinf, Subgroup.mem_bot] at hai
    have hbi : b v = 1 := by rw [hai, one_mul] at h0; exact h0
    have h3 : pr₁ v = 1 := by
      have : e₁.symm (pr₁ v) = 1 := Subtype.ext hai
      rwa [MulEquiv.map_eq_one_iff] at this
    have h4 : pr₂ v = 1 := by
      have : j (e₁.symm (pr₂ v)) = 1 := Subtype.ext hbi
      rwa [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at this
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i
    · exact congrFun (congrArg Multiplicative.toAdd h3) i
    · exact congrFun (congrArg Multiplicative.toAdd h4) i
  have hsurj : Function.Surjective f := by
    intro w
    have hw : w.val ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by rw [hsup]; exact w.val_mem
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W₁ W₂ (le_normalizer_of_le hc h₁ h₂)]
      at hw
    obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := Set.mem_mul.mp hw
    refine ⟨Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd (e₁ ⟨x₁, hx₁⟩))
      (Multiplicative.toAdd (e₁ (j.symm ⟨x₂, hx₂⟩)))), IntMod.val_injective ?_⟩
    rw [hf, ← hx]
    change ((e₁.symm (e₁ ⟨x₁, hx₁⟩) : ↥W₁) : G) * ((j (e₁.symm (e₁ (j.symm ⟨x₂, hx₂⟩))) : ↥W₂) :
      G) = x₁ * x₂
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, fun v => rfl⟩

theorem congrHom_convI_eq {W W₁ W₂ : Subgroup G} {hW : IsElemAbelian 2 W}
    {e₁ : ↥W₁ ≃* StdMod (Fin 3) K} {j : ↥W₁ ≃* ↥W₂} {Φ : IntMod W hW ≃* W6 K}
    (hΦ : ∀ v : W6 K, (Φ.symm v).val =
      ((e₁.symm (pr₁ v) : ↥W₁) : G) * ((j (e₁.symm (pr₂ v)) : ↥W₂) : G))
    {l : G} (hl : l ∈ Subgroup.normalizer (W : Set G)) {γ : GL (Fin 3) K}
    (he : ∀ u : StdMod (Fin 3) K,
      ((e₁.symm (matAut γ u) : ↥W₁) : G) = l * (e₁.symm u : G) * l⁻¹)
    (hj : ∀ w w' : ↥W₁, (w' : G) = l * w * l⁻¹ → ((j w' : ↥W₂) : G) = l * (j w : G) * l⁻¹) :
    congrHom Φ (convI hW ⟨l, hl⟩) = matAut (dgHom γ) := by
  refine MulEquiv.ext fun v => ?_
  rw [congrHom_apply]
  apply Φ.symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply IntMod.val_injective
  rw [convI_apply_val, hΦ, hΦ]
  have h1 : pr₁ (matAut (dgHom γ) v) = matAut γ (pr₁ v) :=
    congrArg Multiplicative.ofAdd (dgHom_mulVec_inl γ (Multiplicative.toAdd v))
  have h2 : pr₂ (matAut (dgHom γ) v) = matAut γ (pr₂ v) :=
    congrArg Multiplicative.ofAdd (dgHom_mulVec_inr γ (Multiplicative.toAdd v))
  rw [h1, h2, he, hj _ _ (he (pr₂ v))]
  change l * _ * l⁻¹ = _
  group

theorem exists_model {L W : Subgroup G} {n : ℕ} (hW : IsElemAbelian 2 W)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (h : TwoNaturalSum L W n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ Φ : IntMod W hW ≃* W6 K, (autI hW L).map (congrHom Φ) = diagSL K := by
  obtain ⟨W₁, W₂, h₁, h₂, hL₁, hL₂, hinf, hsup, ⟨hc, K, hKf, hKfin, hK, π, hπ⟩, -, hiso⟩ := h
  obtain ⟨e₁, he₁⟩ := exists_mulEquiv_of_realizesVia (StatedSL 3 K) hπ
  obtain ⟨j, hj⟩ := exists_iso_of_xSectionIso hL₁ hL₂ hiso
  obtain ⟨Φ, hΦ⟩ := exists_sumEquiv hW h₁ h₂ hinf hsup e₁ j
  refine ⟨K, hKf, hKfin, hK, Φ, ?_⟩
  have key : ∀ (l : G) (hl : l ∈ L) (γ : ↥(StatedSL 3 K)),
      ((π γ : ↥(autOn L W₁)) : MulAut ↥W₁) = conjAct W₁ ⟨l, hL₁ hl⟩ →
      congrHom Φ (convI hW ⟨l, hLW hl⟩) = matAut (dgHom (γ : GL (Fin 3) K)) := by
    intro l hl γ hγ
    refine congrHom_convI_eq hΦ (hLW hl) (fun u => ?_) (hj l hl)
    have h1 := he₁ γ (e₁.symm u)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : ((π γ : ↥(autOn L W₁)) : MulAut ↥W₁) (e₁.symm u) =
        e₁.symm (matAut (γ : GL (Fin 3) K) u) :=
      (MulEquiv.eq_symm_apply e₁).mpr h1
    rw [← h2, hγ]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe W₁
      (Subgroup.inclusion le_rfl ⟨l, hL₁ hl⟩) _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_autI hW).mp hx
    have hmem : conjAct W₁ ⟨(g : G), hL₁ hgL⟩ ∈ autOn L W₁ := ⟨⟨g, hL₁ hgL⟩, hgL, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨_, hmem⟩
    exact ⟨(γ : ↥(StatedSL 3 K)).1, (γ : ↥(StatedSL 3 K)).2,
      (key g hgL γ (congrArg Subtype.val hγ)).symm⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨g, hgL, hg⟩ := (π ⟨γ, hγ⟩).2
    have hgL' : (g : G) ∈ L := hgL
    exact ⟨convI hW ⟨g, hLW hgL'⟩, convI_mem_autI hW hgL' (hLW hgL'),
      key g hgL' ⟨γ, hγ⟩ hg.symm⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
