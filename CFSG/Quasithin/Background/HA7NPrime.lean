module

public import CFSG.Quasithin.Background.HS7Perm
public import CFSG.Quasithin.Background.HPairNPrime
public import CFSG.Quasithin.Background.HA7Alpha

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Equiv PairG

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

noncomputable abbrev ι : ↥(alternatingGroup (Fin 7)) →* MulAut (PairMod (Fin 4) (ZMod 2)) :=
  (pairHom (Γ α) (θ α).toMonoidHom).comp (ψ α).toMonoidHom

theorem ι_injective : Function.Injective (ι α) := by
  intro σ τ h
  have h1 := (pairAut_injective h).1
  exact (ψ α).injective (natAut_injective _ h1)

theorem range_ι : (ι α).range = pairA7 α := by
  have h : (ψ α).toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr (ψ α).surjective
  rw [MonoidHom.range_comp, h, ← MonoidHom.range_eq_map]
  rfl

theorem ι_mem (σ : ↥(alternatingGroup (Fin 7))) : ι α σ ∈ pairA7 α := by
  rw [← range_ι]
  exact ⟨σ, rfl⟩

theorem swapAut_conj_ι (σ : ↥(alternatingGroup (Fin 7))) :
    swapAut (Fin 4) (ZMod 2) * ι α σ * (swapAut (Fin 4) (ZMod 2))⁻¹ =
      ι α (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s σ) := by
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [pairHom_apply, pairHom_apply, swapAut_conj_pairAut, ← θ_apply]
  simp only [MulEquiv.coe_toMonoidHom, θ_θ]

theorem ι_mul_swapAut (x : Perm (Fin 7)) (hx : x ∈ alternatingGroup (Fin 7))
    (hx' : s * x * s⁻¹ ∈ alternatingGroup (Fin 7)) :
    ι α ⟨x, hx⟩ * swapAut (Fin 4) (ZMod 2) =
      swapAut (Fin 4) (ZMod 2) * ι α ⟨s * x * s⁻¹, hx'⟩ := by
  have h := swapAut_conj_ι α ⟨s * x * s⁻¹, hx'⟩
  have e : MulAut.conjNormal (H := alternatingGroup (Fin 7)) s ⟨s * x * s⁻¹, hx'⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    change s * (s * x * s⁻¹) * s⁻¹ = x
    have hs : s * s = 1 := swap_mul_self 0 1
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by rw [hs, one_mul, inv_one, mul_one]
  rw [e] at h
  rw [← h, swapAut_inv]
  calc swapAut (Fin 4) (ZMod 2) * ι α ⟨s * x * s⁻¹, hx'⟩ * swapAut (Fin 4) (ZMod 2) *
        swapAut (Fin 4) (ZMod 2) =
      swapAut (Fin 4) (ZMod 2) * ι α ⟨s * x * s⁻¹, hx'⟩ *
        (swapAut (Fin 4) (ZMod 2) * swapAut (Fin 4) (ZMod 2)) := by group
    _ = swapAut (Fin 4) (ZMod 2) * ι α ⟨s * x * s⁻¹, hx'⟩ := by
      rw [swapAut_mul_self, mul_one]

theorem ι_mk_mul (x y : Perm (Fin 7)) (hx : x ∈ alternatingGroup (Fin 7))
    (hy : y ∈ alternatingGroup (Fin 7)) (hxy : x * y ∈ alternatingGroup (Fin 7)) :
    ι α ⟨x, hx⟩ * ι α ⟨y, hy⟩ = ι α ⟨x * y, hxy⟩ := by
  rw [← map_mul]
  rfl

theorem sign_s_mul {σ : Perm (Fin 7)} (h : Perm.sign σ ≠ 1) :
    s * σ ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, map_mul, sign_s]
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    rfl

@[expose] noncomputable def Φfun (σ : Perm (Fin 7)) : MulAut (PairMod (Fin 4) (ZMod 2)) :=
  if h : Perm.sign σ = 1 then ι α ⟨σ, h⟩
    else swapAut (Fin 4) (ZMod 2) * ι α ⟨s * σ, sign_s_mul h⟩

theorem Φfun_of_even {σ : Perm (Fin 7)} (h : Perm.sign σ = 1) : Φfun α σ = ι α ⟨σ, h⟩ :=
  dite_eq_left h

theorem Φfun_of_odd {σ : Perm (Fin 7)} (h : Perm.sign σ ≠ 1) :
    Φfun α σ = swapAut (Fin 4) (ZMod 2) * ι α ⟨s * σ, sign_s_mul h⟩ :=
  dite_eq_right h

theorem Φfun_mul (σ τ : Perm (Fin 7)) : Φfun α (σ * τ) = Φfun α σ * Φfun α τ := by
  have hs : s * s = 1 := swap_mul_self 0 1
  have hconj : ∀ x : Perm (Fin 7), x ∈ alternatingGroup (Fin 7) →
      s * x * s⁻¹ ∈ alternatingGroup (Fin 7) := fun x hx =>
    (alternatingGroup.normal (α := Fin 7)).conj_mem x hx s
  set sw := swapAut (Fin 4) (ZMod 2) with hsw
  by_cases hσ : Perm.sign σ = 1 <;> by_cases hτ : Perm.sign τ = 1
  · have hστ : Perm.sign (σ * τ) = 1 := by rw [map_mul, hσ, hτ, one_mul]
    rw [Φfun_of_even α hστ, Φfun_of_even α hσ, Φfun_of_even α hτ]
    exact (ι_mk_mul α σ τ hσ hτ hστ).symm
  · have hστ : Perm.sign (σ * τ) ≠ 1 := by rw [map_mul, hσ, one_mul]; exact hτ
    rw [Φfun_of_odd α hστ, Φfun_of_even α hσ, Φfun_of_odd α hτ]
    have p5 : s * σ * s⁻¹ * (s * τ) ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup (Fin 7)).mul_mem (hconj σ hσ) (sign_s_mul hτ)
    have e1 := ι_mul_swapAut α σ hσ (hconj σ hσ)
    have e2 := ι_mk_mul α _ _ (hconj σ hσ) (sign_s_mul hτ) p5
    have e3 : (⟨s * σ * s⁻¹ * (s * τ), p5⟩ : ↥(alternatingGroup (Fin 7))) =
        ⟨s * (σ * τ), sign_s_mul hστ⟩ := by
      apply Subtype.ext
      change s * σ * s⁻¹ * (s * τ) = s * (σ * τ)
      group
    calc sw * ι α ⟨s * (σ * τ), sign_s_mul hστ⟩ =
        sw * ι α ⟨s * σ * s⁻¹ * (s * τ), p5⟩ := congrArg (fun z => sw * ι α z) e3.symm
      _ = sw * (ι α ⟨s * σ * s⁻¹, hconj σ hσ⟩ * ι α ⟨s * τ, sign_s_mul hτ⟩) :=
        congrArg (sw * ·) e2.symm
      _ = (sw * ι α ⟨s * σ * s⁻¹, hconj σ hσ⟩) * ι α ⟨s * τ, sign_s_mul hτ⟩ :=
        (mul_assoc _ _ _).symm
      _ = (ι α ⟨σ, hσ⟩ * sw) * ι α ⟨s * τ, sign_s_mul hτ⟩ :=
        congrArg (· * ι α ⟨s * τ, sign_s_mul hτ⟩) e1.symm
      _ = ι α ⟨σ, hσ⟩ * (sw * ι α ⟨s * τ, sign_s_mul hτ⟩) := mul_assoc _ _ _
  · have hστ : Perm.sign (σ * τ) ≠ 1 := by rw [map_mul, hτ, mul_one]; exact hσ
    rw [Φfun_of_odd α hστ, Φfun_of_odd α hσ, Φfun_of_even α hτ]
    have p5 : s * σ * τ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup (Fin 7)).mul_mem (sign_s_mul hσ) hτ
    have e2 := ι_mk_mul α _ _ (sign_s_mul hσ) hτ p5
    have e3 : (⟨s * σ * τ, p5⟩ : ↥(alternatingGroup (Fin 7))) =
        ⟨s * (σ * τ), sign_s_mul hστ⟩ := Subtype.ext (mul_assoc _ _ _)
    calc sw * ι α ⟨s * (σ * τ), sign_s_mul hστ⟩ = sw * ι α ⟨s * σ * τ, p5⟩ :=
        congrArg (fun z => sw * ι α z) e3.symm
      _ = sw * (ι α ⟨s * σ, sign_s_mul hσ⟩ * ι α ⟨τ, hτ⟩) := congrArg (sw * ·) e2.symm
      _ = sw * ι α ⟨s * σ, sign_s_mul hσ⟩ * ι α ⟨τ, hτ⟩ := (mul_assoc _ _ _).symm
  · have hστ : Perm.sign (σ * τ) = 1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
      · exact absurd h1 hσ
      rcases Int.units_eq_one_or (Perm.sign τ) with h2 | h2
      · exact absurd h2 hτ
      rw [map_mul, h1, h2]
      rfl
    rw [Φfun_of_even α hστ, Φfun_of_odd α hσ, Φfun_of_odd α hτ]
    have q : s * (s * σ) * s⁻¹ ∈ alternatingGroup (Fin 7) := hconj _ (sign_s_mul hσ)
    have p5 : s * (s * σ) * s⁻¹ * (s * τ) ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup (Fin 7)).mul_mem q (sign_s_mul hτ)
    have e1 := ι_mul_swapAut α (s * σ) (sign_s_mul hσ) q
    have e2 := ι_mk_mul α _ _ q (sign_s_mul hτ) p5
    have e3 : (⟨s * (s * σ) * s⁻¹ * (s * τ), p5⟩ : ↥(alternatingGroup (Fin 7))) =
        ⟨σ * τ, hστ⟩ := by
      apply Subtype.ext
      change s * (s * σ) * s⁻¹ * (s * τ) = σ * τ
      calc s * (s * σ) * s⁻¹ * (s * τ) = (s * s) * σ * (s⁻¹ * s) * τ := by group
        _ = σ * τ := by rw [hs, inv_mul_cancel, one_mul, mul_one]
    calc ι α ⟨σ * τ, hστ⟩ = ι α ⟨s * (s * σ) * s⁻¹ * (s * τ), p5⟩ := congrArg (ι α) e3.symm
      _ = ι α ⟨s * (s * σ) * s⁻¹, q⟩ * ι α ⟨s * τ, sign_s_mul hτ⟩ := e2.symm
      _ = (sw * sw) * (ι α ⟨s * (s * σ) * s⁻¹, q⟩ * ι α ⟨s * τ, sign_s_mul hτ⟩) := by
        rw [hsw, swapAut_mul_self, one_mul]
      _ = sw * (sw * ι α ⟨s * (s * σ) * s⁻¹, q⟩) * ι α ⟨s * τ, sign_s_mul hτ⟩ := by group
      _ = sw * (ι α ⟨s * σ, sign_s_mul hσ⟩ * sw) * ι α ⟨s * τ, sign_s_mul hτ⟩ :=
        congrArg (fun z => sw * z * ι α ⟨s * τ, sign_s_mul hτ⟩) e1.symm
      _ = sw * ι α ⟨s * σ, sign_s_mul hσ⟩ * (sw * ι α ⟨s * τ, sign_s_mul hτ⟩) := by group

@[expose] noncomputable def Φ : Perm (Fin 7) →* MulAut (PairMod (Fin 4) (ZMod 2)) where
  toFun := Φfun α
  map_one' := by
    rw [Φfun_of_even α (map_one _)]
    exact map_one (ι α)
  map_mul' := Φfun_mul α

theorem Φ_of_even {σ : Perm (Fin 7)} (h : Perm.sign σ = 1) : Φ α σ = ι α ⟨σ, h⟩ :=
  Φfun_of_even α h

theorem Φ_of_odd {σ : Perm (Fin 7)} (h : Perm.sign σ ≠ 1) :
    Φ α σ = swapAut (Fin 4) (ZMod 2) * ι α ⟨s * σ, sign_s_mul h⟩ :=
  Φfun_of_odd α h

theorem swapAut_not_mem : swapAut (Fin 4) (ZMod 2) ∉ pairA7 α := by
  intro h
  obtain ⟨γ, hγ⟩ := h
  have h1 := map_V₁_pairAut (ι := Fin 4) (K := ZMod 2) (natAut (Γ α) γ)
    (natAut (Γ α) ((θ α).toMonoidHom γ))
  rw [← pairHom_apply, hγ, map_V₁_swapAut] at h1
  exact V₁_ne_V₂ (ι := Fin 4) (K := ZMod 2) h1.symm

theorem Φ_injective : Function.Injective (Φ α) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_cases h : Perm.sign σ = 1
  · rw [Φ_of_even α h] at hσ
    have := ι_injective α (hσ.trans (map_one _).symm)
    exact congrArg Subtype.val this
  · rw [Φ_of_odd α h] at hσ
    exfalso
    apply swapAut_not_mem α
    have e : swapAut (Fin 4) (ZMod 2) = (ι α ⟨s * σ, sign_s_mul h⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_left hσ
    rw [e]
    exact Subgroup.inv_mem _ (ι_mem α _)

theorem range_Φ : (Φ α).range = pairNormA7 α := by
  have hsN : swapAut (Fin 4) (ZMod 2) ∈ pairNormA7 α :=
    swapAut_mem_pairNorm (θ α).toMonoidHom (θ_θ α)
  have hιN : ∀ σ, ι α σ ∈ pairNormA7 α := fun σ => pairImg_le_pairNorm _ _ (ι_mem α σ)
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    by_cases h : Perm.sign σ = 1
    · rw [Φ_of_even α h]
      exact hιN _
    · rw [Φ_of_odd α h]
      exact Subgroup.mul_mem _ hsN (hιN _)
  · intro x hx
    rcases map_V₁_eq_or (isNatIrr α) (θ_surjective α) (not_isoMod α) hx with h1 | h1
    · have hx' := mem_pairA7_of_map α hx h1
      rw [← range_ι] at hx'
      obtain ⟨σ, rfl⟩ := hx'
      exact ⟨σ, Φ_of_even α σ.2⟩
    · have hy : swapAut (Fin 4) (ZMod 2) * x ∈ pairNormA7 α := Subgroup.mul_mem _ hsN hx
      have hy1 : (V₁ (Fin 4) (ZMod 2)).map (swapAut (Fin 4) (ZMod 2) * x).toMonoidHom =
          V₁ (Fin 4) (ZMod 2) := by
        rw [PairN.map_mul_toMonoidHom, h1, PairN.map_V₂_swapAut]
      have hy' := mem_pairA7_of_map α hy hy1
      rw [← range_ι] at hy'
      obtain ⟨τ, hτ⟩ := hy'
      have hsτ : Perm.sign (s * (τ : Perm (Fin 7))) ≠ 1 := by
        rw [map_mul, sign_s, Perm.mem_alternatingGroup.mp τ.2]
        decide
      refine ⟨s * τ, ?_⟩
      rw [Φ_of_odd α hsτ]
      have e : (⟨s * (s * (τ : Perm (Fin 7))), sign_s_mul hsτ⟩ :
          ↥(alternatingGroup (Fin 7))) = τ := by
        apply Subtype.ext
        change s * (s * (τ : Perm (Fin 7))) = τ
        have hs : s * s = 1 := swap_mul_self 0 1
        rw [← mul_assoc, hs, one_mul]
      rw [e, hτ, ← mul_assoc, swapAut_mul_self, one_mul]

theorem nPrime_top_seven : E3.nPrime (⊤ : Subgroup (Perm (Fin 7))) = 2 := by
  let e : Perm (Fin 4 ⊕ Fin 3) ≃* Perm (Fin 7) := (finSumFinEquiv (m := 4) (n := 3)).permCongrHom
  have h1 : (⊤ : Subgroup (Perm (Fin 4 ⊕ Fin 3))).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  rw [← h1, nPrime_map_of_injective e.injective]
  exact S7.nPrime_eq_two

theorem nPrime_eq_two
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hX1 : pairA7 α ≤ X) (hX2 : X ≤ pairNormA7 α)
    (hX3 : ∃ x ∈ X, x ∉ pairSub (Fin 4) (ZMod 2)) : E3.nPrime X = 2 := by
  obtain ⟨x, hxX, hx⟩ := hX3
  have hxV := PairN.map_V₁_eq_V₂_of_not_mem (isNatIrr α) (θ_surjective α) (not_isoMod α)
    (hX2 hxX) hx
  have hsN : swapAut (Fin 4) (ZMod 2) ∈ pairNormA7 α :=
    swapAut_mem_pairNorm (θ α).toMonoidHom (θ_θ α)
  have hy1 : (V₁ (Fin 4) (ZMod 2)).map (swapAut (Fin 4) (ZMod 2) * x).toMonoidHom =
      V₁ (Fin 4) (ZMod 2) := by
    rw [PairN.map_mul_toMonoidHom, hxV, PairN.map_V₂_swapAut]
  have hy := mem_pairA7_of_map α (Subgroup.mul_mem _ hsN (hX2 hxX)) hy1
  have hsX : swapAut (Fin 4) (ZMod 2) ∈ X := by
    have : swapAut (Fin 4) (ZMod 2) = (swapAut (Fin 4) (ZMod 2) * x) * x⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (hX1 hy) (Subgroup.inv_mem _ hxX)
  have hXeq : X = (⊤ : Subgroup (Perm (Fin 7))).map (Φ α) := by
    rw [← MonoidHom.range_eq_map, range_Φ]
    refine le_antisymm hX2 ?_
    rw [← range_Φ]
    rintro _ ⟨σ, rfl⟩
    by_cases h : Perm.sign σ = 1
    · rw [Φ_of_even α h]
      exact hX1 (ι_mem α _)
    · rw [Φ_of_odd α h]
      exact Subgroup.mul_mem _ hsX (hX1 (ι_mem α _))
  rw [hXeq, nPrime_map_of_injective (Φ_injective α)]
  exact nPrime_top_seven

end A7

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Equiv PairG

theorem H8_A7Pair_nPrime
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : A7Four H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) (hφM : φ ∈ M) :
    E3.nPrime M = 2 := by
  obtain ⟨α, π, hπ⟩ := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_natural α hπ
  set π' : ↥(Γ α) →* ↥H := π.comp (ψ α).symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp (ψ α).symm.surjective
  have he₁' : ∀ (γ : ↥(Γ α)) (u : ↥V₁) (hu : ((π' γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL (Fin 4) (ZMod 2)) (e₁ u) := by
    intro γ u hu
    have h := he₁ ((ψ α).symm γ) u hu
    have e : rep α ((ψ α).symm γ) = (γ : GL (Fin 4) (ZMod 2)) := by
      rw [← coe_ψ, MulEquiv.apply_symm_apply]
    rw [← e]
    exact h
  obtain ⟨e, he⟩ := PairG.exists_pair_model (θ α).toMonoidHom π' hπ's hU e₁ he₁' (hAut α) hφ
    hinf hsup hniso
  have h1 : pairA7 α ≤ M.map (congrHom e) := (le_of_eq he.symm).trans (Subgroup.map_mono hHM)
  have h2 : M.map (congrHom e) ≤ pairNormA7 α :=
    PairG.map_le_pairNorm (θ α).toMonoidHom e he hMN
  have hV₁ : V₁ ≠ ⊥ := by
    intro h
    have hc := e₁.toEquiv
    rw [h] at hc
    have h3 := Nat.card_congr hc
    rw [Subgroup.card_bot, card_stdMod_four] at h3
    exact absurd h3 (by norm_num)
  have hX3 : ∃ x ∈ M.map (congrHom e), x ∉ pairSub (Fin 4) (ZMod 2) :=
    ⟨congrHom e φ, ⟨φ, hφM, rfl⟩, PairN.congrHom_not_mem_pairSub (isNatIrr α) (θ_surjective α)
      (not_isoMod α) (fun l hl w hw => hU ⟨l, hl⟩ w hw) hV₁ hinf e he (h2 ⟨φ, hφM, rfl⟩)⟩
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq_two α h1 h2 hX3

end A7

end H

end CFSG.Quasithin
