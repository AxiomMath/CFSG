module

public import CFSG.RankThree.PartOne.S12.LA126
public import CFSG.RankThree.PartOne.S12.Sec126g
public import CFSG.RankThree.PartOne.S12.TerminalWeylDet
public import CFSG.RankThree.PartOne.S12.TerminalWeylPerm
import CFSG.RankThree.PartOne.S12.LAFaithful

public section

namespace CFSG.RankThree.PartOne

namespace TerminalLA

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module Equiv

@[expose] def IsRefl {V : Type} [AddCommGroup V] [Module (ZMod 5) V] (t : V ≃ₗ[ZMod 5] V) :
    Prop :=
  orderOf t = 2 ∧ finrank (ZMod 5) (LinearMap.range ((t : V →ₗ[ZMod 5] V) - LinearMap.id)) = 1

variable {V : Type} [AddCommGroup V] [Module (ZMod 5) V]

structure TermData (Γ Y : Subgroup (V ≃ₗ[ZMod 5] V)) (U : Submodule (ZMod 5) V) : Prop where
  dim : finrank (ZMod 5) U + 1 = finrank (ZMod 5) V
  dimU : finrank (ZMod 5) U = 3
  inv : ∀ g ∈ Γ, ∀ b ∈ U, g b ∈ U
  faith : ∀ g ∈ Γ, (∀ b ∈ U, g b = b) → g = 1
  irr : ∀ B' ≤ U, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = U
  noline : ¬ ∃ ℓ : Submodule (ZMod 5) V, finrank (ZMod 5) ℓ = 1 ∧ Disjoint ℓ U ∧
    ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ
  YΓ : Y ≤ Γ
  Yn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y
  Yperf : Group.IsPerfect Y
  Ycent : ∀ g ∈ Γ, (∀ y ∈ Y, g * y = y * g) → ∃ c : ZMod 5, ∀ b ∈ U, g b = c • b

variable {Γ Y : Subgroup (V ≃ₗ[ZMod 5] V)} {U : Submodule (ZMod 5) V}

theorem IsRefl.mul_self {t : V ≃ₗ[ZMod 5] V} (ht : IsRefl t) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := ht.1 ▸ pow_orderOf_eq_one t
  rwa [pow_two] at h2

theorem IsRefl.conj {t : V ≃ₗ[ZMod 5] V} (ht : IsRefl t) (g : V ≃ₗ[ZMod 5] V) :
    IsRefl (g * t * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · have h : orderOf (g * t * g⁻¹) = orderOf t :=
      orderOf_injective (MulAut.conj g : (V ≃ₗ[ZMod 5] V) →* (V ≃ₗ[ZMod 5] V))
        (MulAut.conj g).injective t
    rw [h]
    exact ht.1
  · have hcomp : ((g * t * g⁻¹ : V ≃ₗ[ZMod 5] V) : V →ₗ[ZMod 5] V) - LinearMap.id =
        (g : V →ₗ[ZMod 5] V) ∘ₗ (((t : V →ₗ[ZMod 5] V) - LinearMap.id) ∘ₗ
          (g.symm : V →ₗ[ZMod 5] V)) := by
      ext x
      simp
    have hr1 := LinearMap.range_comp_of_range_eq_top
      ((t : V →ₗ[ZMod 5] V) - LinearMap.id) (LinearEquiv.range g.symm)
    rw [hcomp, LinearMap.range_comp, hr1, LinearEquiv.finrank_map_eq]
    exact ht.2

section Facts

noncomputable abbrev resU (hD : TermData Γ Y U) : Γ →* (U ≃ₗ[ZMod 5] U) :=
  LA126.restrictAut hD.inv

@[expose] noncomputable def detU (hD : TermData Γ Y U) : Γ →* (ZMod 5)ˣ :=
  (LinearEquiv.det : (U ≃ₗ[ZMod 5] U) →* (ZMod 5)ˣ).comp (resU hD)

theorem resU_apply (hD : TermData Γ Y U) (g : Γ) (b : U) :
    ((resU hD g b : U) : V) = (g : V ≃ₗ[ZMod 5] V) b := rfl

theorem exists_move_of_ne_one (hD : TermData Γ Y U) {g : V ≃ₗ[ZMod 5] V} (hg : g ∈ Γ)
    (hg1 : g ≠ 1) : ∃ u ∈ U, g u ≠ u := by
  by_contra hcon
  push Not at hcon
  exact hg1 (hD.faith g hg hcon)

theorem IsRefl.exists_move (hD : TermData Γ Y U) {t : V ≃ₗ[ZMod 5] V} (htΓ : t ∈ Γ)
    (ht : IsRefl t) : ∃ u ∈ U, t u ≠ u := by
  refine exists_move_of_ne_one hD htΓ fun h1 => ?_
  have h2 := ht.2
  have h3 : ((t : V →ₗ[ZMod 5] V) - LinearMap.id) = 0 := by
    ext x
    simp [h1]
  rw [h3, LinearMap.range_zero, finrank_bot] at h2
  exact absurd h2 (by norm_num)

theorem IsRefl.sub_mem (hD : TermData Γ Y U) {t : V ≃ₗ[ZMod 5] V} (htΓ : t ∈ Γ)
    (ht : IsRefl t) : ∀ v, t v - v ∈ U := by
  obtain ⟨u, huU, hu⟩ := ht.exists_move hD htΓ
  set T : V →ₗ[ZMod 5] V := (t : V →ₗ[ZMod 5] V) - LinearMap.id with hT
  have hTu0 : T u ≠ 0 := fun h => hu (sub_eq_zero.mp h)
  have hmemR : T u ∈ LinearMap.range T := LinearMap.mem_range_self T u
  have hTuU : T u ∈ U := U.sub_mem (hD.inv t htΓ u huU) huU
  intro v
  have hv : T v ∈ LinearMap.range T := LinearMap.mem_range_self T v
  have hne : (⟨T u, hmemR⟩ : LinearMap.range T) ≠ 0 := fun h => hTu0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero' _ hne).mp ht.2) ⟨T v, hv⟩
  have h1 : T v = c • T u := (congrArg Subtype.val hc).symm
  show T v ∈ U
  rw [h1]
  exact U.smul_mem c hTuU

end Facts

section Det

theorem detU_of_scalar (hD : TermData Γ Y U) (g : Γ) (c : ZMod 5)
    (h : ∀ b ∈ U, (g : V ≃ₗ[ZMod 5] V) b = c • b) :
    (((detU hD g : (ZMod 5)ˣ)) : ZMod 5) = c ^ 3 := by
  have h1 := TerminalDet.det_of_forall_smul (resU hD g) c (fun x => Subtype.ext (by
    rw [resU_apply, h x x.2]; rfl))
  rw [hD.dimU] at h1
  exact h1

theorem eq_one_of_scalar (hD : TermData Γ Y U) (g : Γ) (c : ZMod 5)
    (h : ∀ b ∈ U, (g : V ≃ₗ[ZMod 5] V) b = c • b) (h1 : detU hD g = 1) : g = 1 := by
  have h3 : c ^ 3 = 1 := by
    have h4 := detU_of_scalar hD g c h
    rw [h1] at h4
    simpa using h4.symm
  have key : ∀ c : ZMod 5, c ^ 3 = 1 → c = 1 := by decide
  have hc : c = 1 := key c h3
  exact Subtype.ext (hD.faith g g.2 (fun b hb => by rw [h b hb, hc, one_smul]))

theorem IsRefl.detU [Module.Finite (ZMod 5) V] (hD : TermData Γ Y U) {t : V ≃ₗ[ZMod 5] V}
    (htΓ : t ∈ Γ) (ht : IsRefl t) :
    TerminalLA.detU hD ⟨t, htΓ⟩ = -1 := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  set s := resU hD ⟨t, htΓ⟩ with hs
  have hss : s * s = 1 := by
    rw [hs, ← map_mul]
    have h3 : (⟨t, htΓ⟩ * ⟨t, htΓ⟩ : Γ) = 1 := Subtype.ext ht.mul_self
    rw [h3, map_one]
  refine TerminalDet.det_neg_one_of_rank_one s hss h2 ?_
  obtain ⟨u, huU, hu⟩ := ht.exists_move hD htΓ
  set Ts : U →ₗ[ZMod 5] U := (s : U →ₗ[ZMod 5] U) - LinearMap.id with hTs
  set T : V →ₗ[ZMod 5] V := (t : V →ₗ[ZMod 5] V) - LinearMap.id with hT
  have hsub : (LinearMap.range Ts).map U.subtype ≤ LinearMap.range T := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(x : V), rfl⟩
  have hle : finrank (ZMod 5) (LinearMap.range Ts) ≤ 1 := by
    calc finrank (ZMod 5) (LinearMap.range Ts)
        = finrank (ZMod 5) ((LinearMap.range Ts).map U.subtype) :=
          LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype _)
      _ ≤ finrank (ZMod 5) (LinearMap.range T) := Submodule.finrank_mono hsub
      _ = 1 := ht.2
  have hne : LinearMap.range Ts ≠ ⊥ := by
    intro h
    apply hu
    have h3 : Ts ⟨u, huU⟩ = 0 := by
      have hmem : Ts ⟨u, huU⟩ ∈ LinearMap.range Ts := LinearMap.mem_range_self _ _
      rw [h] at hmem
      exact (Submodule.mem_bot _).mp hmem
    have h5 := congrArg Subtype.val h3
    exact sub_eq_zero.mp h5
  have hpos : 0 < finrank (ZMod 5) (LinearMap.range Ts) := by
    rcases Nat.eq_zero_or_pos (finrank (ZMod 5) (LinearMap.range Ts)) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hne
    · exact h
  omega

theorem Y_sub_mem [Module.Finite (ZMod 5) V] (hD : TermData Γ Y U) {y : V ≃ₗ[ZMod 5] V}
    (hy : y ∈ Y) : ∀ v, y v - v ∈ U :=
  LA126.perfect_le_quotientKernel hD.dim hD.inv hD.YΓ hD.Yperf hy

theorem detU_Y (hD : TermData Γ Y U) (y : Γ) (hy : (y : V ≃ₗ[ZMod 5] V) ∈ Y) :
    detU hD y = 1 := by
  have hP : Group.IsPerfect Y := hD.Yperf
  let f : Y →* (ZMod 5)ˣ := (detU hD).comp (Subgroup.inclusion hD.YΓ)
  have h1 : commutator Y ≤ f.ker := Abelianization.commutator_subset_ker f
  have h3 : (⟨y, hy⟩ : Y) ∈ f.ker := h1 (hP.commutator_eq_top ▸ Subgroup.mem_top _)
  exact h3

theorem exists_pi (hD : TermData Γ Y U) (e : Y ≃* alternatingGroup (Fin 5)) :
    ∃ π : Γ →* Perm (Fin 5),
      (∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ y : Γ, π y = σ ∧ (y : V ≃ₗ[ZMod 5] V) ∈ Y) ∧
      (∀ g : Γ, π g = 1 → ∃ c : ZMod 5, ∀ b ∈ U, (g : V ≃ₗ[ZMod 5] V) b = c • b) := by
  obtain ⟨π, hπY, hπK⟩ := TerminalPerm.exists_pi_of_equiv e hD.YΓ hD.Yn
  refine ⟨π, fun σ hσ => ?_, fun g hg => hD.Ycent g g.2 (hπK g hg)⟩
  let a : alternatingGroup (Fin 5) := ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
  let y₀ : Y := e.symm a
  refine ⟨⟨y₀, hD.YΓ y₀.2⟩, ?_, y₀.2⟩
  have h1 := hπY y₀ y₀.2
  have h2 : e ⟨(y₀ : V ≃ₗ[ZMod 5] V), y₀.2⟩ = a := e.apply_symm_apply a
  rw [h2] at h1
  exact h1

end Det

section Central

variable [Module.Finite (ZMod 5) V]

omit [Module.Finite (ZMod 5) V] in
theorem exists_not_mem_U (hD : TermData Γ Y U) : ∃ v : V, v ∉ U := by
  by_contra h
  push Not at h
  have hU : U = ⊤ := eq_top_iff.mpr fun v _ => h v
  have h2 : finrank (ZMod 5) U = finrank (ZMod 5) V := by rw [hU]; exact finrank_top _ _
  have h3 := hD.dim
  omega

theorem neg_on_U_cases (hD : TermData Γ Y U) {z : V ≃ₗ[ZMod 5] V} (hzΓ : z ∈ Γ)
    (hzz : z * z = 1) (hneg : ∀ b ∈ U, z b = -b) :
    (∀ v, z v - v ∈ U) ∨ (∀ v, z v + v ∈ U) := by
  obtain ⟨μ, hμ⟩ := LAFaithful.exists_scalar_of_stabilizes hD.dim (hD.inv z hzΓ)
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_U hD
  have hμ2 : μ * μ = 1 := by
    by_contra hne
    apply hv₀
    set w := z v₀ - μ • v₀ with hw
    have hwU : w ∈ U := hμ v₀
    have hzw : z w = -w := hneg w hwU
    have hz2 : z (z v₀) = v₀ := by simpa using congrArg (fun t : V ≃ₗ[ZMod 5] V => t v₀) hzz
    have hzv : z v₀ = μ • v₀ + w := by rw [hw]; abel
    have e1 : z (z v₀) = (μ * μ) • v₀ + (μ - 1) • w := by
      rw [hzv, map_add, map_smul, hzw, hzv, smul_add, smul_smul, sub_smul, one_smul]
      abel
    have h1 : (1 - μ * μ) • v₀ = (μ - 1) • w := by
      rw [hz2] at e1
      rw [sub_smul, one_smul]
      exact sub_eq_of_eq_add' e1
    have hne' : (1 - μ * μ) ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
    have h2 : v₀ = (1 - μ * μ)⁻¹ • ((μ - 1) • w) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hne', one_smul]
    rw [h2]
    exact U.smul_mem _ (U.smul_mem _ hwU)
  have key : ∀ μ : ZMod 5, μ * μ = 1 → μ = 1 ∨ μ = -1 := by decide
  rcases key μ hμ2 with h | h
  · left
    intro v
    have := hμ v
    rwa [h, one_smul] at this
  · right
    intro v
    have := hμ v
    rwa [h, neg_smul, one_smul, sub_neg_eq_add] at this

theorem false_of_neg_central (hD : TermData Γ Y U) {z : V ≃ₗ[ZMod 5] V} (hzΓ : z ∈ Γ)
    (hzz : z * z = 1) (hneg : ∀ b ∈ U, z b = -b) (hμ : ∀ v, z v - v ∈ U) : False := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have hcent := Sec126g.central_of_neg hD.inv hD.faith hzΓ hzz hneg
  set ℓ : Submodule (ZMod 5) V := LinearMap.ker ((z : V →ₗ[ZMod 5] V) - LinearMap.id) with hℓ
  have hℓmem : ∀ x, x ∈ ℓ ↔ z x = x := fun x => by simp [hℓ, sub_eq_zero]
  have hdisj : Disjoint ℓ U := by
    rw [Submodule.disjoint_def]
    intro x hxℓ hxU
    have h1 : z x = x := (hℓmem x).mp hxℓ
    have h3 : z x = -x := hneg x hxU
    have h4 : (2 : ZMod 5) • x = 0 := by
      rw [two_smul]
      calc x + x = z x + x := by rw [h1]
        _ = -x + x := by rw [h3]
        _ = 0 := neg_add_cancel x
    exact (smul_eq_zero.mp h4).resolve_left h2
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_U hD
  have hz2 : z (z v₀) = v₀ := by simpa using congrArg (fun t : V ≃ₗ[ZMod 5] V => t v₀) hzz
  have hxℓ : v₀ + z v₀ ∈ ℓ := by
    rw [hℓmem, map_add, hz2, add_comm]
  have hx0 : v₀ + z v₀ ≠ 0 := by
    intro h0
    apply hv₀
    have h5 : (2 : ZMod 5) • v₀ = (v₀ + z v₀) - (z v₀ - v₀) := by rw [two_smul]; abel
    have h6 : (2 : ZMod 5) • v₀ ∈ U := by
      rw [h5, h0, zero_sub]
      exact U.neg_mem (hμ v₀)
    have h7 := U.smul_mem ((2 : ZMod 5)⁻¹) h6
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at h7
  have hℓ1 : finrank (ZMod 5) ℓ = 1 := by
    have hle : finrank (ZMod 5) ℓ ≤ 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq ℓ U
      rw [disjoint_iff.mp hdisj, finrank_bot] at h1
      have h2' := Submodule.finrank_le (ℓ ⊔ U)
      have h3 := hD.dim
      omega
    have hpos : 0 < finrank (ZMod 5) ℓ :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hxℓ⟩, fun h => hx0 (congrArg Subtype.val h)⟩
    omega
  refine hD.noline ⟨ℓ, hℓ1, hdisj, fun g hg x hx => ?_⟩
  rw [hℓmem] at hx ⊢
  have h8 := congrArg (fun t : V ≃ₗ[ZMod 5] V => t x) (hcent g hg)
  simp only [LinearEquiv.mul_apply] at h8
  rw [← h8, hx]

end Central

section Swap

variable [Module.Finite (ZMod 5) V]

theorem isSwap_of_refl (hD : TermData Γ Y U) {π : Γ →* Perm (Fin 5)}
    (hπA : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ y : Γ, π y = σ ∧ (y : V ≃ₗ[ZMod 5] V) ∈ Y)
    (hπK : ∀ g : Γ, π g = 1 → ∃ c : ZMod 5, ∀ b ∈ U, (g : V ≃ₗ[ZMod 5] V) b = c • b)
    {t : V ≃ₗ[ZMod 5] V} (htΓ : t ∈ Γ) (ht : IsRefl t) : (π ⟨t, htΓ⟩).IsSwap := by
  set σ := π ⟨t, htΓ⟩ with hσ
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have h3 : (⟨t, htΓ⟩ * ⟨t, htΓ⟩ : Γ) = 1 := Subtype.ext ht.mul_self
    rw [h3, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  swap
  · exact TerminalPerm.isSwap_of_odd_involution σ hσσ hs
  exfalso
  obtain ⟨y, hy, hyY⟩ := hπA σ hs
  have hπg : π (⟨t, htΓ⟩ * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hy, ← hσ, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hπK _ hπg
  have hinvapp : ∀ (f : V ≃ₗ[ZMod 5] V) (x : V), f⁻¹ (f x) = x := fun f x => f.symm_apply_apply x
  have ht1 : ∀ u ∈ U, t u = c • (y : V ≃ₗ[ZMod 5] V) u := by
    intro u hu
    have hyu : (y : V ≃ₗ[ZMod 5] V) u ∈ U := hD.inv y y.2 u hu
    have h1 := hc ((y : V ≃ₗ[ZMod 5] V) u) hyu
    have h2 : ((⟨t, htΓ⟩ * y⁻¹ : Γ) : V ≃ₗ[ZMod 5] V) = t * (y : V ≃ₗ[ZMod 5] V)⁻¹ := rfl
    rw [h2, LinearEquiv.mul_apply, hinvapp] at h1
    exact h1
  have hc0 : c ≠ 0 := by
    intro h0
    have hUbot : U = ⊥ := by
      refine eq_bot_iff.mpr fun u hu => (Submodule.mem_bot _).mpr ?_
      have h1 := ht1 u hu
      rw [h0, zero_smul] at h1
      exact t.injective (by rw [h1, map_zero])
    have h3 := hD.dimU
    rw [hUbot, finrank_bot] at h3
    omega
  have hy2 : ∀ u ∈ U, (c * c) • (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) u) = u := by
    intro u hu
    have hyu : (y : V ≃ₗ[ZMod 5] V) u ∈ U := hD.inv y y.2 u hu
    have e1 : t (t u) = u := by simpa using congrArg (fun f : V ≃ₗ[ZMod 5] V => f u) ht.mul_self
    have e2 : t (t u) = (c * c) • (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) u) := by
      rw [ht1 u hu, map_smul, ht1 _ hyu, smul_smul]
    rw [← e2, e1]
  have hcc0 : c * c ≠ 0 := mul_ne_zero hc0 hc0
  have hscal : ∀ b ∈ U, ((y * y : Γ) : V ≃ₗ[ZMod 5] V) b = (c * c)⁻¹ • b := by
    intro b hb
    have h1 := hy2 b hb
    show (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) b) = _
    calc (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) b)
        = (c * c)⁻¹ • ((c * c) • (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) b)) := by
          rw [smul_smul, inv_mul_cancel₀ hcc0, one_smul]
      _ = (c * c)⁻¹ • b := by rw [h1]
  have hdy : detU hD y = 1 := detU_Y hD y hyY
  have hcc1 : c * c = 1 := by
    have h1 := detU_of_scalar hD (y * y) ((c * c)⁻¹) hscal
    rw [map_mul, hdy, mul_one] at h1
    have h2 : ((c * c)⁻¹) ^ 3 = 1 := by
      rw [← h1]
      simp
    have h3 : (c * c) ^ 3 = 1 := by
      rw [inv_pow] at h2
      exact inv_eq_one.mp h2
    have key : ∀ c : ZMod 5, (c * c) ^ 3 = 1 → c * c = 1 := by decide
    exact key c h3
  have hyy : (y : V ≃ₗ[ZMod 5] V) * y = 1 := by
    refine hD.faith _ (Γ.mul_mem y.2 y.2) fun b hb => ?_
    have h1 := hscal b hb
    rw [hcc1, inv_one, one_smul] at h1
    exact h1
  have hyyapp : ∀ b, (y : V ≃ₗ[ZMod 5] V) ((y : V ≃ₗ[ZMod 5] V) b) = b := fun b => by
    simpa using congrArg (fun f : V ≃ₗ[ZMod 5] V => f b) hyy
  have key2 : ∀ c : ZMod 5, c * c = 1 → c = 1 ∨ c = -1 := by decide
  rcases key2 c hcc1 with hc1 | hc1
  ·
    have hres : resU hD ⟨t, htΓ⟩ = resU hD y := LinearEquiv.ext fun b => Subtype.ext (by
      rw [resU_apply, resU_apply]
      have h1 := ht1 b b.2
      rw [hc1, one_smul] at h1
      exact h1)
    have h1 : detU hD ⟨t, htΓ⟩ = detU hD y := by
      simp only [detU, MonoidHom.comp_apply, hres]
    rw [ht.detU hD htΓ, hdy] at h1
    exact absurd h1 (by decide)
  ·
    have hzΓ : t * (y : V ≃ₗ[ZMod 5] V) ∈ Γ := Γ.mul_mem htΓ y.2
    have hzneg : ∀ b ∈ U, (t * (y : V ≃ₗ[ZMod 5] V)) b = -b := by
      intro b hb
      have hyb : (y : V ≃ₗ[ZMod 5] V) b ∈ U := hD.inv y y.2 b hb
      rw [LinearEquiv.mul_apply, ht1 _ hyb, hc1, neg_smul, one_smul, hyyapp]
    have hzz : (t * (y : V ≃ₗ[ZMod 5] V)) * (t * (y : V ≃ₗ[ZMod 5] V)) = 1 := by
      refine hD.faith _ (Γ.mul_mem hzΓ hzΓ) fun b hb => ?_
      rw [LinearEquiv.mul_apply, hzneg b hb, map_neg, hzneg b hb, neg_neg]
    rcases neg_on_U_cases hD hzΓ hzz hzneg with h1 | h1
    · exact false_of_neg_central hD hzΓ hzz hzneg h1
    · have h2 : (2 : ZMod 5) ≠ 0 := by decide
      have hzV : ∀ v, (t * (y : V ≃ₗ[ZMod 5] V)) v = -v := by
        intro v
        have hw := h1 v
        have hzw := hzneg _ hw
        rw [map_add] at hzw
        have hz2 : (t * (y : V ≃ₗ[ZMod 5] V)) ((t * (y : V ≃ₗ[ZMod 5] V)) v) = v := by
          simpa using congrArg (fun f : V ≃ₗ[ZMod 5] V => f v) hzz
        rw [hz2] at hzw
        have hx : (t * (y : V ≃ₗ[ZMod 5] V)) v + v = -((t * (y : V ≃ₗ[ZMod 5] V)) v + v) := by
          calc (t * (y : V ≃ₗ[ZMod 5] V)) v + v = v + (t * (y : V ≃ₗ[ZMod 5] V)) v := add_comm _ _
            _ = -((t * (y : V ≃ₗ[ZMod 5] V)) v + v) := hzw
        have h3 : (2 : ZMod 5) • ((t * (y : V ≃ₗ[ZMod 5] V)) v + v) = 0 := by
          rw [two_smul]
          exact eq_neg_iff_add_eq_zero.mp hx
        have h4 : (t * (y : V ≃ₗ[ZMod 5] V)) v + v = 0 := (smul_eq_zero.mp h3).resolve_left h2
        exact eq_neg_of_add_eq_zero_left h4
      have htv : ∀ v, t v = -((y : V ≃ₗ[ZMod 5] V)⁻¹ v) := by
        intro v
        calc t v = ((t * (y : V ≃ₗ[ZMod 5] V)) * (y : V ≃ₗ[ZMod 5] V)⁻¹) v := by
              rw [mul_inv_cancel_right]
          _ = -((y : V ≃ₗ[ZMod 5] V)⁻¹ v) := by rw [LinearEquiv.mul_apply, hzV]
      obtain ⟨v₀, hv₀⟩ := exists_not_mem_U hD
      have hA := ht.sub_mem hD htΓ v₀
      have hB := Y_sub_mem hD (Y.inv_mem hyY) v₀
      rw [htv v₀] at hA
      have hC : (2 : ZMod 5) • v₀ ∈ U := by
        have h5 := U.neg_mem (U.add_mem hA hB)
        have e : -((-((y : V ≃ₗ[ZMod 5] V)⁻¹ v₀) - v₀) + ((y : V ≃ₗ[ZMod 5] V)⁻¹ v₀ - v₀)) =
            (2 : ZMod 5) • v₀ := by
          rw [two_smul]
          abel
        rwa [e] at h5
      apply hv₀
      have h7 := U.smul_mem ((2 : ZMod 5)⁻¹) hC
      rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at h7

end Swap

@[expose] def reflSet (Γ : Subgroup (V ≃ₗ[ZMod 5] V)) : Set (V ≃ₗ[ZMod 5] V) :=
  {t | t ∈ Γ ∧ IsRefl t}

section Assembly

variable [Module.Finite (ZMod 5) V]

omit [Module.Finite (ZMod 5) V] in
theorem closure_reflSet_normal (hconj : ∀ g ∈ Γ, ∀ t ∈ reflSet Γ, g * t * g⁻¹ ∈ reflSet Γ) :
    ∀ g ∈ Γ, ∀ y ∈ Subgroup.closure (reflSet Γ), g * y * g⁻¹ ∈ Subgroup.closure (reflSet Γ) := by
  intro g hg y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hconj g hg x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem fixed_vectors_zero (hD : TermData Γ Y U) {t₀ : V ≃ₗ[ZMod 5] V} (ht₀ : t₀ ∈ reflSet Γ)
    (hconj : ∀ g ∈ Γ, ∀ t ∈ reflSet Γ, g * t * g⁻¹ ∈ reflSet Γ) :
    ∀ x : V, (∀ t ∈ reflSet Γ, t x = x) → x = 0 := by
  intro x hx
  by_contra hx0
  set Y' : Subgroup (V ≃ₗ[ZMod 5] V) := Subgroup.closure (reflSet Γ) with hY'
  have hY'Γ : Y' ≤ Γ := (Subgroup.closure_le Γ).mpr fun t ht => ht.1
  have hY'n := closure_reflSet_normal hconj
  have hxY' : ∀ y ∈ Y', y x = x := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hx t ht
    | one => rfl
    | mul a b _ _ ha hb => rw [LinearEquiv.mul_apply, hb, ha]
    | inv a _ ha =>
      have h1 : (a⁻¹ : V ≃ₗ[ZMod 5] V) (a x) = x := (a.symm_apply_apply x)
      rw [ha] at h1
      exact h1
  have hY'1 : Y' ≠ ⊥ := by
    intro h
    have h1 : t₀ ∈ Y' := Subgroup.subset_closure ht₀
    rw [h, Subgroup.mem_bot] at h1
    have h2 := ht₀.2.2
    have h3 : ((t₀ : V →ₗ[ZMod 5] V) - LinearMap.id) = 0 := by
      ext v
      simp [h1]
    rw [h3, LinearMap.range_zero, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  have hxU : x ∉ U := by
    intro hxU
    have hCU : Sec126g.fixedSpace Y' ⊓ U = ⊥ := by
      rcases hD.irr (Sec126g.fixedSpace Y' ⊓ U) inf_le_right
        (fun g hg b hb => ⟨Sec126g.fixedSpace_invariant hY'n hg hb.1, hD.inv g hg b hb.2⟩) with
        h | h
      · exact h
      · exfalso
        have h1 : t₀ = 1 := hD.faith t₀ ht₀.1 fun b hb => (inf_eq_right.mp h hb) t₀
          (Subgroup.subset_closure ht₀)
        have h2 := ht₀.2.2
        have h3 : ((t₀ : V →ₗ[ZMod 5] V) - LinearMap.id) = 0 := by
          ext v
          simp [h1]
        rw [h3, LinearMap.range_zero, finrank_bot] at h2
        exact absurd h2 (by norm_num)
    have hmem : x ∈ Sec126g.fixedSpace Y' ⊓ U := ⟨hxY', hxU⟩
    rw [hCU] at hmem
    exact hx0 ((Submodule.mem_bot _).mp hmem)
  exact hD.noline (Sec126g.exists_line_of_fixed hD.dim hD.inv hD.irr hD.faith hY'Γ hY'n hY'1 hxU
    hxY')

theorem terminal_weyl_linear (hD : TermData Γ Y U) (e : Y ≃* alternatingGroup (Fin 5))
    {Λ : Subgroup (V ≃ₗ[ZMod 5] V)} (hΛΓ : Λ ≤ Γ) (hΛ : Nonempty (Λ ≃* Perm (Fin 4)))
    (hΛgen : Λ = Subgroup.closure {t | t ∈ Λ ∧ IsRefl t}) :
    ∃ ψ : ↥(Subgroup.closure (reflSet Γ)) ≃* Perm (Fin 5),
      (∀ (t : V ≃ₗ[ZMod 5] V) (ht : t ∈ reflSet Γ),
        (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap) ∧
      (∀ σ : Perm (Fin 5), σ.IsSwap → ∃ (t : V ≃ₗ[ZMod 5] V) (ht : t ∈ reflSet Γ),
        ψ ⟨t, Subgroup.subset_closure ht⟩ = σ) ∧
      (∀ x : V, (∀ t ∈ reflSet Γ, t x = x) → x = 0) ∧
      ∃ k : Fin 5, ∀ x ∈ Λ, ∃ h : x ∈ Subgroup.closure (reflSet Γ), ψ ⟨x, h⟩ k = k := by
  have hRΓ : reflSet Γ ⊆ (Γ : Set (V ≃ₗ[ZMod 5] V)) := fun t ht => ht.1
  have hRconj : ∀ g ∈ Γ, ∀ t ∈ reflSet Γ, g * t * g⁻¹ ∈ reflSet Γ := fun g hg t ht =>
    ⟨Γ.mul_mem (Γ.mul_mem hg ht.1) (Γ.inv_mem hg), ht.2.conj g⟩
  have hΛcard : Nat.card Λ = 24 := by
    obtain ⟨f⟩ := hΛ
    rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hΛS : ∃ t₀ ∈ Λ, IsRefl t₀ := by
    by_contra hcon
    push Not at hcon
    have hempty : {t : V ≃ₗ[ZMod 5] V | t ∈ Λ ∧ IsRefl t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ht => hcon t ht.1 ht.2
    rw [hempty, Subgroup.closure_empty] at hΛgen
    rw [hΛgen] at hΛcard
    simp at hΛcard
  obtain ⟨t₀, ht₀Λ, ht₀⟩ := hΛS
  have ht₀R : t₀ ∈ reflSet Γ := ⟨hΛΓ ht₀Λ, ht₀⟩
  obtain ⟨π, hπA, hπK⟩ := exists_pi hD e
  have hswap : ∀ t (ht : t ∈ reflSet Γ), (π ⟨t, hRΓ ht⟩).IsSwap := fun t ht =>
    isSwap_of_refl hD hπA hπK ht.1 ht.2
  have hδ : ∀ t (ht : t ∈ reflSet Γ), detU hD ⟨t, hRΓ ht⟩ = -1 := fun t ht =>
    ht.2.detU hD ht.1
  have hAπ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ y : Γ, π y = σ := fun σ hσ => by
    obtain ⟨y, hy, -⟩ := hπA σ hσ
    exact ⟨y, hy⟩
  have hK : ∀ g : Γ, π g = 1 → detU hD g = 1 → g = 1 := fun g hg hdet => by
    obtain ⟨c, hc⟩ := hπK g hg
    exact eq_one_of_scalar hD g c hc hdet
  obtain ⟨hbij, hswaps⟩ := TerminalPerm.reflection_class_bijective π (detU hD) hRΓ hRconj
    ⟨t₀, ht₀R⟩ hswap hδ hAπ hK
  let ψ : ↥(Subgroup.closure (reflSet Γ)) ≃* Perm (Fin 5) := MulEquiv.ofBijective _ hbij
  have hψ : ∀ (t : V ≃ₗ[ZMod 5] V) (ht : t ∈ reflSet Γ),
      ψ ⟨t, Subgroup.subset_closure ht⟩ = π ⟨t, hRΓ ht⟩ := fun t ht => rfl
  refine ⟨ψ, fun t ht => ?_, fun σ hσ => ?_, fixed_vectors_zero hD ht₀R hRconj, ?_⟩
  · rw [hψ t ht]
    exact hswap t ht
  · obtain ⟨t, ht, hts⟩ := hswaps σ hσ
    exact ⟨t, ht, by rw [hψ t ht]; exact hts⟩
  ·
    have hΛle : Λ ≤ Subgroup.closure (reflSet Γ) := by
      rw [hΛgen, Subgroup.closure_le]
      intro t ht
      exact Subgroup.subset_closure ⟨hΛΓ ht.1, ht.2⟩
    let H : Subgroup (Perm (Fin 5)) := (Λ.subgroupOf (Subgroup.closure (reflSet Γ))).map
      ψ.toMonoidHom
    have hHcard : Nat.card H = 24 := by
      rw [Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛle).toEquiv, hΛcard]
    obtain ⟨k, hk⟩ := TerminalPerm.exists_fixed_point_of_card_24 H hHcard
    refine ⟨k, fun x hx => ⟨hΛle hx, hk _ ?_⟩⟩
    exact ⟨⟨x, hΛle hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

end Assembly

end TerminalLA

end CFSG.RankThree.PartOne
