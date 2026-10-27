module

public import CFSG.Quasithin.MS93.S4A43XE

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section LinAlg

variable {F : Type} [Field F]

theorem finrank_inf_of_ne {P P' : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    (hP' : Module.finrank F P' = 2) (hne : P ≠ P') : Module.finrank F ↥(P ⊓ P') = 1 := by
  have hlt : P < P ⊔ P' := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hle : P' ≤ P := h ▸ le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hP, hP'])).symm
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_le (P ⊔ P')
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq P P'
  rw [Module.finrank_fin_fun] at h2
  omega

theorem sup_eq_of_finrank_eq_one {L₁ L₂ P : Submodule F (Fin 3 → F)}
    (h₁ : Module.finrank F L₁ = 1) (h₂ : Module.finrank F L₂ = 1) (hne : L₁ ≠ L₂)
    (hL₁ : L₁ ≤ P) (hL₂ : L₂ ≤ P) (hP : Module.finrank F P = 2) : L₁ ⊔ L₂ = P := by
  have hinf : L₁ ⊓ L₂ = ⊥ := by
    by_contra hne'
    obtain ⟨x, ⟨hx1, hx2⟩, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
    apply hne
    have e1 : Submodule.span F {x} = L₁ := Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hx1) (by rw [finrank_span_singleton hx0, h₁])
    have e2 : Submodule.span F {x} = L₂ := Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hx2) (by rw [finrank_span_singleton hx0, h₂])
    rw [← e1, ← e2]
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
  rw [hinf, finrank_bot, h₁, h₂] at h3
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hL₁ hL₂) (by rw [hP]; omega)

end LinAlg

section Coord

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

@[expose] def IsNatCoord (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (S : Subgroup G)
    (W : Submodule F (Fin 3 → F)) : Prop :=
  S ≤ V ∧ ∀ v : ↥V, (v : G) ∈ S ↔ natVec hφ v ∈ W

variable {hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1}

theorem isNatCoord_commutator (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {A : Subgroup G}
    (hA : A ≤ K) : IsNatCoord hφ ⁅V, A⁆ (commN (natImage φ A)) :=
  ⟨Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans hφ.1),
    fun v => mem_commutator_iff_natVec hφ hA v⟩

theorem IsNatCoord.inf {S S' : Subgroup G} {W W' : Submodule F (Fin 3 → F)}
    (h : IsNatCoord hφ S W) (h' : IsNatCoord hφ S' W') : IsNatCoord hφ (S ⊓ S') (W ⊓ W') :=
  ⟨inf_le_left.trans h.1, fun v => by
    rw [Subgroup.mem_inf, Submodule.mem_inf, h.2 v, h'.2 v]⟩

theorem IsNatCoord.card {S : Subgroup G} {W : Submodule F (Fin 3 → F)}
    (h : IsNatCoord hφ S W) : Nat.card ↥S = Nat.card ↥W := by
  let e1 : ↥S ≃ {v : ↥V // (v : G) ∈ S} :=
    { toFun := fun x => ⟨⟨x, h.1 x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {v : ↥V // (v : G) ∈ S} ≃ {x : Fin 3 → F // x ∈ W} :=
    Equiv.subtypeEquiv (Equiv.ofBijective (natVec hφ) (natVec_bijective hφ)) fun v => h.2 v
  rw [Nat.card_congr (e1.trans e2)]

theorem IsNatCoord.eq {S S' : Subgroup G} {W : Submodule F (Fin 3 → F)}
    (h : IsNatCoord hφ S W) (h' : IsNatCoord hφ S' W) : S = S' := by
  ext x
  constructor
  · intro hx
    have := (h.2 ⟨x, h.1 hx⟩).mp hx
    exact (h'.2 ⟨x, h.1 hx⟩).mpr this
  · intro hx
    have := (h'.2 ⟨x, h'.1 hx⟩).mp hx
    exact (h.2 ⟨x, h'.1 hx⟩).mpr this

theorem IsNatCoord.sup {S S' S'' : Subgroup G} {W W' W'' : Submodule F (Fin 3 → F)}
    (h : IsNatCoord hφ S W) (h' : IsNatCoord hφ S' W') (h'' : IsNatCoord hφ S'' W'')
    (hW : W ⊔ W' = W'') : S ⊔ S' = S'' := by
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have := (h.2 ⟨x, h.1 hx⟩).mp hx
      exact (h''.2 ⟨x, h.1 hx⟩).mpr (hW ▸ Submodule.mem_sup_left this)
    · have := (h'.2 ⟨x, h'.1 hx⟩).mp hx
      exact (h''.2 ⟨x, h'.1 hx⟩).mpr (hW ▸ Submodule.mem_sup_right this)
  · intro x hx
    have hxv : natVec hφ ⟨x, h''.1 hx⟩ ∈ W ⊔ W' := hW ▸ (h''.2 ⟨x, h''.1 hx⟩).mp hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxv
    obtain ⟨u, rfl⟩ := natVec_surjective hφ a
    obtain ⟨u', rfl⟩ := natVec_surjective hφ b
    have hxe : (⟨x, h''.1 hx⟩ : ↥V) = u * u' :=
      natVec_injective hφ (by rw [natVec_mul, hab])
    have : x = (u : G) * u' := congrArg Subtype.val hxe
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((h.2 u).mpr ha))
      (Subgroup.mem_sup_right ((h'.2 u').mpr hb))

end Coord

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem critR_le_usup {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR 𝔛 α α' ≤ Usup 𝔛 α (geo 𝔛 α α' 1) := by
  have hα := hs.1.1
  have hZs := zm_le_stab_of_star h hs
  rw [critR, commutator_zm_eq_uloc h c.full hα hZs,
    usup_eq_commutator_uloc h c.full hα (adj_geo_one_of_isCritical _ h.critDist_pos hs.1)]
  exact Subgroup.commutator_mono le_rfl (zm_le_qv_geo_one_of_star h hs)

theorem usup_ne_of_gen {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α) : Usup 𝔛 α ρ ≠ Usup 𝔛 α (geo 𝔛 α α' 1) :=
  fun heq => c.not_critR_le_usup_of_gen hs hαρ hgen (heq ▸ c.critR_le_usup hs)

theorem coord_lines {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ∃ (ψ : ↥(stab 𝔛 α) →* ↥(StatedSL 3 F))
      (hψ : IsSumOfNaturalModulesVia (stab 𝔛 α) (Uloc h.le L α) ⊥ ψ false 1),
      Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1)))) = 2 ∧
      IsNatCoord hψ (Usup 𝔛 α (geo 𝔛 α α' 1)) (commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1)))) ∧
      IsNatCoord hψ (critR 𝔛 α α') (commN (natImage ψ (ZM 𝔛 α'))) ∧
      Module.finrank F ↥(commN (natImage ψ (ZM 𝔛 α'))) = 1 ∧
      commN (natImage ψ (ZM 𝔛 α')) ≤ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) ∧
      ∀ ρ, 𝔄 α ρ → Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α →
        IsNatCoord hψ (Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1))
          (commN (natImage ψ (Qv 𝔛 ρ)) ⊓ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1)))) ∧
        Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 ρ)) ⊓
          commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1)))) = 1 := by
  have hα := hs.1.1
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hα
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZs := zm_le_stab_of_star h hs
  have hcoordU : ∀ ρ, 𝔄 α ρ → IsNatCoord hψ (Usup 𝔛 α ρ) (commN (natImage ψ (Qv 𝔛 ρ))) :=
    fun ρ hαρ => by
      rw [usup_eq_commutator_uloc h c.full hα hαρ]
      exact isNatCoord_commutator hψ (qv_le_stab_of_adj _ hαρ.symm)
  have hcoordR : IsNatCoord hψ (critR 𝔛 α α') (commN (natImage ψ (ZM 𝔛 α'))) := by
    rw [critR, commutator_zm_eq_uloc h c.full hα hZs]
    exact isNatCoord_commutator hψ hZs
  have hr : Module.finrank F ↥(commN (natImage ψ (ZM 𝔛 α'))) = 1 := by
    have hcR := c.card_critR hs
    rw [hcoordR.card, Module.natCard_eq_pow_finrank (K := F),
      Nat.card_eq_fintype_card (α := F)] at hcR
    exact Nat.pow_right_injective hq (show Fintype.card F ^ _ = Fintype.card F ^ 1 by
      rw [hcR, pow_one])
  refine ⟨ψ, hψ, c.finrank_commN_qv hα hψ hαβ, hcoordU _ hαβ, hcoordR, hr,
    commN_mono (natImage_mono (zm_le_qv_geo_one_of_star h hs)), fun ρ hαρ hgen => ?_⟩
  refine ⟨(hcoordU ρ hαρ).inf (hcoordU _ hαβ), finrank_inf_of_ne (c.finrank_commN_qv hα hψ hαρ)
    (c.finrank_commN_qv hα hψ hαβ) fun he => c.usup_ne_of_gen hs hαρ hgen ?_⟩
  exact (hcoordU ρ hαρ).eq (he ▸ hcoordU _ hαβ)

theorem card_ell {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α) :
    Nat.card ↥(Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) = Fintype.card F := by
  obtain ⟨ψ, hψ, -, -, -, -, -, hρ⟩ := c.coord_lines hs
  obtain ⟨hc, hf⟩ := hρ ρ hαρ hgen
  rw [hc.card, Module.natCard_eq_pow_finrank (K := F), hf, pow_one, Nat.card_eq_fintype_card]

theorem ell_sup_critR {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α) :
    (Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) ⊔ critR 𝔛 α α' = Usup 𝔛 α (geo 𝔛 α α' 1) := by
  obtain ⟨ψ, hψ, hP, hcU, hcR, hr, hrP, hρ⟩ := c.coord_lines hs
  obtain ⟨hc, hf⟩ := hρ ρ hαρ hgen
  refine hc.sup hcR hcU (sup_eq_of_finrank_eq_one hf hr (fun he => ?_) inf_le_right hrP hP)
  apply c.not_critR_le_usup_of_gen hs hαρ hgen
  have := hc.eq (he ▸ hcR)
  rw [← this]
  exact inf_le_left

theorem ell_sup_ell {α α' ρ₁ ρ₂ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ₁ : 𝔄 α ρ₁)
    (hgen₁ : Gab 𝔛 α ρ₁ ⊔ ZM 𝔛 α' = stab 𝔛 α) (hαρ₂ : 𝔄 α ρ₂)
    (hgen₂ : Gab 𝔛 α ρ₂ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hne : Usup 𝔛 α ρ₁ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≠ Usup 𝔛 α ρ₂ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) :
    (Usup 𝔛 α ρ₁ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) ⊔ (Usup 𝔛 α ρ₂ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) =
      Usup 𝔛 α (geo 𝔛 α α' 1) := by
  obtain ⟨ψ, hψ, hP, hcU, -, -, -, hρ⟩ := c.coord_lines hs
  obtain ⟨hc₁, hf₁⟩ := hρ ρ₁ hαρ₁ hgen₁
  obtain ⟨hc₂, hf₂⟩ := hρ ρ₂ hαρ₂ hgen₂
  exact hc₁.sup hc₂ hcU (sup_eq_of_finrank_eq_one hf₁ hf₂
    (fun he => hne (hc₁.eq (he ▸ hc₂))) inf_le_right inf_le_right hP)

end Ctx43

end CFSG.Quasithin.MS93.S4A
