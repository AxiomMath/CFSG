module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Setup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem commutator_le_left_of_le_normalizer' {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have hk' : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hK hk) h⁻¹).mp (H.inv_mem hh)
  have e : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
  rw [commutatorElement_def, e]
  exact H.mul_mem hh hk'

namespace Config15418

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} (c : Config15418 G T)
  (H : Hyp15418 G T)
include H

theorem E₃_eq : c.E₃ = (⁅VZ T c.M₂, c.X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ⊔ c.EX := by
  set F := ⁅VZ T c.M₂, c.X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  have hXV := c.X_le_normalizer_V₂
  have hF2 : Nat.card F = 2 :=
    card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData H.hyp.sylow.1 c.inM₂.2
      (c.eX_decomp H).1 (c.eX_decomp H).2 c.dataX
  have hFE : F ≤ eOf T := by
    refine le_trans ?_ ((c.eX_decomp H).1 ▸ le_sup_right)
    exact inf_le_inf_right _ (Subgroup.commutator_mono le_rfl c.X₁_le)
  have hFC : F ≤ Subgroup.centralizer (c.X₂ : Set G) :=
    inf_le_left.trans (commutator_le_centralizer_of_sixTwoData c.dataX.symm hXV)
  have hFX : F ⊓ c.EX = ⊥ := by
    rw [eq_bot_iff, ← commutator_inf_centralizer_eq_bot_of_sixTwoData (c.isElemAbelian_V₂ H)
      hXV c.dataX]
    exact inf_le_inf inf_le_left (inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.X₁_le)))
  have hFN : F ≤ Subgroup.normalizer (c.EX : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    exact eOf_mul_comm hb.1 (hFE ha)
  have hcard := card_sup_mul_card_inf hFN
  rw [hFX, Subgroup.card_bot, mul_one, hF2, (c.EX_eq H).2] at hcard
  have hE₃ : Nat.card c.E₃ = 4 :=
    c.card_of_relIndex_eq_two H (show c.E₃ ≤ eOf T from inf_le_left) (c.relIndex_E₃ H)
  exact (Subgroup.eq_of_le_of_card_ge
    (show F ⊔ c.EX ≤ c.E₃ from sup_le (le_inf hFE hFC) c.EX_le_E₃) (by rw [hcard, hE₃])).symm

theorem E₂_eq : c.E₂ = (⁅VZ T c.M₂, c.X₂⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ⊔ c.EX := by
  set F := ⁅VZ T c.M₂, c.X₂⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  have hXV := c.X_le_normalizer_V₂
  have hF2 : Nat.card F = 2 :=
    card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData H.hyp.sylow.1 c.inM₂.2
      (c.eX_decomp H).1 (c.eX_decomp H).2 c.dataX.symm
  have hFE : F ≤ eOf T := by
    refine le_trans ?_ ((c.eX_decomp H).1 ▸ le_sup_right)
    exact inf_le_inf_right _ (Subgroup.commutator_mono le_rfl c.X₂_le)
  have hFC : F ≤ Subgroup.centralizer (c.X₁ : Set G) :=
    inf_le_left.trans (commutator_le_centralizer_of_sixTwoData c.dataX hXV)
  have hFX : F ⊓ c.EX = ⊥ := by
    rw [eq_bot_iff, ← commutator_inf_centralizer_eq_bot_of_sixTwoData (c.isElemAbelian_V₂ H)
      hXV c.dataX.symm]
    exact inf_le_inf inf_le_left (inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.X₂_le)))
  have hFN : F ≤ Subgroup.normalizer (c.EX : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    exact eOf_mul_comm hb.1 (hFE ha)
  have hcard := card_sup_mul_card_inf hFN
  rw [hFX, Subgroup.card_bot, mul_one, hF2, (c.EX_eq H).2] at hcard
  have hE₂ : Nat.card c.E₂ = 4 :=
    c.card_of_relIndex_eq_two H (show c.E₂ ≤ eOf T from inf_le_left) (c.relIndex_E₂ H)
  exact (Subgroup.eq_of_le_of_card_ge
    (show F ⊔ c.EX ≤ c.E₂ from sup_le (le_inf hFE hFC) c.EX_le_E₂) (by rw [hcard, hE₂])).symm

theorem not_E₀_le_E₃ : ¬ c.E₀ ≤ c.E₃ := by
  intro h
  apply c.E₀_ne_bot H
  rw [eq_bot_iff, ← c.E₀_inf_Z H]
  refine le_inf le_rfl ?_
  have h1 : c.E₀ ≤ c.EX := c.E₂_inf_E₃ ▸ le_inf inf_le_right h
  exact h1.trans ((c.EX_eq H).1.le.trans inf_le_left)

omit [Finite G] H in
private theorem map_centralizer_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    (Subgroup.centralizer (R : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (R : Set G) := by
  rw [centralizer_map_mulEquiv, map_conj_eq_of_mem_normalizer hg]

theorem mem_centralizer_eOf {g : G} (hg₁ : g ∈ c.M₁) (hg₂ : g ∈ c.M₂)
    (hgS : g ∈ Subgroup.normalizer (baum T : Set G))
    (hgE₀ : g ∈ Subgroup.centralizer (c.E₀ : Set G)) :
    g ∈ Subgroup.centralizer (eOf T : Set G) := by
  set V := VZ T c.M₂
  set U₁ := ⁅V, c.X₁⁆
  set U₂ := ⁅V, c.X₂⁆
  set φ := (MulAut.conj g).toMonoidHom
  have hV := c.isElemAbelian_V₂ H
  have hXV := c.X_le_normalizer_V₂
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _ hg₂
  have hgX : g ∈ Subgroup.normalizer (c.X : Set G) := (c.M₂_eq H) ▸ hg₂
  have hgY : g ∈ Subgroup.normalizer (c.Y : Set G) := (c.M₁_eq H) ▸ hg₁
  have hgE : g ∈ Subgroup.normalizer (eOf T : Set G) := normalizer_baum_le_normalizer_eOf T hgS
  obtain ⟨hX, -, -, -, -, hVX, -, h₁, h₂, -, -, -, -, -, -, hN₁, -⟩ := c.dataX
  have hW : U₁.map φ = U₁ ∨ U₁.map φ = U₂ := by
    have hmap : U₁.map φ = ⁅V, c.X₁.map φ⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hgV]
    have hX₁X : c.X₁.map φ ≤ c.X := by
      rw [← map_conj_eq_of_mem_normalizer hgX]
      exact Subgroup.map_mono c.X₁_le
    have hXN : c.X ≤ Subgroup.normalizer ((c.X₁.map φ : Subgroup G) : Set G) := by
      intro x hx
      refine mem_normalizer_map_conj (hN₁ ?_)
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgX) x).mp hx
      simpa [mul_assoc] using this
    refine eq_or_eq_of_le_sup (X₁ := c.X₁) ?_ h₁ h₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a ha b hb
      have hcomm := isMulCommutative_subgroup_iff.mp hV.1
      exact hcomm a (commutator_le_left_of_le_normalizer' ((c.X₁_le).trans hXV) ha) b
        (commutator_le_left_of_le_normalizer' ((c.X₂_le).trans hXV) hb)
    · exact fun x hx => A4.mem_normalizer_commutator (hXV (c.X₁_le hx)) (Subgroup.le_normalizer hx)
    · rw [Subgroup.le_centralizer_iff]
      exact commutator_le_centralizer_of_sixTwoData c.dataX hXV
    · exact commutator_inf_centralizer_eq_bot_of_sixTwoData hV hXV c.dataX
    · rw [hmap, ← hVX, hX]
      exact Subgroup.commutator_mono le_rfl (hX ▸ hX₁X)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h₁]
    · rw [hmap]
      exact fun x hx => A4.mem_normalizer_commutator (hXV (c.X₁_le hx)) (hXN (c.X₁_le hx))
  have hCS : (Subgroup.centralizer (baum T : Set G)).map φ =
      Subgroup.centralizer (baum T : Set G) := map_centralizer_of_mem_normalizer hgS
  have hEX : c.EX.map φ = c.EX := by
    rw [EX, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem_normalizer hgE,
      map_centralizer_of_mem_normalizer hgX]
  have hgEX : g ∈ Subgroup.centralizer (c.EX : Set G) :=
    mem_centralizer_of_card_eq_two (c.EX_eq H).2 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEX)
  rcases hW with hW | hW
  ·
    have hF : (U₁ ⊓ Subgroup.centralizer (baum T : Set G)).map φ =
        U₁ ⊓ Subgroup.centralizer (baum T : Set G) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hW, hCS]
    have hF2 : Nat.card ↥(U₁ ⊓ Subgroup.centralizer (baum T : Set G)) = 2 :=
      card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData H.hyp.sylow.1 c.inM₂.2
        (c.eX_decomp H).1 (c.eX_decomp H).2 c.dataX
    have hgF : g ∈ Subgroup.centralizer
        ((U₁ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) : Set G) :=
      mem_centralizer_of_card_eq_two hF2 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hF)
    have hgE₃ : g ∈ Subgroup.centralizer (c.E₃ : Set G) := by
      rw [c.E₃_eq H, centralizer_sup_eq]
      exact ⟨hgF, hgEX⟩
    have hE := sup_eq_of_relIndex_eq_two (show c.E₃ ≤ eOf T from inf_le_left) (c.relIndex_E₃ H)
      (show c.E₀ ≤ eOf T from inf_le_left.trans inf_le_left) (c.not_E₀_le_E₃ H)
    rw [← hE, centralizer_sup_eq]
    exact ⟨hgE₃, hgE₀⟩
  ·
    exfalso
    have hF : (U₁ ⊓ Subgroup.centralizer (baum T : Set G)).map φ =
        U₂ ⊓ Subgroup.centralizer (baum T : Set G) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hW, hCS]
    have hE₃ : c.E₃.map φ = c.E₂ := by
      rw [c.E₃_eq H, c.E₂_eq H, Subgroup.map_sup, hF, hEX]
    have hE₁ : c.E₁.map φ = c.E₁ := by
      rw [E₁, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem_normalizer hgE,
        map_centralizer_of_mem_normalizer hgY]
    have hE₀ : c.E₀.map φ = c.E₀ :=
      map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hgE₀)
    have h : (c.E₁ ⊓ c.E₃).map φ = c.E₀.map φ := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hE₁, hE₃, hE₀]
      rfl
    have heq := Subgroup.map_injective (MulAut.conj g).injective h
    exact c.not_E₀_le_E₃ H (heq ▸ inf_le_right)

theorem normalizer_inf_centralizer_le :
    Subgroup.normalizer (baum T : Set G) ⊓ Subgroup.centralizer (c.E₀ : Set G) ≤ baum T := by
  rintro g ⟨hgS, hgE₀⟩
  have hg₁ : g ∈ c.M₁ := H.h16 c.M₁ c.inM₁ hgS
  have hg₂ : g ∈ c.M₂ := H.h16 c.M₂ c.inM₂ hgS
  have hgE := c.mem_centralizer_eOf H hg₁ hg₂ hgS hgE₀
  have hgT : g ∈ T := by
    rw [← H.h8]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (omegaOneCenter_le_eOf' T)) hgE
  exact ⟨hgT, hgE⟩

omit H in
theorem isSylowTwoOf_of_normalizer_le {S K : Subgroup G} (hSK : S ≤ K) (hS : IsPGroup 2 S)
    (hN : K ⊓ Subgroup.normalizer (S : Set G) ≤ S) : IsSylowTwoOf S K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨hSK, hS, fun P hPK hP hSP => ?_⟩
  by_contra hPS
  let SP : Subgroup P := S.subgroupOf P
  have hlt : SP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPS fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ SP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent
  obtain ⟨x, hxN, hxS⟩ := IsConcreteLE.exists_of_lt (hnc SP hlt)
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxS (Subgroup.mem_subgroupOf.mpr (hN ⟨hPK x.2, hxNorm⟩))

omit [Finite G] H in
theorem baum_le_centralizer_E₀ : baum T ≤ Subgroup.centralizer (c.E₀ : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (inf_le_left.trans inf_le_left)))

theorem isSylowTwoOf_baum : IsSylowTwoOf (baum T) (Subgroup.centralizer (c.E₀ : Set G)) :=
  isSylowTwoOf_of_normalizer_le c.baum_le_centralizer_E₀ (H.hyp.sylow.1.to_le inf_le_left)
    (fun _ hg => c.normalizer_inf_centralizer_le H ⟨hg.2, hg.1⟩)

theorem commutator_inf_centralizer_X :
    ⁅VZ T c.M₂, c.X⁆ ⊓ Subgroup.centralizer (c.X : Set G) = ⊥ := by
  have hXV := c.X_le_normalizer_V₂
  have hV := c.isElemAbelian_V₂ H
  rw [eq_bot_iff, ← commutator_inf_centralizer_eq_bot_of_sixTwoData hV hXV c.dataX.symm,
    ← commutator_inf_centralizer_eq_of_sixTwoData hV hXV c.dataX]
  exact le_inf (le_inf inf_le_left (inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.X₁_le))))
    (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.X₂_le)))

include c in
theorem exists_isElemAbelian_card :
    ∃ A : Subgroup G, A ≤ baum T ∧ IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := VZ T c.M₂
  have hV := c.isElemAbelian_V₂ H
  have hXV := c.X_le_normalizer_V₂
  obtain ⟨hX, -, -, -, -, hVX, hinf, h₁, h₂, -⟩ := c.dataX
  have hcommV := isMulCommutative_subgroup_iff.mp hV.1
  have hUV : ⁅V, c.X⁆ ≤ V := commutator_le_left_of_le_normalizer' hXV
  have hZV : quasithinOmegaOneCenter T ≤ V := by
    intro z hz
    have := mem_conjClosure (Z := quasithinOmegaOneCenter T) (Subgroup.one_mem c.M₂) hz
    simp only [one_mul, inv_one, mul_one] at this
    exact this
  have hEXV : c.EX ≤ V := (c.EX_eq H).1.le.trans (inf_le_left.trans hZV)
  set A := ⁅V, c.X⁆ ⊔ c.EX
  have hAV : A ≤ V := sup_le hUV hEXV
  obtain ⟨Tsyl, hTsyl⟩ := exists_sylow_of_quasithinIsSylowTwo H.hyp.sylow
  have hTM : (Tsyl : Subgroup G) ≤ c.M₂ := hTsyl ▸ c.inM₂.2
  have hF : c.M₂ ⊓ Subgroup.centralizer (pCoreOf 2 c.M₂ : Set G) ≤ pCoreOf 2 c.M₂ :=
    H.hyp.qtke.2.1 c.M₂ c.inM₂.1.1 ⟨Tsyl, hTM⟩
  have hVO : V ≤ centerOf (pCoreOf 2 c.M₂) :=
    (conjClosure_le_centerOf_pCoreOf c.M₂ Tsyl hTM hF (Z := quasithinOmegaOneCenter T)
      (by rw [hTsyl])).1
  have hVT : V ≤ T := by
    have := pCoreOf_two_le_sylow c.M₂ Tsyl hTM
    rw [hTsyl] at this
    exact hVO.trans (inf_le_left.trans this)
  have hEV : eOf T ≤ V := by
    rw [(c.eX_decomp H).1]
    exact sup_le hEXV (inf_le_left.trans hUV)
  have hVS : V ≤ baum T := by
    intro v hv
    refine ⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    exact hcommV e (hEV he) v hv
  refine ⟨A, hAV.trans hVS, isElemAbelian_of_le' hV hAV, ?_⟩
  have hU : Nat.card ↥⁅V, c.X⁆ = 16 := by
    have hN : ⁅V, c.X₁⁆ ≤ Subgroup.normalizer ((⁅V, c.X₂⁆ : Subgroup G) : Set G) := by
      intro a ha
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      exact hcommV b (commutator_le_left_of_le_normalizer' ((c.X₂_le).trans hXV) hb) a
        (commutator_le_left_of_le_normalizer' ((c.X₁_le).trans hXV) ha)
    have h := card_sup_mul_card_inf hN
    rw [hinf, Subgroup.card_bot, mul_one, h₁, h₂] at h
    rw [hVX, h]
  have hN : ⁅V, c.X⁆ ≤ Subgroup.normalizer (c.EX : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    exact hcommV b (hEXV hb) a (hUV ha)
  have h := card_sup_mul_card_inf hN
  have hbot : ⁅V, c.X⁆ ⊓ c.EX = ⊥ := by
    rw [eq_bot_iff, ← c.commutator_inf_centralizer_X H]
    exact inf_le_inf_left _ inf_le_right
  rw [hbot, Subgroup.card_bot, mul_one, hU, (c.EX_eq H).2] at h
  rw [h]
  norm_num

end Config15418

end CFSG.Quasithin.EmptyFaithfulMultiple
