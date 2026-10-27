module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Lines
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Klein
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

set_option linter.unusedSectionVars false

section Tables

open Equiv

theorem tabE_card_le_four (K : Subgroup (Perm (Fin 5))) (hexp : ∀ x ∈ K, x * x = 1) :
    Nat.card K ≤ 4 := by
  obtain ⟨g, hg⟩ := exists_conj_le_syl hexp
  set B := K.map (MulAut.conj g).toMonoidHom with hB
  have hcardB : Nat.card B = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hexpB : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have := hexp y hy
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  rw [← hcardB]
  by_cases hbot : B = ⊥
  · rw [hbot, Subgroup.card_bot]; norm_num
  rcases le_syl_cases hg hexpB hbot with ⟨t, -, -, -, h2⟩ | h | h
  · omega
  · rw [h, card_S5T_eq_four]
  · rw [h, card_S5That_eq_four]

theorem tabE_swap_mul_not_swap {s t : Perm (Fin 5)} (hs : s.IsSwap) (ht : t.IsSwap) :
    s * t ≠ 1 → ¬ (s * t).IsSwap := by
  intro h1 h2
  have e1 := (isSwap_iff s).mp hs
  have e2 := (isSwap_iff t).mp ht
  have e3 := (isSwap_iff (s*t)).mp h2
  have h3 : Equiv.Perm.sign (s * t) = 1 := by
    rw [map_mul]
    have a : Equiv.Perm.sign s = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
      · exact absurd h e1.2.2
      · exact h
    have b : Equiv.Perm.sign t = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h
      · exact absurd h e2.2.2
      · exact h
    rw [a, b]; rfl
  exact e3.2.2 h3

theorem tabE_hM_nat (σ : Perm (Fin 5)) (h1 : σ ≠ 1) (h : idx nat σ ≤ 2) : σ.IsSwap := by
  have := (transvections σ h1).1
  omega

theorem tabE_hM_orth (σ : Perm (Fin 5)) (h1 : σ ≠ 1) (h : idx orth σ ≤ 2) : σ.IsSwap := by
  have h2 := (transvections σ h1).2
  rw [idx_orth] at h
  simp only [h1, ↓reduceIte] at h
  rw [idx_orth] at h2
  simp only [h1, ↓reduceIte] at h2
  split_ifs at h h2 <;> first | omega | exact h2.mp rfl

end Tables

section Algebra

variable {G : Type} [Group G]

theorem tabE_relIndex_le_two {F V Zα Q : Subgroup G} (θ : ↥F →* Equiv.Perm (Fin 5))
    (hker : ∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ Q) (hN : Zα ≤ Subgroup.normalizer (Q : Set G))
    (hZV : Zα ≤ V) (hVF : V ≤ F) (hexp : ∀ x ∈ V, x * x = 1) (hne : ∃ z ∈ Zα, z ∉ Q) :
    (V ⊓ (Zα ⊔ Q)).relIndex V ≤ 2 := by
  let ψ : ↥V →* Equiv.Perm (Fin 5) := θ.comp (Subgroup.inclusion hVF)
  have hψker : ∀ v : ↥V, ψ v = 1 ↔ (v : G) ∈ Q := fun v => hker ⟨v.1, hVF v.2⟩
  set T : Subgroup (Equiv.Perm (Fin 5)) := (Zα.subgroupOf V).map ψ with hT
  have hcomap : (V ⊓ (Zα ⊔ Q)).subgroupOf V = T.comap ψ := by
    ext v
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hT, Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hv⟩
      obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_of_mem_sup_of_le_normalizer hN _ hv
      refine ⟨⟨y, hZV hy⟩, hy, ?_⟩
      have hzV : z ∈ V := by
        have := V.mul_mem (V.inv_mem (hZV hy)) v.2
        rwa [hyz, ← mul_assoc, inv_mul_cancel, one_mul] at this
      have h1 : ψ ⟨z, hzV⟩ = 1 := (hψker _).mpr hz
      have h2 : (⟨y, hZV hy⟩ : ↥V) * ⟨z, hzV⟩ = v := Subtype.ext hyz.symm
      rw [← h2, map_mul, h1, mul_one]
    · rintro ⟨y, hy, hyv⟩
      have h1 : ψ (y⁻¹ * v) = 1 := by rw [map_mul, map_inv, hyv, inv_mul_cancel]
      have h2 : ((y⁻¹ * v : ↥V) : G) ∈ Q := (hψker _).mp h1
      have h3 : (y : G) * ((y⁻¹ * v : ↥V) : G) = v := by simp
      refine ⟨v.2, ?_⟩
      rw [← h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h2)
  have hidx : (V ⊓ (Zα ⊔ Q)).relIndex V = T.relIndex ψ.range := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap]
  rw [hidx]
  set K := ψ.range with hK
  have hTK : T ≤ K := by
    rintro _ ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  have hKexp : ∀ x ∈ K, x * x = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (hexp v v.2)
    rw [this, map_one]
  have hK4 := tabE_card_le_four K hKexp
  have hT2 : 2 ≤ Nat.card T := by
    obtain ⟨z, hz, hzQ⟩ := hne
    have : ψ ⟨z, hZV hz⟩ ≠ 1 := fun h => hzQ ((hψker _).mp h)
    have hTne : T ≠ ⊥ := by
      intro hb
      apply this
      have : ψ ⟨z, hZV hz⟩ ∈ T := ⟨⟨z, hZV hz⟩, hz, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact this
    have := (Subgroup.one_lt_card_iff_ne_bot T).mpr hTne
    omega
  have hmul := Subgroup.relIndex_mul_index hTK
  have h1 := Subgroup.card_mul_index T
  have h2 := Subgroup.card_mul_index K
  have hr : T.relIndex K * Nat.card T = Nat.card K := by
    have e1 : T.relIndex K * K.index * (Nat.card T * Nat.card K) =
        T.index * (Nat.card T * Nat.card K) := by
      rw [hmul]
    have e2 : T.relIndex K * Nat.card T * (K.index * Nat.card K) =
        Nat.card T * T.index * Nat.card K := by
      calc T.relIndex K * Nat.card T * (K.index * Nat.card K)
          = T.relIndex K * K.index * (Nat.card T * Nat.card K) := by ring
        _ = T.index * (Nat.card T * Nat.card K) := e1
        _ = Nat.card T * T.index * Nat.card K := by ring
    rw [mul_comm K.index, h2, h1] at e2
    have : Nat.card (Equiv.Perm (Fin 5)) * (T.relIndex K * Nat.card T) =
        Nat.card (Equiv.Perm (Fin 5)) * Nat.card K := by
      calc _ = T.relIndex K * Nat.card T * Nat.card (Equiv.Perm (Fin 5)) := by ring
        _ = _ := by rw [e2]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
  nlinarith

theorem tabE_no_two_swaps {F V Zα Q : Subgroup G} (θ : ↥F →* Equiv.Perm (Fin 5))
    (hker : ∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ Q)
    (hZV : Zα ≤ V) (hVF : V ≤ F) (hexp : ∀ x ∈ V, x * x = 1)
    (hne : ∃ z ∈ Zα, z ∉ Q) (hne2 : ∃ v ∈ V, ∀ a ∈ Zα, v * a⁻¹ ∉ Q)
    (hsw : ∀ g (hg : g ∈ V), θ ⟨g, hVF hg⟩ = 1 ∨ (θ ⟨g, hVF hg⟩).IsSwap) : False := by
  obtain ⟨z, hz, hzQ⟩ := hne
  obtain ⟨v, hv, hvZ⟩ := hne2
  have hzF : z ∈ F := hVF (hZV hz)
  have hvF : v ∈ F := hVF hv
  have hz1 : θ ⟨z, hzF⟩ ≠ 1 := fun h => hzQ ((hker _).mp h)
  have hv1 : θ ⟨v, hvF⟩ ≠ 1 := fun h => by
    have := hvZ 1 (Subgroup.one_mem _)
    simp only [inv_one, mul_one] at this
    exact this ((hker _).mp h)
  have hzs := (hsw z (hZV hz)).resolve_left hz1
  have hvs := (hsw v hv).resolve_left hv1
  have hzz : z * z = 1 := hexp z (hZV hz)
  have hz' : (θ ⟨z, hzF⟩)⁻¹ = θ ⟨z, hzF⟩ := by
    have : (⟨z, hzF⟩ : ↥F) * ⟨z, hzF⟩ = 1 := Subtype.ext hzz
    rw [inv_eq_iff_mul_eq_one, ← map_mul, this, map_one]
  have hmem : v * z ∈ V := V.mul_mem hv (hZV hz)
  have hmul : θ ⟨v * z, hVF hmem⟩ = θ ⟨v, hvF⟩ * θ ⟨z, hzF⟩ := by
    rw [← map_mul]; rfl
  have hne1 : θ ⟨v * z, hVF hmem⟩ ≠ 1 := by
    intro h
    rw [hmul, mul_eq_one_iff_eq_inv, hz'] at h
    apply hvZ z hz
    apply (hker ⟨v * z⁻¹, F.mul_mem hvF (F.inv_mem hzF)⟩).mp
    have : (⟨v * z⁻¹, F.mul_mem hvF (F.inv_mem hzF)⟩ : ↥F) = ⟨v, hvF⟩ * ⟨z, hzF⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, h, mul_inv_cancel]
  rcases hsw (v * z) hmem with h | h
  · exact hne1 h
  · rw [hmul] at h hne1
    exact tabE_swap_mul_not_swap hvs hzs hne1 h

end Algebra

section Module

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem tabE_theta_of_modelSec {M : Model 5}
    (hM : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 → idx M σ ≤ 2 → σ.IsSwap)
    {F L X : Subgroup G} (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (hLX : L ≤ X)
    (h : IsModelSec M F L X) :
    ∃ θ : ↥F →* Equiv.Perm (Fin 5), (∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 F) ∧
      ∀ g (hg : g ∈ F), (X ⊓ Subgroup.centralizer ({g} : Set G)).relIndex X ≤ 2 →
        θ ⟨g, hg⟩ = 1 ∨ (θ ⟨g, hg⟩).IsSwap := by
  have hc := h.cSecIn_eq_pCoreOf hq
  obtain ⟨hn, θ, β, hs, hk, hsd⟩ := h
  refine ⟨θ, fun x => ?_, fun g hg hidx => ?_⟩
  · rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf, hc]
  · by_cases h1 : θ ⟨g, hg⟩ = 1
    · exact Or.inl h1
    · refine Or.inr (hM _ h1 ?_)
      rw [← hsd.secIdx_eq_idx hLX hg]
      refine le_trans ?_ hidx
      unfold secIdx
      refine Subgroup.relIndex_le_of_le_left ?_ Subgroup.index_ne_zero_of_finite
      intro x hx
      refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
      have hxc : Commute g x := (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have : Commute (g ^ k) x := hxc.zpow_left k
      have h2 : g ^ k * x * (g ^ k)⁻¹ * x⁻¹ = 1 := by rw [this.eq]; group
      rw [h2]
      exact L.one_mem

theorem tabE_theta_of_113c (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = false)
    {L : Subgroup G} (hLX : L ≤ Zv δ)
    (h : IsNatSec (stab δ) L (Zv δ) ∨ IsOrthSec (stab δ) L (Zv δ)) :
    ∃ θ : ↥(stab δ) →* Equiv.Perm (Fin 5), (∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) ∧
      ∀ g (hg : g ∈ stab δ), (Zv δ ⊓ Subgroup.centralizer ({g} : Set G)).relIndex (Zv δ) ≤ 2 →
        θ ⟨g, hg⟩ = 1 ∨ (θ ⟨g, hg⟩).IsSwap := by
  have hq := quot_stab_five hA hv
  rcases h with h | h
  · exact tabE_theta_of_modelSec tabE_hM_nat hq hLX h
  · exact tabE_theta_of_modelSec tabE_hM_orth hq hLX h

end Module

section Geometry

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem tabE_conjSub_le_iff {g : G} {A B : Subgroup G} : conjSub g A ≤ conjSub g B ↔ A ≤ B := by
  refine ⟨fun h => ?_, conjSub_mono g⟩
  have := conjSub_mono g⁻¹ h
  rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_one] at this

theorem tabE_partner_s3 {α β α' : Geo H M} (hc : IsCritData α β α')
    (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hv : vtype α = true) (d : Geo H M) (hd : vtype d = true) :
    ∃ d' : Geo H M, IsCritPair₁ d d' ∧ ⁅Zv d, Zv d'⁆ ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := α) (δ' := d) (by rw [hd, hv])
  refine ⟨g • α', ⟨?_, ?_⟩, ?_⟩
  · rw [Zv_smul, Qv_smul, tabE_conjSub_le_iff]
    exact hc.not_le
  · rw [CosetGeom.dist_smul]; exact hc.dist_eq
  · rw [Zv_smul, Zv_smul, conjSub_commutator]
    exact fun h => hcomm ((conjSub_eq_bot_iff _).mp h)

omit [Finite G] in
theorem tabE_conjSub_Lv_gen (g : ↥(H ⊔ M)) (d e : Geo H M) :
    conjSub (g : G) (Lv d e) = Lv (g • d) (g • e) := by
  unfold Lv
  rw [← conjSub_commutator, ← Zv_smul, ← Qv_smul]

omit [Finite G] in
theorem tabE_vtype_of_adj_false {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hδ : vtype δ = false) :
    vtype μ = true := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from h)
  cases hμ : vtype μ
  · exact absurd (hδ.trans hμ.symm) this
  · rfl

theorem tabE_Vn_comm (hA : F53Amalgam H M S) (hb3 : 3 ≤ bMin H M) {α : Geo H M} (x y : G) (hx : x ∈ Vn α) (hy : y ∈ Vn α) : x * y = y * x := by
  have := (isElemAbelian_Vn hA hb3 α).1.is_comm.comm (⟨x, hx⟩ : ↥(Vn α)) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem tabE_Vn_sq (hA : F53Amalgam H M S) (hb3 : 3 ≤ bMin H M) {α : Geo H M} (x : G) (hx : x ∈ Vn α) : x * x = 1 := by
  have := (isElemAbelian_Vn hA hb3 α).2 x hx
  simpa [pow_two] using this

section Standing

variable (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
  {α β α' : Geo H M} (hc : IsCritData α β α') (hv : vtype α = true)
  (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb3 : 3 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β))

include hA h27 h28 h113a hc hv hcomm hb3 hn

theorem tabE_card_Lv {d e : Geo H M} (hd : vtype d = true) (he : e ∈ nbrs d) :
    Nat.card ↥(Lv d e) = 2 := by
  obtain ⟨d', hd', hcd⟩ := tabE_partner_s3 hc hcomm hv d hd
  exact card_Lv hA h28 h113a (by omega) hd (bAt_eq_bMin hA h27 hc hv hn d) hd' hcd he

theorem tabE_Lv_ne_and_sup {d e e' : Geo H M} (hd : vtype d = true) (he : e ∈ nbrs d)
    (he' : e' ∈ nbrs d) (hne : e ≠ e') : Lv d e ⊔ Lv d e' = Z0v d := by
  obtain ⟨d', hd', hcd⟩ := tabE_partner_s3 hc hcomm hv d hd
  exact (Lv_ne_and_sup hA h28 h113a (by omega) hd (bAt_eq_bMin hA h27 hc hv hn d) hd' hcd he he' hne).2

theorem tabE_Zv_inf_Zv {d e : Geo H M} (hd : vtype d = true) (he : e ∈ nbrs d) :
    Zv d ⊓ Zv e = Lv d e ⊔ Nv d := by
  obtain ⟨d', hd', hcd⟩ := tabE_partner_s3 hc hcomm hv d hd
  exact Zv_inf_Zv_eq hA h28 h113a (by omega) hd (bAt_eq_bMin hA h27 hc hv hn d) hd' hcd he

theorem tabE_Z0v_sup (d : Geo H M) (hd : vtype d = true) : Z0v d ⊔ Nv d = Zv d := by
  obtain ⟨d', hd', hcd⟩ := tabE_partner_s3 hc hcomm hv d hd
  exact (Z0v_decomp hA h28 h113a (by omega) hd (bAt_eq_bMin hA h27 hc hv hn d) hd' hcd).2.1

theorem tabE_Lv_le_inf {d e : Geo H M} (hd : vtype d = true) (he : e ∈ nbrs d) :
    Lv d e ≤ Zv d ⊓ Zv e := by
  obtain ⟨d', hd', hcd⟩ := tabE_partner_s3 hc hcomm hv d hd
  exact Lv_le_Zv_inf hA h28 h113a (by omega) hd (bAt_eq_bMin hA h27 hc hv hn d) hd' hcd he

theorem tabE_claim1_s5 {β' c' : Geo H M} (hβ'n : β' ∈ nbrs α') (hc'n : c' ∈ nbrs α')
    (hZα : Zv α ≤ stab α')
    (hst : stab α' = Zv α ⊔ (stab α' ⊓ stab c')) : ¬ ⁅Zv c', Zv α⁆ ≤ Zv α' := by
  intro hcon
  have hbA := bAt_eq_bMin hA h27 hc hv hn
  have hN1 : Zv α ≤ Subgroup.normalizer ((Zv α' ⊔ Zv c' : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj (fun z hz a ha => ?_) (fun z hz b hb => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α' (hZα hz)) a).mp ha)
    · have hcm : z * b * z⁻¹ * b⁻¹ ∈ Zv α' := by
        have h1 : z * b * z⁻¹ * b⁻¹ ∈ ⁅Zv α, Zv c'⁆ := Subgroup.commutator_mem_commutator hz hb
        rw [Subgroup.commutator_comm] at h1
        exact hcon h1
      have : z * b * z⁻¹ = (z * b * z⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact (Zv α' ⊔ Zv c').mul_mem (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hb)
  have hN2 : stab α' ⊓ stab c' ≤ Subgroup.normalizer ((Zv α' ⊔ Zv c' : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer
      (inf_le_left.trans (stab_le_normalizer_Zv hA α'))
      (inf_le_right.trans (stab_le_normalizer_Zv hA c'))
  have hN : stab α' ≤ Subgroup.normalizer ((Zv α' ⊔ Zv c' : Subgroup G) : Set G) := by
    rw [hst]; exact sup_le hN1 hN2
  obtain ⟨g, hg, hgγ⟩ := stab_transitive_on_nbrs hc'n hβ'n
  have hZβ : Zv β' = conjSub (g : G) (Zv c') := by rw [← hgγ, Zv_smul]
  have hZα' : conjSub (g : G) (Zv α') = Zv α' := by
    rw [← Zv_smul, smul_eq_of_mem_stab hg]
  have hnorm : stab α' ≤ Subgroup.normalizer ((Zv α' ⊔ Zv β' : Subgroup G) : Set G) := by
    have h1 : Zv α' ⊔ Zv β' = conjSub (g : G) (Zv α' ⊔ Zv c') := by
      rw [conjSub_sup, hZα', hZβ]
    rw [h1, conjSub_normalizer]
    calc stab α' = conjSub (g : G) (stab α') := (conjSub_eq_of_mem hg).symm
      _ ≤ _ := conjSub_mono _ hN
  exact Zv_not_central_all hA h27 hc hv hn β' (h27 (by omega) α' β' hβ'n (hbA α') hnorm)

theorem tabE_hRle : ⁅Zv α, Qv β⁆ ≤ Zv α' := by
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  have h := (comm_eq_line hA h28 h113a (by omega) hv (bAt_eq_bMin hA h27 hc hv hn α)
    (show IsCritPair₁ α α' from ⟨hc.not_le, hc.dist_eq⟩) hcomm hc).1
  have h2 : ⁅Zv α, Qv β⁆ = ⁅Zv α, Zv α'⁆ := h.symm
  rw [h2, Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer (hZαα'.trans (stab_le_normalizer_Zv hA α'))

theorem tabE_R1 (hvα' : vtype α' = false) {β' c' : Geo H M} (hβ'n : β' ∈ nbrs α')
    (hc'n : c' ∈ nbrs α') (hst : stab α' = Zv α ⊔ (stab α' ⊓ stab c'))
    (hed : stab α' ⊓ stab c' = Qv α' ⊔ Qv c') :
    ⁅Zv β, Zv c'⁆ = Lv c' α' ∧ ⁅Zv β, Zv c'⁆ ≠ ⊥ ∧ ⁅Zv β, Zv c'⁆ = Lv β' α' := by
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  have hvc' : vtype c' = true := tabE_vtype_of_adj_false hc'n hvα'
  have hnle : ¬ Zv c' ≤ Qv β :=
    not_le_Qv_beta_of_claim1 (tabE_hRle hA h27 h28 h113a hc hv hcomm hb3 hn)
      (tabE_claim1_s5 hA h27 h28 h113a hc hv hcomm hb3 hn hβ'n hc'n hZαα' hst)
  have hne : ⁅Zv β, Zv c'⁆ ≠ ⊥ := (comm_ne_bot_iff_not_le_Qv hA h27 hc hv hn hc'n).mpr hnle
  have hβQ : Zv β ≤ Qv α' := Zv_le_Qv_of_dist_lt' (by have := hc.dist_eq'; omega)
  have hle : ⁅Zv β, Zv c'⁆ ≤ Lv c' α' := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hβQ
  have heq : ⁅Zv β, Zv c'⁆ = Lv c' α' :=
    eq_of_le_of_ne_bot_of_card_eq_two hle
      (tabE_card_Lv hA h27 h28 h113a hc hv hcomm hb3 hn hvc' (mem_nbrs_symm' hc'n)) hne
  refine ⟨heq, hne, ?_⟩
  have hinf := tabE_Lv_le_inf hA h27 h28 h113a hc hv hcomm hb3 hn hvc' (mem_nbrs_symm' hc'n)
  have hR1inf := R₁_le_inf hA hc hc'n
  have hRZα' : ⁅Zv β, Zv c'⁆ ≤ Zv α' := heq ▸ (hinf.trans inf_le_right)
  have hZαc : Zv α ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β (hR1inf hr).1).2) x
      (Zv_le_Qv_of_mem_nbrs hc.adj (by omega) hx)).symm
  have hQcc : Qv c' ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA c' (hR1inf hr).2).2) x hx).symm
  have hQα' : Qv α' ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α' (hRZα' hr)).2) x hx).symm
  have hcen : stab α' ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) := by
    rw [hst, hed]
    exact sup_le hZαc (sup_le hQα' hQcc)
  obtain ⟨g, hg, hgγ⟩ := stab_transitive_on_nbrs hc'n hβ'n
  have h1 := tabE_conjSub_Lv_gen g c' α'
  rw [hgγ, smul_eq_of_mem_stab hg, ← heq] at h1
  rw [← h1]
  exact (conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hcen hg))).symm

theorem tabE_Vn_facts (hvα' : vtype α' = false) {β' c' : Geo H M} (hc' : IsCritData α' β' α)
    (hβ'n : β' ∈ nbrs α') (hc'n : c' ∈ nbrs α') (hst : stab α' = Zv α ⊔ (stab α' ⊓ stab c'))
    (hed : stab α' ⊓ stab c' = Qv α' ⊔ Qv c') :
    ∃ u' ∈ nbrs β', u' ≠ α' ∧ Vn α ≤ Qv β' ∧
      ∀ g ∈ Vn α, Zv u' ⊔ Zv β' ≤ Subgroup.centralizer ({g} : Set G) := by
  have hvβ' : vtype β' = true := tabE_vtype_of_adj_false hβ'n hvα'
  have hdβ' : dist α β' + 1 = bMin H M := by
    have := hc'.dist_eq'; rw [CosetGeom.dist_comm]; exact this
  obtain ⟨u', hu'adj, hdu'⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := β') (d := bMin H M - 2)
    (by omega)
  have hu'n : u' ∈ nbrs β' := hu'adj
  have hu'ne : u' ≠ α' := by
    rintro rfl
    have := hc.dist_eq
    omega
  have hVQ : Vn α ≤ Qv u' := by
    refine iSup₂_le fun μ hμ => Zv_le_Qv_of_dist_lt' ?_
    have h1 := dist_triangle hA.amalgam.gen μ α u'
    have h2 : dist μ α = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj μ α from
      (show (graph (H ⊔ M) H M).Adj α μ from hμ).symm)
    omega
  have hVβ'stab : Vn α ≤ stab β' := hVQ.trans (Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hu'n))
  obtain ⟨hR1, -, hR1'⟩ := tabE_R1 hA h27 h28 h113a hc hv hcomm hb3 hn hvα' hβ'n hc'n hst hed
  have hZβ'le : Zv β' ≤ Zv u' ⊔ ⁅Zv β, Zv c'⁆ := by
    have hinf := tabE_Zv_inf_Zv hA h27 h28 h113a hc hv hcomm hb3 hn hvβ' hu'n
    have hLu : Lv β' u' ≤ Zv u' := (le_sup_left.trans hinf.symm.le).trans inf_le_right
    have hNu : Nv β' ≤ Zv u' := (le_sup_right.trans hinf.symm.le).trans inf_le_right
    rw [← tabE_Z0v_sup hA h27 h28 h113a hc hv hcomm hb3 hn β' hvβ',
      ← tabE_Lv_ne_and_sup hA h27 h28 h113a hc hv hcomm hb3 hn hvβ' hu'n (mem_nbrs_symm' hβ'n) hu'ne, hR1']
    exact sup_le (sup_le (hLu.trans le_sup_left) le_sup_right) (hNu.trans le_sup_left)
  have hZu : ∀ g ∈ Vn α, Zv u' ≤ Subgroup.centralizer ({g} : Set G) := by
    intro g hg z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA u' hz).2) g (hVQ hg)).symm
  have hR1c : ∀ g ∈ Vn α, ⁅Zv β, Zv c'⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
    intro g hg r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hrV : r ∈ Vn α := Zv_le_Vn_of_mem_nbrs hc.adj (R₁_le_inf hA hc hc'n hr).1
    exact (tabE_Vn_comm hA hb3 g r hg hrV).symm
  have hall : ∀ g ∈ Vn α, Zv u' ⊔ Zv β' ≤ Subgroup.centralizer ({g} : Set G) := fun g hg =>
    sup_le (hZu g hg) (hZβ'le.trans (sup_le (hZu g hg) (hR1c g hg)))
  refine ⟨u', hu'n, hu'ne, ?_, hall⟩
  intro g hg
  rw [← centralizer_Zv_eq_Qv_all hA h27 hc hv hn β']
  refine ⟨hVβ'stab hg, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have := (Subgroup.mem_centralizer_singleton_iff.mp ((hall g hg) (Subgroup.mem_sup_right hz)))
  exact this

theorem hss32_odd_false_aux (h113c : Hss113cAt H M) (hodd : Odd (bMin H M)) : False := by
  have hvα' : vtype α' = false := vtype_alpha'_of_odd hA hc hv hodd
  obtain ⟨β', hc', -, -⟩ := exists_critData_symm' hA h27 hc hv hcomm hn
  obtain ⟨c', hc'n, -, hst, hed⟩ := exists_choice_c' hA h28 hc hc' (by omega)
  have hβ'n : β' ∈ nbrs α' := hc'.adj
  have hvβ' : vtype β' = true := tabE_vtype_of_adj_false hβ'n hvα'
  obtain ⟨u', hu'n, hu'ne, hVQ, hVc⟩ :=
    tabE_Vn_facts hA h27 h28 h113a hc hv hcomm hb3 hn hvα' hc' hβ'n hc'n hst hed
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  obtain ⟨-, hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have h113 := h113c α' α ⟨not_le_Qv_of_comm_ne hA hcomm, by rw [CosetGeom.dist_comm]; exact hc.dist_eq⟩
    (comm_symm_ne_bot hcomm) hvα'
  obtain ⟨θ, hker, hθ⟩ := tabE_theta_of_113c hA hvα' (inf_le_left) h113
  have hVF : Vn α ≤ stab α' := hVQ.trans (Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hβ'n))
  have hZV : Zv α ≤ Vn α := Zv_le_Vn_self hA α
  have hexp : ∀ x ∈ Vn α, x * x = 1 := fun x hx => tabE_Vn_sq hA hb3 x hx
  have hne : ∃ z ∈ Zv α, z ∉ Qv α' := by
    obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hc.not_le
    exact ⟨z, hz, hzQ⟩
  have hN : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    hZαα'.trans (le_normalizer_pCoreOf 2 (stab α'))
  have hdec : ∀ x ∈ Vn α ⊓ (Zv α ⊔ Qv α'), ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := fun x hx =>
    exists_mul_of_mem_sup_of_le_normalizer hN x (Subgroup.mem_inf.mp hx).2
  have hH3 : ∃ H0 : Subgroup G, Zv α ≤ H0 ∧ H0 ≤ Vn α ∧ H0.relIndex (Vn α) ≤ 2 ∧
      ⁅H0, Zv α'⁆ ≤ Zv α :=
    ⟨Vn α ⊓ (Zv α ⊔ Qv α'), le_inf hZV le_sup_left, inf_le_left,
      tabE_relIndex_le_two θ hker hN hZV hVF hexp hne, commutator_le_of_decomp hA hZα'G hdec⟩
  have hW := claim3'_transport hA h28 hc hv hcomm (by omega) hH3 β' hvβ' α'
    (mem_nbrs_symm' hβ'n) u' hu'n (Ne.symm hu'ne)
  have hsw : ∀ g (hg : g ∈ Vn α), θ ⟨g, hVF hg⟩ = 1 ∨ (θ ⟨g, hVF hg⟩).IsSwap := by
    intro g hg
    refine hθ g (hVF hg) (le_trans ?_ hW)
    exact Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ (hVc g hg))
      Subgroup.index_ne_zero_of_finite
  have hne2 : ∃ v ∈ Vn α, ∀ a ∈ Zv α, v * a⁻¹ ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨γ, hγn, hγβ⟩ := exists_nbr_ne hA α hc.adj
    refine claim1_left hA (Hss27S3At_of_Hss27At h27) hc hv hcomm (by omega) hn γ hγn hγβ ?_
    refine commutator_le_of_decomp hA hZα'G fun x hx => ?_
    obtain ⟨a, ha, hq⟩ := hcon x (Zv_le_Vn_of_mem_nbrs hγn hx)
    refine ⟨a, ha, a⁻¹ * x, ?_, by group⟩
    have := Qv_conj_mem α' (x := a⁻¹) ((stab α').inv_mem (hZαα' ha)) hq
    have e : a⁻¹ * (x * a⁻¹) * (a⁻¹)⁻¹ = a⁻¹ * x := by group
    rwa [e] at this
  exact tabE_no_two_swaps θ hker hZV hVF hexp hne hne2 hsw

end Standing

end Geometry

theorem hss32_odd_false {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M)
    (h113a : Hss113aAt H M) (h113c : Hss113cAt H M) {α β α' : Geo H M} (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb3 : 3 ≤ bMin H M)
    (hodd : Odd (bMin H M)) (hn : ¬ Zv β ≤ centerOf (stab β)) : False :=
  hss32_odd_false_aux hA h27 h28 h113a hc hv hcomm hb3 hn h113c hodd

end F53.Stellmacher

end CFSG.Quasithin
