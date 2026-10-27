module

public import CFSG.Milestones.ASVolI.F4K.Main
public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF48s_dihedral_pow {Q : Type*} [Group Q] [Finite Q] {σ τ : Q} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hgen : Subgroup.closure ({σ, τ} : Set Q) = ⊤) {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card Q = 2 * m) : (σ * τ) ^ m = 1 := by
  set ρ := σ * τ with hρ
  set C : Subgroup Q := Subgroup.zpowers ρ with hC
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hρc : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    rw [hρ, hσi, mul_inv_rev, hσi, hτi, ← mul_assoc, hσ, one_mul]
  have hconj : ∀ c ∈ C, σ * c * σ⁻¹ ∈ C := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have : σ * ρ ^ k * σ⁻¹ = (σ * ρ * σ⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [this, hρc]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers ρ)) k
  have hconj' : ∀ c ∈ C, σ⁻¹ * c * σ ∈ C := by
    intro c hc
    have := hconj c hc
    rwa [hσi] at this ⊢
  have key : ∀ q : Q, q ∈ C ∨ q * σ ∈ C := by
    intro q
    have hq : q ∈ Subgroup.closure ({σ, τ} : Set Q) := by rw [hgen]; trivial
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · right; rw [hσ]; exact C.one_mem
      · right
        have : x * σ = ρ⁻¹ := by rw [hρ, mul_inv_rev, hσi, hτi]
        rw [this]; exact C.inv_mem (Subgroup.mem_zpowers ρ)
    | one => left; exact C.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · left; exact C.mul_mem hx hy
      · right; rw [mul_assoc]; exact C.mul_mem hx hy
      · right
        have e : x * y * σ = (x * σ) * (σ⁻¹ * y * σ) := by group
        rw [e]; exact C.mul_mem hx (hconj' y hy)
      · left
        have e : x * y = (x * σ) * (σ⁻¹ * (y * σ) * σ) * (σ * σ)⁻¹ := by group
        rw [e, hσ, inv_one, mul_one]
        exact C.mul_mem hx (hconj' _ hy)
    | inv x _ hx =>
      rcases hx with hx | hx
      · left; exact C.inv_mem hx
      · right
        have e : x⁻¹ * σ = σ * (x * σ)⁻¹ * σ⁻¹ := by rw [hσi]; group
        rw [e]; exact hconj _ (C.inv_mem hx)
  haveI : Fintype Q := Fintype.ofFinite Q
  set n := orderOf ρ with hn
  have hCcard : Nat.card C = n := Nat.card_zpowers ρ
  have hle : 2 * m ≤ 2 * n := by
    rw [← hcard, ← hCcard]
    have hsub : (Set.univ : Set Q) ⊆ (C : Set Q) ∪ (fun c => c * σ) '' (C : Set Q) := by
      intro q _
      rcases key q with h | h
      · exact Or.inl h
      · refine Or.inr ⟨q * σ, h, ?_⟩
        show q * σ * σ = q
        rw [mul_assoc, hσ, mul_one]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at h1
    have h2 := Set.ncard_union_le (C : Set Q) ((fun c => c * σ) '' (C : Set Q))
    have h3 := Set.ncard_image_le (f := fun c => c * σ) (s := (C : Set Q)) (Set.toFinite _)
    have h4 : (C : Set Q).ncard = Nat.card C := Nat.card_coe_set_eq (C : Set Q) |>.symm
    omega
  have hdvd : n ∣ 2 * m := by rw [← hcard]; exact orderOf_dvd_natCard ρ
  have hne : n ≠ 2 * m := by
    intro h2m
    have htop : C = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hCcard, hcard, h2m]
    have hσC : σ ∈ C := by rw [htop]; trivial
    have hτC : τ ∈ C := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hσC
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hτC
    have hcomm : σ * τ = τ * σ := by
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have hρ2 : ρ ^ 2 = 1 := by
      rw [hρ, pow_two]
      calc σ * τ * (σ * τ) = σ * (τ * σ) * τ := by group
        _ = σ * (σ * τ) * τ := by rw [hcomm]
        _ = (σ * σ) * (τ * τ) := by group
        _ = 1 := by rw [hσ, hτ, one_mul]
    have := orderOf_le_of_pow_eq_one (by norm_num) hρ2
    omega
  have hnm : n = m := by
    obtain ⟨k, hk⟩ := hdvd
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · omega
    · nlinarith
  rw [← hnm, hn]
  exact pow_orderOf_eq_one ρ

theorem burnsideF48s_dihedral_mem {G : Type*} [Group G] {σ τ : G} {N : Subgroup G}
    (hnorm : ∀ w ∈ Subgroup.closure ({σ, τ} : Set G), ∀ n ∈ N, w * n * w⁻¹ ∈ N)
    (hσ : σ * σ ∈ N) (hτ : τ * τ ∈ N) {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card (↥(Subgroup.closure ({σ, τ} : Set G)) ⧸
      N.subgroupOf (Subgroup.closure ({σ, τ} : Set G))) = 2 * m) :
    (σ * τ) ^ m ∈ N := by
  set W := Subgroup.closure ({σ, τ} : Set G) with hW
  have hNn : (N.subgroupOf W).Normal :=
    ⟨fun n hn w => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm w w.2 n hn⟩
  set Q := W ⧸ N.subgroupOf W
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσW : σ ∈ W := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτW : τ ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let σ' : W := ⟨σ, hσW⟩
  let τ' : W := ⟨τ, hτW⟩
  let π : W →* Q := QuotientGroup.mk' (N.subgroupOf W)
  have hπ : ∀ w : W, π w = 1 ↔ (w : G) ∈ N := by
    intro w
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h1 : π σ' * π σ' = 1 := by rw [← map_mul, hπ]; exact hσ
  have h2 : π τ' * π τ' = 1 := by rw [← map_mul, hπ]; exact hτ
  have hgen : Subgroup.closure ({π σ', π τ'} : Set Q) = ⊤ := by
    have hW' : Subgroup.closure ({σ', τ'} : Set W) = ⊤ := by
      have := Subgroup.closure_closure_coe_preimage (k := ({σ, τ} : Set G))
      rw [← this]
      congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
    have hmap := MonoidHom.map_closure π ({σ', τ'} : Set W)
    rw [hW', Set.image_pair, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)] at hmap
    exact hmap.symm
  have := burnsideF48s_dihedral_pow h1 h2 hgen hm hcard
  rw [← map_mul, ← map_pow, hπ] at this
  simpa using this

theorem burnsideF48s_apartment_other {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S) {u : c.Γ}
    (hu : u ∈ S) : ∃ v ∈ S, v ≠ u ∧ CosetGeom.vtype v = CosetGeom.vtype u := by
  obtain ⟨e⟩ := hS
  haveI : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨i, hi⟩ := e.surjective ⟨u, hu⟩
  have hone : ((1 : Fin (2 * m)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hadj : ∀ j : Fin (2 * m), c.graph.Adj (e j).1 (e (j + 1)).1 := by
    intro j
    have h := (e.map_rel_iff (a := j) (b := j + 1)).2 (by
      rw [SimpleGraph.cycleGraph_adj']
      right
      rw [add_sub_cancel_left, hone])
    exact h
  refine ⟨(e (i + 1 + 1)).1, (e (i + 1 + 1)).2, ?_, ?_⟩
  · intro h
    have h1 : e (i + 1 + 1) = e i := by rw [hi]; exact Subtype.ext h
    have h2 := e.injective h1
    rw [add_assoc, add_eq_left] at h2
    have h3 := congrArg Fin.val h2
    rw [Fin.val_add, hone, Fin.val_zero] at h3
    rw [Nat.mod_eq_of_lt (by omega)] at h3
    omega
  · have t1 := CosetGeom.vtype_ne_of_adj (hadj i)
    have t2 := CosetGeom.vtype_ne_of_adj (hadj (i + 1))
    have hu' : (e i).1 = u := by rw [hi]
    rw [← hu']
    revert t1 t2
    cases CosetGeom.vtype (e i).1 <;> cases CosetGeom.vtype (e (i + 1)).1 <;>
      cases CosetGeom.vtype (e (i + 1 + 1)).1 <;> simp

open scoped Pointwise in
theorem burnsideF48s_smul_mem_of_setStab {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {S : Set c.Γ} {g : c.G0} (hg : g ∈ setStab c S) {v : c.Γ}
    (hv : v ∈ S) : g • v ∈ S := by
  have h : g • S = S := MulAction.mem_stabilizer_iff.1 hg
  rw [← h]
  exact Set.smul_mem_smul_set hv

theorem burnsideF48s_mem_pointwiseStab {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {S : Set c.Γ} {g : c.G0} :
    g ∈ pointwiseStab c S ↔ ∀ v ∈ S, g • v = v := by
  unfold pointwiseStab
  simp only [Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem burnsideF48s_conj_mem_pointwiseStab {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {S : Set c.Γ} {g k : c.G0} (hg : g ∈ setStab c S)
    (hk : k ∈ pointwiseStab c S) : g * k * g⁻¹ ∈ pointwiseStab c S := by
  rw [burnsideF48s_mem_pointwiseStab] at hk ⊢
  intro v hv
  have hv' : g⁻¹ • v ∈ S := burnsideF48s_smul_mem_of_setStab ((setStab c S).inv_mem hg) hv
  rw [mul_smul, mul_smul, hk _ hv', smul_inv_smul]

theorem burnsideF48s_pow_mul_mem {G : Type*} [Group G] {K : Subgroup G} {ρ : G}
    (hρ : ∀ k ∈ K, ρ⁻¹ * k * ρ ∈ K) {k : G} (hk : k ∈ K) :
    ∀ n : ℕ, ∃ k' ∈ K, (ρ * k) ^ n = ρ ^ n * k'
  | 0 => ⟨1, K.one_mem, by simp⟩
  | n + 1 => by
    obtain ⟨k', hk', h⟩ := burnsideF48s_pow_mul_mem hρ hk n
    refine ⟨ρ⁻¹ * k' * ρ * k, K.mul_mem (hρ k' hk') hk, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

section


theorem burnsideF48s_rel_G0 (h45 : F_4_5) (h46 : F_4_6) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) :
    ∃ (sx sl : β.G0) (K : Subgroup β.G0),
      sx ∈ stv β β.xv ∧ sx ∉ stv β β.lv ∧ sl ∈ stv β β.lv ∧ sl ∉ stv β β.xv ∧
      IsComplementIn K (Sp p Gp β) (stv β β.xv ⊓ stv β β.lv) ∧
      (∀ k ∈ K, sx * k * sx⁻¹ ∈ K) ∧ (∀ k ∈ K, sl * k * sl⁻¹ ∈ K) ∧
      sx * sx ∈ K ∧ sl * sl ∈ K ∧
      ∀ k₁ ∈ K, ∀ k₂ ∈ K, (sx * k₁ * (sl * k₂)) ^ κ.m ∈ K := by
  have hm : 3 ≤ κ.m := burnsideF48_three_le_m κ
  have hadj : β.graph.Adj β.xv β.lv := CosetGeom.adj_γ₀_γ₁
  have hsimp : IsSimplex β.graph ({β.xv, β.lv} : Set β.Γ) := Or.inr ⟨_, _, hadj, rfl⟩
  obtain ⟨Sig, hSig, hsub, -⟩ :=
    (burnside_as_F_4_14_of h45 h46 κ p f E Gp M₁ M₂ hyp Y β hβ hs).2 _ _ hsimp hsimp
  have hxS : β.xv ∈ Sig := hsub (Set.mem_insert _ _)
  have hlS : β.lv ∈ Sig := hsub (Set.mem_insert_of_mem _ rfl)
  obtain ⟨sx, sl, hW, -⟩ :=
    (burnside_as_F_4_15_of h45 h46 κ p f E Gp M₁ M₂ hyp Y β hβ hs).2.1
      (fun h => hκ.1 h.2) Sig hSig hxS hlS
  have hLie : IsLieExtAmalgam M₁ M₂ := ⟨κ, p, f, Gp, hκ, hyp⟩
  obtain ⟨⟨-, -, hcompl⟩, -⟩ :=
    burnside_as_F_4_16_of h45 h46 κ p f E Gp M₁ M₂ hyp hLie Y β hβ hs Sig hSig hxS hlS
  obtain ⟨hsx, hsl, ⟨hx1, hx2, -, -⟩, ⟨hl1, hl2, -, -⟩, hcard, htrans⟩ := hW
  set K := setStab β Sig ⊓ pointwiseStab β Sig with hK
  have hKnorm : ∀ g ∈ setStab β Sig, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    exact ⟨(setStab β Sig).mul_mem ((setStab β Sig).mul_mem hg hk.1) ((setStab β Sig).inv_mem hg),
      burnsideF48s_conj_mem_pointwiseStab hg hk.2⟩
  have hsq : ∀ s ∈ setStab β Sig, (∀ w ∈ Sig, (s * s) • w = w) → s * s ∈ K :=
    fun s hs hw => ⟨(setStab β Sig).mul_mem hs hs, burnsideF48s_mem_pointwiseStab.2 hw⟩
  have hWle : Subgroup.closure ({sx, sl} : Set β.G0) ≤ setStab β Sig := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx2
    · exact hl2
  have hρ : (sx * sl) ^ κ.m ∈ K := by
    refine ⟨(setStab β Sig).pow_mem ((setStab β Sig).mul_mem hx2 hl2) _, ?_⟩
    refine burnsideF48s_dihedral_mem (fun w hw n hn => burnsideF48s_conj_mem_pointwiseStab
      (hWle hw) hn) (burnsideF48s_mem_pointwiseStab.2 hx1) (burnsideF48s_mem_pointwiseStab.2 hl1)
      (by omega) hcard
  have hnot : ∀ {s t : β.G0} {u : β.Γ}, u ∈ Sig → t ∈ stv β u →
      (∀ u' ∈ Sig, ∀ v ∈ Sig, CosetGeom.vtype u' = CosetGeom.vtype v →
        ∃ w ∈ Subgroup.closure ({s, t} : Set β.G0), w • u' = v) → s ∉ stv β u := by
    intro s t u hu ht htr hs'
    obtain ⟨v, hv, hvu, hvt⟩ := burnsideF48s_apartment_other β (by omega) hSig hu
    obtain ⟨w, hw, hwu⟩ := htr u hu v hv hvt.symm
    have hle : Subgroup.closure ({s, t} : Set β.G0) ≤ stv β u := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hs'
      · exact ht
    have : w • u = u := MulAction.mem_stabilizer_iff.1 (hle hw)
    exact hvu (hwu.symm.trans this)
  refine ⟨sx, sl, K, hsx, hnot hlS hsl htrans, hsl, ?_, hcompl,
    hKnorm sx hx2, hKnorm sl hl2, hsq sx hx2 hx1, hsq sl hl2 hl1, ?_⟩
  · refine hnot hxS hsx ?_
    intro u' hu' v hv htv
    obtain ⟨w, hw, hwv⟩ := htrans u' hu' v hv htv
    refine ⟨w, ?_, hwv⟩
    have e : ({sl, sx} : Set β.G0) = {sx, sl} := Set.pair_comm _ _
    rw [e]
    exact hw
  · intro k₁ hk₁ k₂ hk₂
    have hslK : ∀ k ∈ K, sl⁻¹ * k * sl ∈ K := by
      intro k hk
      have := hKnorm sl⁻¹ ((setStab β Sig).inv_mem hl2) k hk
      simpa using this
    have hρK : ∀ k ∈ K, (sx * sl)⁻¹ * k * (sx * sl) ∈ K := by
      intro k hk
      have := hKnorm (sx * sl)⁻¹ ((setStab β Sig).inv_mem ((setStab β Sig).mul_mem hx2 hl2)) k hk
      simpa using this
    have hk₃ : sl⁻¹ * k₁ * sl * k₂ ∈ K := K.mul_mem (hslK k₁ hk₁) hk₂
    have e : sx * k₁ * (sl * k₂) = (sx * sl) * (sl⁻¹ * k₁ * sl * k₂) := by group
    obtain ⟨k', hk', h⟩ := burnsideF48s_pow_mul_mem hρK hk₃ κ.m
    rw [e, h]
    exact K.mul_mem hρ hk'

end


@[expose] noncomputable def burnsideF48s_iota12 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) : ↥(M₁ ⊓ M₂) →* β.G0 :=
  (f1 (c := β)).comp (RankTwoAmalgam.ofSubgroups M₁ M₂).α1

theorem burnsideF48s_iota12_eq_f2 {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (d : ↥(M₁ ⊓ M₂)) :
    burnsideF48s_iota12 β d = f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 d) :=
  Subtype.ext ((β.comm1 d).trans (β.comm2 d).symm)

theorem burnsideF48s_iota12_coe {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (d : ↥(M₁ ⊓ M₂)) : ((burnsideF48s_iota12 β d : β.G0) : Y) = β.φ12 d :=
  β.comm1 d

theorem burnsideF48s_iota12_injective {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} (hβ : β.IsFaithful) : Function.Injective (burnsideF48s_iota12 β) :=
  (f1_injective β hβ).comp (Subgroup.inclusion_injective inf_le_left)

theorem burnsideF48s_range_iota12 {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    {β : Cpl M₁ M₂ Y} (hβ : β.IsFaithful) :
    (burnsideF48s_iota12 β).range = stv β β.xv ⊓ stv β β.lv := by
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    refine ⟨MulAction.mem_stabilizer_iff.mpr (f1_smul_xv _), ?_⟩
    rw [burnsideF48s_iota12_eq_f2]
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv _)
  · rintro g ⟨hgx, hgl⟩
    rw [stv_xv_eq_range] at hgx
    obtain ⟨a, rfl⟩ := hgx
    obtain ⟨b, hb⟩ := stv_lv_le_range_f2 β hgl
    have hmem : β.φ1 a ∈ β.φ12.range := by
      rw [← β.inter]
      exact ⟨⟨a, rfl⟩, ⟨b, congrArg Subtype.val hb⟩⟩
    obtain ⟨d, hd⟩ := hmem
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact (burnsideF48s_iota12_coe β d).trans hd

theorem burnsideF48s_pCoreOf_le {E : Type} [Group E] (p : ℕ) (H : Subgroup E) : pCoreOf p H ≤ H := by
  unfold pCoreOf
  rintro _ ⟨x, -, rfl⟩
  exact x.2

section


theorem burnsideF48s_rel (h45 : F_4_5) (h46 : F_4_6) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) :
    ∃ (a : ↥M₁) (b : ↥M₂) (K : Subgroup E),
      (a : E) ∉ M₂ ∧ (b : E) ∉ M₁ ∧ IsComplementIn K (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) (M₁ ⊓ M₂) ∧
      (∀ k ∈ K, (a : E) * k * (a : E)⁻¹ ∈ K) ∧ (∀ k ∈ K, (b : E) * k * (b : E)⁻¹ ∈ K) ∧
      (a : E) * a ∈ K ∧ (b : E) * b ∈ K ∧
      ∀ (a' : ↥M₁) (b' : ↥M₂), (a : E)⁻¹ * a' ∈ K → (b : E)⁻¹ * b' ∈ K →
        ∃ c : ↥(M₁ ⊓ M₂), (c : E) ∈ K ∧ (β.φ1 a' * β.φ2 b') ^ κ.m = β.φ12 c := by
  obtain ⟨sx, sl, KG, hsx, hsx', hsl, hsl', hcompl, hnx, hnl, hx2, hl2, hrel⟩ :=
    burnsideF48s_rel_G0 h45 h46 hyp hκ β hβ hs
  set ι := burnsideF48s_iota12 β with hιdef
  have hιinj : Function.Injective ι := burnsideF48s_iota12_injective hβ
  have hιrange : ι.range = stv β β.xv ⊓ stv β β.lv := burnsideF48s_range_iota12 hβ
  have hKG : KG ≤ ι.range := hιrange ▸ hcompl.2.1
  set S₀ : Subgroup E := pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) with hS₀
  have hS₀le : S₀ ≤ M₁ ⊓ M₂ := (burnsideF48s_pCoreOf_le p _).trans inf_le_right
  have hSp : Sp p Gp β = (S₀.subgroupOf (M₁ ⊓ M₂)).map ι :=
    Subgroup.map_map _ _ _
  set K : Subgroup E := (KG.comap ι).map (M₁ ⊓ M₂).subtype with hK
  have hmemK : ∀ d : ↥(M₁ ⊓ M₂), (d : E) ∈ K ↔ ι d ∈ KG := by
    intro d
    show (M₁ ⊓ M₂).subtype d ∈ (KG.comap ι).map (M₁ ⊓ M₂).subtype ↔ _
    rw [Subgroup.mem_map_iff_mem (M₁ ⊓ M₂).subtype_injective, Subgroup.mem_comap]
  have hKle : K ≤ M₁ ⊓ M₂ := by
    rintro _ ⟨d, -, rfl⟩
    exact d.2
  have hG12 : (stv β β.xv ⊓ stv β β.lv).comap ι = ⊤ := by
    rw [eq_top_iff]
    intro d _
    show ι d ∈ stv β β.xv ⊓ stv β β.lv
    rw [← hιrange]
    exact ⟨d, rfl⟩
  have h1 := (IsComplementIn.comap_iff ι hιinj hKG (by rw [hSp]; exact Subgroup.map_le_range _ _)
    (hιrange ▸ le_refl _)).1 hcompl
  rw [hSp, Subgroup.comap_map_eq_self_of_injective hιinj, hG12] at h1
  have hrange : (M₁ ⊓ M₂).subtype.range = M₁ ⊓ M₂ := Subgroup.range_subtype _
  have hcompl' : IsComplementIn K S₀ (M₁ ⊓ M₂) := by
    refine (IsComplementIn.comap_iff (M₁ ⊓ M₂).subtype (M₁ ⊓ M₂).subtype_injective
      (by rw [hrange]; exact hKle) (by rw [hrange]; exact hS₀le) (by rw [hrange])).2 ?_
    rw [hK, Subgroup.comap_map_eq_self_of_injective (M₁ ⊓ M₂).subtype_injective]
    have e : (M₁ ⊓ M₂).comap (M₁ ⊓ M₂).subtype = ⊤ := Subgroup.subgroupOf_self _
    rw [e]
    exact h1
  let φ₁ : ↥M₁ →* β.G0 := f1 (c := β)
  let φ₂ : ↥M₂ →* β.G0 := f2 (c := β)
  have hf1inj : Function.Injective φ₁ := f1_injective β hβ
  have hf2inj : Function.Injective φ₂ := f2_injective β hβ
  have hsx1 : sx ∈ φ₁.range := stv_xv_eq_range β ▸ hsx
  have hsl1 : sl ∈ φ₂.range := stv_lv_le_range_f2 β hsl
  obtain ⟨a, ha⟩ := hsx1
  obtain ⟨b, hb⟩ := hsl1
  have hι1 : ∀ d : ↥(M₁ ⊓ M₂), ι d = φ₁ ⟨d, d.2.1⟩ := fun d => rfl
  have hι2 : ∀ d : ↥(M₁ ⊓ M₂), ι d = φ₂ ⟨d, d.2.2⟩ :=
    fun d => burnsideF48s_iota12_eq_f2 β d
  have hKGι : ∀ g ∈ KG, ∃ d : ↥(M₁ ⊓ M₂), ι d = g ∧ (d : E) ∈ K := by
    intro g hg
    obtain ⟨d, rfl⟩ := hKG hg
    exact ⟨d, rfl, (hmemK d).2 hg⟩
  have hmemι : ∀ d : ↥(M₁ ⊓ M₂), ι d ∈ stv β β.xv ⊓ stv β β.lv := by
    intro d
    rw [← hιrange]
    exact ⟨d, rfl⟩
  refine ⟨a, b, K, ?_, ?_, hcompl', ?_, ?_, ?_, ?_, ?_⟩
  · intro haM
    apply hsx'
    have e : sx = ι ⟨(a : E), ⟨a.2, haM⟩⟩ := by rw [← ha, hι1]
    rw [e]
    exact (hmemι _).2
  · intro hbM
    apply hsl'
    have e : sl = ι ⟨(b : E), ⟨hbM, b.2⟩⟩ := by rw [← hb, hι2]
    rw [e]
    exact (hmemι _).1
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd'eq, hd'K⟩ := hKGι _ (hnx _ hd)
    have e : φ₁ (a * ⟨(d : E), d.2.1⟩ * a⁻¹) = φ₁ ⟨(d' : E), d'.2.1⟩ := by
      rw [map_mul, map_mul, map_inv, ha, ← hι1, ← hι1, hd'eq]
    have key := congrArg Subtype.val (hf1inj e)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key
    show (a : E) * (d : E) * (a : E)⁻¹ ∈ K
    rw [key]
    exact hd'K
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd'eq, hd'K⟩ := hKGι _ (hnl _ hd)
    have e : φ₂ (b * ⟨(d : E), d.2.2⟩ * b⁻¹) = φ₂ ⟨(d' : E), d'.2.2⟩ := by
      rw [map_mul, map_mul, map_inv, hb, ← hι2, ← hι2, hd'eq]
    have key := congrArg Subtype.val (hf2inj e)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key
    show (b : E) * (d : E) * (b : E)⁻¹ ∈ K
    rw [key]
    exact hd'K
  · obtain ⟨d', hd'eq, hd'K⟩ := hKGι _ hx2
    have e : φ₁ (a * a) = φ₁ ⟨(d' : E), d'.2.1⟩ := by
      rw [map_mul, ha, ← hι1, hd'eq]
    have key := congrArg Subtype.val (hf1inj e)
    simp only [Subgroup.coe_mul] at key
    rw [key]
    exact hd'K
  · obtain ⟨d', hd'eq, hd'K⟩ := hKGι _ hl2
    have e : φ₂ (b * b) = φ₂ ⟨(d' : E), d'.2.2⟩ := by
      rw [map_mul, hb, ← hι2, hd'eq]
    have key := congrArg Subtype.val (hf2inj e)
    simp only [Subgroup.coe_mul] at key
    rw [key]
    exact hd'K
  · intro a' b' ha' hb'
    obtain ⟨d₁, hd₁, hd₁eq⟩ := ha'
    obtain ⟨d₂, hd₂, hd₂eq⟩ := hb'
    have hd₁E : ((d₁ : ↥(M₁ ⊓ M₂)) : E) = (a : E)⁻¹ * a' := hd₁eq
    have hd₂E : ((d₂ : ↥(M₁ ⊓ M₂)) : E) = (b : E)⁻¹ * b' := hd₂eq
    have ha'eq : φ₁ a' = sx * ι d₁ := by
      rw [← ha, hι1, ← map_mul]
      congr 1
      apply Subtype.ext
      show (a' : E) = a * ((d₁ : ↥(M₁ ⊓ M₂)) : E)
      rw [hd₁E]
      group
    have hb'eq : φ₂ b' = sl * ι d₂ := by
      rw [← hb, hι2, ← map_mul]
      congr 1
      apply Subtype.ext
      show (b' : E) = b * ((d₂ : ↥(M₁ ⊓ M₂)) : E)
      rw [hd₂E]
      group
    obtain ⟨c, hcι, hcK⟩ := hKGι _ (hrel _ hd₁ _ hd₂)
    refine ⟨c, hcK, ?_⟩
    rw [← burnsideF48s_iota12_coe, ← hιdef, hcι, ← ha'eq, ← hb'eq]
    rfl

end

end CFSG.ASVolI
