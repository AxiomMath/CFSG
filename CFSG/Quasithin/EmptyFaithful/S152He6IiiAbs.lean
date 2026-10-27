module

public import CFSG.Quasithin.EmptyFaithful.S152He3Chief
public import CFSG.Quasithin.EmptyFaithful.S152He6Pair

public section

namespace CFSG.Quasithin.He6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin
open scoped commutatorElement

section Helpers

theorem exists_conj_le_of_two_sylow {Y : Type*} [Group Y] [Finite Y] {P S : Subgroup Y}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) (hS : IsPGroup 2 S) :
    ∃ g : Y, ∀ s ∈ S, g * s * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 Y := hP.toSylow hidx
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q P'
  refine ⟨g, fun s hs => ?_⟩
  have hs' : s ∈ (Q : Subgroup Y) := hQ hs
  have h1 : g * s * g⁻¹ ∈ ((g • Q : Sylow 2 Y) : Subgroup Y) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs'
  rw [hg] at h1
  exact h1

theorem mem_sup_eq_mul {Y : Type*} [Group Y] {K T : Subgroup Y}
    (hn : ∀ s ∈ T, ∀ k ∈ K, s * k * s⁻¹ ∈ K) {x : Y} (hx : x ∈ K ⊔ T) :
    ∃ k ∈ K, ∃ s ∈ T, x = k * s := by
  let S : Subgroup Y :=
    { carrier := {x | ∃ k ∈ K, ∃ s ∈ T, x = k * s}
      one_mem' := ⟨1, K.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, s₁, hs₁, rfl⟩ ⟨k₂, hk₂, s₂, hs₂, rfl⟩
        refine ⟨k₁ * (s₁ * k₂ * s₁⁻¹), K.mul_mem hk₁ (hn s₁ hs₁ k₂ hk₂), s₁ * s₂,
          T.mul_mem hs₁ hs₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨k, hk, s, hs, rfl⟩
        have h1 : s⁻¹ * k⁻¹ * (s⁻¹)⁻¹ ∈ K := hn s⁻¹ (T.inv_mem hs) k⁻¹ (K.inv_mem hk)
        refine ⟨s⁻¹ * k⁻¹ * (s⁻¹)⁻¹, h1, s⁻¹, T.inv_mem hs, ?_⟩
        group }
  have hle : K ⊔ T ≤ S := sup_le (fun k hk => ⟨k, hk, 1, T.one_mem, by simp⟩)
    (fun s hs => ⟨1, K.one_mem, s, hs, by simp⟩)
  exact hle hx

end Helpers

section Displacement

variable {Γ : Type} [Group Γ] {X L N : Subgroup Γ}

theorem index_fixV_chiefPsi_mul_le [Finite Γ] {E : Subgroup Γ}
    (hXL : X ≤ Subgroup.normalizer (L : Set Γ)) (hXN : X ≤ Subgroup.normalizer (N : Set Γ))
    (hNL : N ≤ Subgroup.normalizer (L : Set Γ)) (hLN : L ≤ N) (hEX : E ≤ X)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) {e : ↥X} (he : (e : Γ) ∈ E) :
    (@fixV ↥(Ch3z.chiefMod L N) (Ch3z.chiefCG hE)
      (Subgroup.zpowers (Ch3z.chiefPsi hXL hXN e))).index * Nat.card L ≤
      Nat.card ↥(⁅N, E⁆ ⊔ L) := by
  classical
  let _ : CommGroup ↥(Ch3z.chiefMod L N) := Ch3z.chiefCG hE
  set t : MulAut ↥(Ch3z.chiefMod L N) := Ch3z.chiefPsi hXL hXN e with ht
  let f : ↥(Ch3z.chiefMod L N) →* ↥(Ch3z.chiefMod L N) :=
    MonoidHom.mk' (fun w => t w * w⁻¹) (fun a b => by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hker : f.ker = fixV (Subgroup.zpowers t) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV_zpowers]
    show t w * w⁻¹ = 1 ↔ t w = w
    exact mul_inv_eq_one
  have hidx : (fixV (Subgroup.zpowers t)).index = Nat.card f.range := by
    rw [← hker]
    exact Subgroup.index_ker f
  set Cm : Subgroup Γ := ⁅N, E⁆ ⊔ L with hCm
  have hCmN : Cm ≤ N := by
    refine sup_le (Subgroup.commutator_le.mpr fun n hn e' he' => ?_) hLN
    have h1 : (e' : Γ) * n⁻¹ * (e' : Γ)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hXN (hEX he')) n⁻¹).mp (N.inv_mem hn)
    have : ⁅n, e'⁆ = n * (e' * n⁻¹ * e'⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact N.mul_mem hn h1
  set Cbar : Subgroup ↥(Ch3z.chiefMod L N) :=
    (Cm.subgroupOf N).map (Ch3z.chiefIota hNL) with hCbar
  have hrange : f.range ≤ Cbar := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL w
    have hen : (e : Γ) * n * (e : Γ)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hXN e.2) n).mp n.2
    have h1 := Ch3z.chiefPsi_iota hXL hXN hNL e n hen
    refine ⟨⟨(e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹, N.mul_mem hen (N.inv_mem n.2)⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      have hc : (e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹ = ⁅(n : Γ), (e : Γ)⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      show (e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹ ∈ Cm
      rw [hc]
      exact Cm.inv_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator n.2 he))
    · show Ch3z.chiefIota hNL _ = f (Ch3z.chiefIota hNL n)
      have : (⟨(e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹, N.mul_mem hen (N.inv_mem n.2)⟩ : ↥N) =
          ⟨(e : Γ) * n * (e : Γ)⁻¹, hen⟩ * n⁻¹ := rfl
      rw [this, map_mul, map_inv]
      show _ = t (Ch3z.chiefIota hNL n) * (Ch3z.chiefIota hNL n)⁻¹
      rw [ht, h1]
  have hcard : Nat.card Cbar * Nat.card L = Nat.card Cm := by
    set C' : Subgroup ↥N := Cm.subgroupOf N with hC'
    set g : ↥C' →* ↥(Ch3z.chiefMod L N) := (Ch3z.chiefIota hNL).comp C'.subtype with hg
    have h1 := Subgroup.index_mul_card g.ker
    rw [Subgroup.index_ker] at h1
    have hrange' : g.range = Cbar := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker' : Nat.card g.ker = Nat.card L := by
      refine Nat.card_eq_of_bijective
        (fun c => ⟨(((c : ↥C') : ↥N) : Γ), (Ch3z.chiefIota_eq_one_iff hNL _).1 c.2⟩) ⟨?_, ?_⟩
      · intro c d hcd
        have := congrArg Subtype.val hcd
        exact Subtype.ext (Subtype.ext (Subtype.ext this))
      · rintro ⟨l, hl⟩
        refine ⟨⟨⟨⟨l, hLN hl⟩, ?_⟩, ?_⟩, rfl⟩
        · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hl)
        · exact (Ch3z.chiefIota_eq_one_iff hNL _).2 hl
    have hC'card : Nat.card C' = Nat.card Cm :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCmN).toEquiv
    rw [hrange', hker', hC'card] at h1
    exact h1
  rw [hidx]
  have h2 : Nat.card f.range ≤ Nat.card Cbar := Subgroup.card_le_of_le hrange
  calc Nat.card f.range * Nat.card L ≤ Nat.card Cbar * Nat.card L := Nat.mul_le_mul_right _ h2
    _ = Nat.card Cm := hcard

end Displacement

section Mv

variable {Ω : Type*} [Group Ω]

@[expose] def Mv (g : Ω) (B B' : Subgroup Ω) : Prop := ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B'

theorem Mv.mul {g h : Ω} {B C D : Subgroup Ω} (hg : Mv g B C) (hh : Mv h C D) : Mv (h * g) B D := by
  intro x
  rw [hg x, hh (g * x * g⁻¹)]
  have : (h * g) * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
  rw [this]

theorem Mv.inv {g : Ω} {B C : Subgroup Ω} (hg : Mv g B C) : Mv g⁻¹ C B := by
  intro x
  rw [hg (g⁻¹ * x * g⁻¹⁻¹)]
  have : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  rw [this]

theorem Mv.refl_of_mem {g : Ω} {B : Subgroup Ω} (hg : g ∈ B) : Mv g B B := by
  intro x
  constructor
  · intro hx
    exact B.mul_mem (B.mul_mem hg hx) (B.inv_mem hg)
  · intro hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ B :=
      B.mul_mem (B.mul_mem (B.inv_mem hg) hx) hg
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [this] at h1

theorem Mv.of_commute {g : Ω} {B : Subgroup Ω} (hg : ∀ x ∈ B, g * x = x * g) : Mv g B B := by
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ = x := by
      rw [hg x hx]
      group
    rw [this]
    exact hx
  · intro hx
    have h1 : g * (g * x * g⁻¹) = (g * x * g⁻¹) * g := hg (g * x * g⁻¹) hx
    have h2 : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = g⁻¹ * (g * (g * x * g⁻¹)) := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [h1]
        _ = x := by group
    rw [h2] at hx
    exact hx

theorem map_conj_eq_of_Mv {g : Ω} {B C : Subgroup Ω} (h : Mv g B C) :
    B.map (MulAut.conj g).toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    have hmem : g⁻¹ * y * g ∈ B := by
      rw [h]
      have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this]
      exact hy
    refine ⟨g⁻¹ * y * g, hmem, ?_⟩
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group

end Mv

section Reduce

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem Mv_map {Ω' : Type*} [Group Ω'] {X : Subgroup Γ} (ψ : ↥X →* Ω') (s : ↥X)
    {B B' : Subgroup Γ} (h : Mv (s : Γ) B B') :
    Mv (ψ s) ((B.subgroupOf X).map ψ) ((B'.subgroupOf X).map ψ) := by
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨s * g * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    have := (h (g : Γ)).1 (Subgroup.mem_subgroupOf.mp hg)
    simpa using this
  · rintro ⟨g', hg', hgy⟩
    refine ⟨s⁻¹ * g' * s, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 : ((s⁻¹ * g' * s : ↥X) : Γ) ∈ B := by
        rw [h]
        have : (s : Γ) * ((s⁻¹ * g' * s : ↥X) : Γ) * (s : Γ)⁻¹ = g' := by
          simp [mul_assoc]
        rw [this]
        exact Subgroup.mem_subgroupOf.mp hg'
      exact h1
    · have : ψ (s⁻¹ * g' * s) = (ψ s)⁻¹ * ψ g' * ψ s := by simp [map_mul, map_inv]
      rw [this, hgy]
      group

theorem iii_reduce
    (Fam : (G : Type) → [Group G] → Prop)
    (hFamIso : ∀ (G H : Type) [Group G] [Group H], G ≃* H → Fam G → Fam H)
    (hFamSimple : ∀ (G : Type) [Group G], Fam G → IsSimpleGroup G)
    (k : ℕ) {K T X Q E Lc Lt A N : Subgroup Γ} {t : Γ}
    (hXKT : X = K ⊔ T) (hXn : ∀ g ∈ X, ∀ κ ∈ K, g * κ * g⁻¹ ∈ K) (hsyl : IsSylowTwoOf T X)
    (hK : K = Lc ⊔ Lt) (hperf : ⁅Lc, Lc⁆ = Lc)
    (hLt : Mv t⁻¹ Lt Lc) (hLc : Mv t⁻¹ Lc Lt) (ht : t ∈ T)
    (hTperm : ∀ s ∈ T, (Mv s⁻¹ Lc Lc ∧ Mv s⁻¹ Lt Lt) ∨ (Mv s⁻¹ Lc Lt ∧ Mv s⁻¹ Lt Lc))
    (hcomm : ⁅Lc, Lt⁆ ≤ Q) (hO2L : ∀ x : ↥Lc, x ∈ CFSG.Open.pCore 2 ↥Lc → (x : Γ) ∈ Q)
    (hFamQ : Fam (OTwoQuot Lc)) (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hQX : Q ≤ X)
    (hET : E ≤ T) (hEn : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hchief : IsChiefStep X Q A N) (hnot : ¬ ⁅N, E⁆ ≤ A)
    (hbound : Nat.card ↥(⁅N, E⁆ ⊔ A) ≤ k * Nat.card A)
    (final : ∀ (W : Type) [CommGroup W] [Finite W] (P : PairData W)
      (Tb Vb : Subgroup (MulAut W)) (τ : MulAut W),
      Fam ↥P.A → Fam ↥P.A' → P.A ≤ P.Xb → P.A' ≤ P.Xb → Tb ≤ P.Xb → IsPGroup 2 Tb →
      (∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S →
        ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb) →
      (∀ x ∈ P.Xb, ∃ κ ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = κ * s) →
      (∀ Q' : Subgroup (MulAut W), Q' ≤ P.Xb → (Q'.subgroupOf P.Xb).Normal → IsPGroup 2 Q' →
        Q' = ⊥) →
      τ ∈ Tb → (∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A') → (∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A) →
      Vb ≤ Tb → (∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb) → Vb ≠ ⊥ →
      (∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ k) → False) : False := by
  classical
  have hLcK : Lc ≤ K := by rw [hK]; exact le_sup_left
  have hLtK : Lt ≤ K := by rw [hK]; exact le_sup_right
  have hKX : K ≤ X := by rw [hXKT]; exact le_sup_left
  have hTX : T ≤ X := hsyl.1
  have hLcX : Lc ≤ X := hLcK.trans hKX
  have hLtX : Lt ≤ X := hLtK.trans hKX
  have hEX : E ≤ X := hET.trans hTX
  have hXL : X ≤ Subgroup.normalizer (A : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.2.1
  have hXN : X ≤ Subgroup.normalizer (N : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.1
  have hNQ : N ≤ Q := hchief.1.1
  have hNL : N ≤ Subgroup.normalizer (A : Set Γ) := (hNQ.trans hQX).trans hXL
  have hLN : A ≤ N := hchief.2.2.1.le
  have hE' : IsElemAbelian 2 (Ch3z.chiefMod A N) := isElemAbelian_chiefMod hchief hQX hQ2
  let _ : CommGroup ↥(Ch3z.chiefMod A N) := Ch3z.chiefCG hE'
  have hW : ∀ w : ↥(Ch3z.chiefMod A N), w * w = 1 := fun w => by
    simpa [sq] using Ch3z.chiefMod_sq hE' w
  set ψ : ↥X →* MulAut ↥(Ch3z.chiefMod A N) := Ch3z.chiefPsi hXL hXN with hψ
  set X' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := Ch3z.chiefAut X A N with hX'
  have hψX' : ∀ g, ψ g ∈ X' := Ch3z.chiefPsi_mem hXL hXN
  have hsurj : ∀ x ∈ X', ∃ g, ψ g = x := by
    intro x hx
    obtain ⟨g, hg⟩ := Ch3z.chiefHom_surjective hXL hXN ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hO2 : ∀ Q' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)), Q' ≤ X' →
      (Q'.subgroupOf X').Normal → IsPGroup 2 Q' → Q' = ⊥ :=
    fun Q' h1 h2 h3 => D15Proof.normal_two_eq_bot hQX hchief hE' Q' h1 h2 h3
  have hQψ : ∀ g : ↥X, (g : Γ) ∈ Q → ψ g = 1 := fun g hg =>
    map_eq_one_of_normal_two152 ψ hψX' hsurj hO2 hQn hQ2 hg
  have hnotAll : ∃ e₁ : ↥X, (e₁ : Γ) ∈ E ∧ ψ e₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnot
    exact Subgroup.commutator_le.mpr fun n hn e he =>
      commutator_mem_of_chiefPsi_eq_one hXL hXN hNL (hall ⟨e, hEX he⟩ he) hn
  have hdef : ∀ (B : Subgroup Γ) (y : MulAut ↥(Ch3z.chiefMod A N)),
      y ∈ (B.subgroupOf X).map ψ ↔ ∃ g : ↥X, (g : Γ) ∈ B ∧ ψ g = y := by
    intro B y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  set Ab : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (Lc.subgroupOf X).map ψ with hAb
  set Ab' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (Lt.subgroupOf X).map ψ with hAb'
  set Tb : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (T.subgroupOf X).map ψ with hTb
  set Vb : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (E.subgroupOf X).map ψ with hVb
  set tX : ↥X := ⟨t, hTX ht⟩ with htX
  set τ : MulAut ↥(Ch3z.chiefMod A N) := ψ tX with hτ
  have hLt' : Mv t Lc Lt := by simpa using hLt.inv
  have hLc' : Mv t Lt Lc := by simpa using hLc.inv
  have hmvt : Mv τ Ab Ab' := Mv_map ψ tX hLt'
  have hmvt' : Mv τ Ab' Ab := Mv_map ψ tX hLc'
  have hKimg : (K.subgroupOf X).map ψ = Ab ⊔ Ab' := by
    rw [hK, Subgroup.subgroupOf_sup hLcX hLtX, Subgroup.map_sup]
  have hAbX : Ab ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hAb'X : Ab' ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hTbX : Tb ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hXKT' : ∀ x ∈ X', ∃ κ ∈ Ab ⊔ Ab', ∃ s ∈ Tb, x = κ * s := by
    intro x hx
    obtain ⟨g, rfl⟩ := hsurj x hx
    have hgsup : (g : Γ) ∈ K ⊔ T := by
      rw [← hXKT]
      exact g.2
    obtain ⟨κ, hκ, s, hs, hgks⟩ := mem_sup_eq_mul
      (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hgsup
    refine ⟨ψ ⟨κ, hKX hκ⟩, ?_, ψ ⟨s, hTX hs⟩, ⟨⟨s, hTX hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, ?_⟩
    · rw [← hKimg]
      exact ⟨⟨κ, hKX hκ⟩, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
    · rw [← map_mul]
      congr 1
      exact Subtype.ext hgks
  by_cases hAb0 : Ab = ⊥
  ·
    have hAb'0 : Ab' = ⊥ := by
      rw [← map_conj_eq_of_Mv hmvt, hAb0, Subgroup.map_bot]
    have hK'bot : (K.subgroupOf X).map ψ = ⊥ := by
      rw [hKimg, hAb0, hAb'0, sup_bot_eq]
    have h2pow : ∀ x ∈ X', ∃ m : ℕ, x ^ 2 ^ m ∈ (K.subgroupOf X).map ψ := by
      intro x hx
      obtain ⟨g, rfl⟩ := hsurj x hx
      have hgsup : (g : Γ) ∈ K ⊔ T := by
        rw [← hXKT]
        exact g.2
      obtain ⟨κ, hκ, s, hs, hgks⟩ := mem_sup_eq_mul
        (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hgsup
      obtain ⟨m, hm⟩ := hsyl.2.1 ⟨s, hs⟩
      have hsm : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hκ1 : ψ ⟨κ, hKX hκ⟩ = 1 := by
        have : ψ ⟨κ, hKX hκ⟩ ∈ (K.subgroupOf X).map ψ :=
          ⟨⟨κ, hKX hκ⟩, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
        rw [hK'bot] at this
        exact Subgroup.mem_bot.mp this
      refine ⟨m, ?_⟩
      have hg : g = ⟨κ, hKX hκ⟩ * ⟨s, hTX hs⟩ := Subtype.ext hgks
      have : ψ g ^ 2 ^ m = 1 := by
        rw [hg, map_mul, hκ1, one_mul, ← map_pow]
        have : (⟨s, hTX hs⟩ : ↥X) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hsm)
        rw [this, map_one]
      rw [this]
      exact Subgroup.one_mem _
    have hX'bot : X' = ⊥ := eq_bot_of_two_pow152 hO2 h2pow (fun k hk => by
      rw [hK'bot] at hk
      exact Subgroup.mem_bot.mp hk)
    obtain ⟨e₁, -, he₁⟩ := hnotAll
    apply he₁
    have := hψX' e₁
    rw [hX'bot] at this
    exact Subgroup.mem_bot.mp this
  let ψL : ↥Lc →* MulAut ↥(Ch3z.chiefMod A N) := ψ.comp (Subgroup.inclusion hLcX)
  have hle : CFSG.Open.pCore 2 ↥Lc ≤ ψL.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hQψ (Subgroup.inclusion hLcX x) (hO2L x hx)
  let π0 : OTwoQuot Lc →* MulAut ↥(Ch3z.chiefMod A N) := QuotientGroup.lift _ ψL hle
  have hπ0range : π0.range = Ab := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨Subgroup.inclusion hLcX x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk ⟨(g : Γ), Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩
  have hsimple : IsSimpleGroup (OTwoQuot Lc) := hFamSimple _ hFamQ
  have hinj : Function.Injective π0 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal π0.ker with h | h
    · exact h
    · exfalso
      apply hAb0
      rw [← hπ0range, eq_bot_iff]
      rintro _ ⟨q, rfl⟩
      have : q ∈ π0.ker := by rw [h]; exact Subgroup.mem_top q
      rw [MonoidHom.mem_ker] at this
      rw [this]
      exact Subgroup.one_mem _
  let eAb : OTwoQuot Lc ≃* ↥Ab :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hπ0range)
  have hFamAb : Fam ↥Ab := hFamIso _ _ eAb hFamQ
  let eAbAb' : ↥Ab ≃* ↥Ab' :=
    (Subgroup.equivMapOfInjective Ab (MulAut.conj τ).toMonoidHom
      (MulAut.conj τ).injective).trans (MulEquiv.subgroupCongr (map_conj_eq_of_Mv hmvt))
  have hFamAb' : Fam ↥Ab' := hFamIso _ _ eAbAb' hFamAb
  have hsimpAb : IsSimpleGroup ↥Ab := hFamSimple _ hFamAb
  have hsimpAb' : IsSimpleGroup ↥Ab' := hFamSimple _ hFamAb'
  have hperfAb : ⁅Ab, Ab⁆ = Ab := by
    rw [hAb, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLcX, hperf]
  have hperfAb' : ⁅Ab', Ab'⁆ = Ab' := by
    rw [← map_conj_eq_of_Mv hmvt, ← Subgroup.map_commutator, hperfAb]
  have hcommAb : ∀ x ∈ Ab, ∀ y ∈ Ab', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hq : ((⁅a, b⁆ : ↥X) : Γ) ∈ Q := by
      have := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb))
      simpa [commutatorElement_def] using this
    have h1 : ψ ⁅a, b⁆ = 1 := hQψ _ hq
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let Stab2 : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) :=
    { carrier := {g | (Mv g Ab Ab ∧ Mv g Ab' Ab') ∨ (Mv g Ab Ab' ∧ Mv g Ab' Ab)}
      one_mem' := Or.inl ⟨fun x => by simp, fun x => by simp⟩
      mul_mem' := by
        rintro g h (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩) (⟨hh1, hh2⟩ | ⟨hh1, hh2⟩)
        · exact Or.inl ⟨hh1.mul hg1, hh2.mul hg2⟩
        · exact Or.inr ⟨hh1.mul hg2, hh2.mul hg1⟩
        · exact Or.inr ⟨hh1.mul hg1, hh2.mul hg2⟩
        · exact Or.inl ⟨hh1.mul hg2, hh2.mul hg1⟩
      inv_mem' := by
        rintro g (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩)
        · exact Or.inl ⟨hg1.inv, hg2.inv⟩
        · exact Or.inr ⟨hg2.inv, hg1.inv⟩ }
  have hAbS : Ab ≤ Stab2 := by
    intro g hg
    exact Or.inl ⟨Mv.refl_of_mem hg, Mv.of_commute fun x hx => hcommAb g hg x hx⟩
  have hAb'S : Ab' ≤ Stab2 := by
    intro g hg
    exact Or.inl ⟨Mv.of_commute fun x hx => (hcommAb x hx g hg).symm, Mv.refl_of_mem hg⟩
  have hTbS : Tb ≤ Stab2 := by
    rintro _ ⟨s, hs, rfl⟩
    have hsT : (s : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hs
    have hs' : (⟨(s : Γ)⁻¹, X.inv_mem s.2⟩ : ↥X) = s⁻¹ := rfl
    have hinv : ψ s⁻¹ ∈ Stab2 := by
      rcases hTperm (s : Γ) hsT with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Mv_map ψ s⁻¹ h1, Mv_map ψ s⁻¹ h2⟩
      · exact Or.inr ⟨Mv_map ψ s⁻¹ h1, Mv_map ψ s⁻¹ h2⟩
    have := Stab2.inv_mem hinv
    rwa [map_inv, inv_inv] at this
  have hX'S : X' ≤ Stab2 := by
    intro x hx
    obtain ⟨κ, hκ, s, hs, rfl⟩ := hXKT' x hx
    exact Stab2.mul_mem ((sup_le hAbS hAb'S) hκ) (hTbS hs)
  let P : PairData ↥(Ch3z.chiefMod A N) :=
    { A := Ab, A' := Ab', Xb := X', hW := hW, comm := hcommAb, simpA := hsimpAb,
      simpA' := hsimpAb', perfA := hperfAb, perfA' := hperfAb',
      irr := fun U hU => Ch3z.chiefMod_irr hchief hQX U hU,
      norm := fun g hg => hX'S hg }
  have hT2 : IsPGroup 2 Tb := (hsyl.2.1.comap_subtype (K := X)).map ψ
  have hconj2 : ∀ S : Subgroup (MulAut ↥(Ch3z.chiefMod A N)), S ≤ X' → IsPGroup 2 S →
      ∃ g ∈ X', ∀ s ∈ S, g * s * g⁻¹ ∈ Tb := by
    intro S hSX hS2
    let φ : ↥X →* ↥X' := Ch3z.chiefHom hXL hXN
    have hφ : Function.Surjective φ := Ch3z.chiefHom_surjective hXL hXN
    have hφψ : ∀ g : ↥X, ((φ g : ↥X') : MulAut ↥(Ch3z.chiefMod A N)) = ψ g := fun g => rfl
    set Pm : Subgroup ↥X' := (T.subgroupOf X).map φ with hPm
    have hPm2 : IsPGroup 2 Pm := (hsyl.2.1.comap_subtype (K := X)).map φ
    have hPmidx : ¬ 2 ∣ Pm.index := by
      intro h2
      exact hsyl.2.2 (h2.trans (Subgroup.index_map_dvd (T.subgroupOf X) hφ))
    have hS' : IsPGroup 2 (S.subgroupOf X') := hS2.comap_subtype
    obtain ⟨g', hg'⟩ := exists_conj_le_of_two_sylow hPm2 hPmidx hS'
    refine ⟨(g' : MulAut ↥(Ch3z.chiefMod A N)), g'.2, fun s hs => ?_⟩
    have h1 := hg' ⟨s, hSX hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
    obtain ⟨u, hu, hu'⟩ := h1
    refine ⟨u, hu, ?_⟩
    have := congrArg Subtype.val hu'
    simpa [hφψ] using this
  have hτTb : τ ∈ Tb := ⟨tX, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hVT : Vb ≤ Tb := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Subgroup.mem_subgroupOf.mpr (hET (Subgroup.mem_subgroupOf.mp he)), rfl⟩
  have hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    refine ⟨s * e * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using hEn (s : Γ) (Subgroup.mem_subgroupOf.mp hs) (e : Γ) (Subgroup.mem_subgroupOf.mp he)
  have hVne : Vb ≠ ⊥ := by
    intro h
    obtain ⟨e₁, he₁E, he₁⟩ := hnotAll
    apply he₁
    have : ψ e₁ ∈ Vb := ⟨e₁, Subgroup.mem_subgroupOf.mpr he₁E, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hbd : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ k := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := index_fixV_chiefPsi_mul_le hXL hXN hNL hLN hEX hE' (e := e)
      (Subgroup.mem_subgroupOf.mp he)
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : (@fixV ↥(Ch3z.chiefMod A N) (Ch3z.chiefCG hE')
        (Subgroup.zpowers (Ch3z.chiefPsi hXL hXN e))).index * Nat.card A ≤ k * Nat.card A :=
      h1.trans hbound
    have h3 := Nat.le_of_mul_le_mul_right h2 hApos
    rw [← index_fixV_zpowers_eq_card_cmt]
    exact h3
  exact final _ P Tb Vb τ hFamAb hFamAb' hAbX hAb'X hTbX hT2 hconj2 hXKT' hO2 hτTb hmvt hmvt'
    hVT hVn hVne hbd

end Reduce

end CFSG.Quasithin.He6
