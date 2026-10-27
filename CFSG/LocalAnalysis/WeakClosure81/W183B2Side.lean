module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2NC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183b2_perm_cj_self_iff (h : Br2TwoComp Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y) :
    cj y L₁ = L₁ ↔ cj y L₂ = L₂ := by
  constructor
  · intro hyL
    rcases h.perm y hy with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hyL.symm.trans h1) h.ne
  · intro hyL
    rcases h.perm y hy with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd (hyL.symm.trans h2) h.ne.symm

private theorem w183b2_perm_cj_swap (h : Br2TwoComp Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y)
    (hyL : cj y L₁ = L₂) : cj y L₂ = L₁ := by
  rcases h.perm y hy with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1 ▸ hyL) h.ne
  · exact h2

private theorem w183b2_cj_centralizer (x : LGL 2 V) (A : Subgroup (LGL 2 V)) :
    cj x (Subgroup.centralizer (A : Set (LGL 2 V))) =
      Subgroup.centralizer (cj x A : Set (LGL 2 V)) := by
  apply le_antisymm
  · intro y hy
    rw [cj] at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro b hb
    rw [cj] at hb
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
    have h := ha c hc
    change (x * c * x⁻¹) * (x * a * x⁻¹) = (x * a * x⁻¹) * (x * c * x⁻¹)
    calc (x * c * x⁻¹) * (x * a * x⁻¹) = x * (c * a) * x⁻¹ := by group
      _ = x * (a * c) * x⁻¹ := by rw [h]
      _ = (x * a * x⁻¹) * (x * c * x⁻¹) := by group
  · intro y hy
    rw [cj]
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hxax : (MulAut.conj x) a ∈ A.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have h := (Subgroup.mem_centralizer_iff.mp hy) ((MulAut.conj x) a) hxax
      rw [MulAut.conj_apply] at h
      change a * (x⁻¹ * y * x) = (x⁻¹ * y * x) * a
      calc a * (x⁻¹ * y * x) = x⁻¹ * (x * a * x⁻¹ * y) * x := by group
        _ = x⁻¹ * (y * (x * a * x⁻¹)) * x := by rw [h]
        _ = (x⁻¹ * y * x) * a := by group
    · change x * (x⁻¹ * y * x) * x⁻¹ = y
      group

private theorem w183b2_le_normalizer_of_comm {A B : Subgroup (LGL 2 V)}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set (LGL 2 V)) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [h a ha b hb, mul_assoc, mul_inv_cancel, mul_one]
  exact hb

theorem Br2TwoComp.core₁ (h : Br2TwoComp Y T L₁ L₂) :
    SimpleCore (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ := by
  refine ⟨?_, ?_, h.simple₁, h.nonab₁, ?_⟩
  · intro a ha
    exact ⟨h.le₁ ha, Subgroup.mem_centralizer_iff.mpr fun b hb => (h.comm a ha b hb).symm⟩
  · intro y hy l hl
    rcases h.perm y hy.1 with h1 | h2
    · rw [← h1.1]
      exact Subgroup.mem_map.mpr ⟨l, hl, by simp [MulAut.conj_apply]⟩
    · exfalso
      have hyN₂ : y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
        Subgroup.centralizer_le_normalizer _ hy.2
      have hcj₂ : cj y L₂ = L₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN₂
      exact h.ne (by rw [← h2.2, hcj₂])
  · intro y hy hl
    exact h.cent y hy.1 hl fun b hb => (Subgroup.mem_centralizer_iff.mp hy.2 b hb).symm

theorem Br2TwoComp.core₂ (h : Br2TwoComp Y T L₁ L₂) :
    SimpleCore (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) L₂ := by
  refine ⟨?_, ?_, h.simple₂, h.nonab₂, ?_⟩
  · intro a ha
    exact ⟨h.le₂ ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm b hb a ha⟩
  · intro y hy l hl
    rcases h.perm y hy.1 with h1 | h2
    · rw [← h1.2]
      exact Subgroup.mem_map.mpr ⟨l, hl, by simp [MulAut.conj_apply]⟩
    · exfalso
      have hyN₁ : y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
        Subgroup.centralizer_le_normalizer _ hy.2
      have hcj₁ : cj y L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN₁
      exact h.ne (h2.1.symm.trans hcj₁).symm
  · intro y hy hl
    exact h.cent y hy.1 (fun b hb => (Subgroup.mem_centralizer_iff.mp hy.2 b hb).symm) hl

theorem Br2TwoComp.comm_X (h : Br2TwoComp Y T L₁ L₂) {a b : LGL 2 V}
    (ha : a ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hb : b ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) : a * b = b * a := by
  have haC₂ : a ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := ha.2
  have hbC₁ : b ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := hb.2
  have haminv : a⁻¹ ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem ha
  have hbminv : b⁻¹ ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
    (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))).inv_mem hb
  let c : LGL 2 V := a * b * a⁻¹ * b⁻¹
  have hc_def : c = a * b * a⁻¹ * b⁻¹ := rfl
  have hcY : c ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem ha.1 hb.1) (Y.inv_mem ha.1)) (Y.inv_mem hb.1)
  have hc₁ : ∀ l ∈ L₁, c * l = l * c := by
    intro l hl
    have hbl : b⁻¹ * l * b = l := by
      have h := Subgroup.mem_centralizer_iff.mp hbC₁ l hl
      calc b⁻¹ * l * b = b⁻¹ * (l * b) := by group
        _ = b⁻¹ * (b * l) := by rw [h]
        _ = l := by group
    have hm : a⁻¹ * l * a ∈ L₁ := by
      have := h.core₁.normal a⁻¹ haminv l hl
      simpa using this
    have hbm : b * (a⁻¹ * l * a) * b⁻¹ = a⁻¹ * l * a := by
      have h := Subgroup.mem_centralizer_iff.mp hbC₁ (a⁻¹ * l * a) hm
      calc b * (a⁻¹ * l * a) * b⁻¹ = ((a⁻¹ * l * a) * b) * b⁻¹ := by rw [← h]
        _ = a⁻¹ * l * a := by group
    have hcl : c * l * c⁻¹ = l := by
      rw [hc_def]
      calc (a * b * a⁻¹ * b⁻¹) * l * (a * b * a⁻¹ * b⁻¹)⁻¹
          = a * b * a⁻¹ * (b⁻¹ * l * b) * a * b⁻¹ * a⁻¹ := by group
        _ = a * b * a⁻¹ * l * a * b⁻¹ * a⁻¹ := by rw [hbl]
        _ = a * (b * (a⁻¹ * l * a) * b⁻¹) * a⁻¹ := by group
        _ = a * (a⁻¹ * l * a) * a⁻¹ := by rw [hbm]
        _ = l := by group
    calc c * l = c * l * c⁻¹ * c := by group
      _ = l * c := by rw [hcl]
  have hc₂ : ∀ l ∈ L₂, c * l = l * c := by
    intro m hm
    have ham : a * m * a⁻¹ = m := by
      have h := Subgroup.mem_centralizer_iff.mp haC₂ m hm
      calc a * m * a⁻¹ = (m * a) * a⁻¹ := by rw [← h]
        _ = m := by group
    have hnb : b⁻¹ * m * b ∈ L₂ := by
      have := h.core₂.normal b⁻¹ hbminv m hm
      simpa using this
    have hna : a⁻¹ * (b⁻¹ * m * b) * a = b⁻¹ * m * b := by
      have h := Subgroup.mem_centralizer_iff.mp haC₂ (b⁻¹ * m * b) hnb
      calc a⁻¹ * (b⁻¹ * m * b) * a = a⁻¹ * ((b⁻¹ * m * b) * a) := by group
        _ = a⁻¹ * (a * (b⁻¹ * m * b)) := by rw [← h]
        _ = b⁻¹ * m * b := by group
    have hcm : c * m * c⁻¹ = m := by
      rw [hc_def]
      calc (a * b * a⁻¹ * b⁻¹) * m * (a * b * a⁻¹ * b⁻¹)⁻¹
          = a * b * (a⁻¹ * (b⁻¹ * m * b) * a) * b⁻¹ * a⁻¹ := by group
        _ = a * b * (b⁻¹ * m * b) * b⁻¹ * a⁻¹ := by rw [hna]
        _ = a * m * a⁻¹ := by group
        _ = m := by rw [ham]
    calc c * m = c * m * c⁻¹ * c := by group
      _ = m * c := by rw [hcm]
  have hcent : c = 1 := h.cent c hcY hc₁ hc₂
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hc_def ▸ hcent
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = 1 * (b * a) := by rw [h1]
    _ = b * a := by group

theorem Br2TwoComp.inf_X (h : Br2TwoComp Y T L₁ L₂) :
    (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ⊓
      (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  exact h.cent y hy.1.1
    (fun l hl => (Subgroup.mem_centralizer_iff.mp hy.2.2 l hl).symm)
    (fun l hl => (Subgroup.mem_centralizer_iff.mp hy.1.2 l hl).symm)

theorem Br2TwoComp.cj_X (h : Br2TwoComp Y T L₁ L₂) (hT : T ≤ Y) {x : LGL 2 V} (hx : x ∈ T)
    (hxL : cj x L₁ = L₂) :
    cj x (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) =
      Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
  have hxY : x ∈ Y := hT hx
  have hxL₂ : cj x L₂ = L₁ := w183b2_perm_cj_swap h hxY hxL
  have hmapY : Y.map (MulAut.conj x).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxY)
  have hmapC : (Subgroup.centralizer (L₂ : Set (LGL 2 V))).map
      (MulAut.conj x).toMonoidHom = Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
    change cj x (Subgroup.centralizer (L₂ : Set (LGL 2 V))) = _
    rw [w183b2_cj_centralizer x L₂, hxL₂]
  rw [cj, Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hmapY, hmapC]

theorem w183b2_isSylowIn_inf_X₁ (hT : IsSylowIn 2 T Y) (h : Br2TwoComp Y T L₁ L₂) :
    IsSylowIn 2 (T ⊓ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
      (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
  let X₁ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  let N : Subgroup (LGL 2 V) := Y ⊓ Subgroup.normalizer (L₁ : Set (LGL 2 V))
  have hX₁N : X₁ ≤ N := by
    refine le_inf inf_le_left ?_
    rw [Subgroup.le_normalizer_iff]
    intro a ha l hl
    exact h.core₁.normal a ha l hl
  have hNnorm : (N.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n y hn hy
    have hzY : y * n * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hn.1) (Y.inv_mem hy)
    refine ⟨hzY, ?_⟩
    have hconjN : y * n * y⁻¹ ∈ Subgroup.normalizer (cj y L₁ : Set (LGL 2 V)) := by
      show y * n * y⁻¹ ∈
        Subgroup.normalizer (L₁.map (MulAut.conj y).toMonoidHom : Set (LGL 2 V))
      have hnN : n ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) := hn.2
      have hmem : (MulAut.conj y) n ∈
          (Subgroup.normalizer (L₁ : Set (LGL 2 V))).map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨n, hnN, rfl⟩
      have := Subgroup.le_normalizer_map (H := L₁) (f := (MulAut.conj y).toMonoidHom) hmem
      simpa only [MulAut.conj_apply] using this
    rcases h.perm y hy with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rwa [h1] at hconjN
    · have hzL₂ : cj (y * n * y⁻¹) L₂ = L₂ := by
        rw [h1] at hconjN
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hconjN
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        ((w183b2_perm_cj_self_iff h hzY).mpr hzL₂)
  have hSylN : IsSylowIn 2 (T ⊓ N) N := hT.inf_normal inf_le_left hNnorm
  have hX₁norm : (X₁.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hX₁N]
    intro a n ha hn
    have hnY : n ∈ Y := hn.1
    refine ⟨Y.mul_mem (Y.mul_mem hnY ha.1) (Y.inv_mem hnY), ?_⟩
    have hnL₁ : cj n L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have hnL₂ : cj n L₂ = L₂ := (w183b2_perm_cj_self_iff h hnY).mp hnL₁
    have hncjC : cj n (Subgroup.centralizer (L₂ : Set (LGL 2 V))) =
        Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rw [w183b2_cj_centralizer n L₂, hnL₂]
    have hmem : n * a * n⁻¹ ∈ cj n (Subgroup.centralizer (L₂ : Set (LGL 2 V))) :=
      show n * a * n⁻¹ ∈ (Subgroup.centralizer (L₂ : Set (LGL 2 V))).map
          (MulAut.conj n).toMonoidHom from Subgroup.mem_map.mpr ⟨a, ha.2, rfl⟩
    rw [hncjC] at hmem
    change n * a * n⁻¹ ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V))
    exact hmem
  have hSylX₁ : IsSylowIn 2 ((T ⊓ N) ⊓ X₁) X₁ := hSylN.inf_normal hX₁N hX₁norm
  have hEq : (T ⊓ N) ⊓ X₁ = T ⊓ X₁ := by
    rw [inf_assoc, inf_eq_right.2 hX₁N]
  rwa [hEq] at hSylX₁

theorem w183b2_exists_type_one {i : ℕ} (hc : Assumption131 Y Γ VA i) (hT : T ≤ Y)
    (h : Br2TwoComp Y T L₁ L₂)
    (hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) (hne : Γ.Nonempty) :
    ∃ D ∈ Γ, D ≤ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
  obtain ⟨D₀, hD₀⟩ := hne
  have hD₀Y : D₀ ≤ Y := hc.le_G D₀ hD₀
  rcases hone D₀ hD₀ with hC₁ | hC₂
  · obtain ⟨x, hxT, hxL⟩ := h.swap
    have hxY : x ∈ Y := hT hxT
    refine ⟨cj x D₀, hc.invariant D₀ hD₀ x hxY, le_inf ?_ ?_⟩
    · intro d hd
      rw [cj, Subgroup.mem_map] at hd
      obtain ⟨d₀, hd₀, rfl⟩ := hd
      exact Y.mul_mem (Y.mul_mem hxY (hD₀Y hd₀)) (Y.inv_mem hxY)
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro l₂ hl₂
      rw [cj, Subgroup.mem_map] at hd
      obtain ⟨d₀, hd₀, rfl⟩ := hd
      have hl₂' : l₂ ∈ cj x L₁ := by rw [hxL]; exact hl₂
      rw [cj, Subgroup.mem_map] at hl₂'
      obtain ⟨l₁, hl₁, hl₁eq⟩ := hl₂'
      rw [← hl₁eq]
      have hcomm : l₁ * d₀ = d₀ * l₁ := Subgroup.mem_centralizer_iff.mp (hC₁ hd₀) l₁ hl₁
      calc (x * l₁ * x⁻¹) * (x * d₀ * x⁻¹) = x * (l₁ * d₀) * x⁻¹ := by group
        _ = x * (d₀ * l₁) * x⁻¹ := by rw [hcomm]
        _ = (x * d₀ * x⁻¹) * (x * l₁ * x⁻¹) := by group
  · exact ⟨D₀, hD₀, le_inf hD₀Y hC₂⟩

theorem w183b2_false_of_swap (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2TwoComp Y T L₁ L₂)
    {X₀ : Subgroup (MulAut ↥L₁)}
    (hX₀ : X₀ ≤ (psiOf (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁
      hL.core₁.normal).range)
    (hX₀n : ∀ r : ↥(Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))), ∀ x ∈ X₀,
      psiOf (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal r * x *
        (psiOf (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal r)⁻¹ ∈ X₀)
    (hmem : ∀ D ∈ Γ, D ≤ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) →
      imgOf (psiOf (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁ hL.core₁.normal) D ≤ X₀)
    (hnc : Br2NormalConj ↥L₁ X₀)
    (hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty) : False := by
  let X₁ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  let ψ : ↥X₁ →* MulAut ↥L₁ := psiOf X₁ L₁ hL.core₁.normal
  have hTY : T ≤ Y := hc.sylow.le
  have hSyl : IsSylowIn 2 (T ⊓ X₁) X₁ := w183b2_isSylowIn_inf_X₁ hc.sylow hL
  obtain ⟨D₀, hD₀mem, hD₀X₁⟩ := w183b2_exists_type_one hc.h131 hTY hL hone hne
  have hD₀card : 8 ≤ Nat.card D₀ := by
    haveI : Nonempty ↥D₀ := (OneMemClass.coe_nonempty D₀).to_subtype
    have h := hrk D₀ hD₀mem
    dsimp only [mRank] at h
    have h2 : 2 ^ 3 ≤ Nat.card D₀ := Nat.pow_le_of_le_log Nat.card_pos.ne' h
    rwa [show (2 : ℕ) ^ 3 = 8 by norm_num] at h2
  obtain ⟨D, hDmem, hDT, -, -, -, hgen⟩ :=
    w183b2_exists_normal_member (R := X₁) (L := L₁) (T := T) hc.h131 inf_le_left hL.core₁
      hSyl hX₀ hX₀n hnc hD₀mem hD₀X₁ (hmem D₀ hD₀mem hD₀X₁) hD₀card
  have hDT' : D ≤ T := hDT.trans inf_le_left
  have hDX₁ : D ≤ X₁ := hDT.trans inf_le_right
  have hgenN : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D', hD'mem, hBD', -⟩ := hc.gens B hB
    have hD'le : D' ≤ Y := hc.h131.le_G D' hD'mem
    rcases hone D' hD'mem with hD'C₁ | hD'C₂
    · have hBX₂ : B ≤ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
        le_inf (hBT.trans hTY) (hBD'.trans hD'C₁)
      refine w183b2_le_normalizer_of_comm ?_
      intro b hb d hd
      exact (hL.comm_X (hDX₁ hd) (hBX₂ hb)).symm
    · have hD'X₁ : D' ≤ X₁ := le_inf hD'le hD'C₂
      have hBinf : B ≤ T ⊓ X₁ := le_inf hBT (hBD'.trans hD'X₁)
      have himg : imgOf ψ B ≤ X₀ := (imgOf_mono ψ hBD').trans (hmem D' hD'mem hD'X₁)
      exact hgen B hBinf himg
  have hTne : T ≠ Y := by
    intro hTYeq
    have hEq : T ⊓ X₁ = X₁ := by
      rw [hTYeq]
      exact inf_eq_right.2 (show X₁ ≤ Y from inf_le_left)
    have hP : IsPGroup 2 X₁ := hEq ▸ hSyl.isPGroup
    exact hL.core₁.not_isPGroup hP
  have hTN : T ≤ Subgroup.normalizer (D : Set (LGL 2 V)) :=
    hc.weakClosure D hDmem hDT' hgenN T hTY le_rfl hTne
  obtain ⟨x, hxT, hxL⟩ := hL.swap
  have hxD : cj x D = D := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN hxT)
  have hxX₂ : cj x D ≤ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
    have h : cj x D ≤ cj x (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) :=
      Subgroup.map_mono hDX₁
    rwa [hL.cj_X hTY hxT hxL] at h
  have hDX₂ : D ≤ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := hxD ▸ hxX₂
  have hle : D ≤ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ⊓
      (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) := le_inf hDX₁ hDX₂
  rw [hL.inf_X] at hle
  exact hc.h131.ne_bot D hDmem (le_bot_iff.mp hle)

theorem w183b2_sp44_not_one_sided {i : ℕ} (hc : Assumption131 Y Γ VA i) (hT : T ≤ Y)
    (h : Br2TwoComp Y T L₁ L₂) (hsp : IsSp4 ↥L₁ 2) (hSp5 : FinSp44Noncyclic5)
    (h5 : ∀ D ∈ Γ, ∀ P : Subgroup (LGL 2 V),
      IsSylowIn 5 P (Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V))) → IsCyclic ↥P)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hone : D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases hone with hC₁ | hC₂
  · obtain ⟨P₀, hP₀g, hP₀nc⟩ := hSp5 ↥L₁ hsp
    let P : Subgroup (LGL 2 V) := P₀.map L₁.subtype
    have hPg : IsPGroup 5 P := hP₀g.map L₁.subtype
    have hPle : P ≤ Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V)) := by
      refine le_inf (le_trans (Subgroup.map_subtype_le P₀) h.le₁) ?_
      refine w183b2_le_normalizer_of_comm ?_
      intro a ha d hd
      exact Subgroup.mem_centralizer_iff.mp (hC₁ hd) a ((Subgroup.map_subtype_le P₀) ha)
    obtain ⟨S, hSyl, hPS⟩ := exists_isSylowIn_ge 5 hPle hPg
    have hScyc : IsCyclic ↥S := h5 D hD S hSyl
    haveI : IsCyclic ↥S := hScyc
    have hPcyc : IsCyclic ↥P := Subgroup.isCyclic_of_le hPS
    exact hP₀nc ((Subgroup.equivMapOfInjective P₀ L₁.subtype L₁.subtype_injective).isCyclic.mpr
      hPcyc)
  · obtain ⟨x, hxT, hxL⟩ := h.swap
    have hsp₂ : IsSp4 ↥L₂ 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        ((Subgroup.equivMapOfInjective L₁ (MulAut.conj x).toMonoidHom
            (MulAut.conj x).injective).trans (MulEquiv.subgroupCongr hxL)) hsp
    obtain ⟨P₀, hP₀g, hP₀nc⟩ := hSp5 ↥L₂ hsp₂
    let P : Subgroup (LGL 2 V) := P₀.map L₂.subtype
    have hPg : IsPGroup 5 P := hP₀g.map L₂.subtype
    have hPle : P ≤ Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V)) := by
      refine le_inf (le_trans (Subgroup.map_subtype_le P₀) h.le₂) ?_
      refine w183b2_le_normalizer_of_comm ?_
      intro a ha d hd
      exact Subgroup.mem_centralizer_iff.mp (hC₂ hd) a ((Subgroup.map_subtype_le P₀) ha)
    obtain ⟨S, hSyl, hPS⟩ := exists_isSylowIn_ge 5 hPle hPg
    have hScyc : IsCyclic ↥S := h5 D hD S hSyl
    haveI : IsCyclic ↥S := hScyc
    have hPcyc : IsCyclic ↥P := Subgroup.isCyclic_of_le hPS
    exact hP₀nc ((Subgroup.equivMapOfInjective P₀ L₂.subtype L₂.subtype_injective).isCyclic.mpr
      hPcyc)

end CFSG.LocalAnalysis.WeakClosure81

end
