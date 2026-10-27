module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.W183B2TwoA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

structure TwoCompBase (Y T L₁ L₂ : Subgroup (LGL 2 V)) : Prop where
  le₁ : L₁ ≤ Y
  le₂ : L₂ ≤ Y
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  ne : L₁ ≠ L₂
  perm : ∀ y ∈ Y, (cj y L₁ = L₁ ∧ cj y L₂ = L₂) ∨ (cj y L₁ = L₂ ∧ cj y L₂ = L₁)
  swap : ∃ x ∈ T, cj x L₁ = L₂
  gen : ∀ y ∈ Y, ∃ l ∈ L₁ ⊔ L₂, ∃ t ∈ T, y = l * t

theorem w183two_perm_cj_self_iff (h : TwoCompBase Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y) :
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

theorem w183two_perm_cj_swap (h : TwoCompBase Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y)
    (hyL : cj y L₁ = L₂) : cj y L₂ = L₁ := by
  rcases h.perm y hy with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1 ▸ hyL) h.ne
  · exact h2

theorem w183two_cj_centralizer (x : LGL 2 V) (A : Subgroup (LGL 2 V)) :
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

theorem w183two_le_normalizer_of_comm {A B : Subgroup (LGL 2 V)}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set (LGL 2 V)) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [h a ha b hb, mul_assoc, mul_inv_cancel, mul_one]
  exact hb

theorem TwoCompBase.mem_normalizer_of_mem_centralizer₂ (h : TwoCompBase Y T L₁ L₂) {y : LGL 2 V}
    (hy : y ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) :
    y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) := by
  rcases h.perm y hy.1 with h1 | h2
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.1
  · exfalso
    have hyN₂ : y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
      Subgroup.centralizer_le_normalizer _ hy.2
    have hcj₂ : cj y L₂ = L₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN₂
    exact h.ne (by rw [← h2.2, hcj₂])

theorem TwoCompBase.mem_normalizer_of_mem_centralizer₁ (h : TwoCompBase Y T L₁ L₂) {y : LGL 2 V}
    (hy : y ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) :
    y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  rcases h.perm y hy.1 with h1 | h2
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.2
  · exfalso
    have hyN₁ : y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
      Subgroup.centralizer_le_normalizer _ hy.2
    have hcj₁ : cj y L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN₁
    exact h.ne (h2.1.symm.trans hcj₁).symm

theorem w183two_exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x)
    (fun y hy => ?_) ?_ (fun y z _ _ ihy ihz => ?_) (fun y _ ihy => ?_) hx
  · rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := ihy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
      _ = (a * b)⁻¹ := by rw [hcomm a ha b hb]

theorem w183two_fixSub_sup (A B : Subgroup (LGL 2 V)) :
    fixSub (A ⊔ B) = fixSub A ⊓ fixSub B := by
  refine le_antisymm ?_ ?_
  · intro v hv
    exact ⟨fun a ha => hv a (Subgroup.mem_sup_left ha),
      fun b hb => hv b (Subgroup.mem_sup_right hb)⟩
  · intro v hv
    let S : Subgroup (LGL 2 V) :=
      { carrier := {g | g v = v}
        one_mem' := rfl
        mul_mem' := by
          intro a b ha hb
          show a (b v) = v
          rw [hb, ha]
        inv_mem' := by
          intro a ha
          show a⁻¹ v = v
          calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
            _ = v := LinearEquiv.symm_apply_apply a v }
    have hle : A ⊔ B ≤ S :=
      sup_le (fun a ha => hv.1 a ha) (fun b hb => hv.2 b hb)
    exact fun g hg => hle hg

theorem TwoCompBase.mem_normalizer_iff (h : TwoCompBase Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ↔
      y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  constructor
  · intro hy1
    have h1 : cj y L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy1
    rcases h.perm y hy with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · exact absurd (h1.symm.trans h2) h.ne
  · intro hy2
    have h2 : cj y L₂ = L₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy2
    rcases h.perm y hy with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exact absurd (h2.symm.trans h1) (Ne.symm h.ne)

theorem TwoCompBase.cj_X (h : TwoCompBase Y T L₁ L₂) (hT : T ≤ Y) {x : LGL 2 V} (hx : x ∈ T)
    (hxL : cj x L₁ = L₂) :
    cj x (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) =
      Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
  have hxY : x ∈ Y := hT hx
  have hxL₂ : cj x L₂ = L₁ := w183two_perm_cj_swap h hxY hxL
  have hmapY : Y.map (MulAut.conj x).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxY)
  have hmapC : (Subgroup.centralizer (L₂ : Set (LGL 2 V))).map
      (MulAut.conj x).toMonoidHom = Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
    change cj x (Subgroup.centralizer (L₂ : Set (LGL 2 V))) = _
    rw [w183two_cj_centralizer x L₂, hxL₂]
  rw [cj, Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hmapY, hmapC]

theorem w183two_isSylowIn_inf_X₁ (hT : IsSylowIn 2 T Y) (h : TwoCompBase Y T L₁ L₂) :
    IsSylowIn 2 (T ⊓ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
      (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
  let X₁ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  let N : Subgroup (LGL 2 V) := Y ⊓ Subgroup.normalizer (L₁ : Set (LGL 2 V))
  have hX₁N : X₁ ≤ N := by
    refine le_inf inf_le_left ?_
    rw [Subgroup.le_normalizer_iff]
    intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (h.mem_normalizer_of_mem_centralizer₂ ha) l).mp hl
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
        ((w183two_perm_cj_self_iff h hzY).mpr hzL₂)
  have hSylN : IsSylowIn 2 (T ⊓ N) N := hT.inf_normal inf_le_left hNnorm
  have hX₁norm : (X₁.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hX₁N]
    intro a n ha hn
    have hnY : n ∈ Y := hn.1
    refine ⟨Y.mul_mem (Y.mul_mem hnY ha.1) (Y.inv_mem hnY), ?_⟩
    have hnL₁ : cj n L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have hnL₂ : cj n L₂ = L₂ := (w183two_perm_cj_self_iff h hnY).mp hnL₁
    have hncjC : cj n (Subgroup.centralizer (L₂ : Set (LGL 2 V))) =
        Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rw [w183two_cj_centralizer n L₂, hnL₂]
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

theorem w183two_exists_type_one {i : ℕ} (hc : Assumption131 Y Γ VA i) (hT : T ≤ Y)
    (h : TwoCompBase Y T L₁ L₂)
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

theorem w183two_two_fixSub_eq_bot (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : TwoCompBase Y T L₁ L₂) : fixSub (L₁ ⊔ L₂) = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ t ∈ T, ∀ w ∈ fixSub (L₁ ⊔ L₂), t w ∈ fixSub (L₁ ⊔ L₂) := by
    intro t ht w hw l hl
    have htY : t ∈ Y := hc.sylow.le ht
    have hcj : cj t (L₁ ⊔ L₂) = L₁ ⊔ L₂ := by
      rcases hL.perm t htY with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [show cj t (L₁ ⊔ L₂) = cj t L₁ ⊔ cj t L₂ from
          Subgroup.map_sup L₁ L₂ (MulAut.conj t).toMonoidHom, h1, h2]
      · rw [show cj t (L₁ ⊔ L₂) = cj t L₁ ⊔ cj t L₂ from
          Subgroup.map_sup L₁ L₂ (MulAut.conj t).toMonoidHom, h1, h2, sup_comm]
    have hmem : t⁻¹ * l * t ∈ L₁ ⊔ L₂ := by
      have hmem' : l ∈ cj t (L₁ ⊔ L₂) := by rw [hcj]; exact hl
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem'
      have : a = t⁻¹ * l * t := by
        rw [← hae]
        change a = t⁻¹ * MulAut.conj t a * t
        rw [MulAut.conj_apply]
        group
      rwa [← this]
    calc l (t w) = (l * t) w := (LinearEquiv.mul_apply l t w).symm
      _ = (t * (t⁻¹ * l * t)) w := by congr 1; group
      _ = t ((t⁻¹ * l * t) w) := LinearEquiv.mul_apply t (t⁻¹ * l * t) w
      _ = t w := by rw [hw _ hmem]
  obtain ⟨w, hwW, hw0, hwT⟩ :=
    exists_fixed_of_isPGroup (p := 2) hc.sylow.isPGroup hne hinv
  have hwZs : w ∈ Zs := by rw [hc.zs_eq]; exact hwT
  obtain ⟨y, hyY, hyw⟩ := hc.zs_nofix w hwZs hw0
  obtain ⟨l, hl, t, ht, rfl⟩ := hL.gen y hyY
  have htw : t w = w := hwT t ht
  have hlw : l w = w := hwW l hl
  exact hyw (by rw [LinearEquiv.mul_apply, htw, hlw])

theorem w183two_two_top_eq (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : TwoCompBase Y T L₁ L₂) :
    Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ = ⊤ := by
  refine le_antisymm le_top ?_
  have hle : (⨆ y ∈ Y, conjSub y Zs) ≤ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
    refine iSup₂_le fun y hy => ?_
    change Zs.map (y : V →ₗ[ZMod 2] V) ≤ _
    rw [Submodule.map_le_iff_le_comap]
    intro z hz
    obtain ⟨l, hl, t, ht, rfl⟩ := hL.gen y hy
    rw [Submodule.mem_comap]
    simp only [LinearEquiv.coe_toLinearMap]
    have htz : t z = z := by
      have hzT : z ∈ fixSub T := by rw [← hc.zs_eq]; exact hz
      exact hzT t ht
    rw [LinearEquiv.mul_apply, htz]
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := w183two_exists_mul_of_mem_sup hL.comm hl
    rw [LinearEquiv.mul_apply]
    have h1 : l₁ (l₂ z) - l₂ z ∈ commSpace L₁ ⊤ :=
      sub_mem_commSpace (K := L₁) (U := ⊤) hl₁ trivial
    have h2 : l₂ z - z ∈ commSpace L₂ ⊤ :=
      sub_mem_commSpace (K := L₂) (U := ⊤) hl₂ trivial
    have hsum : l₁ (l₂ z) - z = (l₁ (l₂ z) - l₂ z) + (l₂ z - z) := by abel
    have hzU : z ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ :=
      Submodule.mem_sup_left (Submodule.mem_sup_left hz)
    have hmem : l₁ (l₂ z) - z ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
      rw [hsum]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_right h1)) (Submodule.mem_sup_right h2)
    have hfin : l₁ (l₂ z) ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
      have h := Submodule.add_mem _ hzU hmem
      rwa [show z + (l₁ (l₂ z) - z) = l₁ (l₂ z) by abel] at h
    exact hfin
  rwa [hc.zs_gen] at hle

theorem w183two_two_false_of_mod (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : TwoCompBase Y T L₁ L₂)
    (hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hDT : D ≤ T)
    (hVA : VA D ⊓ fixSub L₂ = ⊥ ∧ VA D ⊓ fixSub L₁ = ⊥)
    (hmod : commSpace L₂ (commSpace L₁ ⊤) = ⊥ ∧ commSpace L₁ (commSpace L₂ ⊤) = ⊥) : False := by
  have hDe : IsElemAbelian 2 D := hc.h131.isElemAb D hD
  have hDq : commSpace D (commSub D) = ⊥ := hc.h131.quadratic D hD
  obtain ⟨B, hBD, hno, hne⟩ := hc.noOffender D hD
  have hle : fixSub D ≤ fixSub B := fun v hv b hb => hv b (hBD hb)
  have hlt : (fixSub D : Set V) ⊂ (fixSub B : Set V) := by
    rw [Set.ssubset_def]
    exact ⟨hle, fun hB => hne (le_antisymm hle hB)⟩
  obtain ⟨e₀, he₀B, he₀D⟩ := Set.exists_of_ssubset hlt
  have he₀U : e₀ ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
    rw [w183two_two_top_eq hc.toBr1Base hL]; trivial
  obtain ⟨y, hy, e₂, he₂, hye₂⟩ := Submodule.mem_sup.mp he₀U
  obtain ⟨z, hz, e₁, he₁, hze₁⟩ := Submodule.mem_sup.mp hy
  have he₀ : e₀ = z + e₁ + e₂ := by rw [← hye₂, ← hze₁]
  have hzT : z ∈ fixSub T := by rw [← hc.zs_eq]; exact hz
  have hzD : z ∈ fixSub D := fun d hd => hzT d (hDT hd)
  have hzB : z ∈ fixSub B := fun b hb => hzD b (hBD hb)
  have heB : e₁ + e₂ ∈ fixSub B := by
    have h : e₀ - z ∈ fixSub B := Submodule.sub_mem _ he₀B hzB
    rwa [show e₀ - z = e₁ + e₂ by rw [he₀]; abel] at h
  have heD : e₁ + e₂ ∉ fixSub D := by
    intro h
    apply he₀D
    rw [he₀, add_assoc]
    exact Submodule.add_mem _ hzD h
  have hDnorm₁ : D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) := hmem D hD
  have hDnorm₂ : D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := fun d hd =>
    (TwoCompBase.mem_normalizer_iff hL (hc.h131.le_G D hD hd)).mp (hmem D hD hd)
  have hinv₁ : Invariant D (commSpace L₁ ⊤) :=
    invariant_commSpace (fun d hd l hl => (Subgroup.mem_normalizer_iff.mp (hDnorm₁ hd) l).mp hl)
      (fun _ _ _ _ => trivial)
  have hinv₂ : Invariant D (commSpace L₂ ⊤) :=
    invariant_commSpace (fun d hd l hl => (Subgroup.mem_normalizer_iff.mp (hDnorm₂ hd) l).mp hl)
      (fun _ _ _ _ => trivial)
  have hE₁fix : commSpace L₁ ⊤ ≤ fixSub L₂ :=
    fun u hu => fun l hl => (commSpace_eq_bot_iff.mp hmod.1) l hl u hu
  have hE₂fix : commSpace L₂ ⊤ ≤ fixSub L₁ :=
    fun u hu => fun l hl => (commSpace_eq_bot_iff.mp hmod.2) l hl u hu
  have hEinf : commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤
        ≤ fixSub L₂ ⊓ fixSub L₁ := inf_le_inf hE₁fix hE₂fix
      _ = fixSub L₁ ⊓ fixSub L₂ := inf_comm _ _
      _ = fixSub (L₁ ⊔ L₂) := (w183two_fixSub_sup L₁ L₂).symm
      _ = ⊥ := w183two_two_fixSub_eq_bot hc.toBr1Base hL
  have hb_e : ∀ b ∈ B, b e₁ + b e₂ = e₁ + e₂ := by
    intro b hb
    have := heB b hb
    rwa [map_add] at this
  have heq : ∀ b ∈ B, b e₁ - e₁ = b e₂ - e₂ := by
    intro b hb
    have h0 : b e₁ - e₁ - (b e₂ - e₂) = 0 := by
      rw [show b e₁ - e₁ - (b e₂ - e₂) = (b e₁ + b e₂) - (e₁ + e₂) by
        simp only [ZModModule.sub_eq_add]
        abel]
      rw [hb_e b hb, sub_self]
    exact sub_eq_zero.mp h0
  have he₁B : e₁ ∈ fixSub B := by
    intro b hb
    have hbD : b ∈ D := hBD hb
    have h1 : b e₁ - e₁ ∈ commSpace L₁ ⊤ :=
      (commSpace L₁ ⊤).sub_mem (hinv₁ b hbD e₁ he₁) he₁
    have h2 : b e₂ - e₂ ∈ commSpace L₂ ⊤ :=
      (commSpace L₂ ⊤).sub_mem (hinv₂ b hbD e₂ he₂) he₂
    have hmem : b e₁ - e₁ ∈ commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ :=
      ⟨h1, by rw [heq b hb]; exact h2⟩
    rw [hEinf, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have he₂B : e₂ ∈ fixSub B := by
    intro b hb
    have hbD : b ∈ D := hBD hb
    have h1 : b e₁ - e₁ ∈ commSpace L₁ ⊤ :=
      (commSpace L₁ ⊤).sub_mem (hinv₁ b hbD e₁ he₁) he₁
    have h2 : b e₂ - e₂ ∈ commSpace L₂ ⊤ :=
      (commSpace L₂ ⊤).sub_mem (hinv₂ b hbD e₂ he₂) he₂
    have hmem : b e₂ - e₂ ∈ commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ :=
      ⟨by rw [← heq b hb]; exact h1, h2⟩
    rw [hEinf, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have he₁ED : e₁ ∈ ED D := by
    by_contra h
    have hrank := w183b2_finrank_comm_le hDe hDq hBD he₁B
    have h2 := hED.rank D hD e₁ h
    have hδ := hc.delta_le D hD
    have hmi := hc.hmi
    omega
  have he₂ED : e₂ ∈ ED D := by
    by_contra h
    have hrank := w183b2_finrank_comm_le hDe hDq hBD he₂B
    have h2 := hED.rank D hD e₂ h
    have hδ := hc.delta_le D hD
    have hmi := hc.hmi
    omega
  have he₁fixD : e₁ ∈ fixSub D := by
    intro d hd
    have hcomm : d e₁ - e₁ ∈ commSpace D (ED D) :=
      sub_mem_commSpace (K := D) (U := ED D) hd he₁ED
    have h1 : d e₁ - e₁ ∈ VA D := hED.comm_le D hD hcomm
    have h2 : d e₁ - e₁ ∈ fixSub L₂ :=
      hE₁fix ((commSpace L₁ ⊤).sub_mem (hinv₁ d hd e₁ he₁) he₁)
    have hbot : d e₁ - e₁ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hVA.1]; exact ⟨h1, h2⟩
    exact sub_eq_zero.mp (by simpa using hbot)
  have he₂fixD : e₂ ∈ fixSub D := by
    intro d hd
    have hcomm : d e₂ - e₂ ∈ commSpace D (ED D) :=
      sub_mem_commSpace (K := D) (U := ED D) hd he₂ED
    have h1 : d e₂ - e₂ ∈ VA D := hED.comm_le D hD hcomm
    have h2 : d e₂ - e₂ ∈ fixSub L₁ :=
      hE₂fix ((commSpace L₂ ⊤).sub_mem (hinv₂ d hd e₂ he₂) he₂)
    have hbot : d e₂ - e₂ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hVA.2]; exact ⟨h1, h2⟩
    exact sub_eq_zero.mp (by simpa using hbot)
  exact heD (Submodule.add_mem _ he₁fixD he₂fixD)

end CFSG.LocalAnalysis.WeakClosure81

end
