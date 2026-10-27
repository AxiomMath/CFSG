module

public import CFSG.Quasithin.H13.A5S133

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def E12 : W5 := Multiplicative.ofAdd (e2 0 1)

theorem E12_ne_one : E12 ≠ 1 := by decide +kernel

theorem not_isSing_E12 : ¬ IsSing E12 := by decide +kernel

@[expose] def WittPair (x y : W5) : Prop :=
  x ≠ 1 → y ≠ 1 → x ≠ y → IsSing x → IsSing y → ¬ IsSing (x * y)

instance : DecidableRel WittPair := fun x y =>
  inferInstanceAs (Decidable (x ≠ 1 → y ≠ 1 → x ≠ y → IsSing x → IsSing y → ¬ IsSing (x * y)))

theorem wittPair : ∀ x y : W5, WittPair x y := by
  decide +kernel

theorem not_isSing_mul (x y : W5) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (hsx : IsSing x)
    (hsy : IsSing y) : ¬ IsSing (x * y) :=
  wittPair x y hx hy hxy hsx hsy

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

@[expose] noncomputable def v12 : G := (S.frame.ψ.symm E12 : G)

theorem v12_mem_V : S.v12 ∈ V := (S.frame.ψ.symm E12).2

theorem psi_v12 : S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ = E12 := by
  have : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = S.frame.ψ.symm E12 := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

end Setting

@[expose] def Thm13_6_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
      Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (V : Set G)

theorem commutator_eq_bot_of_le_comm {G : Type} [Group G] {A X Y : Subgroup G}
    (hA : IsMulCommutative A) (hX : X ≤ A) (hY : Y ≤ A) : ⁅X, Y⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := hA.is_comm.comm ⟨y, hY hy⟩ ⟨x, hX hx⟩
  exact congrArg Subtype.val this

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem centralizer_le_of_nonsing (h137 : Thm13_6_7)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (u : ↥V) (hu1 : u ≠ 1)
    (hu : ¬ IsSing (S.frame.ψ u)) :
    Subgroup.centralizer ({(u : G)} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hψu : S.frame.ψ u ≠ 1 := fun h => hu1 (S.frame.ψ.injective (h.trans (map_one _).symm))
  obtain ⟨σ, hσ, hσx⟩ := exists_alt_pact E12 (S.frame.ψ u) E12_ne_one hψu
    (iff_of_false not_isSing_E12 hu)
  obtain ⟨l, -, hlσ⟩ := (S.frame.image_L σ).2 hσ
  have hconj := S.psi_conj l ⟨S.v12, S.v12_mem_V⟩
  rw [hlσ, S.psi_v12, hσx] at hconj
  have hlu : (l : G) * S.v12 * (l : G)⁻¹ = u := by
    have := congrArg Subtype.val (S.frame.ψ.injective hconj)
    simpa using this
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : (l : G)⁻¹ * c * l ∈ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hlu] at hc
    calc (l : G)⁻¹ * c * l * S.v12 = (l : G)⁻¹ * (c * ((l : G) * S.v12 * (l : G)⁻¹)) * l := by
          group
      _ = (l : G)⁻¹ * (((l : G) * S.v12 * (l : G)⁻¹) * c) * l := by rw [hc]
      _ = S.v12 * ((l : G)⁻¹ * c * l) := by group
  have h1 := h137 G T L V S hab hc'
  have h2 : c = (l : G) * ((l : G)⁻¹ * c * l) * (l : G)⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ l.2 h1) (Subgroup.inv_mem _ l.2)

theorem isSing_of_mem_inf (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) (u : ↥V) (hu1 : u ≠ 1)
    (hug : (u : G) ∈ conjSub g⁻¹ V) : IsSing (S.frame.ψ u) := by
  by_contra hns
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨c, hc, hcV⟩ := S.exists_centralizer_conj h1326 u.2 hu1' hug
  have hcN := S.centralizer_le_of_nonsing h137 hab u hu1 hns hc
  rw [conjSub_self_of_mem (Subgroup.inv_mem _ hcN)] at hcV
  apply hg
  have hgi : g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcV
  simpa using Subgroup.inv_mem _ hgi

theorem lemma_13_6_24_one (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) (hne : V ⊓ conjSub g⁻¹ V ≠ ⊥) :
    ∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
      V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G) := by
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ V ⊓ conjSub g⁻¹ V, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall _).mpr h)
  have hsing : ∀ (y : G) (hy : y ∈ V ⊓ conjSub g⁻¹ V), y ≠ 1 →
      IsSing (S.frame.ψ ⟨y, hy.1⟩) := fun y hy hy1 =>
    S.isSing_of_mem_inf h137 h1326 hab hg ⟨y, hy.1⟩ (fun h => hy1 (congrArg Subtype.val h)) hy.2
  refine ⟨⟨x, hx.1⟩, fun h => hx1 (congrArg Subtype.val h), hsing x hx hx1, ?_⟩
  apply le_antisymm
  · intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem _
    by_cases hyx : y = x
    · rw [hyx]
      exact Subgroup.mem_zpowers _
    exfalso
    have hxy : x * y ∈ V ⊓ conjSub g⁻¹ V := Subgroup.mul_mem _ hx hy
    have hxy1 : x * y ≠ 1 := by
      intro h
      apply hyx
      have hx2 : x * x = 1 := by
        rw [← pow_two]
        exact S.elemAbelian_V.2 x hx.1
      calc y = x * (x * y) := by rw [← mul_assoc, hx2, one_mul]
        _ = x := by rw [h, mul_one]
    have hne' : S.frame.ψ ⟨x, hx.1⟩ ≠ S.frame.ψ ⟨y, hy.1⟩ := fun h =>
      hyx (congrArg Subtype.val (S.frame.ψ.injective h)).symm
    have hψx1 : S.frame.ψ ⟨x, hx.1⟩ ≠ 1 := fun h =>
      hx1 (congrArg Subtype.val (S.frame.ψ.injective (h.trans (map_one _).symm)))
    have hψy1 : S.frame.ψ ⟨y, hy.1⟩ ≠ 1 := fun h =>
      hy1 (congrArg Subtype.val (S.frame.ψ.injective (h.trans (map_one _).symm)))
    apply not_isSing_mul _ _ hψx1 hψy1 hne' (hsing x hx hx1) (hsing y hy hy1)
    have e : S.frame.ψ ⟨x, hx.1⟩ * S.frame.ψ ⟨y, hy.1⟩ = S.frame.ψ ⟨x * y, hxy.1⟩ :=
      (map_mul S.frame.ψ ⟨x, hx.1⟩ ⟨y, hy.1⟩).symm
    rw [e]
    exact hsing (x * y) hxy hxy1
  · exact Subgroup.zpowers_le.mpr hx

theorem lemma_13_6_24_two (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) (hne : V ⊓ conjSub g⁻¹ V ≠ ⊥) :
    ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
  obtain ⟨u, hu1, hsing, hinf⟩ := S.lemma_13_6_24_one h137 h1326 hab hg hne
  have hψu : S.frame.ψ u ≠ 1 := fun h => hu1 (S.frame.ψ.injective (h.trans (map_one _).symm))
  obtain ⟨σ, hσ, hσx⟩ := exists_alt_pact (S.frame.ψ u) W4 hψu W4_ne_one
    (iff_of_true hsing isSing_W4)
  obtain ⟨l, -, hlσ⟩ := (S.frame.image_L σ).2 hσ
  have hconj := S.psi_conj l u
  rw [hlσ, hσx, ← S.psi_z] at hconj
  have hlu : (l : G) * u * (l : G)⁻¹ = S.z := congrArg Subtype.val (S.frame.ψ.injective hconj)
  have hug : (u : G) ∈ V ⊓ conjSub g⁻¹ V := by
    rw [hinf]
    exact Subgroup.mem_zpowers _
  have hug' : (u : G) ∈ conjSub g⁻¹ V := (Subgroup.mem_inf.mp hug).2
  rw [mem_conjSub, inv_inv] at hug'
  have hz : S.z ∈ conjSub (g * (l : G)⁻¹)⁻¹ V := by
    rw [mem_conjSub, inv_inv, ← hlu]
    have e : g * (l : G)⁻¹ * ((l : G) * u * (l : G)⁻¹) * (g * (l : G)⁻¹)⁻¹ = g * u * g⁻¹ := by
      group
    rw [e]
    exact hug'
  obtain ⟨c, hc, hcV⟩ := S.exists_centralizer_conj h1326 S.z_mem_V S.z_ne_one hz
  have hcG1 : c ∈ S.G1 := hc
  have hVc : conjSub c⁻¹ V ≤ conjClosure V S.G1 := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have := mem_conjClosure (S.G1.inv_mem hcG1) hx
    simpa [mul_assoc] using this
  have h1 : ⁅V, conjSub c⁻¹ V⁆ = ⊥ :=
    commutator_eq_bot_of_le_comm hab.1 (le_conjClosure V S.G1) hVc
  rw [mul_inv_rev, inv_inv, conjSub_mul] at hcV
  have h2 : conjSub (l : G) ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
    rw [← conjSub_commutator, conjSub_self_of_mem l.2, hcV]
    exact h1
  exact (conjSub_eq_bot_iff (l : G)).mp h2

end Setting

end CFSG.Quasithin.H13.A5
