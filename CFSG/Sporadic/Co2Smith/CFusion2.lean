module

public import CFSG.Sporadic.Co2Smith.FusionC

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u v

variable {G : Type u} [Group G] {z : G} {M : Type v} [Group M]
  (φ : centralizer ({z} : Set G) ≃* M)

@[expose] noncomputable def ιM : M →* G :=
  (centralizer ({z} : Set G)).subtype.comp φ.symm.toMonoidHom

theorem ιM_apply (x : M) : ιM φ x = ((φ.symm x : centralizer ({z} : Set G)) : G) := rfl

theorem ιM_injective : Function.Injective (ιM φ) := fun _ _ h =>
  φ.symm.injective (Subtype.ext h)

theorem ιM_mem (x : M) : ιM φ x ∈ centralizer ({z} : Set G) := (φ.symm x).2

theorem ιM_φ (x : centralizer ({z} : Set G)) : ιM φ (φ x) = x := by
  rw [ιM_apply, MulEquiv.symm_apply_apply]

theorem mem_centralizer_iM {v γM : M} (h : ιM φ v ∈ centralizer ({ιM φ γM} : Set G)) :
    v ∈ centralizer ({γM} : Set M) := by
  rw [mem_centralizer_singleton_iff] at h ⊢
  apply ιM_injective φ
  rw [map_mul, map_mul]
  exact h

theorem cent2_eq_map (γM : M) :
    cent2 z (ιM φ γM) = (centralizer ({γM} : Set M)).map (ιM φ) := by
  ext x
  rw [mem_cent2, Subgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr h1
    refine ⟨φ ⟨x, hx⟩, mem_centralizer_singleton_iff.mpr (ιM_injective φ ?_), ιM_φ φ _⟩
    rw [map_mul, map_mul, ιM_φ]
    exact h2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mp (ιM_mem φ y), ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy]

@[expose] noncomputable def cent2Equiv (γM : M) :
    cent2 z (ιM φ γM) ≃* centralizer ({γM} : Set M) :=
  (MulEquiv.subgroupCongr (cent2_eq_map φ γM)).trans
    ((centralizer ({γM} : Set M)).equivMapOfInjective (ιM φ) (ιM_injective φ)).symm

theorem noSwap_of_fixed_M (hz2 : orderOf z = 2)
    (h22 : ∀ k : G, ∀ hk : k⁻¹ * z * k ∈ centralizer ({z} : Set G),
      (⟨_, hk⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) →
        k⁻¹ * z * k = z)
    {γM wM hM : M} (hwE : wM ∈ CFSG.pCore 2 M) (hw1 : wM ≠ 1) (hwr : wM * γM = γM * wM)
    (hγw : hM * (γM * wM) * hM⁻¹ = γM)
    (hfix : ∀ hw : wM ∈ centralizer ({γM} : Set M),
      ∀ α : centralizer ({γM} : Set M) ≃* centralizer ({γM} : Set M), α ⟨wM, hw⟩ = ⟨wM, hw⟩)
    {g : G} (hg1 : g⁻¹ * z * g = ιM φ γM) (hg2 : g * z * g⁻¹ = ιM φ γM) : False := by
  have hwE' : (⟨ιM φ wM, ιM_mem φ wM⟩ : centralizer ({z} : Set G)) ∈
      CFSG.pCore 2 (centralizer ({z} : Set G)) := symm_apply_mem_pCore_two φ hwE
  have hw1' : ιM φ wM ≠ 1 := fun e => hw1 (ιM_injective φ (e.trans (map_one _).symm))
  have hwr' : wM ∈ centralizer ({γM} : Set M) := mem_centralizer_singleton_iff.mpr hwr
  have hwX : ιM φ wM ∈ cent2 z (ιM φ γM) := by
    rw [cent2_eq_map]
    exact ⟨wM, hwr', rfl⟩
  have hγw' : ιM φ hM * (ιM φ γM * ιM φ wM) * (ιM φ hM)⁻¹ = ιM φ γM := by
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hγw]
  refine not_swap_of_fixed hz2 h22 (ιM_mem φ wM) hwE' hw1' hwX hγw' (fun α => ?_) hg1 hg2
  set ψ := cent2Equiv φ γM
  have hψ : ψ.symm ⟨wM, hwr'⟩ = ⟨ιM φ wM, hwX⟩ := Subtype.ext rfl
  have := hfix hwr' (ψ.symm.trans (α.trans ψ))
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ] at this
  calc α ⟨ιM φ wM, hwX⟩ = ψ.symm (ψ (α ⟨ιM φ wM, hwX⟩)) := (ψ.symm_apply_apply _).symm
    _ = ψ.symm ⟨wM, hwr'⟩ := by rw [this]
    _ = ⟨ιM φ wM, hwX⟩ := hψ

theorem ιM_zM {zM : M} (hφz : φ (zC z) = zM) : ιM φ zM = z := by
  rw [← hφz, ιM_φ]
  rfl

theorem mem_map_ιM {A : Subgroup M} {x : G} : x ∈ A.map (ιM φ) ↔ ∃ y ∈ A, ιM φ y = x :=
  Subgroup.mem_map

theorem mem_H_of_map {A : Subgroup M} {x : G} (hx : x ∈ A.map (ιM φ)) :
    x ∈ centralizer ({z} : Set G) := by
  obtain ⟨y, -, rfl⟩ := (mem_map_ιM φ).mp hx
  exact ιM_mem φ y

theorem eq_of_map {A : Subgroup M} {x : G} (hx : x ∈ A.map (ιM φ)) :
    φ ⟨x, mem_H_of_map φ hx⟩ ∈ A ∧ ιM φ (φ ⟨x, mem_H_of_map φ hx⟩) = x := by
  obtain ⟨y, hy, rfl⟩ := (mem_map_ιM φ).mp hx
  refine ⟨?_, ιM_φ φ _⟩
  have : φ ⟨ιM φ y, mem_H_of_map φ hx⟩ = y := by
    rw [show (⟨ιM φ y, mem_H_of_map φ hx⟩ : centralizer ({z} : Set G)) = φ.symm y from rfl,
      MulEquiv.apply_symm_apply]
  rw [this]
  exact hy

theorem centralizer_map_eq (D X : Subgroup M) :
    centralizer ((D.map (ιM φ) : Subgroup G) : Set G) ⊓ X.map (ιM φ) =
      (centralizer (D : Set M) ⊓ X).map (ιM φ) := by
  ext x
  rw [Subgroup.mem_inf, mem_centralizer_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨y, hy, rfl⟩ := (mem_map_ιM φ).mp h2
    refine ⟨y, Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun d hd => ?_, hy⟩, rfl⟩
    exact ιM_injective φ (by rw [map_mul, map_mul]; exact h1 _ ⟨d, hd, rfl⟩)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun d hd => ?_, ⟨y, (Subgroup.mem_inf.mp hy).2, rfl⟩⟩
    obtain ⟨d', hd', rfl⟩ := (mem_map_ιM φ).mp hd
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).1 d' hd']

theorem noSwap_of_D0_M [Finite G] (hz2 : orderOf z = 2)
    (h22 : ∀ k : G, ∀ hk : k⁻¹ * z * k ∈ centralizer ({z} : Set G),
      (⟨_, hk⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) →
        k⁻¹ * z * k = z)
    {zM : M} (hφz : φ (zC z) = zM) {γM : M} (DM : Subgroup M)
    (hDX : DM ≤ centralizer ({γM} : Set M)) (hDE : DM ≤ CFSG.pCore 2 M)
    (hDab : ∀ a ∈ DM, ∀ b ∈ DM, a * b = b * a)
    (hXD : ∀ x ∈ centralizer ({γM} : Set M), ∀ d ∈ DM, x * d * x⁻¹ ∈ DM) (hγD : γM ∉ DM)
    (hmin : ∀ N : Subgroup M, N ≤ DM → (∀ x ∈ centralizer ({γM} : Set M), ∀ n ∈ N,
      x * n * x⁻¹ ∈ N) → N ≠ ⊥ → zM ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : M, h * (γM * d) * h⁻¹ = γM)
    (hA : Nat.card (centralizer (DM : Set M) ⊓ centralizer ({γM} : Set M) : Subgroup M) ≤
      Nat.card DM ^ 2)
    (hZD : Nat.card {d : M // d ∈ DM ∧ ∀ x ∈ centralizer ({γM} : Set M), x * d = d * x} ≤ 2)
    (hZA : 8 ≤ Nat.card {a : M // a ∈ centralizer (DM : Set M) ⊓ centralizer ({γM} : Set M) ∧
      ∀ x ∈ centralizer ({γM} : Set M), x * a = a * x})
    {g : G} (hg1 : g⁻¹ * z * g = ιM φ γM) (hg2 : g * z * g⁻¹ = ιM φ γM) : False := by
  have : Finite M := Finite.of_equiv _ φ.toEquiv
  set X := centralizer ({γM} : Set M)
  have hX := cent2_eq_map φ γM
  have hXm : ∀ x ∈ cent2 z (ιM φ γM), ∃ y ∈ X, ιM φ y = x := fun x hx =>
    (mem_map_ιM φ).mp (hX ▸ hx)
  have hXm' : ∀ y ∈ X, ιM φ y ∈ cent2 z (ιM φ γM) := fun y hy => hX ▸ ⟨y, hy, rfl⟩
  refine false_of_D0 hg1 hg2 (DM.map (ιM φ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX]
    exact Subgroup.map_mono hDX
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hDab a ha b hb]
  · intro x hx d hd
    obtain ⟨y, hy, rfl⟩ := hXm x hx
    obtain ⟨d', hd', rfl⟩ := (mem_map_ιM φ).mp hd
    exact ⟨y * d' * y⁻¹, hXD y hy d' hd', by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨y, hy, hyγ⟩
    exact hγD (ιM_injective φ hyγ ▸ hy)
  · intro k d hd hk
    obtain ⟨d', hd', rfl⟩ := (mem_map_ιM φ).mp hd
    have hmem : k⁻¹ * z * k ∈ centralizer ({z} : Set G) := by
      rw [hk]
      exact (centralizer ({z} : Set G)).mul_mem (mem_centralizer_singleton_iff.mpr rfl)
        (ιM_mem φ d')
    have hE : (⟨_, hmem⟩ : centralizer ({z} : Set G)) ∈
        CFSG.pCore 2 (centralizer ({z} : Set G)) := by
      have e : (⟨_, hmem⟩ : centralizer ({z} : Set G)) = zC z * φ.symm d' := Subtype.ext hk
      rw [e]
      exact Subgroup.mul_mem _ (zC_mem_pCore hz2) (symm_apply_mem_pCore_two φ (hDE hd'))
    have := h22 k hmem hE
    rw [hk] at this
    simpa using this
  · intro N hND hNX hN hzN
    set N' := N.comap (ιM φ)
    have hN'D : N' ≤ DM := by
      intro y hy
      obtain ⟨y', hy', e⟩ := (mem_map_ιM φ).mp (hND hy)
      rwa [ιM_injective φ e] at hy'
    have hN'X : ∀ x ∈ X, ∀ n ∈ N', x * n * x⁻¹ ∈ N' := by
      intro x hx n hn
      show ιM φ (x * n * x⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNX _ (hXm' x hx) _ hn
    have hN'1 : N' ≠ ⊥ := by
      intro h
      apply hN
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨y, -, rfl⟩ := (mem_map_ιM φ).mp (hND ha)
      have : y ∈ N' := ha
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot, this, map_one]
    have hzN' : zM ∉ N' := fun h => hzN (by
      have : ιM φ zM ∈ N := h
      rwa [ιM_zM φ hφz] at this)
    obtain ⟨d, hdN, hd1, h, hh⟩ := hmin N' hN'D hN'X hN'1 hzN'
    refine ⟨ιM φ d, hdN, fun e => hd1 (ιM_injective φ (e.trans (map_one _).symm)), ιM φ h, ?_⟩
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hh]
  · rw [hX, centralizer_map_eq, Subgroup.card_map_of_injective (ιM_injective φ),
      Subgroup.card_map_of_injective (ιM_injective φ)]
    exact hA
  · have hmap : ∀ d : {d : G // d ∈ DM.map (ιM φ) ∧ ∀ x ∈ cent2 z (ιM φ γM), x * d = d * x},
        φ ⟨d.1, mem_H_of_map φ d.2.1⟩ ∈ DM ∧
          ∀ x ∈ X, x * φ ⟨d.1, mem_H_of_map φ d.2.1⟩ = φ ⟨d.1, mem_H_of_map φ d.2.1⟩ * x := by
      intro d
      refine ⟨(eq_of_map φ d.2.1).1, fun x hx => ιM_injective φ ?_⟩
      rw [map_mul, map_mul, (eq_of_map φ d.2.1).2]
      exact d.2.2 _ (hXm' x hx)
    refine le_trans (Nat.card_le_card_of_injective
      (fun d => ⟨φ ⟨d.1, mem_H_of_map φ d.2.1⟩, hmap d⟩) fun a b h => ?_) hZD
    have h' : φ ⟨a.1, mem_H_of_map φ a.2.1⟩ = φ ⟨b.1, mem_H_of_map φ b.2.1⟩ :=
      Subtype.mk.inj h
    exact Subtype.ext (Subtype.mk.inj (φ.injective h'))
  · refine le_trans hZA (Nat.card_le_card_of_injective (fun a => ⟨ιM φ a.1, ?_, ?_⟩) ?_)
    · rw [hX, centralizer_map_eq]
      exact ⟨a.1, a.2.1, rfl⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hXm x hx
      rw [← map_mul, ← map_mul, a.2.2 y hy]
    · intro a b h
      have h' : ιM φ a.1 = ιM φ b.1 := Subtype.mk.inj h
      exact Subtype.ext (ιM_injective φ h')

end CFSG.Sporadic.Co2Smith
