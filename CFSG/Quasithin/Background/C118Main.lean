module

public import CFSG.Quasithin.Background.C118Block
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Background.C118Class

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Helpers

variable {T G' : Type*} [Group T] [Group G']

theorem omegaOneCenterOf_map_of_injective {f : T →* G'} (hf : Function.Injective f)
    (X : Subgroup T) : omegaOneCenterOf (X.map f) = (omegaOneCenterOf X).map f := by
  unfold omegaOneCenterOf omegaOneOf centerOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨⟨y, hyX, rfl⟩, hyC⟩, hx2⟩
    refine ⟨y, ⟨⟨hyX, ?_⟩, ?_⟩, rfl⟩
    · refine Subgroup.mem_centralizer_iff.2 fun w hw => hf ?_
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.1 hyC (f w) ⟨w, hw, rfl⟩
    · apply hf
      rw [map_pow, map_one]
      exact hx2
  · rintro ⟨y, ⟨⟨hyX, hyC⟩, hy2⟩, rfl⟩
    refine ⟨⟨⟨y, hyX, rfl⟩, ?_⟩, by rw [← map_pow, hy2, map_one]⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyC w hw]

theorem baum_map_of_injective {f : T →* G'} (hf : Function.Injective f) (X : Subgroup T) :
    baum (X.map f) = (baum X).map f := by
  unfold baum
  rw [thompsonJ_map_of_injective' hf, omegaOneCenterOf_map_of_injective hf,
    map_inf_centralizer hf]

theorem baum_range_of_injective {f : T →* G'} (hf : Function.Injective f)
    (h : baum (⊤ : Subgroup T) = ⊤) : baum f.range = f.range := by
  rw [MonoidHom.range_eq_map, baum_map_of_injective hf, h]

end Helpers

section BaumTop

variable {Ω : Type*} [Group Ω]

theorem baum_top_of_baum_eq (B : Subgroup Ω) (h : baum B = B) : baum (⊤ : Subgroup ↥B) = ⊤ := by
  have h1 := C1GN.baum_eq_map_top B
  rw [h] at h1
  have h2 : (⊤ : Subgroup ↥B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective B.subtype_injective
  rw [← h1]
  exact h2.symm

theorem characteristic_subgroupOf_congr {A B C : Subgroup Ω} (h : A = B)
    (hc : (C.subgroupOf A).Characteristic) : (C.subgroupOf B).Characteristic := by
  subst h
  exact hc

end BaumTop

section Uniform

variable {T : Type} [Group T] [Finite T]

theorem NatLike.Z_ne_bot {S Q V Z : Subgroup T} {q : ℕ} (h : NatLike S Q V Z q) : Z ≠ ⊥ := by
  intro hZ
  have hSQ : S ≤ Q := by
    intro s hs
    refine h.cent_le s hs fun v hv => ?_
    have h1 : ⁅s, v⁆ ∈ (⁅S, V⁆ : Subgroup T) := Subgroup.commutator_mem_commutator hs hv
    have h2 := h.comm_le h1
    rw [hZ, Subgroup.mem_bot, commutatorElement_def] at h2
    calc s * v = (s * v * s⁻¹ * v⁻¹) * (v * s) := by group
      _ = v * s := by rw [h2, one_mul]
  have h1 : Nat.card S ≤ Nat.card Q := Subgroup.card_le_of_le hSQ
  have h2 := h.card_S
  have h3 : 0 < Nat.card Q := Nat.card_pos
  have h4 := Nat.mul_le_mul_right (Nat.card Q) (h.one_lt : 2 ≤ q)
  omega

end Uniform

section SeedFacts

variable {T : Type} [Group T] [Finite T]

namespace SeedData

variable (X : SeedData T)

theorem Zh_ne_bot : X.Zh ≠ ⊥ := X.partnerData.nat.Z_ne_bot

omit [Finite T] in
theorem Zh_le_cenT : X.Zh ≤ X.cenT :=
  le_iSup_of_le (MulEquiv.refl T) (fun z hz => ⟨z, hz, rfl⟩)

omit [Finite T] in
theorem Fh_le_cstarT : X.Fh ≤ X.cstarT :=
  le_iSup_of_le (MulEquiv.refl T) (fun z hz => ⟨z, hz, rfl⟩)

theorem cenT_ne_bot : X.cenT ≠ ⊥ := fun h =>
  X.Zh_ne_bot (le_bot_iff.mp (h ▸ X.Zh_le_cenT))

theorem cstarT_ne_bot : X.cstarT ≠ ⊥ := fun h =>
  X.Zh_ne_bot (le_bot_iff.mp
    (h ▸ (X.partnerData.core.zp_le_fp.trans X.Fh_le_cstarT)))

omit [Finite T] in
theorem characteristic_cenT : X.cenT.Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  unfold cenT
  rw [Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_map]
  exact le_iSup_of_le (β.trans φ) (le_of_eq rfl)

omit [Finite T] in
theorem characteristic_cstarT : X.cstarT.Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  unfold cstarT
  rw [Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_map]
  exact le_iSup_of_le (β.trans φ) (le_of_eq rfl)

omit [Finite T] in
theorem cenT_le_omega : X.cenT ≤ omegaOneCenterOf (⊤ : Subgroup T) := by
  unfold cenT
  refine iSup_le fun β => ?_
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.subset_closure
  have hnat := X.partnerData.nat
  refine ⟨⟨trivial, Subgroup.mem_centralizer_iff.mpr fun g _ => ?_⟩, ?_⟩
  · have h1 := hnat.Z_central (β.symm g) trivial z hz
    have h2 : g * β z = β z * g := by
      calc g * β z = β (β.symm g * z) := by simp
        _ = β (z * β.symm g) := by rw [h1]
        _ = β z * g := by simp
    exact h2
  · have h2 : z ^ 2 = 1 := (isElemAbelian_iff.mp hnat.V_elem).2 z (hnat.Z_le hz)
    show β z ^ 2 = 1
    rw [← map_pow, h2, map_one]

end SeedData

end SeedFacts

section Bridge

@[expose] def ClassSeedBridge : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B H : Subgroup Ω), baum B = B → InClassG H B →
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (S : Sylow 2 ↥H)
      (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k)
      (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ (Ecore ↥H) ψ

variable {T : Type} [Group T]

@[expose, reducible] noncomputable def seedDataOf {Ω : Type} [Group Ω] [Finite Ω] (ι : T →* Ω)
    (hι : Function.Injective ι) (H : Subgroup Ω) (hH : ι.range ≤ H) {k : Type} [Field k]
    [Finite k] (S : Sylow 2 ↥H) (hS : (S : Subgroup ↥H) = ι.range.subgroupOf H)
    (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k) (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k))
    (h : IsSeed S ρ (Ecore ↥H) ψ) : SeedData T where
  G := ↥H
  k := k
  S := S
  e := (MonoidHom.ofInjective hι).trans
    ((Subgroup.subgroupOfEquivOfLe hH).symm.trans (MulEquiv.subgroupCongr hS.symm))
  ρ := ρ
  ψ := ψ
  seed := h

theorem seedDataOf_map {Ω : Type} [Group Ω] [Finite Ω] (ι : T →* Ω)
    (hι : Function.Injective ι) (H : Subgroup Ω) (hH : ι.range ≤ H) {k : Type} [Field k]
    [Finite k] (S : Sylow 2 ↥H) (hS : (S : Subgroup ↥H) = ι.range.subgroupOf H)
    (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k) (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k))
    (h : IsSeed S ρ (Ecore ↥H) ψ) (Y : Subgroup T) :
    (Y.map (seedDataOf ι hι H hH S hS ρ ψ h).f).map H.subtype = Y.map ι := by
  rw [Subgroup.map_map]
  congr 1

omit [Group T] in
theorem le_normalizer_map_subtype {Ω : Type} [Group Ω] (H : Subgroup Ω) (N : Subgroup ↥H)
    [N.Normal] : H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup Ω) : Set Ω) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance n hn ⟨g, hg⟩, rfl⟩
  · rintro ⟨n, hn, hnx⟩
    have h1 : (⟨g, hg⟩ : ↥H)⁻¹ * n * (⟨g, hg⟩ : ↥H) ∈ N := by
      simpa using Subgroup.Normal.conj_mem inferInstance n hn (⟨g, hg⟩ : ↥H)⁻¹
    refine ⟨_, h1, ?_⟩
    show g⁻¹ * (n : Ω) * g = x
    have : (n : Ω) = g * x * g⁻¹ := hnx
    rw [this]
    group

omit [Group T] in
theorem map_subtype_le_centerOf {Ω : Type} [Group Ω] (H : Subgroup Ω) (N : Subgroup ↥H)
    (hN : N ≤ Subgroup.center ↥H) : N.map H.subtype ≤ centerOf H := by
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  have := Subgroup.mem_center_iff.mp (hN hn) ⟨g, hg⟩
  exact congrArg Subtype.val this

omit [Group T] in
theorem map_top_subtype {Ω : Type*} [Group Ω] (B : Subgroup Ω) :
    (⊤ : Subgroup ↥B).map B.subtype = B := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_isC118Pair_of_bridge (hb : ClassSeedBridge) {Ω₀ : Type} [Group Ω₀] [Finite Ω₀]
    (R : Subgroup Ω₀) (hR : IsPGroup 2 R) (hR0 : R ≠ ⊥) (hbb : baum R = R) :
    ∃ C₁ C₂ : Subgroup Ω₀, IsC118Pair R C₁ C₂ := by
  classical
  have hbaumtop : baum (⊤ : Subgroup ↥(baum R)) = ⊤ :=
    baum_top_of_baum_eq (baum R) (C1GN.baum_baum R)
  by_cases hne : Nonempty (SeedData ↥(baum R))
  · obtain ⟨X₁, hmax⟩ := SeedData.exists_max hne
    have hsub1 : (X₁.cenT.map (baum R).subtype).subgroupOf (baum R) = X₁.cenT :=
      Subgroup.comap_map_eq_self_of_injective (baum R).subtype_injective _
    have hsub2 : (X₁.cstarT.map (baum R).subtype).subgroupOf (baum R) = X₁.cstarT :=
      Subgroup.comap_map_eq_self_of_injective (baum R).subtype_injective _
    refine ⟨X₁.cenT.map (baum R).subtype, X₁.cstarT.map (baum R).subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => X₁.cenT_ne_bot
        ((Subgroup.map_eq_bot_iff_of_injective _ (baum R).subtype_injective).mp h)
    · calc X₁.cenT.map (baum R).subtype
          ≤ (omegaOneCenterOf (⊤ : Subgroup ↥(baum R))).map (baum R).subtype :=
            Subgroup.map_mono X₁.cenT_le_omega
        _ = omegaOneCenterOf ((⊤ : Subgroup ↥(baum R)).map (baum R).subtype) :=
            (C1GN.omegaOneCenterOf_map_subtype (baum R) ⊤).symm
        _ = omegaOneCenterOf (baum R) := by rw [map_top_subtype]
        _ = omegaOneCenterOf R := by rw [hbb]
    · exact characteristic_subgroupOf_congr hbb (by rw [hsub1]; exact X₁.characteristic_cenT)
    · exact fun h => X₁.cstarT_ne_bot
        ((Subgroup.map_eq_bot_iff_of_injective _ (baum R).subtype_injective).mp h)
    · exact Subgroup.map_subtype_le _
    · rw [hsub2]
      exact X₁.characteristic_cstarT
    · intro Ω' _ _ H ι hι hcl
      rw [hsub1, hsub2]
      have hbaum : baum ι.range = ι.range := baum_range_of_injective hι hbaumtop
      obtain ⟨k, _, _, S, ρ, ψ, hS, hseed⟩ := hb Ω' ι.range H hbaum hcl
      have hH : ι.range ≤ H := hcl.isSylow.1
      obtain hX | hX | hX := SeedData.dichotomy X₁ (seedDataOf ι hι H hH S hS ρ ψ hseed)
        (hmax _)
      · obtain ⟨V', hV'S, hV'n, hV'e, hSV', hsup⟩ := hX
        exact Or.inr (Or.inr (isL2OrA3Block_of_supplement hcl.charTwo hseed hV'S hV'n hV'e hSV'
          hsup))
      · refine Or.inr (Or.inl ?_)
        have := le_normalizer_map_subtype H (X₁.cstarT.map (seedDataOf ι hι H hH S hS ρ ψ hseed).f)
        rwa [seedDataOf_map] at this
      · refine Or.inl ?_
        have := map_subtype_le_centerOf H (X₁.cenT.map (seedDataOf ι hι H hH S hS ρ ψ hseed).f) hX
        rwa [seedDataOf_map] at this
  · refine ⟨omegaOneCenterOf R, omegaOneCenterOf R, ?_, le_rfl,
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R, ?_,
      C1GN.omegaOneCenterOf_le_baum R, ?_, ?_⟩
    · exact quasithinOmegaOneCenter_ne_bot hR hR0
    · exact quasithinOmegaOneCenter_ne_bot hR hR0
    · exact characteristic_subgroupOf_congr hbb.symm
        (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R)
    · intro Ω' _ _ H ι hι hcl
      exfalso
      apply hne
      have hbaum : baum ι.range = ι.range := baum_range_of_injective hι hbaumtop
      obtain ⟨k, _, _, S, ρ, ψ, hS, hseed⟩ := hb Ω' ι.range H hbaum hcl
      exact ⟨seedDataOf ι hι H hcl.isSylow.1 S hS ρ ψ hseed⟩

end Bridge

section Final

theorem theoremC118_of_bridge (hb : ClassSeedBridge) : TheoremC118 := by
  intro Ω _ _ S hS hS0
  obtain ⟨C₁, C₂, h⟩ := exists_isC118Pair_of_bridge hb (baum S) (hS.to_le (C1GN.baum_le S))
    (C1GN.baum_ne_bot hS hS0) (C1GN.baum_baum S)
  exact ⟨centerOf S ⊓ C₁, C₂, isC118Pair_of_baum hS h⟩

end Final

end CFSG.Quasithin
