module

public import CFSG.Quasithin.Background.C118BridgeOne

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

abbrev ClassPred : Type 1 := ∀ {Ω : Type} [Group Ω] [Finite Ω], Subgroup Ω → Subgroup Ω → Prop

structure InClassG1 {G : Type*} [Group G] (H S : Subgroup G) : Prop where
  cls : InClassG H S
  one : IsNatL2Section (fstarPre H (VZ S H)) (Subgroup.centralizer (VZ S H : Set G))
    ⁅VZ S H, fstarPre H (VZ S H)⁆
    (⁅VZ S H, fstarPre H (VZ S H)⁆ ⊓ Subgroup.centralizer (fstarPre H (VZ S H) : Set G)) 1

@[expose] def classG : ClassPred := fun H S => InClassG H S

@[expose] def classG1 : ClassPred := fun H S => InClassG1 H S

@[expose] def IsC118PairFor (Cls : ClassPred) {G : Type*} [Group G] (S C₁ C₂ : Subgroup G) : Prop :=
  C₁ ≠ ⊥ ∧ C₁ ≤ omegaOneCenterOf S ∧ (C₁.subgroupOf S).Characteristic ∧
    C₂ ≠ ⊥ ∧ C₂ ≤ baum S ∧ (C₂.subgroupOf (baum S)).Characteristic ∧
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (H : Subgroup Ω) (ι : ↥(baum S) →* Ω),
      Function.Injective ι → Cls H ι.range →
        (C₁.subgroupOf (baum S)).map ι ≤ centerOf H ∨
        H ≤ Subgroup.normalizer (((C₂.subgroupOf (baum S)).map ι : Subgroup Ω) : Set Ω) ∨
        IsL2OrA3Block H (twoResidual H)

theorem isC118Pair_iff {G : Type*} [Group G] {S C₁ C₂ : Subgroup G} :
    IsC118Pair S C₁ C₂ ↔ IsC118PairFor classG S C₁ C₂ := Iff.rfl

theorem IsC118PairFor.mono {Cls Cls' : ClassPred}
    (hCls : ∀ {Ω : Type} [Group Ω] [Finite Ω] {H B : Subgroup Ω}, Cls' H B → Cls H B)
    {G : Type*} [Group G] {S C₁ C₂ : Subgroup G} (h : IsC118PairFor Cls S C₁ C₂) :
    IsC118PairFor Cls' S C₁ C₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun Ω _ _ H ι hι hcl => h7 Ω H ι hι (hCls hcl)⟩

theorem isC118PairFor_of_baum (Cls : ClassPred) {G : Type*} [Group G] [Finite G]
    {T C₁ C₂ : Subgroup G} (hT : IsPGroup 2 T) (h : IsC118PairFor Cls (baum T) C₁ C₂) :
    IsC118PairFor Cls T (centerOf T ⊓ C₁) C₂ := by
  obtain ⟨h1ne, h1Z, h1ch, h2ne, h2B, h2ch, hH⟩ := h
  have hbb : baum (baum T) = baum T := C1GN.baum_baum T
  have hBT : baum T ≤ T := C1GN.baum_le T
  have hC₁B : C₁ ≤ baum T :=
    h1Z.trans ((C1GN.omegaOneCenterOf_le_centerOf _).trans inf_le_left)
  have hC₁T : C₁ ≤ T := hC₁B.trans hBT
  have hCharT : (C₁.subgroupOf T).Characteristic :=
    C1GN.characteristic_subgroupOf_trans hBT hC₁B (C1GN.characteristic_baum T) h1ch
  rw [hbb] at h2B h2ch hH
  refine ⟨?_, ?_, ?_, h2ne, h2B, h2ch, ?_⟩
  ·
    have hT' : IsPGroup 2 ↥T := hT
    have : Group.IsNilpotent ↥T := hT'.isNilpotent
    have hne : C₁.subgroupOf T ≠ ⊥ := by
      obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := C₁)).1 h1ne
      intro hbot
      have : (⟨(x : G), hC₁T x.2⟩ : ↥T) ∈ C₁.subgroupOf T := x.2
      rw [hbot, Subgroup.mem_bot] at this
      have h' : (x : G) = 1 := congrArg (fun z : ↥T => (z : G)) this
      exact hx1 (Subtype.ext h')
    have := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := C₁.subgroupOf T) hne
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 this
    intro hbot
    have hy := y.2
    have hyG : (((y : ↥(C₁.subgroupOf T ⊓ Subgroup.center ↥T)) : ↥T) : G) ∈ centerOf T ⊓ C₁ :=
      ⟨⟨((y : ↥(C₁.subgroupOf T ⊓ Subgroup.center ↥T)) : ↥T).2,
        Subgroup.mem_centralizer_iff.2 fun z hz =>
          congrArg Subtype.val ((Subgroup.mem_center_iff.1 hy.2 ⟨z, hz⟩))⟩, hy.1⟩
    rw [hbot, Subgroup.mem_bot] at hyG
    exact hy1 (Subtype.ext (Subtype.ext hyG))
  ·
    intro x hx
    exact Subgroup.subset_closure ⟨hx.1, sq_eq_one_of_mem_omegaOneCenter _ (h1Z hx.2)⟩
  ·
    have hinf : (centerOf T ⊓ C₁).subgroupOf T = Subgroup.center ↥T ⊓ C₁.subgroupOf T := by
      rw [← C1GN.centerOf_subgroupOf T]
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hinf]
    have := hCharT
    infer_instance
  · intro Ω _ _ H ι hι hcl
    rcases hH Ω H ι hι hcl with h | h | h
    · left
      refine le_trans (Subgroup.map_mono ?_) h
      exact fun x hx => hx.2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

@[expose] def ClassSeedBridgeFor (Cls : ClassPred) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B H : Subgroup Ω), baum B = B → Cls H B →
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (S : Sylow 2 ↥H)
      (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k)
      (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ (Ecore ↥H) ψ

theorem classSeedBridge_iff : ClassSeedBridge ↔ ClassSeedBridgeFor classG := Iff.rfl

theorem exists_isC118PairFor_of_bridge (Cls : ClassPred)
    (hcls : ∀ {Ω : Type} [Group Ω] [Finite Ω] {H B : Subgroup Ω}, Cls H B → InClassG H B)
    (hb : ClassSeedBridgeFor Cls) {Ω₀ : Type} [Group Ω₀] [Finite Ω₀]
    (R : Subgroup Ω₀) (hR : IsPGroup 2 R) (hR0 : R ≠ ⊥) (hbb : baum R = R) :
    ∃ C₁ C₂ : Subgroup Ω₀, IsC118PairFor Cls R C₁ C₂ := by
  classical
  have hbaumtop : baum (⊤ : Subgroup ↥(baum R)) = ⊤ :=
    baum_top_of_baum_eq (baum R) (C1GN.baum_baum R)
  by_cases hne : Nonempty (SeedData ↥(baum R))
  · obtain ⟨X₁, hmax⟩ := SeedData.exists_max hne
    have hsub1 : (X₁.cenT.map (baum R).subtype).subgroupOf (baum R) = X₁.cenT :=
      Subgroup.comap_map_eq_self_of_injective (baum R).subtype_injective _
    have hsub2 : (X₁.cstarT.map (baum R).subtype).subgroupOf (baum R) = X₁.cstarT :=
      Subgroup.comap_map_eq_self_of_injective (baum R).subtype_injective _
    refine ⟨X₁.cenT.map (baum R).subtype, X₁.cstarT.map (baum R).subtype, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
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
      have hcl' := hcls hcl
      have hH : ι.range ≤ H := hcl'.isSylow.1
      obtain hX | hX | hX := SeedData.dichotomy X₁ (seedDataOf ι hι H hH S hS ρ ψ hseed)
        (hmax _)
      · obtain ⟨V', hV'S, hV'n, hV'e, hSV', hsup⟩ := hX
        exact Or.inr (Or.inr (isL2OrA3Block_of_supplement hcl'.charTwo hseed hV'S hV'n hV'e hSV'
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
      exact ⟨seedDataOf ι hι H (hcls hcl).isSylow.1 S hS ρ ψ hseed⟩

theorem theoremC118For_of_bridge (Cls : ClassPred)
    (hcls : ∀ {Ω : Type} [Group Ω] [Finite Ω] {H B : Subgroup Ω}, Cls H B → InClassG H B)
    (hb : ClassSeedBridgeFor Cls) (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω)
    (hS : IsPGroup 2 S) (hS0 : S ≠ ⊥) : ∃ C₁ C₂ : Subgroup Ω, IsC118PairFor Cls S C₁ C₂ := by
  obtain ⟨C₁, C₂, h⟩ := exists_isC118PairFor_of_bridge Cls hcls hb (baum S)
    (hS.to_le (C1GN.baum_le S)) (C1GN.baum_ne_bot hS hS0) (C1GN.baum_baum S)
  exact ⟨centerOf S ⊓ C₁, C₂, isC118PairFor_of_baum Cls hS h⟩

@[expose] def TheoremC118S3 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω), IsPGroup 2 S → S ≠ ⊥ →
    ∃ C₁ C₂ : Subgroup Ω, IsC118PairFor classG1 S C₁ C₂

theorem theoremC118_to_S3 (h : TheoremC118) : TheoremC118S3 := by
  intro Ω _ _ S hS hS0
  obtain ⟨C₁, C₂, hC⟩ := h Ω S hS hS0
  exact ⟨C₁, C₂, IsC118PairFor.mono (Cls := classG) (fun {_ _ _ _ _} hcl => hcl.cls) hC⟩

theorem theoremC118S3 : TheoremC118S3 := fun Ω _ _ S hS hS0 =>
  theoremC118For_of_bridge classG1 (fun {_ _ _ _ _} hcl => hcl.cls)
    (fun Ω _ _ B H hbaum hcl => by
      obtain ⟨d⟩ := exists_natData hcl.one
      exact exists_seed_of_natOneData hcl.cls.isSylow hcl.cls.charTwo hcl.cls.minParabolic hbaum d)
    Ω S hS hS0

end CFSG.Quasithin
