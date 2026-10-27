module

public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG

theorem exists_minimal_cover {H Γ : Type*} [Group H] [Group Γ] [Finite H] (π : H →* Γ)
    (hπ : Function.Surjective π) :
    ∃ U : Subgroup H, U.map π = ⊤ ∧ ∀ V : Subgroup H, V ≤ U → V.map π = ⊤ → V = U := by
  classical
  obtain ⟨U, hU⟩ := (Set.toFinite {V : Subgroup H | V.map π = ⊤}).exists_minimal
    ⟨⊤, map_top_of_surjective π hπ⟩
  exact ⟨U, hU.prop, fun V hVU hV => le_antisymm hVU (hU.2 hV hVU)⟩

theorem minimal_cover_properties {H Γ : Type*} [Group H] [Group Γ] [Finite H] (π : H →* Γ)
    (S : Subgroup Γ) [S.Normal] (hSperf : Group.IsPerfect S) (hΓS : Group.IsSolvable (Γ ⧸ S))
    (U : Subgroup H) (hU : U.map π = ⊤)
    (hmin : ∀ V : Subgroup H, V ≤ U → V.map π = ⊤ → V = U) :
    Group.IsNilpotent (π.comp U.subtype).ker ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q (π.comp U.subtype).ker),
        ((Q : Subgroup (π.comp U.subtype).ker).map (π.comp U.subtype).ker.subtype).Normal) ∧
      (perfectResidual U).Characteristic ∧ Group.IsPerfect (perfectResidual U) ∧
      (perfectResidual U).map (π.comp U.subtype) = S ∧
      Group.IsNilpotent ↥(perfectResidual U ⊓ (π.comp U.subtype).ker) ∧
      (perfectResidual U ⊓ (π.comp U.subtype).ker).Normal ∧
      ∃ e : perfectResidual U ⧸
          (perfectResidual U ⊓ (π.comp U.subtype).ker).subgroupOf (perfectResidual U) ≃* S,
        (∀ x : perfectResidual U, (e (QuotientGroup.mk x) : Γ) = π (x : H)) ∧
        ∀ (u : U) (x : perfectResidual U),
          e (QuotientGroup.mk (MulAut.conjNormal u x)) =
            MulAut.conjNormal (π u) (e (QuotientGroup.mk x)) := by
  classical
  set f := π.comp U.subtype with hf
  have hfs : Function.Surjective f := by
    intro γ
    have hγ : γ ∈ U.map π := hU ▸ mem_top γ
    obtain ⟨u, hu, rfl⟩ := hγ
    exact ⟨⟨u, hu⟩, rfl⟩
  have : Finite Γ := Finite.of_surjective f hfs
  set N := f.ker with hN
  have hmin' : ∀ V : Subgroup U, V.map f = ⊤ → V = ⊤ := by
    intro V hV
    have h := hmin (V.map U.subtype) (map_subtype_le V) (by rw [map_map]; exact hV)
    rw [eq_top_iff]
    intro x _
    have hx : (x : H) ∈ V.map U.subtype := h.symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  have hsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q N),
      ((Q : Subgroup N).map N.subtype).Normal := by
    intro q _ Q
    have hF := congrArg (map f) (Sylow.normalizer_sup_eq_top Q)
    rw [Subgroup.map_sup, map_top_of_surjective f hfs] at hF
    have hNbot : N.map f = ⊥ := by
      rw [hN, Subgroup.map_eq_bot_iff]
    rw [hNbot, sup_bot_eq] at hF
    exact normalizer_eq_top_iff.mp (hmin' _ hF)
  have hnil : Group.IsNilpotent N := by
    refine ((Group.isNilpotent_of_finite_tfae (G := N)).out 4 1).mp ?_
    intro q _ Q
    have hQ := (hsyl q Q).subgroupOf N
    rwa [subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)] at hQ
  set P := perfectResidual U with hP
  obtain ⟨-, hPchar, hPperf, -, -, -⟩ := perfect_residual_characterization (G := U)
  obtain ⟨-, -, -, -, hΓiff, -⟩ := perfect_residual_characterization (G := Γ)
  obtain ⟨-, -, hΓperf⟩ := perfect_residual_transport (G := Γ) (MonoidHom.id Γ)
  have hDΓ : perfectResidual Γ = S :=
    le_antisymm ((hΓiff S).mp hΓS) (hΓperf S hSperf)
  have hPS : P.map f = S :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hfs).trans hDΓ
  have hCnil : Group.IsNilpotent ↥(P ⊓ N) := by
    have := hnil
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ N ≤ N))
  let g : P →* S := (f.comp P.subtype).codRestrict S fun x => hPS ▸ ⟨x, x.2, rfl⟩
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hPS] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : (P ⊓ N).subgroupOf P = g.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker, mem_inf, hN, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  refine ⟨hnil, hsyl, hPchar, hPperf, hPS, hCnil, inferInstance, e, fun x => rfl, ?_⟩
  intro u x
  apply Subtype.ext
  change f (u * x * u⁻¹) = π u * f x * (π u)⁻¹
  rw [map_mul, map_mul, map_inv]
  rfl


theorem minimal_section_cover_retains_perfect_normal_subgroup {H Γ : Type*} [Group H] [Group Γ]
    [Finite H] (π : H →* Γ) (hπ : Function.Surjective π) (S : Subgroup Γ) [S.Normal]
    (hSperf : Group.IsPerfect S) (hΓS : Group.IsSolvable (Γ ⧸ S)) :
    (∃ U : Subgroup H, U.map π = ⊤ ∧ ∀ V : Subgroup H, V ≤ U → V.map π = ⊤ → V = U) ∧
    ∀ U : Subgroup H, U.map π = ⊤ → (∀ V : Subgroup H, V ≤ U → V.map π = ⊤ → V = U) →
      Group.IsNilpotent (π.comp U.subtype).ker ∧
        (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q (π.comp U.subtype).ker),
          ((Q : Subgroup (π.comp U.subtype).ker).map (π.comp U.subtype).ker.subtype).Normal) ∧
        (perfectResidual U).Characteristic ∧ Group.IsPerfect (perfectResidual U) ∧
        (perfectResidual U).map (π.comp U.subtype) = S ∧
        Group.IsNilpotent ↥(perfectResidual U ⊓ (π.comp U.subtype).ker) ∧
        (perfectResidual U ⊓ (π.comp U.subtype).ker).Normal ∧
        ∃ e : perfectResidual U ⧸
            (perfectResidual U ⊓ (π.comp U.subtype).ker).subgroupOf (perfectResidual U) ≃* S,
          (∀ x : perfectResidual U, (e (QuotientGroup.mk x) : Γ) = π (x : H)) ∧
          ∀ (u : U) (x : perfectResidual U),
            e (QuotientGroup.mk (MulAut.conjNormal u x)) =
              MulAut.conjNormal (π u) (e (QuotientGroup.mk x)) :=
  ⟨exists_minimal_cover π hπ, fun U hU hmin =>
    minimal_cover_properties π S hSperf hΓS U hU hmin⟩

end CFSG.RankThree.GroupTheory.SteinbergBK
