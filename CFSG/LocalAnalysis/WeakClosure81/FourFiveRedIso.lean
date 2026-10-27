module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

private theorem fourFive_autQuot_equiv_mk_aux {G G' : Type} [Group G] [Group G']
    (π : G →* G') {T J X C : Subgroup G} (hπker : π.ker = C) [X.Normal] [C.Normal]
    (hJX : J ≤ X) (hXC : X ⊓ C = ⊥) :
    Nonempty ((↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)) ≃*
      (↥(F12.autNL (T.map π) (J.map π)) ⧸
        (F12.autC (T.map π) (J.map π)).subgroupOf
          (F12.autNL (T.map π) (J.map π)))) := by
  let A : Subgroup G := F12.autNL T J
  let K : Subgroup G := F12.autC T J
  let A' : Subgroup G' := F12.autNL (T.map π) (J.map π)
  let K' : Subgroup G' := F12.autC (T.map π) (J.map π)
  have hXnorm : X.Normal := inferInstance
  have hJcomap : (J.map π).comap π = J ⊔ C := by
    rw [Subgroup.comap_map_eq, hπker]
  have hXCJ : X ⊓ (J ⊔ C) = J := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxX, hxsup⟩ := hx
      rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hxsup
      obtain ⟨j, hj, c, hc, hjc⟩ := hxsup
      have hjcX : j * c ∈ X := by rw [hjc]; exact hxX
      have hcX : c ∈ X := by
        have hc_eq : c = j⁻¹ * (j * c) := by group
        rw [hc_eq]
        exact X.mul_mem (X.inv_mem (hJX hj)) hjcX
      have hc1 : c = 1 := by
        have : c ∈ (⊥ : Subgroup G) := by
          rw [← hXC]
          exact ⟨hcX, hc⟩
        simpa using this
      rw [← hjc, hc1, mul_one]
      exact hj
    · exact le_inf hJX le_sup_left
  have hA_le : A ≤ Subgroup.normalizer (J : Set G) := by
    change F12.autNL T J ≤ Subgroup.normalizer (J : Set G)
    rw [F12.autNL]
    exact sup_le inf_le_right Subgroup.le_normalizer
  have hstep : ∀ (u : G), π u ∈ Subgroup.normalizer ((J.map π : Subgroup G') : Set G') →
      ∀ s : G, s ∈ J → u * s * u⁻¹ ∈ J := by
    intro u hu s hs
    have hπs : π s ∈ J.map π := ⟨s, hs, rfl⟩
    have huin : π u * π s * (π u)⁻¹ ∈ J.map π :=
      (Subgroup.mem_normalizer_iff.mp hu (π s)).mp hπs
    have hmap : π (u * s * u⁻¹) ∈ J.map π := by
      simpa [map_mul] using huin
    have hmem : u * s * u⁻¹ ∈ J ⊔ C := by
      rw [← hJcomap, Subgroup.mem_comap]
      exact hmap
    have hx : u * s * u⁻¹ ∈ X ⊓ (J ⊔ C) :=
      ⟨hXnorm.conj_mem s (hJX hs) u, hmem⟩
    rwa [hXCJ] at hx
  have hnormalizer : ∀ t : G, π t ∈ Subgroup.normalizer ((J.map π : Subgroup G') : Set G') →
      t ∈ Subgroup.normalizer (J : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hstep t ht h
    · intro hh
      have htinv : π t⁻¹ ∈ Subgroup.normalizer ((J.map π : Subgroup G') : Set G') := by
        rw [map_inv]
        exact (Subgroup.normalizer _).inv_mem ht
      have hthis := hstep t⁻¹ htinv (t * h * t⁻¹) hh
      have hcancel : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [hcancel] at hthis
  have hTN : T.map π ⊓ Subgroup.normalizer ((J.map π : Subgroup G') : Set G') =
      (T ⊓ Subgroup.normalizer (J : Set G)).map π := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_map] at hx
      obtain ⟨hxT, hxN⟩ := hx
      obtain ⟨t, htT, rfl⟩ := hxT
      exact Subgroup.mem_map.mpr ⟨t, ⟨htT, hnormalizer t hxN⟩, rfl⟩
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩,
          (Subgroup.le_normalizer_map π) (Subgroup.mem_map.mpr ⟨t, ht.2, rfl⟩)⟩
  have hA'map : A' = A.map π := by
    change F12.autNL (T.map π) (J.map π) = (F12.autNL T J).map π
    simp only [F12.autNL, Subgroup.map_sup, hTN]
  let φ : ↥A →* ↥A' :=
    { toFun := fun a => ⟨π (a : G), by
        rw [hA'map]
        exact Subgroup.mem_map_of_mem π a.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [map_mul] }
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : G') ∈ A.map π := by rw [← hA'map]; exact y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, hae⟩ := hy
    exact ⟨⟨a, ha⟩, by ext; exact hae⟩
  have hmemK' : ∀ a : ↥A, π (a : G) ∈ K' ↔ (a : G) ∈ K := by
    intro a
    have hmemA' : π (a : G) ∈ A' := by
      rw [hA'map]
      exact Subgroup.mem_map_of_mem π a.2
    rw [show K' = A' ⊓ Subgroup.centralizer ((J.map π : Subgroup G') : Set G') from rfl,
      show K = A ⊓ Subgroup.centralizer (J : Set G) from rfl,
      Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hcent⟩
      refine ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hcent ⊢
      intro j hj
      have hcomm_pi : π j * π (a : G) = π (a : G) * π j := hcent (π j) ⟨j, hj, rfl⟩
      have ha_norm : (a : G) ∈ Subgroup.normalizer (J : Set G) := hA_le a.2
      have hconj : (a : G) * j * (a : G)⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp ha_norm j).mp hj
      have hcJ : (a : G) * j * (a : G)⁻¹ * j⁻¹ ∈ J :=
        J.mul_mem hconj (J.inv_mem hj)
      have hπc : π ((a : G) * j * (a : G)⁻¹ * j⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        calc π (a : G) * π j * (π (a : G))⁻¹ * (π j)⁻¹
            = (π (a : G) * π j) * ((π j * π (a : G))⁻¹) := by
              rw [mul_inv_rev]; group
          _ = (π (a : G) * π j) * ((π (a : G) * π j)⁻¹) := by rw [hcomm_pi]
          _ = 1 := mul_inv_cancel _
      have hcC : (a : G) * j * (a : G)⁻¹ * j⁻¹ ∈ C := by
        rw [← hπker, MonoidHom.mem_ker]
        exact hπc
      have hcX : (a : G) * j * (a : G)⁻¹ * j⁻¹ ∈ X := hJX hcJ
      have hcbot : (a : G) * j * (a : G)⁻¹ * j⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hXC]
        exact ⟨hcX, hcC⟩
      rw [Subgroup.mem_bot] at hcbot
      have h' : (a : G) * j * (j * (a : G))⁻¹ = 1 := by
        simpa only [mul_inv_rev, mul_assoc] using hcbot
      exact (mul_inv_eq_one.mp h').symm
    · rintro ⟨-, hcent⟩
      refine ⟨hmemA', ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hcent ⊢
      rintro h ⟨j, hj, rfl⟩
      show π j * π (a : G) = π (a : G) * π j
      rw [← map_mul, ← map_mul, hcent j hj]
  let ψ : ↥A →* ↥A' ⧸ K'.subgroupOf A' := (QuotientGroup.mk' (K'.subgroupOf A')).comp φ
  have hψker : ψ.ker = K.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hiff : (ψ a = 1) ↔ π (a : G) ∈ K' := by
      change (QuotientGroup.mk (φ a) : (↥A' ⧸ K'.subgroupOf A')) = 1 ↔ π (a : G) ∈ K'
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [hiff, hmemK' a]
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective ((QuotientGroup.mk' (K'.subgroupOf A')).comp φ)
    exact (QuotientGroup.mk'_surjective (K'.subgroupOf A')).comp hφsurj
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)⟩

theorem fourFive_autQuot_equiv_subgroupOf {Q : Type} [Group Q] {T J U : Subgroup Q}
    (hT : T ≤ U) (hJ : J ≤ U) :
    Nonempty ((↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)) ≃*
      (↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U)) ⧸
        (F12.autC (T.subgroupOf U) (J.subgroupOf U)).subgroupOf
          (F12.autNL (T.subgroupOf U) (J.subgroupOf U)))) := by
  let A : Subgroup Q := F12.autNL T J
  let K : Subgroup Q := F12.autC T J
  have hAU : A ≤ U := by
    change F12.autNL T J ≤ U
    rw [F12.autNL]
    exact sup_le (inf_le_left.trans hT) hJ
  have hNL : F12.autNL (T.subgroupOf U) (J.subgroupOf U) = A.subgroupOf U := by
    have hnorm : Subgroup.normalizer (J.subgroupOf U) = (Subgroup.normalizer J).subgroupOf U :=
      (Subgroup.subgroupOf_normalizer_eq hJ).symm
    have hinf : (T.subgroupOf U) ⊓ (Subgroup.normalizer J).subgroupOf U =
        (T ⊓ Subgroup.normalizer J).subgroupOf U :=
      (Subgroup.comap_inf T (Subgroup.normalizer J) U.subtype).symm
    have hsup : ((T ⊓ Subgroup.normalizer J).subgroupOf U) ⊔ J.subgroupOf U =
        ((T ⊓ Subgroup.normalizer J) ⊔ J).subgroupOf U :=
      (Subgroup.subgroupOf_sup (inf_le_left.trans hT) hJ).symm
    calc F12.autNL (T.subgroupOf U) (J.subgroupOf U)
        = (T.subgroupOf U ⊓ Subgroup.normalizer (J.subgroupOf U)) ⊔ J.subgroupOf U := rfl
      _ = (T.subgroupOf U ⊓ (Subgroup.normalizer J).subgroupOf U) ⊔ J.subgroupOf U := by
            rw [hnorm]
      _ = ((T ⊓ Subgroup.normalizer J).subgroupOf U) ⊔ J.subgroupOf U := by rw [hinf]
      _ = ((T ⊓ Subgroup.normalizer J) ⊔ J).subgroupOf U := hsup
      _ = A.subgroupOf U := rfl
  have hC : F12.autC (T.subgroupOf U) (J.subgroupOf U) = K.subgroupOf U := by
    have hcent : Subgroup.centralizer ((J.subgroupOf U : Subgroup U) : Set U) =
        (Subgroup.centralizer (J : Set Q)).subgroupOf U := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro hc h hh
        have hhU : h ∈ U := hJ hh
        have hmem : (⟨h, hhU⟩ : ↥U) ∈ J.subgroupOf U := by
          rw [Subgroup.mem_subgroupOf]
          exact hh
        exact congrArg Subtype.val (hc ⟨h, hhU⟩ hmem)
      · intro hc h hh
        exact Subtype.ext (hc (h : Q) (Subgroup.mem_subgroupOf.mp hh))
    calc F12.autC (T.subgroupOf U) (J.subgroupOf U)
        = F12.autNL (T.subgroupOf U) (J.subgroupOf U) ⊓
            Subgroup.centralizer ((J.subgroupOf U : Subgroup U) : Set U) := rfl
      _ = (A.subgroupOf U) ⊓ (Subgroup.centralizer (J : Set Q)).subgroupOf U := by
            rw [hNL, hcent]
      _ = (A ⊓ Subgroup.centralizer (J : Set Q)).subgroupOf U :=
            (Subgroup.comap_inf A (Subgroup.centralizer (J : Set Q)) U.subtype).symm
      _ = K.subgroupOf U := rfl
  let e : ↥A ≃* ↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U)) :=
    (Subgroup.subgroupOfEquivOfLe hAU).symm.trans (MulEquiv.subgroupCongr hNL).symm
  have e_apply : ∀ x : ↥A,
      ((e x : ↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U))) : Q) = ((x : ↥A) : Q) := by
    intro x
    change (((e x : ↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U))) : ↥U) : Q) =
      ((x : ↥A) : Q)
    dsimp only [e]
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
    rfl
  have he : (K.subgroupOf A).map e.toMonoidHom =
      (F12.autC (T.subgroupOf U) (J.subgroupOf U)).subgroupOf
        (F12.autNL (T.subgroupOf U) (J.subgroupOf U)) := by
    ext x
    rw [Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf, hC]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((e y : ↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U))) : Q) ∈ K
      rwa [e_apply y]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      have hx' : ((e.symm x : ↥A) : Q) =
          ((x : ↥(F12.autNL (T.subgroupOf U) (J.subgroupOf U))) : Q) := by
        rw [← e_apply (e.symm x), e.apply_symm_apply x]
      rwa [hx']
  exact ⟨QuotientGroup.congr (K.subgroupOf A)
    ((F12.autC (T.subgroupOf U) (J.subgroupOf U)).subgroupOf
      (F12.autNL (T.subgroupOf U) (J.subgroupOf U))) e he⟩

theorem fourFive_autQuot_equiv_mk {G : Type} [Group G] {T J X C : Subgroup G} [X.Normal]
    [C.Normal] (hJX : J ≤ X) (hXC : X ⊓ C = ⊥) :
    Nonempty ((↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)) ≃*
      (↥(F12.autNL (T.map (QuotientGroup.mk' C)) (J.map (QuotientGroup.mk' C))) ⧸
        (F12.autC (T.map (QuotientGroup.mk' C)) (J.map (QuotientGroup.mk' C))).subgroupOf
          (F12.autNL (T.map (QuotientGroup.mk' C)) (J.map (QuotientGroup.mk' C))))) :=
  fourFive_autQuot_equiv_mk_aux (QuotientGroup.mk' C) (QuotientGroup.ker_mk' C) hJX hXC

theorem fourFive_autQuot_equiv_quotient {Q : Type} [Group Q] {T J X U C : Subgroup Q}
    (hTU : T ≤ U) (hJX : J ≤ X) (hXU : X ≤ U) [(X.subgroupOf U).Normal]
    [(C.subgroupOf U).Normal] (hXC : X ⊓ C = ⊥) :
    Nonempty ((↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)) ≃*
      (↥(F12.autNL ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))
          ((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))) ⧸
        (F12.autC ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))
          ((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))).subgroupOf
          (F12.autNL ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))
            ((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))))) := by
  have hJ' : J.subgroupOf U ≤ X.subgroupOf U := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hJX hx
  have hXC' : X.subgroupOf U ⊓ C.subgroupOf U = ⊥ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      ← Subgroup.mem_inf, hXC]
    simp
  obtain ⟨e₁⟩ := fourFive_autQuot_equiv_subgroupOf hTU (hJX.trans hXU)
  obtain ⟨e₂⟩ := fourFive_autQuot_equiv_mk (G := ↥U) (T := T.subgroupOf U)
    (J := J.subgroupOf U) (X := X.subgroupOf U) (C := C.subgroupOf U) hJ' hXC'
  exact ⟨e₁.trans e₂⟩

end CFSG.LocalAnalysis.WeakClosure81
