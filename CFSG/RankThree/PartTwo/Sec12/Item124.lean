module

public import CFSG.RankThree.PartTwo.Sec12.Coordinates
public import CFSG.RankThree.PartTwo.Sec3.TransvectionGroupNine

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Module
open CFSG.ABGLocalTools (IsSylowOf)

section Sylow

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem IsSylowOf.map {Y : Type*} [Group Y] {P B : Subgroup X} (h : IsSylowOf p P B)
    (φ : X →* Y) : IsSylowOf p (P.map φ) (B.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective B), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_of_normalizer_le {R M K : Subgroup X} (hRM : IsSylowOf p R M) (hMK : M ≤ K)
    (hN : K ⊓ Subgroup.normalizer (R : Set X) ≤ M) : IsSylowOf p R K := by
  have hRK : R ≤ K := hRM.le.trans hMK
  obtain ⟨Q, hQ⟩ := (hRM.isPGroup.comap_subtype (K := K)).exists_le_sylow
  set S : Subgroup X := (Q : Subgroup K).map K.subtype with hSdef
  have hRS : R ≤ S := fun x hx => ⟨⟨x, hRK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSK : S ≤ K := Subgroup.map_subtype_le _
  have hS : IsPGroup p S := Q.isPGroup'.map K.subtype
  have hNS : S ⊓ Subgroup.normalizer (R : Set X) = R :=
    hRM.eq_of_le (le_inf hRS Subgroup.le_normalizer) ((inf_le_inf_right _ hSK).trans hN)
      (hS.to_le inf_le_left)
  have hSR : S ≤ R := by
    have hnil : Group.IsNilpotent S := hS.isNilpotent
    have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := S))) (R.subgroupOf S) (by
        refine le_antisymm (fun s hs => ?_) Subgroup.le_normalizer
        rw [Subgroup.mem_subgroupOf, ← hNS]
        refine ⟨s.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
        · have h := (Subgroup.mem_normalizer_iff.mp hs ⟨x, hRS hx⟩).mp
            (Subgroup.mem_subgroupOf.mpr hx)
          exact Subgroup.mem_subgroupOf.mp h
        · have hxS : x ∈ S := by
            have h1 : (s : X) * x * (s : X)⁻¹ ∈ S := hRS hx
            have h2 : x = (s : X)⁻¹ * ((s : X) * x * (s : X)⁻¹) * s := by group
            rw [h2]
            exact S.mul_mem (S.mul_mem (S.inv_mem s.2) h1) s.2
          have h := (Subgroup.mem_normalizer_iff.mp hs ⟨x, hxS⟩).mpr
            (Subgroup.mem_subgroupOf.mpr hx)
          exact Subgroup.mem_subgroupOf.mp h)
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ R.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  rw [le_antisymm hRS hSR]
  exact ⟨Q, rfl⟩

end Sylow

section Line

variable {G : Type*} [Group G] {A : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
  (f : Multiplicative V ≃* A)

theorem conj_mem_zpowers_of_map_eq (c : A) (w : Subgroup.normalizer (A : Set G))
    (hw : (Submodule.span (ZMod 3) {coordVec f c}).map (wAction f w : V →ₗ[ZMod 3] V) =
      Submodule.span (ZMod 3) {coordVec f c}) :
    (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c : G) := by
  have hmem : wAction f w (coordVec f c) ∈ Submodule.span (ZMod 3) {coordVec f c} := by
    rw [← hw]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := wAction_apply f w (coordVec f c)
  have hfc : f (Multiplicative.ofAdd (coordVec f c)) = c := by
    simp [coordVec]
  rw [hfc, ← ht] at h1
  have h2 : (t • coordVec f c : V) = t.val • coordVec f c := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h2, ofAdd_nsmul, map_pow, hfc] at h1
  rw [← h1]
  exact Subgroup.npow_mem_zpowers _ _

theorem mem_normalizer_zpowers_of_map_eq (c : A) (w : Subgroup.normalizer (A : Set G))
    (hw : (Submodule.span (ZMod 3) {coordVec f c}).map (wAction f w : V →ₗ[ZMod 3] V) =
      Submodule.span (ZMod 3) {coordVec f c}) :
    (w : G) ∈ Subgroup.normalizer (Subgroup.zpowers (c : G) : Set G) := by
  set U := Submodule.span (ZMod 3) {coordVec f c}
  have hw' : U.map (wAction f w⁻¹ : V →ₗ[ZMod 3] V) = U := by
    conv_lhs => rw [← hw]
    rw [← Submodule.map_comp]
    convert Submodule.map_id U
    ext x
    simp [map_inv]
  have key : ∀ (v : Subgroup.normalizer (A : Set G)),
      U.map (wAction f v : V →ₗ[ZMod 3] V) = U →
        ∀ y ∈ Subgroup.zpowers (c : G), (v : G) * y * (v : G)⁻¹ ∈ Subgroup.zpowers (c : G) := by
    rintro v hv _ ⟨k, rfl⟩
    have := conj_mem_zpowers_of_map_eq f c v hv
    have e : (v : G) * (c : G) ^ k * (v : G)⁻¹ = ((v : G) * c * (v : G)⁻¹) ^ k := by
      rw [conj_zpow]
    rw [e]
    exact Subgroup.zpow_mem _ this k
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key w hw y, fun hy => ?_⟩
  have := key w⁻¹ hw' _ hy
  simpa [mul_assoc] using this

end Line

theorem range_conj_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (k r : V ≃ₗ[ZMod 3] V) :
    LinearMap.range (((k * r * k⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) - 1) =
      (LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1)).map (k : V →ₗ[ZMod 3] V) := by
  have h : ((k * r * k⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) - 1 =
      (k : V →ₗ[ZMod 3] V) ∘ₗ (((r : V →ₗ[ZMod 3] V) - 1) ∘ₗ (k.symm : V →ₗ[ZMod 3] V)) := by
    ext x
    simp
  rw [h, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

theorem exists_coords_module {G : Type} [Group G] {A : Subgroup G} [Finite A]
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {n : ℕ} (hcard : Nat.card A = 3 ^ n) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V),
      finrank (ZMod 3) V = n ∧ Nonempty (Multiplicative V ≃* A) := by
  obtain ⟨f⟩ := exists_coords hA hcard
  refine ⟨Fin n → ZMod 3, inferInstance,
    @Pi.module (Fin n) (fun _ => ZMod 3) (ZMod 3) _ _ (fun _ => Semiring.toModule), ?_, ⟨f⟩⟩
  exact Module.finrank_fin_fun (ZMod 3)

theorem normalizer_le_of_autIn_eq {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hPaut : Sec4.autIn P A = transvectionGroup A ⟨c, hcA⟩) (hP9 : Nat.card (Sec4.autIn P A) = 9)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (hV : finrank (ZMod 3) V = 3)
    (f : Multiplicative V ≃* A) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set W := Subgroup.normalizer (A : Set G) with hW
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set c' : A := ⟨c, hcA⟩ with hc'
  have hc1' : c' ≠ 1 := fun h1 => hc1 (congrArg Subtype.val h1)
  set U := Submodule.span (ZMod 3) {coordVec f c'} with hU
  set ψ := wAction (G := G) f with hψ
  set K := ψ.range with hK
  set M := ((W ⊓ H).subgroupOf W).map ψ with hM
  set R := (P.subgroupOf W).map ψ with hR
  have hPW : P ≤ W := hP.le.trans inf_le_left
  have hRT : R = (transvectionGroup A c').map (coordHom f) := by
    rw [← hPaut, Sec4.autIn, Subgroup.map_map, hR, hψ, wAction, inf_eq_left.mpr hPW]
  have hR9 : Nat.card R = 9 := by
    rw [hRT, Subgroup.card_map_of_injective (coordHom_injective f), ← hPaut, hP9]
  have hRU : ∀ r ∈ R, r ≠ 1 →
      (∃ v φ, CFSG.RankThree.Classical.IsTransvectionWith r v φ) ∧
        LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1) = U := by
    intro r hr hr1
    rw [hRT] at hr
    obtain ⟨σ, hσ, rfl⟩ := hr
    exact coordHom_isTransvection f hc1' hσ (fun h1 => hr1 (by rw [h1, map_one]))
  have hUdim : finrank (ZMod 3) U = 1 := finrank_span_singleton (coordVec_ne_zero f hc1')
  have hRM : R ≤ M := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hP.le (Subgroup.mem_subgroupOf.mp hx))
  have hMK : M ≤ K := Subgroup.map_le_range _ _
  have hNK : K ⊓ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V)) ≤ M := by
    rintro k ⟨⟨w, rfl⟩, hk⟩
    have hRne : R ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hR9
      exact absurd hR9 (by norm_num)
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
    have hr' : (r : V ≃ₗ[ZMod 3] V) ≠ 1 := fun h1 => hr1 (Subtype.ext h1)
    have hkr : ψ w * r * (ψ w)⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hk r).mp r.2
    have hkr1 : ψ w * r * (ψ w)⁻¹ ≠ 1 := by
      intro h1
      apply hr'
      have := congrArg (fun x => (ψ w)⁻¹ * x * ψ w) h1
      simpa [mul_assoc] using this
    have hUk : U.map (ψ w : V →ₗ[ZMod 3] V) = U := by
      have h1 := (hRU r r.2 hr').2
      have h2 := (hRU _ hkr hkr1).2
      rw [range_conj_sub_one, h1] at h2
      exact h2
    have hwH := mem_normalizer_zpowers_of_map_eq f c' w hUk
    exact ⟨w, Subgroup.mem_subgroupOf.mpr ⟨w.2, hwH⟩, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 3)
  have : Finite (V ≃ₗ[ZMod 3] V) := Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)
  have hPW' : IsSylowOf 3 (P.subgroupOf W) ((W ⊓ H).subgroupOf W) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff W, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPW, inf_eq_left.mpr inf_le_left]
    exact hP
  have hSylM : IsSylowOf 3 R M := IsSylowOf.map hPW' ψ
  have hSylK : IsSylowOf 3 R K := isSylowOf_of_normalizer_le hSylM hMK hNK
  have hfix := (Sec3.rank3II_3_12 hV hUdim (hRM.trans hMK) hR9 hRU).2 hSylK
  intro g hg
  exact mem_normalizer_zpowers_of_map_eq f c' ⟨g, hg⟩ (hfix _ ⟨⟨g, hg⟩, rfl⟩)

theorem item124_of_item123 (h123 : Item123) : Item124 := by
  intro G _ _ A c L h
  obtain ⟨P, hP, hPB⟩ := h.exists_sylow
  obtain ⟨hPaut, hP9⟩ := h123 G A c L h P hP hPB
  have hA27 : Nat.card A = 3 ^ 3 := by rw [h.isE27.2]; norm_num
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := exists_coords_module h.isE27.1 hA27
  exact normalizer_le_of_autIn_eq h.mem_A h.ne_one hP hPaut hP9 hV f

end CFSG.RankThree.PartTwo.Sec12
