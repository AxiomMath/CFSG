module

public import CFSG.Walter.Bender1970.S4.Solvable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

section General

omit [Finite G] in
theorem isPerfect_of_isComponentOf {K A : Subgroup G} (hK : IsComponentOf K A) :
    Group.IsPerfect K :=
  Group.isPerfect_def.mpr hK.2.2.2.1

omit [Finite G] in
theorem le_componentLayerOf_of_isComponentOf {K A : Subgroup G} (hK : IsComponentOf K A) :
    K ≤ componentLayerOf A :=
  le_sSup (s := {E | IsComponentOf E A}) hK

omit [Finite G] in
theorem isComponentOf_of_le {K A Y : Subgroup G} (hK : IsComponentOf K A) (hKY : K ≤ Y)
    (hYA : Y ≤ A) : IsComponentOf K Y :=
  ⟨hKY, isSubnormal_subgroupOf_of_le hKY hYA hK.2.1, hK.2.2⟩

omit [Finite G] in
theorem not_le_centralizer_self_of_isComponentOf {K A : Subgroup G} (hK : IsComponentOf K A) :
    ¬ K ≤ Subgroup.centralizer (K : Set G) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isQuasisimple hK.2.2
  exact hab (Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h a.2)) b b.2).symm)

omit [Finite G] in
theorem ne_bot_of_isComponentOf {K A : Subgroup G} (hK : IsComponentOf K A) : K ≠ ⊥ := by
  intro h
  apply not_le_centralizer_self_of_isComponentOf hK
  rw [h]
  exact bot_le

theorem le_centralizer_of_isComponentOf_ne {K K' A : Subgroup G} (hK : IsComponentOf K A)
    (hK' : IsComponentOf K' A) (hne : K ≠ K') : K ≤ Subgroup.centralizer (K' : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((isComponentOf_eq_or_commutator_eq_bot hK hK').resolve_left hne)

theorem eq_of_isComponentOf_of_le {K K' A : Subgroup G} (hK : IsComponentOf K A)
    (hK' : IsComponentOf K' A) (h : K ≤ K') : K = K' := by
  by_contra hne
  exact not_le_centralizer_self_of_isComponentOf hK
    ((le_centralizer_of_isComponentOf_ne hK hK' hne).trans (Subgroup.centralizer_le h))

omit [Finite G] in
theorem mem_normalizer_componentLayerOf {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (componentLayerOf A : Set G) := by
  unfold componentLayerOf
  exact mem_normalizer_sSup_of_map_mem (fun K hK => isComponentOf_map_conj hK hg)
    (fun K hK => isComponentOf_map_conj hK (Subgroup.inv_mem _ hg))

omit [Finite G] in
theorem le_componentLayerOf_of_isPerfect {Y P : Subgroup G}
    (hY : Group.IsSolvable (Y ⧸ (componentLayerOf Y).subgroupOf Y)) (hPY : P ≤ Y)
    [Group.IsPerfect P] : P ≤ componentLayerOf Y := by
  have : Group.IsPerfect (P.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPY).symm.surjective
  have h := le_ker_of_isPerfect (P.subgroupOf Y)
    (QuotientGroup.mk' ((componentLayerOf Y).subgroupOf Y))
  rw [QuotientGroup.ker_mk'] at h
  intro x hx
  have hx' : (⟨x, hPY hx⟩ : Y) ∈ P.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (h hx')

theorem le_normalizer_of_isPGroup_of_isComponentOf_subgroup {X P L : Subgroup G}
    (hX : HasAbelianSylowTwo X) (hPX : P ≤ X) (hP : IsPGroup 2 P) (hL : IsComponentOf L X) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  have hP' : IsPGroup 2 (P.subgroupOf X) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  have h1 := le_normalizer_of_isPGroup_of_isComponentOf hX hP'
    (fstar_isComponentOf_subgroupOf_top hL)
  intro x hx
  have h2 := h1 (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hPX hx⟩ : X) ∈ P.subgroupOf X)
  rw [← Subgroup.subgroupOf_normalizer_eq hL.1, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem mem_normalizer_of_orderOf_eq_two {X L : Subgroup G} (hX : HasAbelianSylowTwo X)
    {x : G} (hxX : x ∈ X) (hx : orderOf x = 2) (hL : IsComponentOf L X) :
    x ∈ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_isPGroup_of_isComponentOf_subgroup hX (Subgroup.zpowers_le.mpr hxX)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])) hL
    (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem mem_centralizer_of_conj_mem {x g j : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (h : g * j * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G)) :
    j ∈ Subgroup.centralizer ({x} : Set G) := by
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp h
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h3 : g * (j * x) * g⁻¹ = g * (x * j) * g⁻¹ := by
    calc g * (j * x) * g⁻¹ = (g * j * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (g * j * g⁻¹) * x := by rw [h2, mul_inv_cancel_right]
      _ = x * (g * j * g⁻¹) := h1
      _ = (g * x * g⁻¹) * (g * j * g⁻¹) := by rw [h2, mul_inv_cancel_right]
      _ = g * (x * j) * g⁻¹ := by group
  simpa using h3

omit [Finite G] in
theorem le_commutator_zpowers_of_not_le_centralizer {L : Subgroup G}
    (hL : GorensteinWalter.IsQuasisimple L)
    {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (h : ¬ L ≤ Subgroup.centralizer ({x} : Set G)) : L ≤ ⁅L, Subgroup.zpowers x⁆ := by
  have hcL : ⁅L, Subgroup.zpowers x⁆ ≤ L := commutator_zpowers_le_of_mem_normalizer hxL
  refine le_of_not_le_centralizer hL (Subgroup.normalizer_commutator_ge_left L _) le_rfl
    (hcL.trans Subgroup.le_normalizer) fun hC => h ?_
  have hc := mem_centralizer_of_commutator_mem_center hL.2.1 (c := x) fun l hl => by
    have hmem : x * l * x⁻¹ * l⁻¹ ∈ ⁅L, Subgroup.zpowers x⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) hl
    refine ⟨⟨x * l * x⁻¹ * l⁻¹, hcL hmem⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hC y.2)) _ hmem).symm
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hc) l hl

end General

omit [Finite G] in
theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem normalizer_sSup_isComponentOf_eq [IsSimpleGroup G] {H K : Subgroup G}
    (hHco : IsCoatom H) (𝒯 : Subgroup G → Prop)
    (h𝒯 : ∀ (J : Subgroup G) (g : G), 𝒯 J → 𝒯 (J.map (MulAut.conj g).toMonoidHom))
    (hK : IsComponentOf K H) (hPK : 𝒯 K) :
    Subgroup.normalizer ((sSup {J | IsComponentOf J H ∧ 𝒯 J} : Subgroup G) : Set G) = H := by
  set N := sSup {J | IsComponentOf J H ∧ 𝒯 J} with hNdef
  have hKN : K ≤ N := le_sSup ⟨hK, hPK⟩
  have hNH : N ≤ H := sSup_le fun J hJ => hJ.1.1
  have hN1 : N ≠ ⊥ := fun h0 => ne_bot_of_isComponentOf hK (le_bot_iff.mp (h0 ▸ hKN))
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    mem_normalizer_sSup_of_map_mem
      (fun J hJ => ⟨isComponentOf_map_conj hJ.1 (Subgroup.le_normalizer hg), h𝒯 J g hJ.2⟩)
      (fun J hJ => ⟨isComponentOf_map_conj hJ.1 (Subgroup.le_normalizer (H.inv_mem hg)),
        h𝒯 J g⁻¹ hJ.2⟩)
  exact normalizer_eq_of_nontrivial_normal_in_coatom ‹_› hHco hNH hN1
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN)

theorem le_normalizer_of_forall_map_conj_eq {Y K : Subgroup G} (hY : IsAStar Y)
    (hK : IsComponentOf K Y) (T : Sylow 2 G) (hTY : (T : Subgroup G) ≤ Y)
    (huniq : ∀ a ∈ Y, ∀ b ∈ Y, K.map (MulAut.conj a).toMonoidHom ≠ K →
      K.map (MulAut.conj b).toMonoidHom ≠ K →
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    Y ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  obtain ⟨g, hgY, hgN⟩ := Set.not_subset.mp hcon
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'K : K' ≠ K := fun h => hgN (map_conj_eq_iff_mem_normalizer.mp h)
  set A := (Subgroup.normalizer (K : Set G)).subgroupOf Y with hA
  have hmemA : ∀ b : Y, b ∈ A ↔ K.map (MulAut.conj (b : G)).toMonoidHom = K := fun b => by
    rw [Subgroup.mem_subgroupOf, map_conj_eq_iff_mem_normalizer]
  have hinj : ∀ (b : G) (A₁ A₂ : Subgroup G), A₁.map (MulAut.conj b).toMonoidHom =
      A₂.map (MulAut.conj b).toMonoidHom → A₁ = A₂ :=
    fun b _ _ h => Subgroup.map_injective (MulAut.conj b).injective h
  have hA2 : A.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgY⟩, fun b => xor_iff_iff_not.mpr ⟨fun hbg hb => ?_, fun hb => ?_⟩⟩
    · rw [hmemA, Subgroup.coe_mul, ← map_conj_map_conj] at hbg
      rw [hmemA] at hb
      exact hK'K (hinj b K' K (hbg.trans hb.symm))
    · rw [hmemA] at hb
      rw [hmemA, Subgroup.coe_mul, ← map_conj_map_conj]
      by_contra hne
      have h1 := huniq _ (Y.mul_mem b.2 hgY) _ b.2
        (by rw [← map_conj_map_conj]; exact hne) hb
      rw [← map_conj_map_conj] at h1
      exact hK'K (hinj b K' K h1)
  have hTA : (T : Subgroup G).subgroupOf Y ≤ A := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (component_sylow_le_normalizer hY hK T hTY hx)
  have hodd : ¬ 2 ∣ ((T.subtype hTY : Sylow 2 Y) : Subgroup Y).index := Sylow.not_dvd_index _
  rw [Sylow.coe_subtype] at hodd
  have h := Subgroup.index_dvd_of_le hTA
  rw [hA2] at h
  exact hodd h

theorem le_normalizer_of_forall_eq {Y K : Subgroup G} (hY : IsAStar Y) (hK : IsComponentOf K Y)
    (T : Sylow 2 G) (hTY : (T : Subgroup G) ≤ Y)
    (huniq : ∀ J₁ J₂ : Subgroup G, IsComponentOf J₁ Y → IsComponentOf J₂ Y → J₁ ≠ K → J₂ ≠ K →
      J₁ = J₂) :
    Y ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_forall_map_conj_eq hY hK T hTY fun _ ha _ hb h1 h2 =>
    huniq _ _ (isComponentOf_map_conj hK (Subgroup.le_normalizer ha))
      (isComponentOf_map_conj hK (Subgroup.le_normalizer hb)) h1 h2

theorem isComponentOf_of_isComponentOf_inf_centralizer {H K J : Subgroup G}
    (hK : IsComponentOf K H) (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer (K : Set G))) :
    IsComponentOf J H := by
  by_contra hJH
  set C := H ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hJC : J ≤ C := hJ.1
  have hJH' : J ≤ H := hJC.trans inf_le_left
  have hFC : CFSG.fittingSubgroupOf H ≤ C :=
    le_inf (CFSG.fittingSubgroupOf_le H) ((fittingSubgroupOf_le_centralizer_layer H).trans
      (Subgroup.centralizer_le (le_componentLayerOf_of_isComponentOf hK)))
  have hFs : Group.IsSolvable (CFSG.fittingSubgroupOf H) := by
    have := CFSG.fittingSubgroupOf_isNilpotent H
    infer_instance
  have hJF : CFSG.fittingSubgroupOf H ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (isComponentOf_commutator_eq_bot_of_isSolvable hJ hFs hFC
        (inf_le_left.trans (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn H)))))
  have hJE : componentLayerOf H ≤ Subgroup.centralizer (J : Set G) := by
    refine sSup_le fun L hL => ?_
    by_cases hLK : L = K
    · rw [hLK]
      exact Subgroup.le_centralizer_iff.mp (hJC.trans inf_le_right)
    · have hLC : IsComponentOf L C := isComponentOf_of_le hL
        (le_inf hL.1 (le_centralizer_of_isComponentOf_ne hL hK hLK)) inf_le_left
      rcases isComponentOf_eq_or_commutator_eq_bot hJ hLC with h | h
      · exact absurd (h ▸ hL) hJH
      · exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hJF' : J ≤ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) :=
    Subgroup.le_centralizer_iff.mp (sup_le hJF hJE)
  have hJFs : J ≤ generalizedFittingSubgroupOf H :=
    fun j hj => Bender35.inf_centralizer_le_generalizedFitting H ⟨hJH' hj, hJF' hj⟩
  exact not_le_centralizer_self_of_isComponentOf hJ (hJF'.trans (Subgroup.centralizer_le hJFs))

theorem centralizer_le_and_eq_of_forall_isComponentOf [IsSimpleGroup G] {H K : Subgroup G}
    (hHco : IsCoatom H) (hK : IsComponentOf K H) (𝒯 : Subgroup G → Prop)
    (h𝒯 : ∀ (J : Subgroup G) (g : G), 𝒯 J → 𝒯 (J.map (MulAut.conj g).toMonoidHom))
    (hPK : 𝒯 K)
    (h : ∀ J : Subgroup G, IsComponentOf J H → 𝒯 J → J ≠ K →
      IsComponentOf J (Subgroup.centralizer (K : Set G))) :
    Subgroup.centralizer (K : Set G) ≤ H ∧
      Subgroup.normalizer ((sSup {J | IsComponentOf J H ∧ 𝒯 J} : Subgroup G) : Set G) = H ∧
      sSup {J | IsComponentOf J H ∧ 𝒯 J} =
        K ⊔ sSup {J | IsComponentOf J (Subgroup.centralizer (K : Set G)) ∧ 𝒯 J} := by
  set C := Subgroup.centralizer (K : Set G) with hCdef
  set N := sSup {J | IsComponentOf J H ∧ 𝒯 J} with hNdef
  set NC := sSup {J | IsComponentOf J C ∧ 𝒯 J} with hNCdef
  have hKN : K ≤ N := le_sSup ⟨hK, hPK⟩
  have hNorm : Subgroup.normalizer (N : Set G) = H :=
    normalizer_sSup_isComponentOf_eq hHco 𝒯 h𝒯 hK hPK
  have hEN : componentLayerOf C ≤ Subgroup.normalizer (N : Set G) := by
    refine sSup_le fun J' hJ' => ?_
    intro x hx
    refine mem_normalizer_sSup fun J hJ => ?_
    by_cases hJK : J = K
    · rw [hJK]
      exact Subgroup.centralizer_le_normalizer _ (hJ'.1 hx)
    · rcases isComponentOf_eq_or_commutator_eq_bot hJ' (h J hJ.1 hJ.2 hJK) with h' | h'
      · exact Subgroup.le_normalizer (h' ▸ hx)
      · exact Subgroup.centralizer_le_normalizer _
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h') hx)
  have hECH : componentLayerOf C ≤ H := hEN.trans hNorm.le
  have hcomp : ∀ J', IsComponentOf J' C → IsComponentOf J' H := fun J' hJ' =>
    isComponentOf_of_isComponentOf_inf_centralizer hK
      (isComponentOf_of_le hJ'
        (le_inf ((le_componentLayerOf_of_isComponentOf hJ').trans hECH) hJ'.1) inf_le_right)
  have hNeq : N = K ⊔ NC := by
    apply le_antisymm
    · refine sSup_le fun J hJ => ?_
      by_cases hJK : J = K
      · exact hJK ▸ le_sup_left
      · exact (le_sSup (s := {J | IsComponentOf J C ∧ 𝒯 J}) ⟨h J hJ.1 hJ.2 hJK, hJ.2⟩).trans
          le_sup_right
    · exact sup_le hKN (sSup_le fun J' hJ' => le_sSup ⟨hcomp J' hJ'.1, hJ'.2⟩)
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [hNeq]
    refine mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ hg) ?_
    exact mem_normalizer_sSup_of_map_mem
      (fun J hJ => ⟨isComponentOf_map_conj hJ.1 (Subgroup.le_normalizer hg), h𝒯 J g hJ.2⟩)
      (fun J hJ => ⟨isComponentOf_map_conj hJ.1 (Subgroup.le_normalizer (C.inv_mem hg)),
        h𝒯 J g⁻¹ hJ.2⟩)
  exact ⟨hCN.trans hNorm.le, hNorm, hNeq⟩

theorem exists_isComponentOf_of_le
    {X Y : Subgroup G} (hX : HasAbelianSylowTwo X)
    (hY : IsAStar Y) (hYs : Group.IsSolvable (Y ⧸ (componentLayerOf Y).subgroupOf Y)) {x : G}
    (hxX : x ∈ X) (hxY : x ∈ Y) (hx : orderOf x = 2)
    (hCY : Y ⊓ Subgroup.centralizer ({x} : Set G) ≤ X) {L : Subgroup G}
    (hL : IsComponentOf L X) (hLY : L ≤ Y) :
    ∃ L' : Subgroup G, IsComponentOf L' Y ∧ L ≤ L' ∧
      (L = L' ∨ (IsTypeL2Odd (L ⧸ Subgroup.center L) ∧ IsTypeJR (L' ⧸ Subgroup.center L') ∧
        L ≤ Subgroup.centralizer ({x} : Set G))) := by
  have := isPerfect_of_isComponentOf hL
  have hLE : L ≤ componentLayerOf Y := le_componentLayerOf_of_isPerfect hYs hLY
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_orderOf_eq_two hX hxX hx hL
  by_cases hLx : L ≤ Subgroup.centralizer ({x} : Set G)
  ·
    set Y₀ := componentLayerOf Y ⊓ Subgroup.centralizer ({x} : Set G) with hY₀
    have hY₀X : Y₀ ≤ X := (inf_le_inf_right _ (componentLayerOf_isNormalIn Y).1).trans hCY
    have hLY₀ : IsComponentOf L Y₀ := isComponentOf_of_le hL (le_inf hLE hLx) hY₀X
    set E := componentLayerOf Y₀ with hE
    have hLE' : L ≤ E := le_componentLayerOf_of_isComponentOf hLY₀
    have hEY₀ : E ≤ Y₀ := sSup_le fun J hJ => hJ.1
    have hLEc : IsComponentOf L E := isComponentOf_of_le hLY₀ hLE' hEY₀
    have hEt : Y ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (E : Set G) :=
      fun g hg => mem_normalizer_componentLayerOf (mem_normalizer_inf
        (mem_normalizer_componentLayerOf (Subgroup.le_normalizer hg.1))
        (Subgroup.le_normalizer hg.2))
    exact bender1970_2_3_subgroup hY hxY hx (hEY₀.trans inf_le_left) hEt hLEc
  ·
    set 𝒲 : Set (Subgroup G) := {J | IsComponentOf J X ∧ J ≤ Y ∧
      ¬ J ≤ Subgroup.centralizer ({x} : Set G)} with h𝒲
    set W := sSup 𝒲 with hW
    have hL𝒲 : L ∈ 𝒲 := ⟨hL, hLY, hLx⟩
    have hLW : L ≤ W := le_sSup hL𝒲
    have hWY : W ≤ Y := sSup_le fun J hJ => hJ.2.1
    have hWN : ∀ J ∈ 𝒲, W ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
      sSup_le fun J' hJ' => by
        rcases isComponentOf_eq_or_commutator_eq_bot hJ'.1 hJ.1 with h | h
        · exact h ▸ Subgroup.le_normalizer
        · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
            (Subgroup.centralizer_le_normalizer _)
    have hmap : ∀ g ∈ Y ⊓ Subgroup.centralizer ({x} : Set G), ∀ J ∈ 𝒲,
        J.map (MulAut.conj g).toMonoidHom ∈ 𝒲 := by
      intro g hg J hJ
      refine ⟨isComponentOf_map_conj hJ.1 (Subgroup.le_normalizer (hCY hg)), ?_, ?_⟩
      · rintro _ ⟨j, hj, rfl⟩
        exact Y.mul_mem (Y.mul_mem hg.1 (hJ.2.1 hj)) (Y.inv_mem hg.1)
      · intro hcon
        exact hJ.2.2 fun j hj => mem_centralizer_of_conj_mem hg.2 (hcon ⟨j, hj, rfl⟩)
    have hWt : Y ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (W : Set G) :=
      fun g hg => mem_normalizer_sSup_of_map_mem (hmap g hg) (hmap g⁻¹ (Subgroup.inv_mem _ hg))
    have hWE : W ≤ componentLayerOf W := sSup_le fun J hJ =>
      le_sSup (⟨le_sSup hJ, isSubnormal_subgroupOf_of_le_normalizer (le_sSup hJ) (hWN J hJ),
        hJ.1.2.2⟩ : IsComponentOf J W)
    have hWF : generalizedFittingSubgroupOf W = W :=
      le_antisymm (generalizedFittingSubgroupOf_le W) (hWE.trans le_sup_right)
    obtain ⟨hWF', hWsn⟩ := bender1970_2_4_subgroup hY hxY hx hWY hWt hWF
    have hLc : L ≤ ⁅W, Subgroup.zpowers x⁆ :=
      (le_commutator_zpowers_of_not_le_centralizer hL.2.2 hxN hLx).trans
        (Subgroup.commutator_mono hLW le_rfl)
    have hWx : ⁅W, Subgroup.zpowers x⁆ ≤ W := commutator_zpowers_le_of_mem_normalizer
      (hWt ⟨hxY, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    have hLsn : (L.subgroupOf ⁅W, Subgroup.zpowers x⁆).IsSubnormal :=
      isSubnormal_subgroupOf_of_le_normalizer hLc (hWx.trans (hWN L hL𝒲))
    have hL' : (L.subgroupOf Y).IsSubnormal :=
      isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting (hLc.trans hWF')
        (isSubnormal_subgroupOf_trans hLc hLsn hWsn)
    exact ⟨L, ⟨hLY, hL', hL.2.2⟩, le_rfl, Or.inl rfl⟩

end CFSG.Walter
