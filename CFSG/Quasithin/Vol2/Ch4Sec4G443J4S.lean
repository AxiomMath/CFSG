module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4P
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4H
public import CFSG.Quasithin.Background.B5NonInputs

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin

variable {X : Type} [Group X] [Finite X]

theorem exists_normal_cComp_ge' (hA21 : AsA21SQTKSection) (hX : SQTKGroup X) {B : Subgroup X}
    (hBp : ⁅B, B⁆ = B) (hBE : B ≤ cCompSpan (⊤ : Subgroup X)) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (g : ↥B →* S) (hg : Function.Surjective g)
    (hgk : Group.IsSolvable ↥g.ker) (hS3 : 2 ≤ CFSG.pRank 3 S) :
    ∃ K ∈ cComp (⊤ : Subgroup X), B ≤ K ∧ Subgroup.normalizer (K : Set X) = ⊤ := by
  classical
  set R := CFSG.solvableRadical X with hRdef
  have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  set π := QuotientGroup.mk' R with hπ
  have hY : CFSG.solvableRadical (X ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot X
  set E := CFSG.layer (X ⧸ R) with hEdef
  have hEmap : (cCompSpan (⊤ : Subgroup X)).map π = E := map_cCompSpan_eq_layer
  have hrk : CFSG.Open.pRank 3 E ≤ 2 := by
    have hsq : SQTKGroup ↥E := by
      refine hA21 X hX (E.comap π) ↥E
        ((π.comp (E.comap π).subtype).codRestrict E fun x => x.2) ?_ ⊤ ?_ ?_
      · intro y
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R (y : X ⧸ R)
        refine ⟨⟨x, show π x ∈ E by rw [hx]; exact y.2⟩, Subtype.ext ?_⟩
        exact hx
      · exact CFSG.SectionRank.layer_eq_top_of_mulEquiv Subgroup.topEquiv.symm
          (Lay.layer_coe_layer_eq_top (X ⧸ R))
      · intro y
        exact ⟨0, @Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top _ _⟩
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hsq.1 3 Nat.prime_three (by norm_num)
  set Bt := B.map π with hBt
  have hBtE : Bt ≤ E := hEmap ▸ Subgroup.map_mono hBE
  have hproj : ∀ T : Subgroup (X ⧸ R), CFSG.IsComponent T → ⁅T, Bt⁆ ≠ ⊥ →
      ∃ A : Subgroup (X ⧸ R), A ≤ T ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 := by
    intro T hT hne
    obtain ⟨φ, hφT, hφk⟩ := Lay.exists_proj_hom hY hT
    set ρ : ↥B →* ↥E := (π.comp B.subtype).codRestrict E fun b => hBtE ⟨b, b.2, rfl⟩ with hρ
    set N := B ⊓ (Subgroup.centralizer (T : Set (X ⧸ R))).comap π with hN
    have hTn : Bt ≤ Subgroup.normalizer (T : Set (X ⧸ R)) :=
      hBtE.trans (CFSG.LocalCores.layer_le_normalizer hT)
    have hNn : B ≤ Subgroup.normalizer (N : Set X) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ y ∈ B, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
        intro y hy x hx
        refine ⟨B.mul_mem (B.mul_mem hy hx.1) (B.inv_mem hy), ?_⟩
        show π (y * x * y⁻¹) ∈ Subgroup.centralizer (T : Set (X ⧸ R))
        rw [map_mul, map_mul, map_inv]
        have hyT : π y ∈ Subgroup.normalizer (T : Set (X ⧸ R)) := hTn ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have ht' : (π y)⁻¹ * t * π y ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyT) t).mp ht
          rwa [inv_inv] at this
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ ht'
        calc t * (π y * π x * (π y)⁻¹) = π y * (((π y)⁻¹ * t * π y) * π x) * (π y)⁻¹ := by
              group
          _ = π y * (π x * ((π y)⁻¹ * t * π y)) * (π y)⁻¹ := by rw [h1]
          _ = π y * π x * (π y)⁻¹ * t := by group
      intro x
      refine ⟨fun hx => key b hb x hx, fun hx => ?_⟩
      have := key b⁻¹ (B.inv_mem hb) _ hx
      simpa [mul_assoc] using this
    rcases eq_or_le_ker hBp g hg hgk inf_le_left hNn with h | h
    · exfalso
      apply hne
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← h] at hb
      exact (Subgroup.mem_centralizer_iff.mp hb.2 t ht).symm
    · have hf : ∀ b, (φ.comp ρ) b = 1 → g b = 1 := fun b hb => h b ⟨b.2, hφk _ hb⟩
      have h2 := two_le_pRank_of_le_ker g hg hS3 (φ.comp ρ) hf
      obtain ⟨A, hA, hAab, hAc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
      have hle : (φ.comp ρ).range ≤ φ.range := by
        rintro _ ⟨b, rfl⟩
        exact ⟨ρ b, rfl⟩
      exact ⟨A, hA.trans (hle.trans hφT), hAab, by rw [hAc]; norm_num⟩
  obtain ⟨S₀, hS₀, hS₀ne⟩ : ∃ S₀ : Subgroup (X ⧸ R), CFSG.IsComponent S₀ ∧ ⁅S₀, Bt⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hBtC : Bt ≤ Subgroup.centralizer (E : Set (X ⧸ R)) := by
      rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun T hT => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno T hT)
    have hBt1 : Bt = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyZ : y ∈ (Subgroup.center E).map E.subtype :=
        (CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hBtE hy, hBtC hy⟩
      rwa [Lay.center_layer_eq_bot hY] at hyZ
    have hBR : B ≤ R := fun b hb => by
      have : π b ∈ Bt := ⟨b, hb, rfl⟩
      rw [hBt1, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hBs : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBR)
    have hB1 : B = ⊥ := by
      rw [← perfectCore_eq_self_of_perfect hBp]
      exact (isSolvable_iff_perfectCore_eq_bot B).mp hBs
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨b, rfl⟩ := hg s
    apply hs
    have hb1 : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hB1.le b.2))
    rw [hb1, map_one]
  obtain ⟨A₀, hA₀S, hA₀, hcA₀⟩ := hproj S₀ hS₀ hS₀ne
  have hAc : ∀ a b : ↥A₀, a * b = b * a := fun a b => hA₀.1.is_comm.comm a b
  have hA3 : ∀ a : ↥A₀, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA₀.2 a a.2)
  have hrA : A₀.subtype.range ≤ S₀ := by rw [Subgroup.range_subtype]; exact hA₀S
  have huniq : ∀ T : Subgroup (X ⧸ R), CFSG.IsComponent T → T ≠ S₀ → ⁅T, Bt⁆ = ⊥ := by
    intro T hT hTne
    by_contra hne
    obtain ⟨A, hAT, hA, hcA⟩ := hproj T hT hne
    exact Lay.false_of_two_nine hY hrk hS₀ hT (Ne.symm hTne) hAc hA3 hcA₀
      (fun a b => hA.1.is_comm.comm a b) (fun a => Subtype.ext (by simpa using hA.2 a a.2)) hcA
      A₀.subtype A₀.subtype_injective hrA A.subtype A.subtype_injective
      (by rw [Subgroup.range_subtype]; exact hAT)
  have hBtS : Bt ≤ S₀ := Lay.le_of_commute_others hY hS₀ hBtE huniq
  have hS₀c : S₀ ∈ cComp (⊤ : Subgroup (X ⧸ R)) := by
    rw [cComp_top_eq_components hY]
    exact hS₀
  rw [← image_cComp_quotient R hRs] at hS₀c
  obtain ⟨K, hK, hKS⟩ := hS₀c
  have hker : Group.IsSolvable ↥π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hRs
  have hRK : R ≤ Subgroup.normalizer (K : Set X) := by
    intro r hr
    have hKr := cComp_map_mulEquiv (MulAut.conj r) hK
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj r).surjective] at hKr
    have hr1 : π r = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hr
    have hπr : ∀ k, π (r * k * r⁻¹) = π k := by
      intro k
      rw [map_mul, map_mul, map_inv, hr1]
      group
    have heq : (K.map (MulAut.conj r).toMonoidHom).map π = K.map π := by
      rw [Subgroup.map_map]
      apply le_antisymm
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨k, hk, (hπr k).symm⟩
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨k, hk, hπr k⟩
    have := map_injOn_cComp_top π hker hKr hK heq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact this
  have hBK : B ≤ K := by
    have hBKR : B ≤ K ⊔ R := by
      have h1 : B ≤ (B.map π).comap π := Subgroup.le_comap_map π B
      refine h1.trans ?_
      rw [show K ⊔ R = (K.map π).comap π by
        rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']]
      exact Subgroup.comap_mono (hKS ▸ hBtS)
    have hKn : (K.subgroupOf (K ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hRK)
    exact (le_perfectCore_of_perfect hBKR hBp).trans
      (perfectCore_le_of_sup_solvable le_sup_left hKn rfl hRs)
  refine ⟨K, hK, hBK, eq_top_iff.mpr fun x _ => ?_⟩
  have hKx := cComp_map_mulEquiv (MulAut.conj x) hK
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective] at hKx
  have hSx : (K.map (MulAut.conj x).toMonoidHom).map π =
      S₀.map (MulAut.conj (π x)).toMonoidHom := by
    rw [← hKS, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hSxc : CFSG.IsComponent (S₀.map (MulAut.conj (π x)).toMonoidHom) := by
    have h1 := map_mem_cComp_top π (QuotientGroup.mk'_surjective R) hker hKx
    rw [hSx, cComp_top_eq_components hY] at h1
    exact h1
  have heq : S₀.map (MulAut.conj (π x)).toMonoidHom = S₀ := by
    by_contra hne
    exact Lay.false_of_two_nine hY hrk hS₀ hSxc (Ne.symm hne) hAc hA3 hcA₀ hAc hA3 hcA₀
      A₀.subtype A₀.subtype_injective hrA ((MulAut.conj (π x)).toMonoidHom.comp A₀.subtype)
      ((MulAut.conj (π x)).injective.comp A₀.subtype_injective) (by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, hA₀S a.2, rfl⟩)
  have hKeq : K.map (MulAut.conj x).toMonoidHom = K :=
    map_injOn_cComp_top π hker hKx hK (by rw [hSx, heq, hKS])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hKeq

end CFSG.Quasithin.H13.Ch4.G443J4
