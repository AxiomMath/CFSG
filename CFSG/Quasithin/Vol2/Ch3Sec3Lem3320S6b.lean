module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S6a
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem f618SimpleType_of_rest (hIF : F6.InspF618Rest) {Q : Type} [Group Q] [Finite Q]
    {H₁ H₂ : Subgroup Q} (h : F6.IsF618CaseRestCat H₁ H₂) :
    F618SimpleType (↥(perfectCore (⊤ : Subgroup Q)) ⧸
      Subgroup.center ↥(perfectCore (⊤ : Subgroup Q))) := by
  obtain ⟨-, h345, h6, h7, h8, h9, h1011, h1213⟩ := hIF Q H₁ H₂
  have hL2 : ∀ p : ℕ, p.Prime → (p % 24 = 11 ∨ p % 24 = 13) →
      F6.IsL2 p 1 (↥(perfectCore (⊤ : Subgroup Q)) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup Q))) →
      F618SimpleType (↥(perfectCore (⊤ : Subgroup Q)) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup Q))) := fun p hp hp24 hL =>
    Or.inl (Or.inl ⟨p, 1, hp, le_rfl, by norm_num, hL, Or.inl ⟨rfl, hp24⟩⟩)
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inl h)
    exact hL2 p hp hp24 hL
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inr (Or.inl h))
    exact hL2 p hp hp24 hL
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inr (Or.inr h))
    exact hL2 p hp hp24 hL
  · rcases h6 h with hA | ⟨p, e, hp, he1, he2, hpe, hL⟩
    · exact Or.inl (Or.inr (Or.inl hA))
    · refine Or.inl (Or.inl ⟨p, e, hp, he1, he2, hL, ?_⟩)
      rcases hpe with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (h7 h))))
  · rcases h8 h with hA | ⟨p, hp, hp8, hL⟩
    · exact Or.inl (Or.inr (Or.inl hA))
    · exact Or.inl (Or.inl ⟨p, 2, hp, by norm_num, le_rfl, hL,
        Or.inr (Or.inr (Or.inr ⟨rfl, hp8⟩))⟩)
  · rcases h9 h with hA | ⟨p, hp, hp24, hL⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inl hA)))
    · exact Or.inl (Or.inl ⟨p, 2, hp, by norm_num, le_rfl, hL,
        Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))⟩)
  · exact Or.inr (h1011 (Or.inl h))
  · exact Or.inr (h1011 (Or.inr h))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (h1213 (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (h1213 (Or.inr h)))))

theorem exists_modO2Image_hom {H L : Subgroup G} (hLH : L ≤ H) :
    ∃ α : ↥L →* ↥(modO2Image H L), Function.Surjective α ∧ Group.IsSolvable ↥α.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥L ≃* ↥(L.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hLH).symm
  let α : ↥L →* ↥(modO2Image H L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (L.subgroupOf H)).comp e.toMonoidHom
  refine ⟨α, (MonoidHom.subgroupMap_surjective _ _).comp e.surjective, ?_⟩
  let ι : ↥α.ker →* ↥(CFSG.pCore 2 ↥H) :=
    (((L.subgroupOf H).subtype.comp e.toMonoidHom).comp α.ker.subtype).codRestrict _ fun k => by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
      exact (QuotientGroup.eq_one_iff _).mp h1
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg (fun x : ↥(CFSG.pCore 2 ↥H) => (x : ↥H)) hab
    exact Subtype.ext (e.injective (Subtype.ext h1))
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
  exact Group.isSolvable_of_isSolvable_injective hι

theorem exists_hom_perfectCore_quot {I : Subgroup G}
    (hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I)) :
    ∃ β : ↥(perfectCore I) →* (↥(perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)))),
      Function.Surjective β ∧ Group.IsSolvable ↥β.ker := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  set Qp := perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) with hQp
  have hP : (perfectCore (⊤ : Subgroup ↥I)).map I.subtype = perfectCore I := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQ : (perfectCore (⊤ : Subgroup ↥I)).map π = Qp := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hPI : perfectCore I ≤ I := perfectCore_le I
  have hmem : ∀ k : ↥(perfectCore I), π ⟨k, hPI k.2⟩ ∈ Qp := by
    intro k
    have hk : (k : G) ∈ (perfectCore (⊤ : Subgroup ↥I)).map I.subtype := by
      rw [hP]
      exact k.2
    obtain ⟨y, hy, hyk⟩ := hk
    rw [← hQ]
    have : y = ⟨k, hPI k.2⟩ := Subtype.ext hyk
    rw [← this]
    exact Subgroup.mem_map_of_mem π hy
  let β₀ : ↥(perfectCore I) →* ↥Qp :=
    ((π.comp (Subgroup.inclusion hPI)).codRestrict Qp fun k => hmem k)
  have hβ₀s : Function.Surjective β₀ := by
    rintro ⟨q, hq⟩
    rw [← hQ] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hy' : (y : G) ∈ perfectCore I := hP ▸ Subgroup.mem_map_of_mem I.subtype hy
    exact ⟨⟨y, hy'⟩, rfl⟩
  have hβ₀k : Group.IsSolvable ↥β₀.ker := by
    let ι : ↥β₀.ker →* ↥(CFSG.pPrimeCore 3 ↥I) :=
      ((Subgroup.inclusion hPI).comp β₀.ker.subtype).codRestrict _ fun k => by
        have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
        exact (QuotientGroup.eq_one_iff _).mp h1
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 := congrArg (fun x : ↥(CFSG.pPrimeCore 3 ↥I) => ((x : ↥I) : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hι
  let β : ↥(perfectCore I) →* (↥Qp ⧸ Subgroup.center ↥Qp) :=
    (QuotientGroup.mk' (Subgroup.center ↥Qp)).comp β₀
  refine ⟨β, (QuotientGroup.mk'_surjective _).comp hβ₀s, ?_⟩
  let γ : ↥β.ker →* ↥(Subgroup.center ↥Qp) :=
    (β₀.comp β.ker.subtype).codRestrict _ fun k => by
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥Qp)) (β₀ (k : ↥(perfectCore I))) = 1 :=
        MonoidHom.mem_ker.mp k.2
      exact (QuotientGroup.eq_one_iff _).mp h1
  let δ : ↥β₀.ker →* ↥β.ker :=
    (β₀.ker.subtype.codRestrict β.ker fun k => by
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk' (Subgroup.center ↥Qp)) (β₀ (k : ↥(perfectCore I))) = 1
      rw [MonoidHom.mem_ker.mp k.2, map_one])
  refine Group.isSolvable_of_ker_le_range δ γ fun k hk => ?_
  have h1 : β₀ k = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  exact ⟨⟨k, h1⟩, rfl⟩

omit [Finite G] in
theorem exists_rho {H N : Subgroup G} [(N.subgroupOf H).Normal] (hO : pCoreOf 2 H ≤ N) :
    ∃ ρ : (↥H ⧸ CFSG.pCore 2 ↥H) →* (↥H ⧸ N.subgroupOf H),
      ∀ h : ↥H, ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) =
        QuotientGroup.mk' (N.subgroupOf H) h := by
  have hle : CFSG.pCore 2 ↥H ≤ (N.subgroupOf H).comap (MonoidHom.id ↥H) := by
    intro x hx
    rw [Subgroup.comap_id, Subgroup.mem_subgroupOf]
    apply hO
    exact Subgroup.mem_map_of_mem _ hx
  exact ⟨QuotientGroup.map _ _ (MonoidHom.id ↥H) hle, fun h => rfl⟩

omit [Finite G] in
theorem map_modO2Image {H N L : Subgroup G} [(N.subgroupOf H).Normal]
    {ρ : (↥H ⧸ CFSG.pCore 2 ↥H) →* (↥H ⧸ N.subgroupOf H)}
    (hρ : ∀ h : ↥H, ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) =
      QuotientGroup.mk' (N.subgroupOf H) h) :
    (modO2Image H L).map ρ = star H N L := by
  unfold modO2Image star
  rw [Subgroup.map_map]
  congr 1
  ext h
  exact hρ h

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem star_perfectCore_eq (hIF : F6.InspF618Rest) (h312 : Vol2Native.A312ForSQTKCat)
    (hI : InspA312F618) (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G))
    (hrest : F6.IsF618CaseRestCat (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
      F6.IsF618CaseRestCat (plus (gZero X T g) (conjByElt g (X ⊔ T)))
        (plus (gZero X T g) (X ⊔ T)))
    (hK₀ : perfectCore (gZero X T g) ∈ cComp (gZero X T g)) {K : Subgroup G}
    (hK : K ∈ cComp (X ⊔ T ⊔ D)) (hK₀K : perfectCore (gZero X T g) ≤ K)
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = star (X ⊔ T ⊔ D) B₀ K := by
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  have hTI : T ≤ gZero X T g := le_sup_right.trans le_sup_left
  have hK₀B : perfectCore (gZero X T g) ≤ X ⊔ T ⊔ D := (perfectCore_le _).trans (gZero_le hg)
  have hK₀L : perfectCore (gZero X T g) ∈ lFamily T := cComp_subset_lFamily hTI hK₀
  have hKB : K ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK
  have hlist := Vol2Native.lemma_1_2_4_list hKc h312 H.hB.2 H.isSylowTwoOf_B hK₀B hK₀L hK hK₀K
  have hgX := H.not_mem_normalizer_X hg hgR
  have hs := (H.isGoldschmidtTripleIn hg hgX).isSolvable_pPrimeCore
  have hq : CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup
      (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))) := by
    rcases hrest with h | h
    · exact (hIF _ _ _).1 h
    · exact (hIF _ _ _).1 h
  have hW : F618SimpleType (↥(perfectCore (⊤ : Subgroup
      (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup
          (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))))) := by
    rcases hrest with h | h
    · exact f618SimpleType_of_rest hIF h
    · exact f618SimpleType_of_rest hIF h
  obtain ⟨α, hαs, hαk⟩ := exists_modO2Image_hom (H := X ⊔ T ⊔ D) hK₀B
  obtain ⟨β, hβs, hβk⟩ := exists_hom_perfectCore_quot hs
  have hle : modO2Image (X ⊔ T ⊔ D) (perfectCore (gZero X T g)) ≤ modO2Image (X ⊔ T ⊔ D) K :=
    Subgroup.map_mono (Subgroup.comap_mono hK₀K)
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  obtain ⟨ρ, hρ⟩ := exists_rho (H := X ⊔ T ⊔ D) (N := B₀)
    ((le_of_eq hT₀.symm).trans inf_le_right)
  have hρK := map_modO2Image (L := K) hρ
  have hρK₀ := map_modO2Image (L := perfectCore (gZero X T g)) hρ
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hK hBK hKB₀
  have hsol : (solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ = ⊥ := by
    have hle' : (solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ ≤ star (X ⊔ T ⊔ D) B₀ K := by
      rw [← hρK]
      exact Subgroup.map_mono (solvRad_le _)
    set N' := ((solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ).subgroupOf
      (star (X ⊔ T ⊔ D) B₀ K) with hN'
    have hN'n : N'.Normal := by
      refine ⟨fun n hn y => ?_⟩
      rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨s, hs', hsn⟩ := hn
      have hy : (y : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ∈
          (modO2Image (X ⊔ T ⊔ D) K).map ρ := by
        rw [hρK]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨x * s * x⁻¹, ?_, ?_⟩
      · have hxN : x ∈ Subgroup.normalizer ((modO2Image (X ⊔ T ⊔ D) K : Subgroup _) :
            Set (↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D))) := Subgroup.le_normalizer hx
        exact conj_mem_solvRad hxN hs'
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hxy, hsn]
    have hs'' : Group.IsSolvable ↥((solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ) := by
      have := solvRad_isSolvable (modO2Image (X ⊔ T ⊔ D) K)
      exact Group.isSolvable_of_surjective
        (ρ.subgroupMap_surjective (solvRad (modO2Image (X ⊔ T ⊔ D) K)))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h1 | h1
    · rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hle' hz⟩ : ↥(star (X ⊔ T ⊔ D) B₀ K)) ∈ N' := hz
      rw [h1, Subgroup.mem_bot] at hz'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz')
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hst : Group.IsSolvable ↥(star (X ⊔ T ⊔ D) B₀ K) := by
        have h2 : star (X ⊔ T ⊔ D) B₀ K ≤ (solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ := by
          intro z hz
          have : (⟨z, hz⟩ : ↥(star (X ⊔ T ⊔ D) B₀ K)) ∈ N' := h1 ▸ Subgroup.mem_top _
          exact this
        exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h2)
      exact (IsSimpleGroup.comm_iff_isSolvable.mpr hst) a b
  rcases hI _ _ _ hle hlist ⟨↥(perfectCore (gZero X T g)), inferInstance, _, inferInstance,
      α, β, hαs, hαk, hβs, hβk, hq.2.1, hW⟩ with ha | hb
  ·
    have h1 := congrArg (Subgroup.map ρ) ha
    rw [Subgroup.map_sup, hsol, sup_bot_eq, hρK, hρK₀] at h1
    exact h1
  ·
    exfalso
    apply H.not_autOddNormCent hA hB hK hBK hKB₀
    let f : ↥(modO2Image (X ⊔ T ⊔ D) K) →* ↥(star (X ⊔ T ⊔ D) B₀ K) :=
      (MulEquiv.subgroupCongr hρK).toMonoidHom.comp (ρ.subgroupMap _)
    have hfs : Function.Surjective f :=
      (MulEquiv.subgroupCongr hρK).surjective.comp (MonoidHom.subgroupMap_surjective _ _)
    refine hb _ f hfs ?_
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx1 : ρ (x : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) = 1 :=
        congrArg Subtype.val hx
      obtain ⟨k, hk, hkx⟩ := x.2
      rw [← hkx, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hx1
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hks : (k : G) ∈ solvRad K := by
        rw [← H.inf_B₀_eq_solvRad hB (H.le_commutator_sup hA hB) hK hBK hKB₀]
        exact ⟨hkK, hx1⟩
      rw [← hkx]
      refine le_solvRad (Subgroup.map_mono (Subgroup.comap_mono (solvRad_le K))) ?_ ?_
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hks))
      · refine ⟨fun n hn y => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        obtain ⟨s, hs', hsn⟩ := hn
        obtain ⟨k', hk', hk'y⟩ := y.2
        refine ⟨k' * s * k'⁻¹, ?_, ?_⟩
        · show ((k' * s * k'⁻¹ : ↥(X ⊔ T ⊔ D)) : G) ∈ solvRad K
          exact conj_mem_solvRad (Subgroup.le_normalizer (show (k' : G) ∈ K from hk'))
            (show (s : G) ∈ solvRad K from hs')
        · simp only [map_mul, map_inv, hk'y, hsn, Subgroup.coe_mul, Subgroup.coe_inv]
      · have := solvRad_isSolvable K
        have h2 : Group.IsSolvable ↥((solvRad K).subgroupOf (X ⊔ T ⊔ D)) :=
          Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.subgroupOfEquivOfLe ((solvRad_le K).trans hKB)).toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe ((solvRad_le K).trans hKB)).injective
        exact Group.isSolvable_of_surjective
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D))).subgroupMap_surjective
            ((solvRad K).subgroupOf (X ⊔ T ⊔ D)))
    · intro hx
      have h1 : ρ (x : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ∈
          (solvRad (modO2Image (X ⊔ T ⊔ D) K)).map ρ := Subgroup.mem_map_of_mem ρ hx
      rw [hsol, Subgroup.mem_bot] at h1
      exact Subtype.ext h1

end Hyp3320

end S3320

end CFSG.Quasithin.H13
