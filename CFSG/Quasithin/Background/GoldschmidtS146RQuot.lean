module

public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Img

variable {G : Type} [Group G] (H J : Subgroup G) [(J.subgroupOf H).Normal]

@[expose] def imgJ (X : Subgroup G) : Subgroup (↥H ⧸ J.subgroupOf H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (J.subgroupOf H))

variable {H J}

theorem mem_imgJ {X : Subgroup G} {q : ↥H ⧸ J.subgroupOf H} :
    q ∈ imgJ H J X ↔ ∃ h : ↥H, (h : G) ∈ X ∧ (h : ↥H ⧸ J.subgroupOf H) = q := by
  simp [imgJ, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mk_mem_imgJ {X : Subgroup G} (hXH : X ≤ H) (hJH : J ≤ H) (h : ↥H) :
    (h : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J X ↔ (h : G) ∈ X ⊔ J := by
  have h1 : (h : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J X ↔
      h ∈ (imgJ H J X).comap (QuotientGroup.mk' (J.subgroupOf H)) := Iff.rfl
  rw [h1, imgJ, Subgroup.comap_map_eq, QuotientGroup.ker_mk', ← Subgroup.subgroupOf_sup hXH hJH,
    Subgroup.mem_subgroupOf]

theorem imgJ_mono {X Y : Subgroup G} (h : X ≤ Y) : imgJ H J X ≤ imgJ H J Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem imgJ_sup {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    imgJ H J (X ⊔ Y) = imgJ H J X ⊔ imgJ H J Y := by
  rw [imgJ, imgJ, imgJ, Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem imgJ_self : imgJ H J H = ⊤ := by
  rw [imgJ, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

theorem normal_imgJ {X : Subgroup G} (hX : (X.subgroupOf H).Normal) : (imgJ H J X).Normal :=
  Subgroup.Normal.map hX _ (QuotientGroup.mk'_surjective _)

theorem imgJ_map_conj {X : Subgroup G} (hXH : X ≤ H) (g : ↥H) :
    imgJ H J (X.map (MulAut.conj (g : G)).toMonoidHom) =
      (imgJ H J X).map (MulAut.conj (g : ↥H ⧸ J.subgroupOf H)).toMonoidHom := by
  ext q
  constructor
  · intro hq
    obtain ⟨h, hhX, rfl⟩ := mem_imgJ.mp hq
    obtain ⟨x, hx, hxh⟩ := hhX
    have hxH : x ∈ H := hXH hx
    refine ⟨((g : ↥H ⧸ J.subgroupOf H))⁻¹ * h * (g : ↥H ⧸ J.subgroupOf H), ?_, ?_⟩
    · refine mem_imgJ.mpr ⟨g⁻¹ * h * g, ?_, ?_⟩
      · have : (g : G)⁻¹ * (h : G) * (g : G) = x := by
          have : (h : G) = (g : G) * x * (g : G)⁻¹ := by
            simpa [MulAut.conj_apply] using hxh.symm
          rw [this]; group
        simpa using (this ▸ hx)
      · simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨h, hhX, rfl⟩ := mem_imgJ.mp hq'
    refine mem_imgJ.mpr ⟨g * h * g⁻¹, ⟨h, hhX, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · simp [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Img

section KBar

variable {G : Type} [Group G] {H J : Subgroup G} [(J.subgroupOf H).Normal]

theorem nonempty_kbar_equiv_imgJ {K : Subgroup G} (hKH : K ≤ H) (hKJ : K ⊓ J = pCoreOf 2 K) :
    Nonempty (KBar K ≃* ↥(imgJ H J K)) := by
  let f : ↥K →* ↥H ⧸ J.subgroupOf H :=
    (QuotientGroup.mk' (J.subgroupOf H)).comp (Subgroup.inclusion hKH)
  have hker : f.ker = (pCoreOf 2 K).subgroupOf K := by
    ext x
    have h1 : x ∈ f.ker ↔ (x : G) ∈ J := by
      simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    rw [h1, Subgroup.mem_subgroupOf, ← hKJ]
    simp [x.2]
  have hrange : f.range = imgJ H J K := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_imgJ.mpr ⟨Subgroup.inclusion hKH x, x.2, rfl⟩
    · intro hq
      obtain ⟨h, hh, rfl⟩ := mem_imgJ.mp hq
      exact ⟨⟨h, hh⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))⟩

theorem isSylowTwoOf_imgJ {T : Subgroup G} (hT : IsSylowTwoOf T H) (hJT : J ≤ T) :
    IsSylowTwoOf (imgJ H J T) ⊤ := by
  have hT2 : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hsurj : Function.Surjective (QuotientGroup.mk' (J.subgroupOf H)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (J.subgroupOf H)).ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.comap_mono hJT
  refine ⟨le_top, hT2.map _, ?_⟩
  change ¬ 2 ∣ (imgJ H J T).relIndex ⊤
  rw [Subgroup.relIndex_top_right, imgJ, Subgroup.index_map_eq _ hsurj hker]
  exact hT.2.2

end KBar

section Conj

variable {G : Type} [Group G]

theorem nonempty_kbar_conj (g : G) (K : Subgroup G) :
    Nonempty (KBar (K.map (MulAut.conj g).toMonoidHom) ≃* KBar K) := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  let e : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f (MulAut.conj g).injective
  have he : ((pCoreOf 2 K).subgroupOf K).map e.toMonoidHom =
      (pCoreOf 2 (K.map f)).subgroupOf (K.map f) := by
    ext x
    have hp : pCoreOf 2 (K.map f) = (pCoreOf 2 K).map f :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) K
    rw [Subgroup.mem_subgroupOf, hp]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have hzK : z ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hz
      refine ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
      exact Subtype.ext hzx
  exact ⟨(QuotientGroup.congr _ _ e he).symm⟩

end Conj

end CFSG.Quasithin.GoldS146R
