module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F1Amalgam
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.AmalTransport

open CFSG.Open

section Map

variable {G E : Type*} [Group G] [Group E]

theorem isElemAbelian_map (f : G →* E) {A : Subgroup G} (h : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map h _

theorem isElemAbelian_of_map_injective {f : G →* E} (hf : Function.Injective f) {A : Subgroup G}
    (h : IsElemAbelian 2 (A.map f)) : IsElemAbelian 2 A := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have := hc.is_comm.comm (⟨f x, x, x.2, rfl⟩ : A.map f) ⟨f y, y, y.2, rfl⟩
    apply Subtype.ext
    apply hf
    simpa using congrArg Subtype.val this
  · apply hf
    rw [map_pow, map_one]
    exact hp (f x) ⟨x, hx, rfl⟩

theorem isElemAbelian_mono {A B : Subgroup G} (hAB : A ≤ B) (h : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono h hAB

theorem thompsonJ_map_of_injective (f : G →* E) (hf : Function.Injective f) (H : Subgroup G) :
    thompsonJ (H.map f) = (thompsonJ H).map f := by
  unfold thompsonJ
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun A' => iSup_le fun hA' => ?_
    obtain ⟨hA'le, hA'el, hA'max⟩ := hA'
    have hA'r : A' ≤ f.range := hA'le.trans (Subgroup.map_le_range f H)
    have hAH : A'.comap f ≤ H := by
      intro x hx
      obtain ⟨h, hh, hfx⟩ := hA'le hx
      rw [← hf hfx]
      exact hh
    have hmap : (A'.comap f).map f = A' := Subgroup.map_comap_eq_self hA'r
    have hmax : IsMaxElemAbelian H (A'.comap f) := by
      refine ⟨hAH, isElemAbelian_of_map_injective hf (by rw [hmap]; exact hA'el),
        fun B hBH hB => ?_⟩
      have h1 := hA'max (B.map f) (Subgroup.map_mono hBH) (isElemAbelian_map f hB)
      have h2 : Nat.card A' = Nat.card (A'.comap f) := by
        rw [← Subgroup.card_map_of_injective hf (K := A'.comap f), hmap]
      rw [Subgroup.card_map_of_injective hf, h2] at h1
      exact h1
    exact le_iSup₂_of_le (A'.comap f) hmax (by rw [hmap])
  · refine iSup_le fun A => iSup_le fun hA => ?_
    obtain ⟨hAH, hAel, hAmax⟩ := hA
    have hmax : IsMaxElemAbelian (H.map f) (A.map f) := by
      refine ⟨Subgroup.map_mono hAH, isElemAbelian_map f hAel, fun B' hB'H hB' => ?_⟩
      have hB'r : B' ≤ f.range := hB'H.trans (Subgroup.map_le_range f H)
      have hBH : B'.comap f ≤ H := by
        intro x hx
        obtain ⟨h, hh, hfx⟩ := hB'H hx
        rw [← hf hfx]
        exact hh
      have hmap : (B'.comap f).map f = B' := Subgroup.map_comap_eq_self hB'r
      have h1 := hAmax (B'.comap f) hBH
        (isElemAbelian_of_map_injective hf (by rw [hmap]; exact hB'))
      rw [← hmap, Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]
      exact h1
    exact le_iSup₂_of_le (A.map f) hmax le_rfl

end Map

section Amalgam

variable {G E : Type} [Group G] [Group E]

@[expose] def AmalFusion (P₁ P₂ : Subgroup G) : G → G → Prop :=
  Relation.ReflTransGen fun x y => x ∈ P₁ ⊓ P₂ ∧ y ∈ P₁ ⊓ P₂ ∧
    ((∃ h ∈ P₁, h * x * h⁻¹ = y) ∨ ∃ h ∈ P₂, h * x * h⁻¹ = y)

@[expose] def AutConcl (P₁ P₂ : Subgroup G) : Prop :=
  ∃ R : Subgroup G, R ≤ P₁ ⊓ P₂ ∧ R.relIndex (P₁ ⊓ P₂) = 2 ∧
    IsElemAbelian 2 (thompsonJ (P₁ ⊓ P₂)) ∧
    P₂ ≤ Subgroup.normalizer (thompsonJ (P₁ ⊓ P₂) : Set G) ∧
    (∃ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R) ∧
    (∀ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R → ∀ y ∈ P₂, y * j * y⁻¹ ∉ R) ∧
    ∀ r ∈ R, r ^ 2 = 1 → ∃ j ∈ thompsonJ (P₁ ⊓ P₂) ⊓ R, AmalFusion P₁ P₂ r j

theorem thompsonJ_le {H : Subgroup E} : thompsonJ H ≤ H :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem AutConcl.of_iso {P₁ P₂ : Subgroup G} {K₁ K₂ : Subgroup E}
    (iso : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups K₁ K₂))
    (h : AutConcl K₁ K₂) : AutConcl P₁ P₂ := by
  obtain ⟨R, hRK, hRidx, hel, hnorm, ⟨j₀, hj₀J, hj₀R⟩, hinv, hfus⟩ := h
  let θ : ↥(P₁ ⊓ P₂) ≃* ↥(K₁ ⊓ K₂) := iso.φ12
  let φ1 : ↥P₁ ≃* ↥K₁ := iso.φ1
  let φ2 : ↥P₂ ≃* ↥K₂ := iso.φ2
  have hθ1 : ∀ g : ↥(P₁ ⊓ P₂), ((φ1 ⟨g.1, g.2.1⟩ : ↥K₁) : E) = ((θ g : ↥(K₁ ⊓ K₂)) : E) :=
    fun g => (congrArg (fun z : ↥K₁ => (z : E)) (iso.comm1 g)).symm
  have hθ2 : ∀ g : ↥(P₁ ⊓ P₂), ((φ2 ⟨g.1, g.2.2⟩ : ↥K₂) : E) = ((θ g : ↥(K₁ ⊓ K₂)) : E) :=
    fun g => (congrArg (fun z : ↥K₂ => (z : E)) (iso.comm2 g)).symm
  let ι : ↥(P₁ ⊓ P₂) →* E := (K₁ ⊓ K₂).subtype.comp θ.toMonoidHom
  have hι : Function.Injective ι := (K₁ ⊓ K₂).subtype_injective.comp θ.injective
  have hιθ : ∀ g, ι g = ((θ g : ↥(K₁ ⊓ K₂)) : E) := fun g => rfl
  have hsurj : ∀ w : E, w ∈ K₁ ⊓ K₂ → ∃ g : ↥(P₁ ⊓ P₂), ι g = w := by
    intro w hw
    obtain ⟨g, hg⟩ := θ.surjective ⟨w, hw⟩
    exact ⟨g, by rw [hιθ, hg]⟩
  have hJle : thompsonJ (K₁ ⊓ K₂) ≤ K₁ ⊓ K₂ := thompsonJ_le
  have hJeq : thompsonJ (P₁ ⊓ P₂) = ((thompsonJ (K₁ ⊓ K₂)).comap ι).map (P₁ ⊓ P₂).subtype := by
    have e1 : thompsonJ (P₁ ⊓ P₂) = (thompsonJ (⊤ : Subgroup ↥(P₁ ⊓ P₂))).map (P₁ ⊓ P₂).subtype := by
      rw [← thompsonJ_map_of_injective _ (P₁ ⊓ P₂).subtype_injective, Subgroup.map_top,
        Subgroup.range_subtype]
    have e2 : thompsonJ (K₁ ⊓ K₂) = (thompsonJ (⊤ : Subgroup ↥(K₁ ⊓ K₂))).map (K₁ ⊓ K₂).subtype := by
      rw [← thompsonJ_map_of_injective _ (K₁ ⊓ K₂).subtype_injective, Subgroup.map_top,
        Subgroup.range_subtype]
    have e3 : thompsonJ (⊤ : Subgroup ↥(K₁ ⊓ K₂)) =
        (thompsonJ (⊤ : Subgroup ↥(P₁ ⊓ P₂))).map θ.toMonoidHom := by
      rw [← thompsonJ_map_of_injective _ θ.injective, Subgroup.map_top,
        MonoidHom.range_eq_top.2 θ.surjective]
    have e4 : (thompsonJ (K₁ ⊓ K₂)).comap ι = thompsonJ (⊤ : Subgroup ↥(P₁ ⊓ P₂)) := by
      have : ι = (K₁ ⊓ K₂).subtype.comp θ.toMonoidHom := rfl
      rw [this, ← Subgroup.comap_comap, e2, Subgroup.comap_map_eq_self_of_injective
        (K₁ ⊓ K₂).subtype_injective, e3, Subgroup.comap_map_eq_self_of_injective θ.injective]
    rw [e4]
    exact e1
  have mem_pb : ∀ (X : Subgroup E) (g : G), g ∈ (X.comap ι).map (P₁ ⊓ P₂).subtype ↔
      ∃ hg : g ∈ P₁ ⊓ P₂, ι ⟨g, hg⟩ ∈ X := by
    intro X g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, hx⟩
      exact ⟨⟨g, hg⟩, hx, rfl⟩
  have hconj : ∀ (y : G) (hy : y ∈ P₂) (j : ↥(P₁ ⊓ P₂)), ι j ∈ thompsonJ (K₁ ⊓ K₂) →
      ∃ j' : ↥(P₁ ⊓ P₂), (j' : G) = y * j * y⁻¹ ∧
        ι j' = ((φ2 ⟨y, hy⟩ : ↥K₂) : E) * ι j * ((φ2 ⟨y, hy⟩ : ↥K₂) : E)⁻¹ := by
    intro y hy j hj
    have hw : ((φ2 ⟨y, hy⟩ : ↥K₂) : E) * ι j * ((φ2 ⟨y, hy⟩ : ↥K₂) : E)⁻¹ ∈
        thompsonJ (K₁ ⊓ K₂) :=
      (Subgroup.mem_normalizer_iff.1 (hnorm (φ2 ⟨y, hy⟩).2) (ι j)).1 hj
    obtain ⟨g', hg'⟩ := hsurj _ (hJle hw)
    have h2 : (φ2 ⟨g'.1, g'.2.2⟩ : ↥K₂) =
        φ2 (⟨y, hy⟩ * ⟨j.1, j.2.2⟩ * ⟨y, hy⟩⁻¹) := by
      apply Subtype.ext
      have e1 := hθ2 g'
      have e3 : ((φ2 ⟨j.1, j.2.2⟩ : ↥K₂) : E) = ι j := (hθ2 j).trans (hιθ j).symm
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e1, e3]
      exact (hιθ g').symm.trans hg'
    have h3 := φ2.injective h2
    refine ⟨g', ?_, hg'⟩
    have := congrArg Subtype.val h3
    simpa using this
  refine ⟨(R.comap ι).map (P₁ ⊓ P₂).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e1 : (((R.comap ι).map (P₁ ⊓ P₂).subtype).subgroupOf (P₁ ⊓ P₂)) = R.comap ι :=
      Subgroup.comap_map_eq_self_of_injective (P₁ ⊓ P₂).subtype_injective _
    have e2 : R.comap ι = (R.subgroupOf (K₁ ⊓ K₂)).comap θ.toMonoidHom := by
      rw [Subgroup.subgroupOf, Subgroup.comap_comap]
    unfold Subgroup.relIndex
    rw [e1, e2, Subgroup.index_comap_of_surjective _ θ.surjective]
    exact hRidx
  ·
    rw [hJeq]
    refine isElemAbelian_map _ (isElemAbelian_of_map_injective hι (isElemAbelian_mono ?_ hel))
    exact Subgroup.map_comap_le _ _
  ·
    intro y hy
    have key : ∀ y ∈ P₂, ∀ j ∈ thompsonJ (P₁ ⊓ P₂), y * j * y⁻¹ ∈ thompsonJ (P₁ ⊓ P₂) := by
      intro y hy j hj
      rw [hJeq, mem_pb] at hj ⊢
      obtain ⟨hjH, hjJ⟩ := hj
      obtain ⟨j', hj'1, hj'2⟩ := hconj y hy ⟨j, hjH⟩ hjJ
      have hmem : y * j * y⁻¹ ∈ P₁ ⊓ P₂ := by rw [← hj'1]; exact j'.2
      refine ⟨hmem, ?_⟩
      have : (⟨y * j * y⁻¹, hmem⟩ : ↥(P₁ ⊓ P₂)) = j' := Subtype.ext hj'1.symm
      rw [this, hj'2]
      exact (Subgroup.mem_normalizer_iff.1 (hnorm (φ2 ⟨y, hy⟩).2) (ι ⟨j, hjH⟩)).1 hjJ
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => key y hy j hj, fun hj => ?_⟩
    have := key y⁻¹ (P₂.inv_mem hy) _ hj
    simpa [mul_assoc] using this
  ·
    obtain ⟨g, hg⟩ := hsurj j₀ (hJle hj₀J)
    refine ⟨g.1, ?_, ?_⟩
    · rw [hJeq, mem_pb]
      exact ⟨g.2, by simpa [hg] using hj₀J⟩
    · rw [mem_pb]
      rintro ⟨hg', hR⟩
      exact hj₀R (by simpa [hg] using hR)
  ·
    intro j hj hjR y hy
    rw [hJeq, mem_pb] at hj
    obtain ⟨hjH, hjJ⟩ := hj
    obtain ⟨j', hj'1, hj'2⟩ := hconj y hy ⟨j, hjH⟩ hjJ
    have hjR' : ι ⟨j, hjH⟩ ∉ R := fun hR => hjR ((mem_pb R j).2 ⟨hjH, hR⟩)
    have h1 := hinv _ hjJ hjR' _ (φ2 ⟨y, hy⟩).2
    rw [mem_pb]
    rintro ⟨hmem, hR⟩
    have : (⟨y * j * y⁻¹, hmem⟩ : ↥(P₁ ⊓ P₂)) = j' := Subtype.ext hj'1.symm
    rw [this, hj'2] at hR
    exact h1 hR
  ·
    intro r hr hr2
    rw [mem_pb] at hr
    obtain ⟨hrH, hrR⟩ := hr
    have hr2' : (ι ⟨r, hrH⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨r, hrH⟩ : ↥(P₁ ⊓ P₂)) ^ 2 = 1 := Subtype.ext hr2
      rw [this, map_one]
    obtain ⟨j', hj'JR, hj'f⟩ := hfus _ hrR hr2'
    have pull : ∀ (x' y' : E), Relation.ReflTransGen (fun x y => x ∈ K₁ ⊓ K₂ ∧ y ∈ K₁ ⊓ K₂ ∧
        ((∃ h ∈ K₁, h * x * h⁻¹ = y) ∨ ∃ h ∈ K₂, h * x * h⁻¹ = y))
        x' y' → ∀ x : ↥(P₁ ⊓ P₂), ι x = x' → ∃ y : ↥(P₁ ⊓ P₂), ι y = y' ∧
          AmalFusion P₁ P₂ x.1 y.1 := by
      intro x' y' hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl => exact fun x hx => ⟨x, hx, Relation.ReflTransGen.refl⟩
      | @head x' z' hxz _ ih =>
        intro x hx
        obtain ⟨-, hz'K, hcase⟩ := hxz
        obtain ⟨g', hg'⟩ := hsurj z' hz'K
        have hstep : x.1 ∈ P₁ ⊓ P₂ ∧ g'.1 ∈ P₁ ⊓ P₂ ∧
            ((∃ h ∈ P₁, h * x.1 * h⁻¹ = g'.1) ∨ ∃ h ∈ P₂, h * x.1 * h⁻¹ = g'.1) := by
          refine ⟨x.2, g'.2, ?_⟩
          rcases hcase with ⟨h', hh', hconj1⟩ | ⟨h', hh', hconj1⟩
          · left
            refine ⟨(φ1.symm ⟨h', hh'⟩ : ↥P₁).1, (φ1.symm ⟨h', hh'⟩).2, ?_⟩
            have h2 : (φ1 ⟨g'.1, g'.2.1⟩ : ↥K₁) =
                φ1 (φ1.symm ⟨h', hh'⟩ * ⟨x.1, x.2.1⟩ * (φ1.symm ⟨h', hh'⟩)⁻¹) := by
              apply Subtype.ext
              rw [hθ1 g', ← hιθ, hg', ← hconj1, ← hx, hιθ, ← hθ1 x]
              simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
                Subgroup.coe_inv]
            have := congrArg Subtype.val (φ1.injective h2)
            simpa using this.symm
          · right
            refine ⟨(φ2.symm ⟨h', hh'⟩ : ↥P₂).1, (φ2.symm ⟨h', hh'⟩).2, ?_⟩
            have h2 : (φ2 ⟨g'.1, g'.2.2⟩ : ↥K₂) =
                φ2 (φ2.symm ⟨h', hh'⟩ * ⟨x.1, x.2.2⟩ * (φ2.symm ⟨h', hh'⟩)⁻¹) := by
              apply Subtype.ext
              rw [hθ2 g', ← hιθ, hg', ← hconj1, ← hx, hιθ, ← hθ2 x]
              simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
                Subgroup.coe_inv]
            have := congrArg Subtype.val (φ2.injective h2)
            simpa using this.symm
        obtain ⟨y, hy1, hy2⟩ := ih g' hg'
        exact ⟨y, hy1, Relation.ReflTransGen.head hstep hy2⟩
    obtain ⟨y, hy1, hy2⟩ := pull _ _ hj'f ⟨r, hrH⟩ rfl
    refine ⟨y.1, ?_, hy2⟩
    obtain ⟨hjJ, hjR⟩ := Subgroup.mem_inf.1 hj'JR
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hJeq, mem_pb]
      exact ⟨y.2, by rw [hy1]; exact hjJ⟩
    · rw [mem_pb]
      exact ⟨y.2, by rw [hy1]; exact hjR⟩

end Amalgam

section IsoMap

variable {G E E' : Type} [Group G] [Group E] [Group E']

noncomputable def isoMap {P₁ P₂ : Subgroup G} {M₁ M₂ : Subgroup E}
    (iso : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (ψ : E ≃* E') :
    (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso
      (RankTwoAmalgam.ofSubgroups (M₁.map ψ.toMonoidHom) (M₂.map ψ.toMonoidHom)) where
  φ1 := iso.φ1.trans (M₁.equivMapOfInjective ψ.toMonoidHom ψ.injective)
  φ12 := iso.φ12.trans (((M₁ ⊓ M₂).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf M₁ M₂ ψ.toMonoidHom ψ.injective)))
  φ2 := iso.φ2.trans (M₂.equivMapOfInjective ψ.toMonoidHom ψ.injective)
  comm1 g := by
    apply Subtype.ext
    have h := congrArg (fun z : ↥M₁ => ψ (z : E)) (iso.comm1 g)
    exact h
  comm2 g := by
    apply Subtype.ext
    have h := congrArg (fun z : ↥M₂ => ψ (z : E)) (iso.comm2 g)
    exact h

end IsoMap

end CFSG.Quasithin.AmalTransport
