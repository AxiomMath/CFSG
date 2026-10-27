module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
public import CFSG.LocalAnalysis.StandardType.GGA2Conj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.PhanDn.QTwo

section Transport

variable {G : Type} [Group G] [Finite G]

private theorem p9uLE_commute_of_sq_eq_one {H : Type} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h : (a * b) ^ 2 = 1) : a * b = b * a := by
  have ha' : a * a = 1 := by rwa [← pow_two]
  have hb' : b * b = 1 := by rwa [← pow_two]
  have h1 : (a * b) * (a * b) = 1 := by rwa [← pow_two]
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_left hb', inv_eq_of_mul_eq_one_right ha']

private theorem p9uLE_conj_coe {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (u v : M.Group) :
    ((e u : ↥A) : MulAut ↥Bs) * ((e v : ↥A) : MulAut ↥Bs) * ((e u : ↥A) : MulAut ↥Bs)⁻¹ =
      ((e (u * v * u⁻¹) : ↥A) : MulAut ↥Bs) := by
  rw [map_mul, map_mul, map_inv]
  rfl

private theorem p9uLE_pow_three_coe {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (t t' : M.Group)
    (h : (((e t : ↥A) : MulAut ↥Bs) * ((e t' : ↥A) : MulAut ↥Bs)) ^ 3 = 1) :
    (t * t') ^ 3 = 1 := by
  have hinj : Function.Injective (A.subtype.comp e.toMonoidHom) :=
    fun x y hxy => e.injective (A.subtype_injective hxy)
  have hφ : (A.subtype.comp e.toMonoidHom) (t * t') =
      ((e t : ↥A) : MulAut ↥Bs) * ((e t' : ↥A) : MulAut ↥Bs) := by
    rw [map_mul]
    rfl
  refine hinj ?_
  rw [map_pow, map_one, hφ, h]

theorem qtwoDL1_exists_conj_rankTwo {p : ℕ} {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hedge : ∃ i j : ι, M.M i j = 3) {r₀ r₀' r r' : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e)
    (hr₀' : r₀' ∈ ggCoxRefl M e)
    (hne₀ : r₀ * r₀' ≠ r₀' * r₀) (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e)
    (hne : r * r' ≠ r' * r) :
    ∃ g : G, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (ggRankTwo Bs r₀ r₀').map (MulAut.conj g).toMonoidHom = ggRankTwo Bs r r' := by
  have hrefl₀ : GGIsReflection p r₀ := ggCoxRefl_isReflection hpres.2 hr₀
  have hrefl₀' : GGIsReflection p r₀' := ggCoxRefl_isReflection hpres.2 hr₀'
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hr
  have hrefl' : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hr'
  have hordle₀ : (r₀ * r₀') ^ 2 = 1 ∨ (r₀ * r₀') ^ 3 = 1 :=
    ggCoxRefl_mul_orderOf_le_three hpres.1 h3 hr₀ hr₀'
  have hordle : (r * r') ^ 2 = 1 ∨ (r * r') ^ 3 = 1 :=
    ggCoxRefl_mul_orderOf_le_three hpres.1 h3 hr hr'
  obtain ⟨w₀, u₀, rfl⟩ := hr₀
  obtain ⟨w₀', u₀', rfl⟩ := hr₀'
  obtain ⟨w, u, rfl⟩ := hr
  obtain ⟨w', u', rfl⟩ := hr'
  have hne_t : (w₀ * M.simple u₀ * w₀⁻¹) ≠ (w₀' * M.simple u₀' * w₀'⁻¹) := by
    intro h
    exact hne₀ (by rw [h])
  have hne_t' : (w * M.simple u * w⁻¹) ≠ (w' * M.simple u' * w'⁻¹) := by
    intro h
    exact hne (by rw [h])
  have hord_t : ((w₀ * M.simple u₀ * w₀⁻¹) * (w₀' * M.simple u₀' * w₀'⁻¹)) ^ 3 = 1 := by
    rcases hordle₀ with h2 | h3
    · exact absurd (p9uLE_commute_of_sq_eq_one hrefl₀.1 hrefl₀'.1 h2) hne₀
    · exact p9uLE_pow_three_coe e (w₀ * M.simple u₀ * w₀⁻¹) (w₀' * M.simple u₀' * w₀'⁻¹) h3
  have hord_t' : ((w * M.simple u * w⁻¹) * (w' * M.simple u' * w'⁻¹)) ^ 3 = 1 := by
    rcases hordle with h2 | h3
    · exact absurd (p9uLE_commute_of_sq_eq_one hrefl.1 hrefl'.1 h2) hne
    · exact p9uLE_pow_three_coe e (w * M.simple u * w⁻¹) (w' * M.simple u' * w'⁻¹) h3
  obtain ⟨a₀, b₀, hab₀⟩ := hedge
  obtain ⟨w₁, hw₁, hw₁'⟩ :=
    ggA2_conj hpres.1 h3 ⟨w₀, u₀, rfl⟩ ⟨w₀', u₀', rfl⟩ hne_t hord_t hab₀
  obtain ⟨w₂, hw₂, hw₂'⟩ :=
    ggA2_conj hpres.1 h3 ⟨w, u, rfl⟩ ⟨w', u', rfl⟩ hne_t' hord_t' hab₀
  let σ : M.Group := w₂ * w₁⁻¹
  have hσ₀ : σ * (w₀ * M.simple u₀ * w₀⁻¹) * σ⁻¹ = w * M.simple u * w⁻¹ := by
    rw [← hw₁, ← hw₂]
    show (w₂ * w₁⁻¹) * (w₁ * M.simple a₀ * w₁⁻¹) * (w₂ * w₁⁻¹)⁻¹ =
      w₂ * M.simple a₀ * w₂⁻¹
    group
  have hσ₀' : σ * (w₀' * M.simple u₀' * w₀'⁻¹) * σ⁻¹ = w' * M.simple u' * w'⁻¹ := by
    rw [← hw₁', ← hw₂']
    show (w₂ * w₁⁻¹) * (w₁ * M.simple b₀ * w₁⁻¹) * (w₂ * w₁⁻¹)⁻¹ =
      w₂ * M.simple b₀ * w₂⁻¹
    group
  have ha₀ : ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e (w₀ * M.simple u₀ * w₀⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ =
      ((e (w * M.simple u * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    calc ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e (w₀ * M.simple u₀ * w₀⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹
        = ((e (σ * (w₀ * M.simple u₀ * w₀⁻¹) * σ⁻¹) :
              ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := p9uLE_conj_coe e σ _
      _ = ((e (w * M.simple u * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
          rw [hσ₀]
  have ha₀' : ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e (w₀' * M.simple u₀' * w₀'⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ =
      ((e (w' * M.simple u' * w'⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    calc ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e (w₀' * M.simple u₀' * w₀'⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹
        = ((e (σ * (w₀' * M.simple u₀' * w₀'⁻¹) * σ⁻¹) :
              ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := p9uLE_conj_coe e σ _
      _ = ((e (w' * M.simple u' * w'⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
          rw [hσ₀']
  have ha : ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizerJoin L Bs 𝒦 :=
    (e σ).2
  obtain ⟨g, -, hgN, -, hgmap⟩ :=
    ggRankOne_conj_of_mem_ggAutomizerJoin
      (a := ((e σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ha
      ((e (w₀ * M.simple u₀ * w₀⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  refine ⟨g, hgN, ?_⟩
  rw [← ha₀, ← ha₀']
  exact hgmap ((e (w₀' * M.simple u₀' * w₀'⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)

theorem qtwoDL1_card_rankTwo_eq {p : ℕ} {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hedge : ∃ i j : ι, M.M i j = 3) {r₀ r₀' r r' : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e)
    (hr₀' : r₀' ∈ ggCoxRefl M e)
    (hne₀ : r₀ * r₀' ≠ r₀' * r₀) (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e)
    (hne : r * r' ≠ r' * r) :
    Nat.card ↥(ggRankTwo Bs r r') = Nat.card ↥(ggRankTwo Bs r₀ r₀') := by
  obtain ⟨g, -, hgmap⟩ :=
    qtwoDL1_exists_conj_rankTwo hpres h3 hedge hr₀ hr₀' hne₀ hr hr' hne
  rw [← hgmap]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem qtwoDL1_rankTwoIn_le_rankTwo (X Bs : Subgroup G) (r r' : MulAut ↥Bs) :
    ggRankTwoIn X Bs r r' ≤ ggRankTwo Bs r r' := by
  unfold ggRankTwoIn ggRankTwo
  exact LinFusion.ggOTwoPrime_mono inf_le_right

theorem qtwoDL1_rankTwo_eq_of_card_le {X Bs : Subgroup G} {r r' : MulAut ↥Bs}
    (h : Nat.card ↥(ggRankTwo Bs r r') ≤ Nat.card ↥(ggRankTwoIn X Bs r r')) :
    ggRankTwo Bs r r' = ggRankTwoIn X Bs r r' := by
  exact (Subgroup.eq_of_le_of_card_ge (qtwoDL1_rankTwoIn_le_rankTwo X Bs r r') h).symm

end Transport

section Inputs


@[expose] def GGQTwoDL1EdgeBaseInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∃ r₀ ∈ ggCoxRefl M e, ∃ r₀' ∈ ggCoxRefl M e, r₀ * r₀' ≠ r₀' * r₀ ∧
          Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216

@[expose] def GGQTwoDL1EdgeBaseInput : Prop :=
  GGQTwoDL1EdgeBaseInputOn fun m => 7 ≤ m

@[expose] def GGQTwoDL1EdgeLocalInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs,
            r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → 216 ≤ Nat.card ↥(ggRankTwoIn X Bs r r')

@[expose] def GGQTwoDL1EdgeLocalInput : Prop :=
  GGQTwoDL1EdgeLocalInputOn fun m => 7 ≤ m

theorem ggQTwoEdgeAmbientInputOn_of_base_local {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hB : GGQTwoDL1EdgeBaseInputOn R) (hLoc : GGQTwoDL1EdgeLocalInputOn R) :
    GGQTwoEdgeAmbientInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX r hrX hrC r' hr'X hr'C hne
  have hm4 := hR m hm
  obtain ⟨r₀, hr₀C, r₀', hr₀'C, hne₀, hcard₀⟩ :=
    hB G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hloc := hLoc G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX r hrX hrC r' hr'X hr'C hne
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    rcases ggCoxeterMatrixD_two_or_three (e'.symm i) (e'.symm j)
      (fun h => hij (e'.symm.injective h)) with h | h <;> omega
  have hedge : ∃ i j : ι, M.M i j = 3 := by
    obtain ⟨j₀, hj₀⟩ := ggCoxeterMatrixD_exists_three (m := m) hm4 ⟨0, by omega⟩
    exact ⟨e' ⟨0, by omega⟩, e' j₀, by
      rw [hM, CoxeterMatrix.reindex_apply]
      simpa using hj₀⟩
  have hcard := qtwoDL1_card_rankTwo_eq hcfg.2.2.2.1 h3 hedge hr₀C hr₀'C hne₀ hrC hr'C hne
  refine qtwoDL1_rankTwo_eq_of_card_le ?_
  rw [hcard]
  exact hcard₀.trans hloc

theorem ggQTwoEdgeAmbientInput_of_base_local (hB : GGQTwoDL1EdgeBaseInput)
    (hLoc : GGQTwoDL1EdgeLocalInput) : GGQTwoEdgeAmbientInput :=
  ggQTwoEdgeAmbientInputOn_of_base_local (fun m (hm : 7 ≤ m) => by omega) hB hLoc

end Inputs

end CFSG.StandardType.QTwo

end
