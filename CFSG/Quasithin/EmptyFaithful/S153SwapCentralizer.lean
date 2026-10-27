module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.OrderingMax
import CFSG.GroupTheory.SubgroupCardMul
import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

theorem le_normalizer_inf_centralizer_conjSub {T S L A : Subgroup G} {t : G}
    (htT : t ∈ T) (hT : ∀ g ∈ T, g ∈ S ∨ t⁻¹ * g ∈ S) (ht2 : t * t ∈ S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    T ≤ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (B6.conjSub t L : Set G) : Subgroup G) : Set G) := by
  have hS_Lt : S ≤ Subgroup.normalizer (B6.conjSub t L : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change B6.conjSub s (B6.conjSub t L) = B6.conjSub t L
    have hsts : t⁻¹ * s * t ∈ S :=
      (Subgroup.mem_normalizer_iff''.mp (hTS htT) s).mp hs
    calc
      B6.conjSub s (B6.conjSub t L) = B6.conjSub (s * t) L := by
        rw [B6.conjSub_mul]
      _ = B6.conjSub (t * (t⁻¹ * s * t)) L := by congr 1; group
      _ = B6.conjSub t (B6.conjSub (t⁻¹ * s * t) L) := by rw [B6.conjSub_mul]
      _ = B6.conjSub t L := by rw [B6.conjSub_eq_self (hSL hsts)]
  have htLt : B6.conjSub t (B6.conjSub t L) = L := by
    rw [← B6.conjSub_mul]
    exact B6.conjSub_eq_self (hSL ht2)
  have hcent := (CFSG.SignalizerFunctorTheorem.centralizer_sup L
    (B6.conjSub t L)).symm
  have hD : (A ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (B6.conjSub t L : Set G) : Subgroup G) =
      A ⊓ Subgroup.centralizer ((L ⊔ B6.conjSub t L : Subgroup G) : Set G) := by
    rw [inf_assoc, hcent]
  have hmap : ∀ h : G, B6.conjSub h (L ⊔ B6.conjSub t L) =
      B6.conjSub h L ⊔ B6.conjSub h (B6.conjSub t L) := fun h =>
    Subgroup.map_sup L (B6.conjSub t L) (MulAut.conj h).toMonoidHom
  have hstep : ∀ {h : G}, B6.conjSub h A = A →
      B6.conjSub h (L ⊔ B6.conjSub t L) = L ⊔ B6.conjSub t L →
      B6.conjSub h (A ⊓ Subgroup.centralizer (L : Set G) ⊓
        Subgroup.centralizer (B6.conjSub t L : Set G)) ≤
        A ⊓ Subgroup.centralizer (L : Set G) ⊓
          Subgroup.centralizer (B6.conjSub t L : Set G) := by
    intro h hA hsup
    calc
      B6.conjSub h (A ⊓ Subgroup.centralizer (L : Set G) ⊓
          Subgroup.centralizer (B6.conjSub t L : Set G))
          = B6.conjSub h (A ⊓ Subgroup.centralizer
              ((L ⊔ B6.conjSub t L : Subgroup G) : Set G)) := by rw [hD]
      _ ≤ B6.conjSub h A ⊓ B6.conjSub h (Subgroup.centralizer
              ((L ⊔ B6.conjSub t L : Subgroup G) : Set G)) :=
            Subgroup.map_inf_le _ _ _
      _ ≤ A ⊓ Subgroup.centralizer ((L ⊔ B6.conjSub t L : Subgroup G) : Set G) := by
            refine inf_le_inf (le_of_eq hA) ?_
            calc
              B6.conjSub h (Subgroup.centralizer
                    ((L ⊔ B6.conjSub t L : Subgroup G) : Set G))
                  ≤ Subgroup.centralizer ((MulAut.conj h).toMonoidHom ''
                      ((L ⊔ B6.conjSub t L : Subgroup G) : Set G)) :=
                    Subgroup.map_centralizer_le_centralizer_image _ _
              _ = Subgroup.centralizer
                    ((B6.conjSub h (L ⊔ B6.conjSub t L) : Subgroup G) : Set G) := by
                    simp only [B6.conjSub, MulEquiv.coe_mapSubgroup, Subgroup.coe_map]
              _ = Subgroup.centralizer
                    ((L ⊔ B6.conjSub t L : Subgroup G) : Set G) := by rw [hsup]
      _ = A ⊓ Subgroup.centralizer (L : Set G) ⊓
            Subgroup.centralizer (B6.conjSub t L : Set G) := by rw [← hD]
  intro g hg
  have hgA : B6.conjSub g A = A := B6.conjSub_eq_self (hTA hg)
  have hgsup : B6.conjSub g (L ⊔ B6.conjSub t L) = L ⊔ B6.conjSub t L := by
    rcases hT g hg with hgS | hgS
    · exact (hmap g).trans (by
        rw [B6.conjSub_eq_self (hSL hgS), B6.conjSub_eq_self (hS_Lt hgS)])
    · set s : G := t⁻¹ * g with hsdef
      have hsS : s ∈ S := hgS
      have hgs : g = t * s := by
        rw [hsdef]
        group
      have htsL : B6.conjSub (t * s) L = B6.conjSub t L := by
        rw [B6.conjSub_mul, B6.conjSub_eq_self (hSL hsS)]
      have htsL' : B6.conjSub (t * s) (B6.conjSub t L) = L := by
        rw [B6.conjSub_mul, B6.conjSub_eq_self (hS_Lt hsS)]
        exact htLt
      rw [hgs]
      exact (hmap (t * s)).trans (by rw [htsL, htsL', sup_comm])
  have hginvA : B6.conjSub g⁻¹ A = A := by
    calc
      B6.conjSub g⁻¹ A = B6.conjSub g⁻¹ (B6.conjSub g A) := by rw [hgA]
      _ = B6.conjSub (g⁻¹ * g) A := by rw [B6.conjSub_mul]
      _ = A := by rw [inv_mul_cancel, B6.conjSub_one]
  have hginvsup : B6.conjSub g⁻¹ (L ⊔ B6.conjSub t L) = L ⊔ B6.conjSub t L := by
    calc
      B6.conjSub g⁻¹ (L ⊔ B6.conjSub t L)
          = B6.conjSub g⁻¹ (B6.conjSub g (L ⊔ B6.conjSub t L)) := by rw [hgsup]
      _ = B6.conjSub (g⁻¹ * g) (L ⊔ B6.conjSub t L) := by rw [B6.conjSub_mul]
      _ = L ⊔ B6.conjSub t L := by rw [inv_mul_cancel, B6.conjSub_one]
  exact B6.mem_normalizer_of_conjSub_le (hstep hgA hgsup) (hstep hginvA hginvsup)

theorem inf_centralizer_conjSub_eq_bot [Finite G] {X M Y T S L A : Subgroup G} {t : G}
    (hU : IsUniqueM X M) (hX : X ≤ Y ⊔ T) (hYL : Y ≤ L ⊔ B6.conjSub t L) (hLM : ¬ L ≤ M)
    (htT : t ∈ T) (hT : ∀ g ∈ T, g ∈ S ∨ t⁻¹ * g ∈ S) (ht2 : t * t ∈ S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hA : IsPGroup 2 A) (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    A ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (B6.conjSub t L : Set G) = ⊥ := by
  set D : Subgroup G := A ⊓ Subgroup.centralizer (L : Set G) ⊓
    Subgroup.centralizer (B6.conjSub t L : Set G) with hDdef
  by_contra hne
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := by
    rw [hDdef]
    exact le_normalizer_inf_centralizer_conjSub htT hT ht2 hSL hTS hTA
  have hDCL : D ≤ Subgroup.centralizer (L : Set G) := by
    rw [hDdef]
    exact inf_le_left.trans inf_le_right
  have hDCLt : D ≤ Subgroup.centralizer (B6.conjSub t L : Set G) := by
    rw [hDdef]
    exact inf_le_right
  have hLD : L ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.le_centralizer_iff.mp hDCL).trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hLtD : B6.conjSub t L ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.le_centralizer_iff.mp hDCLt).trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) :=
    hYL.trans (sup_le hLD hLtD)
  have hXD : X ≤ Subgroup.normalizer (D : Set G) :=
    hX.trans (sup_le hYD hTD)
  have hD2 : IsPGroup 2 D := by
    rw [hDdef]
    exact hA.to_le (inf_le_left.trans inf_le_left)
  have hDp : D ≤ pCoreOf 2 (Subgroup.normalizer (D : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hD2
  have hpne : pCoreOf 2 (Subgroup.normalizer (D : Set G)) ≠ ⊥ := by
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ hDp))
  have hInH : InH X (Subgroup.normalizer (D : Set G)) := ⟨hXD, hpne⟩
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hpne
  have hM'eq : M' = M := hU.2 M' ⟨hM'.1, hInH.1.trans hM'.2⟩
  have hNM : Subgroup.normalizer (D : Set G) ≤ M := hM'eq ▸ hM'.2
  exact hLM (hLD.trans hNM)

theorem card_inf_centralizer_sq_le [Finite G] {X M Y T S L A : Subgroup G} {t : G}
    (hU : IsUniqueM X M) (hX : X ≤ Y ⊔ T) (hYL : Y ≤ L ⊔ B6.conjSub t L) (hLM : ¬ L ≤ M)
    (htT : t ∈ T) (hT : ∀ g ∈ T, g ∈ S ∨ t⁻¹ * g ∈ S) (ht2 : t * t ∈ S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hA : IsPGroup 2 A) (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)) ^ 2 ≤ Nat.card ↥A := by
  have hD_eq : A ⊓ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (B6.conjSub t L : Set G) = ⊥ :=
    inf_centralizer_conjSub_eq_bot hU hX hYL hLM htT hT ht2 hSL hTS hA hTA
  let D : Subgroup G := A ⊓ Subgroup.centralizer (L : Set G)
  let D' : Subgroup G := B6.conjSub t D
  have hDle : D ≤ A := inf_le_left
  have hD'le : D' ≤ A := by
    change B6.conjSub t D ≤ A
    have h1 : B6.conjSub t D ≤ B6.conjSub t A := (B6.conjSub t).le_iff_le.mpr hDle
    rwa [B6.conjSub_eq_self (hTA htT)] at h1
  have hD'CLt : D' ≤ Subgroup.centralizer (B6.conjSub t L : Set G) := by
    change B6.conjSub t D ≤ Subgroup.centralizer (B6.conjSub t L : Set G)
    refine ((B6.conjSub t).le_iff_le.mpr inf_le_right).trans ?_
    rw [show ((B6.conjSub t L : Subgroup G) : Set G) =
        (MulAut.conj t).toMonoidHom '' (L : Set G) by
      rw [B6.conjSub, MulEquiv.coe_mapSubgroup, Subgroup.coe_map]]
    simpa only [B6.conjSub, MulEquiv.coe_mapSubgroup, Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (L : Set G)
        (MulAut.conj t).toMonoidHom
  have hinf : D ⊓ D' = ⊥ := by
    have hle : D ⊓ D' ≤ A ⊓ Subgroup.centralizer (L : Set G) ⊓
        Subgroup.centralizer (B6.conjSub t L : Set G) := by
      change D ⊓ D' ≤ D ⊓ Subgroup.centralizer (B6.conjSub t L : Set G)
      exact inf_le_inf_left D hD'CLt
    exact le_bot_iff.mp (hD_eq ▸ hle)
  have hcard : Nat.card D * Nat.card D' ≤ Nat.card A :=
    CFSG.card_mul_card_le_of_inf_eq_bot hDle hD'le hinf
  have hD'card : Nat.card D' = Nat.card D := by
    change Nat.card (B6.conjSub t D) = Nat.card D
    exact Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).toEquiv.symm
  rw [hD'card] at hcard
  simpa [D, pow_two] using hcard

end CFSG.Quasithin
