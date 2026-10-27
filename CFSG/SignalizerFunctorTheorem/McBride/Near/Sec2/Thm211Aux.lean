module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

variable {Γ : Type u} [Group Γ]

theorem admits_iff {Q X : Subgroup Γ} :
    Admits Q X ↔ ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X :=
  Subgroup.le_normalizer_iff

theorem isSolvable_of_le {P Q : Subgroup Γ} (h : P ≤ Q) (hQ : Group.IsSolvable Q) :
    Group.IsSolvable P :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)

theorem normalizer_le_normalizer_centralizer (F : Subgroup Γ) :
    Subgroup.normalizer (F : Set Γ) ≤
      Subgroup.normalizer ((Subgroup.centralizer (F : Set Γ) : Subgroup Γ) : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (F : Set Γ) → ∀ {x : Γ},
      x ∈ Subgroup.centralizer (F : Set Γ) → g * x * g⁻¹ ∈ Subgroup.centralizer (F : Set Γ) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : g⁻¹ * f * g ∈ F := (Subgroup.mem_normalizer_iff''.mp hg f).mp hf
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ hf'
    calc f * (g * x * g⁻¹) = g * ((g⁻¹ * f * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * f := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key hg hx, fun hx => by simpa [mul_assoc] using key (inv_mem hg) hx⟩

theorem normalizer_le_normalizer_map_subtype {Y : Subgroup Γ} (P : Subgroup ↥Y)
    [P.Characteristic] :
    Subgroup.normalizer (Y : Set Γ) ≤
      Subgroup.normalizer ((P.map Y.subtype : Subgroup Γ) : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (Y : Set Γ) → ∀ {x : Γ},
      x ∈ P.map Y.subtype → g * x * g⁻¹ ∈ P.map Y.subtype := by
    intro g hg x hx
    let φ : MulAut ↥Y := Y.normalizerMonoidHom ⟨g, hg⟩
    have hφ : ∀ t : Y, ((φ t : Y) : Γ) = g * t * g⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨g, hg⟩ t
    have hchar : P.map φ.toMonoidHom = P := Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨φ t, ?_, (hφ t).symm ▸ rfl⟩
    rw [← hchar]
    exact ⟨t, ht, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key hg hx, fun hx => by simpa [mul_assoc] using key (inv_mem hg) hx⟩

theorem normalizer_le_normalizer_fitting (Y : Subgroup Γ) :
    Subgroup.normalizer (Y : Set Γ) ≤ Subgroup.normalizer (CFSG.fittingSubgroupOf Y : Set Γ) :=
  normalizer_le_normalizer_map_subtype (CFSG.fittingSubgroup ↥Y)

theorem inf_normalizer_le_normalizer_norIn_cenIn (K F : Subgroup Γ) :
    Subgroup.normalizer (K : Set Γ) ⊓ Subgroup.normalizer (F : Set Γ) ≤
      Subgroup.normalizer ((norIn K ((cenIn K (F : Set Γ) : Subgroup Γ) : Set Γ) : Subgroup Γ) :
        Set Γ) := by
  rintro g ⟨hK, hF⟩
  have h1 : g ∈ Subgroup.normalizer ((cenIn K (F : Set Γ) : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hK, normalizer_le_normalizer_centralizer F hF⟩
  have h2 : g ∈ Subgroup.normalizer
      ((Subgroup.normalizer ((cenIn K (F : Set Γ) : Subgroup Γ) : Set Γ) : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer h1
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hK, h2⟩

theorem mem_normalizer_of_forall {H : Subgroup Γ} {g : Γ} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem mem_scalSet_iff {X A D S : Subgroup Γ} :
    S ∈ scalSet X A D ↔ S ≤ X ∧ Admits ((X ⊓ D) ⊔ A) S ∧ Group.IsSolvable S :=
  Iff.rfl

theorem le_scalJoin {X A D S : Subgroup Γ} (hS : S ∈ scalSet X A D) : S ≤ scalJoin X A D :=
  le_iSup₂ (f := fun S (_ : S ∈ scalSet X A D) => S) S hS

theorem scalJoin_le {X A D Y : Subgroup Γ} (h : ∀ S ∈ scalSet X A D, S ≤ Y) :
    scalJoin X A D ≤ Y :=
  iSup₂_le h

theorem scalJoin_le_left (X A D : Subgroup Γ) : scalJoin X A D ≤ X :=
  scalJoin_le fun _ hS => hS.1

theorem scalSet_congr {X A D D' : Subgroup Γ} (h : X ⊓ D = X ⊓ D') :
    scalSet X A D = scalSet X A D' := by
  unfold scalSet
  rw [h]

theorem scalJoin_congr {X A D D' : Subgroup Γ} (h : X ⊓ D = X ⊓ D') :
    scalJoin X A D = scalJoin X A D' := by
  unfold scalJoin
  rw [scalSet_congr h]

theorem scalJoin_bot (A D : Subgroup Γ) : scalJoin ⊥ A D = ⊥ :=
  le_bot_iff.mp (scalJoin_le_left _ _ _)

theorem map_conj_mem_scalSet {X A D S : Subgroup Γ} {g : Γ}
    (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hgE : g ∈ Subgroup.normalizer (((X ⊓ D) ⊔ A : Subgroup Γ) : Set Γ))
    (hS : S ∈ scalSet X A D) : S.map (MulAut.conj g).toMonoidHom ∈ scalSet X A D := by
  obtain ⟨hSX, hSE, hSs⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgX s).mp (hSX hs)
  · rw [admits_iff]
    rintro e he _ ⟨s, hs, rfl⟩
    have he' : g⁻¹ * e * g ∈ (X ⊓ D) ⊔ A := (Subgroup.mem_normalizer_iff''.mp hgE e).mp he
    have h1 := (admits_iff.mp hSE) _ he' s hs
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have e := Subgroup.equivMapOfInjective S (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    have := hSs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem mem_normalizer_scalJoin {X A D : Subgroup Γ} {g : Γ}
    (hgX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hgE : g ∈ Subgroup.normalizer (((X ⊓ D) ⊔ A : Subgroup Γ) : Set Γ)) :
    g ∈ Subgroup.normalizer (scalJoin X A D : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (X : Set Γ) →
      g ∈ Subgroup.normalizer (((X ⊓ D) ⊔ A : Subgroup Γ) : Set Γ) →
      ∀ x ∈ scalJoin X A D, g * x * g⁻¹ ∈ scalJoin X A D := by
    intro g hgX hgE x hx
    have : (scalJoin X A D).map (MulAut.conj g).toMonoidHom ≤ scalJoin X A D := by
      unfold scalJoin
      rw [Subgroup.map_iSup]
      refine iSup_le fun S => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hS => ?_
      exact le_scalJoin (map_conj_mem_scalSet hgX hgE hS)
    exact this ⟨x, hx, by simp [MulAut.conj_apply]⟩
  exact mem_normalizer_of_forall (key hgX hgE)
    (fun x hx => by simpa using key (inv_mem hgX) (inv_mem hgE) x hx)

theorem le_normalizer_inf_of_le_centralizer {X A D : Subgroup Γ}
    (hD : D ≤ Subgroup.centralizer (A : Set Γ)) :
    A ≤ Subgroup.normalizer ((X ⊓ D : Subgroup Γ) : Set Γ) := by
  have key : ∀ {a : Γ}, a ∈ A → ∀ x ∈ X ⊓ D, a * x * a⁻¹ = x := by
    intro a ha x hx
    have := Subgroup.mem_centralizer_iff.mp (hD hx.2) a ha
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  intro a ha
  exact mem_normalizer_of_forall (fun x hx => by rw [key ha x hx]; exact hx)
    (fun x hx => by
      have h1 := key (inv_mem ha) x hx
      rw [inv_inv] at h1
      rw [h1]
      exact hx)

theorem sup_le_normalizer_scalJoin {X A D : Subgroup Γ}
    (hD : D ≤ Subgroup.centralizer (A : Set Γ)) (hDX : Admits D X) (hAX : Admits A X) :
    D ⊔ A ≤ Subgroup.normalizer (scalJoin X A D : Set Γ) := by
  refine sup_le (fun g hg => mem_normalizer_scalJoin (hDX hg) ?_)
    (fun g hg => mem_normalizer_scalJoin (hAX hg) ?_)
  · refine Subgroup.inf_normalizer_le_normalizer_sup (X ⊓ D) A ⟨?_, ?_⟩
    · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hDX hg, Subgroup.le_normalizer hg⟩
    · exact Subgroup.centralizer_le_normalizer _ (hD hg)
  · exact Subgroup.inf_normalizer_le_normalizer_sup (X ⊓ D) A
      ⟨le_normalizer_inf_of_le_centralizer hD hg, Subgroup.le_normalizer hg⟩

theorem inf_le_scalJoin {X A D : Subgroup Γ} (hD : D ≤ Subgroup.centralizer (A : Set Γ))
    (hs : Group.IsSolvable (X ⊓ D : Subgroup Γ)) : X ⊓ D ≤ scalJoin X A D :=
  le_scalJoin ⟨inf_le_left, sup_le Subgroup.le_normalizer
    (le_normalizer_inf_of_le_centralizer hD), hs⟩

theorem nearPSolvable_of_le {p : ℕ} {G J : Subgroup Γ} (hJG : J ≤ G)
    (h : signalizerNearPSolvable p ↥G) : signalizerNearPSolvable p ↥J := by
  obtain ⟨hcop, hsec⟩ := signalizerNearPSolvable_iff.1 h
  refine signalizerNearPSolvable_iff.2
    ⟨hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hJG), fun S _ _ hS hnc => ?_⟩
  exact hsec S (isSectionOf_of_le hJG hS) hnc

theorem nearAsolvAction_of_le {p : ℕ} {A G : Subgroup Γ} (h : NearAsolvAction p A G)
    {J : Subgroup Γ} (hJG : J ≤ G) (hAJ : Admits A J) : NearAsolvAction p A J where
  prime := h.prime
  odd := h.odd
  elemAbelian := h.elemAbelian
  admits := hAJ
  nearPSolvable := nearPSolvable_of_le hJG h.nearPSolvable
  solvable_cen := isSolvable_of_le (inf_le_inf_right _ hJG) h.solvable_cen

theorem nearAsolvAction_qimg {p : ℕ} {A G : Subgroup Γ} (h : NearAsolvAction p A G)
    {R : Subgroup Γ} (hG : G ≤ AChief.nrm R) (hA : A ≤ AChief.nrm R) :
    NearAsolvAction p (AChief.qimg R A) (AChief.qimg R G) where
  prime := h.prime
  odd := h.odd
  elemAbelian := AChief.isElemAbelian_qimg h.elemAbelian
  admits := AChief.qimg_le_normalizer h.admits
  nearPSolvable := by
    obtain ⟨hcop, hsec⟩ := signalizerNearPSolvable_iff.1 h.nearPSolvable
    refine signalizerNearPSolvable_iff.2 ⟨?_, fun S _ _ hS hnc => ?_⟩
    · have h1 : Nat.card (AChief.qimg R G) ∣ Nat.card (G.subgroupOf (AChief.nrm R)) :=
        Subgroup.card_map_dvd _ _
      rw [AChief.card_subgroupOf hG] at h1
      exact hcop.coprime_dvd_right h1
    · exact hsec S ((isSectionOf_of_isSectionOf_map (AChief.qmap R)
        (G.subgroupOf (AChief.nrm R)) hS).trans
          (IsSectionOf.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hG).symm)) hnc
  solvable_cen := by
    have himg := AChief.qimg_inf_centralizer h.prime h.elemAbelian h.admits hA hG
      h.nearPSolvable.1
    have hY : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ AChief.nrm R := inf_le_left.trans hG
    have hs : Group.IsSolvable (G ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) :=
      h.solvable_cen
    show Group.IsSolvable (AChief.qimg R G ⊓ Subgroup.centralizer
      ((AChief.qimg R A : Subgroup (AChief.QG R)) : Set (AChief.QG R)) : Subgroup (AChief.QG R))
    rw [← himg]
    exact Group.isSolvable_of_surjective (SolQuot.qres_surjective hY)

theorem qimg_scalE {R X A D : Subgroup Γ} (hRX : R ≤ X) (hX : X ≤ AChief.nrm R)
    (hA : A ≤ AChief.nrm R) :
    AChief.qimg R ((X ⊓ D) ⊔ A) = (AChief.qimg R X ⊓ AChief.qimg R D) ⊔ AChief.qimg R A := by
  have h1 : AChief.qimg R (X ⊓ D) = AChief.qimg R X ⊓ AChief.qimg R D := by
    rw [inf_comm X D, SolQuot.qimg_inf_of_le hX hRX, inf_comm]
  rw [SolQuot.qimg_sup (inf_le_left.trans hX) hA, h1]

theorem qimg_mem_scalSet {R X A D S : Subgroup Γ} (hR : Group.IsSolvable R) (hRX : R ≤ X)
    (hX : X ≤ AChief.nrm R) (hA : A ≤ AChief.nrm R) (hS : S ∈ scalSet X A D) :
    AChief.qimg R S ∈ scalSet (AChief.qimg R X) (AChief.qimg R A) (AChief.qimg R D) := by
  obtain ⟨hSX, hSE, hSs⟩ := hS
  refine ⟨SolQuot.qimg_mono hSX, ?_, ?_⟩
  · rw [← qimg_scalE hRX hX hA]
    exact AChief.qimg_le_normalizer hSE
  · exact (SolQuot.isSolvable_qimg_iff hR (hSX.trans hX)).mpr hSs

theorem qpre_mem_scalSet {R X A D : Subgroup Γ} {S' : Subgroup (AChief.QG R)}
    (hR : Group.IsSolvable R) (hRX : R ≤ X) (hX : X ≤ AChief.nrm R) (hA : A ≤ AChief.nrm R)
    (hS' : S' ∈ scalSet (AChief.qimg R X) (AChief.qimg R A) (AChief.qimg R D)) :
    SolQuot.qpre R S' ∈ scalSet X A D := by
  obtain ⟨hSX, hSE, hSs⟩ := hS'
  have hE : (X ⊓ D) ⊔ A ≤ AChief.nrm R := sup_le (inf_le_left.trans hX) hA
  refine ⟨?_, ?_, ?_⟩
  · have := SolQuot.qpre_mono hSX
    rwa [SolQuot.qpre_qimg hX, sup_eq_left.mpr hRX] at this
  · refine (SolQuot.qimg_le_normalizer_iff (Y := AChief.nrm R) (SolQuot.qpre_le_nrm S')
      (inf_le_right.trans (SolQuot.le_qpre S')) le_rfl hE).mp ?_
    rw [SolQuot.qimg_qpre, qimg_scalE hRX hX hA]
    exact hSE
  · exact AChief.isSolvable_of_qimg (SolQuot.le_qpre S') (SolQuot.qpre_le_nrm S') hR
      (by rw [SolQuot.qimg_qpre]; exact hSs)

theorem qimg_scalJoin {R X A D : Subgroup Γ} (hR : Group.IsSolvable R) (hRX : R ≤ X)
    (hX : X ≤ AChief.nrm R) (hA : A ≤ AChief.nrm R) :
    AChief.qimg R (scalJoin X A D) =
      scalJoin (AChief.qimg R X) (AChief.qimg R A) (AChief.qimg R D) := by
  have hle : ∀ S ∈ scalSet X A D, S ≤ AChief.nrm R := fun S hS => hS.1.trans hX
  unfold scalJoin
  rw [SolQuot.qimg_biSup (S := fun S : Subgroup Γ => S) hle]
  apply le_antisymm
  · refine iSup₂_le fun S hS => ?_
    exact le_iSup₂_of_le (AChief.qimg R S) (qimg_mem_scalSet hR hRX hX hA hS) le_rfl
  · refine iSup₂_le fun S' hS' => ?_
    have hmem := qpre_mem_scalSet hR hRX hX hA hS'
    refine le_iSup₂_of_le (SolQuot.qpre R S') hmem ?_
    rw [SolQuot.qimg_qpre]

theorem le_scalJoin_of_admits {X A D R : Subgroup Γ} (hRX : R ≤ X)
    (hRE : Admits ((X ⊓ D) ⊔ A) R) (hR : Group.IsSolvable R) : R ≤ scalJoin X A D :=
  le_scalJoin ⟨hRX, hRE, hR⟩

theorem isSolvable_sup_inf {X D K : Subgroup Γ} (hDX : D ≤ Subgroup.normalizer (X : Set Γ))
    (hD : Group.IsSolvable D) (hXK : Group.IsSolvable (X ⊓ K : Subgroup Γ)) :
    Group.IsSolvable ((X ⊔ D) ⊓ K : Subgroup Γ) := by
  have hXD : X ⊔ D ≤ AChief.nrm X := sup_le Subgroup.le_normalizer hDX
  have hYn : (X ⊔ D) ⊓ K ≤ AChief.nrm X := inf_le_left.trans hXD
  have hk : Group.IsSolvable ↥((X ⊔ D) ⊓ K ⊓ X) :=
    isSolvable_of_le (le_inf inf_le_right (inf_le_left.trans inf_le_right)) hXK
  refine (SolQuot.isSolvable_qimg_iff_of_inf hk hYn).mp ?_
  have h1 : AChief.qimg X ((X ⊔ D) ⊓ K) ≤ AChief.qimg X D := by
    have : AChief.qimg X ((X ⊔ D) ⊓ K) ≤ AChief.qimg X (X ⊔ D) :=
      SolQuot.qimg_mono inf_le_left
    rwa [SolQuot.qimg_sup Subgroup.le_normalizer hDX, SolQuot.qimg_self, bot_sup_eq] at this
  exact isSolvable_of_le h1 (Group.isSolvable_of_surjective (SolQuot.qres_surjective hDX))

theorem normalizer_le_normalizer_kOf [Finite Γ] (N : Subgroup Γ) :
    Subgroup.normalizer (N : Set Γ) ≤ Subgroup.normalizer (kOf N : Set Γ) :=
  normalizer_le_normalizer_map_subtype (Nonsolvable.oStar ↥N)

theorem centralizer_bot : Subgroup.centralizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr fun x hx => by
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _

theorem kOf_ne_bot [Finite Γ] {N : Subgroup Γ} (hsol : sol N = ⊥) (hN : N ≠ ⊥) : kOf N ≠ ⊥ := by
  intro hK
  apply hN
  have := centralizer_kOf_eq_bot hsol
  rw [hK, centralizer_bot, inf_top_eq] at this
  exact this

theorem mOf_ne_bot
    [Finite Γ] {p : ℕ} {A K : Subgroup Γ} (h : SemisimpleAction p A K) :
    mOf A K ≠ ⊥ := by
  intro hM
  have hD : cenIn K A ≤ ⊥ := hM ▸ (thm210b h).1.2.1
  have hF : CFSG.fittingSubgroupOf (cenIn K A) = ⊥ :=
    le_bot_iff.mp ((Subgroup.map_subtype_le _).trans hD)
  have hMK : mOf A K = K := by
    unfold mOf
    rw [hF]
    have h1 : cenIn K ((⊥ : Subgroup Γ) : Set Γ) = K := by
      unfold cenIn
      rw [centralizer_bot, inf_top_eq]
    rw [h1]
    exact inf_eq_left.mpr Subgroup.le_normalizer
  exact h.ne_bot (hMK ▸ hM)

theorem le_normalizer_mOf {A K Q : Subgroup Γ} (hQK : Q ≤ Subgroup.normalizer (K : Set Γ))
    (hQA : Q ≤ Subgroup.normalizer (A : Set Γ)) :
    Q ≤ Subgroup.normalizer (mOf A K : Set Γ) := by
  intro q hq
  have h1 : q ∈ Subgroup.normalizer ((cenIn K (A : Set Γ) : Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hQK hq, normalizer_le_normalizer_centralizer A (hQA hq)⟩
  exact inf_normalizer_le_normalizer_norIn_cenIn K _
    ⟨hQK hq, normalizer_le_normalizer_fitting _ h1⟩

theorem inf_cenIn_eq {K G A : Subgroup Γ} (hKG : K ≤ G) :
    K ⊓ cenIn G (A : Set Γ) = cenIn K (A : Set Γ) := by
  unfold cenIn
  rw [← inf_assoc, inf_eq_left.mpr hKG]

theorem cenIn_eq_of_le {G₁ G A : Subgroup Γ} (hG₁G : G₁ ≤ G) (hD : cenIn G (A : Set Γ) ≤ G₁) :
    cenIn G₁ (A : Set Γ) = cenIn G (A : Set Γ) :=
  le_antisymm (inf_le_inf_right _ hG₁G) (le_inf hD inf_le_right)

theorem exists_mem_of_qmap_eq {R : Subgroup Γ} {x y : ↥(AChief.nrm R)}
    (h : AChief.qmap R x = AChief.qmap R y) : ∃ r ∈ R, (y : Γ) = x * r := by
  have h1 : x⁻¹ * y ∈ R.subgroupOf (AChief.nrm R) := QuotientGroup.eq.mp h
  refine ⟨(x : Γ)⁻¹ * y, Subgroup.mem_subgroupOf.mp h1, ?_⟩
  group

theorem card_lt_of_ne [Finite Γ] {H G : Subgroup Γ} (hHG : H ≤ G) (hne : H ≠ G) :
    Nat.card H < Nat.card G :=
  lt_of_le_of_ne (Subgroup.card_le_of_le hHG) fun heq =>
    hne (Subgroup.eq_of_le_of_card_ge hHG heq.ge)

theorem card_qimg_lt [Finite Γ] {R G : Subgroup Γ} (hRG : R ≤ G) (hG : G ≤ AChief.nrm R)
    (hR : R ≠ ⊥) : Nat.card (AChief.qimg R G) < Nat.card G := by
  have h1 := AChief.card_qimg_mul_card hRG hG
  have h2 : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).mpr hR
  have h3 : 0 < Nat.card (AChief.qimg R G) := Nat.card_pos
  nlinarith

theorem isSolvable_sup {X D : Subgroup Γ} (hDX : D ≤ Subgroup.normalizer (X : Set Γ))
    (hD : Group.IsSolvable D) (hX : Group.IsSolvable X) :
    Group.IsSolvable (X ⊔ D : Subgroup Γ) := by
  have := isSolvable_sup_inf (K := ⊤) hDX hD (by rwa [inf_top_eq])
  rwa [inf_top_eq] at this

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211
