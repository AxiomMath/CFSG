module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Quotient
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot

open AChief

variable {Γ : Type u} [Group Γ] {R : Subgroup Γ}

@[expose] def qpre (R : Subgroup Γ) (T : Subgroup (QG R)) : Subgroup Γ :=
  (T.comap (qmap R)).map (nrm R).subtype

theorem mem_qpre_iff {T : Subgroup (QG R)} {x : Γ} :
    x ∈ qpre R T ↔ ∃ h : x ∈ nrm R, qmap R ⟨x, h⟩ ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem qpre_le_nrm (T : Subgroup (QG R)) : qpre R T ≤ nrm R := fun _ hx =>
  (mem_qpre_iff.mp hx).1

theorem qpre_mono {S T : Subgroup (QG R)} (h : S ≤ T) : qpre R S ≤ qpre R T :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem le_qpre (T : Subgroup (QG R)) : R ≤ qpre R T := fun x hx =>
  mem_qpre_iff.mpr ⟨Subgroup.le_normalizer hx, by
    rw [show qmap R ⟨x, Subgroup.le_normalizer hx⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)]
    exact one_mem _⟩

theorem qpre_bot : qpre R ⊥ = R := by
  refine le_antisymm (fun x hx => ?_) (le_qpre _)
  obtain ⟨h, hx⟩ := mem_qpre_iff.mp hx
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hx))

theorem qimg_mono {S T : Subgroup Γ} (h : S ≤ T) : qimg R S ≤ qimg R T :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem qimg_le_iff {S : Subgroup Γ} {T : Subgroup (QG R)} (hS : S ≤ nrm R) :
    qimg R S ≤ T ↔ S ≤ qpre R T := by
  constructor
  · intro h x hx
    exact mem_qpre_iff.mpr ⟨hS hx, h ((mem_qimg_iff R S _).mpr ⟨⟨x, hS hx⟩, hx, rfl⟩)⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R S _).mp hz
    exact (mem_qpre_iff.mp (h hy)).2

theorem qimg_qpre (T : Subgroup (QG R)) : qimg R (qpre R T) = T := by
  refine le_antisymm ((qimg_le_iff (qpre_le_nrm T)).mpr le_rfl) fun z hz => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  exact (mem_qimg_iff R _ _).mpr ⟨y, mem_qpre_iff.mpr ⟨y.2, hz⟩, rfl⟩

theorem qpre_qimg {S : Subgroup Γ} (hS : S ≤ nrm R) : qpre R (qimg R S) = S ⊔ R := by
  refine le_antisymm (fun x hx => ?_) (sup_le ((qimg_le_iff hS).mp le_rfl) (le_qpre _))
  obtain ⟨hxN, hxS⟩ := mem_qpre_iff.mp hx
  obtain ⟨y, hy, hyx⟩ := (mem_qimg_iff R S _).mp hxS
  have hr : (y : Γ)⁻¹ * x ∈ R := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hyx)
  have : x = (y : Γ) * ((y : Γ)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hy hr

theorem qimg_bot : qimg R ⊥ = ⊥ := by
  unfold qimg
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem qimg_self : qimg R R = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [qimg_le_iff (Subgroup.le_normalizer), qpre_bot]

theorem qimg_eq_bot_iff {S : Subgroup Γ} (hS : S ≤ nrm R) : qimg R S = ⊥ ↔ S ≤ R := by
  rw [← le_bot_iff, qimg_le_iff hS, qpre_bot]

theorem qimg_le_qimg_iff {S T : Subgroup Γ} (hS : S ≤ nrm R) (hT : T ≤ nrm R) :
    qimg R S ≤ qimg R T ↔ S ≤ T ⊔ R := by
  rw [qimg_le_iff hS, qpre_qimg hT]

theorem qimg_le_qimg_iff_of_le {S T : Subgroup Γ} (hS : S ≤ nrm R) (hT : T ≤ nrm R)
    (hRT : R ≤ T) : qimg R S ≤ qimg R T ↔ S ≤ T := by
  rw [qimg_le_qimg_iff hS hT, sup_eq_left.mpr hRT]

theorem qimg_injOn : Set.InjOn (qimg R) {S | R ≤ S ∧ S ≤ nrm R} := by
  rintro S ⟨hRS, hS⟩ T ⟨hRT, hT⟩ h
  exact le_antisymm ((qimg_le_qimg_iff_of_le hS hT hRT).mp h.le)
    ((qimg_le_qimg_iff_of_le hT hS hRS).mp h.ge)

theorem qimg_iSup {ι : Sort*} {S : ι → Subgroup Γ} (hS : ∀ i, S i ≤ nrm R) :
    qimg R (⨆ i, S i) = ⨆ i, qimg R (S i) :=
  le_antisymm ((qimg_le_iff (iSup_le hS)).mpr
    (iSup_le fun i => (qimg_le_iff (hS i)).mp (le_iSup (fun i => qimg R (S i)) i)))
    (iSup_le fun i => qimg_mono (le_iSup S i))

theorem qimg_biSup {ι : Type*} {s : Set ι} {S : ι → Subgroup Γ} (hS : ∀ i ∈ s, S i ≤ nrm R) :
    qimg R (⨆ i ∈ s, S i) = ⨆ i ∈ s, qimg R (S i) := by
  have h1 : ∀ i, (⨆ (_ : i ∈ s), S i) ≤ nrm R := fun i => iSup_le fun hi => hS i hi
  rw [qimg_iSup h1]
  exact iSup_congr fun i => qimg_iSup (ι := i ∈ s) (S := fun _ => S i) fun hi => hS i hi

theorem qimg_sSup {S : Set (Subgroup Γ)} (hS : ∀ M ∈ S, M ≤ nrm R) :
    qimg R (sSup S) = sSup (qimg R '' S) := by
  rw [sSup_eq_iSup, sSup_image]
  exact qimg_biSup hS

theorem qimg_sup {S T : Subgroup Γ} (hS : S ≤ nrm R) (hT : T ≤ nrm R) :
    qimg R (S ⊔ T) = qimg R S ⊔ qimg R T :=
  le_antisymm ((qimg_le_iff (sup_le hS hT)).mpr (sup_le ((qimg_le_iff hS).mp le_sup_left)
    ((qimg_le_iff hT).mp le_sup_right))) (sup_le (qimg_mono le_sup_left) (qimg_mono le_sup_right))

theorem qimg_inf_of_le {S T : Subgroup Γ} (hT : T ≤ nrm R) (hRT : R ≤ T) :
    qimg R (S ⊓ T) = qimg R S ⊓ qimg R T := by
  refine le_antisymm (le_inf (qimg_mono inf_le_left) (qimg_mono inf_le_right)) fun z hz => ?_
  obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R S _).mp hz.1
  have hyT : (y : Γ) ∈ qpre R (qimg R T) := mem_qpre_iff.mpr ⟨y.2, hz.2⟩
  rw [qpre_qimg hT, sup_eq_left.mpr hRT] at hyT
  exact (mem_qimg_iff R _ _).mpr ⟨y, ⟨hy, hyT⟩, rfl⟩

theorem qimg_map_conj {g : Γ} (hg : g ∈ nrm R) (S : Subgroup Γ) :
    qimg R (S.map (MulAut.conj g).toMonoidHom) =
      (qimg R S).map (MulAut.conj (qmap R ⟨g, hg⟩)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨s, hs, hsy⟩, rfl⟩ := (mem_qimg_iff R _ _).mp hx
    have hsN : s ∈ nrm R := by
      have : s = g⁻¹ * (y : Γ) * g := by
        rw [← hsy]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]
      exact mul_mem (mul_mem (inv_mem hg) y.2) hg
    refine ⟨qmap R ⟨s, hsN⟩, (mem_qimg_iff R S _).mpr ⟨⟨s, hsN⟩, hs, rfl⟩, ?_⟩
    have hy : y = ⟨g, hg⟩ * ⟨s, hsN⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hsy]
      simp [MulAut.conj_apply])
    have h2 : qmap R y = qmap R ⟨g, hg⟩ * qmap R ⟨s, hsN⟩ * (qmap R ⟨g, hg⟩)⁻¹ := by
      rw [hy, map_mul, map_mul, map_inv]
    rw [h2]
    simp [MulAut.conj_apply]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R S _).mp hz
    refine (mem_qimg_iff R _ _).mpr
      ⟨⟨g * y * g⁻¹, mul_mem (mul_mem hg y.2) (inv_mem hg)⟩, ⟨y, hy, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · have : (⟨g * y * g⁻¹, mul_mem (mul_mem hg y.2) (inv_mem hg)⟩ : ↥(nrm R)) =
          ⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      simp [MulAut.conj_apply]

variable {Y : Subgroup Γ}

@[expose] def qres (R Y : Subgroup Γ) (hY : Y ≤ nrm R) : ↥Y →* ↥(qimg R Y) :=
  ((qmap R).comp (Subgroup.inclusion hY)).codRestrict (qimg R Y) fun y =>
    (mem_qimg_iff R Y _).mpr ⟨Subgroup.inclusion hY y, y.2, rfl⟩

theorem coe_qres (hY : Y ≤ nrm R) (y : ↥Y) :
    ((qres R Y hY y : ↥(qimg R Y)) : QG R) = qmap R ⟨y, hY y.2⟩ := rfl

theorem qres_surjective (hY : Y ≤ nrm R) : Function.Surjective (qres R Y hY) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R Y z).mp hz
  exact ⟨⟨y, hy⟩, rfl⟩

theorem ker_qres (hY : Y ≤ nrm R) : (qres R Y hY).ker = R.subgroupOf Y := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : qmap R ⟨y, hY y.2⟩ = 1 := congrArg Subtype.val h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨y, hY y.2⟩ : ↥(nrm R))).mp h1)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff (⟨y, hY y.2⟩ : ↥(nrm R))).mpr
      (Subgroup.mem_subgroupOf.mpr h))

theorem isSolvable_ker_qres (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    Group.IsSolvable (qres R Y hY).ker := by
  rw [ker_qres]
  exact Group.isSolvable_of_isSolvable_injective
    (f := Y.subtype.subgroupComap R) (MonoidHom.subgroupComap_injective _ _ Y.subtype_injective)

theorem qimg_map_subtype (hY : Y ≤ nrm R) (S : Subgroup ↥Y) :
    qimg R (S.map Y.subtype) = (S.map (qres R Y hY)).map (qimg R Y).subtype := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, ⟨s, hs, hsy⟩, hyz⟩ := (mem_qimg_iff R _ _).mp hz
    have hy : y = ⟨s, hY s.2⟩ := Subtype.ext hsy.symm
    refine ⟨qres R Y hY s, ⟨s, hs, rfl⟩, ?_⟩
    rw [← hyz, hy]
    rfl
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact (mem_qimg_iff R _ _).mpr ⟨⟨s, hY s.2⟩, ⟨s, hs, rfl⟩, rfl⟩

theorem subgroupOf_qimg (hY : Y ≤ nrm R) {S : Subgroup Γ} (hSY : S ≤ Y) :
    (qimg R S).subgroupOf (qimg R Y) = (S.subgroupOf Y).map (qres R Y hY) := by
  have h := qimg_map_subtype hY (S.subgroupOf Y)
  rw [Subgroup.map_subgroupOf_eq_of_le hSY] at h
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective (qimg R Y).subtype_injective _

theorem isSolvable_qimg_iff (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    Group.IsSolvable (qimg R Y) ↔ Group.IsSolvable Y :=
  (isSolvable_iff (qres_surjective hY) (isSolvable_ker_qres hR hY)).symm

theorem isSolvable_qimg_iff_of_inf (hk : Group.IsSolvable ↥(Y ⊓ R)) (hY : Y ≤ nrm R) :
    Group.IsSolvable (qimg R Y) ↔ Group.IsSolvable Y := by
  have e : ↥(R.subgroupOf Y) ≃* ↥(R ⊓ Y) := by
    rw [← Subgroup.inf_subgroupOf_right R Y]
    exact Subgroup.subgroupOfEquivOfLe inf_le_right
  rw [inf_comm] at hk
  have hker : Group.IsSolvable (qres R Y hY).ker := by
    rw [ker_qres]
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (isSolvable_iff (qres_surjective hY) hker).symm

theorem mem_of_qmap_mem_qimg {M : Subgroup Γ} (hMY : M ≤ Y) (hRM : Y ⊓ R ≤ M)
    {z : ↥(nrm R)} (hzY : (z : Γ) ∈ Y) (hz : qmap R z ∈ qimg R M) : (z : Γ) ∈ M := by
  obtain ⟨m, hm, hmz⟩ := (mem_qimg_iff R M _).mp hz
  have hr : (m : Γ)⁻¹ * z ∈ R := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmz)
  have hmY : (m : Γ) ∈ Y := hMY hm
  have : (z : Γ) = m * ((m : Γ)⁻¹ * z) := by group
  rw [this]
  exact mul_mem hm (hRM (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hmY) hzY, hr⟩))

theorem mem_normalizer_qimg_iff {M : Subgroup Γ} (hMY : M ≤ Y) (hRM : Y ⊓ R ≤ M)
    (hY : Y ≤ nrm R) {y : Γ} (hy : y ∈ Y) :
    qmap R ⟨y, hY hy⟩ ∈ Subgroup.normalizer (qimg R M : Set (QG R)) ↔
      y ∈ Subgroup.normalizer (M : Set Γ) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxY : x ∈ Y := hMY hx
      have hyx : y * x * y⁻¹ ∈ Y := mul_mem (mul_mem hy hxY) (inv_mem hy)
      refine mem_of_qmap_mem_qimg hMY hRM (z := ⟨y * x * y⁻¹, hY hyx⟩) hyx ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp h (qmap R ⟨x, hY hxY⟩)).mp
        ((mem_qimg_iff R M _).mpr ⟨⟨x, hY hxY⟩, hx, rfl⟩)
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact h1
    · intro hx
      have hxy : x = y⁻¹ * (y * x * y⁻¹) * y := by group
      have hxY : x ∈ Y := by
        rw [hxy]
        exact mul_mem (mul_mem (inv_mem hy) (hMY hx)) hy
      refine mem_of_qmap_mem_qimg hMY hRM (z := ⟨x, hY hxY⟩) hxY ?_
      refine (Subgroup.mem_normalizer_iff.mp h _).mpr ?_
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (mem_qimg_iff R M _).mpr ⟨⟨y * x * y⁻¹, hY (hMY hx)⟩, hx, rfl⟩
  · intro h
    have hz : Subgroup.zpowers y ≤ Subgroup.normalizer (M : Set Γ) := Subgroup.zpowers_le.mpr h
    exact qimg_le_normalizer hz
      ((mem_qimg_iff R _ _).mpr ⟨⟨y, hY hy⟩, Subgroup.mem_zpowers y, rfl⟩)

theorem qimg_le_normalizer_iff {M X : Subgroup Γ} (hMY : M ≤ Y) (hRM : Y ⊓ R ≤ M)
    (hY : Y ≤ nrm R) (hXY : X ≤ Y) :
    qimg R X ≤ Subgroup.normalizer (qimg R M : Set (QG R)) ↔
      X ≤ Subgroup.normalizer (M : Set Γ) := by
  refine ⟨fun h x hx => ?_, qimg_le_normalizer⟩
  exact (mem_normalizer_qimg_iff hMY hRM hY (hXY hx)).mp
    (h ((mem_qimg_iff R X _).mpr ⟨⟨x, hY (hXY hx)⟩, hx, rfl⟩))

theorem qimg_zpowers {a : Γ} (ha : a ∈ nrm R) :
    qimg R (Subgroup.zpowers a) = Subgroup.zpowers (qmap R ⟨a, ha⟩) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, ⟨k, hk⟩, rfl⟩ := (mem_qimg_iff R _ _).mp hz
    refine ⟨k, ?_⟩
    have hy : y = ⟨a, ha⟩ ^ k := Subtype.ext (by simpa using hk.symm)
    rw [hy, map_zpow]
  · rintro ⟨k, rfl⟩
    refine (mem_qimg_iff R _ _).mpr ⟨⟨a, ha⟩ ^ k, ⟨k, ?_⟩, ?_⟩
    · simp
    · simp

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
