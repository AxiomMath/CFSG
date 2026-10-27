module

public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918J3

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace CaseIISec

section Basic

variable {V : Type} [CommGroup V] {D A : Subgroup (MulAut V)} {I : Subgroup V}

theorem A_le_normalizer (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) :
    A ≤ Subgroup.normalizer (D : Set (MulAut V)) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hAD a ha y hy, fun hy => ?_⟩
  have h := hAD a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using h

theorem sup_le_normalizer (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) :
    D ⊔ A ≤ Subgroup.normalizer (D : Set (MulAut V)) :=
  sup_le Subgroup.le_normalizer (A_le_normalizer hAD)

theorem faithful (hsimp : IsSimpleGroup ↥D) (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v) : D ⊓ centSub I = ⊥ := by
  refine inf_centSub_eq_bot_of_isSimpleGroup hsimp (le_stabSub_of_forall_mem hID) fun h => ?_
  obtain ⟨y, hy, v, hv, hne⟩ := hnt
  exact hne (h hy v hv)

theorem equiv (hsimp : IsSimpleGroup ↥D) (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v) : Nonempty (↥D ≃* ↥(autSub D I)) :=
  ⟨autSubEquivOfFaithful (le_stabSub_of_forall_mem hID) (faithful hsimp hID hnt)⟩

theorem normal (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) :
    ∀ x ∈ autSub (D ⊔ A) I, ∀ k ∈ autSub D I, x * k * x⁻¹ ∈ autSub D I :=
  insp5a_sec_normal fun _ hg => sup_le_normalizer hAD hg.1

theorem mem_normalizer_of_normal {G : Type*} [Group G] {X K : Subgroup G}
    (h : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {x : G} (hx : x ∈ X) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h x hx k hk, fun hk => ?_⟩
  have h2 := h x⁻¹ (X.inv_mem hx) _ hk
  simpa [mul_assoc] using h2

theorem two (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I) (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I)
    (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) (hA2 : IsPGroup 2 ↥A) :
    ∀ x ∈ autSub (D ⊔ A) I, ∃ e : ℕ, x ^ 2 ^ e ∈ autSub D I := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  have hg' : (g : MulAut V) ∈ ((D ⊔ A : Subgroup (MulAut V)) : Set (MulAut V)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left D A (A_le_normalizer hAD)] at hg'
  obtain ⟨d, hd, a, ha, hda⟩ := hg'
  have hdI : d ∈ stabSub I := le_stabSub_of_forall_mem hID hd
  have haI : a ∈ stabSub I := le_stabSub_of_forall_mem hIA ha
  obtain ⟨e, he⟩ : ∃ e : ℕ, a ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hA2 ⟨a, ha⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hσX : resHom I ⟨a, haI⟩ ∈ autSub (D ⊔ A) I :=
    mem_autSub.mpr ⟨⟨a, haI⟩, Subgroup.mem_sup_right ha, rfl⟩
  have hσe : (resHom I ⟨a, haI⟩) ^ 2 ^ e = 1 := by
    rw [← map_pow, show (⟨a, haI⟩ : ↥(stabSub I)) ^ 2 ^ e = 1 from Subtype.ext (by simpa using he),
      map_one]
  have hσN : resHom I ⟨a, haI⟩ ∈ Subgroup.normalizer ((autSub D I : Subgroup (MulAut ↥I)) :
      Set (MulAut ↥I)) := mem_normalizer_of_normal (normal hAD) hσX
  have hκ : resHom I ⟨d, hdI⟩ ∈ autSub D I := mem_autSub.mpr ⟨⟨d, hdI⟩, hd, rfl⟩
  have hgda : g = ⟨d, hdI⟩ * ⟨a, haI⟩ := Subtype.ext hda.symm
  obtain ⟨k', hk', hpow⟩ := insp5a_sec_mul_pow_mem hκ hσN (2 ^ e)
  refine ⟨e, ?_⟩
  rw [hgda, map_mul, hpow, hσe, mul_one]
  exact hk'

theorem commSub_eq (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I)
    (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v) : commSub I D = I := by
  have hle : commSub I D ≤ I := commSub_le_of_invariant hID
  have hinv : ∀ y ∈ D, ∀ v ∈ commSub I D, y v ∈ commSub I D := by
    intro y hy v hv
    exact (mem_stabSub_commSub (le_stabSub_of_forall_mem hID hy)
      (Subgroup.le_normalizer hy) v).2 hv
  rcases hImin _ hle hinv with h | h
  · exfalso
    obtain ⟨y, hy, v, hv, hne⟩ := hnt
    exact hne ((mem_fixV.mp (commSub_eq_bot_iff.mp h hv)) y hy)
  · exact h

theorem faithful_sec (hsimp : IsSimpleGroup ↥D) (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v) :
    autSub D I ⊓ centSec (⊤ : Subgroup ↥I) ⊥ = ⊥ := by
  have hfaith := faithful hsimp hID hnt
  rw [eq_bot_iff]
  rintro φ ⟨hφ, hc⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  have hcent : (g : MulAut V) ∈ centSub I := by
    intro u hu
    have h := hc.2 ⟨u, hu⟩ trivial
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    exact congrArg Subtype.val h
  have h1 : (g : MulAut V) ∈ D ⊓ centSub I := ⟨hg, hcent⟩
  rw [hfaith, Subgroup.mem_bot] at h1
  have hg1 : g = 1 := Subtype.ext h1
  rw [hg1, map_one]
  exact Subgroup.one_mem _

theorem irr (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) :
    ∀ J : Subgroup ↥I, (⊥ : Subgroup ↥I) ≤ J → (∀ k ∈ autSub D I, ∀ w ∈ J, k w ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
  intro J _ hJ
  have hDs : D ≤ stabSub I := le_stabSub_of_forall_mem hID
  have hinv : ∀ y ∈ D, ∀ v ∈ J.map I.subtype, y v ∈ J.map I.subtype := by
    rintro y hy _ ⟨w, hw, rfl⟩
    have hk : resHom I ⟨y, hDs hy⟩ ∈ autSub D I := mem_autSub.mpr ⟨⟨y, hDs hy⟩, hy, rfl⟩
    exact ⟨resHom I ⟨y, hDs hy⟩ w, hJ _ hk w hw, rfl⟩
  rcases hImin _ (Subgroup.map_subtype_le J) hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have hwU : (w : V) ∈ J.map I.subtype := ⟨w, hw, rfl⟩
    rw [h, Subgroup.mem_bot] at hwU
    exact Subgroup.mem_bot.2 (Subtype.ext hwU)
  · right
    rw [eq_top_iff]
    intro w _
    have hw : (w : V) ∈ J.map I.subtype := by rw [h]; exact w.2
    exact (Subgroup.mem_map_iff_mem I.subtype_injective).mp hw

theorem bot_lt_top (hI : I ≠ ⊥) : (⊥ : Subgroup ↥I) < ⊤ := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hI
  rw [bot_lt_iff_ne_bot]
  intro h
  have hmem : a ∈ (⊤ : Subgroup ↥I) := Subgroup.mem_top a
  rw [h, Subgroup.mem_bot] at hmem
  exact ha hmem

theorem qsec (hsimp : IsSimpleGroup ↥D) (hnonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a)
    (hA2 : IsPGroup 2 ↥A) (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) (hI : I ≠ ⊥)
    (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I)
    (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I) (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v) :
    InternalSec.QSec (autSub (D ⊔ A) I) (autSub D I) ⊥ := by
  have hDs : D ≤ stabSub I := le_stabSub_of_forall_mem hID
  obtain ⟨e⟩ := equiv hsimp hID hnt
  have hnc : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  exact
    { le := autSub_mono le_sup_left I
      normal := normal hAD
      two := two hID hIA hAD hA2
      stab := fun g _ u => by simp
      fix := bot_le
      comm := insp5a_sec_comm hDs (commSub_eq hID hImin hnt)
      lt := bot_lt_top hI
      irr := irr hID hImin
      faithful := faithful_sec hsimp hID hnt
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1 }

end Basic

end CaseIISec

end CFSG.Quasithin
