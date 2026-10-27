module

public import CFSG.Quasithin.Background.B15P4Comp
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.Quasithin.B15P4

open CFSG.Open
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

@[expose] def trivQuot (Z : Subgroup V) : Subgroup (MulAut V) where
  carrier := {t | ∀ v : V, t v * v⁻¹ ∈ Z}
  one_mem' := fun v => by simp
  mul_mem' := fun {s t} hs ht v => by
    have h : (s * t) v * v⁻¹ = (s (t v) * (t v)⁻¹) * (t v * v⁻¹) := by
      simp only [MulAut.mul_apply]
      group
    rw [h]
    exact Z.mul_mem (hs (t v)) (ht v)
  inv_mem' := fun {t} ht v => by
    have h : t⁻¹ v * v⁻¹ = (t (t⁻¹ v) * (t⁻¹ v)⁻¹)⁻¹ := by
      simp
    rw [h]
    exact Z.inv_mem (ht _)

theorem mem_trivQuot {Z : Subgroup V} {t : MulAut V} :
    t ∈ trivQuot Z ↔ ∀ v : V, t v * v⁻¹ ∈ Z := Iff.rfl

theorem conj_mem_trivQuot {Z : Subgroup V} {g t : MulAut V} (hg : ∀ z ∈ Z, g z ∈ Z)
    (ht : t ∈ trivQuot Z) : g * t * g⁻¹ ∈ trivQuot Z := by
  intro v
  have h1 : g (t (g⁻¹ v) * (g⁻¹ v)⁻¹) ∈ Z := hg _ (ht (g⁻¹ v))
  have h2 : (g * t * g⁻¹) v * v⁻¹ = g (t (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
    simp [MulAut.mul_apply]
  rw [h2]
  exact h1

theorem mul_mul_inv_mem_Kspan (A K : Subgroup (MulAut V)) {a : MulAut V} (ha : a ∈ A)
    {e : MulAut V} (he : e ∈ Kspan A K) : a * e * a⁻¹ ∈ Kspan A K :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_Kspan A K ha) e).mp he

theorem inv_mul_mul_mem_Kspan (A K : Subgroup (MulAut V)) {a : MulAut V} (ha : a ∈ A)
    {e : MulAut V} (he : e ∈ Kspan A K) : a⁻¹ * e * a ∈ Kspan A K := by
  have := mul_mul_inv_mem_Kspan A K (A.inv_mem ha) he
  simpa using this

theorem apply_mem_fixV_Kspan (A K : Subgroup (MulAut V)) {a : MulAut V} (ha : a ∈ A) {z : V}
    (hz : z ∈ fixV (Kspan A K)) : a z ∈ fixV (Kspan A K) := by
  intro e he
  have h1 : (a⁻¹ * e * a) z = z := hz _ (inv_mul_mul_mem_Kspan A K ha he)
  have h2 : a⁻¹ (e (a z)) = z := by simpa [MulAut.mul_apply] using h1
  have := congrArg a h2
  simpa using this

section LemmaZ

variable [Finite V]

theorem Kspan_inf_central {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G) (hAG : A ≤ G)
    {T : Subgroup (MulAut V)} (hTn : ∀ e ∈ Kspan A K, ∀ t ∈ T, e * t * e⁻¹ ∈ T)
    (hKT : ∀ a ∈ A, ¬ B1.conjAut a K ≤ T) :
    ⁅Kspan A K ⊓ T, Kspan A K⁆ = ⊥ := by
  set E := Kspan A K with hE
  set R := E ⊓ T with hR
  have hRn : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := by
    intro e he r hr
    exact ⟨E.mul_mem (E.mul_mem he hr.1) (E.inv_mem he), hTn e he r hr.2⟩
  have hRK : ∀ a ∈ A, ⁅B1.conjAut a K, R⁆ = ⊥ := by
    intro a ha
    set Ki := B1.conjAut a K with hKi
    have hKic : IsComponentOf Ki G := isComponentOf_conjAut_of_mem hK hAG ha
    have hKiE : Ki ≤ E := conjAut_le_Kspan ha
    have hEKi : E ≤ Subgroup.normalizer (Ki : Set (MulAut V)) := Kspan_le_normalizer hK hAG ha
    have h1 : ⁅R, Ki⁆ ≤ R ⊓ Ki := by
      rw [Subgroup.commutator_le]
      intro r hr k hk
      constructor
      · have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact R.mul_mem hr (hRn k (hKiE hk) r⁻¹ (R.inv_mem hr))
      · have hrn := hEKi hr.1
        rw [Subgroup.mem_normalizer_iff] at hrn
        have h3 : r * k * r⁻¹ ∈ Ki := (hrn k).mp hk
        have e : ⁅r, k⁆ = (r * k * r⁻¹) * k⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact Ki.mul_mem h3 (Ki.inv_mem hk)
    have h2 : ⁅R ⊓ Ki, Ki⁆ = ⊥ := by
      have hnormal : ((R ⊓ Ki).subgroupOf Ki).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_right]
        intro h k hh hk
        exact ⟨hRn k (hKiE hk) h hh.1, Ki.mul_mem (Ki.mul_mem hk hh.2) (Ki.inv_mem hk)⟩
      have hproper : (R ⊓ Ki).subgroupOf Ki ≠ ⊤ := by
        intro htop
        apply hKT a ha
        rw [Subgroup.subgroupOf_eq_top] at htop
        exact fun x hx => (htop hx).1.2
      have hcen := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
        hKic.2.2 _ hproper
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro r hr k hk
      have hmem : (⟨r, hr.2⟩ : Ki) ∈ (R ⊓ Ki).subgroupOf Ki := hr
      have h4 := Subgroup.mem_center_iff.mp (hcen hmem) ⟨k, hk⟩
      have h5 : k * r = r * k := congrArg Subtype.val h4
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h5.symm
    have h3 : ⁅⁅R, Ki⁆, Ki⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (h1.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2))
    have h4 : ⁅⁅Ki, R⁆, Ki⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Ki R]
      exact h3
    have h5 := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h3
    rwa [perfect_of_isComponentOf hKic] at h5
  have hEcent : E ≤ Subgroup.centralizer (R : Set (MulAut V)) := by
    refine Kspan_le_iff.mpr fun a ha => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hRK a ha)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcent

theorem eq_one_of_commV_le {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G) (hAG : A ≤ G)
    (hcomm : commV (Kspan A K) = ⊤)
    (hC : A ⊓ Subgroup.centralizer (Kspan A K : Set (MulAut V)) = ⊥) {b : MulAut V} (hb : b ∈ A)
    (hbZ : ∀ v : V, b v * v⁻¹ ∈ fixV (Kspan A K)) : b = 1 := by
  set E := Kspan A K with hE
  set Z := fixV E with hZ
  set T := trivQuot Z with hT
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := fun a ha z hz => apply_mem_fixV_Kspan A K ha hz
  have hTn : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := fun e he t ht =>
    conj_mem_trivQuot (fun z hz => by rw [hz e he]; exact hz) ht
  have hAT : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun a ha t ht =>
    conj_mem_trivQuot (hZA a ha) ht
  have hKT : ∀ a ∈ A, ¬ B1.conjAut a K ≤ T := by
    intro a ha hle
    have hKle : K ≤ T := by
      intro k hk
      have hk' : a * k * a⁻¹ ∈ B1.conjAut a K := by
        rw [B1.mem_conjAut]
        simpa [mul_assoc] using hk
      have := hAT a⁻¹ (A.inv_mem ha) _ (hle hk')
      simpa [mul_assoc] using this
    have hEle : E ≤ T := by
      refine Kspan_le_iff.mpr fun a' ha' x hx => ?_
      rw [B1.mem_conjAut] at hx
      have := hAT a' ha' _ (hKle hx)
      simpa [mul_assoc] using this
    have hcZ : commV E ≤ Z := G6.commV_le_iff.2 fun x hx v => hEle hx v
    rw [hcomm] at hcZ
    have hKbot : K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxE : x ∈ E := le_Kspan A K hx
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro v
      exact hcZ (Subgroup.mem_top v) x hxE
    exact ne_bot_of_isComponentOf hK hKbot
  have hR : ⁅E ⊓ T, E⁆ = ⊥ := Kspan_inf_central hK hAG hTn hKT
  have h1 : ⁅E, A ⊓ T⁆ ≤ E ⊓ T := by
    rw [Subgroup.commutator_le]
    intro e he c hc
    refine ⟨?_, ?_⟩
    · exact commutator_Kspan_le A K (Subgroup.commutator_mem_commutator he hc.1)
    · have : ⁅e, c⁆ = (e * c * e⁻¹) * c⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact T.mul_mem (hTn e he c hc.2) (T.inv_mem hc.2)
  have h2 : ⁅⁅E, A ⊓ T⁆, E⁆ = ⊥ :=
    le_bot_iff.mp (hR ▸ Subgroup.commutator_mono h1 le_rfl)
  have h3 : ⁅⁅A ⊓ T, E⁆, E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (A ⊓ T) E]
    exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rw [Kspan_perfect hK hAG] at h4
  have h5 : A ⊓ T ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h4
  have hbT : b ∈ A ⊓ T := ⟨hb, hbZ⟩
  have hb1 : b ∈ A ⊓ Subgroup.centralizer (E : Set (MulAut V)) := ⟨hb, h5 hbT⟩
  rw [hC, Subgroup.mem_bot] at hb1
  exact hb1

end LemmaZ

end CFSG.Quasithin.B15P4
