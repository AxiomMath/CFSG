module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UDih5
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

section Dih

variable {G : Type} [Group G] {I : Subgroup G}

open Classical in
@[expose] noncomputable def ob5dd (f : ↥I →* DihedralGroup 5) (g : G) : DihedralGroup 5 :=
  if hg : g ∈ I then f ⟨g, hg⟩ else 1

theorem ob5dd_mul (f : ↥I →* DihedralGroup 5) {g g' : G} (hg : g ∈ I) (hg' : g' ∈ I) :
    ob5dd f (g * g') = ob5dd f g * ob5dd f g' := by
  simp only [ob5dd, dif_pos hg, dif_pos hg', dif_pos (I.mul_mem hg hg')]
  rw [← map_mul]
  rfl

theorem ob5dd_one (f : ↥I →* DihedralGroup 5) : ob5dd f 1 = 1 := by
  simp only [ob5dd, dif_pos I.one_mem]
  have : (⟨1, I.one_mem⟩ : ↥I) = 1 := rfl
  rw [this, map_one]

theorem ob5dd_inv (f : ↥I →* DihedralGroup 5) {g : G} (hg : g ∈ I) :
    ob5dd f g⁻¹ = (ob5dd f g)⁻¹ := by
  simp only [ob5dd, dif_pos hg, dif_pos (I.inv_mem hg)]
  rw [← map_inv]
  rfl

theorem ob5dd_pow (f : ↥I →* DihedralGroup 5) {x : G} (hx : x ∈ I) (n : ℕ) :
    ob5dd f (x ^ n) = ob5dd f x ^ n := by
  induction n with
  | zero => simp [ob5dd_one]
  | succ n ih =>
    rw [pow_succ, ob5dd_mul f (I.pow_mem hx n) hx, ih, pow_succ]

end Dih

section DihFacts

variable {G : Type} [Group G] {I P V Vh : Subgroup G} {h : G}

open scoped Classical in
theorem ob5_exists_v (f : ↥I →* DihedralGroup 5) (hsurj : Function.Surjective f)
    (hfP : ∀ g ∈ I, ob5dd f g = 1 ↔ g ∈ P) (hIV : I = V ⊔ Vh) (hh : h ∈ I)
    (hPn : ∀ i ∈ I, ∀ p ∈ P, i * p * i⁻¹ ∈ P)
    (hVh' : ∀ w ∈ Vh, ∃ v ∈ V, w = h * v * h⁻¹) :
    ∃ v ∈ V, ob5dd f v ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hVP : V ≤ P := fun v hv => (hfP v (hIV ▸ Subgroup.mem_sup_left hv)).mp (hcon v hv)
  have hVhP : Vh ≤ P := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hVh' w hw
    exact hPn h hh v (hVP hv)
  have hIP : I ≤ P := by
    rw [hIV]
    exact sup_le hVP hVhP
  obtain ⟨g, hg⟩ := hsurj (DihedralGroup.r 1)
  have h1 : ob5dd f (g : G) = 1 := (hfP g g.2).mpr (hIP g.2)
  have h2 : ob5dd f (g : G) = DihedralGroup.r 1 := by
    unfold ob5dd
    rw [dif_pos g.2]
    exact hg
  rw [h2] at h1
  exact absurd h1 (by decide)

theorem ob5dd_conj (f : ↥I →* DihedralGroup 5) {g x : G} (hg : g ∈ I) (hx : x ∈ I) :
    ob5dd f (g * x * g⁻¹) = ob5dd f g * ob5dd f x * (ob5dd f g)⁻¹ := by
  rw [ob5dd_mul f (I.mul_mem hg hx) (I.inv_mem hg), ob5dd_mul f hg hx, ob5dd_inv f hg]

theorem ob5_exists_y [Finite G] (f : ↥I →* DihedralGroup 5) (hsurj : Function.Surjective f) :
    ∃ y ∈ I, Odd (orderOf y) ∧ ob5dd f y = DihedralGroup.r 1 := by
  obtain ⟨g, hg⟩ := hsurj (DihedralGroup.r 1)
  have h2 : ob5dd f (g : G) = DihedralGroup.r 1 := by
    unfold ob5dd
    rw [dif_pos g.2]
    exact hg
  have hn : orderOf (g : G) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a, m, hm, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨(g : G) ^ (2 ^ (4 * a)), I.pow_mem g.2 _, ?_, ?_⟩
  · have hdvd : orderOf (g : G) ∣ 2 ^ (4 * a) * m := by
      rw [hdecomp]
      exact mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) m
    have hpow : ((g : G) ^ (2 ^ (4 * a))) ^ m = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hpow)
  · rw [ob5dd_pow f g.2, h2, DihedralGroup.r_one_pow]
    have h16 : ((2 ^ (4 * a) : ℕ) : ZMod 5) = 1 := by
      push_cast
      rw [pow_mul, show (2 : ZMod 5) ^ 4 = 1 from by decide, one_pow]
    rw [h16]

theorem ob5_V_cover (f : ↥I →* DihedralGroup 5) (hfP : ∀ g ∈ I, ob5dd f g = 1 ↔ g ∈ P)
    {V B : Subgroup G} (hBdef : ∀ x, x ∈ B ↔ x ∈ V ∧ x ∈ P) (hVI : V ≤ I)
    (hV2 : ∀ v ∈ V, v * v = 1) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    {v : G} (hv : v ∈ V) (hvP : ob5dd f v ≠ 1) :
    ∀ w ∈ V, w ∈ B ∨ ∃ b ∈ B, w = v * b := by
  intro w hw
  have hwI : w ∈ I := hVI hw
  have hvI : v ∈ I := hVI hv
  have ha2 : ob5dd f v * ob5dd f v = 1 := by
    rw [← ob5dd_mul f hvI hvI, hV2 v hv, ob5dd_one]
  have hb2 : ob5dd f w * ob5dd f w = 1 := by
    rw [← ob5dd_mul f hwI hwI, hV2 w hw, ob5dd_one]
  have hab : ob5dd f v * ob5dd f w = ob5dd f w * ob5dd f v := by
    rw [← ob5dd_mul f hvI hwI, ← ob5dd_mul f hwI hvI, hVc v hv w hw]
  rcases ob5_dih_comm_inv _ _ ha2 hvP hb2 hab with hb1 | hbeq
  · left
    exact (hBdef w).mpr ⟨hw, (hfP w hwI).mp hb1⟩
  · right
    refine ⟨v⁻¹ * w, (hBdef _).mpr ⟨V.mul_mem (V.inv_mem hv) hw, ?_⟩, by group⟩
    have hdd : ob5dd f (v⁻¹ * w) = 1 := by
      rw [ob5dd_mul f (I.inv_mem hvI) hwI, ob5dd_inv f hvI, hbeq, inv_mul_cancel]
    exact (hfP _ (I.mul_mem (I.inv_mem hvI) hwI)).mp hdd

theorem ob5_Vh_cover (f : ↥I →* DihedralGroup 5) (hfP : ∀ g ∈ I, ob5dd f g = 1 ↔ g ∈ P)
    {Vh A : Subgroup G} (hAdef : ∀ x, x ∈ A ↔ x ∈ Vh ∧ x ∈ P) (hVhI : Vh ≤ I)
    (hVh2 : ∀ w ∈ Vh, w * w = 1) (hVhc : ∀ w ∈ Vh, ∀ w' ∈ Vh, w * w' = w' * w)
    {w0 : G} (hw0 : w0 ∈ Vh) (hw0P : ob5dd f w0 ≠ 1) :
    ∀ w ∈ Vh, w ∈ A ∨ ∃ a ∈ A, w = w0 * a := by
  intro w hw
  have hwI : w ∈ I := hVhI hw
  have hw0I : w0 ∈ I := hVhI hw0
  have ha2 : ob5dd f w0 * ob5dd f w0 = 1 := by
    rw [← ob5dd_mul f hw0I hw0I, hVh2 w0 hw0, ob5dd_one]
  have hb2 : ob5dd f w * ob5dd f w = 1 := by
    rw [← ob5dd_mul f hwI hwI, hVh2 w hw, ob5dd_one]
  have hab : ob5dd f w0 * ob5dd f w = ob5dd f w * ob5dd f w0 := by
    rw [← ob5dd_mul f hw0I hwI, ← ob5dd_mul f hwI hw0I, hVhc w0 hw0 w hw]
  rcases ob5_dih_comm_inv _ _ ha2 hw0P hb2 hab with hb1 | hbeq
  · left
    exact (hAdef w).mpr ⟨hw, (hfP w hwI).mp hb1⟩
  · right
    refine ⟨w0⁻¹ * w, (hAdef _).mpr ⟨Vh.mul_mem (Vh.inv_mem hw0) hw, ?_⟩, by group⟩
    have hdd : ob5dd f (w0⁻¹ * w) = 1 := by
      rw [ob5dd_mul f (I.inv_mem hw0I) hwI, ob5dd_inv f hw0I, hbeq, inv_mul_cancel]
    exact (hfP _ (I.mul_mem (I.inv_mem hw0I) hwI)).mp hdd

theorem ob5_vw_rel (f : ↥I →* DihedralGroup 5) (hfP : ∀ g ∈ I, ob5dd f g = 1 ↔ g ∈ P)
    {V : Subgroup G} (hVI : V ≤ I) {y : G} (hyI : y ∈ I) (hy : ob5dd f y = DihedralGroup.r 1)
    {v : G} (hv : v ∈ V) (hvP : ob5dd f v ≠ 1) (hV2 : ∀ v ∈ V, v * v = 1)
    {w0 : G} (hw0I : w0 ∈ I) (hw0 : w0 * w0 = 1) (hw0P : ob5dd f w0 ≠ 1) :
    ∃ j : ℕ, ∃ q ∈ P, v * w0 = y ^ j * q := by
  have hvI : v ∈ I := hVI hv
  have ha2 : ob5dd f v * ob5dd f v = 1 := by
    rw [← ob5dd_mul f hvI hvI, hV2 v hv, ob5dd_one]
  have hb2 : ob5dd f w0 * ob5dd f w0 = 1 := by
    rw [← ob5dd_mul f hw0I hw0I, hw0, ob5dd_one]
  obtain ⟨k, hk | hb⟩ := ob5_dih_two_mul _ _ ha2 hvP hb2
  · have hdy : ob5dd f (y ^ k.val) = DihedralGroup.r k := by
      rw [ob5dd_pow f hyI, hy, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    have hvw : ob5dd f (v * w0) = DihedralGroup.r k := by
      rw [ob5dd_mul f hvI hw0I, hk]
    have hqI : (y ^ k.val)⁻¹ * (v * w0) ∈ I :=
      I.mul_mem (I.inv_mem (I.pow_mem hyI _)) (I.mul_mem hvI hw0I)
    have hq1 : ob5dd f ((y ^ k.val)⁻¹ * (v * w0)) = 1 := by
      rw [ob5dd_mul f (I.inv_mem (I.pow_mem hyI _)) (I.mul_mem hvI hw0I),
        ob5dd_inv f (I.pow_mem hyI _), hdy, hvw, inv_mul_cancel]
    exact ⟨k.val, (y ^ k.val)⁻¹ * (v * w0), (hfP _ hqI).mp hq1, by group⟩
  · exact absurd hb hw0P

end DihFacts

section Concrete

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

@[expose] noncomputable def ob5dihHom (c : S828Ctx T L I H h k)
    (e : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)
    (hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h)) :
    ↥(ch82I (fsuV T I) h) →* DihedralGroup 5 :=
  e.toMonoidHom.comp (QuotientGroup.mk' ((kerIn (fsuM T L ⊓ ch82I (fsuV T I) h)
    (ch82I (fsuV T I) h)).subgroupOf (ch82I (fsuV T I) h)))

theorem ob5dihHom_surj (c : S828Ctx T L I H h k)
    (e : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)
    (hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h)) :
    Function.Surjective (ob5dihHom c e hkerI) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ob5dihHom_ker (c : S828Ctx T L I H h k)
    (e : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)
    (hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h)) (g : ↥(ch82I (fsuV T I) h)) :
    ob5dihHom c e hkerI g = 1 ↔ (g : G) ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
  unfold ob5dihHom
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, hkerI]

end Concrete

end CFSG.Quasithin.H13
