module

public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.Quasithin.EmptyFaithful.S152O4Facts

public section

namespace CFSG.Quasithin

namespace S153E

open CFSG.Open CFSG.QuasithinUnique

section Polar

variable {W : Type*} [CommGroup W] {q : W → ZMod 2}

theorem quadPolar_one_right (hq : IsQuadraticFormOn q) (x : W) : quadPolar q x 1 = 0 := by
  have h := hq.2.2 x 1 1
  rw [mul_one] at h
  have h2 : quadPolar q x 1 + quadPolar q x 1 = 0 := CharTwo.add_self_eq_zero _
  rw [← h2, ← h]

theorem quadPolar_one_left (hq : IsQuadraticFormOn q) (y : W) : quadPolar q 1 y = 0 := by
  have h := hq.2.1 1 1 y
  rw [mul_one] at h
  have h2 : quadPolar q 1 y + quadPolar q 1 y = 0 := CharTwo.add_self_eq_zero _
  rw [← h2, ← h]

theorem quadPolar_apply_isometry {g : MulAut W} (hg : g ∈ orthogonalGroupOf q) (x y : W) :
    quadPolar q (g x) (g y) = quadPolar q x y := by
  unfold quadPolar
  rw [← map_mul]
  have h1 : q (g (x * y)) = q (x * y) := hg (x * y)
  have h2 : q (g x) = q x := hg x
  have h3 : q (g y) = q y := hg y
  rw [h1, h2, h3]

def polarHom (hq : IsQuadraticFormOn q) (x : W) : W →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun y => Multiplicative.ofAdd (quadPolar q x y)) fun y z => by
    rw [hq.2.2 x y z]
    rfl

def perpSub (hq : IsQuadraticFormOn q) (X : Subgroup W) : Subgroup W :=
  ⨅ x ∈ X, (polarHom hq x).ker

theorem mem_perpSub (hq : IsQuadraticFormOn q) {X : Subgroup W} {w : W} :
    w ∈ perpSub hq X ↔ ∀ x ∈ X, quadPolar q x w = 0 := by
  simp only [perpSub, Subgroup.mem_iInf, MonoidHom.mem_ker]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  show Multiplicative.ofAdd (quadPolar q x w) = 1 ↔ _
  exact ofAdd_eq_one

theorem commV_le_perpSub (hq : IsQuadraticFormOn q) (hexp : ∀ w : W, w * w = 1)
    {A : Subgroup (MulAut W)} (hA : A ≤ orthogonalGroupOf q) : commV A ≤ perpSub hq (fixV A) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, v, rfl⟩
  rw [SetLike.mem_coe, mem_perpSub]
  intro z hz
  have hgz : g z = z := hz g hg
  have h1 : quadPolar q z (g v * v⁻¹) = quadPolar q z (g v) + quadPolar q z v⁻¹ := hq.2.2 z (g v) v⁻¹
  have h2 : quadPolar q z (g v) = quadPolar q z v := by
    have := quadPolar_apply_isometry (hA hg) z v
    rwa [hgz] at this
  have h3 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hexp v)
  rw [h1, h2, h3]
  exact CharTwo.add_self_eq_zero _

theorem card_ker_polarHom [Finite W] (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q) {z : W}
    (hz : z ≠ 1) : Nat.card ↥(polarHom hq z).ker * 2 = Nat.card W := by
  have hsurj : Function.Surjective (polarHom hq z) := by
    intro a
    have hy : ∃ y : W, quadPolar q z y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz (hn z hcon)
    obtain ⟨y, hy⟩ := hy
    have h1 : quadPolar q z y = 1 := by
      generalize quadPolar q z y = b at hy ⊢
      revert b
      decide
    by_cases ha : a = 1
    · exact ⟨1, by rw [ha, map_one]⟩
    · refine ⟨y, ?_⟩
      show Multiplicative.ofAdd (quadPolar q z y) = a
      rw [h1]
      generalize a = b at ha ⊢
      revert b
      decide
  have h1 : (polarHom hq z).ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    simp
  have := Subgroup.card_mul_index (polarHom hq z).ker
  rw [h1] at this
  exact this

end Polar

section Cyclic

variable {W : Type*} [CommGroup W]

theorem commV_zpowers_le_fixV_of_sq (hexp : ∀ w : W, w * w = 1) {g : MulAut W} (hg : g * g = 1) :
    commV (Subgroup.zpowers g) ≤ fixV (Subgroup.zpowers g) :=
  CFSG.Quasithin.commV_zpowers_le_fixV_of_involution (fun w => (pow_two w).trans (hexp w)) ((pow_two g).trans hg)

end Cyclic

section Hyperplane

variable {W : Type} [CommGroup W] [Finite W] {q : W → ZMod 2}

theorem card_perpSub_of_card_two (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q) {Z : Subgroup W}
    (hZ : Nat.card Z = 2) : Nat.card ↥(perpSub hq Z) * 2 = Nat.card W := by
  obtain ⟨z, hzZ, hz1, hzz, hzeq⟩ := S152O4.exists_eq_zpowers_of_card_two hZ
  have hperp : perpSub hq Z = (polarHom hq z).ker := by
    ext w
    rw [mem_perpSub, MonoidHom.mem_ker]
    constructor
    · intro h
      have := h z hzZ
      show Multiplicative.ofAdd (quadPolar q z w) = 1
      rw [this]
      rfl
    · intro h x hx
      rw [hzeq] at hx
      rcases S152O4.eq_one_or_eq_of_mem_zpowers_two hzz hx with rfl | rfl
      · exact quadPolar_one_left hq w
      · exact ofAdd_eq_one.mp h
  rw [hperp]
  exact card_ker_polarHom hq hn hz1

theorem commV_eq_perpSub (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q)
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {A : Subgroup (MulAut W)}
    (hA : A ≤ orthogonalGroupOf q) {r x : MulAut W} (hr : r ∈ A) (hx : x ∈ A) (hrr : r * r = 1)
    (hxx : x * x = 1) (hfr : Nat.card ↥(fixV (Subgroup.zpowers r)) = 4)
    (hfx : Nat.card ↥(fixV (Subgroup.zpowers x)) = 4)
    (hne : fixV (Subgroup.zpowers r) ≠ fixV (Subgroup.zpowers x)) (hfA : Nat.card ↥(fixV A) = 2) :
    commV A = perpSub hq (fixV A) ∧ Nat.card ↥(commV A) = 8 := by
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  have hle : commV A ≤ perpSub hq (fixV A) := commV_le_perpSub hq hexp hA
  have hperp8 : Nat.card ↥(perpSub hq (fixV A)) = 8 := by
    have := card_perpSub_of_card_two hq hn hfA
    omega
  have hcomm : ∀ g : MulAut W, g * g = 1 → Nat.card ↥(fixV (Subgroup.zpowers g)) = 4 →
      commV (Subgroup.zpowers g) = fixV (Subgroup.zpowers g) := by
    intro g hgg hf
    have h1 := commV_zpowers_le_fixV_of_sq hexp hgg
    have h2 := rk_commV_add_rk_fixV g
    have h3 : rk (fixV (Subgroup.zpowers g)) = 2 := T1531O4.rk_eq_of_card hexp' (n := 2) (by rw [hf]; norm_num)
    rw [S152O4.rk_V_eq_four hcard, h3] at h2
    exact eq_of_le_of_rk_le hexp' h1 (by omega)
  have hcr := hcomm r hrr hfr
  have hcx := hcomm x hxx hfx
  have hmono : ∀ g ∈ A, commV (Subgroup.zpowers g) ≤ commV A := fun g hg =>
    Subgroup.closure_mono fun w ⟨y, hy, v, hv⟩ =>
      ⟨y, (Subgroup.zpowers_le.mpr hg) hy, v, hv⟩
  have hsup : fixV (Subgroup.zpowers r) ⊔ fixV (Subgroup.zpowers x) ≤ commV A := by
    refine sup_le ?_ ?_
    · rw [← hcr]
      exact hmono r hr
    · rw [← hcx]
      exact hmono x hx
  have hlt : Nat.card ↥(fixV (Subgroup.zpowers r)) < Nat.card ↥(fixV (Subgroup.zpowers r) ⊔
      fixV (Subgroup.zpowers x)) := by
    have hle1 : fixV (Subgroup.zpowers r) ≤ fixV (Subgroup.zpowers r) ⊔ fixV (Subgroup.zpowers x) :=
      le_sup_left
    have h1 := Subgroup.card_le_of_le hle1
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge hle1 h1.symm.le
      have hxle : fixV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers r) := by
        rw [heq]
        exact le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hxle (by rw [hfr, hfx])).symm
  have hdvd : Nat.card ↥(fixV (Subgroup.zpowers r)) ∣ Nat.card ↥(fixV (Subgroup.zpowers r) ⊔
      fixV (Subgroup.zpowers x)) := Subgroup.card_dvd_of_le le_sup_left
  have hge : 8 ≤ Nat.card ↥(fixV (Subgroup.zpowers r) ⊔ fixV (Subgroup.zpowers x)) := by
    rw [hfr] at hlt hdvd
    omega
  have hcardle : 8 ≤ Nat.card ↥(commV A) := hge.trans (Subgroup.card_le_of_le hsup)
  have heq : commV A = perpSub hq (fixV A) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hperp8]; exact hcardle)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hperp8

end Hyperplane

end S153E

end CFSG.Quasithin
