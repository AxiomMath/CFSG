module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Quasithin.SzN31
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_zpowers_eq_one_or_self {A : Type*} [Group A] {t : A} (ht : t * t = 1)
    {b : A} (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two]
    exact ht
  have hmod := zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h, zpow_zero]
  · right; rw [hmod, h, zpow_one]

private theorem w16g_conj_commutator_self_inv {A : Type*} [Group A] {t a : A}
    (htt : t * t = 1) : t * ⁅a, t⁆ * t⁻¹ = ⁅a, t⁆⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have h1 : t * ⁅a, t⁆ * t⁻¹ = t * a * t * a⁻¹ := by
    rw [commutatorElement_def, htinv]
    rw [show t * (a * t * a⁻¹ * t) * t = (t * a * t * a⁻¹) * (t * t) by group]
    rw [htt, mul_one]
  have h2 : ⁅a, t⁆⁻¹ = t * a * t * a⁻¹ := by
    rw [commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, htinv]
    group
  rw [h1, h2]

private theorem w16g_commutator_mul_left {A : Type*} [Group A]
    (hcc : ∀ g h : A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center A)
    {z : A} (hz : z ∈ Subgroup.center A) (w x : A) : ⁅z * x, w⁆ = ⁅x, w⁆ := by
  rw [commutatorElement_def]
  rw [SmD6Grp.comm_mul hcc w z x]
  have hz1 : z * w * z⁻¹ * w⁻¹ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz w).symm
  rw [hz1, one_mul]
  rfl

private theorem w16g_commutator_mul_right {A : Type*} [Group A]
    (hcc : ∀ g h : A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center A)
    {z : A} (hz : z ∈ Subgroup.center A) (w x : A) : ⁅w, z * x⁆ = ⁅w, x⁆ := by
  calc ⁅w, z * x⁆ = (⁅z * x, w⁆)⁻¹ := (commutatorElement_inv (z * x) w).symm
    _ = (⁅x, w⁆)⁻¹ := by rw [w16g_commutator_mul_left hcc hz w x]
    _ = ⁅w, x⁆ := commutatorElement_inv x w

private theorem w16g_commutator_inv_left {A : Type*} [Group A]
    (hcc : ∀ g h : A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center A) (x y : A) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  change x⁻¹ * y * (x⁻¹)⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹
  exact SmD6Grp.comm_inv hcc y x

private theorem w16g_commutator_inv_inv_of_class_two {A : Type*} [Group A]
    (hcc : ∀ g h : A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center A) (x y : A) :
    ⁅x⁻¹, y⁻¹⁆ = ⁅x, y⁆ := by
  have h1 : ⁅y⁻¹, x⁻¹⁆ = ⁅y, x⁻¹⁆⁻¹ := w16g_commutator_inv_left hcc y x⁻¹
  have h2 : ⁅y, x⁻¹⁆ = ⁅x, y⁆ := by
    calc ⁅y, x⁻¹⁆ = ⁅x⁻¹, y⁆⁻¹ := (commutatorElement_inv (x⁻¹) y).symm
      _ = (⁅x, y⁆⁻¹)⁻¹ := by rw [w16g_commutator_inv_left hcc x y]
      _ = ⁅x, y⁆ := inv_inv _
  calc ⁅x⁻¹, y⁻¹⁆ = ⁅y⁻¹, x⁻¹⁆⁻¹ := (commutatorElement_inv (y⁻¹) (x⁻¹)).symm
    _ = (⁅y, x⁻¹⁆⁻¹)⁻¹ := by rw [h1]
    _ = ⁅y, x⁻¹⁆ := inv_inv _
    _ = ⁅x, y⁆ := h2

private theorem w16g_even_of_three_dvd_two_pow_sub_one {a : ℕ} (h : 3 ∣ 2 ^ a - 1) : Even a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases a with _ | _ | a
    · exact ⟨0, rfl⟩
    · norm_num at h
    · have h2 : 2 ^ (a + 2) = 4 * 2 ^ a := by ring
      have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      rw [h2] at h
      have h3 : 3 ∣ 2 ^ a - 1 := by omega
      obtain ⟨m, hm⟩ := ih a (by omega) h3
      exact ⟨m + 1, by omega⟩

theorem w16h_central_of_order_27 {t : MulAut W} (htt : t * t = 1) {P : Subgroup (MulAut W)}
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P)
    (h27 : Nat.card P = 27) (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z := by
  have hnc : ∃ u v : ↥P, u * v ≠ v * u := by
    push Not at hnab
    obtain ⟨u, hu, v, hv, huv⟩ := hnab
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (congrArg Subtype.val h)⟩
  let Q := ↥P
  let Z : Subgroup Q := Subgroup.center Q
  have hZ3 : Nat.card Z = 3 := SmD6Grp.card_center_eq_three h27 hnc
  have hcc : ∀ g h : Q, g * h * g⁻¹ * h⁻¹ ∈ Z := SmD6Grp.commutator_mem_center h27 hnc
  obtain ⟨σ, hσ⟩ := SmD6Grp.exists_conj_hom t hn
  have hσσ : ∀ g : Q, σ (σ g) = g := by
    intro g
    apply Subtype.ext
    rw [hσ, hσ]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
    rw [htinv]
    calc t * (t * (g : MulAut W) * t) * t
        = (t * t) * (g : MulAut W) * (t * t) := by group
      _ = g := by rw [htt]; group
  have hσZ : ∀ z ∈ Z, σ z ∈ Z := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    calc h * σ z = σ (σ h) * σ z := by rw [hσσ]
      _ = σ (σ h * z) := (map_mul σ _ _).symm
      _ = σ (z * σ h) := by rw [Subgroup.mem_center_iff.mp hz (σ h)]
      _ = σ z * σ (σ h) := map_mul σ _ _
      _ = σ z * h := by rw [hσσ]
  have hcomm_le : commutator Q ≤ Z := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _
    simpa [commutatorElement_def] using hcc g h
  haveI : IsMulCommutative (Q ⧸ Z) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
  let σbar : Q ⧸ Z →* Q ⧸ Z := QuotientGroup.map Z Z σ hσZ
  let φ : Q ⧸ Z →* Q ⧸ Z :=
    { toFun := fun q => σbar q * q
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [map_mul]
        ac_rfl }
  let A : Subgroup Q := φ.ker.comap (QuotientGroup.mk' Z)
  have hA_mem : ∀ x : Q, x ∈ A ↔ σ x * x ∈ Z := by
    intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    have hmap : σbar (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (σ x) :=
      QuotientGroup.map_mk Z Z σ hσZ x
    constructor
    · intro h
      have h1 : QuotientGroup.mk' Z (σ x * x) = 1 := by
        calc QuotientGroup.mk' Z (σ x * x)
            = QuotientGroup.mk' Z (σ x) * QuotientGroup.mk' Z x :=
              (map_mul (QuotientGroup.mk' Z) (σ x) x).symm
          _ = σbar (QuotientGroup.mk' Z x) * QuotientGroup.mk' Z x := by rw [hmap]
          _ = φ (QuotientGroup.mk' Z x) := rfl
          _ = 1 := h
      exact (QuotientGroup.eq_one_iff (σ x * x)).mp (by simpa using h1)
    · intro h
      have h1 : QuotientGroup.mk' Z (σ x * x) = 1 := by
        simpa using (QuotientGroup.eq_one_iff (σ x * x)).mpr h
      calc φ (QuotientGroup.mk' Z x)
          = σbar (QuotientGroup.mk' Z x) * QuotientGroup.mk' Z x := rfl
        _ = QuotientGroup.mk' Z (σ x) * QuotientGroup.mk' Z x := by rw [hmap]
        _ = QuotientGroup.mk' Z (σ x * x) := map_mul (QuotientGroup.mk' Z) (σ x) x
        _ = 1 := h1
  have hgen : ⁅P, Subgroup.zpowers t⁆ ≤ A.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hb2
    · rw [hb1]
      simpa using (A.map P.subtype).one_mem
    · rw [hb2]
      have hmem : ⁅a, t⁆ ∈ P := by
        rw [commutatorElement_def]
        simpa only [mul_assoc] using P.mul_mem ha (hn a⁻¹ (P.inv_mem ha))
      refine Subgroup.mem_map.mpr ⟨⟨⁅a, t⁆, hmem⟩, ?_, rfl⟩
      rw [hA_mem]
      have hxinv : σ ⟨⁅a, t⁆, hmem⟩ = (⟨⁅a, t⁆, hmem⟩ : Q)⁻¹ := by
        apply Subtype.ext
        rw [hσ]
        simp only [Subgroup.coe_inv]
        exact w16g_conj_commutator_self_inv htt
      rw [hxinv, inv_mul_cancel]
      exact Z.one_mem
  have hA_le : A.map P.subtype ≤ P := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hPA : P ≤ A.map P.subtype := by
    intro x hx
    exact hgen (by rwa [hc])
  have hA_eq : A.map P.subtype = P := le_antisymm hA_le hPA
  have hstepA : ∀ x : Q, σ x * x ∈ Z := by
    intro x
    have hx : (x : MulAut W) ∈ A.map P.subtype := by rw [hA_eq]; exact x.2
    obtain ⟨y, hyA, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hyA
    exact (hA_mem x).mp hyA
  have hstepB : ∀ x y : Q, σ ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    have hx : σ x * x ∈ Z := hstepA x
    have hy : σ y * y ∈ Z := hstepA y
    have hx' : σ x = (σ x * x) * x⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hy' : σ y = (σ y * y) * y⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [map_commutatorElement, hx', hy']
    rw [w16g_commutator_mul_left hcc hx ((σ y * y) * y⁻¹) x⁻¹]
    rw [w16g_commutator_mul_right hcc hy x⁻¹ y⁻¹]
    exact w16g_commutator_inv_inv_of_class_two hcc x y
  have hcardComm : Nat.card (commutator Q) = 3 := by
    have hdvd : Nat.card (commutator Q) ∣ Nat.card Z := Subgroup.card_dvd_of_le hcomm_le
    have hne : commutator Q ≠ ⊥ := by
      intro hbot
      obtain ⟨u, v, huv⟩ := hnc
      have h1 : ⁅u, v⁆ ∈ commutator Q := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
      rw [hbot] at h1
      exact huv (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1))
    have hne1 : Nat.card (commutator Q) ≠ 1 := fun h1 =>
      hne ((Subgroup.card_eq_one).mp h1)
    rw [hZ3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hZeq : Z = commutator Q :=
    (Subgroup.eq_of_le_of_card_ge hcomm_le (by rw [hZ3, hcardComm])).symm
  let F : Subgroup Q :=
    { carrier := {x | σ x = x}
      one_mem' := map_one σ
      mul_mem' := by
        intro x y hx hy
        change σ (x * y) = x * y
        rw [map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change σ x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have hcommF : commutator Q ≤ F := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _
    exact hstepB g h
  have hσZfix : ∀ z ∈ Z, σ z = z := fun z hz => hcommF (hZeq ▸ hz)
  intro z hzP hzc
  have hzZ : (⟨z, hzP⟩ : Q) ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g.1 g.2)
  have hzfix : σ ⟨z, hzP⟩ = ⟨z, hzP⟩ := hσZfix _ hzZ
  have hval := congrArg Subtype.val hzfix
  rw [hσ] at hval
  exact hval

theorem w16h_even_rk_of_fixedFree (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W} (hz : z ^ 3 = 1)
    {S : Subgroup W}
    (hS : ∀ u ∈ S, z u ∈ S) (hfix : ∀ u ∈ S, z u = u → u = 1) : Even (rk ↥S) := by
  rcases eq_or_ne z 1 with rfl | hz1
  · have hSbot : S = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      simpa using hfix u hu rfl
    rw [hSbot, rk_bot]
    exact ⟨0, rfl⟩
  · have hord : orderOf z = 3 := by
      have hdvd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hY : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hord]
    have hzstab : z ∈ stabSub S := by
      rw [mem_stabSub]
      intro u
      refine ⟨fun hu => ?_, hS u⟩
      have h1 : z (z u) ∈ S := hS (z u) hu
      have h2 : z (z (z u)) ∈ S := hS (z (z u)) h1
      have h3 : z (z (z u)) = u := by
        have hz3u : (z ^ 3) u = u := by rw [hz]; rfl
        simpa [pow_succ, MulAut.mul_apply] using hz3u
      rwa [h3] at h2
    have hF : ∀ g ∈ Subgroup.zpowers z, ∀ f ∈ S, g f ∈ S := by
      intro g hg f hf
      exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr hzstab hg) f).mpr hf
    have hfixY : S ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_inf, mem_fixV] at hu
      rw [Subgroup.mem_bot]
      exact hfix u hu.1 (hu.2 z (Subgroup.mem_zpowers z))
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card S - 1 := prime_dvd_card_sub_one hY hF hfixY
    rw [card_eq_two_pow hW S] at h3
    exact w16g_even_of_three_dvd_two_pow_sub_one h3

theorem w16h_acts_trivially_of_comm_eq_self {t : MulAut W} (htt : t * t = 1)
    {P : Subgroup (MulAut W)} (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P)
    {S : Subgroup W} (hSP : ∀ x ∈ P, ∀ u ∈ S, x u ∈ S) (hSt : ∀ u ∈ S, t u ∈ S)
    (ht : ∀ u : W, t u * u⁻¹ ∈ S) : ∀ x ∈ P, ∀ u : W, x u * u⁻¹ ∈ S := by
  let A : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ P ∧ ∀ u : W, x u * u⁻¹ ∈ S}
      one_mem' := ⟨P.one_mem, by intro u; simp⟩
      mul_mem' := by
        intro x y hx hy
        refine ⟨P.mul_mem hx.1 hy.1, fun u => ?_⟩
        have h1 : x (y u) * (y u)⁻¹ ∈ S := hx.2 (y u)
        have h2 : y u * u⁻¹ ∈ S := hy.2 u
        have hkey : (x * y) u * u⁻¹ = (x (y u) * (y u)⁻¹) * (y u * u⁻¹) := by
          simp only [MulAut.mul_apply]; group
        rw [hkey]
        exact S.mul_mem h1 h2
      inv_mem' := by
        intro x hx
        refine ⟨P.inv_mem hx.1, fun u => ?_⟩
        have h1 : x (x⁻¹ u) * (x⁻¹ u)⁻¹ ∈ S := hx.2 (x⁻¹ u)
        have h2 : x (x⁻¹ u) * (x⁻¹ u)⁻¹ = u * (x⁻¹ u)⁻¹ := by simp
        rw [h2] at h1
        have h3 : x⁻¹ u * u⁻¹ = (u * (x⁻¹ u)⁻¹)⁻¹ := by group
        rw [h3]
        exact S.inv_mem h1 }
  have hgen : ⁅P, Subgroup.zpowers t⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hb2
    · rw [hb1]
      simpa using A.one_mem
    · rw [hb2]
      have hmem : ⁅a, t⁆ ∈ P := by
        rw [commutatorElement_def]
        simpa only [mul_assoc] using P.mul_mem ha (hn a⁻¹ (P.inv_mem ha))
      refine ⟨hmem, fun u => ?_⟩
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
      set w : W := a⁻¹ (t u) with hw
      have hw1 : a w = t u := by simp [hw]
      have hs1 : t w * w⁻¹ ∈ S := ht w
      have htw : t w = w * (t w * w⁻¹) := by
        rw [← mul_assoc, mul_comm w (t w), mul_assoc, mul_inv_cancel, mul_one]
      have hkey : ⁅a, t⁆ u * u⁻¹ = (t u * u⁻¹) * a (t w * w⁻¹) := by
        rw [commutatorElement_def, htinv]
        change a (t (a⁻¹ (t u))) * u⁻¹ = (t u * u⁻¹) * a (t w * w⁻¹)
        rw [← hw]
        conv_lhs => rw [htw, map_mul, hw1]
        ac_rfl
      rw [hkey]
      exact S.mul_mem (ht u) (hSP a ha (t w * w⁻¹) hs1)
  have hPA : P ≤ A := hc ▸ hgen
  intro x hx u
  exact (hPA hx).2 u

end CFSG.LocalAnalysis.WeakClosure81
