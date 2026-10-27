module

public import CFSG.RankThree.PartOne.S12.Sec136
import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.InvolAbelian
public import CFSG.RankThree.PartOne.S12.ZStarStep

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

namespace Sec1322

theorem reflectionGroup_le_torusWeyl {p : ℕ} {E : Subgroup G}
    (h : ∀ t ∈ reflectionSet p E, t ∈ torusWeyl E) : reflectionGroup p E ≤ torusWeyl E :=
  (Subgroup.closure_le _).2 h

theorem reflectionSet_subset_torusWeyl {p : ℕ} {E : Subgroup G} :
    ∀ t ∈ reflectionSet p E, t ∈ torusWeyl E := by
  rintro t ⟨-, X, -, htX⟩
  exact Sec127.torusImage_le_torusWeyl E X htX

theorem reflectionGroup_le {p : ℕ} (E : Subgroup G) : reflectionGroup p E ≤ torusWeyl E :=
  reflectionGroup_le_torusWeyl reflectionSet_subset_torusWeyl

theorem exists_lift {E : Subgroup G} {g : MulAut E} (hg : g ∈ torusWeyl E) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), conjAut E w hw = g := by
  obtain ⟨⟨w, hw⟩, h⟩ := MonoidHom.mem_range.mp hg
  exact ⟨w, hw, h⟩

variable [Finite G]

theorem conj_mem_reflectionGroup {p : ℕ} (hp : p.Prime) {E : Subgroup G} {g x : MulAut E}
    (hg : g ∈ torusWeyl E) (hx : x ∈ reflectionGroup p E) :
    g * x * g⁻¹ ∈ reflectionGroup p E := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ reflectionGroup p E)
    (fun t ht => by
      obtain ⟨w, hw, rfl⟩ := exists_lift hg
      exact Subgroup.subset_closure (conj_mem_reflectionSet hp ht hw)) ?_ ?_ ?_ hx
  · simp
  · intro a b _ _ ha hb
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact (reflectionGroup p E).mul_mem ha hb
  · intro a _ ha
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact (reflectionGroup p E).inv_mem ha

theorem inverts_of_central {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) {z : MulAut E}
    (hzX : z ∈ reflectionGroup p E) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : ∀ y ∈ reflectionGroup p E, y * z = z * y)
    (huniq : ∀ y ∈ reflectionGroup p E, y * y = 1 → y ≠ 1 →
      (∀ x ∈ reflectionGroup p E, x * y = y * x) → y = z) :
    ∀ e : E, z e = e⁻¹ := by
  classical
  have hp := h.prime
  have hinv : torusInvariant E ⊤ (autFixedInG E z) := by
    intro w hw b hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
    have hg : conjAut E w hwN ∈ torusWeyl E := ⟨⟨w, hwN⟩, rfl⟩
    have hg' : (conjAut E w hwN)⁻¹ ∈ torusWeyl E := (torusWeyl E).inv_mem hg
    set g := conjAut E w hwN with hgdef
    have hgz : g * z * g⁻¹ ∈ reflectionGroup p E := conj_mem_reflectionGroup hp hg hzX
    have hconj : g * z * g⁻¹ = z := by
      refine huniq _ hgz ?_ ?_ ?_
      · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
          _ = 1 := by rw [hz2]; group
      · intro h1
        apply hz1
        have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
        rw [this, h1]
        group
      · intro x hx
        have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ reflectionGroup p E := conj_mem_reflectionGroup hp hg' hx
        have h2 := hcen _ hx'
        calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by
            rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, h2]
          _ = g * z * g⁻¹ * x := by group
    have hfix : autFixedInG E z = conjBy w (autFixedInG E z) := by
      have := Equivariance.autFixedInG_conj z hwN
      rw [hconj] at this
      exact this
    rw [hfix]
    exact Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hb
  have hle : autFixedInG E z ≤ E := Subgroup.map_subtype_le _
  rcases hF13.irreducible _ hle hinv with hbot | htop
  · intro e
    have hzz : z (z e) = e := by simpa using congrArg (fun m : MulAut E => m e) hz2
    have hmem : ((e * z e : E) : G) ∈ autFixedInG E z := by
      rw [mem_autFixedInG_iff_apply]
      rw [map_mul, hzz]
      exact h.E_elem.is_comm.comm (z e) e
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : e * z e = 1 := Subtype.ext hmem
    exact eq_inv_of_mul_eq_one_right h1
  · exfalso
    apply hz1
    refine MulEquiv.ext fun x => ?_
    have hx : (x : G) ∈ autFixedInG E z := by rw [htop]; exact x.2
    rw [mem_autFixedInG_iff_apply] at hx
    simpa using hx

omit [Finite G] in
theorem exactly_one_eq_prime {p a b : ℕ} (hp : p.Prime) (hab : a * b = p ^ 3) (ha : a ≠ 1)
    (hb : b ≠ 1) : a = p ↔ ¬ b = p := by
  have hdvda : a ∣ p ^ 3 := ⟨b, hab.symm⟩
  have hdvdb : b ∣ p ^ 3 := ⟨a, by rw [← hab, mul_comm]⟩
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvda
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvdb
  rw [← pow_add] at hab
  have hij : i + j = 3 := Nat.pow_right_injective hp.two_le hab
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact ha (pow_zero _)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hb (pow_zero _)
  have hp2 : p ^ 2 ≠ p := by
    intro h2
    have := hp.two_le
    nlinarith
  have : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [pow_one, true_iff]
    exact hp2
  · simp only [pow_one, not_true_eq_false, iff_false]
    exact hp2

theorem reflection_dichotomy {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcardE : Nat.card E = p ^ 3) {z : MulAut E}
    (hz : ∀ e : E, z e = e⁻¹) {x : MulAut E} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    IsAutReflection p E x ↔ ¬ IsAutReflection p E (z * x) := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  have hzz : z * z = 1 := by
    refine MulEquiv.ext fun e => ?_
    show z (z e) = e
    rw [hz, hz, inv_inv]
  have hxz' : x * z = z * x := by
    refine MulEquiv.ext fun e => ?_
    show x (z e) = z (x e)
    rw [hz, hz, map_inv]
  have hy2 : (z * x) * (z * x) = 1 := by
    calc z * x * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [hxz']
      _ = (z * z) * (x * x) := by group
      _ = 1 := by rw [hzz, hx2, one_mul]
  have hy1 : z * x ≠ 1 := by
    intro h1
    apply hxz
    have h3 : x = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h3]
    exact inv_eq_of_mul_eq_one_right hzz
  let _inst : CommGroup ↥E := commGroupOf hEc
  have hpow : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h y.2)
  have hrefl : ∀ σ : MulAut ↥E, σ * σ = 1 → σ ≠ 1 →
      (IsAutReflection p E σ ↔ Nat.card (Invol.invS σ) = p) := by
    intro σ hσ2 hσ1
    have hmv : autMoved E σ = Invol.invS σ := Invol.movedS_eq_invS hp hp2 hpow hσ2
    constructor
    · rintro ⟨-, hc⟩
      rwa [hmv] at hc
    · intro hc
      refine ⟨?_, by rwa [hmv]⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hinv : Invol.invS (z * x) = Invol.fixS x := by
    ext e
    show (z * x) e = e⁻¹ ↔ x e = e
    show z (x e) = e⁻¹ ↔ x e = e
    rw [hz, inv_inj]
  have hcard := Invol.card_eq_mul hp hp2 hpow hx2
  rw [hcardE] at hcard
  have hinvne : Invol.invS x ≠ ⊥ := by
    intro hbot
    apply hx1
    refine MulEquiv.ext fun e => ?_
    have hm : x e * e⁻¹ ∈ Invol.movedS x := Subgroup.subset_closure ⟨e, rfl⟩
    rw [Invol.movedS_eq_invS hp hp2 hpow hx2, hbot, Subgroup.mem_bot] at hm
    exact mul_inv_eq_one.1 hm
  have hfixne : Invol.fixS x ≠ ⊥ := by
    intro hbot
    apply hxz
    refine MulEquiv.ext fun e => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Invol.exists_mul_of_involution hp hp2 hpow hx2 e
    rw [hbot, Subgroup.mem_bot] at ha
    subst ha
    rw [one_mul, (hb : x b = b⁻¹), hz]
  rw [hrefl x hx2 hx1, hrefl (z * x) hy2 hy1, hinv]
  exact exactly_one_eq_prime hp (by rw [mul_comm]; exact hcard.symm)
    (fun h1 => hinvne (Subgroup.card_eq_one.1 h1)) (fun h1 => hfixne (Subgroup.card_eq_one.1 h1))

theorem not_isAutReflection_of_inverts {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcardE : Nat.card E = p ^ 3) {z : MulAut E}
    (hz : ∀ e : E, z e = e⁻¹) : ¬ IsAutReflection p E z := by
  rintro ⟨-, hc⟩
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  have hzz : z * z = 1 := by
    refine MulEquiv.ext fun e => ?_
    show z (z e) = e
    rw [hz, hz, inv_inv]
  let _inst : CommGroup ↥E := commGroupOf hEc
  have hpow : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h y.2)
  have hmv : autMoved E z = Invol.invS z := Invol.movedS_eq_invS hp hp2 hpow hzz
  have htop : Invol.invS z = ⊤ := eq_top_iff.2 fun e _ => hz e
  rw [hmv, htop, Subgroup.card_top, hcardE] at hc
  have h2 := hp.two_le
  have h3 : p * p * p = p := by
    calc p * p * p = p ^ 3 := by ring
      _ = p := hc
  nlinarith

end Sec1322

end CFSG.RankThree.PartOne
