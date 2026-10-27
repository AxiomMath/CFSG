module

public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.KC.PlaneLifting
import CFSG.RankThree.GroupTheory.SteinbergCEAschbacherGeneratedCores
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Sec12Two

section Basic

variable {G : Type*} [Group G]

theorem commute_of_mem_normalizer_zpowers {p : ℕ} (hp : p.Prime) {c x : G}
    (hc : orderOf c = p) (hx : x ^ p = 1)
    (hn : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : x * c = c * x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, x * c * x⁻¹ = c ^ j := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hn c).mp (Subgroup.mem_zpowers c))
    exact ⟨j, hj.symm⟩
  have hit : ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = c ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * c ^ (j ^ n) * x⁻¹ := by rw [ih]
        _ = (x * c * x⁻¹) ^ (j ^ n) := conj_zpow.symm
        _ = c ^ (j ^ (n + 1)) := by rw [hj, ← zpow_mul, pow_succ, mul_comm]
  have h1 : c ^ (j ^ p - 1) = 1 := by
    have := hit p
    rw [hx] at this
    rw [zpow_sub, zpow_one, ← this]
    simp
  have h2 : (p : ℤ) ∣ j ^ p - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j ^ p - 1)).mpr h1
    rwa [hc] at this
  have h3 : ((j : ZMod p)) = 1 := by
    have h4 : (((j ^ p - 1 : ℤ)) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
    push_cast at h4
    rw [ZMod.pow_card] at h4
    exact sub_eq_zero.mp h4
  have h5 : (p : ℤ) ∣ j - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h3, sub_self]
  have h6 : c ^ (j - 1) = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j - 1)).mp (by rwa [hc])
  have h7 : x * c * x⁻¹ = c := by
    rw [hj]
    have : c ^ j = c ^ (j - 1) * c := by rw [← zpow_add_one]; simp
    rw [this, h6, one_mul]
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [h7]

theorem commutatorElement_mul_mul_of_commute {u v x y : G} (hux : Commute u x) (huy : Commute u y)
    (hvx : Commute v x) (hvy : Commute v y) (huv : Commute u v) :
    ⁅u * x, v * y⁆ = ⁅x, y⁆ := by
  have e1 : u * x * (v * y) = (u * v) * (x * y) := by
    calc u * x * (v * y) = u * (x * v) * y := by group
      _ = u * (v * x) * y := by rw [hvx.eq]
      _ = u * v * (x * y) := by group
  have e2 : v * y * (u * x) = (u * v) * (y * x) := by
    calc v * y * (u * x) = v * (y * u) * x := by group
      _ = v * (u * y) * x := by rw [huy.eq]
      _ = (v * u) * (y * x) := by group
      _ = u * v * (y * x) := by rw [huv.symm.eq]
  have hx : Commute (u * v) x := hux.mul_left hvx
  have hy : Commute (u * v) y := huy.mul_left hvy
  have hW : Commute (u * v) (x * y * (y * x)⁻¹) :=
    (hx.mul_right hy).mul_right (hy.mul_right hx).inv_right
  calc ⁅u * x, v * y⁆ = (u * x * (v * y)) * (v * y * (u * x))⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = (u * v) * (x * y * (y * x)⁻¹) * (u * v)⁻¹ := by
        rw [e1, e2, mul_inv_rev]; group
    _ = x * y * (y * x)⁻¹ := hW.mul_inv_cancel
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def, mul_inv_rev]; group

theorem mem_centralizer_of_comm_mem_centralizer {L : Subgroup G} (hL : ⁅L, L⁆ = L) {z : G}
    (hz : z ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    z ∈ Subgroup.centralizer (L : Set G) := by
  have hcomm : ⁅L, L⁆ ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hu₁ := h g₁ hg₁
    have hu₂ := h g₂ hg₂
    have hu₂L : z * g₂ * z⁻¹ * g₂⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hz g₂).mp hg₂) (L.inv_mem hg₂)
    have c11 : Commute (z * g₁ * z⁻¹ * g₁⁻¹) g₁ :=
      (Subgroup.mem_centralizer_iff.mp hu₁ g₁ hg₁).symm
    have c12 : Commute (z * g₁ * z⁻¹ * g₁⁻¹) g₂ :=
      (Subgroup.mem_centralizer_iff.mp hu₁ g₂ hg₂).symm
    have c21 : Commute (z * g₂ * z⁻¹ * g₂⁻¹) g₁ :=
      (Subgroup.mem_centralizer_iff.mp hu₂ g₁ hg₁).symm
    have c22 : Commute (z * g₂ * z⁻¹ * g₂⁻¹) g₂ :=
      (Subgroup.mem_centralizer_iff.mp hu₂ g₂ hg₂).symm
    have c12' : Commute (z * g₁ * z⁻¹ * g₁⁻¹) (z * g₂ * z⁻¹ * g₂⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hu₁ _ hu₂L).symm
    have key := commutatorElement_mul_mul_of_commute c11 c12 c21 c22 c12'
    have e1 : z * g₁ * z⁻¹ * g₁⁻¹ * g₁ = z * g₁ * z⁻¹ := by group
    have e2 : z * g₂ * z⁻¹ * g₂⁻¹ * g₂ = z * g₂ * z⁻¹ := by group
    rw [e1, e2] at key
    have hconj : z * ⁅g₁, g₂⁆ * z⁻¹ = ⁅z * g₁ * z⁻¹, z * g₂ * z⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have : z * ⁅g₁, g₂⁆ * z⁻¹ = ⁅g₁, g₂⁆ := hconj.trans key
    have final : z * ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆ * z :=
      calc z * ⁅g₁, g₂⁆ = z * ⁅g₁, g₂⁆ * z⁻¹ * z := by group
        _ = ⁅g₁, g₂⁆ * z := by rw [this]
    exact final.symm
  have hle : L ≤ Subgroup.centralizer ({z} : Set G) := hL ▸ hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)

theorem eq_one_of_mem_center_of_pow_eq_one {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) {x : G} (hxL : x ∈ L)
    (hxc : x ∈ Subgroup.centralizer (L : Set G)) (hx : x ^ p = 1) : x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hord : orderOf x = p := orderOf_eq_prime hx hne
  have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc g g.2)
  have hdvd := orderOf_dvd_natCard (⟨⟨x, hxL⟩, hmem⟩ : Subgroup.center L)
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord] at hdvd
  exact hZ hdvd

theorem conj_eq_of_mul_eq {q z a n : G} (haz : a = q * z) (hzn : z * n = n * z) :
    a * n * a⁻¹ = q * n * q⁻¹ := by
  subst haz
  calc q * z * n * (q * z)⁻¹ = q * (z * n * z⁻¹) * q⁻¹ := by group
    _ = q * n * q⁻¹ := by rw [hzn]; group

theorem comm_of_conj_eq {x g : G} (h : x * g * x⁻¹ = g) : g * x = x * g :=
  calc g * x = (x * g * x⁻¹) * x := by rw [h]
    _ = x * g := by group

theorem isElementaryAbelian_range {R : Type*} [Group R] {p : ℕ}
    [hR : IsElementaryAbelian p R] (f : R →* G) : IsElementaryAbelian p f.range := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm' x y]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨x, hx⟩ := a.2
    apply Subtype.ext
    change (a : G) ^ p = 1
    rw [← hx, ← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hR.exponent_dvd_p x,
      map_one]

theorem mem_ker_conjAction_iff {A L : Subgroup G} (α : ↥A →* MulAut ↥L)
    (hα : ∀ (a : A) (l : L), ((α a l : L) : G) = (a : G) * l * (a : G)⁻¹) (a : A) :
    a ∈ α.ker ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : L) : G)) h
    simp only [hα, MulAut.one_apply] at h1
    calc l * (a : G) = ((a : G) * l * (a : G)⁻¹) * a := by rw [h1]
      _ = (a : G) * l := by group
  · intro h
    ext l
    rw [hα, MulAut.one_apply, show (a : G) * l * (a : G)⁻¹ = l by
      rw [← h l l.2]; group]

end Basic

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem theta_le_inf_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hL : CFSG.IsQuasisimple L) :
    inSubgroup (aschbacherSolvableCore p) L ≤ L ⊓ Subgroup.centralizer (L : Set G) := by
  have hsolv : Group.IsSolvable (aschbacherSolvableCore p L) :=
    (solvable_prime_complement_core_characterization (H := L) hp).1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL
    (inferInstance : (aschbacherSolvableCore p L).Normal) with htop | hcen
  · exfalso
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL
    have hs : Group.IsSolvable L := by
      rw [htop] at hsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom) (MulEquiv.injective _)
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial L
    have hperf : commutator L = ⊤ := by
      have := hL.1
      rwa [Group.isPerfect_def] at this
    exact absurd hperf hlt.ne
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp (hcen hy) ⟨g, hg⟩
    simpa using congrArg Subtype.val this

theorem mem_zpowers_of_mem_zpowers_ne_one {p : ℕ} (hp : p.Prime) {w y : G} (hw : w ^ p = 1)
    (hy : y ∈ Subgroup.zpowers w) (hy1 : y ≠ 1) : w ∈ Subgroup.zpowers y := by
  have : Fact p.Prime := ⟨hp⟩
  have hw1 : w ≠ 1 := by
    rintro rfl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hy1 (by rw [← hk, one_zpow])
  have hwo : orderOf w = p := orderOf_eq_prime hw hw1
  have hyp : y ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers w := Subgroup.zpowers_le.mpr hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers w := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hyo]
  rw [heq]
  exact Subgroup.mem_zpowers w

theorem inf_zpowers_eq_bot {p : ℕ} (hp : p.Prime) {w : G} (hw : w ^ p = 1) {P : Subgroup G}
    (hwP : w ∉ P) : P ⊓ Subgroup.zpowers w = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyP, hyw⟩
  by_contra hy1
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; exact Subgroup.one_mem _)
  have := mem_zpowers_of_mem_zpowers_ne_one hp hw hyw hy1'
  exact hwP ((Subgroup.zpowers_le).mpr hyP this)

theorem le_pRank_of_commute_of_inf_eq_bot {p : ℕ} (hp : p.Prime) {P Q H : Subgroup G}
    (hP : CFSG.Assembly.IsElemAbelian p P) (hQ : CFSG.Assembly.IsElemAbelian p Q)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, Commute x y) (hPQ : P ⊓ Q = ⊥) {a b : ℕ}
    (ha : Nat.card P = p ^ a) (hb : Nat.card Q = p ^ b) (hPH : P ≤ H) (hQH : Q ≤ H) :
    a + b ≤ CFSG.Assembly.pRank p H := by
  have hPc := hP.1
  have hQc := hQ.1
  have hc : ∀ (x : P) (y : Q), Commute (P.subtype x) (Q.subtype y) := fun x y =>
    hcomm x x.2 y y.2
  let f : P × Q →* G := MonoidHom.noncommCoprod P.subtype Q.subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hyP : (y : G) ∈ P := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact P.inv_mem x.2
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ P ⊓ Q := ⟨hyP, y.2⟩
      rw [hPQ, Subgroup.mem_bot] at this
      exact this
    rw [hy1, mul_one] at hxy'
    have hx1 : x = 1 := Subtype.ext hxy'
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hx1, hy1']
    rfl
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := P × Q) ?_ ?_ ?_ f hf ?_
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    exact Prod.ext (mul_comm' x₁ x₂) (mul_comm' y₁ y₂)
  · rintro ⟨x, y⟩
    exact Prod.ext (Subtype.ext (hP.2 x x.2)) (Subtype.ext (hQ.2 y y.2))
  · rw [Nat.card_prod, ha, hb, pow_add]
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact H.mul_mem (hPH x.2) (hQH y.2)

theorem pRank_le_localRank_of_isTwoLocal {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsTwoLocal H) : CFSG.Assembly.pRank p H ≤ localRank p G :=
  CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp H hH

theorem exists_isTwoLocal_pRank_eq_localRank {p : ℕ} (hp : p.Prime) (hpos : 0 < localRank p G) :
    ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Assembly.pRank p H = localRank p G :=
  CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained p hp G hpos

theorem pRank_le_evenRank_of_isTwoLocal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : IsTwoLocal H) : CFSG.Assembly.pRank p H ≤ evenRank G :=
  CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 H hH

theorem localRank_add_le_evenRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M P : Subgroup G}
    (hpos : 0 < localRank p ↥M) (hP : CFSG.Assembly.IsElemAbelian p P)
    (hPM : P ≤ Subgroup.centralizer (M : Set G)) (hdisj : P ⊓ M = ⊥) {k : ℕ}
    (hk : Nat.card P = p ^ k) : localRank p ↥M + k ≤ evenRank G := by
  obtain ⟨H', ⟨S', hS'1, hS'2, rfl⟩, hrk⟩ := exists_isTwoLocal_pRank_eq_localRank hp hpos
  obtain ⟨E', hE'H, hE', hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (S' : Set ↥M))
  have hE'card' : Nat.card E' = p ^ localRank p ↥M := by
    rw [← hrk]
    exact hE'card
  set S : Subgroup G := S'.map M.subtype with hS
  set E : Subgroup G := E'.map M.subtype with hE
  have hSne : S ≠ ⊥ := fun h =>
    hS'1 ((Subgroup.map_eq_bot_iff_of_injective S' M.subtype_injective).mp h)
  have hS2 : IsPGroup 2 S := hS'2.map _
  have hEM : E ≤ M := Subgroup.map_subtype_le _
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hEN : E ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.map_mono hE'H).trans (Subgroup.le_normalizer_map M.subtype)
  have hEel : CFSG.Assembly.IsElemAbelian p E := CFSG.SectionRank.isElemAbelian_map hE' _
  have hEcard : Nat.card E = p ^ localRank p ↥M := by
    rw [hE, Subgroup.card_map_of_injective M.subtype_injective, hE'card']
  have hPN : P ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSM)
      (hPM hx))
  have hPEbot : P ⊓ E = ⊥ := eq_bot_iff.mpr (hdisj ▸ inf_le_inf_left P hEM)
  have hcomm : ∀ x ∈ P, ∀ y ∈ E, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hPM hx) y (hEM hy)).symm
  have hloc : IsTwoLocal (Subgroup.normalizer (S : Set G)) := ⟨S, hSne, hS2, rfl⟩
  have h1 := le_pRank_of_commute_of_inf_eq_bot hp hP hEel hcomm hPEbot hk hEcard hPN hEN
  have h2 := pRank_le_evenRank_of_isTwoLocal hp hp2 hloc
  omega

end Rank

section Setup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem orderOf_c (h : Sec12Hyp G p A c L E) : orderOf c = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : IsElementaryAbelian p A := h.A_elem
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c h.c_mem)
    h.c_ne_one

theorem c_pow_eq_one (h : Sec12Hyp G p A c L E) : c ^ p = 1 := by
  have : IsElementaryAbelian p A := h.A_elem
  exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c h.c_mem

theorem L_le_centralizer_c (h : Sec12Hyp G p A c L E) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  (mem_thetaComponentsAt_iff.mp h.L_mem.2).1

theorem c_mem_centralizer_L (h : Sec12Hyp G p A c L E) :
    c ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (L_le_centralizer_c h hl)

theorem L_mem_zeroStar (h : Sec12Hyp G p A c L E) : L ∈ sectionTenZeroStar p A := h.L_mem.1.1

theorem thetaQuotientCentralizer_eq_zpowers (h : Sec12Hyp G p A c L E)
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L)) :
    thetaQuotientCentralizer p A L = Subgroup.zpowers c := by
  have : IsElementaryAbelian p A := h.A_elem
  have hcK : c ∈ thetaQuotientCentralizer p A L := by
    refine mem_thetaQuotientCentralizer_iff.mpr ⟨h.c_mem,
      Subgroup.centralizer_le_normalizer _ (c_mem_centralizer_L h), fun k hk => ?_⟩
    have hkc : k * c = c * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (L_le_centralizer_c h hk)
    rw [show c * k * c⁻¹ * k⁻¹ = 1 by rw [← hkc]; group]
    exact Subgroup.one_mem _
  have hle : Subgroup.zpowers c ≤ thetaQuotientCentralizer p A L := (Subgroup.zpowers_le).mpr hcK
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_c h]
  have hexp : Monoid.exponent ↥(thetaQuotientCentralizer p A L) ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    have hxA : (x : G) ∈ A := (inf_le_left : thetaQuotientCentralizer p A L ≤ A) x.2
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (x : G) hxA
  rw [← hcyc.exponent_eq_card]
  exact Nat.le_of_dvd h.prime.pos hexp

theorem inf_centralizer_eq_zpowers (h : Sec12Hyp G p A c L E)
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L)) :
    A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
  refine le_antisymm (fun a ha => ?_) (le_inf ((Subgroup.zpowers_le).mpr h.c_mem)
    ((Subgroup.zpowers_le).mpr (c_mem_centralizer_L h)))
  rw [← thetaQuotientCentralizer_eq_zpowers h hcyc]
  refine mem_thetaQuotientCentralizer_iff.mpr ⟨ha.1,
    Subgroup.centralizer_le_normalizer _ ha.2, fun k hk => ?_⟩
  have hka : k * a = a * k := Subgroup.mem_centralizer_iff.mp ha.2 k hk
  rw [show a * k * a⁻¹ * k⁻¹ = 1 by rw [← hka]; group]
  exact Subgroup.one_mem _

theorem exists_inv_mul_mem_centralizer (h : Sec12Hyp G p A c L E) (hqs : CFSG.IsQuasisimple L)
    {a : G} (ha : a ∈ A) :
    ∃ q ∈ L, q⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨-, hAL, hact⟩ := mem_sectionTenOne_iff.mp h.L_mem.1.2
  obtain ⟨q, hq⟩ := hact ⟨a, ha⟩
  obtain ⟨q₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hqs.1
  have hθ := theta_le_inf_centralizer h.prime hqs
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hAL ha
  have key : ∀ l ∈ L, ∃ t ∈ Subgroup.centralizer (L : Set G),
      a * l * a⁻¹ = q₀ * l * (q₀ : G)⁻¹ * t⁻¹ := by
    intro l hl
    have h1 := congrArg (fun φ => φ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore p L)) hq
    have h2 : ((L.normalizerMonoidHom (Subgroup.inclusion hAL ⟨a, ha⟩) ⟨l, hl⟩ : L) :
        L ⧸ aschbacherSolvableCore p L) =
        ((q₀ * ⟨l, hl⟩ * q₀⁻¹ : L) : L ⧸ aschbacherSolvableCore p L) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h1
    rw [QuotientGroup.eq] at h2
    have h3 := Subgroup.mem_map_of_mem L.subtype h2
    have h4 : (L.subtype ((L.normalizerMonoidHom (Subgroup.inclusion hAL ⟨a, ha⟩) ⟨l, hl⟩)⁻¹ *
        (q₀ * ⟨l, hl⟩ * q₀⁻¹)) : G) = (a * l * a⁻¹)⁻¹ * (q₀ * l * (q₀ : G)⁻¹) := by
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [h4] at h3
    refine ⟨(a * l * a⁻¹)⁻¹ * (q₀ * l * (q₀ : G)⁻¹), (hθ h3).2, ?_⟩
    group
  refine ⟨q₀, q₀.2, mem_centralizer_of_comm_mem_centralizer hperf ?_ ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer q₀.2)) haN
  · intro l hl
    obtain ⟨t, ht, hal⟩ := key l hl
    have e : (q₀ : G)⁻¹ * a * l * ((q₀ : G)⁻¹ * a)⁻¹ * l⁻¹ =
        (l * (q₀ : G)⁻¹) * t⁻¹ * (l * (q₀ : G)⁻¹)⁻¹ := by
      have : (q₀ : G)⁻¹ * a * l * ((q₀ : G)⁻¹ * a)⁻¹ * l⁻¹ =
          (q₀ : G)⁻¹ * (a * l * a⁻¹) * q₀ * l⁻¹ := by group
      rw [this, hal]
      group
    have hcomm : (l * (q₀ : G)⁻¹) * t⁻¹ = t⁻¹ * (l * (q₀ : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ ht) _ (L.mul_mem hl (L.inv_mem q₀.2))
    rw [e, hcomm, mul_inv_cancel_right]
    exact Subgroup.inv_mem _ ht

theorem card_range_conjAction (h : Sec12Hyp G p A c L E)
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L)) (α : ↥A →* MulAut ↥L)
    (hα : ∀ (a : A) (l : L), ((α a l : L) : G) = (a : G) * l * (a : G)⁻¹) :
    Nat.card α.range = p ^ 2 := by
  have hker : α.ker = (Subgroup.zpowers c).subgroupOf A := by
    ext a
    rw [mem_ker_conjAction_iff α hα, Subgroup.mem_subgroupOf,
      ← inf_centralizer_eq_zpowers h hcyc, Subgroup.mem_inf]
    exact ⟨fun hc => ⟨a.2, hc⟩, fun hc => hc.2⟩
  have hkercard : Nat.card α.ker = p := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).mpr h.c_mem)).toEquiv, Nat.card_zpowers, orderOf_c h]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv, hkercard, h.A_card] at h1
  have h2 : Nat.card α.range * p = p ^ 2 * p := by rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_right h.prime.pos h2

theorem two_le_localRank (h : Sec12Hyp G p A c L E) (hqs : CFSG.IsQuasisimple L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) : 2 ≤ localRank p ↥L := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p A := h.A_elem
  obtain ⟨S, hSL, hS1, hS2, hAS, -⟩ := h.L_mem.1.1.1.2
  set S' : Subgroup ↥L := S.subgroupOf L with hS'
  have hS'1 : S' ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [← Subgroup.map_subgroupOf_eq_of_le hSL, ← hS', hbot, Subgroup.map_bot]
  have hS'2 : IsPGroup 2 S' := hS2.comap_subtype
  set H : Subgroup ↥L := Subgroup.normalizer (S' : Set ↥L) with hH
  have hHloc : IsTwoLocal H := ⟨S', hS'1, hS'2, rfl⟩
  let ρ : ↥H →* MulAut ↥L := MulAut.conj.comp H.subtype
  let α : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ (a : A) (l : L), ((α a l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun a l => by
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hρ : ∀ (x : H) (l : L), ((ρ x l : L) : G) = ((x : L) : G) * l * ((x : L) : G)⁻¹ :=
    fun x l => by simp [ρ]
  have hker : ¬ p ∣ Nat.card ρ.ker := by
    intro hdvd
    apply hZ
    refine hdvd.trans ?_
    have hle : ρ.ker.map H.subtype ≤ Subgroup.center ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ g : L) : G)) (MonoidHom.mem_ker.mp hx)
      simp only [hρ, MulAut.one_apply] at h1
      exact Subtype.ext (comm_of_conj_eq h1)
    have hinj : Nat.card (ρ.ker.map H.subtype) = Nat.card ρ.ker :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← hinj]
    exact Subgroup.card_dvd_of_le hle
  have hrange : α.range ≤ ρ.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨q, hq, hz⟩ := exists_inv_mul_mem_centralizer h hqs a.2
    have hqH : (⟨q, hq⟩ : L) ∈ H := by
      rw [hH, Subgroup.mem_normalizer_iff]
      intro n
      have hn := Subgroup.mem_normalizer_iff.mp (hAS a.2) (n : G)
      have e : (a : G) * n * (a : G)⁻¹ = q * n * (q : G)⁻¹ :=
        conj_eq_of_mul_eq (z := (q : G)⁻¹ * a) (by group)
          (Subgroup.mem_centralizer_iff.mp hz n n.2).symm
      rw [hS', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      change (n : G) ∈ S ↔ q * n * (q : G)⁻¹ ∈ S
      rw [← e]
      exact hn
    refine ⟨⟨⟨q, hq⟩, hqH⟩, ?_⟩
    ext l
    rw [hρ, hα]
    show (q : G) * l * (q : G)⁻¹ = (a : G) * l * (a : G)⁻¹
    exact (conj_eq_of_mul_eq (z := (q : G)⁻¹ * a) (by group)
      (Subgroup.mem_centralizer_iff.mp hz l l.2).symm).symm
  have hEel : IsElementaryAbelian p α.range := isElementaryAbelian_range α
  obtain ⟨E₀, hE₀, hE₀card, -⟩ := exists_lift_elementaryAbelian ρ hp hker α.range hrange
    (card_range_conjAction h hcyc α hα)
  have hE₁ : IsElementaryAbelian p (E₀.map H.subtype) := IsElementaryAbelian.map_subtype
  have hE₁card : Nat.card (E₀.map H.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hE₀card]
  have hE₁H : E₀.map H.subtype ≤ H := Subgroup.map_subtype_le _
  have h2 : 2 ≤ CFSG.Assembly.pRank p H :=
    CFSG.SectionRank.le_pRank hp.one_lt hE₁H
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hE₁) hE₁card
  exact h2.trans (pRank_le_localRank_of_isTwoLocal hp hHloc)

theorem exists_plane_data (h : Sec12Hyp G p A c L E) (hqs : CFSG.IsQuasisimple L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    ∃ A₀ : Subgroup G, A₀ ≤ L ∧ IsElementaryAbelian p A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p A := h.A_elem
  obtain ⟨S, hSL, hS1, hS2, hAS, hSA⟩ := h.L_mem.1.1.1.2
  set S' : Subgroup ↥L := S.subgroupOf L with hS'
  have hS'1 : S' ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [← Subgroup.map_subgroupOf_eq_of_le hSL, ← hS', hbot, Subgroup.map_bot]
  have hS'2 : IsPGroup 2 S' := hS2.comap_subtype
  set H : Subgroup ↥L := Subgroup.normalizer (S' : Set ↥L) with hH
  let ρ : ↥H →* MulAut ↥L := MulAut.conj.comp H.subtype
  let α : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ (a : A) (l : L), ((α a l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun a l => by
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hρ : ∀ (x : H) (l : L), ((ρ x l : L) : G) = ((x : L) : G) * l * ((x : L) : G)⁻¹ :=
    fun x l => by simp [ρ]
  have hker : ¬ p ∣ Nat.card ρ.ker := by
    intro hdvd
    apply hZ
    refine hdvd.trans ?_
    have hle : ρ.ker.map H.subtype ≤ Subgroup.center ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ g : L) : G)) (MonoidHom.mem_ker.mp hx)
      simp only [hρ, MulAut.one_apply] at h1
      exact Subtype.ext (comm_of_conj_eq h1)
    have hinj : Nat.card (ρ.ker.map H.subtype) = Nat.card ρ.ker :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← hinj]
    exact Subgroup.card_dvd_of_le hle
  have hrange : α.range ≤ ρ.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨q, hq, hz⟩ := exists_inv_mul_mem_centralizer h hqs a.2
    have hqH : (⟨q, hq⟩ : L) ∈ H := by
      rw [hH, Subgroup.mem_normalizer_iff]
      intro n
      have hn := Subgroup.mem_normalizer_iff.mp (hAS a.2) (n : G)
      have e : (a : G) * n * (a : G)⁻¹ = q * n * (q : G)⁻¹ :=
        conj_eq_of_mul_eq (z := (q : G)⁻¹ * a) (by group)
          (Subgroup.mem_centralizer_iff.mp hz n n.2).symm
      rw [hS', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      change (n : G) ∈ S ↔ q * n * (q : G)⁻¹ ∈ S
      rw [← e]
      exact hn
    refine ⟨⟨⟨q, hq⟩, hqH⟩, ?_⟩
    ext l
    rw [hρ, hα]
    show (q : G) * l * (q : G)⁻¹ = (a : G) * l * (a : G)⁻¹
    exact (conj_eq_of_mul_eq (z := (q : G)⁻¹ * a) (by group)
      (Subgroup.mem_centralizer_iff.mp hz l l.2).symm).symm
  have hEel : IsElementaryAbelian p α.range := isElementaryAbelian_range α
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian ρ hp hker α.range hrange
    (card_range_conjAction h hcyc α hα)
  have hE₁ : IsElementaryAbelian p (E₀.map H.subtype) := IsElementaryAbelian.map_subtype
  have hE₁card : Nat.card (E₀.map H.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hE₀card]
  have hA₀ : IsElementaryAbelian p ((E₀.map H.subtype).map L.subtype) :=
    IsElementaryAbelian.map_subtype
  have hA₀card : Nat.card ((E₀.map H.subtype).map L.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE₁card]
  have hmemA₀ : ∀ y : G, y ∈ (E₀.map H.subtype).map L.subtype ↔
      ∃ e ∈ E₀, ((((e : H) : L)) : G) = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, rfl⟩
  have hA₀S : (E₀.map H.subtype).map L.subtype ≤ Subgroup.normalizer (S : Set G) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := (hmemA₀ y).mp hy
    have heH : ((e : H) : L) ∈ H := (e : H).2
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hgL : g ∈ L
    · have := (Subgroup.mem_normalizer_iff.mp heH) ⟨g, hgL⟩
      rw [hS', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
      exact this
    · have hy' : ((((e : H) : L)) : G) ∈ L := ((e : H) : L).2
      have h1 : g ∉ S := fun hg => hgL (hSL hg)
      have h2 : (((((e : H) : L)) : G)) * g * (((((e : H) : L)) : G))⁻¹ ∉ S := by
        intro hg
        apply hgL
        have := L.mul_mem (L.mul_mem (L.inv_mem hy') (hSL hg)) hy'
        simpa [mul_assoc] using this
      exact ⟨fun hg => absurd hg h1, fun hg => absurd hg h2⟩
  refine ⟨(E₀.map H.subtype).map L.subtype, Subgroup.map_subtype_le _, hA₀, hA₀card, S, hSL, hS1,
    hS2, hA₀S, le_antisymm ?_ ?_⟩
  ·
    refine hSA.le.trans (Subgroup.commutator_le.mpr fun s hs a ha => ?_)
    have hmem : α ⟨a, ha⟩ ∈ E₀.map ρ := by
      rw [hE₀map]
      exact ⟨_, rfl⟩
    obtain ⟨e, he, hρe⟩ := hmem
    have hsL : s ∈ L := hSL hs
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨s⁻¹, L.inv_mem hsL⟩ : L) : G)) hρe
    simp only [hρ, hα] at h1
    have heA₀ : ((((e : H) : L)) : G) ∈ (E₀.map H.subtype).map L.subtype :=
      (hmemA₀ _).mpr ⟨e, he, rfl⟩
    have h2 := Subgroup.commutator_mem_commutator hs heA₀
    have h3 : ⁅s, a⁆ = ⁅s, ((((e : H) : L)) : G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s * a * s⁻¹ * a⁻¹ = s * (a * s⁻¹ * a⁻¹) := by group
        _ = s * ((((e : H) : L) : G) * s⁻¹ * (((e : H) : L) : G)⁻¹) := by rw [← h1]
        _ = s * (((e : H) : L) : G) * s⁻¹ * (((e : H) : L) : G)⁻¹ := by group
    rw [h3]
    exact h2
  · exact Subgroup.commutator_le.mpr fun s hs y hy => by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hA₀S hy) s⁻¹).mp (S.inv_mem hs)
      have h2 := S.mul_mem hs h1
      simpa [commutatorElement_def, mul_assoc] using h2

theorem localRank_eq_and_pRank_centralizer_eq (h : Sec12Hyp G p A c L E)
    (hqs : CFSG.IsQuasisimple L) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : IsCyclic ↥(thetaQuotientCentralizer p A L))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    localRank p ↥L = 2 ∧ CFSG.Assembly.pRank p (Subgroup.centralizer (L : Set G)) = 1 := by
  have hp := h.prime
  have h2 := two_le_localRank h hqs hAL hcyc hZ
  have hc1 : 1 ≤ CFSG.Assembly.pRank p (Subgroup.centralizer (L : Set G)) := by
    have hel : IsElementaryAbelian p (Subgroup.zpowers c) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (c_pow_eq_one h)
    exact CFSG.SectionRank.le_pRank hp.one_lt (E := Subgroup.zpowers c) (k := 1)
      ((Subgroup.zpowers_le).mpr (c_mem_centralizer_L h))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hel)
      (by rw [Nat.card_zpowers, orderOf_c h, pow_one])
  obtain ⟨P₀, hP₀C, hP₀el, hP₀card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.centralizer (L : Set G))
  have hdisj : P₀ ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxL⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_center_of_pow_eq_one hp hZ hxL (hP₀C hxP) (hP₀el.2 x hxP)
  have hR := localRank_add_le_evenRank hp (by have := h.three_lt; omega) (M := L) (P := P₀)
    (by omega) hP₀el hP₀C hdisj (k := CFSG.Assembly.pRank p (Subgroup.centralizer (L : Set G)))
    hP₀card
  rw [h.evenRank_eq] at hR
  omega

theorem mem_sup_zpowers_of_mem_sup_centralizer (h : Sec12Hyp G p A c L E)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    (hC : CFSG.Assembly.pRank p (Subgroup.centralizer (L : Set G)) ≤ 1) {x : G}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxp : x ^ p = 1)
    (hx : x ∈ L ⊔ Subgroup.centralizer (L : Set G)) : x ∈ Subgroup.zpowers c ⊔ L := by
  have hp := h.prime
  have hLN : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mpr le_rfl hl)
  have hx' : x ∈ ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN] at hx'
  obtain ⟨l, hl, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  have hzc : z ∈ Subgroup.centralizer ({c} : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (L_le_centralizer_c h hl)) hxc
    rwa [inv_mul_cancel_left] at this
  have hlz : l * z = z * l := Subgroup.mem_centralizer_iff.mp hz l hl
  have hpow : l ^ p * z ^ p = 1 := by
    rw [← (Commute.mul_pow hlz p), hxp]
  have hzpL : z ^ p ∈ L := by
    have : z ^ p = (l ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [this]
    exact L.inv_mem (L.pow_mem hl p)
  set n := Nat.card (Subgroup.center L) with hn
  have hzpn : (z ^ p) ^ n = 1 := by
    have hmem : (⟨z ^ p, hzpL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hz p) g g.2)
    have := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨⟨z ^ p, hzpL⟩, hmem⟩)
    exact congrArg (fun y : Subgroup.center L => ((y : L) : G)) this
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  obtain ⟨k, ⟨s, hs⟩, hkp⟩ : ∃ k : ℕ, n ∣ k ∧ k % p = 1 := ⟨n * m, dvd_mul_right _ _, hm⟩
  obtain ⟨t, hkt⟩ : ∃ t : ℕ, k = p * t + 1 := ⟨k / p, by
    have := Nat.div_add_mod k p
    rw [hkp] at this
    omega⟩
  set w := z ^ k with hw
  set r := (z ^ p) ^ t with hr
  have hwr : w = r * z := by
    rw [hw, hr, hkt, pow_succ, pow_mul]
  have hwp : w ^ p = 1 := by
    rw [hw, pow_right_comm, hs, pow_mul, hzpn, one_pow]
  have hwL : w ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hz k
  have hwc : w ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.pow_mem _ hzc k
  have hrL : r ∈ L := L.pow_mem hzpL t
  have hwzc : w ∈ Subgroup.zpowers c := by
    by_contra hwn
    have hbot := inf_zpowers_eq_bot hp hwp hwn
    have hw1 : w ≠ 1 := fun h1 => hwn (h1 ▸ Subgroup.one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hword : orderOf w = p := orderOf_eq_prime hwp hw1
    have hPel : IsElementaryAbelian p (Subgroup.zpowers c) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (c_pow_eq_one h)
    have hQel : IsElementaryAbelian p (Subgroup.zpowers w) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hwp
    have hcw : Commute w c := Subgroup.mem_centralizer_singleton_iff.mp hwc
    have hcomm : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ Subgroup.zpowers w, Commute a b := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow hcw.symm i j)
    have h2 := le_pRank_of_commute_of_inf_eq_bot hp
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hPel)
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hQel) hcomm hbot
      (a := 1) (b := 1) (by rw [Nat.card_zpowers, orderOf_c h, pow_one])
      (by rw [Nat.card_zpowers, hword, pow_one])
      ((Subgroup.zpowers_le).mpr (c_mem_centralizer_L h)) ((Subgroup.zpowers_le).mpr hwL)
    omega
  have hxeq : l * z = (l * r⁻¹) * w := by
    rw [hwr]; group
  rw [hxeq, sup_comm]
  exact Subgroup.mul_mem_sup (L.mul_mem hl (L.inv_mem hrL)) hwzc

theorem mem_normalizer_thetaComponentsAt_of_mem_centralizer
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hp : p.Prime) (hp3 : 3 < p) (hG : evenRank G ≤ 3) {a : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p a) {x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (hxp : x ^ p = 1) : x ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hH : evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hG
  have hxp' : (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) ^ p = 1 :=
    Subtype.ext (by simpa using hxp)
  have hord : ∃ k : ℕ, orderOf (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) = p ^ k := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp
      (show orderOf (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) ∣ p ^ 1 from by
        rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hxp')
    exact ⟨k, hk⟩
  have hmem := hnorm.1 (Subgroup.centralizer ({a} : Set G)) hH p hp hp3 _ hord _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({a} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hxgY
      have h1 : x * g * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := hYC hxgY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hx) h1) hx
      simpa [mul_assoc] using h2

theorem mem_sup_zpowers_of_mem_cNormalizer (h : Sec12Hyp G p A c L E)
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents) (hKF : KF122)
    (hLie : CFSG.Blueprint.EvenLieType (L ⧸ Subgroup.center L)) (hqs : CFSG.IsQuasisimple L)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hrank : localRank p ↥L = 2)
    (hplane : ∃ A₀ : Subgroup G, A₀ ≤ L ∧ IsElementaryAbelian p A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆)
    (hC : CFSG.Assembly.pRank p (Subgroup.centralizer (L : Set G)) ≤ 1) {x : G}
    (hx : x ∈ cNormalizer c) (hxo : orderOf x = p) : x ∈ Subgroup.zpowers c ⊔ L := by
  have hp := h.prime
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxcomm : x * c = c * x :=
    commute_of_mem_normalizer_zpowers hp (orderOf_c h) hxp hx
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
  by_cases hxLC : x ∈ L ⊔ Subgroup.centralizer (L : Set G)
  · exact mem_sup_zpowers_of_mem_sup_centralizer h hZ hC hxc hxp hxLC
  · exfalso
    have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_thetaComponentsAt_of_mem_centralizer hnorm hp h.three_lt h.evenRank_eq.le
        h.L_mem.2 hxc hxp
    have h5 : 5 ≤ p := by
      have h3 := h.three_lt
      by_contra hlt
      have : p = 4 := by omega
      exact absurd hp (by rw [this]; decide)
    have hevL : evenRank ↥L ≤ 3 :=
      (Sec9A.evenRank_subgroup_le L).trans h.evenRank_eq.le
    have hK := hKF G p hp h5 L hqs hLie hZ hrank hevL hplane x hxN hxp hxLC
    have hMc : L ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (L_le_centralizer_c h) ((Subgroup.zpowers_le).mpr hxc)
    have hcM : Subgroup.zpowers c ≤
        Subgroup.centralizer ((L ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
      refine (Subgroup.zpowers_le).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hMc hm)
    have hcnM : c ∉ L ⊔ Subgroup.zpowers x := by
      intro hcM'
      have hxL : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
        (Subgroup.zpowers_le).mpr hxN
      have hcM'' : c ∈ ((Subgroup.zpowers x ⊔ L : Subgroup G) : Set G) := by
        rw [sup_comm]; exact hcM'
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) L hxL] at hcM''
      obtain ⟨y, hy, l, hl, hyl⟩ := Set.mem_mul.mp hcM''
      have hyD : y ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
        have : y = c * l⁻¹ := eq_mul_inv_of_mul_eq hyl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (c_mem_centralizer_L h))
          (Subgroup.mem_sup_left (L.inv_mem hl))
      by_cases hy1 : y = 1
      · rw [hy1, one_mul] at hyl
        have hcl : c ∈ L := hyl ▸ hl
        exact h.c_ne_one (eq_one_of_mem_center_of_pow_eq_one hp hZ hcl (c_mem_centralizer_L h)
          (c_pow_eq_one h))
      · exact hxLC ((Subgroup.zpowers_le).mpr hyD
          (mem_zpowers_of_mem_zpowers_ne_one hp hxp hy hy1))
    have hbot : Subgroup.zpowers c ⊓ (L ⊔ Subgroup.zpowers x) = ⊥ := by
      rw [inf_comm]
      exact inf_zpowers_eq_bot hp (c_pow_eq_one h) hcnM
    have hPel : IsElementaryAbelian p (Subgroup.zpowers c) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (c_pow_eq_one h)
    have hR := localRank_add_le_evenRank hp (by have := h.three_lt; omega)
      (M := L ⊔ Subgroup.zpowers x) (P := Subgroup.zpowers c) (by omega)
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hPel) hcM hbot (k := 1)
      (by rw [Nat.card_zpowers, orderOf_c h, pow_one])
    rw [h.evenRank_eq] at hR
    omega

end Setup

end Sec12Two

theorem node122_of_prime_to_center
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h104 : SectionTenMaximalComponentQuotientActorKernelCyclic)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h107 : InSec10Seven)
    (hKF : KF122)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    CFSG.IsQuasisimple L ∧ localRank p L = 2 ∧
    CFSG.pRank p ↥(Subgroup.centralizer (L : Set G)) = 1 ∧
    (∀ x : G, x ∈ cNormalizer c → orderOf x = p → x ∈ Subgroup.zpowers c ⊔ L) ∧
    E = (E ⊓ L) ⊔ Subgroup.zpowers c := by
  have hzs : L ∈ sectionTenZeroStar p A := Sec12Two.L_mem_zeroStar h
  have hqs : CFSG.IsQuasisimple L := h106 hSchreier hTwoAction G p A h.setup L hzs
  obtain ⟨hAL, hcyc⟩ := h104 hSchreier G p A h.setup L ((sectionTenZeroStar_subset p A).2.1 hzs)
  obtain ⟨hrank, hCrank⟩ := Sec12Two.localRank_eq_and_pRank_centralizer_eq h hqs hAL hcyc hZ
  have hplane := Sec12Two.exists_plane_data h hqs hAL hcyc hZ
  have hLie := h107 G p A h.setup L hzs
  have hmem : ∀ x : G, x ∈ cNormalizer c → orderOf x = p → x ∈ Subgroup.zpowers c ⊔ L :=
    fun x hx hxo =>
      Sec12Two.mem_sup_zpowers_of_mem_cNormalizer h h81 hKF hLie hqs hZ hrank hplane hCrank.le hx hxo
  refine ⟨hqs, hrank, ?_, hmem, ?_⟩
  · rw [← assembly_pRank_eq_pRank]
    exact hCrank
  · have hcE : Subgroup.zpowers c ≤ E := (Subgroup.zpowers_le).mpr (h.A_le_E h.c_mem)
    refine le_antisymm (fun e he => ?_) (sup_le inf_le_left hcE)
    have : IsElementaryAbelian p E := h.E_elem
    have hep : e ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
    by_cases he1 : e = 1
    · rw [he1]
      exact Subgroup.one_mem _
    · have : Fact p.Prime := ⟨h.prime⟩
      have hord : orderOf e = p := orderOf_eq_prime hep he1
      have hec : e * c = c * e := (Subgroup.mem_centralizer_iff.mp (h.E_le he) c h.c_mem).symm
      have heN : e ∈ cNormalizer c := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (Commute.symm hec) j)).eq
      have hecL := hmem e heN hord
      have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
        (Subgroup.zpowers_le).mpr
          (Subgroup.centralizer_le_normalizer _ (Sec12Two.c_mem_centralizer_L h))
      have hecL' : e ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hecL
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) L hcN] at hecL'
      obtain ⟨y, hy, l, hl, rfl⟩ := Set.mem_mul.mp hecL'
      have hlE : l ∈ E := by
        have := E.mul_mem (E.inv_mem (hcE hy)) he
        rwa [inv_mul_cancel_left] at this
      rw [sup_comm]
      exact Subgroup.mul_mem_sup hy (Subgroup.mem_inf.mpr ⟨hlE, hl⟩)

end CFSG.RankThree.PartOne
