module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3P
public import CFSG.RankThree.PartTwo.Sec21.FF84S3T0
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG Equiv Equiv.Perm
open scoped commutatorElement

section Theta

variable {G : Type} [Group G]

structure PreTheta (L : Subgroup G) (θ : G → P8) : Prop where
  mul : ∀ g ∈ Nor L, ∀ h ∈ Nor L, θ (g * h) = θ g * θ h
  ker : ∀ g ∈ Nor L, θ g = 1 ↔ g ∈ CenS L
  mem : ∀ x ∈ L, θ x ∈ A8s
  surj : ∀ a ∈ A8s, ∃ x ∈ L, θ x = a

structure HasTheta (L : Subgroup G) (b₁ b₂ : G) (θ : G → P8) : Prop extends PreTheta L θ where
  hb₁ : θ b₁ = m₁
  hb₂ : θ b₂ = m₂

namespace PreTheta

variable {L : Subgroup G} {θ : G → P8} (P : PreTheta L θ)

include P in
theorem one : θ 1 = 1 := by
  have h := P.mul 1 (one_mem _) 1 (one_mem _)
  simpa using h

include P in
theorem inv {g : G} (hg : g ∈ Nor L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h := P.mul g hg g⁻¹ (inv_mem hg)
  rw [mul_inv_cancel, P.one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

include P in
theorem pow {g : G} (hg : g ∈ Nor L) (n : ℕ) : θ (g ^ n) = (θ g) ^ n := by
  induction n with
  | zero => simpa using P.one
  | succ n ih => rw [pow_succ, P.mul _ (pow_mem hg n) _ hg, ih, pow_succ]

include P in
theorem orderOf_dvd {g : G} (hg : g ∈ Nor L) : orderOf (θ g) ∣ orderOf g := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← P.pow hg, pow_orderOf_eq_one, P.one]

include P in
theorem conj {g h : G} (hg : g ∈ Nor L) (hh : h ∈ Nor L) :
    θ (g * h * g⁻¹) = θ g * θ h * (θ g)⁻¹ := by
  rw [P.mul _ (mul_mem hg hh) _ (inv_mem hg), P.mul _ hg _ hh, P.inv hg]

include P in
theorem comm {g h : G} (hg : g ∈ Nor L) (hh : h ∈ Nor L) (hc : g * h = h * g) :
    θ g * θ h = θ h * θ g := by
  rw [← P.mul _ hg _ hh, ← P.mul _ hh _ hg, hc]

def toHom : ↥(Nor L) →* P8 where
  toFun n := θ n
  map_one' := P.one
  map_mul' a b := P.mul a a.2 b b.2

end PreTheta

end Theta

section Lift

variable {G : Type} [Group G]

theorem center_sq {L : Subgroup G} (hZ : Nat.card (Subgroup.center L) ∣ 2) {z : G} (hzL : z ∈ L)
    (hz : z ∈ CenS L) : z ^ 2 = 1 := by
  have hmem : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz g g.2)
  have h1 : orderOf (⟨z, hzL⟩ : ↥L) ∣ 2 :=
    (Subgroup.orderOf_dvd_natCard _ hmem).trans hZ
  have h2 : (⟨z, hzL⟩ : ↥L) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
  exact congrArg Subtype.val h2

variable {L : Subgroup G} {θ : G → P8}

theorem PreTheta.lift_comm (P : PreTheta L θ) (hZ : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) {x y : G}
    (hx : x ∈ L) (hx3 : x ^ 3 = 1) (hy : y ∈ L) (hc : θ y * θ x = θ x * θ y) :
    y * x = x * y := by
  have hxN : x ∈ Nor L := Subgroup.le_normalizer hx
  have hyN : y ∈ Nor L := Subgroup.le_normalizer hy
  set c : G := y * x * y⁻¹ * x⁻¹ with hc_def
  have hcL : c ∈ L := L.mul_mem (L.mul_mem (L.mul_mem hy hx) (L.inv_mem hy)) (L.inv_mem hx)
  have hcN : c ∈ Nor L := Subgroup.le_normalizer hcL
  have hyxN : y * x * y⁻¹ ∈ Nor L := mul_mem (mul_mem hyN hxN) (inv_mem hyN)
  have hθc : θ c = 1 := by
    rw [hc_def, P.mul _ hyxN _ (inv_mem hxN), P.conj hyN hxN, P.inv hxN, hc]
    group
  have hcz : c ∈ CenS L := (P.ker c hcN).1 hθc
  have hc2 : c ^ 2 = 1 := hZ c hcL hcz
  have hcomm : Commute c x := (Subgroup.mem_centralizer_iff.1 hcz x hx).symm
  have hyx : y * x * y⁻¹ = c * x := by rw [hc_def]; group
  have h3 : (c * x) ^ 3 = 1 := by
    rw [← hyx, conj_pow, hx3]
    simp
  have hc3 : c ^ 3 = 1 := by
    rw [hcomm.mul_pow, hx3, mul_one] at h3
    exact h3
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; simp
  have : ⁅y, x⁆ = 1 := hc1
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem PreTheta.card_cent (P : PreTheta L θ) (hZ : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) {x : G}
    (hx : x ∈ L) (hx3 : x ^ 3 = 1) :
    Nat.card ↥(L ⊓ Cen x) =
      Nat.card (Subgroup.center ↥L) *
        Nat.card ↥(Subgroup.centralizer ({θ x} : Set P8) ⊓ A8s) := by
  have hle : L ⊓ Cen x ≤ Nor L := inf_le_left.trans Subgroup.le_normalizer
  let f : ↥(L ⊓ Cen x) →* P8 := P.toHom.comp (Subgroup.inclusion hle)
  have hf : ∀ k : ↥(L ⊓ Cen x), f k = θ (k : G) := fun k => rfl
  have hrange : f.range = Subgroup.centralizer ({θ x} : Set P8) ⊓ A8s := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      rw [hf]
      obtain ⟨hkL, hkc⟩ := Subgroup.mem_inf.1 k.2
      exact ⟨P.comm (Subgroup.le_normalizer hkL) (Subgroup.le_normalizer hx)
        (Subgroup.mem_centralizer_singleton_iff.1 hkc), P.mem _ hkL⟩
    · rintro ⟨hc, hyA⟩
      obtain ⟨z, hzL, rfl⟩ := P.surj y hyA
      have hzc : z * x = x * z := P.lift_comm hZ hx hx3 hzL hc
      exact ⟨⟨z, Subgroup.mem_inf.2 ⟨hzL, Subgroup.mem_centralizer_singleton_iff.2 hzc⟩⟩, rfl⟩
  have hkc : ∀ k : f.ker, (k.1.1 : G) ∈ CenS L := fun k =>
    (P.ker _ (hle k.1.2)).1 (by have := k.2; rwa [MonoidHom.mem_ker, hf] at this)
  have hk : Nat.card f.ker = Nat.card (Subgroup.center ↥L) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun k : f.ker => (⟨⟨(k.1.1 : G), (Subgroup.mem_inf.1 k.1.2).1⟩, ?_⟩ : Subgroup.center ↥L))
      ⟨?_, ?_⟩)
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hkc k) g g.2)
    · intro k₁ k₂ h12
      have : (k₁.1.1 : G) = k₂.1.1 := congrArg (fun z : Subgroup.center ↥L => ((z.1 : ↥L) : G)) h12
      exact Subtype.ext (Subtype.ext this)
    · intro z
      have hzc : ((z.1 : ↥L) : G) ∈ CenS L := by
        refine Subgroup.mem_centralizer_iff.2 (fun g hg => ?_)
        have := Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩
        exact congrArg Subtype.val this
      have hzx : ((z.1 : ↥L) : G) ∈ Cen x := by
        have := Subgroup.mem_center_iff.1 z.2 ⟨x, hx⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this).symm
      refine ⟨⟨⟨(z.1 : ↥L).1, Subgroup.mem_inf.2 ⟨(z.1 : ↥L).2, hzx⟩⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, hf]
      exact (P.ker _ (Subgroup.le_normalizer (z.1 : ↥L).2)).2 hzc
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hrange, hk] at hcard
  exact hcard.symm

end Lift

section Exists

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem exists_preTheta (L : Subgroup G) (hL : ⁅L, L⁆ = L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    ∃ θ : G → P8, PreTheta L θ := by
  obtain ⟨θ0, -, hL0, hker0⟩ := T0_thetaBar L hL e
  classical
  let θ1 : G → P8 := fun g => if hg : g ∈ Nor L then θ0 ⟨g, hg⟩ else 1
  have hθ1 : ∀ (g : G) (hg : g ∈ Nor L), θ1 g = θ0 ⟨g, hg⟩ := fun g hg => dif_pos hg
  refine ⟨θ1, ?_, ?_, ?_, ?_⟩
  · intro g hg k hk
    rw [hθ1 _ (mul_mem hg hk), hθ1 g hg, hθ1 k hk]
    exact map_mul θ0 ⟨g, hg⟩ ⟨k, hk⟩
  · intro g hg
    rw [hθ1 g hg]
    exact hker0 ⟨g, hg⟩
  · intro x hx
    rw [hθ1 x (Subgroup.le_normalizer hx)]
    have := hL0 ⟨x, hx⟩
    rw [this]
    exact (e (QuotientGroup.mk ⟨x, hx⟩)).2
  · intro a ha
    obtain ⟨q, hq⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨x, x.2, ?_⟩
    rw [hθ1 x (Subgroup.le_normalizer x.2)]
    have := hL0 x
    rw [this, hq]

theorem exists_theta (h : FF84Sec3 b L B b₁ b₂) (hZ : Nat.card (Subgroup.center L) ∣ 2) :
    ∃ θ : G → P8, HasTheta L b₁ b₂ θ := by
  obtain ⟨e⟩ : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, h.hyp.model⟩)
  have hL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.hyp.quasi.1
  obtain ⟨θ1, P⟩ := exists_preTheta L hL e
  have hZ' : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1 := fun z hz hc => center_sq hZ hz hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer hb₁L
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer hb₂L
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, -⟩ :=
    mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have ord3 : ∀ x ∈ L, x ^ 3 = 1 → x ≠ 1 → orderOf (θ1 x) = 3 := by
    intro x hxL hx3 hx1
    have hxN : x ∈ Nor L := Subgroup.le_normalizer hxL
    refine orderOf_eq_prime ?_ ?_
    · rw [← P.pow hxN, hx3, P.one]
    · intro h1
      have hsq := hZ' x hxL ((P.ker x hxN).1 h1)
      apply hx1
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, hsq]; simp
  have o₁ := ord3 b₁ hb₁L h13 hne1
  have o₂ := ord3 b₂ hb₂L h23 hne2
  have hpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  have t₁ : (θ1 b₁).cycleType = {3, 3} := by
    refine (A1_class _ (P.mem _ hb₁L) o₁).1 ?_
    have := P.card_cent hZ' hb₁L h13
    rw [h.caseA, mul_comm] at this
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have t₂ : (θ1 b₂).cycleType = {3, 3} := by
    refine (A1_class _ (P.mem _ hb₂L) o₂).1 ?_
    have := P.card_cent hZ' hb₂L h23
    rw [P_caseA₂ h, mul_comm] at this
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have hn : θ1 b₂ ∉ Subgroup.zpowers (θ1 b₁) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hz1 : θ1 (b₁ ^ k) = (θ1 b₁) ^ k := by
      have := map_zpow P.toHom (⟨b₁, hb₁N⟩ : ↥(Nor L)) k
      simpa [PreTheta.toHom] using this
    have hb₁kL : b₁ ^ k ∈ L := zpow_mem hb₁L k
    have hcL : b₂ * (b₁ ^ k)⁻¹ ∈ L := L.mul_mem hb₂L (L.inv_mem hb₁kL)
    have hcN : b₂ * (b₁ ^ k)⁻¹ ∈ Nor L := Subgroup.le_normalizer hcL
    have hθc : θ1 (b₂ * (b₁ ^ k)⁻¹) = 1 := by
      rw [P.mul _ hb₂N _ (inv_mem (Subgroup.le_normalizer hb₁kL)),
        P.inv (Subgroup.le_normalizer hb₁kL), hz1, hk]
      simp
    have hsq := hZ' _ hcL ((P.ker _ hcN).1 hθc)
    have hcB : b₂ * (b₁ ^ k)⁻¹ ∈ B :=
      B.mul_mem (mem_B_b₂ h) (B.inv_mem (zpow_mem (mem_B_b₁ h) k))
    have hcube := pow3_of_mem_B h hcB
    have hc1 : b₂ * (b₁ ^ k)⁻¹ = 1 := by
      calc b₂ * (b₁ ^ k)⁻¹ = (b₂ * (b₁ ^ k)⁻¹) ^ 3 * ((b₂ * (b₁ ^ k)⁻¹) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hcube, hsq]; simp
    exact hind k (by rw [mul_inv_eq_one] at hc1; exact hc1)
  obtain ⟨σ, hσ₁, hσ₂⟩ := A2_normalize (θ1 b₁) (θ1 b₂) (P.mem _ hb₁L) (P.mem _ hb₂L)
    (P.comm hb₁N hb₂N hcomm) o₁ o₂ t₁ t₂ hn
  have hA : ∀ y ∈ A8s, ∀ τ : P8, τ * y * τ⁻¹ ∈ A8s := fun y hy τ =>
    (alternatingGroup.normal (α := Fin 8)).conj_mem y hy τ
  refine ⟨fun g => σ * θ1 g * σ⁻¹, ⟨?_, ?_, ?_, ?_⟩, hσ₁, hσ₂⟩
  · intro g hg k hk
    simp only [P.mul g hg k hk]
    group
  · intro g hg
    rw [← P.ker g hg]
    constructor
    · intro h1
      have := congrArg (fun z => σ⁻¹ * z * σ) h1
      simpa [mul_assoc] using this
    · intro h1
      simp [h1]
  · intro x hx
    exact hA _ (P.mem x hx) σ
  · intro a ha
    obtain ⟨x, hxL, hx⟩ := P.surj (σ⁻¹ * a * σ⁻¹⁻¹) (hA a ha σ⁻¹)
    refine ⟨x, hxL, ?_⟩
    simp only [hx]
    group

end Exists

theorem two_elt_Eo {σ : P8} (h₁ : σ * m₁ = m₁ * σ) (h₂ : σ * m₂ = m₂ * σ) {n : ℕ}
    (hn : σ ^ (2 ^ n) = 1) : σ = 1 ∨ σ = τ₀ := by
  obtain ⟨i, j, k, hk, hσ⟩ := A3_centralizer_Eo σ h₁ h₂
  have c12 : m₁ * m₂ = m₂ * m₁ := by decide +kernel
  have c1t : m₁ * τ₀ = τ₀ * m₁ := by decide +kernel
  have c2t : m₂ * τ₀ = τ₀ * m₂ := by decide +kernel
  have hτ2 : τ₀ ^ 2 = 1 := by decide +kernel
  have h3 : σ ^ 3 = τ₀ ^ k := by
    have ca : Commute (m₁ ^ i) (m₂ ^ j) := (Commute.pow_pow ((show Commute m₁ m₂ from c12)) i j)
    have cb : Commute (m₁ ^ i * m₂ ^ j) (τ₀ ^ k) :=
      Commute.mul_left (Commute.pow_pow ((show Commute m₁ τ₀ from c1t)) i k) (Commute.pow_pow ((show Commute m₂ τ₀ from c2t)) j k)
    rw [hσ, cb.mul_pow, ca.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
      pow_mul, pow_mul, m₁_cube, m₂_cube]
    simp only [one_pow, one_mul]
    rw [show k * 3 = k + 2 * k by ring, pow_add, pow_mul, hτ2, one_pow, mul_one]
  have h6 : σ ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul, h3, ← pow_mul, mul_comm, pow_mul, hτ2, one_pow]
  have hd2 : orderOf σ ∣ 2 := by
    have d1 : orderOf σ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have d2 : orderOf σ ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    obtain ⟨a, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 d1
    rw [hd] at d2 ⊢
    have ha : a ≤ 1 := by
      by_contra ha1
      have ha1 : 2 ≤ a := by omega
      have h4 : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha1
      have := h4.trans d2
      omega
    simpa using pow_dvd_pow 2 ha
  have hs2 : σ * σ = 1 := by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 hd2
  exact A3_inv σ h₁ h₂ hs2

section Facts

variable {G : Type} [Group G] {L : Subgroup G} {θ : G → P8}

theorem comm_aux {a b c d : G} (hca : Commute c a) (hcb : Commute c b)
    (hda : Commute d a) (hdb : Commute d b) (hcd : Commute c d) :
    ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hK : Commute (c * d) ⁅a, b⁆ := by
    have hza : Commute (c * d) a := hca.mul_left hda
    have hzb : Commute (c * d) b := hcb.mul_left hdb
    rw [commutatorElement_def]
    exact ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have hc' : Commute c⁻¹ (b⁻¹ * d⁻¹) := hcb.inv_inv.mul_right hcd.inv_inv
  have key : ⁅c * a, d * b⁆ = (c * d) * ⁅a, b⁆ * (c * d)⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc c * a * (d * b) * (c * a)⁻¹ * (d * b)⁻¹
        = c * (a * d) * b * (a⁻¹ * (c⁻¹ * (b⁻¹ * d⁻¹))) := by group
      _ = c * (d * a) * b * (a⁻¹ * (c⁻¹ * (b⁻¹ * d⁻¹))) := by rw [← hda.eq]
      _ = c * (d * a) * b * (a⁻¹ * ((b⁻¹ * d⁻¹) * c⁻¹)) := by rw [hc'.eq]
      _ = (c * d) * (a * b * a⁻¹ * b⁻¹) * (c * d)⁻¹ := by group
  rw [key, hK.eq, mul_inv_cancel_right]

theorem PreTheta.comm_elt (P : PreTheta L θ) {x y : G} (hx : x ∈ Nor L) (hy : y ∈ Nor L) :
    θ (x * y * x⁻¹ * y⁻¹) = θ x * θ y * (θ x)⁻¹ * (θ y)⁻¹ := by
  have hxy : x * y * x⁻¹ ∈ Nor L := mul_mem (mul_mem hx hy) (inv_mem hx)
  rw [P.mul _ hxy _ (inv_mem hy), P.conj hx hy, P.inv hy]

theorem HasTheta.two_elt {b₁ b₂ : G} (H : HasTheta L b₁ b₂ θ) (hb₁N : b₁ ∈ Nor L)
    (hb₂N : b₂ ∈ Nor L) {v : G} (hvN : v ∈ Nor L) (hv₁ : v * b₁ = b₁ * v)
    (hv₂ : v * b₂ = b₂ * v) {n : ℕ} (hn : v ^ (2 ^ n) = 1) : θ v = 1 ∨ θ v = τ₀ := by
  have c₁ := H.toPreTheta.comm hvN hb₁N hv₁
  have c₂ := H.toPreTheta.comm hvN hb₂N hv₂
  rw [H.hb₁] at c₁
  rw [H.hb₂] at c₂
  refine two_elt_Eo (n := n) c₁ c₂ ?_
  rw [← H.toPreTheta.pow hvN, hn, H.toPreTheta.one]

theorem PreTheta.A6tau_lift (P : PreTheta L θ) {v : G} (hvN : v ∈ Nor L) (hv : θ v = τ₀) :
    ∀ r ∈ A6tau, ∃ l ∈ L, v * l = l * v ∧ θ l = r := by
  have hle : L ⊓ Cen v ≤ Nor L := inf_le_left.trans Subgroup.le_normalizer
  let f : ↥(L ⊓ Cen v) →* P8 := P.toHom.comp (Subgroup.inclusion hle)
  have hf : ∀ k : ↥(L ⊓ Cen v), f k = θ (k : G) := fun k => rfl
  have hz : ∀ x ∈ L, θ x * τ₀ = τ₀ * θ x →
      v * x * v⁻¹ * x⁻¹ ∈ L ∧ v * x * v⁻¹ * x⁻¹ ∈ CenS L := by
    intro x hx hc
    have hxN : x ∈ Nor L := Subgroup.le_normalizer hx
    have hzL : v * x * v⁻¹ * x⁻¹ ∈ L := by
      have h1 : v * x * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hvN x).1 hx
      exact L.mul_mem h1 (L.inv_mem hx)
    refine ⟨hzL, (P.ker _ (Subgroup.le_normalizer hzL)).1 ?_⟩
    rw [P.comm_elt hvN hxN, hv]
    rw [← hc]
    group
  have hcomm : ∀ x ∈ L, ∀ y ∈ L, θ x * τ₀ = τ₀ * θ x → θ y * τ₀ = τ₀ * θ y →
      v * ⁅x, y⁆ = ⁅x, y⁆ * v := by
    intro x hx y hy hcx hcy
    obtain ⟨hzxL, hzx⟩ := hz x hx hcx
    obtain ⟨hzyL, hzy⟩ := hz y hy hcy
    set zx := v * x * v⁻¹ * x⁻¹ with hzx_def
    set zy := v * y * v⁻¹ * y⁻¹ with hzy_def
    have e1 : v * x * v⁻¹ = zx * x := by rw [hzx_def]; group
    have e2 : v * y * v⁻¹ = zy * y := by rw [hzy_def]; group
    have h1 : Commute zx x := (Subgroup.mem_centralizer_iff.1 hzx x hx).symm
    have h2 : Commute zx y := (Subgroup.mem_centralizer_iff.1 hzx y hy).symm
    have h3 : Commute zy x := (Subgroup.mem_centralizer_iff.1 hzy x hx).symm
    have h4 : Commute zy y := (Subgroup.mem_centralizer_iff.1 hzy y hy).symm
    have h5 : Commute zx zy := (Subgroup.mem_centralizer_iff.1 hzx zy hzyL).symm
    have key : v * ⁅x, y⁆ * v⁻¹ = ⁅x, y⁆ := by
      calc v * ⁅x, y⁆ * v⁻¹ = ⁅v * x * v⁻¹, v * y * v⁻¹⁆ := by
            rw [commutatorElement_def, commutatorElement_def]; group
        _ = ⁅zx * x, zy * y⁆ := by rw [e1, e2]
        _ = ⁅x, y⁆ := comm_aux h1 h2 h3 h4 h5
    exact mul_inv_eq_iff_eq_mul.1 key
  have hR : A6tau ≤ f.range := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hr
    have hcomm' : commutator ↥(Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s) ≤
        f.range.comap (Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s).subtype := by
      show ⁅(⊤ : Subgroup ↥(Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s)), ⊤⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro c₁ _ c₂ _
      obtain ⟨hc₁c, hc₁A⟩ := Subgroup.mem_inf.1 c₁.2
      obtain ⟨hc₂c, hc₂A⟩ := Subgroup.mem_inf.1 c₂.2
      obtain ⟨x₁, hx₁L, hx₁⟩ := P.surj _ hc₁A
      obtain ⟨x₂, hx₂L, hx₂⟩ := P.surj _ hc₂A
      have hcx₁ : θ x₁ * τ₀ = τ₀ * θ x₁ := by
        rw [hx₁]; exact Subgroup.mem_centralizer_singleton_iff.1 hc₁c
      have hcx₂ : θ x₂ * τ₀ = τ₀ * θ x₂ := by
        rw [hx₂]; exact Subgroup.mem_centralizer_singleton_iff.1 hc₂c
      have hkL : ⁅x₁, x₂⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem hx₁L hx₂L) (L.inv_mem hx₁L)) (L.inv_mem hx₂L)
      have hkc : ⁅x₁, x₂⁆ ∈ Cen v :=
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm x₁ hx₁L x₂ hx₂L hcx₁ hcx₂).symm
      refine ⟨⟨⁅x₁, x₂⁆, Subgroup.mem_inf.2 ⟨hkL, hkc⟩⟩, ?_⟩
      show θ ⁅x₁, x₂⁆ = _
      rw [commutatorElement_def, P.comm_elt (Subgroup.le_normalizer hx₁L)
        (Subgroup.le_normalizer hx₂L), hx₁, hx₂]
      simp [commutatorElement_def]
    exact hcomm' hc
  intro r hr
  obtain ⟨k, hk⟩ := hR hr
  obtain ⟨hkL, hkc⟩ := Subgroup.mem_inf.1 k.2
  exact ⟨k, hkL, (Subgroup.mem_centralizer_singleton_iff.1 hkc).symm, hk⟩

end Facts

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
