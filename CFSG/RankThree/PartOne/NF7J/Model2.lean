module

public import CFSG.RankThree.PartOne.NF7J.Model1
public import CFSG.RankThree.PartOne.NF7J.GLFacts

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem conjBy_mul' (a b : G) (S : Subgroup G) : conjBy (a * b) S = conjBy a (conjBy b S) := by
  ext x
  rw [Equivariance.mem_conjBy, Equivariance.mem_conjBy, Equivariance.mem_conjBy]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

theorem conjAut_mul' {E : Subgroup G} {w w' : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hw' : w' ∈ Subgroup.normalizer (E : Set G)) :
    conjAut E (w * w') ((Subgroup.normalizer (E : Set G)).mul_mem hw hw') =
      conjAut E w hw * conjAut E w' hw' := by
  unfold conjAut
  rw [← map_mul]
  rfl

end Basic

theorem gl_conj_inv (a b : GL (Fin 3) (ZMod 2)) (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1)
    (hb1 : b ≠ 1) : ∃ k : GL (Fin 3) (ZMod 2), k * a * k⁻¹ = b := by
  have hK : ∀ x : GL (Fin 3) (ZMod 2), x * x = 1 → x ≠ 1 →
      ∃ K : GL (Fin 3) (ZMod 2), K * matUnit' (mk32 275) det3_mk32_275 = x * K := by
    intro x hx hx1
    have hxx : (x : M32) * (x : M32) = 1 := by
      have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : M32)) hx
      simpa using this
    have hx1' : (x : M32) ≠ 1 := fun h => hx1 (Units.ext (by simpa using h))
    obtain ⟨K, hKd, hKe⟩ := exists_conj_A0 (x : M32) (det3_GL x) hx1' hxx
    refine ⟨matUnit' K hKd, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, matUnit'_val, matUnit'_val]
    exact hKe
  obtain ⟨Ka, hKa⟩ := hK a ha ha1
  obtain ⟨Kb, hKb⟩ := hK b hb hb1
  refine ⟨Kb * Ka⁻¹, ?_⟩
  have h1 : Ka⁻¹ * a * Ka = matUnit' (mk32 275) det3_mk32_275 := by
    calc Ka⁻¹ * a * Ka = Ka⁻¹ * (a * Ka) := by rw [mul_assoc]
      _ = Ka⁻¹ * (Ka * matUnit' (mk32 275) det3_mk32_275) := by rw [hKa]
      _ = matUnit' (mk32 275) det3_mk32_275 := by group
  calc Kb * Ka⁻¹ * a * (Kb * Ka⁻¹)⁻¹ = Kb * (Ka⁻¹ * a * Ka) * Kb⁻¹ := by group
    _ = b := by rw [h1, hKb]; group

section FrameDatum

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K) (D : Datum p E) (X : EFacts G p c E)

theorem Datum.exists_conj {x y : MulAut E} (hx : x ∈ D.H) (hy : y ∈ D.H) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : ∃ h ∈ D.H, h * x * h⁻¹ = y := by
  have hinj := D.e.injective
  have h2 : ∀ (a : MulAut E) (ha : a ∈ D.H), a * a = 1 → D.e ⟨a, ha⟩ * D.e ⟨a, ha⟩ = 1 := by
    intro a ha h
    rw [← map_mul]
    have : (⟨a, ha⟩ : ↥D.H) * ⟨a, ha⟩ = 1 := Subtype.ext h
    rw [this, map_one]
  have h1 : ∀ (a : MulAut E) (ha : a ∈ D.H), a ≠ 1 → D.e ⟨a, ha⟩ ≠ 1 := by
    intro a ha h h'
    apply h
    have : (⟨a, ha⟩ : ↥D.H) = 1 := hinj (h'.trans (map_one D.e).symm)
    exact congrArg Subtype.val this
  obtain ⟨k, hk⟩ := gl_conj_inv _ _ (h2 x hx hx2) (h1 x hx hx1) (h2 y hy hy2) (h1 y hy hy1)
  refine ⟨((D.e.symm k : ↥D.H) : MulAut E), (D.e.symm k).2, ?_⟩
  have h3 : D.e.symm k * ⟨x, hx⟩ * (D.e.symm k)⁻¹ = ⟨y, hy⟩ := by
    apply hinj
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hk]
  have := congrArg Subtype.val h3
  simpa using this

include F X in
theorem νmul_torus_ne_one {r : MulAut E} (hr : r ∈ torusImage E L) : D.ν * r ≠ 1 := by
  intro h
  have h1 : (D.ν * r) X.cE = X.cE := by rw [h]; rfl
  rw [MulAut.mul_apply, torusImage_fix_c F X hr, D.hν] at h1
  have hp := X.prime
  have hc : X.cE ^ 2 = 1 := by
    have h2 : X.cE⁻¹ = X.cE := h1
    calc X.cE ^ 2 = X.cE * X.cE := sq _
      _ = X.cE * X.cE⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel _
  have hcp : X.cE ^ p = 1 := Subtype.ext X.c_pow
  have hodd : Odd p := hp.odd_of_ne_two (by have := X.five_le; omega)
  have h3 : X.cE = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have h4 : X.cE ^ (2 * k + 1) = X.cE := by
      rw [pow_succ, pow_mul, hc, one_pow, one_mul]
    have : X.cE ^ p = X.cE :=
      (congrArg (fun n => X.cE ^ n) hk).trans h4
    rw [← this, hcp]
  exact X.c_ne (congrArg Subtype.val h3)

include F X in
theorem a₁_ne_one : D.ν * F.r₀ ≠ 1 := νmul_torus_ne_one F D X F.r₀_L

include F X in
theorem a₂_ne_one : D.ν * F.r₁ ≠ 1 := νmul_torus_ne_one F D X F.r₁_L

include X in
theorem exists_base :
    ∃ (u₀ : G) (hu₀ : u₀ ∈ Subgroup.normalizer (E : Set G)),
      conjAut E u₀ hu₀ * F.r₀ * (conjAut E u₀ hu₀)⁻¹ = D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) := by
  have h1 := Datum.exists_conj D (a₁_mem F D) (zz_mem F D) (a₁_sq F D) (a₁_ne_one F D X) (zz_sq F)
    (rho_sq_ne F)
  obtain ⟨h₀, hh₀, hconj⟩ := h1
  obtain ⟨u₀, hu₀, hu⟩ := D.exists_lift hh₀
  refine ⟨u₀, hu₀, ?_⟩
  rw [hu]
  have h3 : h₀ * (D.ν * F.r₀) * h₀⁻¹ = (F.r₀ * F.r₁) * (F.r₀ * F.r₁) := hconj
  have h4 : h₀ * F.r₀ * h₀⁻¹ = D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) := by
    rw [← h3]
    have : h₀ * (D.ν * F.r₀) * h₀⁻¹ = D.ν * (h₀ * F.r₀ * h₀⁻¹) := by
      calc h₀ * (D.ν * F.r₀) * h₀⁻¹ = (h₀ * D.ν) * F.r₀ * h₀⁻¹ := by simp only [mul_assoc]
        _ = (D.ν * h₀) * F.r₀ * h₀⁻¹ := by rw [D.ν_comm h₀]
        _ = D.ν * (h₀ * F.r₀ * h₀⁻¹) := by simp only [mul_assoc]
    rw [this, D.ν_mul_ν_mul]
  exact h4

structure Base where
  u : G
  hu : u ∈ Subgroup.normalizer (E : Set G)
  hconj : conjAut E u hu * F.r₀ * (conjAut E u hu)⁻¹ = D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))

include X in
theorem exists_Base : Nonempty (Base F D) := by
  obtain ⟨u, hu, h⟩ := exists_base F D X
  exact ⟨⟨u, hu, h⟩⟩

variable {F D}

namespace Base

@[expose] noncomputable def R (B : Base F D) : Subgroup G := conjBy B.u (F.rg 0)

@[expose] noncomputable def R' (B : Base F D) : Subgroup G := conjBy B.u (F.rg 4)

theorem R_ne (B : Base F D) : B.R ≠ B.R' := by
  intro h
  have hinj : Function.Injective (conjBy B.u : Subgroup G → Subgroup G) :=
    Subgroup.map_injective (MulAut.conj B.u).injective
  exact F.rg_ne (i := 0) (j := 4) (by decide) (hinj h)

end Base

omit [Finite G] in
theorem rule_aux {u w : G} (hu : u ∈ Subgroup.normalizer (E : Set G))
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {r z : MulAut E}
    (h1 : conjAut E u hu * r * (conjAut E u hu)⁻¹ = z)
    (hfix : conjAut E w hw * z * (conjAut E w hw)⁻¹ = z)
    (hw' : u⁻¹ * w * u ∈ Subgroup.normalizer (E : Set G)) :
    conjAut E (u⁻¹ * w * u) hw' * r * (conjAut E (u⁻¹ * w * u) hw')⁻¹ = r := by
  have hN := Subgroup.normalizer (E : Set G)
  have hcw' : conjAut E (u⁻¹ * w * u) hw' =
      (conjAut E u hu)⁻¹ * conjAut E w hw * conjAut E u hu := by
    have := conjAut_mul' ((Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).inv_mem hu) hw) hu
    rw [conjAut_mul' ((Subgroup.normalizer (E : Set G)).inv_mem hu) hw,
      Equivariance.conjAut_inv hu] at this
    exact this
  rw [hcw']
  calc (conjAut E u hu)⁻¹ * conjAut E w hw * conjAut E u hu * r *
        ((conjAut E u hu)⁻¹ * conjAut E w hw * conjAut E u hu)⁻¹
      = (conjAut E u hu)⁻¹ * (conjAut E w hw * (conjAut E u hu * r * (conjAut E u hu)⁻¹) *
        (conjAut E w hw)⁻¹) * conjAut E u hu := by group
    _ = r := by
      rw [h1, hfix, ← h1]
      group

include X in
theorem Base.rule (B : Base F D) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hfix : conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (conjAut E w hw)⁻¹ =
      D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) {n : ℕ} (hn : w * c * w⁻¹ = c ^ n) :
    (n % p = 1 → conjBy w B.R = B.R ∧ conjBy w B.R' = B.R') ∧
      ((n + 1) % p = 0 → conjBy w B.R = B.R' ∧ conjBy w B.R' = B.R) := by
  have hp := X.prime
  have h5 := X.five_le
  have hp2 : p ≠ 2 := by omega
  have hu := B.hu
  have hw' : B.u⁻¹ * w * B.u ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem ((Subgroup.normalizer (E : Set G)).inv_mem hu) hw) hu
  have hfix' := rule_aux hu hw B.hconj hfix hw'
  have hb : B.u * F.b₀ * B.u⁻¹ ∈ Subgroup.zpowers c := by
    have h1 := F.b₀_mem_moved hp
    have h2 : B.u * F.b₀ * B.u⁻¹ ∈ conjBy B.u (autMovedInG E F.r₀) := by
      rw [Equivariance.mem_conjBy]
      simpa [mul_assoc] using h1
    rw [← Equivariance.autMovedInG_conj F.r₀ hu, B.hconj, moved_zp F D X] at h2
    exact h2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hb₀ : F.b₀ = B.u⁻¹ * c ^ m * B.u := by rw [hm]; group
  have hn' : (B.u⁻¹ * w * B.u) * F.b₀ * (B.u⁻¹ * w * B.u)⁻¹ = F.b₀ ^ n := by
    have e1 : (B.u⁻¹ * w * B.u) * F.b₀ * (B.u⁻¹ * w * B.u)⁻¹ =
        B.u⁻¹ * (w * c ^ m * w⁻¹) * B.u := by rw [hb₀]; group
    have e2 : F.b₀ ^ n = B.u⁻¹ * (c ^ m) ^ n * B.u := by
      rw [hb₀]
      have := conj_pow (a := B.u⁻¹) (b := c ^ m) (i := n)
      simpa only [inv_inv] using this
    have e3 : w * c ^ m * w⁻¹ = (c ^ n) ^ m := by
      rw [← hn]
      exact (conj_zpow).symm
    have e4 : (c ^ n) ^ m = (c ^ m) ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rw [e1, e2, e3, e4]
  have hr := F.rule_r₀ hp hp2 h5 hdvd hodd hw' hfix' hn'
  have hwu : w * B.u = B.u * (B.u⁻¹ * w * B.u) := by group
  have hconjw : ∀ S, conjBy w (conjBy B.u S) = conjBy B.u (conjBy (B.u⁻¹ * w * B.u) S) := fun S => by
    rw [← conjBy_mul', ← conjBy_mul', hwu]
  unfold Base.R Base.R'
  rw [hconjw, hconjw]
  rcases hr with ⟨h1, h2⟩
  constructor
  · intro hn1
    obtain ⟨a, b⟩ := h1 hn1
    rw [a, b]
    exact ⟨rfl, rfl⟩
  · intro hn1
    obtain ⟨a, b⟩ := h2 hn1
    rw [a, b]
    exact ⟨rfl, rfl⟩

end FrameDatum

end CFSG.RankThree.PartOne.NF7J
