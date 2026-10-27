module

public import CFSG.Quasithin.Vol2.KGFact4413L3M
public import CFSG.Quasithin.Vol2.KGFact4413L3X

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {X : Type} [Group X]

theorem commutator_zpow_of_comm {D : Subgroup X} (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    {n : X} (hnD : ∀ d ∈ D, n * d * n⁻¹ ∈ D) {e : X} (he : e ∈ D) (m : ℤ) :
    e ^ m * n * (e ^ m)⁻¹ * n⁻¹ = (e * n * e⁻¹ * n⁻¹) ^ m := by
  have h1 : e * n * e⁻¹ * n⁻¹ = e * (n * e⁻¹ * n⁻¹) := by group
  have hc : Commute e (n * e⁻¹ * n⁻¹) := hDab _ he _ (hnD _ (D.inv_mem he))
  rw [h1, hc.mul_zpow, conj_zpow, _root_.inv_zpow]
  group

theorem gamma_commutator {D : Subgroup X} (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {n : X}
    (hnD : ∀ d ∈ D, n * d * n⁻¹ ∈ D) (γ : MulAut X) (m : ℤ)
    (hγD : ∀ d ∈ D, γ d * (d ^ m)⁻¹ ∈ Subgroup.center X) (hγn : n⁻¹ * γ n ∈ D) {e : X}
    (he : e ∈ D) : γ (e * n * e⁻¹ * n⁻¹) = (e * n * e⁻¹ * n⁻¹) ^ m := by
  set ζ := γ e * (e ^ m)⁻¹ with hζdef
  have hζ : ζ ∈ Subgroup.center X := hγD e he
  have hγe : γ e = ζ * e ^ m := by rw [hζdef, inv_mul_cancel_right]
  set f := n⁻¹ * γ n with hfdef
  have hγn' : γ n = n * f := by rw [hfdef, mul_inv_cancel_left]
  have hcomm : f * (e ^ m)⁻¹ = (e ^ m)⁻¹ * f := hDab _ hγn _ (D.inv_mem (D.zpow_mem he m))
  have hζc : ∀ w, ζ * w = w * ζ := fun w => (Subgroup.mem_center_iff.mp hζ w).symm
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hγe, hγn']
  have e1 : ζ * e ^ m * (n * f) * (ζ * e ^ m)⁻¹ * (n * f)⁻¹ =
      (ζ * (e ^ m * n * (f * (e ^ m)⁻¹))) * ζ⁻¹ * f⁻¹ * n⁻¹ := by group
  rw [e1, hζc (e ^ m * n * (f * (e ^ m)⁻¹)), hcomm, ← commutator_zpow_of_comm hDab hnD he m]
  group

theorem commutator_le_closure {D : Subgroup X} (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {c : X}
    (hcD : ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hcD' : ∀ d ∈ D, c⁻¹ * d * c ∈ D) {P : Subgroup X}
    (hP : ∀ x ∈ P, ∃ d ∈ D, ∃ k : ℤ, x = d * c ^ k) :
    ⁅P, P⁆ ≤ Subgroup.closure {x | ∃ d ∈ D, x = d * c * d⁻¹ * c⁻¹} := by
  set K' := Subgroup.closure {x | ∃ d ∈ D, x = d * c * d⁻¹ * c⁻¹} with hK'
  have hgen : ∀ e ∈ D, e * c * e⁻¹ * c⁻¹ ∈ K' := fun e he => Subgroup.subset_closure ⟨e, he, rfl⟩
  have hτ : ∀ k : ℤ, ∀ d ∈ D, c ^ k * d * c ^ (-k) ∈ D := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro d hd
      simpa using hd
    · intro k ih d hd
      have e : c ^ ((k : ℤ) + 1) * d * c ^ (-((k : ℤ) + 1)) =
          c * (c ^ (k : ℤ) * d * c ^ (-(k : ℤ))) * c⁻¹ := by group
      rw [e]
      exact hcD _ (ih d hd)
    · intro k ih d hd
      have e : c ^ (-(k : ℤ) - 1) * d * c ^ (-(-(k : ℤ) - 1)) =
          c⁻¹ * (c ^ (-(k : ℤ)) * d * c ^ (-(-(k : ℤ)))) * c := by group
      rw [e]
      exact hcD' _ (ih d hd)
  have hK : ∀ k : ℤ, ∀ d ∈ D, d * (c ^ k * d * c ^ (-k))⁻¹ ∈ K' := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro d _
      simp
    · intro k ih d hd
      have heD : c ^ (k : ℤ) * d * c ^ (-(k : ℤ)) ∈ D := hτ k d hd
      have e1 : d * (c ^ ((k : ℤ) + 1) * d * c ^ (-((k : ℤ) + 1)))⁻¹ =
          (d * (c ^ (k : ℤ) * d * c ^ (-(k : ℤ)))⁻¹) *
            ((c ^ (k : ℤ) * d * c ^ (-(k : ℤ))) * c * (c ^ (k : ℤ) * d * c ^ (-(k : ℤ)))⁻¹ *
              c⁻¹) := by group
      rw [e1]
      exact K'.mul_mem (ih d hd) (hgen _ heD)
    · intro k ih d hd
      have heD : c ^ (-(k : ℤ) - 1) * d * c ^ (-(-(k : ℤ) - 1)) ∈ D := hτ _ d hd
      have e1 : d * (c ^ (-(k : ℤ) - 1) * d * c ^ (-(-(k : ℤ) - 1)))⁻¹ =
          (d * (c ^ (-(k : ℤ)) * d * c ^ (-(-(k : ℤ))))⁻¹) *
            ((c ^ (-(k : ℤ) - 1) * d * c ^ (-(-(k : ℤ) - 1))) * c *
              (c ^ (-(k : ℤ) - 1) * d * c ^ (-(-(k : ℤ) - 1)))⁻¹ * c⁻¹)⁻¹ := by group
      rw [e1]
      exact K'.mul_mem (ih d hd) (K'.inv_mem (hgen _ heD))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨d₁, hd₁, i, rfl⟩ := hP x hx
  obtain ⟨d₂, hd₂, j, rfl⟩ := hP y hy
  have hτ₁ := hτ j d₁ hd₁
  have hτ₂ := hτ i d₂ hd₂
  have e1 : ⁅d₁ * c ^ i, d₂ * c ^ j⁆ =
      d₁ * ((c ^ i * d₂ * c ^ (-i)) * (c ^ j * d₁ * c ^ (-j))⁻¹) * d₂⁻¹ := by
    rw [commutatorElement_def]
    group
  have hsw : (c ^ i * d₂ * c ^ (-i)) * (c ^ j * d₁ * c ^ (-j))⁻¹ =
      (c ^ j * d₁ * c ^ (-j))⁻¹ * (c ^ i * d₂ * c ^ (-i)) :=
    hDab _ hτ₂ _ (D.inv_mem hτ₁)
  have e2 : d₁ * ((c ^ j * d₁ * c ^ (-j))⁻¹ * (c ^ i * d₂ * c ^ (-i))) * d₂⁻¹ =
      (d₁ * (c ^ j * d₁ * c ^ (-j))⁻¹) * (d₂ * (c ^ i * d₂ * c ^ (-i))⁻¹)⁻¹ := by group
  rw [e1, hsw, e2]
  exact K'.mul_mem (hK j d₁ hd₁) (K'.inv_mem (hK i d₂ hd₂))

section Core

variable [Finite X] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_lift_w0_mem_normalizer (hF : 2 < Nat.card F) (h3 : 3 ∣ Nat.card F - 1)
    (hperf : commutator X = ⊤) (θ : X →* projectiveSL 3 F) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center X) {D A : Subgroup X}
    (hθD : ∀ x, θ x ∈ dL3 F ↔ x ∈ D) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hAD : A ≤ D) (hA : ∀ a ∈ A, a ^ 3 = 1) (β : MulAut X) (α : MulAut (projectiveSL 3 F))
    (hβθ : ∀ x, θ (β x) = α (θ x)) (hβD : ∀ d ∈ D, β d ∈ D) (hβA : ∀ a ∈ A, β a ∈ A)
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ LinearFlag.semilinearAutGroup 3 F) :
    ∃ x₀ : X, θ x₀ = w0L3 F ∧ x₀ ∈ Subgroup.normalizer (A : Set X) := by
  classical
  have hαD : ∀ d ∈ dL3 F, α d ∈ dL3 F := by
    intro d hd
    obtain ⟨x, rfl⟩ := hθ d
    rw [← hβθ, hθD]
    exact hβD x ((hθD x).mp hd)
  obtain ⟨m, hmD, hmw, hmc⟩ := exists_zpow_of_not_semilinear hF hαU hαD hαs
  obtain ⟨x₀, hx₀⟩ := hθ (w0L3 F)
  obtain ⟨c, hc⟩ := hθ (cyc3L3 F)
  have hconj : ∀ y : X, (∀ d ∈ dL3 F, θ y * d * (θ y)⁻¹ ∈ dL3 F) →
      ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    rw [← hθD, map_mul, map_mul, map_inv]
    exact hy _ ((hθD d).mpr hd)
  have hx₀D := hconj x₀ (by rw [hx₀]; exact fun d hd => w0L3_conj_mem_dL3 hd)
  have hx₀D' := hconj x₀⁻¹ (by
    rw [map_inv, hx₀, inv_inv]
    exact fun d hd => w0L3_inv_conj_mem_dL3 hd)
  have hcD := hconj c (by rw [hc]; exact fun d hd => cyc3L3_conj_mem_dL3 hd)
  have hcD' : ∀ d ∈ D, c⁻¹ * d * c ∈ D := by
    have h := hconj c⁻¹ (by
      rw [map_inv, hc, inv_inv]
      exact fun d hd => cyc3L3_inv_conj_mem_dL3 hd)
    intro d hd
    simpa using h d hd
  set γ : MulAut X := MulAut.conj x₀⁻¹ * β with hγ
  have hγapp : ∀ x, γ x = x₀⁻¹ * β x * x₀ := fun x => by
    rw [hγ, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hθγ : ∀ x, θ (γ x) = (w0L3 F)⁻¹ * α (θ x) * w0L3 F := fun x => by
    rw [hγapp, map_mul, map_mul, map_inv, hβθ, hx₀]
  have hγDc : ∀ d ∈ D, γ d * (d ^ m)⁻¹ ∈ Subgroup.center X := by
    intro d hd
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hθγ, hmD _ ((hθD d).mpr hd),
      mul_inv_cancel]
  have hγn : ∀ n : X, (θ n)⁻¹ * θ (γ n) ∈ dL3 F → n⁻¹ * γ n ∈ D := fun n h => by
    rw [← hθD, map_mul, map_inv]
    exact h
  have hγx₀ : x₀⁻¹ * γ x₀ ∈ D := hγn x₀ (by rw [hθγ, hx₀]; exact hmw)
  have hγc : c⁻¹ * γ c ∈ D := hγn c (by rw [hθγ, hc]; exact hmc)
  set K' := Subgroup.closure {x | ∃ d ∈ D, x = d * c * d⁻¹ * c⁻¹} with hK'
  have hK'D : K' ≤ D := by
    rw [hK', Subgroup.closure_le]
    rintro _ ⟨d, hd, rfl⟩
    have e : d * c * d⁻¹ * c⁻¹ = d * (c * d⁻¹ * c⁻¹) := by group
    rw [SetLike.mem_coe, e]
    exact D.mul_mem hd (hcD _ (D.inv_mem hd))
  have hγK : ∀ k ∈ K', γ k = k ^ m := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      exact gamma_commutator hDab hcD γ m hγDc hγc hd
    | one => rw [map_one, _root_.one_zpow]
    | mul x y hx hy ihx ihy =>
      rw [map_mul, ihx, ihy, Commute.mul_zpow (hDab x (hK'D hx) y (hK'D hy))]
    | inv x hx ihx => rw [map_inv, ihx, _root_.inv_zpow]
  set P := (dL3 F ⊔ Subgroup.zpowers (cyc3L3 F)).comap θ with hP
  have hN3 : Nat.Coprime 3 P.index := by
    rw [hP, Subgroup.index_comap_of_surjective _ hθ, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact not_three_dvd_index_dL3_sup h3
  have hPform : ∀ x ∈ P, ∃ d ∈ D, ∃ k : ℤ, x = d * c ^ k := by
    intro x hx
    have hN : Subgroup.zpowers (cyc3L3 F) ≤
        Subgroup.normalizer ((dL3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
      rw [Subgroup.zpowers_le]
      exact A4.mem_normalizer_of_conj_mem fun d hd => cyc3L3_conj_mem_dL3 hd
    have hx' : θ x ∈ ((dL3 F ⊔ Subgroup.zpowers (cyc3L3 F) : Subgroup _) :
        Set (projectiveSL 3 F)) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hx'
    obtain ⟨db, hdb, _, ⟨k, rfl⟩, he⟩ := hx'
    refine ⟨x * c ^ (-k), ?_, k, by group⟩
    rw [← hθD, map_mul, map_zpow, hc, ← he]
    simpa using hdb
  have hPK : ⁅P, P⁆ ≤ K' := commutator_le_closure hDab hcD hcD' hPform
  have hzN : ∀ z ∈ θ.ker, z ^ P.index ∈ K' := fun z hz =>
    hPK (pow_index_mem_commutator hperf (hker hz) P)
  have hγA : ∀ a ∈ A, γ a = a ^ m := by
    intro a ha
    have haD := hAD ha
    obtain ⟨eb₁, heb₁, eb₂, heb₂, hdec⟩ := exists_commutator_mul_of_mem_dL3 ((hθD a).mpr haD)
    obtain ⟨e₁, rfl⟩ := hθ eb₁
    obtain ⟨e₂, rfl⟩ := hθ eb₂
    have he₁ := (hθD e₁).mp heb₁
    have he₂ := (hθD e₂).mp heb₂
    have hk₁D : e₁ * c * e₁⁻¹ * c⁻¹ ∈ D := hK'D (Subgroup.subset_closure ⟨e₁, he₁, rfl⟩)
    have hk₂D : e₂ * x₀ * e₂⁻¹ * x₀⁻¹ ∈ D := by
      have e : e₂ * x₀ * e₂⁻¹ * x₀⁻¹ = e₂ * (x₀ * e₂⁻¹ * x₀⁻¹) := by group
      rw [e]
      exact D.mul_mem he₂ (hx₀D _ (D.inv_mem he₂))
    set k₁ := e₁ * c * e₁⁻¹ * c⁻¹ with hk₁
    set k₂ := e₂ * x₀ * e₂⁻¹ * x₀⁻¹ with hk₂
    have hθk : θ (k₁ * k₂) = θ a := by
      rw [hdec, hk₁, hk₂]
      simp only [map_mul, map_inv, hc, hx₀]
    obtain ⟨z, hz, hza⟩ : ∃ z ∈ θ.ker, a = k₁ * k₂ * z := by
      refine ⟨(k₁ * k₂)⁻¹ * a, ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθk, inv_mul_cancel]
    have hzD : z ∈ D := (hθD z).mp (by rw [MonoidHom.mem_ker.mp hz]; exact (dL3 F).one_mem)
    have hγk₁ : γ k₁ = k₁ ^ m := gamma_commutator hDab hcD γ m hγDc hγc he₁
    have hγk₂ : γ k₂ = k₂ ^ m := gamma_commutator hDab hx₀D γ m hγDc hγx₀ he₂
    have hβz : β z ∈ θ.ker := by
      rw [MonoidHom.mem_ker, hβθ, MonoidHom.mem_ker.mp hz, map_one]
    have hβzc := hker hβz
    have hγz : γ z = β z := by
      rw [hγapp]
      have h := E2.TorusCover.conj_of_central hβzc x₀⁻¹
      simpa using h
    set w := (z ^ m)⁻¹ * β z with hw
    have hwk : w ∈ θ.ker := by
      rw [hw]
      exact θ.ker.mul_mem (θ.ker.inv_mem (θ.ker.zpow_mem hz m)) hβz
    have hwc := hker hwk
    have hγa : γ a = a ^ m * w := by
      rw [hza, map_mul, map_mul, hγk₁, hγk₂, hγz]
      have hc1 : Commute k₁ k₂ := hDab _ hk₁D _ hk₂D
      have hc2 : Commute (k₁ * k₂) z := hDab _ (D.mul_mem hk₁D hk₂D) _ hzD
      rw [hc2.mul_zpow, hc1.mul_zpow, hw]
      group
    have hw3 : w ^ 3 = 1 := by
      have h1 : (a ^ m * w) ^ 3 = 1 := by rw [← hγa, ← map_pow, hA a ha, map_one]
      have hcw : Commute (a ^ m) w := Subgroup.mem_center_iff.mp hwc (a ^ m)
      rw [hcw.mul_pow, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hA a ha, _root_.one_zpow, one_mul] at h1
      exact h1
    have hwN : w ^ P.index = 1 := by
      have h1 := hγK _ (hzN z hz)
      have h2 : β (z ^ P.index) = (z ^ P.index) ^ m := by
        rw [← h1, hγapp]
        have h := E2.TorusCover.conj_of_central (hker (θ.ker.pow_mem hβz P.index)) x₀⁻¹
        rw [map_pow]
        simpa using h.symm
      have hcw : Commute ((z ^ m)⁻¹) (β z) :=
        (Subgroup.mem_center_iff.mp hβzc ((z ^ m)⁻¹))
      rw [hw, hcw.mul_pow, ← map_pow, h2]
      group
    have hw1 : w = 1 := by
      have h1 : orderOf w ∣ Nat.gcd 3 P.index :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one hwN)
      rw [hN3, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact h1
    rw [hγa, hw1, mul_one]
  refine ⟨x₀, hx₀, A4.mem_normalizer_of_conj_mem fun a ha => ?_⟩
  have hinj : Function.Injective (fun b : A => (⟨b ^ m, A.zpow_mem b.2 m⟩ : A)) := by
    intro b₁ b₂ h
    have h1 : (b₁ : X) ^ m = (b₂ : X) ^ m := congrArg Subtype.val h
    rw [← hγA _ b₁.2, ← hγA _ b₂.2] at h1
    exact Subtype.ext (γ.injective h1)
  obtain ⟨⟨b, hb⟩, hbe⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨a, ha⟩
  have hab : a = b ^ m := (congrArg Subtype.val hbe).symm
  have h1 := hγA b hb
  rw [hγapp] at h1
  have h2 : x₀ * b ^ m * x₀⁻¹ = β b := by
    rw [← h1]
    group
  rw [hab, h2]
  exact hβA b hb

end Core

section Cover

variable [Finite X] {Y : Type} [Group Y]

theorem ker_le_of_complement {φ : X →* Y} (hker : φ.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card φ.ker)) {S D : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    (hDN : D ≤ Subgroup.normalizer (S : Set X)) (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S)
    (hDS : D ⊓ S = ⊥) : φ.ker ≤ D := by
  have hS2 : IsPGroup 2 S := hS.2.1
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [E2.TorusCover.conj_central (hker hy)]
  have hy' : y ∈ ((D ⊔ S : Subgroup X) : Set X) := hND hyN
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D S hDN] at hy'
  obtain ⟨d', hd', s, hs, rfl⟩ := hy'
  have hyo : Odd (orderOf (d' * s)) := by
    have := orderOf_dvd_natCard (⟨d' * s, hy⟩ : φ.ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have hcomm : Commute d' s := by
    have hc : ∀ g : X, g * (d' * s) = (d' * s) * g := Subgroup.mem_center_iff.1 (hker hy)
    have h1 : d' * (d' * s) = (d' * s) * d' := hc d'
    show d' * s = s * d'
    have : d' * d' * s = d' * s * d' := by rw [mul_assoc, h1]
    exact mul_left_cancel (a := d') (by rw [← mul_assoc, this, mul_assoc])
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hdo : Odd (orderOf d') := odd_orderOf_of_complement hS hDN hDS hd'
  have hpow : (d' * s) ^ orderOf d' = s ^ orderOf d' := by
    rw [hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
  have hs1 : s ^ orderOf d' = 1 := by
    rw [← hpow]
    refine eq_one_of_odd_of_pow_two_pow (m := m) (hyo.of_dvd_nat (orderOf_pow_dvd _)) ?_
    rw [hpow, ← pow_mul, mul_comm, pow_mul, hm', one_pow]
  have hso : orderOf s ∣ Nat.gcd (orderOf d') (2 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs1) (orderOf_dvd_of_pow_eq_one hm')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hdo)),
    Nat.dvd_one, orderOf_eq_one_iff] at hso
  have hsD : s ∈ D := by
    rw [hso]
    exact D.one_mem
  exact D.mul_mem hd' hsD

theorem card_projUpperTriangular_three {F : Type} [Field F] [Finite F] [CharP F 2] :
    Nat.card (projUpperTriangular 3 F) =
      Nat.card (dL3 F) * Nat.card (projUnitriangular 3 F) := by
  have hB : projUpperTriangular 3 F = dL3 F ⊔ projUnitriangular 3 F :=
    le_antisymm projUpperTriangular_le (sup_le dL3_le_projUpperTriangular
      (Subgroup.map_mono (unitriangular_le_upperTriangular 3 F)))
  have h := E2.BorelLift.card_sup_mul_card_inf (dL3_le_normalizer (F := F))
  rw [dL3_inf, Subgroup.card_bot, mul_one] at h
  rw [hB, h]

omit [Finite X] in
theorem map_conj_eq_of_mem {P : Subgroup X} {g : X} (hg : g ∈ P) :
    P.map (MulAut.conj g).toMonoidHom = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact P.mul_mem (P.mul_mem hg hy) (P.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conj_mem_semilinearAutGroup {F : Type} [Field F] (g : projectiveSL 3 F) :
    MulAut.conj g ∈ LinearFlag.semilinearAutGroup 3 F := by
  obtain ⟨g', rfl⟩ := proj_surjective 3 F g
  rw [conj_proj_eq_conjAut]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem exists_mem_normalizer_of_cover_psl3_three {n : ℕ} (hY : IsPSL 3 2 n Y) (hn : 2 ≤ n)
    (hperf : commutator X = ⊤) (φ : X →* Y) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker)) {S D A : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hDN : D ≤ Subgroup.normalizer (S : Set X))
    (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hAD : A ≤ D) (hA : ∀ a ∈ A, a ^ 3 = 1)
    (𝒜 : Set (MulAut Y))
    (h𝒜P : ∀ P : Subgroup Y, IsCoatom P →
      Subgroup.normalizer ((S.map φ : Subgroup Y) : Set Y) ≤ P →
        ∃ α ∈ 𝒜, P.map α.toMonoidHom ≠ P)
    (hlift : ∀ α ∈ 𝒜, ∃ β : MulAut X, (∀ x, φ (β x) = α (φ x)) ∧
      S.map β.toMonoidHom = S ∧ ∀ a ∈ A, β a ∈ A ⊔ S) :
    ∃ x : X, x ∉ Subgroup.normalizer (S : Set X) ∧ x ∈ Subgroup.normalizer (A : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_surjective φ hφ
  have hS2 : IsPGroup 2 S := hS.2.1
  set S' := S.map φ with hS'def
  have hNmap : ∀ x : X, φ x ∈ Subgroup.normalizer (S' : Set Y) ↔
      x ∈ Subgroup.normalizer (S : Set X) := fun x =>
    ⟨fun h => E2.TorusCover.mem_normalizer_of_map hker hodd hS2 h,
      fun h => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ h)⟩
  have hS'syl : IsSylowTwoOf S' ⊤ := isSylowTwoOf_map hφ hS
  have hZD : φ.ker ≤ D := ker_le_of_complement hker hodd hS hDN hND hDS
  have hDodd : Odd (Nat.card D) := odd_card_of_complement hS hDN hDS
  obtain ⟨F, _, _, _, ψ, hF, hψU, hRes, -⟩ := even_rank_two_residual_linear hY hS'syl
  obtain ⟨-, hUP, hmax, -⟩ := hRes
  have hNU : (Subgroup.normalizer (S' : Set Y)).map ψ.toMonoidHom = projUpperTriangular 3 F := by
    rw [Subgroup.map_equiv_normalizer_eq, hψU, normalizer_projUnitriangular 2]
  set P₀ := (projStabilizer (flagSpace 3 F ((0 : Fin 2) + 1))).map ψ.symm.toMonoidHom with hP₀
  have hP₀c : IsCoatom P₀ := by
    rw [← covBy_top_iff]
    exact (hmax P₀ (hUP 0)).mpr ⟨0, rfl⟩
  have hNP₀ : Subgroup.normalizer (S' : Set Y) ≤ P₀ := by
    intro x hx
    have h1 : ψ x ∈ projUpperTriangular 3 F := hNU ▸ Subgroup.mem_map_of_mem _ hx
    have h2 := projUpperTriangular_le_projStabilizer_flag (F := F) ((0 : Fin 2) + 1) h1
    exact ⟨ψ x, h2, by simp⟩
  obtain ⟨α, hα𝒜, hαP⟩ := h𝒜P P₀ hP₀c hNP₀
  obtain ⟨β, hβφ, hβS, hβA⟩ := hlift α hα𝒜
  have hαS' : S'.map α.toMonoidHom = S' := by
    rw [hS'def, Subgroup.map_map]
    have : α.toMonoidHom.comp φ = φ.comp β.toMonoidHom :=
      MonoidHom.ext fun x => (hβφ x).symm
    rw [this, ← Subgroup.map_map, hβS]
  set α₀ : MulAut (projectiveSL 3 F) := (ψ.symm.trans α).trans ψ with hα₀
  have hα₀app : ∀ y : Y, α₀ (ψ y) = ψ (α y) := fun y => by simp [hα₀]
  have hα₀U : (projUnitriangular 3 F).map α₀.toMonoidHom = projUnitriangular 3 F := by
    rw [← hψU]
    ext y
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨α u, ?_, by simp [hα₀]⟩
      rw [← hαS']
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ S'.map α.toMonoidHom := hαS'.symm ▸ hv
      obtain ⟨u, hu, rfl⟩ := hv'
      exact ⟨ψ u, ⟨u, hu, rfl⟩, by simp [hα₀]⟩
  have hα₀s : α₀ ∉ LinearFlag.semilinearAutGroup 3 F := by
    intro hs
    have h1 := CFSG.QuasithinUnique.Setup.X7Sec.semilinear_flag hs hα₀U
      (d := (0 : Fin 2) + 1) (by norm_num)
    apply hαP
    rw [hP₀, Subgroup.map_map]
    conv_rhs => rw [← h1, Subgroup.map_map]
    refine congrArg (fun f => (projStabilizer (flagSpace 3 F ((0 : Fin 2) + 1))).map f) ?_
    ext x
    simp [hα₀]
  have hnotN : ∀ x : X, x ∈ Subgroup.normalizer (S : Set X) → ψ (φ x) ∈ projUpperTriangular 3 F :=
    fun x hx => hNU ▸ Subgroup.mem_map_of_mem _ ((hNmap x).mpr hx)
  by_cases h3 : 3 ∣ 2 ^ n - 1
  swap
  ·
    obtain ⟨x₁, hx₁⟩ := hφ (ψ.symm (w0L3 F))
    refine ⟨x₁, fun h => w0L3_not_mem (F := F) ?_, A4.mem_normalizer_of_conj_mem fun a ha => ?_⟩
    · have := hnotN x₁ h
      rwa [hx₁, MulEquiv.apply_symm_apply] at this
    · have haD := hAD ha
      have ha1 : φ a = 1 := by
        have hN : φ a ∈ Subgroup.normalizer (S' : Set Y) := (hNmap a).mpr (hDN haD)
        have ho : Odd (orderOf (φ a)) :=
          (odd_orderOf_of_complement hS hDN hDS haD).of_dvd_nat (orderOf_map_dvd φ a)
        have h1 := pow_eq_one_of_isPSL3 hY hS'syl hN ho
        have hcop : Nat.Coprime 3 (2 ^ n - 1) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
        have h4 : orderOf (φ a) ∣ Nat.gcd 3 (2 ^ n - 1) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hA a ha, map_one]))
            (orderOf_dvd_of_pow_eq_one h1)
        rw [hcop, Nat.dvd_one] at h4
        exact orderOf_eq_one_iff.1 h4
      rw [E2.TorusCover.conj_of_central (hker ha1) x₁]
      exact ha
  have hF2 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3F : 3 ∣ Nat.card F - 1 := hF ▸ h3
  set DY := D.map φ with hDY
  have hDYN : DY ≤ Subgroup.normalizer (S' : Set Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hNmap d).mpr (hDN hd)
  have hDYodd : Odd (Nat.card DY) := hDodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hNS' : Subgroup.normalizer (S' : Set Y) = DY ⊔ S' := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hφ y
      have hx := hND ((hNmap x).mp hy)
      have := Subgroup.mem_map_of_mem φ hx
      rwa [Subgroup.map_sup] at this
    · exact sup_le hDYN Subgroup.le_normalizer
  have hcardDY : Nat.card DY = Nat.card (dL3 F) := by
    have hcardN : Nat.card (Subgroup.normalizer (S' : Set Y)) = Nat.card DY * Nat.card S' := by
      have h := E2.BorelLift.card_sup_mul_card_inf hDYN
      rw [E2.BorelLift.inf_eq_bot_of_odd hDYodd hS'syl.2.1, Subgroup.card_bot, mul_one] at h
      rw [hNS', h]
    have h1 : Nat.card (Subgroup.normalizer (S' : Set Y)) =
        Nat.card (projUpperTriangular 3 F) := by
      rw [← hNU, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    have h2 : Nat.card S' = Nat.card (projUnitriangular 3 F) := by
      rw [← hψU, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    rw [hcardN, card_projUpperTriangular_three, h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  set D₁ := DY.map ψ.toMonoidHom with hD₁
  have hD₁B : D₁ ≤ dL3 F ⊔ projUnitriangular 3 F :=
    (hNU ▸ Subgroup.map_mono hDYN).trans projUpperTriangular_le
  have hcardD₁ : Nat.card D₁ = Nat.card (dL3 F) := by
    rw [hD₁, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hcardDY]
  obtain ⟨u, hu, hDu⟩ := E2.BorelLift.exists_conj_of_card_eq isPGroup_projUnitriangular_three
    odd_card_dL3 dL3_le_normalizer hD₁B hcardD₁
  have huB : u ∈ projUpperTriangular 3 F :=
    Subgroup.map_mono (unitriangular_le_upperTriangular 3 F) hu
  set θ : X →* projectiveSL 3 F :=
    ((MulAut.conj u).toMonoidHom.comp ψ.toMonoidHom).comp φ with hθ
  have hθapp : ∀ x, θ x = u * ψ (φ x) * u⁻¹ := fun x => rfl
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨x, hx⟩ := hφ (ψ.symm (u⁻¹ * y * u))
    refine ⟨x, ?_⟩
    rw [hθapp, hx, MulEquiv.apply_symm_apply]
    group
  have hθker : θ.ker ≤ Subgroup.center X := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hθapp] at hx
    have h1 : ψ (φ x) = 1 := by
      have e : ψ (φ x) = u⁻¹ * (u * ψ (φ x) * u⁻¹) * u := by group
      rw [e, hx]
      group
    exact (MulEquiv.map_eq_one_iff ψ).mp h1
  have hθD : ∀ x, θ x ∈ dL3 F ↔ x ∈ D := by
    intro x
    constructor
    · intro h
      have h1 : ψ (φ x) ∈ D₁ := by
        rw [hDu]
        refine ⟨θ x, h, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hθapp]
        group
      obtain ⟨y, ⟨d, hd, rfl⟩, hy⟩ := h1
      have hφd : φ d = φ x := ψ.injective hy
      have hk : d⁻¹ * x ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφd, inv_mul_cancel]
      have := D.mul_mem hd (hZD hk)
      simpa using this
    · intro h
      have h1 : ψ (φ x) ∈ D₁ := ⟨φ x, ⟨x, h, rfl⟩, rfl⟩
      rw [hDu] at h1
      obtain ⟨d, hd, hde⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hde
      rw [hθapp, ← hde]
      simpa [mul_assoc] using hd
  have hβN : ∀ x ∈ Subgroup.normalizer (S : Set X), β x ∈ Subgroup.normalizer (S : Set X) := by
    intro x hx
    have h := Subgroup.map_equiv_normalizer_eq S β
    rw [hβS] at h
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  have hβD : D.map β.toMonoidHom ≤ D ⊔ S := by
    rintro _ ⟨d, hd, rfl⟩
    exact hND (hβN d (hDN hd))
  obtain ⟨s, hs, hDs⟩ := E2.BorelLift.exists_conj_of_card_eq hS2 hDodd hDN hβD
    (Subgroup.card_map_of_injective β.injective)
  set β₁ : MulAut X := MulAut.conj s * β with hβ₁
  have hβ₁app : ∀ x, β₁ x = s * β x * s⁻¹ := fun x => rfl
  have hβ₁D : ∀ d ∈ D, β₁ d ∈ D := by
    intro d hd
    have h1 : β d ∈ D.map (MulAut.conj s⁻¹).toMonoidHom := by
      rw [← hDs]
      exact ⟨d, hd, rfl⟩
    obtain ⟨d', hd', hd'e⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hd'e
    rw [hβ₁app, ← hd'e]
    simpa [mul_assoc] using hd'
  have hβ₁A : ∀ a ∈ A, β₁ a ∈ A := by
    intro a ha
    have h1 : β₁ a ∈ A ⊔ S := by
      rw [hβ₁app]
      exact (A ⊔ S).mul_mem ((A ⊔ S).mul_mem (Subgroup.mem_sup_right hs) (hβA a ha))
        ((A ⊔ S).inv_mem (Subgroup.mem_sup_right hs))
    have h2 := hβ₁D a (hAD ha)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A S (hAD.trans hDN)]
      at h1
    obtain ⟨a', ha', s', hs', he⟩ := h1
    dsimp only at he
    have hs'D : s' ∈ D := by
      have : s' = a'⁻¹ * β₁ a := by rw [← he]; group
      rw [this]
      exact D.mul_mem (D.inv_mem (hAD ha')) h2
    have hs'1 : s' = 1 := by
      have : s' ∈ D ⊓ S := ⟨hs'D, hs'⟩
      rwa [hDS, Subgroup.mem_bot] at this
    rw [← he, hs'1, mul_one]
    exact ha'
  set α₁ : MulAut (projectiveSL 3 F) :=
    MulAut.conj (θ s) * MulAut.conj u * α₀ * (MulAut.conj u)⁻¹ with hα₁
  have hβ₁θ : ∀ x, θ (β₁ x) = α₁ (θ x) := by
    intro x
    rw [hβ₁app, map_mul, map_mul, map_inv, hθapp (β x), hβφ, ← hα₀app]
    simp only [hα₁, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
      MulAut.conj_symm_apply, hθapp]
    group
  have hθsU : θ s ∈ projUnitriangular 3 F := by
    rw [hθapp]
    have h1 : ψ (φ s) ∈ projUnitriangular 3 F := by
      rw [← hψU]
      exact ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
    exact (projUnitriangular 3 F).mul_mem ((projUnitriangular 3 F).mul_mem hu h1)
      ((projUnitriangular 3 F).inv_mem hu)
  have hα₁U : (projUnitriangular 3 F).map α₁.toMonoidHom = projUnitriangular 3 F := by
    rw [hα₁, CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      map_inv_eq_of_map_eq (map_conj_eq_of_mem hu), hα₀U, map_conj_eq_of_mem hu,
      map_conj_eq_of_mem hθsU]
  have hα₁s : α₁ ∉ LinearFlag.semilinearAutGroup 3 F := by
    intro h
    apply hα₀s
    have e : α₀ = (MulAut.conj u)⁻¹ * (MulAut.conj (θ s))⁻¹ * α₁ * MulAut.conj u := by
      rw [hα₁]
      group
    rw [e]
    have hc1 := conj_mem_semilinearAutGroup u
    have hc2 := conj_mem_semilinearAutGroup (θ s)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc1)
      (Subgroup.inv_mem _ hc2)) h) hc1
  obtain ⟨x₀, hx₀, hx₀A⟩ := exists_lift_w0_mem_normalizer hF2 h3F hperf θ hθs hθker hθD hDab
    hAD hA β₁ α₁ hβ₁θ hβ₁D hβ₁A hα₁U hα₁s
  refine ⟨x₀, fun h => w0L3_not_mem (F := F) ?_, hx₀A⟩
  rw [← hx₀, hθapp]
  exact (projUpperTriangular 3 F).mul_mem ((projUpperTriangular 3 F).mul_mem huB (hnotN x₀ h))
    ((projUpperTriangular 3 F).inv_mem huB)

end Cover

end CFSG.Quasithin.H13.KG4413
