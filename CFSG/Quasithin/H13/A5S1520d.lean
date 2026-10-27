module

public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.G2A5
public import CFSG.Quasithin.H13.A5S1520b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.SectionRank.Ccomm
open scoped commutatorElement

section General

variable {Y : Type*} [Group Y]

theorem abel_of_eq_iff {a b : Y} :
    Abelianization.of a = Abelianization.of b ↔ a⁻¹ * b ∈ commutator Y :=
  QuotientGroup.eq

theorem abel_of_eq_one_iff {a : Y} : Abelianization.of a = 1 ↔ a ∈ commutator Y :=
  QuotientGroup.eq_one_iff a

theorem abel_of_surjective : Function.Surjective (Abelianization.of : Y →* Abelianization Y) :=
  QuotientGroup.mk_surjective

theorem commutatorElement_inv_inv {a b : Y} (h : ⁅a, b⁆ ∈ Subgroup.center Y) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have hk := Subgroup.mem_center_iff.mp h (a⁻¹ * b⁻¹)
  calc ⁅a⁻¹, b⁻¹⁆ = a⁻¹ * b⁻¹ * ⁅a, b⁆ * (b * a) := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ * (a⁻¹ * b⁻¹) * (b * a) := by rw [hk]
    _ = ⁅a, b⁆ := by group

end General

theorem single_facts : (Pi.single 0 1 : Fin 2 → ZMod 3) ≠ 0 ∧ (Pi.single 1 1 : Fin 2 → ZMod 3) ≠ 0 ∧
    (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ZMod 3) ≠ 0 ∧
    (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1) : Fin 2 → ZMod 3) ≠ 0 := by
  decide

section Core

variable {K : Type*} [Group K] [Finite K]

theorem caseB_core {P : Subgroup K} [P.Normal] (hPp : IsPGroup 3 P) [Nontrivial P]
    (hrK : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2) {X : Subgroup ↥P}
    (hXs : IsSupercritical 3 X) {b c : K} (hb : b * b = 1) (hc : c ^ 3 = 1) (hbc : b * c = c * b)
    (hβ : ∃ x ∈ X, x⁻¹ * MulAut.conjNormal b x ∉ frattiniIn X)
    (hγ : ∃ x ∈ X, x⁻¹ * MulAut.conjNormal c x ∉ frattiniIn X)
    (hnoE9 : ∀ x y : K, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → b * x * b = x⁻¹ →
      b * y * b = y⁻¹ → x ≠ 1 → y ≠ 1 → x * y ≠ 1 → x * (y * y) ≠ 1 → False) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hXs.characteristic
  have hXp : IsPGroup 3 ↥X := hPp.to_subgroup X
  have : Fact (IsPGroup 3 ↥X) := ⟨hXp⟩
  have hrP : CFSG.Open.pRank 3 (⊤ : Subgroup ↥P) ≤ 2 := by
    rw [pRank_top_subtype]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hrK
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  set βX := MulAut.characteristic X (MulAut.conjNormal b) with hβX
  set γX := MulAut.characteristic X (MulAut.conjNormal c) with hγX
  have hβXv : ∀ x : ↥X, (((βX x : ↥X) : ↥P) : K) = b * x * b⁻¹ := fun x => rfl
  have hγXv : ∀ x : ↥X, (((γX x : ↥X) : ↥P) : K) = c * x * c⁻¹ := fun x => rfl
  have hββ : ∀ x : ↥X, βX (βX x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [hβXv, hβXv, hbinv]
    calc b * (b * (x : K) * b) * b = (b * b) * x * (b * b) := by group
      _ = x := by rw [hb, one_mul, mul_one]
  have hγγγ : ∀ x : ↥X, γX (γX (γX x)) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [hγXv, hγXv, hγXv]
    have hc3 : c * c * c = 1 := by rw [← pow_three', hc]
    calc c * (c * (c * (x : K) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by
          group
      _ = x := by rw [hc3, one_mul, inv_one, mul_one]
  have hβγ : ∀ x : ↥X, βX (γX x) = γX (βX x) := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [hβXv, hγXv, hγXv, hβXv]
    have hcb : c⁻¹ * b⁻¹ = b⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hbc]
    calc b * (c * (x : K) * c⁻¹) * b⁻¹ = (b * c) * x * (c⁻¹ * b⁻¹) := by group
      _ = (c * b) * x * (b⁻¹ * c⁻¹) := by rw [hbc, hcb]
      _ = c * (b * x * b⁻¹) * c⁻¹ := by group
  have hXexp : ∀ x : ↥X, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hXs.pow_eq_one x x.2)
  set βW := Abelianization.map βX.toMonoidHom with hβW
  set γW := Abelianization.map γX.toMonoidHom with hγW
  have hβWof : ∀ x, βW (Abelianization.of x) = Abelianization.of (βX x) := fun x => rfl
  have hγWof : ∀ x, γW (Abelianization.of x) = Abelianization.of (γX x) := fun x => rfl
  have hWexp : ∀ w : Abelianization ↥X, w ^ 3 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := abel_of_surjective w
    rw [← map_pow, hXexp, map_one]
  have hββW : ∀ w, βW (βW w) = w := by
    intro w
    obtain ⟨x, rfl⟩ := abel_of_surjective w
    rw [hβWof, hβWof, hββ]
  have hγγγW : ∀ w, γW (γW (γW w)) = w := by
    intro w
    obtain ⟨x, rfl⟩ := abel_of_surjective w
    rw [hγWof, hγWof, hγWof, hγγγ]
  have hβγW : ∀ w, βW (γW w) = γW (βW w) := by
    intro w
    obtain ⟨x, rfl⟩ := abel_of_surjective w
    rw [hγWof, hβWof, hβWof, hγWof, hβγ]
  have hnt : ∀ α : MulAut ↥P, (∃ x ∈ X, x⁻¹ * α x ∉ frattiniIn X) →
      ∃ w, Abelianization.map (MulAut.characteristic X α).toMonoidHom w ≠ w := by
    rintro α ⟨x, hx, hxn⟩
    refine ⟨Abelianization.of ⟨x, hx⟩, fun h => hxn ?_⟩
    have h1 : Abelianization.of (MulAut.characteristic X α ⟨x, hx⟩) =
        Abelianization.of (⟨x, hx⟩ : ↥X) := h
    rw [abel_of_eq_iff] at h1
    have h2 := Subgroup.inv_mem _ (commutator_le_frattini_of_isPGroup (p := 3) h1)
    rw [mul_inv_rev, inv_inv] at h2
    exact ⟨_, h2, rfl⟩
  have hβW1 := hnt _ hβ
  have hγW1 := hnt _ hγ
  have hcX : ∀ c' : ↥P, c' ∈ X → (c' : K) ≠ c := by
    rintro c' hc' rfl
    obtain ⟨x, hx, hxn⟩ := hγ
    apply hxn
    refine ⟨⁅(⟨x, hx⟩ : ↥X)⁻¹, ⟨c', hc'⟩⁆, commutator_le_frattini_of_isPGroup (p := 3)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_subtype, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_inv, MulAut.conjNormal_apply]
    group
  rcases hXs.iso_cases (by norm_num) hPp hrP with hZ3 | hE9 | hX27
  ·
    obtain ⟨e⟩ := hZ3
    have hcardX : Nat.card ↥X = 3 := by
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]
    have hcardW : Nat.card (Abelianization ↥X) ≤ 3 :=
      hcardX ▸ Nat.card_le_card_of_surjective _ abel_of_surjective
    obtain ⟨w0, hw0⟩ := hγW1
    have hw01 : w0 ≠ 1 := fun h => hw0 (by rw [h, map_one])
    by_cases hm : γW w0 ∈ Subgroup.zpowers w0
    · exact hw0 (fix_of_mem_zpowers hγγγW (hWexp w0) hm)
    · have := Nat.card_le_card_of_injective _ (pair_injective hWexp hw01 hm)
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
      omega
  ·
    obtain ⟨e⟩ := hE9
    have hXc : ∀ x y : ↥X, x * y = y * x := fun x y =>
      e.injective (by rw [map_mul, map_mul, mul_comm])
    have hcomm : commutator ↥X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hXc y x
    have hcardX : Nat.card ↥X = 9 := by
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
      norm_num
    have hcardW : Nat.card (Abelianization ↥X) ≤ 9 :=
      hcardX ▸ Nat.card_le_card_of_surjective _ abel_of_surjective
    have hinv := inv_of_commute hWexp hcardW βW γW hββW hγγγW hβγW hβW1 hγW1
    have hβinv : ∀ x : ↥X, βX x = x⁻¹ := by
      intro x
      have h1 := hinv (Abelianization.of x)
      rw [hβWof, ← map_inv, abel_of_eq_iff, hcomm, Subgroup.mem_bot] at h1
      exact inv_mul_eq_one.mp h1
    set x0 := e.symm (Multiplicative.ofAdd (Pi.single 0 1))
    set y0 := e.symm (Multiplicative.ofAdd (Pi.single 1 1))
    have hne : ∀ u : Fin 2 → ZMod 3, u ≠ 0 →
        (((e.symm (Multiplicative.ofAdd u) : ↥X) : ↥P) : K) ≠ 1 := by
      intro u hu h
      apply hu
      have h1 : e.symm (Multiplicative.ofAdd u) = 1 := Subtype.ext (Subtype.ext h)
      have h2 := congrArg e h1
      rw [MulEquiv.apply_symm_apply, map_one] at h2
      exact h2
    have hbX : ∀ x : ↥X, b * ((x : ↥P) : K) * b = ((x : ↥P) : K)⁻¹ := by
      intro x
      have h1 := congrArg (fun z : ↥X => ((z : ↥P) : K)) (hβinv x)
      rw [hβXv, hbinv] at h1
      rw [h1]
      rfl
    refine hnoE9 ((x0 : ↥P) : K) ((y0 : ↥P) : K)
      (congrArg (fun z : ↥X => ((z : ↥P) : K)) (hXexp x0))
      (congrArg (fun z : ↥X => ((z : ↥P) : K)) (hXexp y0))
      (congrArg (fun z : ↥X => ((z : ↥P) : K)) (hXc x0 y0)) (hbX x0) (hbX y0)
      (hne _ single_facts.1) (hne _ single_facts.2.1) ?_ ?_
    · have e1 : x0 * y0 = e.symm (Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1)) := by
        rw [ofAdd_add, map_mul]
      have := hne _ single_facts.2.2.1
      rwa [← e1] at this
    · have e1 : x0 * (y0 * y0) = e.symm (Multiplicative.ofAdd
          (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1))) := by
        rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
      have := hne _ single_facts.2.2.2
      rwa [← e1] at this
  ·
    obtain ⟨hext, hcard27, -⟩ := hX27
    have hcenter : Nat.card (Subgroup.center ↥X) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥X
    have hcomm_le : commutator ↥X ≤ Subgroup.center ↥X := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ⁅(x : ↥P), (y : ↥P)⁆ ∈ centerOf X :=
        hXs.commutator_le (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _))
      have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (g : ↥P) g.2
      have e : ((⁅x, y⁆ : ↥X) : ↥P) = ⁅(x : ↥P), (y : ↥P)⁆ := map_commutatorElement X.subtype x y
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, e]
      exact h2
    have hcentral : ∀ f ∈ commutator ↥X, ∀ g : ↥X, g * f = f * g := fun f hf g =>
      Subgroup.mem_center_iff.mp (hcomm_le hf) g
    have hcomm_ne : commutator ↥X ≠ ⊥ := by
      intro h
      have htop : Subgroup.center ↥X = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro x
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : ⁅g, x⁆ ∈ commutator ↥X :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      rw [htop, Subgroup.card_top, hcard27] at hcenter
      norm_num at hcenter
    have hcard_comm : Nat.card ↥(commutator ↥X) = 3 := by
      have hdvd : Nat.card ↥(commutator ↥X) ∣ 3 := hcenter ▸ Subgroup.card_dvd_of_le hcomm_le
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hcomm_ne
      · exact h
    have hcardW : Nat.card (Abelianization ↥X) ≤ 9 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥X)
      rw [hcard27, hcard_comm] at h
      norm_num at h
      have : Nat.card (Abelianization ↥X) = Nat.card (↥X ⧸ commutator ↥X) := rfl
      omega
    have hinv := inv_of_commute hWexp hcardW βW γW hββW hγγγW hβγW hβW1 hγW1
    have hβX1 : ∀ x : ↥X, x * βX x ∈ commutator ↥X := by
      intro x
      have h1 := hinv (Abelianization.of x)
      rw [hβWof, ← map_inv, abel_of_eq_iff] at h1
      have := Subgroup.inv_mem _ h1
      rwa [mul_inv_rev, inv_inv, inv_inv] at this
    have hβfix : ∀ f ∈ commutator ↥X, βX f = f := by
      have hle : commutator ↥X ≤ MonoidHom.eqLocus βX.toMonoidHom (MonoidHom.id _) := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        show βX ⁅x, y⁆ = ⁅x, y⁆
        rw [map_commutatorElement]
        have ex : βX x = x⁻¹ * (x * βX x) := by group
        have ey : βX y = y⁻¹ * (y * βX y) := by group
        rw [ex, ey, commutatorElement_mul_center_left _ (hcomm_le (hβX1 x)),
          commutatorElement_mul_center_right _ (hcomm_le (hβX1 y))]
        exact commutatorElement_inv_inv (hcomm_le (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top _) (Subgroup.mem_top _)))
      exact fun f hf => hle hf
    obtain ⟨w0, hw01, hw0⟩ := exists_fixed_ne_one hWexp γW hγγγW hγW1
    obtain ⟨x0, rfl⟩ := abel_of_surjective w0
    have hx0 : x0 ∉ commutator ↥X := fun h => hw01 (abel_of_eq_one_iff.2 h)
    have hf : x0⁻¹ * γX x0 ∈ commutator ↥X := by
      have h1 : Abelianization.of (γX x0) = Abelianization.of x0 := hw0
      rw [abel_of_eq_iff] at h1
      have := Subgroup.inv_mem _ h1
      rwa [mul_inv_rev, inv_inv] at this
    set x := x0⁻¹ * βX x0 with hxdef
    have hγx : γX x = x := by
      have e1 : γX x0 = x0 * (x0⁻¹ * γX x0) := by group
      calc γX x = (γX x0)⁻¹ * βX (γX x0) := by rw [hxdef, map_mul, map_inv, hβγ]
        _ = (x0 * (x0⁻¹ * γX x0))⁻¹ * βX (x0 * (x0⁻¹ * γX x0)) := by rw [← e1]
        _ = (x0⁻¹ * γX x0)⁻¹ * x * βX (x0⁻¹ * γX x0) := by
          rw [map_mul βX x0, hxdef]
          group
        _ = (x0⁻¹ * γX x0)⁻¹ * x * (x0⁻¹ * γX x0) := by rw [hβfix _ hf]
        _ = (x0⁻¹ * γX x0)⁻¹ * (x * (x0⁻¹ * γX x0)) := by group
        _ = (x0⁻¹ * γX x0)⁻¹ * ((x0⁻¹ * γX x0) * x) := by rw [hcentral _ hf x]
        _ = x := by group
    have hxnot : x ∉ commutator ↥X := by
      intro hxc
      apply hx0
      have h1 : x0⁻¹ * x0⁻¹ ∈ commutator ↥X := by
        have := Subgroup.mul_mem _ hxc (Subgroup.inv_mem _ (hβX1 x0))
        convert this using 1
        rw [hxdef]
        group
      have h2 : x0⁻¹ * x0⁻¹ = x0 := by
        calc x0⁻¹ * x0⁻¹ = x0⁻¹ * x0⁻¹ * x0 ^ 3 := by rw [hXexp x0, mul_one]
          _ = x0 := by group
      rw [← h2]
      exact h1
    obtain ⟨z0, hz01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcomm_ne
    have hz0 : (z0 : ↥X) ≠ 1 := fun h => hz01 (Subtype.ext h)
    have hzpow : Subgroup.zpowers (z0 : ↥X) = commutator ↥X := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z0.2) ?_
      rw [hcard_comm, Nat.card_zpowers, orderOf_eq_prime (hXexp _) hz0]
    have hγz : γX z0 = z0 := by
      refine fix_of_mem_zpowers (γ := γX.toMonoidHom) hγγγ (hXexp _) ?_
      rw [hzpow]
      have h2 : (z0 : ↥X) ∈ (commutator ↥X).comap γX.toMonoidHom := by
        rw [(Subgroup.characteristic_iff_comap_eq.1 inferInstance γX)]
        exact z0.2
      exact h2
    have hxc : ((x : ↥P) : K) * c = c * ((x : ↥P) : K) := by
      have h1 := congrArg (fun z : ↥X => ((z : ↥P) : K)) hγx
      rw [hγXv] at h1
      calc ((x : ↥P) : K) * c = c * x * c⁻¹ * c := by rw [h1]
        _ = c * ((x : ↥P) : K) := by group
    have hzc : (((z0 : ↥X) : ↥P) : K) * c = c * (((z0 : ↥X) : ↥P) : K) := by
      have h1 := congrArg (fun z : ↥X => ((z : ↥P) : K)) hγz
      rw [hγXv] at h1
      calc (((z0 : ↥X) : ↥P) : K) * c = c * (z0 : ↥X) * c⁻¹ * c := by rw [h1]
        _ = c * (((z0 : ↥X) : ↥P) : K) := by group
    have hxz : ((x : ↥P) : K) * (((z0 : ↥X) : ↥P) : K) =
        (((z0 : ↥X) : ↥P) : K) * ((x : ↥P) : K) :=
      congrArg (fun z : ↥X => ((z : ↥P) : K)) (hcentral _ z0.2 x)
    have hpow : ∀ z : ↥X, (((z : ↥P) : K)) ^ 3 = 1 := fun z =>
      congrArg (fun z : ↥X => ((z : ↥P) : K)) (hXexp z)
    have hz1 : (((z0 : ↥X) : ↥P) : K) ≠ 1 := fun h => hz0 (Subtype.ext (Subtype.ext h))
    have hxz' : ((x : ↥P) : K) ∉ Subgroup.zpowers (((z0 : ↥X) : ↥P) : K) := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      apply hxnot
      rw [← hzpow]
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      rw [← hk]
      simp
    have hc' : c ∉ Subgroup.zpowers (((z0 : ↥X) : ↥P) : K) ⊔ Subgroup.zpowers ((x : ↥P) : K) := by
      intro h
      have hle : Subgroup.zpowers (((z0 : ↥X) : ↥P) : K) ⊔ Subgroup.zpowers ((x : ↥P) : K) ≤
          (X.map P.subtype) := sup_le (Subgroup.zpowers_le.mpr ⟨_, (z0 : ↥X).2, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨_, x.2, rfl⟩)
      obtain ⟨c', hc'X, hc'c⟩ := hle h
      exact hcX c' hc'X hc'c
    have h3 := three_le_pRank hxz hxc hzc (hpow x) (hpow _) hc hz1 hxz' hc'
    omega

end Core

end CFSG.Quasithin.H13.A5
