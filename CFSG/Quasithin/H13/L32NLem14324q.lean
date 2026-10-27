module

public import CFSG.Quasithin.Vol2.Ch1Five
public import CFSG.Quasithin.H13.L32NLem14324p
public import CFSG.Quasithin.Vol2.Ch1Chief

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem card_SL_two_zmod (r : ℕ) [Fact r.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) = r * (r ^ 2 - 1) := by
  let := Fintype.ofFinite (ZMod r)
  have hq : 1 < Fintype.card (ZMod r) := Fintype.one_lt_card
  have hc : Fintype.card (ZMod r) = r := ZMod.card r
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    show Fintype.card (ZMod r) ^ 2 - Fintype.card (ZMod r) =
      Fintype.card (ZMod r) * (Fintype.card (ZMod r) - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm, hc]

theorem ne_40320 (r : ℕ) : r * (r ^ 2 - 1) ≠ 40320 := by
  intro h
  rcases (by omega : r ≤ 34 ∨ 35 ≤ r) with hr | hr
  · interval_cases r <;> norm_num at h
  · have h1 : 35 ^ 2 - 1 ≤ r ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hr 2) 1
    have h2 : 35 * (35 ^ 2 - 1) ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul hr h1
    rw [h] at h2
    norm_num at h2

section Abstract

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (M : S8Five.Model5 Γ) {Q : Type} [Group Q] [Finite Q]

theorem a9_pow_ne_b9 (n : ℕ) : S8Five.a9 ^ n ≠ S8Five.b9 := by
  have h3 : S8Five.a9 ^ 3 = 1 := S8Five.e9_facts.1
  have key : ∀ i : Fin 3, S8Five.a9 ^ (i : ℕ) ≠ S8Five.b9 := by decide
  rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
  exact key ⟨n % 3, Nat.mod_lt n (by norm_num)⟩

theorem dvd_of_a9_b9 {m n : ℕ} (h : S8Five.a9 ^ m * S8Five.b9 ^ n = 1) : 3 ∣ m ∧ 3 ∣ n := by
  have h3a : S8Five.a9 ^ 3 = 1 := S8Five.e9_facts.1
  have h3b : S8Five.b9 ^ 3 = 1 := S8Five.e9_facts.2.1
  have hm : S8Five.a9 ^ m = S8Five.a9 ^ (m % 3) := by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, h3a, one_pow, mul_one]
  have hn : S8Five.b9 ^ n = S8Five.b9 ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3b, one_pow, mul_one]
  rw [hm, hn] at h
  obtain ⟨h1, h2⟩ := S8Five.e9_facts.2.2.2.2.2.2.2.2.2.2.2.2.2
    ⟨m % 3, Nat.mod_lt m (by norm_num)⟩ ⟨n % 3, Nat.mod_lt n (by norm_num)⟩ h
  exact ⟨Nat.dvd_of_mod_eq_zero (congrArg Fin.val h1), Nat.dvd_of_mod_eq_zero (congrArg Fin.val h2)⟩

theorem pow_eq_one_of_dvd {X : Type*} [Monoid X] {x : X} (hx : x ^ 3 = 1) {m : ℕ} (hm : 3 ∣ m) :
    x ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_mul, hx, one_pow]

theorem three_le_of_e9 (φ : Q →* (V ≃ₗ[ZMod 2] V)) {x y z : Q} (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hφx : φ x = M.ψ S8Five.a9) (hφy : φ y = M.ψ S8Five.b9)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hxz : x * z = z * x) (hyz : y * z = z * y) (hφz : φ z = 1) :
    3 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup Q) := by
  refine S8Five.three_le_pRank_of_triple hx3 hy3 hz3 hxy hxz hyz ?_ ?_ ?_
  · intro h
    have h1 : M.ψ S8Five.a9 = M.ψ 1 := by rw [← hφx, h, map_one, map_one]
    exact absurd (M.ψ_injective h1) (by decide)
  · intro n h
    apply a9_pow_ne_b9 n
    apply M.ψ_injective
    rw [map_pow, ← hφx, ← map_pow, h, hφy]
  · intro m n h
    apply hz1
    rw [← h]
    have h1 : M.ψ (S8Five.a9 ^ m * S8Five.b9 ^ n) = 1 := by
      rw [map_mul, map_pow, map_pow, ← hφx, ← hφy, ← map_pow, ← map_pow, ← map_mul, h, hφz]
    have h2 : S8Five.a9 ^ m * S8Five.b9 ^ n = 1 :=
      M.ψ_injective (h1.trans (map_one M.ψ).symm)
    obtain ⟨hm, hn⟩ := dvd_of_a9_b9 h2
    rw [pow_eq_one_of_dvd hx3 hm, pow_eq_one_of_dvd hy3 hn, one_mul]

variable {M}

theorem mem_of_cube' (φ : Q →* (V ≃ₗ[ZMod 2] V)) {Kb : Subgroup Q} (hKn : Kb.Normal)
    (hinj : ∀ k ∈ Kb, φ k = 1 → k = 1) (hrange : Kb.map φ = M.A)
    (hrk : CFSG.Assembly.pRank 3 (⊤ : Subgroup Q) ≤ 2) {y : Q} (hy3 : y ^ 3 = 1)
    (hyA : φ y ∈ M.A) : y ∈ Kb := by
  obtain ⟨k, hk, hke⟩ : φ y ∈ Kb.map φ := hrange ▸ hyA
  set c := k⁻¹ * y with hcdef
  have hφc : φ c = 1 := by rw [hcdef, map_mul, map_inv, hke, inv_mul_cancel]
  have hcK : ∀ x ∈ Kb, x * c = c * x := by
    intro x hx
    have h1 : x * c * x⁻¹ * c⁻¹ ∈ Kb := by
      have := hKn.conj_mem x⁻¹ (Kb.inv_mem hx) c
      rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
      exact Kb.mul_mem hx this
    have h2 := hinj _ h1 (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφc]; group)
    calc x * c = (x * c * x⁻¹ * c⁻¹) * (c * x) := by group
      _ = c * x := by rw [h2, one_mul]
  have hyc : y = k * c := by rw [hcdef]; group
  have hkc := hcK k hk
  have hk3 : k ^ 3 = 1 := by
    have h1 : k ^ 3 * c ^ 3 = 1 := by
      rw [← (Commute.mul_pow hkc 3), ← hyc, hy3]
    have h2 : φ (k ^ 3) = 1 := by
      have : k ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, map_inv, map_pow, hφc, one_pow, inv_one]
    exact hinj _ (Kb.pow_mem hk 3) h2
  have hc3 : c ^ 3 = 1 := by
    have h1 : k ^ 3 * c ^ 3 = 1 := by
      rw [← (Commute.mul_pow hkc 3), ← hyc, hy3]
    rwa [hk3, one_mul] at h1
  by_cases hc1 : c = 1
  · rw [hyc, hc1, mul_one]
    exact hk
  exfalso
  have ha : M.ψ S8Five.a9 ∈ Kb.map φ :=
    hrange ▸ ⟨S8Five.a9, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.1, rfl⟩
  have hb : M.ψ S8Five.b9 ∈ Kb.map φ :=
    hrange ▸ ⟨S8Five.b9, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.2.1, rfl⟩
  obtain ⟨x, hx, hφx⟩ := ha
  obtain ⟨w, hw, hφw⟩ := hb
  have hxw : x * w = w * x := by
    have h1 : x * w * (w * x)⁻¹ = 1 := hinj _ (Kb.mul_mem (Kb.mul_mem hx hw)
      (Kb.inv_mem (Kb.mul_mem hw hx))) (by
        rw [map_mul, map_inv, map_mul, map_mul, hφx, hφw, ← map_mul, ← map_mul,
          S8Five.e9_facts.2.2.1, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hx3 : x ^ 3 = 1 := hinj _ (Kb.pow_mem hx 3) (by
    rw [map_pow, hφx, ← map_pow, S8Five.e9_facts.1, map_one])
  have hw3 : w ^ 3 = 1 := hinj _ (Kb.pow_mem hw 3) (by
    rw [map_pow, hφw, ← map_pow, S8Five.e9_facts.2.1, map_one])
  have := three_le_of_e9 M φ hxw hx3 hw3 hφx hφw hc1 hc3 (hcK x hx) (hcK w hw) hφc
  omega

theorem inj_of_a36 (φ : Q →* (V ≃ₗ[ZMod 2] V)) {Kb : Subgroup Q}
    (hcc : Kb ∈ cComp (⊤ : Subgroup Q)) (hstrong : A36Strong Kb) (hrange : Kb.map φ = M.A)
    (hrk : CFSG.Assembly.pRank 3 (⊤ : Subgroup Q) ≤ 2) : ∀ k ∈ Kb, φ k = 1 → k = 1 := by
  classical
  set X := ↥Kb
  set φX : X →* (V ≃ₗ[ZMod 2] V) := φ.comp Kb.subtype with hφX
  have hφXr : ∀ α ∈ M.A, ∃ x : X, φX x = α := by
    intro α hα
    obtain ⟨k, hk, rfl⟩ : α ∈ Kb.map φ := hrange ▸ hα
    exact ⟨⟨k, hk⟩, rfl⟩
  have hφXA : ∀ x : X, φX x ∈ M.A := fun x => hrange ▸ ⟨x, x.2, rfl⟩
  set N := φX.ker with hN
  set R := CFSG.solvableRadical X with hR
  have hnc : M.ψ S8Five.a9 * M.ψ S8Five.n1 ≠ M.ψ S8Five.n1 * M.ψ S8Five.a9 := by
    rw [← map_mul, ← map_mul]
    intro h
    exact absurd (M.ψ_injective h) (by decide)
  set φA : X →* ↥M.A := φX.codRestrict M.A hφXA with hφA
  have hφAs : Function.Surjective φA := fun α => by
    obtain ⟨x, hx⟩ := hφXr α α.2
    exact ⟨x, Subtype.ext hx⟩
  have hkerA : φA.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have : IsSimpleGroup ↥M.A := M.isSimpleGroup_A
  have hAnc : ¬ IsMulCommutative ↥M.A := by
    rintro ⟨⟨hc⟩⟩
    apply hnc
    have := hc ⟨_, ⟨S8Five.a9, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.1, rfl⟩⟩
      ⟨_, ⟨S8Five.n1, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.2.2.1, rfl⟩⟩
    exact congrArg Subtype.val this
  have hN1 : N ≠ ⊤ := by
    intro htop
    apply hnc
    obtain ⟨x, hx⟩ := hφXr _ ⟨S8Five.a9, Equiv.Perm.mem_alternatingGroup.mpr
      S8Five.e9_facts.2.2.2.1, rfl⟩
    have h1 : φX x = 1 := (htop ▸ Subgroup.mem_top x : x ∈ N)
    rw [← hx, h1, one_mul, mul_one]
  have hRN : R ≤ N := by
    rw [← hkerA]
    have hRn : (R.map φA).Normal := Subgroup.Normal.map inferInstance φA hφAs
    have hRs : Group.IsSolvable ↥(R.map φA) := by
      have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
      exact Group.isSolvable_of_surjective (f := φA.subgroupMap R) (φA.subgroupMap_surjective R)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map φA) with h | h
    · exact (Subgroup.map_eq_bot_iff R).mp h
    · exfalso
      apply hAnc
      have hsA : Group.IsSolvable ↥M.A := by
        rw [h] at hRs
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
          (MulEquiv.surjective _)
      exact ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hsA) a b⟩⟩
  have hNR : N ≤ R := by
    obtain ⟨hsimp, -⟩ := A36A.simple_quotient_of_mem_cComp hcc
    have := hsimp
    have hNn : (N.map (QuotientGroup.mk' R)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' R)) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      apply hN1
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk' R x) ∈ N.map (QuotientGroup.mk' R) := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hnx' : n⁻¹ * x ∈ R := by
        rw [← QuotientGroup.eq]
        exact hnx
      have := N.mul_mem hn (hRN hnx')
      rwa [mul_inv_cancel_left] at this
  have hNR' : N = R := le_antisymm hNR hRN
  have hcardX : Nat.card X = Nat.card R * 20160 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hφAs
    rw [hkerA, hNR', M.card_A] at h1
    exact h1.symm
  obtain ⟨hconc, ⟨-, -, hcase, -, -⟩, -⟩ := hstrong
  have hFR : CFSG.fittingSubgroup X ≤ R :=
    A3.le_solvableRadical inferInstance inferInstance
  have hno3 : ¬ (N ≤ Subgroup.center X ∧ Nat.card N = 3) := by
    rintro ⟨hNZ, hN3⟩
    have hker : ∀ c, φX c = 1 → ∀ w, c * w = w * c := fun c hc w =>
      (Subgroup.mem_center_iff.mp (hNZ hc) w).symm
    have hker3 : ∀ c, φX c = 1 → c ^ 3 = 1 := fun c hc => by
      have := pow_card_eq_one' (G := ↥N) (x := ⟨c, hc⟩)
      rw [hN3] at this
      exact congrArg Subtype.val this
    have hmem : ∀ σ : Equiv.Perm (Fin 8), Equiv.Perm.sign σ = 1 → ∃ x : X, φX x = M.ψ σ :=
      fun σ hσ =>
      hφXr _ ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, rfl⟩
    obtain ⟨xa, hat⟩ := hmem S8Five.a9 S8Five.e9_facts.2.2.2.1
    obtain ⟨xb, hxb⟩ := hmem S8Five.b9 S8Five.e9_facts.2.2.2.2.1
    obtain ⟨xn₁, hxn₁⟩ := hmem S8Five.n1 S8Five.e9_facts.2.2.2.2.2.1
    obtain ⟨xn₂, hxn₂⟩ := hmem S8Five.n2 S8Five.e9_facts.2.2.2.2.2.2.1
    have hconjψ : ∀ σ τ : Equiv.Perm (Fin 8),
        M.ψ σ * M.ψ τ * (M.ψ σ)⁻¹ = M.ψ (σ * τ * σ⁻¹) := fun σ τ => by
      rw [map_mul, map_mul, map_inv]
    obtain ⟨hab, ha3, hb3⟩ := S8Five.comm_of_inverters φX hker hker3
      (a := xa) (b := xb) (n₁ := xn₁) (n₂ := xn₂)
      (by rw [hat, hxb, ← map_mul, ← map_mul, S8Five.e9_facts.2.2.1])
      (by rw [hat, ← map_pow, S8Five.e9_facts.1, map_one])
      (by rw [hxb, ← map_pow, S8Five.e9_facts.2.1, map_one])
      (by rw [hxn₁, hat, hconjψ, S8Five.e9_facts.2.2.2.2.2.2.2.1, map_inv])
      (by rw [hxn₁, hxb, hconjψ, S8Five.e9_facts.2.2.2.2.2.2.2.2.1])
      (by rw [hxn₂, hxb, hconjψ, S8Five.e9_facts.2.2.2.2.2.2.2.2.2.2.1, map_inv])
    obtain ⟨z, hz1⟩ : ∃ z : ↥N, z ≠ 1 := by
      by_contra hall
      push Not at hall
      have : Nat.card ↥N = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by
        rw [hall a, hall b]⟩, ⟨1⟩⟩
      omega
    have hz1' : (z : X) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hz3 : (z : X) ^ 3 = 1 := hker3 _ z.2
    have := three_le_of_e9 M φ (x := (xa : Q)) (y := (xb : Q)) (z := ((z : X) : Q))
      (by exact_mod_cast congrArg Subtype.val hab) (by exact_mod_cast congrArg Subtype.val ha3)
      (by exact_mod_cast congrArg Subtype.val hb3) hat hxb
      (fun h => hz1' (Subtype.ext h)) (by exact_mod_cast congrArg Subtype.val hz3)
      (by exact_mod_cast congrArg Subtype.val (hker _ z.2 xa).symm)
      (by exact_mod_cast congrArg Subtype.val (hker _ z.2 xb).symm) z.2
    omega
  rcases hcase with ⟨-, hidx⟩ | ⟨hFZ, hFRe, hF13⟩
  ·
    have hR2 : Nat.card R = 2 * Nat.card (CFSG.fittingSubgroup X) := by
      have h1 := Subgroup.relIndex_mul_card (H := CFSG.fittingSubgroup X) (K := R)
      rw [hidx, inf_eq_left.mpr hFR] at h1
      omega
    exfalso
    rcases hconc with ⟨-, hsimp, -⟩ | ⟨hcomp, hZ3, -⟩ | h34
    ·
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
      · rw [h, Subgroup.card_bot] at hR2
        omega
      · exact hN1 (hNR'.trans h)
    ·
      have hqs : CFSG.IsQuasisimple X := hcomp.1
      have hRZ : R ≤ Subgroup.center X := by
        obtain ⟨-, hsZ, a, b, hab⟩ := hqs
        have := hsZ
        have hRn : (R.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
          Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
            (R.map (QuotientGroup.mk' (Subgroup.center X))) with h | h
        · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
          exact h
        · exfalso
          have hRs : Group.IsSolvable ↥(R.map (QuotientGroup.mk' (Subgroup.center X))) := by
            have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
            exact Group.isSolvable_of_surjective
              (f := (QuotientGroup.mk' (Subgroup.center X)).subgroupMap R)
              ((QuotientGroup.mk' _).subgroupMap_surjective R)
          rw [h] at hRs
          have hs : Group.IsSolvable (X ⧸ Subgroup.center X) :=
            Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
              (MulEquiv.surjective _)
          exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b)
      have hdvd : Nat.card R ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hRZ
      rw [hR2] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card (CFSG.fittingSubgroup X) := Nat.card_pos
      have h1 : Nat.card (CFSG.fittingSubgroup X) = 1 := by omega
      rw [h1] at hdvd
      norm_num at hdvd
    · obtain ⟨r, hr, -, χ₀, hχ₀, hχker⟩ := exists_sl2_surjection_of_case34 h34
      have : Fact r.Prime := ⟨hr⟩
      have h1 := Subgroup.card_ker_mul_card_of_surjective hχ₀
      rw [hχker, card_SL_two_zmod, hcardX, hR2] at h1
      have hpos : 0 < Nat.card (CFSG.fittingSubgroup X) := Nat.card_pos
      have h2 : r * (r ^ 2 - 1) = 40320 := by
        have : Nat.card (CFSG.fittingSubgroup X) * (r * (r ^ 2 - 1)) =
            Nat.card (CFSG.fittingSubgroup X) * 40320 := by rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      exact ne_40320 r h2
  ·
    rw [← hR] at hFRe
    rcases hF13 with h1 | h3
    · intro k hk hφk
      have hkN : (⟨k, hk⟩ : X) ∈ N := hφk
      rw [hNR', ← hFRe, Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hkN
      exact congrArg Subtype.val hkN
    · exfalso
      apply hno3
      rw [hNR', ← hFRe]
      exact ⟨hFZ.le, h3⟩

end Abstract

variable {G : Type} [Group G] [Finite G]

namespace Ctx5

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx5 G T L V V₂ g a D)
include C

theorem mem_of_cube (h36 : A36ForSQTK) (M : S8Five.Model5 (D.img (l32nH T V)))
    {K : Subgroup G} (hK : K ∈ cComp (l32nH T V)) (hKimg : D.img K = M.A)
    (hKn : l32nH T V ≤ Subgroup.normalizer (K : Set G)) {y : G} (hyH : y ∈ l32nH T V)
    (hy3 : y ^ 3 = 1) : ∃ k ∈ K, ∃ q ∈ pCoreOf 2 (l32nH T V), y = k * q := by
  classical
  have hH := C.pCoreOf_ne
  set P2 := CFSG.pCore 2 ↥(l32nH T V) with hP2
  have hP2n : P2.Normal := CFSG.pCore_normal
  have hO : P2 ≤ (rhoH D).ker := by
    intro x hx
    have hxG : (x : G) ∈ pCoreOf 2 (l32nH T V) := by
      rw [hP2] at hx
      exact ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [coe_rhoH]
    exact C.rho_eq_one_of_pCoreOf hxG _
  set φ : (↥(l32nH T V) ⧸ P2) →* (D.V ≃ₗ[ZMod 2] D.V) :=
    (D.img (l32nH T V)).subtype.comp (QuotientGroup.lift P2 (rhoH D) hO) with hφ
  have hφmk : ∀ x : ↥(l32nH T V), φ (QuotientGroup.mk' P2 x) = D.ρ ⟨x, H_N x.2⟩ := fun x => rfl
  set Kb := modO2Image (l32nH T V) K with hKb
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hrange : Kb.map φ = M.A := by
    rw [← hKimg]
    ext γ
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [hφmk]
      exact L128A.HatU.rho_mem_img D (Subgroup.mem_subgroupOf.mp hk) _
    · intro hγ
      obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      exact ⟨QuotientGroup.mk' P2 ⟨k, hKH hk⟩, ⟨⟨k, hKH hk⟩, hk, rfl⟩, rfl⟩
  have hKbn : Kb.Normal := by
    have hn : (K.subgroupOf (l32nH T V)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
    exact Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective P2)
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot C.hyp.fsu.qtke C.hyp.fsu.simple
    C.hyp.fsu.nonabelian hH
  have : Finite (↥(l32nH T V) ⧸ P2) := hQ.finite
  have hrk : CFSG.Assembly.pRank 3 (⊤ : Subgroup (↥(l32nH T V) ⧸ P2)) ≤ 2 :=
    hQ.sqt 3 Nat.prime_three (by norm_num)
  have hstrong := lemma_1_2_1_four_strong C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian
    h36 hH hK
  have hinj := inj_of_a36 φ (modO2Image_mem_cComp hK) hstrong hrange hrk
  set yb := QuotientGroup.mk' P2 (⟨y, hyH⟩ : ↥(l32nH T V)) with hyb
  have hyb3 : yb ^ 3 = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyH⟩ : ↥(l32nH T V)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hybA : φ yb ∈ M.A := by
    have hmemΓ : φ yb ∈ D.img (l32nH T V) := L128A.HatU.rho_mem_img D hyH (H_N hyH)
    exact M.mem_A_of_pow_three hmemΓ (by rw [← map_pow, hyb3, map_one])
  have hmem := mem_of_cube' φ hKbn hinj hrange hrk hyb3 hybA
  obtain ⟨k, hk, hke⟩ := hmem
  have hkq : k⁻¹ * ⟨y, hyH⟩ ∈ P2 := by
    rw [← QuotientGroup.eq]
    exact hke
  refine ⟨k, Subgroup.mem_subgroupOf.mp hk, ((k⁻¹ * ⟨y, hyH⟩ : ↥(l32nH T V)) : G), ?_, ?_⟩
  · rw [hP2] at hkq
    exact ⟨_, hkq, rfl⟩
  · simp

end Ctx5

end L14324

end CFSG.Quasithin.H13
