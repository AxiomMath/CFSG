module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace E6TwoTB

section Abstract

variable {R : Type} [Group R] [Finite R]

theorem not_isTransvection_of_sylow
    (hZ : Subgroup.center R = ⊥)
    (hinn : ∀ (x : MulAut R) (k : ℕ), x ^ 3 ^ k = 1 →
      x ∈ Set.range (MulAut.conj : R →* MulAut R))
    (S B : Subgroup R)
    (hSyl : ∀ X : Subgroup R, IsPGroup 3 X → ∃ g : R, X.map (MulAut.conj g).toMonoidHom ≤ S)
    (hB : ∀ A : Subgroup R, A ≤ S → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → 3 ^ 4 ≤ Nat.card A →
      A = B)
    (hfix : ∀ s ∈ S, B ≤ Subgroup.centralizer {s} ∨
      Nat.card ↥(B ⊓ Subgroup.centralizer ({s} : Set R)) ≤ 9)
    {Eh : Subgroup (MulAut R)} (hA : IsElemAbelian 3 Eh) (h4 : 3 ^ 4 ≤ Nat.card Eh)
    (a : Subgroup.normalizer (Eh : Set (MulAut R))) :
    ¬ GGIsTransvection 3 (Eh.normalizerMonoidHom a) := by
  classical
  intro htv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut R) := TableBSymp.finite_mulAut (R := R)
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 := congrArg (fun f : MulAut R => f h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc h * g = (g * h * g⁻¹) * g := by rw [h1]
        _ = g * h := by group
    rw [hZ] at hgc
    exact Subgroup.mem_bot.mp hgc
  obtain ⟨hfixcard, hfixc⟩ := htv
  have hEhpos : 0 < Nat.card Eh := lt_of_lt_of_le (by norm_num) h4
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut Eh, φ = Eh.normalizerMonoidHom a := ⟨_, rfl⟩
  rw [← hφ] at hfixcard hfixc
  have hφapp : ∀ b : Eh, ((φ b : Eh) : MulAut R) = (a : MulAut R) * b * (a : MulAut R)⁻¹ := by
    intro b
    rw [hφ]
    rfl
  have hφ3 : φ ^ 3 = 1 := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨c, hc⟩ : ∃ c : Eh, c = b⁻¹ * φ b := ⟨_, rfl⟩
    have hφc : φ c = c := by rw [hc]; exact hfixc b
    have h1 : φ b = b * c := by rw [hc, mul_inv_cancel_left]
    have h2 : φ (φ b) = b * c * c := by rw [h1, map_mul, hφc, h1]
    have h3 : φ (φ (φ b)) = b * c * c * c := by rw [h2, map_mul, map_mul, hφc, h1]
    have hc3 : c * c * c = 1 := by
      apply Subtype.ext
      have h := hA.2 (c : MulAut R) c.2
      simpa [pow_succ] using h
    change φ (φ (φ b)) = b
    rw [h3]
    calc b * c * c * c = b * (c * c * c) := by simp only [mul_assoc]
      _ = b := by rw [hc3, mul_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    have hall : ∀ b : Eh, φ b = b := fun b => by rw [h1]; rfl
    have h2 : Nat.card {b : Eh // φ b = b} = Nat.card Eh :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    omega
  obtain ⟨e, m, hm3, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos (a : MulAut R)).ne' 3 (by norm_num)
  obtain ⟨a'', ha''⟩ : ∃ a'' : MulAut R, a'' = (a : MulAut R) ^ m := ⟨_, rfl⟩
  have ha''pow : a'' ^ 3 ^ e = 1 := by
    rw [ha'', ← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have ha''N : a'' ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
    rw [ha'']
    exact Subgroup.pow_mem _ a.2 m
  obtain ⟨s, hs⟩ := hinn a'' e ha''pow
  have hconj_sr : ∀ r : R, MulAut.conj (s * r * s⁻¹) = a'' * MulAut.conj r * a''⁻¹ := by
    intro r
    rw [map_mul, map_mul, map_inv, hs]
  have hEhin : ∀ b ∈ Eh, ∃ r : R, MulAut.conj r = b := fun b hb =>
    hinn b 1 (by rw [pow_one]; exact hA.2 b hb)
  have hEhle : Eh ≤ (MulAut.conj : R →* MulAut R).range := fun b hb => hEhin b hb
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup R, E₀ = Eh.comap (MulAut.conj : R →* MulAut R) :=
    ⟨_, rfl⟩
  have hE₀A : IsElemAbelian 3 E₀ := by
    rw [hE₀]
    exact ExcFrames.isElemAbelian_comap_frame _ hinj hA
  have hcardE₀ : Nat.card E₀ = Nat.card Eh := by
    rw [hE₀]
    exact ExcFrames.card_comap_of_le_range _ hinj hEhle
  have hE₀mem : ∀ r : R, r ∈ E₀ ↔ MulAut.conj r ∈ Eh := fun r => by
    rw [hE₀]
    rfl
  have hsE : ∀ r : R, r ∈ E₀ ↔ s * r * s⁻¹ ∈ E₀ := by
    intro r
    rw [hE₀mem, hE₀mem, hconj_sr]
    exact Subgroup.mem_normalizer_iff.mp ha''N _
  have hs3 : s ^ 3 ^ e = 1 := by
    apply hinj
    rw [map_pow, hs, ha''pow, map_one]
  have hsP : IsPGroup 3 (Subgroup.zpowers s) := by
    rintro ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨e, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
  have hE₀P : IsPGroup 3 E₀ := TableB.isPGroup_of_isElemAbelian hE₀A
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer (E₀ : Set R) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_iff.mpr hsE
  have hX : IsPGroup 3 ↥(E₀ ⊔ Subgroup.zpowers s) := hE₀P.to_sup_of_normal_left' hsP hsN
  obtain ⟨g, hg⟩ := hSyl _ hX
  have hE₀g : E₀.map (MulAut.conj g).toMonoidHom ≤ S :=
    (Subgroup.map_mono le_sup_left).trans hg
  have hBeq : E₀.map (MulAut.conj g).toMonoidHom = B := by
    refine hB _ hE₀g ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE₀A hx hy]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardE₀]
      exact h4
  have hs'S : g * s * g⁻¹ ∈ S := by
    have h1 : (MulAut.conj g).toMonoidHom s ∈
        (E₀ ⊔ Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom :=
      ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s), rfl⟩
    exact hg h1
  rcases hfix _ hs'S with hcent | hcard
  ·
    have hcs : ∀ r ∈ E₀, s * r * s⁻¹ = r := by
      intro r hr
      have hrB : g * r * g⁻¹ ∈ B := by
        rw [← hBeq]
        exact ⟨r, hr, rfl⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hcent hrB)
      have h2 : r * s = s * r := by
        have h3 : g * (r * s) * g⁻¹ = g * (s * r) * g⁻¹ := by
          calc g * (r * s) * g⁻¹ = g * r * g⁻¹ * (g * s * g⁻¹) := by group
            _ = g * s * g⁻¹ * (g * r * g⁻¹) := h1
            _ = g * (s * r) * g⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel h3)
      calc s * r * s⁻¹ = (r * s) * s⁻¹ := by rw [h2]
        _ = r := mul_inv_cancel_right r s
    have hφm : φ ^ m = 1 := by
      rw [hφ, ← map_pow]
      refine MulEquiv.ext fun b => Subtype.ext ?_
      change (↑(a ^ m) : MulAut R) * (b : MulAut R) * (↑(a ^ m) : MulAut R)⁻¹ = (b : MulAut R)
      obtain ⟨r, hr⟩ := hEhin b b.2
      have hrE : r ∈ E₀ := by
        rw [hE₀mem, hr]
        exact b.2
      rw [Subgroup.coe_pow, ← ha'', ← hr, ← hconj_sr r, hcs r hrE]
    have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    have hdvd : orderOf φ ∣ Nat.gcd 3 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hφ3) (orderOf_dvd_of_pow_eq_one hφm)
    rw [hcop.gcd_eq_one] at hdvd
    exact hφ1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
  ·
    have hlift : ∀ b : Eh, ∃ r : R, MulAut.conj r = (b : MulAut R) := fun b => hEhin b b.2
    choose lift hlift using hlift
    have hmemE : ∀ b : Eh, lift b ∈ E₀ := fun b => by
      rw [hE₀mem, hlift b]
      exact b.2
    have hf_mem : ∀ b : {b : Eh // φ b = b},
        g * lift b.1 * g⁻¹ ∈ B ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set R) := by
      intro b
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [← hBeq]
        exact ⟨lift b.1, hmemE b.1, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm0 : (a : MulAut R) * (b.1 : MulAut R) = (b.1 : MulAut R) * (a : MulAut R) := by
          have h1 := hφapp b.1
          rw [b.2] at h1
          exact mul_inv_eq_iff_eq_mul.mp h1.symm
        have hcomm1 : a'' * (b.1 : MulAut R) = (b.1 : MulAut R) * a'' := by
          rw [ha'']
          exact (Commute.pow_left hcomm0 m).eq
        have hfixb : s * lift b.1 * s⁻¹ = lift b.1 := by
          apply hinj
          rw [hconj_sr, hlift b.1]
          exact mul_inv_eq_of_eq_mul hcomm1
        have h2 : lift b.1 * s = s * lift b.1 := by
          calc lift b.1 * s = (s * lift b.1 * s⁻¹) * s := by rw [hfixb]
            _ = s * lift b.1 := inv_mul_cancel_right _ _
        calc g * lift b.1 * g⁻¹ * (g * s * g⁻¹) = g * (lift b.1 * s) * g⁻¹ := by group
          _ = g * (s * lift b.1) * g⁻¹ := by rw [h2]
          _ = g * s * g⁻¹ * (g * lift b.1 * g⁻¹) := by group
    let f : {b : Eh // φ b = b} →
        ↥(B ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set R)) := fun b => ⟨_, hf_mem b⟩
    have hf_inj : Function.Injective f := by
      intro b b' hbb'
      have h1 : g * lift b.1 * g⁻¹ = g * lift b'.1 * g⁻¹ := congrArg Subtype.val hbb'
      have h2 : lift b.1 = lift b'.1 := mul_left_cancel (mul_right_cancel h1)
      refine Subtype.ext (Subtype.ext ?_)
      rw [← hlift b.1, ← hlift b'.1, h2]
    have h3 := Nat.card_le_card_of_injective f hf_inj
    omega

end Abstract

section E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  E6TwoPilot

variable {K : Type} [Field K] [CharP K 2] [Finite K]


theorem exists_le_conj_range_psiHom (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {X : Subgroup (adjointGroup .E6 K)} (hX : IsPGroup 3 ↥X) :
    ∃ g : adjointGroup .E6 K, X.map (MulAut.conj g).toMonoidHom ≤ (psiHom K h2).range := by
  have := Fact.mk Nat.prime_three
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have hC0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (adjointGroup .E6 K)).factorization 3 = 6 := by
    have h6 : 3 ^ 6 ∣ Nat.card (adjointGroup .E6 K) := by
      rw [← card_range_psiHom h2]
      exact Subgroup.card_subgroup_dvd_card _
    have h7 := not_pow_seven_dvd_E6_two hK
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hC0] at h6 h7
    omega
  have : Finite (Sylow 3 (adjointGroup .E6 K)) :=
    Finite.of_injective (fun P : Sylow 3 (adjointGroup .E6 K) =>
      (P : Subgroup (adjointGroup .E6 K))) fun _ _ h => Sylow.ext h
  let P : Sylow 3 (adjointGroup .E6 K) :=
    Sylow.ofCard (psiHom K h2).range (by rw [card_range_psiHom h2, hfac])
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup .E6 K) Q P
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : (MulAut.conj c) x ∈ ((c • Q : Sylow 3 _) : Subgroup (adjointGroup .E6 K)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q : Subgroup _) (hXQ hx)
  rw [hc] at h1
  exact h1

theorem torus_fix_le (h2 : (2 : K) = 0) {s : adjointGroup .E6 K}
    (hs : s ∈ (psiHom K h2).range) :
    (torusE6Two h2).range ≤ Subgroup.centralizer {s} ∨
      Nat.card ↥((torusE6Two h2).range ⊓
        Subgroup.centralizer ({s} : Set (adjointGroup .E6 K))) ≤ 9 := by
  obtain ⟨x, rfl⟩ := hs
  have hconj : ∀ w : Multiplicative (Fin 4 → ZMod 3),
      psiHom K h2 x * torusE6Two h2 w * (psiHom K h2 x)⁻¹ =
        torusE6Two h2 (phiAct x.right w) := by
    intro w
    have e1 : psiHom K h2 x * torusE6Two h2 w * (psiHom K h2 x)⁻¹ =
        torusE6Two h2 x.left * (stHom K x.right * torusE6Two h2 w * (stHom K x.right)⁻¹) *
          (torusE6Two h2 x.left)⁻¹ := by
      rw [psiHom_apply]
      group
    rw [e1, stHom_conj_torusE6Two h2, ← map_mul, ← map_inv, ← map_mul, mul_comm x.left,
      mul_inv_cancel_right]
  by_cases hg : x.right = 1
  · left
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hconj w
    rw [hg, map_one, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · right
    have hfixed : ∀ w : Multiplicative (Fin 4 → ZMod 3),
        torusE6Two h2 w ∈ Subgroup.centralizer ({psiHom K h2 x} : Set (adjointGroup .E6 K)) ↔
          actG x.right (Multiplicative.toAdd w) = Multiplicative.toAdd w := by
      intro w
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hconj w
      constructor
      · intro hc
        have h3 : torusE6Two h2 (phiAct x.right w) = torusE6Two h2 w := by
          rw [← h1, mul_inv_eq_iff_eq_mul]
          exact hc.symm
        have h4 : phiAct x.right w = w := torusE6Two_injective h2 h3
        have h5 := congrArg Multiplicative.toAdd h4
        rwa [phiAct_eq_actG, toAdd_ofAdd] at h5
      · intro hw
        have h4 : phiAct x.right w = w := by
          rw [phiAct_eq_actG, hw, ofAdd_toAdd]
        rw [h4] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hΦ_mem : ∀ v : {v : Fin 4 → ZMod 3 // actG x.right v = v},
        torusE6Two h2 (.ofAdd v.1) ∈ (torusE6Two h2).range ⊓
          Subgroup.centralizer ({psiHom K h2 x} : Set (adjointGroup .E6 K)) := by
      intro v
      rw [Subgroup.mem_inf]
      refine ⟨⟨_, rfl⟩, (hfixed _).mpr ?_⟩
      rw [toAdd_ofAdd]
      exact v.2
    let Φ : {v : Fin 4 → ZMod 3 // actG x.right v = v} →
        ↥((torusE6Two h2).range ⊓
          Subgroup.centralizer ({psiHom K h2 x} : Set (adjointGroup .E6 K))) :=
      fun v => ⟨_, hΦ_mem v⟩
    have hΦ_surj : Function.Surjective Φ := by
      rintro ⟨y, hy⟩
      rw [Subgroup.mem_inf] at hy
      obtain ⟨⟨w, rfl⟩, hyc⟩ := hy
      refine ⟨⟨Multiplicative.toAdd w, (hfixed w).mp hyc⟩, ?_⟩
      apply Subtype.ext
      change torusE6Two h2 (.ofAdd (Multiplicative.toAdd w)) = torusE6Two h2 w
      rw [ofAdd_toAdd]
    calc Nat.card ↥((torusE6Two h2).range ⊓
          Subgroup.centralizer ({psiHom K h2 x} : Set (adjointGroup .E6 K)))
        ≤ Nat.card {v : Fin 4 → ZMod 3 // actG x.right v = v} :=
          Nat.card_le_card_of_surjective Φ hΦ_surj
      _ ≤ 9 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact card_fix_le_nine x.right hg

theorem mem_inn_recipe_E6_two (hK : Nat.card K = 2)
    {x : MulAut (TableBExc.RecipeGroup .E6 K)} {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    x ∈ Set.range (MulAut.conj :
      TableBExc.RecipeGroup .E6 K →* MulAut (TableBExc.RecipeGroup .E6 K)) := by
  obtain ⟨Ψ, hker⟩ := exists_quot_E6 K
  refine recipeID_subset_inn_E6_two hK ((hker x).1 (Prod.ext ?_ ?_))
  · rw [ringEquiv_eq_refl_of_card_two hK (Ψ x).1]
    rfl
  · have hsq : ∀ y : Multiplicative (ZMod (exactE TwistTag.E6.tag)), y ^ 2 = 1 := by
      have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
      intro y
      rw [pow_two]
      exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
    refine TableBExc.eq_one_of_sq_of_pow_odd (p := 3 ^ k) (Odd.pow (by decide)) (hsq _) ?_
    rw [← Prod.pow_snd, ← map_pow, hx, map_one, Prod.snd_one]

theorem mem_inn_adjoint_E6_two (hK : Nat.card K = 2) {x : MulAut (adjointGroup .E6 K)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) :
    x ∈ Set.range (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := by
  obtain ⟨w, hw⟩ := mem_inn_recipe_E6_two hK
    (x := (MulAut.congr (TableBExc.recipeEquiv .E6 K)).symm x) (k := k) (by
      rw [← map_pow, hx, map_one])
  refine ⟨TableBExc.recipeEquiv .E6 K w, ?_⟩
  rw [← congr_conj, hw]
  exact (MulAut.congr (TableBExc.recipeEquiv .E6 K)).apply_symm_apply x

theorem ggNoTransvectionTorus_adjoint_E6_two (hK : Nat.card K = 2)
    (I : Set (MulAut (adjointGroup .E6 K))) :
    GGNoTransvectionTorus 3 4 (adjointGroup .E6 K) I := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  intro Eh _ hA h4 _ a
  exact not_isTransvection_of_sylow (center_adjointGroup_eq_bot (τ := .E6) (K := K))
    (fun _ _ hx => mem_inn_adjoint_E6_two hK hx) (psiHom K h2).range (torusE6Two h2).range
    (fun _ hX => exists_le_conj_range_psiHom h2 hK hX)
    (fun _ hAS hAc hcard => eq_range_torusE6Two_of_le h2 hAS hAc hcard)
    (fun _ hs => torus_fix_le h2 hs) hA h4 a

theorem ggNoTransvectionTorus_E6_two (hK : Nat.card K = 2) :
    GGNoTransvectionTorus 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggNoTransvectionTorus_of_mulEquiv (TableBExc.recipeEquiv .E6 K) (fun _ _ => Set.mem_univ _)
    (ggNoTransvectionTorus_adjoint_E6_two hK Set.univ)

end E6

end E6TwoTB

section Label


theorem largeEvenLabelAll_noTransvection_e6TwoThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGE6TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoTransvectionTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 4, TableBExc.E6Three.ggTorusLift_E6_two,
    E6TwoTB.ggNoTransvectionTorus_E6_two hK2⟩

theorem ggLTransvectionCenterInputOn_e6TwoThree_holds :
    GGLTransvectionCenterInputOn GGE6TwoThreeLabel :=
  ggLTransvectionCenterInputOn_of_labels' ggLNoncyclicInput_holds
    fun _ _ _ _ h => largeEvenLabelAll_noTransvection_e6TwoThree h

theorem ggLTransvectionCenterInputOn_of_not_e6TwoThree {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := ggLTransvectionCenterInputOn_e6TwoThree_holds.or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGE6TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Label

end CFSG.StandardType
