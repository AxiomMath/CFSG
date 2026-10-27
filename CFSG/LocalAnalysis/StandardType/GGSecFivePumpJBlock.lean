module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot

theorem ggDk_comp_eq_block {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type}
    [Group G] [Finite G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} {δ : ↥Bs →* (Fin (m + 1) → Fˣ)}
    (hδ : ∀ b : ↥Bs, ((b : G), InnerDiagA.diagGL (δ b)) ∈ LinFusion.ggInducedPairs ψ)
    (hfull : ∀ v : Fin (m + 1) → Fˣ, (∀ j, v j ^ p = 1) →
      ∃ (b : ↥Bs) (c : Fˣ), ∀ j, δ b j = c * v j)
    {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) {D J : Subgroup G}
    (hDJ : D = Bs ⊓ Subgroup.centralizer (J : Set G)) (hDcard : Nat.card D = p ^ 2)
    {x : ↥Bs} (hxD : (x : G) ∈ D) (hx1 : x ≠ 1) (hxδ : δ x = 1)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin (m + 1)), J = (blockSpecialLinear I).map ψ ∧ m ≤ I.card := by
  classical
  have hDBs : D ≤ Bs := by rw [hDJ]; exact inf_le_left
  let δ' : ↥D →* (Fin (m + 1) → Fˣ) := δ.comp (Subgroup.inclusion hDBs)
  have hb : ∀ k : ↥D, ((k : G), InnerDiagA.diagGL (δ' k)) ∈ LinFusion.ggInducedPairs ψ :=
    fun k => hδ ⟨k, hDBs k.2⟩
  have hrange : Set.range (fun k : ↥D => (k : G)) = (D : Set G) := by ext g; simp
  rw [← hrange] at hJ
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hker hb hJ
  refine ⟨LinSemisimple.eigClass δ' i, hi, ?_⟩
  by_contra hlt
  push Not at hlt
  set I := LinSemisimple.eigClass δ' i
  have hiI : i ∈ I := LinSemisimple.self_mem_eigClass δ' i
  obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := Finset.one_lt_card.mp (show 1 < Iᶜ.card by
    rw [Finset.card_compl, Fintype.card_fin]; omega)
  rw [Finset.mem_compl] at hj₁ hj₂
  have hi₁ : i ≠ j₁ := fun h => hj₁ (h ▸ hiI)
  have hi₂ : i ≠ j₂ := fun h => hj₂ (h ▸ hiI)
  have hpow : ∀ (y j : Fin (m + 1)), (Pi.mulSingle y ζ : Fin (m + 1) → Fˣ) j ^ p = 1 := by
    intro y j
    by_cases hj : j = y
    · rw [hj, Pi.mulSingle_eq_same, hζ.pow_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  have hmemD : ∀ (b : ↥Bs) (r : Fˣ) (y : Fin (m + 1)), y ∉ I →
      (∀ j, δ b j = r * (Pi.mulSingle y ζ : Fin (m + 1) → Fˣ) j) → (b : G) ∈ D := by
    intro b r y hy hb'
    have hc : ∀ j ∈ I, ∀ l ∈ I, δ b j = δ b l := fun j hj l hl => by
      rw [hb', hb', Pi.mulSingle_eq_of_ne (fun h : j = y => hy (h ▸ hj)),
        Pi.mulSingle_eq_of_ne (fun h : l = y => hy (h ▸ hl))]
    rw [hDJ]
    refine Subgroup.mem_inf.mpr ⟨b.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rw [hi]
    rintro _ ⟨u, hu, rfl⟩
    have h1 := LinFusion.mem_ggInducedPairs.mp (hδ b) u
    rw [LinFusion.conjSL_diagGL_of_mem_blockSpecialLinear hc hu] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  obtain ⟨b₁, r₁, hb₁⟩ := hfull (Pi.mulSingle j₁ ζ) (hpow j₁)
  obtain ⟨b₂, r₂, hb₂⟩ := hfull (Pi.mulSingle j₂ ζ) (hpow j₂)
  have hb₁D := hmemD b₁ r₁ j₁ hj₁ hb₁
  have hb₂D := hmemD b₂ r₂ j₂ hj₂ hb₂
  let θ : ↥D →* Fˣ × Fˣ :=
    ((Pi.evalMonoidHom (fun _ => Fˣ) j₁).comp δ' / (Pi.evalMonoidHom (fun _ => Fˣ) i).comp δ').prod
      ((Pi.evalMonoidHom (fun _ => Fˣ) j₂).comp δ' / (Pi.evalMonoidHom (fun _ => Fˣ) i).comp δ')
  have hθ₁ : θ ⟨b₁, hb₁D⟩ = (ζ, 1) := by
    show (δ b₁ j₁ / δ b₁ i, δ b₁ j₂ / δ b₁ i) = (ζ, 1)
    simp only [hb₁, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi₁,
      Pi.mulSingle_eq_of_ne hj₁₂.symm, mul_one, mul_div_cancel_left, div_self']
  have hθ₂ : θ ⟨b₂, hb₂D⟩ = (1, ζ) := by
    show (δ b₂ j₁ / δ b₂ i, δ b₂ j₂ / δ b₂ i) = (1, ζ)
    simp only [hb₂, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi₂,
      Pi.mulSingle_eq_of_ne hj₁₂, mul_one, mul_div_cancel_left, div_self']
  have hθx : θ ⟨x, hxD⟩ = 1 := by
    show (δ x j₁ / δ x i, δ x j₂ / δ x i) = 1
    simp [hxδ]
  have hθpow : ∀ a b : ℕ, θ (⟨b₁, hb₁D⟩ ^ a * ⟨b₂, hb₂D⟩ ^ b) = (ζ ^ a, ζ ^ b) := by
    intro a b
    rw [map_mul, map_pow, map_pow, hθ₁, hθ₂, Prod.pow_mk, Prod.pow_mk, one_pow, one_pow,
      Prod.mk_mul_mk, mul_one, one_mul]
  have hr : p * p ≤ Nat.card θ.range := by
    have hinj : Function.Injective fun ab : Fin p × Fin p =>
        (⟨(ζ ^ (ab.1 : ℕ), ζ ^ (ab.2 : ℕ)), MonoidHom.mem_range.mpr ⟨_, hθpow _ _⟩⟩ :
          θ.range) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Prod.ext (Fin.ext (hζ.pow_inj a.2 a'.2 h.1)) (Fin.ext (hζ.pow_inj b.2 b'.2 h.2))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_fin] at h1
  have hk : 1 < Nat.card θ.ker := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => hx1 (Subtype.ext ?_)
    have h2 : (⟨x, hxD⟩ : ↥D) = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact hθx
    exact congrArg (Subtype.val : ↥D → G) h2
  have htot := Subgroup.card_ker_mul_card_range θ
  rw [hDcard, pow_two] at htot
  have h3 : 2 * (p * p) ≤ p * p :=
    calc 2 * (p * p) ≤ Nat.card θ.ker * Nat.card θ.range :=
          Nat.mul_le_mul (show 2 ≤ Nat.card θ.ker from hk) hr
      _ = p * p := htot
  have h4 : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  omega

theorem ggDk_pair_eq_of_fix_iff {m : ℕ} {F : Type} [Field F] {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime) {Bs : Subgroup G} {δ : ↥Bs →* (Fin (m + 1) → Fˣ)}
    (hfull : ∀ v : Fin (m + 1) → Fˣ, (∀ j, v j ^ p = 1) →
      ∃ (b : ↥Bs) (c : Fˣ), ∀ j, δ b j = c * v j)
    {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) {a c a' c' : Fin (m + 1)} (hac : a ≠ c)
    (h : ∀ b : ↥Bs, δ b a = δ b c ↔ δ b a' = δ b c') :
    (a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a) := by
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hsingle : ∀ y i j : Fin (m + 1), (Pi.mulSingle y ζ : Fin (m + 1) → Fˣ) i =
      (Pi.mulSingle y ζ : Fin (m + 1) → Fˣ) j ↔ (i = y ↔ j = y) := by
    intro y i j
    by_cases hi : i = y <;> by_cases hj : j = y
    · subst hi hj; simp
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hj]
      simp [hζ1, hj]
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi]
      simp [hζ1.symm, hi]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hj]
      simp [hi, hj]
  have hcond : ∀ y : Fin (m + 1), ((a = y ↔ c = y) ↔ (a' = y ↔ c' = y)) := by
    intro y
    obtain ⟨b, r, hb⟩ := hfull (Pi.mulSingle y ζ) fun j => by
      by_cases hj : j = y
      · rw [hj, Pi.mulSingle_eq_same, hζ.pow_eq_one]
      · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
    have h1 := h b
    rwa [hb, hb, hb, hb, mul_right_inj, mul_right_inj, hsingle, hsingle] at h1
  have ha : ¬ (a' = a ↔ c' = a) := fun h' => hac.symm (((hcond a).mpr h').mp rfl)
  have hc : ¬ (a' = c ↔ c' = c) := fun h' => hac (((hcond c).mpr h').mpr rfl)
  by_cases h1 : a' = a
  · refine Or.inl ⟨h1, ?_⟩
    by_contra h2
    exact hc ⟨fun h3 => absurd (h1.symm.trans h3) hac, fun h3 => absurd h3 h2⟩
  · have h2 : c' = a := by
      by_contra h2
      exact ha ⟨fun h3 => absurd h3 h1, fun h3 => absurd h3 h2⟩
    refine Or.inr ⟨?_, h2⟩
    by_contra h3
    exact hc ⟨fun h4 => absurd h4 h3, fun h4 => absurd (h2.symm.trans h4) hac⟩

theorem ggDk_prime_dvd_card_block {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m) {G : Type}
    [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) {I : Finset (Fin (m + 1))}
    {a c : Fin (m + 1)} (ha : a ∈ I) (hc : c ∈ I) (hac : a ≠ c) :
    p ∣ Nat.card ↥((blockSpecialLinear I).map ψ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hka, hkc⟩ := Fin.exists_ne_and_ne_of_two_lt a c (by omega)
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle a ζ * Pi.mulSingle c ζ⁻¹ with he
  have hea : e a = ζ := by
    rw [he, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hac, mul_one]
  have hek : e k = 1 := by
    rw [he, Pi.mul_apply, Pi.mulSingle_eq_of_ne hka, Pi.mulSingle_eq_of_ne hkc, mul_one]
  have hprod : ∏ j, e j = 1 := by
    simp only [he, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle',
      mul_inv_cancel]
  have hep : ∀ j, e j ^ p = 1 := by
    intro j
    have h1 : ∀ (y : Fin (m + 1)) (z : Fˣ), z ^ p = 1 →
        (Pi.mulSingle y z : Fin (m + 1) → Fˣ) j ^ p = 1 := by
      intro y z hz
      by_cases hj : j = y
      · rw [hj, Pi.mulSingle_eq_same, hz]
      · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
    rw [he, Pi.mul_apply, mul_pow, h1 a ζ hζ.pow_eq_one,
      h1 c ζ⁻¹ (by rw [inv_pow, hζ.pow_eq_one, inv_one]), one_mul]
  let u := LinModel.diagSL e hprod
  have hu : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal fun l => ((e l : Fˣ) : F) := rfl
  have hu_mem : u ∈ blockSpecialLinear I := by
    rw [mem_blockSpecialLinear]
    intro i j hij
    rw [hu]
    by_cases h : i = j
    · subst h
      have hi : i ∉ I := hij.elim id id
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, he, Pi.mul_apply,
        Pi.mulSingle_eq_of_ne (fun h' : i = a => hi (h' ▸ ha)),
        Pi.mulSingle_eq_of_ne (fun h' : i = c => hi (h' ▸ hc)), mul_one, Units.val_one]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hu,
      Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hep, Units.val_one]
  have hne : ψ u ≠ 1 := by
    intro h1
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker h1)
    have hk' := congrFun (congrFun hr k) k
    have ha' := congrFun (congrFun hr a) a
    rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hek,
      Units.val_one] at hk'
    rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hea,
      hk'] at ha'
    exact hζ.ne_one hp.one_lt (Units.ext ha'.symm)
  let g : ↥((blockSpecialLinear I).map ψ) := ⟨ψ u, Subgroup.mem_map_of_mem ψ hu_mem⟩
  have hg : orderOf g = p := orderOf_eq_prime
    (Subtype.ext (show ψ u ^ p = 1 by rw [← map_pow, hup, map_one]))
    (fun h => hne (congrArg Subtype.val h))
  rw [← hg]
  exact orderOf_dvd_natCard g

end CFSG.StandardType

end
