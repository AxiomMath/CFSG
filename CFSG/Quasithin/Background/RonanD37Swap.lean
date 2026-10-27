module

public import CFSG.Quasithin.Background.SmithD37Orth

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37
open scoped Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

theorem coordAut_left (Mm : MatModel L₁ L₂ F d) {x : MulAut U} {l l' : ↥L₁}
    (hl' : (l' : MulAut U) = x * l * x⁻¹) (X : Matrix (Fin d) (Fin d) F) :
    coordAut Mm x ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X) =
      (Mm.R₁ l' : Matrix (Fin d) (Fin d) F) * coordAut Mm x X := by
  obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (Mm.β u) = X :=
    ⟨Mm.β.symm (Multiplicative.ofAdd X), by simp⟩
  have e1 : (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (Mm.β u) =
      Multiplicative.toAdd (Mm.β ((l : MulAut U) u)) := by rw [Mm.act₁, toAdd_ofAdd]
  have e2 : x ((l : MulAut U) u) = (l' : MulAut U) (x u) := by
    rw [hl']
    simp [MulAut.mul_apply]
  rw [e1, coordAut_β, coordAut_β, e2, Mm.act₁, toAdd_ofAdd]

theorem coordAut_right (Mm : MatModel L₁ L₂ F d) {x : MulAut U} {k k' : ↥L₂}
    (hk' : (k' : MulAut U) = x * k * x⁻¹) (X : Matrix (Fin d) (Fin d) F) :
    coordAut Mm x (X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ) =
      coordAut Mm x X * (Mm.R₂ k' : Matrix (Fin d) (Fin d) F)ᵀ := by
  obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (Mm.β u) = X :=
    ⟨Mm.β.symm (Multiplicative.ofAdd X), by simp⟩
  have e1 : Multiplicative.toAdd (Mm.β u) * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ =
      Multiplicative.toAdd (Mm.β ((k : MulAut U) u)) := by rw [Mm.act₂, toAdd_ofAdd]
  have e2 : x ((k : MulAut U) u) = (k' : MulAut U) (x u) := by
    rw [hk']
    simp [MulAut.mul_apply]
  rw [e1, coordAut_β, coordAut_β, e2, Mm.act₂, toAdd_ofAdd]

theorem coordAut_invol (Mm : MatModel L₁ L₂ F d) {x : MulAut U} (hx : x * x = 1)
    (X : Matrix (Fin d) (Fin d) F) : coordAut Mm x (coordAut Mm x X) = X := by
  obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (Mm.β u) = X :=
    ⟨Mm.β.symm (Multiplicative.ofAdd X), by simp⟩
  have h : x (x u) = u := by rw [← MulAut.mul_apply, hx, MulAut.one_apply]
  rw [coordAut_β, coordAut_β, h]

theorem exists_semilinear_of_norm (Mm : MatModel L₁ L₂ F d) {x : MulAut U} (hx : x * x = 1)
    (h₁ : ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁) (h₂ : ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂) (c : F) :
    ∃ c' : F, ∀ X, coordAut Mm x (c • X) = c' • coordAut Mm x X := by
  have hxx : ∀ l : MulAut U, x * (x * l * x⁻¹) * x⁻¹ = l := by
    intro l
    calc x * (x * l * x⁻¹) * x⁻¹ = (x * x) * l * (x * x)⁻¹ := by group
      _ = l := by rw [hx]; simp
  let S : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
    { toFun := fun X => coordAut Mm x (c • coordAut Mm x X)
      map_zero' := by simp
      map_add' := fun X Y => by simp [smul_add] }
  obtain ⟨c', hc'⟩ := exists_smul_of_comm Mm S
    (fun l X => by
      let l' : ↥L₁ := ⟨x * l * x⁻¹, h₁ l l.2⟩
      show coordAut Mm x (c • coordAut Mm x (_ * X)) = _ * coordAut Mm x (c • coordAut Mm x X)
      rw [coordAut_left Mm (l' := l') rfl, ← Matrix.mul_smul,
        coordAut_left Mm (l := l') (l' := l) (hxx l).symm])
    (fun k X => by
      let k' : ↥L₂ := ⟨x * k * x⁻¹, h₂ k k.2⟩
      show coordAut Mm x (c • coordAut Mm x (X * _)) = coordAut Mm x (c • coordAut Mm x X) * _
      rw [coordAut_right Mm (k' := k') rfl, ← Matrix.smul_mul,
        coordAut_right Mm (k := k') (k' := k) (hxx k).symm])
  refine ⟨c', fun X => ?_⟩
  have h := hc' (coordAut Mm x X)
  rwa [show S (coordAut Mm x X) = coordAut Mm x (c • X) by
    show coordAut Mm x (c • coordAut Mm x (coordAut Mm x X)) = _
    rw [coordAut_invol Mm hx]] at h

theorem natCard_fix_two_mul_le [Fintype F]
    (T₁ T₂ : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F)
    (h₁ : ∀ (c : F) X, T₁ (c • X) = c • T₁ X) (h₂ : ∀ (c : F) X, T₂ (c • X) = c • T₂ X)
    (hne : ∃ X, T₁ X = X ∧ T₂ X ≠ X) :
    Nat.card {X // T₁ X = X ∧ T₂ X = X} * Nat.card F ≤ Nat.card {X // T₁ X = X} := by
  classical
  let T₁' : Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F :=
    { T₁ with map_smul' := h₁ }
  let T₂' : Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F :=
    { T₂ with map_smul' := h₂ }
  let S₁ : Submodule F (Matrix (Fin d) (Fin d) F) := LinearMap.eqLocus T₁' LinearMap.id
  let S₂ : Submodule F (Matrix (Fin d) (Fin d) F) := S₁ ⊓ LinearMap.eqLocus T₂' LinearMap.id
  have hm₁ : ∀ X, X ∈ S₁ ↔ T₁ X = X := fun X => Iff.rfl
  have hm₂ : ∀ X, X ∈ S₂ ↔ T₁ X = X ∧ T₂ X = X := fun X => Iff.rfl
  have hlt : S₂ < S₁ := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    obtain ⟨X, hX₁, hX₂⟩ := hne
    have hX : X ∈ S₂ := heq ▸ (hm₁ X).mpr hX₁
    exact hX₂ ((hm₂ X).mp hX).2
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hc₁ : Nat.card {X // T₁ X = X} = Nat.card ↥S₁ :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => (hm₁ X).symm)
  have hc₂ : Nat.card {X // T₁ X = X ∧ T₂ X = X} = Nat.card ↥S₂ :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => (hm₂ X).symm)
  rw [hc₁, hc₂, Module.natCard_eq_pow_finrank (K := F) (V := ↥S₁),
    Module.natCard_eq_pow_finrank (K := F) (V := ↥S₂), ← pow_succ]
  exact Nat.pow_le_pow_right Nat.card_pos hfr

section Core

variable [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U} [Fintype F] [CharP F 2]

theorem norm_inf_cent_eq_bot (Mm : MatModel L₁ L₂ F d) {B : Subgroup (MulAut U)}
    (hE : IsElemAbelian2 B) {b : MulAut U} (hbB : b ∈ B)
    (ht₂ : L₂.map (MulAut.conj b).toMonoidHom = L₁) :
    (B ⊓ Subgroup.normalizer (L₁ : Set (MulAut U))) ⊓
      Subgroup.centralizer (L₁ : Set (MulAut U)) = ⊥ := by
  have hsw₂ : ∀ k ∈ L₂, b * k * b⁻¹ ∈ L₁ := fun k hk => by
    rw [← ht₂]
    exact ⟨k, hk, rfl⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hc₁ : ∀ l ∈ L₁, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp hx.2 l hl).symm
  have hxt : x * b = b * x := hE.1 x hx.1.1 b hbB
  exact eq_one_of_comm Mm hc₁ (commute_of_swap hsw₂ hxt hc₁) (e := 1)
    (by rw [pow_one]; exact hE.2 x hx.1.1)

theorem exists_fix_moved (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d) (hd : 2 ≤ d)
    {b x : MulAut U} (hb : b * b = 1) (ht₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (ht₂ : L₂.map (MulAut.conj b).toMonoidHom = L₁) (hx2 : x ^ 2 = 1)
    (hxN : ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁) (hxb : x * b = b * x) (hx1 : x ≠ 1) :
    ∃ u, b u = u ∧ x u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hsw₁ : ∀ l ∈ L₁, b * l * b⁻¹ ∈ L₂ := fun l hl => by
    rw [← ht₁]
    exact ⟨l, hl, rfl⟩
  have hsw₂ : ∀ k ∈ L₂, b * k * b⁻¹ ∈ L₁ := fun k hk => by
    rw [← ht₂]
    exact ⟨k, hk, rfl⟩
  have := hC.simple
  have hc₁ := commute_of_fix_t hb hC.comm hsw₁ hC.exp hC.inf (Mm.not_comm hd) hxb hxN hcon
  have hc₂ := commute_of_swap hsw₂ hxb hc₁
  exact hx1 (eq_one_of_comm Mm hc₁ hc₂ (e := 1) (by rw [pow_one]; exact hx2))

theorem natCard_fix_two_eq (Mm : MatModel L₁ L₂ F d) (b x : MulAut U) :
    Nat.card {u : U // b u = u ∧ x u = u} =
      Nat.card {X // coordAut Mm b X = X ∧ coordAut Mm x X = X} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Mm.β.toEquiv.trans Multiplicative.toAdd) ?_)
  intro u
  show _ ↔ coordAut Mm b (Multiplicative.toAdd (Mm.β u)) = Multiplicative.toAdd (Mm.β u) ∧
    coordAut Mm x (Multiplicative.toAdd (Mm.β u)) = Multiplicative.toAdd (Mm.β u)
  rw [coordAut_β, coordAut_β, Multiplicative.toAdd.injective.eq_iff, Mm.β.injective.eq_iff,
    Multiplicative.toAdd.injective.eq_iff, Mm.β.injective.eq_iff]

theorem card_fixV_le_fix_two {B : Subgroup (MulAut U)} {b x : MulAut U} (hb : b ∈ B)
    (hx : x ∈ B) : Nat.card ↥(fixV B) ≤ Nat.card {u : U // b u = u ∧ x u = u} := by
  refine Nat.card_le_card_of_injective (fun u => ⟨u.1, u.2 b hb, u.2 x hx⟩) ?_
  intro u v h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext h

theorem natCard_fix_two_le_left (T T' : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F) :
    Nat.card {X // T X = X ∧ T' X = X} ≤ Nat.card {X // T X = X} :=
  Nat.card_le_card_of_injective (fun X => ⟨X.1, X.2.1⟩) fun X Y h => by
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

theorem natCard_fix_two_le_right (T T' : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F) :
    Nat.card {X // T X = X ∧ T' X = X} ≤ Nat.card {X // T' X = X} :=
  Nat.card_le_card_of_injective (fun X => ⟨X.1, X.2.2⟩) fun X Y h => by
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

theorem card_fixV_le_swap_two (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2)
    {B : Subgroup (MulAut U)} (hB : IsA2 X B) {b : MulAut U} (hbB : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (L₁ : Set (MulAut U)))
    (hB0 : B ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) ≠ ⊥) :
    Nat.card F ^ 2 * Nat.card ↥(fixV B) ≤ Nat.card U := by
  have hE := hB.2.2
  have hb : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbB
  obtain ⟨ht₁, ht₂⟩ := hC.swap_of_not_mem (hB.1 hbB) hbN
  obtain ⟨⟨x, hxB, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB0
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxN₁ : ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁ := fun l hl => mul_mem_of_mem_normalizer hxN hl
  have hxN₂ : ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := fun k hk =>
    mul_mem_of_mem_normalizer (hC.mem_normalizer₂ (hB.1 hxB) hxN) hk
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hE.2 x hxB
  have hxb : x * b = b * x := hE.1 x hxB b hbB
  obtain ⟨u₀, hu₀b, hu₀x⟩ := exists_fix_moved hC Mm le_rfl hb ht₁ ht₂ (hE.2 x hxB) hxN₁ hxb hx1'
  have hU := natCard_eq_of_matModel Mm
  have hswap := card_fixV_swap_le Mm b hb ht₁ ht₂
  rw [natCard_fixV_zpowers_eq Mm b, hU, show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl,
    pow_one] at hswap
  set Tb := coordAut Mm b with hTb
  set Tx := coordAut Mm x with hTx
  have hfix := (card_fixV_le_fix_two hbB hxB).trans_eq (natCard_fix_two_eq Mm b x)
  have hq : 0 < Nat.card F := Nat.card_pos
  rw [hU]
  have hsq : ∀ T : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F,
      (∀ c : F, ∃ c' : F, ∀ X, T (c • X) = c' • T X) →
      ¬ (∀ (c : F) X, T (c • X) = c • T X) → Nat.card {X // T X = X} ≤ Nat.card F ^ 2 := by
    intro T hsemi hlin
    push Not at hlin
    obtain ⟨c, X, hX⟩ := hlin
    obtain ⟨c', hc'⟩ := hsemi c
    have hcc : c ≠ c' := by
      rintro rfl
      exact hX (hc' X)
    have h := natCard_fix_sq_le_of_semilinear T hcc hc'
    rw [show Nat.card F ^ (2 * 2) = (Nat.card F ^ 2) ^ 2 by ring] at h
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h
  by_cases hlb : ∀ (c : F) X, Tb (c • X) = c • Tb X
  · by_cases hlx : ∀ (c : F) X, Tx (c • X) = c • Tx X
    · have hne : ∃ X, Tb X = X ∧ Tx X ≠ X := by
        refine ⟨Multiplicative.toAdd (Mm.β u₀), ?_, ?_⟩
        · rw [hTb, coordAut_β, hu₀b]
        · rw [hTx, coordAut_β]
          intro h
          exact hu₀x (Mm.β.injective (Multiplicative.toAdd.injective h))
      have h1 := natCard_fix_two_mul_le Tb Tx hlb hlx hne
      calc Nat.card F ^ 2 * Nat.card ↥(fixV B)
          ≤ Nat.card F ^ 2 * Nat.card {X // Tb X = X ∧ Tx X = X} :=
            Nat.mul_le_mul_left _ hfix
        _ = Nat.card F * (Nat.card {X // Tb X = X ∧ Tx X = X} * Nat.card F) := by ring
        _ ≤ Nat.card F * Nat.card {X // Tb X = X} := Nat.mul_le_mul_left _ h1
        _ ≤ Nat.card F ^ (2 * 2) := hswap
    · have h1 := hsq Tx (exists_semilinear_of_norm Mm hx2 hxN₁ hxN₂) hlx
      calc Nat.card F ^ 2 * Nat.card ↥(fixV B)
          ≤ Nat.card F ^ 2 * Nat.card {X // Tx X = X} :=
            Nat.mul_le_mul_left _ (hfix.trans (natCard_fix_two_le_right Tb Tx))
        _ ≤ Nat.card F ^ 2 * Nat.card F ^ 2 := Nat.mul_le_mul_left _ h1
        _ = Nat.card F ^ (2 * 2) := by ring
  · have h1 := hsq Tb (swapInvOf Mm b hb ht₁ ht₂).exists_semilinear hlb
    calc Nat.card F ^ 2 * Nat.card ↥(fixV B)
        ≤ Nat.card F ^ 2 * Nat.card {X // Tb X = X} :=
          Nat.mul_le_mul_left _ (hfix.trans (natCard_fix_two_le_left Tb Tx))
      _ ≤ Nat.card F ^ 2 * Nat.card F ^ 2 := Nat.mul_le_mul_left _ h1
      _ = Nat.card F ^ (2 * 2) := by ring

theorem two_mul_card_fixV_le_swap (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d) (hd : 2 ≤ d)
    {B : Subgroup (MulAut U)} (hB : IsA2 X B) {b : MulAut U} (hbB : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (L₁ : Set (MulAut U)))
    (hB0 : B ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) ≠ ⊥) :
    2 * Nat.card ↥(fixV B) ≤ Nat.card ↥(fixV (Subgroup.zpowers b)) := by
  have hE := hB.2.2
  have hb : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbB
  obtain ⟨ht₁, ht₂⟩ := hC.swap_of_not_mem (hB.1 hbB) hbN
  obtain ⟨⟨x, hxB, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB0
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxN₁ : ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁ := fun l hl => mul_mem_of_mem_normalizer hxN hl
  have hxb : x * b = b * x := hE.1 x hxB b hbB
  obtain ⟨u₀, hu₀b, hu₀x⟩ := exists_fix_moved hC Mm hd hb ht₁ ht₂ (hE.2 x hxB) hxN₁ hxb hx1'
  have hle : fixV B ≤ fixV (Subgroup.zpowers b) := fixV_anti (Subgroup.zpowers_le.mpr hbB)
  have hne : fixV B ≠ fixV (Subgroup.zpowers b) := by
    intro heq
    have hu : u₀ ∈ fixV B := heq ▸ mem_fixV_zpowers_iff.mpr hu₀b
    exact hu₀x (hu x hxB)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · exfalso
    interval_cases c
    · have : 0 < Nat.card ↥(fixV (Subgroup.zpowers b)) := Nat.card_pos
      omega
    · exact hne (Subgroup.eq_of_le_of_card_ge hle (by omega))
  · rw [hc]
    calc 2 * Nat.card ↥(fixV B) = Nat.card ↥(fixV B) * 2 := by ring
      _ ≤ Nat.card ↥(fixV B) * c := Nat.mul_le_mul_left _ hc2

end Core

end CFSG.Quasithin.RonanD37
