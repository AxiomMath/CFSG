module

public import CFSG.Quasithin.MS93.ASC134NC5Rep
public import CFSG.Quasithin.MS93.ASC134NCLin

public section

namespace CFSG.Quasithin.MS93.AS

open Matrix

variable {F : Type} [Field F]

@[expose] def fixAE (a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)) :
    AddSubgroup (Fin 2 → Fin 3 → F) where
  carrier := {n | a n = n}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  zero_mem' := map_zero a
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_neg, hx]

theorem mem_fixAE {a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)} {n : Fin 2 → Fin 3 → F} :
    n ∈ fixAE a ↔ a n = n := Iff.rfl

omit [Field F] in
theorem card_N2 [Finite F] : Nat.card (Fin 2 → Fin 3 → F) = Nat.card F ^ 6 := by
  rw [Nat.card_fun, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

theorem card_fixAE_le [Finite F] [CharP F 2] {a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)}
    {Λ : Matrix (Fin 2) (Fin 2) F} {t : (Fin 3 → F) ≃+ (Fin 3 → F)} (h : IsNRep a Λ t)
    (hΛ : Λ ≠ 1) : Nat.card (fixAE a) ≤ Nat.card F ^ 3 := by
  set N₁ := Λ - 1 with hN₁
  have hN₁0 : N₁ ≠ 0 := fun h0 => hΛ (sub_eq_zero.mp h0)
  have hN₁sq : N₁ * N₁ = 0 := by
    have e : N₁ * N₁ = Λ * Λ - Λ - Λ + 1 := by rw [hN₁]; noncomm_ring
    rw [e, h.2.1, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_assoc 1 Λ Λ,
      CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  obtain ⟨j, hj⟩ : ∃ j, N₁ *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hN₁0 (Matrix.ext_of_mulVec_single fun j => by rw [hcon j, Matrix.zero_mulVec])
  set f₂ : Fin 2 → F := Pi.single j 1 with hf₂
  set f₁ := N₁ *ᵥ f₂ with hf₁
  have hNf₁ : N₁ *ᵥ f₁ = 0 := by rw [hf₁, Matrix.mulVec_mulVec, hN₁sq, Matrix.zero_mulVec]
  have hΛf₂ : Λ *ᵥ f₂ = f₂ + f₁ := by
    rw [hf₁, hN₁, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  obtain ⟨k₀, hk₀⟩ : ∃ k, f₁ k ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hj (funext hcon)
  have hkey : ∀ w : Fin 3 → F, (fun i => f₂ i • w) ∈ fixAE a → w = 0 := by
    intro w hw
    have hfix : ∀ i, (f₂ i + f₁ i) • t w = f₂ i • w := by
      intro i
      have := congrFun (mem_fixAE.mp hw) i
      rw [h.1.2.2] at this
      simp only [h.1.1, smul_smul] at this
      rw [← Finset.sum_smul] at this
      rw [← this]
      congr 1
      have := congrFun hΛf₂ i
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply] at this
      rw [← this]
    have hcomb : ∑ i, N₁ k₀ i • ((f₂ i + f₁ i) • t w) = ∑ i, N₁ k₀ i • (f₂ i • w) :=
      Finset.sum_congr rfl fun i _ => by rw [hfix]
    simp only [smul_smul, ← Finset.sum_smul, mul_add, Finset.sum_add_distrib] at hcomb
    have e1 : ∑ i, N₁ k₀ i * f₂ i = f₁ k₀ := rfl
    have e2 : ∑ i, N₁ k₀ i * f₁ i = 0 := congrFun hNf₁ k₀
    rw [e1, e2, add_zero] at hcomb
    have htw : t w = w := smul_right_injective _ hk₀ hcomb
    have := hfix k₀
    rw [htw, add_smul] at this
    have h0 : f₁ k₀ • w = 0 := by
      have := congrArg (· - f₂ k₀ • w) this
      simpa using this
    exact (smul_eq_zero.mp h0).resolve_left hk₀
  let ψ : ↥(fixAE a) × (Fin 3 → F) → (Fin 2 → Fin 3 → F) := fun p => p.1 + fun i => f₂ i • p.2
  have hψ : Function.Injective ψ := by
    rintro ⟨x, w⟩ ⟨x', w'⟩ hxx
    simp only [ψ] at hxx
    have hmem : (fun i => f₂ i • (w' - w)) ∈ fixAE a := by
      have : (fun i => f₂ i • (w' - w)) = (x : Fin 2 → Fin 3 → F) - x' := by
        funext i
        have hi := congrFun hxx i
        simp only [Pi.add_apply] at hi
        rw [Pi.sub_apply]
        calc f₂ i • (w' - w) = ((x' : Fin 2 → Fin 3 → F) i + f₂ i • w') -
              ((x' : Fin 2 → Fin 3 → F) i + f₂ i • w) := by rw [smul_sub]; abel
          _ = ((x : Fin 2 → Fin 3 → F) i + f₂ i • w) -
              ((x' : Fin 2 → Fin 3 → F) i + f₂ i • w) := by rw [hi]
          _ = (x : Fin 2 → Fin 3 → F) i - (x' : Fin 2 → Fin 3 → F) i := by abel
      rw [this]
      exact (fixAE a).sub_mem x.2 x'.2
    have hw := sub_eq_zero.mp (hkey _ hmem)
    subst hw
    simp only [add_left_inj] at hxx
    exact Prod.ext (Subtype.ext hxx) rfl
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [Nat.card_prod, card_N2, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3),
    Fintype.card_fin] at hle
  have hq : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
  nlinarith


theorem mem_qPt_iff {g : SL3 F} : g ∈ (qPt : Subgroup (SL3 F)) ↔ ∃ a b : F, uniTri a b 0 = g := by
  constructor
  · intro hg
    let P : Subgroup (SL3 F) :=
      { carrier := {g | ∃ a b : F, uniTri a b 0 = g}
        mul_mem' := by
          rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
          exact ⟨a + a', b + b', by rw [uniTri_mul, mul_zero, add_zero, add_zero]⟩
        one_mem' := ⟨0, 0, uniTri_zero⟩
        inv_mem' := by
          rintro _ ⟨a, b, rfl⟩
          exact ⟨-a, -b, by rw [uniTri_inv, mul_zero, zero_sub, neg_zero]⟩ }
    have hle : (qPt : Subgroup (SL3 F)) ≤ P := by
      rw [qPt]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, (rootElt01_eq_uniTri a).symm⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, (rootElt02_eq_uniTri b).symm⟩
    exact hle hg
  · rintro ⟨a, b, rfl⟩
    rw [uniTri_eq_prod, mul_zero, sub_zero, rootElt_zero, mul_one]
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

theorem card_qPt [Finite F] : Nat.card (qPt : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  have e : F × F ≃ (qPt : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri p.1 p.2 0, mem_qPt_iff.mpr ⟨_, _, rfl⟩⟩)
      ⟨fun p p' h => by
        have h' : uniTri p.1 p.2 0 = uniTri p'.1 p'.2 0 := congrArg Subtype.val h
        have := @uniTri_injective F _ (p.1, p.2, 0) (p'.1, p'.2, 0) h'
        simp only [Prod.mk.injEq, and_true] at this
        exact Prod.ext this.1 this.2, by
        rintro ⟨g, hg⟩
        obtain ⟨a, b, rfl⟩ := mem_qPt_iff.mp hg
        exact ⟨(a, b), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem card_bounds_of_le_qPt [Finite F] {B : Subgroup (SL3 F)} (hB : B ≤ qPt) (hB1 : B ≠ ⊥) :
    Nat.card (fixN B) ≤ Nat.card F ^ 2 ∧ Nat.card B * Nat.card (fixN B) ≤ Nat.card F ^ 3 ∧
      (Nat.card F < Nat.card B → Nat.card (fixN B) ≤ Nat.card F) := by
  classical
  have hcardB : Nat.card B ≤ Nat.card F ^ 2 := (Subgroup.card_le_of_le hB).trans card_qPt.le
  have hpt : pt0 ≤ fixN B := pt0_le_fixN_of_le_sStar (hB.trans qPt_le_sStar)
  have htop : fixN B ≠ ⊤ := by
    intro htop
    apply hB1
    refine eq_bot_iff.mpr fun g hg => ?_
    rw [Subgroup.mem_bot]
    exact eq_one_of_mulVec_eq_self fun x =>
      (show x ∈ fixN B from htop ▸ Submodule.mem_top) g hg
  have hfr : Module.finrank F (fixN B) ≤ 2 := by
    have := Submodule.finrank_lt htop
    rw [Module.finrank_fin_fun] at this
    omega
  have hcardH : Nat.card (fixN B) ≤ Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    exact Nat.pow_le_pow_right Nat.card_pos hfr
  by_cases hle : fixN B ≤ pt0
  · have hH : Nat.card (fixN B) = Nat.card F := by rw [le_antisymm hle hpt, card_pt0]
    refine ⟨hcardH, ?_, fun _ => hH.le⟩
    rw [hH]
    calc Nat.card B * Nat.card F ≤ Nat.card F ^ 2 * Nat.card F := Nat.mul_le_mul_right _ hcardB
      _ = Nat.card F ^ 3 := by ring
  · obtain ⟨h, hh, hhpt⟩ := Set.not_subset.mp hle
    have hhpt' : ¬ (h 1 = 0 ∧ h 2 = 0) := hhpt
    have hform : ∀ g ∈ B, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 1 * h 1 +
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 2 * h 2 = 0 := by
      intro g hg
      obtain ⟨a, b, rfl⟩ := mem_qPt_iff.mp (hB hg)
      have := congrFun (hh _ hg) 0
      rw [coe_uniTri] at this ⊢
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this ⊢
      linear_combination this
    have hBq : Nat.card B ≤ Nat.card F := by
      refine Nat.card_le_card_of_injective (fun g : B => if h 2 ≠ 0 then
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 1 else
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 2) ?_
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg
      obtain ⟨a, b, rfl⟩ := mem_qPt_iff.mp (hB hg)
      obtain ⟨a', b', rfl⟩ := mem_qPt_iff.mp (hB hg')
      have e := hform _ hg
      have e' := hform _ hg'
      simp only [coe_uniTri] at hgg e e'
      simp at hgg e e'
      have hab : a = a' ∧ b = b' := by
        by_cases h2 : h 2 = 0
        · simp only [h2, ↓reduceIte] at hgg
          have h1 : h 1 ≠ 0 := fun h1 => hhpt' ⟨h1, h2⟩
          rw [h2, mul_zero, add_zero] at e e'
          have ha : a = 0 := (mul_eq_zero.mp e).resolve_right h1
          have ha' : a' = 0 := (mul_eq_zero.mp e').resolve_right h1
          exact ⟨by rw [ha, ha'], hgg⟩
        · simp only [h2, ↓reduceIte] at hgg
          subst hgg
          refine ⟨rfl, ?_⟩
          have := e.trans e'.symm
          exact mul_right_cancel₀ h2 (add_left_cancel this)
      obtain ⟨rfl, rfl⟩ := hab
      rfl
    refine ⟨hcardH, ?_, fun hlt => absurd hlt (not_lt.mpr hBq)⟩
    calc Nat.card B * Nat.card (fixN B) ≤ Nat.card F * Nat.card F ^ 2 := Nat.mul_le_mul hBq hcardH
      _ = Nat.card F ^ 3 := by ring

theorem two_mul_card_fixAE_lt [Finite F] {a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)}
    {σ : F → F} (hσ : ∀ (μ : F) n, a (μ • n) = σ μ • a n) {μ : F} (hμ : σ μ ≠ μ) :
    2 * Nat.card (fixAE a) < Nat.card (Fin 2 → Fin 3 → F) := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn⟩ := a.surjective (Pi.single 0 (Pi.single 0 1))
    have := hσ 0 n
    rw [zero_smul, map_zero, hn] at this
    have := congrFun (congrFun this.symm 0) 0
    simp at this
    exact hμ this
  by_contra hcon
  push Not at hcon
  let m : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F) :=
    { toFun := fun n => μ • n
      invFun := fun n => μ⁻¹ • n
      left_inv := fun n => by simp [smul_smul, inv_mul_cancel₀ hμ0]
      right_inv := fun n => by simp [smul_smul, mul_inv_cancel₀ hμ0]
      map_add' := fun x y => smul_add μ x y }
  set S := fixAE a ⊓ (fixAE a).comap (m : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F)) with hS
  have hidx : (fixAE a).index ≤ 2 := by
    have h := (fixAE a).card_mul_index
    have hpos : 0 < Nat.card (fixAE a) := Nat.card_pos
    nlinarith
  have hidx' : ((fixAE a).comap (m : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F))).index =
      (fixAE a).index := AddSubgroup.index_comap_of_surjective _ m.surjective
  have hidxS : S.index ≤ 4 := by
    have := AddSubgroup.index_inf_le (H := fixAE a)
      (K := (fixAE a).comap (m : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F)))
    rw [hidx'] at this
    nlinarith
  have hcardS : 1 < Nat.card S := by
    have h := S.card_mul_index
    rw [card_N2] at h
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h64 : 64 ≤ Nat.card F ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left hq 6
    by_contra hS1
    push Not at hS1
    have : Nat.card S * S.index ≤ 1 * 4 := Nat.mul_le_mul hS1 hidxS
    omega
  have hnt : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp hcardS
  obtain ⟨⟨n, hnS⟩, hn0⟩ := exists_ne (0 : S)
  have hn0' : n ≠ 0 := fun h => hn0 (Subtype.ext h)
  have h1 : a n = n := hnS.1
  have h2 : a (μ • n) = μ • n := hnS.2
  rw [hσ, h1] at h2
  have : (σ μ - μ) • n = 0 := by rw [sub_smul, h2, sub_self]
  exact hμ (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hn0'))


@[expose] def dgPerm : SL3 F →* Equiv.Perm (Fin 2 → Fin 3 → F) where
  toFun g :=
    { toFun := dg g
      invFun := dg g⁻¹
      left_inv := fun n => by
        funext i
        simp only [dg_apply]
        rw [← sl3_mulVec_mul, inv_mul_cancel, sl3_one_mulVec]
      right_inv := fun n => by
        funext i
        simp only [dg_apply]
        rw [← sl3_mulVec_mul, mul_inv_cancel, sl3_one_mulVec] }
  map_one' := by
    ext n i
    simp only [Equiv.coe_fn_mk, dg_apply, sl3_one_mulVec, Equiv.Perm.coe_one, id_eq]
  map_mul' := fun g h => by
    ext n i
    simp only [Equiv.coe_fn_mk, dg_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [sl3_mulVec_mul]

theorem dgPerm_apply (g : SL3 F) (n : Fin 2 → Fin 3 → F) : dgPerm g n = dg g n := rfl

theorem dgPerm_injective : Function.Injective (dgPerm : SL3 F →* Equiv.Perm _) :=
  fun g h hgh => dg_injective fun n => by
    rw [← dgPerm_apply, ← dgPerm_apply, hgh]

@[expose] def fixP (𝒜 : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))) : Set (Fin 2 → Fin 3 → F) :=
  {n | ∀ a ∈ 𝒜, a n = n}

theorem eq_one_of_mul_self_eq_one [CharP F 2] {x : F} (hx : x * x = 1) : x = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (x - 1) ^ 2 = 0 := by linear_combination hx + (1 - x) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)

theorem card_le_of_isPGroup_GL [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {U : Subgroup (GL (Fin 2) F)} (hU : IsPGroup 2 U) : Nat.card U ≤ Fintype.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hU.exists_card_eq
  have hd := Subgroup.card_subgroup_dvd_card U
  rw [hm, Matrix.card_GL_field, Fin.prod_univ_two] at hd
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hd
  set q := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := Fintype.one_lt_card (α := F)
      rw [← hq, hF, h0] at this
      norm_num at this
    · exact h0
  have hodd1 : Odd (q ^ 2 - 1) := by
    rw [hF, ← pow_mul]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by positivity⟩) odd_one
  have hodd2 : Odd (q - 1) := by
    rw [hF]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hsplit : (q ^ 2 - 1) * (q ^ 2 - q) = q * ((q ^ 2 - 1) * (q - 1)) := by
    have : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [this]
    ring
  rw [hsplit] at hd
  have hcop : Nat.Coprime (2 ^ m) ((q ^ 2 - 1) * (q - 1)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (hodd1.mul hodd2))
  rw [hm]
  exact Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hd)

theorem offender_eq_bot [Fintype F] [CharP F 2] {n₀ : ℕ} (hF : Fintype.card F = 2 ^ n₀)
    (𝒜 : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)))
    (hadd : ∀ a ∈ 𝒜, ∀ x y, a (x + y) = a x + a y)
    (hcomm : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, a * b = b * a) (hsq : ∀ a ∈ 𝒜, a * a = 1)
    (hnorm : ∀ a ∈ 𝒜, ∀ g : SL3 F, ∃ h : SL3 F, ∀ n, a (dg g n) = dg h (a n))
    (hpt : ∀ a ∈ 𝒜, ∀ g : SL3 F, (∀ n, a n = dg g n) → g ∈ qPt)
    (hoff : Nat.card (Fin 2 → Fin 3 → F) ≤ Nat.card 𝒜 * Nat.card ↥(fixP 𝒜)) :
    𝒜 = ⊥ := by
  classical
  set q := Nat.card F with hqdef
  have hqF : q = Fintype.card F := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hN := card_N2 (F := F)
  rw [hN] at hoff
  let ae : ∀ a ∈ 𝒜, (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F) :=
    fun a ha => AddEquiv.mk' a (hadd a ha)
  have haa : ∀ a ∈ 𝒜, ∀ n, a (a n) = n := fun a ha n => by
    have := congrArg (fun f : Equiv.Perm (Fin 2 → Fin 3 → F) => f n) (hsq a ha)
    simpa using this
  have hne0 : (Pi.single 0 (Pi.single 0 1) : Fin 2 → Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  have hsemi : ∀ a ∈ 𝒜, ∃ σ : F ≃+* F, ∀ (μ : F) n, a (μ • n) = σ μ • a n := by
    intro a ha
    obtain ⟨t, Λ, σ, -, hσ, hrep⟩ := exists_decomp_of_sq (a := ae a ha) (haa a ha) (hnorm a ha)
    refine ⟨σ, fun μ n => funext fun i => ?_⟩
    rw [Pi.smul_apply]
    show ae a ha (μ • n) i = σ μ • ae a ha n i
    rw [hrep, hrep, ← hσ, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_comm]
  have hinvol : ∀ a ∈ 𝒜, ∀ σ : F ≃+* F, (∀ (μ : F) n, a (μ • n) = σ μ • a n) →
      ∀ x, σ (σ x) = x := by
    intro a ha σ hσ x
    have e : σ (σ x) • (Pi.single 0 (Pi.single 0 1) : Fin 2 → Fin 3 → F) =
        x • Pi.single 0 (Pi.single 0 1) := by
      have h1 : a (a (x • (Pi.single 0 (Pi.single 0 1) : Fin 2 → Fin 3 → F))) =
          x • Pi.single 0 (Pi.single 0 1) := haa a ha _
      rw [hσ, hσ, haa a ha] at h1
      exact h1
    have := congrFun (congrFun e 0) 0
    simpa using this
  let A₀ : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)) :=
    { carrier := {a | a ∈ 𝒜 ∧ ∀ (μ : F) n, a (μ • n) = μ • a n}
      mul_mem' := fun {a b} ha hb => ⟨𝒜.mul_mem ha.1 hb.1, fun μ n => by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [hb.2, ha.2]⟩
      one_mem' := ⟨𝒜.one_mem, fun μ n => rfl⟩
      inv_mem' := fun {a} ha => ⟨𝒜.inv_mem ha.1, fun μ n => by
        apply a.injective
        simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
        rw [ha.2, Equiv.apply_symm_apply]⟩ }
  have hA₀𝒜 : A₀ ≤ 𝒜 := fun a ha => ha.1
  have hmemA₀ : ∀ a, a ∈ A₀ ↔ a ∈ 𝒜 ∧ ∀ (μ : F) n, a (μ • n) = μ • a n := fun _ => Iff.rfl
  have hnotA₀ : ∀ a ∈ 𝒜, a ∉ A₀ → ∃ σ : F ≃+* F, (∀ (μ : F) n, a (μ • n) = σ μ • a n) ∧
      (∀ x, σ (σ x) = x) ∧ ∃ μ, σ μ ≠ μ := by
    intro a ha haA₀
    obtain ⟨σ, hσ⟩ := hsemi a ha
    refine ⟨σ, hσ, hinvol a ha σ hσ, ?_⟩
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact haA₀ ⟨ha, fun μ n => by rw [hσ, hcon]⟩
  have hε : Nat.card 𝒜 ≤ 2 * Nat.card A₀ := by
    by_cases hall : 𝒜 ≤ A₀
    · have := Subgroup.card_le_of_le hall
      omega
    · obtain ⟨c, hc𝒜, hcA₀⟩ := Set.not_subset.mp hall
      obtain ⟨σ, hσ, hσσ, hσ1⟩ := hnotA₀ c hc𝒜 hcA₀
      have hprod : ∀ x ∈ 𝒜, x ∉ A₀ → c * x ∈ A₀ := by
        intro x hx hxA₀
        obtain ⟨τ, hτ, hττ, hτ1⟩ := hnotA₀ x hx hxA₀
        have hστ : σ = τ := ringEquiv_eq_of_involutive hσσ hττ hσ1 hτ1
        refine ⟨𝒜.mul_mem hc𝒜 hx, fun μ n => ?_⟩
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [hτ, hσ, hστ, hττ]
      let f : 𝒜 → A₀ × Bool := fun x => if hx : (x : Equiv.Perm _) ∈ A₀ then (⟨x, hx⟩, true)
        else (⟨c * x, hprod x x.2 hx⟩, false)
      have hf : Function.Injective f := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simp only [f] at hxy
        by_cases hxA : x ∈ A₀ <;> by_cases hyA : y ∈ A₀ <;>
          simp only [hxA, hyA, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
            Bool.true_eq_false, Bool.false_eq_true, and_false, and_true] at hxy
        · exact Subtype.ext hxy
        · exact Subtype.ext (mul_left_cancel hxy)
      have := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
      omega
  have hε2 : q = 2 → 𝒜 ≤ A₀ := by
    intro hq a ha
    by_contra haA₀
    obtain ⟨σ, -, -, μ, hμ⟩ := hnotA₀ a ha haA₀
    have hF2 : ∀ x : F, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).mp (hqdef ▸ hq)
        exact (hy x hx).trans (hy 1 one_ne_zero).symm
    rcases hF2 μ with h0 | h1
    · exact hμ (by rw [h0, map_zero])
    · exact hμ (by rw [h1, map_one])
  have hnrep : ∀ a ∈ A₀, ∃ (Λ : Matrix (Fin 2) (Fin 2) F) (t : (Fin 3 → F) ≃+ (Fin 3 → F)),
      IsNRep a Λ t := fun a ha =>
    exists_nrep (a := ae a ha.1) (haa a ha.1) (hnorm a ha.1) ha.2
  choose Λf tf hΛf using hnrep
  have hΛsq : ∀ a (ha : a ∈ A₀), Λf a ha * Λf a ha = 1 := fun a ha => (hΛf a ha).2.1
  have hidrep : IsNRep (⇑(1 : Equiv.Perm (Fin 2 → Fin 3 → F))) 1 (AddEquiv.refl _) := by
    refine ⟨⟨fun μ w => rfl, fun g => ⟨g, fun w => rfl⟩, fun n i => ?_⟩, one_mul 1,
      fun w => rfl⟩
    simp [Matrix.one_apply]
  let φ : ↥A₀ →* GL (Fin 2) F :=
    { toFun := fun a => ⟨Λf a a.2, Λf a a.2, hΛsq a a.2, hΛsq a a.2⟩
      map_one' := Units.ext
        (IsNRep.unique (Equiv.surjective _) (hΛf 1 A₀.one_mem) hidrep).1
      map_mul' := fun a b => by
        apply Units.ext
        show Λf (a * b) _ = Λf a a.2 * Λf b b.2
        have ha := hΛf a a.2
        have hb := hΛf b b.2
        have hab := IsRep.mul ha.1 hb.1
        have hba := IsRep.mul hb.1 ha.1
        have hcomm' : (⇑(b : Equiv.Perm (Fin 2 → Fin 3 → F)) ∘
            ⇑(a : Equiv.Perm (Fin 2 → Fin 3 → F))) =
            (⇑(a : Equiv.Perm (Fin 2 → Fin 3 → F)) ∘ ⇑(b : Equiv.Perm (Fin 2 → Fin 3 → F))) := by
          have := hcomm (a : Equiv.Perm (Fin 2 → Fin 3 → F)) (hA₀𝒜 a.2)
            (b : Equiv.Perm (Fin 2 → Fin 3 → F)) (hA₀𝒜 b.2)
          rw [← Equiv.Perm.coe_mul, ← Equiv.Perm.coe_mul, this]
        rw [hcomm'] at hba
        obtain ⟨c, hc, htc⟩ := IsRep.unique (Equiv.surjective _ |>.comp (Equiv.surjective _))
          hab hba
        have hdet : (Λf a a.2 * Λf b b.2).det ≠ 0 := by
          intro h0
          have := congrArg Matrix.det (hΛsq a a.2)
          rw [Matrix.det_mul, Matrix.det_one] at this
          rw [Matrix.det_mul] at h0
          have := congrArg Matrix.det (hΛsq b b.2)
          rw [Matrix.det_mul, Matrix.det_one] at this
          rcases mul_eq_zero.mp h0 with h | h <;> simp_all
        have hc1 : c = 1 := by
          have e := congrArg Matrix.det hc
          rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul, mul_comm
            (Matrix.det (Λf b b.2))] at e
          rw [Matrix.det_mul] at hdet
          have : c ^ 2 = 1 := by
            have := mul_right_cancel₀ hdet (e.symm.trans (one_mul _).symm)
            exact this
          exact eq_one_of_mul_self_eq_one (by rw [← sq]; exact this)
        rw [hc1, one_smul] at hc
        have htab : ∀ w, tf a a.2 (tf b b.2 w) = tf b b.2 (tf a a.2 w) := fun w => by
          have := htc w
          rw [hc1, one_smul] at this
          exact this
        have hnab : IsNRep (⇑((a * b : ↥A₀) : Equiv.Perm (Fin 2 → Fin 3 → F))) (Λf a a.2 * Λf b b.2)
            ((tf b b.2).trans (tf a a.2)) := by
          refine ⟨?_, ?_, fun w => ?_⟩
          · simpa [Equiv.Perm.coe_mul] using hab
          · calc Λf a a.2 * Λf b b.2 * (Λf a a.2 * Λf b b.2) =
                Λf a a.2 * (Λf b b.2 * Λf a a.2) * Λf b b.2 := by noncomm_ring
              _ = Λf a a.2 * (Λf a a.2 * Λf b b.2) * Λf b b.2 := by rw [hc]
              _ = 1 := by
                rw [← mul_assoc, hΛsq, one_mul, hΛsq]
          · simp only [AddEquiv.trans_apply]
            rw [← htab, (hΛf b b.2).2.2]
            exact (hΛf a a.2).2.2 w
        exact (IsNRep.unique (Equiv.surjective _) (hΛf (a * b) (a * b).2) hnab).1 }
  set B : Subgroup (SL3 F) := 𝒜.comap dgPerm with hBdef
  set A₁ : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)) := B.map dgPerm with hA₁def
  have hA₁𝒜 : A₁ ≤ 𝒜 := Subgroup.map_comap_le _ _
  have hcardA₁ : Nat.card A₁ = Nat.card B := Subgroup.card_map_of_injective dgPerm_injective
  have hBpt : B ≤ qPt := fun g hg => hpt (dgPerm g) hg g fun n => rfl
  have hA₁A₀ : A₁ ≤ A₀ := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg, fun μ n => funext fun i => by
      simp only [dgPerm_apply, dg_apply, Pi.smul_apply, Matrix.mulVec_smul]⟩
  have hker : ∀ a : ↥A₀, φ a = 1 ↔ (a : Equiv.Perm (Fin 2 → Fin 3 → F)) ∈ A₁ := by
    intro a
    constructor
    · intro h1
      have hΛ1 : Λf a a.2 = 1 := congrArg Units.val h1
      have hrep := (hΛf a a.2).1
      have hat : ∀ n i, (a : Equiv.Perm (Fin 2 → Fin 3 → F)) n i = tf a a.2 (n i) := by
        intro n i
        rw [hrep.2.2, hΛ1]
        simp [Matrix.one_apply]
      let T : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
        { toFun := tf a a.2, map_add' := map_add (tf a a.2), map_smul' := hrep.1 }
      set M := LinearMap.toMatrix' T with hMdef
      have hM : ∀ w, M *ᵥ w = tf a a.2 w := fun w => LinearMap.toMatrix'_mulVec T w
      have hMM : M * M = 1 := by
        refine Matrix.ext_of_mulVec_single fun j => ?_
        rw [← Matrix.mulVec_mulVec, hM, hM, (hΛf a a.2).2.2, Matrix.one_mulVec]
      have hdet : M.det = 1 :=
        eq_one_of_mul_self_eq_one (by rw [← Matrix.det_mul, hMM, Matrix.det_one])
      let g : SL3 F := ⟨M, hdet⟩
      have hgM : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = M := rfl
      have hga : dgPerm g = a := by
        refine Equiv.ext fun n => funext fun i => ?_
        rw [dgPerm_apply, dg_apply, hgM, hM, hat]
      refine ⟨g, ?_, hga⟩
      show dgPerm _ ∈ 𝒜
      rw [hga]
      exact hA₀𝒜 a.2
    · rintro ⟨g, hg, hga⟩
      have hgg : g * g = 1 := by
        apply dgPerm_injective
        rw [map_mul, map_one, hga]
        exact hsq _ (hA₀𝒜 a.2)
      let tg : (Fin 3 → F) ≃+ (Fin 3 → F) :=
        { toFun := fun w => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w
          invFun := fun w => ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w
          left_inv := fun w => by
            simp only
            rw [← sl3_mulVec_mul, inv_mul_cancel, sl3_one_mulVec]
          right_inv := fun w => by
            simp only
            rw [← sl3_mulVec_mul, mul_inv_cancel, sl3_one_mulVec]
          map_add' := fun x y => Matrix.mulVec_add _ x y }
      have hn : IsNRep (⇑(a : Equiv.Perm (Fin 2 → Fin 3 → F))) 1 tg := by
        refine ⟨⟨fun μ w => Matrix.mulVec_smul _ μ w, fun h => ⟨g * h * g⁻¹, fun w => ?_⟩,
          fun n i => ?_⟩, one_mul 1, fun w => ?_⟩
        · show ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((h : SL3 F) :
            Matrix (Fin 3) (Fin 3) F) *ᵥ w) = ((g * h * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w)
          rw [← sl3_mulVec_mul, ← sl3_mulVec_mul, show g * h * g⁻¹ * g = g * h by group]
        · rw [← hga, dgPerm_apply, dg_apply]
          simp [Matrix.one_apply]
          rfl
        · show ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w
          rw [← sl3_mulVec_mul, hgg, sl3_one_mulVec]
      exact Units.ext (IsNRep.unique (Equiv.surjective _) (hΛf a a.2) hn).1
  have hcardA₀ : Nat.card A₀ ≤ q * Nat.card A₁ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
    have hkerA₁ : φ.ker = A₁.subgroupOf A₀ := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
    have hk : Nat.card φ.ker = Nat.card A₁ := by
      rw [hkerA₁]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁A₀).toEquiv
    have hr : Nat.card φ.range ≤ q := by
      have h2 : IsPGroup 2 φ.range := by
        rintro ⟨u, ⟨a, rfl⟩⟩
        refine ⟨1, Subtype.ext ?_⟩
        have haa' : a * a = 1 := Subtype.ext (hsq _ (hA₀𝒜 a.2))
        simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
        rw [pow_two, ← map_mul, haa', map_one]
      rw [hqF]
      exact card_le_of_isPGroup_GL hF h2
    rw [h1, hk]
    exact Nat.mul_le_mul_right _ hr
  have hfixle : ∀ (X : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))), X ≤ 𝒜 →
      Nat.card ↥(fixP 𝒜) ≤ Nat.card ↥(fixP X) := fun X hX =>
    Nat.card_mono (Set.toFinite _) fun n hn a ha => hn a (hX ha)
  have hfixa : ∀ a (ha : a ∈ 𝒜), Nat.card ↥(fixP 𝒜) ≤ Nat.card (fixAE (ae a ha)) :=
    fun a ha => Nat.card_mono (Set.toFinite (fixAE (ae a ha) : Set (Fin 2 → Fin 3 → F)))
      fun n hn => hn a ha
  have hfixA₁ : Nat.card ↥(fixP A₁) = Nat.card (fixN B) ^ 2 := by
    have hmem : ∀ n, n ∈ fixP A₁ ↔ ∀ i, n i ∈ fixN B := by
      intro n
      constructor
      · intro hn i g hg
        have := congrFun (hn (dgPerm g) ⟨g, hg, rfl⟩) i
        rwa [dgPerm_apply, dg_apply] at this
      · rintro hn _ ⟨g, hg, rfl⟩
        funext i
        rw [dgPerm_apply, dg_apply]
        exact hn i g hg
    let e : ↥(fixP A₁) ≃ (fixN B) × (fixN B) :=
      { toFun := fun n => (⟨n.1 0, (hmem n.1).mp n.2 0⟩, ⟨n.1 1, (hmem n.1).mp n.2 1⟩)
        invFun := fun p => ⟨![p.1, p.2], (hmem _).mpr fun i => by
          fin_cases i
          · exact p.1.2
          · exact p.2.2⟩
        left_inv := fun n => by
          apply Subtype.ext
          funext i
          fin_cases i <;> rfl
        right_inv := fun p => rfl }
    rw [Nat.card_congr e, Nat.card_prod, sq]
  have hε' : 2 * Nat.card 𝒜 ≤ q * Nat.card A₀ := by
    by_cases hq : q = 2
    · have := Subgroup.card_le_of_le (hε2 hq)
      rw [hq]
      omega
    · have hq4 : 4 ≤ q := by
        rw [hqF, hF] at hq ⊢
        rcases n₀ with _ | _ | n
        · rw [hqF, hF] at hq2
          norm_num at hq2
        · norm_num at hq
        · calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
  have hq6 : 0 < q ^ 6 := pow_pos (by omega) 6
  by_contra hne
  by_cases hI : A₀ ≤ A₁
  · have hA₀A₁ : Nat.card A₀ ≤ Nat.card A₁ := Subgroup.card_le_of_le hI
    by_cases hBb : B = ⊥
    ·
      have hA₀1 : Nat.card A₀ ≤ 1 := by
        rw [← Subgroup.card_bot (G := SL3 F), ← hBb, ← hcardA₁]
        exact hA₀A₁
      obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      have haA₀ : a ∉ A₀ := by
        intro haA₀
        have hbot : A₀ = ⊥ := Subgroup.eq_bot_of_card_le A₀ hA₀1
        rw [hbot, Subgroup.mem_bot] at haA₀
        exact ha1' haA₀
      obtain ⟨σ, hσ, -, μ, hμ⟩ := hnotA₀ a ha haA₀
      have h2 := two_mul_card_fixAE_lt (a := ae a ha) hσ hμ
      rw [card_N2] at h2
      have h3 := hfixa _ ha
      have : Nat.card 𝒜 ≤ 2 := by omega
      nlinarith
    · obtain ⟨hH2, hBH, -⟩ := card_bounds_of_le_qPt hBpt hBb
      have hF2 : Nat.card ↥(fixP 𝒜) ≤ Nat.card (fixN B) ^ 2 := by
        rw [← hfixA₁]
        exact hfixle A₁ hA₁𝒜
      have : 2 * q ^ 6 ≤ q ^ 6 := by
        calc 2 * q ^ 6 ≤ 2 * (Nat.card 𝒜 * Nat.card ↥(fixP 𝒜)) := by
              rw [hqdef]; exact Nat.mul_le_mul_left 2 hoff
          _ = (2 * Nat.card 𝒜) * Nat.card ↥(fixP 𝒜) := by ring
          _ ≤ (q * Nat.card A₀) * Nat.card (fixN B) ^ 2 := Nat.mul_le_mul hε' hF2
          _ ≤ (q * Nat.card B) * Nat.card (fixN B) ^ 2 := by
              rw [← hcardA₁]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA₀A₁)
          _ = q * (Nat.card B * Nat.card (fixN B)) * Nat.card (fixN B) := by ring
          _ ≤ q * q ^ 3 * q ^ 2 := by
              rw [hqdef]
              exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hBH) hH2
          _ = q ^ 6 := by ring
      omega
  · obtain ⟨a, haA₀, haA₁⟩ := Set.not_subset.mp hI
    have hφa : φ ⟨a, haA₀⟩ ≠ 1 := fun h => haA₁ ((hker ⟨a, haA₀⟩).mp h)
    have hΛa : Λf a haA₀ ≠ 1 := fun h => hφa (Units.ext h)
    have hfa : Nat.card ↥(fixP 𝒜) ≤ q ^ 3 :=
      (hfixa a (hA₀𝒜 haA₀)).trans (card_fixAE_le (a := ae a (hA₀𝒜 haA₀)) (hΛf a haA₀) hΛa)
    by_cases hBq : Nat.card B ≤ q
    · have : 2 * q ^ 6 ≤ q ^ 6 := by
        calc 2 * q ^ 6 ≤ 2 * (Nat.card 𝒜 * Nat.card ↥(fixP 𝒜)) := by
              rw [hqdef]; exact Nat.mul_le_mul_left 2 hoff
          _ = (2 * Nat.card 𝒜) * Nat.card ↥(fixP 𝒜) := by ring
          _ ≤ (q * Nat.card A₀) * q ^ 3 := Nat.mul_le_mul hε' hfa
          _ ≤ (q * (q * Nat.card B)) * q ^ 3 := by
              rw [← hcardA₁]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcardA₀)
          _ ≤ (q * (q * q)) * q ^ 3 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hBq))
          _ = q ^ 6 := by ring
      omega
    · push Not at hBq
      have hBb : B ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hBq
        omega
      obtain ⟨-, -, hBH⟩ := card_bounds_of_le_qPt hBpt hBb
      have hH : Nat.card (fixN B) ≤ q := hBH hBq
      have hF2 : Nat.card ↥(fixP 𝒜) ≤ q ^ 2 := by
        calc Nat.card ↥(fixP 𝒜) ≤ Nat.card ↥(fixP A₁) := hfixle A₁ hA₁𝒜
          _ = Nat.card (fixN B) ^ 2 := hfixA₁
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hH 2
      have hBq2 : Nat.card B ≤ q ^ 2 := (Subgroup.card_le_of_le hBpt).trans card_qPt.le
      have : 2 * q ^ 6 ≤ q ^ 6 := by
        calc 2 * q ^ 6 ≤ 2 * (Nat.card 𝒜 * Nat.card ↥(fixP 𝒜)) := by
              rw [hqdef]; exact Nat.mul_le_mul_left 2 hoff
          _ = (2 * Nat.card 𝒜) * Nat.card ↥(fixP 𝒜) := by ring
          _ ≤ (q * Nat.card A₀) * q ^ 2 := Nat.mul_le_mul hε' hF2
          _ ≤ (q * (q * Nat.card B)) * q ^ 2 := by
              rw [← hcardA₁]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcardA₀)
          _ ≤ (q * (q * q ^ 2)) * q ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hBq2))
          _ = q ^ 6 := by ring
      omega

end CFSG.Quasithin.MS93.AS
