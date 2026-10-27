module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmPlus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace OrdPOm

section MinusForm

variable {K : Type} [Field K] {n : ℕ}

@[expose] def minusUnits {m : ℕ} (u : Fin m → Kˣ) : Fin m ⊕ Fin m ⊕ Fin 2 → Kˣ :=
  Sum.elim u (Sum.elim (fun i => (u i)⁻¹) 1)

@[expose] def minusHom {m : ℕ} : (Fin m → Kˣ) →* (Fin m ⊕ Fin m ⊕ Fin 2 → Kˣ) where
  toFun := minusUnits
  map_one' := by
    funext x
    rcases x with x | x | x <;> simp [minusUnits]
  map_mul' u v := by
    funext x
    rcases x with x | x | x <;> simp [minusUnits, mul_comm]

theorem minusHom_apply {m : ℕ} (u : Fin m → Kˣ) : minusHom u = minusUnits u :=
  rfl

theorem isHypCoord_quadMinus (b c : K) (k : Fin (n - 1)) :
    SeitzReduction.OmegaPilot.IsHypCoord (quadMinus n K b c) (Sum.inl k)
      (Sum.inr (Sum.inl k)) where
  ne := Sum.inl_ne_inr
  map_left := by
    rw [quadMinus_apply]
    simp [Pi.single_apply]
  map_right := by
    rw [quadMinus_apply]
    simp [Pi.single_apply]
  polar_left v := by rw [QuadraticMap.polar_comm, polar_quadMinus_single_inl]
  polar_right v := by rw [QuadraticMap.polar_comm, polar_quadMinus_single_inr_inl]

theorem finrank_le_of_singular_quadMinus [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 1 ≤ n)
    (T : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
    (hT : ∀ w ∈ T, quadMinus n K b c w = 0) : Module.finrank K T ≤ n - 1 :=
  TableBOrth.finrank_le_of_isometryEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry n K hn b c)
    (SeitzReduction.OmegaPilot.regular_wittIndex_coordinateQuadMinus hn hirr).2 T hT

variable [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] {ζ : Kˣ} {b c : K}

theorem exists_orth_conj_minus_le (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 1 ≤ n)
    {A : Subgroup (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)}
    (hAO : A ≤ LargeEvenOrthGroup (StatedQuadMinus n K b c)) (hA : IsElemAbelian p A) :
    ∃ g ∈ LargeEvenOrthGroup (StatedQuadMinus n K b c), ∃ χ : Fin (n - 1) → A →* Kˣ,
      ∀ x : A, g * (x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) * g⁻¹ =
        TauCeti.diagGL (minusUnits fun k => χ k x) := by
  rw [← coe_quadMinus n K b c] at hAO ⊢
  exact exists_orth_conj_diag_le (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) hp2 hζo
    (finrank_le_of_singular_quadMinus hirr hn) (isHypCoord_quadMinus b c)
    (fun i j h => Sum.inl_injective (Sum.inr_injective h)) (fun i j => Sum.inl_ne_inr)
    minusUnits (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with k | k | k
      · exact absurd rfl (hi k).1
      · exact absurd rfl (hi k).2
      · rfl)
    hAO hA

theorem card_le_minus (hp2 : p ≠ 2) (hζo : orderOf ζ = p) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 1 ≤ n) {A : Subgroup (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)}
    (hAO : A ≤ LargeEvenOrthGroup (StatedQuadMinus n K b c)) (hA : IsElemAbelian p A) :
    Nat.card A ≤ p ^ (n - 1) := by
  rw [← coe_quadMinus n K b c] at hAO
  exact card_le_of_orth (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) hp2 hζo
    (finrank_le_of_singular_quadMinus hirr hn) (isHypCoord_quadMinus b c)
    (fun i j h => Sum.inl_injective (Sum.inr_injective h)) (fun i j => Sum.inl_ne_inr)
    minusUnits (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with k | k | k
      · exact absurd rfl (hi k).1
      · exact absurd rfl (hi k).2
      · rfl)
    hAO hA

end MinusForm

section Torus

theorem mem_commutator_of_conj_eq_inv {H : Type*} [Group H] {O : Subgroup H} {p : ℕ} (hp : Odd p)
    {d w : H} (hdO : d ∈ O) (hwO : w ∈ O) (hdp : d ^ p = 1) (hwd : w * d * w⁻¹ = d⁻¹) :
    d ∈ (⁅O, O⁆ : Subgroup H) := by
  obtain ⟨k, hk⟩ := hp
  have hx : w * d ^ (k + 1) * w⁻¹ = (d ^ (k + 1))⁻¹ := by rw [← conj_pow, hwd, inv_pow]
  have hc : ⁅d ^ (k + 1), w⁆ = d := by
    rw [commutatorElement_def]
    calc d ^ (k + 1) * w * (d ^ (k + 1))⁻¹ * w⁻¹ = d ^ (k + 1) * (w * d ^ (k + 1) * w⁻¹)⁻¹ := by
          group
      _ = d ^ (k + 1 + (k + 1)) := by rw [hx, inv_inv, ← pow_add]
      _ = d := by rw [show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hdp, one_mul]
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (pow_mem hdO _) hwO

variable {K : Type} [Field K] {p : ℕ} {ζ : Kˣ} {m : ℕ}

@[expose] noncomputable def minusTorusGL (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* GL (Fin m ⊕ Fin m ⊕ Fin 2) K :=
  TauCeti.diagGL.comp (minusHom.comp ((TableBSymp.zmodPowHom hζ).compLeft (Fin m)))

theorem minusTorusGL_apply (hζ : ζ ^ p = 1) (a : Fin m → Multiplicative (ZMod p)) :
    minusTorusGL hζ a = TauCeti.diagGL (minusUnits fun i => TableBSymp.zmodPowHom hζ (a i)) :=
  rfl

theorem isElemAbelian_range_minusTorusGL (hζ : ζ ^ p = 1) :
    IsElemAbelian p (minusTorusGL (K := K) (m := m) hζ).range := by
  rw [MonoidHom.range_eq_map]
  refine isElemAbelian_map _ ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun a _ => ?_⟩
  exact TableBSymp.pow_card_eq_one_zmod a

theorem minusTorusGL_injective [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (minusTorusGL (K := K) (m := m) hζ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have ha' : TauCeti.diagGL (minusUnits fun i => TableBSymp.zmodPowHom hζ (a i)) =
      TauCeti.diagGL 1 := by
    rw [map_one]
    exact ha
  funext i
  exact (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp
    (congrFun (TauCeti.diagGL_injective ha') (Sum.inl i))

theorem card_range_minusTorusGL [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Nat.card (minusTorusGL (K := K) (m := m) hζ).range = p ^ m := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (minusTorusGL_injective hζ hζo)).toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem diagGL_minusUnits_commute (t : Fin m → Kˣ) (hζ : ζ ^ p = 1)
    (a : Fin m → Multiplicative (ZMod p)) :
    TauCeti.diagGL (minusUnits t) * minusTorusGL hζ a =
      minusTorusGL hζ a * TauCeti.diagGL (minusUnits t) := by
  rw [minusTorusGL_apply, ← map_mul, ← map_mul, mul_comm]

@[expose] def minusSwap : Equiv.Perm (Fin m ⊕ Fin m ⊕ Fin 2) where
  toFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim (fun k => .inl k) fun j => .inr (.inr j))
  invFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim (fun k => .inl k) fun j => .inr (.inr j))
  left_inv := by rintro (k | k | j) <;> rfl
  right_inv := by rintro (k | k | j) <;> rfl

theorem minusSwap_inv : (minusSwap (m := m))⁻¹ = minusSwap :=
  Equiv.ext fun _ => rfl

variable {n : ℕ} {b c : K}

theorem minusSwap_mem_orth :
    TauCeti.permutationGL (k := K) (minusSwap (m := n - 1)) ∈
      LargeEvenOrthGroup (StatedQuadMinus n K b c) :=
  TableBSymp.mem_orthGroup_of_isometry fun v => by
    rw [TableBSymp.permutationGL_mulVec, minusSwap_inv]
    simp only [StatedQuadMinus, Function.comp_apply]
    congr 3
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem diagGL_minusUnits_mem_orth (t : Fin (n - 1) → Kˣ) :
    TauCeti.diagGL (minusUnits t) ∈ LargeEvenOrthGroup (StatedQuadMinus n K b c) :=
  TableBSymp.mem_orthGroup_of_isometry fun v => by
    rw [TauCeti.diagGL_coe]
    simp only [StatedQuadMinus, Matrix.mulVec_diagonal, minusUnits, Sum.elim_inl, Sum.elim_inr,
      Pi.one_apply, Units.val_one, one_mul]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem minusTorusGL_mem_omega (hζ : ζ ^ p = 1) (hp : Odd p)
    (a : Fin (n - 1) → Multiplicative (ZMod p)) :
    minusTorusGL hζ a ∈ LargeEvenOmega (StatedQuadMinus n K b c) := by
  refine mem_commutator_of_conj_eq_inv hp (diagGL_minusUnits_mem_orth _) minusSwap_mem_orth
    (by rw [← map_pow, TableBSymp.pow_card_eq_one_zmod, map_one]) ?_
  rw [minusTorusGL_apply, TauCeti.mul_diagGL_of_coe_eq_permMatrix _ (minusSwap (m := n - 1))⁻¹
    (TauCeti.permutationGL_coe _), mul_inv_cancel_right, ← map_inv]
  congr 1
  funext x
  rcases x with x | x | x
  · rfl
  · change _ = ((TableBSymp.zmodPowHom hζ (a x))⁻¹)⁻¹
    rw [inv_inv]
    rfl
  · change (1 : Kˣ) = (1 : Kˣ)⁻¹
    rw [inv_one]

end Torus

section Split

open TableBOrth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n f : ℕ}

theorem exists_conj_mem_centralizer_split_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (minusDatum n hirr) .POmegaMinus n f ψ)
    (hp : p ∣ Nat.card K - 1) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (minusDatum n hirr) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have hp2 := hS.ne_two
  have hodd : Odd p := hS.prime.odd_of_ne_two hp2
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  set j := spinMatrix (quadMinus n K b c) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (StatedQuadMinus n K b c) :=
    range_spinMatrix_quadMinus hn hirr
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u, rfl⟩ := hin y hy
  have hup : u ^ p = 1 := hψ (by rw [map_pow, hyp, map_one])
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := p) hp
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
  obtain ⟨hA, hAj, hAc⟩ := transfer_range ψ hψ j hj hS.elem hBsψ
  have hBs : Nat.card Bs ≤ p ^ (n - 1) := by
    rw [← hAc]
    exact card_le_minus hp2 hζ hirr (by omega) (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  have hxO : j u ∈ LargeEvenOrthGroup (StatedQuadMinus n K b c) :=
    omega_le_orth _ (hjr ▸ ⟨u, rfl⟩)
  have hxp : j u ^ p = 1 := by rw [← map_pow, hup, map_one]
  obtain ⟨g, hgO, χ, hχ⟩ := exists_orth_conj_minus_le hp2 hζ hirr (by omega)
    (Subgroup.zpowers_le.mpr hxO) (isElemAbelian_zpowers hxp)
  have hgx := hχ ⟨j u, Subgroup.mem_zpowers _⟩
  set T := (minusTorusGL (K := K) (m := n - 1) hζp).range with hT
  set E := T.map (MulAut.conj g⁻¹).toMonoidHom with hE
  have hEel : IsElemAbelian p E := isElemAbelian_map _ (isElemAbelian_range_minusTorusGL hζp)
  have hEcard : Nat.card E = p ^ (n - 1) := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      card_range_minusTorusGL hζp hζ]
  have hEj : E ≤ j.range := by
    rw [hjr, hE, ← map_conj_omega (inv_mem hgO)]
    refine Subgroup.map_mono ?_
    rintro _ ⟨a, rfl⟩
    exact minusTorusGL_mem_omega hζp hodd a
  set D := TauCeti.diagGL (minusUnits fun k => χ k ⟨j u, Subgroup.mem_zpowers _⟩) with hD
  have hu' : j u = g⁻¹ * D * g := by
    rw [← hgx]
    group
  have hxE : ∀ z ∈ E, j u * z = z * j u := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hu']
    calc g⁻¹ * D * g * (g⁻¹ * minusTorusGL hζp a * g) =
        g⁻¹ * (D * minusTorusGL hζp a) * g := by group
      _ = g⁻¹ * (minusTorusGL hζp a * D) * g := by
        rw [hD, diagGL_minusUnits_commute]
      _ = g⁻¹ * minusTorusGL hζp a * g * (g⁻¹ * D * g) := by group
  obtain ⟨hE', hEG, hEc, hcomm⟩ := transfer_mat ψ hψ j hj hEel hEj hxE
  exact OrdPNS.exists_conj_mem_centralizer_of_card hS
    (hEG.trans (hrange.le.trans Subgroup.le_normalizer)) hE' (by rw [hEc, hEcard]; exact hBs)
    hcomm

end Split

end OrdPOm

section Family

theorem ggOrdPInnerConj_POmegaMinus_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hp y _ hyo hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨-, hf, hn⟩ := hadm
  exact OrdPOm.exists_conj_mem_centralizer_split_minus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hS (by rw [GaloisField.card 2 f (by omega)]; exact hp)
    (hyo ▸ pow_orderOf_eq_one y) hy

@[expose] def GGOrdPInnerConjPOmegaMinusNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .POmegaMinus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPInnerConjAt_POmegaMinus_of_nonsplit (h : GGOrdPInnerConjPOmegaMinusNonsplit) :
    GGOrdPInnerConjAt .POmegaMinus := by
  intro G _ _ p Bs G₀ n f ψ hS h24 _ y hyM hyo hy
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPInnerConj_POmegaMinus_split G p Bs G₀ n f ψ hS hpq y hyM hyo hy
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hy

end Family

end CFSG.StandardType
