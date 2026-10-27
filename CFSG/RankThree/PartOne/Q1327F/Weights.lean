module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.Q1327T.R8Weir
import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.Q1327T.R8Core
public import CFSG.RankThree.PartOne.Q1327T.R8Lift
public import CFSG.RankThree.PartOne.Q1327T.R8Weights

public section

namespace CFSG.RankThree.PartOne.Q1327F

open Matrix Module CFSG CFSG.GroupTheory.WeirSylow CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.Q1327T CFSG.RankThree.PartOne.Q1327T.R8

section Weights

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_weight_set' {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {f : ℕ} (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (E : Subgroup (GL ι K)) [hE : IsElementaryAbelian p E]
    (β : MulAut E) (hβW : β ∈ E.normalizerMonoidHom.range) (hβ : orderOf β = 3)
    (hfpf : ∀ x : E, β x = x → x = 1) :
    ∃ (X : Finset (E →* rootsOfUnity p (AlgebraicClosure K))) (c : (ZMod p)ˣ),
      (c : ZMod p) = ((ℓ ^ f : ℕ) : ZMod p) ∧ (∀ χ ∈ X, χ ≠ 1) ∧
      (∀ e : E, (∀ χ ∈ X, χ e = 1) → e = 1) ∧ X.card ≤ Fintype.card ι ∧ 3 ∣ X.card ∧
      (∀ χ ∈ X, chPow p (c : ZMod p) χ ∈ X) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpK : (p : K) ≠ 0 := fun h0 => hpℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).1
    ((CharP.cast_eq_zero_iff K ℓ p).1 h0)).symm
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := fun h0 =>
    hpK ((algebraMap K L).injective (by rw [map_natCast, map_zero]; exact h0))
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  have : Fintype (Wts L E) := Fintype.ofFinite _
  have : CharP L ℓ := inferInstance
  let σ : L →+* L := iterateFrobenius L ℓ f
  have hσpow : ∀ x : L, σ x = x ^ (ℓ ^ f) := fun x => rfl
  have hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x := by
    intro x
    rw [hσpow, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    have := FiniteField.pow_card x
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hqne : ((ℓ ^ f : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff (ℓ ^ f) p).1 h0
    have h2 : p ∣ ℓ := hp.dvd_of_dvd_pow this
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).1 h2)
  set X : Finset (E →* rootsOfUnity p L) :=
    (Finset.univ.filter fun w : Wts L E => wtRoots hexp w ≠ 1).image (wtRoots hexp) with hX
  have hXmem : ∀ χ, χ ∈ X ↔ ∃ w : Wts L E, wtRoots hexp w = χ ∧ χ ≠ 1 := by
    intro χ
    rw [hX, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, rfl, (Finset.mem_filter.1 hw).2⟩
    · rintro ⟨w, rfl, h1⟩
      exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, rfl⟩
  have hX1 : ∀ χ ∈ X, χ ≠ 1 := fun χ hχ => ((hXmem χ).1 hχ).choose_spec.2
  refine ⟨X, Units.mk0 _ hqne, rfl, hX1, ?_, ?_, ?_, ?_⟩
  · intro e he
    refine eq_of_forall_weight_eq L E hpL hexp hcomm (a := e) (b := 1) fun χ hχ => ?_
    rw [weight_one L E hχ]
    by_cases h1 : wtRoots hexp ⟨χ, hχ⟩ = 1
    · exact (wtRoots_eq_one_iff hexp ⟨χ, hχ⟩).1 h1 e
    · have hmem : wtRoots hexp ⟨χ, hχ⟩ ∈ X := (hXmem _).2 ⟨⟨χ, hχ⟩, rfl, h1⟩
      have := he _ hmem
      have h2 := congrArg (fun z : rootsOfUnity p L => ((z : Lˣ) : L)) this
      simpa [wtRoots_apply] using h2
  · calc X.card ≤ (Finset.univ.filter fun w : Wts L E => wtRoots hexp w ≠ 1).card :=
          Finset.card_image_le
      _ ≤ Fintype.card (Wts L E) := Finset.card_filter_le _ _
      _ ≤ Fintype.card ι := by
          rw [← Nat.card_eq_fintype_card]
          exact hcard
  ·
    have hβi : orderOf β⁻¹ = 3 := by rwa [orderOf_inv]
    have hfpf' : ∀ x : E, β⁻¹ x = x → x = 1 := fun x hx => hfpf x (by
      have := congrArg (⇑β) hx
      simpa using this.symm)
    refine three_dvd_card_of_fixedFree (fun a b => Subtype.ext (hcomm a b)) β⁻¹ hβi hfpf' X hX1 ?_
    intro χ hχ
    obtain ⟨w, rfl, h1⟩ := (hXmem χ).1 hχ
    refine (hXmem _).2 ⟨weightAction (L := L) ⟨β, hβW⟩ w, ?_, ?_⟩
    · ext e
      rfl
    · intro h0
      apply h1
      ext e
      have := DFunLike.congr_fun h0 (β e)
      simpa using this
  ·
    intro χ hχ
    obtain ⟨w, rfl, h1⟩ := (hXmem χ).1 hχ
    refine (hXmem _).2 ⟨frobWt σ hσ w, ?_, ?_⟩
    · ext e
      have h2 : (w.1 e) ^ ((ℓ ^ f : ℕ) : ZMod p).val = (w.1 e) ^ (ℓ ^ f) := by
        rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (weight_pow_eq_one L E hexp w.2 e)]
      simp only [chPow_apply, Units.val_mk0]
      rw [wtRoots_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, wtRoots_apply, frobWt_apply,
        hσpow]
      exact h2.symm
    · intro h0
      apply h1
      have hμ : ∀ z : rootsOfUnity p L, z ^ p = 1 := fun z =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact (mem_rootsOfUnity p (z : Lˣ)).1 z.2)
      have h3 := congrArg (chPow p (((Units.mk0 _ hqne)⁻¹ : (ZMod p)ˣ) : ZMod p)) h0
      rw [← chPow_mul hμ, ← Units.val_mul, inv_mul_cancel, Units.val_one, chPow_one] at h3
      rw [h3]
      ext e
      simp [chPow_apply]

theorem row8_weight_numbers' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {f : ℕ} (hK : Nat.card K = ℓ ^ f)
    (M : Subgroup (GL ι K)) {Q : Type} [Group Q]
    (e : Q ≃* StatedProj M) {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (hp5 : 5 ≤ p) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hpd : ¬ p ∣ d) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē)
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) :
    ∃ (m : ℕ) (u : (ZMod p)ˣ), (u : ZMod p) = ((ℓ ^ f : ℕ) : ZMod p) ∧ 0 < m ∧
      m ≤ Fintype.card ι ∧ 3 ∣ m ∧ orderOf u ∣ m := by
  classical
  have hp := (Fact.out : p.Prime)
  have : Finite Q := Finite.of_equiv (StatedProj M) e.symm.toEquiv
  obtain ⟨F, eF, hFel, hFM, hFmax, hle⟩ := exists_lifted_conf M e hd hpd hE hmax
  obtain ⟨φ⟩ := hW
  let W : Subgroup (MulAut Ē) := Ē.normalizerMonoidHom.range
  have hWeq : torusImage Ē ⊤ = W := torusImage_top_eq_range Ē
  let φ' : W ≃* Equiv.Perm (Fin 3) := (MulEquiv.subgroupCongr hWeq.symm).trans φ
  have : IsElementaryAbelian p Ē := hE
  obtain ⟨β₀, hβ₀W, hβ₀ord, hβ₀fpf⟩ := exists_order_three_fixedFree hp5 hcard W φ'
  let β : MulAut F := MulAut.congr eF.symm β₀
  have hβrange : β ∈ F.normalizerMonoidHom.range := hle β₀ hβ₀W
  have hβord : orderOf β = 3 := by
    rw [MulEquiv.orderOf_eq, hβ₀ord]
  have hβfpf : ∀ x : F, β x = x → x = 1 := by
    intro x hx
    have h1 : eF.symm (β₀ (eF x)) = x := hx
    have h2 : β₀ (eF x) = eF x := by
      have := congrArg eF h1
      simpa using this
    have := hβ₀fpf _ h2
    simpa using this
  have : IsElementaryAbelian p F := hFel
  obtain ⟨X, c, hc, hX1, hXsep, hXn, hX3, hXc⟩ :=
    exists_weight_set' hK hpℓ F β hβrange hβord hβfpf
  have hμ : ∀ z : rootsOfUnity p (AlgebraicClosure K), z ^ p = 1 := fun z =>
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact (mem_rootsOfUnity p (z : (AlgebraicClosure K)ˣ)).1 z.2)
  have hodvd : orderOf c ∣ X.card := orderOf_dvd_card_of_stable hμ X hX1 c hXc
  have hXpos : 0 < X.card := by
    rw [Finset.card_pos]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ x : F, x = 1 := fun x => hXsep x (by simp [hne])
    have : Nat.card F = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card F = p ^ 2 := by rw [Nat.card_congr eF.toEquiv, hcard]
    have : p ^ 2 = 1 := by rw [← h2, this]
    have := hp.two_le
    nlinarith
  exact ⟨X.card, c, hc, hXpos, hXn, hX3, hodvd⟩

theorem false_of_plane_sl4' {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpK0 : ¬ p ∣ Nat.card K) (F : Subgroup (GL (Fin 4) K))
    (hFM : F ≤ StatedSL 4 K) [IsElementaryAbelian p F] (hFc : Nat.card F = p ^ 2)
    (hmax : ∀ D : Subgroup (GL (Fin 4) K), D ≤ StatedSL 4 K → IsElementaryAbelian p D →
      F ≤ D → D ≤ Subgroup.centralizer (F : Set (GL (Fin 4) K)) → Nat.card D ≤ Nat.card F)
    (he2 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 2) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp1 : Odd p := hp.odd_of_ne_two (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hpK : ¬ p ∣ Fintype.card K := by rwa [Fintype.card_eq_nat_card]
  refine false_of_homocyclic_sylow (F := F) (r := 1) hFc (fun D hD hFD hDc => ?_) (fun S => ?_)
  ·
    let φ : D →* Kˣ := (Matrix.GeneralLinearGroup.det).comp D.subtype
    have hdet1 : ∀ x : GL (Fin 4) K, x ∈ StatedSL 4 K →
        Matrix.GeneralLinearGroup.det x = 1 := fun x hx =>
      Units.ext (N143X.det_eq_one_of_mem_statedSL' hx)
    let D' : Subgroup (GL (Fin 4) K) := φ.ker.map D.subtype
    have hD'D : D' ≤ D := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hD'SL : D' ≤ StatedSL 4 K := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.subset_closure ?_
      have h1 : Matrix.GeneralLinearGroup.det (y : GL (Fin 4) K) = 1 := hy
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using h2
    have hFD' : F ≤ D' := fun x hx =>
      ⟨⟨x, hFD hx⟩, hdet1 x (hFM hx), rfl⟩
    have hD'el : IsElementaryAbelian p D' := CFSG.IsElementaryAbelian.of_le hD hD'D
    have hD'c : D' ≤ Subgroup.centralizer (F : Set (GL (Fin 4) K)) := hD'D.trans hDc
    have h1 : Nat.card D' ≤ p ^ 2 := by
      have := hmax D' hD'SL hD'el hFD' hD'c
      rwa [hFc] at this
    have hD'card : Nat.card D' = Nat.card φ.ker :=
      Subgroup.card_map_of_injective D.subtype_injective
    have hrange : Nat.card φ.range ≤ p := by
      have hel : IsElementaryAbelian p φ.range := by
        refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩
                 exponent_dvd_p := ?_ }
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun y => ?_
        obtain ⟨d, hd⟩ := y.2
        apply Subtype.ext
        change (y : Kˣ) ^ p = 1
        rw [← hd, ← map_pow]
        have : d ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := D) _ d.2)
        rw [this, map_one]
      have hexp : Monoid.exponent ↥φ.range ∣ p := IsElementaryAbelian.exponent_dvd_p p _
      rw [IsCyclic.exponent_eq_card] at hexp
      exact Nat.le_of_dvd hp.pos hexp
    have h2 : Nat.card D = Nat.card φ.ker * Nat.card φ.range := by
      rw [← Subgroup.index_ker φ]
      exact (Subgroup.card_mul_index φ.ker).symm
    calc Nat.card D = Nat.card φ.ker * Nat.card φ.range := h2
      _ ≤ p ^ 2 * p := by
          rw [← hD'card]
          exact Nat.mul_le_mul h1 hrange
      _ = p ^ (1 + 2) := by ring
  · obtain ⟨φ⟩ := sylow_GL hp1 K hpK 4 S
    have he : 0 < weirE p K := weirE_pos hpK
    have ha : 1 ≤ weirA p K := one_le_weirA hpK
    have he2' : weirE p K ≠ 2 := by
      have : weirE p K = orderOf ((Nat.card K : ℕ) : ZMod p) := by
        rw [weirE, Nat.card_eq_fintype_card]
      rw [this]
      exact he2
    obtain ⟨hle4, hcases⟩ := gl4_rank_cases he he2'
    refine ⟨4 / weirE p K, weirA p K, ha, ?_, hcases⟩
    obtain ⟨ψ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := p) (e := weirE p K) (a := weirA p K)
      (N := 4) (by omega)
    exact ⟨φ.trans ψ⟩

end Weights

end CFSG.RankThree.PartOne.Q1327F
