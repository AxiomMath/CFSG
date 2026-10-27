module

public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData
import CFSG.RankThree.GF2n.Stroth80.Conj
import CFSG.RankThree.GF2n.Smith81.Sec1Model
import CFSG.GH74.GLS.IVK.L2.BorelField
public import CFSG.RankThree.GF2n.Stroth80.Ctx

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

section Weyl

private theorem diagElt_pow {F : Type} [Field F] (c : Fˣ) (m : ℕ) :
    Timmesfeld.ARS.NaturalModule.diagElt c ^ m =
      Timmesfeld.ARS.NaturalModule.diagElt (c ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Timmesfeld.ARS.NaturalModule.diagElt_one]
  | succ m ih => rw [pow_succ, pow_succ, ih, Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt]

private theorem ringAut_eq_one_of_iterate {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {a x₁ : K} (hx₁ : x₁ ≠ 0)
    (h : ∀ i : ℕ, (fun x => a * σ x)^[i] x₁ = x₁ ↔ Nat.card K - 1 ∣ i) :
    σ = 1 ∧ orderOf a = Nat.card K - 1 := by
  have ha : a ≠ 0 := by
    intro ha0
    have h0 : (fun x => a * σ x)^[Nat.card K - 1] x₁ = 0 := by
      rw [CFSG.GH74.GLS.IVK.L2Borel.iterate_semilinear]
      have hmem : (0 : ℕ) ∈ Finset.range (Nat.card K - 1) :=
        Finset.mem_range.mpr (by have := Finite.one_lt_card (α := K); omega)
      rw [Finset.prod_eq_zero hmem (by simp [ha0]), zero_mul]
    have hfix : (fun x => a * σ x)^[Nat.card K - 1] x₁ = x₁ :=
      (h (Nat.card K - 1)).mpr dvd_rfl
    exact hx₁ (h0.symm.trans hfix).symm
  have hσ : σ = 1 := by
    by_contra hne
    obtain ⟨m, hm0, hmlt, hm⟩ :=
      CFSG.GH74.GLS.IVK.L2Borel.exists_iterate_eq_id σ hne ha
    have hdvd : Nat.card K - 1 ∣ m := (h m).mp (hm x₁)
    have hle : Nat.card K - 1 ≤ m := Nat.le_of_dvd hm0 hdvd
    omega
  refine ⟨hσ, ?_⟩
  have hiter : ∀ i : ℕ, (fun x => a * σ x)^[i] x₁ = a ^ i * x₁ := by
    intro i
    rw [hσ]
    simpa using CFSG.GH74.GLS.IVK.L2Borel.iterate_mul_left a i x₁
  have hiff : ∀ i : ℕ, a ^ i = 1 ↔ Nat.card K - 1 ∣ i := by
    intro i
    rw [← h i, hiter i]
    constructor
    · intro hi
      rw [hi, one_mul]
    · intro hi
      exact mul_right_cancel₀ hx₁ (by rw [hi, one_mul])
  have hdvd₁ : orderOf a ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one ((hiff (Nat.card K - 1)).mpr dvd_rfl)
  have hdvd₂ : Nat.card K - 1 ∣ orderOf a :=
    (hiff (orderOf a)).mp (pow_orderOf_eq_one a)
  exact Nat.dvd_antisymm hdvd₁ hdvd₂

section Coordinates

variable {G : Type} [Group G]

private theorem toAdd_psi_mul {W : Subgroup G} {V : Type} [AddCommGroup V]
    (ψ : ↥W ≃* Multiplicative V) {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    Multiplicative.toAdd (ψ ⟨a * b, W.mul_mem ha hb⟩) =
      Multiplicative.toAdd (ψ ⟨a, ha⟩) + Multiplicative.toAdd (ψ ⟨b, hb⟩) := by
  have h : ψ ⟨a * b, W.mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ := by
    rw [← map_mul]
    rfl
  rw [h, toAdd_mul]

private theorem toAdd_psi_inv {W : Subgroup G} {V : Type} [AddCommGroup V]
    (ψ : ↥W ≃* Multiplicative V) {a : G} (ha : a ∈ W) :
    Multiplicative.toAdd (ψ ⟨a⁻¹, W.inv_mem ha⟩) = - Multiplicative.toAdd (ψ ⟨a, ha⟩) := by
  have h : ψ ⟨a⁻¹, W.inv_mem ha⟩ = (ψ ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h, toAdd_inv]

private theorem eq_of_toAdd_psi_eq {W : Subgroup G} {V : Type} [AddCommGroup V]
    (ψ : ↥W ≃* Multiplicative V) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (h : Multiplicative.toAdd (ψ ⟨a, ha⟩) = Multiplicative.toAdd (ψ ⟨b, hb⟩)) : a = b :=
  congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective h))

private theorem eq_one_of_toAdd_psi_eq_zero {W : Subgroup G} {V : Type} [AddCommGroup V]
    (ψ : ↥W ≃* Multiplicative V) {a : G} (ha : a ∈ W)
    (h : Multiplicative.toAdd (ψ ⟨a, ha⟩) = 0) : a = 1 := by
  have h1 : ψ ⟨a, ha⟩ = 1 := Multiplicative.toAdd.injective (by rw [h]; rfl)
  have h2 : (⟨a, ha⟩ : ↥W) = 1 := ψ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end Coordinates

variable {G : Type} [Group G] [Finite G] {M Q Z C : Subgroup G}

theorem exists_frame (hc : Ctx M Q Z C) :
    ∃ (n : ℕ) (φ : ↥(Q ⊔ QB C) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (ψ : ↥(Z ⊔ C) ≃* Multiplicative (Fin 2 → GaloisField 2 n)),
      2 ≤ n ∧ Nat.card Z = 2 ^ n ∧ Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer ((Z ⊔ C : Subgroup G) : Set G)).subgroupOf (Q ⊔ QB C) ∧
      IsPGroup 2 ↥((Q ⊔ QB C) ⊓ Subgroup.centralizer ((Z ⊔ C : Subgroup G) : Set G)) ∧
      Q ⊔ QB C ≤ Subgroup.normalizer ((Z ⊔ C : Subgroup G) : Set G) ∧
      (∀ (z : ↥(Q ⊔ QB C)) (w w' : ↥(Z ⊔ C)), (w' : G) = (z : G) * w * (z : G)⁻¹ →
        Multiplicative.toAdd (ψ w') =
          (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)) ∧
      (Q.subgroupOf (Q ⊔ QB C)).map φ = Timmesfeld.upperUnipotent (GaloisField 2 n) ∧
      ((QB C).subgroupOf (Q ⊔ QB C)).map φ = Timmesfeld.lowerUnipotent (GaloisField 2 n) ∧
      (∀ w : ↥(Z ⊔ C), (w : G) ∈ Z ↔ Multiplicative.toAdd (ψ w) 1 = 0) ∧
      (∀ w : ↥(Z ⊔ C), (w : G) ∈ C ↔ Multiplicative.toAdd (ψ w) 0 = 0) ∧
      ∀ (z : ↥(Q ⊔ QB C)) (μ : (GaloisField 2 n)ˣ),
        φ z = Timmesfeld.ARS.NaturalModule.diagElt μ →
          (z : G) ∈ M ∧ ∀ c ∈ C, (z : G) * c * (z : G)⁻¹ ∈ C := by
  classical
  obtain ⟨g, rfl⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := hc.le
  have H := hc.hyp.toHyp79
  rw [(Ctx.QB_eq hc rfl).2]
  obtain ⟨n, hn2, hZn, ⟨N⟩⟩ := Tim79.exists_natData H hgV hgQ
  have hn : n ≠ 0 := by omega
  have hC0 : ∀ w : ↥(Z ⊔ conjSubgroup g Z), (w : G) ∈ conjSubgroup g Z →
      Multiplicative.toAdd (N.ψ w) 0 = 0 := by
    intro w hw
    refine (Timmesfeld.ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff _).mp fun s => ?_
    have hl : Timmesfeld.RankOne.lowerElt (GaloisField 2 n) s ∈
        Timmesfeld.lowerUnipotent (GaloisField 2 n) :=
      (Timmesfeld.RankOne.mem_lowerUnipotent_iff _).mpr ⟨s, rfl⟩
    rw [← N.lower] at hl
    obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.mp hl
    have hzQ : (z : G) ∈ conjSubgroup g Q := Subgroup.mem_subgroupOf.mp hz
    have hcomm : (w : G) * z = z * w := H.conj_central g hw hzQ
    have h1 := N.compat z w w (by rw [← hcomm, mul_inv_cancel_right])
    rw [hzs] at h1
    exact h1.symm
  have hCψ : ∀ w : ↥(Z ⊔ conjSubgroup g Z), (w : G) ∈ conjSubgroup g Z ↔
      Multiplicative.toAdd (N.ψ w) 0 = 0 := by
    intro w
    refine ⟨hC0 w, fun hw0 => ?_⟩
    have hUW : conjSubgroup g Z ≤ Z ⊔ conjSubgroup g Z := le_sup_right
    let f : ↥(conjSubgroup g Z) → GaloisField 2 n := fun u =>
      Multiplicative.toAdd (N.ψ ⟨u, hUW u.2⟩) 1
    have hext : ∀ a b : ↥(Z ⊔ conjSubgroup g Z), Multiplicative.toAdd (N.ψ a) 0 = 0 →
        Multiplicative.toAdd (N.ψ b) 0 = 0 →
        Multiplicative.toAdd (N.ψ a) 1 = Multiplicative.toAdd (N.ψ b) 1 → a = b := by
      intro a b ha hb hab
      apply N.ψ.injective
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact ha.trans hb.symm
      · exact hab
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : ↥(Z ⊔ conjSubgroup g Z) => (x : G)) (hext ⟨a, hUW a.2⟩
        ⟨b, hUW b.2⟩ (hC0 _ a.2) (hC0 _ b.2) hab)
    have hcard : Nat.card (conjSubgroup g Z) = Nat.card (GaloisField 2 n) := by
      rw [card_conjSubgroup, hZn, GaloisField.card 2 n hn]
    obtain ⟨u, hu⟩ := (hf_inj.bijective_of_nat_card_le hcard.ge).2
      (Multiplicative.toAdd (N.ψ w) 1)
    have h1 : (⟨u, hUW u.2⟩ : ↥(Z ⊔ conjSubgroup g Z)) = w :=
      hext _ _ (hC0 _ u.2) hw0 hu
    rw [← h1]
    exact u.2
  refine ⟨n, N.φ, N.ψ, hn2, hZn, N.surj, N.ker, N.two, N.norm, N.compat, N.upper, N.lower,
    N.hV, hCψ, fun z μ hz => ?_⟩
  have hzW : ∀ w : ↥(Z ⊔ conjSubgroup g Z),
      ∃ hw' : (z : G) * w * (z : G)⁻¹ ∈ Z ⊔ conjSubgroup g Z,
        Multiplicative.toAdd (N.ψ ⟨_, hw'⟩) =
          ![(μ : GaloisField 2 n) * Multiplicative.toAdd (N.ψ w) 0,
            ((μ⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * Multiplicative.toAdd (N.ψ w) 1] := by
    intro w
    have hw' := (Subgroup.mem_normalizer_iff.mp (N.norm z.2) w).mp w.2
    refine ⟨hw', ?_⟩
    rw [N.compat z w ⟨_, hw'⟩ rfl, hz, Timmesfeld.ARS.NaturalModule.diagElt_mulVec]
  refine ⟨?_, fun c hc' => ?_⟩
  · rw [← hc.hyp.normalizer_Z.1]
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    obtain ⟨hw', hψ⟩ := hzW ⟨v, Subgroup.mem_sup_left hv⟩
    refine (N.hV ⟨_, hw'⟩).mpr ?_
    rw [hψ]
    simp [(N.hV ⟨v, Subgroup.mem_sup_left hv⟩).mp hv]
  · obtain ⟨hw', hψ⟩ := hzW ⟨c, Subgroup.mem_sup_right hc'⟩
    refine (hCψ ⟨_, hw'⟩).mpr ?_
    rw [hψ]
    simp [hC0 ⟨c, Subgroup.mem_sup_right hc'⟩ hc']

private theorem exists_torus_power {n : ℕ} (hn2 : 2 ≤ n)
    {φ : ↥(Q ⊔ QB C) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hφs : Function.Surjective φ)
    (hφker : φ.ker = (Subgroup.centralizer ((Z ⊔ C : Subgroup G) : Set G)).subgroupOf (Q ⊔ QB C))
    (hL2 : IsPGroup 2 ↥((Q ⊔ QB C) ⊓ Subgroup.centralizer ((Z ⊔ C : Subgroup G) : Set G)))
    (htor : ∀ (z : ↥(Q ⊔ QB C)) (μ : (GaloisField 2 n)ˣ),
      φ z = Timmesfeld.ARS.NaturalModule.diagElt μ →
        (z : G) ∈ M ∧ ∀ c ∈ C, (z : G) * c * (z : G)⁻¹ ∈ C) :
    ∃ (t : G) (htX : t ∈ Q ⊔ QB C) (μ : (GaloisField 2 n)ˣ),
      t ∈ M ∧ Odd (orderOf t) ∧ (∀ c ∈ C, t * c * t⁻¹ ∈ C) ∧
      φ ⟨t, htX⟩ = Timmesfeld.ARS.NaturalModule.diagElt μ ∧ orderOf μ = 2 ^ n - 1 := by
  classical
  have hn : n ≠ 0 := by omega
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 n)ˣ)
  rw [Nat.card_units, GaloisField.card 2 n hn] at hc₀
  obtain ⟨t₁, ht₁⟩ := hφs (Timmesfeld.ARS.NaturalModule.diagElt c₀)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (t₁ : G) ^ ((2 ^ n - 1) * 2 ^ j) = 1 := by
    have h1 : t₁ ^ (2 ^ n - 1) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ht₁, diagElt_pow, ← hc₀, pow_orderOf_eq_one,
        Timmesfeld.ARS.NaturalModule.diagElt_one]
    rw [hφker, Subgroup.mem_subgroupOf] at h1
    obtain ⟨j, hj⟩ := hL2 ⟨_, (t₁ ^ (2 ^ n - 1)).2, h1⟩
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    simpa [pow_mul] using this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 ^ j := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ↥(Q ⊔ QB C), t' = t₁ ^ k := ⟨_, rfl⟩
  have htt : (t' : G) = (t₁ : G) ^ k := by rw [ht', Subgroup.coe_pow]
  have ht'φ : φ t' = Timmesfeld.ARS.NaturalModule.diagElt (c₀ ^ k) := by
    rw [ht', map_pow, ht₁, diagElt_pow]
  obtain ⟨htM, htC⟩ := htor t' (c₀ ^ k) ht'φ
  have hμord : orderOf (c₀ ^ k) = 2 ^ n - 1 := by
    rw [← hc₀, hk]
    refine Nat.Coprime.orderOf_pow (Nat.Coprime.pow_right j ?_)
    rw [hc₀]
    exact Nat.coprime_two_right.mpr hodd
  have htodd : Odd (orderOf (t' : G)) := by
    have htq : (t' : G) ^ (2 ^ n - 1) = 1 := by
      have e : k * (2 ^ n - 1) = (2 ^ n - 1) * 2 ^ j := by rw [hk]; ring
      rw [htt, ← pow_mul, e, hj]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one htq)
  exact ⟨t', t'.2, c₀ ^ k, htM, htodd, htC, ht'φ, hμord⟩

private theorem exists_torus_orbit_z {n : ℕ}
    {ψ : ↥(Z ⊔ C) ≃* Multiplicative (Fin 2 → GaloisField 2 n)}
    {t x₀ c : G} (htM : t ∈ M) (hZnorm : M ≤ Subgroup.normalizer Z)
    (μ : (GaloisField 2 n)ˣ) (hμord : orderOf μ = 2 ^ n - 1)
    (htW : ∀ w ∈ Z ⊔ C, t * w * t⁻¹ ∈ Z ⊔ C)
    (hcommW : ∀ w ∈ Z ⊔ C, ⁅x₀, w⁆ ∈ Z ⊔ C)
    (htψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨t * w * t⁻¹, htW w hw⟩) =
        ![(μ : GaloisField 2 n) * Multiplicative.toAdd (ψ ⟨w, hw⟩) 0,
          ((μ⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) *
            Multiplicative.toAdd (ψ ⟨w, hw⟩) 1])
    (hcommψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨⁅x₀, w⁆, hcommW w hw⟩) =
        ![Multiplicative.toAdd (ψ ⟨w, hw⟩) 1, 0])
    (hcW : c ∈ Z ⊔ C) (hv1 : Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1 ≠ 0)
    (hz₁Z : ⁅x₀, c⁆ ∈ Z) :
    (∀ i : ℕ, t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹ ∈ Z) ∧
    (∀ i : ℕ, t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹ = ⁅x₀, c⁆ ↔ 2 ^ n - 1 ∣ i) := by
  have hpowZ : ∀ i : ℕ, t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹ ∈ Z := by
    intro i
    induction i with
    | zero => simpa using hz₁Z
    | succ i ih =>
      have e : t ^ (i + 1) * ⁅x₀, c⁆ * (t ^ (i + 1))⁻¹ =
          t * (t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹) * t⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hZnorm htM) _).mp ih
  have hz₁ψ : Multiplicative.toAdd (ψ ⟨⁅x₀, c⁆, hcommW c hcW⟩) =
      ![Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1, 0] := hcommψ c hcW
  have htpowψ : ∀ i : ℕ,
      Multiplicative.toAdd (ψ ⟨t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹,
        Subgroup.mem_sup_left (hpowZ i)⟩) =
      ![(μ : GaloisField 2 n) ^ i * Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1, 0] := by
    intro i
    induction i with
    | zero =>
      have e : (⟨t ^ 0 * ⁅x₀, c⁆ * (t ^ 0)⁻¹,
          Subgroup.mem_sup_left (hpowZ 0)⟩ : ↥(Z ⊔ C)) = ⟨⁅x₀, c⁆, hcommW c hcW⟩ :=
        Subtype.ext (by simp)
      rw [e, hz₁ψ]
      simp
    | succ i ih =>
      have hw : t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹ ∈ Z ⊔ C :=
        Subgroup.mem_sup_left (hpowZ i)
      have e : (⟨t ^ (i + 1) * ⁅x₀, c⁆ * (t ^ (i + 1))⁻¹,
          Subgroup.mem_sup_left (hpowZ (i + 1))⟩ : ↥(Z ⊔ C)) =
          ⟨t * (t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹) * t⁻¹, htW _ hw⟩ :=
        Subtype.ext (by group)
      rw [e, htψ _ hw, ih]
      funext m
      fin_cases m
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [pow_succ]
        ring
      · simp
  have hfixZ : ∀ i : ℕ, t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹ = ⁅x₀, c⁆ ↔ 2 ^ n - 1 ∣ i := by
    intro i
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (ψ ⟨t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹,
          Subgroup.mem_sup_left (hpowZ i)⟩) =
          Multiplicative.toAdd (ψ ⟨⁅x₀, c⁆, hcommW c hcW⟩) :=
        congrArg (fun w : ↥(Z ⊔ C) => Multiplicative.toAdd (ψ w)) (Subtype.ext h)
      rw [htpowψ i, hz₁ψ] at h1
      have h2 : (μ : GaloisField 2 n) ^ i * Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1 =
          Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1 := by
        simpa using congrFun h1 0
      have h3 : (μ : GaloisField 2 n) ^ i = 1 :=
        mul_right_cancel₀ hv1 (by rw [h2, one_mul])
      have h4 : μ ^ i = 1 := by
        apply Units.ext
        rwa [Units.val_pow_eq_pow_val, Units.val_one]
      have hdvd : orderOf μ ∣ i := orderOf_dvd_of_pow_eq_one h4
      exact hμord ▸ hdvd
    · intro h
      have h1 : μ ^ i = 1 := by
        have h' : orderOf μ ∣ i := hμord.symm ▸ h
        exact (orderOf_dvd_iff_pow_eq_one).mp h'
      have h2 : (μ : GaloisField 2 n) ^ i = 1 := by
        rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      have hcoord : Multiplicative.toAdd (ψ ⟨t ^ i * ⁅x₀, c⁆ * (t ^ i)⁻¹,
          Subgroup.mem_sup_left (hpowZ i)⟩) =
          Multiplicative.toAdd (ψ ⟨⁅x₀, c⁆, hcommW c hcW⟩) := by
        rw [htpowψ i, hz₁ψ, h2]
        simp
      exact eq_of_toAdd_psi_eq ψ (Subgroup.mem_sup_left (hpowZ i)) (hcommW c hcW) hcoord
  exact ⟨hpowZ, hfixZ⟩

private theorem exists_torus_semilinear {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (gm : GlobalModelData M Q Z γ M₀) {t z₁ : G} (htM : t ∈ M) {n : ℕ}
    (hKcard : Nat.card K = 2 ^ n)
    (hpowZ : ∀ i : ℕ, t ^ i * z₁ * (t ^ i)⁻¹ ∈ Z)
    (hfixZ : ∀ i : ℕ, t ^ i * z₁ * (t ^ i)⁻¹ = z₁ ↔ 2 ^ n - 1 ∣ i)
    (hγz₁ : γ z₁ ≠ 0) :
    ∃ (σ : K ≃+* K) (a : Kˣ) (T : M₀.E ≃+ M₀.E),
      (∀ (c : K) (e : M₀.E), T (c • e) = σ c • T e) ∧
      (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) ∧
      (∀ z ∈ Z, γ (t * z * t⁻¹) = (a : K) * σ (γ z)) ∧
      (∀ e, M₀.Qf (T e) = (a : K) * σ (M₀.Qf e)) ∧
      σ = 1 ∧ orderOf (a : K) = Nat.card K - 1 := by
  obtain ⟨σ, a, T, hTσ, hTπ, hTγ, hTQ⟩ := gm.act t htM
  have hz₁Z : z₁ ∈ Z := by simpa using hpowZ 0
  have hfixZK : ∀ i : ℕ, t ^ i * z₁ * (t ^ i)⁻¹ = z₁ ↔ Nat.card K - 1 ∣ i := by
    intro i
    rw [hKcard]
    exact hfixZ i
  have horbit : ∀ i : ℕ, γ (t ^ i * z₁ * (t ^ i)⁻¹) =
      (fun x => (a : K) * σ x)^[i] (γ z₁) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : t ^ (i + 1) * z₁ * (t ^ (i + 1))⁻¹ =
          t * (t ^ i * z₁ * (t ^ i)⁻¹) * t⁻¹ := by group
      rw [e, hTγ _ (hpowZ i), ih]
      exact (Function.iterate_succ_apply' (f := fun x => (a : K) * σ x) i (γ z₁)).symm
  have hfixγ : ∀ i : ℕ, (fun x => (a : K) * σ x)^[i] (γ z₁) = γ z₁ ↔
      Nat.card K - 1 ∣ i := by
    intro i
    rw [← horbit i]
    constructor
    · intro h
      exact (hfixZK i).mp (GM.eq_of_γ_eq gm (hpowZ i) hz₁Z h)
    · intro h
      rw [(hfixZK i).mpr h]
  obtain ⟨hσ, haord⟩ := ringAut_eq_one_of_iterate σ hγz₁ (fun i => hfixγ i)
  exact ⟨σ, a, T, hTσ, hTπ, hTγ, hTQ, hσ, haord⟩

private theorem exists_torus_linear {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (gm : GlobalModelData M Q Z γ M₀) (hc : Ctx M Q Z C)
    {n : ℕ} {ψ : ↥(Z ⊔ C) ≃* Multiplicative (Fin 2 → GaloisField 2 n)}
    {t x₀ c : G} (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (hcC : c ∈ C) (hx₀Q : x₀ ∈ Q) (hγz₁ : γ ⁅x₀, c⁆ ≠ 0)
    (μ : (GaloisField 2 n)ˣ) (hcW : c ∈ Z ⊔ C)
    (hcommW : ∀ w ∈ Z ⊔ C, ⁅x₀, w⁆ ∈ Z ⊔ C)
    (hcommψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨⁅x₀, w⁆, hcommW w hw⟩) =
        ![Multiplicative.toAdd (ψ ⟨w, hw⟩) 1, 0])
    (htW : ∀ w ∈ Z ⊔ C, t * w * t⁻¹ ∈ Z ⊔ C)
    (htψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨t * w * t⁻¹, htW w hw⟩) =
        ![(μ : GaloisField 2 n) * Multiplicative.toAdd (ψ ⟨w, hw⟩) 0,
          ((μ⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) *
            Multiplicative.toAdd (ψ ⟨w, hw⟩) 1])
    (hz₁ψ : Multiplicative.toAdd (ψ ⟨⁅x₀, c⁆, hcommW c hcW⟩) =
      ![Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1, 0])
    (T' : M₀.E ≃+ M₀.E) (σ : K ≃+* K) (a : Kˣ)
    (hT'σ : ∀ (c : K) (e : M₀.E), T' (c • e) = σ c • T' e)
    (hT'π : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T' (M₀.π x))
    (hT'γ : ∀ z ∈ Z, γ (t * z * t⁻¹) = (a : K) * σ (γ z))
    (hT'Q : ∀ e, M₀.Qf (T' e) = (a : K) * σ (M₀.Qf e))
    (hσ : σ = 1) :
    ∃ (T : M₀.E ≃ₗ[K] M₀.E) (ℓ : K),
      (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = (a : K) * M₀.Qf e) ∧
      (∀ z ∈ Z, γ (t * z * t⁻¹) = (a : K) * γ z) ∧
      (∀ c ∈ C, M₀.π (t * c * t⁻¹) = ℓ • M₀.π c) ∧ (a : K) * ℓ = 1 := by
  have hCQ : C ≤ Q := hc.le
  let T : M₀.E ≃ₗ[K] M₀.E := T'.toLinearEquiv fun c e => by
    rw [hT'σ, hσ]
    simp
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨b, hb0, hb⟩ := gm.line g (hg ▸ hc.ne) (hg ▸ hc.le)
  rw [← hg] at hb
  obtain ⟨c₁, hc₁C, hc₁Q, hc₁b⟩ :=
    (Tim79.QuadModel.mem_img M₀).mp ((hb b).mpr ⟨1, (one_smul K b).symm⟩)
  have hTbC : T b ∈ M₀.img C :=
    (Tim79.QuadModel.mem_img M₀).mpr ⟨t * c₁ * t⁻¹, htC c₁ hc₁C,
      hCQ (htC c₁ hc₁C), by rw [hT'π c₁ hc₁Q, hc₁b]; rfl⟩
  obtain ⟨ℓ, hℓ⟩ := (hb (T b)).mp hTbC
  have hℓC : ∀ c ∈ C, M₀.π (t * c * t⁻¹) = ℓ • M₀.π c := by
    intro c hc'
    obtain ⟨s, hs⟩ := (hb (M₀.π c)).mp (Tim79.QuadModel.pi_mem_img M₀ hc' (hCQ hc'))
    have h1 : M₀.π (t * c * t⁻¹) = T (M₀.π c) := hT'π c (hCQ hc')
    rw [h1, hs, map_smul, hℓ, smul_comm]
  have hc'C : t * c * t⁻¹ ∈ C := htC c hcC
  have hz₂ψ := hcommψ _ (htW c hcW)
  rw [htψ c hcW] at hz₂ψ
  have hz₂z₁ : t * ⁅x₀, t * c * t⁻¹⁆ * t⁻¹ = ⁅x₀, c⁆ := by
    refine eq_of_toAdd_psi_eq ψ (htW _ (hcommW _ (htW c hcW))) (hcommW c hcW) ?_
    rw [htψ _ (hcommW _ (htW c hcW)), hz₂ψ, hz₁ψ]
    funext i
    fin_cases i <;> simp
  have hz₂Z : ⁅x₀, t * c * t⁻¹⁆ ∈ Z := M₀.comm_mem x₀ hx₀Q _ (hCQ hc'C)
  have hγz₂ : γ ⁅x₀, t * c * t⁻¹⁆ = ℓ * γ ⁅x₀, c⁆ := by
    rw [M₀.comm_eq x₀ hx₀Q _ (hCQ hc'C), M₀.comm_eq x₀ hx₀Q c (hCQ hcC), hℓC c hcC,
      map_smul, smul_eq_mul]
  have hγz₁' : γ ⁅x₀, c⁆ = (a : K) * γ ⁅x₀, t * c * t⁻¹⁆ := by
    rw [← hz₂z₁, hT'γ _ hz₂Z, hσ]
    simp
  have haℓ : (a : K) * ℓ = 1 := by
    have h1 : ((a : K) * ℓ - 1) * γ ⁅x₀, c⁆ = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← hγz₂, ← hγz₁', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hγz₁
  refine ⟨T, ℓ, fun x hx => hT'π x hx, ?_, ?_, hℓC, haℓ⟩
  · intro e
    show M₀.Qf (T' e) = _
    rw [hT'Q, hσ]
    simp
  · intro z hz
    rw [hT'γ z hz, hσ]
    simp

theorem exists_torus_full {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (gm : GlobalModelData M Q Z γ M₀) (hc : Ctx M Q Z C) :
    ∃ (t : G) (T : M₀.E ≃ₗ[K] M₀.E) (a ℓ : K),
      t ∈ M ∧ t ∈ Q ⊔ QB C ∧ Odd (orderOf t) ∧ (∀ c ∈ C, t * c * t⁻¹ ∈ C) ∧
      orderOf a = Nat.card K - 1 ∧
      (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = a * M₀.Qf e) ∧ (∀ z ∈ Z, γ (t * z * t⁻¹) = a * γ z) ∧
      (∀ c ∈ C, M₀.π (t * c * t⁻¹) = ℓ • M₀.π c) ∧ a * ℓ = 1 := by
  obtain ⟨n, φ, ψ, hn2, hZn, hφs, hφker, hL2, hXW, hcompat, hφQ, -, -, hCψ, htor⟩ :=
    exists_frame hc
  obtain ⟨t, htX, μ, htM, htodd, htC, htφ, hμord⟩ :=
    exists_torus_power (n := n) hn2 hφs hφker hL2 htor
  obtain ⟨c, hcC, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
    have hCne : C ≠ ⊥ := by
      intro hbot
      obtain ⟨g, hg⟩ := hc.conj
      have h1 : Nat.card C = Nat.card Z := by rw [hg, card_conjSubgroup]
      rw [hbot, Subgroup.card_bot] at h1
      have := hc.hyp.q4
      omega
    obtain ⟨⟨c, hc'⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hCne
    exact ⟨c, hc', fun h => hc1 (Subtype.ext h)⟩
  obtain ⟨x₀, hx₀Q, hx₀⟩ : ∃ (x₀ : G) (hx : x₀ ∈ Q),
      φ ⟨x₀, Subgroup.mem_sup_left hx⟩ = Timmesfeld.RankOne.upperElt (GaloisField 2 n) 1 := by
    have h : Timmesfeld.RankOne.upperElt (GaloisField 2 n) 1 ∈
        (Q.subgroupOf (Q ⊔ QB C)).map φ := by
      rw [hφQ]
      exact (Timmesfeld.RankOne.mem_upperUnipotent_iff _).mpr ⟨1, rfl⟩
    obtain ⟨z, hz, hz1⟩ := Subgroup.mem_map.mp h
    exact ⟨z, Subgroup.mem_subgroupOf.mp hz, hz1⟩
  have hx₀W : ∀ w ∈ Z ⊔ C, x₀ * w * x₀⁻¹ ∈ Z ⊔ C := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hXW (Subgroup.mem_sup_left hx₀Q)) w).mp hw
  have hcommW : ∀ w ∈ Z ⊔ C, ⁅x₀, w⁆ ∈ Z ⊔ C := fun w hw => by
    rw [commutatorElement_def]
    exact mul_mem (hx₀W w hw) (inv_mem hw)
  have hcommψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨⁅x₀, w⁆, hcommW w hw⟩) =
        ![Multiplicative.toAdd (ψ ⟨w, hw⟩) 1, 0] := by
    intro w hw
    have e : (⟨⁅x₀, w⁆, hcommW w hw⟩ : ↥(Z ⊔ C)) =
        ⟨x₀ * w * x₀⁻¹ * w⁻¹, (Z ⊔ C).mul_mem (hx₀W w hw) ((Z ⊔ C).inv_mem hw)⟩ :=
      Subtype.ext (commutatorElement_def x₀ w)
    rw [e, toAdd_psi_mul ψ (hx₀W w hw) ((Z ⊔ C).inv_mem hw), toAdd_psi_inv ψ hw,
      hcompat ⟨x₀, Subgroup.mem_sup_left hx₀Q⟩ ⟨w, hw⟩ ⟨_, hx₀W w hw⟩ rfl, hx₀,
      ← sub_eq_add_neg, Timmesfeld.ARS.NaturalModule.upperElt_mulVec_sub, one_mul]
  have htW : ∀ w ∈ Z ⊔ C, t * w * t⁻¹ ∈ Z ⊔ C := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hXW htX) w).mp hw
  have htψ : ∀ w (hw : w ∈ Z ⊔ C),
      Multiplicative.toAdd (ψ ⟨t * w * t⁻¹, htW w hw⟩) =
        ![(μ : GaloisField 2 n) * Multiplicative.toAdd (ψ ⟨w, hw⟩) 0,
          ((μ⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) *
            Multiplicative.toAdd (ψ ⟨w, hw⟩) 1] := by
    intro w hw; rw [hcompat ⟨t, htX⟩ ⟨w, hw⟩ ⟨_, htW w hw⟩ rfl, htφ,
      Timmesfeld.ARS.NaturalModule.diagElt_mulVec]
  have hcW : c ∈ Z ⊔ C := Subgroup.mem_sup_right hcC
  have hv1 : Multiplicative.toAdd (ψ ⟨c, hcW⟩) 1 ≠ 0 := by
    intro h1; apply hc1
    refine eq_one_of_toAdd_psi_eq_zero ψ hcW ?_
    funext i
    fin_cases i
    · exact (hCψ ⟨c, hcW⟩).mp hcC
    · exact h1
  have hz₁ψ := hcommψ c hcW
  have hz₁Z : ⁅x₀, c⁆ ∈ Z := M₀.comm_mem x₀ hx₀Q c (hc.le hcC)
  have hz₁1 : ⁅x₀, c⁆ ≠ 1 := by
    intro h1
    have h2 : Multiplicative.toAdd (ψ ⟨⁅x₀, c⁆, hcommW c hcW⟩) = 0 := by
      rw [show (⟨⁅x₀, c⁆, hcommW c hcW⟩ : ↥(Z ⊔ C)) = 1 from Subtype.ext h1,
        map_one, toAdd_one]
    rw [hz₁ψ] at h2; exact hv1 (congrFun h2 0)
  have hγz₁ : γ ⁅x₀, c⁆ ≠ 0 := fun h0 => hz₁1 (gm.reg.inj _ hz₁Z h0)
  obtain ⟨hpowZ, hfixZ⟩ :=
    exists_torus_orbit_z (Z := Z) (C := C) (ψ := ψ) htM hc.hyp.Z_normal.2 μ hμord htW
      hcommW htψ hcommψ hcW hv1 hz₁Z
  obtain ⟨σ, a, T', hT'σ, hT'π, hT'γ, hT'Q, hσ, haord⟩ :=
    exists_torus_semilinear (Q := Q) (Z := Z) gm htM (gm.card.trans hZn) hpowZ hfixZ hγz₁
  obtain ⟨T, ℓ, hTπ, hTQ, hTγ, hTℓ, haℓ⟩ :=
    exists_torus_linear (M := M) (Q := Q) (Z := Z) (C := C) gm hc (ψ := ψ) htC hcC hx₀Q
      hγz₁ μ hcW hcommW hcommψ htW htψ hz₁ψ T' σ a hT'σ hT'π hT'γ hT'Q hσ
  exact ⟨t, T, (a : K), ℓ, htM, htX, htodd, htC, haord, hTπ, hTQ, hTγ, hTℓ, haℓ⟩

end Weyl

end CFSG.RankThree.GF2n.Smith81
