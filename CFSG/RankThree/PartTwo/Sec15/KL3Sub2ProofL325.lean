module

public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofSeven
public import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofL325
public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.RankThree.PartTwo.Sec15

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

@[expose] def KL325Quasi : Prop :=
  ∀ G H : Subgroup (GL (Fin 3) (GaloisField 5 2)), H ≤ G →
    (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) → CFSG.IsQuasisimple H →
    IsIrreducibleMatrixRep H.subtype →
    (∀ M : Matrix (Fin 3) (Fin 3) (GaloisField 5 2),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)) * M = M * x) →
        ∃ c : GaloisField 5 2, M = Matrix.scalar (Fin 3) c) →
    (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1) →
    Nat.card (Subgroup.center H) ∣ 3 →
    (∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1) →
    20160 ∣ Nat.card G →
    ∀ g : GL (Fin 3) (GaloisField 5 2), (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1 →
      g ∈ G

namespace KL3Sub2Proof

variable {K : Type} [Field K] [Finite K]

theorem false_of_cyclic (hK : Nat.card K = 25) {G C : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ g ∈ G, ∀ x ∈ C, g * x * g⁻¹ ∈ C) (hirr : IsIrreducibleMatrixRep C.subtype)
    (hcyc : IsCyclic C) {y : GL (Fin 3) K} (hyG : y ∈ G) (hy : orderOf y = 5) : False := by
  classical
  have hC' : IsIrreducibleOn C := isIrreducibleOn_iff.mpr hirr
  let := commutantField hC'
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    have := hcyc.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hCF : ∀ c ∈ C, (c : Matrix (Fin 3) (Fin 3) K) ∈ commutant C := by
    intro c hc
    rw [mem_commutant]
    intro g hg
    rw [← Units.val_mul, ← Units.val_mul, hcomm g hg c hc]
  have hdvd := finrank_commutant_dvd hC'
  rw [Fintype.card_fin] at hdvd
  have hrank : Module.finrank K (commutant C) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hbot : commutant C = ⊥ := Subalgebra.finrank_eq_one_iff.mp h1
      apply not_irreducible_of_forall_scalar (by norm_num) _ hirr
      intro g hg
      have := hCF g hg
      rw [hbot, Algebra.mem_bot] at this
      obtain ⟨a, ha⟩ := this
      exact ⟨a, by rw [← ha, Matrix.algebraMap_eq_diagonal]; rfl⟩
    · exact h3
  have hcardF : Nat.card (commutant C) = 5 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := commutant C), hK, hrank]
    norm_num
  have hyinv : y⁻¹ ∈ G := G.inv_mem hyG
  have hconjmem : ∀ (g : GL (Fin 3) K), g ∈ G → ∀ M ∈ commutant C,
      (g : Matrix (Fin 3) (Fin 3) K) * M * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈
        commutant C := by
    intro g hg M hM
    rw [mem_commutant] at hM ⊢
    intro c hc
    have hc' : g⁻¹ * c * g ∈ C := by
      have := hnorm g⁻¹ (G.inv_mem hg) c hc
      rwa [inv_inv] at this
    have h1 := hM _ hc'
    have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hgg' : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    set c' : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ * c * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) with hc'def
    have hcg : (c : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) * c' *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hc'def]
      simp only [Units.val_mul, Matrix.mul_assoc]
      rw [hgg', Matrix.mul_one, ← Matrix.mul_assoc, hgg', Matrix.one_mul]
    calc (c : Matrix (Fin 3) (Fin 3) K) * (g * M * ((g⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K))
        = (g : Matrix (Fin 3) (Fin 3) K) * (c' * M) *
            ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hcg]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            (g : Matrix (Fin 3) (Fin 3) K), hgg, Matrix.one_mul]
      _ = (g : Matrix (Fin 3) (Fin 3) K) * (M * c') *
            ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
      _ = (g * M * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            ((g : Matrix (Fin 3) (Fin 3) K) * c' *
              ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            (g : Matrix (Fin 3) (Fin 3) K), hgg, Matrix.one_mul]
      _ = (g * M * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * c := by rw [← hcg]
  set σ : commutant C ≃+* commutant C :=
    { toFun := fun M => ⟨(y : Matrix (Fin 3) (Fin 3) K) * M *
        ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hconjmem y hyG M M.2⟩
      invFun := fun M => ⟨((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
        ((y⁻¹⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hconjmem y⁻¹ hyinv M M.2⟩
      left_inv := fun M => Subtype.ext (by
        simp only [inv_inv, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one])
      right_inv := fun M => Subtype.ext (by
        simp only [inv_inv, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
      map_mul' := fun M N => Subtype.ext (by
        change (y : Matrix (Fin 3) (Fin 3) K) * ((M : Matrix (Fin 3) (Fin 3) K) * N) *
            ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((y : Matrix (Fin 3) (Fin 3) K) * M * ((y⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) * ((y : Matrix (Fin 3) (Fin 3) K) * N *
              ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])
      map_add' := fun M N => Subtype.ext (by
        change (y : Matrix (Fin 3) (Fin 3) K) * ((M : Matrix (Fin 3) (Fin 3) K) + N) *
            ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (y : Matrix (Fin 3) (Fin 3) K) * M * ((y⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) + (y : Matrix (Fin 3) (Fin 3) K) * N *
              ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        rw [Matrix.mul_add, Matrix.add_mul]) } with hσ
  have hσpow : ∀ n : ℕ, ∀ M : commutant C, (((σ ^ n) M : commutant C) :
      Matrix (Fin 3) (Fin 3) K) = ((y ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
        (((y ^ n)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro n
    induction n with
    | zero => intro M; simp
    | succ n ih =>
      intro M
      rw [pow_succ', RingAut.mul_apply]
      change (y : Matrix (Fin 3) (Fin 3) K) * (((σ ^ n) M : commutant C) :
          Matrix (Fin 3) (Fin 3) K) * ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [ih, pow_succ', _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc]
  have hσ5 : σ ^ 5 = 1 := by
    ext M
    rw [hσpow, ← hy, pow_orderOf_eq_one, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one]
    rfl
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 5 6
      (by norm_num) (by norm_num) (commutant C) hcardF
  have hσ1 : σ = 1 := by
    have h6 := orderOf_dvd_natCard σ
    rw [hAut] at h6
    have h5 := orderOf_dvd_of_pow_eq_one hσ5
    have h1 : orderOf σ ∣ Nat.gcd 6 5 := Nat.dvd_gcd h6 h5
    rw [show Nat.gcd 6 5 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hyC : (y : Matrix (Fin 3) (Fin 3) K) ∈ commutant C := by
    rw [mem_commutant]
    intro c hc
    have h1 := congrArg (fun M : commutant C => (M : Matrix (Fin 3) (Fin 3) K))
      (RingEquiv.congr_fun hσ1 ⟨c, hCF c hc⟩)
    change (y : Matrix (Fin 3) (Fin 3) K) * c * ((y⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = c at h1
    have hyy : ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (y : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (c : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
          (y : Matrix (Fin 3) (Fin 3) K) * c *
            ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (y : Matrix (Fin 3) (Fin 3) K) := by
            rw [h1]
      _ = (y : Matrix (Fin 3) (Fin 3) K) * c := by
          rw [Matrix.mul_assoc ((y : Matrix (Fin 3) (Fin 3) K) * (c : Matrix (Fin 3) (Fin 3) K)),
            hyy, Matrix.mul_one]
  set u : commutant C := ⟨y, hyC⟩ with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have hy0 : (y : Matrix (Fin 3) (Fin 3) K) = 0 := by
      have := congrArg (fun M : commutant C => (M : Matrix (Fin 3) (Fin 3) K)) h0
      simp [hu] at this
    have hdet := congrArg Matrix.det hy0
    rw [Matrix.det_zero] at hdet
    exact (Matrix.GeneralLinearGroup.det y).ne_zero
      (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)
  set v : (commutant C)ˣ := Units.mk0 u hu0 with hv
  have hupow : ∀ n : ℕ, ((u ^ n : commutant C) : Matrix (Fin 3) (Fin 3) K) =
      ((y ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subalgebra.coe_mul, ih, pow_succ, Units.val_mul]
  have hv5 : v ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    apply Subtype.ext
    rw [hupow, ← hy, pow_orderOf_eq_one, Units.val_one]
    rfl
  have hv1 : v ≠ 1 := by
    intro h1
    have := congrArg (fun w : (commutant C)ˣ => ((w : commutant C) : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [hv, Units.val_mk0, hu, Units.val_one] at this
    have hy1 : y = 1 := Units.ext (by rw [Units.val_one]; exact this)
    rw [hy1, orderOf_one] at hy
    omega
  have hord : orderOf v = 5 := orderOf_eq_prime hv5 hv1
  have hdvd5 := orderOf_dvd_natCard v
  rw [hord, Nat.card_units, hcardF] at hdvd5
  norm_num at hdvd5

omit [Finite K] in
theorem translate_mul (g h : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)) :
    SubgroupLists.translate (g * h) W =
      SubgroupLists.translate g (SubgroupLists.translate h W) := by
  rw [SubgroupLists.translate, SubgroupLists.translate, SubgroupLists.translate,
    Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem false_of_monomial (hK : Nat.card K = 25) {G : Subgroup (GL (Fin 3) K)}
    (hmono : IsTransitiveMonomial G) {x : GL (Fin 3) K} (hxG : x ∈ G) (hx : orderOf x = 7) :
    False := by
  classical
  obtain ⟨L, -, hL1, hperm, -⟩ := hmono
  have hstep : ∀ k : ℕ, ∃ j, SubgroupLists.translate (x ^ k) (L 0) = L j := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      rw [pow_zero, SubgroupLists.translate]
      simp
    | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨j', hj'⟩ := hperm x hxG j
      exact ⟨j', by rw [pow_succ', translate_mul, hj, hj']⟩
  choose f hf using hstep
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin 4 => f i) (by simp)
  have key : ∀ a b : Fin 4, a < b → f a = f b → False := by
    intro a b hlt hfeq
    set m := (b : ℕ) - a with hm
    have hm1 : 1 ≤ m := by omega
    have hm3 : m ≤ 3 := by omega
    have hxm : orderOf (x ^ m) = 7 := by
      rw [orderOf_pow' x (by omega), hx]
      have : Nat.gcd 7 m = 1 := by interval_cases m <;> norm_num
      rw [this, Nat.div_one]
    have hinj : ∀ (g : GL (Fin 3) K) (U V : Submodule K (Fin 3 → K)),
        SubgroupLists.translate g U = SubgroupLists.translate g V → U = V := by
      intro g U V h
      have := congrArg (SubgroupLists.translate g⁻¹) h
      rwa [← translate_mul, ← translate_mul, inv_mul_cancel, SubgroupLists.translate,
        SubgroupLists.translate,
        Units.val_one, Matrix.toLin'_one, Submodule.map_id, Submodule.map_id] at this
    have hfix : SubgroupLists.translate (x ^ m) (L 0) = L 0 := by
      apply hinj (x ^ (a : ℕ))
      rw [← translate_mul, ← pow_add, show (a : ℕ) + m = b by omega, hf a, hf b, hfeq]
    have hW : ∀ w ∈ L 0, ((x ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ L 0 := by
      intro w hw
      rw [← hfix]
      exact ⟨w, hw, rfl⟩
    rcases irreducible_of_orderOf_eq_seven hK hxm (L 0) hW with h0 | h3
    · have := hL1 0
      rw [h0, finrank_bot] at this
      omega
    · have := hL1 0
      rw [h3, finrank_top, Module.finrank_fin_fun] at this
      omega
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hfab
  · exact key b a h hfab.symm

theorem false_of_card_twentySeven (hK : Nat.card K = 25) {G E : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ g ∈ G, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hirr : IsIrreducibleMatrixRep E.subtype) (hE : Nat.card E = 27) {x : GL (Fin 3) K}
    (hxG : x ∈ G) (hx : orderOf x = 7) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Z := Subgroup.zpowers x with hZ
  have hZp : IsPGroup 7 Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hZG : ∀ g ∈ Z, g ∈ G := fun g hg => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact G.zpow_mem hxG k
  let _ : MulAction Z E :=
    { smul := fun g e => ⟨(g : GL (Fin 3) K) * e * (g : GL (Fin 3) K)⁻¹,
        hnorm g (hZG g g.2) e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show ((1 : Z) : GL (Fin 3) K) * e * ((1 : Z) : GL (Fin 3) K)⁻¹ = e
        simp)
      mul_smul := fun g g' e => Subtype.ext (by
        show ((g * g' : Z) : GL (Fin 3) K) * e * ((g * g' : Z) : GL (Fin 3) K)⁻¹ =
          (g : GL (Fin 3) K) * ((g' : GL (Fin 3) K) * e * (g' : GL (Fin 3) K)⁻¹) *
            (g : GL (Fin 3) K)⁻¹
        simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
        group) }
  have hmod := hZp.card_modEq_card_fixedPoints E
  set C : Subgroup (GL (Fin 3) K) := E ⊓ Subgroup.centralizer {x} with hCdef
  have hfixC : Nat.card (MulAction.fixedPoints Z E) = Nat.card C := by
    apply Nat.card_congr
    refine
      { toFun := fun e => ⟨e.1, Subgroup.mem_inf.mpr ⟨e.1.2, ?_⟩⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.mp c.2).1⟩, ?_⟩
        left_inv := fun e => rfl
        right_inv := fun c => rfl }
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val (e.2 ⟨x, Subgroup.mem_zpowers x⟩)
      change x * e.1 * x⁻¹ = e.1 at this
      calc (e.1 : GL (Fin 3) K) * x = x * e.1 * x⁻¹ * x := by rw [this]
        _ = x * e.1 := by group
    · intro g
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      change x ^ k * c.1 * (x ^ k)⁻¹ = c.1
      have hc : Commute x c.1 :=
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2).symm
      rw [(hc.zpow_left k).eq, mul_inv_cancel_right]
  rw [hfixC, hE] at hmod
  have hCdvd : Nat.card C ∣ 27 := hE ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
    (show Nat.card C ∣ 3 ^ 3 by simpa using hCdvd)
  have hC27 : Nat.card C = 27 := by
    interval_cases i <;> simp_all [Nat.ModEq]
  have hCE : C = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hC27, hE])
  have hxE : ∀ e ∈ E, (e : Matrix (Fin 3) (Fin 3) K) * x = x * e := by
    intro e he
    rw [← hCE] at he
    have := Subgroup.mem_centralizer_singleton_iff.mp he.2
    rw [← Units.val_mul, ← Units.val_mul, this]
  rcases scalar_commutant_or_cyclic Nat.prime_three hirr with hsc | ⟨-, hdvd, -⟩
  · obtain ⟨c, hc⟩ := hsc x hxE
    have hc7 : c ^ 7 = 1 := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0)
        (pow_orderOf_eq_one x)
      simp only [hx, Units.val_pow_eq_pow_val, hc, Units.val_one] at this
      rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] at this
      exact this
    have hc0 : c ≠ 0 := by
      rintro rfl
      norm_num at hc7
    set cu : Kˣ := Units.mk0 c hc0
    have hcu7 : cu ^ 7 = 1 := Units.ext (by simp [cu, hc7])
    have hord := orderOf_dvd_of_pow_eq_one hcu7
    have hord' := orderOf_dvd_natCard cu
    rw [Nat.card_units, hK] at hord'
    have hcu1 : orderOf cu = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hord with h1 | h7
      · exact h1
      · rw [h7] at hord'
        norm_num at hord'
    have hc1 : c = 1 := by
      have := orderOf_eq_one_iff.mp hcu1
      have := congrArg Units.val this
      simpa [cu] using this
    have hx1 : x = 1 := by
      apply Units.ext
      rw [hc, hc1, Units.val_one, map_one]
    rw [hx1, orderOf_one] at hx
    omega
  · rw [hE, hK] at hdvd
    norm_num at hdvd

theorem mem_of_twenty_thousand (hQ : KL325Quasi) (G : Subgroup (GL (Fin 3) (GaloisField 5 2)))
    (hdet : ∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1)
    (hcard : 20160 ∣ Nat.card G) (g : GL (Fin 3) (GaloisField 5 2))
    (hg : (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1) : g ∈ G := by
  have hK : Nat.card (GaloisField 5 2) = 25 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [GaloisField.card 5 2 (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 7
    ((by norm_num : 7 ∣ 20160).trans hcard)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := G) 5
    ((by norm_num : 5 ∣ 20160).trans hcard)
  have hx' : orderOf (x : GL (Fin 3) (GaloisField 5 2)) = 7 := by
    rw [Subgroup.orderOf_coe, hx]
  have hy' : orderOf (y : GL (Fin 3) (GaloisField 5 2)) = 5 := by
    rw [Subgroup.orderOf_coe, hy]
  have hirr : IsIrreducibleMatrixRep G.subtype := fun W hW =>
    irreducible_of_orderOf_eq_seven hK hx' W (fun w hw => hW x w hw)
  rcases irreducible_gl3_reduction hirr with
    ⟨C, -, hnorm, hCirr, hcyc, -, -⟩ | hmono | ⟨-, E, -, hnorm, hEirr, hE27, -⟩ |
      ⟨H, hHG, hnorm, hq, hHirr, hscal, hHdet, hZ⟩
  · exact (false_of_cyclic hK hnorm hCirr hcyc y.2 hy').elim
  · exact (false_of_monomial hK hmono x.2 hx').elim
  · exact (false_of_card_twentySeven hK hnorm hEirr (by rw [hE27]; norm_num) x.2 hx').elim
  · exact hQ G H hHG hnorm hq hHirr hscal hHdet hZ hdet hcard g hg

theorem kl325SubgroupOrder_of_quasi (hQ : KL325Quasi) : KL325SubgroupOrder := by
  intro X _ _ _ hX H hH
  obtain ⟨e⟩ := hX
  set P := CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2) with hP
  set S : Subgroup (GL (Fin 3) (GaloisField 5 2)) :=
    (Matrix.GeneralLinearGroup.det : GL (Fin 3) (GaloisField 5 2) →* (GaloisField 5 2)ˣ).ker
    with hS
  have hmemS : ∀ g : GL (Fin 3) (GaloisField 5 2),
      g ∈ S ↔ (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1 := by
    intro g
    rw [hS, MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one]
  have hψmem : ∀ s : S, Matrix.ProjGenLinGroup.mk (s : GL (Fin 3) (GaloisField 5 2)) ∈ P :=
    fun s => ⟨s, s.2, rfl⟩
  set ψ : S →* P :=
    { toFun := fun s => ⟨Matrix.ProjGenLinGroup.mk (s : GL (Fin 3) (GaloisField 5 2)), hψmem s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) } with hψ
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨p, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  set H₁ : Subgroup P := H.map e.toMonoidHom with hH₁
  set G' : Subgroup S := H₁.comap ψ with hG'
  set G : Subgroup (GL (Fin 3) (GaloisField 5 2)) := G'.map S.subtype with hG
  have hGdet : ∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 2)).det = 1 := by
    rintro _ ⟨s, -, rfl⟩
    exact (hmemS _).mp s.2
  have hGcard : 20160 ∣ Nat.card G := by
    have h1 : Nat.card H₁ ∣ Nat.card G' :=
      Subgroup.card_dvd_of_surjective (ψ.subgroupComap_surjective H₁ hψsurj)
    have h2 : Nat.card H₁ = Nat.card H := Subgroup.card_map_of_injective e.injective
    have h3 : Nat.card G = Nat.card G' := Subgroup.card_map_of_injective S.subtype_injective
    rw [h3]
    exact hH.trans (h2 ▸ h1)
  have hall := mem_of_twenty_thousand hQ G hGdet hGcard
  rw [eq_top_iff]
  intro z _
  obtain ⟨s, hs⟩ := hψsurj (e z)
  have hsG : (s : GL (Fin 3) (GaloisField 5 2)) ∈ G := hall _ ((hmemS _).mp s.2)
  obtain ⟨s', hs'G, hs's⟩ := hsG
  have hss' : s' = s := Subtype.ext hs's
  rw [hss'] at hs'G
  have hez : e z ∈ H₁ := by
    rw [← hs]
    exact hs'G
  obtain ⟨z', hz', hzz'⟩ := hez
  have : z' = z := e.injective hzz'
  rw [← this]
  exact hz'

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
