module

public import CFSG.RankThree.PartTwo.Census.NineCoverU43

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix
open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartTwo.Sec4.Census.NineCoverU43
open CFSG.Assembly.RankThreeEven (projSU)

namespace U43Rank

@[expose] def cmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![1, 0, 1, ⟨1, 2⟩;
    0, 1, ⟨1, 1⟩, ⟨2, 0⟩;
    ⟨2, 0⟩, ⟨2, 1⟩, 1, 0;
    ⟨2, 2⟩, 1, 0, 1]

@[expose] def gmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, ⟨2, 0⟩, 0;
    0, 0, 0, ⟨2, 0⟩]

theorem det_cmat : cmat.det = 1 := by decide +kernel

theorem cmat_unitary : (cmat.map (· ^ 3))ᵀ * cmat = 1 := by decide +kernel

theorem det_gmat : gmat.det = 1 := by decide +kernel

theorem gmat_unitary : (gmat.map (· ^ 3))ᵀ * gmat = 1 := by decide +kernel

theorem mat_mul_cmat : ∀ a b : ZMod 3, mat a b * cmat = cmat * mat a b := by decide +kernel

theorem gmat_mul_mat : ∀ a b : ZMod 3, gmat * mat a b = mat a b * gmat := by decide +kernel

theorem gmat_mul_cmat : gmat * cmat = cmat * cmat * gmat := by decide +kernel

theorem cmat_cube : cmat * cmat * cmat = 1 := by decide +kernel

theorem mat_mul_mat_neg : ∀ a b : ZMod 3, mat a b * mat (-a) (-b) = 1 := by decide +kernel

theorem mat_mul_cmat_zero_two : ∀ a b : ZMod 3, (mat a b * cmat) 0 2 = 1 := by decide +kernel

@[expose] noncomputable def cSU : StatedSU 4 3 F9 := toSU cmat det_cmat cmat_unitary

@[expose] noncomputable def gSU : StatedSU 4 3 F9 := toSU gmat det_gmat gmat_unitary

@[expose] noncomputable def u3 : X₀ := QuotientGroup.mk cSU

@[expose] noncomputable def gBar : X₀ := QuotientGroup.mk gSU

theorem u3_pow_three : u3 ^ 3 = 1 := by
  rw [u3, ← QuotientGroup.mk_pow]
  have h : cSU ^ 3 = 1 := ext_matrix (by
    rw [pow_three, ← mul_assoc]
    exact cmat_cube)
  rw [h, QuotientGroup.mk_one]

theorem commute_theta_u3 (x : Multiplicative (ZMod 3 × ZMod 3)) : Commute (theta x) u3 := by
  show QuotientGroup.mk (theta0 x * cSU) = (QuotientGroup.mk (cSU * theta0 x) : X₀)
  have h : theta0 x * cSU = cSU * theta0 x := ext_matrix (mat_mul_cmat _ _)
  rw [h]

theorem gBar_conj_theta (x : Multiplicative (ZMod 3 × ZMod 3)) :
    gBar * theta x * gBar⁻¹ = theta x := by
  rw [mul_inv_eq_iff_eq_mul]
  show QuotientGroup.mk (gSU * theta0 x) = (QuotientGroup.mk (theta0 x * gSU) : X₀)
  have h : gSU * theta0 x = theta0 x * gSU := ext_matrix (gmat_mul_mat _ _)
  rw [h]

theorem gBar_conj_u3 : gBar * u3 * gBar⁻¹ = u3⁻¹ := by
  have h3 := u3_pow_three
  have hinv : u3⁻¹ = u3 * u3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact h3
  rw [hinv, mul_inv_eq_iff_eq_mul]
  show QuotientGroup.mk (gSU * cSU) = (QuotientGroup.mk (cSU * cSU * gSU) : X₀)
  have h : gSU * cSU = cSU * cSU * gSU := ext_matrix gmat_mul_cmat
  rw [h]

theorem u3_not_mem_range : u3 ∉ theta.range := by
  rintro ⟨x, hx⟩
  have h : QuotientGroup.mk (theta0 x) = (QuotientGroup.mk cSU : X₀) := hx
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9)) hc
  simp only [GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Subgroup.coe_inv,
    Units.val_mul] at hc'
  have hcs : ((cSU : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = cmat := rfl
  have hmul : ((theta0 x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
      mat (-x.toAdd.1) (-x.toAdd.2) = 1 := by
    rw [coe_theta0]
    exact mat_mul_mat_neg _ _
  have hts : (((theta0 x : GL (Fin 4) F9)⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      mat (-x.toAdd.1) (-x.toAdd.2) :=
    Units.inv_eq_of_mul_eq_one_right hmul
  rw [hts, hcs] at hc'
  have h02 := congrFun (congrFun hc' 0) 2
  rw [mat_mul_cmat_zero_two, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 4) ≠ 2 by decide)] at h02
  exact absurd h02 (by decide)

abbrev E3 : Subgroup X₀ := Subgroup.closure {u1, u2, u3}

theorem range_theta_le_E3 : theta.range ≤ E3 :=
  range_theta_le.trans (Subgroup.closure_mono (by
    intro w hw
    rcases hw with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem u3_mem_E3 : u3 ∈ E3 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem card_E3_ge : 27 ≤ Nat.card E3 := by
  set H := theta.range
  set K := Subgroup.zpowers u3
  have hu3 : u3 ≠ 1 := fun h => u3_not_mem_range (h ▸ H.one_mem)
  have hK : Nat.card K = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime u3_pow_three hu3
  have hinf : ∀ w ∈ H, w ∈ K → w = 1 := by
    intro w hwH hwK
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwK
    have ho : orderOf u3 = 3 := orderOf_eq_prime u3_pow_three hu3
    rw [← zpow_mod_orderOf, ho] at hwH ⊢
    have h0 := Int.emod_nonneg j (show (3 : ℤ) ≠ 0 by norm_num)
    have h1 := Int.emod_lt_of_pos j (show (0 : ℤ) < 3 by norm_num)
    have hcases : j % (3 : ℕ) = 0 ∨ j % (3 : ℕ) = 1 ∨ j % (3 : ℕ) = 2 := by push_cast; omega
    rcases hcases with h | h | h <;> rw [h] at hwH ⊢
    · exact zpow_zero u3
    · rw [zpow_one] at hwH
      exact absurd hwH u3_not_mem_range
    · exfalso
      apply u3_not_mem_range
      have hw2 : u3 ^ 2 ∈ H := by
        rw [← zpow_natCast]
        exact hwH
      have h2 : u3 = (u3 ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, u3_pow_three, one_mul]
      rw [h2]
      exact H.pow_mem hw2 2
  let f : H × K → E3 := fun p => ⟨(p.1 : X₀) * p.2,
    E3.mul_mem (range_theta_le_E3 p.1.2) ((Subgroup.zpowers_le.mpr u3_mem_E3) p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨h, k⟩ ⟨h', k'⟩ hhk
    have he : (h : X₀) * k = h' * k' := congrArg Subtype.val hhk
    have hw : (h' : X₀)⁻¹ * h = k' * (k : X₀)⁻¹ := by
      calc (h' : X₀)⁻¹ * h = (h' : X₀)⁻¹ * (h * k) * (k : X₀)⁻¹ := by group
        _ = (h' : X₀)⁻¹ * (h' * k') * (k : X₀)⁻¹ := by rw [he]
        _ = k' * (k : X₀)⁻¹ := by group
    have h1 : (h' : X₀)⁻¹ * h = 1 :=
      hinf _ (H.mul_mem (H.inv_mem h'.2) h.2) (hw ▸ K.mul_mem k'.2 (K.inv_mem k.2))
    have hh : (h : X₀) = h' := by
      have := h1
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hk : (k : X₀) = k' := by
      rw [hh] at he
      exact mul_left_cancel he
    exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_range_theta, hK] at hcard
  norm_num at hcard
  exact hcard

section Lifts

variable {G : Type} [Group G] {φ : G →* X₀}

theorem commute_of_gen3 (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (x y : G) (hx : φ x ∈ ({u1, u2, u3} : Set X₀)) (hy : φ y ∈ ({u1, u2, u3} : Set X₀))
    (hxy : φ x ≠ φ y) : x * y = y * x := by
  have hu12 : ∀ a b : G, φ a ∈ ({u1, u2} : Set X₀) → φ b ∈ ({u1, u2} : Set X₀) →
      φ a ≠ φ b → a * b = b * a := commute_of_gen hφ hker
  have hg : ∀ a b : G, φ a ∈ ({u1, u2} : Set X₀) → φ b = u3 → a * b = b * a := by
    intro a b ha hb
    have hθ : ∃ t, φ a = theta t := by
      rcases ha with ha | ha
      · exact ⟨_, ha⟩
      · exact ⟨_, ha⟩
    obtain ⟨t, ht⟩ := hθ
    have hc : Commute (φ a) (φ b) := by rw [ht, hb]; exact commute_theta_u3 t
    refine TripleCoverLift.commute_of_conj hφ hker (p := 3) (by decide) hc
      (by rw [hb]; exact u3_pow_three) (n := gBar)
      (Or.inl ⟨by rw [ht]; exact gBar_conj_theta t, by rw [hb]; exact gBar_conj_u3⟩)
  have hS : ∀ w : X₀, w ∈ ({u1, u2, u3} : Set X₀) → w ∈ ({u1, u2} : Set X₀) ∨ w = u3 := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (Set.mem_insert _ _)
    · exact Or.inl (Set.mem_insert_of_mem _ rfl)
    · exact Or.inr rfl
  rcases hS _ hx with hx' | hx' <;> rcases hS _ hy with hy' | hy'
  · exact hu12 x y hx' hy' hxy
  · exact hg x y hx' hy'
  · exact (hg y x hy' hx').symm
  · exact absurd (hx'.trans hy'.symm) hxy

theorem commute_of_mem_E3 (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {x y : G} (hx : φ x ∈ E3) (hy : φ y ∈ E3) : x * y = y * x :=
  TripleCoverLift.commute_of_mem_closure hφ hker (commute_of_gen3 hφ hker) hx hy

theorem exists_lift_of_mem_E3 (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {e : X₀} (he : e ∈ E3) : ∃ y : G, φ y = e ∧ y ^ 3 = 1 := by
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure (E := E3)
    (fun x hx y hy => commute_of_mem_E3 hφ hker hx hy) (S := {u1, u2, u3})
    Subgroup.subset_closure ?_ he
  rintro _ (rfl | rfl | rfl)
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      (theta_pow_three _) (nBar_conj_theta _)
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      (theta_pow_three _) (nBar_conj_theta _)
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      u3_pow_three gBar_conj_u3

end Lifts

theorem four_le_pRank_of_cover {G : Type} [Group G] [Finite G] (φ : G →* X₀)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ 3 = 1) (hZ : 3 ≤ Nat.card Z) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ E3.comap φ, ∀ y ∈ E3.comap φ, x * y = y * x :=
    fun x hx y hy => commute_of_mem_E3 hφ hker hx hy
  set U := TripleCoverLift.powOneSubgroup φ E3 3 hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup 3 U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X₀ := φ.comp U.subtype
  have hψr : ψ.range = E3 := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := exists_lift_of_mem_E3 hφ hker he
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => TripleCoverLift.mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact E3.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : 3 ≤ Nat.card ψ.ker := by
    calc 3 ≤ Nat.card Z := hZ
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have h81 : 3 ^ 4 ≤ 3 ^ k := by
    rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr]
    calc 3 ^ 4 = 3 * 27 := by norm_num
      _ ≤ Nat.card ψ.ker * Nat.card E3 := Nat.mul_le_mul hψk card_E3_ge
  have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h81
  exact hk4.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hUab hk)

end U43Rank

open U43Rank in
theorem four_le_pRank_of_threeCoverU43 {X : Type} [Group X] [Finite X]
    (h3 : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* projSU 4 3 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨eX⟩ := nonempty_mulEquiv_X₀ lieModel_U43
  let φ : X →* X₀ := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center X := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  refine four_le_pRank_of_cover φ hφ hker.le hker.ge (fun z hz => ?_) h3.ge
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center X))
  rw [h3] at h
  exact congrArg Subtype.val h

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
