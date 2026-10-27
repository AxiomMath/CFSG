module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectGal
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectNat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem conj_one_apply {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) (w : Fin 2 → D.K) :
    D.conj 1 w = w := by
  obtain ⟨v, rfl⟩ : ∃ v : ↥N, Multiplicative.toAdd (D.E v) = w :=
    ⟨D.E.symm (Multiplicative.ofAdd w), by simp⟩
  have h1 : conjAct N (1 : Subgroup.normalizer (N : Set G)) v = v :=
    Subtype.ext (by simp [conjAct_apply_coe])
  rw [NatL2Data.conj_apply, h1]

theorem conj_cube_apply {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m)
    {g : Subgroup.normalizer (N : Set G)} (hg : g * g * g = 1) (w : Fin 2 → D.K) :
    D.conj g (D.conj g (D.conj g w)) = w := by
  calc D.conj g (D.conj g (D.conj g w)) = D.conj (g * g * g) w := by
        rw [NatL2Data.conj_mul, NatL2Data.conj_mul]
    _ = D.conj 1 w := by rw [hg]
    _ = w := conj_one_apply D w

theorem normalizer_cube_eq_one {N : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (N : Set G))
    (hd3 : d ^ 3 = 1) :
    (⟨d, hdN⟩ * ⟨d, hdN⟩ * ⟨d, hdN⟩ : Subgroup.normalizer (N : Set G)) = 1 :=
  Subtype.ext (by
    have h3 : d * d * d = 1 := by
      have := hd3
      rw [pow_three] at this
      rwa [mul_assoc]
    simpa using h3)

theorem conj_linear_of_pow_three {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m)
    (hm : m = 2 ∨ m = 4) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1) :
    ∃ hd : d ∈ Subgroup.normalizer (N : Set G), ∀ (a : D.K) (w : Fin 2 → D.K),
      D.conj ⟨d, hd⟩ (a • w) = a • D.conj ⟨d, hd⟩ w := by
  have hdN : d ∈ Subgroup.normalizer (N : Set G) := D.le_normalizer hdL
  refine ⟨hdN, ?_⟩
  set g : Subgroup.normalizer (N : Set G) := ⟨d, hdN⟩ with hg
  obtain ⟨σ, hσ⟩ := D.exists_semilinear g (Subgroup.le_normalizer hdL)
  have hcube1 : g * g * g = 1 := normalizer_cube_eq_one hdN hd3
  have hcube : ∀ w : Fin 2 → D.K, D.conj g (D.conj g (D.conj g w)) = w :=
    fun w => conj_cube_apply D hcube1 w
  have hw : (![1, 0] : Fin 2 → D.K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hσ3 : ∀ x : D.K, σ (σ (σ x)) = x := by
    intro x
    have h := hcube (x • ![1, 0])
    rw [hσ, hσ, hσ, hcube] at h
    exact smul_left_injective D.K hw h
  have ha : 1 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have hco : Nat.Coprime 3 m := by rcases hm with rfl | rfl <;> norm_num
  haveI : CharP D.K 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D.card
  have hσid : ∀ x, σ x = x :=
    Direct523Gal.eq_id_of_pow_three ha D.card hco σ hσ3
  intro a w
  rw [hσ, hσid]

@[expose] noncomputable def coordN {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) (x : G) (hx : x ∈ N) :
    Fin 2 → D.K :=
  Multiplicative.toAdd (D.E ⟨x, hx⟩)

theorem coordN_mul {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {x y : G} (hx : x ∈ N)
    (hy : y ∈ N) (hxy : x * y ∈ N) : coordN D (x * y) hxy = coordN D x hx + coordN D y hy := by
  unfold coordN
  have : (⟨x * y, hxy⟩ : ↥N) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem coordN_injective {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {x y : G} (hx : x ∈ N)
    (hy : y ∈ N) (h : coordN D x hx = coordN D y hy) : x = y := by
  unfold coordN at h
  have h1 := D.E.injective (Multiplicative.toAdd.injective h)
  exact congrArg Subtype.val h1

theorem step1_coord (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) {N : Subgroup G} {m : ℕ} (D : NatL2Data L N m)
    (hD : D.SylowAdapted (T ⊓ L)) (hm : m = 2 ∨ m = 4) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N) :
    ∃ c : D.K, c ^ 3 = 1 ∧ c ≠ 1 ∧
      conjClosure Z₁ D₃ ≤ N ∧
      (∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
          coordN D v hv = μ • coordN D z hzN) := by
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hdL : d ∈ L := s.D₃_le_L hd
  have hd3 : d ^ 3 = 1 := pow_three_of_mem_of_card_three s.card_D₃ hd
  obtain ⟨hdN, hlin⟩ := conj_linear_of_pow_three D hm hdL hd3
  set g : Subgroup.normalizer (N : Set G) := ⟨d, hdN⟩ with hg
  have hzC : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le inf_le_left (quasithinOmegaOneCenter_le_inf T (s.Z₁_le_Z hz)).2
  have hzdN : d * z * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hLN hdL) z).mp hzN
  have hzdC : d * z * d⁻¹ ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s' hs'
    have hdS : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := s.D₃_le_normalizer_inf hd
    have h1 : d⁻¹ * s' * d⁻¹⁻¹ ∈ (T ⊓ L : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdS) s').mp hs'
    have hc := Subgroup.mem_centralizer_iff.mp hzC _ h1
    calc s' * (d * z * d⁻¹) = d * (d⁻¹ * s' * d⁻¹⁻¹ * z) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * s' * d⁻¹⁻¹)) * d⁻¹ := by rw [hc]
      _ = (d * z * d⁻¹) * s' := by group
  have hzS := (NatL2Data.mem_centralizer_iff_line D inf_le_right hD ⟨z, hzN⟩).mp
    (show z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) from hzC)
  have hzdS := (NatL2Data.mem_centralizer_iff_line D inf_le_right hD ⟨d * z * d⁻¹, hzdN⟩).mp
    hzdC
  obtain ⟨a₀, ha₀⟩ := hzS
  obtain ⟨a₁, ha₁⟩ := hzdS
  have hw0 : coordN D z hzN ≠ 0 := by
    intro h0
    apply hz1
    have h1 : (⟨z, hzN⟩ : ↥N) = 1 := by
      apply D.E.injective
      apply Multiplicative.toAdd.injective
      have : Multiplicative.toAdd (D.E ⟨z, hzN⟩) = 0 := h0
      rw [this]
      simp
    exact congrArg Subtype.val h1
  have ha0 : a₀ ≠ 0 := by
    intro h0
    apply hw0
    unfold coordN
    rw [ha₀, h0]
    ext i
    fin_cases i <;> simp
  set c : D.K := a₁ * a₀⁻¹ with hc
  have hzd_coord : coordN D (d * z * d⁻¹) hzdN = c • coordN D z hzN := by
    unfold coordN at *
    rw [ha₀, ha₁, hc]
    ext i
    fin_cases i <;> simp [mul_assoc, ha0]
  have hgz : D.conj g (coordN D z hzN) = coordN D (d * z * d⁻¹) hzdN := by
    unfold coordN
    rw [NatL2Data.conj_apply]
    congr 2
  have hgc : D.conj g (coordN D z hzN) = c • coordN D z hzN := by
    rw [hgz, hzd_coord]
  have hg2 : D.conj g (D.conj g (coordN D z hzN)) = (c * c) • coordN D z hzN := by
    rw [hgc, hlin, hgc, smul_smul]
  have hg3' : D.conj g (D.conj g (D.conj g (coordN D z hzN))) = (c * c * c) • coordN D z hzN := by
    rw [hg2, hlin, hgc, smul_smul]
  have hg3 : D.conj g (D.conj g (D.conj g (coordN D z hzN))) = coordN D z hzN :=
    conj_cube_apply D (normalizer_cube_eq_one hdN hd3) _
  have hc3 : c ^ 3 = 1 := by
    have h1 : (c * c * c) • coordN D z hzN = (1 : D.K) • coordN D z hzN := by
      rw [one_smul, ← hg3', hg3]
    have h2 : c * c * c = 1 := smul_left_injective D.K hw0 h1
    calc c ^ 3 = c * c * c := by ring
      _ = 1 := h2
  have hc1 : c ≠ 1 := by
    intro h
    apply (s.b_props hz hz1 hd hd1 h5114).2.2.2
    have h1 : coordN D (d * z * d⁻¹) hzdN = coordN D z hzN := by
      rw [hzd_coord, h, one_smul]
    exact coordN_injective D hzdN hzN h1
  have hV2N : conjClosure Z₁ D₃ ≤ N := by
    refine conjClosure_le fun g' hg' y hy => ?_
    rcases s.eq_one_or_eq hz hz1 hy with h | h
    · rw [h, mul_one, mul_inv_cancel]
      exact N.one_mem
    · rw [h]
      exact (Subgroup.mem_normalizer_iff.mp (hLN (s.D₃_le_L hg')) _).mp hzN
  have hcoordEq : ∀ (x y : G) (hx : x ∈ N) (hy : y ∈ N), x = y →
      coordN D x hx = coordN D y hy := by
    intro x y hx hy h
    subst h
    rfl
  have hzb : z * (d * z * d⁻¹) ∈ N := N.mul_mem hzN hzdN
  have hzb_coord : coordN D (z * (d * z * d⁻¹)) hzb = (1 + c) • coordN D z hzN := by
    rw [coordN_mul D hzN hzdN hzb, hzd_coord, add_smul, one_smul]
  have h2N : d ^ 2 * z * (d ^ 2)⁻¹ ∈ N := by
    rw [s.c_eq hz hz1 hd hd1 h5114 hF]
    exact hzb
  have hsq_coord : coordN D (d ^ 2 * z * (d ^ 2)⁻¹) h2N = (c * c) • coordN D z hzN := by
    have hgg : D.conj (g * g) (coordN D z hzN) = coordN D (d ^ 2 * z * (d ^ 2)⁻¹) h2N := by
      unfold coordN
      rw [NatL2Data.conj_apply]
      congr 2
      apply Subtype.ext
      rw [conjAct_apply_coe]
      simp only [hg, Subgroup.coe_mul, pow_two]
    rw [← hgg, NatL2Data.conj_mul, hg2]
  have hcc : (1 + c) = c * c := by
    have h1 : (1 + c) • coordN D z hzN = (c * c) • coordN D z hzN := by
      rw [← hzb_coord, ← hsq_coord]
      exact hcoordEq _ _ _ _ (s.c_eq hz hz1 hd hd1 h5114 hF).symm
    exact smul_left_injective D.K hw0 h1
  refine ⟨c, hc3, hc1, hV2N, ?_⟩
  intro v hv
  refine ⟨hV2N hv, ?_⟩
  obtain ⟨u, hu, huv⟩ := s.mem_V₂_iff hz hz1 hd hd1 h5114 hF hv
  have hc4 : c ^ 4 = c := by
    calc c ^ 4 = c ^ 3 * c := by ring
      _ = c := by rw [hc3, one_mul]
  have hcc4 : (c * c) ^ 4 = c * c := by
    calc (c * c) ^ 4 = (c ^ 3) ^ 2 * (c * c) := by ring
      _ = c * c := by rw [hc3, one_pow, one_mul]
  have hzero : coordN D 1 N.one_mem = 0 := by
    unfold coordN
    simp
  rcases s.eq_one_or_eq hz hz1 hu with hu1 | hu1
  · rcases huv with hv1 | hv1
    ·
      refine ⟨0, by simp, ?_⟩
      rw [hcoordEq v 1 (hV2N hv) N.one_mem (hv1.trans hu1), hzero, zero_smul]
    ·
      refine ⟨c, hc4, ?_⟩
      have hvb : v = d * z * d⁻¹ := by rw [hv1, hu1, one_mul]
      rw [hcoordEq v _ (hV2N hv) hzdN hvb, hzd_coord]
  · rcases huv with hv1 | hv1
    ·
      refine ⟨1, by simp, ?_⟩
      rw [hcoordEq v z (hV2N hv) hzN (hv1.trans hu1), one_smul]
    ·
      refine ⟨c * c, hcc4, ?_⟩
      have hvb : v = z * (d * z * d⁻¹) := by rw [hv1, hu1]
      rw [hcoordEq v _ (hV2N hv) hzb hvb, hzb_coord, hcc]

end CFSG.Quasithin.H13
