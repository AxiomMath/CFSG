module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofMat
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (GeneralLinearGroup diagonal)
open Item211Res2Proof Item2130Res6Proof

namespace Item2130Res7Proof

section Matrices

variable {K : Type} [Field K]

theorem diagUnits_comm (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem diagUnits_one : (diagUnits 1 1 1 : GL (Fin 3) K) = 1 := by
  apply Units.ext
  rw [coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => simp [diagUnits_one]
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, ← pow_succ, ← pow_succ, ← pow_succ]

theorem diagUnits_mem_slPi_true {a b c : Kˣ} (h : a * b * c = 1) (q : ℕ) :
    diagUnits a b c ∈ slPi true 3 q K := by
  rw [mem_slPi_true, coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
  have := congrArg Units.val h
  simpa [mul_assoc] using this

theorem conj_scalar_mul (l : Kˣ) (X M : GL (Fin 3) K) :
    (GeneralLinearGroup.scalar (Fin 3) l * X) * M *
      (GeneralLinearGroup.scalar (Fin 3) l * X)⁻¹ = X * M * X⁻¹ := by
  have h := scalar_mul_comm l (X * M * X⁻¹)
  calc (GeneralLinearGroup.scalar (Fin 3) l * X) * M *
        (GeneralLinearGroup.scalar (Fin 3) l * X)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l * (X * M * X⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ := by group
    _ = X * M * X⁻¹ * GeneralLinearGroup.scalar (Fin 3) l *
        (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ := by rw [h]
    _ = X * M * X⁻¹ := by group

theorem conj_frame_scalar (g X : GL (Fin 3) K) (l : Kˣ) :
    g * (GeneralLinearGroup.scalar (Fin 3) l * X) * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l * (g * X * g⁻¹) := by
  have h := scalar_mul_comm l g
  calc g * (GeneralLinearGroup.scalar (Fin 3) l * X) * g⁻¹ =
      (g * GeneralLinearGroup.scalar (Fin 3) l) * X * g⁻¹ := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) l * g) * X * g⁻¹ := by rw [h]
    _ = _ := by group

theorem conj_frame_eq_of_commute {g y X : GL (Fin 3) K}
    (h : (g⁻¹ * y * g) * X = X * (g⁻¹ * y * g)) : y * (g * X * g⁻¹) * y⁻¹ = g * X * g⁻¹ := by
  calc y * (g * X * g⁻¹) * y⁻¹ = g * ((g⁻¹ * y * g) * X) * (g⁻¹ * y * g)⁻¹ * g⁻¹ := by group
    _ = g * (X * (g⁻¹ * y * g)) * (g⁻¹ * y * g)⁻¹ * g⁻¹ := by rw [h]
    _ = g * X * g⁻¹ := by group

theorem conj_pow_eq_self {H : Type*} [Group H] {x y : H} (h : x * y * x⁻¹ = y) (n : ℕ) :
    x ^ n * y * (x ^ n)⁻¹ = y := by
  have hc : Commute x y := by
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h]
  rw [(hc.pow_left n).eq, mul_inv_cancel_right]

theorem sq_ne_one_of_cube {σ : Kˣ} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) : σ ^ 2 ≠ 1 := by
  intro h
  apply hσ1
  calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
    _ = 1 := by rw [hσ3, h, inv_one, one_mul]

end Matrices

variable {G : Type} [Group G] [Finite G] {A E U L U₀ Y : Subgroup G} {c b : G}

theorem barHom_mk {x : G} (hx : x ∈ Subgroup.normalizer (Y : Set G)) (y : Y) :
    barHom Y ⟨x, hx⟩ (y : lBar Y) = ((Y.normalizerMonoidHom ⟨x, hx⟩ y : Y) : lBar Y) :=
  rfl

theorem eq_of_mk_eq {A : Subgroup G} (hAe : IsElemAbelian 3 A) {u v : Y} (hu : (u : G) ∈ A)
    (hv : (v : G) ∈ A) (h : (u : lBar Y) = (v : lBar Y)) : u = v := by
  have h1 : ((u⁻¹ * v : Y) : lBar Y) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]
  have h3 : (u⁻¹ * v) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    exact hAe.2 _ (A.mul_mem (A.inv_mem hu) hv)
  have := eq_one_of_mk_eq_one h1 h3
  rw [inv_mul_eq_one] at this
  exact this

theorem false_of_typeC_sl (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    (hcY : c ∉ Y) {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K)
    (hq : ModThree true (p ^ f)) (e : lBar Y ≃* slPi true 3 (p ^ f) K)
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC true (p ^ f) K D)
    (hAD : ∀ τ ∈ autThetaQuot A Y, ∃ y ∈ D, ∀ z : lBar Y,
      ((e (τ z) : slPi true 3 (p ^ f) K) : GL (Fin 3) K) = y * (e z : GL (Fin 3) K) * y⁻¹)
    {yc : GL (Fin 3) K} (hycD : yc ∈ D)
    (hyc : ∀ z : lBar Y, ((e (barHom Y ⟨c, hC.c_norm⟩ z) : slPi true 3 (p ^ f) K) :
      GL (Fin 3) K) = yc * (e z : GL (Fin 3) K) * yc⁻¹)
    (h2t : Type123 true (p ^ f) K yc 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hcfg.pair.mem_S.1.2.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hbA : b ∈ A := hC.b_mem.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  set ε : lBar Y →* GL (Fin 3) K := (slPi true 3 (p ^ f) K).subtype.comp e.toMonoidHom with hε
  have hεinj : Function.Injective ε := fun z z' h => e.injective (Subtype.ext h)
  have hεsymm : ∀ (M : GL (Fin 3) K) (hM : M ∈ slPi true 3 (p ^ f) K),
      ε (e.symm ⟨M, hM⟩) = M := fun M hM => by
    simp [hε]
  have hycZ : yc ∉ StatedScalars (Fin 3) K := by
    intro hZ
    have hcC : c ∈ thetaQuotCentralizer Y := by
      refine mem_thetaQuotCentralizer_iff.mpr ⟨hC.c_norm, ?_⟩
      ext z
      apply hεinj
      change ((e (barHom Y ⟨c, hC.c_norm⟩ z) : slPi true 3 (p ^ f) K) : GL (Fin 3) K) = ε z
      rw [hyc z, ← commute_of_mem_statedScalars hZ, mul_inv_cancel_right]
      rfl
    have hCA : A ⊓ thetaQuotCentralizer Y = Subgroup.zpowers b := by
      have hset := Sec13.sectionCentralizer_eq_inf hAL
      rw [hC.sec_cent] at hset
      exact SetLike.coe_injective hset.symm
    have hcb : c ∈ Subgroup.zpowers b := hCA ▸ (⟨hcA, hcC⟩ : c ∈ A ⊓ thetaQuotCentralizer Y)
    exact hcfg.not_mem ((Subgroup.zpowers_le.mpr hC.b_mem.2) hcb)
  obtain ⟨g, -, hdiag, -, lc, σ, hσ, hσ1, hgc⟩ := exists_frame_of_type2 hK hq hD hycD hycZ h2t
  have hσ3 : σ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hσ
  have hSL : ∀ X ∈ slPi true 3 (p ^ f) K, g * X * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
    fun X hX => conj_mem_slPi hπ (mem_glPi_true _ g) hX
  have hAmat : ∀ (a : G) (ha : a ∈ A), ∃ s t : Kˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z : lBar Y,
      ε (barHom Y ⟨a, hAL ha⟩ z) =
        (g * diagUnits 1 s t * g⁻¹) * ε z * (g * diagUnits 1 s t * g⁻¹)⁻¹ := by
    intro a ha
    obtain ⟨y, hyD, hy⟩ := hAD _ (mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩)
    obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag y hyD
    refine ⟨s, t, (mem_rootsOfUnity _ _).mp hs, (mem_rootsOfUnity _ _).mp ht, fun z => ?_⟩
    have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
      rw [← hl]
      group
    have h1 : ε (barHom Y ⟨a, hAL ha⟩ z) = y * ε z * y⁻¹ := hy z
    rw [h1, hy', conj_frame_scalar, conj_scalar_mul]
  have hfix : ∀ (u v w : Kˣ) (hM : g * diagUnits u v w * g⁻¹ ∈ slPi true 3 (p ^ f) K)
      (a : G) (ha : a ∈ A), barHom Y ⟨a, hAL ha⟩ (e.symm ⟨_, hM⟩) = e.symm ⟨_, hM⟩ := by
    intro u v w hM a ha
    obtain ⟨s, t, -, -, hst⟩ := hAmat a ha
    apply hεinj
    rw [hst, hεsymm]
    calc g * diagUnits 1 s t * g⁻¹ * (g * diagUnits u v w * g⁻¹) *
          (g * diagUnits 1 s t * g⁻¹)⁻¹ =
        g * (diagUnits 1 s t * diagUnits u v w * (diagUnits 1 s t)⁻¹) * g⁻¹ := by group
      _ = g * diagUnits u v w * g⁻¹ := by rw [diagUnits_comm, mul_inv_cancel_right]
  have hcube : ∀ (u v w : Kˣ) (hM : g * diagUnits u v w * g⁻¹ ∈ slPi true 3 (p ^ f) K),
      u ^ 3 = 1 → v ^ 3 = 1 → w ^ 3 = 1 → (e.symm ⟨_, hM⟩) ^ 3 = 1 := by
    intro u v w hM hu hv hw
    apply hεinj
    rw [map_pow, hεsymm, map_one, conj_pow, diagUnits_pow, hu, hv, hw, diagUnits_one, mul_one,
      mul_inv_cancel]
  have hD'S : g * diagUnits 1 σ (σ ^ 2) * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
    hSL _ (diagUnits_mem_slPi_true (by rw [one_mul, ← pow_succ', hσ3]) _)
  set Dp : lBar Y := e.symm ⟨_, hD'S⟩ with hDp
  have hDp3 : Dp ^ 3 = 1 := hcube 1 σ (σ ^ 2) hD'S (one_pow 3) hσ3
    (by rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hσ3, one_pow])
  obtain ⟨d, hdA, hd⟩ := exists_lift_mem hAe hAmax hAL hDp3 (hfix 1 σ (σ ^ 2) hD'S)
  have hPS : g * cycThree * g⁻¹ ∈ slPi true 3 (p ^ f) K := hSL _ (cycThree_mem_slPi hπ)
  set Wb : lBar Y := e.symm ⟨_, hPS⟩ with hWb
  obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective Wb
  have hFr : ∀ a ∈ A, (w₀ : G) * a * (w₀ : G)⁻¹ ∈
      A ⊔ (aschbacherSolvableCore 3 Y).map Y.subtype := by
    intro a ha
    obtain ⟨s, t, hs, ht, hst⟩ := hAmat a ha
    set u : Y := w₀ * Y.normalizerMonoidHom ⟨a, hAL ha⟩ w₀⁻¹ with hu
    have hucoe : (u : G) = (w₀ : G) * a * (w₀ : G)⁻¹ * a⁻¹ := by
      rw [hu, Subgroup.coe_mul, normalizerMonoidHom_apply_coe]
      simp only [Subgroup.coe_inv]
      group
    have hMS : g * diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
      hSL _ (diagUnits_mem_slPi_true (by group) _)
    have huimg : (u : lBar Y) = e.symm ⟨_, hMS⟩ := by
      apply hεinj
      have h1 : (u : lBar Y) = Wb * (barHom Y ⟨a, hAL ha⟩ Wb)⁻¹ := by
        rw [hu, QuotientGroup.mk_mul, ← barHom_mk, QuotientGroup.mk_inv, hw₀, map_inv]
      rw [h1, map_mul, map_inv, hst, hWb, hεsymm, hεsymm]
      calc g * cycThree * g⁻¹ * (g * diagUnits 1 s t * g⁻¹ * (g * cycThree * g⁻¹) *
            (g * diagUnits 1 s t * g⁻¹)⁻¹)⁻¹ =
          g * ((cycThree * diagUnits 1 s t * cycThree⁻¹) * (diagUnits 1 s t)⁻¹) * g⁻¹ := by
            group
        _ = g * diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹ := by
            rw [cycThree_conj_diagUnits, diagUnits_inv, diagUnits_mul, inv_one, mul_one, one_mul]
    have hs3 : (s⁻¹) ^ 3 = 1 := by rw [inv_pow, hs, inv_one]
    have hst3 : (s * t⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hs, ht, inv_one, one_mul]
    obtain ⟨z, hzA, hz⟩ := exists_lift_mem hAe hAmax hAL (hcube _ _ _ hMS ht hs3 hst3)
      (hfix _ _ _ hMS)
    have hzu : ((z⁻¹ * u : Y) : lBar Y) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hz, huimg, inv_mul_cancel]
    have hθ : z⁻¹ * u ∈ aschbacherSolvableCore 3 Y := (QuotientGroup.eq_one_iff _).mp hzu
    have e1 : (w₀ : G) * a * (w₀ : G)⁻¹ = (z : G) * ((z⁻¹ * u : Y) : G) * a := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hucoe]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hzA)
      (Subgroup.mem_sup_right ⟨_, hθ, rfl⟩)) (Subgroup.mem_sup_left ha)
  obtain ⟨t₀, ht₀, hwN⟩ := exists_mem_normalizer_of_conj_mem hA hAL hFr
  obtain ⟨t₀', ht₀', rfl⟩ := ht₀
  set w : Y := t₀' * w₀ with hw
  have hwcoe : (w : G) = (t₀' : G) * w₀ := rfl
  have hwN' : (w : G) ∈ Subgroup.normalizer (A : Set G) := hwN
  have hwimg : (w : lBar Y) = Wb := by
    rw [hw, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ht₀', one_mul, hw₀]
  have hwAY : ∀ y : Y, (y : G) ∈ A → ((w * y * w⁻¹ : Y) : G) ∈ A := fun y hy => by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hwN' y).mp hy
  have hAYB : ∀ y : Y, (y : G) ∈ A → (y : G) ∈ A ⊓ L := fun y hy =>
    mem_inf_of_mem hcfg hC hcY hy y.2
  set β : G := c⁻¹ * ((w : G) * c * (w : G)⁻¹) with hβ
  have hβA : β ∈ A := A.mul_mem (A.inv_mem hcA) ((Subgroup.mem_normalizer_iff.mp hwN' c).mp hcA)
  have hβY : β ∈ Y := by
    have h1 : c⁻¹ * (w : G) * c ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hC.c_norm) (w : G)).mp w.2
      simpa using this
    have e1 : β = c⁻¹ * (w : G) * c * (w : G)⁻¹ := by rw [hβ]; group
    rw [e1]
    exact Y.mul_mem h1 (Y.inv_mem w.2)
  have hβB : β ∈ A ⊓ L := mem_inf_of_mem hcfg hC hcY hβA hβY
  obtain ⟨q, hqN, hqB, hqc⟩ := hcfg.full β hβB
  set x : G := q⁻¹ * (w : G) with hx
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem hqN) hwN'
  have hqinv : ∀ y ∈ A ⊓ L, q⁻¹ * y * q = y := fun y hy => by
    have := hqB y hy
    calc q⁻¹ * y * q = q⁻¹ * (q * y * q⁻¹) * q := by rw [this]
      _ = y := by group
  have hxc : x * c * x⁻¹ = c := by
    have h3 : c = (q⁻¹ * c * q) * β := by
      calc c = q⁻¹ * (q * c * q⁻¹) * q := by group
        _ = q⁻¹ * (c * β) * q := by rw [hqc]
        _ = (q⁻¹ * c * q) * (q⁻¹ * β * q) := by group
        _ = (q⁻¹ * c * q) * β := by rw [hqinv β hβB]
    have h1 : q⁻¹ * c * q = c * β⁻¹ := by
      calc q⁻¹ * c * q = (q⁻¹ * c * q) * β * β⁻¹ := by group
        _ = c * β⁻¹ := by rw [← h3]
    have hwc : (w : G) * c * (w : G)⁻¹ = c * β := by rw [hβ]; group
    calc x * c * x⁻¹ = q⁻¹ * ((w : G) * c * (w : G)⁻¹) * q := by rw [hx]; group
      _ = q⁻¹ * (c * β) * q := by rw [hwc]
      _ = (q⁻¹ * c * q) * (q⁻¹ * β * q) := by group
      _ = c := by rw [h1, hqinv β hβB]; group
  have hxb : x * b * x⁻¹ = b := by
    have hwb : (w : G) * b * (w : G)⁻¹ = b := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hYC w.2), mul_inv_cancel_right]
    calc x * b * x⁻¹ = q⁻¹ * ((w : G) * b * (w : G)⁻¹) * q := by rw [hx]; group
      _ = b := by rw [hwb, hqinv b hC.b_mem]
  have hxj : ∀ j : ℕ, x ^ j * (d : G) * (x ^ j)⁻¹ = ((w ^ j * d * (w ^ j)⁻¹ : Y) : G) ∧
      ((w ^ j * d * (w ^ j)⁻¹ : Y) : G) ∈ A := by
    intro j
    induction j with
    | zero => simp [hdA]
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hmem := hwAY _ ih2
      have e1 : ((w ^ (j + 1) * d * (w ^ (j + 1))⁻¹ : Y) : G) =
          ((w * (w ^ j * d * (w ^ j)⁻¹) * w⁻¹ : Y) : G) := by
        congr 1
        group
      refine ⟨?_, e1 ▸ hmem⟩
      rw [e1]
      calc x ^ (j + 1) * (d : G) * (x ^ (j + 1))⁻¹ = x * (x ^ j * (d : G) * (x ^ j)⁻¹) * x⁻¹ := by
            group
        _ = q⁻¹ * ((w * (w ^ j * d * (w ^ j)⁻¹) * w⁻¹ : Y) : G) * q := by
            rw [ih1, hx]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = _ := hqinv _ (hAYB _ hmem)
  have hWb3 : Wb ^ 3 = 1 := by
    apply hεinj
    rw [map_pow, hWb, hεsymm, map_one, conj_pow]
    have hc3 : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hc3, mul_one, mul_inv_cancel]
  have hw3d : w ^ 3 * d * (w ^ 3)⁻¹ = d := by
    refine eq_of_mk_eq hAe (hxj 3).2 hdA ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
      hwimg, hWb3, one_mul, inv_one, mul_one]
  have hx3d : x ^ 3 * (d : G) * (x ^ 3)⁻¹ = d := by
    rw [(hxj 3).1, hw3d]
  obtain ⟨r, hr, k, hk⟩ := exists_pow_three_part x
  set x₃ : G := x ^ r with hx₃
  have hpow3 : ∀ {y : G}, x ^ 3 * y * (x ^ 3)⁻¹ = y → x₃ * y * x₃⁻¹ = x * y * x⁻¹ := by
    intro y hy
    have hc : Commute (x ^ 3) y := by
      calc x ^ 3 * y = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by group
        _ = y * x ^ 3 := by rw [hy]
    have hr' : r = 3 * (r / 3) + 1 := by omega
    have e1 : x₃ = x * (x ^ 3) ^ (r / 3) := by
      rw [hx₃, ← pow_mul, ← pow_succ', hr']
      congr 1
      omega
    rw [e1]
    have hc' := (hc.pow_left (r / 3)).eq
    calc x * (x ^ 3) ^ (r / 3) * y * (x * (x ^ 3) ^ (r / 3))⁻¹ =
        x * ((x ^ 3) ^ (r / 3) * y) * ((x ^ 3) ^ (r / 3))⁻¹ * x⁻¹ := by group
      _ = x * (y * (x ^ 3) ^ (r / 3)) * ((x ^ 3) ^ (r / 3))⁻¹ * x⁻¹ := by rw [hc']
      _ = x * y * x⁻¹ := by group
  have hx3c : x ^ 3 * c * (x ^ 3)⁻¹ = c := conj_pow_eq_self hxc 3
  have hx₃c : x₃ * c * x₃⁻¹ = c := by rw [hpow3 hx3c, hxc]
  have hx3b : x ^ 3 * b * (x ^ 3)⁻¹ = b := conj_pow_eq_self hxb 3
  have hx₃b : x₃ * b * x₃⁻¹ = b := by rw [hpow3 hx3b, hxb]
  have hx₃d : x₃ * (d : G) * x₃⁻¹ = ((w * d * w⁻¹ : Y) : G) := by
    rw [hpow3 hx3d]
    have := (hxj 1).1
    simpa using this
  have hx₃N : x₃ ∈ Subgroup.normalizer (Y : Set G) := by
    have hZ : IsPGroup 3 (Subgroup.zpowers x₃) := by
      refine IsPGroup.of_card_dvd_pow (n := k) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk
    have hZC : Subgroup.zpowers x₃ ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc x₃ * b = x₃ * b * x₃⁻¹ * x₃ := by group
        _ = b * x₃ := by rw [hx₃b]
    exact hC.three_norm _ hZ hZC (Subgroup.mem_zpowers x₃)
  have hXS : g * diagUnits 1 (σ ^ 2) σ * g⁻¹ ∈ slPi true 3 (p ^ f) K :=
    hSL _ (diagUnits_mem_slPi_true (by rw [one_mul, ← pow_succ, hσ3]) _)
  have hNS : g * negSwap * g⁻¹ ∈ slPi true 3 (p ^ f) K := hSL _ (negSwap_mem_slPi _)
  set Xb : lBar Y := e.symm ⟨_, hXS⟩ with hXb
  set Nb : lBar Y := e.symm ⟨_, hNS⟩ with hNb
  set cb := barHom Y ⟨c, hC.c_norm⟩ with hcb
  have hcfix : ∀ z : lBar Y, cb z = z ↔ yc * ε z = ε z * yc := by
    intro z
    constructor
    · intro h
      have h1 := hyc z
      rw [h] at h1
      change ε z = yc * ε z * yc⁻¹ at h1
      calc yc * ε z = yc * ε z * yc⁻¹ * yc := by group
        _ = ε z * yc := by rw [← h1]
    · intro h
      apply hεinj
      change ((e (cb z) : slPi true 3 (p ^ f) K) : GL (Fin 3) K) = ε z
      rw [hcb, hyc z]
      change yc * ε z * yc⁻¹ = ε z
      rw [h, mul_inv_cancel_right]
  have hycd : g⁻¹ * yc * g = diagUnits lc (lc * σ) (lc * σ) := by
    rw [hgc, scalar_mul_diagUnits_eq]
    rfl
  have hcX : cb Xb = Xb := by
    rw [hcfix, hXb, hεsymm]
    have := conj_frame_eq_of_commute (y := yc) (g := g) (X := diagUnits 1 (σ ^ 2) σ)
      (by rw [hycd, diagUnits_comm])
    calc yc * (g * diagUnits 1 (σ ^ 2) σ * g⁻¹) =
        yc * (g * diagUnits 1 (σ ^ 2) σ * g⁻¹) * yc⁻¹ * yc := by group
      _ = g * diagUnits 1 (σ ^ 2) σ * g⁻¹ * yc := by rw [this]
  have hcN : cb Nb = Nb := by
    rw [hcfix, hNb, hεsymm]
    have hcomm' : (g⁻¹ * yc * g) * negSwap = negSwap * (g⁻¹ * yc * g) := by
      rw [hycd]
      have h1 := negSwap_conj_diagUnits (K := K) lc (lc * σ) (lc * σ)
      calc diagUnits lc (lc * σ) (lc * σ) * negSwap =
          (negSwap * diagUnits lc (lc * σ) (lc * σ) * negSwap⁻¹) * negSwap := by rw [h1]
        _ = negSwap * diagUnits lc (lc * σ) (lc * σ) := by group
    have := conj_frame_eq_of_commute (y := yc) (g := g) (X := negSwap) hcomm'
    calc yc * (g * negSwap * g⁻¹) = yc * (g * negSwap * g⁻¹) * yc⁻¹ * yc := by group
      _ = g * negSwap * g⁻¹ * yc := by rw [this]
  have hDpc : Dp = Xb * Nb * Xb⁻¹ * Nb⁻¹ := by
    apply hεinj
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hDp, hXb, hNb, hεsymm, hεsymm, hεsymm]
    rw [← commutator_diagUnits_negSwap hσ3]
    group
  set φ := barHom Y ⟨x₃, hx₃N⟩ with hφ
  have hφc : ∀ z, cb (φ z) = φ (cb z) := by
    intro z
    have h1 : (⟨c, hC.c_norm⟩ : Subgroup.normalizer (Y : Set G)) * ⟨x₃, hx₃N⟩ =
        ⟨x₃, hx₃N⟩ * ⟨c, hC.c_norm⟩ := by
      apply Subtype.ext
      change c * x₃ = x₃ * c
      calc c * x₃ = x₃ * c * x₃⁻¹ * x₃ := by rw [hx₃c]
        _ = x₃ * c := by group
    have h2 := congrArg (fun φ' : MulAut (lBar Y) => φ' z) (congrArg (barHom Y) h1)
    simpa only [map_mul, MulAut.mul_apply] using h2
  set δ : Fin 3 → K := ![(lc : K), (lc * σ : Kˣ), (lc * σ : Kˣ)] with hδ
  have hδ01 : δ 0 ≠ δ 1 := by
    intro h
    apply hσ1
    have h' : ((lc * 1 : Kˣ) : K) = ((lc * σ : Kˣ) : K) := by simpa [hδ] using h
    exact (mul_left_cancel (Units.ext h')).symm
  have hδ02 : δ 0 ≠ δ 2 := by simpa [hδ] using hδ01
  have hblock : ∀ z, cb z = z → ((g⁻¹ * ε z * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      diagonal δ = diagonal δ * ((g⁻¹ * ε z * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro z hz
    have h1 := (hcfix z).mp hz
    have hgδ : ((g⁻¹ * yc * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ := by
      rw [hycd, coe_diagUnits]
    rw [← hgδ, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc g⁻¹ * ε z * g * (g⁻¹ * yc * g) = g⁻¹ * (ε z * yc) * g := by group
      _ = g⁻¹ * (yc * ε z) * g := by rw [h1]
      _ = g⁻¹ * yc * g * (g⁻¹ * ε z * g) := by group
  have hfixX : cb (φ Xb) = φ Xb := by rw [hφc, hcX]
  have hfixN : cb (φ Nb) = φ Nb := by rw [hφc, hcN]
  have hentry1 := entry_commutator_eq_one hδ01 hδ02 (hblock _ hfixX) (hblock _ hfixN)
  have hφDp : g⁻¹ * ε (φ Dp) * g = (g⁻¹ * ε (φ Xb) * g) * (g⁻¹ * ε (φ Nb) * g) *
      (g⁻¹ * ε (φ Xb) * g)⁻¹ * (g⁻¹ * ε (φ Nb) * g)⁻¹ := by
    rw [hDpc, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    group
  rw [← hφDp] at hentry1
  have hφDp' : φ Dp = Wb * Dp * Wb⁻¹ := by
    rw [← hd, hφ, barHom_mk]
    have h1 : Y.normalizerMonoidHom ⟨x₃, hx₃N⟩ d = w * d * w⁻¹ := by
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe, hx₃d]
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwimg]
  have hfinal : g⁻¹ * ε (φ Dp) * g = diagUnits (σ ^ 2) 1 σ := by
    rw [hφDp', map_mul, map_mul, map_inv, hWb, hDp, hεsymm, hεsymm]
    calc g⁻¹ * (g * cycThree * g⁻¹ * (g * diagUnits 1 σ (σ ^ 2) * g⁻¹) *
          (g * cycThree * g⁻¹)⁻¹) * g = cycThree * diagUnits 1 σ (σ ^ 2) * cycThree⁻¹ := by
          group
      _ = diagUnits (σ ^ 2) 1 σ := cycThree_conj_diagUnits 1 σ (σ ^ 2)
  rw [hfinal, coe_diagUnits, Matrix.diagonal_apply_eq] at hentry1
  exact sq_ne_one_of_cube hσ3 hσ1 (Units.ext (by simpa using hentry1))

end Item2130Res7Proof

end CFSG.RankThree.PartTwo.Sec21
