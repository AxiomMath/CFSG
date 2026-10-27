module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam6
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model
import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
import CFSG.RankThree.PartTwo.Sec12.Hering129KN2
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129C

section Cover

variable {X Q : Type} [Group X] [Group Q]

theorem conj_mul_central {x a : X} (k : X) (ha : ∀ y : X, a * y = y * a) :
    k * (a * x) * k⁻¹ = a * (k * x * k⁻¹) := by
  calc k * (a * x) * k⁻¹ = (k * a) * x * k⁻¹ := by group
    _ = (a * k) * x * k⁻¹ := by rw [← ha k]
    _ = a * (k * x * k⁻¹) := by group

theorem commutator_commute_of_central {m g h a b : X} (ha : ∀ y : X, a * y = y * a)
    (hb : ∀ y : X, b * y = y * b) (hg : g * m * g⁻¹ = a * m) (hh : h * m * h⁻¹ = b * m) :
    g * h * g⁻¹ * h⁻¹ * m = m * (g * h * g⁻¹ * h⁻¹) := by
  have hg' : g⁻¹ * m * g = a⁻¹ * m := by
    have h1 : g⁻¹ * (g * m * g⁻¹) * g = m := by group
    rw [hg] at h1
    have h2 : g⁻¹ * (a * m) * g⁻¹⁻¹ = a * (g⁻¹ * m * g⁻¹⁻¹) := conj_mul_central g⁻¹ ha
    rw [inv_inv] at h2
    rw [h2] at h1
    calc g⁻¹ * m * g = a⁻¹ * (a * (g⁻¹ * m * g)) := by group
      _ = a⁻¹ * m := by rw [h1]
  have hh' : h⁻¹ * m * h = b⁻¹ * m := by
    have h1 : h⁻¹ * (h * m * h⁻¹) * h = m := by group
    rw [hh] at h1
    have h2 : h⁻¹ * (b * m) * h⁻¹⁻¹ = b * (h⁻¹ * m * h⁻¹⁻¹) := conj_mul_central h⁻¹ hb
    rw [inv_inv] at h2
    rw [h2] at h1
    calc h⁻¹ * m * h = b⁻¹ * (b * (h⁻¹ * m * h)) := by group
      _ = b⁻¹ * m := by rw [h1]
  have ha' : ∀ y : X, a⁻¹ * y = y * a⁻¹ := fun y => by
    have := ha y
    calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
      _ = y * a⁻¹ := by group
  have hb' : ∀ y : X, b⁻¹ * y = y * b⁻¹ := fun y => by
    have := hb y
    calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * y) * b⁻¹ := by rw [this]
      _ = y * b⁻¹ := by group
  have key : g * h * g⁻¹ * h⁻¹ * m * (g * h * g⁻¹ * h⁻¹)⁻¹ = m := by
    have e1 : g * h * g⁻¹ * h⁻¹ * m * (g * h * g⁻¹ * h⁻¹)⁻¹ =
        g * (h * (g⁻¹ * (h⁻¹ * m * h) * g) * h⁻¹) * g⁻¹ := by group
    rw [e1, hh']
    have e2 : g⁻¹ * (b⁻¹ * m) * g = b⁻¹ * (g⁻¹ * m * g) := by
      have := conj_mul_central (x := m) g⁻¹ hb'
      rwa [inv_inv] at this
    rw [e2, hg']
    have e3 : h * (b⁻¹ * (a⁻¹ * m)) * h⁻¹ = b⁻¹ * (a⁻¹ * (h * m * h⁻¹)) := by
      rw [conj_mul_central h hb', conj_mul_central h ha']
    rw [e3, hh]
    have e4 : g * (b⁻¹ * (a⁻¹ * (b * m))) * g⁻¹ = a⁻¹ * (g * m * g⁻¹) := by
      have : b⁻¹ * (a⁻¹ * (b * m)) = a⁻¹ * m := by
        calc b⁻¹ * (a⁻¹ * (b * m)) = b⁻¹ * ((a⁻¹ * b) * m) := by simp only [mul_assoc]
          _ = b⁻¹ * ((b * a⁻¹) * m) := by rw [ha' b]
          _ = a⁻¹ * m := by group
      rw [this, conj_mul_central g ha']
    rw [e4, hg]
    group
  calc g * h * g⁻¹ * h⁻¹ * m = g * h * g⁻¹ * h⁻¹ * m * (g * h * g⁻¹ * h⁻¹)⁻¹ *
        (g * h * g⁻¹ * h⁻¹) := by group
    _ = m * (g * h * g⁻¹ * h⁻¹) := by rw [key]

theorem exists_lift_mem_commutator (μ : X →* Q) (hμ : Function.Surjective μ)
    (hker : ∀ g : X, μ g = 1 → g ∈ Subgroup.center X) {c : Q} {J : Subgroup Q}
    (hcJ : c ∈ J) (hJC : J ≤ Subgroup.centralizer ({c} : Set Q)) (hJp : Group.IsPerfect ↥J) :
    ∃ m : X, μ m = c ∧ m ∈ ⁅J.comap μ, J.comap μ⁆ ∧ ⁅J.comap μ, J.comap μ⁆.map μ = J ∧
      (∀ g ∈ J.comap μ, g * m * g⁻¹ * m⁻¹ ∈ Subgroup.center X) ∧
      (∀ u ∈ ⁅J.comap μ, J.comap μ⁆, u * m = m * u) := by
  have hJJ : ⁅J, J⁆ = J := by
    haveI := hJp
    exact Subgroup.commutator_eq_self (H := J)
  have hmap : ⁅J.comap μ, J.comap μ⁆.map μ = J := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hμ, hJJ]
  have hcN : c ∈ ⁅J.comap μ, J.comap μ⁆.map μ := by
    rw [hmap]
    exact hcJ
  obtain ⟨m, hmN, hmc⟩ := Subgroup.mem_map.mp hcN
  have hcen : ∀ g ∈ J.comap μ, g * m * g⁻¹ * m⁻¹ ∈ Subgroup.center X := by
    intro g hg
    apply hker
    have h1 : μ g ∈ J := hg
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hJC h1)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hmc, h2]
    group
  refine ⟨m, hmc, hmN, hmap, hcen, ?_⟩
  have hNC : ⁅J.comap μ, J.comap μ⁆ ≤ Subgroup.centralizer ({m} : Set X) := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    have hga := Subgroup.mem_center_iff.mp (hcen g hg)
    have hhb := Subgroup.mem_center_iff.mp (hcen h hh)
    exact commutator_commute_of_central (a := g * m * g⁻¹ * m⁻¹) (b := h * m * h⁻¹ * m⁻¹)
      (fun y => (hga y).symm) (fun y => (hhb y).symm) (by group) (by group)
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.mp (hNC hu)

theorem false_of_commute (μ : X →* Q) {N : Subgroup X} {J : Subgroup Q} (hN : N.map μ = J)
    (hJp : Group.IsPerfect ↥J) {m : X} (hNm : ∀ u ∈ N, u * m = m * u)
    (hcomm : ∀ u v : X, u * m = m * u → v * m = m * v → u * v = v * u) {c : Q} (hcJ : c ∈ J)
    (hc1 : c ≠ 1) : False := by
  have hNN : ⁅N, N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hcomm v u (hNm v hv) (hNm u hu)
  have hJ0 : ⁅J, J⁆ = ⊥ := by
    rw [← hN, ← Subgroup.map_commutator, hNN, Subgroup.map_bot]
  have hJJ : ⁅J, J⁆ = J := by
    haveI := hJp
    exact Subgroup.commutator_eq_self (H := J)
  rw [hJJ] at hJ0
  rw [hJ0] at hcJ
  exact hc1 (Subgroup.mem_bot.mp hcJ)

end Cover

section SL

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem isSLThreePiAt_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    IsSLThreePiAt ↥(slPi π 3 (p ^ f) K) (p ^ f) := by
  have hfin : Finite K := hK.finite
  cases π with
  | true => exact ⟨K, inferInstance, hfin, Or.inl ⟨hK.card, hq, ⟨MulEquiv.subgroupCongr rfl⟩⟩⟩
  | false => exact ⟨K, inferInstance, hfin, Or.inr ⟨hK.card, hq, ⟨MulEquiv.subgroupCongr rfl⟩⟩⟩

theorem commute_of_cube_eq_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {m : ↥(slPi π 3 (p ^ f) K)} (hm3 : m ^ 3 = 1)
    (hmz : m ∉ Subgroup.center ↥(slPi π 3 (p ^ f) K)) {u v : ↥(slPi π 3 (p ^ f) K)}
    (hu : u * m = m * u) (hv : v * m = m * v) : u * v = v * u := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨g, hg⟩ := Hering129L.exists_conj_to_diagTau hK hq hτ hτ1 hm3 hmz
  have hcent : ∀ w : ↥(slPi π 3 (p ^ f) K), w * m = m * w →
      ((g * w * g⁻¹ : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈
        slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} := by
    intro w hw
    refine Subgroup.mem_inf.mpr ⟨(g * w * g⁻¹).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have : g * w * g⁻¹ * (g * m * g⁻¹) = g * m * g⁻¹ * (g * w * g⁻¹) := by
      calc g * w * g⁻¹ * (g * m * g⁻¹) = g * (w * m) * g⁻¹ := by group
        _ = g * (m * w) * g⁻¹ := by rw [hw]
        _ = g * m * g⁻¹ * (g * w * g⁻¹) := by group
    exact congrArg Subtype.val this
  have hcomm := Hering129KN2.commute_of_mem hK hq hτ hτ1 (hcent u hu) (hcent v hv)
  have h2 : g * u * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * u * g⁻¹) := Subtype.ext hcomm
  have h3 : g * (u * v) * g⁻¹ = g * (v * u) * g⁻¹ := by
    calc g * (u * v) * g⁻¹ = g * u * g⁻¹ * (g * v * g⁻¹) := by group
      _ = g * v * g⁻¹ * (g * u * g⁻¹) := h2
      _ = g * (v * u) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

theorem entry_mul {y g₀ : GL (Fin 3) K} {e : Kˣ} (he1 : (e : K) ≠ 1)
    (hg₀ : g₀⁻¹ * y * g₀ = diagE e) {u v : GL (Fin 3) K} (hu : u * y = y * u) :
    ((g₀⁻¹ * (u * v) * g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      ((g₀⁻¹ * u * g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
        ((g₀⁻¹ * v * g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 := by
  have hAD : (g₀⁻¹ * u * g₀ : GL (Fin 3) K) * diagE e = diagE e * (g₀⁻¹ * u * g₀) := by
    rw [← hg₀]
    calc g₀⁻¹ * u * g₀ * (g₀⁻¹ * y * g₀) = g₀⁻¹ * (u * y) * g₀ := by group
      _ = g₀⁻¹ * (y * u) * g₀ := by rw [hu]
      _ = g₀⁻¹ * y * g₀ * (g₀⁻¹ * u * g₀) := by group
  have key : ∀ M : GL (Fin 3) K, M * diagE e = diagE e * M →
      (M : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    intro M hM
    have h1 := congrArg Units.val hM
    rw [Units.val_mul M (diagE e), Units.val_mul (diagE e) M, coe_diagE] at h1
    have h01 := congrFun (congrFun h1 0) 1
    have h02 := congrFun (congrFun h1 0) 2
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h01 h02
    have e0 : (![(e : K), 1, 1] : Fin 3 → K) 0 = e := by simp
    have e1 : (![(e : K), 1, 1] : Fin 3 → K) 1 = 1 := by simp
    have e2 : (![(e : K), 1, 1] : Fin 3 → K) 2 = 1 := by simp
    rw [e0, e1] at h01
    rw [e0, e2] at h02
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.1 (show ((e : K) - 1) * (M : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 by
        linear_combination (-1 : K) * h01) with h | h
      · exact absurd (sub_eq_zero.1 h) he1
      · exact h
    · rcases mul_eq_zero.1 (show ((e : K) - 1) * (M : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 by
        linear_combination (-1 : K) * h02) with h | h
      · exact absurd (sub_eq_zero.1 h) he1
      · exact h
  obtain ⟨h01, h02⟩ := key _ hAD
  have hsplit : (g₀⁻¹ * (u * v) * g₀ : GL (Fin 3) K) =
      (g₀⁻¹ * u * g₀) * (g₀⁻¹ * v * g₀) := by group
  rw [hsplit, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h01, h02]
  ring

theorem false_of_diagE_case (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {J : Subgroup ↥(slPi π 3 (p ^ f) K)} {m : ↥(slPi π 3 (p ^ f) K)}
    (hJC : ∀ g ∈ J, g * m = m * g) (hmN : m ∈ ⁅J, J⁆) {y g₀ : GL (Fin 3) K} {ξ e : Kˣ}
    (hyx : y = (m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ)
    (he : (e : K) = τ ∨ (e : K) = τ ^ 2) (hg₀ : g₀⁻¹ * y * g₀ = diagE e) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have he3 : (e : K) ^ 3 = 1 := by
    rcases he with h | h <;> rw [h]
    · exact hτ
    · rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have he1 : (e : K) ≠ 1 := by
    rcases he with h | h <;> rw [h]
    · exact hτ1
    · intro h2
      apply hτ1
      calc τ = τ * τ ^ 2 := by rw [h2, mul_one]
        _ = τ ^ 3 := by ring
        _ = 1 := hτ
  have hcomm_y : ∀ u : ↥(slPi π 3 (p ^ f) K), u * m = m * u →
      (u : GL (Fin 3) K) * y = y * (u : GL (Fin 3) K) := by
    intro u hu
    have hu' : (u : GL (Fin 3) K) * (m : GL (Fin 3) K) = (m : GL (Fin 3) K) * (u : GL (Fin 3) K) :=
      congrArg Subtype.val hu
    rw [hyx]
    calc (u : GL (Fin 3) K) * ((m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ)
        = ((u : GL (Fin 3) K) * (m : GL (Fin 3) K)) * GeneralLinearGroup.scalar (Fin 3) ξ := by
          rw [mul_assoc]
      _ = ((m : GL (Fin 3) K) * (u : GL (Fin 3) K)) * GeneralLinearGroup.scalar (Fin 3) ξ := by
          rw [hu']
      _ = (m : GL (Fin 3) K) * ((u : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ) := by
          rw [mul_assoc]
      _ = (m : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) ξ * (u : GL (Fin 3) K)) := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ξ (u : GL (Fin 3) K)).eq]
      _ = ((m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ) * (u : GL (Fin 3) K) := by
          rw [mul_assoc]
  set ent : GL (Fin 3) K → K := fun u =>
    ((g₀⁻¹ * u * g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 with hent
  have ent_one : ent 1 = 1 := by simp [hent]
  have ent_mul : ∀ u v : GL (Fin 3) K, u * y = y * u → ent (u * v) = ent u * ent v :=
    fun u v hu => entry_mul he1 hg₀ hu
  have ent_inv : ∀ u : GL (Fin 3) K, u * y = y * u → ent u⁻¹ * ent u = 1 := by
    intro u hu
    have hu' : u⁻¹ * y = y * u⁻¹ := by
      calc u⁻¹ * y = u⁻¹ * (y * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * y) * u⁻¹ := by rw [hu]
        _ = y * u⁻¹ := by group
    rw [← ent_mul u⁻¹ u hu', inv_mul_cancel, ent_one]
  let Ker : Subgroup ↥(slPi π 3 (p ^ f) K) :=
    { carrier := {u | (u : GL (Fin 3) K) ∈ Subgroup.centralizer {y} ∧ ent (u : GL (Fin 3) K) = 1}
      mul_mem' := by
        rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
        refine ⟨Subgroup.mul_mem _ hu1 hv1, ?_⟩
        show ent ((u : GL (Fin 3) K) * v) = 1
        rw [ent_mul _ _ (Subgroup.mem_centralizer_singleton_iff.mp hu1), hu2, hv2, one_mul]
      one_mem' := ⟨Subgroup.one_mem _, ent_one⟩
      inv_mem' := by
        rintro u ⟨hu1, hu2⟩
        refine ⟨Subgroup.inv_mem _ hu1, ?_⟩
        have := ent_inv _ (Subgroup.mem_centralizer_singleton_iff.mp hu1)
        rw [hu2, mul_one] at this
        exact this }
  have hJJ : ⁅J, J⁆ ≤ Ker := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    have hGc : (g : GL (Fin 3) K) ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm_y g (hJC g hg))
    have hHc : (h : GL (Fin 3) K) ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm_y h (hJC h hh))
    have hG := Subgroup.mem_centralizer_singleton_iff.mp hGc
    have hH := Subgroup.mem_centralizer_singleton_iff.mp hHc
    have hGH : (g : GL (Fin 3) K) * h ∈ Subgroup.centralizer {y} := Subgroup.mul_mem _ hGc hHc
    have hGHG : (g : GL (Fin 3) K) * h * (g : GL (Fin 3) K)⁻¹ ∈ Subgroup.centralizer {y} :=
      Subgroup.mul_mem _ hGH (Subgroup.inv_mem _ hGc)
    have hcomm4 : (g : GL (Fin 3) K) * h * (g : GL (Fin 3) K)⁻¹ * (h : GL (Fin 3) K)⁻¹ ∈
        Subgroup.centralizer {y} := Subgroup.mul_mem _ hGHG (Subgroup.inv_mem _ hHc)
    refine ⟨hcomm4, ?_⟩
    show ent ((g : GL (Fin 3) K) * h * (g : GL (Fin 3) K)⁻¹ * (h : GL (Fin 3) K)⁻¹) = 1
    rw [ent_mul _ _ (Subgroup.mem_centralizer_singleton_iff.mp hGHG),
      ent_mul _ _ (Subgroup.mem_centralizer_singleton_iff.mp hGH), ent_mul _ _ hG]
    have h1 := ent_inv _ hG
    have h2 := ent_inv _ hH
    calc ent (g : GL (Fin 3) K) * ent (h : GL (Fin 3) K) * ent (g : GL (Fin 3) K)⁻¹ *
          ent (h : GL (Fin 3) K)⁻¹
        = (ent (g : GL (Fin 3) K)⁻¹ * ent (g : GL (Fin 3) K)) *
            (ent (h : GL (Fin 3) K)⁻¹ * ent (h : GL (Fin 3) K)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hent_m : ent (m : GL (Fin 3) K) = 1 := (hJJ hmN).2
  have hm_eq : (m : GL (Fin 3) K) = y * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ := by
    rw [hyx, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hconj : g₀⁻¹ * (m : GL (Fin 3) K) * g₀ =
      diagE e * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ := by
    rw [hm_eq]
    have hs : g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ * g₀ =
        GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ := by
      have := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ξ⁻¹ g₀).eq
      calc g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ * g₀
          = g₀⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ * g₀) := by rw [mul_assoc]
        _ = g₀⁻¹ * (g₀ * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹) := by rw [this]
        _ = GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ := by group
    calc g₀⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹) * g₀
        = (g₀⁻¹ * y * g₀) * (g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ * g₀) := by group
      _ = diagE e * GeneralLinearGroup.scalar (Fin 3) ξ⁻¹ := by rw [hg₀, hs]
  have hent_m' : ent (m : GL (Fin 3) K) = (e : K) * ((ξ⁻¹ : Kˣ) : K) := by
    simp only [hent]
    rw [hconj, Units.val_mul, coe_diagE, GeneralLinearGroup.coe_scalar]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  have hdet : GeneralLinearGroup.det y = e := by
    rw [← det_inv_conj g₀ y, hg₀, det_diagE]
  have hdetm : GeneralLinearGroup.det (m : GL (Fin 3) K) = 1 :=
    Units.ext (by
      rw [GeneralLinearGroup.val_det_apply]
      exact ((mem_slPi_iff hπ).mp m.2).2)
  have hdets : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ξ) = ξ ^ 3 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
  have heξ3 : e = ξ ^ 3 := by
    rw [← hdet, hyx, map_mul, hdetm, hdets, one_mul]
  have heξ : (e : K) = ξ := by
    have h1 : (e : K) * ((ξ⁻¹ : Kˣ) : K) = 1 := by rw [← hent_m', hent_m]
    rw [Units.val_inv_eq_inv_val] at h1
    exact (mul_inv_eq_one₀ ξ.ne_zero).1 h1
  apply he1
  have h1 : (ξ : K) ^ 3 = 1 := by rw [← heξ]; exact he3
  have h2 : (e : K) = (ξ : K) ^ 3 := by rw [heξ3, Units.val_pow_eq_pow_val]
  rw [h2, h1]

theorem false_of_cube_ne_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {J : Subgroup ↥(slPi π 3 (p ^ f) K)} {m : ↥(slPi π 3 (p ^ f) K)}
    (hm3 : m ^ 3 ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K)) (hm31 : m ^ 3 ≠ 1)
    (hmz : m ∉ Subgroup.center ↥(slPi π 3 (p ^ f) K))
    (hJcen : ∀ g ∈ J, g * m * g⁻¹ * m⁻¹ ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K))
    (hmN : m ∈ ⁅J, J⁆) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hJC : ∀ g ∈ J, g * m = m * g := by
    intro g hg
    have h := Item128StepsProof.conj_eq_of_mul_inv_mem_center ⟨p ^ f, isSLThreePiAt_slPi hK hq⟩
      hm3 hm31 (hJcen g hg)
    calc g * m = (g * m * g⁻¹) * g := by group
      _ = m * g := by rw [h]
  have hxH : (m : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ m.2
  have hxZ : (m : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hz
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    apply hmz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext
      (commute_of_mem_statedScalars (Subgroup.mem_inf.mp hz).2 (g : GL (Fin 3) K))
  have hx3 : (m : GL (Fin 3) K) ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    obtain ⟨ζ, -, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq hm3
    have hpow : ((m ^ 3 : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = (m : GL (Fin 3) K) ^ 3 := rfl
    rw [← hpow]
    exact Subgroup.mem_inf.mpr ⟨slPi_le_glPi hπ (m ^ 3).2, ⟨ζ, hζ.symm⟩⟩
  have habel : (∀ u v : ↥(slPi π 3 (p ^ f) K), u * m = m * u → v * m = m * v → u * v = v * u) →
      False := by
    intro hcomm
    have hJJ : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcomm v u (hJC v hv) (hJC u hu)
    rw [hJJ, Subgroup.mem_bot] at hmN
    exact hmz (hmN ▸ Subgroup.one_mem _)
  have common : ∀ y z : GL (Fin 3) K, z ∈ zPi π 3 (p ^ f) K → y = (m : GL (Fin 3) K) * z →
      ∃ ξ : Kˣ, y = (m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ ∧
        ∀ u : ↥(slPi π 3 (p ^ f) K), u * m = m * u →
          (u : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} := by
    intro y z hz hyz
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
    have hyx : y = (m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ := by
      rw [hyz, hξ]
    refine ⟨ξ, hyx, fun u hu => ?_⟩
    refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hyx]
    have hu' : (u : GL (Fin 3) K) * (m : GL (Fin 3) K) = (m : GL (Fin 3) K) * (u : GL (Fin 3) K) :=
      congrArg Subtype.val hu
    calc (u : GL (Fin 3) K) * ((m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ)
        = ((u : GL (Fin 3) K) * (m : GL (Fin 3) K)) * GeneralLinearGroup.scalar (Fin 3) ξ := by
          rw [mul_assoc]
      _ = ((m : GL (Fin 3) K) * (u : GL (Fin 3) K)) * GeneralLinearGroup.scalar (Fin 3) ξ := by
          rw [hu']
      _ = (m : GL (Fin 3) K) * ((u : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ) := by
          rw [mul_assoc]
      _ = (m : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) ξ * (u : GL (Fin 3) K)) := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ξ (u : GL (Fin 3) K)).eq]
      _ = ((m : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ξ) * (u : GL (Fin 3) K) := by
          rw [mul_assoc]
  obtain ⟨y, ⟨z, hz, hyz⟩, h1 | h2 | h3⟩ := rank3II_4_10_one hK hq hτ hτ1 hxH hxZ hx3
  ·
    obtain ⟨ξ, hyx, hmem⟩ := common y z hz hyz
    obtain ⟨-, ⟨φ⟩, -⟩ := h1
    refine habel fun u v hu hv => ?_
    have := φ.injective (a₁ := (⟨_, hmem u hu⟩ : ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y})) *
        ⟨_, hmem v hv⟩) (a₂ := ⟨_, hmem v hv⟩ * ⟨_, hmem u hu⟩)
      (by rw [map_mul, map_mul]; exact mul_comm _ _)
    have h2 : (u : GL (Fin 3) K) * v = (v : GL (Fin 3) K) * u := congrArg Subtype.val this
    exact Subtype.ext h2
  ·
    obtain ⟨ξ, hyx, -⟩ := common y z hz hyz
    obtain ⟨⟨g₀, -, e, he, hg₀⟩, -, -⟩ := h2
    exact false_of_diagE_case hK hτ hτ1 hJC hmN hyx he hg₀
  ·
    obtain ⟨ξ, hyx, hmem⟩ := common y z hz hyz
    obtain ⟨-, -, -, hcyc, -⟩ := h3
    refine habel fun u v hu hv => ?_
    letI := hcyc.commGroup
    have := mul_comm (⟨_, hmem u hu⟩ : ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}))
      ⟨_, hmem v hv⟩
    have h2 : (u : GL (Fin 3) K) * v = (v : GL (Fin 3) K) * u := congrArg Subtype.val this
    exact Subtype.ext h2

theorem false_of_slPi_cover (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {Q : Type} [Group Q]
    (μ : ↥(slPi π 3 (p ^ f) K) →* Q) (hμ : Function.Surjective μ)
    (hker : ∀ g, μ g = 1 → g ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K)) {c : Q} (hc3 : c ^ 3 = 1)
    (hcZ : c ∉ Subgroup.center Q) {J : Subgroup Q} (hcJ : c ∈ J)
    (hJC : J ≤ Subgroup.centralizer ({c} : Set Q)) (hJp : Group.IsPerfect ↥J) : False := by
  obtain ⟨m, hmc, hmN, hmap, hcen, hNm⟩ := exists_lift_mem_commutator μ hμ hker hcJ hJC hJp
  have hmz : m ∉ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
    intro hm
    apply hcZ
    rw [← hmc, Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hμ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hm x]
  have hc1 : c ≠ 1 := fun h => hcZ (h ▸ Subgroup.one_mem _)
  have hm3 : m ^ 3 ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) :=
    hker _ (by rw [map_pow, hmc, hc3])
  by_cases hm31 : m ^ 3 = 1
  · exact false_of_commute μ hmap hJp hNm
      (fun u v hu hv => commute_of_cube_eq_one hK hq hm31 hmz hu hv) hcJ hc1
  · exact false_of_cube_ne_one hK hq hm3 hm31 hmz hcen hmN

theorem exists_lmodel_gen {T : Type} [Group T] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : IsoLThreePi T p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      Nonempty (Sec15.KS1424.LModel π p e K T) := by
  rcases h with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField p e, inferInstance, ⟨Fact.out, he, ?_⟩, hq3,
      ⟨Sec15.KS1424.LModel.ofEquiv
        (φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card p e (by omega)]
    rfl
  · refine ⟨false, GaloisField p (2 * e), inferInstance, ⟨Fact.out, he, ?_⟩, hq3,
      ⟨Sec15.KS1424.LModel.ofEquiv
        (φ.trans (MulEquiv.subgroupCongr (projSU_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card p (2 * e) (by omega)]
    change p ^ (2 * e) = (p ^ e) ^ 2
    rw [← pow_mul, mul_comm]

end SL

section Census

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank in
theorem census_false_of_pi (hD : Census129 c a I X f) (hπ : IsSLThreePiAny Q) : False := by
  have hc3 := c_pow_three hD
  have hcZ := c_not_mem_center hD
  rcases hπ with ⟨q, hq⟩ | ⟨p, e, hp, he, hiso⟩
  · obtain ⟨π, p, f, K, _, hK, hq3, -, ⟨φ⟩⟩ := Item128StepsProof.exists_model hq
    refine false_of_slPi_cover hK hq3 φ.symm.toMonoidHom φ.symm.surjective (fun g hg => ?_) hc3
      hcZ hD.c_mem hD.le_centralizer hD.isPerfect
    have hg1 : g = 1 := φ.symm.injective (hg.trans (map_one _).symm)
    rw [hg1]
    exact Subgroup.one_mem _
  · obtain ⟨π, K, _, hK, hq3, ⟨M⟩⟩ := exists_lmodel_gen he hiso
    refine false_of_slPi_cover hK hq3 M.μ M.surjective (fun g hg => ?_) hc3 hcZ hD.c_mem
      hD.le_centralizer hD.isPerfect
    have hs := (M.ker_iff g).1 hg
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (commute_of_mem_statedScalars hs (h : GL (Fin 3) K))

end Census

theorem kFCensus46TwoPi_holds : KFCensus46TwoPi := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exact (census_false_of_pi hD hQ.2).elim

theorem kFCensus46SixL3Pi_holds : KFCensus46SixL3Pi := by
  intro Q Lb _ _ _ c a I X f hQ hD
  obtain ⟨n, hn, -, hπ⟩ := hQ
  exact (census_false_of_pi hD hπ).elim

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
