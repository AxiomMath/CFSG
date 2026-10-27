module

public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec83W1_card_le_of_comm (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hWQ : Sec8W1 M Q Z B t r ≤ Q) (hZW : Z ≤ Sec8W1 M Q Z B t r)
    (hcomm : ∀ x ∈ Sec8W1 M Q Z B t r, ∀ y ∈ Sec8W1 M Q Z B t r, x * y = y * x) :
    Nat.card ↥(Sec8W1 M Q Z B t r) ≤ Nat.card Z ^ (n + 1) := by
  classical
  obtain ⟨K, iK, iF, γ, M₀, hKcard, -, hγinj, -, -, -⟩ := stroth_globalModel hc.hyp
  letI := iK
  letI := iF
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hqpos : 0 < Nat.card Z := by omega
  have hZV : Z ≤ Sec8V1 M Q Z B t r :=
    sec39_Z_le_Vt.trans (le_inf le_sup_right le_sup_right)
  have hVQ : Sec8V1 M Q Z B t r ≤ Q := hVW.trans hWQ
  have hπ1 : M₀.π (1 : G) = 0 := (M₀.π_ker 1 Q.one_mem).mpr Z.one_mem
  let πQ : ↥Q →* Multiplicative M₀.E :=
    { toFun := fun x => Multiplicative.ofAdd (M₀.π (x : G))
      map_one' := by
        show Multiplicative.ofAdd (M₀.π ((1 : ↥Q) : G)) = 1
        rw [Subgroup.coe_one, hπ1]
        rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (M₀.π ((x * y : ↥Q) : G)) =
          Multiplicative.ofAdd (M₀.π (x : G)) * Multiplicative.ofAdd (M₀.π (y : G))
        rw [Subgroup.coe_mul, M₀.π_mul (x : G) x.2 (y : G) y.2]
        rfl }
  have hπQker : πQ.ker = Z.subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      change Multiplicative.ofAdd (M₀.π (x : G)) = 1 at h
      rw [ofAdd_eq_one] at h
      exact (M₀.π_ker (x : G) x.2).mp h
    · intro h
      change Multiplicative.ofAdd (M₀.π (x : G)) = 1
      rw [ofAdd_eq_one]
      exact (M₀.π_ker (x : G) x.2).mpr h
  have hπQrange : πQ.range = ⊤ := by
    ext y
    constructor
    · intro _; exact Subgroup.mem_top y
    · intro _
      obtain ⟨x, hxQ, hxy⟩ := M₀.π_surj (Multiplicative.toAdd y)
      refine ⟨⟨x, hxQ⟩, ?_⟩
      show Multiplicative.ofAdd (M₀.π x) = y
      rw [hxy]
      exact ofAdd_toAdd y
  have hEmult : Nat.card (Multiplicative M₀.E) = Nat.card M₀.E :=
    Nat.card_congr Multiplicative.toAdd
  have hZkerQ : Nat.card ↥(Z.subgroupOf Q) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.Z_le_Q).toEquiv
  have hQcardZ : Nat.card Z * Nat.card M₀.E = Nat.card ↥Q := by
    have h := Subgroup.card_ker_mul_card_range πQ
    rw [hπQker, hπQrange, Subgroup.card_top, hEmult, hZkerQ] at h
    exact h
  have hEcard : Nat.card M₀.E = Nat.card Z ^ (2 * n) := by
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc Nat.card Z * Nat.card M₀.E = Nat.card ↥Q := hQcardZ
      _ = Nat.card Z ^ (2 * n + 1) := hs.width
      _ = Nat.card Z * Nat.card Z ^ (2 * n) := by ring
  have hEpow : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E :=
    Module.natCard_eq_pow_finrank (K := K) (V := M₀.E)
  have hfinE : Module.finrank K M₀.E = 2 * n := by
    have h : Nat.card Z ^ Module.finrank K M₀.E = Nat.card Z ^ (2 * n) := by
      calc Nat.card Z ^ Module.finrank K M₀.E = Nat.card K ^ Module.finrank K M₀.E := by
            rw [hKcard]
        _ = Nat.card M₀.E := hEpow.symm
        _ = Nat.card Z ^ (2 * n) := hEcard
    exact Nat.pow_right_injective hq2 h
  let S : Submodule K M₀.E :=
    Submodule.span K (M₀.π '' (Sec8V1 M Q Z B t r : Set G))
  let U : Submodule K M₀.E := M₀.B.orthogonal S
  have hW1eqU : M₀.π '' (Sec8W1 M Q Z B t r : Set G) = (U : Set M₀.E) := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      change M₀.π x ∈ M₀.B.orthogonal S
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro s hsS
      refine Submodule.span_induction (p := fun s _ => M₀.B s (M₀.π x) = 0) ?_ ?_ ?_ ?_ hsS
      · rintro _ ⟨v, hv, rfl⟩
        have hvx : v * x = x * v := Subgroup.mem_centralizer_iff.mp hx.2 v hv
        have hcommvx : ⁅v, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hvx
        have hγ1 : γ 1 = 0 := by
          have hsq := M₀.sq_eq (1 : G) Q.one_mem
          rw [one_pow, hπ1] at hsq
          rw [hsq]
          have h := M₀.Qf_smul (0 : K) (0 : M₀.E)
          simpa using h
        rw [← M₀.comm_eq v (hVQ hv) x (hWQ hx), hcommvx, hγ1]
      · simp
      · intro a b ha hb ha' hb'
        simp [ha', hb']
      · intro c a ha ha'
        simp [ha']
    · intro he
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      change M₀.π x ∈ M₀.B.orthogonal S at he
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
      refine ⟨x, ?_, rfl⟩
      refine ⟨hxQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      have hvS : M₀.π v ∈ S := Submodule.subset_span ⟨v, hv, rfl⟩
      have hB : M₀.B (M₀.π v) (M₀.π x) = 0 := he _ hvS
      have hcommvx : ⁅v, x⁆ = 1 := by
        apply hγinj ⁅v, x⁆ (M₀.comm_mem v (hVQ hv) x hxQ)
        rw [M₀.comm_eq v (hVQ hv) x hxQ, hB]
      exact commutatorElement_eq_one_iff_mul_comm.mp hcommvx
  have hiso : ∀ e ∈ U, ∀ f ∈ U, M₀.B e f = 0 := by
    intro e he f hf
    have heW : e ∈ M₀.π '' (Sec8W1 M Q Z B t r : Set G) := by
      rw [hW1eqU]; exact he
    have hfW : f ∈ M₀.π '' (Sec8W1 M Q Z B t r : Set G) := by
      rw [hW1eqU]; exact hf
    obtain ⟨x, hx, rfl⟩ := heW
    obtain ⟨y, hy, rfl⟩ := hfW
    have hxy : ⁅x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x hx y hy)
    have hγ1 : γ 1 = 0 := by
      have hsq := M₀.sq_eq (1 : G) Q.one_mem
      rw [one_pow, hπ1] at hsq
      rw [hsq]
      have h := M₀.Qf_smul (0 : K) (0 : M₀.E)
      simpa using h
    rw [← M₀.comm_eq x (hWQ hx) y (hWQ hy), hxy, hγ1]
  have hBalt : M₀.B.IsAlt := M₀.alt
  have hBnd : M₀.B.Nondegenerate := by
    refine ⟨M₀.nondeg, ?_⟩
    intro y hy
    apply M₀.nondeg y
    intro f
    rw [← hBalt.neg_eq f y, hy f, neg_zero]
  have horth : U ≤ M₀.B.orthogonal U := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro f hf
    exact hiso f hf e he
  have hdimU : 2 * Module.finrank K ↥U ≤ Module.finrank K M₀.E := by
    have h1 : Module.finrank K ↥U ≤ Module.finrank K ↥(M₀.B.orthogonal U) :=
      Submodule.finrank_mono horth
    have h2 : Module.finrank K ↥(M₀.B.orthogonal U) =
        Module.finrank K M₀.E - Module.finrank K ↥U :=
      LinearMap.BilinForm.finrank_orthogonal hBnd U
    omega
  have hfinU : Module.finrank K ↥U ≤ n := by omega
  let piW : ↥(Sec8W1 M Q Z B t r) →* Multiplicative M₀.E :=
    πQ.comp (Subgroup.inclusion hWQ)
  have hpiWker : piW.ker = Z.subgroupOf (Sec8W1 M Q Z B t r) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : M₀.π (x : G) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [piW, πQ] using this
      exact (M₀.π_ker (x : G) (hWQ x.2)).mp h'
    · intro h
      have h' : M₀.π (x : G) = 0 := (M₀.π_ker (x : G) (hWQ x.2)).mpr h
      show Multiplicative.ofAdd (M₀.π (x : G)) = 1
      rw [h']
      rfl
  have hUcard : Nat.card ↥piW.range = Nat.card ↥U := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd ?_)
    intro x
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := hx
      have hxπ : Multiplicative.toAdd x = M₀.π (w : G) := by
        rw [← hw]
        simp [piW, πQ]
      rw [hxπ]
      change M₀.π (w : G) ∈ (U : Set M₀.E)
      rw [← hW1eqU]
      exact ⟨w, w.2, rfl⟩
    · intro hx
      change Multiplicative.toAdd x ∈ (U : Set M₀.E) at hx
      rw [← hW1eqU] at hx
      obtain ⟨w, hw, hwx⟩ := hx
      refine ⟨⟨w, hw⟩, ?_⟩
      show Multiplicative.ofAdd (M₀.π w) = x
      rw [hwx]
      exact ofAdd_toAdd x
  have hkerCard : Nat.card ↥(Z.subgroupOf (Sec8W1 M Q Z B t r)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hWcard : Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card Z * Nat.card ↥U := by
    have h := Subgroup.card_ker_mul_card_range piW
    rw [hpiWker, hkerCard, hUcard] at h
    exact h.symm
  have hUpow : Nat.card ↥U = Nat.card K ^ Module.finrank K ↥U :=
    Module.natCard_eq_pow_finrank (K := K) (V := ↥U)
  calc Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card Z * Nat.card ↥U := hWcard
    _ = Nat.card Z * Nat.card K ^ Module.finrank K ↥U := by rw [hUpow]
    _ = Nat.card Z * Nat.card Z ^ Module.finrank K ↥U := by rw [hKcard]
    _ ≤ Nat.card Z * Nat.card Z ^ n :=
        Nat.mul_le_mul_left (Nat.card Z) (Nat.pow_le_pow_right hqpos hfinU)
    _ = Nat.card Z ^ (n + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

end CFSG.RankThree.GF2n.Stroth80
