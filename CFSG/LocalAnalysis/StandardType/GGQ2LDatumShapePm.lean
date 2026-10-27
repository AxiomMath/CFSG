module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLDatumWeyl
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
import CFSG.LocalAnalysis.StandardType.GGQ2PmWHeartA
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreRefl
import CFSG.LocalAnalysis.StandardType.GGForkClassify
import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7

public section

namespace CFSG.StandardType

open CFSG Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQ2LDatum.cartan_ker_of_root_comb {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u) (κ : M.Λ → ZMod p)
    (h : ∀ i, M.root i (∑ j, κ j • M.coroot j) = 0) (i : M.Λ) :
    ∑ j, (M.cartan i j : ZMod p) * κ j = 0 := by
  rw [← h i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, M.pairing, smul_eq_mul, mul_comm]

theorem GGQ2LDatum.exists_cartan_ker_of_not_linearIndependent {p : ℕ} [Fact p.Prime] {G : Type}
    [Group G] {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u)
    (h : ¬ LinearIndependent (ZMod p) M.coroot) :
    ∃ κ : M.Λ → ZMod p, κ ≠ 0 ∧ ∀ i, ∑ j, (M.cartan i j : ZMod p) * κ j = 0 := by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
  exact ⟨g, fun h0 => hi (congrFun h0 i),
    fun i => M.cartan_ker_of_root_comb g (fun i => by rw [hg, map_zero]) i⟩

theorem GGQ2LDatum.not_linearIndependent_of_finrank_succ {p : ℕ} [Fact p.Prime] {G : Type}
    [Group G] {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u)
    (h : finrank (ZMod p) M.coSpan + 1 = Fintype.card M.Λ) :
    ¬ LinearIndependent (ZMod p) M.coroot := by
  intro hLI
  have hco : Module.finrank (ZMod p) M.coSpan = Fintype.card M.Λ :=
    finrank_span_eq_card hLI
  omega

theorem GGQ2LDatum.exists_cartan_ker_of_xV_mem {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (hx0 : M.xV ≠ 0) (hmem : M.xV ∈ M.coSpan) :
    ∃ κ : M.Λ → ZMod 3, κ ≠ 0 ∧ ∀ i, ∑ j, (M.cartan i j : ZMod 3) * κ j = 0 := by
  rw [GGQ2LDatum.coSpan] at hmem
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3) (v := M.coroot)).mp hmem
  refine ⟨c, ?_, fun i => M.cartan_ker_of_root_comb c (fun i => ?_) i⟩
  · intro h0
    exact hx0 (by rw [← hc, h0]; simp)
  · rw [hc, GGQ2LDatum.root_xV]

theorem GGQ2LDatum.pmW_of_shape {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (hsh : M.Shape) (hx0 : M.xV ≠ 0)
    (hinner : M.ShapeFull → ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 →
      ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ),
        (∀ i j, M.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀)
    (hheart : M.ShapeB → ∃ r, 4 ≤ r ∧ ∃ e : Fin r ≃ M.Λ,
      ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j)
    (u₀ : M.toWDatum.V) (hu0 : u₀ ≠ 0)
    (hfix : ∀ v : M.toWDatum.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {u₀})
    (hdim : finrank (ZMod 3) M.toWDatum.V ≤ Fintype.card M.toWDatum.Λ + 1)
    (h4 : 4 ≤ finrank (ZMod 3) M.toWDatum.V) (hTF : TransvectionFree M.toWDatum.weyl)
    (T : M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V)
    (hT : T ∈ Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V))) :
    ∃ w ∈ M.toWDatum.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.toWDatum.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u₀} := by
  classical
  have hcard : 3 ≤ Fintype.card M.toWDatum.Λ := by omega
  rcases hsh with hF | hA | hB | hC | hD
  · by_cases hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0
    · obtain ⟨n, C₀, e, hC₀, hW⟩ := hinner hF hdet
      exact M.toWDatum.pmW_of_det u₀ hfix hcard hdet C₀ e hC₀ hW T hT
    · have hdet0 : ((M.cartan.det : ℤ) : ZMod 3) = 0 := not_ne_iff.mp hdet
      have hker : ∃ κ : M.Λ → ZMod 3, κ ≠ 0 ∧
          ∀ i : M.Λ, ∑ j : M.Λ, (M.cartan i j : ZMod 3) * κ j = 0 := by
        have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix M.cartan).det = 0 := by
          rw [← RingHom.map_det]
          exact hdet0
        obtain ⟨κ, hκ0, hκ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
        exact ⟨κ, hκ0, fun i => by simpa [Matrix.mulVec, dotProduct] using congrFun hκ i⟩
      exact M.toWDatum.pmW_of_ker u₀ hu0 hfix hker hdim h4 hTF (Or.inl hF.2.1) T hT
  · obtain ⟨κ, hκ0, hκ⟩ := M.exists_cartan_ker_of_xV_mem hx0 hA.2.2.1
    exact M.toWDatum.pmW_of_ker u₀ hu0 hfix ⟨κ, hκ0, hκ⟩ hdim h4 hTF (Or.inl hA.2.1) T hT
  · obtain ⟨r, hr, e, hC₀⟩ := hheart hB
    have hcru : Fintype.card M.Λ = r := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    have hdimr : Module.finrank (ZMod 3) M.toWDatum.V = r := by
      show Module.finrank (ZMod 3) M.V = r
      rw [ggQ2LD_dim_heart M (Or.inl hB), hcru]
    have hdep : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range M.toWDatum.coroot)) + 1 = r := by
      rw [← hcru]
      exact hB.2.1
    exact M.toWDatum.pmW_of_heartA hr e hC₀ hdimr hdep u₀ hu0 hfix T hT
  · have hker := M.exists_cartan_ker_of_not_linearIndependent
      (M.not_linearIndependent_of_finrank_succ hC.2.1)
    exact M.toWDatum.pmW_of_ker u₀ hu0 hfix hker hdim h4 hTF
      (Or.inr hC.2.2.2.1) T hT
  · have hmem : M.xV ∈ M.coSpan := by
      rw [hD.2.2]
      exact Submodule.mem_top
    obtain ⟨κ, hκ0, hκ⟩ := M.exists_cartan_ker_of_xV_mem hx0 hmem
    exact M.toWDatum.pmW_of_ker u₀ hu0 hfix ⟨κ, hκ0, hκ⟩ hdim h4 hTF (Or.inl hD.2.1) T hT

theorem ggQ2_weylInner_of_odd {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h5 : 5 ≤ Fintype.card Λ) (hodd : Odd (Fintype.card Λ)) :
    ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ Λ),
      (∀ i j, C (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀ := by
  rcases ggIntCartan_models hM hC with
    ⟨n, e, hn, hA | ⟨hn2, hB | hC₀⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4 | hF4t⟩ | ⟨e, hG2 | hG2t⟩
  · have hcard : Fintype.card Λ = n := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    exact ⟨n, CartanMatrix.A n, e, hA, ggQ2WeylInner_A (by omega)⟩
  · have hcard : Fintype.card Λ = n := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    exact ⟨n, CartanMatrix.B n, e, hB, ggQ2WeylInner_B (by omega)⟩
  · have hcard : Fintype.card Λ = n := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    exact ⟨n, CartanMatrix.C n, e, hC₀, ggQ2WeylInner_C (by omega)⟩
  · have hcard : Fintype.card Λ = n := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    have hoddn : Odd n := by rw [← hcard]; exact hodd
    exact ⟨n, CartanMatrix.D n, e, hD, ggQ2WeylInner_D_odd (by omega) hoddn⟩
  · have hcard : Fintype.card Λ = 6 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    rw [hcard] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · exact ⟨7, CartanMatrix.E 7, e, hE7, ggQ2WeylInner_E7⟩
  · have hcard : Fintype.card Λ = 8 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    rw [hcard] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · have hcard : Fintype.card Λ = 4 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    omega
  · have hcard : Fintype.card Λ = 4 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    omega
  · have hcard : Fintype.card Λ = 2 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    omega
  · have hcard : Fintype.card Λ = 2 := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    omega

theorem GGQ2LDatum.heart_cartan_A {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (hB : M.ShapeB) (h4 : 4 ≤ Fintype.card M.Λ)
    (h6 : Fintype.card M.Λ ≠ 6) :
    ∃ r, 4 ≤ r ∧ ∃ e : Fin r ≃ M.Λ, ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j := by
  obtain ⟨κ, hκ0, hκ⟩ := M.exists_cartan_ker_of_not_linearIndependent
    (M.not_linearIndependent_of_finrank_succ hB.2.1)
  rcases ggIntCartan_A_or_E6_of_nonzero_kernel M.isWeyl M.isCartan (p := 3) (by decide)
      ⟨κ, hκ0, hκ⟩ with ⟨n, e, hn, hdiv, hA⟩ | ⟨-, e, hE6⟩
  · have hcard : Fintype.card M.Λ = n := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
    exact ⟨n, by omega, e, hA⟩
  · exfalso
    apply h6
    rw [Fintype.card_congr e.symm, Fintype.card_fin]

theorem GGQ2LDatum.inner_of_even {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (hev : Even (finrank (ZMod 3) M.V))
    (h6 : 6 ≤ finrank (ZMod 3) M.V) :
    M.ShapeFull → ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 →
      ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ),
        (∀ i j, M.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀ := by
  intro hF hdet
  have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
    ggQ2LD_dim_nonheart M (Or.inl hF)
  have hEven : Even (Fintype.card M.Λ + 1) := by
    rw [← hdim]
    exact hev
  have hodd : Odd (Fintype.card M.Λ) :=
    Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hEven)
  exact ggQ2_weylInner_of_odd M.isWeyl M.isCartan (by omega) hodd

theorem GGQ2LDatum.heartA_of_dim {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (h4 : 4 ≤ finrank (ZMod 3) M.V)
    (h6 : finrank (ZMod 3) M.V ≠ 6) :
    M.ShapeB → ∃ r, 4 ≤ r ∧ ∃ e : Fin r ≃ M.Λ,
      ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j := by
  intro hB
  have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
    ggQ2LD_dim_heart M (Or.inl hB)
  have h6' : Fintype.card M.Λ ≠ 6 := by
    intro h
    exact h6 (by rw [hdim, h])
  exact M.heart_cartan_A hB (by omega) h6'

end CFSG.StandardType

end
