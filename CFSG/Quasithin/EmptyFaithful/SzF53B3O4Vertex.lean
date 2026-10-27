module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3OrthDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53MNat
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EAlg
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B3.NoEO

variable {G : Type} [Group G]

@[expose] def genVec (i : Fin 4) : orth.W :=
  ⟨Multiplicative.ofAdd (fun j : Fin 5 => if j = 0 ∨ j = i.succ then (1 : ZMod 2) else 0),
    G6.mem_coreMod.mpr (by revert i; decide)⟩

theorem genVec_span : ∀ w : orth.W, ∃ a b c d : Fin 2,
    w = genVec 0 ^ (a : ℕ) * genVec 1 ^ (b : ℕ) * genVec 2 ^ (c : ℕ) * genVec 3 ^ (d : ℕ) := by
  decide +kernel

theorem exists_gens_of_isOrthSec {F Z V : Subgroup G} (h : IsOrthSec F Z V) :
    ∃ x : Fin 4 → G, (∀ i, x i ∈ V) ∧ ∀ v ∈ V, ∃ a b c d : ℕ,
      v * (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d)⁻¹ ∈ Z := by
  obtain ⟨hn, θ, β, -, -, hsd⟩ := h
  choose y hy using fun i : Fin 4 => QuotientGroup.mk_surjective (β (genVec i))
  refine ⟨fun i => (y i : G), fun i => (y i).2, fun v hv => ?_⟩
  obtain ⟨w, hw⟩ := hsd.surj (QuotientGroup.mk (⟨v, hv⟩ : ↥V))
  obtain ⟨a, b, c, d, rfl⟩ := genVec_span w
  refine ⟨a, b, c, d, ?_⟩
  have hmk : (QuotientGroup.mk (y 0 ^ (a : ℕ) * y 1 ^ (b : ℕ) * y 2 ^ (c : ℕ) * y 3 ^ (d : ℕ)) :
      ↥V ⧸ Z.subgroupOf V) = QuotientGroup.mk ⟨v, hv⟩ := by
    rw [← hw]
    simp only [map_mul, map_pow, ← hy]
    rfl
  have := (mk_eq_iff_mem (L := Z) (X := V)).mp hmk
  simpa using this

structure OrthVertex (H V Z : Subgroup G) : Prop where
  V_le_Q : V ≤ pCoreOf 2 H
  normV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V
  comm_V : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  central : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z
  sq_Z : ∀ z ∈ Z, z * z = 1
  Z_le_V : Z ≤ V
  comm_Q : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ V, ⁅q, x⁆ ∈ Z
  card_Z : Nat.card Z = 2
  orth : IsOrthSec H Z V

namespace OrthVertex

variable {H V Z : Subgroup G}

theorem toPairing (hF : OrthVertex H V Z) : NoE.Pairing H (pCoreOf 2 H) V Z :=
  ⟨⟨pCoreOf_le 2 H, fun _ hh e he =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) e).mp he,
    hF.normV, hF.comm_V, hF.central, hF.sq_Z⟩, hF.comm_Q⟩

@[expose] def pairHom (hF : OrthVertex H V Z) (x : Fin 4 → G) (hx : ∀ i, x i ∈ V) :
    ↥(pCoreOf 2 H) →* (Fin 4 → ↥Z) where
  toFun q i := ⟨⁅(q : G), x i⁆, hF.comm_Q _ q.2 _ (hx i)⟩
  map_one' := by
    funext i
    apply Subtype.ext
    simp [commutatorElement_def]
  map_mul' q q' := by
    funext i
    apply Subtype.ext
    show ⁅((q * q' : ↥(pCoreOf 2 H)) : G), x i⁆ = ⁅(q : G), x i⁆ * ⁅(q' : G), x i⁆
    rw [Subgroup.coe_mul, hF.toPairing.pair_mul_left q.2 q'.2 (hx i)]
    exact hF.comm_V _ (hF.Z_le_V (hF.comm_Q _ q'.2 _ (hx i))) _
      (hF.Z_le_V (hF.comm_Q _ q.2 _ (hx i)))

theorem relIndex_le_sixteen (hF : OrthVertex H V Z) :
    (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex (pCoreOf 2 H) ≤ 16 := by
  obtain ⟨x, hx, hspan⟩ := exists_gens_of_isOrthSec hF.orth
  have hker : (hF.pairHom x hx).ker ≤
      (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf (pCoreOf 2 H) := by
    intro q hq
    have hc : ∀ i, Commute (q : G) (x i) := fun i => by
      have h2 : ⁅(q : G), x i⁆ = 1 := congrArg Subtype.val (congrFun hq i)
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    obtain ⟨a, b, c, d, hz⟩ := hspan v hv
    have hcP : Commute (q : G) (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d) :=
      ((((hc 0).pow_right a).mul_right ((hc 1).pow_right b)).mul_right
        ((hc 2).pow_right c)).mul_right ((hc 3).pow_right d)
    have hcz : Commute (q : G) (v * (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d)⁻¹) := by
      have h1 := hF.central _ hz q (pCoreOf_le 2 H q.2)
      generalize (q : G) = g at h1 ⊢
      generalize v * (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d)⁻¹ = w at h1 ⊢
      refine (?_ : g * w = w * g)
      calc g * w = (g * w * g⁻¹) * g := by group
        _ = w * g := by rw [h1]
    have hv' : v = (v * (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d)⁻¹) *
        (x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d) := by group
    have hcv : Commute (q : G) v := by
      rw [hv']
      exact hcz.mul_right hcP
    exact hcv.eq.symm
  have h1 : (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex (pCoreOf 2 H) ∣
      Nat.card (hF.pairHom x hx).range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  have h2 : Nat.card (hF.pairHom x hx).range ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card (hF.pairHom x hx).range
    rwa [Nat.card_fun, hF.card_Z, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this
  exact Nat.le_of_dvd (by norm_num) (h1.trans h2)

theorem of_geometry [Finite G] {M S : Subgroup G} (hB : B3FactsO H M S) (hBl : B3Block H M S)
    (hC1 : OrthC1 H M S) {β : Geo H M} (hβ : vtype β = false) (hst : stab β = H) :
    OrthVertex H (Vn β) (Zv β) := by
  have hA : F53Amalgam H M S := hB.amalgam
  have hQ : Qv β = pCoreOf 2 H := by unfold Qv; rw [hst]
  have hVQ : Vn β ≤ Qv β := hBl.vn_le_qv β β (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)
  have hnormV : H ≤ Subgroup.normalizer (Vn β : Set G) := by
    have := stab_le_normalizer_Vn (H := H) (M := M) β
    rw [hst] at this
    exact this
  have hcentral : ∀ z ∈ Zv β, ∀ h ∈ H, h * z * h⁻¹ = z := by
    intro z hz h hh
    have hzc := hB.central β hβ hz
    rw [hst] at hzc
    have h1 := Subgroup.mem_centralizer_iff.mp hzc.2 h hh
    calc h * z * h⁻¹ = z * h * h⁻¹ := by rw [h1]
      _ = z := by group
  have hZV : Zv β ≤ Vn β := by
    obtain ⟨μ, hμ⟩ := exists_adj β
    exact (hBl.zv_le_zv β μ hβ hμ).trans (le_iSup₂_of_le
      (f := fun (μ' : Geo H M) (_ : μ' ∈ nbrs β) => Zv μ') μ (show μ ∈ nbrs β from hμ) le_rfl)
  refine ⟨?_, ?_, ?_, hcentral, ?_, hZV, ?_, hB.card_two β hβ, ?_⟩
  · rw [← hQ]; exact hVQ
  · intro h hh v hv
    exact (Subgroup.mem_normalizer_iff.mp (hnormV hh) v).mp hv
  · exact fun x hx y hy => isElemAbelian_comm (hBl.elemAbelian_vn β) hx hy
  · intro z hz
    have := isElemAbelian_pow_eq_one (isElemAbelian_Zv hA β) hz
    rw [← sq]
    exact this
  · intro q hq' x hx
    have h1 : ⁅x, q⁆ ∈ ⁅Vn β, Qv β⁆ :=
      Subgroup.commutator_mem_commutator hx (by rw [hQ]; exact hq')
    rw [hBl.comm_vn_qv β hβ] at h1
    rw [← commutatorElement_inv x q]
    exact (Zv β).inv_mem h1
  · have := hB.orth β hβ
    rwa [hst, hC1.cv_eq β hβ] at this

end OrthVertex

end F53B3.NoEO

end CFSG.Quasithin
