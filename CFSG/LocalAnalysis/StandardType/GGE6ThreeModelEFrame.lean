module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Def

variable (K : Type) [Field K]

@[expose] noncomputable def eFrame (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : FrameData (adjointGroup .E6 K) where
  H := (hatAut .E6 K).range
  diag := NoOffE6Three.diag3 ζ hζ
  Tor := (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K)
  nb i := ⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup (τ := .E6) (K := K) i 1⟩

end Def

section Rows

variable {K : Type} [Field K] [Finite K]

theorem eFrame_center : Subgroup.center (adjointGroup .E6 K) = ⊥ :=
  center_adjointGroup_eq_bot (τ := .E6) (K := K)

theorem eFrame_faithful {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).Faithful :=
  NoOffE6Three.diag3_injective hζo hζ

theorem eFrame_torus [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : (eFrame K ζ hζ).TorusOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs t ht
    have hsT : (s : ModGL .E6 K) ∈ torusGroup .E6 K := Subgroup.mem_subgroupOf.mp hs
    have htT : (t : ModGL .E6 K) ∈ torusGroup .E6 K := Subgroup.mem_subgroupOf.mp ht
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hsT
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hb]
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b htT)
  · intro t ht
    have htT : (t : ModGL .E6 K) ∈ torusGroup .E6 K := Subgroup.mem_subgroupOf.mp ht
    have hpow : (t : ModGL .E6 K) ^ Nat.card Kˣ = 1 := by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
      rw [hb, rootDiagUnit_pow]
      have hb1 : b ^ Nat.card Kˣ = 1 := by
        funext i
        exact pow_card_eq_one' (x := b i)
      rw [hb1, rootDiagUnit_one]
    have hodd : Odd (Nat.card Kˣ) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      haveI := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
      have h1 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.pos.ne'
      have h2 : 0 < 2 ^ (n : ℕ) := by positivity
      omega
    have h1 : orderOf (t : ModGL .E6 K) ∣ Nat.card Kˣ := orderOf_dvd_of_pow_eq_one hpow
    have h2 : Odd (orderOf (t : ModGL .E6 K)) := Odd.of_dvd_nat hodd h1
    exact (Subgroup.orderOf_coe t) ▸ h2
  · intro x t ht
    exact Subtype.ext (by
      rw [show ((eFrame K ζ hζ).ad x t : ModGL .E6 K) =
          rootDiagUnit .E6 (zetaVec ζ hζ x) * (t : ModGL .E6 K) *
            (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹
          from NoOffE6Three.diag3_apply ζ hζ x t]
      exact conj_rootDiagUnit_of_mem_torusGroup (zetaVec ζ hζ x) (Subgroup.mem_subgroupOf.mp ht))

private theorem exists_torus_conj_rootDiagAut_cartanChar (t : Fin Tag.E6.rank → Kˣ) :
    ∃ r ∈ (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K),
      MulAut.conj r = rootDiagAut .E6 K (cartanChar t) := by
  have hmem : ((List.finRange Tag.E6.rank).map fun j => torusElt .E6 K j (t j)).prod ∈
      adjointGroup .E6 K :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      exact torusElt_mem_adjointGroup j _
  have hT : ((List.finRange Tag.E6.rank).map fun j => torusElt .E6 K j (t j)).prod ∈
      torusGroup .E6 K :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      exact Subgroup.subset_closure ⟨(j, t j), rfl⟩
  let r : adjointGroup .E6 K :=
    ⟨((List.finRange Tag.E6.rank).map fun j => torusElt .E6 K j (t j)).prod, hmem⟩
  have hrT : r ∈ (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K) :=
    Subgroup.mem_subgroupOf.mpr hT
  have hrconj : MulAut.conj r = rootDiagAut .E6 K (cartanChar t) := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_rootDiagAut, ← list_prod_torusElt_eq_rootDiagUnit]
    rfl
  exact ⟨r, hrT, hrconj⟩

theorem eFrame_inner [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).InnerPts := by
  intro v hv
  obtain ⟨y, hy⟩ := NoOffE6Three.zetaVec_eq_cartanChar_of_mem_hyp ζ hζ hv
  obtain ⟨r, hrT, hrconj⟩ := exists_torus_conj_rootDiagAut_cartanChar (K := K) (zetaVec ζ hζ y)
  refine ⟨r, hrT, ?_, ?_⟩
  · have h3 : MulAut.conj (r ^ 3) = 1 := by
      rw [map_pow, hrconj, ← hy]
      change ((eFrame K ζ hζ).ad v) ^ 3 = 1
      rw [show (eFrame K ζ hζ).ad v = (eFrame K ζ hζ).diag (Multiplicative.ofAdd v) from rfl,
        ← map_pow, NoOffE6Three.pow_three_eq_one, map_one]
    have hcen : r ^ 3 ∈ Subgroup.center (adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun h3 g
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    have := eFrame_center (K := K) ▸ hcen
    simpa using this
  · rw [hrconj, ← hy]
    rfl

end Rows

end CFSG.StandardType.E6ThreeModel
