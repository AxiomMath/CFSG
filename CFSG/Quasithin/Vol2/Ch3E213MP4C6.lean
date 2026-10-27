module

public import CFSG.Quasithin.Vol2.Ch3E213MP4C5
public import CFSG.Quasithin.Vol2.Ch3E213MSL2Pair
public import CFSG.Quasithin.Vol2.Ch3E213MP4C4

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.Quasithin.H13.QRC CFSG.GorensteinWalter
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped MatrixGroups

variable {H : Type} [Group H] [Finite H]

theorem qrc_unitary_pair
    (hns : ¬ Group.IsSolvable H) (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V) {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    (J : HermitianForm 3 k) (hcard : Nat.card k = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (θ₀ : ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) :
    SL2Pair.Pair T M V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨-, -, -, hKn, hCK, hKS, ⟨hSB, hBtop, hBmax⟩, -, -, hEO⟩ :=
    bender_section_setup hns T hTn hTM hMH hmax hVT hVM
  set D := kerIn M ⊤ with hDdef
  set π := QuotientGroup.mk' D with hπdef
  set K := (oddResidualPreimage H).map π with hKdef
  have := hKn
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  set S := (T : Subgroup H).map π with hSdef
  set B := M.map π with hBdef
  set E := V.map π with hEdef
  have hS2 : IsPGroup 2 S := T.isPGroup'.map π
  have hSsyl : IsSylowOf 2 S ⊤ := isSylowOf_iff.2 ⟨le_top, hS2, by
    rw [relIndex_top_right, hSdef, ← Sylow.coe_mapSurjective hπs T]
    exact (T.mapSurjective hπs).not_dvd_index⟩
  have hUsyl : IsSylowOf 2 (S ⊓ K) K :=
    hSsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top])
  obtain ⟨U₁, hU₁⟩ := hUsyl.exists_sylow_eq_subgroupOf
  have hEel : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
  have hES : E ≤ S := map_mono hVT
  have hCK' : ∀ a : H ⧸ D, (∀ x ∈ K, a * x = x * a) → a = 1 := hCK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨SP, hSP⟩, -⟩ :=
    unitary_three_point_structure J n hn hcard hfixed hJ
  obtain ⟨θ, hθU, hθN⟩ := exists_mulEquiv_map_sylow θ₀ U₁.isPGroup' U₁.not_dvd_index
    (hSP ▸ SP.isPGroup') (hSP ▸ SP.not_dvd_index)
  rw [normalizer_root_eq J hn hcard hfixed hJ] at hθN
  have hco : IsCoatom (normalizer ((U₁ : Subgroup K) : Set K)) := by
    rw [← map_symm_eq_of_map_eq θ hθN]
    exact (OrderIso.isCoatom_iff θ.symm.mapSubgroup _).2 (isCoatom_stabilizer J hn hcard hfixed hJ)
  obtain ⟨hBK, hBN⟩ := borel_eq_of_isCoatom hU₁ U₁.isPGroup' U₁.not_dvd_index hco hKS hSB hBtop
    hBmax
  have hRK := pCore_le_of_unitary hCK' hS2 hSB hU₁ U₁.not_dvd_index hBK hBN J hn hcard hfixed hJ
    θ hθU hθN
  have hEK : E ≤ K := hEO.trans hRK
  set k₀ := fixedSubfield J.conj
  have hk₀ : Nat.card k₀ = 2 ^ n :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans hfixed
  set ι : k₀ →+* k := k₀.subtype
  have hι : ∀ x, J.conj (ι x) = ι x := fun x => x.2
  set φ : SL(2, k₀) →* H ⧸ D :=
    K.subtype.comp (θ.symm.toMonoidHom.comp (sublineHom J hJ ι hι)) with hφdef
  have hφinj : Function.Injective φ := K.subtype_injective.comp
    (θ.symm.injective.comp (sublineHom_injective J hJ ι hι))
  have hφK : ∀ g, φ g ∈ K := fun g => (θ.symm (sublineHom J hJ ι hι g)).2
  have hθmem : ∀ (X : Subgroup K) (y : K), θ y ∈ X.map θ.toMonoidHom ↔ y ∈ X := fun X y => by
    rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  have hφS : ∀ g, φ g ∈ S ↔ g ∈ sl2UpperUnipotentSubgroup k₀ := fun g => by
    rw [← sublineHom_mem_root_iff J hJ ι hι, ← hθU, ← θ.apply_symm_apply (sublineHom J hJ ι hι g),
      hθmem, hU₁, mem_subgroupOf]
    exact ⟨fun h => ⟨h, hφK g⟩, fun h => h.1⟩
  have hφB : ∀ g ∈ sl2Borel k₀, φ g ∈ B := fun g hg => by
    rw [← sublineHom_mem_stabilizer_iff J hJ ι hι, ← hθN,
      ← θ.apply_symm_apply (sublineHom J hJ ι hι g), hθmem] at hg
    have h1 : φ g ∈ (normalizer ((U₁ : Subgroup K) : Set K)).map K.subtype := ⟨_, hg, rfl⟩
    rw [← hBK] at h1
    exact h1.1
  have hEφ : E ≤ (sl2UpperUnipotentSubgroup k₀).map φ := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact one_mem _
    have he2 : orderOf e = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1
    set e' : K := ⟨e, hEK he⟩
    have he'U : θ e' ∈ (hermitianUnipotentPSU J hJ).range := by
      rw [← hθU, hθmem, hU₁, mem_subgroupOf]
      exact ⟨hES he, hEK he⟩
    have he'B : θ e' ∈ unitaryCoordinateStabilizer J 0 :=
      (normalizer_root_eq J hn hcard hfixed hJ) ▸ le_normalizer he'U
    have he'2 : orderOf (θ e') = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact he2
    obtain ⟨y, hy, hye⟩ := exists_sublineHom_eq_of_involution J hJ ι hι hn hcard hfixed
      (fun b hb => ⟨⟨b, hb⟩, rfl⟩) he'B he'2
    refine ⟨y, hy, ?_⟩
    change ((θ.symm (sublineHom J hJ ι hι y) : K) : H ⧸ D) = e
    rw [hye, θ.symm_apply_apply]
  exact SL2Pair.qrc_pair_of_sl2 hns hchar T hTn hTM hMH hmax hVT hTV hVM hVQ hk₀ φ hφinj hφK hφS
    hφB hEφ

end CFSG.Quasithin.Ch3E213M.P4C
