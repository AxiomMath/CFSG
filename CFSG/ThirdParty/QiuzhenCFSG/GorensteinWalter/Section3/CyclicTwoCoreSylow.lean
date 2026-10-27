module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFitting

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped commutatorElement
open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The ambient subgroup of `G` carried by a Sylow subgroup of a
subgroup `X`. -/
public noncomputable def sylowCarrier {G : Type u} [Group G] [Finite G]
    {p : ℕ} {X : Subgroup G} (P : Sylow p X) : Subgroup G :=
  (P : Subgroup X).map X.subtype

/-- The carrier of a Sylow `p`-subgroup of `X` sits inside any equal
subgroup `K` and has the maximal `p`-power cardinality there. -/
public theorem sylowCarrier_le_and_card {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X K : Subgroup G} (P : Sylow p X)
    (hXK : X = K) :
    sylowCarrier P ≤ K ∧
      Nat.card (sylowCarrier P) = p ^ (Nat.card K).factorization p := by
  have hle : sylowCarrier P ≤ X := by
    intro z hz
    rcases (Subgroup.mem_map).1 hz with ⟨x, hx, rfl⟩
    exact x.2
  have hcard : Nat.card (sylowCarrier P) =
      p ^ (Nat.card X).factorization p := by
    calc
      Nat.card (sylowCarrier P) = Nat.card (P : Subgroup X) := by
        rw [sylowCarrier, Subgroup.card_map_of_injective X.subtype_injective]
      _ = p ^ (Nat.card X).factorization p := P.card_eq_multiplicity
  refine ⟨?_, ?_⟩
  · simpa [hXK] using hle
  · simpa [hXK] using hcard

private theorem index_subgroupOf_sup_dvd_card_of_le_normalizer
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G)
    (hBnormA : B ≤ Subgroup.normalizer (A : Set G)) :
    ((B.subgroupOf (B ⊔ A)).index) ∣ Nat.card A := by
  classical
  have hAC : A.relIndex (B ⊔ A : Subgroup G) = A.relIndex B := by
    let : (A.subgroupOf B).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (H := B) (N := A) hBnormA
    let : (A.subgroupOf (B ⊔ A : Subgroup G)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := B) (N := A) hBnormA
    let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hBnormA
    have hcard : Nat.card (B ⧸ A.subgroupOf B) =
        Nat.card (↥(B ⊔ A : Subgroup G) ⧸ A.subgroupOf (B ⊔ A : Subgroup G)) :=
          Nat.card_congr e.toEquiv
    simpa [Subgroup.relIndex, Subgroup.index_eq_card] using hcard.symm
  have h1 : A.relIndex B * B.relIndex (B ⊔ A : Subgroup G) =
      (A ⊓ B).relIndex (B ⊔ A : Subgroup G) := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := A) (K := B)
      (L := (B ⊔ A : Subgroup G))
    have hBC : B ⊓ (B ⊔ A : Subgroup G) = B := by
      ext x
      constructor
      · intro hx
        exact (Subgroup.mem_inf.mp hx).1
      · intro hx
        exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_sup_left hx⟩
    rw [hBC] at h
    exact h
  have h2 : (A ⊓ B).relIndex A * A.relIndex (B ⊔ A : Subgroup G) =
      (A ⊓ B).relIndex (B ⊔ A : Subgroup G) := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := A ⊓ B) (K := A)
      (L := (B ⊔ A : Subgroup G))
    have hAC' : A ⊓ (B ⊔ A : Subgroup G) = A := by
      ext x
      constructor
      · intro hx
        exact (Subgroup.mem_inf.mp hx).1
      · intro hx
        exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_sup_right hx⟩
    have hN' : (A ⊓ B) ⊓ A = A ⊓ B := by
      ext x
      constructor
      · intro hx
        exact (Subgroup.mem_inf.mp hx).1
      · intro hx
        exact Subgroup.mem_inf.mpr ⟨hx, (Subgroup.mem_inf.mp hx).1⟩
    rw [hAC', hN'] at h
    exact h
  have h3 : A.relIndex B * B.relIndex (B ⊔ A : Subgroup G) =
      (A ⊓ B).relIndex A * A.relIndex B := by
    calc
      A.relIndex B * B.relIndex (B ⊔ A : Subgroup G) =
          (A ⊓ B).relIndex (B ⊔ A : Subgroup G) := h1
      _ = (A ⊓ B).relIndex A * A.relIndex (B ⊔ A : Subgroup G) := h2.symm
      _ = (A ⊓ B).relIndex A * A.relIndex B := by rw [hAC]
  have hApos : 0 < A.relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := A.subgroupOf B))
  have hB : B.relIndex (B ⊔ A : Subgroup G) = (A ⊓ B).relIndex A := by
    apply Nat.mul_left_cancel hApos
    simpa [mul_comm] using h3
  change B.relIndex (B ⊔ A : Subgroup G) ∣ Nat.card A
  rw [hB]
  exact Subgroup.relIndex_dvd_card (H := A ⊓ B) (K := A)

/-! ## Centralizer decomposition `C_U(s) = C_{F(U)}(s)·B`

In the cyclic branch `U = F(U)·B`; for `s ∈ S` the fixed-point subgroup
`B = C_U(S)` is pointwise fixed by `s`, so the centralizer of `s` in `U`
decomposes as the product of the centralizer in `F(U)` and `B`.
-/

private theorem mem_centralizerIn_iff_local {G : Type u} [Group G]
    (X : Subgroup G) (s x : G) :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ s * x * s⁻¹ = x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
    rw [hcomm]
    group
  · rintro ⟨hxX, hxfix⟩
    refine ⟨hxX, ?_⟩
    change x ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxfix)

/-- Conjugation by `s ∈ S` preserves `F(U)`. -/
private theorem s_normalizes_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) {s : G} (hs : s ∈ (bg.S : Subgroup G)) :
    ∀ f : G, f ∈ fittingSubgroupOf bg.U → s * f * s⁻¹ ∈ fittingSubgroupOf bg.U := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro f hf
  rcases (Subgroup.mem_map).1 hf with ⟨fU, hfCore, rfl⟩
  let φ : ↥bg.U ≃* ↥bg.U := {
    toFun := fun u => ⟨s * (u : G) * s⁻¹,
      BenderGlauberman.S_normalizes_U bg s hs (u : G) u.2⟩
    invFun := fun u => ⟨s⁻¹ * (u : G) * s, by
      have h := BenderGlauberman.S_normalizes_U bg s⁻¹
        ((bg.S : Subgroup G).inv_mem hs) (u : G) u.2
      simpa [mul_assoc, inv_inv] using h⟩
    left_inv := by
      intro u
      apply Subtype.ext
      change s⁻¹ * (s * (u : G) * s⁻¹) * s = (u : G)
      group
    right_inv := by
      intro u
      apply Subtype.ext
      change s * (s⁻¹ * (u : G) * s) * s⁻¹ = (u : G)
      group
    map_mul' := by
      intro u v
      apply Subtype.ext
      change s * ((u : G) * (v : G)) * s⁻¹ =
        (s * (u : G) * s⁻¹) * (s * (v : G) * s⁻¹)
      group
  }
  have hconj : φ fU ∈ fittingSubgroup bg.U :=
    Subgroup.mem_comap.mp (by
      rw [(inferInstance : (fittingSubgroup bg.U).Characteristic).fixed φ]
      exact hfCore)
  exact Subgroup.mem_map.mpr ⟨φ fU, hconj, by
    change s * (fU : G) * s⁻¹ = s * (fU : G) * s⁻¹
    rfl⟩

private theorem B_le_centralizerIn_U_of_mem_S
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) {s : G} (hs : s ∈ (bg.S : Subgroup G)) :
    bg.B ≤ centralizerIn bg.U s := by
  let : Fintype G := Fintype.ofFinite G
  have hBleU : bg.B ≤ bg.U := by
    intro b hbB
    have hbB12 : b ∈ bg.B1 ⊓ bg.B2 := by
      simpa [BenderGlauberman.Hyp11.B] using hbB
    exact (mem_centralizerIn_iff_local bg.U bg.t1 b).mp hbB12.1 |>.1
  intro b hbB
  refine (mem_centralizerIn_iff_local bg.U s b).2 ⟨hBleU hbB, ?_⟩
  have hfix : (⟨b, hBleU hbB⟩ : ↥bg.U) ∈
      BenderGlauberman.fixedSubgroup (bg.S : Subgroup G) bg.U := by
    simpa using BenderGlauberman.b_mem_fixedSubgroup_s4 bg hbB
  have hfix' : (⟨s, hs⟩ : ↥(bg.S : Subgroup G)) •
        (⟨b, hBleU hbB⟩ : ↥bg.U) =
      (⟨b, hBleU hbB⟩ : ↥bg.U) :=
    (BenderGlauberman.mem_fixedSubgroup_iff (bg.S : Subgroup G) bg.U
      (⟨b, hBleU hbB⟩ : ↥bg.U)).mp hfix (⟨s, hs⟩ : ↥(bg.S : Subgroup G))
  have h' := congrArg Subtype.val hfix'
  exact (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
    (bg.S : Subgroup G) bg.U
    (⟨s, hs⟩ : ↥(bg.S : Subgroup G)) (⟨b, hBleU hbB⟩ : ↥bg.U)).symm.trans h'

public theorem B_normalizes_centralizerIn_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) {s : G} (hs : s ∈ (bg.S : Subgroup G)) :
    bg.B ≤ Subgroup.normalizer
      (centralizerIn (fittingSubgroupOf bg.U) s : Set G) := by
  have hBleU : bg.B ≤ bg.U := by
    intro b hbB
    have hbB12 : b ∈ bg.B1 ⊓ bg.B2 := by
      simpa [BenderGlauberman.Hyp11.B] using hbB
    exact (mem_centralizerIn_iff_local bg.U bg.t1 b).mp hbB12.1 |>.1
  have hFnorm : IsNormalIn (fittingSubgroupOf bg.U) bg.U :=
    fittingSubgroupOf_isNormalIn bg.U
  have hconj : ∀ b : G, b ∈ bg.B → ∀ x : G,
      x ∈ centralizerIn (fittingSubgroupOf bg.U) s →
        b * x * b⁻¹ ∈ centralizerIn (fittingSubgroupOf bg.U) s := by
    intro b hbB x hxC
    have hxF : x ∈ fittingSubgroupOf bg.U :=
      (mem_centralizerIn_iff_local (fittingSubgroupOf bg.U) s x).mp hxC |>.1
    have hxfix : s * x * s⁻¹ = x :=
      (mem_centralizerIn_iff_local (fittingSubgroupOf bg.U) s x).mp hxC |>.2
    have hbCent : b ∈ centralizerIn bg.U s :=
      B_le_centralizerIn_U_of_mem_S bg hs hbB
    have hbcomm : s * b = b * s := by
      have hb' : s * b * s⁻¹ = b :=
        (mem_centralizerIn_iff_local bg.U s b).mp hbCent |>.2
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hb')
    have hbcomm' : b⁻¹ * s = s * b⁻¹ := by
      calc
        b⁻¹ * s = b⁻¹ * (s * b * b⁻¹) := by group
        _ = b⁻¹ * (b * s * b⁻¹) := by rw [hbcomm]
        _ = s * b⁻¹ := by group
    have hbF : b * x * b⁻¹ ∈ fittingSubgroupOf bg.U :=
      hFnorm.2 b (hBleU hbB) x hxF
    have hbFix : s * (b * x * b⁻¹) * s⁻¹ = b * x * b⁻¹ := by
      have hbcomm_inv : b⁻¹ * s⁻¹ = s⁻¹ * b⁻¹ := by
        calc
          b⁻¹ * s⁻¹ = (s * b)⁻¹ := by rw [mul_inv_rev]
          _ = (b * s)⁻¹ := by rw [hbcomm]
          _ = s⁻¹ * b⁻¹ := by rw [mul_inv_rev]
      calc
        s * (b * x * b⁻¹) * s⁻¹ = (s * b) * x * (b⁻¹ * s⁻¹) := by group
        _ = (b * s) * x * ((b * s)⁻¹) := by
          rw [hbcomm, hbcomm_inv, mul_inv_rev]
        _ = b * (s * x * s⁻¹) * b⁻¹ := by group
        _ = b * x * b⁻¹ := by rw [hxfix]
    exact (mem_centralizerIn_iff_local (fittingSubgroupOf bg.U) s
      (b * x * b⁻¹)).2 ⟨hbF, hbFix⟩
  intro b hbB
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj b hbB x
  · intro hxC
    have hb' : b⁻¹ ∈ bg.B := bg.B.inv_mem hbB
    have hxC'' : b⁻¹ * (b * x * b⁻¹) * b ∈
        centralizerIn (fittingSubgroupOf bg.U) s := by
      simpa [inv_inv] using hconj b⁻¹ hb' (b * x * b⁻¹) hxC
    have hxeq : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    simpa [hxeq] using hxC''

private theorem B_normalizes_pPrimeCoreMap
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) (p : ℕ) :
    bg.B ≤ Subgroup.normalizer
      (((pPrimeCore p (fittingSubgroup bg.U)).map (fittingSubgroup bg.U).subtype).map
        bg.U.subtype : Set G) := by
  let U0 : Subgroup G := bg.U
  let F0 : Subgroup U0 := fittingSubgroup U0
  let Q0 : Subgroup F0 := pPrimeCore p F0
  let K0 : Subgroup U0 := Q0.map F0.subtype
  have : F0.Characteristic := inferInstance
  have : Q0.Characteristic := pPrimeCore_characteristic (p := p) (G := F0)
  have : K0.Characteristic := inferInstance
  have hBleU : bg.B ≤ U0 := by
    intro b hbB
    have hbB12 : b ∈ bg.B1 ⊓ bg.B2 := by
      simpa [BenderGlauberman.Hyp11.B] using hbB
    exact (mem_centralizerIn_iff_local bg.U bg.t1 b).mp hbB12.1 |>.1
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨u, hu, rfl⟩
    let φ : U0 ≃* U0 := MulAut.conj (⟨b, hBleU hb⟩ : U0)
    have hu' : φ u ∈ K0 := by
      have hfix : K0.comap φ.toMonoidHom = K0 :=
        (Subgroup.characteristic_iff_comap_eq.mp (inferInstance : K0.Characteristic)) φ
      exact Subgroup.mem_comap.mp (by rw [hfix]; exact hu)
    exact Subgroup.mem_map.mpr ⟨φ u, hu', rfl⟩
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨u, hu, hxeq⟩
    dsimp [U0] at hxeq ⊢
    let φ : U0 ≃* U0 := MulAut.conj (⟨b⁻¹, hBleU (bg.B.inv_mem hb)⟩ : U0)
    have hu' : φ u ∈ K0 := by
      have hfix : K0.comap φ.toMonoidHom = K0 :=
        (Subgroup.characteristic_iff_comap_eq.mp (inferInstance : K0.Characteristic)) φ
      exact Subgroup.mem_comap.mp (by rw [hfix]; exact hu)
    exact Subgroup.mem_map.mpr ⟨φ u, hu', by
      change (b⁻¹ : G) * (u : G) * (b⁻¹ : G)⁻¹ = x
      calc
        (b⁻¹ : G) * (u : G) * (b⁻¹ : G)⁻¹ =
            (b⁻¹ : G) * (b * x * b⁻¹) * (b⁻¹ : G)⁻¹ := by simp [hxeq]
        _ = x := by group⟩

private theorem B_normalizes_pCoreCentralizer_inter_pPrimeCoreMap
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) :
    bg.B ≤ Subgroup.normalizer
      ((centralizerIn (fittingSubgroupOf bg.U) s ⊓
        (((pPrimeCore p (fittingSubgroup bg.U)).map (fittingSubgroup bg.U).subtype).map
          bg.U.subtype) : Subgroup G) : Set G) := by
  let QF : Subgroup G :=
    ((pPrimeCore p (fittingSubgroup bg.U)).map (fittingSubgroup bg.U).subtype).map
      bg.U.subtype
  have hBnormA : bg.B ≤ Subgroup.normalizer
      (centralizerIn (fittingSubgroupOf bg.U) s : Set G) :=
    B_normalizes_centralizerIn_fittingSubgroupOf bg hs
  have hBnormQ : bg.B ≤ Subgroup.normalizer (QF : Set G) :=
    B_normalizes_pPrimeCoreMap bg p
  have hconj : ∀ b : G, b ∈ bg.B → ∀ x : G,
      x ∈ centralizerIn (fittingSubgroupOf bg.U) s ⊓ QF →
        b * x * b⁻¹ ∈ centralizerIn (fittingSubgroupOf bg.U) s ⊓ QF := by
    intro b hb x hx
    have hxA : b * x * b⁻¹ ∈ centralizerIn (fittingSubgroupOf bg.U) s :=
      (Subgroup.mem_normalizer_iff.mp (hBnormA hb) x).1 hx.1
    have hxQ : b * x * b⁻¹ ∈ QF :=
      (Subgroup.mem_normalizer_iff.mp (hBnormQ hb) x).1 hx.2
    exact Subgroup.mem_inf.mpr ⟨hxA, hxQ⟩
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj b hb x
  · intro hx
    have hb' : b⁻¹ ∈ bg.B := bg.B.inv_mem hb
    have hx'' : b⁻¹ * (b * x * b⁻¹) * b ∈
        centralizerIn (fittingSubgroupOf bg.U) s ⊓ QF := by
      simpa [inv_inv] using hconj b⁻¹ hb' (b * x * b⁻¹) hx
    have hxeq : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    change x ∈ centralizerIn (fittingSubgroupOf bg.U) s ⊓ QF
    simpa [hxeq] using hx''

public theorem centralizerIn_U_eq_centralizerIn_FU_sup_B
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G)) :
    centralizerIn bg.U s = centralizerIn (fittingSubgroupOf bg.U) s ⊔ bg.B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let F : Subgroup G := fittingSubgroupOf bg.U
  have hFleU : F ≤ bg.U := fittingSubgroupOf_le bg.U
  have hBleU : bg.B ≤ bg.U := by
    intro b hbB
    have hbB12 : b ∈ bg.B1 ⊓ bg.B2 := by
      simpa [BenderGlauberman.Hyp11.B] using hbB
    exact (mem_centralizerIn_iff_local bg.U bg.t1 b).mp hbB12.1 |>.1
  have hBleC : bg.B ≤ centralizerIn bg.U s := by
    intro b hbB
    refine (mem_centralizerIn_iff_local bg.U s b).2 ⟨hBleU hbB, ?_⟩
    have hfix : (⟨b, hBleU hbB⟩ : ↥bg.U) ∈
        BenderGlauberman.fixedSubgroup (bg.S : Subgroup G) bg.U := by
      simpa using BenderGlauberman.b_mem_fixedSubgroup_s4 bg hbB
    have hfix' : (⟨s, hs⟩ : ↥(bg.S : Subgroup G)) •
          (⟨b, hBleU hbB⟩ : ↥bg.U) =
        (⟨b, hBleU hbB⟩ : ↥bg.U) :=
      (BenderGlauberman.mem_fixedSubgroup_iff (bg.S : Subgroup G) bg.U
        (⟨b, hBleU hbB⟩ : ↥bg.U)).mp hfix (⟨s, hs⟩ : ↥(bg.S : Subgroup G))
    have h' := congrArg Subtype.val hfix'
    exact (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
      (bg.S : Subgroup G) bg.U
      (⟨s, hs⟩ : ↥(bg.S : Subgroup G)) (⟨b, hBleU hbB⟩ : ↥bg.U)).symm.trans h'
  have hFleC : centralizerIn F s ≤ centralizerIn bg.U s := by
    intro x hx
    exact (mem_centralizerIn_iff_local bg.U s x).2
      ⟨hFleU ((mem_centralizerIn_iff_local F s x).mp hx).1,
        ((mem_centralizerIn_iff_local F s x).mp hx).2⟩
  ext x
  constructor
  · intro hxC
    let xU : ↥bg.U := ⟨x, ((mem_centralizerIn_iff_local bg.U s x).mp hxC).1⟩
    have hxsupU : xU ∈ (F.subgroupOf bg.U) ⊔ (bg.B.subgroupOf bg.U) := by
      have hsub : (F ⊔ bg.B).subgroupOf bg.U =
          F.subgroupOf bg.U ⊔ bg.B.subgroupOf bg.U :=
        Subgroup.subgroupOf_sup hFleU hBleU
      have hxFB : x ∈ F ⊔ bg.B := by
        rw [← hU]
        exact xU.2
      have hxsub : (⟨x, xU.2⟩ : ↥bg.U) ∈ (F ⊔ bg.B).subgroupOf bg.U :=
        Subgroup.mem_subgroupOf.mpr hxFB
      change (⟨x, xU.2⟩ : ↥bg.U) ∈
        (F.subgroupOf bg.U) ⊔ (bg.B.subgroupOf bg.U)
      rw [← hsub]
      exact hxsub
    have hFnorm : (F.subgroupOf bg.U).Normal := by
      have hIsNorm : IsNormalIn F bg.U := fittingSubgroupOf_isNormalIn bg.U
      exact (Subgroup.normal_subgroupOf_iff hFleU).mpr
        (fun h k hh hk => hIsNorm.2 k hk h hh)
    let : (F.subgroupOf bg.U).Normal := hFnorm
    rcases (Subgroup.mem_sup_of_normal_left
      (s := F.subgroupOf bg.U) (t := bg.B.subgroupOf bg.U)).mp hxsupU with
      ⟨fU, hfU, bU, hbU, hxeq⟩
    have hxeq' : (fU : G) * (bU : G) = x := congrArg Subtype.val hxeq
    have hxfix : s * ((fU : G) * (bU : G)) * s⁻¹ = (fU : G) * (bU : G) := by
      simpa [hxeq'] using ((mem_centralizerIn_iff_local bg.U s x).mp hxC).2
    have hbfix : s * (bU : G) * s⁻¹ = (bU : G) :=
      ((mem_centralizerIn_iff_local bg.U s (bU : G)).mp
        (hBleC (Subgroup.mem_subgroupOf.mp hbU))).2
    have hffix : s * (fU : G) * s⁻¹ = (fU : G) := by
      calc
        s * (fU : G) * s⁻¹ =
            (s * ((fU : G) * (bU : G)) * s⁻¹) * (s * (bU : G)⁻¹ * s⁻¹) := by group
        _ = ((fU : G) * (bU : G)) * (s * (bU : G)⁻¹ * s⁻¹) := by rw [hxfix]
        _ = (fU : G) := by
          have hbfix' : s * (bU : G)⁻¹ * s⁻¹ = (bU : G)⁻¹ := by
            calc
              s * (bU : G)⁻¹ * s⁻¹ = (s * (bU : G) * s⁻¹)⁻¹ := by group
              _ = (bU : G)⁻¹ := by rw [hbfix]
          rw [hbfix']
          group
    have hconcl : (fU : G) * (bU : G) ∈ centralizerIn F s ⊔ bg.B :=
      (centralizerIn F s ⊔ bg.B).mul_mem
        (Subgroup.mem_sup_left ((mem_centralizerIn_iff_local F s (fU : G)).2
          ⟨Subgroup.mem_subgroupOf.mp hfU, hffix⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hbU))
    simpa [hxeq'] using hconcl
  · intro hx
    exact sup_le hFleC hBleC hx

/-- A Sylow `p`-subgroup of `B` is a Sylow `p`-subgroup of `C = A ⊔ B` when
`B` normalizes `A` and `A` is `p`-free. -/
public noncomputable def sylowOf_join_of_pFree
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (A B C : Subgroup G) (hC : C = A ⊔ B)
    (hBnormA : B ≤ Subgroup.normalizer (A : Set G))
    (hAcop : Nat.Coprime p (Nat.card A))
    (Q : Sylow p ↥B) :
    Sylow p ↥C := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let P2G : Subgroup G := (Q : Subgroup ↥B).map B.subtype
  have hBleC : B ≤ C := by
    exact le_sup_right.trans (le_of_eq hC.symm)
  have hP2GC : P2G ≤ C := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨b, hb, rfl⟩
    exact hBleC (show (b : G) ∈ B from b.2)
  let P2C : Subgroup C := P2G.subgroupOf C
  have hidx : (B.subgroupOf (B ⊔ A)).index ∣ Nat.card A :=
    index_subgroupOf_sup_dvd_card_of_le_normalizer A B hBnormA
  have hidx' : (B.subgroupOf C).index ∣ Nat.card A := by
    rw [hC, sup_comm]
    exact hidx
  have hBcop : Nat.Coprime p ((B.subgroupOf C).index) :=
    Nat.Coprime.coprime_dvd_right hidx' hAcop
  have hCcard : Nat.card C = Nat.card B * (B.subgroupOf C).index := by
    have hBcard : Nat.card (B.subgroupOf C) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := B) (K := C)
        hBleC).toEquiv
    rw [← hBcard]
    exact (B.subgroupOf C).card_mul_index.symm
  have hfac : (Nat.card C).factorization p = (Nat.card B).factorization p := by
    rw [hCcard]
    have h0 : ((B.subgroupOf C).index).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hBcop)
    rw [Nat.factorization_mul (Nat.card_pos (α := B)).ne'
      (Subgroup.FiniteIndex.index_ne_zero (H := B.subgroupOf C))]
    simp [h0]
  have hQcard : Nat.card P2G = p ^ (Nat.card B).factorization p := by
    calc
      Nat.card P2G = Nat.card (Q : Subgroup ↥B) := by
        rw [Subgroup.card_map_of_injective B.subtype_injective]
      _ = p ^ (Nat.card B).factorization p := Q.card_eq_multiplicity
  have hP2Ccard : Nat.card P2C = p ^ (Nat.card C).factorization p := by
    calc
      Nat.card P2C = Nat.card P2G := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P2G) (K := C)
          hP2GC).toEquiv
      _ = p ^ (Nat.card B).factorization p := hQcard
      _ = p ^ (Nat.card C).factorization p := by rw [hfac]
  exact Sylow.ofCard P2C hP2Ccard

/-- A Sylow `p`-subgroup of `B = C_U(S)` is a Sylow `p`-subgroup of
`C_U(s)` whenever `C_{F(U)}(s)` is `p`-free. -/
@[expose]
public noncomputable def centralizerIn_sylow_of_B
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) [Fact p.Prime]
    (hApcop : Nat.Coprime p (Nat.card
      (centralizerIn (fittingSubgroupOf bg.U) s)))
    (Q : Sylow p ↥bg.B) :
    Sylow p ↥(centralizerIn bg.U s) := by
  have hCeq : centralizerIn bg.U s =
      centralizerIn (fittingSubgroupOf bg.U) s ⊔ bg.B :=
    centralizerIn_U_eq_centralizerIn_FU_sup_B bg hU hs
  have hBnormF : bg.B ≤ Subgroup.normalizer
      (centralizerIn (fittingSubgroupOf bg.U) s : Set G) :=
    B_normalizes_centralizerIn_fittingSubgroupOf bg hs
  exact sylowOf_join_of_pFree p
    (centralizerIn (fittingSubgroupOf bg.U) s) bg.B (centralizerIn bg.U s)
    hCeq hBnormF hApcop Q

/-- If `N` is a normal `p`-subgroup, `C = N ⊔ D`, and `Q` is a Sylow
`p`-subgroup of `D`, then `N ⊔ Q` is a Sylow `p`-subgroup of `C`. -/
public noncomputable def sylowOf_normal_pCore_sup
    {C : Type u} [Group C] [Finite C]
    (p : ℕ) [Fact p.Prime]
    (N : Subgroup C) [N.Normal] (hNp : IsPGroup p N)
    (D : Subgroup C) (QD : Sylow p D)
    (hCD : N ⊔ D = ⊤) :
    Sylow p C := by
  classical
  let q : C →* C ⧸ N := QuotientGroup.mk' N
  let QDc : Subgroup C := (QD : Subgroup D).map D.subtype
  let φ : D →* C ⧸ N := q.comp D.subtype
  have hφsurj : Function.Surjective φ := by
    intro z
    rcases (QuotientGroup.mk'_surjective N z) with ⟨c, rfl⟩
    have hset : (⊤ : Subgroup C).carrier = (N : Set C) * (D : Set C) := by
      rw [← hCD]
      exact Subgroup.normal_mul N D
    have hc : (c : C) ∈ (N : Set C) * (D : Set C) := by
      rw [← hset]
      trivial
    rcases hc with ⟨n, hn, d, hd, rfl⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.leftRel N (D.subtype ⟨d, hd⟩)
      ((fun x1 x2 : C => x1 * x2) n d)
    rw [QuotientGroup.leftRel_apply]
    change (d : C)⁻¹ * ((n : C) * d) ∈ N
    simpa [mul_assoc] using
      (inferInstance : N.Normal).conj_mem n hn ((d : C)⁻¹)
  let Qbar : Sylow p (C ⧸ N) := QD.mapSurjective (f := φ) hφsurj
  have hqker : q.ker = N := QuotientGroup.ker_mk' N
  have hqkerp : IsPGroup p q.ker := by rw [hqker]; exact hNp
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hQbar_range : (Qbar : Subgroup (C ⧸ N)) ≤ q.range := by
    intro x hx
    rcases hqsurj x with ⟨c, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  exact Qbar.comapOfKerIsPGroup q hqkerp hQbar_range

public theorem sylowOf_normal_pCore_sup_coe
    {C : Type u} [Group C] [Finite C]
    (p : ℕ) [Fact p.Prime]
    (N : Subgroup C) [N.Normal] (hNp : IsPGroup p N)
    (D : Subgroup C) (QD : Sylow p D)
    (hCD : N ⊔ D = ⊤) :
    ((sylowOf_normal_pCore_sup p N hNp D QD hCD : Sylow p C) : Subgroup C) =
      N ⊔ (QD : Subgroup D).map D.subtype := by
  classical
  unfold sylowOf_normal_pCore_sup
  let q : C →* C ⧸ N := QuotientGroup.mk' N
  let QDc : Subgroup C := (QD : Subgroup D).map D.subtype
  let φ : D →* C ⧸ N := q.comp D.subtype
  have hφsurj : Function.Surjective φ := by
    intro z
    rcases (QuotientGroup.mk'_surjective N z) with ⟨c, rfl⟩
    have hset : (⊤ : Subgroup C).carrier = (N : Set C) * (D : Set C) := by
      rw [← hCD]
      exact Subgroup.normal_mul N D
    have hc : (c : C) ∈ (N : Set C) * (D : Set C) := by
      rw [← hset]
      trivial
    rcases hc with ⟨n, hn, d, hd, rfl⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.leftRel N (D.subtype ⟨d, hd⟩)
      ((fun x1 x2 : C => x1 * x2) n d)
    rw [QuotientGroup.leftRel_apply]
    change (d : C)⁻¹ * ((n : C) * d) ∈ N
    simpa [mul_assoc] using
      (inferInstance : N.Normal).conj_mem n hn ((d : C)⁻¹)
  let Qbar : Sylow p (C ⧸ N) := QD.mapSurjective (f := φ) hφsurj
  have hqker : q.ker = N := QuotientGroup.ker_mk' N
  have hqkerp : IsPGroup p q.ker := by rw [hqker]; exact hNp
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hQbar_range : (Qbar : Subgroup (C ⧸ N)) ≤ q.range := by
    intro x hx
    rcases hqsurj x with ⟨c, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  change ((Qbar.comapOfKerIsPGroup q hqkerp hQbar_range : Sylow p C) : Subgroup C) =
      N ⊔ QDc
  rw [Sylow.coe_comapOfKerIsPGroup]
  have hQbar : (Qbar : Subgroup (C ⧸ N)) = QDc.map q := by
    rw [Sylow.coe_mapSurjective]
    rw [Subgroup.map_map]
  rw [hQbar]
  exact QuotientGroup.comap_map_mk' N QDc

/-- If `P = O_p(U)` is centralized by `s`, then `P · P₂` is a Sylow
`p`-subgroup of `C_U(s)` for every Sylow `p`-subgroup `P₂` of `B`. -/
public noncomputable def centralizerIn_sylow_of_pCore
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) [Fact p.Prime]
    (hPleC : qCoreOf bg.U p ≤ centralizerIn (fittingSubgroupOf bg.U) s)
    (Q : Sylow p ↥bg.B) :
    Sylow p ↥(centralizerIn bg.U s) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let C : Subgroup G := centralizerIn bg.U s
  let F : Subgroup G := fittingSubgroupOf bg.U
  let A : Subgroup G := centralizerIn F s
  let P : Subgroup G := qCoreOf bg.U p
  let QF : Subgroup G :=
    ((pPrimeCore p (fittingSubgroup bg.U)).map (fittingSubgroup bg.U).subtype).map
      bg.U.subtype
  let A0 : Subgroup G := A ⊓ QF
  let D : Subgroup G := A0 ⊔ bg.B
  have hCeq : C = A ⊔ bg.B :=
    centralizerIn_U_eq_centralizerIn_FU_sup_B bg hU hs
  have hAdecomp : A = P ⊔ A0 :=
    centralizerIn_fittingSubgroupOf_eq_pCore_sup_inter_pPrimeCore bg.U p s hPleC
  have hA0cop : Nat.Coprime p (Nat.card A0) := by
    have hQcop := pPrimeCore_map_card_coprime bg.U p
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_right : A0 ≤ QF)) hQcop
  have hBnormA0 : bg.B ≤ Subgroup.normalizer (A0 : Set G) :=
    B_normalizes_pCoreCentralizer_inter_pPrimeCoreMap bg hs p
  let QD : Sylow p ↥D :=
    sylowOf_join_of_pFree p A0 bg.B D rfl hBnormA0 hA0cop Q
  have hAleC : A ≤ C := by
    intro x hx
    exact (mem_centralizerIn_iff_local bg.U s x).2
      ⟨(fittingSubgroupOf_le bg.U) ((mem_centralizerIn_iff_local F s x).mp hx |>.1),
        ((mem_centralizerIn_iff_local F s x).mp hx |>.2)⟩
  have hA0leC : A0 ≤ C := (inf_le_left : A0 ≤ A).trans hAleC
  have hDleC : D ≤ C := sup_le hA0leC (B_le_centralizerIn_U_of_mem_S bg hs)
  have hPleC' : P ≤ C := hPleC.trans hAleC
  let Pc : Subgroup C := P.subgroupOf C
  let Dc : Subgroup C := D.subgroupOf C
  have hCleU : C ≤ bg.U := by
    intro x hx
    exact (mem_centralizerIn_iff_local bg.U s x).mp hx |>.1
  have hPc_norm : Pc.Normal := by
    have hnormU : bg.U ≤ Subgroup.normalizer (P : Set G) :=
      le_normalizer_of_isNormalIn (qCoreOf_normal_in bg.U p)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPleC').mpr
      (le_trans hCleU hnormU)
  have hPc_p : IsPGroup p Pc :=
    (qCoreOf_isPGroup bg.U p).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P) (K := C) hPleC').symm
  let eD : Dc ≃* D := Subgroup.subgroupOfEquivOfLe (H := D) (K := C) hDleC
  let QDc : Sylow p Dc := QD.comapOfInjective eD.toMonoidHom eD.injective
    (by
      intro x hx
      exact MonoidHom.mem_range.mpr ⟨eD.symm x, by simp⟩)
  have hPsupD : P ⊔ D = C := by
    calc
      P ⊔ D = P ⊔ (A0 ⊔ bg.B) := rfl
      _ = (P ⊔ A0) ⊔ bg.B := by rw [sup_assoc]
      _ = A ⊔ bg.B := by rw [hAdecomp]
      _ = C := hCeq.symm
  have hCD : Pc ⊔ Dc = ⊤ := by
    have hsub : Pc ⊔ Dc = (P ⊔ D).subgroupOf C := by
      symm
      exact Subgroup.subgroupOf_sup (A := P) (A' := D) (B := C) hPleC' hDleC
    rw [hsub]
    apply (Subgroup.subgroupOf_eq_top).2
    intro x hx
    simpa [hPsupD] using hx
  letI : Pc.Normal := hPc_norm
  exact sylowOf_normal_pCore_sup p Pc hPc_p Dc QDc hCD

/-- Version of `centralizerIn_sylow_of_B` with the `p`-freeness of
`C_{F(U)}(s)` derived from inversion of `O_p(U)`. -/
@[expose]
public noncomputable def centralizerIn_sylow_of_B_of_inverted
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) [Fact p.Prime]
    (hodd : Nat.Coprime 2 (Nat.card (qCoreOf bg.U p)))
    (hinv : ∀ x : G, x ∈ qCoreOf bg.U p → s * x * s⁻¹ = x⁻¹)
    (Q : Sylow p ↥bg.B) :
    Sylow p ↥(centralizerIn bg.U s) :=
  centralizerIn_sylow_of_B bg hU hs p
    (centralizerIn_fittingSubgroupOf_card_coprime_of_inverted
      bg.U p s hodd hinv) Q

/-- The carrier in `G` of `centralizerIn_sylow_of_B` is the image of `Q`
in `G`. -/
public theorem centralizerIn_sylow_of_B_carrier
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) [Fact p.Prime]
    (hApcop : Nat.Coprime p (Nat.card
      (centralizerIn (fittingSubgroupOf bg.U) s)))
    (Q : Sylow p ↥bg.B) :
    sylowCarrier (centralizerIn_sylow_of_B bg hU hs p hApcop Q) =
      (Q : Subgroup ↥bg.B).map bg.B.subtype := by
  classical
  let C : Subgroup G := centralizerIn bg.U s
  let A : Subgroup G := centralizerIn (fittingSubgroupOf bg.U) s
  let P2G : Subgroup G := (Q : Subgroup ↥bg.B).map bg.B.subtype
  have hCeq : C = A ⊔ bg.B :=
    centralizerIn_U_eq_centralizerIn_FU_sup_B bg hU hs
  have hBnormA : bg.B ≤ Subgroup.normalizer (A : Set G) :=
    B_normalizes_centralizerIn_fittingSubgroupOf bg hs
  have hP2GC : P2G ≤ C := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨b, hb, rfl⟩
    exact (le_of_eq hCeq.symm)
      (Subgroup.mem_sup_right (show (b : G) ∈ bg.B from b.2))
  have hcoe : (centralizerIn_sylow_of_B bg hU hs p hApcop Q : Subgroup C) =
      P2G.subgroupOf C := by
    simp [centralizerIn_sylow_of_B, sylowOf_join_of_pFree, Sylow.coe_ofCard]
    rfl
  rw [sylowCarrier]
  rw [hcoe]
  exact Subgroup.map_subgroupOf_eq_of_le hP2GC

/-- The carrier in `G` of `centralizerIn_sylow_of_pCore` is
`P ⊔ P₂`, where `P = O_p(U)` and `P₂` is the image of `Q`. -/
public theorem centralizerIn_sylow_of_pCore_carrier
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hU : bg.U = fittingSubgroupOf bg.U ⊔ bg.B)
    {s : G} (hs : s ∈ (bg.S : Subgroup G))
    (p : ℕ) [Fact p.Prime]
    (hPleC : qCoreOf bg.U p ≤ centralizerIn (fittingSubgroupOf bg.U) s)
    (Q : Sylow p ↥bg.B) :
    sylowCarrier (centralizerIn_sylow_of_pCore bg hU hs p hPleC Q) =
      qCoreOf bg.U p ⊔ ((Q : Subgroup ↥bg.B).map bg.B.subtype) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let C : Subgroup G := centralizerIn bg.U s
  let F : Subgroup G := fittingSubgroupOf bg.U
  let A : Subgroup G := centralizerIn F s
  let P : Subgroup G := qCoreOf bg.U p
  let QF : Subgroup G :=
    ((pPrimeCore p (fittingSubgroup bg.U)).map (fittingSubgroup bg.U).subtype).map
      bg.U.subtype
  let A0 : Subgroup G := A ⊓ QF
  let D : Subgroup G := A0 ⊔ bg.B
  have hCeq : C = A ⊔ bg.B :=
    centralizerIn_U_eq_centralizerIn_FU_sup_B bg hU hs
  have hAdecomp : A = P ⊔ A0 :=
    centralizerIn_fittingSubgroupOf_eq_pCore_sup_inter_pPrimeCore bg.U p s hPleC
  have hA0cop : Nat.Coprime p (Nat.card A0) := by
    have hQcop := pPrimeCore_map_card_coprime bg.U p
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_right : A0 ≤ QF)) hQcop
  have hBnormA0 : bg.B ≤ Subgroup.normalizer (A0 : Set G) :=
    B_normalizes_pCoreCentralizer_inter_pPrimeCoreMap bg hs p
  let QD : Sylow p ↥D :=
    sylowOf_join_of_pFree p A0 bg.B D rfl hBnormA0 hA0cop Q
  have hAleC : A ≤ C := by
    intro x hx
    exact (mem_centralizerIn_iff_local bg.U s x).2
      ⟨(fittingSubgroupOf_le bg.U) ((mem_centralizerIn_iff_local F s x).mp hx |>.1),
        ((mem_centralizerIn_iff_local F s x).mp hx |>.2)⟩
  have hA0leC : A0 ≤ C := (inf_le_left : A0 ≤ A).trans hAleC
  have hDleC : D ≤ C := sup_le hA0leC (B_le_centralizerIn_U_of_mem_S bg hs)
  have hPleC' : P ≤ C := hPleC.trans hAleC
  let Pc : Subgroup C := P.subgroupOf C
  let Dc : Subgroup C := D.subgroupOf C
  have hCleU : C ≤ bg.U := by
    intro x hx
    exact (mem_centralizerIn_iff_local bg.U s x).mp hx |>.1
  have hPc_norm : Pc.Normal := by
    have hnormU : bg.U ≤ Subgroup.normalizer (P : Set G) :=
      le_normalizer_of_isNormalIn (qCoreOf_normal_in bg.U p)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPleC').mpr
      (le_trans hCleU hnormU)
  have hPc_p : IsPGroup p Pc :=
    (qCoreOf_isPGroup bg.U p).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P) (K := C) hPleC').symm
  let eD : Dc ≃* D := Subgroup.subgroupOfEquivOfLe (H := D) (K := C) hDleC
  let QDc : Sylow p Dc := QD.comapOfInjective eD.toMonoidHom eD.injective
    (by
      intro x hx
      exact MonoidHom.mem_range.mpr ⟨eD.symm x, by simp⟩)
  have hPsupD : P ⊔ D = C := by
    calc
      P ⊔ D = P ⊔ (A0 ⊔ bg.B) := rfl
      _ = (P ⊔ A0) ⊔ bg.B := by rw [sup_assoc]
      _ = A ⊔ bg.B := by rw [hAdecomp]
      _ = C := hCeq.symm
  have hCD : Pc ⊔ Dc = ⊤ := by
    have hsub : Pc ⊔ Dc = (P ⊔ D).subgroupOf C := by
      symm
      exact Subgroup.subgroupOf_sup (A := P) (A' := D) (B := C) hPleC' hDleC
    rw [hsub]
    apply (Subgroup.subgroupOf_eq_top).2
    intro x hx
    simpa [hPsupD] using hx
  let : Pc.Normal := hPc_norm
  have hcoe : (centralizerIn_sylow_of_pCore bg hU hs p hPleC Q : Subgroup C) =
      Pc ⊔ (QDc : Subgroup Dc).map Dc.subtype := by
    simp [centralizerIn_sylow_of_pCore, sylowOf_normal_pCore_sup_coe]
    rfl
  have hQDcoe : (QDc : Subgroup Dc) = (QD : Subgroup D).comap eD.toMonoidHom := by
    rfl
  have hQD_map : (((QD : Subgroup D).comap eD.toMonoidHom).map Dc.subtype).map
      C.subtype = (QD : Subgroup D).map D.subtype := by
    ext z
    constructor
    · intro hz
      rcases (Subgroup.mem_map).1 hz with ⟨c, hc, rfl⟩
      rcases (Subgroup.mem_map).1 hc with ⟨d, hd, rfl⟩
      refine Subgroup.mem_map.mpr ⟨eD d, (Subgroup.mem_comap.mp hd), ?_⟩
      rfl
    · intro hz
      rcases (Subgroup.mem_map).1 hz with ⟨d, hd, rfl⟩
      obtain ⟨d₀, hd₀⟩ := eD.surjective d
      refine Subgroup.mem_map.mpr
        ⟨Dc.subtype d₀, ?_, ?_⟩
      · refine Subgroup.mem_map.mpr ⟨d₀, (Subgroup.mem_comap).mpr ?_, rfl⟩
        change eD d₀ ∈ ↑QD
        rwa [hd₀]
      · change (d₀ : Dc).1.1 = (d : D).1
        rw [← hd₀]
        rfl
  have hQDc_map : ((QDc : Subgroup Dc).map Dc.subtype).map C.subtype =
      (Q : Subgroup ↥bg.B).map bg.B.subtype := by
    rw [hQDcoe, hQD_map]
    have hQD_join : (QD : Subgroup D) =
        ((Q : Subgroup ↥bg.B).map bg.B.subtype).subgroupOf D := by
      simp [QD, sylowOf_join_of_pFree, Sylow.coe_ofCard]
    rw [hQD_join]
    have hP2GD : (Q : Subgroup ↥bg.B).map bg.B.subtype ≤ D := by
      intro x hx
      rcases (Subgroup.mem_map).1 hx with ⟨b, hb, rfl⟩
      exact (le_sup_right : bg.B ≤ A0 ⊔ bg.B)
        (show (b : G) ∈ bg.B from b.2)
    exact Subgroup.map_subgroupOf_eq_of_le hP2GD
  rw [sylowCarrier]
  rw [hcoe]
  rw [Subgroup.map_sup]
  have hPmap : Pc.map C.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPleC'
  rw [hPmap, hQDc_map]

end CFSG.GorensteinWalter
