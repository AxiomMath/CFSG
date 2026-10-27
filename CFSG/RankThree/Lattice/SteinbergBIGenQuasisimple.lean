module

public import CFSG.RankThree.Lattice.SteinbergBIGenBruhat
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootQuasisimple

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open scoped Pointwise commutatorElement

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

@[expose] def IsCLift (n : ModGL τ k) (w : WeylGroup τ) : Prop :=
  n ∈ D.orbitGroup ∧ ∃ h : n ∈ monomialSubgroup τ k, weylQuotientHom τ k ⟨n, h⟩ = w

theorem isCLift_of_isOrbitLift {n : ModGL τ k} {w : WeylGroup τ} (h : D.IsOrbitLift n w) :
    D.IsCLift n w :=
  ⟨(D.isOrbitLift_spec h).1, (D.isOrbitLift_spec h).2.1⟩

theorem isCLift_inv {n : ModGL τ k} {w : WeylGroup τ} (h : D.IsCLift n w) :
    D.IsCLift n⁻¹ w⁻¹ := by
  obtain ⟨hC, hN, hw⟩ := h
  refine ⟨inv_mem hC, inv_mem hN, ?_⟩
  have e : (⟨n⁻¹, inv_mem hN⟩ : monomialSubgroup τ k) = (⟨n, hN⟩ : monomialSubgroup τ k)⁻¹ := rfl
  rw [e, map_inv, hw]

theorem isCLift_mul {n n' : ModGL τ k} {w w' : WeylGroup τ} (h : D.IsCLift n w)
    (h' : D.IsCLift n' w') : D.IsCLift (n * n') (w * w') := by
  obtain ⟨hC, hN, hw⟩ := h
  obtain ⟨hC', hN', hw'⟩ := h'
  refine ⟨mul_mem hC hC', mul_mem hN hN', ?_⟩
  have e : (⟨n * n', mul_mem hN hN'⟩ : monomialSubgroup τ k) =
      (⟨n, hN⟩ : monomialSubgroup τ k) * ⟨n', hN'⟩ := rfl
  rw [e, map_mul, hw, hw']

theorem inv_mul_mem_orbitTorus_of_isCLift {n n' : ModGL τ k} {w : WeylGroup τ}
    (hn : D.IsCLift n w) (hn' : D.IsCLift n' w) : n⁻¹ * n' ∈ D.orbitTorus := by
  obtain ⟨hnC, hN, hw⟩ := hn
  obtain ⟨hnC', hN', hw'⟩ := hn'
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hnC) hnC',
    mem_torusGroup_of_mapsRootLines_one (mul_mem (inv_mem hN) hN') ?_⟩
  have h1 := mapsRootLines_weylQuotientHom (⟨n, hN⟩ : monomialSubgroup τ k)
  have h2 := mapsRootLines_weylQuotientHom (⟨n', hN'⟩ : monomialSubgroup τ k)
  rw [hw] at h1
  rw [hw'] at h2
  simpa using h1.inv.mul h2

theorem fixedCell_eq_of_inv_mul_mem {n n' : ModGL τ k} (h : n⁻¹ * n' ∈ D.orbitBorel) :
    D.fixedCell n = D.fixedCell n' := by
  ext g
  rw [mem_fixedCell, mem_fixedCell]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b, hb, (n⁻¹ * n')⁻¹ * b', mul_mem (inv_mem h) hb', by group⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b, hb, (n⁻¹ * n') * b', mul_mem h hb', by group⟩

theorem fixedCell_eq_of_isCLift {n n' : ModGL τ k} {w : WeylGroup τ} (hn : D.IsCLift n w)
    (hn' : D.IsCLift n' w) : D.fixedCell n = D.fixedCell n' :=
  D.fixedCell_eq_of_inv_mul_mem (D.orbitTorus_le_orbitBorel
    (D.inv_mul_mem_orbitTorus_of_isCLift hn hn'))

theorem inv_mem_fixedCell {n g : ModGL τ k} (hg : g ∈ D.fixedCell n) : g⁻¹ ∈ D.fixedCell n⁻¹ := by
  obtain ⟨b, hb, b', hb', rfl⟩ := D.mem_fixedCell.1 hg
  exact D.mem_fixedCell.2 ⟨b'⁻¹, inv_mem hb', b⁻¹, inv_mem hb, by group⟩

theorem self_mem_fixedCell (n : ModGL τ k) : n ∈ D.fixedCell n :=
  D.mem_fixedCell.2 ⟨1, one_mem _, 1, one_mem _, by group⟩

theorem orbitN_eq_mul {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O = D.orbitX O 1 * D.orbitY O (-1) * D.orbitX O 1 := by
  rw [orbitN, orbitX, orbitY, WSL_eq_uSL_vSL_uSL, D.orbitMap_mul hO, D.orbitMap_mul hO]

theorem orbitN_mem_of_lift_mem {A : Subgroup (ModGL τ k)} (hBA : D.orbitBorel ≤ A)
    {w : WeylGroup τ} {x : adjointGroup τ k} (hx : D.IsOrbitLift (x : ModGL τ k) w)
    (hxF : D.F x = x) (hxA : (x : ModGL τ k) ∈ A) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (hneg : (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots) :
    D.orbitN O ∈ A := by
  have hX : ∀ c, D.orbitX O c ∈ A := fun c => hBA (D.orbitX_mem_orbitBorel hO c)
  have hY : ∀ c, D.orbitY O c ∈ A := fun c => by
    have hu := hBA (D.fixedUnipotentM_le_orbitBorel
      (D.conj_orbitY_mem_fixedUnipotentM hO hneg hx hxF c))
    have e : D.orbitY O c = (x : ModGL τ k) *
        ((x : ModGL τ k)⁻¹ * D.orbitY O c * x) * (x : ModGL τ k)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hxA hu) (inv_mem hxA)
  rw [D.orbitN_eq_mul hO]
  exact mul_mem (mul_mem (hX 1) (hY (-1))) (hX 1)

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem orbitBorel_le_orbitGroup : D.orbitBorel ≤ D.orbitGroup := inf_le_left

theorem orbitX_mem_unipotentJ {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (c : D.orbitField O) : D.orbitX O c ∈ D.unipotentJ :=
  rootSpan_mono (fun _ hα => D.mem_posRootsJ_of_mem_orbits hO hα) (D.orbitX_mem_rootSpan hO c)

theorem normalCore_orbitBorel_le_center :
    (D.orbitBorel.subgroupOf D.orbitGroup).normalCore ≤ Subgroup.center D.orbitGroup := by
  set C := D.orbitGroup
  set R := (D.orbitBorel.subgroupOf C).normalCore
  obtain ⟨w₀, hw₀, himg⟩ := D.exists_longest
  obtain ⟨x₀, hx₀, -⟩ := D.exists_fixed_lift hw₀
  obtain ⟨hn₀C, hn₀N, hn₀w⟩ := D.isCLift_of_isOrbitLift hx₀
  set n₀ : ModGL τ k := (x₀ : ModGL τ k) with hn₀def
  have hmaps : MapsRootLines n₀ w₀ := by
    have := mapsRootLines_weylQuotientHom (⟨n₀, hn₀N⟩ : monomialSubgroup τ k)
    rwa [hn₀w] at this
  have hnegroot : ∀ α ∈ negRoots D.roots, IsRoot τ α ∧ height α < 0 := fun α hα => by
    have hαΨ : α ∈ D.roots := by
      have := neg_mem_unionRoots hα.1
      rwa [neg_neg] at this
    exact ⟨isRoot_of_mem_unionRoots hαΨ, (mem_negRoots_iff_height_neg hαΨ).1 hα⟩
  have hconjU : ∀ u ∈ D.unipotentJ, n₀ * u * n₀⁻¹ ∈ negUnipotent τ k := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hn₀N hmaps (S := D.posRootsJ)
      (fun α hα => isRoot_of_mem_unionRoots hα.1) hu
    rw [himg] at h
    exact rootSpan_le_negUnipotent hnegroot h
  have hRT : ∀ x ∈ R, (x : ModGL τ k) ∈ D.orbitTorus := by
    intro x hx
    have hxB : (x : ModGL τ k) ∈ D.orbitBorel :=
      Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
    have hx' : n₀⁻¹ * (x : ModGL τ k) * n₀ ∈ unionBorel k D.χ D.J := by
      have h := hx (⟨n₀, hn₀C⟩ : C)⁻¹
      rw [Subgroup.mem_subgroupOf] at h
      exact D.orbitBorel_le_unionBorel (by simpa using h)
    have hxopp : (x : ModGL τ k) ∈ torusGroup τ k ⊔ negUnipotent τ k := by
      obtain ⟨t, ht, u, hu, htu⟩ := D.exists_torus_mul_unipotent hx'
      have e : (x : ModGL τ k) = (n₀ * t * n₀⁻¹) * (n₀ * u * n₀⁻¹) := by
        calc (x : ModGL τ k) = n₀ * (n₀⁻¹ * (x : ModGL τ k) * n₀) * n₀⁻¹ := by group
          _ = _ := by rw [← htu]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1
        (mem_normalizer_torusGroup_of_mem_monomialSubgroup hn₀N) _).1
          (unionTorus_le_torusGroup ht)))
        (Subgroup.mem_sup_right (hconjU _ hu))
    obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
    have hH : (x : ModGL τ k) ∈ torusGroup τ k := by
      rw [← (opposite_Borel_intersection τ k w₁ hw₁).2.2.1]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxB).2, hxopp⟩
    exact Subgroup.mem_inf.2 ⟨x.2, hH⟩
  have hRU : ∀ x ∈ R, ∀ u ∈ D.unipotentJ, u ∈ C → (x : ModGL τ k) * u = u * x := by
    intro x hx u hu huC
    have hxT := D.orbitTorus_le_torusJ (hRT x hx)
    have h1 : (x : ModGL τ k) * u * (x : ModGL τ k)⁻¹ * u⁻¹ ∈ D.unipotentJ :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (unionTorus_le_normalizer hxT) u).1 hu)
        (inv_mem hu)
    have h2 : (x : ModGL τ k) * u * (x : ModGL τ k)⁻¹ * u⁻¹ ∈ D.torusJ := by
      have hc : x * ((⟨u, huC⟩ : C) * x⁻¹ * (⟨u, huC⟩ : C)⁻¹) ∈ R :=
        mul_mem hx ((Subgroup.normalCore_normal _).conj_mem _ (inv_mem hx) _)
      have h := D.orbitTorus_le_torusJ (hRT _ hc)
      simpa [mul_assoc] using h
    have h3 : (x : ModGL τ k) * u * (x : ModGL τ k)⁻¹ * u⁻¹ = 1 := by
      have h := Subgroup.mem_inf.2 ⟨h2, h1⟩
      rwa [show D.torusJ = unionTorus k D.χ D.J from rfl,
        show D.unipotentJ = unionUnipotent k D.χ D.J from rfl, unionTorus_inf_unionUnipotent,
        Subgroup.mem_bot] at h
    calc (x : ModGL τ k) * u = ((x : ModGL τ k) * u * (x : ModGL τ k)⁻¹ * u⁻¹) * (u * x) := by
          group
      _ = u * x := by rw [h3, one_mul]
  intro x hx
  have hgen : ∀ g ∈ C, (x : ModGL τ k) * g = g * x := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨O, hO, c, rfl | rfl⟩ := hg
      · exact hRU x hx _ (D.orbitX_mem_unipotentJ hO c) (D.orbitMap_mem_orbitGroup hO _)
      · have hN := D.orbitMap_mem_orbitGroup hO WSL
        have hy : (⟨D.orbitN O, hN⟩ : C)⁻¹ * x * (⟨D.orbitN O, hN⟩ : C)⁻¹⁻¹ ∈ R :=
          (Subgroup.normalCore_normal _).conj_mem x hx _
        have h := hRU _ hy _ (D.orbitX_mem_unipotentJ hO (-c)) (D.orbitMap_mem_orbitGroup hO _)
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at h
        rw [D.orbitY_eq hO]
        calc (x : ModGL τ k) * (D.orbitN O * D.orbitX O (-c) * (D.orbitN O)⁻¹) =
            D.orbitN O * (((D.orbitN O)⁻¹ * x * D.orbitN O) * D.orbitX O (-c)) *
              (D.orbitN O)⁻¹ := by group
          _ = D.orbitN O * (D.orbitX O (-c) * ((D.orbitN O)⁻¹ * x * D.orbitN O)) *
              (D.orbitN O)⁻¹ := by rw [h]
          _ = _ := by group
    | one => rw [mul_one, one_mul]
    | mul g h _ _ hg hh =>
      calc (x : ModGL τ k) * (g * h) = (x * g) * h := by group
        _ = g * (x * h) := by rw [hg]; group
        _ = g * h * x := by rw [hh]; group
    | inv g _ hg =>
      calc (x : ModGL τ k) * g⁻¹ = g⁻¹ * (g * x) * g⁻¹ := by group
        _ = g⁻¹ * (x * g) * g⁻¹ := by rw [hg]
        _ = g⁻¹ * x := by group
  rw [Subgroup.mem_center_iff]
  intro s
  exact Subtype.ext (hgen s s.2).symm

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem foldedLength_setReflection {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.foldedLength (setReflection O) = 1 := by
  obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
  have := (D.foldedLength_mul_setReflection hO (one_mem _)).2
    ((D.not_image_subset_negRoots_iff (one_mem _) hO hβ).2 (by
      rw [one_smul]
      exact D.mem_posRootsJ_of_mem_orbits hO hβ))
  rwa [one_mul, D.foldedLength_one] at this

theorem foldedLength_setReflection_mul_setReflection {O P : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (hP : P ∈ D.orbits) (hne : O ≠ P) :
    D.foldedLength (setReflection P * setReflection O) = 2 := by
  obtain ⟨β, hβO⟩ := D.nonempty_of_mem_orbits hO
  have hβP : β ∉ P := fun h => hne ((D.eq_thetaOrbit_of_mem_orbits hO hβO).trans
    (D.eq_thetaOrbit_of_mem_orbits hP h).symm)
  have hrP := D.setReflection_mem_fixedWeyl hP
  have := (D.foldedLength_mul_setReflection hO hrP).2
    ((D.not_image_subset_negRoots_iff hrP hO hβO).2
      (D.setReflection_smul_mem_posRootsJ hP (D.mem_posRootsJ_of_mem_orbits hO hβO) hβP).1)
  rw [this, D.foldedLength_setReflection hP]

theorem sup_orbitBorel_eq_top {M : Subgroup D.orbitGroup} (hM : M.Normal)
    (hMZ : ¬ M ≤ Subgroup.center D.orbitGroup) :
    M ⊔ D.orbitBorel.subgroupOf D.orbitGroup = ⊤ := by
  set B := D.orbitBorel with hB
  set M₀ := M.map D.orbitGroup.subtype with hM₀
  have hM₀C : M₀ ≤ D.orbitGroup := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hconj : ∀ s ∈ D.orbitGroup, ∀ m ∈ M₀, s * m * s⁻¹ ∈ M₀ := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨⟨s, hs⟩ * m * ⟨s, hs⟩⁻¹, hM.conj_mem m hm ⟨s, hs⟩, rfl⟩
  obtain ⟨m, hmM, hmB⟩ : ∃ m ∈ M₀, m ∉ B := by
    by_contra! h
    apply hMZ
    intro x hx
    refine D.normalCore_orbitBorel_le_center (fun b => ?_)
    rw [Subgroup.mem_subgroupOf]
    exact h _ ⟨b * x * b⁻¹, hM.conj_mem x hx b, rfl⟩
  set E := M₀ ⊔ B with hE
  have hBE : B ≤ E := le_sup_right
  have hME : M₀ ≤ E := le_sup_left
  have hBnorm : B ≤ Subgroup.normalizer (M₀ : Set (ModGL τ k)) :=
    fun b hb => Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨fun hy => hconj b (D.orbitBorel_le_orbitGroup hb) y hy, fun hy => by
        have h := hconj b⁻¹ (inv_mem (D.orbitBorel_le_orbitGroup hb)) _ hy
        rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at h⟩
  have hEset : (E : Set (ModGL τ k)) = (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBnorm
  have hlift : ∀ w ∈ D.fixedWeyl, ∃ x : adjointGroup τ k,
      D.IsOrbitLift (x : ModGL τ k) w ∧ D.F x = x := fun w hw => D.exists_fixed_lift hw
  choose! xw hxw hxwF using hlift
  have hmU : m ∈ ⋃ w ∈ D.fixedWeyl, D.fixedCell (xw w) := by
    rw [← D.coe_orbitGroup_eq_iUnion (nw := xw) fun w hw => ⟨hxw w hw, hxwF w hw⟩]
    exact hM₀C hmM
  obtain ⟨w, hw, hmw⟩ := Set.mem_iUnion₂.1 hmU
  obtain ⟨b, hb, b', hb', hbgb⟩ := D.mem_fixedCell.1 hmw
  have hxE : ((xw w : adjointGroup τ k) : ModGL τ k) ∈ E := by
    have e : ((xw w : adjointGroup τ k) : ModGL τ k) = b⁻¹ * m * b'⁻¹ := by
      rw [← hbgb]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBE hb)) (hME hmM)) (inv_mem (hBE hb'))
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hmB
    have h1 : D.IsOrbitLift 1 1 := ⟨[], fun _ h => absurd h List.not_mem_nil, rfl, rfl⟩
    have hT := D.inv_mul_mem_orbitTorus h1 (hxw 1 hw)
    rw [inv_one, one_mul] at hT
    rw [← hbgb]
    exact mul_mem (mul_mem hb (D.orbitTorus_le_orbitBorel hT)) hb'
  obtain ⟨O₀, hO₀, hneg₀⟩ :=
    D.exists_orbits_image_subset_negRoots (inv_mem hw) (inv_ne_one.2 hw1)
  have hO₀E := D.orbitN_mem_of_lift_mem hBE (hxw w hw) (hxwF w hw) hxE hO₀ hneg₀
  have hall : ∀ O ∈ D.orbits, D.orbitN O ∈ E := by
    by_contra! hnot
    obtain ⟨P₀, hP₀, hP₀E⟩ := hnot
    obtain ⟨O, P, ⟨hO, hP, hOP, hadj⟩, hOE, hPE⟩ :=
      exists_edge_of_reflTransGen (P := fun X => D.orbitN X ∈ E)
        (D.orbits_connected hO₀ hP₀) hO₀E hP₀E
    apply hPE
    have hOE' : D.orbitN O ∈ (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) := by
      rw [← hEset]
      exact hOE
    obtain ⟨m₁, hm₁, b₁, hb₁, hmb⟩ := hOE'
    have hrO := D.setReflection_mem_fixedWeyl hO
    have hrP := D.setReflection_mem_fixedWeyl hP
    have hNOC := D.orbitMap_mem_orbitGroup hO WSL
    have hNPC := D.orbitMap_mem_orbitGroup hP WSL
    have hlO := D.isOrbitLift_orbitN hO
    have hlP := D.isOrbitLift_orbitN hP
    have l1 := D.foldedLength_setReflection hO
    have l2 := D.foldedLength_setReflection_mul_setReflection hO hP hOP
    have l2' := D.foldedLength_setReflection_mul_setReflection hP hO hOP.symm
    have l3 := D.foldedLength_braid hO hP hOP hadj
    have hm₁cell : m₁⁻¹ ∈ D.fixedCell (D.orbitN O) := by
      have hsq : D.orbitN O * D.orbitN O ∈ B :=
        D.orbitTorus_le_orbitBorel ⟨mul_mem hNOC hNOC, D.orbitN_mul_self_mem_torusGroup hO⟩
      refine D.mem_fixedCell.2 ⟨b₁, hb₁, (D.orbitN O * D.orbitN O)⁻¹, inv_mem hsq, ?_⟩
      have e : m₁ = D.orbitN O * b₁⁻¹ := by
        rw [← hmb]
        group
      rw [e]
      group
    have h1 : D.orbitN P * m₁⁻¹ ∈ D.fixedCell (D.orbitN P * D.orbitN O) := by
      rw [← (D.fixedCell_orbitN_mul_fixedCell hP hrO hlO).1 (by rw [l2, l1])]
      exact Set.mul_mem_mul (D.self_mem_fixedCell _) hm₁cell
    have h2 : m₁ * (D.orbitN P)⁻¹ ∈ D.fixedCell (D.orbitN O * D.orbitN P) := by
      have h := D.inv_mem_fixedCell h1
      have e1 : (D.orbitN P * m₁⁻¹)⁻¹ = m₁ * (D.orbitN P)⁻¹ := by group
      rw [e1] at h
      rwa [D.fixedCell_eq_of_isCLift
        (D.isCLift_inv (D.isCLift_mul (D.isCLift_of_isOrbitLift hlP)
          (D.isCLift_of_isOrbitLift hlO)))
        (by
          have h' := D.isCLift_mul (D.isCLift_of_isOrbitLift hlO) (D.isCLift_of_isOrbitLift hlP)
          rwa [show setReflection O * setReflection P =
            (setReflection P * setReflection O)⁻¹ by
              rw [mul_inv_rev, D.setReflection_inv hO, D.setReflection_inv hP]] at h')] at h
    have hlOP := D.isOrbitLift_orbitN_mul hO hlP
    have h3 : D.orbitN P * m₁ * (D.orbitN P)⁻¹ ∈
        D.fixedCell (D.orbitN P * (D.orbitN O * D.orbitN P)) := by
      rw [← (D.fixedCell_orbitN_mul_fixedCell hP (mul_mem hrO hrP) hlOP).1
        (by rw [← mul_assoc, l3, l2']), mul_assoc]
      exact Set.mul_mem_mul (D.self_mem_fixedCell _) h2
    have hl3 := D.isOrbitLift_orbitN_mul hP hlOP
    obtain ⟨-, -, x₃, hx₃, hx₃F⟩ := D.isOrbitLift_spec hl3
    obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := D.mem_fixedCell.1 h3
    have hx₃E : ((x₃ : adjointGroup τ k) : ModGL τ k) ∈ E := by
      rw [hx₃]
      have e : D.orbitN P * (D.orbitN O * D.orbitN P) =
          c₁⁻¹ * (D.orbitN P * m₁ * (D.orbitN P)⁻¹) * c₂⁻¹ := by
        rw [← hc]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBE hc₁)) (hME (hconj _ hNPC m₁ hm₁)))
        (inv_mem (hBE hc₂))
    have hw' := mul_mem hrP (mul_mem hrO hrP)
    have hdesc : (fun γ => (setReflection P * (setReflection O * setReflection P))⁻¹ • γ) '' P ⊆
        negRoots D.roots := by
      refine (D.foldedLength_setReflection_mul hP hw').1.1 ?_
      rw [← mul_assoc (setReflection P) (setReflection P), D.setReflection_mul_self hP, one_mul,
        ← mul_assoc, l3, l2']
    exact D.orbitN_mem_of_lift_mem hBE (hx₃ ▸ hl3) hx₃F hx₃E hP hdesc
  have hCE : D.orbitGroup ≤ E := by
    rw [D.orbitGroup_eq_closure, Subgroup.closure_le]
    rintro _ (hb | ⟨O, hO, rfl⟩)
    · exact hBE hb
    · exact hall O hO
  rw [eq_top_iff]
  intro s _
  have hs : (s : ModGL τ k) ∈ (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) := by
    rw [← hEset]
    exact hCE s.2
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hs
  obtain ⟨m'', hm'', rfl⟩ := hm'
  simp only [Subgroup.coe_subtype] at hmb
  have hb₀C : b₀ ∈ D.orbitGroup := by
    have e : b₀ = (m'' : ModGL τ k)⁻¹ * s := by
      rw [← hmb]
      group
    rw [e]
    exact mul_mem (inv_mem m''.2) s.2
  have hs' : s = m'' * ⟨b₀, hb₀C⟩ := Subtype.ext hmb.symm
  rw [hs']
  exact mul_mem (Subgroup.mem_sup_left hm'')
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb₀))

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem conj_mem_fixedUnipotentM {b u : ModGL τ k} (hb : b ∈ D.orbitBorel)
    (hu : u ∈ D.fixedUnipotentM) : b * u * b⁻¹ ∈ D.fixedUnipotentM := by
  have h := D.fixedUnipotentM_normal.conj_mem ⟨u, D.fixedUnipotentM_le_orbitBorel hu⟩
    (Subgroup.mem_subgroupOf.2 hu) ⟨b, hb⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem commutator_mem_fixedUnipotentM {x y : ModGL τ k} (hx : x ∈ D.orbitBorel)
    (hy : y ∈ D.orbitBorel) : x * y * x⁻¹ * y⁻¹ ∈ D.fixedUnipotentM := by
  rw [← SetLike.mem_coe, D.coe_orbitBorel_eq_mul] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hy
  have haB := D.orbitTorus_le_orbitBorel ha
  have hcB := D.orbitTorus_le_orbitBorel hc
  have e : a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = (a * b * a⁻¹) *
      ((a * c) * (d * b⁻¹) * (a * c)⁻¹) * (a * c * a⁻¹ * c⁻¹) * (c * d⁻¹ * c⁻¹) := by
    group
  rw [e, show a * c * a⁻¹ * c⁻¹ = 1 by
    rw [D.mul_comm_of_mem_orbitTorus ha hc]
    group, mul_one]
  exact mul_mem (mul_mem (D.conj_mem_fixedUnipotentM haB hb)
    (D.conj_mem_fixedUnipotentM (mul_mem haB hcB) (mul_mem hd (inv_mem hb))))
    (D.conj_mem_fixedUnipotentM hcB (inv_mem hd))

theorem isSolvable_orbitBorel : Group.IsSolvable D.orbitBorel := by
  set U' := D.fixedUnipotentM.subgroupOf D.orbitBorel
  have : U'.Normal := D.fixedUnipotentM_normal
  have := D.isNilpotent_fixedUnipotentM
  have : Group.IsNilpotent U' := (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe
    D.fixedUnipotentM_le_orbitBorel)).2 inferInstance
  have : Group.IsSolvable (D.orbitBorel ⧸ U') := Group.isSolvable_of_comm fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : D.orbitBorel) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by
      group
    rw [e]
    exact D.commutator_mem_fixedUnipotentM (inv_mem y.2) (inv_mem x.2)
  exact Group.isSolvable_of_ker_le_range U'.subtype (QuotientGroup.mk' U')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_orbitBorel_subgroupOf :
    Group.IsSolvable (D.orbitBorel.subgroupOf D.orbitGroup) := by
  have := D.isSolvable_orbitBorel
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe D.orbitBorel_le_orbitGroup).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe D.orbitBorel_le_orbitGroup).symm.surjective

theorem isSolvable_quotient_of_not_le_center {M : Subgroup D.orbitGroup} (hM : M.Normal)
    (hMZ : ¬ M ≤ Subgroup.center D.orbitGroup) : Group.IsSolvable (D.orbitGroup ⧸ M) := by
  have htop := D.sup_orbitBorel_eq_top hM hMZ
  have := D.isSolvable_orbitBorel_subgroupOf
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp
      (D.orbitBorel.subgroupOf D.orbitGroup).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ M ⊔ D.orbitBorel.subgroupOf D.orbitGroup := htop ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨m, hm, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
  exact Group.isSolvable_of_surjective hsurj

theorem nontrivial_orbitGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Nontrivial D.orbitGroup := by
  refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
  have h1 := D.orbitMap_mem_orbitGroup hO (uSL 1)
  rw [h, Subgroup.mem_bot] at h1
  have h0 : D.orbitX O 0 = 1 := by rw [orbitX, uSL_zero_eq_one, D.orbitMap_one]
  exact one_ne_zero (D.orbitX_injective hO (h1.trans h0.symm))

theorem isQuasisimple_orbitGroup_of_isPerfect {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hperf : Group.IsPerfect D.orbitGroup) : CFSG.IsQuasisimple D.orbitGroup := by
  have := D.nontrivial_orbitGroup hO
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun M hM => ?_
  by_cases hZ : M ≤ Subgroup.center D.orbitGroup
  · exact Or.inl hZ
  · have := hM
    exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      D.isSolvable_orbitBorel_subgroupOf (D.sup_orbitBorel_eq_top hM hZ))

@[expose] def orbitGroupEquiv :
    (D.orbitGroupC.subgroupOf D.fixedGroup) ≃* D.orbitGroup :=
  (Subgroup.subgroupOfEquivOfLe D.orbitGroupC_le_fixedGroup).trans
    ((Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup))

end GenFixedRootDatum

end CFSG.RankThree.Lattice
