module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootSeed
public import CFSG.Monster.B.TwoA.Fischer.CertRemOrbit
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3069
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3068
public import Certificates.Certificate16003
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

theorem ncard_orbit_perm_mul {G : Type*} [Group G] (π : G →* Equiv.Perm fixedL) (u : fixedL) :
    {u' | ∃ g : G, u' = π g u}.ncard *
      Nat.card ((MulAction.stabilizer (Equiv.Perm fixedL) u).comap π) = Nat.card G := by
  let _ := MulAction.compHom fixedL π
  have h1 : {u' | ∃ g : G, u' = π g u} = MulAction.orbit G u := by
    ext u'
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
  have h2 : (MulAction.stabilizer (Equiv.Perm fixedL) u).comap π = MulAction.stabilizer G u := by
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    rfl
  rw [h1, h2, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]

theorem actStar_mem_rootVecSet
    (γ : GStar) {u : fixedL} (hu : u ∈ rootVecSet) :
    actStar γ u ∈ rootVecSet := by
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨hx', e⟩ := rootVecOf_conj_star γ hx (conj_inl γ x).symm
  exact ⟨_, hx', e⟩

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem conj_iff_mem_hOrbit
    (ρ : sliceGroup lab Y →* stdGroup) {x x' : stdGroup}
    (hx : IsConj rootInv x) (hx' : IsConj rootInv x') :
    (∃ h : sliceGroup lab Y, x' = ρ h * x * (ρ h)⁻¹) ↔ rootVecOf x' ∈ hOrbit ρ (rootVecOf x) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [rootVecOf_conj hx, actStar_inl_eq_gL]⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, bijOn_rootVecOf.injOn hx' (conj_mem_rootClass hx _) ?_⟩
    rw [hh, rootVecOf_conj hx, actStar_inl_eq_gL]

theorem conj_mem_sliceGroup {q : S} (hq : ∀ y ∈ Y, act q y ∈ Y) (hS : IsFischerSlice act lab Y)
    {h : S} (hh : h ∈ sliceGroup lab Y) : q * h * q⁻¹ ∈ sliceGroup lab Y := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨y, hy, rfl⟩ := hh
    rw [← hS.lab_act]
    exact lab_mem_sliceGroup (hq y hy)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ by group]
    exact inv_mem ha

@[expose] def orbitReps
    (ρ : sliceGroup lab Y →* stdGroup) (Φ : Y ≃ CFSG.Monster.B.Fischer.Y)
    (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL) (s : Fin 4 → sliceGroup lab Y) (q : stdGroup)
    (y₀ : Y) : Fin 4 → fixedL :=
  ![Ψ (ncommVec lab Y y₀), cliqueFixedVec Φ Ψ, seedRootVec ρ s q (cliqueFixedVec Φ Ψ),
    cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)]

theorem ncard_commute_lab_ne (hS : IsFischerSlice act lab Y) (y' : Y) :
    {y : Y | y ≠ y' ∧ Commute (lab y') (lab y)}.ncard = 693 := by
  have e : Subtype.val '' {y : Y | y ≠ y' ∧ Commute (lab y') (lab y)} =
      (sliceGraph lab Y).neighborSet y' := by
    ext v
    constructor
    · rintro ⟨y, ⟨hne, hc⟩, rfl⟩
      exact ⟨y'.2, y.2, fun e => hne (Subtype.ext e.symm), hc⟩
    · rintro ⟨-, hv, hne, hc⟩
      exact ⟨⟨v, hv⟩, ⟨fun e => hne (congrArg Subtype.val e).symm, hc⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, e, hS.valency y' y'.2]

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
  {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
  {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
  (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
  {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
include H hΦ

omit hΦ in
theorem conjHom_fourGens
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    (k : Fin 4) : H.conjHom Φ (s k) = jGen (Cert.fourGen k) := by
  rw [← fourGens_eq]
  refine Equiv.ext fun u => ?_
  obtain ⟨v, rfl⟩ := Φ.surjective u
  rw [← H.phi_act (s k) v (H.slice.mapsTo _ (s k).2 _ v.2)]
  exact hs k v _ rfl

include hroot hΨ in
theorem reach4_mem_hOrbit
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {v₀ v : Fin 78 → ZMod 2} (hv : Cert.Reach4 v₀ v) :
    H.coordEquiv hΦ Ψ v ∈ hOrbit ρ (H.coordEquiv hΦ Ψ v₀) := by
  induction hv with
  | refl => exact mem_hOrbit_self _ _
  | step k hk _ ih =>
    rw [← H.gL_coordEquiv_fourMat hΦ hroot hΨ hk (H.conjHom_fourGens hs ⟨k, hk⟩),
      ← actH_eq_gL]
    exact actH_mem_hOrbit ρ ih _

include hρ hroot hΨ in
theorem le_ncard_hOrbit_seed
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {q : stdGroup} (hq : IsConj rootInv q) (hqz : rootVecOf q = cliqueFixedVec Φ Ψ) :
    694980 ≤ (hOrbit ρ (seedRootVec ρ s q (cliqueFixedVec Φ Ψ))).ncard := by
  have := finite_fixedL
  obtain ⟨O, hcard, hreach⟩ := Cert.fischer_rem_orbit_certificate
  have hsub : H.coordEquiv hΦ Ψ '' O ⊆
      hOrbit ρ (seedRootVec ρ s q (cliqueFixedVec Φ Ψ)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [H.seedRootVec_eq hΦ hρ hroot hΨ hs hq hqz]
    exact H.reach4_mem_hOrbit hΦ hroot hΨ hs (hreach v hv)
  calc 694980 = (H.coordEquiv hΦ Ψ '' O).ncard := by
        rw [Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end FullIntertwinerHyp

namespace IsFischerSlice

theorem complete_ambient_root_orbits_core
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {qC : stdGroup} (hqC : IsConj rootInv qC) (hqCz : rootVecOf qC = cliqueFixedVec Φ Ψ)
    (Q : Subgroup S) (hHQ : sliceGroup lab Y ≤ Q) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, act q y ∈ Y)
    (ρQ : Q →* GStar)
    (hρQ : ∀ (h : S) (hh : h ∈ sliceGroup lab Y),
      ρQ ⟨h, hHQ hh⟩ = SemidirectProduct.inl (ρ ⟨h, hh⟩)) :
    (∀ u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q},
      ∃! k : Fin 4, u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)) ∧
    (∀ k : Fin 4, (hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)).ncard =
      (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 4, Nat.card (stabH ρ (orbitReps ρ Φ Ψ s qC y₀ k)) =
      (![18393661440, 454164480, 92897280, 20643840] : Fin 4 → ℕ) k) ∧
    (∀ x x' : stdGroup, IsConj rootInv x → IsConj rootInv x' →
      ((∃ h : sliceGroup lab Y, x' = ρ h * x * (ρ h)⁻¹) ↔
        rootVecOf x' ∈ hOrbit ρ (rootVecOf x))) ∧
    (∀ k : Fin 4, ∀ u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k), ∀ q : stdGroup,
      IsConj rootInv q → rootVecOf q = u →
      {y : Y | ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ q ∧
        Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard =
        (![693, 22, 126, 22] : Fin 4 → ℕ) k) ∧
    ∀ k : Fin 4, {u' | ∃ q : Q, u' = actStar (ρQ q) (orbitReps ρ Φ Ψ s qC y₀ k)} =
      hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k) := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  have := finite_fixedL
  obtain ⟨-, -, hlab, h0, h1, h3, hd01, hd03, hd13, hsubU, hc1, hc3, hrem, hinv⟩ :=
    hS.two_additional_ambient_root_orbits hC hx hη hθ hφ hα hΦ hρ hroot hΨ hy₀
  obtain ⟨-, -, hseed⟩ := hS.explicit_126_neighbor_ambient_root hC hx hη hθ hφ hα hΦ hρ hroot hΨ
  obtain ⟨hmem, -, hcount, hremmem⟩ := hseed s hs qC hqC hqCz
  set z := cliqueFixedVec Φ Ψ with hz
  set a := fun y : Y => Ψ (ncommVec lab Y y) with ha
  set aS := seedRootVec ρ s qC z with haS
  set U := Set.range a ∪ hOrbit ρ z ∪ hOrbit ρ (z + a y₀) with hU
  have hO2 : hOrbit ρ aS = rootVecSet \ U := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨h, rfl⟩
      exact hinv h _ (hremmem y₀ hy₀)
    · rw [hrem]
      exact H.le_ncard_hOrbit_seed hΦ hρ hroot hΨ hs hqC hqCz
  have hsize : ∀ k : Fin 4, (hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)).ncard =
      (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k := by
    intro k
    fin_cases k
    · change (hOrbit ρ (a y₀)).ncard = 3510
      rw [hlab, h0]
    · exact h1
    · change (hOrbit ρ aS).ncard = 694980
      rw [hO2, hrem]
    · exact h3
  have hsize_inj : Function.Injective (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) := by
    decide
  have hcover : ∀ u ∈ rootVecSet, ∃ k : Fin 4, u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k) := by
    intro u hu
    by_cases hU' : u ∈ U
    · rcases hU' with (hu0 | hu1) | hu3
      · exact ⟨0, by change u ∈ hOrbit ρ (a y₀); rw [hlab]; exact hu0⟩
      · exact ⟨1, hu1⟩
      · exact ⟨3, hu3⟩
    · exact ⟨2, by change u ∈ hOrbit ρ aS; rw [hO2]; exact ⟨hu, hU'⟩⟩
  have huniq : ∀ (u : fixedL) (k k' : Fin 4), u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k) →
      u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k') → k = k' := by
    intro u k k' hk hk'
    apply hsize_inj
    rw [← hsize k, ← hsize k', ← hOrbit_eq_of_mem hk, ← hOrbit_eq_of_mem hk']
  have hreps_mem : ∀ k : Fin 4, orbitReps ρ Φ Ψ s qC y₀ k ∈ rootVecSet := by
    intro k
    fin_cases k
    · exact psi_mem_rootVecSet hroot hΨ y₀
    · exact H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
    · exact hmem
    · exact H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy₀
  have hQorb : ∀ k : Fin 4, {u' | ∃ q : Q, u' = actStar (ρQ q) (orbitReps ρ Φ Ψ s qC y₀ k)} =
      hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k) := by
    intro k
    apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      set u := orbitReps ρ Φ Ψ s qC y₀ k
      set u' := actStar (ρQ q) u
      have hu' : u' ∈ rootVecSet := actStar_mem_rootVecSet _ (hreps_mem k)
      have himg : actStar (ρQ q) '' hOrbit ρ u = hOrbit ρ u' := by
        have key : ∀ h : sliceGroup lab Y, actStar (ρQ q) (actH ρ h u) =
            actH ρ ⟨(q : S) * h * (q : S)⁻¹, conj_mem_sliceGroup (hQY q q.2) hS h.2⟩ u' := by
          intro h
          have e : ρQ q * SemidirectProduct.inl (ρ h) =
              SemidirectProduct.inl (ρ ⟨(q : S) * h * (q : S)⁻¹,
                conj_mem_sliceGroup (hQY q q.2) hS h.2⟩) * ρQ q := by
            rw [← hρQ, ← hρQ, ← map_mul, ← map_mul]
            congr 1
            exact Subtype.ext (by simp only [Subgroup.coe_mul, inv_mul_cancel_right])
          change (actStar (ρQ q) * actStar (SemidirectProduct.inl (ρ h))) u =
            (actStar (SemidirectProduct.inl _) * actStar (ρQ q)) u
          rw [← map_mul, ← map_mul, e]
        ext w
        constructor
        · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
          exact ⟨_, key h⟩
        · rintro ⟨h, rfl⟩
          have hmem' : (q : S)⁻¹ * h * q ∈ sliceGroup lab Y := by
            simpa using conj_mem_sliceGroup (q := (q : S)⁻¹)
              (fun y hy => hQY _ (inv_mem q.2) y hy) hS h.2
          refine ⟨actH ρ ⟨(q : S)⁻¹ * h * q, hmem'⟩ u, ⟨_, rfl⟩, ?_⟩
          rw [key]
          have e : (⟨(q : S) * ((q : S)⁻¹ * h * q) * (q : S)⁻¹,
              conj_mem_sliceGroup (hQY q q.2) hS hmem'⟩ : sliceGroup lab Y) = h :=
            Subtype.ext (show (q : S) * ((q : S)⁻¹ * h * q) * (q : S)⁻¹ = h by group)
          rw [e]
          rfl
      obtain ⟨k', hk'⟩ := hcover u' hu'
      have e1 : (hOrbit ρ u').ncard = (hOrbit ρ u).ncard := by
        rw [← himg, Set.ncard_image_of_injective _ (Equiv.injective _)]
      have e2 : k' = k := by
        apply hsize_inj
        rw [← hsize k, ← hsize k', ← hOrbit_eq_of_mem hk', e1]
      rw [e2] at hk'
      exact hk'
    · rintro _ ⟨h, rfl⟩
      exact ⟨⟨h, hHQ h.2⟩, by rw [hρQ h h.2]⟩
  refine ⟨fun u hu => ?_, hsize, fun k => ?_, fun x x' hx hx' => conj_iff_mem_hOrbit ρ hx hx',
    fun k u hu q hq hqu => ?_, hQorb⟩
  · obtain ⟨k, hk⟩ := hcover u hu
    exact ⟨k, hk, fun k' hk' => huniq u k' k hk' hk⟩
  · have h := ncard_hOrbit_mul ρ (orbitReps ρ Φ Ψ s qC y₀ k)
    rw [hsize k, H.card_sliceGroup hΦ] at h
    fin_cases k <;> simp at h ⊢ <;> omega
  · have hnot : k ≠ 0 → ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ q := by
      intro hk0 y hy
      apply hk0
      refine huniq u k 0 hu ?_
      change u ∈ hOrbit ρ (a y₀)
      rw [hlab, ← hqu, ← hy]
      exact ⟨y, hΨ y⟩
    have hdrop : k ≠ 0 → {y : Y | ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ q ∧
        Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
          {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} := fun hk0 =>
      Set.ext fun y => and_iff_right (hnot hk0 y)
    fin_cases k
    · change u ∈ hOrbit ρ (a y₀) at hu
      rw [hlab] at hu
      obtain ⟨y', rfl⟩ := hu
      have e : q = ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩ :=
        bijOn_rootVecOf.injOn hq (hroot y') (hqu.trans (hΨ y'))
      subst e
      have e2 : {y : Y | ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩ ∧
          Commute (ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩) (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
          {y : Y | y ≠ y' ∧ Commute (lab y') (lab y)} := by
        ext y
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, IsFischerSlice.commute_rho_iff hρ y' y]
        refine and_congr_left' ⟨fun h e => h (by rw [e]), fun h e => h ?_⟩
        exact Subtype.ext (hS.injOn y.2 y'.2 (congrArg Subtype.val (hρ e)))
      rw [e2, ncard_commute_lab_ne hS y']
      rfl
    · rw [hdrop (by decide)]
      exact hc1 u hu q hq hqu
    · rw [hdrop (by decide)]
      obtain ⟨q₀, hq₀, hq₀a⟩ := hmem
      rw [H.ncard_commute_of_mem_hOrbit hu hq₀ hq hq₀a hqu, (hcount q₀ hq₀ hq₀a).2]
      rfl
    · rw [hdrop (by decide)]
      exact hc3 u hu q hq hqu
theorem complete_ambient_root_orbits
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {qC : stdGroup} (hqC : IsConj rootInv qC) (hqCz : rootVecOf qC = cliqueFixedVec Φ Ψ)
    (Q : Subgroup S) (hHQ : sliceGroup lab Y ≤ Q) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, act q y ∈ Y)
    (ρQ : Q →* GStar)
    (hρQ : ∀ (h : S) (hh : h ∈ sliceGroup lab Y),
      ρQ ⟨h, hHQ hh⟩ = SemidirectProduct.inl (ρ ⟨h, hh⟩))
    (hQcard : Nat.card Q = 2 * Nat.card (sliceGroup lab Y)) :
    (∀ u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q},
      ∃! k : Fin 4, u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)) ∧
    (∀ k : Fin 4, (hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)).ncard =
      (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 4, Nat.card (stabH ρ (orbitReps ρ Φ Ψ s qC y₀ k)) =
      (![18393661440, 454164480, 92897280, 20643840] : Fin 4 → ℕ) k) ∧
    (∀ x x' : stdGroup, IsConj rootInv x → IsConj rootInv x' →
      ((∃ h : sliceGroup lab Y, x' = ρ h * x * (ρ h)⁻¹) ↔
        rootVecOf x' ∈ hOrbit ρ (rootVecOf x))) ∧
    (∀ k : Fin 4, ∀ u ∈ hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k), ∀ q : stdGroup,
      IsConj rootInv q → rootVecOf q = u →
      {y : Y | ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ q ∧
        Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard =
        (![693, 22, 126, 22] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 4, {u' | ∃ q : Q, u' = actStar (ρQ q) (orbitReps ρ Φ Ψ s qC y₀ k)} =
      hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k)) ∧
    ∀ k : Fin 4, Nat.card ((MulAction.stabilizer (Equiv.Perm fixedL)
      (orbitReps ρ Φ Ψ s qC y₀ k)).comap (actStar.comp ρQ)) =
        (![36787322880, 908328960, 185794560, 41287680] : Fin 4 → ℕ) k := by
  obtain ⟨hpart, hsize, hstab, hconj, hcount, hQorb⟩ :=
    hS.complete_ambient_root_orbits_core hC hx hη hθ hφ hα hΦ hρ hroot hΨ hy₀ hs hqC hqCz Q hHQ
      hQY ρQ hρQ
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  refine ⟨hpart, hsize, hstab, hconj, hcount, hQorb, fun k => ?_⟩
  have h := ncard_orbit_perm_mul (actStar.comp ρQ) (orbitReps ρ Φ Ψ s qC y₀ k)
  have e : {u' | ∃ q : Q, u' = (actStar.comp ρQ) q (orbitReps ρ Φ Ψ s qC y₀ k)} =
      hOrbit ρ (orbitReps ρ Φ Ψ s qC y₀ k) := hQorb k
  rw [e, hsize k, hQcard, H.card_sliceGroup hΦ] at h
  fin_cases k <;> simp at h ⊢ <;> omega

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
