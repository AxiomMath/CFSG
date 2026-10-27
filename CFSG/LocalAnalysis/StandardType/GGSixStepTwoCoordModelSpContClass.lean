module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpContSwap

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective spEnd spSupported mem_spSupported
  SpPrimaryBlocks altPrimaryData_spLin)
open CFSG.RankThree.PartOne (spPull)
open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryComponent mem_primaryComponent
  apply_mem_primaryComponent)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace SpNsCont

open CoordSpNs

section Generic

theorem commute_spEnd {F : Type} [Field F] {n : ℕ} {Y x : StatedSp n F} (h : Y * x = x * Y) :
    Commute (spEnd Y) (spEnd x) := by
  have h2 : spEnd (Y * x) = spEnd (x * Y) := by rw [h]
  change ((spLin n F (Y * x) : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      Module.End F (Fin n ⊕ Fin n → F)) =
    ((spLin n F (x * Y) : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      Module.End F (Fin n ⊕ Fin n → F)) at h2
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul] at h2
  exact h2

theorem fix_of_forall_primary {F : Type} [Field F] {n f p : ℕ} {x Y : StatedSp n F}
    (blocks : SpPrimaryBlocks 2 f p x (proj n F x))
    (h : ∀ k ∈ primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) k, spEnd Y v = v)
    (v : Fin n ⊕ Fin n → F) : spEnd Y v = v := by
  classical
  have hsq := blocks.isInternal.submodule_iSup_eq_top
  have hv : v ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : F[X]) := by
    rw [hsq]
    trivial
  refine Submodule.iSup_induction (fun k : primaryFactors (spEnd x) =>
    primaryComponent (spEnd x) (k : F[X])) (motive := fun v => spEnd Y v = v) hv ?_ ?_ ?_
  · intro k v hv
    exact h k k.2 v hv
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb]

theorem frame_induction {F D κ : Type} [Field F] [AddCommGroup D] [Module F D] {s : ℕ}
    (S : Set (Fin s)) {P : (Fin s → D) × (κ → F) → Prop} (hadd : ∀ a b, P a → P b → P (a + b))
    (h0 : ∀ y : (Fin s → D) × (κ → F), (∀ i ∈ S, y.1 i = 0) → P y)
    (h1 : ∀ j ∈ S, ∀ z : D, P (Pi.single j z, 0)) (y : (Fin s → D) × (κ → F)) : P y := by
  classical
  have key : y = ((fun k => if k ∈ S then 0 else y.1 k), y.2) +
      ∑ j ∈ Finset.univ.filter (· ∈ S), ((Pi.single j (y.1 j) : Fin s → D), (0 : κ → F)) := by
    refine Prod.ext (funext fun k => ?_) ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Pi.add_apply, Finset.sum_apply, Pi.single_apply,
        Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hk : k ∈ S <;> simp [hk]
    · simp only [Prod.snd_add, Prod.snd_sum, Finset.sum_const_zero, add_zero]
  rw [key]
  refine hadd _ _ (h0 _ fun i hi => by simp [hi]) ?_
  exact Finset.sum_induction _ P hadd (h0 0 fun i _ => rfl) fun j hj =>
    h1 j (Finset.mem_filter.mp hj).2 _

theorem eq_mul_of_aligned {s p : ℕ} {β : Fin s → ZMod p} {η : Fin s → (ZMod p)ˣ} {k l : Fin s}
    (h : (η k : ZMod p) * β k = (η l : ZMod p) * β l) :
    β l = (((η l)⁻¹ * η k : (ZMod p)ˣ) : ZMod p) * β k := by
  rw [Units.val_mul, mul_assoc, h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul]

theorem eq_sum_smul_ite {R : Type*} [CommRing R] {s : ℕ} (S : Set (Fin s))
    [DecidablePred (· ∈ S)] (i₀ : Fin s) (t u : Fin s → R) (ht : ∀ i ∉ S, t i = 0)
    (hu0 : ∑ i, t i * u i = 0) :
    t = ∑ i, t i • (if i ∈ S then Pi.single i 1 - Pi.single i₀ (u i) else 0) := by
  funext k
  rw [Finset.sum_apply]
  have h1 : ∀ i, (t i • (if i ∈ S then Pi.single i 1 - Pi.single i₀ (u i) else 0 :
      Fin s → R)) k = (if k = i then t i else 0) - (if k = i₀ then t i * u i else 0) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
        mul_sub]
      congr 1 <;> split_ifs <;> simp
    · simp [hi, ht i hi]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  by_cases hk : k = i₀
  · simp [hk, hu0]
  · simp [hk]

theorem sum_mul_eq_zero_of {R : Type*} [CommRing R] {s : ℕ} (t v u : Fin s → R) (a : R)
    (hu : ∀ i, u i = a * v i) (h : ∑ i, v i * t i = 0) : ∑ i, t i * u i = 0 := by
  calc ∑ i, t i * u i = a * ∑ i, v i * t i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hu]; ring
    _ = 0 := by rw [h, mul_zero]

end Generic

section Class

variable {F : Type} [Field F] [Finite F] [CharP F 2] {g : F[X]} [Fact (Irreducible g)] {n p : ℕ}
  [Fact p.Prime] {D : Type} [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D}
  (hc : c ^ p = 1) {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
  {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
  (hcω : ∀ x y, ω (c x) (c y) = ω x y)

theorem torElt_sub_mem (hp2 : p ≠ 2) (hbt : NsBlockType g p D c)
    (hζ : AdjoinRoot.root g ^ p = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    {β : Fin s → ZMod p} {S : Set (Fin s)} {η : Fin s → (ZMod p)ˣ} {c₀ : ZMod p} (hc₀ : c₀ ≠ 0)
    (hηO : ∀ i, η i ∈ galSigns p (Nat.card F)) (hal : ∀ i ∈ S, (η i : ZMod p) * β i = c₀)
    {L : Subgroup (StatedSp n F)}
    (hL : IsComponentOf L (Subgroup.centralizer {torElt hc hdec hcω β}))
    (hLfix : ∀ Y ∈ L, ∀ y : (Fin s → D) × (κ → F), (∀ i ∈ S, y.1 i = 0) → frameEnd Φ Y y = y)
    {i j : Fin s} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    torElt hc hdec hcω (Pi.single i 1 - Pi.single j (((η j)⁻¹ * η i : (ZMod p)ˣ) : ZMod p)) ∈
      L := by
  classical
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have : Nontrivial D := nontrivial_of_blockType hbt
  have hβ : ∀ k ∈ S, β k ≠ 0 := fun k hk h0 => hc₀ (by rw [← hal k hk, h0, mul_zero])
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (F := F)
  have blocks := spPrimaryBlocks_torElt hc hdec hcω hp2 hbt hζ hprim (hβ i hi) hf hK
  have hxp := torElt_pow_p hc hdec hcω β
  have H := altPrimaryData_spLin hpF hxp
  have htw := galSigns_le_twistGroup hbt hζ hprim hc (isAlt_of_dec hdec i)
    (nondegenerate_of_dec hdec i) hcω
  have hswap : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → ∃ (Y : StatedSp n F) (T : D ≃ₗ[F] D),
      Y * torElt hc hdec hcω β = torElt hc hdec hcω β * Y ∧
      Y * torElt hc hdec hcω (Pi.single k (1 : ZMod p)) =
        torElt hc hdec hcω (Pi.single l (((η l)⁻¹ * η k : (ZMod p)ˣ) : ZMod p)) * Y ∧
      (∀ z : D, frameEnd Φ Y (Pi.single k z, 0) = (Pi.single l (T z), 0)) ∧
      ∀ y : (Fin s → D) × (κ → F), y.1 k = 0 → y.1 l = 0 → frameEnd Φ Y y = y := by
    intro k hk l hl hkl
    have hkl' : (η k : ZMod p) * β k = (η l : ZMod p) * β l := by rw [hal k hk, hal l hl]
    obtain ⟨Y, T, h1, h2, h3, h4⟩ := exists_swap hdec hc hcω hkl
      (htw ((galSigns _ _).mul_mem ((galSigns _ _).inv_mem (hηO l)) (hηO k)))
      (htw ((galSigns _ _).mul_mem ((galSigns _ _).inv_mem (hηO k)) (hηO l)))
      (eq_mul_of_aligned hkl') (eq_mul_of_aligned hkl'.symm)
    refine ⟨Y, T, h1, ?_, h3, h4⟩
    rw [h2, mul_inv_rev, inv_inv]
  obtain ⟨h, hh, hLO⟩ := SevSpNs.exists_le_spSupported blocks hL
  have hX1 : h ≠ X - 1 := by
    rintro rfl
    refine false_of_forall_fix hL fun Y hY => fix_of_forall_primary blocks fun k hk v hv => ?_
    by_cases hk1 : k = X - 1
    · rw [hk1, blocks.fixed_eq, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] at hv
      have h1 := hLfix Y hY (Φ.symm v) fun l hl => by
        have h2 := spEnd_torElt hc hdec hcω β (Φ.symm v)
        rw [LinearEquiv.apply_symm_apply, hv] at h2
        have h3 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 l)
          (congrArg Φ.symm h2)
        simp only [LinearEquiv.symm_apply_apply, torD_apply'] at h3
        exact block_pow_fix hbt hζ hprim (hβ l hl) h3.symm
      rw [frameEnd_apply, LinearEquiv.apply_symm_apply] at h1
      exact Φ.symm.injective h1
    · refine (mem_spSupported.mp (hLO hY)).2 k hk ?_ v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, or_self]
      exact hk1
  have hq := SevSpNs.isQuasisimple_spPull_of_le (h := ⟨h, hh⟩) hpp hp2 hf blocks hX1 hL hLO
  have hLeq := SevSpNs.eq_spPull_of_le hL hLO hq
  have hkey : ∀ k ∈ primaryFactors (spEnd (torElt hc hdec hcω β)), k ≠ h →
      k ≠ reciprocalPolynomial h → ∀ v ∈ primaryComponent (spEnd (torElt hc hdec hcω β)) k,
        ∀ l ∈ S, (Φ.symm v).1 l = 0 := by
    intro k hk hkh hkh' v hv l hl
    by_contra hne
    refine false_of_forall_fix hL fun Y hY u => ?_
    have hYF := mem_spSupported.mp (hLO hY)
    have hfixk : ∀ u ∈ primaryComponent (spEnd (torElt hc hdec hcω β)) k, spEnd Y u = u :=
      hYF.2 k hk (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hkh, hkh'⟩)
    have hfixk' : ∀ u ∈ primaryComponent (spEnd (torElt hc hdec hcω β))
        (reciprocalPolynomial k), spEnd Y u = u :=
      hYF.2 _ (H.reciprocal_mem hk) (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨fun e => hkh' ?_, fun e => hkh ?_⟩
        · rw [← H.reciprocal_reciprocal hk, e]
        · rw [← H.reciprocal_reciprocal hk, e, H.reciprocal_reciprocal hh])
    have hblock : ∀ m ∈ S, ∀ z : D, spEnd Y (Φ (Pi.single m z, 0)) = Φ (Pi.single m z, 0) := by
      intro m hm z
      obtain ⟨z₀, hz₀, hz₀k⟩ : ∃ z₀ : D, z₀ ≠ 0 ∧
          aeval ((c ^ (β m).val : D ≃ₗ[F] D) : Module.End F D) k z₀ = 0 := by
        by_cases hml : m = l
        · rw [hml]
          exact ⟨_, hne, aeval_block_eq_zero hc hdec hcω hv l⟩
        · obtain ⟨Y', T, hY'x, -, hY'1, -⟩ := hswap l hl m hm (Ne.symm hml)
          have h1 : Φ (Pi.single l ((Φ.symm v).1 l), 0) ∈
              primaryComponent (spEnd (torElt hc hdec hcω β)) k :=
            single_mem_primaryComponent hc hdec hcω (aeval_block_eq_zero hc hdec hcω hv l)
          have h2 := apply_mem_primaryComponent (commute_spEnd hY'x) h1
          have h3 : spEnd Y' (Φ (Pi.single l ((Φ.symm v).1 l), 0)) =
              Φ (Pi.single m (T ((Φ.symm v).1 l)), 0) := by
            have h4 := hY'1 ((Φ.symm v).1 l)
            rw [frameEnd_apply] at h4
            rw [← h4, LinearEquiv.apply_symm_apply]
          rw [h3] at h2
          have h5 := aeval_block_eq_zero hc hdec hcω h2 m
          simp only [LinearEquiv.symm_apply_apply, Pi.single_eq_same] at h5
          exact ⟨T ((Φ.symm v).1 l), T.map_ne_zero_iff.mpr hne, h5⟩
      obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := block_split hbt hpp.one_lt.le hζ hz₀ hz₀k z
      have hsplit : ((Pi.single m z : Fin s → D), (0 : κ → F)) =
          (Pi.single m z₁, 0) + (Pi.single m z₂, 0) := by
        rw [Prod.mk_add_mk, ← Pi.single_add, ← hz, add_zero]
      rw [hsplit, map_add, map_add, hfixk _ (single_mem_primaryComponent hc hdec hcω hz₁),
        hfixk' _ (single_mem_primaryComponent hc hdec hcω hz₂)]
    have h1 := frame_induction S (P := fun y => spEnd Y (Φ y) = Φ y)
      (fun a b ha hb => by simp only [map_add, ha, hb]) (fun y hy => by
        have h2 := congrArg Φ (hLfix Y hY y hy)
        rwa [frameEnd_apply, LinearEquiv.apply_symm_apply] at h2) hblock (Φ.symm u)
    rwa [LinearEquiv.apply_symm_apply] at h1
  have hF : ∀ Z : StatedSp n F, Z * torElt hc hdec hcω β = torElt hc hdec hcω β * Z →
      ∀ m₁ ∈ S, ∀ m₂ ∈ S,
        (∀ y : (Fin s → D) × (κ → F), y.1 m₁ = 0 → y.1 m₂ = 0 → frameEnd Φ Z y = y) →
        Z ∈ spSupported (torElt hc hdec hcω β) {h, reciprocalPolynomial h} := by
    intro Z hZx m₁ hm₁ m₂ hm₂ hZ
    rw [mem_spSupported]
    refine ⟨hZx, fun k hk hkO v hv => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hkO
    have h1 := hZ (Φ.symm v) (hkey k hk hkO.1 hkO.2 v hv m₁ hm₁)
      (hkey k hk hkO.1 hkO.2 v hv m₂ hm₂)
    rw [frameEnd_apply, LinearEquiv.apply_symm_apply] at h1
    exact Φ.symm.injective h1
  have hτ : torElt hc hdec hcω (Pi.single i (1 : ZMod p)) ∈
      spSupported (torElt hc hdec hcω β) {h, reciprocalPolynomial h} :=
    hF _ (torElt_comm hc hdec hcω _ β) i hi i hi fun y hy _ => by
      rw [frameEnd_torElt]
      obtain ⟨d, w⟩ := y
      refine Prod.ext (funext fun k => ?_) rfl
      change (c ^ ((Pi.single i (1 : ZMod p) : Fin s → ZMod p) k).val) (d k) = d k
      by_cases hk : k = i
      · rw [hk]
        change d i = 0 at hy
        rw [hy, map_zero]
      · rw [Pi.single_eq_of_ne hk, ZMod.val_zero, pow_zero]
        rfl
  obtain ⟨Y, T, hYx, hYc, -, hYfix⟩ := hswap i hi j hj hij
  have hYF := hF Y hYx i hi j hj hYfix
  have hcomm : ⁅torElt hc hdec hcω (Pi.single i (1 : ZMod p)), Y⁆ =
      torElt hc hdec hcω (Pi.single i 1 - Pi.single j (((η j)⁻¹ * η i : (ZMod p)ˣ) : ZMod p)) := by
    rw [torElt_sub, commutatorElement_def]
    have h1 : Y * (torElt hc hdec hcω (Pi.single i (1 : ZMod p)))⁻¹ =
        (torElt hc hdec hcω (Pi.single j (((η j)⁻¹ * η i : (ZMod p)ˣ) : ZMod p)))⁻¹ * Y := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hYc, mul_assoc, mul_inv_cancel, mul_one]
    rw [mul_assoc (torElt hc hdec hcω (Pi.single i (1 : ZMod p))) Y, h1]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [← hcomm, hLeq]
  exact SevSpNs.commutator_le_spPull _ h (Subgroup.commutator_mem_commutator hτ hYF)

end Class

end SpNsCont

open SpNsCont CoordSpNs

theorem ggSpNsClassContInput_holds : GGSpNsClassContInput := by
  intro G _ _ F _ _ _ n p _ hp2 hns ψ hψ g _ hgd D _ _ c hbt hc s κ _ Φ ω hdec hcω β L₁ S η c₀
    hc₀ hηO hal hL₁ hLfix t ht hsum
  classical
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have hprim := NSFrame.root_isPrimitiveRoot (g := g) hpp hpF hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := hprim.pow_eq_one
  by_cases hSe : ∃ i₀, i₀ ∈ S
  swap
  · push Not at hSe
    have ht0 : t = 0 := funext fun i => ht i (hSe i)
    rw [ht0, ofAdd_zero, map_one]
    exact L₁.one_mem
  obtain ⟨i₀, hi₀⟩ := hSe
  rw [nsCoord_eq_torElt] at hL₁
  obtain ⟨hL', hmapL⟩ := isComponentOf_comap hψ hL₁
  have hLfix' : ∀ Y ∈ L₁.comap ψ, ∀ y : (Fin s → D) × (κ → F), (∀ i ∈ S, y.1 i = 0) →
      frameEnd Φ Y y = y := by
    intro Y hY y hy
    obtain ⟨Z, hZ, hZY⟩ := hLfix hY
    rw [hψ hZY] at hZ
    exact (mem_fixGrp Φ).mp hZ y hy
  obtain ⟨u, hu⟩ : ∃ u : Fin s → ZMod p, ∀ i, u i = (((η i₀)⁻¹ * η i : (ZMod p)ˣ) : ZMod p) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin s → Fin s → ZMod p,
      w = fun i => if i ∈ S then Pi.single i 1 - Pi.single i₀ (u i) else 0 := ⟨_, rfl⟩
  have hwS : ∀ i ∈ S, w i = Pi.single i 1 - Pi.single i₀ (u i) := fun i hi => by
    simp [hw, hi]
  have hwS' : ∀ i ∉ S, w i = 0 := fun i hi => by
    simp [hw, hi]
  have hwmem : ∀ i, nsCoord ψ hc hdec hcω (ofAdd (w i)) ∈ L₁ := by
    intro i
    by_cases hi : i ∈ S
    · by_cases hii : i = i₀
      · rw [hwS i hi, hii, hu, inv_mul_cancel, Units.val_one, sub_self, ofAdd_zero, map_one]
        exact L₁.one_mem
      · rw [hwS i hi, hu, nsCoord_eq_torElt, ← hmapL]
        exact Subgroup.mem_map_of_mem ψ
          (torElt_sub_mem hc hdec hcω hp2 hbt hζ hprim hc₀ hηO hal hL' hLfix' hi hi₀ hii)
    · rw [hwS' i hi, ofAdd_zero, map_one]
      exact L₁.one_mem
  have hu0 : ∑ i, t i * u i = 0 := sum_mul_eq_zero_of t (fun i => (η i : ZMod p)) u
    (((η i₀)⁻¹ : (ZMod p)ˣ) : ZMod p) (fun i => by rw [hu, Units.val_mul]) hsum
  have hdecomp : t = ∑ i, t i • w i := by
    rw [hw]
    exact eq_sum_smul_ite S i₀ t u ht hu0
  rw [hdecomp]
  exact ofAdd_sum_smul_mem w hwmem t

end CFSG.StandardType
