module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.RankThree.Chevalley.SteinbergBID4ThetaFixed

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Ω : Type} [Field Ω]

@[expose] def d4LatHom : (Fin Tag.D4.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) where
  toFun := d4Lat
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' := d4Lat_add

theorem d4Lat_eq_sum (β : Fin Tag.D4.rank → ℤ) :
    d4Lat β = ∑ k, β k • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) := by
  have hβ : β = ∑ k, β k • (Pi.single k 1 : Fin Tag.D4.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hβ]
  change d4LatHom _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  exact congrArg _ (d4Lat_single k)

theorem weyl_smul_d4Lat_eq_sum (w : WeylGroup Tag.E6) (β : Fin Tag.D4.rank → ℤ) :
    w • d4Lat β = ∑ k, β k • (w • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) := by
  rw [d4Lat_eq_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ =>
    (DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) w).map_zsmul (β k) _

@[expose] def d4RhoPerm : Equiv.Perm (Fin Tag.D4.rank) where
  toFun := d4Rho
  invFun := d4RhoInv
  left_inv := d4RhoInv_d4Rho
  right_inv := d4Rho_d4RhoInv

theorem d4RhoPerm_apply (k : Fin Tag.D4.rank) : d4RhoPerm k = TwistTag.D4.perm k :=
  d4Rho_eq_perm k

theorem trialityWeyl_smul_d4Lat (β : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd d4TrialityWord • d4Lat β =
      d4Lat (permLattice d4RhoPerm β) := by
  rw [weyl_smul_d4Lat_eq_sum, d4Lat_eq_sum]
  have h : ∀ k, (coxeterSystem Tag.E6).wordProd d4TrialityWord •
      (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
        Pi.single (d4Idx (d4RhoPerm k)) 1 := fun k => by
    rw [← wordAct_eq_smul, (d4TrialityWord_check k).1]
    rfl
  simp only [h]
  rw [← Equiv.sum_comp d4RhoPerm (fun k => permLattice d4RhoPerm β k •
    (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [permLattice, Function.comp_apply, Equiv.symm_apply_apply]

theorem trialityWeyl_pow_smul_d4Lat (e : ℕ) (β : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd d4TrialityWord ^ e • d4Lat β =
      d4Lat (permLattice (d4RhoPerm ^ e) β) := by
  induction e generalizing β with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ', mul_smul, ih, trialityWeyl_smul_d4Lat]
    rfl

theorem wordAct_map_d4Idx (ω : List (Fin Tag.D4.rank)) (β : Fin Tag.D4.rank → ℤ) :
    wordAct Tag.E6 (ω.map d4Idx) (d4Lat β) = d4Lat (wordAct Tag.D4 ω β) := by
  induction ω with
  | nil => rfl
  | cons k ω ih =>
    simp only [List.map_cons, wordAct, List.foldr_cons] at ih ⊢
    rw [ih, d4Lat_reflect]

theorem wordRep_map_d4Idx_mem (ω : List (Fin Tag.D4.rank)) :
    wordRep Tag.E6 Ω (ω.map d4Idx) ∈ subsystemGroup Tag.E6 Ω d4Support :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
    exact weylElt_mem_subsystemGroup (d4Idx_mem k) 1

theorem d4RhoPerm_pow_cartan (e : ℕ) (i j : Fin Tag.D4.rank) :
    Tag.D4.cartan ((d4RhoPerm ^ e) i) ((d4RhoPerm ^ e) j) = Tag.D4.cartan i j := by
  have h1 : ∀ i j : Fin Tag.D4.rank,
      Tag.D4.cartan (d4RhoPerm i) (d4RhoPerm j) = Tag.D4.cartan i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  induction e generalizing i j with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, ih]

theorem permLattice_inv_cancel {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice π (permLattice π⁻¹ v) = v := by
  funext j
  simp [permLattice, Equiv.Perm.inv_def]

theorem coe_d4Triality_pow (e : ℕ) (g : subsystemGroup Tag.E6 Ω d4Support) :
    (((d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support)) g :
      subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) =
      d4TrialityRep Ω ^ e * g * (d4TrialityRep Ω ^ e)⁻¹ := by
  induction e generalizing g with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', MulAut.mul_apply, coe_d4Triality, ih, pow_succ']
    group

theorem coe_d4Theta (Fr : Ω →+* Ω) (e : ℕ) (g : subsystemGroup Tag.E6 Ω d4Support) :
    ((d4Theta Ω Fr e g : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) =
      d4TrialityRep Ω ^ e * baseChangeGL Fr g * (d4TrialityRep Ω ^ e)⁻¹ := by
  rw [d4Theta_apply, coe_d4Triality_pow]
  rfl

@[expose] def D4TrialityWeylType (w : WeylGroup Tag.E6) (e : ℕ) : Prop :=
  ∃ u : WeylGroup Tag.D4, ∀ β, IsRoot Tag.D4 β →
    w • d4Lat β = d4Lat (u • permLattice (d4RhoPerm ^ e) β)

theorem rootSL2_single_apply (τ : Tag) (i : Fin τ.rank) (A : SL2 Ω) :
    rootSL2 τ Ω (Pi.single i 1) A = simpleRootSL2 τ Ω i A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem exists_conj_xUnit_yUnit_of_monomial {a : ModGL Tag.E6 Ω}
    (ha : a ∈ monomialSubgroup Tag.E6 Ω) {i : Fin Tag.E6.rank}
    (hi : weylQuotientHom Tag.E6 Ω ⟨a, ha⟩ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single i 1) :
    ∃ s : Ωˣ, ∀ c : Ω, a * xUnit Tag.E6 Ω i c * a⁻¹ = xUnit Tag.E6 Ω i (s * c) ∧
      a * yUnit Tag.E6 Ω i c * a⁻¹ = yUnit Tag.E6 Ω i (((s⁻¹ : Ωˣ) : Ω) * c) := by
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq ha (mapsRootLines_weylQuotientHom ⟨a, ha⟩)
    (isRoot_single Tag.E6 i) hi
  refine ⟨s, fun c => ⟨?_, ?_⟩⟩
  · have h := hs (uSL c)
    rw [rootSL2_single_apply, rootSL2_single_apply, simpleRootSL2_uSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 Tag.E6 Ω i) (conjSL_sl2Upper s c)).trans
      (simpleRootSL2_uSL i _)
  · have h := hs (vSL c)
    rw [rootSL2_single_apply, rootSL2_single_apply, simpleRootSL2_vSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 Tag.E6 Ω i) (conjSL_sl2Lower s c)).trans
      (simpleRootSL2_vSL i _)

theorem e6Pair_neg (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    e6Pair i (-v) = -e6Pair i v := by
  simp [e6Pair, Finset.sum_neg_distrib]

theorem torusRootChar_list_prod_D4 (t : Fin Tag.D4.rank → Ωˣ) (k : Fin Tag.D4.rank) :
    torusRootChar (((List.finRange Tag.D4.rank).map fun j => torusElt Tag.D4 Ω j (t j)).prod)
      (Pi.single k 1) = ((t 0 ^ Tag.D4.cartan 0 k * t 1 ^ Tag.D4.cartan 1 k *
        t 2 ^ Tag.D4.cartan 2 k * t 3 ^ Tag.D4.cartan 3 k : Ωˣ) : Ω) := by
  have hd : ∀ (i : Fin Tag.D4.rank) (u : Ωˣ), torusElt Tag.D4 Ω i u ∈ diagonalGroup :=
    fun i u => torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i u)
  have hl : ((List.finRange Tag.D4.rank).map fun j => torusElt Tag.D4 Ω j (t j)).prod =
      torusElt Tag.D4 Ω 0 (t 0) * (torusElt Tag.D4 Ω 1 (t 1) *
        (torusElt Tag.D4 Ω 2 (t 2) * torusElt Tag.D4 Ω 3 (t 3))) := by
    have hf : List.finRange Tag.D4.rank = [0, 1, 2, 3] := by decide
    rw [hf]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hs : ∀ (i : Fin Tag.D4.rank) (u : Ωˣ), torusRootChar (torusElt Tag.D4 Ω i u)
      (Pi.single k 1) = ((u ^ Tag.D4.cartan i k : Ωˣ) : Ω) := fun i u => by
    rw [torusRootChar_torusElt i u (isRoot_single _ k)]
    congr 2
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
  rw [hl, torusRootChar_mul (hd _ _) (mul_mem (hd _ _) (mul_mem (hd _ _) (hd _ _))),
    torusRootChar_mul (hd _ _) (mul_mem (hd _ _) (hd _ _)), torusRootChar_mul (hd _ _) (hd _ _),
    hs, hs, hs, hs]
  simp only [Units.val_mul, mul_assoc]

theorem exists_d4TorusHom_scalars [IsAlgClosed Ω] (s : Fin Tag.D4.rank → Ωˣ) :
    ∃ t : Fin 4 → Ωˣ, ∀ (k : Fin Tag.D4.rank) (c : Ω),
      d4TorusHom Ω t * xUnit Tag.E6 Ω (d4Idx k) c * (d4TorusHom Ω t)⁻¹ =
        xUnit Tag.E6 Ω (d4Idx k) (s k * c) ∧
      d4TorusHom Ω t * yUnit Tag.E6 Ω (d4Idx k) c * (d4TorusHom Ω t)⁻¹ =
        yUnit Tag.E6 Ω (d4Idx k) (((s k)⁻¹ : Ωˣ) * c) := by
  obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift Tag.D4 Ω s
  have hkey : ∀ k : Fin Tag.D4.rank, ((t 0 ^ Tag.D4.cartan 0 k * t 1 ^ Tag.D4.cartan 1 k *
      t 2 ^ Tag.D4.cartan 2 k * t 3 ^ Tag.D4.cartan 3 k : Ωˣ) : Ω) = s k := fun k => by
    rw [← torusRootChar_list_prod_D4, ← ht]
    refine torusRootChar_eq_of_apply (isRoot_single _ k) ?_
    change rootDiag s (rootVec Tag.D4 Ω (Pi.single k 1)) = _
    rw [rootDiag_rootVec s (isRoot_single _ k)]
    congr 2
    rw [rootChar, Finset.prod_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, zpow_one]
  have hc : ∀ (l k : Fin Tag.D4.rank),
      Tag.E6.cartan (d4Idx l) (d4Idx k) = Tag.D4.cartan l k := cartan_d4Idx
  have hT := d4TorusHom_mem_torusGroup (K := Ω) t
  refine ⟨t, fun k c => ⟨?_, ?_⟩⟩
  · rw [← pinnedX_single, ← pinnedX_single, conj_pinnedX_of_mem_torusGroup hT (isRoot_single _ _),
      torusRootChar_d4TorusHom t (isRoot_single _ _), e6Pair_single, e6Pair_single, e6Pair_single,
      e6Pair_single]
    rw [show Tag.E6.cartan 1 (d4Idx k) = Tag.D4.cartan 0 k from hc 0 k,
      show Tag.E6.cartan 2 (d4Idx k) = Tag.D4.cartan 1 k from hc 1 k,
      show Tag.E6.cartan 3 (d4Idx k) = Tag.D4.cartan 2 k from hc 2 k,
      show Tag.E6.cartan 4 (d4Idx k) = Tag.D4.cartan 3 k from hc 3 k]
    exact congrArg _ (congrArg (· * c) (hkey k))
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      conj_pinnedX_of_mem_torusGroup hT (isRoot_neg_single _ _),
      torusRootChar_d4TorusHom t (isRoot_neg_single _ _), e6Pair_neg, e6Pair_neg, e6Pair_neg,
      e6Pair_neg, e6Pair_single, e6Pair_single, e6Pair_single, e6Pair_single]
    rw [show Tag.E6.cartan 1 (d4Idx k) = Tag.D4.cartan 0 k from hc 0 k,
      show Tag.E6.cartan 2 (d4Idx k) = Tag.D4.cartan 1 k from hc 1 k,
      show Tag.E6.cartan 3 (d4Idx k) = Tag.D4.cartan 2 k from hc 2 k,
      show Tag.E6.cartan 4 (d4Idx k) = Tag.D4.cartan 3 k from hc 3 k]
    have hinv : t 0 ^ (-Tag.D4.cartan 0 k) * t 1 ^ (-Tag.D4.cartan 1 k) *
        t 2 ^ (-Tag.D4.cartan 2 k) * t 3 ^ (-Tag.D4.cartan 3 k) = (s k)⁻¹ := by
      rw [← Units.ext (hkey k)]
      simp only [zpow_neg, mul_inv]
    exact congrArg (pinnedX Tag.E6 Ω (-Pi.single (d4Idx k) 1))
      (congrArg (· * c) (congrArg Units.val hinv))

theorem wordRep_mem_monomialSubgroup {τ : Tag} (R : Type) [CommRing R] (ω : List (Fin τ.rank)) :
    wordRep τ R ω ∈ monomialSubgroup τ R :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

theorem weylQuotientHom_wordRep {τ : Tag} (K : Type) [Field K] (ω : List (Fin τ.rank)) :
    weylQuotientHom τ K ⟨wordRep τ K ω, wordRep_mem_monomialSubgroup K ω⟩ =
      (coxeterSystem τ).wordProd ω :=
  weylQuotientHom_eq (mapsRootLines_list_prod ω)

theorem exists_conj_eq_d4Theta (ℓ d : ℕ) [Fact ℓ.Prime] [IsAlgClosed Ω] [CharP Ω ℓ] (hd : 1 ≤ d)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) {e : ℕ}
    {m : ModGL Tag.E6 Ω} (hm : m ∈ monomialSubgroup Tag.E6 Ω)
    (hw : D4TrialityWeylType (weylQuotientHom Tag.E6 Ω ⟨m, hm⟩) e) :
    ∃ g ∈ subsystemGroup Tag.E6 Ω d4Support, ∀ x (hx : x ∈ subsystemGroup Tag.E6 Ω d4Support),
      g * (m * baseChangeGL Fr (g⁻¹ * x * g) * m⁻¹) * g⁻¹ =
        (d4Theta Ω Fr e ⟨x, hx⟩ : ModGL Tag.E6 Ω) := by
  obtain ⟨u, hu⟩ := hw
  obtain ⟨ω', rfl⟩ := (coxeterSystem Tag.D4).wordProd_surjective u
  set n := d4TrialityRep Ω with hndef
  set n' := wordRep Tag.E6 Ω (ω'.map d4Idx) with hn'def
  have hnM : n ∈ monomialSubgroup Tag.E6 Ω := wordRep_mem_monomialSubgroup Ω _
  have hn'M : n' ∈ monomialSubgroup Tag.E6 Ω := wordRep_mem_monomialSubgroup Ω _
  set a' := m * (n ^ e)⁻¹ * n'⁻¹ with ha'def
  have ha'M : a' ∈ monomialSubgroup Tag.E6 Ω :=
    mul_mem (mul_mem hm (inv_mem (pow_mem hnM e))) (inv_mem hn'M)
  have hW : weylQuotientHom Tag.E6 Ω ⟨a', ha'M⟩ = weylQuotientHom Tag.E6 Ω ⟨m, hm⟩ *
      ((coxeterSystem Tag.E6).wordProd d4TrialityWord ^ e)⁻¹ *
        ((coxeterSystem Tag.E6).wordProd (ω'.map d4Idx))⁻¹ := by
    have e1 : (⟨a', ha'M⟩ : monomialSubgroup Tag.E6 Ω) =
        ⟨m, hm⟩ * (⟨n, hnM⟩ ^ e)⁻¹ * (⟨n', hn'M⟩)⁻¹ := Subtype.ext (by simp [ha'def])
    rw [e1, map_mul, map_mul, map_inv, map_inv, map_pow]
    rw [show (⟨n, hnM⟩ : monomialSubgroup Tag.E6 Ω) =
      ⟨wordRep Tag.E6 Ω d4TrialityWord, wordRep_mem_monomialSubgroup Ω _⟩ from rfl,
      show (⟨n', hn'M⟩ : monomialSubgroup Tag.E6 Ω) =
      ⟨wordRep Tag.E6 Ω (ω'.map d4Idx), wordRep_mem_monomialSubgroup Ω _⟩ from rfl,
      weylQuotientHom_wordRep, weylQuotientHom_wordRep]
  have hfix : ∀ k : Fin Tag.D4.rank, weylQuotientHom Tag.E6 Ω ⟨a', ha'M⟩ •
      (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (d4Idx k) 1 := by
    intro k
    have hU : ∀ γ, (coxeterSystem Tag.E6).wordProd (ω'.map d4Idx) • d4Lat γ =
        d4Lat ((coxeterSystem Tag.D4).wordProd ω' • γ) := fun γ => by
      rw [← wordAct_eq_smul, ← wordAct_eq_smul, wordAct_map_d4Idx]
    have hS : ∀ γ, ((coxeterSystem Tag.E6).wordProd d4TrialityWord ^ e)⁻¹ • d4Lat γ =
        d4Lat (permLattice (d4RhoPerm ^ e)⁻¹ γ) := fun γ => by
      rw [inv_smul_eq_iff, trialityWeyl_pow_smul_d4Lat, permLattice_inv_cancel]
    have hroot : IsRoot Tag.D4 (permLattice (d4RhoPerm ^ e)⁻¹
        (((coxeterSystem Tag.D4).wordProd ω')⁻¹ • (Pi.single k 1 : Fin Tag.D4.rank → ℤ))) :=
      IsRoot.permLattice (fun i j => cartan_perm_symm (d4RhoPerm_pow_cartan e) i j)
        (IsRoot.smul (isRoot_single _ k) _)
    rw [hW, mul_smul, mul_smul, ← d4Lat_single]
    have hU' : ((coxeterSystem Tag.E6).wordProd (ω'.map d4Idx))⁻¹ • d4Lat (Pi.single k 1) =
        d4Lat (((coxeterSystem Tag.D4).wordProd ω')⁻¹ • Pi.single k 1) := by
      rw [inv_smul_eq_iff, hU, smul_inv_smul]
    rw [hU', hS, hu _ hroot, permLattice_inv_cancel, smul_inv_smul]
  have hsc := fun k => exists_conj_xUnit_yUnit_of_monomial ha'M (hfix k)
  choose sk hsk using hsc
  obtain ⟨t, ht⟩ := exists_d4TorusHom_scalars sk
  set T := d4TorusHom Ω t
  have hTQ : T ∈ subsystemGroup Tag.E6 Ω d4Support := d4TorusHom_mem_d4Q t
  have hact : ∀ y : subsystemGroup Tag.E6 Ω d4Support,
      a' * (y : ModGL Tag.E6 Ω) * a'⁻¹ = T * y * T⁻¹ := by
    have h : (MulAut.conj a').toMonoidHom.comp (subsystemGroup Tag.E6 Ω d4Support).subtype =
        (MulAut.conj T).toMonoidHom.comp (subsystemGroup Tag.E6 Ω d4Support).subtype := by
      refine d4Q_hom_ext (fun k c => ?_) (fun k c => ?_)
      · simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [(hsk k c).1, (ht k c).1]
      · simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [(hsk k c).2, (ht k c).2]
    exact fun y => DFunLike.congr_fun h y
  set h₀ := T * n' with hh₀def
  have hh₀Q : h₀ ∈ subsystemGroup Tag.E6 Ω d4Support :=
    mul_mem hTQ (wordRep_map_d4Idx_mem ω')
  have hΨ : ∀ y : subsystemGroup Tag.E6 Ω d4Support, m * baseChangeGL Fr y * m⁻¹ =
      h₀ * (d4Theta Ω Fr e y : ModGL Tag.E6 Ω) * h₀⁻¹ := by
    intro y
    have hmem : n' * (d4Theta Ω Fr e y : ModGL Tag.E6 Ω) * n'⁻¹ ∈
        subsystemGroup Tag.E6 Ω d4Support :=
      mul_mem (mul_mem (wordRep_map_d4Idx_mem ω') (d4Theta Ω Fr e y).2)
        (inv_mem (wordRep_map_d4Idx_mem ω'))
    have hm' : m = a' * n' * n ^ e := by rw [ha'def]; group
    have h1 : a' * (n' * (d4Theta Ω Fr e y : ModGL Tag.E6 Ω) * n'⁻¹) * a'⁻¹ =
        T * (n' * (d4Theta Ω Fr e y : ModGL Tag.E6 Ω) * n'⁻¹) * T⁻¹ := hact ⟨_, hmem⟩
    have h2 : m * baseChangeGL Fr y * m⁻¹ =
        a' * (n' * (d4Theta Ω Fr e y : ModGL Tag.E6 Ω) * n'⁻¹) * a'⁻¹ := by
      rw [coe_d4Theta, ← hndef, hm']
      group
    rw [h2, h1, hh₀def]
    group
  obtain ⟨S, hS, hsurj⟩ :=
    (CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity ℓ Ω d
      hd).2
      TwistTag.D4 (e : ℤ)
  have hFrI : iterateFrobenius Ω ℓ d = Fr := RingHom.ext fun c => by
    rw [iterateFrobenius_def, hFr]
  obtain ⟨yS, hyS⟩ := hsurj ⟨d4Res Ω ⟨h₀, hh₀Q⟩, d4Res_mem_adjointGroup _⟩
  obtain ⟨g, hg⟩ : ∃ g : subsystemGroup Tag.E6 Ω d4Support,
      (d4Res Ω g : ModGL TwistTag.D4.tag Ω) = yS.1 := by
    have h : yS.1 ∈ adjointGroup Tag.D4 Ω := yS.2
    rw [← range_d4Res] at h
    exact h
  have hSg : ((S yS : adjointGroup TwistTag.D4.tag Ω) : ModGL TwistTag.D4.tag Ω) =
      d4Res Ω (d4Theta Ω Fr e g) := by
    rw [hS, d4Res_d4Theta, hFrI, ← hg, zpow_natCast]
    rfl
  have hr : d4Res Ω ⟨h₀, hh₀Q⟩ = d4Res Ω (g⁻¹ * d4Theta Ω Fr e g) := by
    have h := congrArg Subtype.val hyS
    rw [map_mul, map_inv, hg, ← hSg]
    exact h
  set z := (g⁻¹ * d4Theta Ω Fr e g)⁻¹ * ⟨h₀, hh₀Q⟩ with hzdef
  have hz : d4Res Ω z = 1 := by rw [hzdef, map_mul, map_inv, hr, inv_mul_cancel]
  have hzc : ∀ y, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.1 (mem_center_of_d4Res_eq_one hz) y).symm
  refine ⟨g, g.2, fun x hx => ?_⟩
  set X : subsystemGroup Tag.E6 Ω d4Support := ⟨x, hx⟩
  set Θ := d4Theta Ω Fr e
  have hH : (⟨h₀, hh₀Q⟩ : subsystemGroup Tag.E6 Ω d4Support) = g⁻¹ * Θ g * z := by
    rw [hzdef]
    group
  have key : g * ⟨h₀, hh₀Q⟩ * Θ (g⁻¹ * X * g) * (⟨h₀, hh₀Q⟩)⁻¹ * g⁻¹ = Θ X := by
    rw [hH, map_mul, map_mul, map_inv]
    calc g * (g⁻¹ * Θ g * z) * ((Θ g)⁻¹ * Θ X * Θ g) * (g⁻¹ * Θ g * z)⁻¹ * g⁻¹ =
          Θ g * (z * ((Θ g)⁻¹ * Θ X * Θ g)) * z⁻¹ * (Θ g)⁻¹ := by group
      _ = Θ g * ((Θ g)⁻¹ * Θ X * Θ g) * z * z⁻¹ * (Θ g)⁻¹ := by rw [hzc]; group
      _ = Θ X := by group
  have hx' : (g : ModGL Tag.E6 Ω)⁻¹ * x * g =
      ((g⁻¹ * X * g : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) := rfl
  rw [hx', hΨ]
  have := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [← this]
  group

theorem fixed_iff_conj_mem_d4ThetaFixed {Fr : Ω →+* Ω} {e : ℕ} {m g : ModGL Tag.E6 Ω}
    (hg : g ∈ subsystemGroup Tag.E6 Ω d4Support)
    (hconj : ∀ x (hx : x ∈ subsystemGroup Tag.E6 Ω d4Support),
      g * (m * baseChangeGL Fr (g⁻¹ * x * g) * m⁻¹) * g⁻¹ =
        (d4Theta Ω Fr e ⟨x, hx⟩ : ModGL Tag.E6 Ω))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ subsystemGroup Tag.E6 Ω d4Support) :
    m * baseChangeGL Fr x * m⁻¹ = x ↔
      (⟨g * x * g⁻¹, mul_mem (mul_mem hg hx) (inv_mem hg)⟩ :
        subsystemGroup Tag.E6 Ω d4Support) ∈ d4ThetaFixed Ω Fr e := by
  rw [mem_d4ThetaFixed, ← Subtype.coe_inj]
  change _ ↔ (d4Theta Ω Fr e ⟨g * x * g⁻¹, _⟩ : ModGL Tag.E6 Ω) = g * x * g⁻¹
  rw [← hconj, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using h'

end CFSG.RankThree.Chevalley
