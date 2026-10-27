module

public import CFSG.GroupTheory.SteinbergBKMaximalChiefQuotient
public import CFSG.LocalAnalysis.SteinbergCEFittingCentralizesChiefFactors
public import CFSG.GroupTheory.SteinbergBKPrimeFrobeniusQuotient
public import CFSG.Quasithin.SteinbergCBFrobeniusKernelRep
public import CFSG.GroupTheory.LocalCores.Fitting

public section

universe u

namespace CFSG.LocalAnalysis.SteinbergBV

open CFSG CFSG.GroupTheory.SteinbergBK

theorem isComplement'_subgroupOf_sup {G : Type*} [Group G] {K L R : Subgroup G} [L.Normal]
    (hKR : K.IsComplement' R) (hLK : L ≤ K) :
    (L.subgroupOf (L ⊔ R)).IsComplement' (R.subgroupOf (L ⊔ R)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxR
    exact Subtype.ext (Subgroup.disjoint_def.mp hKR.disjoint (hLK hxL) hxR)
  · refine Set.eq_univ_of_forall fun m => ?_
    have hm : (m : G) ∈ ((L ⊔ R : Subgroup G) : Set G) := m.2
    rw [Subgroup.normal_mul] at hm
    obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hm
    exact Set.mem_mul.mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, ⟨r, Subgroup.mem_sup_right hr⟩, hr,
      Subtype.ext hlr⟩

theorem solvable_prime_frobenius_kernel_nilpotent_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Group.IsSolvable G → ∀ (K R : Subgroup G), K.Normal →
      K.IsComplement' R → (Nat.card R).Prime →
        (∀ k ∈ K, (∀ x ∈ R, x * k = k * x) → k = 1) → Nat.card K = n →
          Group.IsNilpotent K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hG K R hKn hKR hR hfix hn
  by_cases hK : K = ⊥
  · subst hK
    infer_instance
  obtain ⟨L, hLn, hLK, -, q, e, hq, -, -, hcardKL⟩ := maximal_normal_chief_quotient hG K hK
  have hLnil : Group.IsNilpotent L := by
    have hLM : L ≤ L ⊔ R := le_sup_left
    have hRM : R ≤ L ⊔ R := le_sup_right
    have hcomp := isComplement'_subgroupOf_sup hKR hLK.le
    have hRcard : Nat.card (R.subgroupOf (L ⊔ R)) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
    have hfixM : ∀ k ∈ L.subgroupOf (L ⊔ R),
        (∀ x ∈ R.subgroupOf (L ⊔ R), x * k = k * x) → k = 1 := by
      intro k hk hkR
      apply Subtype.ext
      refine hfix k (hLK.le hk) fun x hx => ?_
      exact congrArg Subtype.val (hkR ⟨x, hRM hx⟩ hx)
    have hlt : Nat.card (L.subgroupOf (L ⊔ R)) < n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, ← hn]
      exact Subgroup.card_lt_of_lt hLK
    have h := ih _ hlt (↥(L ⊔ R)) inferInstance (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))
      (hLn.subgroupOf _) hcomp (hRcard ▸ hR) hfixM rfl
    exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hLM).toMonoidHom
      (MulEquiv.surjective _)
  have hLF : L ≤ (fittingSubgroup K).map K.subtype := by
    have hLsub : L.subgroupOf K ≤ fittingSubgroup K :=
      LocalCores.fitting_characteristic.2.2 _ (hLn.subgroupOf K)
        (Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hLK.le).symm.toMonoidHom
          (MulEquiv.surjective _))
    calc L = (L.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hLK.le).symm
      _ ≤ _ := Subgroup.map_mono hLsub
  obtain ⟨hKLn, hKLcomp, -, -, -, hRLfix⟩ := prime_frobenius_quotient hKR hR rfl hfix L hLK
  have hKLq : IsPGroup q (K.map (QuotientGroup.mk' L)) := IsPGroup.of_card hcardKL
  have hchiefK : ∀ X Y : Subgroup G, X.Normal → Y.Normal → Y < X →
      X ≤ (fittingSubgroup K).map K.subtype →
        (∀ Z : Subgroup G, Z.Normal → ¬ (Y < Z ∧ Z < X)) → ⁅K, X⁆ ≤ Y := by
    intro X Y hXn hYn hYX hXF hchief
    have hXK : X ≤ K := hXF.trans (Subgroup.map_subtype_le _)
    obtain ⟨p, d, hpf, hd, -, hcardV, hc, hp, ρ, hρconj, hρirr, hρtriv⟩ :=
      solvable_chief_factor_module hG hYX hchief
    have hLX : ⁅L, X⁆ ≤ Y := (Subgroup.commutator_mono hLF le_rfl).trans
      (LocalAnalysis.solvable_fitting_centralizes_chief_factors hG hKn hXn hYn hYX hchief)
    have hρL : ∀ g ∈ L, ρ g = 1 := (hρtriv L).mpr hLX
    let _ : CommGroup (chiefQuot X Y) := commGroupOfComm hc
    let _ : Module (ZMod p) (Additive (chiefQuot X Y)) := elemModule p hc hp
    have hnt : Nontrivial (chiefQuot X Y) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardV]
      exact Nat.one_lt_pow (by omega) hpf.out.one_lt
    have : FiniteDimensional (ZMod p) (Additive (chiefQuot X Y)) := Module.Finite.of_finite
    set gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
      (Additive (chiefQuot X Y)) with hgl
    have hker : L ≤ (gl.symm.toMonoidHom.comp ρ).ker := by
      intro l hl
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hρL l hl, MulEquiv.coe_toMonoidHom, map_one]
    set ρ' := QuotientGroup.lift L (gl.symm.toMonoidHom.comp ρ) hker with hρ'def
    have hρ' : ∀ g : G, ρ' (QuotientGroup.mk' L g) = gl.symm (ρ g) := fun g => rfl
    have hirr : ∀ W : Submodule (ZMod p) (Additive (chiefQuot X Y)),
        (∀ g : G ⧸ L, ∀ w ∈ W,
          ((ρ' g : LinearMap.GeneralLinearGroup (ZMod p) (Additive (chiefQuot X Y))) :
            Additive (chiefQuot X Y) →ₗ[ZMod p] Additive (chiefQuot X Y)) w ∈ W) →
          W = ⊥ ∨ W = ⊤ := by
      intro W hW
      refine hρirr W fun g w hw => ?_
      have h := hW (QuotientGroup.mk' L g) w hw
      rw [hρ'] at h
      exact h
    have hfixed1 : ∀ v : Additive (chiefQuot X Y), (∀ r ∈ R, ρ r v = v) →
        ((Additive.toMul v : chiefQuot X Y) : G ⧸ Y) = 1 := by
      intro v hv
      obtain ⟨⟨_, x, hxX, rfl⟩, rfl⟩ : ∃ w : chiefQuot X Y, Additive.ofMul w = v :=
        ⟨Additive.toMul v, rfl⟩
      have hcommY : ∀ r ∈ R, QuotientGroup.mk' Y (r * x * r⁻¹) = QuotientGroup.mk' Y x := by
        intro r hr
        have h' := hv r hr
        rw [hρconj r x hxX] at h'
        exact congrArg (fun z => ((Additive.toMul z : chiefQuot X Y) : G ⧸ Y)) h'
      obtain ⟨-, -, -, -, hYfix, -⟩ := prime_frobenius_quotient hKR hR rfl hfix Y
        (hYX.trans_le hXK)
      refine hYfix _ (Subgroup.mem_map_of_mem _ (hXK hxX)) ?_
      rintro _ ⟨r, hr, rfl⟩
      have h := hcommY r hr
      rw [map_mul, map_mul, map_inv] at h
      calc QuotientGroup.mk' Y r * QuotientGroup.mk' Y x =
          QuotientGroup.mk' Y r * QuotientGroup.mk' Y x * (QuotientGroup.mk' Y r)⁻¹ *
            QuotientGroup.mk' Y r := by group
        _ = QuotientGroup.mk' Y x * QuotientGroup.mk' Y r := by rw [h]
    have hK1 := Quasithin.SteinbergCB.frobenius_prime_power_kernel_representation (p := p) hq
      hKLcomp hKLq (fun r hr hr1 k hk hkr => hRLfix r hr hr1 k hk hkr.symm) ρ' hirr (by
        intro v hv
        have hv' : ∀ r ∈ R, ρ r v = v := fun r hr => by
          have h := hv (QuotientGroup.mk' L r) (Subgroup.mem_map_of_mem _ hr)
          rw [hρ'] at h
          exact h
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hfixed1 v hv', hfixed1 _ fun r _ => (ρ r).map_zero])
    refine (hρtriv K).mp fun g hg => ?_
    have h := hK1 (QuotientGroup.mk' L g) (Subgroup.mem_map_of_mem _ hg)
    rw [hρ'] at h
    have h' := congrArg gl h
    rwa [MulEquiv.apply_symm_apply, map_one] at h'
  obtain ⟨D, hDset, -, hDF, -⟩ := solvable_fitting_chief_factor_detection hG K
  have hKD : K ≤ D := by
    intro g hg
    have h : g ∈ (D : Set G) := by
      rw [hDset]
      refine ⟨hg, fun X Y hXn hYn hYX hXF hchief => ?_⟩
      exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hg) le_rfl).trans
        (hchiefK X Y hXn hYn hYX hXF hchief)
    exact h
  have hKF := hKD.trans hDF
  have htop : fittingSubgroup K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨k', hk', hkk'⟩ := hKF k.2
    rw [show k = k' from Subtype.ext hkk'.symm]
    exact hk'
  have hnil := (LocalCores.fitting_nilpotent (G := K)).1
  rw [htop] at hnil
  exact Group.nilpotent_of_surjective (Subgroup.topEquiv).toMonoidHom (MulEquiv.surjective _)

theorem solvable_prime_frobenius_kernel_nilpotent {G : Type u} [Group G] [Finite G]
    (hG : Group.IsSolvable G) {K R : Subgroup G} [hKn : K.Normal] (hKR : K.IsComplement' R)
    (hR : (Nat.card R).Prime) (hfix : ∀ k ∈ K, (∀ x ∈ R, x * k = k * x) → k = 1) :
    Group.IsNilpotent K :=
  solvable_prime_frobenius_kernel_nilpotent_aux _ G hG K R hKn hKR hR hfix rfl

end CFSG.LocalAnalysis.SteinbergBV
