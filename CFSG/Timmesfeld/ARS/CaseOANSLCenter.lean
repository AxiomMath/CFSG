module

public import CFSG.Timmesfeld.ARS.CaseOANSLLow
public import CFSG.Timmesfeld.ARS.CaseOANSLWeyl
public import CFSG.Timmesfeld.ARS.Sec12Center

public section

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

namespace CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOANSL

open ExclNS (memberRoots memberRoots_subset weylAction_mem_memberRoots neg_mem_memberRoots
  map_rootGroup_mem opposite_map_rootGroup)

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)}

theorem mem_lambdaSet_conjSub_iff (hR : IsRootClass R) {X Y : Subgroup G} (g : G) :
    Y ∈ lambdaSet R (conjSub X g) ↔ conjSub Y g⁻¹ ∈ lambdaSet R X := by
  constructor
  · intro hY
    have := conjSub_mem_lambdaSet hR hY g⁻¹
    rwa [conjSub_conjSub_inv] at this
  · intro hY
    have := conjSub_mem_lambdaSet hR hY g
    rwa [ExclNS.conjSub_inv_conjSub] at this

theorem special_conjSub_iff (hR : IsRootClass R) {X Y : Subgroup G} (g : G) :
    Special R Y (conjSub X g) ↔ Special R (conjSub Y g⁻¹) X := by
  constructor
  · intro hY
    have := Sec3.special_conjSub hR hY g⁻¹
    rwa [conjSub_conjSub_inv] at this
  · intro hY
    have := Sec3.special_conjSub hR hY g
    rwa [ExclNS.conjSub_inv_conjSub] at this


theorem actsAs_inv {K : Type*} [Group K] {D : UniversalRootDatum K} {x : K}
    {w : (coxeterMatrix D.isFiniteType).Group} (hx : ActsAs D x w) : ActsAs D x⁻¹ w⁻¹ := by
  intro γ hγ
  have hγ' : weylAction D.isFiniteType w⁻¹ γ ∈ D.roots := weylAction_mem_roots _ _ hγ
  have h1 := hx _ hγ'
  rw [← weylAction_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply] at h1
  rw [← h1, Subgroup.map_map]
  convert Subgroup.map_id (D.rootGroup (weylAction D.isFiniteType w⁻¹ γ))
  ext g
  simp [mul_assoc]

theorem commute_of_isConfig_D4 (h : Hyp G R) (hA : A ∈ R) {P Q : Fin 4 → Subgroup G}
    (hcfg : IsConfig R (edgeD 4) P Q) (hE : P 1 ∈ lambdaStar R A A₀)
    (hP0 : P 0 ∈ leviSet R A A₀) (hP2 : P 2 ∈ leviSet R A A₀) (hP3 : P 3 ∈ leviSet R A A₀)
    {z : G} (hzV : ∀ v ∈ levi R A A₀, Commute z v) (hzA : ∀ a ∈ A, Commute z a)
    (hzE : conjSub (P 1) z = P 1) : ∀ e ∈ P 1, Commute z e := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨f, hf, hcard, Ψ, hΨA, -, -, -⟩ := CaseM.exists_hom_D hR hiso le_rfl hcfg
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpar := SpinPlus.isParametrization (n := 4) (K := GaloisField 2 f) CaseM.three_le_four
  have hxmem : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots, ∀ c,
      SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c ∈
        (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ :=
    fun γ hγ c => ((hpar γ hγ).1 _).2 ⟨c, rfl⟩
  have hxsurj : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      ∀ g ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ,
        ∃ c, SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c = g :=
    fun γ hγ g hg => ((hpar γ hγ).1 g).1 hg
  have hsingle : ∀ k : Fin 4, (Pi.single k 1 : Fin 4 → ℤ) ∈
      (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots := fun k =>
    LevisExtras.single_mem_roots (D := Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four) k
  have hΨmem : ∀ k : Fin 4, ∀ c,
      Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single k 1) c) ∈ P k := by
    intro k c
    rw [← hΨA k]
    exact ⟨_, hxmem _ (hsingle k) c, rfl⟩
  have hP : ∀ k, ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      (Pi.single k 1)).map Ψ ∈ R := fun k => by
    have := hcfg.memA k
    rwa [← hΨA k] at this
  have hmemR : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ).map Ψ ∈ R :=
    fun γ hγ => CaseM.map_rootGroup_mem hR (Spin.plusDatum_isCTGroupDatum CaseM.three_le_four
      (Spin.plusDatum_iSup_eq_top 4 _ CaseM.three_le_four)) rfl Ψ hP hγ
  have hinjγ : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      Function.Injective fun c => Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c) := by
    intro γ hγ c d hcd
    let φ : GaloisField 2 f →
        ↥(((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ).map Ψ) :=
      fun c => ⟨Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c),
        ⟨_, hxmem γ hγ c, rfl⟩⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨_, g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hxsurj γ hγ g hg
      exact ⟨c, rfl⟩
    have hbij := hsurj.bijective_of_nat_card_le (by rw [hcard _ (hmemR γ hγ), hF])
    exact hbij.1 (Subtype.ext hcd)
  have hNM : ∀ {X : Subgroup G}, X ∈ leviSet R A A₀ →
      X ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) := fun hX =>
    QD.le_normalizer_M hR hA ⟨hX.1.1, hX.1.2.2⟩
  have hcm₁ : ∀ {n m : G}, n ∈ Subgroup.normalizer ((M R A : Subgroup G) : Set G) →
      m ∈ M R A → ⁅n, m⁆ ∈ M R A := fun {n m} hn hm => by
    rw [commutatorElement_def]
    exact (M R A).mul_mem ((Subgroup.mem_normalizer_iff.1 hn m).1 hm) ((M R A).inv_mem hm)
  have hcm₂ : ∀ {n m : G}, n ∈ Subgroup.normalizer ((M R A : Subgroup G) : Set G) →
      m ∈ M R A → ⁅m, n⁆ ∈ M R A := fun {n m} hn hm => by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc n]
    refine (M R A).mul_mem hm ?_
    exact (Subgroup.mem_normalizer_iff.1 hn m⁻¹).1 ((M R A).inv_mem hm)
  have hEM : P 1 ≤ M R A := QD.le_M hE.1
  have r1 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 0 1) c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_α₀_α₁, mul_one]
  have r2 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 2 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₁_α₂, mul_one]
  have r3 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 3 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₂_α₃, mul_one]
  have r4 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₃_α₁, mul_one]
  have hβ₁M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c) ∈
      M R A := fun c => by
    rw [r1]
    exact hcm₁ (hNM hP0 (hΨmem 0 c)) (hEM (hΨmem 1 1))
  have hβ₂M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c) ∈
      M R A := fun c => by
    rw [r2]
    exact hcm₂ (hNM hP2 (hΨmem 2 1)) (hβ₁M c)
  have hβ₃M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c) ∈
      M R A := fun c => by
    rw [r3]
    exact hcm₂ (hNM hP3 (hΨmem 3 1)) (hβ₂M c)
  have hX₃R : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ∈ R := hmemR _ CaseM.mem_roots_B₃
  have hX₃M : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≤ M R A := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := hxsurj _ CaseM.mem_roots_B₃ g hg
    exact hβ₃M c
  have hθ1 : Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta 1) ≠ 1 :=
    fun h1 => by
      have h0 : Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta 0) = 1 := by
        have e0 := (hpar _ CaseM.mem_roots_theta).2.1 0 0
        rw [add_zero] at e0
        rw [left_eq_mul.1 e0, map_one]
      exact one_ne_zero (hinjγ _ CaseM.mem_roots_theta (h1.trans h0.symm))
  have hncomm : ¬ Commuting (((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ) (P 1) := fun hc => hθ1 (by
    rw [r4, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ ⟨_, hxmem _ CaseM.mem_roots_B₃ 1, rfl⟩ _ (hΨmem 1 1))
  have hX₃A : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≠ A := fun e => hncomm (by rw [e]; exact hE.1.1.2.2)
  have hX₃E : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≠ P 1 := fun e => hncomm (by rw [e]; exact hR.commuting_self hE.1.1.1)
  have hX₃EA := ((commuting_or_commutator_eq_of_mem_lambdaSet h hA
    (mem_lambdaSet_of_le_M_of_hyp h hA hX₃R hX₃M hX₃A) hE.1 hX₃E).resolve_left hncomm).2
  have hθA : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta c) ∈ A :=
    fun c => by
      rw [r4, ← hX₃EA]
      exact Subgroup.commutator_mem_commutator ⟨_, hxmem _ CaseM.mem_roots_B₃ c, rfl⟩ (hΨmem 1 1)
  have hE1 : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      (Pi.single (1 : Fin 4) 1)).map Ψ = P 1 := hΨA 1
  have key := CaseM.commute_of_commute_legs (F := GaloisField 2 f) Ψ (z := z)
    (fun k hk c => by
      refine hzV _ (le_gen ?_ (hΨmem k c))
      fin_cases k
      · exact hP0
      · exact absurd rfl hk
      · exact hP2
      · exact hP3)
    (fun c => by
      have hmem : z * Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) c) *
          z⁻¹ ∈ P 1 := by
        rw [← hzE]
        exact conj_mem_conjSub z (hΨmem 1 c)
      rw [← hE1] at hmem
      obtain ⟨g, hg, hgz⟩ := hmem
      obtain ⟨d, rfl⟩ := hxsurj _ (hsingle 1) g hg
      exact ⟨d, hgz.symm⟩)
    (hinjγ _ CaseM.mem_roots_B₁) (hinjγ _ CaseM.mem_roots_theta)
    (fun c => hzA _ (hθA c))
  intro e he
  rw [← hE1] at he
  obtain ⟨g, hg, rfl⟩ := he
  obtain ⟨c, rfl⟩ := hxsurj _ (hsingle 1) g hg
  exact key c

section Members

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
  {F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)}
include h hA hAne hA₀ hΔ₁

theorem exists_member₁ {β : Fin F.D.rank → ℤ} (hβ : β ∈ memberRoots F) :
    ∃ X ∈ Δ₁, quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ :=
  map_rootGroup_mem F (isRootClass_quot₁ h hA hAne hA₀ hΔ₁) hβ

theorem conjSub_member₁ {β : Fin F.D.rank → ℤ} (hβR : β ∈ F.D.roots) {X : Subgroup G}
    (hX : X ∈ Δ₁) (hXβ : quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ) {k : F.K}
    {w : (coxeterMatrix F.D.isFiniteType).Group} (hk : ActsAs F.D k w) (v : ↥(gen Δ₁))
    (hv : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v = F.Ψ k) :
    conjSub X (v : G) ∈ Δ₁ ∧ quotMap (gen Δ₁) (conjSub X (v : G)) =
      (F.D.rootGroup (weylAction F.D.isFiniteType w β)).map F.Ψ := by
  refine ⟨Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hX (gen_le_levi h hA hAne hA₀ hΔ₁ v.2), ?_⟩
  rw [LeviQuot.quotMap_conjSub X v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(v : G), v.2⟩ = F.Ψ k := hv
  rw [e, hXβ, map_conjSub_eq, hk β hβR]

theorem eq_of_quotMap_eq₁ {X Y : Subgroup G} (hX : X ∈ Δ₁) (hY : Y ∈ Δ₁)
    (hXY : quotMap (gen Δ₁) X = quotMap (gen Δ₁) Y) : X = Y :=
  quot_injOn₁ h hA hAne hA₀ hΔ₁ hX hY hXY

end Members

section V₂

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀)
  (hne : Δ₁ ≠ Δ₂)
include h hA hAne hA₀ hΔ₁ hΔ₂ hne

theorem stabBar₁_conjSub_of_mem_gen₂ (B : Subgroup G) {g : G} (hg : g ∈ gen Δ₂) :
    stabBar₁ Δ₁ (conjSub B g) = stabBar₁ Δ₁ B := by
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  unfold stabBar₁
  congr 1
  ext ⟨v, hv⟩
  simp only [Subgroup.mem_subgroupOf]
  rw [← conjSub_eq_self_iff, ← conjSub_eq_self_iff, ← conjSub_mul, (hc v hv g hg).eq,
    conjSub_mul]
  exact RankOne.map_conj_inj

theorem lowSet₁_conjSub_of_mem_gen₂ (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
    (B : Subgroup G) {g : G} (hg : g ∈ gen Δ₂) :
    lowSet₁ R A A₀ Δ₁ F (conjSub B g) = lowSet₁ R A A₀ Δ₁ F B := by
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  ext β
  simp only [lowSet₁, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => exists_congr fun X => and_congr_right fun hX => ?_
  have hXg : conjSub X g⁻¹ = X := conjSub_of_forall_commute fun x hx =>
    (hc x (le_gen hX hx) _ (inv_mem hg)).symm
  simp only [deltaSet, Set.mem_inter_iff, mem_lambdaSet_conjSub_iff h.root, hXg]

theorem LowMember₁.conjSub_of_mem_gen₂ {F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)}
    {B : Subgroup G} (hB : LowMember₁ R A A₀ Δ₁ F B) {g : G} (hg : g ∈ gen Δ₂) :
    LowMember₁ R A A₀ Δ₁ F (conjSub B g) := by
  refine ⟨conjSub_mem_lambdaStar_of_mem_levi h.root hB.mem
    (gen_le_levi h hA hAne hA₀ hΔ₂ hg), ?_⟩
  rw [stabBar₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne B hg]
  exact hB.le

omit hΔ₁ hne in
theorem exists_conjSub_commuting_of_mem₂ {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) :
    ∃ g ∈ gen Δ₂, Commuting Q₂ (conjSub B g) := by
  have := h.finite
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  obtain ⟨D', hD', hD'B⟩ : ∃ D' ∈ Δ₂, Commuting D' B := by
    by_cases hc : Commuting B P₂
    · exact ⟨P₂, hP₂, hc.symm⟩
    · have hs := special_of_not_commuting_of_mem_leviSet h hA hB (hl₂ hP₂) hc
      obtain ⟨-, D'', hD'', hPD'', hBD''⟩ :=
        exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hl₂ hP₂) hB hs
      exact ⟨D'', Sec9.mem_of_opposite h hA hAne hA₀ hΔ₂ hP₂ hD'' hPD'', hBD''.1.2.2⟩
  obtain ⟨g, hg, hgQ⟩ := Sec9.exists_conjSub_eq h hΔ₂ hD' hQ₂
  refine ⟨g, hg, ?_⟩
  rw [← hgQ]
  exact hD'B.conjSub g

end V₂

theorem weylAction_apply_zero_of_neg {n : ℕ} {A' : Matrix (Fin n) (Fin n) ℤ}
    (hA' : TauCeti.IsFiniteType A') (P : ExclNS.EpsCoords A') (hn : 2 ≤ n) {l : Fin n → ℤ}
    (hl : P.E l = P.c • ExclNS.ev n 0) {y : (coxeterMatrix hA').Group}
    (hy : weylAction hA' y l = -l) {β : Fin n → ℤ} (hβ : β ⟨0, by omega⟩ = 0) :
    weylAction hA' y β ⟨0, by omega⟩ = 0 := by
  have key : ∀ v, P.invForm.Q v l = P.c * v ⟨0, by omega⟩ := fun v => by
    rw [ExclNS.EpsCoords.invForm_apply, hl, dotProduct_smul, ExclNS.dotProduct_ev _ (by omega),
      CaseE.eps_apply_zero P hn, smul_eq_mul]
  have h1 := P.invForm.weylAction hA' y β l
  rw [hy, map_neg, key, key, hβ, mul_zero, neg_eq_zero] at h1
  exact (mul_eq_zero.1 h1).resolve_left P.c_pos.ne'

section Highest

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2)
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
  {F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)} {B : Subgroup G}
  (hB : LowMember₁ R A A₀ Δ₁ F B)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB

theorem LowMember₁.reflection_mem_of_mem_stabBar {t : Fin F.D.rank}
    (ht : F.Ψ (F.n t) ∈ stabBar₁ Δ₁ B) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) :
    weylAction F.D.isFiniteType ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple t) β ∈
      lowSet₁ R A A₀ Δ₁ F B := by
  obtain ⟨Y, hY₁, hY, hYβ⟩ := hβ.2
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ (F.n t))
  have hvB : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B := by
    rw [hv]
    exact ht
  obtain ⟨h1, h2'⟩ := hB.conjSub_mem h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hY₁ hY v hvB
  refine ⟨weylAction_mem_memberRoots F hβ.1 _, conjSub Y (v : G), h1, h2', ?_⟩
  rw [LeviQuot.quotMap_conjSub Y v.2]
  have e : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(v : G), v.2⟩ = F.Ψ (F.n t) := hv
  rw [e, hYβ, map_conjSub_eq, actsAs_n F.hct t β (memberRoots_subset F hβ.1)]

theorem LowMember₁.mem_lowSet_iff_of_parJ
    (hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B)
    {u : (coxeterMatrix F.D.isFiniteType).Group} (hu : u ∈ parJ F.D.isFiniteType)
    (β : Fin F.D.rank → ℤ) :
    β ∈ lowSet₁ R A A₀ Δ₁ F B ↔ weylAction F.D.isFiniteType u β ∈ lowSet₁ R A A₀ Δ₁ F B := by
  obtain ⟨ω, hω, rfl⟩ :=
    (coxeterMatrix F.D.isFiniteType).toCoxeterSystem.exists_wordProd_eq_of_mem_parabolic hu
  clear hu
  induction ω generalizing β with
  | nil => simp
  | cons a ω ih =>
    have ha := hns a (hω a List.mem_cons_self)
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply,
      ih β (fun i hi => hω i (List.mem_cons_of_mem a hi))]
    refine ⟨hB.reflection_mem_of_mem_stabBar h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne ha, fun hβ => ?_⟩
    have := hB.reflection_mem_of_mem_stabBar h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne ha hβ
    rwa [← weylAction_mul_apply, CoxeterSystem.simple_mul_simple_self, map_one,
      Module.End.one_apply] at this

omit hmax h2 hΔ₂ hne in
theorem LowMember₁.mem_lambdaSet_of_mem_lowSet {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet₁ R A A₀ Δ₁ F B) {X : Subgroup G} (hX : X ∈ Δ₁)
    (hXβ : quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ) : B ∈ lambdaSet R X := by
  obtain ⟨Y, hY₁, hY, hYβ⟩ := hβ.2
  have e : X = Y := quot_injOn₁ h hA hAne hA₀ hΔ₁ hX hY₁ (hXβ.trans hYβ.symm)
  subst e
  exact mem_lambdaSet_comm hB.mem.1.1.1 hY.2

omit hmax h2 hΔ₂ hne in
theorem LowMember₁.special_of_neg_mem_lowSet {β : Fin F.D.rank → ℤ}
    (hβ : -β ∈ lowSet₁ R A A₀ Δ₁ F B) {X : Subgroup G} (hX : X ∈ Δ₁)
    (hXβ : quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ) : Special R B X := by
  have := h.finite
  have hq := isRootClass_quot₁ h hA hAne hA₀ hΔ₁
  have hβO : β ∈ memberRoots F := by
    have := neg_mem_memberRoots F hβ.1
    rwa [neg_neg] at this
  obtain ⟨Y, hY₁, hYβ⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hβ.1
  have hBY := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ hβ hY₁ hYβ
  have hopp : Opposite X Y := by
    refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hX hY₁ ?_
    rw [hXβ, hYβ]
    exact opposite_map_rootGroup F hβO
  refine special_of_not_commuting_of_mem_leviSet h hA hB.mem
    (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX) fun hc => ?_
  exact not_commuting_of_opposite_of_mem_lambdaSet h.root
    (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX).1.1 hopp hBY hc.symm

omit hB in
theorem conjSub_eq_of_mk_eq₁ {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) {v v' : ↥(gen Δ₁)}
    (hvv : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v =
      QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v') :
    conjSub X (v : G) = conjSub X (v' : G) := by
  have hz : v'⁻¹ * v ∈ Subgroup.center ↥(gen Δ₁) := QuotientGroup.eq.1 hvv.symm
  have e : (v : G) = (v' : G) * ((v'⁻¹ * v : ↥(gen Δ₁)) : G) := by simp
  rw [e, conjSub_mul, conjSub_eq_of_mem_center h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hX hz]

omit h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne in
theorem LowMember₁.map_rootGroup_le_of_apply_zero (hn : 1 ≤ F.D.rank)
    (hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B)
    (hT : (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B) {β : Fin F.D.rank → ℤ} (hβ : β ∈ F.D.roots)
    (h0 : β ⟨0, by omega⟩ = 0) : (F.D.rootGroup β).map F.Ψ ≤ stabBar₁ Δ₁ B := by
  set J : Set (Fin F.D.rank) := {k | k.val ≠ 0} with hJ
  set Par := (stabBar₁ Δ₁ B).comap F.Ψ with hPar
  have hTPar : (⨆ i, F.H i) ≤ Par := Subgroup.map_le_iff_le_comap.1 hT
  have hUPar : negUnipotent F.D ≤ Par := Subgroup.map_le_iff_le_comap.1 hB.le
  have hnPar : ∀ k ∈ J, F.n k ∈ Par := fun k hk => hns k hk
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single F.hdiv hβ
  have hsupp : ∀ k ∉ J, weylAction F.D.isFiniteType w (Pi.single i 1) k = 0 := by
    intro k hk
    have hk0 : k = ⟨0, by omega⟩ := Fin.ext (by simpa [hJ] using hk)
    rw [hk0]
    exact h0
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support F.D.isFiniteType J w i hsupp
  have hzPar : nrep F.hct z⁻¹ ∈ Par := by
    obtain ⟨p, hp, p', hp', he⟩ := exists_eq_mul_mul_of_weylNHom_eq F.hct F.hext hTPar hnPar 1
      ⟨nrep F.hct z⁻¹, nrep_mem_weylN F.hct z⁻¹⟩ (inv_mem hz) (one_mem _)
      (by rw [weylNHom_nrep, map_one, mul_one, mul_one])
    have he' : nrep F.hct z⁻¹ = p * p' := by simpa using he
    rw [he']
    exact mul_mem hp hp'
  have hmR : -Pi.single m 1 ∈ F.D.roots :=
    (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).neg_mem _
      ((RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem m)
  have hXm : F.D.rootGroup (Pi.single m 1) ≤ Par := by
    have e := actsAs_n F.hct m _ hmR
    rw [map_neg, weylAction_simple_single, neg_neg] at e
    rw [← e]
    rintro _ ⟨x, hx, rfl⟩
    have hxPar : x ∈ Par := hUPar (rootGroup_le_negUnipotent hmR (by
      rw [ht_neg, ht_single]
      omega) hx)
    exact Par.mul_mem (Par.mul_mem (hnPar m hm) hxPar) (Par.inv_mem (hnPar m hm))
  have hβz : weylAction F.D.isFiniteType w (Pi.single i 1) =
      weylAction F.D.isFiniteType z⁻¹ (Pi.single m 1) := by
    rw [← hzm, weylAction_inv_apply_apply]
  rw [hβz, ← actsAs_nrep F.hct z⁻¹ _
    ((RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem m),
    Subgroup.map_le_iff_le_comap]
  rintro _ ⟨x, hx, rfl⟩
  exact Par.mul_mem (Par.mul_mem hzPar (hXm hx)) (Par.inv_mem hzPar)

theorem LowMember₁.exists_highest (P : ExclNS.EpsCoords F.D.cartan) (hn : 2 ≤ F.D.rank)
    (hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B)
    (hT : (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B)
    (h0 : -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ lowSet₁ R A A₀ Δ₁ F B)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) (hQB : Commuting Q₂ B) :
    ∃ γ : Fin F.D.rank → ℤ, P.E γ = ExclNS.ev F.D.rank 0 + ExclNS.ev F.D.rank 1 ∧
      -γ ∈ lowSet₁ R A A₀ Δ₁ F B ∧ ∃ C ∈ lambdaStar R A A₀, Special R B C ∧ ⁅B, C⁆ = A ∧
        C ∈ lambdaSet R P₂ ∧ Special R C Q₂ ∧
        (∀ X ∈ Δ₁, quotMap (gen Δ₁) X =
          (F.D.rootGroup (Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1)).map F.Ψ →
            C ∈ lambdaSet R X) ∧
        (∀ Y ∈ Δ₁, quotMap (gen Δ₁) Y =
          (F.D.rootGroup (-Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1)).map F.Ψ →
            Special R C Y) ∧
        (∀ X ∈ Δ₁, quotMap (gen Δ₁) X = (F.D.rootGroup γ).map F.Ψ → C ∈ lambdaSet R X) ∧
        (∀ Y ∈ Δ₁, quotMap (gen Δ₁) Y = (F.D.rootGroup (-γ)).map F.Ψ → Special R C Y) ∧
        (∀ X ∈ Δ₁, ∀ β ∈ F.D.roots, β ⟨0, by omega⟩ = 0 →
          quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ → Commuting C X) ∧
        (∀ β ∈ F.D.roots, β ⟨0, by omega⟩ = 0 → (F.D.rootGroup β).map F.Ψ ≤ stabBar₁ Δ₁ C) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hq := isRootClass_quot₁ h hA hAne hA₀ hΔ₁
  have hBR : B ∈ R := hB.mem.1.1.1
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hV₁ := gen_le_levi h hA hAne hA₀ hΔ₁
  have hc₁₂ := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  set α₀ : Fin F.D.rank → ℤ := Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 with hα₀
  obtain ⟨l, hl, hstab, htri⟩ := exists_dominant F.D.isFiniteType P hn
  obtain ⟨u₁, hu₁, hγE⟩ := exists_parJ_eq_add F.D.isFiniteType P hn hl hstab
  set γ := weylAction F.D.isFiniteType u₁ α₀ with hγdef
  have hα₀O : α₀ ∈ memberRoots F := by
    have := neg_mem_memberRoots F h0.1
    rwa [neg_neg] at this
  have hγO : γ ∈ memberRoots F := weylAction_mem_memberRoots F hα₀O u₁
  have hγS : -γ ∈ lowSet₁ R A A₀ Δ₁ F B := by
    have := (hB.mem_lowSet_iff_of_parJ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hns hu₁ (-α₀)).1 h0
    rwa [map_neg] at this
  obtain ⟨y, hyα, hyγ, hyl⟩ := exists_weyl_neg F.D.isFiniteType P hn hl hγE
  obtain ⟨hBQ₂, hsPB⟩ := CaseOA.natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hB.mem hQB
  set E₁ := ⁅P₂, B⁆ with hE₁def
  have hE₁' : E₁ = ⁅B, P₂⁆ := Subgroup.commutator_comm P₂ B
  obtain ⟨hE₁, hE₁B, hE₁P⟩ :=
    commutator_mem_lambdaStar h hA hAne hA₀ hB.mem (hl₂ hP₂) hsPB.symm
  rw [← hE₁'] at hE₁ hE₁B hE₁P
  obtain ⟨g₂, hg₂, hBg₂⟩ : ∃ g₂ ∈ gen Δ₂, conjSub B g₂ = E₁ := by
    obtain ⟨D', hD', hPD', hpts⟩ :=
      Sec9.natural_points h hA hAne hA₀ (hl₂ hP₂) hB.mem hsPB.symm
    obtain ⟨-, g, hg, hgE⟩ := hpts E₁ hE₁.1.1.1 (by rw [hE₁']; exact le_sup_right)
    refine ⟨g, ?_, hgE⟩
    have hD'₂ : D' ∈ Δ₂ := Sec9.mem_of_opposite h hA hAne hA₀ hΔ₂ hP₂ hD' hPD'
    exact sup_le (le_gen hD'₂) (le_gen hP₂) (sup_comm D' P₂ ▸ hg)
  have hfix₂ : ∀ {X : Subgroup G}, X ∈ Δ₂ → ∀ {v : G}, v ∈ gen Δ₁ → conjSub X v = X :=
    fun hX _ hv => conjSub_eq_of_mem_comp₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne hX hv
  have hfix₁ : ∀ {X : Subgroup G}, X ∈ Δ₁ → ∀ {g : G}, g ∈ gen Δ₂ → conjSub X g = X :=
    fun hX _ hg => conjSub_of_forall_commute fun x hx => (hc₁₂ x (le_gen hX hx) _ hg).symm
  have hE₁l : ∀ {X : Subgroup G}, X ∈ Δ₁ → B ∈ lambdaSet R X → E₁ ∈ lambdaSet R X := by
    intro X hX hBX
    have := conjSub_mem_lambdaSet hR hBX g₂
    rwa [hBg₂, hfix₁ hX hg₂] at this
  have hE₁s : ∀ {X : Subgroup G}, X ∈ Δ₁ → Special R B X → Special R E₁ X := by
    intro X hX hBX
    have := Sec3.special_conjSub hR hBX g₂
    rwa [hBg₂, hfix₁ hX hg₂] at this
  have hsE₁Q : Special R E₁ Q₂ := by
    refine special_of_not_commuting_of_mem_leviSet h hA hE₁ (hl₂ hQ₂) fun hc => ?_
    refine Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₂ hE₁ fun Z hZ => ?_
    have hZle : Z ≤ P₂ ⊔ Q₂ := hgen₂ ▸ le_gen hZ
    exact (Commuting.sup_left hE₁P.1.2.2 hc.symm).mono hZle le_rfl
  have hstep7 : ∃ v₁ : ↥(gen Δ₁), ¬ Commuting B (conjSub E₁ (v₁ : G)) := by
    obtain ⟨C', hC', hBC'⟩ : ∃ C' ∈ lambdaStar R A A₀, ¬ Commuting B C' := by
      by_contra! hall
      have hBM : Commuting B (M R A) := by
        rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
        exact gen_le fun C hC => commuting_iff_le_centralizer.1 (hall C hC)
      have hmem : B ∈ {X | X ∈ R ∧ Commuting X (M R A)} := ⟨hBR, hBM⟩
      rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
      exact hB.mem.1.1.2.1 hmem
    obtain ⟨v, hv, rfl⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hB.mem hC'
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
      CaseOA.exists_eq_mul_of_mem_levi h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hv
    refine ⟨⟨v₁, hv₁⟩, fun hc => hBC' ?_⟩
    have hle : conjSub B v₂ ≤ B ⊔ E₁ := by
      have hinv := Sec3.conjSub_sup_commutator_eq hR hiso (hl₂ hQ₂).1.1 (hl₂ hP₂).1.1
        hPQ₂.symm hBQ₂ ⟨hBR, hsPB⟩ (show v₂ ∈ Q₂ ⊔ P₂ by rw [sup_comm, ← hgen₂]; exact hv₂)
      rw [← hinv]
      exact Subgroup.map_mono le_sup_left
    have hle' : conjSub B (v₁ * v₂) ≤ conjSub B v₁ ⊔ conjSub E₁ v₁ := by
      rw [conjSub_mul, ← Subgroup.map_sup]
      exact Subgroup.map_mono hle
    have hBv₁ : Commuting B (conjSub B v₁) := by
      have hBv : conjSub B v₁ ∈ lambdaStar R A A₀ :=
        conjSub_mem_lambdaStar_of_mem_levi hR hB.mem (hV₁ hv₁)
      have hQv : Commuting Q₂ (conjSub B v₁) := by
        have := hQB.conjSub v₁
        rwa [hfix₂ hQ₂ hv₁] at this
      obtain ⟨hBvQ, -⟩ :=
        CaseOA.natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hBv hQv
      exact Sec9.commuting_of_mem_lambdaSet_inter h hA (hl₂ hQ₂).1.1 (hl₂ hQ₂).1.2.1 hBQ₂ hBvQ
        hB.mem.1 hBv.1
    exact (Commuting.sup_right hBv₁ hc).mono le_rfl hle'
  set Par := (stabBar₁ Δ₁ B).comap F.Ψ with hPar
  have hTPar : (⨆ i, F.H i) ≤ Par := Subgroup.map_le_iff_le_comap.1 hT
  have hUPar : negUnipotent F.D ≤ Par := Subgroup.map_le_iff_le_comap.1 hB.le
  have hnPar : ∀ k ∈ {k : Fin F.D.rank | k.val ≠ 0}, F.n k ∈ Par := fun k hk => hns k hk
  have hfixPar : ∀ v : ↥(gen Δ₁),
      QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B →
        conjSub B (v : G) = B ∧ conjSub E₁ (v : G) = E₁ := by
    intro v hv
    have hvB : conjSub B (v : G) = B := conjSub_eq_self_iff.2
      ((mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem v).1 hv)
    refine ⟨hvB, ?_⟩
    change (⁅P₂, B⁆ : Subgroup G).map (MulAut.conj (v : G)).toMonoidHom = ⁅P₂, B⁆
    rw [Subgroup.map_commutator]
    change ⁅conjSub P₂ (v : G), conjSub B (v : G)⁆ = _
    rw [hfix₂ hP₂ v.2, hvB]
  set Φ : F.K → Prop := fun k => ∀ v : ↥(gen Δ₁),
    QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v = F.Ψ k →
      Commuting B (conjSub E₁ (v : G)) with hΦdef
  have hΦiff : ∀ k (v : ↥(gen Δ₁)), QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v = F.Ψ k →
      (Φ k ↔ Commuting B (conjSub E₁ (v : G))) := by
    intro k v hv
    refine ⟨fun hΦ => hΦ v hv, fun hc v' hv' => ?_⟩
    rwa [conjSub_eq_of_mk_eq₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hE₁ (hv'.trans hv.symm)]
  have hΦPar : ∀ k, ∀ p ∈ Par, ∀ p' ∈ Par, (Φ (p * k * p') ↔ Φ k) := by
    intro k p hp p' hp'
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ k)
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ p)
    obtain ⟨u', hu'⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (F.Ψ p')
    have huB := hfixPar u (hu ▸ hp)
    have hu'B := hfixPar u' (hu' ▸ hp')
    rw [hΦiff (p * k * p') (u * v * u') (by rw [map_mul, map_mul, hu, hv, hu', map_mul, map_mul]),
      hΦiff k v hv]
    simp only [Subgroup.coe_mul]
    rw [conjSub_mul, conjSub_mul, hu'B.2]
    conv_lhs => rw [← huB.1]
    exact commuting_conjSub_iff' (u : G)
  have hΦ1 : Φ 1 := by
    rw [hΦiff 1 1 (by rw [map_one, map_one])]
    simpa using hE₁B.1.2.2
  have hΦn₀ : Φ (F.n ⟨0, by omega⟩) := by
    have hα₀' : -α₀ ∈ memberRoots F := h0.1
    obtain ⟨X₀, hX₀, hX₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hα₀O
    obtain ⟨Y₀, hY₀, hY₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hα₀'
    have hBY₀ := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hY₀ hY₀q
    have hsBX₀ := hB.special_of_neg_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hX₀ hX₀q
    have hopp : Opposite X₀ Y₀ := by
      refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hX₀ hY₀ ?_
      rw [hX₀q, hY₀q]
      exact opposite_map_rootGroup F hα₀O
    have hmem : F.Ψ (F.n ⟨0, by omega⟩) ∈ quotMap (gen Δ₁) (X₀ ⊔ Y₀) := by
      rw [quotMap_sup₁ (le_gen hX₀) (le_gen hY₀), hX₀q, hY₀q, ← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem F.Ψ (F.hct.n_mem _)
    obtain ⟨ℓ, hℓ, hℓe⟩ := LeviQuot.exists_of_mem_quotMap hmem
    rw [hΦiff _ ℓ hℓe]
    set B' := conjSub B (ℓ : G) with hB'def
    have hB' : B' ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hB.mem (hV₁ ℓ.2)
    obtain ⟨-, hKB, -⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hB.mem (hl₁ hX₀) hsBX₀
    have hK' : ⁅X₀, B⁆ ∈ lambdaSet R B := by rw [Subgroup.commutator_comm]; exact hKB
    have hB'le : B' ≤ B ⊔ ⁅X₀, B⁆ := by
      have hinv := Sec3.conjSub_sup_commutator_eq hR hiso (hl₁ hY₀).1.1 (hl₁ hX₀).1.1 hopp.symm
        hBY₀ ⟨hBR, hsBX₀.symm⟩ (show (ℓ : G) ∈ Y₀ ⊔ X₀ by rw [sup_comm]; exact hℓ)
      rw [← hinv]
      exact Subgroup.map_mono le_sup_left
    have hBB' : Commuting B' B := by
      by_cases he : B' = B
      · rw [he]
        exact hR.commuting_self hBR
      · have := (mem_lambdaSet_of_le_sup hR hiso hBR hK' hBR le_sup_left hB'.1.1.1 hB'le
          (Ne.symm he)).1
        exact this.1.2.2.symm
    have hE₁B' : Commuting E₁ B' := by
      by_cases he : B' = B
      · rw [he]
        exact hE₁B.1.2.2.symm
      · have hB'B := (mem_lambdaSet_of_le_sup hR hiso hBR hK' hBR le_sup_left hB'.1.1.1 hB'le
          (Ne.symm he)).1
        exact Sec9.commuting_of_mem_lambdaSet_inter h hA hBR hB.mem.1.1.2.1 hE₁B hB'B hE₁.1
          hB'.1
    have hconj : conjSub E₁ (ℓ : G) = ⁅P₂, B'⁆ := by
      change (⁅P₂, B⁆ : Subgroup G).map (MulAut.conj (ℓ : G)).toMonoidHom = _
      rw [Subgroup.map_commutator]
      change ⁅conjSub P₂ (ℓ : G), conjSub B (ℓ : G)⁆ = _
      rw [hfix₂ hP₂ ℓ.2]
    rw [hconj]
    refine (commuting_iff_commutator_eq_bot.2
      (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)).symm
    · rw [commuting_iff_commutator_eq_bot.1 hBB', Subgroup.commutator_bot_left]
    · rw [← hE₁', commuting_iff_commutator_eq_bot.1 hE₁B']
  have hn₀N : F.n ⟨0, by omega⟩ ∈ weylN F.n F.H := n_mem_weylN _
  have hΦN : ∀ x : weylN F.n F.H, Φ x ∨ (Φ x ↔ Φ (nrep F.hct y⁻¹)) := by
    intro x
    rcases htri (weylNHom F.hct F.hext x) with hw | hw | ⟨u, hu, v, hv, hw⟩
    · left
      obtain ⟨p, hp, p', hp', he⟩ := exists_eq_mul_mul_of_weylNHom_eq F.hct F.hext hTPar hnPar 1 x
        (hstab _ hw) (one_mem _) (by rw [map_one, mul_one, mul_one])
      rw [he]
      simpa using (hΦPar 1 p hp p' hp').2 hΦ1
    · right
      have hyw : weylNHom F.hct F.hext x = 1 * weylNHom F.hct F.hext ⟨nrep F.hct y⁻¹,
          nrep_mem_weylN F.hct y⁻¹⟩ * (y * weylNHom F.hct F.hext x) := by
        rw [weylNHom_nrep]
        group
      have hv' : y * weylNHom F.hct F.hext x ∈ parJ F.D.isFiniteType := by
        refine hstab _ ?_
        rw [weylAction_mul_apply, hw, map_neg, hyl, neg_neg]
      obtain ⟨p, hp, p', hp', he⟩ := exists_eq_mul_mul_of_weylNHom_eq F.hct F.hext hTPar hnPar
        ⟨nrep F.hct y⁻¹, nrep_mem_weylN F.hct y⁻¹⟩ x (one_mem _) hv' hyw
      rw [he]
      exact hΦPar _ p hp p' hp'
    · left
      obtain ⟨p, hp, p', hp', he⟩ := exists_eq_mul_mul_of_weylNHom_eq F.hct F.hext hTPar hnPar
        ⟨_, hn₀N⟩ x hu hv (by rw [hw, weylNHom_n])
      rw [he]
      exact (hΦPar _ p hp p' hp').2 hΦn₀
  have hnot : ¬ Φ (nrep F.hct y⁻¹) := by
    obtain ⟨v₁, hv₁⟩ := hstep7
    obtain ⟨g, hg⟩ := F.surj (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v₁)
    have hΦg : ¬ Φ g := fun hΦ => hv₁ ((hΦiff g v₁ hg.symm).1 hΦ)
    obtain ⟨b, hb, x, hx, b', hb', rfl⟩ := exists_eq_mul_mul_negBorel F.hct F.hext g
    have hbPar : b ∈ Par := sup_le hTPar hUPar hb
    have hb'Par : b' ∈ Par := sup_le hTPar hUPar hb'
    rw [hΦPar x b hbPar b' hb'Par] at hΦg
    rcases hΦN ⟨x, hx⟩ with h1 | h1
    · exact absurd h1 hΦg
    · exact fun h' => hΦg (h1.2 h')
  simp only [hΦdef, not_forall] at hnot
  obtain ⟨vt, hvt, hBC⟩ := hnot
  set C := conjSub E₁ (vt : G) with hCdef
  have hC : C ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hE₁ (hV₁ vt.2)
  have hBCne : B ≠ C := fun e => hBC (by rw [← e]; exact hR.commuting_self hBR)
  obtain ⟨hsBC, hBCA⟩ :=
    (commuting_or_commutator_eq_of_mem_lambdaSet h hA hB.mem.1 hC.1 hBCne).resolve_left hBC
  have hact : ActsAs F.D (nrep F.hct y⁻¹)⁻¹ y := by
    have := actsAs_inv (actsAs_nrep F.hct y⁻¹)
    rwa [inv_inv] at this
  have hvt' : QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) vt⁻¹ = F.Ψ (nrep F.hct y⁻¹)⁻¹ := by
    rw [map_inv, map_inv, hvt]
  have hrelC : ∀ {X : Subgroup G} {β : Fin F.D.rank → ℤ}, β ∈ F.D.roots → X ∈ Δ₁ →
      quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ →
        (weylAction F.D.isFiniteType y β ∈ lowSet₁ R A A₀ Δ₁ F B → C ∈ lambdaSet R X) ∧
        (-weylAction F.D.isFiniteType y β ∈ lowSet₁ R A A₀ Δ₁ F B → Special R C X) := by
    intro X β hβR hX hXq
    obtain ⟨hX', hX'q⟩ := conjSub_member₁ h hA hAne hA₀ hΔ₁ hβR hX hXq hact vt⁻¹ hvt'
    have hXX : conjSub (conjSub X ((vt⁻¹ : ↥(gen Δ₁)) : G)) (vt : G) = X := by
      simp only [Subgroup.coe_inv]
      exact ExclNS.conjSub_inv_conjSub X _
    refine ⟨fun hyβ => ?_, fun hyβ => ?_⟩
    · have hBX' := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ hyβ hX' hX'q
      have := conjSub_mem_lambdaSet hR (hE₁l hX' hBX') (vt : G)
      rwa [hXX] at this
    · have hsBX' := hB.special_of_neg_mem_lowSet h hA hAne hA₀ hΔ₁ hyβ hX' hX'q
      have := Sec3.special_conjSub hR (hE₁s hX' hsBX') (vt : G)
      rwa [hXX] at this
  have hα₀R : α₀ ∈ F.D.roots := memberRoots_subset F hα₀O
  have hγR : γ ∈ F.D.roots := memberRoots_subset F hγO
  have hnα₀R : -α₀ ∈ F.D.roots := memberRoots_subset F h0.1
  have hnγR : -γ ∈ F.D.roots := memberRoots_subset F hγS.1
  refine ⟨γ, hγE, hγS, C, hC, hsBC, hBCA, ?_, ?_, fun X hX hXq => ?_, fun Y hY hYq => ?_,
    fun X hX hXq => ?_, fun Y hY hYq => ?_, fun X hX β hβR hβ0 hXq => ?_,
    fun β hβR hβ0 => ?_⟩
  · have := conjSub_mem_lambdaSet hR hE₁P (vt : G)
    rwa [hfix₂ hP₂ vt.2] at this
  · have := Sec3.special_conjSub hR hsE₁Q (vt : G)
    rwa [hfix₂ hQ₂ vt.2] at this
  · exact (hrelC hα₀R hX hXq).1 (by rw [hyα]; exact hγS)
  · exact (hrelC hnα₀R hY hYq).2 (by rw [map_neg, neg_neg, hyα]; exact hγS)
  · exact (hrelC hγR hX hXq).1 (by rw [hyγ]; exact h0)
  · exact (hrelC hnγR hY hYq).2 (by rw [map_neg, neg_neg, hyγ]; exact h0)
  ·
    obtain ⟨hX', hX'q⟩ := conjSub_member₁ h hA hAne hA₀ hΔ₁ hβR hX hXq hact vt⁻¹ hvt'
    have hy0 := weylAction_apply_zero_of_neg F.D.isFiniteType P hn hl hyl hβ0
    have hle := hB.map_rootGroup_le_of_apply_zero (by omega) hns hT
      (weylAction_mem_roots _ _ hβR) hy0
    have hX'B := (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB.mem
      hX').2 (hX'q ▸ hle)
    have hE₁X' := hX'B.symm.conjSub g₂
    rw [hBg₂, hfix₁ hX' hg₂] at hE₁X'
    have hXX : conjSub (conjSub X ((vt⁻¹ : ↥(gen Δ₁)) : G)) (vt : G) = X := by
      simp only [Subgroup.coe_inv]
      exact ExclNS.conjSub_inv_conjSub X _
    have := hE₁X'.conjSub (vt : G)
    rwa [hXX] at this
  ·
    have hy0 := weylAction_apply_zero_of_neg F.D.isFiniteType P hn hl hyl hβ0
    have hle := hB.map_rootGroup_le_of_apply_zero (by omega) hns hT
      (weylAction_mem_roots _ _ hβR) hy0
    rw [hCdef, stabBar₁_conjSub h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hE₁ vt, hvt, ← hBg₂,
      stabBar₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne B hg₂]
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_conjSub, ← map_inv, ← map_mul, ← map_mul]
    refine hle ⟨_, ?_, rfl⟩
    rw [← hact β hβR]
    exact ⟨z, hz, by simp⟩

end Highest

section D4

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2)
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne

theorem exists_D4 (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)) {P₂ Q₂ : Subgroup G}
    (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) :
    ∃ P Q : Fin 4 → Subgroup G, IsConfig R (edgeD 4) P Q ∧ P 0 = P₂ ∧
      P 1 ∈ lambdaStar R A A₀ ∧ P 2 ∈ Δ₁ ∧ P 3 ∈ Δ₁ := by
  have := h.finite
  have hR := h.root
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hc₁₂ := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  obtain ⟨hCt, hn, hi₀, B₀, hB₀, h0₀, hns₀, hT₀⟩ :=
    exists_attach h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F
  obtain ⟨P⟩ : Nonempty (ExclNS.EpsCoords F.D.cartan) := by
    rcases hCt with hCt | hCt
    · exact ⟨hCt ▸ ExclNS.epsB F.D.rank⟩
    · exact ⟨hCt ▸ ExclNS.epsC F.D.rank⟩
  obtain ⟨g, hg, hgQ⟩ :=
    exists_conjSub_commuting_of_mem₂ h hA hAne hA₀ hΔ₂ hB₀.mem hP₂ hQ₂
  set B := conjSub B₀ g with hBdef
  have hB : LowMember₁ R A A₀ Δ₁ F B := hB₀.conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne hg
  have hS : lowSet₁ R A A₀ Δ₁ F B = lowSet₁ R A A₀ Δ₁ F B₀ :=
    lowSet₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne F B₀ hg
  have hstab : stabBar₁ Δ₁ B = stabBar₁ Δ₁ B₀ :=
    stabBar₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne B₀ hg
  have h0 : -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ lowSet₁ R A A₀ Δ₁ F B := hS ▸ h0₀
  have hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B :=
    fun s hs => hstab ▸ hns₀ s hs
  have hT : (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B := hstab ▸ hT₀
  obtain ⟨γ, hγE, hγS, C, hC, hsBC, hBCA, hCP₂, hsCQ₂, hCX₀, hsCY₀, hCXγ, hsCYγ, -, -⟩ :=
    hB.exists_highest h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne P (by omega) hns hT h0 hP₂ hQ₂ hPQ₂
      hgen₂ hgQ
  set α₀ : Fin F.D.rank → ℤ := Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 with hα₀
  have hα₀O : α₀ ∈ memberRoots F := by
    have := neg_mem_memberRoots F h0.1
    rwa [neg_neg] at this
  have hγO : γ ∈ memberRoots F := by
    have := neg_mem_memberRoots F hγS.1
    rwa [neg_neg] at this
  obtain ⟨X₀, hX₀, hX₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hα₀O
  obtain ⟨Y₀, hY₀, hY₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ h0.1
  obtain ⟨Xγ, hXγ, hXγq⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hγO
  obtain ⟨Yγ, hYγ, hYγq⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hγS.1
  have hBY₀ := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hY₀ hY₀q
  have hBYγ := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ hγS hYγ hYγq
  have hsBX₀ := hB.special_of_neg_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hX₀ hX₀q
  have hsBXγ := hB.special_of_neg_mem_lowSet h hA hAne hA₀ hΔ₁ hγS hXγ hXγq
  have hopp₀ : Opposite X₀ Y₀ := by
    refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hX₀ hY₀ ?_
    rw [hX₀q, hY₀q]
    exact opposite_map_rootGroup F hα₀O
  have hoppγ : Opposite Xγ Yγ := by
    refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hXγ hYγ ?_
    rw [hXγq, hYγq]
    exact opposite_map_rootGroup F hγO
  obtain ⟨hBQ₂, hsPB⟩ := CaseOA.natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hB.mem hgQ
  obtain ⟨hF', -, -, -⟩ := CaseD4.commutator_props h hA hA₀ hC
  set F' := ⁅A₀, C⁆ with hF'def
  have hBF' : Opposite B F' := CaseOA.opposite_of_extremal h hA hA₀ hB.mem hC hsBC hBCA
  have e0 : EdgeRel R P₂ B Q₂ F' := CaseOA.edgeRel_of_extremal h hA hAne hA₀ (hl₂ hP₂) (hl₂ hQ₂)
    hPQ₂ hB.mem hC hBQ₂ hsPB.symm hCP₂ hsCQ₂ hsBC hBCA
  have e2 : EdgeRel R X₀ B Y₀ F' := CaseOA.edgeRel_of_extremal h hA hAne hA₀ (hl₁ hX₀) (hl₁ hY₀)
    hopp₀ hB.mem hC hBY₀ hsBX₀ (hCX₀ X₀ hX₀ hX₀q) (hsCY₀ Y₀ hY₀ hY₀q) hsBC hBCA
  have e3 : EdgeRel R Xγ B Yγ F' := CaseOA.edgeRel_of_extremal h hA hAne hA₀ (hl₁ hXγ)
    (hl₁ hYγ) hoppγ hB.mem hC hBYγ hsBXγ (hCXγ Xγ hXγ hXγq) (hsCYγ Yγ hYγ hYγq) hsBC hBCA
  have hc₂ : ∀ {X Y : Subgroup G}, X ∈ Δ₂ → Y ∈ Δ₁ → Commuting X Y := fun hX hY x hx y hy =>
    (hc₁₂ y (le_gen hY hy) x (le_gen hX hx)).symm
  obtain ⟨ñ, hñ⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁))
    (F.Ψ (F.n ⟨0, by omega⟩))
  have hact := actsAs_n F.hct (⟨0, by omega⟩ : Fin F.D.rank)
  have hs₀γ : weylAction F.D.isFiniteType
      ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple ⟨0, by omega⟩) γ = γ := by
    refine P.inj ?_
    rw [weylAction_simple, P.refl, hγE, ExclNS.stdReflB_add, ExclNS.stdReflB_ev_of_lt
      (by simp only; omega), ExclNS.stdReflB_ev_of_lt (by simp only; omega)]
    simp [ExclNS.swapN, add_comm]
  have hR' := fun {X : Subgroup G} (hX : X ∈ Δ₁) => (hl₁ hX).1.1
  have hconj : ∀ {X : Subgroup G} {β β' : Fin F.D.rank → ℤ}, β ∈ F.D.roots → X ∈ Δ₁ →
      quotMap (gen Δ₁) X = (F.D.rootGroup β).map F.Ψ →
      weylAction F.D.isFiniteType
        ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple ⟨0, by omega⟩) β = β' →
      ∀ {X' : Subgroup G}, X' ∈ Δ₁ → quotMap (gen Δ₁) X' = (F.D.rootGroup β').map F.Ψ →
        conjSub X (ñ : G) = X' := by
    intro X β β' hβ hX hXq hββ' X' hX' hX'q
    obtain ⟨h1, h2'⟩ := conjSub_member₁ h hA hAne hA₀ hΔ₁ hβ hX hXq hact ñ hñ
    rw [hββ'] at h2'
    exact eq_of_quotMap_eq₁ h hA hAne hA₀ hΔ₁ h1 hX' (h2'.trans hX'q.symm)
  have hα₀R : α₀ ∈ F.D.roots := memberRoots_subset F hα₀O
  have hγR : γ ∈ F.D.roots := memberRoots_subset F hγO
  have hs₀α : weylAction F.D.isFiniteType
      ((coxeterMatrix F.D.isFiniteType).toCoxeterSystem.simple ⟨0, by omega⟩) α₀ = -α₀ :=
    weylAction_simple_single _ _
  have eY₀ : conjSub Y₀ (ñ : G) = X₀ := hconj (memberRoots_subset F h0.1) hY₀ hY₀q
    (by rw [map_neg, hs₀α, neg_neg]) hX₀ hX₀q
  have eX₀ : conjSub X₀ (ñ : G) = Y₀ := hconj hα₀R hX₀ hX₀q hs₀α hY₀ hY₀q
  have eYγ : conjSub Yγ (ñ : G) = Yγ := hconj (memberRoots_subset F hγS.1) hYγ hYγq
    (by rw [map_neg, hs₀γ]) hYγ hYγq
  have eXγ : conjSub Xγ (ñ : G) = Xγ := hconj hγR hXγ hXγq hs₀γ hXγ hXγq
  have hñV : (ñ : G) ∈ levi R A A₀ := gen_le_levi h hA hAne hA₀ hΔ₁ ñ.2
  have hmemΔ : ∀ {D X : Subgroup G}, X ∈ Δ₁ → D ∈ lambdaSet R X → X ∈ deltaSet R A A₀ D :=
    fun {D X} hX hDX => ⟨hl₁ hX, mem_lambdaSet_comm (hR' hX) hDX⟩
  have hY₀Yγ : Commuting Y₀ Yγ :=
    commuting_of_mem_deltaSet h hA hA₀ hB.mem (hmemΔ hY₀ hBY₀) (hmemΔ hYγ hBYγ)
  have hX₀Xγ : Commuting X₀ Xγ :=
    commuting_of_mem_deltaSet h hA hA₀ hC (hmemΔ hX₀ (hCX₀ X₀ hX₀ hX₀q))
      (hmemΔ hXγ (hCXγ Xγ hXγ hXγq))
  have hX₀Yγ : Commuting X₀ Yγ := by
    have hBñ := conjSub_mem_lambdaStar_of_mem_levi hR hB.mem hñV
    have h1 := conjSub_mem_lambdaSet hR hBY₀ (ñ : G)
    have h2' := conjSub_mem_lambdaSet hR hBYγ (ñ : G)
    rw [eY₀] at h1
    rw [eYγ] at h2'
    exact commuting_of_mem_deltaSet h hA hA₀ hBñ (hmemΔ hX₀ h1) (hmemΔ hYγ h2')
  have hY₀Xγ : Commuting Y₀ Xγ := by
    have hCñ := conjSub_mem_lambdaStar_of_mem_levi hR hC hñV
    have h1 := conjSub_mem_lambdaSet hR (hCX₀ X₀ hX₀ hX₀q) (ñ : G)
    have h2' := conjSub_mem_lambdaSet hR (hCXγ Xγ hXγ hXγq) (ñ : G)
    rw [eX₀] at h1
    rw [eXγ] at h2'
    exact commuting_of_mem_deltaSet h hA hA₀ hCñ (hmemΔ hY₀ h1) (hmemΔ hXγ h2')
  refine ⟨![P₂, B, X₀, Xγ], ![Q₂, F', Y₀, Yγ], ⟨fun k => ?_, fun k => ?_, fun k => ?_,
    fun i j hij => ?_, fun i j hij h1 h2' => ?_⟩, rfl, hB.mem, hX₀, hXγ⟩
  · fin_cases k
    exacts [(hl₂ hP₂).1.1, hB.mem.1.1.1, hR' hX₀, hR' hXγ]
  · fin_cases k
    exacts [(hl₂ hQ₂).1.1, hF'.1.1.1, hR' hY₀, hR' hYγ]
  · fin_cases k
    exacts [hPQ₂, hBF', hopp₀, hoppγ]
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij
    · exact e0
    · exact e2.symm
    · exact e3.symm
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij h1 h2'
    · exact ⟨hc₂ hP₂ hX₀, hc₂ hP₂ hY₀, hc₂ hQ₂ hX₀, hc₂ hQ₂ hY₀⟩
    · exact ⟨hc₂ hP₂ hXγ, hc₂ hP₂ hYγ, hc₂ hQ₂ hXγ, hc₂ hQ₂ hYγ⟩
    · exact ⟨(hc₂ hP₂ hX₀).symm, (hc₂ hQ₂ hX₀).symm, (hc₂ hP₂ hY₀).symm, (hc₂ hQ₂ hY₀).symm⟩
    · exact ⟨hX₀Xγ, hX₀Yγ, hY₀Xγ, hY₀Yγ⟩
    · exact ⟨(hc₂ hP₂ hXγ).symm, (hc₂ hQ₂ hXγ).symm, (hc₂ hP₂ hYγ).symm, (hc₂ hQ₂ hYγ).symm⟩
    · exact ⟨hX₀Xγ.symm, hY₀Xγ.symm, hX₀Yγ.symm, hY₀Yγ.symm⟩

theorem center_gen_eq_bot (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
    (hS₂ : IsSL2Comp Δ₂) : Subgroup.center ↥(gen Δ₁) = ⊥ := by
  have := h.finite
  have hR := h.root
  obtain ⟨P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩ := hS₂
  obtain ⟨P, Q, hcfg, hP0, hP1, hP2, hP3⟩ :=
    exists_D4 h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F hP₂ hQ₂ hPQ₂ hgen₂
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  rw [eq_bot_iff]
  rintro ⟨z, hz⟩ hzc
  rw [Subgroup.mem_bot]
  have hzc' : (⟨z, hz⟩ : ↥(gen Δ₁)) ∈ Subgroup.center ↥(gen Δ₁) := hzc
  have hzV : ∀ v ∈ levi R A A₀, Commute z v := by
    have hle : levi R A A₀ ≤ Subgroup.centralizer {z} := iSup₂_le fun X hX x hx =>
      Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_mem_center h hA hAne hA₀ hΔ₁ hΔ₂ hne h2 hzc' hX hx).symm
    exact fun v hv => (Subgroup.mem_centralizer_singleton_iff.1 (hle hv)).symm
  have hzlevi : z ∈ levi R A A₀ := gen_le_levi h hA hAne hA₀ hΔ₁ hz
  have hzA : ∀ a ∈ A, Commute z a := fun a ha =>
    ((Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hzlevi)) a ha).symm
  have hzA₀ : ∀ a ∈ A₀, Commute z a := fun a ha =>
    ((Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hzlevi)) a ha).symm
  have hzE : conjSub (P 1) z = P 1 :=
    conjSub_eq_of_mem_center h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP1 hzc'
  have hP0' : P 0 ∈ leviSet R A A₀ := by
    rw [hP0]
    exact Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hP₂
  have hzE' := commute_of_isConfig_D4 h hA hcfg hP1 hP0' (hl₁ hP2) (hl₁ hP3) hzV hzA hzE
  have hzΛ : ∀ B ∈ lambdaStar R A A₀, ∀ b ∈ B, Commute z b := by
    intro B hB b hb
    obtain ⟨v, hv, rfl⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hP1 hB
    obtain ⟨e, he, rfl⟩ := hb
    exact ((hzV v hv).mul_right (hzE' e he)).mul_right (hzV v hv).inv_right
  have hMc : M R A ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    exact gen_le fun B hB b hb => Subgroup.mem_centralizer_singleton_iff.2 (hzΛ B hB b hb).symm
  have hA₀c : A₀ ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzA₀ a ha).symm
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← gen_lambdaSet_sup_eq_top h hA hA₀]
    exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hMc) hA₀c
  have hzG : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (htop (Subgroup.mem_top g))
  rw [h.center, Subgroup.mem_bot] at hzG
  exact Subtype.ext hzG

end D4

end CaseOANSL

end CFSG.Timmesfeld.ARS
