module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtLocal
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtModel

import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut)

section Iso

variable {G Y : Type} [Group G] [Group Y] {P1 P2 : Subgroup G} {M1 M2 : Subgroup Y}

theorem coe_ofSubgroupsIso_φ1_eq_φ2
    (Φ : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    {a : ↥P1} {b : ↥P2} (hab : (a : G) = b) : Subtype.val (Φ.φ1 a) = Subtype.val (Φ.φ2 b) := by
  obtain ⟨b, hb⟩ := b
  obtain rfl : (a : G) = b := hab
  let c : ↥(P1 ⊓ P2) := ⟨a, Subgroup.mem_inf.mpr ⟨a.2, hb⟩⟩
  exact (congrArg Subtype.val (Φ.comm1 c)).symm.trans (congrArg Subtype.val (Φ.comm2 c))

theorem coe_ofSubgroupsIso_φ1_symm_eq_φ2_symm
    (Φ : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    {x : ↥M1} {y : ↥M2} (hxy : (x : Y) = y) :
    Subtype.val (Φ.φ1.symm x) = Subtype.val (Φ.φ2.symm y) := by
  obtain ⟨y, hy⟩ := y
  obtain rfl : (x : Y) = y := hxy
  have hc := Φ.φ12.apply_symm_apply (⟨x, Subgroup.mem_inf.mpr ⟨x.2, hy⟩⟩ : ↥(M1 ⊓ M2))
  set c := Φ.φ12.symm (⟨x, Subgroup.mem_inf.mpr ⟨x.2, hy⟩⟩ : ↥(M1 ⊓ M2))
  have h1 : Φ.φ1.symm x = (RankTwoAmalgam.ofSubgroups P1 P2).α1 c :=
    Φ.φ1.injective ((Φ.φ1.apply_symm_apply x).trans
      ((congrArg (RankTwoAmalgam.ofSubgroups M1 M2).α1 hc).symm.trans (Φ.comm1 c)))
  have h2 : Φ.φ2.symm ⟨x, hy⟩ = (RankTwoAmalgam.ofSubgroups P1 P2).α2 c :=
    Φ.φ2.injective ((Φ.φ2.apply_symm_apply ⟨x, hy⟩).trans
      ((congrArg (RankTwoAmalgam.ofSubgroups M1 M2).α2 hc).symm.trans (Φ.comm2 c)))
  exact (congrArg Subtype.val h1).trans (congrArg Subtype.val h2).symm

end Iso

variable {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qExtLocalReduction.exists_mem_notMem_left (R : U4qExtLocalReduction L1 L2 S f) :
    ∃ τ ∈ S, τ ∉ L1 := by
  by_contra! h
  have hle : S ≤ S ⊓ L1 := fun s hs => ⟨hs, h s hs⟩
  have h1 := Subgroup.relIndex_eq_one.mpr hle
  have h2 := R.relIndex_eq
  omega

theorem U4qExtLocalReduction.sq_mem_inf (R : U4qExtLocalReduction L1 L2 S f) {τ : G}
    (hτS : τ ∈ S) : τ ^ 2 ∈ S ⊓ L1 :=
  Subgroup.mem_subgroupOf.mp (Subgroup.sq_mem_of_index_two R.relIndex_eq ⟨τ, hτS⟩)

theorem U4qExtLocalReduction.le_inf_sup_zpowers (R : U4qExtLocalReduction L1 L2 S f) {τ : G}
    (hτS : τ ∈ S) (hτL : τ ∉ L1) : S ≤ S ⊓ L1 ⊔ Subgroup.zpowers τ := by
  intro s hs
  by_cases hsL : s ∈ L1
  · exact Subgroup.mem_sup_left ⟨hs, hsL⟩
  · have h : (⟨s, hs⟩ * (⟨τ, hτS⟩ : ↥S)⁻¹ : ↥S) ∈ (S ⊓ L1).subgroupOf S := by
      rw [Subgroup.mul_mem_iff_of_index_two R.relIndex_eq, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      exact iff_of_false (fun h => hsL h.2) (fun h => hτL (by simpa using h.2))
    have h' : s * τ⁻¹ ∈ S ⊓ L1 := Subgroup.mem_subgroupOf.mp h
    rw [show s = s * τ⁻¹ * τ by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h')
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ))

theorem U4qExtLocalReduction.inf_left_le_right (R : U4qExtLocalReduction L1 L2 S f) :
    S ⊓ L1 ≤ L2 :=
  (R.inf_left_eq.trans R.inf_right_eq.symm).le.trans inf_le_right

variable [Finite G]

theorem U4qExtLocalReduction.notMem_sup_bigB_left (R : U4qExtLocalReduction L1 L2 S f) {τ : G}
    (hτS : τ ∈ S) (hτL : τ ∉ L1) : τ ∉ L1 ⊔ bigB L1 L2 (S ⊓ L1) := by
  intro hτ
  have hsyl := isSylowTwoOf_sup_bigB_left_of_le R.hyp inf_le_right R.inf_left_le_right
  have hSP : S ≤ L1 ⊔ bigB L1 L2 (S ⊓ L1) := (R.le_inf_sup_zpowers hτS hτL).trans
    (sup_le (inf_le_right.trans le_sup_left) (Subgroup.zpowers_le.mpr hτ))
  have h := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : S ⊓ L1 ≤ S) hSP
  rw [R.relIndex_eq] at h
  exact hsyl.2.2 (Dvd.intro _ h)

theorem U4qExtLocalReduction.notMem_sup_bigB_right (R : U4qExtLocalReduction L1 L2 S f) {τ : G}
    (hτS : τ ∈ S) (hτL : τ ∉ L1) : τ ∉ L2 ⊔ bigB L1 L2 (S ⊓ L1) := by
  intro hτ
  have hsyl := isSylowTwoOf_sup_bigB_right_of_le R.hyp inf_le_right R.inf_left_le_right
  have hSP : S ≤ L2 ⊔ bigB L1 L2 (S ⊓ L1) := (R.le_inf_sup_zpowers hτS hτL).trans
    (sup_le (R.inf_left_le_right.trans le_sup_left) (Subgroup.zpowers_le.mpr hτ))
  have h := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : S ⊓ L1 ≤ S) hSP
  rw [R.relIndex_eq] at h
  exact hsyl.2.2 (Dvd.intro _ h)

omit [Finite G] in
private theorem le_pCoreOf_of_normal_u4Twist {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hcore : N.subgroupOf H ≤ CFSG.pCore p H :=
    le_sSup ⟨hN, hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

omit [Finite G] in
private theorem U4qExtLocalReduction.sup_bigB_le_u4Twist (R : U4qExtLocalReduction L1 L2 S f) :
    L1 ⊔ bigB L1 L2 (S ⊓ L1) ≤ L1 ⊔ S ⊔ borelOf L2 S := by
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  rw [bigB, R.borelOf_right]
  exact sup_le (sup_le ((borelOf_le L1 _).trans (le_sup_left.trans le_sup_left)) le_sup_right)
    (inf_le_left.trans (le_sup_right.trans le_sup_left))

theorem U4qExtLocalReduction.false_of_conj_eq_conj {Y : Type} [Group Y] {M1 M2 : Subgroup Y}
    (R : U4qExtLocalReduction L1 L2 S f) (hH : Hyp111 L1 L2 S)
    (Φ : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 (S ⊓ L1))
      (L2 ⊔ bigB L1 L2 (S ⊓ L1))).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    {τ : G} (hτS : τ ∈ S) (hτL : τ ∉ L1) {b₀ : Y} (hb₀ : b₀ ∈ M1 ⊓ M2)
    (h1 : ∀ x y : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
      Subtype.val (Φ.φ1 y) = b₀ * Subtype.val (Φ.φ1 x) * b₀⁻¹)
    (h2 : ∀ x y : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
      Subtype.val (Φ.φ2 y) = b₀ * Subtype.val (Φ.φ2 x) * b₀⁻¹) : False := by
  let φ₁ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)) ≃* ↥M1 := Φ.φ1
  let φ₂ : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)) ≃* ↥M2 := Φ.φ2
  have h1' : ∀ x y : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
      ((φ₁ y : ↥M1) : Y) = b₀ * ((φ₁ x : ↥M1) : Y) * b₀⁻¹ := h1
  have h2' : ∀ x y : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
      ((φ₂ y : ↥M2) : Y) = b₀ * ((φ₂ x : ↥M2) : Y) * b₀⁻¹ := h2
  have hφ : ((φ₁.symm ⟨b₀, hb₀.1⟩ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) : G) =
      ((φ₂.symm ⟨b₀, hb₀.2⟩ : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1))) : G) :=
    coe_ofSubgroupsIso_φ1_symm_eq_φ2_symm Φ (x := ⟨b₀, hb₀.1⟩) (y := ⟨b₀, hb₀.2⟩) rfl
  obtain ⟨β, hβ⟩ : ∃ β : G,
      β = ((φ₁.symm ⟨b₀, hb₀.1⟩ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) : G) := ⟨_, rfl⟩
  have hβ1 : β ∈ L1 ⊔ bigB L1 L2 (S ⊓ L1) := by
    rw [hβ]
    exact (φ₁.symm _).2
  have hβ2 : β ∈ L2 ⊔ bigB L1 L2 (S ⊓ L1) := by
    rw [hβ, hφ]
    exact (φ₂.symm _).2
  have hφβ1 : ((φ₁ ⟨β, hβ1⟩ : ↥M1) : Y) = b₀ := by
    rw [show (⟨β, hβ1⟩ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) = φ₁.symm ⟨b₀, hb₀.1⟩ from Subtype.ext hβ,
      MulEquiv.apply_symm_apply]
  have hφβ2 : ((φ₂ ⟨β, hβ2⟩ : ↥M2) : Y) = b₀ := by
    rw [show (⟨β, hβ2⟩ : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1))) = φ₂.symm ⟨b₀, hb₀.2⟩ from
      Subtype.ext (hβ.trans hφ), MulEquiv.apply_symm_apply]
  have hc1 : ∀ a ∈ L1 ⊔ bigB L1 L2 (S ⊓ L1), τ * a * τ⁻¹ = β * a * β⁻¹ := by
    intro a ha
    have hmem : τ * a * τ⁻¹ ∈ L1 ⊔ bigB L1 L2 (S ⊓ L1) :=
      (Subgroup.mem_normalizer_iff.mp (R.le_normalizer_sup_left hτS) a).mp ha
    have e1 := h1' ⟨a, ha⟩ ⟨τ * a * τ⁻¹, hmem⟩ rfl
    have e2 : ((φ₁ (⟨β, hβ1⟩ * ⟨a, ha⟩ * (⟨β, hβ1⟩ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)))⁻¹) :
        ↥M1) : Y) = b₀ * ((φ₁ ⟨a, ha⟩ : ↥M1) : Y) * b₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφβ1]
    exact congrArg Subtype.val (φ₁.injective (Subtype.ext (e1.trans e2.symm)))
  have hc2 : ∀ a ∈ L2 ⊔ bigB L1 L2 (S ⊓ L1), τ * a * τ⁻¹ = β * a * β⁻¹ := by
    intro a ha
    have hmem : τ * a * τ⁻¹ ∈ L2 ⊔ bigB L1 L2 (S ⊓ L1) :=
      (Subgroup.mem_normalizer_iff.mp (R.le_normalizer_sup_right hτS) a).mp ha
    have e1 := h2' ⟨a, ha⟩ ⟨τ * a * τ⁻¹, hmem⟩ rfl
    have e2 : ((φ₂ (⟨β, hβ2⟩ * ⟨a, ha⟩ * (⟨β, hβ2⟩ : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)))⁻¹) :
        ↥M2) : Y) = b₀ * ((φ₂ ⟨a, ha⟩ : ↥M2) : Y) * b₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφβ2]
    exact congrArg Subtype.val (φ₂.injective (Subtype.ext (e1.trans e2.symm)))
  have hP : ∀ a, τ * a * τ⁻¹ = β * a * β⁻¹ → a ∈ Subgroup.centralizer ({β⁻¹ * τ} : Set G) := by
    intro a hae
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (β⁻¹ * τ) = β⁻¹ * (β * a * β⁻¹) * τ := by group
      _ = β⁻¹ * (τ * a * τ⁻¹) * τ := by rw [← hae]
      _ = β⁻¹ * τ * a := by group
  have hτC : τ ∈ Subgroup.centralizer ({β⁻¹ * τ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hτβ : τ * β * τ⁻¹ = β := by rw [hc1 β hβ1]; group
    calc τ * (β⁻¹ * τ) = (τ * β * τ⁻¹)⁻¹ * τ * τ := by group
      _ = β⁻¹ * τ * τ := by rw [hτβ]
  have hXC : L1 ⊔ L2 ⊔ S ≤ Subgroup.centralizer ({β⁻¹ * τ} : Set G) := by
    refine sup_le (sup_le (fun a ha => hP a (hc1 a (Subgroup.mem_sup_left ha)))
      (fun a ha => hP a (hc2 a (Subgroup.mem_sup_left ha)))) ?_
    refine (R.le_inf_sup_zpowers hτS hτL).trans (sup_le ?_ (Subgroup.zpowers_le.mpr hτC))
    exact fun a ha => hP a (hc1 a (Subgroup.mem_sup_left ha.2))
  have hHX : L1 ⊔ S ⊔ borelOf L2 S ≤ L1 ⊔ L2 ⊔ S :=
    sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      ((borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))
  have htH : β⁻¹ * τ ∈ L1 ⊔ S ⊔ borelOf L2 S := mul_mem (inv_mem (R.sup_bigB_le_u4Twist hβ1))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hτS))
  have htX : β⁻¹ * τ ∈ L1 ⊔ L2 ⊔ S := hHX htH
  have hchar : (L1 ⊔ S ⊔ borelOf L2 S) ⊓
      Subgroup.centralizer (pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) : Set G) ≤
        pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) := hH.h1.charTwo
  have hcoreH : pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) ≤ L1 ⊔ S ⊔ borelOf L2 S :=
    Subgroup.map_subtype_le _
  have htcore : β⁻¹ * τ ∈ pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) :=
    hchar (Subgroup.mem_inf.mpr ⟨htH, Subgroup.mem_centralizer_iff.mpr fun _ hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXC (hHX (hcoreH hh)))⟩)
  have hp : IsPGroup 2 (pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(L1 ⊔ S ⊔ borelOf L2 S))).map
      (L1 ⊔ S ⊔ borelOf L2 S).subtype
  have hpt : IsPGroup 2 (Subgroup.zpowers (β⁻¹ * τ)) := hp.to_le (Subgroup.zpowers_le.mpr htcore)
  have hNX : Subgroup.zpowers (β⁻¹ * τ) ≤ L1 ⊔ L2 ⊔ S := Subgroup.zpowers_le.mpr htX
  have hnorm : ((Subgroup.zpowers (β⁻¹ * τ)).subgroupOf (L1 ⊔ L2 ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    refine Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun _ hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXC hh)
  have ht1 : β⁻¹ * τ ∈ (⊥ : Subgroup G) := by
    rw [← hH.o2]
    exact le_pCoreOf_of_normal_u4Twist hNX hnorm hpt (Subgroup.mem_zpowers _)
  have hτβ : τ = β := by
    rw [Subgroup.mem_bot, inv_mul_eq_one] at ht1
    exact ht1.symm
  rw [← hτβ] at hβ1
  exact R.notMem_sup_bigB_left hτS hτL hβ1

theorem fieldAut_eq_u4FieldInvol {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    {ρ : K ≃+* K} (hρ : ∀ x, ρ x = h.bar x) : fieldAut h ρ = u4FieldInvol h := by
  obtain rfl : ρ = h.barEquiv := RingEquiv.ext fun x => (hρ x).trans (h.barEquiv_apply x).symm
  rfl

end CFSG.Quasithin.F112R.St84

end
