module

public import CFSG.RankThree.GF2n.Tim78S48PhaseCore
public import CFSG.RankThree.GF2n.Tim78S48PhaseGen
public import CFSG.RankThree.GF2n.Tim78S48PairBasic
import CFSG.RankThree.GF2n.Tim77Prop24TwoL2
import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.RankThree.GF2n.NaturalDecomp
import CFSG.RankThree.GF2n.Tim78S45Aux
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.RankThree.GF2n.Tim78S47
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

section Acting

variable {Γ W : Type} [Group Γ] [CommGroup W]

def distribActionOfMulAut (ρ : Γ →* MulAut W) : DistribMulAction Γ (Additive W) where
  smul γ v := Additive.ofMul (ρ γ (Additive.toMul v))
  one_smul v := by
    show Additive.ofMul (ρ 1 (Additive.toMul v)) = v
    rw [map_one, MulAut.one_apply, ofMul_toMul]
  mul_smul γ δ v := by
    show Additive.ofMul (ρ (γ * δ) (Additive.toMul v)) =
      Additive.ofMul (ρ γ (Additive.toMul (Additive.ofMul (ρ δ (Additive.toMul v)))))
    rw [map_mul, MulAut.mul_apply, toMul_ofMul]
  smul_zero γ := by
    show Additive.ofMul (ρ γ (Additive.toMul 0)) = 0
    rw [toMul_zero, map_one, ofMul_one]
  smul_add γ v w := by
    show Additive.ofMul (ρ γ (Additive.toMul (v + w))) =
      Additive.ofMul (ρ γ (Additive.toMul v)) + Additive.ofMul (ρ γ (Additive.toMul w))
    rw [toMul_add, map_mul, ofMul_mul]

end Acting

structure L2Coords (B T : Subgroup G) (g : G) (F : Type) [Field F] where
  ε : ↥(T ⊔ conjSubgroup g T) →* SL(2, F)
  surj : Function.Surjective ε
  ker : ε.ker = (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)
  up : (T.subgroupOf (T ⊔ conjSubgroup g T)).map ε = utri F
  low : ((conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T)).map ε = ltri F

namespace L2Coords

variable {B T : Subgroup G} {g : G} {F : Type} [Field F] (D : L2Coords B T g F)

theorem ker_iff (x : ↥(T ⊔ conjSubgroup g T)) :
    D.ε x = 1 ↔ (x : G) ∈ kernel48 B T g := by
  rw [← MonoidHom.mem_ker, D.ker, Subgroup.mem_subgroupOf]

theorem exists_utri {t : G} (ht : t ∈ T) :
    ∃ s : F, D.ε ⟨t, Subgroup.mem_sup_left ht⟩ = utriElt s := by
  have : D.ε ⟨t, Subgroup.mem_sup_left ht⟩ ∈ utri F := by
    rw [← D.up]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨s, hs⟩ := mem_utri_iff.mp this
  exact ⟨s, hs⟩

theorem exists_ltri {t : G} (ht : t ∈ conjSubgroup g T) :
    ∃ s : F, D.ε ⟨t, Subgroup.mem_sup_right ht⟩ = ltriElt s := by
  have : D.ε ⟨t, Subgroup.mem_sup_right ht⟩ ∈ ltri F := by
    rw [← D.low]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  exact ⟨_, eq_ltriElt_of_mem_ltri this⟩

theorem exists_T (s : F) :
    ∃ t : G, ∃ ht : t ∈ T, D.ε ⟨t, Subgroup.mem_sup_left ht⟩ = utriElt s := by
  have : utriElt s ∈ (T.subgroupOf (T ⊔ conjSubgroup g T)).map D.ε := by
    rw [D.up]; exact utriElt_mem_utri s
  obtain ⟨y, hy, hys⟩ := this
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hys⟩

theorem exists_Tg (s : F) :
    ∃ t : G, ∃ ht : t ∈ conjSubgroup g T,
      D.ε ⟨t, Subgroup.mem_sup_right ht⟩ = ltriElt s := by
  have : ltriElt s ∈ ((conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T)).map D.ε := by
    rw [D.low]; exact ltriElt_mem_ltri s
  obtain ⟨y, hy, hys⟩ := this
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hys⟩

end L2Coords

open Matrix in
@[expose] def HasNatCoords {B T : Subgroup G} {g : G} {F : Type} [Field F]
    (D : L2Coords B T g F) : Prop :=
  ∃ Θ : (Fin 2 → F) → G, (∀ v, Θ v ∈ B ⊔ conjSubgroup g B) ∧
    (∀ v v', Θ (v + v') = Θ v * Θ v') ∧ Function.Injective Θ ∧
    (∀ w ∈ B ⊔ conjSubgroup g B, ∃ v, Θ v = w) ∧
    ∀ (x : ↥(T ⊔ conjSubgroup g T)) (v : Fin 2 → F),
      (x : G) * Θ v * (x : G)⁻¹ = Θ ((D.ε x : Matrix (Fin 2) (Fin 2) F) *ᵥ v)

structure IsTorusLift {B T : Subgroup G} {g : G} {F : Type} [Field F] (D : L2Coords B T g F)
    (K₁ : Subgroup G) : Prop where
  le_X : K₁ ≤ T ⊔ conjSubgroup g T
  cyclic : IsCyclic K₁
  card : Nat.card K₁ = Nat.card F - 1
  inf_ker : K₁ ⊓ kernel48 B T g = ⊥
  eps_mem : ∀ x : ↥(T ⊔ conjSubgroup g T), (x : G) ∈ K₁ → D.ε x ∈ torus F
  eps_surj : ∀ a : Fˣ, ∃ x : ↥(T ⊔ conjSubgroup g T), (x : G) ∈ K₁ ∧ D.ε x = torusElt a

theorem exists_torusLift [Finite G] {f : ℕ} (hf : f ≠ 0) {B T : Subgroup G} {g : G}
    (D : L2Coords B T g (GaloisField 2 f)) (hKp : IsPGroup 2 (kernel48 B T g)) :
    ∃ K₁ : Subgroup G, IsTorusLift D K₁ := by
  have hker : IsPGroup 2 D.ε.ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hKp
    refine IsPGroup.of_card (n := n) ?_
    rw [D.ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      kernel48 B T g ≤ T ⊔ conjSubgroup g T)).toEquiv, hn]
  obtain ⟨K₁', hcyc, hcard, hmap, hinf⟩ := exists_sl2_torus_lift hf D.ε D.surj hker
  refine ⟨K₁'.map (T ⊔ conjSubgroup g T).subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact isCyclic_of_surjective
      (K₁'.equivMapOfInjective _ (Subgroup.subtype_injective _)).toMonoidHom
      (K₁'.equivMapOfInjective _ (Subgroup.subtype_injective _)).surjective
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard,
      GaloisField.card 2 f hf]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hker'⟩
    have h1 : y ∈ D.ε.ker := by
      rw [D.ker, Subgroup.mem_subgroupOf]; exact hker'
    have h2 : y ∈ K₁' ⊓ D.ε.ker := ⟨hy, h1⟩
    rw [hinf, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot, h2]
    rfl
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    have : D.ε y ∈ K₁'.map D.ε := Subgroup.mem_map_of_mem _ hy
    rwa [hmap] at this
  · intro a
    have : torusElt a ∈ K₁'.map D.ε := by rw [hmap]; exact torusElt_mem_torus a
    obtain ⟨y, hy, hya⟩ := this
    exact ⟨y, ⟨y, hy, rfl⟩, hya⟩

section TorusConj

variable {F : Type} [Field F]

theorem torusElt_inv' (a : Fˣ) : (torusElt a⁻¹ : SL(2, F)) = (torusElt a)⁻¹ :=
  map_inv (CFSG.Glauberman.Dickson.splitTorusSLHom F) a

theorem inv_mul_utri_mul_mem {τ u : SL(2, F)} (hτ : τ ∈ torus F) (hu : u ∈ utri F) :
    τ⁻¹ * u * τ ∈ utri F := by
  obtain ⟨a, rfl⟩ := mem_torus_iff.mp hτ
  obtain ⟨s, rfl⟩ := mem_utri_iff.mp hu
  have e : (torusElt a)⁻¹ * utriElt s * torusElt a =
      utriElt (((a⁻¹ : Fˣ) : F) ^ 2 * s) := by
    rw [← torusElt_mul_utriElt_mul_inv a⁻¹ s, torusElt_inv', inv_inv]
  rw [e]
  exact utriElt_mem_utri _

theorem inv_mul_ltri_mul_mem {τ u : SL(2, F)} (hτ : τ ∈ torus F) (hu : u ∈ ltri F) :
    τ⁻¹ * u * τ ∈ ltri F := by
  obtain ⟨a, rfl⟩ := mem_torus_iff.mp hτ
  obtain ⟨s, rfl⟩ := mem_ltri_iff.mp hu
  have e : (torusElt a)⁻¹ * ltriElt s * torusElt a =
      ltriElt ((((a⁻¹ : Fˣ) : F) ^ 2)⁻¹ * s) := by
    rw [← torusElt_mul_ltriElt_mul_inv a⁻¹ s, torusElt_inv', inv_inv]
  rw [e]
  exact ltriElt_mem_ltri _

end TorusConj

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

theorem W_cent_T (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) :
    ∀ w ∈ B ⊔ conjSubgroup g B, (∀ t ∈ T, t * w = w * t) → w ∈ B := by
  obtain ⟨t, htT, htK⟩ := hTK
  have hnc : ¬ ∀ b ∈ conjSubgroup g B, t * b = b * t := fun h =>
    htK ((H.T_mem_kernel_iff h48 htT (Subgroup.mem_sup_left htT)).mpr h)
  exact fun w hw hc => H.T_side h48 hP htT hnc w hw (hc t htT)

theorem W_cent_Tg (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g) :
    ∀ w ∈ B ⊔ conjSubgroup g B, (∀ t ∈ conjSubgroup g T, t * w = w * t) →
      w ∈ conjSubgroup g B := by
  obtain ⟨t, htT, htK⟩ := hTgK
  have hnc : ¬ ∀ b ∈ B, t * b = b * t := fun h =>
    htK ((H.Tg_mem_kernel_iff h48 htT (Subgroup.mem_sup_right htT)).mpr h)
  exact fun w hw hc => H.Tg_side h48 hP htT hnc w hw (hc t htT)

theorem comm_T_W_mem_B (h48 : Hyp48 M B T g) {t : G} (ht : t ∈ T) {w : G}
    (hw : w ∈ B ⊔ conjSubgroup g B) : t * w * t⁻¹ * w⁻¹ ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
  have h1 := h48.comm_T b hb t ht
  have hB : t * a * t⁻¹ = a := by
    rw [H.T_comm_B ht ha]; group
  have e : t * (a * b) * t⁻¹ * (a * b)⁻¹ = a * (t * b * t⁻¹ * b⁻¹) * a⁻¹ := by
    calc t * (a * b) * t⁻¹ * (a * b)⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹ * b⁻¹) * a⁻¹ := by group
      _ = a * (t * b * t⁻¹ * b⁻¹) * a⁻¹ := by rw [hB]
  rw [e]
  have h2 : t * b * t⁻¹ * b⁻¹ ∈ B := by
    have := B.inv_mem h1
    simpa [commutatorElement_def, mul_assoc] using this
  exact (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (H.B_le_M ha)) _).mp h2 |> fun h => by
    simpa using h

theorem commute_of_mem_utri {F : Type} [Field F] (D : L2Coords B T g F)
    {y : ↥(T ⊔ conjSubgroup g T)} (hy : D.ε y ∈ utri F) {b : G} (hb : b ∈ B) :
    (y : G) * b = b * (y : G) := by
  have hmem : D.ε y ∈ (T.subgroupOf (T ⊔ conjSubgroup g T)).map D.ε := by rw [D.up]; exact hy
  obtain ⟨y', hy', hyy'⟩ := hmem
  have hκ : D.ε (y'⁻¹ * y) = 1 := by rw [map_mul, map_inv, hyy', inv_mul_cancel]
  have hκK : ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) ∈ kernel48 B T g := (D.ker_iff _).mp hκ
  have hc1 := Subgroup.mem_centralizer_iff.mp hκK.2 b (Subgroup.mem_sup_left hb)
  have hc2 := H.T_comm_B (Subgroup.mem_subgroupOf.mp hy') hb
  have hyeq : (y : G) = (y' : G) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by simp
  rw [hyeq]
  calc (y' : G) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) * b
      = y' * (((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) * b) := by rw [mul_assoc]
    _ = y' * (b * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G)) := by rw [hc1]
    _ = (y' * b) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by rw [mul_assoc]
    _ = (b * y') * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by rw [hc2]
    _ = b * (y' * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G)) := by rw [mul_assoc]

theorem commute_of_mem_ltri {F : Type} [Field F] (D : L2Coords B T g F)
    {y : ↥(T ⊔ conjSubgroup g T)} (hy : D.ε y ∈ ltri F) {b : G} (hb : b ∈ conjSubgroup g B) :
    (y : G) * b = b * (y : G) := by
  have hmem : D.ε y ∈ ((conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T)).map D.ε := by
    rw [D.low]; exact hy
  obtain ⟨y', hy', hyy'⟩ := hmem
  have hκ : D.ε (y'⁻¹ * y) = 1 := by rw [map_mul, map_inv, hyy', inv_mul_cancel]
  have hκK : ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) ∈ kernel48 B T g := (D.ker_iff _).mp hκ
  have hc1 := Subgroup.mem_centralizer_iff.mp hκK.2 b (Subgroup.mem_sup_right hb)
  have hc2 := H.Tg_comm_Bg (Subgroup.mem_subgroupOf.mp hy') hb
  have hyeq : (y : G) = (y' : G) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by simp
  rw [hyeq]
  calc (y' : G) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) * b
      = y' * (((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) * b) := by rw [mul_assoc]
    _ = y' * (b * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G)) := by rw [hc1]
    _ = (y' * b) * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by rw [mul_assoc]
    _ = (b * y') * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G) := by rw [hc2]
    _ = b * (y' * ((y'⁻¹ * y : ↥(T ⊔ conjSubgroup g T)) : G)) := by rw [mul_assoc]

local notation "XX" => (T ⊔ conjSubgroup g T : Subgroup G)
local notation "WW" => (B ⊔ conjSubgroup g B : Subgroup G)

theorem torus_normalizes (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    {F : Type} [Field F] (D : L2Coords B T g F) {x : ↥XX} (hx : D.ε x ∈ torus F) :
    (x : G) ∈ Subgroup.normalizer (B : Set G) ∧
      (x : G) ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
  have hXW : XX ≤ Subgroup.normalizer (WW : Set G) := H.X_le_normalizer_W h48
  constructor
  · refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have hyW : (x : G) * b * (x : G)⁻¹ ∈ WW :=
      (Subgroup.mem_normalizer_iff.mp (hXW x.2) b).mp (Subgroup.mem_sup_left hb)
    refine H.W_cent_T h48 hP hTK _ hyW fun t ht => ?_
    set t₁ : ↥XX := x⁻¹ * ⟨t, Subgroup.mem_sup_left ht⟩ * x with ht₁
    have hε : D.ε t₁ ∈ utri F := by
      obtain ⟨s, hs⟩ := D.exists_utri ht
      rw [ht₁, map_mul, map_mul, map_inv, hs]
      exact inv_mul_utri_mul_mem hx (utriElt_mem_utri s)
    have hc := H.commute_of_mem_utri D hε hb
    have hc' : ((x : G)⁻¹ * t * x) * b = b * ((x : G)⁻¹ * t * x) := by simpa [ht₁] using hc
    calc t * ((x : G) * b * (x : G)⁻¹) = (x : G) * (((x : G)⁻¹ * t * x) * b) * (x : G)⁻¹ := by
          group
      _ = (x : G) * (b * ((x : G)⁻¹ * t * x)) * (x : G)⁻¹ := by rw [hc']
      _ = ((x : G) * b * (x : G)⁻¹) * t := by group
  · refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have hyW : (x : G) * b * (x : G)⁻¹ ∈ WW :=
      (Subgroup.mem_normalizer_iff.mp (hXW x.2) b).mp (Subgroup.mem_sup_right hb)
    refine H.W_cent_Tg h48 hP hTgK _ hyW fun t ht => ?_
    set t₁ : ↥XX := x⁻¹ * ⟨t, Subgroup.mem_sup_right ht⟩ * x with ht₁
    have hε : D.ε t₁ ∈ ltri F := by
      obtain ⟨s, hs⟩ := D.exists_ltri ht
      rw [ht₁, map_mul, map_mul, map_inv, hs]
      exact inv_mul_ltri_mul_mem hx (ltriElt_mem_ltri s)
    have hc := H.commute_of_mem_ltri D hε hb
    have hc' : ((x : G)⁻¹ * t * x) * b = b * ((x : G)⁻¹ * t * x) := by simpa [ht₁] using hc
    calc t * ((x : G) * b * (x : G)⁻¹) = (x : G) * (((x : G)⁻¹ * t * x) * b) * (x : G)⁻¹ := by
          group
      _ = (x : G) * (b * ((x : G)⁻¹ * t * x)) * (x : G)⁻¹ := by rw [hc']
      _ = ((x : G) * b * (x : G)⁻¹) * t := by group

open Matrix in
theorem exists_natural_W (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    (hconj : ∃ x ∈ XX, conjSubgroup g B = conjSubgroup x B)
    {F : Type} [Field F] [Finite F] [CharP F 2] (D : L2Coords B T g F) :
    ∃ m : ℕ, Nat.card B = Nat.card F ^ m ∧ (m = 1 → HasNatCoords D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXW : XX ≤ Subgroup.normalizer (WW : Set G) := H.X_le_normalizer_W h48
  have hWe : Assembly.IsElemAbelian 2 WW := H.W_elem h48
  haveI : IsMulCommutative ↥WW := hWe.1
  letI : CommGroup ↥WW := IsMulCommutative.instCommGroup
  let ε := D.ε
  let φ₀ : ↥XX →* MulAut ↥WW := (Subgroup.normalizerMonoidHom WW).comp (Subgroup.inclusion hXW)
  have hφ₀ : ∀ (x : ↥XX) (w : ↥WW), ((φ₀ x w : ↥WW) : G) = (x : G) * w * (x : G)⁻¹ :=
    fun _ _ => rfl
  have hkerφ : ε.ker ≤ φ₀.ker := by
    intro x hx
    rw [D.ker, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    ext w
    rw [hφ₀, MulAut.one_apply, (Subgroup.mem_centralizer_iff.mp hx.2 w w.2).symm,
      mul_inv_cancel_right]
  let ρ : SL(2, F) →* MulAut ↥WW := ε.liftOfSurjective D.surj ⟨φ₀, hkerφ⟩
  have hρ : ∀ x : ↥XX, ρ (ε x) = φ₀ x := fun x =>
    ε.liftOfRightInverse_comp_apply (Function.surjInv D.surj)
      (Function.rightInverse_surjInv D.surj) ⟨φ₀, hkerφ⟩ x
  letI : DistribMulAction SL(2, F) (Additive ↥WW) := distribActionOfMulAut ρ
  have hsmul : ∀ (x : ↥XX) (v : Additive ↥WW),
      ((((ε x) • v).toMul : ↥WW) : G) = (x : G) * (v.toMul : G) * (x : G)⁻¹ := fun x v => by
    show ((ρ (ε x) v.toMul : ↥WW) : G) = _
    rw [hρ]; rfl
  have hTX : ∀ t ∈ T, t ∈ XX := fun t ht => Subgroup.mem_sup_left ht
  have hTgX : ∀ t ∈ conjSubgroup g T, t ∈ XX := fun t ht => Subgroup.mem_sup_right ht
  have hupper : ∀ a ∈ upperUnipotent F, ∃ t : G, ∃ ht : t ∈ T, ε ⟨t, hTX t ht⟩ = a := by
    intro a ha
    rw [← Tim77.utri_eq_upperUnipotent, ← D.up] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hfix : ∀ v : Additive ↥WW, (∀ y : SL(2, F), y • v = v) → v = 0 := by
    intro v hv
    have hc : ∀ x : ↥XX, (x : G) * (v.toMul : G) = (v.toMul : G) * x := by
      intro x
      have h := congrArg (fun u : Additive ↥WW => ((u.toMul : ↥WW) : G)) (hv (ε x))
      simp only [hsmul] at h
      calc (x : G) * (v.toMul : G) = ((x : G) * (v.toMul : G) * (x : G)⁻¹) * (x : G) := by group
        _ = (v.toMul : G) * (x : G) := by rw [h]
    have h1 : (v.toMul : G) ∈ B :=
      H.W_cent_T h48 hP hTK _ v.toMul.2 fun t ht => hc ⟨t, hTX t ht⟩
    have h2 : (v.toMul : G) ∈ conjSubgroup g B :=
      H.W_cent_Tg h48 hP hTgK _ v.toMul.2 fun t ht => hc ⟨t, hTgX t ht⟩
    have h3 : (v.toMul : G) ∈ B ⊓ conjSubgroup g B := ⟨h1, h2⟩
    rw [H.B_inf_Bg hP, Subgroup.mem_bot] at h3
    exact Additive.toMul.injective (Subtype.ext h3)
  have hquad : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ v : Additive ↥WW,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨t, ht, rfl⟩ := hupper a ha
    obtain ⟨t', ht', rfl⟩ := hupper a' ha'
    apply Additive.toMul.injective
    apply Subtype.ext
    have e1 : ((((ε ⟨t, hTX t ht⟩) • v - v).toMul : ↥WW) : G) =
        t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, hsmul, div_eq_mul_inv]
    have hu : t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹ ∈ B := H.comm_T_W_mem_B h48 ht v.toMul.2
    rw [hsmul ⟨t', hTX t' ht'⟩, e1]
    have := H.T_comm_B ht' hu
    calc t' * (t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹) * t'⁻¹
        = (t' * (t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹)) * t'⁻¹ := by rw [mul_assoc]
      _ = ((t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹) * t') * t'⁻¹ := by rw [this]
      _ = t * v.toMul * t⁻¹ * (v.toMul : G)⁻¹ := by group
  set L : AddSubgroup (Additive ↥WW) := Subgroup.toAddSubgroup (B.subgroupOf WW) with hL
  have hLmem : ∀ w : Additive ↥WW, w ∈ L ↔ (w.toMul : G) ∈ B := fun w => Iff.rfl
  have hLw : ∀ w ∈ L, ∀ a ∈ upperUnipotent F, a • w = w := by
    intro w hw a ha
    obtain ⟨t, ht, rfl⟩ := hupper a ha
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hsmul]
    have := H.T_comm_B ht ((hLmem w).mp hw)
    calc t * (w.toMul : G) * t⁻¹ = ((w.toMul : G) * t) * t⁻¹ := by rw [this]
      _ = w.toMul := by group
  have hgen : ∀ U : AddSubgroup (Additive ↥WW), (∀ y : SL(2, F), ∀ v ∈ U, y • v ∈ U) →
      L ≤ U → U = ⊤ := by
    intro U hU hLU
    have hB : ∀ b : G, ∀ hb : b ∈ B,
        Additive.ofMul (⟨b, Subgroup.mem_sup_left hb⟩ : ↥WW) ∈ U := fun b hb =>
      hLU ((hLmem _).mpr hb)
    have hBg : ∀ b' : G, ∀ hb' : b' ∈ conjSubgroup g B,
        Additive.ofMul (⟨b', Subgroup.mem_sup_right hb'⟩ : ↥WW) ∈ U := by
      intro b' hb'
      obtain ⟨x, hxX, hx⟩ := hconj
      have hb'' : b' ∈ conjSubgroup x B := hx ▸ hb'
      have hxb : x⁻¹ * b' * x ∈ B := mem_conjSubgroup.mp hb''
      have h1 := hU (ε ⟨x, hxX⟩) _ (hB _ hxb)
      have h2 : (ε ⟨x, hxX⟩) • Additive.ofMul (⟨x⁻¹ * b' * x, Subgroup.mem_sup_left hxb⟩ : ↥WW) =
          Additive.ofMul (⟨b', Subgroup.mem_sup_right hb'⟩ : ↥WW) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hsmul]
        simp only [toMul_ofMul]
        group
      rwa [h2] at h1
    rw [eq_top_iff]
    intro v _
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup (le_normalizer_of_comm fun x hx y hy =>
      (H.commute_of_conj_le_M h48.leM y hy x hx).symm) v.toMul.2
    have hv : v = Additive.ofMul (⟨a, Subgroup.mem_sup_left ha⟩ : ↥WW) +
        Additive.ofMul (⟨b, Subgroup.mem_sup_right hb⟩ : ↥WW) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa using hab
    rw [hv]
    exact U.add_mem (hB a ha) (hBg b hb)
  obtain ⟨m, hm, hm1⟩ := natural_module_decomp hfix hquad hLw hgen
  have hcardV : Nat.card (Additive ↥WW) = Nat.card B ^ 2 := by
    rw [show Nat.card (Additive ↥WW) = Nat.card ↥WW from Nat.card_congr Additive.toMul]
    exact H.card_W h48 hP
  refine ⟨m, ?_, fun hm1' => ?_⟩
  · have h2 : Nat.card B ^ 2 = (Nat.card F ^ m) ^ 2 := by
      rw [← hcardV, hm, ← pow_mul, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective (by norm_num) h2
  · obtain ⟨θ, hθbij, hθ⟩ := hm1 hm1'
    refine ⟨fun v => (((θ v).toMul : ↥WW) : G), fun v => (θ v).toMul.2, ?_, ?_, ?_, ?_⟩
    · intro v v'
      simp [map_add, toMul_add]
    · intro v v' h
      exact hθbij.1 (Additive.toMul.injective (Subtype.ext h))
    · intro w hw
      obtain ⟨v, hv⟩ := hθbij.2 (Additive.ofMul (⟨w, hw⟩ : ↥WW))
      exact ⟨v, by simpa using congrArg (fun u : Additive ↥WW => ((u.toMul : ↥WW) : G)) hv⟩
    · intro x v
      show (x : G) * (((θ v).toMul : ↥WW) : G) * (x : G)⁻¹ = (((θ _).toMul : ↥WW) : G)
      rw [hθ, hsmul]

end Hyp4

end CFSG.RankThree.GF2n.Tim78
