module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesPrimeField
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.QuotMod
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private noncomputable def secConjAut {K W : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G)) :
    MulAut (↥K ⧸ W.subgroupOf K) :=
  CFSG.Quasithin.H.SecQ.conjW huK huW

private theorem secConjAut_mk {K W : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G)) (n : ↥K) :
    secConjAut huK huW (QuotientGroup.mk n) =
      QuotientGroup.mk ⟨u * n * u⁻¹,
        (Subgroup.mem_normalizer_iff.mp huK (n : G)).1 n.2⟩ := by
  rw [secConjAut, CFSG.Quasithin.H.SecQ.conjW_mk]
  congr 1

private theorem secConjAdd_mk {K W H : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (hs : QuotMod.Hyp H K W) (n : ↥K) :
    MulEquiv.toAdditive (secConjAut huK huW) (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * n * u⁻¹,
        (Subgroup.mem_normalizer_iff.mp huK (n : G)).1 n.2⟩ := by
  change Additive.ofMul (secConjAut huK huW (QuotientGroup.mk n)) =
    Additive.ofMul (QuotientGroup.mk ⟨u * n * u⁻¹,
      (Subgroup.mem_normalizer_iff.mp huK (n : G)).1 n.2⟩)
  rw [secConjAut_mk]

private theorem secConjAdd_sq {K W H : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (hs : QuotMod.Hyp H K W) (hu2 : u * u ∈ K) (n : ↥K) :
    MulEquiv.toAdditive (secConjAut huK huW)
      (MulEquiv.toAdditive (secConjAut huK huW) (SecMod.mk hs n)) = SecMod.mk hs n := by
  rw [secConjAdd_mk]
  change MulEquiv.toAdditive (secConjAut huK huW)
    (SecMod.mk hs ⟨u * (n : G) * u⁻¹,
      (Subgroup.mem_normalizer_iff.mp huK (n : G)).1 n.2⟩) = SecMod.mk hs n
  rw [secConjAdd_mk]
  refine (QuotMod.mk_eq_mk_iff (N := K) (N₀ := W) _ _).2 ?_
  change (u * (u * (n : G) * u⁻¹) * u⁻¹)⁻¹ * (n : G) ∈ W
  have h := hs.comm (u * u) hu2 (n : G)⁻¹ (K.inv_mem n.2)
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

private theorem secConjAdd_comm_repSec {K W H : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (hs : QuotMod.Hyp H K W)
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ K, k * n * k⁻¹ * n⁻¹ ∈ W)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (huKcomm : ∀ x ∈ H, ⁅u, x⁆ ∈ K)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (z : ↥H) (n : ↥K) :
    MulEquiv.toAdditive (secConjAut huK huW)
      (repSec hs hKsec SL(2, F) ψ (ψ (piK V H z)) (SecMod.mk hs n)) =
    repSec hs hKsec SL(2, F) ψ (ψ (piK V H z))
      (MulEquiv.toAdditive (secConjAut huK huW) (SecMod.mk hs n)) := by
  rw [repSec_apply_piK_mk, secConjAdd_mk, secConjAdd_mk, repSec_apply_piK_mk]
  apply_fun Additive.toMul
  simp only [SecMod.mk, QuotMod.mk, toMul_ofMul]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  have hcK : ⁅u, (z : G)⁆ ∈ K := huKcomm (z : G) z.2
  have huK' : u * n * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp huK (n : G)).1 n.2
  have hbK : (z : G) *
      (((K.normalizerMonoidHom ⟨u, huK⟩) n : ↥K) : G) * (z : G)⁻¹ ∈ K := by
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe] using
      (Subgroup.mem_normalizer_iff.mp (hHK z.2) (u * n * u⁻¹)).1 huK'
  have hmem : ⁅⁅u, (z : G)⁆, ((z : G) *
      (((K.normalizerMonoidHom ⟨u, huK⟩) n : ↥K) : G) * (z : G)⁻¹)⁆ ∈ ⁅K, K⁆ :=
    Subgroup.commutator_mem_commutator hcK hbK
  have hKK : ⁅K, K⁆ ≤ W :=
    Subgroup.commutator_le.mpr (fun x hx y hy => hs.comm x hx y hy)
  convert hKK hmem using 1
  simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
    div_eq_mul_inv, commutatorElement_def, Subgroup.normalizerMonoidHom_apply_apply_coe]
  group

private noncomputable def secFinOneEquiv (F : Type) [Field F] :
    (Fin 1 → Fin 2 → F) ≃+ (Fin 2 → F) :=
  { toFun := fun v => v 0
    invFun := fun w _ => w
    left_inv := by intro v; funext i; fin_cases i; rfl
    right_inv := by intro w; rfl
    map_add' := by intro v w; rfl }

private noncomputable def moduleT {K W : Subgroup G} {u : G}
    [(W.subgroupOf K).Normal]
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G)) :
    Additive (↥K ⧸ W.subgroupOf K) ≃+ Additive (↥K ⧸ W.subgroupOf K) :=
  MulEquiv.toAdditive (secConjAut huK huW)

private noncomputable def moduleF {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (T : X ≃+ X) : Y ≃+ Y :=
  (e.symm.trans T).trans e

private theorem module_k_eq_one {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {k : ℕ} (φ : SecMod hs ≃+ (Fin k → Fin 2 → F))
    (hKWcard : Nat.card (SecMod hs) = Nat.card V ^ 4)
    (hFcard : Nat.card F = Nat.card V ^ 2)
    (hq1 : 1 < Nat.card V) : k = 1 := by
  have hcardφ : Nat.card (SecMod hs) = Nat.card (Fin k → Fin 2 → F) :=
    Nat.card_congr φ.toEquiv
  have hcardR : Nat.card (Fin k → Fin 2 → F) = Nat.card F ^ (2 * k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    simp [Fintype.card_fin, pow_mul, mul_comm]
    ring
  have h1 : Nat.card V ^ 4 = Nat.card V ^ (4 * k) := by
    rw [← hKWcard, hcardφ, hcardR, hFcard, ← pow_mul]
    congr 1
    ring
  have := Nat.pow_right_injective hq1 h1
  omega

private theorem module_e_intertwines {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ K, k * n * k⁻¹ * n⁻¹ ∈ W)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V H ≃* SL(2, F)}
    (φ : SecMod hs ≃+ (Fin 1 → Fin 2 → F))
    (hφ : ∀ (g : SL(2, F)) (w : SecMod hs) (i : Fin 1),
      φ ((repSec hs hKsec SL(2, F) ψ g).toFun w) i =
        (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w i)) :
    ∀ (g : SL(2, F)) (w : SecMod hs),
      (φ.trans (secFinOneEquiv F)) ((repSec hs hKsec SL(2, F) ψ g).toFun w) =
        natEndHom F g ((φ.trans (secFinOneEquiv F)) w) := by
  intro g w
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  change (secFinOneEquiv F) (φ ((repSec hs hKsec SL(2, F) ψ g).toFun
    (SecMod.mk hs n))) = natEndHom F g ((secFinOneEquiv F) (φ (SecMod.mk hs n)))
  have hvec : φ ((repSec hs hKsec SL(2, F) ψ g).toFun (SecMod.mk hs n)) =
      fun i => (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ (SecMod.mk hs n) i) := by
    funext i
    exact hφ g (SecMod.mk hs n) i
  rw [hvec]
  rfl

private theorem module_T_comm {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ K, k * n * k⁻¹ * n⁻¹ ∈ W)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (huKcomm : ∀ x ∈ H, ⁅u, x⁆ ∈ K)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (g : SL(2, F)) (w : SecMod hs) :
    moduleT huK huW ((repSec hs hKsec SL(2, F) ψ g).toFun w) =
      (repSec hs hKsec SL(2, F) ψ g).toFun (moduleT huK huW w) := by
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  obtain ⟨z, rfl⟩ := ψ.surjective g
  obtain ⟨z', rfl⟩ := piK_surjective V H z
  change moduleT huK huW
      (((repSec hs hKsec SL(2, F) ψ) (ψ (piK V H z'))) (SecMod.mk hs n)) =
    ((repSec hs hKsec SL(2, F) ψ) (ψ (piK V H z')))
      (moduleT huK huW (SecMod.mk hs n))
  simpa only [moduleT] using
    secConjAdd_comm_repSec hs hKsec hHK huK huW huKcomm ψ z' n

private theorem module_T_sq {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G)) (hu2 : u * u ∈ K) (w : SecMod hs) :
    moduleT huK huW (moduleT huK huW w) = w := by
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  exact secConjAdd_sq huK huW hs hu2 n


private theorem module_scalar {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ K, k * n * k⁻¹ * n⁻¹ ∈ W)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (huKcomm : ∀ x ∈ H, ⁅u, x⁆ ∈ K)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V H ≃* SL(2, F)}
    (φ : SecMod hs ≃+ (Fin 1 → Fin 2 → F))
    (hφ : ∀ (g : SL(2, F)) (w : SecMod hs) (i : Fin 1),
      φ ((repSec hs hKsec SL(2, F) ψ g).toFun w) i =
        (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w i)) :
    ∃ c : F,
      (moduleF (φ.trans (secFinOneEquiv F)) (moduleT huK huW)).toAddMonoidHom = scalEnd c := by
  let e := φ.trans (secFinOneEquiv F)
  let T := moduleT huK huW
  let f := moduleF e T
  have hact : ∀ (g : SL(2, F)) (w : SecMod hs),
      e ((repSec hs hKsec SL(2, F) ψ g).toFun w) = natEndHom F g (e w) :=
    module_e_intertwines hs hKsec φ hφ
  have hT_comm : ∀ (g : SL(2, F)) (w : SecMod hs),
      T ((repSec hs hKsec SL(2, F) ψ g).toFun w) =
        (repSec hs hKsec SL(2, F) ψ g).toFun (T w) :=
    module_T_comm hs hKsec hHK huK huW huKcomm ψ
  have hf_comm : ∀ g : SL(2, F),
      f.toAddMonoidHom.comp (natEndHom F g) =
        (natEndHom F g).comp f.toAddMonoidHom := by
    intro g
    apply AddMonoidHom.ext
    intro v
    change f (natEndHom F g v) = natEndHom F g (f v)
    have h1 : e.symm (natEndHom F g v) =
        (repSec hs hKsec SL(2, F) ψ g).toFun (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, hact, e.apply_symm_apply]
    calc f (natEndHom F g v)
        = e (T (e.symm (natEndHom F g v))) := rfl
      _ = e (T ((repSec hs hKsec SL(2, F) ψ g).toFun (e.symm v))) := by rw [h1]
      _ = e ((repSec hs hKsec SL(2, F) ψ g).toFun (T (e.symm v))) := by rw [hT_comm]
      _ = natEndHom F g (e (T (e.symm v))) := hact g (T (e.symm v))
      _ = natEndHom F g (f v) := rfl
  have hend := (CFSG.QuasithinUnique.Setup.SL2Modules.natural_SL2_prime_field_normalizer
    (F := F) (p := 2)).1
  exact (hend f.toAddMonoidHom).mp (by
    intro g
    change f.toAddMonoidHom.comp (natEndHom F g) =
      (natEndHom F g).comp f.toAddMonoidHom
    exact hf_comm g)

private theorem module_T_eq_refl {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G)) (hu2 : u * u ∈ K)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (φ : SecMod hs ≃+ (Fin 1 → Fin 2 → F))
    {c : F}
    (hc : (moduleF (φ.trans (secFinOneEquiv F)) (moduleT huK huW)).toAddMonoidHom =
      scalEnd c) :
    moduleT huK huW = AddEquiv.refl (SecMod hs) := by
  let e := φ.trans (secFinOneEquiv F)
  let T := moduleT huK huW
  let f := moduleF e T
  have hc0 : c ≠ 0 := by
    intro h0
    have hf0 : (f : (Fin 2 → F) → (Fin 2 → F)) = 0 := by
      change (f.toAddMonoidHom : (Fin 2 → F) → (Fin 2 → F)) = 0
      rw [hc, h0]
      ext v
      simp [scalEnd]
    have hsingle : (Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F) = 0 :=
      f.injective (by rw [hf0]; simp)
    exact one_ne_zero (congrFun hsingle 0)
  have hT2 : ∀ w, T (T w) = w := module_T_sq hs huK huW hu2
  have hf2 : f.trans f = AddEquiv.refl (Fin 2 → F) := by
    ext v x
    change f (f v) x = v x
    have hvv : f (f v) = v := by
      calc f (f v) = e (T (e.symm (e (T (e.symm v))))) := rfl
        _ = e (T (T (e.symm v))) := by rw [e.symm_apply_apply]
        _ = e (e.symm v) := by rw [hT2]
        _ = v := e.apply_symm_apply v
    exact congrFun hvv x
  have hf2_eval : f (f (Pi.single (0 : Fin 2) (1 : F))) =
      Pi.single (0 : Fin 2) (1 : F) := by
    have h := congrArg (fun g : (Fin 2 → F) ≃+ (Fin 2 → F) =>
      g (Pi.single (0 : Fin 2) (1 : F))) hf2
    simpa using h
  have hc2 : c * c = 1 := by
    have h := hf2_eval
    change f.toAddMonoidHom (f.toAddMonoidHom (Pi.single (0 : Fin 2) (1 : F))) =
      Pi.single (0 : Fin 2) (1 : F) at h
    rw [hc] at h
    simpa [scalEnd, Pi.smul_apply, smul_eq_mul, mul_assoc] using congrFun h 0
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa [pow_two] using hc2)
  have hf1 : f = AddEquiv.refl (Fin 2 → F) := by
    ext v x
    change f.toAddMonoidHom v x = v x
    rw [hc, hc1]
    simp [scalEnd]
  ext w
  have h := congrArg (fun g : (Fin 2 → F) ≃+ (Fin 2 → F) => g (e w)) hf1
  have h2 : e (T w) = e w := by simpa [f, moduleF] using h
  exact e.injective h2


private theorem module_section_card {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    (hW_le_K : W ≤ K)
    (hcardK : Nat.card K = Nat.card V ^ 8)
    (hcardW : Nat.card W = Nat.card V ^ 4) :
    Nat.card (SecMod hs) = Nat.card V ^ 4 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_K).toEquiv] at hcard
  have hcardSec : Nat.card (SecMod hs) =
      Nat.card (↥K ⧸ W.subgroupOf K) := Nat.card_congr Additive.toMul
  have hcard' : Nat.card K = Nat.card (SecMod hs) * Nat.card W := by
    rw [hcardSec]
    exact hcard
  have hqpos : 0 < Nat.card V := Nat.card_pos
  have hq4pos : 0 < Nat.card V ^ 4 := pow_pos hqpos 4
  have h1 : Nat.card (SecMod hs) * Nat.card V ^ 4 = Nat.card V ^ 8 := by
    calc Nat.card (SecMod hs) * Nat.card V ^ 4
        = Nat.card (SecMod hs) * Nat.card W := by rw [hcardW]
      _ = Nat.card K := hcard'.symm
      _ = Nat.card V ^ 8 := hcardK
  have h2 : Nat.card V ^ 8 = Nat.card V ^ 4 * Nat.card V ^ 4 := by
    rw [← pow_add]
  have h3 : Nat.card (SecMod hs) * Nat.card V ^ 4 =
      Nat.card V ^ 4 * Nat.card V ^ 4 := by rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right hq4pos h3


private theorem module_mem_of_T_eq_refl {H K W : Subgroup G}
    (hs : QuotMod.Hyp H K W) [(W.subgroupOf K).Normal]
    {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (hT1 : moduleT huK huW = AddEquiv.refl (SecMod hs)) :
    ∀ n ∈ K, u * n * u⁻¹ * n⁻¹ ∈ W := by
  intro n hn
  have hTn : moduleT huK huW (SecMod.mk hs ⟨n, hn⟩) = SecMod.mk hs ⟨n, hn⟩ := by
    rw [hT1]
    rfl
  have hTn' : MulEquiv.toAdditive (secConjAut huK huW) (SecMod.mk hs ⟨n, hn⟩) =
      SecMod.mk hs ⟨n, hn⟩ := by
    simpa only [moduleT] using hTn
  rw [secConjAdd_mk] at hTn'
  have hmem : (⟨u * n * u⁻¹,
      (Subgroup.mem_normalizer_iff.mp huK n).1 hn⟩ /
      ⟨n, hn⟩ : ↥K) ∈ W.subgroupOf K := by
    apply (QuotientGroup.eq_iff_div_mem).mp
    apply_fun Additive.toMul at hTn'
    simpa [SecMod.mk, QuotMod.mk, toMul_ofMul] using hTn'
  simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmem

private theorem mul_self_eq_one_of_inv_mul_mem {W : Subgroup G} (hW : ∀ w ∈ W, w * w = 1)
    {t n : G} (ht : t ∈ Subgroup.centralizer (W : Set G)) (htt : t * t = 1)
    (hw : t⁻¹ * n ∈ W) : n * n = 1 := by
  have hwc : t⁻¹ * n * t = t * (t⁻¹ * n) := Subgroup.mem_centralizer_iff.mp ht _ hw
  calc n * n = t * (t⁻¹ * n * t) * (t⁻¹ * n) := by group
    _ = t * (t * (t⁻¹ * n)) * (t⁻¹ * n) := by rw [hwc]
    _ = (t * t) * (t⁻¹ * n * (t⁻¹ * n)) := by group
    _ = 1 := by rw [htt, hW _ hw, one_mul]

private theorem module_exists_conj_eq {H K W : Subgroup G} (hs : QuotMod.Hyp H K W)
    [(W.subgroupOf K).Normal] [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ K, k * n * k⁻¹ * n⁻¹ ∈ W)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {ψ : HBar V H ≃* SL(2, F)}
    (φ : SecMod hs ≃+ (Fin 1 → Fin 2 → F))
    (hφ : ∀ (g : SL(2, F)) (w : SecMod hs) (i : Fin 1),
      φ ((repSec hs hKsec SL(2, F) ψ g).toFun w) i =
        (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w i))
    {k n : ↥K} (hk : (k : G) ∉ W) (hn : (n : G) ∉ W) :
    ∃ z : ↥H, SecMod.mk hs ⟨(z : G) * k * (z : G)⁻¹, hs.conj z z.2 k k.2⟩ =
      SecMod.mk hs n := by
  classical
  have hne : ∀ m : ↥K, (m : G) ∉ W → φ (SecMod.mk hs m) 0 ≠ 0 := by
    intro m hm h0
    apply hm
    rw [← SecMod.mk_eq_zero_iff hs]
    apply φ.injective
    rw [map_zero]
    funext i
    rw [Subsingleton.elim i 0, h0]
    rfl
  obtain ⟨g₀, hg₀⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq (hne k hk)
  obtain ⟨g₁, hg₁⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq (hne n hn)
  obtain ⟨t, ht⟩ := ψ.surjective (g₁ * g₀⁻¹)
  obtain ⟨z, rfl⟩ := piK_surjective V H t
  refine ⟨z, ?_⟩
  rw [← repSec_apply_piK_mk hs hKsec SL(2, F) ψ z k, ht]
  apply φ.injective
  funext i
  rw [Subsingleton.elim i 0]
  change φ ((repSec hs hKsec SL(2, F) ψ (g₁ * g₀⁻¹)).toFun (SecMod.mk hs k)) 0 = _
  rw [hφ, ← hg₀, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel_right, hg₁]

theorem Sec45Shape.commutator_mem_xOf_of_mul_self_mem
    {H : Subgroup G} {h₀ : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V H ≃* SL(2, F)}
    (hw : Sec45ShapeWith M V H F l hl ψ)
    {u : G}
    (huK : u ∈ Subgroup.normalizer (kOf V H : Set G))
    (huW : u ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G))
    (huKcomm : ∀ x ∈ H, ⁅u, x⁆ ∈ kOf V H)
    (hu2 : u * u ∈ kOf V H)
    (hcardK : Nat.card (kOf V H) = Nat.card V ^ 8)
    (hcardW : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4) :
    ∀ n ∈ kOf V H, ⁅u, n⁆ ∈ Tim79a.xOf V H := by
  classical
  let K := kOf V H
  let W := Tim79a.xOf V H
  let hs : QuotMod.Hyp H K W := hS.quotModHyp h
  haveI hsN : (W.subgroupOf K).Normal := hs.normal
  have hW_le_K : W ≤ K := by
    dsimp [K, W, kOf]
    refine le_inf (Tim79a.xOf_le_H (h.toHyp.le_Pc.trans hS.Pc_le)) ?_
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact (hS.isElemAbelian h).1
  have hKWcard : Nat.card (SecMod hs) = Nat.card V ^ 4 :=
    module_section_card hs hW_le_K (by simpa [K] using hcardK)
      (by simpa [W] using hcardW)
  let hsq : ∀ n ∈ K, n * n ∈ W := by
    intro n hn
    exact hw.sq_mem n hn
  letI hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hsq
  have hSum : Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ) :=
    hw.natSum hs hmod
  obtain ⟨k, φ, hφ⟩ := hSum
  have hcardφ : Nat.card (SecMod hs) = Nat.card (Fin k → Fin 2 → F) :=
    Nat.card_congr φ.toEquiv
  have hcardR : Nat.card (Fin k → Fin 2 → F) = Nat.card F ^ (2 * k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    simp [Fintype.card_fin, pow_mul, mul_comm]
    ring
  have hFcard : Nat.card F = Nat.card V ^ 2 := by
    rw [Nat.card_eq_fintype_card, hl, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hq1 : 1 < Nat.card V := by
    have := h.four_le_card
    omega
  have hk1 : k = 1 :=
    module_k_eq_one hs φ hKWcard hFcard hq1
  subst hk1
  obtain ⟨c, hc⟩ := module_scalar hs hs.comm (le_normalizer_kOf V H) huK huW huKcomm φ hφ
  have hT1 : moduleT huK huW = AddEquiv.refl (SecMod hs) :=
    module_T_eq_refl hs huK huW hu2 φ hc
  intro n hn
  simpa [commutatorElement_def] using module_mem_of_T_eq_refl hs huK huW hT1 n hn

theorem Sec45Shape.mem_xOf_of_mul_self_eq_one
    {H : Subgroup G} {h₀ : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V H ≃* SL(2, F)}
    (hw : Sec45ShapeWith M V H F l hl ψ)
    (hcardK : Nat.card (kOf V H) = Nat.card V ^ 8)
    (hcardW : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4)
    {k : G} (hk : k ∈ kOf V H) (hk2 : k * k = 1) : k ∈ Tim79a.xOf V H := by
  classical
  by_contra hkW
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hS.quotModHyp h
  haveI hsN : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  have hW_le_K : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hKWcard : Nat.card (SecMod hs) = Nat.card V ^ 4 :=
    module_section_card hs hW_le_K hcardK hcardW
  letI hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  obtain ⟨m, φ, hφ⟩ := hw.natSum hs hmod
  have hFcard : Nat.card F = Nat.card V ^ 2 := by
    rw [Nat.card_eq_fintype_card, hl, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hq1 : 1 < Nat.card V := by
    have := h.four_le_card
    omega
  have hm1 : m = 1 := module_k_eq_one hs φ hKWcard hFcard hq1
  subst hm1
  have hWab := hS.isElemAbelian h
  have hW2 : ∀ w ∈ Tim79a.xOf V H, w * w = 1 := fun w hw' => by
    simpa [pow_two] using hWab.2 w hw'
  have hsq : ∀ n ∈ kOf V H, n * n = 1 := by
    intro n hn
    by_cases hnW : n ∈ Tim79a.xOf V H
    · exact hW2 n hnW
    obtain ⟨z, hz⟩ := module_exists_conj_eq hs hs.comm φ hφ
      (k := ⟨k, hk⟩) (n := ⟨n, hn⟩) hkW hnW
    have hwW : ((z : G) * k * (z : G)⁻¹)⁻¹ * n ∈ Tim79a.xOf V H :=
      (QuotMod.mk_eq_mk_iff (N := kOf V H) (N₀ := Tim79a.xOf V H) _ _).1 hz
    have htK : (z : G) * k * (z : G)⁻¹ ∈ kOf V H := hs.conj z z.2 k hk
    have htt : (z : G) * k * (z : G)⁻¹ * ((z : G) * k * (z : G)⁻¹) = 1 := by
      rw [show (z : G) * k * (z : G)⁻¹ * ((z : G) * k * (z : G)⁻¹) =
        (z : G) * (k * k) * (z : G)⁻¹ by group, hk2]
      group
    exact mul_self_eq_one_of_inv_mul_mem hW2 (mem_kOf_iff.mp htK).2 htt hwW
  have hKab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (hsq _ ((kOf V H).mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (hsq x hx), inv_eq_of_mul_eq_one_right (hsq y hy)]
  have hKW : kOf V H ≤ Tim79a.xOf V H := by
    rw [← hw.center_K]
    exact fun x hx => Subgroup.mem_inf.mpr
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hKab y hy x hx⟩
  exact hkW (hKW hk)

end CFSG.RankThree.GF2n.Tim81
