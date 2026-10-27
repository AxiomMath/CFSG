module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.Assembly.OpenBridges
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem F09_rank_obstruction {z : G} (hz : orderOf z = 3) {K₁ K₂ : Subgroup G} (hne : K₁ ≠ K₂)
    (h₁ : LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) K₁)
    (h₂ : LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) K₂) {r : ℕ}
    (hw₁ : Rank3Witness ↥(barImage z K₁) r) (hw₂ : Elem3Disjoint ↥(barImage z K₂) r) :
    2 * r + 1 ≤ LargeEvenTwoLocalRank 3 G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hzC : z ∈ C := by
    change z ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  let O : Subgroup ↥C := LargeEvenPPrimeCore 3 ↥C
  let Q := ↥C ⧸ O
  let mk : ↥C →* Q := QuotientGroup.mk' O
  let K1b : Subgroup Q := barImage z K₁
  let K2b : Subgroup Q := barImage z K₂
  have hGLA₁ : CFSG.Open.GLAPComponent 3 C K₁ :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 C K₁).1 h₁
  have hGLA₂ : CFSG.Open.GLAPComponent 3 C K₂ :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 C K₂).1 h₂
  have hcomp₁ : CFSG.Open.IsComponentOf K1b ⊤ := hGLA₁.2.2.1
  have hcomp₂ : CFSG.Open.IsComponentOf K2b ⊤ := hGLA₂.2.2.1
  have hnebar : K1b ≠ K2b := by
    intro h
    exact hne (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_unique hGLA₁ hGLA₂ h)
  have hcommK : ⁅K1b, K2b⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne K1b K2b hcomp₁ hcomp₂ hnebar
  obtain ⟨E₁, t₁, hE₁ea, hE₁card, hE₁disj, ⟨k, hk⟩, ht₁nc, hE₁cent⟩ := hw₁
  obtain ⟨E₂, hE₂ea, hE₂card, hE₂disj⟩ := hw₂
  let F₁ : Subgroup Q := E₁.map K1b.subtype
  let F₂ : Subgroup Q := E₂.map K2b.subtype
  let zbar : Q := mk ⟨z, hzC⟩
  let Z : Subgroup Q := Subgroup.zpowers zbar
  let W : Subgroup Q := F₁ ⊔ F₂
  let Ebar : Subgroup Q := W ⊔ Z
  have hzC_center : (⟨z, hzC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 c.2 z (by simp)).symm
  have hzbar_center : zbar ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O q
    show mk c * mk ⟨z, hzC⟩ = mk ⟨z, hzC⟩ * mk c
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subgroup.mem_center_iff.1 hzC_center c)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hzbar_pow : zbar ^ 3 = 1 := by
    show mk ⟨z, hzC⟩ ^ 3 = 1
    rw [← map_pow]
    have h : (⟨z, hzC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [h, map_one]
  have hcopO : Nat.Coprime 3 (Nat.card O) := by
    have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥C)
    simpa [O, LargeEvenPPrimeCore] using h
  have hzbar_ne : zbar ≠ 1 := by
    intro hzbar_one
    have hzO : (⟨z, hzC⟩ : ↥C) ∈ O := by
      have hmem : (⟨z, hzC⟩ : ↥C) ∈ (QuotientGroup.mk' O).ker := by
        rw [MonoidHom.mem_ker]
        exact hzbar_one
      rwa [QuotientGroup.ker_mk'] at hmem
    have horder : orderOf (⟨z, hzC⟩ : ↥C) = 3 := by
      rw [Subgroup.orderOf_mk, hz]
    have h3dvd : 3 ∣ Nat.card O := by
      rw [← horder]
      exact Subgroup.orderOf_dvd_natCard O hzO
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopO h3dvd
  have hzbar_order : orderOf zbar = 3 := orderOf_eq_prime hzbar_pow hzbar_ne
  have hZcard : Nat.card Z = 3 := by
    change Nat.card (Subgroup.zpowers zbar) = 3
    rw [Nat.card_zpowers, hzbar_order]
  have hF₁ea : IsElemAbelian 3 F₁ := CFSG.Open.IsElemAbelian.map hE₁ea K1b.subtype
  have hF₂ea : IsElemAbelian 3 F₂ := CFSG.Open.IsElemAbelian.map hE₂ea K2b.subtype
  have hZea : IsElemAbelian 3 Z := CFSG.Open.isElemAbelian_zpowers hzbar_pow
  have hF₁card : Nat.card F₁ = 3 ^ r := by
    change Nat.card (E₁.map K1b.subtype) = 3 ^ r
    rw [Subgroup.card_map_of_injective K1b.subtype_injective, hE₁card]
  have hF₂card : Nat.card F₂ = 3 ^ r := by
    change Nat.card (E₂.map K2b.subtype) = 3 ^ r
    rw [Subgroup.card_map_of_injective K2b.subtype_injective, hE₂card]
  have hF₁le : F₁ ≤ K1b := Subgroup.map_subtype_le E₁
  have hF₂le : F₂ ≤ K2b := Subgroup.map_subtype_le E₂
  have hKcomm : ∀ x ∈ K1b, ∀ y ∈ K2b, x * y = y * x := by
    intro x hx y hy
    have hmem := Subgroup.commutator_mem_commutator (H₁ := K1b) (H₂ := K2b) hx hy
    rw [hcommK] at hmem
    have h1 : ⁅x, y⁆ = 1 := by simpa using hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcomm12 : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hKcomm x x.2 y y.2
  have hcommF₁Z : ∀ a ∈ F₁, ∀ b ∈ Z, a * b = b * a := by
    intro a _ b hb
    exact Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzbar_center hb) a
  have hcommF₂Z : ∀ a ∈ F₂, ∀ b ∈ Z, a * b = b * a := by
    intro a _ b hb
    exact Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzbar_center hb) a
  have hF₁F₂ : F₁ ⊓ F₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha₁, ha₂⟩
    rw [Subgroup.mem_bot]
    change a ∈ E₁.map K1b.subtype at ha₁
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha₁
    have hxK2 : (x : Q) ∈ K2b := hF₂le ha₂
    have hxcenter : x ∈ Subgroup.center ↥K1b := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply K1b.subtype_injective
      show ((z * x : ↥K1b) : Q) = ((x * z : ↥K1b) : Q)
      simpa using hKcomm z z.2 x hxK2
    have hxbot : x ∈ E₁ ⊓ Subgroup.center ↥K1b := ⟨hx, hxcenter⟩
    rw [hE₁disj, Subgroup.mem_bot] at hxbot
    rw [hxbot, map_one]
  have hWZ : W ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haW, haZ⟩
    rw [Subgroup.mem_bot]
    change a ∈ F₁ ⊔ F₂ at haW
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.i224_mem_sup_of_comm hcomm12 haW
    have hf₁eq : f₁ = (f₁ * f₂) * f₂⁻¹ := by group
    have hf₁comm : ∀ z ∈ K1b, Commute f₁ z := by
      intro z hz
      have hf₂z : Commute f₂ z :=
        (commute_iff_eq _ _).mpr (hKcomm z hz f₂ (hF₂le hf₂)).symm
      have haz : Commute (f₁ * f₂) z :=
        (commute_iff_eq _ _).mpr
          (Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzbar_center haZ) z).symm
      have h : Commute ((f₁ * f₂) * f₂⁻¹) z := haz.mul_left hf₂z.inv_left
      rw [← hf₁eq] at h
      exact h
    have hf₁center : (⟨f₁, hF₁le hf₁⟩ : ↥K1b) ∈ Subgroup.center ↥K1b := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply K1b.subtype_injective
      show ((z * ⟨f₁, hF₁le hf₁⟩ : ↥K1b) : Q) = ((⟨f₁, hF₁le hf₁⟩ * z : ↥K1b) : Q)
      simpa using (hf₁comm z z.2).eq.symm
    change f₁ ∈ E₁.map K1b.subtype at hf₁
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf₁
    have hxcenter : x ∈ Subgroup.center ↥K1b := by simpa using hf₁center
    have hxbot : x = 1 := by
      have hmem : x ∈ E₁ ⊓ Subgroup.center ↥K1b := ⟨hx, hxcenter⟩
      rwa [hE₁disj, Subgroup.mem_bot] at hmem
    have hf₂Z : f₂ ∈ Z := by simpa [hxbot] using haZ
    have hf₂centerQ : f₂ ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzbar_center hf₂Z) g
    rw [hxbot, map_one, one_mul]
    change f₂ ∈ E₂.map K2b.subtype at hf₂
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hf₂
    have hycenter : y ∈ Subgroup.center ↥K2b := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply K2b.subtype_injective
      show ((z * y : ↥K2b) : Q) = ((y * z : ↥K2b) : Q)
      simpa using Subgroup.mem_center_iff.1 hf₂centerQ (z : Q)
    have hybot : y = 1 := by
      have hmem : y ∈ E₂ ⊓ Subgroup.center ↥K2b := ⟨hy, hycenter⟩
      rwa [hE₂disj, Subgroup.mem_bot] at hmem
    rw [hybot, map_one]
  have hcommWZ : ∀ a ∈ W, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    change a ∈ F₁ ⊔ F₂ at ha
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.i224_mem_sup_of_comm hcomm12 ha
    calc f₁ * f₂ * b = f₁ * (f₂ * b) := by group
      _ = f₁ * (b * f₂) := by rw [hcommF₂Z f₂ hf₂ b hb]
      _ = f₁ * b * f₂ := by group
      _ = b * f₁ * f₂ := by rw [hcommF₁Z f₁ hf₁ b hb]
      _ = b * (f₁ * f₂) := by group
  have hWea : IsElemAbelian 3 W := hF₁ea.sup_of_commute hF₂ea hcomm12
  have hEbar_ea : IsElemAbelian 3 Ebar := hWea.sup_of_commute hZea hcommWZ
  have hcardW : Nat.card W = 3 ^ r * 3 ^ r := by
    change Nat.card ↥(F₁ ⊔ F₂) = 3 ^ r * 3 ^ r
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i224_card_sup hcomm12 hF₁F₂,
      hF₁card, hF₂card]
  have hcardEbar : Nat.card Ebar = 3 ^ (2 * r + 1) := by
    change Nat.card ↥(W ⊔ Z) = 3 ^ (2 * r + 1)
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i224_card_sup hcommWZ hWZ,
      hcardW, hZcard]
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  let tbar : Q := K1b.subtype t₁
  have htbar_pow : tbar ^ 2 ^ k = 1 := by
    have h := congrArg K1b.subtype hk
    simpa [tbar] using h
  have htbar_ne : tbar ≠ 1 := by
    intro h
    have h1 : t₁ = 1 := K1b.subtype_injective (by simpa [tbar] using h)
    rw [h1] at ht₁nc
    exact ht₁nc (Subgroup.one_mem _)
  have hF₁comm : ∀ a ∈ F₁, Commute a tbar := by
    rintro _ ⟨x, hx, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 (hE₁cent hx) t₁ (by simp)
    exact (commute_iff_eq _ _).mpr (by simpa [tbar, map_mul] using (congrArg K1b.subtype h).symm)
  have hF₂comm : ∀ a ∈ F₂, Commute a tbar := by
    rintro _ ⟨y, hy, rfl⟩
    exact (commute_iff_eq _ _).mpr (hKcomm t₁ t₁.2 y y.2).symm
  have hZcomm : ∀ b ∈ Z, Commute b tbar := by
    intro b hb
    exact (commute_iff_eq _ _).mpr
      (Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzbar_center hb) tbar).symm
  have hEbar_cent : Ebar ≤ Subgroup.centralizer ({tbar} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact Subgroup.mem_centralizer_iff.2 (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hF₁comm a ha).eq.symm)
    · intro a ha
      exact Subgroup.mem_centralizer_iff.2 (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hF₂comm a ha).eq.symm)
    · intro b hb
      exact Subgroup.mem_centralizer_iff.2 (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hZcomm b hb).eq.symm)
  have hEbar_comm : ∀ q ∈ Ebar, Commute q tbar := by
    intro q hq
    exact (commute_iff_eq _ _).mpr
      (Subgroup.mem_centralizer_iff.1 (hEbar_cent hq) tbar (by simp)).symm
  let H : Subgroup ↥C := Ebar.comap mk
  have hOle_comap : ∀ V : Subgroup Q, O ≤ V.comap mk := by
    intro V o ho
    rw [Subgroup.mem_comap]
    have h1 : mk o = 1 := by
      change (o : ↥C ⧸ O) = 1
      exact (QuotientGroup.eq_one_iff (N := O) o).mpr ho
    rw [h1]
    exact V.one_mem
  have hker_comap : ∀ V : Subgroup Q,
      (mk.comp (V.comap mk).subtype).ker = O.subgroupOf (V.comap mk) := by
    intro V
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hx : mk (x : ↥C) = 1 := by
        show (mk.comp (V.comap mk).subtype) x = 1
        exact h
      have hker : (x : ↥C) ∈ (QuotientGroup.mk' O).ker := by
        apply MonoidHom.mem_ker.mpr
        show (QuotientGroup.mk' O) (x : ↥C) = 1
        exact hx
      rwa [QuotientGroup.ker_mk'] at hker
    · intro h
      apply MonoidHom.mem_ker.mpr
      show mk (x : ↥C) = 1
      show (QuotientGroup.mk' O) (x : ↥C) = 1
      exact (QuotientGroup.eq_one_iff (N := O) (x : ↥C)).mpr h
  have hrange_comap : ∀ V : Subgroup Q, (mk.comp (V.comap mk).subtype).range = V := by
    intro V
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hq
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O q
      exact ⟨⟨c, Subgroup.mem_comap.2 hq⟩, rfl⟩
  have hcard_comap : ∀ V : Subgroup Q,
      Nat.card ↥(V.comap mk) = Nat.card O * Nat.card V := by
    intro V
    have h := Subgroup.card_ker_mul_card_range (mk.comp (V.comap mk).subtype)
    rw [hker_comap V, hrange_comap V] at h
    have hOsub : Nat.card ↥(O.subgroupOf (V.comap mk)) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOle_comap V)).toEquiv
    rw [hOsub] at h
    exact h.symm
  have hOleH : O ≤ H := hOle_comap Ebar
  have hcardH : Nat.card ↥H = Nat.card O * Nat.card Ebar := hcard_comap Ebar
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥H))
  have hfacO : Nat.factorization (Nat.card O) 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopO)
  have hfacEbar : Nat.factorization (Nat.card Ebar) 3 = 2 * r + 1 := by
    rw [hcardEbar, Nat.factorization_pow_self Nat.prime_three]
  have hcardS : Nat.card (S : Subgroup ↥H) = 3 ^ (2 * r + 1) := by
    rw [Sylow.card_eq_multiplicity S, hcardH,
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
    simp [hfacO, hfacEbar]
  have hS_disjO : (S : Subgroup ↥H) ⊓ O.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxO⟩
    rw [Subgroup.mem_bot]
    have hxS_card : orderOf x ∣ Nat.card (S : Subgroup ↥H) :=
      Subgroup.orderOf_dvd_natCard _ hxS
    have hxO_card : orderOf x ∣ Nat.card (O.subgroupOf H) :=
      Subgroup.orderOf_dvd_natCard _ hxO
    have hOsub : Nat.card (O.subgroupOf H) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleH).toEquiv
    have hcopSO : Nat.Coprime (Nat.card (S : Subgroup ↥H))
        (Nat.card (O.subgroupOf H)) := by
      rw [hcardS, hOsub]
      exact Nat.Coprime.pow_left _ hcopO
    have hone : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopSO hxS_card hxO_card
    exact orderOf_eq_one_iff.mp hone
  have hmk_ker : (mk.comp H.subtype).ker = O.subgroupOf H := hker_comap Ebar
  let fS : ↥S →* Q := (mk.comp H.subtype).comp (S : Subgroup ↥H).subtype
  have hfS_mem : ∀ a : ↥S, fS a ∈ Ebar := by
    intro a
    have haH : ((a : ↥H) : ↥C) ∈ H := (a : ↥H).2
    show mk ((a : ↥H) : ↥C) ∈ Ebar
    exact Subgroup.mem_comap.1 haH
  have hfS_inj : Function.Injective fS := by
    intro a b h
    have hmemS : (a : ↥H) * (b : ↥H)⁻¹ ∈ (S : Subgroup ↥H) :=
      (S : Subgroup ↥H).mul_mem a.2 ((S : Subgroup ↥H).inv_mem b.2)
    have hmemO : (a : ↥H) * (b : ↥H)⁻¹ ∈ O.subgroupOf H := by
      rw [← hmk_ker, MonoidHom.mem_ker]
      have hh : (mk.comp H.subtype) (a : ↥H) = (mk.comp H.subtype) (b : ↥H) := by
        change fS a = fS b
        exact h
      have h' : (mk.comp H.subtype) ((a : ↥H) * (b : ↥H)⁻¹) = 1 := by
        rw [map_mul, map_inv, hh]
        simp
      exact h'
    have hmem : (a : ↥H) * (b : ↥H)⁻¹ ∈
        (S : Subgroup ↥H) ⊓ O.subgroupOf H := ⟨hmemS, hmemO⟩
    rw [hS_disjO] at hmem
    have hxone : (a : ↥H) * (b : ↥H)⁻¹ = 1 := by simpa using hmem
    exact Subtype.ext (mul_inv_eq_one.mp hxone)
  have hS_ea : IsElemAbelian 3 (S : Subgroup ↥H) := by
    refine (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mpr
      (CFSG.IsElementaryAbelian.of_forall ?_ ?_)
    · intro x hx y hy
      have h1 : (⟨x * y, (S : Subgroup ↥H).mul_mem hx hy⟩ : ↥S) =
          ⟨y * x, (S : Subgroup ↥H).mul_mem hy hx⟩ := by
        apply hfS_inj
        show fS ((⟨x, hx⟩ : ↥S) * ⟨y, hy⟩) = fS ((⟨y, hy⟩ : ↥S) * ⟨x, hx⟩)
        rw [map_mul, map_mul]
        exact hEbar_ea.comm (hfS_mem ⟨x, hx⟩) (hfS_mem ⟨y, hy⟩)
      exact congrArg Subtype.val h1
    · intro x hx
      have h1 : (⟨x ^ 3, (S : Subgroup ↥H).pow_mem hx 3⟩ : ↥S) =
          ⟨1, (S : Subgroup ↥H).one_mem⟩ := by
        apply hfS_inj
        change fS ((⟨x, hx⟩ : ↥S) ^ 3) = fS 1
        rw [map_pow, map_one]
        exact hEbar_ea.2 _ (hfS_mem ⟨x, hx⟩)
      exact congrArg Subtype.val h1
  let S' : Subgroup ↥C := (S : Subgroup ↥H).map H.subtype
  have hS'ea : IsElemAbelian 3 S' := CFSG.Open.IsElemAbelian.map hS_ea H.subtype
  have hS'card : Nat.card S' = 3 ^ (2 * r + 1) := by
    change Nat.card ((S : Subgroup ↥H).map H.subtype) = 3 ^ (2 * r + 1)
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardS]
  let P : Subgroup ↥C := (Subgroup.zpowers tbar).comap mk
  have hOleP : O ≤ P := hOle_comap _
  have hPcard : Nat.card ↥P = Nat.card O * Nat.card (Subgroup.zpowers tbar) :=
    hcard_comap _
  have htbar_order_dvd : orderOf tbar ∣ 2 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr htbar_pow
  have htbar_order_ne : orderOf tbar ≠ 1 := fun h => htbar_ne (orderOf_eq_one_iff.mp h)
  have h2zp : 2 ∣ Nat.card (Subgroup.zpowers tbar) := by
    rw [Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp htbar_order_dvd
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · exact absurd (by rw [hj, hj0]; simp) htbar_order_ne
    · rw [hj]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hjpos)
  have hzp_coprime : Nat.Coprime 3 (Nat.card (Subgroup.zpowers tbar)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.of_dvd_right htbar_order_dvd (Nat.Coprime.pow_right k (by norm_num))
  have hP_coprime : Nat.Coprime 3 (Nat.card ↥P) := by
    rw [hPcard]
    exact hcopO.mul_right hzp_coprime
  have h3P : ¬ 3 ∣ Nat.card ↥P :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hP_coprime
  have h2P : 2 ∣ Nat.card ↥P := by
    rw [hPcard]
    exact dvd_mul_of_dvd_right h2zp _
  have hS'normP : S' ≤ Subgroup.normalizer (P : Set ↥C) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha p hp
    rw [Subgroup.mem_comap] at hp ⊢
    change a ∈ (S : Subgroup ↥H).map H.subtype at ha
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ha
    have haE : mk (H.subtype s) ∈ Ebar := Subgroup.mem_comap.1 s.2
    have hcomm_at : Commute (mk (H.subtype s)) (mk p) := by
      have hcentral : Subgroup.zpowers tbar ≤
          Subgroup.centralizer ({mk (H.subtype s)} : Set Q) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hEbar_comm _ haE).eq
      exact (commute_iff_eq _ _).mpr
        (Subgroup.mem_centralizer_iff.1 (hcentral hp) (mk (H.subtype s)) (by simp))
    have hcalc : mk (H.subtype s * p * (H.subtype s)⁻¹) = mk p := by
      calc mk (H.subtype s * p * (H.subtype s)⁻¹)
          = mk (H.subtype s) * mk p * (mk (H.subtype s))⁻¹ := by simp [map_mul]
        _ = mk p := by rw [hcomm_at.eq]; group
    rw [hcalc]
    exact hp
  have hS'class : CFSG.IsElementaryAbelian 3 ↥S' := hS'ea.isElementaryAbelian
  let φ : ↥S' →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hS'normP)
  let : MulDistribMulAction ↥S' ↥P := MulDistribMulAction.compHom ↥P φ
  obtain ⟨U, hUinv⟩ :=
    CFSG.SolvableHall.exists_invariant_sylow (A := ↥S') (p := 3) (H := ↥P) h3P 2
  have hUne : (U : Subgroup ↥P) ≠ ⊥ := Sylow.ne_bot_of_dvd_card U h2P
  have hsmul_coe : ∀ (a : ↥S') (x : ↥P),
      ((a • x : ↥P) : ↥C) = (a : ↥C) * (x : ↥C) * (a : ↥C)⁻¹ := fun _ _ => rfl
  let U' : Subgroup ↥C := (U : Subgroup ↥P).map P.subtype
  have hU'ne : U' ≠ ⊥ := by
    intro h
    apply hUne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := (U : Subgroup ↥P))
      P.subtype_injective).mp h
  have hS'normU' : S' ≤ Subgroup.normalizer (U' : Set ↥C) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    change x ∈ (U : Subgroup ↥P).map P.subtype at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    change a * P.subtype y * a⁻¹ ∈ (U : Subgroup ↥P).map P.subtype
    let s : ↥S' := ⟨a, ha⟩
    have hzU : (s • y : ↥P) ∈ (U : Subgroup ↥P) := hUinv s y hy
    have hzEq : P.subtype (s • y : ↥P) = a * P.subtype y * a⁻¹ := by
      change ((s • y : ↥P) : ↥C) = a * (y : ↥C) * a⁻¹
      exact hsmul_coe s y
    rw [Subgroup.mem_map]
    exact ⟨(s • y : ↥P), hzU, hzEq⟩
  let E : Subgroup G := S'.map C.subtype
  let V : Subgroup G := U'.map C.subtype
  have hEea : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hS'ea C.subtype
  have hEcard : Nat.card E = 3 ^ (2 * r + 1) := by
    change Nat.card (S'.map C.subtype) = 3 ^ (2 * r + 1)
    rw [Subgroup.card_map_of_injective C.subtype_injective, hS'card]
  have hV2 : IsPGroup 2 V := ((Sylow.isPGroup' U).map P.subtype).map C.subtype
  have hVne : V ≠ ⊥ := by
    intro h
    apply hU'ne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := U')
      C.subtype_injective).mp h
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := Subgroup.map_mono hS'normU' (f := C.subtype)
    have h2 := Subgroup.le_normalizer_map (H := U') C.subtype
    exact h1.trans h2
  have hrank : 2 * r + 1 ≤ CFSG.Open.GLATwoLocalRank 3 G :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_le_glaTwoLocalRank
      Nat.prime_three hV2 hVne hEV hEea hEcard
  rwa [CFSG.Assembly.LargeEven.largeEvenTwoLocalRank_eq_glaTwoLocalRank]

end CFSG.StandardType.FrameRoute

end
