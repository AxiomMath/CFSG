module

public import CFSG.Quasithin.H13.U3S1347B
public import CFSG.Quasithin.H13.U3S1349L

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Side (S : A6.Setting134 G T L V) (z : G) (H₂ : Subgroup G) : Prop where
  zV1 : z ∈ fsuV1 T V
  zL : z ∉ centralizer (L : Set G)
  L1T : L₁Of L (fsuV1 T V) ⊔ T ≤ centralizer ({z} : Set G)
  star : IsHStar T (normalizer (L : Set G)) H₂
  le_Gz : H₂ ≤ centralizer ({z} : Set G)
  quot : quasithinO2QuotientIso H₂ (Perm (Fin 3))
  cls : ∀ X : Subgroup G, T ≤ X → X ≤ centralizer ({z} : Set G) →
    X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = centralizer ({z} : Set G)
  inc1 : ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂
  inc2 : ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T
  cZ : U3.cZ T H₂ = zpowers z

structure SideI (S : A6.Setting134 G T L V) (z : G) (H₂ : Subgroup G) : Prop where
  side : Side S z H₂
  concl : U3.Concl1347i T H₂ (U3.l2Of S ⊔ T)
  psi : ∀ hz : z ∈ V, (S.frame.ψ ⟨z, hz⟩ : G6.PermMod 6) = e0123
  chief : HasTwoNoncentralChiefFactors (oTwoRes H₂)
  bad : ∀ X : Subgroup G, InH T X → centralizer ({z} : Set G) ≤ X → ∀ zb : G,
    zb ∈ fsuV1 T V → zb ∉ centralizer (L : Set G) → zb ≠ z → ∀ Y : Subgroup G, T ≤ Y →
    Y ≤ X → Y ≤ centralizer ({zb} : Set G) → ¬ Y ≤ normalizer (L : Set G) → False

structure SideII (S : A6.Setting134 G T L V) (z : G) (H₂ : Subgroup G) : Prop where
  side : Side S z H₂
  nj : H₂ ⊔ (U3.l2Of S ⊔ T) = normalizer (thompsonJ T : Set G)
  inM : InM T (H₂ ⊔ (U3.l2Of S ⊔ T))
  uniq : ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X →
    X ≤ H₂ ⊔ (U3.l2Of S ⊔ T) → X = H₂

omit [Finite G] in
theorem eq_of_zpowers_eq {a b : G} (hb : b ^ 2 = 1) (ha1 : a ≠ 1)
    (h : zpowers a = zpowers b) : a = b := by
  have hab : a ∈ zpowers b := h ▸ mem_zpowers a
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hab
  have hb' : b ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, hb]
  rcases Int.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exfalso
    apply ha1
    rw [← two_mul, zpow_mul, hb', one_zpow]
  · rw [zpow_add, zpow_one, zpow_mul, hb', one_zpow, one_mul]

omit [Finite G] in
theorem le_normalizer_of_comm {A B : Subgroup G} (h : ⁅A, B⁆ ≤ pCoreOf 2 A ⊓ pCoreOf 2 B) :
    B ≤ normalizer (A : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun b hb a ha => ?_
  have hba : ⁅b, a⁆ ∈ ⁅A, B⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hb ha
  have e : b * a * b⁻¹ = ⁅b, a⁆ * a := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (LieType.BorelTits.pCoreOf_le 2 _ (mem_inf.1 (h hba)).1) ha

theorem oThree_eq_oTwoRes (hT : IsPGroup 2 T) {H : Subgroup G} (hTH : T ≤ H)
    (h3 : T.relIndex H = 3) : oThreePrimeResidual H = oTwoRes H := by
  refine le_antisymm ?_ (U3.oTwoRes_le_oThreePrimeResidual hT hTH h3 (oTwoRes_le H))
  rw [oThreePrimeResidual, closure_le]
  rintro x ⟨hx, k, hk⟩
  exact U3.mem_oTwoRes_of_odd hx (Odd.pow (by decide)) hk

namespace Side

variable {S : A6.Setting134 G T L V} {z : G} {H₂ : Subgroup G} (A : Side S z H₂)
include A

theorem z_sq : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 A.zV1.2).2.2

theorem z_ne_one : z ≠ 1 := fun h => A.zL (h ▸ one_mem _)

theorem T_le : T ≤ H₂ := A.star.1.1

theorem isSylowTwoOf : IsSylowTwoOf T H₂ := A5.isSylowTwoOf_of_le S.h13.sylow A.T_le

theorem ne_T : H₂ ≠ T := fun h => A.star.2.1 (h ▸ S.T_le_NL)

theorem card_cZ : Nat.card ↥(U3.cZ T H₂) = 2 := by
  rw [A.cZ, Nat.card_zpowers, orderOf_eq_prime A.z_sq A.z_ne_one]

theorem eq_sup : L₁Of L (fsuV1 T V) ⊔ T ⊔ H₂ = centralizer ({z} : Set G) := by
  rcases A.cls _ (A.T_le.trans le_sup_right) (sup_le A.L1T A.le_Gz) with h | h | h | h
  · exact absurd (le_antisymm ((le_sup_right : H₂ ≤ _).trans h.le) A.T_le) A.ne_T
  · exact absurd ((le_sup_right : H₂ ≤ _).trans h.le) A.inc2
  · exact absurd ((le_sup_left : L₁Of L (fsuV1 T V) ⊔ T ≤ _).trans h.le) A.inc1
  · exact h

theorem inf_eq {X : Subgroup G} (hX : H₂ ≤ X) (hL : ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ X) :
    X ⊓ centralizer ({z} : Set G) = H₂ := by
  have hle : H₂ ≤ X ⊓ centralizer ({z} : Set G) := le_inf hX A.le_Gz
  rcases A.cls _ (A.T_le.trans hle) inf_le_right with h | h | h | h
  · exact absurd (le_antisymm (hle.trans h.le) A.T_le) A.ne_T
  · exact absurd (hle.trans h.le) A.inc2
  · exact h
  · exact absurd (A.L1T.trans (h.symm.le.trans inf_le_left)) hL

theorem inf_cZ_eq {X : Subgroup G} (hX : H₂ ≤ X) (hL : ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ X) :
    X ⊓ centralizer (U3.cZ T (oTwoRes H₂) : Set G) = H₂ := by
  rw [← U3.cZ_eq_cZ_oTwoRes A.isSylowTwoOf, A.cZ]
  refine le_antisymm (fun x hx => ?_) (le_inf hX (le_centralizer_iff.mpr
    (zpowers_le.2 (U3.mem_centralizer_of_le_centralizer A.le_Gz))))
  rw [← A.inf_eq hX hL]
  exact mem_inf.2 ⟨(mem_inf.1 hx).1,
    centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers z)) (mem_inf.1 hx).2⟩

theorem ne_of_ne {b : G} {H₂' : Subgroup G} (B : Side S b H₂') (hab : z ≠ b) : H₂ ≠ H₂' :=
  fun h => hab (eq_of_zpowers_eq B.z_sq A.z_ne_one (A.cZ.symm.trans (h ▸ B.cZ)))

theorem pCoreOf_oTwoRes_ne_bot : pCoreOf 2 (oTwoRes H₂) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hchar : CFSG.QuasithinUnique.CharTwo H₂ := U3.s134_charTwo_of_inH S A.star.1
  set R := pCoreOf 2 H₂ with hR
  set K₂ := oTwoRes H₂ with hK₂
  have hK₂H : K₂ ≤ H₂ := oTwoRes_le H₂
  have hH₂K : H₂ ≤ normalizer (K₂ : Set G) := le_normalizer_oTwoRes H₂
  have hH₂R : H₂ ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 H₂
  have hRK : R ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => inf_normalizer_le_normalizer_inf ⟨hH₂R (hK₂H hk), le_normalizer hk⟩)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 H₂).to_le inf_le_left)
  have hcen : K₂ ≤ centralizer (R : Set G) := by
    intro k hk
    rw [mem_centralizer_iff]
    intro r hr
    have hc1 : r * k * r⁻¹ * k⁻¹ ∈ R := by
      have h1 : k * r⁻¹ * k⁻¹ ∈ R := (mem_normalizer_iff.mp (hH₂R (hK₂H hk)) _).mp (inv_mem hr)
      have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem hr h1
    have hc2 : r * k * r⁻¹ * k⁻¹ ∈ K₂ :=
      mul_mem ((mem_normalizer_iff.mp (hH₂K (LieType.BorelTits.pCoreOf_le 2 H₂ hr)) k).mp hk)
        (inv_mem hk)
    have h1 := hRK (mem_inf.2 ⟨hc1, hc2⟩)
    rw [hbot, mem_bot] at h1
    calc r * k = r * k * r⁻¹ * k⁻¹ * (k * r) := by group
      _ = k * r := by rw [h1, one_mul]
  have hK₂R : K₂ ≤ R := fun k hk => hchar (mem_inf.2 ⟨hK₂H hk, hcen hk⟩)
  have hK₂bot : K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have h1 := hRK (mem_inf.2 ⟨hK₂R hk, hk⟩)
    rwa [hbot] at h1
  apply A.ne_T
  refine le_antisymm ((le_oTwoRes_sup_of_isSylowTwoOf A.isSylowTwoOf).trans ?_) A.T_le
  rw [← hK₂, hK₂bot, bot_sup_eq]

end Side

theorem false_of_ii_ii {S : A6.Setting134 G T L V} {a b : G} {Ha Hb : Subgroup G}
    (A : SideII S a Ha) (B : SideII S b Hb) (hab : a ≠ b) : False :=
  A.side.ne_of_ne B.side hab (B.uniq Ha A.side.star (by
    rw [B.nj, ← A.nj]
    exact le_sup_left))

theorem false_of_i_i {S : A6.Setting134 G T L V} {a b : G} {Ha Hb : Subgroup G}
    (A : SideI S a Ha) (B : SideI S b Hb) (hab : a ≠ b) : False := by
  apply hab
  have h := (A.psi A.side.zV1.1).trans (B.psi B.side.zV1.1).symm
  exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))

theorem false_of_i_ii (h1347 : U3.Stmt13_4_7One) {S : A6.Setting134 G T L V}
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4) {a b : G} {Ha Hb : Subgroup G}
    (A : SideI S a Ha) (B : SideII S b Hb) (hab : a ≠ b) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Ha ≠ Hb := A.side.ne_of_ne B.side hab
  have hL1 : InH T (Ha ⊔ Hb) → ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ Ha ⊔ Hb := fun hInH hle =>
    A.bad (Ha ⊔ Hb) hInH (A.side.eq_sup ▸ sup_le hle le_sup_left) b B.side.zV1 B.side.zL
      hab.symm Hb B.side.T_le le_sup_right B.side.le_Gz B.side.star.2.1
  have hcent : InH T (Ha ⊔ Hb) →
      ((Ha ⊔ Hb) ⊓ centralizer (U3.cZ T (oTwoRes Ha) : Set G) ≤
          normalizer (oTwoRes Ha : Set G) ∧
        (Ha ⊔ Hb) ⊓ centralizer (U3.cZ T (oTwoRes Hb) : Set G) ≤
          normalizer (oTwoRes Hb : Set G)) ∧
      (oTwoRes Ha = oThreePrimeResidual ((Ha ⊔ Hb) ⊓
          centralizer (U3.cZ T (oTwoRes Ha) : Set G)) ∨
        oTwoRes Hb = oThreePrimeResidual ((Ha ⊔ Hb) ⊓
          centralizer (U3.cZ T (oTwoRes Hb) : Set G))) := by
    intro hInH
    rw [A.side.inf_cZ_eq le_sup_left (hL1 hInH), B.side.inf_cZ_eq le_sup_right (hL1 hInH)]
    refine ⟨⟨le_normalizer_oTwoRes _, le_normalizer_oTwoRes _⟩, Or.inl ?_⟩
    rw [oThree_eq_oTwoRes S.h13.sylow.1 A.side.T_le
      (U3.s1347_relIndex_three S A.side.T_le A.side.quot)]
  have hyp : U3.Hyp1347 T Ha Hb :=
    { inH₁ := A.side.star.1
      inH₂ := B.side.star.1
      ne := hne
      s3₁ := A.side.quot
      s3₂ := B.side.quot
      chief := Or.inl A.chief
      index₁ := by rw [hZ4, A.side.card_cZ]
      index₂ := by rw [hZ4, B.side.card_cZ]
      cent := hcent }
  obtain ⟨-, -, -, -, -, -, -, hcases⟩ := h1347 G T L V S Ha Hb hyp
  have hJ : Ha ⊔ Hb ≤ normalizer (thompsonJ T : Set G) → False := fun h =>
    hne (B.uniq Ha A.side.star (by rw [B.nj]; exact le_sup_left.trans h))
  rcases hcases with hi | hii | hiii | hiv
  ·
    obtain ⟨-, hcomm, -⟩ := hi
    obtain ⟨-, hcomm2, -⟩ := A.concl
    rw [U3.s134_oTwoRes_L2T S] at hcomm2
    have hTN : T ≤ normalizer (oTwoRes Ha : Set G) :=
      A.side.T_le.trans (le_normalizer_oTwoRes Ha)
    have hNJN : Hb ⊔ (U3.l2Of S ⊔ T) ≤ normalizer (oTwoRes Ha : Set G) :=
      sup_le ((le_oTwoRes_sup_of_isSylowTwoOf B.side.isSylowTwoOf).trans
          (sup_le (le_normalizer_of_comm hcomm) hTN))
        (sup_le (le_normalizer_of_comm hcomm2) hTN)
    have hloc : IsTwoLocal (normalizer (pCoreOf 2 (oTwoRes Ha) : Set G)) :=
      ⟨_, A.side.pCoreOf_oTwoRes_ne_bot, LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have heq := B.inM.1.2 _ hloc
      (hNJN.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    have hKa : oTwoRes Ha ≤ Hb ⊔ (U3.l2Of S ⊔ T) := by
      rw [← heq]
      exact le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    exact hne (B.uniq Ha A.side.star ((le_oTwoRes_sup_of_isSylowTwoOf A.side.isSylowTwoOf).trans
      (sup_le hKa (le_sup_right.trans le_sup_right))))
  · obtain ⟨-, -, -, -, -, -, hJ', -⟩ := hii
    exact hJ hJ'
  · obtain ⟨-, -, -, hJ'⟩ := hiii
    exact hJ hJ'
  · obtain ⟨-, -, -, -, hJ', -⟩ := hiv
    rw [← thompsonJ_eq_thompsonJi_zero] at hJ'
    exact hJ hJ'

end CFSG.Quasithin.H13.NQS134
