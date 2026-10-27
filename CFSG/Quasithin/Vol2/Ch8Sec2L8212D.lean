module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8212C
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212D

variable {G : Type} [Group G] [Finite G]

theorem structure_E_82 {T L V : Subgroup G} {z : G} {e : ℕ} [hc : IsMulCommutative ↥V]
    (hT : quasithinIsSylowTwo T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ L)
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V) (hV : IsElemAbelian 2 V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hTCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hzV : z ∈ V)
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) (hz2 : z ^ 2 = 1) (he : 1 ≤ e)
    (hchar : Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hWc : Nat.card ↥(vz82 (autOn L V) ⟨z, hzV⟩) = 2 ^ (e + 1))
    (hRc : Nat.card ↥(radz82 (autOn L V) ⟨z, hzV⟩) = 2 ^ e)
    (hRP : ⁅radz82 (autOn L V) ⟨z, hzV⟩, parz82 (autOn L V) ⟨z, hzV⟩⁆ =
      radz82 (autOn L V) ⟨z, hzV⟩)
    (hmin : ∀ N : Subgroup (MulAut ↥V), N ≤ radz82 (autOn L V) ⟨z, hzV⟩ → N ≠ ⊥ →
      parz82 (autOn L V) ⟨z, hzV⟩ ≤ Subgroup.normalizer (N : Set (MulAut ↥V)) →
        N = radz82 (autOn L V) ⟨z, hzV⟩)
    (hirr : ∀ Y : Subgroup ↥V, Subgroup.zpowers (⟨z, hzV⟩ : ↥V) < Y →
      Y ≤ vz82 (autOn L V) ⟨z, hzV⟩ → parz82 (autOn L V) ⟨z, hzV⟩ ≤ stabSub Y →
        Y = vz82 (autOn L V) ⟨z, hzV⟩)
    (hfixW : vz82 (autOn L V) ⟨z, hzV⟩ ⊓ fixV (radz82 (autOn L V) ⟨z, hzV⟩) =
      Subgroup.zpowers (⟨z, hzV⟩ : ↥V))
    (hVP : commV (parz82 (autOn L V) ⟨z, hzV⟩) = ⊤)
    (hcoc : ∀ δ : MulAut ↥V → ↥V,
      (∀ g ∈ autOn L V, ∀ k ∈ autOn L V, δ (g * k) = δ g * g (δ k)) →
      (∀ r ∈ radz82 (autOn L V) ⟨z, hzV⟩, δ r ∈ Subgroup.zpowers (⟨z, hzV⟩ : ↥V)) →
      ∃ w ∈ vz82 (autOn L V) ⟨z, hzV⟩, ∀ g ∈ autOn L V, δ g = w * (g w)⁻¹)
    (h11 : pCoreOf 2 (autOn (ch8Lz L z ⊔ T) V) = pCoreOf 2 (autOn (ch8Lz L z) V))
    (hEV : ¬ ch8E V L z ≤ Subgroup.centralizer (V : Set G)) :
    ch8E V L z = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      pCoreOf 2 (ch8Lz L z) = ch8E V L z ⊔ V ∧ ch8Vz V L z = ch8E V L z ⊓ V ∧
      (∀ x ∈ ch8E V L z, ∀ y ∈ ch8E V L z, ⁅x, y⁆ ∈ Subgroup.zpowers z) ∧
      (∀ x ∈ ch8E V L z, x ^ 2 ∈ Subgroup.zpowers z) ∧
      Nat.card ↥(ch8E V L z) = 2 ^ (2 * e + 1) ∧ Nat.card ↥(ch8Vz V L z) = 2 ^ (e + 1) ∧
      (∀ a ∈ ch8Vz V L z, a ∉ Subgroup.zpowers z → ∃ x ∈ ch8E V L z, ⁅a, x⁆ ≠ 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set Q := pCoreOf 2 C with hQdef
  set Lz := ch8Lz L z with hLzdef
  set R := pCoreOf 2 Lz with hRdef
  set Vz := ch8Vz V L z with hVzdef
  set E := ch8E V L z with hEdef
  set z' : ↥V := ⟨z, hzV⟩ with hz'def
  have hTp : IsPGroup 2 ↥T := hT.1
  have hVC' : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hc
  have hTC : T ≤ C := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT t ht)
  have hzC : ∀ c ∈ C, c * z = z * c := fun c hc' => Subgroup.mem_centralizer_singleton_iff.mp hc'
  have hVC : V ≤ C := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hVC' hv) z hzV).symm
  have hZc : ∀ ζ ∈ Subgroup.zpowers z, ∀ c ∈ C, c * ζ = ζ * c := by
    intro ζ hζ c hc'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
    exact Commute.zpow_right (hzC c hc') k
  have hLzLC : Lz ≤ L ⊓ C := perfectCore_le _
  have hLzL : Lz ≤ L := hLzLC.trans inf_le_left
  have hLzC : Lz ≤ C := hLzLC.trans inf_le_right
  have hLzN : Lz ≤ Subgroup.normalizer (V : Set G) := hLzL.trans hLN
  have hRLz : R ≤ Lz := CFSG.LieType.BorelTits.pCoreOf_le 2 Lz
  have hRL : R ≤ L := hRLz.trans hLzL
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRL.trans hLN
  have hRp : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lz
  have hLzR : Lz ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lz
  have hCN : ∀ X : Subgroup G, X ≤ C → X ≤ Subgroup.normalizer (C : Set G) := fun X hX =>
    hX.trans Subgroup.le_normalizer
  have hTLC : T ≤ Subgroup.normalizer ((L ⊓ C : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hTL ht) x,
      Subgroup.mem_normalizer_iff.mp (hCN T hTC ht) x]
  have hTLz : T ≤ Subgroup.normalizer (Lz : Set G) :=
    hTLC.trans (normalizer_le_normalizer_perfectCore _)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    hTLz.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lz)
  have hRT : R ≤ T := le_of_le_normalizer_82 hT hRp hTR
  have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hQC : Q ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hQT : Q ≤ T := le_of_le_normalizer_82 hT hQp (hTC.trans hCQ)
  have hVLz : V ≤ Subgroup.normalizer (Lz : Set G) :=
    ((le_inf hVL hVC).trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_perfectCore _)
  have hVR : V ≤ Subgroup.normalizer (R : Set G) :=
    hVLz.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lz)
  have hVzV : Vz ≤ V := by
    change ⁅V, R⁆ ≤ V
    rw [Subgroup.commutator_le]
    intro v hv r hr
    have h1 : r * v⁻¹ * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hRN hr) v⁻¹).mp (V.inv_mem hv)
    have := V.mul_mem hv h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  have hVzR : Vz ≤ R := by
    change ⁅V, R⁆ ≤ R
    rw [Subgroup.commutator_le]
    intro v hv r hr
    rw [commutatorElement_def]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVR hv) r).mp hr) (R.inv_mem hr)
  have hLzVz : Lz ≤ Subgroup.normalizer (Vz : Set G) := fun l hl =>
    mem_normalizer_commutator_82 (hLzN hl) (hLzR hl)
  have hTVz : T ≤ Subgroup.normalizer (Vz : Set G) := fun t ht =>
    mem_normalizer_commutator_82 (hTV ht) (hTR ht)
  have hCLzV : IsPGroup 2 ↥(Lz ⊓ Subgroup.centralizer (V : Set G)) :=
    (isPGroup_of_isElemAbelian_two hV).to_le
      ((inf_le_inf_right _ hLzL).trans hCLV.le)
  have hPbar : autOn Lz V = parz82 (autOn L V) z' := autOn_ch8Lz_82 hLN z'
  have hRbar : autOn R V = radz82 (autOn L V) z' := by
    rw [autOn_pCoreOf_82 hLzN hCLzV, hPbar]
    rfl
  have hWbar : vz82 (autOn L V) z' = Vz.subgroupOf V := by
    rw [vz82, ← hRbar, commV_autOn_82 hRN]
    rfl
  have hzVz : z ∈ Vz := by
    have h1 : z' ∈ vz82 (autOn L V) z' :=
      (hfixW.symm.le.trans inf_le_left) (Subgroup.mem_zpowers z')
    rw [hWbar, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hVzc : Nat.card ↥Vz = 2 ^ (e + 1) := by
    rw [← hWc, hWbar]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVzV).toEquiv).symm
  have hstep1 : ∀ v ∈ Vz, ∀ q ∈ Q, ⁅v, q⁆ ∈ Subgroup.zpowers z := by
    let Y : Subgroup ↥V :=
      { carrier := {v | (v : G) ∈ Vz ∧ ∀ q ∈ Q, ⁅(v : G), q⁆ ∈ Subgroup.zpowers z}
        one_mem' := ⟨Vz.one_mem, fun q _ => by
          rw [OneMemClass.coe_one, commutatorElement_one_left]
          exact Subgroup.one_mem _⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨Vz.mul_mem ha hb, fun q hq => ?_⟩
          have e1 : ⁅((a * b : ↥V) : G), q⁆ =
              (a : G) * ⁅(b : G), q⁆ * (a : G)⁻¹ * ⁅(a : G), q⁆ := by
            simp only [Subgroup.coe_mul, commutatorElement_def]
            group
          rw [e1, hZc _ (hb' q hq) a (hVC a.2), mul_inv_cancel_right]
          exact Subgroup.mul_mem _ (hb' q hq) (ha' q hq)
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨Vz.inv_mem ha, fun q hq => ?_⟩
          have e1 : ⁅((a⁻¹ : ↥V) : G), q⁆ = (a : G)⁻¹ * ⁅(a : G), q⁆⁻¹ * (a : G) := by
            simp only [Subgroup.coe_inv, commutatorElement_def]
            group
          rw [e1, mul_assoc, ← hZc _ (Subgroup.inv_mem _ (ha' q hq)) a (hVC a.2), ← mul_assoc,
            inv_mul_cancel, one_mul]
          exact Subgroup.inv_mem _ (ha' q hq) }
    have hY : ∀ v : ↥V, v ∈ Y ↔ (v : G) ∈ Vz ∧ ∀ q ∈ Q, ⁅(v : G), q⁆ ∈ Subgroup.zpowers z :=
      fun v => Iff.rfl
    have hzY : Subgroup.zpowers z' ≤ Y := by
      rw [Subgroup.zpowers_le, hY]
      refine ⟨hzVz, fun q hq => ?_⟩
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hzC q (hQC hq)).symm]
      exact Subgroup.one_mem _
    have hYW : Y ≤ vz82 (autOn L V) z' := by
      intro v hv
      rw [hWbar, Subgroup.mem_subgroupOf]
      exact ((hY v).mp hv).1
    have hzlt : Subgroup.zpowers z < Vz := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hzVz) fun h => ?_
      have h1 : Nat.card ↥(Subgroup.zpowers z) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) hz2
      rw [h, hVzc] at h1
      have : 2 ^ 2 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨n, hnVz, hnz, hnT⟩ :=
      exists_mem_center_mod_82 hTp (hVzV.trans hVT) hTVz hzT hzlt
    have hnY : (⟨n, hVzV hnVz⟩ : ↥V) ∈ Y :=
      (hY _).mpr ⟨hnVz, fun q hq => hnT q (hQT hq)⟩
    have hYne : Subgroup.zpowers z' < Y := by
      refine lt_of_le_of_ne hzY fun h => hnz ?_
      rw [← h] at hnY
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnY
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_zpow] at this
      rw [← this]
      exact Subgroup.zpow_mem_zpowers z k
    have hPY : parz82 (autOn L V) z' ≤ stabSub Y := by
      rw [← hPbar]
      rintro _ ⟨l, hl, rfl⟩
      have hl' : (l : G) ∈ Lz := hl
      rw [mem_stabSub]
      intro u
      rw [hY, hY, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
      have hlC : (l : G) ∈ C := hLzC hl'
      constructor
      · rintro ⟨hu1, hu2⟩
        refine ⟨?_, fun q hq => ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLzVz hl')) _).mp hu1
          simpa [mul_assoc] using this
        · have hq' : (l : G) * q * (l : G)⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp (hCQ hlC) q).mp hq
          have h1 := hu2 _ hq'
          have e1 : ⁅(l : G) * u * (l : G)⁻¹, (l : G) * q * (l : G)⁻¹⁆ =
              (l : G) * ⁅(u : G), q⁆ * (l : G)⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e1] at h1
          have e2 : ⁅(u : G), q⁆ = (l : G)⁻¹ * ((l : G) * ⁅(u : G), q⁆ * (l : G)⁻¹) * l := by
            group
          rw [e2]
          have := hZc _ h1 _ (C.inv_mem hlC)
          rw [this, mul_assoc, inv_mul_cancel, mul_one]
          exact h1
      · rintro ⟨hu1, hu2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hLzVz hl') _).mp hu1, fun q hq => ?_⟩
        have hq' : (l : G)⁻¹ * q * l ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCQ hlC)) q).mp hq
          simpa using this
        have h1 := hu2 _ hq'
        have e1 : ⁅(l : G) * u * (l : G)⁻¹, q⁆ =
            (l : G) * ⁅(u : G), (l : G)⁻¹ * q * l⁆ * (l : G)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e1, hZc _ h1 _ hlC, mul_inv_cancel_right]
        exact h1
    have hYeq := hirr Y hYne hYW hPY
    intro v hv q hq
    have hvY : (⟨v, hVzV hv⟩ : ↥V) ∈ Y := by
      rw [hYeq, hWbar, Subgroup.mem_subgroupOf]
      exact hv
    exact ((hY _).mp hvY).2 q hq
  have hVzQ : Vz ≤ Q := fun v hv =>
    mem_pCoreOf_of_commutator_82 hz2 hzC hchar (hVC (hVzV hv)) (hstep1 v hv)
  let Q0 : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ Subgroup.zpowers z}
      one_mem' := ⟨Q.one_mem, fun q _ => by
        rw [commutatorElement_one_left]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Q.mul_mem ha hb, fun q hq => ?_⟩
        have e1 : ⁅a * b, q⁆ = a * ⁅b, q⁆ * a⁻¹ * ⁅a, q⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e1, hZc _ (hb' q hq) a (hQC ha), mul_inv_cancel_right]
        exact Subgroup.mul_mem _ (hb' q hq) (ha' q hq)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Q.inv_mem ha, fun q hq => ?_⟩
        have e1 : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e1, mul_assoc, ← hZc _ (Subgroup.inv_mem _ (ha' q hq)) a (hQC ha), ← mul_assoc,
          inv_mul_cancel, one_mul]
        exact Subgroup.inv_mem _ (ha' q hq) }
  have hEQ0 : E ≤ Q0 := by
    refine conjClosure_le fun c hc' x hx => ⟨?_, fun q hq => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hCQ hc') x).mp (hVzQ hx)
    · have hq' : c⁻¹ * q * c ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCQ hc')) q).mp hq
        simpa using this
      have e1 : ⁅c * x * c⁻¹, q⁆ = c * ⁅x, c⁻¹ * q * c⁆ * c⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1, hZc _ (hstep1 x hx _ hq') c hc', mul_inv_cancel_right]
      exact hstep1 x hx _ hq'
  have hEQ : E ≤ Q := fun x hx => (hEQ0 hx).1
  have hEQz : ∀ x ∈ E, ∀ q ∈ Q, ⁅x, q⁆ ∈ Subgroup.zpowers z := fun x hx => (hEQ0 hx).2
  have hET : E ≤ T := hEQ.trans hQT
  have hEN : E ≤ Subgroup.normalizer (V : Set G) := hET.trans hTV
  have hCE : C ≤ Subgroup.normalizer (E : Set G) := le_normalizer_conjClosure Vz C
  have hLzTE : Lz ⊔ T ≤ Subgroup.normalizer (E : Set G) := sup_le (hLzC.trans hCE) (hTC.trans hCE)
  have hEp : IsPGroup 2 ↥E := hTp.to_le hET
  have hEbarO : autOn E V ≤ pCoreOf 2 (autOn (Lz ⊔ T) V) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono fun x hx => (le_sup_right : T ≤ Lz ⊔ T) (hET hx))
      (autOn_le_normalizer_82 hLzTE) ?_
    have h1 : IsPGroup 2 ↥(E.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
    exact h1.map _
  have hO2Lz : pCoreOf 2 (autOn Lz V) = radz82 (autOn L V) z' := by
    rw [← autOn_pCoreOf_82 hLzN hCLzV]
    exact hRbar
  have hEbarR : autOn E V ≤ radz82 (autOn L V) z' := by
    rw [← hO2Lz, ← h11]
    exact hEbarO
  have hEbar1 : autOn E V ≠ ⊥ := by
    intro h
    apply hEV
    intro x hx
    have h1 : conjAct V ⟨x, hEN hx⟩ ∈ autOn E V := ⟨_, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (conjAct_eq_one_iff_82 _).mp h1
  have hEbarP : parz82 (autOn L V) z' ≤
      Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) := by
    rw [← hPbar]
    exact autOn_le_normalizer_82 (hLzC.trans hCE)
  have hEbar : autOn E V = radz82 (autOn L V) z' := hmin _ hEbarR hEbar1 hEbarP
  have hQMab : ∀ x y : G, x ∈ T ⊓ Subgroup.centralizer (V : Set G) →
      y ∈ T ⊓ Subgroup.centralizer (V : Set G) → x * y = y * x := fun x y hx hy =>
    commute_of_inf_centralizer_82 hTL hLN hCLV hVC' hTCL hx hy
  have hstep4 : ∀ x ∈ T ⊓ Subgroup.centralizer (V : Set G), x ∈ Q → x ∈ Vz := by
    intro x hx hxQ
    have hxR : ∀ ρ ∈ R, ⁅x, ρ⁆ ∈ Subgroup.zpowers z := by
      intro ρ hρ
      have h1 : conjAct V ⟨ρ, hRN hρ⟩ ∈ autOn E V := by
        rw [hEbar, ← hRbar]
        exact ⟨_, hρ, rfl⟩
      obtain ⟨e', he', he'ρ⟩ := h1
      have he'E : (e' : G) ∈ E := he'
      have hqM : (e' : G)⁻¹ * ρ ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
        refine ⟨T.mul_mem (T.inv_mem (hET he'E)) (hRT hρ), ?_⟩
        have h2 : conjAct V (e'⁻¹ * ⟨ρ, hRN hρ⟩) = 1 := by
          rw [map_mul, map_inv, he'ρ, inv_mul_cancel]
        exact (conjAct_eq_one_iff_82 _).mp h2
      have hxq := hQMab x _ hx hqM
      set q := (e' : G)⁻¹ * ρ with hqdef
      have hqx' : q * x⁻¹ = x⁻¹ * q := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hxq, inv_mul_cancel_left]
      have hρ' : ρ = (e' : G) * q := by
        rw [hqdef]
        group
      have e1 : ⁅x, ρ⁆ = ⁅x, (e' : G)⁆ := by
        rw [hρ', commutatorElement_def, commutatorElement_def]
        calc x * (↑e' * q) * x⁻¹ * (↑e' * q)⁻¹ = x * ↑e' * (q * x⁻¹) * q⁻¹ * (↑e')⁻¹ := by
              group
          _ = x * ↑e' * (x⁻¹ * q) * q⁻¹ * (↑e')⁻¹ := by rw [hqx']
          _ = x * ↑e' * x⁻¹ * (↑e')⁻¹ := by group
      rw [e1, ← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hEQz _ he'E x hxQ)
    have hcoc' : ∀ δ : MulAut ↥V → ↥V,
        (∀ g ∈ autOn L V, ∀ k ∈ autOn L V, δ (g * k) = δ g * g (δ k)) →
        (∀ r ∈ autOn R V, δ r ∈ Subgroup.zpowers z') →
        ∃ w ∈ vz82 (autOn L V) z', ∀ g ∈ autOn L V, δ g = w * (g w)⁻¹ := by
      intro δ h1 h2
      refine hcoc δ h1 ?_
      rw [← hRbar]
      exact h2
    obtain ⟨w, hwW, hxw⟩ := mem_of_deriv_82 hTL hLN hCLV hTCL hVT hRL hcoc' hx hxR
    rw [hWbar, Subgroup.mem_subgroupOf] at hwW
    rw [hxw]
    exact hwW
  have hEcV : E ⊓ Subgroup.centralizer (V : Set G) ≤ Vz := fun x hx =>
    hstep4 x ⟨hET hx.1, hx.2⟩ (hEQ hx.1)
  have hVzE : Vz ≤ E := le_conjClosure Vz C
  have hEcVeq : E ⊓ Subgroup.centralizer (V : Set G) = Vz :=
    le_antisymm hEcV (le_inf hVzE (hVzV.trans hVC'))
  have hVzEV : Vz = E ⊓ V :=
    le_antisymm (le_inf hVzE hVzV) fun x hx => hEcV ⟨hx.1, hVC' hx.2⟩
  have hVLzR : V ⊓ Lz ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((isPGroup_of_isElemAbelian_two hV).to_le inf_le_left)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hLzN hl) x,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) x]
  have hmemR : ∀ (l : G) (hl : l ∈ Lz) (ρ : G) (hρ : ρ ∈ R),
      conjAct V ⟨l, hLzN hl⟩ = conjAct V ⟨ρ, hRN hρ⟩ → l ∈ R := by
    intro l hl ρ hρ he'
    have h2 : conjAct V (⟨ρ, hRN hρ⟩⁻¹ * ⟨l, hLzN hl⟩) = 1 := by
      rw [map_mul, map_inv, he', inv_mul_cancel]
    have h1 : ρ⁻¹ * l ∈ V ⊓ Lz :=
      ⟨hCLV.le ⟨L.mul_mem (L.inv_mem (hRL hρ)) (hLzL hl), (conjAct_eq_one_iff_82 _).mp h2⟩,
        Lz.mul_mem (Lz.inv_mem (hRLz hρ)) hl⟩
    have h3 : l = ρ * (ρ⁻¹ * l) := by group
    rw [h3]
    exact R.mul_mem hρ (hVLzR h1)
  have hRnorm : parz82 (autOn L V) z' ≤
      Subgroup.normalizer (radz82 (autOn L V) z' : Set (MulAut ↥V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hELz : ⁅E, Lz⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have h1 : ⁅x, l⁆ ∈ Lz := by
      rw [commutatorElement_def]
      exact Lz.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTLz (hET hx)) l).mp hl) (Lz.inv_mem hl)
    have hxbar : conjAct V ⟨x, hEN hx⟩ ∈ radz82 (autOn L V) z' := by
      rw [← hEbar]
      exact ⟨_, hx, rfl⟩
    have hlbar : conjAct V ⟨l, hLzN hl⟩ ∈ parz82 (autOn L V) z' := by
      rw [← hPbar]
      exact ⟨_, hl, rfl⟩
    have h2 : conjAct V ⟨⁅x, l⁆, hLzN h1⟩ ∈ radz82 (autOn L V) z' := by
      have e1 : (⟨⁅x, l⁆, hLzN h1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hEN hx⟩ * (⟨l, hLzN hl⟩ * ⟨x, hEN hx⟩⁻¹ * ⟨l, hLzN hl⟩⁻¹) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (radz82 _ _).mul_mem hxbar ((Subgroup.mem_normalizer_iff.mp (hRnorm hlbar) _).mp
        ((radz82 _ _).inv_mem hxbar))
    rw [← hRbar] at h2
    obtain ⟨ρ, hρ, hρe⟩ := h2
    exact hmemR _ h1 _ hρ hρe.symm
  have hELzE : ⁅E, Lz⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    rw [commutatorElement_def]
    have h1 : l * x⁻¹ * l⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hLzC.trans hCE hl) x⁻¹).mp (E.inv_mem hx)
    have := E.mul_mem hx h1
    simpa [mul_assoc] using this
  have hER : E ≤ R := by
    intro x hx
    have hxbar : conjAct V ⟨x, hEN hx⟩ ∈ autOn ⁅E, Lz⁆ V := by
      rw [autOn_commutator_82 hEN hLzN, hEbar, hPbar, hRP, ← hEbar]
      exact ⟨_, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hxbar
    have hy' : (y : G) ∈ ⁅E, Lz⁆ := hy
    have hyE : (y : G) ∈ E := hELzE hy'
    have h2 : conjAct V (y⁻¹ * ⟨x, hEN hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h1 : (y : G)⁻¹ * x ∈ E ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨E.mul_mem (E.inv_mem hyE) hx, (conjAct_eq_one_iff_82 _).mp h2⟩
    have h3 : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [h3]
    exact R.mul_mem (hELz hy') (hVzR (hEcV h1))
  have hVLzc : V ≤ ⁅V, Lz⁆ := by
    have h1 : commV (autOn Lz V) = ⊤ := by
      rw [hPbar]
      exact hVP
    rw [commV_autOn_82 hLzN] at h1
    intro v hv
    have : (⟨v, hv⟩ : ↥V) ∈ (⁅V, Lz⁆).subgroupOf V := by
      rw [h1]
      exact Subgroup.mem_top _
    exact this
  have hVLz' : V ≤ Lz := by
    refine hVLzc.trans ?_
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact Lz.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVLz hv) l).mp hl) (Lz.inv_mem hl)
  have hVR' : V ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVLz' hLzN
      (isPGroup_of_isElemAbelian_two hV)
  have hREV : R = E ⊔ V := by
    apply le_antisymm
    · intro ρ hρ
      have h1 : conjAct V ⟨ρ, hRN hρ⟩ ∈ autOn E V := by
        rw [hEbar, ← hRbar]
        exact ⟨_, hρ, rfl⟩
      obtain ⟨x, hx, hxρ⟩ := h1
      have hx' : (x : G) ∈ E := hx
      have h2 : conjAct V (x⁻¹ * ⟨ρ, hRN hρ⟩) = 1 := by rw [map_mul, map_inv, hxρ, inv_mul_cancel]
      have h3 : (x : G)⁻¹ * ρ ∈ V :=
        hCLV.le ⟨L.mul_mem (L.inv_mem (hRL (hER hx'))) (hRL hρ), (conjAct_eq_one_iff_82 _).mp h2⟩
      have h4 : ρ = (x : G) * ((x : G)⁻¹ * ρ) := by group
      rw [h4]
      exact Subgroup.mul_mem_sup hx' h3
    · exact sup_le hER hVR'
  have hEQeq : E = Q := by
    apply le_antisymm hEQ
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := hTV (hQT hq)
    have hQle : autOn Q V ≤ autOn (Lz ⊔ T) V :=
      Subgroup.map_mono fun y (hy : (y : G) ∈ Q) => (le_sup_right : T ≤ Lz ⊔ T) (hQT hy)
    have h2 : IsPGroup 2 ↥(Q.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe (hQT.trans hTV)).symm
    have hQO : autOn Q V ≤ pCoreOf 2 (autOn (Lz ⊔ T) V) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQle
        (autOn_le_normalizer_82 (sup_le (hLzC.trans hCQ) (hTC.trans hCQ))) (h2.map _)
    have h1 : conjAct V ⟨q, hqN⟩ ∈ pCoreOf 2 (autOn (Lz ⊔ T) V) := hQO ⟨⟨q, hqN⟩, hq, rfl⟩
    rw [h11, hO2Lz, ← hEbar] at h1
    obtain ⟨x, hx, hxq⟩ := h1
    have hx' : (x : G) ∈ E := hx
    have h2' : conjAct V (x⁻¹ * ⟨q, hqN⟩) = 1 := by rw [map_mul, map_inv, hxq, inv_mul_cancel]
    have h3 : (x : G)⁻¹ * q ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨T.mul_mem (T.inv_mem (hET hx')) (hQT hq), (conjAct_eq_one_iff_82 _).mp h2'⟩
    have h4 := hstep4 _ h3 (Q.mul_mem (Q.inv_mem (hEQ hx')) hq)
    have h5 : q = (x : G) * ((x : G)⁻¹ * q) := by group
    rw [h5]
    exact E.mul_mem hx' (hVzE h4)
  have hEc : Nat.card ↥E = 2 ^ (2 * e + 1) := by
    have h1 := card_autOn_mul_82 hEN
    rw [hEbar, hRc, hEcVeq, hVzc] at h1
    rw [← h1, ← pow_add]
    congr 1
    omega
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z := fun x hx y hy =>
    hEQz x hx y (hEQ hy)
  have hsqE : ∀ x ∈ E, x ^ 2 ∈ Subgroup.zpowers z := by
    let S2 : Subgroup G :=
      { carrier := {x | x ∈ E ∧ x ^ 2 ∈ Subgroup.zpowers z}
        one_mem' := ⟨E.one_mem, by rw [one_pow]; exact Subgroup.one_mem _⟩
        mul_mem' := by
          rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
          refine ⟨E.mul_mem hx hy, ?_⟩
          have hc' := hcommE _ (E.inv_mem hy) _ (E.inv_mem hx)
          have hcy : ⁅y⁻¹, x⁻¹⁆ * y = y * ⁅y⁻¹, x⁻¹⁆ :=
            (hZc _ hc' y (hQC (hEQ hy))).symm
          have e1 : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅y⁻¹, x⁻¹⁆ := by
            rw [sq, sq, sq]
            calc x * y * (x * y) = x * (y * x) * y := by group
              _ = x * (x * y * ⁅y⁻¹, x⁻¹⁆) * y := by
                rw [commutatorElement_def]
                group
              _ = x * x * y * (⁅y⁻¹, x⁻¹⁆ * y) := by group
              _ = x * x * y * (y * ⁅y⁻¹, x⁻¹⁆) := by rw [hcy]
              _ = x * x * (y * y) * ⁅y⁻¹, x⁻¹⁆ := by group
          rw [e1]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx2 hy2) hc'
        inv_mem' := by
          rintro x ⟨hx, hx2⟩
          refine ⟨E.inv_mem hx, ?_⟩
          rw [inv_pow]
          exact Subgroup.inv_mem _ hx2 }
    have hES2 : E ≤ S2 := by
      refine conjClosure_le fun c hc' v hv => ⟨mem_conjClosure hc' hv, ?_⟩
      have hv2 : v ^ 2 = 1 := hV.2 v (hVzV hv)
      have e1 : (c * v * c⁻¹) ^ 2 = c * v ^ 2 * c⁻¹ := by
        rw [sq, sq]
        group
      rw [e1, hv2, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact fun x hx => (hES2 hx).2
  have hnc : ∀ a ∈ Vz, a ∉ Subgroup.zpowers z → ∃ x ∈ E, ⁅a, x⁆ ≠ 1 := by
    intro a ha haz
    have ha' : (⟨a, hVzV ha⟩ : ↥V) ∈ vz82 (autOn L V) z' := by
      rw [hWbar, Subgroup.mem_subgroupOf]
      exact ha
    have hnf : (⟨a, hVzV ha⟩ : ↥V) ∉ fixV (radz82 (autOn L V) z') := by
      intro hf
      have h1 : (⟨a, hVzV ha⟩ : ↥V) ∈ Subgroup.zpowers z' := by
        rw [← hfixW]
        exact ⟨ha', hf⟩
      apply haz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have h2 := congrArg Subtype.val hk
      simp only [Subgroup.coe_zpow] at h2
      rw [← h2]
      exact Subgroup.zpow_mem_zpowers z k
    rw [mem_fixV] at hnf
    push Not at hnf
    obtain ⟨r, hr, hra⟩ := hnf
    rw [← hEbar] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    refine ⟨x, hx, fun h1 => hra ?_⟩
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    show (x : G) * a * (x : G)⁻¹ = a
    rw [← h1, mul_inv_cancel_right]
  exact ⟨hEQeq, hREV, hVzEV, hcommE, hsqE, hEc, hVzc, hnc⟩

end L8212D

end CFSG.Quasithin.H13
