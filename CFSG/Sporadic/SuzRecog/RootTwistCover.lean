module

public import CFSG.Sporadic.SuzRecog.RootTwistCentre
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverMaps
public import CFSG.Sporadic.SuzRecog.LevelTwoCover
public import CFSG.Sporadic.SuzRecog.Rigid
public import Certificates.Certificate15090
public import Certificates.Certificate15112
public import Certificates.Certificate15113
public import Certificates.Certificate2289
public import Certificates.Certificate2293
public import Certificates.Certificate2296
public import Certificates.Certificate2297
public import Certificates.Certificate2298
public import Certificates.Certificate2299
public import Certificates.Certificate2300
public import Certificates.Certificate2301
public import Certificates.Certificate2302
public import Certificates.Certificate2305
public import Certificates.Certificate2306
public import Certificates.Certificate3173

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.RootTwist

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.RootTwistCheck
  CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.ModelGroups CFSG.Sporadic.SuzRecog.LevelTwoCover

attribute [local irreducible] LevelTwo.nbr nbrC LevelTwo.vtab LevelTwo.vtabs LevelTwo.aPts
  LevelTwo.wPts LevelTwo.trips LevelTwo.aIdx LevelTwo.vIdx LevelTwo.p1 LevelTwo.elPq LevelTwo.elQp
  hEl uEl sheetAt liftAt0 xTwArr yTwArr

local notation "Pm" => Equiv.Perm (Fin 1782)

local notation "P₂" => Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)

theorem squareOK_parts {v : ℕ} {m : Array ℕ} (h : squareOK v m = true) :
    LevelTwo.pElemOK (hEl v) 2835 v = true ∧ LevelTwo.elemOK (uEl v).1 (uEl v).2 = true ∧
      LevelTwo.sendsB (uEl v).1 (uEl v).2 0 LevelTwo.p1 = true ∧
      LevelTwo.sendsB (uEl v).1 (uEl v).2 2835 v = true ∧
      plusB (conjInvA (hEl v) m) = true ∧ plusB (conjInvA (uEl v) m) = true := by
  simp only [squareOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem sheetOK_parts {v : ℕ} (h : sheetOK v = true) :
    listedAt0 v = true ∧ sheetAt (liftAt0 v) < 3 ∧
      ElimCert.adjB nbrC (LevelTwo.p1 + 2997 * sheetAt (liftAt0 v)) (liftAt0 v) = true := by
  simp only [sheetOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem transOK_parts :
    squareOK 2970 xTwArr = true ∧ squareOK 2890 yTwArr = true := by
  have h := trans_check
  simp only [transOK, Bool.and_eq_true] at h
  exact h

theorem holOK_parts : sheetOK 2970 = true ∧ sheetOK 2890 = true ∧
    sheetAt (liftAt0 2970) ≠ sheetAt (liftAt0 2890) := by
  have h := hol_check
  simp only [holOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem isInvA_of_elemOK {g gi : Array ℕ} (h : LevelTwo.elemOK g gi = true) :
    isInvA 1782 g gi = true := by
  simp only [LevelTwo.elemOK, Bool.and_eq_true] at h
  exact h.1

theorem rep_conjInvA {g : LevelTwo.Elt} (hg : isInvA 1782 g.1 g.2 = true) {a : Array ℕ}
    {A : Pm} (ha : Rep 1782 a A) :
    Rep 1782 (conjInvA g a) ((permC 1782 g.1)⁻¹ * A * permC 1782 g.1) := by
  rw [mul_assoc]
  exact rep_compA (rep_permC hg).2 (rep_compA ha (rep_permC hg).1)

theorem mem_B0Plus_of_plusB
    {m : Array ℕ} {g : Pm} (hm : Rep 1782 m g) (hM : g ∈ suzM)
    (h : plusB m = true) : g ∈ B0Plus := by
  simp only [plusB, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hc, hn⟩, he⟩ := h
  have hw1 : Rep 1782 w0RArr (rho1 * w0 * rho1⁻¹) := rep_conjA rep_rho1 LevelTwo.rep_w0
  refine mem_inf.2 ⟨mem_inf.2 ⟨mem_invE_one_iff.2 ⟨(commA_iff hm rep_t1).1 hc, hM⟩,
    mem_normalizer_of_normV LevelTwo.rep_w0 hm hn⟩, ?_⟩
  have key : ∀ a : ℕ, evenAt m a = true →
      g ∈ centralizer (R0 : Set Pm) ⊔ zpowers rho1 := by
    intro a ha
    simp only [evenAt, Bool.and_eq_true] at ha
    have hr := rep_compA hm (rep_powA (rep_invCand rep_rho1) a)
    have hC : g * rho1⁻¹ ^ a ∈ centralizer (R0 : Set Pm) := by
      rw [R0, centralizer_closure, mem_centralizer_iff]
      rintro z (rfl | rfl)
      · exact ((commA_iff hr LevelTwo.rep_w0).1 ha.1).symm
      · exact ((commA_iff hr hw1).1 ha.2).symm
    have e : g = g * rho1⁻¹ ^ a * rho1 ^ a := by
      rw [mul_assoc, inv_pow, inv_mul_cancel, mul_one]
    rw [e]
    exact mul_mem (mem_sup_left hC) (mem_sup_right (pow_mem (mem_zpowers _) a))
  rcases he with (he | he) | he
  · exact key 0 he
  · exact key 1 he
  · exact key 2 he

theorem B0Plus_le_invE {x : Pm} (h : x ∈ B0Plus) : x ∈ invE 1 :=
  (mem_inf.1 (mem_inf.1 h).1).1

theorem B0Plus_le_NR0
    {x : Pm} (h : x ∈ B0Plus) : x ∈ Model.NR0 :=
  mem_inf.2 ⟨(invE_le_centM (by norm_num) (B0Plus_le_invE h)).2, (mem_inf.1 (mem_inf.1 h).1).2⟩

theorem conj_t1_eq
    {u : LevelTwo.Elt} (hu : LevelTwo.elemOK u.1 u.2 = true)
    (h : LevelTwo.sendsB u.1 u.2 0 LevelTwo.p1 = true) :
    permC 1782 u.1 * suzInv 1 * (permC 1782 u.1)⁻¹ = aPrime := by
  obtain ⟨hv', e⟩ := LevelTwo.eltG_smul hu (v := 0) (by norm_num) h
  have hs := LevelTwo.smul_spec (LevelTwo.eltG u.1 u.2 hu) ⟨0, by norm_num⟩
  rw [e] at hs
  change LevelTwo.vset LevelTwo.p1 = LevelTwo.conjSet (permC 1782 u.1) (LevelTwo.vset 0) at hs
  have h0 : LevelTwo.vset 0 = {suzInv 1} := LevelTwo.vset_pV
  have h1 : LevelTwo.vset LevelTwo.p1 = {LevelTwo.aP LevelTwo.p1} := LevelTwo.vset_p1V
  rw [h0, h1] at hs
  simp only [LevelTwo.conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff] at hs
  exact hs.symm

theorem conj_mem_invE_of_mem_CW
    {u : Pm} (hu : u * suzInv 1 * u⁻¹ = aPrime) (huM : u ∈ suzM)
    {m : Pm} (hm : m ∈ CW) : u⁻¹ * m * u ∈ invE 1 := by
  obtain ⟨-, h2, h3⟩ := mem_CW_iff.1 hm
  refine mem_invE_one_iff.2 ⟨?_, mul_mem (mul_mem (inv_mem huM) h3) huM⟩
  have ht : suzInv 1 = u⁻¹ * aPrime * u := by rw [← hu]; group
  rw [ht]
  calc u⁻¹ * m * u * (u⁻¹ * aPrime * u) = u⁻¹ * (m * aPrime) * u := by group
    _ = u⁻¹ * (aPrime * m) * u := by rw [h2]
    _ = u⁻¹ * aPrime * u * (u⁻¹ * m * u) := by group

theorem liftP_mul_deck
    {s : ℕ} (hs : s < 2) : liftP s * deck = deck * liftP s := by
  refine Equiv.ext fun u => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← rep_liftP hs (deck u), deck_val (liftP s u),
    ← rep_liftP hs u, liftArr_get (deck u).2, liftArr_get u.2, deck_val u,
    show (u.1 + 2997) % 8991 % 2997 = u.1 % 2997 by omega]
  have hA := (LevelTwo.gens_vset hs (Nat.mod_lt u.1 (by norm_num : 0 < 2997))).1
  have := u.2
  omega

theorem snd_mul_deck
    {g : P₂} (hg : g ∈ F) : g.2 * deck = deck * g.2 := by
  refine F_induction (P := fun g : P₂ => g.2 * deck = deck * g.2)
    (liftP_mul_deck (s := 0) (by norm_num)) (liftP_mul_deck (s := 1) (by norm_num))
    (by simp) (fun a b ha hb => ?_) hg
  simp only [Prod.snd_mul]
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem d_comm
    (g : F) : g * d = d * g := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show (g : P₂).1 * 1 = 1 * (g : P₂).1
    rw [mul_one, one_mul]
  · exact snd_mul_deck g.2

theorem deck_pow_val (j : ℕ) (u : Fin 8991) : ((deck ^ j) u).1 = (u.1 + 2997 * j) % 8991 := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt u.2]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, deck_val, ih]
    omega

theorem d_pow_smul
    (j : ℕ) (u : Fin 8991) : ((d ^ j) • u).1 = (u.1 + 2997 * j) % 8991 := by
  have e : ((d ^ j : F) : P₂).2 = deck ^ j := by
    rw [SubgroupClass.coe_pow, Prod.pow_snd]
    rfl
  rw [smul_def, e, deck_pow_val]

theorem d_pow_fst
    (j : ℕ) : ((d ^ j : F) : P₂).1 = 1 := by
  rw [SubgroupClass.coe_pow, Prod.pow_fst]
  exact one_pow j

theorem exists_square
    {v : ℕ} (hv : v < 2997) (hl : listedAt0 v = true) {h u : LevelTwo.Elt}
    (hh : LevelTwo.pElemOK h 2835 v = true) (hu : LevelTwo.elemOK u.1 u.2 = true)
    (hu0 : LevelTwo.sendsB u.1 u.2 0 LevelTwo.p1 = true)
    (huq : LevelTwo.sendsB u.1 u.2 2835 v = true) {i : ℕ} (hi : i < 3)
    (hadj : ElimCert.adjB nbrC (LevelTwo.p1 + 2997 * i) (liftAt0 v) = true) :
    ∃ g k : F, g ∈ Fp ∧ k ∈ Fq ∧ (g : P₂).1 = permC 1782 h.1 ∧
      ((g * k : F) : P₂).1 = permC 1782 u.1 ∧ ((g * k) • LevelTwoCover.pt : Fin 8991).1 =
        LevelTwo.p1 + 2997 * i := by
  obtain ⟨he, h00, hqv⟩ := LevelTwo.pElemOK_parts hh
  obtain ⟨_, hX0⟩ := LevelTwo.eltG_smul he (v := 0) (by norm_num) h00
  obtain ⟨_, hXq⟩ := LevelTwo.eltG_smul he (v := 2835) (by norm_num) hqv
  obtain ⟨_, uX0⟩ := LevelTwo.eltG_smul hu (v := 0) (by norm_num) hu0
  obtain ⟨_, uXq⟩ := LevelTwo.eltG_smul hu (v := 2835) (by norm_num) huq
  obtain ⟨hlt, hmod, hadj0⟩ := liftAt0_spec hl
  have hprV : pr ⟨liftAt0 v, hlt⟩ = ⟨v, hv⟩ := Fin.ext hmod
  obtain ⟨g, hgX, hgp⟩ := exists_lift (LevelTwo.eltG h.1 h.2 he) (u := LevelTwoCover.pt)
    (v := LevelTwoCover.pt) (by rw [pr_pt]; exact hX0)
  have hgq : g • qt = ⟨liftAt0 v, hlt⟩ := by
    have h1 : Γc.Adj LevelTwoCover.pt (g • qt) := by
      have := adjC_smul g adj_pt_qt
      rwa [hgp] at this
    exact adjC_inj h1 hadj0 (by rw [pr_smul, hgX, pr_qt, hprV]; exact hXq)
  obtain ⟨f, hfX, hfq⟩ := exists_lift (LevelTwo.eltG u.1 u.2 hu) (u := qt)
    (v := ⟨liftAt0 v, hlt⟩) (by rw [pr_qt, hprV]; exact uXq)
  have hk : g⁻¹ * f ∈ Fq := (mem_Fq _).2 (by rw [mul_smul, hfq, ← hgq, inv_smul_smul])
  refine ⟨g, g⁻¹ * f, (mem_Fp g).2 hgp, hk, ?_, ?_, ?_⟩
  · rw [← coe_projX, hgX]
    rfl
  · rw [mul_inv_cancel_left, ← coe_projX, hfX]
    rfl
  · rw [mul_inv_cancel_left]
    have hp1 := LevelTwo.p1_lt_2835
    have ha : LevelTwo.p1 + 2997 * i < 8991 := by omega
    have h1 : Γc.Adj ⟨liftAt0 v, hlt⟩ (f • LevelTwoCover.pt) := by
      have := adjC_smul f adj_pt_qt
      rw [hfq] at this
      exact this.symm
    have h2 : Γc.Adj ⟨liftAt0 v, hlt⟩ ⟨LevelTwo.p1 + 2997 * i, ha⟩ :=
      ((nbrGraph_adj_iff (x := ⟨LevelTwo.p1 + 2997 * i, ha⟩) (y := ⟨liftAt0 v, hlt⟩)).2 hadj).symm
    have h3 := adjC_inj h1 h2 (by
      rw [pr_smul, hfX, pr_pt]
      refine (uX0.trans ?_)
      apply Fin.ext
      show LevelTwo.p1 = (LevelTwo.p1 + 2997 * i) % 2997
      omega)
    rw [h3]

theorem hom_conj {H : Subgroup Pm} {G : Type*} [Group G] (f : ↥H →* G) {a b c : Pm}
    (e : a = c * b * c⁻¹) (ha : a ∈ H) (hc : c ∈ H) (hb : b ∈ H) :
    f ⟨a, ha⟩ = f ⟨c, hc⟩ * f ⟨b, hb⟩ * (f ⟨c, hc⟩)⁻¹ := by
  subst e
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem eq_conj_of_square
    {G : Type*} [Group G] (s : ↥(invE 1) →* G) (ψ : ↥Model.NR0 →* G)
    (hB : ∀ x ∈ B0Plus, ∀ (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = s ⟨x, hx⟩)
    (Φ : F →* G) (hP : ∀ x ∈ Fp, ∀ y (hy : y ∈ invE 1), (x : P₂).1 = y → Φ x = s ⟨y, hy⟩)
    (hQ : ∀ x ∈ Fq, ∀ y (hy : y ∈ Model.NR0), (x : P₂).1 = y → Φ x = ψ ⟨y, hy⟩)
    {g k : F} (hg : g ∈ Fp) (hk : k ∈ Fq) {h u m : Pm} (hgh : (g : P₂).1 = h)
    (hgu : ((g * k : F) : P₂).1 = u) (hh : h ∈ invE 1) (hkN : (k : P₂).1 ∈ Model.NR0)
    (hm : m ∈ invE 1) (h1 : h⁻¹ * m * h ∈ B0Plus) (h2 : u⁻¹ * m * u ∈ B0Plus) :
    s ⟨m, hm⟩ = Φ (g * k) * s ⟨u⁻¹ * m * u, B0Plus_le_invE h2⟩ * (Φ (g * k))⁻¹ := by
  have hku : u = h * (k : P₂).1 := by
    rw [← hgu, ← hgh]
    rfl
  rw [hom_conj s (by group : m = h * (h⁻¹ * m * h) * h⁻¹) hm hh (B0Plus_le_invE h1),
    ← hP g hg h hh hgh, ← hB _ h1 (B0Plus_le_invE h1) (B0Plus_le_NR0 h1),
    hom_conj ψ (show h⁻¹ * m * h = (k : P₂).1 * (u⁻¹ * m * u) * (k : P₂).1⁻¹ by
      rw [hku]; group) (B0Plus_le_NR0 h1) hkN (B0Plus_le_NR0 h2),
    ← hQ k hk _ hkN rfl, hB _ h2 (B0Plus_le_invE h2) (B0Plus_le_NR0 h2), map_mul]
  group

end CFSG.Sporadic.SuzRecog.RootTwist

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.SuzRecog.RootTwistCheck CFSG.Sporadic.SuzRecog.RootTwistData
  CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ModelGroups
  CFSG.Sporadic.SuzRecog.LevelTwoCover CFSG.Sporadic.SuzRecog.RootTwist CFSG.Sporadic.SuzRecog.Model

attribute [local irreducible] LevelTwo.nbr nbrC LevelTwo.vtab LevelTwo.vtabs LevelTwo.aPts
  LevelTwo.wPts LevelTwo.trips LevelTwo.aIdx LevelTwo.vIdx LevelTwo.p1 LevelTwo.elPq LevelTwo.elQp
  hEl uEl sheetAt liftAt0 xTwArr yTwArr

local notation "Pm" => Equiv.Perm (Fin 1782)

local notation "P₂" => Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)

set_option maxRecDepth 100000 in
theorem rootTwistTrivial' :
    RootTwistTrivial' coverData proj d (suzInv 1 * LevelTwo.aP LevelTwo.p1) := by
  intro G _ _ _ S _ σ ψ ζ hB _ _ Φ hΦp hΦq _
  let s : ↥(invE 1) →* G := S.M.subtype.comp σ.symm.toMonoidHom
  have hs : Function.Injective s := fun a b h => σ.symm.injective (Subtype.ext h)
  have hP : ∀ x ∈ Fp, ∀ y (hy : y ∈ invE 1), (x : P₂).1 = y → Φ x = s ⟨y, hy⟩ :=
    fun x hx y hy e => by
      rw [hΦp x hx (by rw [coe_proj, e]; exact hy)]
      exact congrArg (fun c => ((σ.symm c : S.M) : G)) (Subtype.ext e)
  have hQ : ∀ x ∈ Fq, ∀ y (hy : y ∈ Model.NR0), (x : P₂).1 = y → Φ x = ψ ⟨y, hy⟩ :=
    fun x hx y hy e => by
      rw [hΦq x hx (by rw [coe_proj, e]; exact hy)]
      exact congrArg ψ (Subtype.ext e)
  have hB' : ∀ x ∈ B0Plus, ∀ (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0),
      ψ ⟨x, hxN⟩ = s ⟨x, hx⟩ := fun x h hx hxN => hB x h hx hxN
  have ht1X : suzInv 1 ∈ LevelTwo.xGroup :=
    LevelTwo.mem_xGroup_of_memX LevelTwo.rep_t1 LevelTwo.basicOK_parts.2.2.2.2.2.2.1
  have ht1M : suzInv 1 ∈ suzM := LevelTwo.xGroup_le_suzM ht1X
  have ht1 : suzInv 1 ∈ invE 1 := mem_invE_one_iff.2 ⟨rfl, ht1M⟩
  have ht1C : suzInv 1 ∈ Model.Crho1 := mem_Crho1_iff.2 ⟨comm_facts.1.symm, ht1M⟩
  have hz : s ⟨suzInv 1, ht1⟩ = S.z := by
    have hc : (⟨suzInv 1, ht1⟩ : ↥(invE 1)) ∈ center ↥(invE 1) :=
      mem_center_iff.2 fun g => Subtype.ext (mem_invE_one_iff.1 g.2).1
    have h1 : (⟨suzInv 1, ht1⟩ : ↥(invE 1)) ≠ 1 :=
      fun h => suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)
    show ((σ.symm ⟨suzInv 1, ht1⟩ : S.M) : G) = S.z
    rw [← map_zM_eq S σ hc h1, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨xt₁, hxt₁, hxt₁p⟩ := exists_proj_eq_of_mem_invE coverData rfl _ ht1C ht1
  have hΦt : Φ xt₁ = S.z := by
    rw [hP xt₁ hxt₁ _ ht1 (congrArg Subtype.val hxt₁p), hz]
  have hdM : Φ d ∈ S.M := by
    show Φ d ∈ centralizer ({S.z} : Set G)
    rw [mem_centralizer_singleton_iff, ← hΦt, ← map_mul, ← map_mul, d_comm]
  set c : ↥(invE 1) := σ ⟨Φ d, hdM⟩ with hcdef
  have hsc : s c = Φ d := by
    show ((σ.symm (σ ⟨Φ d, hdM⟩) : S.M) : G) = Φ d
    rw [MulEquiv.symm_apply_apply]
  have hcent : ∀ g ∈ invE 1 ⊓ Model.Crho1, (c : Pm) * g = g * c := by
    intro g hg
    obtain ⟨y, hy, hyp⟩ := exists_proj_eq_of_mem_invE coverData rfl g (mem_inf.1 hg).2
      (mem_inf.1 hg).1
    have h1 : Φ y = s ⟨g, (mem_inf.1 hg).1⟩ := hP y hy g _ (congrArg Subtype.val hyp)
    have h2 : s (c * ⟨g, (mem_inf.1 hg).1⟩) = s (⟨g, (mem_inf.1 hg).1⟩ * c) := by
      rw [map_mul, map_mul, hsc, ← h1, ← map_mul, ← map_mul, d_comm]
    exact congrArg Subtype.val (hs h2)
  have hc3 : (c : Pm) ^ 3 = 1 := by
    have h : s (c ^ 3) = s 1 := by
      rw [map_pow, hsc, ← map_pow, d_pow_three, map_one, map_one]
    simpa using congrArg Subtype.val (hs h)
  obtain ⟨ε, hε⟩ := mem_zpowers_iff.1 (mem_zpowers_rho1_of_mem_centralizer c.2 hcent hc3)
  obtain ⟨hsqV, hsqV'⟩ := transOK_parts
  obtain ⟨hhV, huV, huV0, huVq, hpV1, hpV2⟩ := squareOK_parts hsqV
  obtain ⟨hhV', huV', huV0', huVq', hpV1', hpV2'⟩ := squareOK_parts hsqV'
  obtain ⟨hsV, hsV', hne⟩ := holOK_parts
  obtain ⟨hlV, hiV, hadjV⟩ := sheetOK_parts hsV
  obtain ⟨hlV', hiV', hadjV'⟩ := sheetOK_parts hsV'
  obtain ⟨gV, kV, hgV, hkV, hgV1, hfV1, hfVp⟩ :=
    exists_square (by norm_num) hlV hhV huV huV0 huVq hiV hadjV
  obtain ⟨gV', kV', hgV', hkV', hgV1', hfV1', hfVp'⟩ :=
    exists_square (by norm_num) hlV' hhV' huV' huV0' huVq' hiV' hadjV'
  have hxI : xTw ∈ invE 1 := CW_le_invE xTw_mem_CW
  have hyI : yTw ∈ invE 1 := CW_le_invE yTw_mem_CW
  have hxM : xTw ∈ suzM := (mem_CW_iff.1 xTw_mem_CW).2.2
  have hyM : yTw ∈ suzM := (mem_CW_iff.1 yTw_mem_CW).2.2
  have hhVi := isInvA_of_elemOK (LevelTwo.pElemOK_parts hhV).1
  have hhVi' := isInvA_of_elemOK (LevelTwo.pElemOK_parts hhV').1
  have hhVM : permC 1782 (hEl 2970).1 ∈ suzM :=
    LevelTwo.xGroup_le_suzM (LevelTwo.eltG_mem (LevelTwo.pElemOK_parts hhV).1)
  have hhVM' : permC 1782 (hEl 2890).1 ∈ suzM :=
    LevelTwo.xGroup_le_suzM (LevelTwo.eltG_mem (LevelTwo.pElemOK_parts hhV').1)
  have huVM : permC 1782 (uEl 2970).1 ∈ suzM := LevelTwo.xGroup_le_suzM (LevelTwo.eltG_mem huV)
  have huVM' : permC 1782 (uEl 2890).1 ∈ suzM :=
    LevelTwo.xGroup_le_suzM (LevelTwo.eltG_mem huV')
  have hb1 := mem_B0Plus_of_plusB (rep_conjInvA hhVi rep_xTw)
    (mul_mem (mul_mem (inv_mem hhVM) hxM) hhVM) hpV1
  have hb2 := mem_B0Plus_of_plusB (rep_conjInvA (isInvA_of_elemOK huV) rep_xTw)
    (mul_mem (mul_mem (inv_mem huVM) hxM) huVM) hpV2
  have hb1' := mem_B0Plus_of_plusB (rep_conjInvA hhVi' rep_yTw)
    (mul_mem (mul_mem (inv_mem hhVM') hyM) hhVM') hpV1'
  have hb2' := mem_B0Plus_of_plusB (rep_conjInvA (isInvA_of_elemOK huV') rep_yTw)
    (mul_mem (mul_mem (inv_mem huVM') hyM) huVM') hpV2'
  have memC : ∀ x ∈ Fp, ∀ y, (x : P₂).1 = y → y ∈ invE 1 := fun x hx y e => by
    have := proj_mem_invE coverData rfl x hx
    rwa [coe_proj, e] at this
  have hhI := memC gV hgV _ hgV1
  have hhI' := memC gV' hgV' _ hgV1'
  have eqV := eq_conj_of_square s ψ hB' Φ hP hQ hgV hkV hgV1 hfV1 hhI
    (proj_mem_NR0 coverData rfl kV hkV) hxI hb1 hb2
  have eqV' := eq_conj_of_square s ψ hB' Φ hP hQ hgV' hkV' hgV1' hfV1' hhI'
    (proj_mem_NR0 coverData rfl kV' hkV') hyI hb1' hb2'
  set fV := gV * kV with hfV
  set fV' := gV' * kV' with hfV'
  clear_value fV fV'
  set u₁ := permC 1782 (uEl 2970).1 with hu₁
  set u₂ := permC 1782 (uEl 2890).1 with hu₂
  set j := (sheetAt (liftAt0 2890) + 3 - sheetAt (liftAt0 2970)) % 3 with hj
  have hj12 : j = 1 ∨ j = 2 := by omega
  have hp1 := LevelTwo.p1_lt_2835
  have heP : fV'⁻¹ * d ^ j * fV ∈ Fp := by
    rw [mem_Fp, mul_smul, mul_smul]
    have e : d ^ j • (fV • LevelTwoCover.pt) = fV' • LevelTwoCover.pt :=
      Fin.ext (by rw [d_pow_smul, hfVp, hfVp']; omega)
    rw [e, inv_smul_smul]
  have he1 : ((fV'⁻¹ * d ^ j * fV : F) : P₂).1 = u₂⁻¹ * u₁ := by
    show (fV' : P₂).1⁻¹ * ((d ^ j : F) : P₂).1 * (fV : P₂).1 = _
    rw [d_pow_fst, mul_one, hfV1, hfV1']
  have heI : u₂⁻¹ * u₁ ∈ invE 1 := memC _ heP _ he1
  have hΦe : Φ (fV'⁻¹ * d ^ j * fV) = s ⟨u₂⁻¹ * u₁, heI⟩ := hP _ heP _ heI he1
  have hu₁X : u₁ ∈ LevelTwo.xGroup := LevelTwo.eltG_mem huV
  have hu₁ρ : u₁ * rho1 = rho1 * u₁ :=
    mem_centralizer_singleton_iff.1 (LevelTwo.xGroup_le_centralizer hu₁X)
  have hcu : ∀ m ∈ CW, u₁⁻¹ * m * u₁ ∈ invE 1 := fun m hm =>
    conj_mem_invE_of_mem_CW (conj_t1_eq huV huV0) huVM hm
  let cu : ↥CW →* ↥(invE 1) :=
    { toFun := fun m => ⟨u₁⁻¹ * m * u₁, hcu m m.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show u₁⁻¹ * ((a : Pm) * b) * u₁ = u₁⁻¹ * a * u₁ * (u₁⁻¹ * b * u₁)
        group) }
  let κ : ↥CW →* G := s.comp (Subgroup.inclusion CW_le_invE)
  let κ' : ↥CW →* G := (MulAut.conj (Φ fV)).toMonoidHom.comp (s.comp cu)
  have hκ' : Function.Injective κ' := by
    intro a b hab
    have h0 : Φ fV * s (cu a) * (Φ fV)⁻¹ = Φ fV * s (cu b) * (Φ fV)⁻¹ := hab
    have h1 : u₁⁻¹ * (a : Pm) * u₁ = u₁⁻¹ * b * u₁ :=
      congrArg Subtype.val (hs (mul_left_cancel (mul_right_cancel h0)))
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hρI : rho1 ∈ invE 1 := CW_le_invE rho1_mem_CW
  let r : ↥CW := ⟨rho1, rho1_mem_CW⟩
  have hκr : κ' r ^ ε = Φ d := by
    have e0 : cu r = ⟨rho1, hρI⟩ := Subtype.ext (by
      show u₁⁻¹ * rho1 * u₁ = rho1
      rw [mul_assoc, ← hu₁ρ, ← mul_assoc, inv_mul_cancel, one_mul])
    have e1 : κ' r = Φ fV * s ⟨rho1, hρI⟩ * (Φ fV)⁻¹ := by
      show Φ fV * s (cu r) * (Φ fV)⁻¹ = _
      rw [e0]
    have e2 : s ⟨rho1, hρI⟩ ^ ε = Φ d := by
      rw [← map_zpow, ← hsc]
      congr 1
      exact Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hε)
    rw [e1, conj_zpow, e2, ← map_mul, d_comm, map_mul, mul_inv_cancel_right]
  have hx : ∀ h : xTw ∈ CW, κ ⟨xTw, h⟩ = κ' ⟨xTw, h⟩ := fun _ => eqV
  have hy : ∀ h : yTw ∈ CW, κ ⟨yTw, h⟩ = κ' (r ^ (ε * j) * ⟨yTw, h⟩ * (r ^ (ε * j))⁻¹) := by
    intro h
    rw [map_mul, map_mul, map_inv, map_zpow, zpow_mul, hκr, zpow_natCast]
    show s ⟨yTw, _⟩ = Φ d ^ j * (Φ fV * s ⟨u₁⁻¹ * yTw * u₁, hcu _ h⟩ * (Φ fV)⁻¹) *
      (Φ d ^ j)⁻¹
    have hfe : Φ fV' = Φ d ^ j * Φ fV * (s ⟨u₂⁻¹ * u₁, heI⟩)⁻¹ := by
      rw [← hΦe, map_mul, map_mul, map_inv, map_pow]
      group
    have hconj : (s ⟨u₂⁻¹ * u₁, heI⟩)⁻¹ * s ⟨u₂⁻¹ * yTw * u₂, B0Plus_le_invE hb2'⟩ *
        s ⟨u₂⁻¹ * u₁, heI⟩ = s ⟨u₁⁻¹ * yTw * u₁, hcu _ h⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by
        show (u₂⁻¹ * u₁)⁻¹ * (u₂⁻¹ * yTw * u₂) * (u₂⁻¹ * u₁) = u₁⁻¹ * yTw * u₁
        group)
    rw [eqV', hfe, ← hconj]
    generalize s ⟨u₂⁻¹ * u₁, heI⟩ = A
    generalize s ⟨u₂⁻¹ * yTw * u₂, B0Plus_le_invE hb2'⟩ = B
    group
  have h3 : (3 : ℤ) ∣ ε * j := three_dvd_of_twist_at κ κ' hκ' (r := r) rfl hx hy
  have h3ε : (3 : ℤ) ∣ ε := by
    rcases hj12 with h | h <;> rw [h] at h3 <;> push_cast at h3 <;> omega
  obtain ⟨t, rfl⟩ := h3ε
  have hc1 : c = 1 := Subtype.ext (by
    rw [← hε, zpow_mul, zpow_ofNat, ModelGroups.rho1_pow_three, one_zpow]
    rfl)
  rw [← hsc, hc1, map_one]

end CFSG.Sporadic.SuzRecog
