module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
import CFSG.Quasithin.Recognition.St84.Gen.NatQuotL2
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F6 (sqClosure sqClosure_le normalizer_le_normalizer_sqClosure)
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

private theorem conjSub_eq_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) : conjSub g H = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)

private theorem conjSub_s_Gv_neg_one {s : G} (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.Gv (-1)) = t.Gv 1 := by
  have hsplit : s = t.x₁ * (t.x₁⁻¹ * s) := by group
  rw [hsplit, conjSub_mul, conjSub_eq_self_of_mem hs.2]
  simpa [conjSub] using t.map_Gv_x₁ (-1)

private theorem conjSub_s_Qv_one {s : G} (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.Qv 1) = t.Qv (-1) := by
  have hsplit : s = t.x₁ * (t.x₁⁻¹ * s) := by group
  rw [hsplit, conjSub_mul,
    F7.conjSub_eq_of_mem_normalizer ((t.Gv_le_normalizer_Qv 1) hs.1)]
  simpa [conjSub] using t.map_Qv_x₁ 1

private theorem conjSub_s_Qv_neg_one {s : G} (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.Qv (-1)) = t.Qv 1 := by
  have hsplit : s = t.x₁ * (t.x₁⁻¹ * s) := by group
  rw [hsplit, conjSub_mul,
    F7.conjSub_eq_of_mem_normalizer ((t.Gv_le_normalizer_Qv (-1)) hs.2)]
  simpa [conjSub] using t.map_Qv_x₁ (-1)

private theorem conjSub_s_Qv_zero {s : G} (hs0 : s ∈ t.MX X 0) :
    conjSub s (t.Qv 0) = t.Qv 0 :=
  F7.conjSub_eq_of_mem_normalizer ((t.Gv_le_normalizer_Qv 0) hs0.2)

private theorem conjSub_s_MX_neg_one {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.MX X (-1)) = t.MX X 1 := by
  have hNX : conjSub s (Subgroup.normalizer (X : Set G)) = Subgroup.normalizer (X : Set G) :=
    F7.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs0.1)
  rw [show t.MX X (-1) = Subgroup.normalizer (X : Set G) ⊓ t.Gv (-1) from rfl,
    show t.MX X 1 = Subgroup.normalizer (X : Set G) ⊓ t.Gv 1 from rfl,
    conjSub_inf, hNX, t.conjSub_s_Gv_neg_one hs]

private theorem conjSub_s_EX_one {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.EX X 1) = t.EX X (-1) := by
  have hNX : conjSub s (Subgroup.normalizer (X : Set G)) = Subgroup.normalizer (X : Set G) :=
    F7.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs0.1)
  rw [show t.EX X 1 = (t.Qv 1) ⊓ Subgroup.normalizer (X : Set G) from rfl,
    show t.EX X (-1) = (t.Qv (-1)) ⊓ Subgroup.normalizer (X : Set G) from rfl,
    conjSub_inf, t.conjSub_s_Qv_one hs, hNX]

private theorem conjSub_s_EX_neg_one {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.EX X (-1)) = t.EX X 1 := by
  have hNX : conjSub s (Subgroup.normalizer (X : Set G)) = Subgroup.normalizer (X : Set G) :=
    F7.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs0.1)
  rw [show t.EX X (-1) = (t.Qv (-1)) ⊓ Subgroup.normalizer (X : Set G) from rfl,
    show t.EX X 1 = (t.Qv 1) ⊓ Subgroup.normalizer (X : Set G) from rfl,
    conjSub_inf, t.conjSub_s_Qv_neg_one hs, hNX]

private theorem inf_Qv_zero_MX_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv 0 ⊓ t.MX X (-1) = t.PX X := by
  have hQ := t.Qv_le_Gv hfr 0
  refine le_antisymm ?_ ?_
  · exact le_inf inf_le_left
      (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans hQ.2))
  · exact le_inf inf_le_left
      (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans hQ.1))

private theorem conjSub_s_PX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {s : G} (hs0 : s ∈ t.MX X 0) (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (t.PX X) = t.PX X := by
  rw [← t.inf_Qv_zero_MX_neg_one hfr, conjSub_inf, t.conjSub_s_Qv_zero hs0,
    t.conjSub_s_MX_neg_one hs0 hs, t.inf_Qv_zero_MX_neg_one hfr]

private theorem MX_le_normalizer_EX :
    t.MX X 1 ≤ Subgroup.normalizer (t.EX X 1 : Set G) := by
  intro m hm
  obtain ⟨hmN, hmG⟩ := Subgroup.mem_inf.mp hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub m (t.Qv 1 ⊓ Subgroup.normalizer (X : Set G)) =
    t.Qv 1 ⊓ Subgroup.normalizer (X : Set G)
  rw [conjSub_inf, F7.conjSub_eq_of_mem_normalizer ((t.Gv_le_normalizer_Qv 1) hmG),
    F7.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hmN)]

private theorem MX_le_normalizer_YX :
    t.MX X 1 ≤ Subgroup.normalizer (t.YX X 1 : Set G) := by
  intro m hm
  have hm' : conjSub m (t.LX X 1) = t.LX X 1 := by
    have h := le_normalizer_oTwoPrime (t.MX X 1) hm
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub m (oTwoRes (t.LX X 1)) = oTwoRes (t.LX X 1)
  rw [conjSub_oTwoRes, hm']

private theorem MX_le_normalizer_commutator :
    t.MX X 1 ≤ Subgroup.normalizer (⁅t.EX X 1, t.YX X 1⁆ : Subgroup G) :=
  CFSG.Quasithin.D14.le_normalizer_commutator t.MX_le_normalizer_EX t.MX_le_normalizer_YX

private theorem commutator_le_EX :
    ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X 1 :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((oTwoRes_le (t.LX X 1)).trans ((oTwoPrime_le _).trans t.MX_le_normalizer_EX))

private theorem EX_eq_inf_PX (hEP : t.EX X 1 ≤ t.PX X) :
    t.EX X 1 = t.Qv 1 ⊓ t.PX X := by
  refine le_antisymm (le_inf inf_le_left hEP) ?_
  exact le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans inf_le_left))

private theorem EX_neg_one_le_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hEP : t.EX X 1 ≤ t.PX X) :
    t.EX X (-1) ≤ t.PX X := by
  calc t.EX X (-1) = conjSub s (t.EX X 1) := (t.conjSub_s_EX_one hs0 hs).symm
    _ ≤ conjSub s (t.PX X) := conjSub_mono s hEP
    _ = t.PX X := t.conjSub_s_PX hfr hs0 hs

private theorem K_le_normalizer_EX (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K) :
    t.K ≤ Subgroup.normalizer (t.EX X 1 : Set G) := by
  refine (le_sup_right : t.K ≤ t.LX X 1 ⊔ t.K).trans ?_
  rw [← hMK]
  exact t.MX_le_normalizer_EX

private theorem K_le_normalizer_EX_neg (hX : t.ArcL X) :
    t.K ≤ Subgroup.normalizer (t.EX X (-1) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub k (t.Qv (-1) ⊓ Subgroup.normalizer (X : Set G)) =
    t.Qv (-1) ⊓ Subgroup.normalizer (X : Set G)
  have hQ : k ∈ Subgroup.normalizer (t.Qv (-1) : Set G) :=
    (t.Gv_le_normalizer_Qv (-1)) (t.K_le_Gv (-1) hk)
  have hN : k ∈ Subgroup.normalizer (Subgroup.normalizer (X : Set G) : Set G) :=
    Subgroup.le_normalizer (hX.K_le hk)
  rw [conjSub_inf, F7.conjSub_eq_of_mem_normalizer hQ, F7.conjSub_eq_of_mem_normalizer hN]

private theorem K_le_normalizer_commutator (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K) :
    t.K ≤ Subgroup.normalizer (⁅t.EX X 1, t.YX X 1⁆ : Subgroup G) :=
  ((le_sup_right : t.K ≤ t.LX X 1 ⊔ t.K).trans (le_of_eq hMK.symm)).trans
    t.MX_le_normalizer_commutator

private theorem conjSub_sqClosure (g : G) (A : Subgroup G) :
    conjSub g (sqClosure A) = sqClosure (conjSub g A) := by
  have hS : (MulAut.conj g).toMonoidHom '' {x : G | ∃ a ∈ A, a ^ 2 = x} =
      {y : G | ∃ b ∈ conjSub g A, b ^ 2 = y} := by
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨(MulAut.conj g).toMonoidHom a, Subgroup.mem_map_of_mem _ ha, ?_⟩
      exact (map_pow (MulAut.conj g).toMonoidHom a 2).symm
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      exact ⟨a ^ 2, ⟨a, ha, rfl⟩, map_pow (MulAut.conj g).toMonoidHom a 2⟩
  rw [sqClosure, conjSub, MonoidHom.map_closure, hS, sqClosure]

private theorem sqClosure_eq_bot_iff {A : Subgroup G} :
    sqClosure A = ⊥ ↔ ∀ x ∈ A, x ^ 2 = 1 := by
  constructor
  · intro h x hx
    have hmem : x ^ 2 ∈ sqClosure A := Subgroup.subset_closure ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at hmem
  · intro h
    refine le_antisymm ?_ bot_le
    rw [sqClosure, Subgroup.closure_le]
    rintro x ⟨a, ha, rfl⟩
    exact Subgroup.mem_bot.mpr (h a ha)

private theorem isElemAbelian_of_sqClosure_eq_bot {A : Subgroup G}
    (h : sqClosure A = ⊥) : IsElemAbelian 2 A := by
  have hsq := sqClosure_eq_bot_iff.mp h
  exact ⟨⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g : A => orderOf_dvd_of_pow_eq_one (Subtype.ext (hsq g g.2))) a b).eq⟩⟩, hsq⟩

private theorem sqClosure_mono {A B : Subgroup G} (h : A ≤ B) : sqClosure A ≤ sqClosure B := by
  rw [sqClosure, sqClosure, Subgroup.closure_le]
  rintro x ⟨a, ha, rfl⟩
  exact Subgroup.subset_closure ⟨a, h ha, rfl⟩

private theorem sqClosure_sup_eq_right_of_central {H K : Subgroup G}
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) (hH : sqClosure H = ⊥) :
    sqClosure (H ⊔ K) = sqClosure K := by
  refine le_antisymm ?_ (sqClosure_mono le_sup_right)
  rw [sqClosure, Subgroup.closure_le]
  rintro x ⟨a, ha, rfl⟩
  have ha' : a ∈ ((H ⊔ K : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H K
    (hHK.trans (Subgroup.centralizer_le_normalizer _))] at ha'
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp ha'
  have hcomm : k * h = h * k := Subgroup.mem_centralizer_iff.mp (hHK hh) k hk
  have hh2 : h * h = 1 := by
    have := sqClosure_eq_bot_iff.mp hH h hh
    simpa [pow_two] using this
  have hsq : (h * k) ^ 2 = k * k := by
    rw [pow_two]
    calc (h * k) * (h * k) = h * (k * h) * k := by group
      _ = h * (h * k) * k := by rw [hcomm]
      _ = (h * h) * (k * k) := by group
      _ = k * k := by rw [hh2, one_mul]
  rw [hsq]
  exact Subgroup.subset_closure ⟨k, hk, by rw [pow_two]⟩

private theorem oTwoRes_eq_pResidualOf (A : Subgroup G) : oTwoRes A = pResidualOf 2 A :=
  (oTwoRes_eq_oTwoUpper A).trans (oTwoUpper_eq_pResidualOf A)

private theorem commutator_le_centerOf_EX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hP : IsSylowTwoOf (t.PX X) (t.LX X 1))
    (hnc : NoCharNormal (t.PX X) (t.LX X 1)) :
    ⁅t.EX X 1, t.YX X 1⁆ ≤ centerOf (t.EX X 1) ∧
      IsElemAbelian 2 ⁅t.EX X 1, t.YX X 1⁆ := by
  have hYX : t.YX X 1 = pResidualOf 2 (t.LX X 1) := oTwoRes_eq_pResidualOf _
  have hbaum := CFSG.Quasithin.St84.baumannC_pushZ_L2 (n := f) (X := t.LX X 1)
    (P := t.PX X) (by have := hfr.hf; omega) hc hq hP hnc
  unfold CFSG.Quasithin.F53Push.BaumannC at hbaum
  rw [hE] at hbaum
  have hW := CFSG.Quasithin.St84.pushZ_le_centerOf_pCoreOf hc hP
  rw [hE] at hW
  rw [hYX]
  exact ⟨hbaum.trans hW.1, hW.2.mono hbaum⟩

private theorem commutator_ne_bot {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1))
    (hLY : t.LX X 1 = t.YX X 1 ⊔ t.PX X) :
    ⁅t.EX X 1, t.YX X 1⁆ ≠ ⊥ := by
  intro hV
  have hV' : ⁅t.YX X 1, t.EX X 1⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm] at hV
  have hYcent : t.YX X 1 ≤ Subgroup.centralizer (t.EX X 1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV'
  have hYLE : t.YX X 1 ≤ t.EX X 1 := by
    have h2 : t.YX X 1 ≤ t.LX X 1 ⊓ Subgroup.centralizer (t.EX X 1 : Set G) :=
      le_inf (oTwoRes_le _) hYcent
    unfold CharTwo at hc
    rw [hE] at hc
    exact h2.trans hc
  have hLP : t.LX X 1 = t.PX X := by
    rw [hLY]
    exact sup_eq_right.mpr (hYLE.trans hEP)
  have hLXp : IsPGroup 2 (t.LX X 1) := hLP ▸ hP.2.1
  have hpc : pCoreOf 2 (t.LX X 1) = t.LX X 1 := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (N := t.LX X 1)
      (H := t.LX X 1) (r := 2) le_rfl Subgroup.le_normalizer hLXp
  have hpcore : CFSG.pCore 2 ↥(t.LX X 1) = ⊤ := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (t.LX X 1), hpc, Subgroup.subgroupOf_self]
  have htriv : Nat.card (oTwoQuot ↥(t.LX X 1)) = 1 := by
    haveI : Subsingleton (oTwoQuot ↥(t.LX X 1)) := by
      change Subsingleton (↥(t.LX X 1) ⧸ CFSG.pCore 2 ↥(t.LX X 1))
      rw [hpcore]
      exact QuotientGroup.subsingleton_quotient_top
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  obtain ⟨e⟩ := hq
  have hcard : Nat.card (oTwoQuot ↥(t.LX X 1)) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Nat.card_congr e.toEquiv
  have h2 : 2 ∣ Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.two_dvd_natCard_psl2 (GaloisField 2 f)
  rw [← hcard, htriv] at h2
  exact Nat.prime_two.not_dvd_one h2

private theorem K_le_normalizer_PX (hX : t.ArcL X) :
    t.K ≤ Subgroup.normalizer (t.PX X : Set G) := by
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
    ⟨(t.Gv_le_normalizer_Qv 0) ((t.K_le_Gv 0) hk),
      Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
        ⟨Subgroup.le_normalizer (hX.K_le hk), Subgroup.le_normalizer ((t.K_le_Gv 1) hk)⟩)⟩)

private theorem PX_le_normalizer_PX : t.PX X ≤ Subgroup.normalizer (t.PX X : Set G) :=
  Subgroup.le_normalizer

private theorem cj_conjJoin_le_of_le {H Z : Subgroup G} {g : G}
    (hH : F53Push.cj g H ≤ H) (hZ : F53Push.cj g Z ≤ Z) :
    F53Push.cj g (F53Push.conjJoin H Z) ≤ F53Push.conjJoin H Z := by
  rw [F53Push.cj, Subgroup.map_le_iff_le_comap]
  refine F53Push.conjJoin_le fun h hh => ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_comap]
  have hgh : g * h * g⁻¹ ∈ H := hH (Subgroup.mem_map_of_mem _ hh)
  have hgz : g * z * g⁻¹ ∈ Z := hZ (Subgroup.mem_map_of_mem _ hz)
  have hmem := F53Push.cj_le_conjJoin (J := Z) hgh
    (Subgroup.mem_map_of_mem (MulAut.conj (g * h * g⁻¹)).toMonoidHom hgz)
  show g * (h * z * h⁻¹) * g⁻¹ ∈ F53Push.conjJoin H Z
  convert hmem using 1
  show g * (h * z * h⁻¹) * g⁻¹ = g * h * g⁻¹ * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹
  group

private theorem cj_s_closure_t'_K_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) {s t' : G} (hs0 : s ∈ t.MX X 0)
    (hsK : s ∈ normalizer (t.K : Set G))
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hst' : ⁅s, t'⁆ ∈ t.PX X) :
    F53Push.cj s (Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (t.PX X : Set G))) ≤
      Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (t.PX X : Set G)) := by
  let H : Subgroup G :=
    Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (t.PX X : Set G))
  change F53Push.cj s H ≤ H
  have hKH : t.K ≤ H := fun k hk =>
    Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_right _ hk))
  have hPH : t.PX X ≤ H := fun p hp =>
    Subgroup.subset_closure (Set.mem_union_right _ hp)
  have ht'H : t' ∈ H :=
    Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton t')))
  have hKfix : F53Push.cj s (t.K) = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hsK
  have hPfix : F53Push.cj s (t.PX X) = t.PX X := t.conjSub_s_PX hfr hs0 hs
  show (H.map (MulAut.conj s).toMonoidHom) ≤ H
  rw [show H = Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (t.PX X : Set G))
    from rfl, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  rcases hy with (hy | hy) | hy
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change s * t' * s⁻¹ ∈
      Subgroup.closure ({t'} ∪ (t.K : Set G) ∪ (t.PX X : Set G))
    have h1 : s * t' * s⁻¹ = ⁅s, t'⁆ * t' := conj_eq_commutatorElement_mul
    rw [show s * t' * s⁻¹ = ⁅s, t'⁆ * t' from h1]
    exact H.mul_mem (hPH hst') ht'H
  · have h := Subgroup.mem_normalizer_iff.mp hsK (y : G)
    exact hKH ((h).mp hy)
  · have hmem := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hy
    rw [show (t.PX X).map (MulAut.conj s).toMonoidHom = t.PX X from hPfix] at hmem
    exact Subgroup.subset_closure (Or.inr hmem)

private theorem closure_t'_K_PX_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hEP : t.EX X 1 ≤ t.PX X) {t' : G}
    (ht' : t' ∈ t.Qv 0) (ht'N : t' ∈ normalizer (t.PX X : Set G)) :
    Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (t.PX X : Set G)) ≤
      Subgroup.normalizer (t.EX X 1 : Set G) := by
  have hQ : t.Qv 0 ≤ t.Gv 1 := (t.Qv_le_Gv hfr 0).2
  have ht'NQ : t' ∈ Subgroup.normalizer (t.Qv 1 : Set G) :=
    (t.Gv_le_normalizer_Qv 1) (hQ ht')
  have hKNQ : t.K ≤ Subgroup.normalizer (t.Qv 1 : Set G) :=
    (t.K_le_Gv 1).trans (t.Gv_le_normalizer_Qv 1)
  have hPNQ : t.PX X ≤ Subgroup.normalizer (t.Qv 1 : Set G) :=
    (inf_le_left.trans hQ).trans (t.Gv_le_normalizer_Qv 1)
  rw [t.EX_eq_inf_PX hEP, Subgroup.closure_le]
  rintro x ((hx | hx) | hx)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨ht'NQ, ht'N⟩)
  · exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hKNQ hx, t.K_le_normalizer_PX hX hx⟩)
  · exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hPNQ hx, t.PX_le_normalizer_PX hx⟩)

private theorem cj_sup_cj_eq {V : Subgroup G} {s : G}
    (hV : s * s ∈ Subgroup.normalizer (V : Set G)) :
    F53Push.cj s (V ⊔ F53Push.cj s V) = V ⊔ F53Push.cj s V := by
  have h2 : (F53Push.cj s V).map (MulAut.conj s).toMonoidHom = V := by
    change F53Push.cj s (F53Push.cj s V) = V
    rw [F53Push.cj_cj, F53Push.cj_eq_of_mem_normalizer hV]
  change (V ⊔ F53Push.cj s V).map (MulAut.conj s).toMonoidHom =
    V ⊔ F53Push.cj s V
  rw [Subgroup.map_sup, h2]
  change F53Push.cj s V ⊔ V = V ⊔ F53Push.cj s V
  rw [sup_comm]

private theorem mem_normalizer_conjJoin_of_cj {H Z : Subgroup G} {s : G}
    (hHnR : H ≤ Subgroup.normalizer (F53Push.conjJoin H Z : Set G))
    (hcsH : F53Push.cj s H ≤ H)
    (hZfix : F53Push.cj s Z = Z) (hs2 : s ^ 2 ∈ H) :
    s ∈ Subgroup.normalizer (F53Push.conjJoin H Z : Set G) := by
  set R : Subgroup G := F53Push.conjJoin H Z with hRdef
  have hcsR : F53Push.cj s R ≤ R := by
    simpa [hRdef] using cj_conjJoin_le_of_le hcsH (le_of_eq hZfix)
  have hqN : (s ^ 2)⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normalizer (R : Set G)).inv_mem (by rw [hRdef]; exact hHnR hs2)
  have hcinvR : F53Push.cj s⁻¹ R ≤ R := by
    have hsinv : s⁻¹ = s * (s ^ 2)⁻¹ := by group
    rw [hsinv, ← F53Push.cj_cj, F53Push.cj_eq_of_mem_normalizer hqN]
    exact hcsR
  simpa [hRdef] using F7.mem_normalizer_of_conj_le hcsR hcinvR

theorem ArcLMax.not_commutator_le_EX_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1)) (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K)
    (hLY : t.LX X 1 = t.YX X 1 ⊔ t.PX X)
    {s : G} (hs0 : s ∈ t.MX X 0) (hsK : s ∈ normalizer (t.K : Set G))
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hs2 : s * s ∈ t.PX X)
    {t' : G} (ht' : t' ∈ t.Qv 0) (ht'N : t' ∈ normalizer (t.PX X : Set G))
    (hst' : ⁅s, t'⁆ ∈ t.PX X)
    (hmax : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ t.EX X 1 → t.MX X 1 ≤ normalizer (R : Set G) →
      t.K ≤ normalizer (R : Set G) → s ∈ normalizer (R : Set G) →
      t' ∉ normalizer (R : Set G)) :
    ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1) := by
  have hV : ⁅t.EX X 1, t.YX X 1⁆ ≠ ⊥ :=
    t.commutator_ne_bot hfr hq hc hE hEP hP hLY
  intro hVE2
  let M : Subgroup G := t.MX X 1
  let P : Subgroup G := t.PX X
  let E : Subgroup G := t.EX X 1
  let E2 : Subgroup G := t.EX X (-1)
  let Y : Subgroup G := t.YX X 1
  let V : Subgroup G := ⁅E, Y⁆
  have hPM : P ≤ M := inf_le_right
  have hVnormM : M ≤ Subgroup.normalizer (V : Set G) := t.MX_le_normalizer_commutator
  have hEt2 : F53Push.cj s E2 = E := t.conjSub_s_EX_neg_one hs0 hs
  have hVtE : F53Push.cj s V ≤ E := by
    calc F53Push.cj s V ≤ F53Push.cj s E2 := F53Push.cj_mono s hVE2
      _ = E := hEt2
  have hVE : V ≤ E := t.commutator_le_EX
  let Z : Subgroup G := V ⊔ F53Push.cj s V
  have hZ_E : Z ≤ E := sup_le hVE hVtE
  let H : Subgroup G :=
    Subgroup.closure (({t'} : Set G) ∪ (t.K : Set G) ∪ (P : Set G))
  have hKH : t.K ≤ H := fun k hk =>
    Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_right _ hk))
  have hPH : P ≤ H := fun p hp => Subgroup.subset_closure (Set.mem_union_right _ hp)
  have ht'H : t' ∈ H :=
    Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton t')))
  have hcsH : F53Push.cj s H ≤ H := t.cj_s_closure_t'_K_PX hfr hX.1 hs0 hsK hs hst'
  have hZfix : F53Push.cj s Z = Z :=
    cj_sup_cj_eq (s := s) (hPM hs2 |> fun h => hVnormM h)
  set R : Subgroup G := F53Push.conjJoin H Z with hRdef
  have hHnR : H ≤ Subgroup.normalizer (R : Set G) := by
    simpa [hRdef] using F53Push.le_normalizer_conjJoin H Z
  have hsN : s ∈ Subgroup.normalizer (R : Set G) := by
    refine mem_normalizer_conjJoin_of_cj hHnR hcsH hZfix ?_
    simpa [pow_two] using hPH hs2
  have hHnormE : H ≤ Subgroup.normalizer (E : Set G) :=
    t.closure_t'_K_PX_le_normalizer hfr hX.1 hEP ht' ht'N
  have hRE : R ≤ E := by
    rw [hRdef]
    exact F53Push.conjJoin_le_of_le hZ_E hHnormE
  have hVR : V ≤ R := by
    rw [hRdef]
    exact (le_sup_left : V ≤ Z).trans (F53Push.le_conjJoin (X := H) (J := Z))
  have hRY : ⁅R, Y⁆ ≤ R := by
    have h1 : ⁅R, Y⁆ ≤ ⁅E, Y⁆ := Subgroup.commutator_mono hRE le_rfl
    exact h1.trans hVR
  have hYnR : Y ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hRY
  have hMnR : M ≤ Subgroup.normalizer (R : Set G) := by
    rw [show M = t.MX X 1 from rfl, hMK, hLY]
    exact sup_le (sup_le hYnR (hPH.trans hHnR)) (hKH.trans hHnR)
  have hRne : R ≠ ⊥ := fun hbot => hV (le_bot_iff.mp (hbot ▸ hVR))
  exact (hmax R hRne hRE hMnR (hKH.trans hHnR) hsN) (hHnR ht'H)

private theorem Qv_neg_one_le_Gw {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv (-1) ≤ t.Gw (-1) 0 := by
  have hGv0 : t.Qv (-1) ≤ t.Gv 0 := by
    have h := (t.Qv_le_Gv hfr (-1)).2
    rwa [show (-1 : ℤ) + 1 = 0 from by norm_num] at h
  intro q hq
  rw [mem_win_iff]
  intro i h1 h2
  rcases (show i = -1 ∨ i = 0 by omega) with rfl | rfl
  · exact t.Qv_le_Gv_self (-1) hq
  · exact hGv0 hq

private theorem rootOmega_neg_one_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.rootOmega (-1) = pCoreOf 2 (t.Gw (-1) 0) := by
  have hodd : ¬ Even (-1 : ℤ) := by
    rintro ⟨k, hk⟩
    omega
  have hΩR : t.rootOmega (-1) ≤ pCoreOf 2 (t.Gw (-1) 0) := by
    intro x hx
    have hx' := (mem_rootOmega_iff t hfr (-1)).mp hx
    rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at hx'
    exact hx'.1
  have hQ_R : t.Qv (-1) ≤ pCoreOf 2 (t.Gw (-1) 0) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Qv (-1)) (t.Qv_neg_one_le_Gw hfr)
  have hrelΩ : (t.Qv (-1)).relIndex (t.rootOmega (-1)) = 2 ^ f := by
    have h := t.relIndex_rootOmega hfr (-1)
    rw [if_neg hodd] at h
    exact h
  have hrelR : (t.Qv (-1)).relIndex (pCoreOf 2 (t.Gw (-1) 0)) = 2 ^ f := by
    have h := (t.relIndex_Qv_pCoreOf hfr (-1)).2
    rw [show (-1 : ℤ) + 1 = 0 from by norm_num, if_neg hodd] at h
    exact h
  refine le_antisymm hΩR ?_
  have hprod := Subgroup.relIndex_mul_relIndex (H := t.Qv (-1)) (K := t.rootOmega (-1))
    (L := pCoreOf 2 (t.Gw (-1) 0)) (t.Qv_le_rootOmega hfr (-1)) hΩR
  rw [hrelΩ, hrelR] at hprod
  have hunit : (t.rootOmega (-1)).relIndex (pCoreOf 2 (t.Gw (-1) 0)) = 1 := by
    have h : 2 ^ f * (t.rootOmega (-1)).relIndex (pCoreOf 2 (t.Gw (-1) 0)) =
        2 ^ f * 1 := by
      rw [mul_one]
      exact hprod
    exact Nat.mul_left_cancel (by positivity) h
  exact Subgroup.relIndex_eq_one.mp hunit

private theorem PX_le_sup_commutator_EX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hEP : t.EX X 1 ≤ t.PX X)
    (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K) {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hPp : IsPGroup 2 (t.PX X))
    (hnot : ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1)) :
    t.PX X ≤ ⁅t.EX X 1, t.YX X 1⁆ ⊔ t.EX X (-1) ⊔ t.Qv (-1) := by
  let E2 : Subgroup G := t.EX X (-1)
  let P : Subgroup G := t.PX X
  let V : Subgroup G := ⁅t.EX X 1, t.YX X 1⁆
  let Xs : Subgroup G := V ⊔ E2
  have hE2P : E2 ≤ P := t.EX_neg_one_le_PX hfr hs0 hs hEP
  have hVP : V ≤ P := t.commutator_le_EX.trans hEP
  have hXsP : Xs ≤ P := sup_le hVP hE2P
  have hGv0 : t.Qv 0 ≤ t.Gv 0 := t.Qv_le_Gv_self 0
  have hGvm1 : t.Qv 0 ≤ t.Gv (-1) := by
    have h := (t.Qv_le_Gv hfr 0).1
    rwa [show (0 : ℤ) - 1 = -1 from by norm_num] at h
  have hPGw : P ≤ t.Gw (-1) 0 := by
    intro p hp
    rw [mem_win_iff]
    intro i h1 h2
    rcases (show i = -1 ∨ i = 0 by omega) with rfl | rfl
    · exact hGvm1 (Subgroup.mem_inf.mp hp).1
    · exact hGv0 (Subgroup.mem_inf.mp hp).1
  have hPsubR : P ≤ pCoreOf 2 (t.Gw (-1) 0) :=
    t.le_pCoreOf_Gw hfr (by omega) hPp hPGw
  have hXsubR : Xs ≤ pCoreOf 2 (t.Gw (-1) 0) := hXsP.trans hPsubR
  have hKXs : t.K ≤ Subgroup.normalizer (Xs : Set G) :=
    CFSG.Quasithin.D14.le_normalizer_sup (t.K_le_normalizer_commutator hMK)
      (t.K_le_normalizer_EX_neg hX)
  have hnotXs : ¬ Xs ≤ t.Qv (-1) := by
    intro hle
    apply hnot
    have hVQ : V ≤ t.Qv (-1) := (le_sup_left : V ≤ Xs).trans hle
    have hVN : V ≤ Subgroup.normalizer (X : Set G) := t.commutator_le_EX.trans inf_le_right
    have h1 : V ≤ t.Qv (-1) ⊓ Subgroup.normalizer (X : Set G) := le_inf hVQ hVN
    have h2 : t.Qv (-1) ⊓ Subgroup.normalizer (X : Set G) = E2 := rfl
    exact h1.trans_eq h2
  have hΩsup : t.rootOmega (-1) ≤ Xs ⊔ t.Qv (-1) :=
    t.rootOmega_le_sup hfr (-1) hXsubR hKXs hnotXs
  calc P ≤ pCoreOf 2 (t.Gw (-1) 0) := hPsubR
    _ = t.rootOmega (-1) := (t.rootOmega_neg_one_eq hfr).symm
    _ ≤ Xs ⊔ t.Qv (-1) := hΩsup
    _ = V ⊔ E2 ⊔ t.Qv (-1) := rfl

private theorem PX_eq_sup_commutator_EX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hEP : t.EX X 1 ≤ t.PX X)
    (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K) {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hPp : IsPGroup 2 (t.PX X))
    (hnot : ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1)) :
    t.PX X = ⁅t.EX X 1, t.YX X 1⁆ ⊔ t.EX X (-1) := by
  let E2 : Subgroup G := t.EX X (-1)
  let V : Subgroup G := ⁅t.EX X 1, t.YX X 1⁆
  let Xs : Subgroup G := V ⊔ E2
  have hE2P : E2 ≤ t.PX X := t.EX_neg_one_le_PX hfr hs0 hs hEP
  have hVP : V ≤ t.PX X := t.commutator_le_EX.trans hEP
  have hXsP : Xs ≤ t.PX X := sup_le hVP hE2P
  have hPle : t.PX X ≤ Xs ⊔ t.Qv (-1) :=
    t.PX_le_sup_commutator_EX_neg hfr hX hEP hMK hs0 hs hPp hnot
  have hQ0Gvm1 : t.Qv 0 ≤ t.Gv (-1) := by
    have h := (t.Qv_le_Gv hfr 0).1
    rwa [show (0 : ℤ) - 1 = -1 from by norm_num] at h
  have hXsNQ : Xs ≤ Subgroup.normalizer (t.Qv (-1) : Set G) :=
    (hXsP.trans inf_le_left).trans (hQ0Gvm1.trans (t.Gv_le_normalizer_Qv (-1)))
  refine le_antisymm ?_ hXsP
  show t.PX X ≤ Xs
  intro p hp
  have h1 : (p : G) ∈ (↑(Xs ⊔ t.Qv (-1)) : Set G) := hPle hp
  have hcoe : (↑(Xs ⊔ t.Qv (-1)) : Set G) = (Xs : Set G) * (t.Qv (-1) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Xs (t.Qv (-1)) hXsNQ
  rw [hcoe] at h1
  obtain ⟨x, hx, q, hq, hpq⟩ := Set.mem_mul.mp h1
  have hxP : x ∈ t.PX X := hXsP hx
  have hqP : q ∈ t.PX X := by
    have h2 : x⁻¹ * p ∈ t.PX X := (t.PX X).mul_mem ((t.PX X).inv_mem hxP) hp
    rw [← hpq] at h2
    simpa using h2
  have hqE2 : q ∈ E2 := by
    refine Subgroup.mem_inf.mpr ⟨hq, ?_⟩
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hqP).2).1
  have hmem : x * q ∈ Xs ⊔ E2 :=
    (Xs ⊔ E2).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hqE2)
  rw [← hpq]
  exact (sup_le le_rfl (le_sup_right : E2 ≤ V ⊔ E2)) hmem

private theorem sqClosure_EX_eq_sqClosure_EX_neg
    {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1))
    (hnc : NoCharNormal (t.PX X) (t.LX X 1))
    (hPsup : t.PX X = ⁅t.EX X 1, t.YX X 1⁆ ⊔ t.EX X (-1))
    {s : G} (hs0 : s ∈ t.MX X 0) (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    sqClosure (t.EX X 1) = sqClosure (t.EX X (-1)) := by
  let E : Subgroup G := t.EX X 1
  let E2 : Subgroup G := t.EX X (-1)
  let V : Subgroup G := ⁅t.EX X 1, t.YX X 1⁆
  let D : Subgroup G := E ⊓ E2
  have hE2V : E2 ≤ Subgroup.normalizer (V : Set G) :=
    ((t.EX_neg_one_le_PX hfr hs0 hs hEP).trans inf_le_right).trans
      t.MX_le_normalizer_commutator
  have hVE : V ≤ E := t.commutator_le_EX
  have hDed : E = V ⊔ D := by
    have h1 : E = E ⊓ t.PX X := (inf_eq_left.mpr hEP).symm
    have h3 : E ⊓ (V ⊔ E2) = (E ⊓ E2) ⊔ V := by
      rw [sup_comm V E2]
      exact (Subgroup.inf_sup_assoc_of_le (H := E2) (K := E) (N := V) hE2V hVE).symm
    calc E = E ⊓ t.PX X := h1
      _ = E ⊓ (V ⊔ E2) := by rw [hPsup]
      _ = (E ⊓ E2) ⊔ V := h3
      _ = V ⊔ D := by rw [sup_comm]
  have hVZ : V ≤ centerOf E :=
    (t.commutator_le_centerOf_EX hfr hq hc hE hP hnc).1
  have hVea : IsElemAbelian 2 V :=
    (t.commutator_le_centerOf_EX hfr hq hc hE hP hnc).2
  have hVcentD : V ≤ Subgroup.centralizer (D : Set G) :=
    hVZ.trans (by
      rw [centerOf]
      exact inf_le_right.trans (Subgroup.centralizer_le (s := (D : Set G)) (t := (E : Set G))
        (fun x hx => hx.1)))
  have hVsq : sqClosure V = ⊥ := sqClosure_eq_bot_iff.mpr hVea.2
  have hPhiE : sqClosure E = sqClosure D := by
    rw [hDed]
    exact sqClosure_sup_eq_right_of_central hVcentD hVsq
  have hEt2 : conjSub s E = E2 := t.conjSub_s_EX_one hs0 hs
  have hE2t : conjSub s E2 = E := t.conjSub_s_EX_neg_one hs0 hs
  have hDt : conjSub s D = D := by
    rw [show D = E ⊓ E2 from rfl, conjSub_inf, hEt2, hE2t, inf_comm]
  have hPhiE2 : sqClosure E2 = sqClosure D := by
    calc sqClosure E2 = sqClosure (conjSub s E) := by rw [hEt2]
      _ = conjSub s (sqClosure E) := (conjSub_sqClosure s E).symm
      _ = conjSub s (sqClosure D) := by rw [hPhiE]
      _ = sqClosure (conjSub s D) := conjSub_sqClosure s D
      _ = sqClosure D := by rw [hDt]
  exact hPhiE.trans hPhiE2.symm

private theorem isElemAbelian_EX_of_commutator_ne_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1)) (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K)
    (hnc : NoCharNormal (t.PX X) (t.LX X 1))
    (hPsup : t.PX X = ⁅t.EX X 1, t.YX X 1⁆ ⊔ t.EX X (-1))
    {s t' : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1))
    (ht' : t' ∈ t.Qv 0) (ht'N : t' ∈ normalizer (t.PX X : Set G))
    (hmax : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ t.EX X 1 → t.MX X 1 ≤ normalizer (R : Set G) →
      t.K ≤ normalizer (R : Set G) → s ∈ normalizer (R : Set G) →
      t' ∉ normalizer (R : Set G)) :
    IsElemAbelian 2 (t.EX X 1) := by
  let E : Subgroup G := t.EX X 1
  let E2 : Subgroup G := t.EX X (-1)
  let H0 : Subgroup G := sqClosure E
  have hPhi : sqClosure E = sqClosure E2 :=
    t.sqClosure_EX_eq_sqClosure_EX_neg hfr hq hc hE hEP hP hnc hPsup hs0 hs
  have hH0E : H0 ≤ E := sqClosure_le E
  have hM0N : t.MX X 1 ≤ Subgroup.normalizer (H0 : Set G) :=
    t.MX_le_normalizer_EX.trans (normalizer_le_normalizer_sqClosure E)
  have hK0N : t.K ≤ Subgroup.normalizer (H0 : Set G) :=
    (t.K_le_normalizer_EX hMK).trans (normalizer_le_normalizer_sqClosure E)
  have hsN : s ∈ Subgroup.normalizer (H0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub s H0 = H0
    rw [show H0 = sqClosure E from rfl, conjSub_sqClosure, t.conjSub_s_EX_one hs0 hs, ← hPhi]
  have htN : t' ∈ Subgroup.normalizer (H0 : Set G) := by
    have hQ1 : t' ∈ Subgroup.normalizer (t.Qv 1 : Set G) := by
      have hGv : t' ∈ t.Gv 1 := by
        have h := (t.Qv_le_Gv hfr 0).2 ht'
        rwa [show (0 : ℤ) + 1 = 1 from by norm_num] at h
      exact (t.Gv_le_normalizer_Qv 1) hGv
    have hE' : E = t.Qv 1 ⊓ t.PX X := t.EX_eq_inf_PX hEP
    have h1 : t' ∈ Subgroup.normalizer (E : Set G) := by
      rw [hE']
      exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hQ1, ht'N⟩)
    exact normalizer_le_normalizer_sqClosure E h1
  have hBot : H0 = ⊥ := by
    by_contra hne
    exact (hmax H0 hne hH0E hM0N hK0N hsN) htN
  exact isElemAbelian_of_sqClosure_eq_bot hBot

theorem ArcLMax.isElemAbelian_EX
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1)) (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K)
    (hLY : t.LX X 1 = t.YX X 1 ⊔ t.PX X)
    (hnc : NoCharNormal (t.PX X) (t.LX X 1))
    {s : G} (hs0 : s ∈ t.MX X 0) (hsK : s ∈ normalizer (t.K : Set G))
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hs2 : s * s ∈ t.PX X)
    {t' : G} (ht' : t' ∈ t.Qv 0)
    (ht'N : t' ∈ normalizer (t.PX X : Set G))
    (hst' : ⁅s, t'⁆ ∈ t.PX X)
    (hmax : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ t.EX X 1 → t.MX X 1 ≤ normalizer (R : Set G) →
      t.K ≤ normalizer (R : Set G) → s ∈ normalizer (R : Set G) →
      t' ∉ normalizer (R : Set G)) :
    IsElemAbelian 2 (t.EX X 1) ∧
      St84.NatQuot (t.LX X 1) (t.EX X 1) (centerOf (t.LX X 1)) f := by
  have hnot : ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1) :=
    ArcLMax.not_commutator_le_EX_neg_one t hfr hX hq hc hE hEP hP hMK hLY hs0 hsK hs
      hs2 ht' ht'N hst' hmax
  have hPsup : t.PX X = ⁅t.EX X 1, t.YX X 1⁆ ⊔ t.EX X (-1) :=
    t.PX_eq_sup_commutator_EX_neg hfr hX.1 hEP hMK hs0 hs hP.2.1 hnot
  have hEab : IsElemAbelian 2 (t.EX X 1) :=
    t.isElemAbelian_EX_of_commutator_ne_bot hfr hq hc hE hEP hP hMK hnc hPsup hs0 hs
      ht' ht'N hmax
  refine ⟨hEab, ?_⟩
  have he : IsElemAbelian 2 (pCoreOf 2 (t.LX X 1)) := hE.symm ▸ hEab
  obtain ⟨hnat, -⟩ := CFSG.Quasithin.St84.natQuot_of_isL2Quot (L := t.LX X 1) (P := t.PX X)
    (n := f) (by have := hfr.hf; omega) hc hq hP hnc he
  rwa [hE] at hnat

end Track

end CFSG.Quasithin.Stroth.Rq

end
