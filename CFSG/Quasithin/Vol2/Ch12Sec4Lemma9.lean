module

public import CFSG.Quasithin.Background.AutOnElemAb
public import CFSG.Quasithin.Vol2.Ch12Sec4Post
public import CFSG.Quasithin.Vol2.Ch12Sec4Mod
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Vocab
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma1
public import CFSG.Quasithin.Vol2.Ch12Sec4Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_conjugate_iff_mul_mem {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H :=
  mem_conjSubgroup_iff

theorem card_conjugate_eq (H : Subgroup G) (g : G) : Nat.card (CFSG.conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_conjugate_inv' (H : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate H g) g⁻¹ = H := by
  show conjSubgroup (conjSubgroup H g) g⁻¹ = H
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem conjugate_inv_conjugate' (H : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate H g⁻¹) g = H := by
  show conjSubgroup (conjSubgroup H g⁻¹) g = H
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem conjugate_eq_of_mem_normalizer' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : CFSG.conjugate H g = H := by
  ext x
  rw [mem_conjugate_iff_mul_mem]
  exact (Subgroup.mem_normalizer_iff.1 hg x).symm

theorem conjugate_le_normalizer_conjugate {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (g : G) :
    CFSG.conjugate H g ≤ Subgroup.normalizer (CFSG.conjugate K g : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjugate_iff_mul_mem, mem_conjugate_iff_mul_mem]
  have h1 := Subgroup.mem_normalizer_iff.1 (hHK (mem_conjugate_iff_mul_mem.1 hx)) (g * y * g⁻¹)
  rw [show g * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ by group]
  exact h1

theorem conjugate_inf_centralizer (H K : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊓ Subgroup.centralizer (K : Set G)) g =
      CFSG.conjugate H g ⊓ Subgroup.centralizer (CFSG.conjugate K g : Set G) := by
  ext x
  rw [Subgroup.mem_inf, mem_conjugate_iff_mul_mem, mem_conjugate_iff_mul_mem, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun hx y hy => ?_, fun hx k hk => ?_⟩
  · have h1 := hx _ (mem_conjugate_iff_mul_mem.1 hy)
    rw [show g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ by group,
      show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · have hk' : g⁻¹ * k * g ∈ CFSG.conjugate K g := by
      rw [mem_conjugate_iff_mul_mem, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
      exact hk
    have h1 := hx _ hk'
    calc k * (g * x * g⁻¹) = g * (g⁻¹ * k * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * k := by group

theorem conjugate_le_centralizer_conjugate {H K : Subgroup G}
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) (g : G) :
    CFSG.conjugate H g ≤ Subgroup.centralizer (CFSG.conjugate K g : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := Subgroup.mem_centralizer_iff.1 (hHK (mem_conjugate_iff_mul_mem.1 hx)) _
    (mem_conjugate_iff_mul_mem.1 hy)
  rw [show g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ by group,
    show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at h1
  exact mul_left_cancel (mul_right_cancel h1)

theorem conj_mem_autOn_iff {L V : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (φ : MulAut ↥V) :
    φ ∈ autOn L V ↔ conjAct V ⟨x, hxV⟩ * φ * (conjAct V ⟨x, hxV⟩)⁻¹ ∈ autOn L V := by
  have key : ∀ (y : G) (hyL : y ∈ Subgroup.normalizer (L : Set G))
      (hyV : y ∈ Subgroup.normalizer (V : Set G)), ∀ ψ ∈ autOn L V,
      conjAct V ⟨y, hyV⟩ * ψ * (conjAct V ⟨y, hyV⟩)⁻¹ ∈ autOn L V := by
    intro y hyL hyV ψ hψ
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    exact (Subgroup.mem_normalizer_iff.1 hyL _).1 hh
  refine ⟨key x hxL hxV φ, fun h => ?_⟩
  have h1 := key x⁻¹ (inv_mem hxL) (inv_mem hxV) _ h
  have e : conjAct V ⟨x⁻¹, inv_mem hxV⟩ = (conjAct V ⟨x, hxV⟩)⁻¹ :=
    map_inv (conjAct V) ⟨x, hxV⟩
  rw [e, inv_inv,
    show (conjAct V ⟨x, hxV⟩)⁻¹ * (conjAct V ⟨x, hxV⟩ * φ * (conjAct V ⟨x, hxV⟩)⁻¹) *
      conjAct V ⟨x, hxV⟩ = φ by group] at h1
  exact h1

theorem autOn_le_normalizer_autOn_of_le {L V M : Subgroup G}
    (hML : M ≤ Subgroup.normalizer (L : Set G)) :
    autOn M V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hML

theorem isElemAbelian2_autOn' {X V : Subgroup G} [IsMulCommutative ↥V]
    (hX : IsElemAbelian 2 X) : IsElemAbelian2 (autOn X V) :=
  CFSG.Quasithin.AutOn.isElemAbelian2_autOn hX

theorem mem_commutator_of_fixV_le {V X : Subgroup G} [IsMulCommutative ↥V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) {z : G} (hzV : z ∈ V)
    (hz : (⟨z, hzV⟩ : ↥V) ∈ commV (autOn X V)) : z ∈ ⁅V, X⁆ := by
  rw [← map_commV_autOn hXV]
  exact ⟨_, hz, rfl⟩

theorem mem_commutator_of_l3 {L V X : Subgroup G} [IsMulCommutative ↥V]
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hV16 : Nat.card V = 2 ^ 4)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1)
    (hcomm : commV (autOn L V) = ⊤) {z : G} (hzV : z ∈ V)
    (hzL : z ∈ Subgroup.centralizer (L : Set G))
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXel : IsElemAbelian 2 X) (hne : ¬ X ≤ Subgroup.centralizer (V : Set G)) :
    z ∈ ⁅V, X⁆ := by
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV16]; norm_num)
  obtain ⟨x, hxX, hxC⟩ : ∃ x ∈ X, x ∉ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hne fun y hy => h y hy
  set a := conjAct V ⟨x, hXV hxX⟩ with ha
  have ha1 : a ≠ 1 := fun h => hxC (A4.conjAct_eq_one_iff.1 h)
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow]
    have : (⟨x, hXV hxX⟩ : Subgroup.normalizer (V : Set G)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hXel.2 x hxX)
    rw [this, map_one]
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hsq w w.2)
  have h1 := fixV_le_commV_zpowers_of_normalizes hW hV16 hnat hcomm
    (fun φ => conj_mem_autOn_iff (hXL hxX) (hXV hxX) φ) ha1 ha2
  have hzfix : (⟨z, hzV⟩ : ↥V) ∈ fixV (autOn L V) := by
    rw [fixV_autOn_eq hLV]
    exact hzL
  have haX : a ∈ autOn X V := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxX)
  exact mem_commutator_of_fixV_le hXV hzV
    (commV_le_of_le (Subgroup.zpowers_le.2 haX) (h1 hzfix))

theorem mem_commutator_of_g2 (hB46 : B46OffenderCommEqFix) [Finite G] {L V M X : Subgroup G}
    [IsMulCommutative ↥V] (hsq : ∀ v ∈ V, v ^ 2 = 1) (hLM : L ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hML : M ≤ Subgroup.normalizer (L : Set G))
    (hMC : autOn M V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥)
    (hcomm : commV (autOn L V) = ⊤)
    (hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1) {z : G} (hzV : z ∈ V)
    (hzM : z ∈ Subgroup.centralizer (M : Set G)) (hXM : X ≤ M) (hXel : IsElemAbelian 2 X)
    (hne : ¬ X ≤ Subgroup.centralizer (V : Set G)) (hXcard : Nat.card X = Nat.card V)
    (hle : Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G))) :
    z ∈ ⁅V, X⁆ := by
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hsq w w.2)
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := hXM.trans hMV
  have hA : IsA2 (autOn M V) (autOn X V) := by
    refine ⟨A4.autOn_mono hXM, fun hb => hne ?_, isElemAbelian2_autOn' hXel⟩
    intro x hx
    have h1 : conjAct V ⟨x, hXV hx⟩ ∈ autOn X V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [hb, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hr : Nat.card ↥V ≤ Nat.card (autOn X V) * Nat.card (fixV (autOn X V)) := by
    have h1 : Nat.card (autOn X V) * Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card X := by
      rw [card_autOn_eq_relIndex hXV]
      have h := Subgroup.relIndex_mul_card (X ⊓ Subgroup.centralizer (V : Set G)) X
      rwa [inf_eq_left.2 (inf_le_left : X ⊓ Subgroup.centralizer (V : Set G) ≤ X)] at h
    have h2 : Nat.card (fixV (autOn X V)) = Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [fixV_autOn_eq hXV, card_subgroupOf_eq_card_inf]
    rw [h2, ← hXcard, ← h1]
    exact Nat.mul_le_mul_left _ hle
  have h1 := fixV_le_commV_of_g2 hB46 hW (A4.autOn_mono hLM) (autOn_le_normalizer_autOn_of_le hML)
    hMC hcomm hnat hA hr
  have hzfix : (⟨z, hzV⟩ : ↥V) ∈ fixV (autOn M V) := by
    rw [fixV_autOn_eq hMV]
    exact hzM
  exact mem_commutator_of_fixV_le hXV hzV (h1 hzfix)

theorem lemma12_4_9_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h12210 : Stmt12_2_10) (h1247 : Lemma12_4_7) (hB46 : B46OffenderCommEqFix) :
    Lemma12_4_9 := by
  intro G _ _ T L V hcx hq g hAN hne hVA
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hz2, hzeq, hMz, hMV⟩ := post1244_core h331 h1222 hpre hcx hq
  obtain ⟨hc, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hVel : IsElemAbelian 2 V := ⟨hc, hsq⟩
  have hab : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
  have hnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hV1
    rw [← hcomm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
  have hzZ : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := hzeq ▸ Subgroup.mem_zpowers z
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hzeq, Nat.card_zpowers, hz2]
  have hcommGr : commV (autOn L V) = ⊤ := commV_autOn_eq_top hLV hcomm
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hLV, card_subgroupOf_eq_card_inf, hZ2]
  have hweak : ∀ h : G, z ∈ CFSG.conjugate V h → h ∈ Subgroup.normalizer (V : Set G) := by
    intro h hzh
    have h1 : (h⁻¹)⁻¹ * z * h⁻¹ ∈ V := by
      rw [inv_inv]
      exact mem_conjugate_iff_mul_mem.1 hzh
    obtain ⟨l, hl, hle⟩ := h1247 G T L V hcx hq z hzZ.1 h⁻¹ h1
    have hlz : l⁻¹ * z * l = z := by
      have h2 := Subgroup.mem_centralizer_iff.1 hzZ.2 l hl
      rw [mul_assoc, ← h2]
      group
    rw [hlz, inv_inv] at hle
    have hhz : h ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * z = h * z * h⁻¹ * h := by group
        _ = z * h := by rw [← hle]
    rw [← hMV, hMz]
    exact hhz
  have hAel : IsElemAbelian 2 (CFSG.conjugate V g) := E3.isElemAbelian_conjSubgroup hVel g
  have hBel : IsElemAbelian 2 (CFSG.conjugate V g⁻¹) := E3.isElemAbelian_conjSubgroup hVel g⁻¹
  have hAcard : Nat.card (CFSG.conjugate V g) = Nat.card V := card_conjugate_eq V g
  have hBcard : Nat.card (CFSG.conjugate V g⁻¹) = Nat.card V := card_conjugate_eq V g⁻¹
  have hBN : CFSG.conjugate V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjugate_le_normalizer_conjugate hVA g⁻¹
    rwa [conjugate_conjugate_inv'] at h1
  have hVB : V ≤ Subgroup.normalizer (CFSG.conjugate V g⁻¹ : Set G) := by
    have h1 := conjugate_le_normalizer_conjugate hAN g⁻¹
    rwa [conjugate_conjugate_inv'] at h1
  have hneA : ¬ CFSG.conjugate V g ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hne (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h)
  have hneB : ¬ CFSG.conjugate V g⁻¹ ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    have h1 := conjugate_le_centralizer_conjugate h g
    rw [conjugate_inv_conjugate'] at h1
    exact hneA (Subgroup.le_centralizer_iff.1 h1)
  have hcB1 : Nat.card ↥(CFSG.conjugate V g⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G)) := by
    rw [← card_conjugate_eq (V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G)) g⁻¹,
      conjugate_inf_centralizer, conjugate_conjugate_inv']
  have hcB2 : Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g⁻¹ : Set G)) =
      Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← card_conjugate_eq (CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) g⁻¹,
      conjugate_inf_centralizer, conjugate_conjugate_inv']
  have hside : ∀ X : Subgroup G, IsElemAbelian 2 X → X ≤ Subgroup.normalizer (V : Set G) →
      ¬ X ≤ Subgroup.centralizer (V : Set G) → Nat.card X = Nat.card V →
      Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) → z ∈ ⁅V, X⁆ := by
    intro X hXel hXN hXne hXcard hXle
    have hXL : X ≤ Subgroup.normalizer (L : Set G) := hXN.trans hMV.symm.le
    rcases hq with h3' | hU
    ·
      obtain ⟨e⟩ := h3'
      have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
        have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
        exact e.isSimpleGroup
      have h168 := card_quot_of_sl_three ⟨e⟩
      obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hs3 hnc
      have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
      have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]
      have hV16 : Nat.card V = 2 ^ 4 := by
        have hle := hcases.1 ⟨e⟩
        have hidx := four_lt_relIndex_of_simple hLV hcomm hnc hO2 hs3 (by rw [h168]; norm_num)
        have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
        rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
        have h2 := E3.relIndex_eq_two_pow hVp (V ⊓ Subgroup.centralizer (L : Set G))
        rw [h2] at hidx h1
        have hm : 3 ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) := by
          by_contra hm
          push Not at hm
          interval_cases (E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G))) <;>
            norm_num at hidx
        have h8 : 8 ≤ 2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
        rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hle ⊢
        omega
      have hnat := binaryNaturalSL_of_card_sixteen
        (fun w : ↥V => Subtype.ext (by simpa using hsq w w.2)) hV16 hGrs hGr hcommGr hfixGr
      exact mem_commutator_of_l3 hsq hV16 hLV hnat hcommGr hzZ.1 hzZ.2 hXN hXL hXel hXne
    ·
      have hsU : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
        CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
      obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hsU hnc
      have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
      have hZL : autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ := by
        have hnab : ¬ ∀ a b : autOn L V, a * b = b * a := by
          intro hall'
          obtain ⟨-, -, a, b, hab'⟩ := hyp.quasisimple
          apply hab'
          obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
          have h1 : a' * b' = b' * a' := eA.symm.injective (by
            rw [map_mul, map_mul]
            exact hall' _ _)
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
        have hnorm : ((Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
            (autOn L V)).Normal := by
          refine ⟨fun n hn x => ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
          intro y hy
          have h1 := hn y hy
          have h2 := hn (x : MulAut ↥V) x.2
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc y * (↑x * ↑n * (↑x)⁻¹) = y * (↑n * ↑x * (↑x)⁻¹) := by rw [← h2]
            _ = y * n := by group
            _ = n * y := h1
            _ = ↑n * ↑x * (↑x)⁻¹ * y := by group
            _ = ↑x * ↑n * (↑x)⁻¹ * y := by rw [h2]
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.centralizer
            (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V)) with hb | ht
        · refine eq_bot_iff.2 fun y hy => ?_
          have h1 : (⟨y, hy.1⟩ : autOn L V) ∈ (Subgroup.centralizer
              (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V) :=
            Subgroup.mem_subgroupOf.2 hy.2
          rw [hb, Subgroup.mem_bot] at h1
          exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
        · exfalso
          apply hnab
          intro a b
          have h1 : a ∈ (Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
              (autOn L V) := ht ▸ Subgroup.mem_top a
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
          exact Subtype.ext (h1 b b.2).symm
      have hMC : autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V ⊓
          Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ := by
        have h1 := (h12210 G T L V hyp).1
        exact h1.trans hZL
      have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
        rw [fixV_autOn_eq hLV]
        exact hcases.2.1 hU
      have hzM : z ∈ Subgroup.centralizer
          ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) :
            Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 : m ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [← hMz]
          exact hm.1
        exact Subgroup.mem_centralizer_singleton_iff.1 h1
      exact mem_commutator_of_g2 hB46 hsq (le_inf Subgroup.le_normalizer hLV) inf_le_right
        inf_le_left hMC hcommGr hnat hzZ.1 hzM (le_inf hXL hXN) hXel hXne hXcard hXle
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
    rcases le_total (Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)))
        (Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G))) with hle | hle
    · have hz := hside _ hAel hAN hneA hAcard hle
      have h1 : ⁅V, CFSG.conjugate V g⁆ ≤ CFSG.conjugate V g := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_of_le_normalizer hVA
      exact hweak g (h1 hz)
    · have hz := hside _ hBel hBN hneB hBcard (by rw [hcB1, hcB2]; exact hle)
      have h1 : ⁅V, CFSG.conjugate V g⁻¹⁆ ≤ CFSG.conjugate V g⁻¹ := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_of_le_normalizer hVB
      simpa using inv_mem (hweak g⁻¹ (h1 hz))
  apply hne
  rw [conjugate_eq_of_mem_normalizer' hgN]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hab

end CFSG.Quasithin.H13
