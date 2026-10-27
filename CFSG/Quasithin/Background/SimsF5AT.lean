module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.SimsF5Ah
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cl
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7E16
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Sub
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Tra
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6All
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Fz
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Mov
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem tDot_mem_M0Dot : tDot ∈ M0Dot :=
  GDot_le_M0Dot (eJ_mem_GDot {0, 1} (by decide) (by decide))

noncomputable def t1A : Ah := lamA.symm ⟨tDot, tDot_mem_M0Dot⟩

theorem atLamA_t1A : lamA t1A = ⟨tDot, tDot_mem_M0Dot⟩ :=
  MulEquiv.apply_symm_apply lamA _

theorem atK_t : ∀ j : Fin 45,
    (ahLab (((tDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ pt45 j) : ℕ) =
      (Tl.getD 20 []).getD j 0 := by
  decide +kernel

theorem atRepL_t1A :
    RepL (Tl.getD 20 []) ((t1A : Ah) : Equiv.Perm (Fin 45)) := by
  refine ⟨by decide +kernel, fun j => ?_⟩
  have h : act45 ⟨tDot, tDot_mem_M0Dot⟩ = ((t1A : Ah) : Equiv.Perm (Fin 45)) := by
    rw [← act45_lamA, atLamA_t1A]
  rw [← h]
  exact (atK_t j).symm

theorem t1A_mem_That : t1A ∈ That :=
  (mem_That_iff t1A).2 ⟨Tl.getD 20 [], t0L_mem, atRepL_t1A⟩

noncomputable def t1B : Bh :=
  ⟨t1A, That_le_Bh t1A_mem_That⟩

theorem atCoe_t1B :
    (t1B : Ah) = t1A := by
  simp only [t1B]

theorem atCom_of_mem_Ttl {l : PL} (h : l ∈ Ttl) :
    comp l (Tl.getD 20 []) = comp (Tl.getD 20 []) l := by
  have := (List.mem_filter.1 h).2
  simpa using this

theorem atCenV : ∀ l ∈ Thl, comp l l = idL → (∀ a ∈ Vl, comp l a = comp a l) → l ∈ Vl := by
  decide +kernel

theorem atCenV_elt {a : Ah} (haT : a ∈ That) (ha2 : a * a = 1)
    (hac : ∀ x ∈ VA, a * x = x * a) : a ∈ VA := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff a).1 haT
  have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
    have : (a : P45) * (a : P45) = 1 := congrArg Subtype.val ha2
    rw [this]
    exact repL_one 45)
  have hcomm : ∀ b ∈ Vl, comp l b = comp b l := by
    intro b hb
    obtain ⟨x, -, hxrep⟩ := exists_That_of_mem_Thl (Vl_mem_Thl b hb)
    exact comp_comm_of_comm hxrep hrep (hac x ((mem_VA_iff x).2 ⟨b, hb, hxrep⟩))
  exact (mem_VA_iff a).2 ⟨l, atCenV l hl hl2 hcomm, hrep⟩

theorem atCard_le {K : Subgroup Ah}
    (hKT : K ≤ That) (hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    Nat.card K ≤ 16 := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hK2 : IsPGroup 2 K := isSylowTwoOf_That_Bh.2.1.to_le hKT
  obtain ⟨X', hX'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 4) Nat.prime_two hK2
    (by norm_num; omega)
  set X : Subgroup Ah := X'.map K.subtype with hXdef
  have hXK : X ≤ K := Subgroup.map_subtype_le X'
  have hXc : Nat.card X = 16 := by
    rw [hXdef, Subgroup.card_map_of_injective K.subtype_injective, hX']
    norm_num
  have hXT : X ≤ That := hXK.trans hKT
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => hab a (hXK ha) b (hXK hb)
  have hXsq : ∀ a ∈ X, a * a = 1 := fun a ha => hsq a (hXK ha)
  obtain ⟨a, haK, haX⟩ : ∃ a ∈ K, a ∉ X := by
    by_contra h
    have := Subgroup.card_le_of_le (show K ≤ X from fun a ha => by
      by_contra hax
      exact h ⟨a, ha, hax⟩)
    omega
  have haT : a ∈ That := hKT haK
  have ha2 := hsq a haK
  have hac : ∀ x ∈ X, a * x = x * a := fun x hx => hab a haK x (hXK hx)
  rcases e16_classify hXT hXc hXab hXsq with h | h | h | h
  · rw [h] at haX hac
    exact haX (centralizer_A1 hac)
  · rw [h] at haX hac
    exact haX (centralizer_A2 hac)
  · rw [h] at haX hac
    have hmem : ∀ x ∈ A2h, yA * x * yA⁻¹ ∈ B6.conjSub yA A2h := by
      intro x hx
      rw [B6.mem_conjSub]
      have e : yA⁻¹ * (yA * x * yA⁻¹) * yA = x := by group
      rw [e]
      exact hx
    refine haX ?_
    rw [B6.mem_conjSub]
    refine centralizer_A2 (g := yA⁻¹ * a * yA) fun x hx => ?_
    have h1 := hac _ (hmem x hx)
    calc yA⁻¹ * a * yA * x = yA⁻¹ * (a * (yA * x * yA⁻¹)) * yA := by group
      _ = yA⁻¹ * ((yA * x * yA⁻¹) * a) * yA := by rw [h1]
      _ = x * (yA⁻¹ * a * yA) := by group
  · rw [h] at haX hac
    exact haX (atCenV_elt haT ha2 hac)

section Transport

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem atPre (iso : AutIso M₁ M₂) {B : Subgroup G} (hB : B ≤ iso.imgG That)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1) :
    ∃ K : Subgroup Ah, K ≤ That ∧ iso.imgG K = B ∧ (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) ∧
      ∀ a ∈ K, a * a = 1 := by
  obtain ⟨K, hKT, hKB⟩ := iso.exists_pre hB
  have hKB' : K ≤ Bh := hKT.trans That_le_Bh
  have hmemK : ∀ a : Ah, a ∈ K → ∀ h : a ∈ Bh, iso.toG ⟨a, h⟩ ∈ B := fun a ha h => by
    rw [← hKB]
    exact iso.mem_imgG.2 ⟨⟨a, h⟩, ha, rfl⟩
  refine ⟨K, hKT, hKB, ?_, ?_⟩
  · intro a ha b hb
    have h1 := hab _ (hmemK a ha (hKB' ha)) _ (hmemK b hb (hKB' hb))
    rw [← AutIso.toG_mul, ← AutIso.toG_mul] at h1
    have h2 := iso.toG_injective h1
    exact congrArg (fun x : Bh => (x : Ah)) h2
  · intro a ha
    have h1 := hsq _ (hmemK a ha (hKB' ha))
    rw [← AutIso.toG_mul, ← iso.toG_one] at h1
    have h2 := iso.toG_injective h1
    exact congrArg (fun x : Bh => (x : Ah)) h2

theorem atCard_le_G (iso : AutIso M₁ M₂) {B : Subgroup G}
    (hB : B ≤ iso.imgG That) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1) :
    Nat.card B ≤ 16 := by
  obtain ⟨K, hKT, hKB, habK, hsqK⟩ := atPre iso hB hab hsq
  rw [← hKB, iso.card_imgG (hKT.trans That_le_Bh)]
  exact atCard_le hKT habK hsqK

end Transport

section MaxElemAbelian

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem atIsElem {B : Subgroup G} (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hsq : ∀ a ∈ B, a * a = 1) : IsElemAbelian 2 B :=
  ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hab a a.2 b b.2), fun x hx => by
    rw [pow_two]
    exact hsq x hx⟩

theorem atElem_comm {B : Subgroup G} (h : IsElemAbelian 2 B) :
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
  fun a ha b hb => congrArg Subtype.val (isMulCommutative_iff.1 h.1 ⟨a, ha⟩ ⟨b, hb⟩)

theorem atElem_sq {B : Subgroup G} (h : IsElemAbelian 2 B) : ∀ a ∈ B, a * a = 1 :=
  fun a ha => by
    rw [← pow_two]
    exact h.2 a ha

theorem atConj_le_That : B6.conjSub yA A2h ≤ That := by
  intro x hx
  rw [B6.mem_conjSub] at hx
  have h1 : yA * (yA⁻¹ * x * yA) * yA⁻¹ ∈ That :=
    That.mul_mem (That.mul_mem yA_mem (A2h_le_That hx)) (That.inv_mem yA_mem)
  have e : yA * (yA⁻¹ * x * yA) * yA⁻¹ = x := by group
  rwa [e] at h1

theorem atE16_data
    (iso : AutIso M₁ M₂) {A : Subgroup G}
    (hA : A = iso.imgG A1h ∨ A = iso.imgG A2h ∨ A = B6.conjSub (iso.toG yB) (iso.imgG A2h) ∨
      A = iso.imgG VA) :
    A ≤ iso.imgG That ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
      Nat.card A = 16 := by
  rcases hA with rfl | rfl | rfl | rfl
  · have h := imgG_E16 iso (K := A1h) (fun a ha b hb => A1h_comm ha hb) fun a ha => A1h_sq ha
    exact ⟨imgG_mono' iso A1h_le_That, h.1, h.2, by
      rw [iso.card_imgG (A1h_le_That.trans That_le_Bh), card_A1h]⟩
  · have h := imgG_E16 iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
    exact ⟨imgG_mono' iso A2h_le_That, h.1, h.2, by
      rw [iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]⟩
  · have h := imgG_E16 iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
    have hc := conjSub_E16 (iso.toG yB) h.1 h.2
    refine ⟨?_, hc.1, hc.2, ?_⟩
    · rw [← iso.imgG_conjSub yB A2h]
      exact imgG_mono' iso atConj_le_That
    · rw [conjSub_card, iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
  · have h := imgG_E16 iso (K := VA) (fun a ha b hb => VA_comm ha hb) fun a ha => VA_sq ha
    exact ⟨AutIso.imgG_VA_le iso, h.1, h.2, by
      rw [iso.card_imgG VA_le_Bh, card_VA_eq]⟩

end MaxElemAbelian

theorem isMaxElemAbelian_imgG_iff
    {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) (A : Subgroup G) :
    IsMaxElemAbelian (iso.imgG That) A ↔
      (A = iso.imgG A1h ∨ A = iso.imgG A2h ∨ A = B6.conjSub (iso.toG yB) (iso.imgG A2h) ∨
        A = iso.imgG VA) := by
  constructor
  · rintro ⟨hAT, hAel, hmax⟩
    have hab := atElem_comm hAel
    have hsq := atElem_sq hAel
    obtain ⟨h1T, h1ab, h1sq, h1c⟩ := atE16_data iso (Or.inl rfl)
    have h1 : Nat.card (iso.imgG A1h) ≤ Nat.card A := hmax _ h1T (atIsElem h1ab h1sq)
    have h2 : Nat.card A ≤ 16 := atCard_le_G iso hAT hab hsq
    exact e16_G iso hAT (by omega) hab hsq
  · intro hA
    obtain ⟨hAT, hab, hsq, hc⟩ := atE16_data iso hA
    exact ⟨hAT, atIsElem hab hsq, fun B hB hBel => by
      rw [hc]
      exact atCard_le_G iso hB (atElem_comm hBel) (atElem_sq hBel)⟩

theorem atCj_eq {E : Type} [Group E] (g : E) (X : Subgroup E) :
    CFSG.ASVolI.ChF.cj g X = B6.conjSub g X := rfl

theorem cj_A2_eq
    {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) {y : G}
    (hy : y ∈ iso.imgG That) (hyt : y ∉ Subgroup.centralizer ({iso.toG t1B} : Set G)) :
    CFSG.ASVolI.ChF.cj y⁻¹ (iso.imgG A2h) = B6.conjSub (iso.toG yB) (iso.imgG A2h) := by
  obtain ⟨b, hbT, rfl⟩ := iso.mem_imgG.1 hy
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff ((b⁻¹ : Bh) : Ah)).1 (That.inv_mem hbT)
  rcases coset_check l hl with h | h
  · exfalso
    refine hyt ?_
    have hc : b⁻¹ * t1B = t1B * b⁻¹ :=
      Subtype.ext (comm_of_comp_comm atRepL_t1A hrep (atCom_of_mem_Ttl h))
    have h1 : iso.toG b⁻¹ ∈ Subgroup.centralizer ({iso.toG t1B} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← AutIso.toG_mul, ← AutIso.toG_mul, hc]
    have h2 := Subgroup.inv_mem _ h1
    rwa [← AutIso.toG_inv, inv_inv] at h2
  · have hyy : yB * yB = 1 := Subtype.ext yA_sq
    set c : Bh := yB * b⁻¹ with hc
    have hcN : (c : Ah) ∈ Subgroup.normalizer (A2h : Set Ah) :=
      mem_normalizer_A2h_of_Ttl h (repL_mul repL_yA hrep)
    have hcN' : iso.toG c ∈ Subgroup.normalizer (iso.imgG A2h : Set G) := by
      refine mem_normalizer_of_conjSub_eq ?_
      rw [← iso.imgG_conjSub c A2h, B6.conjSub_eq_self hcN]
    have e : (iso.toG b)⁻¹ = iso.toG yB * iso.toG c := by
      rw [hc, AutIso.toG_mul, AutIso.toG_inv, ← mul_assoc, ← AutIso.toG_mul, hyy, iso.toG_one,
        one_mul]
    rw [atCj_eq, e, B6.conjSub_mul, B6.conjSub_eq_self hcN']

end CFSG.Quasithin.SimsF5
