module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Vec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Odd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Count

variable {G : Type} [Group G] [Finite G]

theorem card_sup_of_card_four_eight {V A Z : Subgroup G} (hV4 : Nat.card V = 4)
    (hA8 : Nat.card A = 8) (hZ2 : Nat.card Z = 2) (hZV : Z ≤ V) (hZA : Z ≤ A)
    (hVA : V ≤ Subgroup.normalizer (A : Set G)) {v : G} (hvV : v ∈ V) (hvA : v ∉ A) :
    Nat.card ↥(V ⊔ A) = 16 := by
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hVA
  have hdvd : Nat.card ↥(V ⊓ A) ∣ 4 := hV4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : 2 ≤ Nat.card ↥(V ⊓ A) := hZ2 ▸ Subgroup.card_le_of_le (le_inf hZV hZA)
  have hne4 : Nat.card ↥(V ⊓ A) ≠ 4 := by
    intro h4
    have hVA' : V ⊓ A = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hV4])
    have : v ∈ V ⊓ A := by
      rw [hVA']
      exact hvV
    exact hvA this.2
  have hn : Nat.card ↥(V ⊓ A) = 2 := by
    have hle : Nat.card ↥(V ⊓ A) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(V ⊓ A) = n at hdvd h2 hne4 hle
    interval_cases n <;> first | rfl | (exfalso; omega)
  rw [hn, hV4, hA8] at hprod
  omega

end Count

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem card_conjClosure_core (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hKC : kOf (rhoH h) ⊓ fixV (rhoH h).range = ⊥)
    {Tb P Q₁ Q₂ : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h)))
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hpp : PlanePair Tb P Q₁ Q₂) :
    Nat.card (conjClosure (VZ T M) (oTwoUpper (HLb (resBeta (rhoH h)) Q₂))) = 2 ^ 4 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hvV, hvZ, a, c, ha, ha1, haT, hc, hvac⟩ := exists_VZ_decomp S hH h hsplit
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hvV
  have hrk₂ := (hstr.rk_commV_plane hpp).2
  have hf := hstr.fixV_Tb hpp
  obtain ⟨hQ₁P, hQ₂P, hQ₁3, hQ₂3, -, -, hsupK, hf₁, -, -⟩ := id hpp
  have hr₂ : Q₂ ≤ (resBeta (rhoH h)).range := hQ₂P.trans hstr.P_le_X
  let a' : ↥(kOf (rhoH h)) := ⟨a, ha⟩
  have ha'1 : a' ≠ 1 := fun e => ha1 (congrArg Subtype.val e)
  have ha'T : ∀ y ∈ Tb, y a' = a' := by
    intro y hy
    obtain ⟨x, hxT', rfl⟩ := Subgroup.mem_map.mp (hTb ▸ hy)
    exact Subtype.ext ((resBeta_apply _ _ _).trans
      (haT (x : G) (Subgroup.mem_subgroupOf.mp hxT') x.2))
  have hnot := hf.2 a' ha'T ha'1
  obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ : ∃ w₁ ∈ commV Q₁, ∃ w₂ ∈ commV Q₂, w₁ * w₂ = a' := by
    have : a' ∈ commV Q₁ ⊔ commV Q₂ := by
      rw [hsupK]
      exact Subgroup.mem_top _
    exact Subgroup.mem_sup.mp this
  have hw₂1 : w₂ ≠ 1 := fun e => hnot.1 (by rw [← hww, e, mul_one]; exact hw₁)
  obtain ⟨q, hqQ, hq1, -, -⟩ := exists_generator_of_prime_card hQ₂3
  obtain ⟨x₀, hx₀H, hx₀O, hx₀q⟩ := exists_mem_oTwoUpper_resBeta_eq h hr₂ hQ₂3 hqQ
  have hdmem : q a' * a'⁻¹ ∈ commV Q₂ := Subgroup.subset_closure ⟨q, hqQ, a', rfl⟩
  have hd1 : q a' * a'⁻¹ ≠ 1 := by
    intro e
    have e1 : q a' = a' := mul_inv_eq_one.mp e
    rw [← hww, map_mul, hf₁ hw₁ q hqQ] at e1
    exact hw₂1 (hstr.eq_one_of_fix_plane hQ₂3 hqQ hq1 hw₂ (mul_left_cancel e1))
  set Y : Subgroup G := conjClosure (VZ T M)
    (oTwoUpper (HLb (resBeta (rhoH h)) Q₂)) with hYdef
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVY : VZ T M ≤ Y := le_conjClosure _ _
  have hYU : Y ≤ conjClosure (VZ T M) H :=
    conjClosure_le fun x hx w hw =>
      conj_mem_UH (HLb_le _ (oTwoUpper_le _ hx)) (le_conjClosure _ _ hw)
  have hYN : oTwoUpper (HLb (resBeta (rhoH h)) Q₂) ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_conjClosure _ _
  have hxvY : x₀ * v * x₀⁻¹ ∈ Y := mem_conjClosure hx₀O hvV
  have hy₀Y : x₀ * v * x₀⁻¹ * v⁻¹ ∈ Y := Y.mul_mem hxvY (Y.inv_mem (hVY hvV))
  have hxvU : x₀ * v * x₀⁻¹ ∈ conjClosure (VZ T M) H := conj_mem_UH hx₀H hvU
  have hy₀U : x₀ * v * x₀⁻¹ * v⁻¹ ∈ conjClosure (VZ T M) H := hYU hy₀Y
  have hcls₀ : clsU h hy₀U = ((q a' * a'⁻¹ : ↥(kOf (rhoH h))) : UMod h) := by
    have e1 : clsU h hy₀U = clsU h hxvU * (clsU h hvU)⁻¹ := by
      rw [clsU_inv h hvU, clsU_mul h hxvU ((conjClosure (VZ T M) H).inv_mem hvU)]
    have e2 : clsU h hxvU = rhoH h ⟨x₀, hx₀H⟩ (clsU h hvU) :=
      (rhoH_clsU h ⟨x₀, hx₀H⟩ hvU).symm
    have hρc : rhoH h ⟨x₀, hx₀H⟩ c = c := hc _ ⟨⟨x₀, hx₀H⟩, rfl⟩
    have hρa : rhoH h ⟨x₀, hx₀H⟩ a = ((q a' : ↥(kOf (rhoH h))) : UMod h) := by
      rw [← hx₀q]
      exact (resBeta_apply _ _ a').symm
    rw [e1, e2, hvac, map_mul, hρc, hρa]
    calc ((q a' : ↥(kOf (rhoH h))) : UMod h) * c * (a * c)⁻¹
        = ((q a' : ↥(kOf (rhoH h))) : UMod h) * c / (a * c) := (div_eq_mul_inv _ _).symm
      _ = ((q a' : ↥(kOf (rhoH h))) : UMod h) / a := mul_div_mul_right_eq_div _ _ _
      _ = ((q a' * a'⁻¹ : ↥(kOf (rhoH h))) : UMod h) := by
        rw [div_eq_mul_inv]
        rfl
  have hW : ∀ e ∈ commV Q₂, (e : UMod h) ∈ Wsub h Y := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact (Wsub h Y).one_mem
    · obtain ⟨b, hb, hbd⟩ := hstr.plane_transitive hQ₂3 hrk₂ hdmem he hd1 he1
      obtain ⟨x, hxH, hxO, hxb⟩ := exists_mem_oTwoUpper_resBeta_eq h hr₂ hQ₂3 hb
      have hxy : x * (x₀ * v * x₀⁻¹ * v⁻¹) * x⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hYN hxO) _).mp hy₀Y
      have h1 := clsU_mem_Wsub h (conj_mem_UH hxH hy₀U) hxy
      have h2 : clsU h (conj_mem_UH hxH hy₀U) = (e : UMod h) := by
        rw [← rhoH_clsU h ⟨x, hxH⟩ hy₀U, hcls₀, ← resBeta_apply, hxb, hbd]
      rwa [h2] at h1
  have hAY : uHi T M H (HLb (resBeta (rhoH h)) Q₂) ≤ Y := by
    intro u hu
    have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
    obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr₂ hUu hu
    refine mem_of_clsU_mem_Wsub h hYU (hZV.trans hVY) hUu ?_
    rw [← hkc]
    exact hW k hk
  have hYle : Y ≤ VZ T M ⊔ uHi T M H (HLb (resBeta (rhoH h)) Q₂) := by
    refine conjClosure_le fun x hx w hw => ?_
    have hxR : x ∈ HLb (resBeta (rhoH h)) Q₂ := oTwoUpper_le _ hx
    have hwU : w ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hw
    have hcomm : x * w * x⁻¹ * w⁻¹ ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₂) := by
      have h1 : x * w * x⁻¹ * w⁻¹ ∈ ⁅HLb (resBeta (rhoH h)) Q₂, conjClosure (VZ T M) H⁆ :=
        Subgroup.commutator_mem_commutator hxR hwU
      rw [Subgroup.commutator_comm] at h1
      exact Subgroup.mem_sup_left h1
    have e : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hw)
  have hYeq : Y = VZ T M ⊔ uHi T M H (HLb (resBeta (rhoH h)) Q₂) :=
    le_antisymm hYle (sup_le hVY hAY)
  have hvA : v ∉ uHi T M H (HLb (resBeta (rhoH h)) Q₂) := by
    intro hvA'
    obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr₂ hvU hvA'
    have hkac : (k : UMod h) = a * c := hkc.trans hvac
    have hcK : c ∈ kOf (rhoH h) := by
      have e : c = a⁻¹ * (k : UMod h) := by
        rw [hkac]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) k.2
    have hc1 : c = 1 := by
      have : c ∈ kOf (rhoH h) ⊓ fixV (rhoH h).range := ⟨hcK, hc⟩
      rwa [hKC, Subgroup.mem_bot] at this
    have hka : k = a' := Subtype.ext (by rw [hkac, hc1, mul_one])
    exact hnot.2 (by rw [← hka]; exact hk)
  have hA8 : Nat.card (uHi T M H (HLb (resBeta (rhoH h)) Q₂)) = 8 := by
    have h1 := relIndex_Z_uHi_eq h hsplit hr₂
    have h4 : Nat.card ↥(commV Q₂) = 4 := by
      rw [card_eq_two_pow hstr.sq, hrk₂]
      norm_num
    have h2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T)
      (uHi T M H (HLb (resBeta (rhoH h)) Q₂))
    rw [inf_eq_left.mpr (Z_le_uHi _ _ _ _), S.card_Z] at h2
    have h1' : (quasithinOmegaOneCenter T).relIndex
        (uHi T M H (HLb (resBeta (rhoH h)) Q₂)) = 4 := h1.trans h4
    rw [h1'] at h2
    omega
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hVN : VZ T M ≤ Subgroup.normalizer
      ((uHi T M H (HLb (resBeta (rhoH h)) Q₂) : Subgroup G) : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      isElemAbelian_comm hUab (uHi_le_conjClosure (HLb_le _) hx) (le_conjClosure _ _ hw))
  have hcard := card_sup_of_card_four_eight S.hyp.rank_two hA8 S.card_Z hZV (Z_le_uHi _ _ _ _) hVN
    hvV hvA
  rw [hYeq, hcard]
  norm_num

theorem e9z4_card_conjClosure (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Nat.card (conjClosure (VZ T M) (oTwoUpper R₂)) = 2 ^ 4 := by
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, -, hR₂⟩ := hdat.setup h35 S hred hshape
  subst hR₂
  exact card_conjClosure_core S hred.isHTM h98.toHypF91 hsplit
    (shape_splitting h35 S hred h98).2.1 rfl hstr hpp

end Main

end CFSG.Quasithin
