module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import Certificates.Certificate7179
import CFSG.Quasithin.Background.E1ElevenIso
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.CharacterTheory.Burnside
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.H13.A7NP

open Equiv Equiv.Perm CFSG.Quasithin
open scoped Pointwise

@[expose] def H1 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | A7EOne.inH1 σ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (hb x).trans (ha (b x))
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at h
    exact h.symm

@[expose] def H2 : Subgroup (Perm (Fin 7)) := Subgroup.centralizer {A7EOne.pInv}

theorem mem_H1 {σ : Perm (Fin 7)} : σ ∈ H1 ↔ A7EOne.inH1 σ := Iff.rfl

theorem mem_H2 {σ : Perm (Fin 7)} : σ ∈ H2 ↔ A7EOne.inH2 σ :=
  Subgroup.mem_centralizer_singleton_iff

theorem stmt_holds : A7EOne.stmt :=
  of_decide_eq_true Certificates.certificate7179

theorem card_eq_filter {P : Perm (Fin 7) → Prop} [DecidablePred P]
    {H : Subgroup (Perm (Fin 7))} (hH : ∀ σ, σ ∈ H ↔ P σ) :
    Nat.card H = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight hH)

theorem card_H1 : Nat.card H1 = 144 :=
  (card_eq_filter fun _ => mem_H1).trans stmt_holds.1

theorem card_H2 : Nat.card H2 = 48 :=
  (card_eq_filter fun _ => mem_H2).trans stmt_holds.2.1

theorem card_T0 : Nat.card ↥(H1 ⊓ H2) = 16 :=
  (card_eq_filter (H := H1 ⊓ H2) (P := fun σ => A7EOne.inH1 σ ∧ A7EOne.inH2 σ) fun σ => by
    rw [Subgroup.mem_inf, mem_H1, mem_H2]).trans stmt_holds.2.2.1

theorem card_T0A :
    Nat.card ↥(H1 ⊓ H2 ⊓ alternatingGroup (Fin 7)) = 8 :=
  (card_eq_filter (H := H1 ⊓ H2 ⊓ alternatingGroup (Fin 7))
    (P := fun σ => A7EOne.inH1 σ ∧ A7EOne.inH2 σ ∧ Perm.sign σ = 1) fun σ => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_H1, mem_H2, mem_alternatingGroup,
      and_assoc]).trans stmt_holds.2.2.2

theorem isSolvable_H1 : Group.IsSolvable H1 := by
  have := Fintype.ofFinite ↥H1
  have h : Fintype.card ↥H1 = 144 := by rw [← Nat.card_eq_fintype_card, card_H1]
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 4) (b := 2)
    Nat.prime_two Nat.prime_three (by norm_num) (h.trans (by norm_num))

theorem isSolvable_H2 : Group.IsSolvable H2 := by
  have := Fintype.ofFinite ↥H2
  have h : Fintype.card ↥H2 = 48 := by rw [← Nat.card_eq_fintype_card, card_H2]
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 4) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (h.trans (by norm_num))

theorem card_perm : Nat.card (Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alt : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isSylowIn_T0 : IsSylowIn 2 (H1 ⊓ H2) ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 4) (card_T0.trans (by norm_num)), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := (H1 ⊓ H2).card_mul_index
  rw [card_T0, card_perm] at h
  omega

theorem isSylowIn_T0A :
    IsSylowIn 2 (H1 ⊓ H2 ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)) := by
  refine ⟨inf_le_right, IsPGroup.of_card (n := 3) (card_T0A.trans (by norm_num)), ?_⟩
  have h := Subgroup.relIndex_mul_card (H1 ⊓ H2 ⊓ alternatingGroup (Fin 7))
    (alternatingGroup (Fin 7))
  rw [inf_of_le_left (inf_le_right : H1 ⊓ H2 ⊓ alternatingGroup (Fin 7) ≤ _), card_T0A,
    card_alt] at h
  omega

theorem sup_H1_H2 : H1 ⊔ H2 = ⊤ := by
  have h34 : swap (3 : Fin 7) 4 ∈ H1 ⊔ H2 := by
    have e : swap (3 : Fin 7) 4 =
        swap 1 3 * (swap 2 4 * swap 3 5 * swap 1 2 * (swap 2 4 * swap 3 5)⁻¹) * (swap 1 3)⁻¹ := by
      decide
    have h13 : swap (1 : Fin 7) 3 ∈ H1 ⊔ H2 := Subgroup.mem_sup_left (mem_H1.mpr (by decide))
    have h12 : swap (1 : Fin 7) 2 ∈ H1 ⊔ H2 := Subgroup.mem_sup_left (mem_H1.mpr (by decide))
    have h24 : swap (2 : Fin 7) 4 * swap 3 5 ∈ H1 ⊔ H2 :=
      Subgroup.mem_sup_right (mem_H2.mpr (by decide))
    rw [e]
    exact mul_mem (mul_mem h13 (mul_mem (mul_mem h24 h12) (inv_mem h24))) (inv_mem h13)
  have key : ∀ i : Fin 6, swap (Fin.castSucc i) (Fin.succ i) ∈ H1 ⊔ H2 := by
    intro i
    fin_cases i
    all_goals first
      | exact Subgroup.mem_sup_left (mem_H1.mpr (by decide))
      | exact h34
  rw [eq_top_iff]
  intro σ _
  have hσ : σ ∈ Submonoid.closure
      (Set.range fun i : Fin 6 => swap (Fin.castSucc i) (Fin.succ i)) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ 6]
    exact Submonoid.mem_top σ
  exact (Submonoid.closure_le (S := (H1 ⊔ H2).toSubmonoid)).mpr
    (by rintro _ ⟨i, rfl⟩; exact key i) hσ

theorem sup_inf_alternatingGroup :
    H1 ⊓ alternatingGroup (Fin 7) ⊔ H2 ⊓ alternatingGroup (Fin 7) = alternatingGroup (Fin 7) := by
  set A := alternatingGroup (Fin 7)
  set G' := H1 ⊓ A ⊔ H2 ⊓ A with hG'
  set s : Perm (Fin 7) := swap 0 1
  have hs1 : s ∈ H1 := mem_H1.mpr (by decide)
  have hs2 : s ∈ H2 := mem_H2.mpr (by decide)
  have hsign : Perm.sign s = -1 := Perm.sign_swap (by decide)
  have hss : s * s = 1 := swap_mul_self 0 1
  have hsi : s⁻¹ = s := swap_inv 0 1
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  have hnormD : ∀ D : Subgroup (Perm (Fin 7)), s ∈ D → ∀ x ∈ D ⊓ A, s * x * s⁻¹ ∈ D ⊓ A :=
    fun D hsD x hx => Subgroup.mem_inf.mpr
      ⟨D.mul_mem (D.mul_mem hsD (Subgroup.mem_inf.mp hx).1) (D.inv_mem hsD),
        (alternatingGroup.normal (α := Fin 7)).conj_mem x (Subgroup.mem_inf.mp hx).2 s⟩
  have hmap : G'.map (MulAut.conj s).toMonoidHom ≤ G' := by
    rw [hG', Subgroup.map_sup]
    refine sup_le_sup (Subgroup.map_le_iff_le_comap.mpr fun x hx => ?_)
      (Subgroup.map_le_iff_le_comap.mpr fun x hx => ?_)
    · exact hnormD H1 hs1 x hx
    · exact hnormD H2 hs2 x hx
  have hconj : ∀ x ∈ G', s * x * s⁻¹ ∈ G' := fun x hx => hmap ⟨x, hx, rfl⟩
  have hsN : s ∈ Subgroup.normalizer (G' : Set (Perm (Fin 7))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj x, fun hx => ?_⟩
    have h1 := hconj _ hx
    have h2 : s * (s * x * s⁻¹) * s⁻¹ = x := by
      calc s * (s * x * s⁻¹) * s⁻¹ = s * s * x * (s⁻¹ * s⁻¹) := by group
        _ = x := by rw [hss, hsi, hss, one_mul, mul_one]
    rwa [h2] at h1
  have hzs : Subgroup.zpowers s ≤ Subgroup.normalizer (G' : Set (Perm (Fin 7))) :=
    Subgroup.zpowers_le.mpr hsN
  have hDi : ∀ D : Subgroup (Perm (Fin 7)), s ∈ D → D ⊓ A ≤ G' →
      D ≤ G' ⊔ Subgroup.zpowers s := by
    intro D hsD hDG h hh
    rcases Int.units_eq_one_or (Perm.sign h) with h1 | h1
    · exact Subgroup.mem_sup_left (hDG (Subgroup.mem_inf.mpr ⟨hh, mem_alternatingGroup.mpr h1⟩))
    · have hmem : h * s ∈ D ⊓ A := Subgroup.mem_inf.mpr ⟨D.mul_mem hh hsD,
        mem_alternatingGroup.mpr (by rw [map_mul, h1, hsign, Int.units_mul_self])⟩
      have e : h = h * s * s⁻¹ := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (hDG hmem))
        (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers s)))
  have htop : (⊤ : Subgroup (Perm (Fin 7))) ≤ G' ⊔ Subgroup.zpowers s := by
    rw [← sup_H1_H2]
    exact sup_le (hDi H1 hs1 le_sup_left) (hDi H2 hs2 le_sup_right)
  intro x hx
  have hx' : x ∈ ((G' : Set (Perm (Fin 7))) * (Subgroup.zpowers s : Set (Perm (Fin 7)))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left G' (Subgroup.zpowers s) hzs]
    exact htop (Subgroup.mem_top x)
  obtain ⟨v, hv, u, hu, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hGA : G' ≤ A := sup_le inf_le_right inf_le_right
  have hvA : Perm.sign v = 1 := mem_alternatingGroup.mp (hGA hv)
  have hk : s ^ k = s ^ (k % 2) := zpow_eq_zpow_emod k (by rw [zpow_two, hss])
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [hk, h0, zpow_zero, mul_one]
    exact hv
  · exfalso
    rw [hk, h0, zpow_one] at hx
    have h3 := mem_alternatingGroup.mp hx
    rw [map_mul, hvA, hsign, one_mul] at h3
    exact Int.units_ne_iff_eq_neg.mpr rfl h3

theorem inEFor_one_of_solvable {G : Type} [Group G] [Finite G] {D T : Subgroup G}
    (hD : Group.IsSolvable ↥D) (hT : IsSylowIn 2 T D) : E1.InEFor 1 D T := by
  have h := E1.solvable_nParam_le_one hD
  have h' : E1.nParam D ≤ ((1 : ℕ) : ℕ∞) := by simpa using h
  exact (E1.nParam_le_iff one_pos).mp h' T hT

theorem nParam_perm_le_one :
    E1.nParam (⊤ : Subgroup (Perm (Fin 7))) ≤ 1 := by
  have hT := isSylowIn_T0
  have hF : E1.InEFor 1 ⊤ (H1 ⊓ H2) := by
    refine E1.inEFor_of_generated hT (Δ := {H1, H2}) ?_ ?_ ?_
    · rw [iSup_pair]
      exact sup_H1_H2
    · rintro D (rfl | rfl)
      · exact inf_le_left
      · exact inf_le_right
    · rintro D (rfl | rfl)
      · exact inEFor_one_of_solvable isSolvable_H1 (B6.isSylowTwoOf_mono hT inf_le_left le_top)
      · exact inEFor_one_of_solvable isSolvable_H2 (B6.isSylowTwoOf_mono hT inf_le_right le_top)
  have h := (E1.nParam_le_iff (H := (⊤ : Subgroup (Perm (Fin 7)))) (n := 1) one_pos).mpr
    ((E1.inE_iff_inEFor hT).mpr hF)
  simpa using h

theorem nParam_alt_le_one :
    E1.nParam (alternatingGroup (Fin 7)) ≤ 1 := by
  set A := alternatingGroup (Fin 7)
  have hT := isSylowIn_T0A
  have hle1 : H1 ⊓ H2 ⊓ A ≤ H1 ⊓ A := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hle2 : H1 ⊓ H2 ⊓ A ≤ H2 ⊓ A := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hs1 : Group.IsSolvable ↥(H1 ⊓ A) := by
    have := isSolvable_H1
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : H1 ⊓ A ≤ H1))
  have hs2 : Group.IsSolvable ↥(H2 ⊓ A) := by
    have := isSolvable_H2
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : H2 ⊓ A ≤ H2))
  have hF : E1.InEFor 1 A (H1 ⊓ H2 ⊓ A) := by
    refine E1.inEFor_of_generated hT (Δ := {H1 ⊓ A, H2 ⊓ A}) ?_ ?_ ?_
    · rw [iSup_pair]
      exact sup_inf_alternatingGroup
    · rintro D (rfl | rfl)
      · exact hle1
      · exact hle2
    · rintro D (rfl | rfl)
      · exact inEFor_one_of_solvable hs1 (B6.isSylowTwoOf_mono hT hle1 inf_le_right)
      · exact inEFor_one_of_solvable hs2 (B6.isSylowTwoOf_mono hT hle2 inf_le_right)
  have h := (E1.nParam_le_iff (H := A) (n := 1) one_pos).mpr ((E1.inE_iff_inEFor hT).mpr hF)
  simpa using h

theorem nParam_le_one_of_fStar_alt7 {G : Type} [Group G]
    [Finite G] (hA7 : IsAlt 7 (ASInputs.FStar G)) : E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  set Y : Subgroup G := CFSG.generalizedFitting G
  obtain ⟨-, hYn⟩ := CFSG.LocalCores.generalized_fitting_characteristic (G := G)
  have : Y.Normal := hYn
  obtain ⟨e⟩ := hA7
  have hs7 : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card ↥Y = 2520 := by rw [Nat.card_congr e.toEquiv, card_alt]
  have hsY : IsSimpleGroup ↥Y := e.isSimpleGroup
  have hnaY : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥Y := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hsY
    rw [hcard] at hp
    norm_num at hp
  have hZ : Subgroup.center ↥Y = ⊥ :=
    CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple (↥Y) hnaY
  have hCG : Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := CFSG.centralizer_generalizedFitting_le G hx
    have hxc : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [hZ, Subgroup.mem_bot] at hxc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxc
  have hconj : Function.Injective (MulAut.conjNormal (H := Y) : G →* MulAut ↥Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥Y => ((f ⟨x, hx⟩ : ↥Y) : G)) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hCG] at hgC
    exact hgC
  let autE : Perm (Fin 7) ≃* MulAut ↥(alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num))
  let θ : G →* Perm (Fin 7) :=
    autE.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
      (MulAut.conjNormal (H := Y) : G →* MulAut ↥Y))
  have hθ : Function.Injective θ :=
    autE.symm.injective.comp ((MulAut.congr e).injective.comp hconj)
  have hAR : alternatingGroup (Fin 7) ≤ θ.range := by
    intro a ha
    obtain ⟨y, hy⟩ := e.surjective ⟨a, ha⟩
    refine MonoidHom.mem_range.mpr ⟨(y : G), ?_⟩
    apply autE.injective
    change autE (autE.symm (MulAut.congr e (MulAut.conjNormal (H := Y) (y : G)))) = autE a
    rw [MulEquiv.apply_symm_apply]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    change ((e (MulAut.conjNormal (H := Y) (y : G) (e.symm b)) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) = ((MulAut.conjNormal (H := alternatingGroup (Fin 7)) a b :
        alternatingGroup (Fin 7)) : Perm (Fin 7))
    have h1 : MulAut.conjNormal (H := Y) (y : G) (e.symm b) = y * e.symm b * y⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hy]
    simp [MulAut.conjNormal_apply]
  have hR : θ.range = alternatingGroup (Fin 7) ∨ θ.range = ⊤ := by
    by_cases h : θ.range ≤ alternatingGroup (Fin 7)
    · exact Or.inl (le_antisymm h hAR)
    · right
      rw [IsConcreteLE.not_le_iff_exists] at h
      obtain ⟨r, hrR, hrA⟩ := h
      rw [eq_top_iff]
      intro σ _
      by_cases hσ : σ ∈ alternatingGroup (Fin 7)
      · exact hAR hσ
      · have hr1 : Perm.sign r = -1 :=
          (Int.units_eq_one_or _).resolve_left fun h1 => hrA (mem_alternatingGroup.mpr h1)
        have hσ1 : Perm.sign σ = -1 :=
          (Int.units_eq_one_or _).resolve_left fun h1 => hσ (mem_alternatingGroup.mpr h1)
        have hmem : σ * r⁻¹ ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr
          (by rw [map_mul, map_inv, hσ1, hr1, mul_inv_cancel])
        have e2 : σ = σ * r⁻¹ * r := by group
        rw [e2]
        exact mul_mem (hAR hmem) hrR
  rw [E1.Eleven.nParam_top_mulEquiv (MonoidHom.ofInjective hθ), ← E1.nParam_subgroupOf]
  rcases hR with h | h
  · rw [h]
    exact nParam_alt_le_one
  · rw [h]
    exact nParam_perm_le_one

end CFSG.Quasithin.H13.A7NP

end
