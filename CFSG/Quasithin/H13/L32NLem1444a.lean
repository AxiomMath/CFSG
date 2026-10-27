module

public import CFSG.Quasithin.H13.L32NThm14326
public import CFSG.Quasithin.H13.L32NLem14323
public import CFSG.Quasithin.H13.L32NLem14332f
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L1444

section General

variable {A : Type*} [Group A]

theorem oTwoUpper_subgroupOf_self [Finite A] (X : Subgroup A) :
    (oTwoUpper X).subgroupOf X = oTwoUpper (⊤ : Subgroup ↥X) := by
  have h := oTwoUpper_map X.subtype (⊤ : Subgroup ↥X)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [h]
  exact A4.subgroupOf_map_subtype' X _

theorem oTwoUpper_top_map [Finite A] {B : Type*} [Group B] (f : A →* B)
    (hf : Function.Surjective f) :
    (oTwoUpper (⊤ : Subgroup A)).map f = oTwoUpper (⊤ : Subgroup B) := by
  rw [← oTwoUpper_map, Subgroup.map_top_of_surjective f hf]

theorem oTwoUpper_top_eq_of_index_two {N : Subgroup A} (hN : N.index = 2)
    (h3 : ∀ x ∈ N, x ^ 3 = 1) : oTwoUpper (⊤ : Subgroup A) = N := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨-, m, hm⟩
    have hx1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hm, pow_succ, pow_mul] at hx1
    have hx : x = ((x ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hx1
    rw [SetLike.mem_coe, hx]
    exact N.inv_mem (N.pow_mem (Subgroup.sq_mem_of_index_two hN x) m)
  · intro x hx
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top x) ?_
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (h3 x hx))

theorem isElemAbelian_of_mulEquiv {B : Type*} [Group B] {p : ℕ} {X : Subgroup A}
    {Y : Subgroup B} (e : ↥X ≃* ↥Y) (h : IsElemAbelian p Y) : IsElemAbelian p X := by
  refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact h.1.is_comm.comm _ _
  · have h1 := h.2 _ (e ⟨x, hx⟩).2
    have h2 : e (⟨x, hx⟩ ^ p) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by simpa using h1)
    have h3 : (⟨x, hx⟩ : ↥X) ^ p = 1 := by
      rw [← e.map_eq_one_iff]
      exact h2
    simpa using congrArg Subtype.val h3

end General

@[expose] def s33Three : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) where
  carrier := {x | x ^ 3 = 1}
  mul_mem' {a b} ha hb := by
    have key : ∀ a b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), a ^ 3 ≠ 1 ∨ b ^ 3 ≠ 1 ∨
        (a * b) ^ 3 = 1 := by
      decide +kernel
    rcases key a b with h1 | h1 | h1
    · exact absurd ha h1
    · exact absurd hb h1
    · exact h1
  one_mem' := one_pow 3
  inv_mem' {a} ha := by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

theorem s33_pow_six : ∀ x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), x ^ 6 = 1 := by
  decide +kernel

theorem s33Three_comm' : ∀ a b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), a ^ 3 ≠ 1 ∨
    b ^ 3 ≠ 1 ∨ a * b = b * a := by
  decide +kernel

theorem s33Three_comm (a b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : a * b = b * a := by
  rcases s33Three_comm' a b with h1 | h1 | h1
  · exact absurd ha h1
  · exact absurd hb h1
  · exact h1

theorem card_s33Three_filter :
    (Finset.univ.filter fun x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) => x ^ 3 = 1).card =
      9 := by
  decide +kernel

theorem card_s33Three : Nat.card s33Three = 9 := by
  classical
  rw [← card_s33Three_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

theorem isElemAbelian_s33Three : IsElemAbelian 3 s33Three :=
  ⟨⟨⟨fun a b => Subtype.ext (s33Three_comm a b a.2 b.2)⟩⟩, fun _ hx => hx⟩

theorem oTwoUpper_top_s33 :
    oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) = s33Three := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨-, ho⟩
    have h6 : orderOf x ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one (s33_pow_six x)
    have hc : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr ho
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left h6)
  · intro x hx
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top x) ?_
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx)

variable {G : Type} [Group G]

theorem comm_mem_centerOf {U : Subgroup G} (hext : CFSG.IsExtraspecialPGroup 2 ↥U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U := by
  intro a ha b hb
  have hc : ⁅(⟨a, ha⟩ : ↥U), ⟨b, hb⟩⁆ ∈ Subgroup.center ↥U := by
    rw [← hext.2.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcoe : ((⁅(⟨a, ha⟩ : ↥U), ⟨b, hb⟩⁆ : ↥U) : G) = a * b * a⁻¹ * b⁻¹ := by
    simp [commutatorElement_def]
  rw [← hcoe]
  refine ⟨Subtype.coe_prop _, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have := (Subgroup.mem_center_iff.mp hc) ⟨u, hu⟩
  exact congrArg Subtype.val this

theorem img_eq_bot_of_le {U : Subgroup G} (D : HatModelU U)
    (hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U) {K : Subgroup G} (hK : K ≤ U) :
    D.img K = ⊥ := by
  unfold HatModelU.img
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker]
  exact L128A.HatU.rho_eq_one_of_mem D hc (hK hx) x.2

variable [Finite G] {T L V : Subgroup G}

theorem zU_eq (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) : centerOf (fsuU T V) = fsuV1 T V := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨V₂, hV₂⟩ := h.exists_plane hV
  obtain ⟨⟨U₀, -, hU₀ext, hΦ, hU₀Z⟩, -⟩ :=
    lemma12_8_8_n3 h1222 h12213 (h.setting1282One h13322 hV hV₂)
  have hV1Z := fsuV1_le_centerOf_of_decomp hU₀Z hU₀ext hΦ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  exact (Subgroup.eq_of_le_of_card_ge hV1Z (by rw [hZ2, hV1])).symm

theorem cHat_eq (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) :
    l32nCHat T V = pCoreOf 2 (l32nH T V) := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have h1281 := h.hyp1281One h13322 hV
  have hZ := zU_eq h1332 h1334 h1222 h12213 h hext
  show centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) = _
  rw [hZ]
  exact (lemma12_8_4 h1222 h37 h38 h39 G T L V 3 h1281 (fsuV1 T V) (l32nH T V)
    (h.isTSub_fsuV1 hV) (h.isHzOne_l32nH h13322 hV (lemma12_8_3 h12213))).2.2.2

omit [Finite G] in
theorem imgHom_ker_eq {D : HatModelU (fsuU T V)} (hC : l32nCHat T V = pCoreOf 2 (l32nH T V)) :
    (L14332.imgHom D).ker = CFSG.Open.pCore 2 ↥(l32nH T V) := by
  rw [L14332.imgHom_ker, hC]
  exact A4.subgroupOf_map_subtype' _ _

noncomputable def mulEquivHdot (D : HatModelU (fsuU T V))
    (hC : l32nCHat T V = pCoreOf 2 (l32nH T V)) :
    OTwoQuot (l32nH T V) ≃* ↥(D.img (l32nH T V)) :=
  (QuotientGroup.quotientMulEquivOfEq (imgHom_ker_eq hC).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (L14332.imgHom_surjective D))

theorem imageOTwoQuot_oTwoUpper (H : Subgroup G) :
    imageOTwoQuot H (oTwoUpper H) = oTwoUpper (⊤ : Subgroup (OTwoQuot H)) := by
  rw [imageOTwoQuot, oTwoUpper_subgroupOf_self]
  exact oTwoUpper_top_map _ (QuotientGroup.mk'_surjective _)

noncomputable def mulEquivKStar (D : HatModelU (fsuU T V))
    (hC : l32nCHat T V = pCoreOf 2 (l32nH T V)) :
    ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) ≃*
      ↥(oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V)))) :=
  (Subgroup.equivMapOfInjective _ (mulEquivHdot D hC).toMonoidHom
    (mulEquivHdot D hC).injective).trans
    (MulEquiv.subgroupCongr (by
      rw [imageOTwoQuot_oTwoUpper]
      exact oTwoUpper_top_map _ (mulEquivHdot D hC).surjective))

end L1444

open L1444 in
theorem lemma1444One_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest) : Lemma1444One := by
  intro G _ _ T L V h hext h32 _
  classical
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
  have hZ := zU_eq h1332 h1334 h1222 h12213 h hext
  have hC := cHat_eq h1332 h1334 h1222 h12213 h37 h38 h39 h hext
  have hd : Module.finrank (ZMod 2) D.V = 4 := by
    have hcard := D.card_U
    rw [hZ, hV1, h32] at hcard
    have h16 : Nat.card D.V = 2 ^ 4 := by omega
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)
    rw [h16, Nat.card_zmod] at hpow
    exact (Nat.pow_right_injective (le_refl 2) hpow).symm
  obtain ⟨-, hcases, -, -⟩ := hRest G T L V h V₂ g hV₂ hgP hgH D hd
  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hZgU : CFSG.conjugate (centerOf (fsuU T V)) g ≤ fsuU T V := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hZ] at hx
    have hxV₂ : x ∈ V₂ := hV₂.2 hx
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgN) x).mp hxV₂
    have hV₂V : V₂ ≤ V := hV₂.1.1
    exact le_conjClosure V _ (hV₂V (by simpa using h1))
  have hZg : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = ⊥ :=
    img_eq_bot_of_le D (comm_mem_centerOf hext) hZgU
  set e := mulEquivKStar D hC
  rcases hcases with hi | hii | hiii | hiv
  · obtain ⟨e₁⟩ := hi.iso
    have e₂ : ↥(oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V)))) ≃* ↥s33Three :=
      (Subgroup.equivMapOfInjective _ e₁.toMonoidHom e₁.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [← oTwoUpper_top_s33]
          exact oTwoUpper_top_map _ e₁.surjective))
    exact ⟨isElemAbelian_of_mulEquiv (e.trans e₂) isElemAbelian_s33Three,
      by rw [Nat.card_congr (e.trans e₂).toEquiv, card_s33Three]⟩
  · exfalso
    have h2 := hii.card_zU
    rw [hZg, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  · exfalso
    have h2 := hiii.card_zU
    rw [hZg, Subgroup.card_bot] at h2
    omega
  · obtain ⟨N, -, hNe, hN9, hN2⟩ := hiv.e9
    have hNeq : oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V))) = N :=
      oTwoUpper_top_eq_of_index_two hN2 hNe.2
    have e₂ : ↥(oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V)))) ≃* ↥N :=
      MulEquiv.subgroupCongr hNeq
    exact ⟨isElemAbelian_of_mulEquiv (e.trans e₂) hNe,
      by rw [Nat.card_congr (e.trans e₂).toEquiv, hN9]⟩

end CFSG.Quasithin.H13
