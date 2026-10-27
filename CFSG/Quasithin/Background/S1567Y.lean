module

public import CFSG.Quasithin.Background.S1567Mod
public import CFSG.Quasithin.Background.S1567Cx
public import CFSG.Quasithin.Background.S1567BYE
public import CFSG.Quasithin.EmptyFaithful.T1531In66b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoUpper_sup_le {N P : Subgroup G} (hP : P ≤ Subgroup.normalizer (N : Set G))
    (hp : IsPGroup 2 P) : oTwoUpper (N ⊔ P) ≤ N := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hmulN := Subgroup.coe_mul_of_right_le_normalizer_left N P hP
  have hx' : x ∈ (N : Set G) * (P : Set G) := by rw [← hmulN]; exact hx
  obtain ⟨n, hn, p, hp', rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hp ⟨p, hp'⟩
  obtain ⟨n', hn', hnp⟩ := A4.exists_pow_mul_eq hn (hP hp') (2 ^ j)
  refine ⟨j, ?_⟩
  have hp1 : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  rw [hnp, hp1, mul_one]
  exact hn'

theorem eq_of_not_le_pCore {X N : Subgroup G} (hX : oTwoUpper X = X)
    (hidx : (pCoreOf 2 X).relIndex X = 3) (hNle : N ≤ X)
    (hNn : X ≤ Subgroup.normalizer (N : Set G)) (hnot : ¬ N ≤ pCoreOf 2 X) : N = X := by
  have hUle : N ⊔ pCoreOf 2 X ≤ X := sup_le hNle (pCoreOf_le 2 _)
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) (N ⊔ pCoreOf 2 X) X le_sup_right hUle
  rw [hidx] at hmul
  have hUX : (N ⊔ pCoreOf 2 X).relIndex X = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hmul) with h1 | h3
    · exact h1
    · exfalso
      have h1 : (pCoreOf 2 X).relIndex (N ⊔ pCoreOf 2 X) = 1 := by
        rw [h3] at hmul; omega
      exact hnot (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1))
  have hXU : X ≤ N ⊔ pCoreOf 2 X := Subgroup.relIndex_eq_one.mp hUX
  have hP₂N : pCoreOf 2 X ≤ Subgroup.normalizer (N : Set G) := (pCoreOf_le 2 _).trans hNn
  have hO2 : oTwoUpper X ≤ N :=
    (oTwoUpper_mono hXU).trans (oTwoUpper_sup_le hP₂N (pCoreOf_isPGroup 2 X))
  rw [hX] at hO2
  exact le_antisymm hNle hO2

theorem mulAut_noncomm {E : Type*} [Group E] [IsKleinFour E] (a b : MulAut E) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) : a * b ≠ b * a := by
  let e := CFSG.kleinFourAutomorphismEquivSymmetricThree E
  have key : ∀ x y : Equiv.Perm (Fin 3), x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 2 = 1 →
      x * y ≠ y * x := by decide +kernel
  intro h
  exact key (e a) (e b) (fun h' => ha1 (e.injective (by rw [h', map_one])))
    (by rw [← map_pow, ha3, map_one]) (fun h' => hb1 (e.injective (by rw [h', map_one])))
    (by rw [← map_pow, hb2, map_one]) (by rw [← map_mul, ← map_mul, h])

end General

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem exists_tau (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∃ τ ∈ pCoreOf 2 Mc, τ ∈ TE153 T E ∧ τ * τ ∈ Subgroup.centralizer (VZ T M : Set G) ∧
      ∃ e ∈ E, τ * e * τ⁻¹ ≠ e := by
  have h := k.c.hyp
  have hsylMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo h.qtfe.sylow h.qtfe.t_le_mc
  have hQT : pCoreOf 2 Mc ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylMc
  have hQn : T ≤ Subgroup.normalizer (pCoreOf 2 Mc : Set G) :=
    h.qtfe.t_le_mc.trans (le_normalizer_pCoreOf 2 Mc)
  have hQ : ¬ pCoreOf 2 Mc ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro hle
    have hcomm := k.r49.comm_ZS
    have hbot : ⁅ZS153 T M V₁, pCoreOf 2 Mc⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro z hz q hq
      have hc := Subgroup.mem_centralizer_iff.mp (hle hq) z hz.1
      have : ⁅z, q⁆ = 1 := by
        rw [commutatorElement_def, hc]; group
      rw [this]
      exact Subgroup.one_mem _
    rw [hbot] at hcomm
    have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := h.lemma_15_3_2_two.2
    have hZbot : quasithinOmegaOneCenter T = ⊥ := hcomm.symm
    rw [hZbot, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨q, hq, hqTE, hqq, hqe⟩ := exists_central_move k.c k.L hQT hQn hQ
  exact ⟨q, hq, hqTE, hqq, hqe⟩

theorem exists_comm_not_centralizer (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) {τ : G}
    (hτTE : τ ∈ TE153 T E) (hττ : τ * τ ∈ Subgroup.centralizer (VZ T M : Set G))
    (hmove : ∃ e ∈ E, τ * e * τ⁻¹ ≠ e) :
    ∃ y ∈ YE153 Mc M E, y * τ * y⁻¹ * τ⁻¹ ∉ Subgroup.centralizer (E : Set G) := by
  have := isKleinFour_E c L
  obtain ⟨-, y, hyYE, ⟨e, heE, hye⟩, hy3⟩ := Y_facts h113 c L
  have hYEN : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := hYEN hyYE
  have hτN : τ ∈ Subgroup.normalizer (E : Set G) := hτTE.2
  refine ⟨y, hyYE, fun hcomm => ?_⟩
  have hσ₃ne : conjAct E ⟨y, hyN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨y, hyN⟩).1 h
    apply hye
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e heE
    rw [← h1]
    group
  have hσ₃3 : conjAct E ⟨y, hyN⟩ ^ 3 = 1 := by
    have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le L.le_V hy3
  obtain ⟨e', he'E, hτe'⟩ := hmove
  have hσ₂ne : conjAct E ⟨τ, hτN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨τ, hτN⟩).1 h
    apply hτe'
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e' he'E
    rw [← h1]
    group
  have hσ₂2 : conjAct E ⟨τ, hτN⟩ ^ 2 = 1 := by
    have hττN : τ * τ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hτN hτN
    have e1 : conjAct E ⟨τ, hτN⟩ ^ 2 = conjAct E ⟨τ * τ, hττN⟩ := by
      rw [← map_pow, pow_two]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le L.le_V hττ
  have hcN : y * τ * y⁻¹ * τ⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hyN hτN)
        ((Subgroup.normalizer _).inv_mem hyN)) ((Subgroup.normalizer _).inv_mem hτN)
  have h1 : conjAct E ⟨y * τ * y⁻¹ * τ⁻¹, hcN⟩ = 1 := (conjAct_eq_one_iff''' E _).2 hcomm
  have h2 : conjAct E ⟨y * τ * y⁻¹ * τ⁻¹, hcN⟩ =
      conjAct E ⟨y, hyN⟩ * conjAct E ⟨τ, hτN⟩ * (conjAct E ⟨y, hyN⟩)⁻¹ * (conjAct E ⟨τ, hτN⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [h2] at h1
  apply mulAut_noncomm (conjAct E ⟨y, hyN⟩) (conjAct E ⟨τ, hτN⟩) hσ₃ne hσ₃3 hσ₂ne hσ₂2
  have h3 : conjAct E ⟨y, hyN⟩ * conjAct E ⟨τ, hτN⟩ * (conjAct E ⟨y, hyN⟩)⁻¹ *
      (conjAct E ⟨τ, hτN⟩)⁻¹ = 1 := h1
  calc conjAct E ⟨y, hyN⟩ * conjAct E ⟨τ, hτN⟩
      = (conjAct E ⟨y, hyN⟩ * conjAct E ⟨τ, hτN⟩ * (conjAct E ⟨y, hyN⟩)⁻¹ *
          (conjAct E ⟨τ, hτN⟩)⁻¹) * (conjAct E ⟨τ, hτN⟩ * conjAct E ⟨y, hyN⟩) := by group
    _ = conjAct E ⟨τ, hτN⟩ * conjAct E ⟨y, hyN⟩ := by rw [h3, one_mul]

theorem pCoreOf_Mc_le_T (c : Ctx153 G T Mc M V₁ V₂ t) : pCoreOf 2 Mc ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.qtfe.sylow c.hyp.qtfe.t_le_mc)

theorem YE_eq_commutator (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {τ : G}
    (hτQ : τ ∈ pCoreOf 2 Mc) (hτTE : τ ∈ TE153 T E)
    (hττ : τ * τ ∈ Subgroup.centralizer (VZ T M : Set G))
    (hmove : ∃ e ∈ E, τ * e * τ⁻¹ ≠ e) :
    YE153 Mc M E =
      ⁅YE153 Mc M E, pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)⁆ := by
  have hPT : pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) ≤ TE153 T E := fun x hx =>
    ⟨pCoreOf_Mc_le_T k.c hx.1, hx.2⟩
  have hPN : pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (YE153 Mc M E : Set G) := hPT.trans (TE153_le_normalizer_YE153 k.c)
  have hN_le : ⁅YE153 Mc M E, pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)⁆ ≤ YE153 Mc M E :=
    commutator_le_of_le_normalizer hPN
  have hN_norm : YE153 Mc M E ≤ Subgroup.normalizer
      ((⁅YE153 Mc M E, pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left _ _
  obtain ⟨y, hyY, hyc⟩ := exists_comm_not_centralizer h113 k.c k.L hτTE hττ hmove
  have hmem : y * τ * y⁻¹ * τ⁻¹ ∈
      ⁅YE153 Mc M E, pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)⁆ :=
    Subgroup.commutator_mem_commutator hyY ⟨hτQ, hτTE.2⟩
  have hnot : ¬ ⁅YE153 Mc M E, pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)⁆ ≤
      pCoreOf 2 (YE153 Mc M E) := by
    intro hle
    rw [pCoreOf_YE k.c k.r66] at hle
    exact hyc (hle hmem).2
  have hX : oTwoUpper (YE153 Mc M E) = YE153 Mc M E :=
    oTwoUpper_oTwoUpper (Y153 Mc M ⊓ Subgroup.normalizer (E : Set G))
  have hidx : (pCoreOf 2 (YE153 Mc M E)).relIndex (YE153 Mc M E) = 3 := by
    obtain ⟨e⟩ := YE_quot h113 k.c k.L k.r66
    rw [C1Pack153.relIndex_pCoreOf_eq_card_quot, Nat.card_congr e.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact (eq_of_not_le_pCore hX hidx hN_le hN_norm hnot).symm

theorem exists_decomp_GE (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    ∃ y ∈ YE153 Mc M E, ∃ u ∈ TE153 T E, ∃ w ∈ Subgroup.centralizer (E : Set G),
      g = y * (u * w) := by
  have hg' : g ∈ (YE153 Mc M E ⊔ TE153 T E) ⊔ Subgroup.centralizer (E : Set G) := r66.GE_eq ▸ hg
  have hYE : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hW : (YE153 Mc M E ⊔ TE153 T E) ≤
      Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) :=
    sup_le (hYE.trans (normalizer_le_normalizer_CE E))
      (inf_le_right.trans (normalizer_le_normalizer_CE E))
  have hmul1 := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hW
  have hmul2 := Subgroup.coe_mul_of_right_le_normalizer_left (YE153 Mc M E) (TE153 T E)
    (TE153_le_normalizer_YE153 c)
  have h1 : g ∈ ((YE153 Mc M E ⊔ TE153 T E : Subgroup G) : Set G) *
      (Subgroup.centralizer (E : Set G) : Set G) := by
    rw [← hmul1]; exact hg'
  obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.mp h1
  have h2 : a ∈ (YE153 Mc M E : Set G) * (TE153 T E : Set G) := by
    rw [← hmul2]; exact ha
  obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp h2
  exact ⟨y, hy, u, hu, w, hw, by group⟩

omit [Finite G] in
theorem le_normalizer_Pc {K : Subgroup G} (hK : K ≤ Mc) (hKE : K ≤ Subgroup.normalizer (E : Set G)) :
    K ≤ Subgroup.normalizer
      ((pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G) := fun _ hx =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pCoreOf 2 Mc (hK hx), Subgroup.le_normalizer (hKE hx)⟩

theorem normalizer_le_normalizer_YE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (YE153 Mc M E : Set G) := by
  obtain ⟨τ, hτQ, hτTE, hττ, hmove⟩ := exists_tau k
  have hcomm := YE_eq_commutator h113 k hτQ hτTE hττ hmove
  have hPT : pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) ≤ TE153 T E := fun x hx =>
    ⟨pCoreOf_Mc_le_T k.c hx.1, hx.2⟩
  have hPY : pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (YE153 Mc M E : Set G) := hPT.trans (TE153_le_normalizer_YE153 k.c)
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)) :=
    (pCoreOf_isPGroup 2 Mc).to_le inf_le_left
  have hTEMc : TE153 T E ≤ Mc := inf_le_left.trans k.c.hyp.qtfe.t_le_mc
  have hCMc : Subgroup.centralizer (E : Set G) ≤ Mc := k.r66.centralizer_le_mc
  have hTEn := le_normalizer_Pc (E := E) hTEMc inf_le_right
  have hCn := le_normalizer_Pc (E := E) hCMc (Subgroup.centralizer_le_normalizer _)
  have hYGE : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  set Pi : Subgroup G := conjClosure (pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G))
    (Subgroup.normalizer (E : Set G)) with hPi
  have hYPi : YE153 Mc M E ≤ Pi := by
    rw [hcomm, Subgroup.commutator_le]
    intro y hy p hp
    have e : ⁅y, p⁆ = (y * p * y⁻¹) * p⁻¹ := rfl
    rw [e]
    exact Pi.mul_mem (mem_conjClosure (hYGE hy) hp)
      (Pi.inv_mem (le_conjClosure _ _ hp))
  have hPile : Pi ≤ YE153 Mc M E ⊔ (pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G)) := by
    refine conjClosure_le fun g hg p hp => ?_
    obtain ⟨y, hy, u, hu, w, hw, rfl⟩ := exists_decomp_GE k.c k.r66 hg
    have hmem : u * w ∈ Subgroup.normalizer
        ((pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).mul_mem (hTEn hu) (hCn hw)
    have hp₂ : (u * w) * p * (u * w)⁻¹ ∈ pCoreOf 2 Mc ⊓ Subgroup.normalizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hmem p).mp hp
    set p₂ := (u * w) * p * (u * w)⁻¹ with hp₂def
    have e : y * (u * w) * p * (y * (u * w))⁻¹ = (y * (p₂ * y⁻¹ * p₂⁻¹)) * p₂ := by
      simp only [hp₂def]; group
    rw [e]
    have h3 : p₂ * y⁻¹ * p₂⁻¹ ∈ YE153 Mc M E :=
      (Subgroup.mem_normalizer_iff.mp (hPY hp₂) y⁻¹).mp ((YE153 Mc M E).inv_mem hy)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((YE153 Mc M E).mul_mem hy h3))
      (Subgroup.mem_sup_right hp₂)
  have hO : oTwoUpper Pi = YE153 Mc M E := by
    apply le_antisymm
    · exact (oTwoUpper_mono hPile).trans (oTwoUpper_sup_le hPY hP2)
    · calc YE153 Mc M E = oTwoUpper (YE153 Mc M E) :=
            (oTwoUpper_oTwoUpper (Y153 Mc M ⊓ Subgroup.normalizer (E : Set G))).symm
        _ ≤ oTwoUpper Pi := oTwoUpper_mono hYPi
  intro g hg
  have h1 : g ∈ Subgroup.normalizer (Pi : Set G) := le_normalizer_conjClosure _ _ hg
  have h2 := normalizer_le_normalizer_oTwoUpper Pi h1
  rwa [hO] at h2

end Main

end S1567

theorem step67Normal (h113 : StageLemma14113) : Step67Normal := by
  intro G _ _ T Mc M V₁ V₂ E t k
  exact S1567.normalizer_le_normalizer_YE h113 k

end CFSG.Quasithin
