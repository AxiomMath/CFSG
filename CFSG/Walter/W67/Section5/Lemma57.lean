module

public import CFSG.Walter.ReeOrder.WardLocal.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Walter.W67.Section5.Lemma53
public import CFSG.Walter.W67.Section5.Sylow52

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec57

theorem not_isSolvable_psl2 {F : Type} [Field F] [Finite F] (h : 3 < Nat.card F) :
    ¬ Group.IsSolvable PSL(2, F) := by
  have := psl2_isPerfect_of_card_gt_three F h
  have : Nontrivial PSL(2, F) := ⟨⟨Borel5.weyl F, 1, Borel5.weyl_ne_one⟩⟩
  exact Group.IsPerfect.not_isSolvable _

theorem sylow_eq_of_TI {L : Type} [Group L] [Finite L]
    (hTI : ∀ (P : Sylow 3 L) (g : L), (P : Subgroup L) ⊓ (MulAut.conj g • (P : Subgroup L)) = ⊥ ∨
      (P : Subgroup L) ⊓ (MulAut.conj g • (P : Subgroup L)) = P)
    {Q : Subgroup L} (hQ1 : Q ≠ ⊥) {P P' : Sylow 3 L} (hQP : Q ≤ P) (hQP' : Q ≤ P') :
    P = P' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P P'
  have hP' : (P' : Subgroup L) = MulAut.conj g • (P : Subgroup L) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  rcases hTI P g with h | h
  · exfalso
    apply hQ1
    rw [eq_bot_iff, ← h]
    exact le_inf hQP (hP' ▸ hQP')
  · have hle : (P : Subgroup L) ≤ P' := by
      have h1 := inf_le_right (a := (P : Subgroup L)) (b := MulAut.conj g • (P : Subgroup L))
      rw [h] at h1
      rw [hP']
      exact h1
    exact Sylow.ext (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]))

theorem conj_mem_of_TI {L : Subgroup G}
    (hTI : ∀ (P : Sylow 3 L) (g : L), (P : Subgroup L) ⊓ (MulAut.conj g • (P : Subgroup L)) = ⊥ ∨
      (P : Subgroup L) ⊓ (MulAut.conj g • (P : Subgroup L)) = P)
    {Q S : Subgroup G} (hQ1 : Q ≠ ⊥) (hQS : Q ≤ S) (hSL : S ≤ L)
    (hS : Nat.card S = 3 ^ (Nat.card L).factorization 3) {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) :
    ∀ x ∈ S, a * x * a⁻¹ ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S' := S.map (MulAut.conj a).toMonoidHom with hS'def
  have hS'L : S' ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp haL x).mp (hSL hx)
  have hS'card : Nat.card S' = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hQeq : Q.map (MulAut.conj a).toMonoidHom = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact haQ x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  have hQS' : Q ≤ S' := by
    rw [← hQeq]
    exact Subgroup.map_mono hQS
  have hcardS : Nat.card (S.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hS]
  have hcardS' : Nat.card (S'.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'L).toEquiv, hS'card, hS]
  let P : Sylow 3 L := Sylow.ofCard (S.subgroupOf L) hcardS
  let P' : Sylow 3 L := Sylow.ofCard (S'.subgroupOf L) hcardS'
  have hQ1' : Q.subgroupOf L ≠ ⊥ := by
    intro h
    apply hQ1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hSL (hQS hx)⟩ : L) ∈ Q.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hPP' := sylow_eq_of_TI hTI hQ1' (P := P) (P' := P')
    (Subgroup.subgroupOf_mono L hQS) (Subgroup.subgroupOf_mono L hQS')
  have hSS' : S = S' := by
    have h1 : S.subgroupOf L = S'.subgroupOf L :=
      congrArg (fun P : Sylow 3 L => (P : Subgroup L)) hPP'
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hSL, inf_eq_left.mpr hS'L] at h2
  intro x hx
  rw [hSS']
  exact ⟨x, hx, rfl⟩

end Sec57

open Sec52 Sec57 in
theorem lemma_5_7_of
    (h26i : S_lemma_2_6_i) (hJR : S_IsJRSubgroup_nonempty_jrGroup)
    (h56 : S_prop_5_6) : S_lemma_5_7 := by
  intro G _ _ s hR X hXE hX1 hsol
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heX : ∀ Y : Subgroup G, s.eX Y = Nat.card Y := fun Y => by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr hXE hX1
  obtain ⟨K', hK'jr, -⟩ := (s.L_spec X hXE hX1).jr
  have hXpos : 0 < s.eX X := by rw [heX]; exact Nat.card_pos
  have hepos : 0 < s.f / s.eX X := Nat.div_pos (Nat.le_of_dvd s.f_pos hediv) hXpos
  obtain ⟨eK'⟩ := hK'jr.iso
  have hK'sol : Group.IsSolvable K' := by
    have hle : K' ≤ s.L X := hK'jr.K_le.trans inf_le_left
    have : Group.IsSolvable (s.L X) := hsol
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hpsl : Group.IsSolvable PSL(2, GaloisField s.p (s.f / s.eX X)) :=
    Group.isSolvable_of_surjective (f := eK'.toMonoidHom) eK'.surjective
  have hFcard : Nat.card (GaloisField s.p (s.f / s.eX X)) = s.p ^ (s.f / s.eX X) :=
    GaloisField.card _ _ hepos.ne'
  have hq3 : s.p ^ (s.f / s.eX X) ≤ 3 := by
    by_contra h
    exact not_isSolvable_psl2 (hFcard ▸ (not_le.mp h)) hpsl
  have hp2 : 2 ≤ s.p := (Fact.out : s.p.Prime).two_le
  have hp3 : s.p = 3 := by
    have h1 : s.p ≤ s.p ^ (s.f / s.eX X) := Nat.le_self_pow hepos.ne' _
    have h2 : s.p ≠ 2 := s.p_ne_two
    omega
  have hfe : s.f / s.eX X = 1 := by
    rw [hp3] at hq3
    by_contra hne
    have h2 : 2 ≤ s.f / s.eX X := by omega
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) h2
    omega
  have hXf : Nat.card X = s.f := by
    rw [← heX]
    obtain ⟨c, hc⟩ := hediv
    rw [hc, Nat.mul_div_cancel_left _ hXpos] at hfe
    rw [hc, hfe, mul_one]
  obtain ⟨hEdiv, ⟨eKE⟩, -⟩ := h26i G s.toHyp s.fr le_rfl s.E_ne_bot
  have hEdiv' := hEdiv
  rw [heX] at hEdiv'
  have hEf : Nat.card s.fr.E = s.f :=
    le_antisymm (Nat.le_of_dvd s.f_pos hEdiv') (hXf ▸ Subgroup.card_le_of_le hXE)
  have hXE' : X = s.fr.E := Subgroup.eq_of_le_of_card_ge hXE (by rw [hEf, hXf])
  refine ⟨hXE', ?_⟩
  rw [hXE'] at hsol
  by_contra hnp
  have h3E : ¬ 3 ∣ Nat.card s.fr.E := h56 G s hp3 hR
  obtain ⟨g, hgE, hgen⟩ := s.fr.exists_generator_E
  rw [s.F_eq_bot, sup_bot_eq] at hgen
  have hog : orderOf g = s.f := by rw [← Nat.card_zpowers, hgen, hEf]
  have hn2 : 2 ≤ s.f := by
    have h1 := s.three_lt_q
    rw [Hyp.q, hp3] at h1
    by_contra h
    have h2 : s.f = 1 := by have := s.f_pos; omega
    rw [h2] at h1
    norm_num at h1
  set n := s.f with hn
  set r := n.minFac with hrdef
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hrlt : r < n := (Nat.not_prime_iff_minFac_lt hn2).mp (hEf ▸ hnp)
  have hnodd : Odd n := hEf ▸ s.fr.odd_card_E
  have hr2 : r ≠ 2 := by
    rintro h
    rw [h] at hrn
    exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr hrn)
  have hr3 : r ≠ 3 := fun h => h3E (hEf ▸ h ▸ hrn)
  have hr5 : 5 ≤ r := by
    have h1 := hrp.two_le
    rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with h | h | h | h
    · exact absurd h hr2
    · exact absurd h hr3
    · exact absurd (h ▸ hrp) (by norm_num)
    · exact h
  set Y := Subgroup.zpowers (g ^ r) with hYdef
  have hYcard : Nat.card Y = n / r := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hrp.ne_zero (hog ▸ hrn), hog]
  have hYE : Y ≤ s.fr.E := by
    rw [← hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) r)
  have hnr : 1 < n / r := by
    obtain ⟨c, hc⟩ := hrn
    rw [hc, Nat.mul_div_cancel_left _ hrp.pos]
    by_contra h
    have : c ≤ 1 := by omega
    have : r * c ≤ r := by nlinarith
    omega
  have hY1 : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    omega
  set v := n.factorization r with hvdef
  set m := n / r ^ v with hmdef
  have hmdvd : m ∣ n := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n r)
  set A := Subgroup.zpowers (g ^ m) with hAdef
  have hAcard : Nat.card A = r ^ v := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (Nat.pos_of_dvd_of_pos hmdvd (by omega)).ne'
      (hog ▸ hmdvd), hog, hmdef, Nat.div_div_self (Nat.ordProj_dvd n r) (by omega)]
  have hAr : IsPGroup r A := IsPGroup.of_card hAcard
  have hAE : A ≤ s.fr.E := by
    rw [← hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) m)
  have hEAY : s.fr.E ≤ A ⊔ Y := by
    have hcop : Nat.Coprime m r := (Nat.coprime_ordCompl hrp (by omega)).symm
    obtain ⟨u, w, huw⟩ : IsCoprime (m : ℤ) (r : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcop
    rw [← hgen, Subgroup.zpowers_le]
    have hg : g = (g ^ m) ^ u * (g ^ r) ^ w := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (m : ℤ),
        mul_comm (r : ℤ), huw, zpow_one]
    rw [hg]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _))
  have hEcomm : ∀ x ∈ s.fr.E, ∀ y ∈ s.fr.E, x * y = y * x := by
    intro x hx y hy
    rw [← hgen] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self g i j).eq
  have hLY := s.L_spec Y hYE hY1
  have hEN : ∀ e ∈ s.fr.E, e ∈ Subgroup.normalizer ((s.L Y : Subgroup G) : Set G) := by
    intro e he
    have heY : e ∈ Subgroup.normalizer (Y : Set G) := by
      apply Sec53.mem_normalizer_of_conj_le
      intro y hy
      rw [hEcomm e he y (hYE hy), mul_inv_cancel_right]
      exact hy
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    exact Subgroup.mem_subgroupOf.mp (hLY.normal.2.conj_mem ⟨y, hLY.normal.1 hy⟩
      (Subgroup.mem_subgroupOf.mpr hy) ⟨e, heY⟩)
  obtain ⟨K'', hK''jr, hK''eq⟩ := hLY.jr
  have hfY : s.f / s.eX Y = r := by
    rw [heX, hYcard]
    exact Nat.div_div_self hrn (by omega)
  have hq3r : 3 < 3 ^ r := by
    calc 3 = 3 ^ 1 := by norm_num
      _ < 3 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hK''K : K'' = s.KX Y := hK''eq (by rw [hfY, hp3]; exact hq3r)
  obtain ⟨hL', hL'p, hL'f, -, -⟩ := hJR G s.p_ne_two (by rw [hfY]; omega) hK''jr
  have hq' : hL'.q = 3 ^ r := by rw [JRGroup.q, hL'p, hL'f, hfY, hp3]
  have hq'5 : 5 < hL'.q := by
    rw [hq']
    calc 5 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨-, -, hR3, -⟩ := hR _ hL' (by omega)
  have hW : Ward.ReeTypeHyp (s.L Y) := Classical.choice
    ((hL'.toJTHyp hq'5).nonempty_reeTypeHyp_of_three (by
      change hL'.p = 3
      rw [hL'p, hp3]))
  have hTI : ∀ (P : Sylow 3 (s.L Y)) (g : s.L Y),
      (P : Subgroup (s.L Y)) ⊓ (MulAut.conj g • (P : Subgroup (s.L Y))) = ⊥ ∨
        (P : Subgroup (s.L Y)) ⊓ (MulAut.conj g • (P : Subgroup (s.L Y))) = P :=
    fun P g => (WardLocal.ward_two_three hW P).2.1 g
  have hfE : s.f / s.eX s.fr.E = 1 := by
    rw [heX, hEf]
    exact Nat.div_self (by omega)
  have hKEcard : Nat.card (s.KX s.fr.E) = 12 := by
    have hFcard : Nat.card (GaloisField s.p (s.f / s.eX s.fr.E)) = s.p ^ (s.f / s.eX s.fr.E) :=
      GaloisField.card _ _ (by rw [hfE]; norm_num)
    rw [Nat.card_congr eKE.toEquiv, psl2_card_formula _ ⟨s.p, s.f / s.eX s.fr.E, Fact.out,
      s.odd_p, by omega, hFcard⟩, hFcard, hfE, hp3]
    norm_num
  obtain ⟨⟨x₀, hx₀⟩, hox₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := s.KX s.fr.E) 3 (by rw [hKEcard]; norm_num)
  rw [Subgroup.orderOf_mk] at hox₀
  set Q₀ := Subgroup.zpowers x₀ with hQ₀def
  have hx₀L : x₀ ∈ s.L Y := by
    have hx₀KY : x₀ ∈ s.KX Y := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx₀).1,
      Subgroup.centralizer_le hYE (Subgroup.mem_inf.mp hx₀).2⟩
    rw [← hK''K] at hx₀KY
    exact (hK''jr.K_le hx₀KY).1
  have hQ₀L : Q₀ ≤ s.L Y := Subgroup.zpowers_le.mpr hx₀L
  have hQ₀3 : IsPGroup 3 Q₀ := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox₀, pow_one])
  have hQ₀1 : Q₀ ≠ ⊥ := by
    intro h
    have : Nat.card Q₀ = 3 := by rw [Nat.card_zpowers, hox₀]
    rw [h, Subgroup.card_bot] at this
    omega
  have hQ₀E : ∀ e ∈ s.fr.E, ∀ x ∈ Q₀, e * x * e⁻¹ ∈ Q₀ := by
    intro e he x hx
    have hxC : x ∈ Subgroup.centralizer (s.fr.E : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hx₀).2 hx
    rw [show e * x * e⁻¹ = x by rw [Subgroup.mem_centralizer_iff.mp hxC e he,
      mul_inv_cancel_right]]
    exact hx
  obtain ⟨P, hP⟩ := (hQ₀3.comap_subtype (K := s.L Y)).exists_le_sylow
  set S := (P : Subgroup (s.L Y)).map (s.L Y).subtype with hSdef
  have hSL : S ≤ s.L Y := Subgroup.map_subtype_le _
  have hS : Nat.card S = 3 ^ (Nat.card (s.L Y)).factorization 3 := by
    rw [hSdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity]
  have hQ₀S : Q₀ ≤ S := fun x hx => ⟨⟨x, hQ₀L hx⟩, hP (show (⟨x, hQ₀L hx⟩ : s.L Y) ∈
    Q₀.comap (s.L Y).subtype from hx), rfl⟩
  have hES : ∀ e ∈ s.fr.E, ∀ x ∈ S, e * x * e⁻¹ ∈ S := fun e he =>
    conj_mem_of_TI hTI hQ₀1 hQ₀S hSL hS (hEN e he) (hQ₀E e he)
  set W := Subgroup.closure {y : G | y ∈ S ∧ y ^ 3 = 1} with hWdef
  have hWmap : W = (Subgroup.closure {x : s.L Y | x ∈ (P : Subgroup (s.L Y)) ∧ x ^ 3 = 1}).map
      (s.L Y).subtype := by
    rw [MonoidHom.map_closure, hWdef]
    apply congrArg Subgroup.closure
    ext y
    constructor
    · rintro ⟨⟨x, hxP, rfl⟩, hy3⟩
      exact ⟨x, ⟨hxP, Subtype.ext (by simpa using hy3)⟩, rfl⟩
    · rintro ⟨x, ⟨hxP, hx3⟩, rfl⟩
      exact ⟨⟨x, hxP, rfl⟩, by simpa using congrArg Subtype.val hx3⟩
  have hWcard : Nat.card W = 3 ^ (2 * r) := by
    obtain ⟨-, -, -, -, -, hcl, -, hZ₂card, -⟩ := hR3 (by omega) P
    rw [hWmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hcl, hZ₂card, hq',
      ← pow_mul, mul_comm]
  have hWS : W ≤ S := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hEW : s.fr.E ≤ Subgroup.normalizer (W : Set G) := by
    intro e he
    apply Sec53.mem_normalizer_of_conj_le
    have hle : W.map (MulAut.conj e).toMonoidHom ≤ W := by
      rw [hWdef, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨hyS, hy3⟩, rfl⟩
      refine ⟨hES e he y hyS, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hy3]
      group
    exact fun y hy => hle ⟨y, hy, rfl⟩
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := hAE.trans hEW
  let := JT.conjAct A W hAW
  have : Fact r.Prime := ⟨hrp⟩
  have hcong := hAr.card_modEq_card_fixedPoints (α := W)
  set C := W ⊓ Subgroup.centralizer (A : Set G) with hCdef
  have hfixC : Nat.card (MulAction.fixedPoints A W) = Nat.card C := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1, Subgroup.mem_inf.mpr ⟨w.1.2, Subgroup.mem_centralizer_iff.mpr
          fun a ha => ?_⟩⟩
        invFun := fun c => ⟨⟨c, (Subgroup.mem_inf.mp c.2).1⟩, fun a => ?_⟩
        left_inv := fun w => rfl
        right_inv := fun c => rfl }
    · have h' : a * (w.1 : G) * a⁻¹ = w.1 := congrArg Subtype.val (w.2 ⟨a, ha⟩)
      calc a * (w.1 : G) = a * w.1 * a⁻¹ * a := by group
        _ = w.1 * a := by rw [h']
    · apply Subtype.ext
      change (a : G) * c * (a : G)⁻¹ = c
      rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 a a.2,
        mul_inv_cancel_right]
  rw [hWcard, hfixC] at hcong
  have hC3 : IsPGroup 3 C := by
    have hS3 : IsPGroup 3 S := IsPGroup.of_card hS
    exact hS3.to_le (inf_le_left.trans hWS)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hC3
  have hferm : 3 ^ r ≡ 3 [MOD r] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact ZMod.pow_card 3
  have h9 : 3 ^ j ≡ 9 [MOD r] := by
    rw [← hj]
    refine hcong.symm.trans ?_
    rw [mul_comm 2 r, pow_mul]
    exact (hferm.pow 2).trans (by norm_num [Nat.ModEq])
  have hj2 : 2 ≤ j := by
    by_contra hj2
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have h8 : r ∣ 8 := (Nat.modEq_iff_dvd' (by norm_num)).mp h9
      have : r ∣ 2 := hrp.dvd_of_dvd_pow (show r ∣ 2 ^ 3 by simpa using h8)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have h6 : r ∣ 6 := (Nat.modEq_iff_dvd' (by norm_num)).mp h9
      rcases (Nat.Prime.dvd_mul hrp).mp (show r ∣ 2 * 3 by simpa using h6) with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  have h9C : 9 ∣ Nat.card C := by
    rw [hj, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 3 hj2
  have hCE : C ≤ Subgroup.centralizer (s.fr.E : Set G) := by
    intro c hc
    obtain ⟨hcW, hcA⟩ := Subgroup.mem_inf.mp hc
    have hcY : c ∈ Subgroup.centralizer (Y : Set G) := hLY.le_centralizer (hSL (hWS hcW))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : A ⊔ Y ≤ Subgroup.centralizer ({c} : Set G) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hcA a ha
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hcY y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hEAY he))
  have h9CE : 9 ∣ Nat.card (Subgroup.centralizer (s.fr.E : Set G)) :=
    h9C.trans (Subgroup.card_dvd_of_le hCE)
  have hLE := s.L_spec s.fr.E le_rfl s.E_ne_bot
  obtain ⟨K₃, hK₃jr, -⟩ := hLE.jr
  obtain ⟨hL₃, hL₃p, hL₃f, -, -⟩ := hJR G s.p_ne_two (by omega) hK₃jr
  have hq₃ : hL₃.q = 3 := by rw [JRGroup.q, hL₃p, hL₃f, hfE, hp3, pow_one]
  obtain ⟨⟨-, -, -, hsolv168⟩, -⟩ := hR _ hL₃ (by omega)
  have hL168 : Nat.card (s.L s.fr.E) = 168 := (hsolv168 hsol).2.1
  have hCEeq := hLE.centralizer_eq (by rw [s.F_eq_bot]; exact bot_le)
  have hDN : Subgroup.centralizer (s.fr.E : Set G) ⊓ s.fr.E ≤
      Subgroup.normalizer ((s.L s.fr.E : Subgroup G) : Set G) := by
    intro d hd
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    have hdN : d ∈ Subgroup.normalizer (s.fr.E : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hd).1
    exact Subgroup.mem_subgroupOf.mp (hLE.normal.2.conj_mem ⟨y, hLE.normal.1 hy⟩
      (Subgroup.mem_subgroupOf.mpr hy) ⟨d, hdN⟩)
  have h1 := card_sup_mul_card_inf hDN
  rw [sup_comm, ← hCEeq, hL168] at h1
  have hdvd : Nat.card (Subgroup.centralizer (s.fr.E : Set G)) ∣
      168 * Nat.card (Subgroup.centralizer (s.fr.E : Set G) ⊓ s.fr.E : Subgroup G) :=
    Dvd.intro _ h1
  have hDE : Nat.card (Subgroup.centralizer (s.fr.E : Set G) ⊓ s.fr.E : Subgroup G) ∣
      Nat.card s.fr.E := Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime 9 (Nat.card (Subgroup.centralizer (s.fr.E : Set G) ⊓ s.fr.E :
      Subgroup G)) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun h => h3E (h.trans hDE)
  have := hcop.dvd_of_dvd_mul_right (h9CE.trans hdvd)
  norm_num at this

end CFSG.Walter.W67
