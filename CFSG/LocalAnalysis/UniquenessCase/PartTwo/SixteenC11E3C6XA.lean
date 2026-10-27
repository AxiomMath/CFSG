module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C6Prod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3ParaZ
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_c6_centSub_map_conj {W : Type} [CommGroup W]
    (g : MulAut W) (U : Subgroup W) :
    centSub (U.map g.toMonoidHom) = (centSub U).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine mem_centSub.mpr fun u hu => ?_
      have h1 : x (g u) = g u :=
        mem_centSub.mp hx (g u) (Subgroup.mem_map_of_mem g.toMonoidHom hu)
      show (g⁻¹ * x * g) u = u
      rw [MulAut.mul_apply, MulAut.mul_apply, h1]
      simp
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    refine mem_centSub.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    show (g * y * g⁻¹) (g u) = g u
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, mem_centSub.mp hy u hu]

private theorem s1611e3_c6_eq_of_mul_eq_mul_of_inf_bot {W : Type} [CommGroup W]
    {A B : Subgroup W} (h : A ⊓ B = ⊥) {u u' v v' : W} (hu : u ∈ A) (hu' : u' ∈ B)
    (hv : v ∈ A) (hv' : v' ∈ B) (hmul : u * u' = v * v') : u = v ∧ u' = v' := by
  have h1 : v⁻¹ * u = v' * u'⁻¹ := by
    calc v⁻¹ * u = v⁻¹ * (u * u') * u'⁻¹ := by group
      _ = v⁻¹ * (v * v') * u'⁻¹ := by rw [hmul]
      _ = v' * u'⁻¹ := by group
  have hmem : v⁻¹ * u ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem hv) hu, by rw [h1]; exact B.mul_mem hv' (B.inv_mem hu')⟩
  rw [h, Subgroup.mem_bot] at hmem
  have huv : u = v := (inv_mul_eq_one.mp hmem).symm
  subst huv
  exact ⟨rfl, mul_left_cancel hmul⟩

private theorem s1611e3_c6_exists_mul_of_mem_sup_of_commute {X : Type} [Group X]
    {A B : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x :=
  CFSG.mem_sup_of_commute (fun a ha b hb => hcomm a ha b hb) |>.mp hx

private theorem s1611e3_c6_fixV_ne_bot_of_isPGroup_two {W : Type} [CommGroup W] [Finite W]
    [Nontrivial W] (hsq : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    (hP : IsPGroup 2 P) : fixV P ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints ↥P W) = Nat.card ↥(fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hW2 : IsPGroup 2 W := fun v => ⟨1, by rw [pow_one]; exact hsq v⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card W % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

private theorem s1611e3_c6_pow_three_eq_one_of_card_24 {X : Type} [Group X] [Finite X]
    (h24 : Nat.card X = 24) {x : X} (hx : ∃ n : ℕ, x ^ 3 ^ n = 1) : x ^ 3 = 1 := by
  obtain ⟨n, hn⟩ := hx
  have hdvd24 : orderOf x ∣ 24 := by rw [← h24]; exact orderOf_dvd_natCard x
  have hdvd3 : orderOf x ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h2k : 2 ≤ k := by omega
    have h9dvd : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 h2k
    have h24' : 3 ^ k ∣ 24 := hk ▸ hdvd24
    have h9 : 9 ∣ 24 := by
      have h := h9dvd.trans h24'
      simpa using h
    norm_num at h9
  have hfin : orderOf x = 1 ∨ orderOf x = 3 := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left; simpa using hk
    · right; simpa using hk
  rcases hfin with h | h
  · exact orderOf_dvd_iff_pow_eq_one.mp (by simpa [h] using one_dvd (3 : ℕ))
  · exact orderOf_dvd_iff_pow_eq_one.mp (by simpa [h] using dvd_refl (3 : ℕ))

private theorem s1611e3_c6_map_conj_conj_inv {W : Type} [Group W] (t : MulAut W)
    (A : Subgroup (MulAut W)) :
    (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext y
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

private theorem s1611e3_c6_conj_mul_comp {W : Type} [Group W] (x t : MulAut W) :
    (MulAut.conj t).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj (x⁻¹ * t * x)).toMonoidHom := by
  have h1 : (MulAut.conj t).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj t * MulAut.conj x).toMonoidHom := by ext y; rfl
  have h2 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj (x⁻¹ * t * x)).toMonoidHom =
      (MulAut.conj x * MulAut.conj (x⁻¹ * t * x)).toMonoidHom := by ext y; rfl
  rw [h1, h2,
    show MulAut.conj t * MulAut.conj x = MulAut.conj (t * x) from (map_mul _ _ _).symm,
    show MulAut.conj x * MulAut.conj (x⁻¹ * t * x) = MulAut.conj (x * (x⁻¹ * t * x)) from
      (map_mul _ _ _).symm,
    show t * x = x * (x⁻¹ * t * x) by group]

private theorem s1611e3_c6_conj_inv_comp {W : Type} [Group W] (x t : MulAut W) :
    (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (x⁻¹ * t)).toMonoidHom := by
  have h1 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj x⁻¹ * MulAut.conj t).toMonoidHom := by ext y; rfl
  rw [h1, show MulAut.conj x⁻¹ * MulAut.conj t = MulAut.conj (x⁻¹ * t) from
    (map_mul _ _ _).symm]

private theorem s1611e3_c6_map_conj_mul {W : Type} [Group W] (x u : MulAut W)
    (A : Subgroup (MulAut W)) :
    A.map (MulAut.conj (x * u)).toMonoidHom =
      (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s1611e3_c6_sandwich {W : Type} [Group W] (x t : MulAut W)
    (A : Subgroup (MulAut W)) :
    ((A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom =
      A.map (MulAut.conj (x⁻¹ * t * x)).toMonoidHom := by
  rw [← s1611e3_c6_map_conj_mul, ← s1611e3_c6_map_conj_mul]

private theorem s1611e3_c6_two_parabolics {W : Type} [Group W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsL3 ↥L 1) {T1 : Subgroup (MulAut W)}
    (hT1L : T1 ≤ L) (hT1card : Nat.card ↥T1 = 8) {P : Subgroup (MulAut W)}
    (hPL : P ≤ L) (hPcard : Nat.card ↥P = 24) (hT1P : T1 ≤ P) :
    ∃ Pstar : Subgroup (MulAut W), Pstar ≤ L ∧ T1 ≤ Pstar ∧ Nat.card ↥Pstar = 24 ∧
      Pstar ≠ P ∧ P ⊓ Pstar = T1 ∧
      ∀ Q : Subgroup (MulAut W), Q ≤ L → T1 ≤ Q → Nat.card ↥Q = 24 → Q = P ∨ Q = Pstar := by
  classical
  have hT1scard : Nat.card ↥(T1.subgroupOf L) = 8 := by
    rw [← hT1card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT1L).toEquiv
  obtain ⟨P1, P2, hT1P1, hT1P2, hP1card, hP2card, hP1neP2, hP1infP2, huniq⟩ :=
    s1611e3_l3_two_parabolics (L := ↥L) hL (T₁ := T1.subgroupOf L) hT1scard
  let Q : Subgroup ↥L := P.subgroupOf L
  have hQmap : Q.map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hQcard : Nat.card ↥Q = 24 := by
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hT1Q : T1.subgroupOf L ≤ Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hT1P hx
  have hQ : Q = P1 ∨ Q = P2 := huniq Q hT1Q hQcard
  have hex : ∃ Ps : Subgroup ↥L, (Ps = P1 ∨ Ps = P2) ∧ Ps ≠ Q ∧
      T1.subgroupOf L ≤ Ps ∧ Nat.card ↥Ps = 24 ∧ Q ⊓ Ps = T1.subgroupOf L := by
    rcases hQ with hq | hq
    · refine ⟨P2, Or.inr rfl, ?_, hT1P2, hP2card, ?_⟩
      · rw [hq]; exact fun h => hP1neP2 h.symm
      · rw [hq]; exact hP1infP2
    · refine ⟨P1, Or.inl rfl, ?_, hT1P1, hP1card, ?_⟩
      · rw [hq]; exact hP1neP2
      · rw [hq, inf_comm]; exact hP1infP2
  obtain ⟨Ps, hPs, hPsne, hPsT1, hPscard, hPsinf⟩ := hex
  refine ⟨Ps.map L.subtype, Subgroup.map_subtype_le Ps, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨⟨y, hT1L hy⟩, hPsT1 (by
      change (⟨y, hT1L hy⟩ : ↥L) ∈ T1.subgroupOf L
      exact hy), rfl⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hPscard]
  · intro heq
    apply hPsne
    have h1 : (Ps.map L.subtype).comap L.subtype = (Q.map L.subtype).comap L.subtype := by
      rw [heq, hQmap]
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h1
  · have h1 : P ⊓ Ps.map L.subtype = (Q ⊓ Ps).map L.subtype := by
      rw [← hQmap, Subgroup.map_inf _ _ _ L.subtype_injective]
    rw [h1, hPsinf, Subgroup.map_subgroupOf_eq_of_le hT1L]
  · intro X hXL hT1X hXcard
    let Xs : Subgroup ↥L := X.subgroupOf L
    have hXmap : Xs.map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
    have hXscard : Nat.card ↥Xs = 24 := by
      rw [← hXcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv
    have hT1Xs : T1.subgroupOf L ≤ Xs := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hT1X hx
    have hXs : Xs = P1 ∨ Xs = P2 := huniq Xs hT1Xs hXscard
    rcases hQ with hq | hq
    · rcases hXs with hx | hx
      · left
        rw [← hXmap, hx, ← hq]
        exact hQmap
      · right
        have hPs' : Ps = P2 := by
          rcases hPs with h | h
          · exact absurd (h.trans hq.symm) hPsne
          · exact h
        rw [← hXmap, hx, hPs']
    · rcases hXs with hx | hx
      · right
        have hPs' : Ps = P1 := by
          rcases hPs with h | h
          · exact h
          · exact absurd (h.trans hq.symm) hPsne
        rw [← hXmap, hx, hPs']
      · left
        rw [← hXmap, hx, ← hq]
        exact hQmap

theorem s1611e3_case6_l3_routeF_data {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1) : S1611e3RouteF D V₀ V hV 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, Z, hxT, hcomm, hinfA, hEeq, hfixBW, hfixAW, hinfW, hsupW, hT1syl, hZcard,
    hZM, hZnorm, hZL, hZJ, hZf, hFsup, hZinf, hZLp, hZJp, hZfp, hswap, -⟩ :=
    s1611e3_case6_prod h hc h6
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMb
  set Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hTb
  set Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hLb
  set Lp : Subgroup (MulAut (Vtil V₀ V hV)) := Lb.map (MulAut.conj x).toMonoidHom with hLp
  set Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWt
  set Wp : Subgroup (Vtil V₀ V hV) := Wt.map x.toMonoidHom with hWp
  set T1 : Subgroup (MulAut (Vtil V₀ V hV)) := Tb ⊓ Lb with hT1
  set T0 : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Tb ⊓ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) with hT0
  have hLbcard : Nat.card ↥Lb = 168 := card_eq_of_isL3 hL3
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
      hc.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTsyl : IsSylowIn 2 Tb Mb :=
    s1611e3_barSub_sylow hMstab (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)
  have hTbMb : Tb ≤ Mb := hTsyl.le
  have hTb2 : IsPGroup 2 Tb := hTsyl.isPGroup
  have hxMb : x ∈ Mb := hTbMb hxT
  have hT1L : T1 ≤ Lb := inf_le_right
  have hT1card : Nat.card ↥T1 = 8 := by
    have hc' := IsSylowIn.card_eq hT1syl
    rw [hLbcard] at hc'
    have hf : (168).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two,
        show (168 : ℕ) = 2 ^ 3 * 21 by norm_num,
        padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21), add_zero]
    rw [hf] at hc'
    norm_num at hc'
    exact hc'
  have hT1p : IsPGroup 2 T1 := hT1syl.isPGroup
  haveI : Nontrivial (Vtil V₀ V hV) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI : Subsingleton (MulAut (Vtil V₀ V hV)) :=
      ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim (a v) (b v)⟩
    apply hc.ne_bot
    change Lb = ⊥
    rw [Subgroup.eq_bot_iff_forall]
    intro y _
    exact Subsingleton.elim y 1
  have hfixV : fixV Tb ≠ ⊥ :=
    s1611e3_c6_fixV_ne_bot_of_isPGroup_two (s15_Infra_vtil_sq_eq_one V₀ V hV) hTb2
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixV
  have hvT : (v : Vtil V₀ V hV) ∈ fixV Tb := v.2
  have hvne : (v : Vtil V₀ V hV) ≠ 1 := fun hh => hv1 (Subtype.ext hh)
  obtain ⟨w, hwWt, w', hwWp, hwv⟩ :=
    Subgroup.mem_sup.1 (by rw [hsupW]; exact Subgroup.mem_top (v : Vtil V₀ V hV))
  have hxLb_ne : Lb.map (MulAut.conj x).toMonoidHom ≠ Lb := by
    intro heq
    have hLbBot : Lb = ⊥ := by
      have hh := hinfA
      rw [hLp, heq, inf_idem] at hh
      exact hh
    rw [hLbBot, Subgroup.card_bot] at hLbcard
    omega
  have hx2N : Lb.map (MulAut.conj (x ^ 2)).toMonoidHom = Lb := by
    rcases hswap x hxMb with h' | h'
    · exact absurd h'.1 hxLb_ne
    · have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          (MulAut.conj (x ^ 2)).toMonoidHom := by
        have h1 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
            (MulAut.conj x * MulAut.conj x).toMonoidHom := by ext y; rfl
        rw [h1, map_pow (MulAut.conj) x 2, pow_two]
      calc Lb.map (MulAut.conj (x ^ 2)).toMonoidHom
          = Lb.map ((MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom) := by
              rw [← hcomp]
        _ = (Lb.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
              rw [Subgroup.map_map]
        _ = Lp.map (MulAut.conj x).toMonoidHom := by rw [hLp]
        _ = Lb := h'.2.1
  have hWtx2 : Wt.map (x ^ 2).toMonoidHom = Wt := by
    have h1 : commSub (⊤ : Subgroup (Vtil V₀ V hV))
        (Lb.map (MulAut.conj (x ^ 2)).toMonoidHom) =
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb).map (x ^ 2).toMonoidHom :=
      s16c167_commSub_top_conj (x ^ 2) Lb
    rw [hx2N] at h1
    have h2 : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb = Wt := by
      rw [hLb, hWt]; rfl
    rw [h2] at h1
    exact h1.symm
  have hWpx : Wp.map x.toMonoidHom = Wt := by
    have hcomp : x.toMonoidHom.comp x.toMonoidHom = (x ^ 2).toMonoidHom := by ext y; rfl
    calc Wp.map x.toMonoidHom = (Wt.map x.toMonoidHom).map x.toMonoidHom := by rw [hWp]
      _ = Wt.map (x.toMonoidHom.comp x.toMonoidHom) := by rw [Subgroup.map_map]
      _ = Wt.map (x ^ 2).toMonoidHom := by rw [hcomp]
      _ = Wt := hWtx2
  have hxw_mem : x w ∈ Wp := Subgroup.mem_map_of_mem x.toMonoidHom hwWt
  have hxw'_mem : x w' ∈ Wt := by
    have hh : x w' ∈ Wp.map x.toMonoidHom := Subgroup.mem_map_of_mem x.toMonoidHom hwWp
    rwa [hWpx] at hh
  have hxv : x (v : Vtil V₀ V hV) = (v : Vtil V₀ V hV) := mem_fixV.mp hvT x hxT
  have huniqv := s1611e3_c6_eq_of_mul_eq_mul_of_inf_bot hinfW hxw'_mem hxw_mem hwWt hwWp
    (by
      have hh : x w * x w' = w * w' := by
        have h2 := hxv
        rw [← hwv, map_mul] at h2
        exact h2
      rw [mul_comm (x w') (x w)]
      exact hh)
  have hxw : x w = w' := huniqv.2
  have hxw' : x w' = w := huniqv.1
  have hw1 : w ≠ 1 := by
    intro hw
    have hw'1 : w' = 1 := by rw [← hxw, hw, map_one]
    exact hvne (by rw [← hwv, hw, hw'1, mul_one])
  have hw'1 : w' ≠ 1 := by
    intro hw'
    have hw1' : w = 1 := by rw [← hxw', hw', map_one]
    exact hw1 hw1'
  have hwT1 : w ∈ fixV T1 := by
    rw [mem_fixV]
    intro t ht
    have htv : t (v : Vtil V₀ V hV) = (v : Vtil V₀ V hV) := mem_fixV.mp hvT t ht.1
    have htw' : t w' = w' := hfixAW t ht.2 w' hwWp
    have hmul : t w * w' = w * w' := by
      have hh := htv
      rw [← hwv, map_mul, htw'] at hh
      exact hh
    exact mul_right_cancel hmul
  have hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) Lb Wt ⊥ 2 := by
    rcases h6.2.1 with ⟨hAlt, -⟩ | ⟨-, hsum⟩
    · exfalso
      obtain ⟨e⟩ := hAlt
      have h1 : Nat.card ↥Lb = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num
      omega
    · simpa [← hLb, ← hWt] using hsum
  set P : Subgroup (MulAut (Vtil V₀ V hV)) := Lb ⊓ centSub (Subgroup.zpowers w) with hP
  have hPcard : Nat.card ↥P = 24 := by
    rw [hP]
    exact s1611e3_para_stab hL3 (Or.inl ⟨rfl, rfl⟩) hsum hT1L hT1syl hZcard hZJ hZL hZf
      w ⟨hwWt, hwT1⟩ hw1
  have hT1P : T1 ≤ P := by
    intro t ht
    exact ⟨ht.2, mem_centSub.mpr fun y hy =>
      mem_fixV.mp (Subgroup.zpowers_le.mpr hwT1 hy) t ht⟩
  have hPL : P ≤ Lb := inf_le_left
  obtain ⟨Pstar, hPstarL, hT1Pstar, hPstarcard, hPstar_ne_P, hPinfPstar, hPuniq⟩ :=
    s1611e3_c6_two_parabolics hL3 hT1L hT1card hPL hPcard hT1P
  set Pstar' : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Pstar.map (MulAut.conj x).toMonoidHom with hPstar'
  have hPstar'L : Pstar' ≤ Lp := by
    rw [hPstar', hLp]
    exact Subgroup.map_mono hPstarL
  have hPstar'card : Nat.card ↥Pstar' = 24 := by
    rw [hPstar', Subgroup.card_map_of_injective (MulAut.conj x).injective, hPstarcard]
  have hPinfPstar' : Pstar ⊓ Pstar' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyLb : y ∈ Lb := hPstarL hy.1
    have hyLp : y ∈ Lp := hPstar'L hy.2
    have hbot : Lb ⊓ Lp = ⊥ := hinfA
    exact (Subgroup.mem_bot.mp (hbot ▸ ⟨hyLb, hyLp⟩))
  have hcommPP' : ∀ p ∈ Pstar, ∀ q ∈ Pstar', p * q = q * p := by
    intro p hp q hq
    exact hcomm p (hPstarL hp) q (hPstar'L hq)
  have hx2T0 : x ^ 2 ∈ T0 :=
    ⟨Subgroup.pow_mem _ hxT 2, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hx2N⟩
  have hxT0 : x ∉ T0 := fun hx0 =>
    hxLb_ne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hx0.2)
  have huniqCls : ∀ a ∈ Tb, ∀ b ∈ Tb, Lb.map (MulAut.conj a).toMonoidHom ≠ Lb →
      Lb.map (MulAut.conj b).toMonoidHom ≠ Lb →
      Lb.map (MulAut.conj a).toMonoidHom = Lb.map (MulAut.conj b).toMonoidHom := by
    intro a ha b hb ha1 hb1
    rcases hswap a (hTbMb ha) with h | h
    · exact absurd h.1 ha1
    rcases hswap b (hTbMb hb) with h' | h'
    · exact absurd h'.1 hb1
    exact h.1.trans h'.1.symm
  have hT0index : T0.relIndex Tb = 2 := by
    have hidx := s1611e3_relIndex_stabilizer_eq_two (X := Tb) (K := Lb) (x₁ := x)
      hxT hxLb_ne huniqCls
    simpa [hT0, Subgroup.relIndex] using hidx
  have hTbT0 : T0 ≤ Tb := inf_le_left
  have hTbsup : T0 ⊔ Subgroup.zpowers x = Tb := by
    have hle : T0 ⊔ Subgroup.zpowers x ≤ Tb :=
      sup_le hTbT0 (Subgroup.zpowers_le.mpr hxT)
    have hdvd : (T0 ⊔ Subgroup.zpowers x).relIndex Tb ∣ T0.relIndex Tb :=
      Subgroup.relIndex_dvd_of_le_left (L := Tb) le_sup_left
    rw [hT0index] at hdvd
    have hrel : (T0 ⊔ Subgroup.zpowers x).relIndex Tb = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exfalso
        have hmul := Subgroup.relIndex_mul_relIndex (H := T0)
          (K := T0 ⊔ Subgroup.zpowers x) (L := Tb) le_sup_left hle
        rw [hT0index, h] at hmul
        have h1 : T0.relIndex (T0 ⊔ Subgroup.zpowers x) = 1 := by omega
        have h2 : T0 ⊔ Subgroup.zpowers x ≤ T0 := Subgroup.relIndex_eq_one.mp h1
        exact hxT0 (h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hrel)
  have hT0fix_alt : ∀ t ∈ T0, (Lb.map (MulAut.conj t).toMonoidHom = Lb ∧
      Lp.map (MulAut.conj t).toMonoidHom = Lp ∧ Wt.map t.toMonoidHom = Wt ∧
      Wp.map t.toMonoidHom = Wp) := by
    intro t ht
    have htLb : Lb.map (MulAut.conj t).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
    rcases hswap t (hTbMb ht.1) with h | h
    · exact h
    · exact absurd (by rw [← hLp, ← h.1]; exact htLb) hxLb_ne
  have hT0fixw : ∀ t ∈ T0, t w = w := by
    intro t ht
    obtain ⟨-, -, hWtmap, hWpmap⟩ := hT0fix_alt t ht
    have htv : t (v : Vtil V₀ V hV) = (v : Vtil V₀ V hV) := mem_fixV.mp hvT t ht.1
    have htw_mem : t w ∈ Wt := by
      have h := Subgroup.mem_map_of_mem t.toMonoidHom hwWt
      rwa [hWtmap] at h
    have htw'_mem : t w' ∈ Wp := by
      have h := Subgroup.mem_map_of_mem t.toMonoidHom hwWp
      rwa [hWpmap] at h
    have hmul : t w * t w' = w * w' := by
      have h := htv
      rw [← hwv, map_mul] at h
      exact h
    exact (s1611e3_c6_eq_of_mul_eq_mul_of_inf_bot hinfW htw_mem htw'_mem hwWt hwWp hmul).1
  have hT0T1 : ∀ t ∈ T0, T1.map (MulAut.conj t).toMonoidHom = T1 := by
    intro t ht
    have htTb : Tb.map (MulAut.conj t).toMonoidHom = Tb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht.1)
    have htLb : Lb.map (MulAut.conj t).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
    rw [hT1, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, htTb, htLb]
  have hT0P : ∀ t ∈ T0, P.map (MulAut.conj t).toMonoidHom = P := by
    intro t ht
    have htLb : Lb.map (MulAut.conj t).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
    have htw : t w = w := hT0fixw t ht
    have hcent : (centSub (Subgroup.zpowers w)).map (MulAut.conj t).toMonoidHom =
        centSub (Subgroup.zpowers w) := by
      rw [← s1611e3_c6_centSub_map_conj]
      congr 1
      rw [MonoidHom.map_zpowers, show t.toMonoidHom w = w from htw]
    rw [hP, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, htLb, hcent]
  have hT0Pstar : ∀ t ∈ T0, Pstar.map (MulAut.conj t).toMonoidHom = Pstar := by
    intro t ht
    have htLb : Lb.map (MulAut.conj t).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
    have htT1 : T1.map (MulAut.conj t).toMonoidHom = T1 := hT0T1 t ht
    have hPt : P.map (MulAut.conj t).toMonoidHom = P := hT0P t ht
    have hle : Pstar.map (MulAut.conj t).toMonoidHom ≤ Lb := by
      rw [← htLb]; exact Subgroup.map_mono hPstarL
    have hT1le : T1 ≤ Pstar.map (MulAut.conj t).toMonoidHom := by
      rw [← htT1]; exact Subgroup.map_mono hT1Pstar
    have hcard : Nat.card ↥(Pstar.map (MulAut.conj t).toMonoidHom) = 24 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hPstarcard]
    rcases hPuniq _ hle hT1le hcard with h | h
    · exfalso
      apply hPstar_ne_P
      calc Pstar = (Pstar.map (MulAut.conj t).toMonoidHom).map
              (MulAut.conj t⁻¹).toMonoidHom :=
            (s1611e3_c6_map_conj_conj_inv t Pstar).symm
        _ = P.map (MulAut.conj t⁻¹).toMonoidHom := by rw [h]
        _ = P := by
            have h := s1611e3_c6_map_conj_conj_inv t P
            rwa [hPt] at h
    · exact h
  have hxin : ∀ t ∈ T0, x⁻¹ * t * x ∈ T0 := by
    intro t ht
    have hfixalt := hT0fix_alt t ht
    refine ⟨?_, ?_⟩
    · exact Tb.mul_mem (Tb.mul_mem (Tb.inv_mem hxT) ht.1) hxT
    · change x⁻¹ * t * x ∈ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV)))
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h' : (Lb.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom =
          Lb.map (MulAut.conj x).toMonoidHom := by
        change Lp.map (MulAut.conj t).toMonoidHom = Lp
        exact hfixalt.2.1
      have h2 : Lb.map (MulAut.conj (x⁻¹ * t * x)).toMonoidHom =
          ((Lb.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj x⁻¹).toMonoidHom :=
        (s1611e3_c6_sandwich x t Lb).symm
      change Lb.map (MulAut.conj (x⁻¹ * t * x)).toMonoidHom = Lb
      rw [h2, h', s1611e3_c6_map_conj_conj_inv]
  have hT0Pstar' : ∀ t ∈ T0, Pstar'.map (MulAut.conj t).toMonoidHom = Pstar' := by
    intro t ht
    have hu : Pstar.map (MulAut.conj (x⁻¹ * t * x)).toMonoidHom = Pstar :=
      hT0Pstar _ (hxin t ht)
    have hcomp := s1611e3_c6_conj_mul_comp x t
    calc Pstar'.map (MulAut.conj t).toMonoidHom
        = (Pstar.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
            rw [hPstar']
      _ = Pstar.map ((MulAut.conj t).toMonoidHom.comp (MulAut.conj x).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = Pstar.map ((MulAut.conj x).toMonoidHom.comp
            (MulAut.conj (x⁻¹ * t * x)).toMonoidHom) := by rw [hcomp]
      _ = (Pstar.map (MulAut.conj (x⁻¹ * t * x)).toMonoidHom).map
            (MulAut.conj x).toMonoidHom := by rw [Subgroup.map_map]
      _ = Pstar.map (MulAut.conj x).toMonoidHom := by rw [hu]
      _ = Pstar' := hPstar'
  have hxPstar' : Pstar'.map (MulAut.conj x).toMonoidHom = Pstar := by
    rw [hPstar', Subgroup.map_map]
    have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x ^ 2)).toMonoidHom := by
      have h1 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          (MulAut.conj x * MulAut.conj x).toMonoidHom := by ext y; rfl
      rw [h1, map_pow (MulAut.conj) x 2, pow_two]
    rw [hcomp]
    exact hT0Pstar (x ^ 2) hx2T0
  have hxinvT0 : ∀ t ∈ Tb, t ∉ T0 → x⁻¹ * t ∈ T0 := by
    intro t ht ht0
    refine ⟨Tb.mul_mem (Tb.inv_mem hxT) ht, ?_⟩
    change x⁻¹ * t ∈ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases hswap t (hTbMb ht) with h | h
    · exact absurd ⟨ht, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.1⟩ ht0
    · calc Lb.map (MulAut.conj (x⁻¹ * t)).toMonoidHom
          = (Lb.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
              rw [Subgroup.map_map, s1611e3_c6_conj_inv_comp]
        _ = Lp.map (MulAut.conj x⁻¹).toMonoidHom := by rw [h.1]
        _ = Lb := by rw [hLp]; exact s1611e3_c6_map_conj_conj_inv x Lb
  have hTbPstar : ∀ t ∈ Tb, Pstar.map (MulAut.conj t).toMonoidHom = Pstar ∨
      Pstar.map (MulAut.conj t).toMonoidHom = Pstar' := by
    intro t ht
    by_cases ht0 : t ∈ T0
    · exact Or.inl (hT0Pstar t ht0)
    · refine Or.inr ?_
      have hu : x⁻¹ * t ∈ T0 := hxinvT0 t ht ht0
      have ht_eq : x * (x⁻¹ * t) = t := by group
      rw [← ht_eq, s1611e3_c6_map_conj_mul, hT0Pstar _ hu, hPstar']
  have hTbPstar' : ∀ t ∈ Tb, Pstar'.map (MulAut.conj t).toMonoidHom = Pstar' ∨
      Pstar'.map (MulAut.conj t).toMonoidHom = Pstar := by
    intro t ht
    by_cases ht0 : t ∈ T0
    · exact Or.inl (hT0Pstar' t ht0)
    · refine Or.inr ?_
      have hu : x⁻¹ * t ∈ T0 := hxinvT0 t ht ht0
      have ht_eq : x * (x⁻¹ * t) = t := by group
      rw [← ht_eq, s1611e3_c6_map_conj_mul, hT0Pstar' _ hu, hxPstar']
  set Q : Subgroup (MulAut (Vtil V₀ V hV)) := Pstar ⊔ Pstar' with hQdef
  set N : Subgroup (MulAut (Vtil V₀ V hV)) := Z ⊔ Q with hN
  have hQLbLp : Q ≤ Lb ⊔ Lp := by
    rw [hQdef]
    exact sup_le (le_trans hPstarL le_sup_left) (le_trans hPstar'L le_sup_right)
  have hQcard : Nat.card ↥Q = 24 * 24 := by
    rw [hQdef]
    rw [CFSG.card_sup_eq_mul_of_commute Pstar Pstar'
      (fun p hp q hq => hcommPP' p hp q hq) hPinfPstar',
      hPstarcard, hPstar'card]
  have hZQ : Z ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (Subgroup.mem_bot.mp (hZinf ▸ ⟨hz.1, hQLbLp hz.2⟩))
  have hZcQ : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := by
    have hcent : Z ≤ Subgroup.centralizer (Q : Set (MulAut (Vtil V₀ V hV))) := by
      rw [hQdef]
      exact CFSG.le_centralizer_sup_of_commute_both
        (fun p hp q hq => hcommPP' p hp q hq)
        (fun z hz p hp => hZL z hz p (hPstarL hp))
        (fun z hz q hq => hZLp z hz q (hPstar'L hq))
    intro z hz q hq
    exact (Subgroup.mem_centralizer_iff.mp (hcent hz) q hq).symm
  have hT0Q : ∀ t ∈ T0, Q.map (MulAut.conj t).toMonoidHom = Q := by
    intro t ht
    rw [hQdef, Subgroup.map_sup, hT0Pstar t ht, hT0Pstar' t ht]
  have hxQ : Q.map (MulAut.conj x).toMonoidHom = Q := by
    rw [hQdef, Subgroup.map_sup, hxPstar', hPstar', sup_comm]
  have hTbQ : ∀ t ∈ Tb, Q.map (MulAut.conj t).toMonoidHom = Q := by
    intro t ht
    by_cases ht0 : t ∈ T0
    · exact hT0Q t ht0
    · have hu : x⁻¹ * t ∈ T0 := hxinvT0 t ht ht0
      have ht_eq : x * (x⁻¹ * t) = t := by group
      rw [← ht_eq, s1611e3_c6_map_conj_mul, hT0Q _ hu, hxQ]
  have hTbN : Tb ≤ Subgroup.normalizer (N : Set (MulAut (Vtil V₀ V hV))) := by
    intro t ht
    change t ∈ Subgroup.normalizer (N : Set (MulAut (Vtil V₀ V hV)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hN]
    calc (Z ⊔ Q).map (MulAut.conj t).toMonoidHom
        = Z.map (MulAut.conj t).toMonoidHom ⊔ Q.map (MulAut.conj t).toMonoidHom :=
          Subgroup.map_sup Z Q _
      _ = Z ⊔ Q := by rw [hZnorm t (hTbMb ht), hTbQ t ht]
  have hFacts := s16c167_cfg10_fstar_facts Mb
  have hFMb : Fstar Mb ≤ Mb := hFacts.1
  have hLbF : Lb ≤ Fstar Mb := by
    rw [hFsup]
    exact le_trans le_sup_left le_sup_right
  have hLpF : Lp ≤ Fstar Mb := by
    rw [hFsup]
    exact le_trans le_sup_right le_sup_right
  have hNMb : N ≤ Mb := by
    rw [hN]
    refine sup_le hZM ?_
    rw [hQdef]
    exact sup_le (hPstarL.trans (hLbF.trans hFMb)) (hPstar'L.trans (hLpF.trans hFMb))
  show S1611e3RouteF D V₀ V hV 3
  have hQN : Q ≤ N := by rw [hN]; exact le_sup_right
  have hQMb : Q ≤ Mb := hQN.trans hNMb
  have hTbQnorm : Tb ≤ Subgroup.normalizer (Q : Set (MulAut (Vtil V₀ V hV))) :=
    fun t ht => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hTbQ t ht)
  obtain ⟨m, hm⟩ := hTb2.exists_card_eq
  have hXQdvd : Nat.card ↥(Q ⊔ Tb) ∣ 2 ^ (m + 6) * 3 ^ 2 := by
    have hsup : Nat.card ↥(Q ⊔ Tb) ∣ Nat.card ↥Tb * Nat.card ↥Q := by
      rw [sup_comm]
      exact CFSG.Semidihedral.FixedCoreNontrivial.card_sup_dvd_mul_of_le_normalizer hTbQnorm
    refine hsup.trans ?_
    rw [hm, hQcard, show (24 : ℕ) * 24 = 2 ^ 6 * 3 ^ 2 by norm_num]
    rw [← mul_assoc, ← pow_add]
  have hWtmap : ∀ c ∈ Lb, Wt.map c.toMonoidHom = Wt := by
    intro c hc
    have hconj : Lb.map (MulAut.conj c).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)
    have h := s16c167_commSub_top_conj c Lb
    rw [hconj] at h
    have h1 : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb = Wt := by rw [hLb, hWt]; rfl
    rw [h1] at h
    exact h.symm
  have hQcent : ∀ s : MulAut (Vtil V₀ V hV), s ∈ Q → s ∈ centSub (fixV Tb) →
      orderOf s ≠ 3 := by
    intro s hsQ hscent hord
    have hsQ' : s ∈ Pstar ⊔ Pstar' := by rw [← hQdef]; exact hsQ
    obtain ⟨a, haP, b, hbP', hab⟩ :=
      s1611e3_c6_exists_mul_of_mem_sup_of_commute hcommPP' hsQ'
    have hab_comm : Commute a b := hcommPP' a haP b hbP'
    have hs3 : s ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one s
    have ha3 : a ^ 3 = 1 := by
      have h := hab_comm.mul_pow 3
      rw [hab, hs3] at h
      have hmem : a ^ 3 ∈ Pstar ⊓ Pstar' := by
        refine ⟨Pstar.pow_mem haP 3, ?_⟩
        have he : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h.symm
        rw [he]
        exact Pstar'.inv_mem (Pstar'.pow_mem hbP' 3)
      rwa [hPinfPstar', Subgroup.mem_bot] at hmem
    have hb3 : b ^ 3 = 1 := by
      have h := hab_comm.mul_pow 3
      rw [hab, hs3] at h
      have hmem : b ^ 3 ∈ Pstar ⊓ Pstar' := by
        refine ⟨?_, Pstar'.pow_mem hbP' 3⟩
        have he : b ^ 3 = (a ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
        rw [he]
        exact Pstar.inv_mem (Pstar.pow_mem haP 3)
      rwa [hPinfPstar', Subgroup.mem_bot] at hmem
    have hawWt : a w ∈ Wt := by
      have h := Subgroup.mem_map_of_mem a.toMonoidHom hwWt
      rwa [hWtmap a (hPstarL haP)] at h
    obtain ⟨a', ha'P, ha'b⟩ := Subgroup.mem_map.mp (by rwa [hPstar'] at hbP')
    have ha'wWt : a' w ∈ Wt := by
      have h := Subgroup.mem_map_of_mem a'.toMonoidHom hwWt
      rwa [hWtmap a' (hPstarL ha'P)] at h
    have hbw'Wp : b w' ∈ Wp := by
      have hb_eq : b w' = x (a' w) := by
        rw [← ha'b, ← hxw]
        simp [MulAut.conj_apply, MulAut.mul_apply]
      rw [hb_eq, hWp]
      exact Subgroup.mem_map_of_mem x.toMonoidHom ha'wWt
    have hs_v : s (v : Vtil V₀ V hV) = (v : Vtil V₀ V hV) :=
      mem_centSub.mp hscent _ hvT
    have hs_eq : a w * b w' = w * w' := by
      have h := hs_v
      rw [← hab, MulAut.mul_apply, ← hwv, map_mul, hfixBW b (hPstar'L hbP') w hwWt,
        map_mul, hfixAW a (hPstarL haP) (b w') hbw'Wp] at h
      exact h
    obtain ⟨haw, hbw'⟩ :=
      s1611e3_c6_eq_of_mul_eq_mul_of_inf_bot hinfW hawWt hbw'Wp hwWt hwWp hs_eq
    have haPmem : a ∈ P := by
      rw [hP]
      refine ⟨hPstarL haP, ?_⟩
      refine mem_centSub.mpr fun y hy => ?_
      have hle : Subgroup.zpowers w ≤ fixV (Subgroup.zpowers a) :=
        Subgroup.zpowers_le.mpr ((mem_fixV_zpowers a w).mpr haw)
      exact (mem_fixV_zpowers a y).mp (hle hy)
    have haT1 : a ∈ T1 := by rw [← hPinfPstar]; exact ⟨haPmem, haP⟩
    have ha1 : a = 1 := by
      have h8 : orderOf (⟨a, haT1⟩ : ↥T1) ∣ 8 := by
        have := orderOf_dvd_natCard (⟨a, haT1⟩ : ↥T1)
        rwa [hT1card] at this
      have h3 : orderOf (⟨a, haT1⟩ : ↥T1) ∣ 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_dvd_iff_pow_eq_one.mpr ha3
      have h1 : orderOf (⟨a, haT1⟩ : ↥T1) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 8 3) h8 h3
      exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)
    have ha'w : a' w = w := by
      have h := hbw'
      rw [← ha'b, ← hxw] at h
      have h4 : x (a' w) = x w := by
        simpa [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self] using h
      exact x.injective h4
    have ha'Pmem : a' ∈ P := by
      rw [hP]
      refine ⟨hPstarL ha'P, ?_⟩
      refine mem_centSub.mpr fun y hy => ?_
      have hle : Subgroup.zpowers w ≤ fixV (Subgroup.zpowers a') :=
        Subgroup.zpowers_le.mpr ((mem_fixV_zpowers a' w).mpr ha'w)
      exact (mem_fixV_zpowers a' y).mp (hle hy)
    have ha'T1 : a' ∈ T1 := by rw [← hPinfPstar]; exact ⟨ha'Pmem, ha'P⟩
    have ha'3 : a' ^ 3 = 1 := by
      have hab_coe : (MulAut.conj x) a' = b := by simpa using ha'b
      apply (MulAut.conj x).injective
      rw [map_pow, hab_coe, hb3, map_one]
    have ha'1 : a' = 1 := by
      have h8 : orderOf (⟨a', ha'T1⟩ : ↥T1) ∣ 8 := by
        have := orderOf_dvd_natCard (⟨a', ha'T1⟩ : ↥T1)
        rwa [hT1card] at this
      have h3 : orderOf (⟨a', ha'T1⟩ : ↥T1) ∣ 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_dvd_iff_pow_eq_one.mpr ha'3
      have h1 : orderOf (⟨a', ha'T1⟩ : ↥T1) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 8 3) h8 h3
      exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)
    have hb1 : b = 1 := by rw [← ha'b, ha'1, map_one]
    have hs1 : s = 1 := by rw [← hab, ha1, hb1, one_mul]
    rw [hs1, orderOf_one] at hord
    omega
  refine ⟨Q ⊔ Tb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hMb]
    exact sup_le hQMb hTbMb
  · rw [← hTb]
    exact le_sup_right
  · exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (a := m + 6) (b := 2) hXQdvd
  · intro x hxX hx3n
    obtain ⟨n, hn⟩ := hx3n
    have hodd : Odd (orderOf x) := by
      have hdvd : orderOf x ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
      obtain ⟨k, hk⟩ := hdvd
      have h3 : Odd (3 ^ n) := Odd.pow (n := n) (by norm_num : Odd (3 : ℕ))
      rw [hk] at h3
      exact Nat.Odd.of_mul_left h3
    have hxQ : x ∈ Q :=
      CFSG.Semidihedral.FixedCoreNontrivial.mem_of_odd_of_mem_sup hTbQnorm hTb2 hxX hodd
    have hxQ' : x ∈ Pstar ⊔ Pstar' := by rw [← hQdef]; exact hxQ
    obtain ⟨a, haP, b, hbP', hab⟩ :=
      s1611e3_c6_exists_mul_of_mem_sup_of_commute hcommPP' hxQ'
    have hab_comm : Commute a b := hcommPP' a haP b hbP'
    have ha3n : a ^ 3 ^ n = 1 := by
      have h := hab_comm.mul_pow (3 ^ n)
      rw [hab, hn] at h
      have hmem : a ^ 3 ^ n ∈ Pstar ⊓ Pstar' := by
        refine ⟨Pstar.pow_mem haP _, ?_⟩
        have he : a ^ 3 ^ n = (b ^ 3 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h.symm
        rw [he]
        exact Pstar'.inv_mem (Pstar'.pow_mem hbP' _)
      rwa [hPinfPstar', Subgroup.mem_bot] at hmem
    have hb3n : b ^ 3 ^ n = 1 := by
      have h := hab_comm.mul_pow (3 ^ n)
      rw [hab, hn] at h
      have hmem : b ^ 3 ^ n ∈ Pstar ⊓ Pstar' := by
        refine ⟨?_, Pstar'.pow_mem hbP' _⟩
        have he : b ^ 3 ^ n = (a ^ 3 ^ n)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
        rw [he]
        exact Pstar.inv_mem (Pstar.pow_mem haP _)
      rwa [hPinfPstar', Subgroup.mem_bot] at hmem
    have ha3 : a ^ 3 = 1 := by
      have h := s1611e3_c6_pow_three_eq_one_of_card_24 (X := ↥Pstar) hPstarcard
        (x := ⟨a, haP⟩) ⟨n, by simpa using ha3n⟩
      simpa using h
    have hb3 : b ^ 3 = 1 := by
      have h := s1611e3_c6_pow_three_eq_one_of_card_24 (X := ↥Pstar') hPstar'card
        (x := ⟨b, hbP'⟩) ⟨n, by simpa using hb3n⟩
      simpa using h
    have hx3 : x ^ 3 = 1 := by
      have h := hab_comm.mul_pow 3
      rw [hab, ha3, hb3, one_mul] at h
      exact h
    exact hx3
  · set R : Subgroup (MulAut (Vtil V₀ V hV)) :=
      (Q ⊔ Tb) ⊓ centSub (fixV (barSub V₀ V hV D.T)) with hR
    have hR3 : ¬ 3 ∣ Nat.card ↥R := by
      intro h3dvd
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
      have hyord : orderOf (y : MulAut (Vtil V₀ V hV)) = 3 := by
        rw [← Subgroup.orderOf_mk y.1 y.2]
        exact hy
      have hyodd : Odd (orderOf (y : MulAut (Vtil V₀ V hV))) := by
        rw [hyord]
        exact ⟨1, by norm_num⟩
      have hyQ : (y : MulAut (Vtil V₀ V hV)) ∈ Q :=
        CFSG.Semidihedral.FixedCoreNontrivial.mem_of_odd_of_mem_sup hTbQnorm hTb2 y.2.1 hyodd
      have hycent : (y : MulAut (Vtil V₀ V hV)) ∈ centSub (fixV Tb) := y.2.2
      exact hQcent _ hyQ hycent hyord
    have hpadR : padicValNat 3 (Nat.card ↥R) = 0 :=
      padicValNat.eq_zero_of_not_dvd hR3
    have hXQpos : Nat.card ↥(Q ⊔ Tb) ≠ 0 :=
      (Nat.card_pos : 0 < Nat.card ↥(Q ⊔ Tb)).ne'
    have hle2 : padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) ≤ 2 := by
      have h1 : 3 ^ padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) ∣ Nat.card ↥(Q ⊔ Tb) :=
        pow_padicValNat_dvd
      have h2 : 3 ^ padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) ∣ 2 ^ (m + 6) * 3 ^ 2 :=
        h1.trans hXQdvd
      have h3 : padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) ≤
          padicValNat 3 (2 ^ (m + 6) * 3 ^ 2) :=
        (padicValNat_dvd_iff_le (p := 3) (by positivity : 2 ^ (m + 6) * 3 ^ 2 ≠ 0)).mp h2
      have hnot3 : ¬ 3 ∣ 2 ^ (m + 6) := by
        intro hd
        exact (by norm_num : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
      have h4 : padicValNat 3 (2 ^ (m + 6) * 3 ^ 2) = 2 := by
        rw [padicValNat.mul (by positivity) (by positivity),
          padicValNat.eq_zero_of_not_dvd hnot3,
          padicValNat.prime_pow]
      omega
    have hge2 : 2 ≤ padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) := by
      have hQ3 : 3 ^ 2 ∣ Nat.card ↥Q := by
        rw [hQcard]
        exact ⟨2 ^ 6, by norm_num⟩
      have hdvd : 3 ^ 2 ∣ Nat.card ↥(Q ⊔ Tb) :=
        hQ3.trans (Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ Tb))
      exact (padicValNat_dvd_iff_le (p := 3) hXQpos).mp hdvd
    have hXQ2 : padicValNat 3 (Nat.card ↥(Q ⊔ Tb)) = 2 := le_antisymm hle2 hge2
    rw [hpadR, hXQ2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
