module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Quasithin.Vol2.Ch10SecEFix
public import CFSG.Quasithin.Background.E2Three
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Frame

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_isAltType_three' {K : Subgroup G} (h : IsAltType K 3) :
    Group.IsSolvable ↥K := by
  obtain ⟨α, -, hker, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  have : Group.IsSolvable ↥(alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥K).subtype α
    (by rw [hker, Subgroup.range_subtype])

theorem false_of_isSolvable_subnormal_sup {X T L K : Subgroup G} (hT : IsPGroup 2 T)
    (hTX : T ≤ X) (hL : L ∈ cComp X) (hKX : K ≤ X) (hsub : (K.subgroupOf X).IsSubnormal)
    (hsol : Group.IsSolvable ↥K) (heq : X = K ⊔ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsol' : Group.IsSolvable ↥(K.subgroupOf X) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKX).symm.surjective
  set R := CFSG.solvableRadical ↥X with hR
  have hKR : K.subgroupOf X ≤ R := by
    rw [hR, A3.solvableRadical_eq_solvRad_top]
    exact le_solvRad_of_subnormal (A3.subnormal_top_iff.mpr hsub) hsol'
  have htop : R ⊔ T.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup ↥X) = (K ⊔ T).subgroupOf X := by rw [← heq, Subgroup.subgroupOf_self]
      _ = K.subgroupOf X ⊔ T.subgroupOf X := Subgroup.subgroupOf_sup hKX hTX
      _ ≤ R ⊔ T.subgroupOf X := sup_le_sup_right hKR _
  have hT2 : IsPGroup 2 ↥(T.subgroupOf X) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp (T.subgroupOf X).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hx : x ∈ ((R ⊔ T.subgroupOf X : Subgroup ↥X) : Set ↥X) := by rw [htop]; trivial
    rw [Subgroup.normal_mul] at hx
    obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := (A3.instNormalSolvableRadical ↥X).conj_mem r hr s⁻¹
    simpa [mul_assoc] using h1
  have hQ : IsPGroup 2 (↥X ⧸ R) := hT2.of_surjective _ hsurj
  have : Group.IsNilpotent (↥X ⧸ R) := hQ.isNilpotent
  have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  have hXs : Group.IsSolvable ↥X :=
    Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLs : Group.IsSolvable ↥L :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLX).surjective
  exact not_isSolvable_of_mem_cComp hL hLs

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem normalizer_le_of_le (h : Hyp5_0_1 G T M L n) (h432 : Stmt4_3_2) {C : Subgroup G}
    (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hLC : L ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ M := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨C, hC, hC2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have h1 := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1 M' hM' (hLC.trans hle)
  rw [← h1]
  exact hle

theorem le_of_isShort2 (h : Hyp5_0_1 G T M L n) {K : Subgroup G} (hK : IsShort2 K)
    (hKX : K ≤ L ⊔ T) : K ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := hKX.trans h.sup_le_normalizer
  have hNn : (L.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKN g.2) x).mp hx
  have h2 : IsPGroup 2 (↥K ⧸ L.subgroupOf K) := by
    intro q
    induction q using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 h.T_le_normalizer x (hKX x.2)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  have htop := hK.1 (L.subgroupOf K) h2
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ L.subgroupOf K := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem le_T_of_isCh5Module (h : Hyp5_0_1 G T M L n) {V : Subgroup G}
    (hV : IsCh5Module T L V) : V ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hV2 : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 v v.2)⟩
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hred.2.1 hV2).trans
    (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_right))

theorem commutator_le_pCoreOf (h : Hyp5_0_1 G T M L n) {V : Subgroup G}
    (hV : IsCh5Module T L V) : ⁅V, L⁆ ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := (h.le_T_of_isCh5Module hV).trans
    h.T_le_normalizer
  have hV2 : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 v v.2)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hVL)
    (le_normalizer_commutator_of hLV Subgroup.le_normalizer)
    (hV2.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hLV))

theorem pCoreOf_le_centralizer (h : Hyp5_0_1 G T M L n) {V : Subgroup G}
    (hV : IsCh5Module T L V) : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal L (L ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer)
      (IsSubnormal.refl _)
  have h1 := A4.pCoreOf_le_of_subnormal 2 hsub
  rw [← h.sup_inf_centralizer_eq hV] at h1
  exact h1.trans inf_le_right

end Hyp5_0_1

section Frame

variable {G : Type} [Group G] [Finite G] {T L W : Subgroup G}

omit [Finite G] in
theorem S5Frame.exists_mem_of_sign (F : S5Frame (L ⊔ T) W) (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (σ : Perm (Fin 5)) (hσ : Perm.sign σ = 1) :
    ∃ x : ↥(L ⊔ T), (x : G) ∈ L ∧ F.ρ x = σ := by
  set R : Subgroup (Perm (Fin 5)) := (L.subgroupOf (L ⊔ T)).map F.ρ with hRdef
  have h3 : ∀ c : Perm (Fin 5), c.IsThreeCycle → c ∈ R := by
    intro c hc
    obtain ⟨x, hx⟩ := F.ρ_surj c
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hT hTL x x.2
    have hmem : c ^ 2 ^ e ∈ R :=
      ⟨x ^ 2 ^ e, Subgroup.mem_subgroupOf.mpr (by simpa using he), by rw [map_pow, hx]⟩
    have hcpow : (c ^ 2 ^ e) ^ 2 ^ e = c := by
      rw [← pow_mul, ← pow_mod_orderOf, hc.orderOf]
      have h4 : 2 ^ e * 2 ^ e % 3 = 1 := by
        rw [← mul_pow]
        norm_num [Nat.pow_mod]
      rw [h4, pow_one]
    rw [← hcpow]
    exact R.pow_mem hmem _
  have hA : alternatingGroup (Fin 5) ≤ R := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    exact (Subgroup.closure_le R).mpr fun c hc => h3 c hc
  obtain ⟨x, hxL, hxσ⟩ := hA (Perm.mem_alternatingGroup.mpr hσ)
  exact ⟨x, Subgroup.mem_subgroupOf.mp hxL, hxσ⟩

theorem pmv_c3_fix : pmv (swap 0 1 * swap 1 2) ![0, 0, 0, 1, 1] = ![0, 0, 0, 1, 1] := by
  decide

theorem pmv_c234_move : pmv (swap 2 3 * swap 3 4) ![0, 0, 0, 1, 1] ≠ ![0, 0, 0, 1, 1] := by
  decide

theorem pmv_comm_e34 :
    ![0, 0, 1, 1, 0] + pmv (swap 0 1 * swap 3 4) ![0, 0, 1, 1, 0] = ![0, 0, 0, 1, 1] := by
  decide

theorem c3_sq_ne_one : (swap 0 1 * swap 1 2 : Perm (Fin 5)) * (swap 0 1 * swap 1 2) ≠ 1 := by
  decide

omit [Finite G] in
theorem false_of_isLin2Type {Y : Subgroup G} (F : S5Frame Y W)
    (hLρ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ x : ↥Y, (x : G) ∈ L ∧ F.ρ x = σ)
    (hWQ : W ≤ pCoreOf 2 L) (hO2W : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) {n : ℕ}
    (hlin : IsLin2Type L n) : False := by
  classical
  obtain ⟨𝕜, _, _, h𝕜, α, -, hαk, β, -, hβk, hβe⟩ := hlin
  obtain ⟨x, hxL, hx⟩ := hLρ (swap 0 1 * swap 1 2) (by decide)
  obtain ⟨y, hyL, hy⟩ := hLρ (swap 2 3 * swap 3 4) (by decide)
  obtain ⟨l, hlL, hl⟩ := hLρ (swap 0 1 * swap 3 4) (by decide)
  obtain ⟨u, hu⟩ := F.c_surj ![0, 0, 1, 1, 0] (by decide)
  have hlu : (l : G) * ((u⁻¹ : ↥W) : G) * (l : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (F.le l.2) _).mp (u⁻¹).2
  set w : ↥W := u * ⟨_, hlu⟩ with hwdef
  have hwc : F.c w = ![0, 0, 0, 1, 1] := by
    rw [hwdef, F.c_mul, F.equiv l u⁻¹ hlu, F.c_inv, hl, hu]
    exact pmv_comm_e34
  have hwB : (w : G) ∈ blockU L := by
    have h1 : (w : G) = ⁅(u : G), (l : G)⁆ := by
      rw [hwdef, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact Subgroup.commutator_mem_commutator (hWQ u.2) hlL
  have hxw' : (x : G) * w * (x : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (F.le x.2) w).mp w.2
  have hxw : (x : G) * w * (x : G)⁻¹ = w := by
    have h1 := F.equiv x w hxw'
    rw [hx, hwc, pmv_c3_fix, ← hwc] at h1
    exact congrArg Subtype.val (F.c_inj h1)
  have hwC : (w : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro hwz
    have hyw' : (y : G) * w * (y : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (F.le y.2) w).mp w.2
    have h1 := F.equiv y w hyw'
    have h2 : (⟨(y : G) * w * (y : G)⁻¹, hyw'⟩ : ↥W) = w := by
      apply Subtype.ext
      show (y : G) * w * (y : G)⁻¹ = w
      rw [Subgroup.mem_centralizer_iff.mp hwz y hyL, mul_inv_cancel_right]
    rw [h2, hy, hwc] at h1
    exact pmv_c234_move h1.symm
  have hβw : Multiplicative.toAdd (β ⟨w, hwB⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w, hwB⟩ = 1 := Multiplicative.toAdd.injective h0
    have h3 : (⟨w, hwB⟩ : ↥(blockU L)) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h3
    exact hwC h3.2
  have hfix := hβe ⟨x, hxL⟩ ⟨w, hwB⟩ ⟨w, hwB⟩ hxw.symm
  have hc𝕜 : Nat.card 𝕜 = 2 ^ n := by rw [Nat.card_eq_fintype_card, h𝕜]
  have : CharP 𝕜 2 := charP_two_of_card hc𝕜
  have hsq := Vol2.Ch10.SecE.mul_self_eq_one_of_mulVec_eq CharTwo.two_eq_zero
    (α ⟨x, hxL⟩).2 hβw hfix.symm
  have hα : α (⟨x, hxL⟩ * ⟨x, hxL⟩) = 1 := by
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hsq]
    rfl
  have hker : (⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk]
    exact hα
  have hxx : (x : G) * x ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hker
  have hρ : F.ρ (x * x) = 1 := (F.ρ_eq_one_iff _).2 (hO2W hxx)
  rw [map_mul, hx] at hρ
  exact c3_sq_ne_one hρ

end Frame

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem isA5Block (he234 : E2.E23FourStatement) (h432 : Stmt4_3_2) (hR : L2RankOneSylowFact)
    (h : Hyp5_0_1 G T M L n) {V W : Subgroup G} (hV : IsCh5Module T L V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hNS : ¬ Subgroup.normalizer (baum T : Set G) ≤ M) (F : S5Frame (L ⊔ T) W)
    (hWQ : W ≤ pCoreOf 2 L) (hO2W : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    IsShort2 L ∧ IsAltType L 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    intro C hCS hC hch hLN
    exact hNS ((normalizer_le_normalizer_of_characteristic hCS hch).trans
      (h.normalizer_le_of_le h432 hC (h.sylow.1.to_le (hCS.trans inf_le_left))
        (le_sup_left.trans hLN)))
  have hct : CharTwo (L ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, h.maximal.1.2.2.2⟩
  obtain ⟨K, hKb, hKT, hKC⟩ := he234 G (L ⊔ T) T (borelL T L ⊔ T) V (h.minParabolic_sup hR)
    h.sqtkGroup_sup hct hV.isTwoReducedIn hJ hchar
  have hLc : L ∈ cComp (L ⊔ T) := h.maximal.1.2.1
  have hn3 : ¬ IsAltType K 3 := fun h3 =>
    false_of_isSolvable_subnormal_sup h.sylow.1 le_sup_right hLc hKb.1.2.1 hKb.1.2.2
      (isSolvable_of_isAltType_three' h3) hKT
  have hKc : K ∈ cComp (L ⊔ T) := hKC hn3
  have hKL : K ≤ L := h.le_of_isShort2 hKb.1.1 hKb.1.2.1
  have hKeq : K = L := by
    by_contra hne
    exact hLc.2.2.2 K (lt_of_le_of_ne hKL hne) hKc.1 hKc.2.1 hKc.2.2.1
  rw [hKeq] at hKb
  obtain ⟨⟨hsh, -, -⟩, hty⟩ := hKb
  refine ⟨hsh, ?_⟩
  rcases hty with ⟨m, -, hlin⟩ | h3 | h5
  · exact (false_of_isLin2Type F (F.exists_mem_of_sign h.sylow.1 h.T_le_normalizer) hWQ hO2W
      hlin).elim
  · exact (not_isSolvable_of_mem_cComp hLc (isSolvable_of_isAltType_three' h3)).elim
  · exact h5

end Hyp5_0_1

end CFSG.Quasithin.H13
