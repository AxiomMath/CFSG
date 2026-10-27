module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522One
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522
public import CFSG.Quasithin.Vol2.Ch5Sec1L34BorelThree
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem card_B_eq_three (h510 : Stmt5_1_10) : Nat.card B = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf h.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hker : π.ker ≤ (T ⊓ K).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := ⟨x, by assumption, rfl⟩
    exact CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK hx'
  have hS : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map π) ⊤ := by
    refine ⟨le_top, IsPGroup.map (A4.isPGroup_subgroupOf_of_le hTK.1 hTK.2.1) _, ?_⟩
    have h1 : ((((T ⊓ K).subgroupOf K).map π).subgroupOf ⊤).index =
        (((T ⊓ K).subgroupOf K).map π).index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
    exact hTK.2.2
  obtain ⟨y', hy'N, hy'3⟩ := exists_orderOf_eq_three_mem_normalizer h.l34 hS
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y'
  have hyN : (y : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forall_conj_mem'
    intro t ht
    set t' : ↥K := ⟨t, ht.2⟩ with ht'
    have hmem : π (y * t' * y⁻¹) ∈ ((T ⊓ K).subgroupOf K).map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy'N _).mp ⟨t', ht, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hk : s'⁻¹ * (y * t' * y⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs'e, inv_mul_cancel]
    have h1 : y * t' * y⁻¹ ∈ (T ⊓ K).subgroupOf K := by
      have e : y * t' * y⁻¹ = s' * (s'⁻¹ * (y * t' * y⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ hs' (hker hk)
    exact Subgroup.mem_subgroupOf.mp h1
  have hyMK : (y : G) ∈ M ⊓ K := by
    rw [hMK]
    exact ⟨y.2, hyN⟩
  have h3MK : 3 ∣ Nat.card ↥(M ⊓ K) := by
    have h1 : 3 ∣ orderOf y := by
      rw [← hy'3]
      exact orderOf_map_dvd _ y
    have h2 := orderOf_dvd_natCard (⟨(y : G), hyMK⟩ : ↥(M ⊓ K))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h2
    exact h1.trans h2
  obtain ⟨hBle, -, j, hj⟩ := hBK
  have e1 := B.relIndex_mul_card (M ⊓ K)
  rw [inf_eq_left.mpr hBle, hj] at e1
  rw [← e1] at h3MK
  have h3B : 3 ∣ Nat.card B :=
    (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h3MK
  exact Nat.dvd_antisymm (h.card_B_dvd_three h510 l34BorelFact) h3B

theorem pow_three_eq_one_of_pow_nine (h516 : Stmt5_1_16) {x : G}
    (hx : x ∈ Subgroup.normalizer (oTwoUpper H : Set G)) (hx9 : x ^ 9 = 1) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := oTwoUpper H with hKdef
  let y : ↥(Subgroup.normalizer (K : Set G)) := ⟨x, hx⟩
  have hy9 : quotConjAut K y ^ 9 = 1 := by
    rw [← map_pow]
    have : y ^ 9 = 1 := Subtype.ext (by simpa [y] using hx9)
    rw [this, map_one]
  have hy3 := l34AutNoNineFact _ h.l34 _ hy9
  rw [← map_pow] at hy3
  have hmem : x ^ 3 ∈ centralizerModO2 K := by
    have := mem_centralizerModO2_of_quotConjAut_eq_one hy3
    simpa [y] using this
  by_contra hne
  have hx3 : orderOf (x ^ 3) = 3 := orderOf_eq_prime (by rw [← pow_mul]; exact hx9) hne
  have hdvd : 3 ∣ Nat.card ↥(centralizerModO2 K) := by
    have := orderOf_dvd_natCard (⟨x ^ 3, hmem⟩ : ↥(centralizerModO2 K))
    rwa [Subgroup.orderOf_mk, hx3] at this
  exact (h516 G T M L V H B D n h.hyp h.notation59 h.module h.l34).1 hdvd

theorem pow_three_eq_one_of_pow_three_pow (h516 : Stmt5_1_16) {x : G}
    (hx : x ∈ Subgroup.normalizer (oTwoUpper H : Set G)) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ^ 3 = 1 := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, pow_one] at hk
    rw [hk, one_pow]
  | succ k ih =>
    have h1 : (x ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hk
    have h2 := ih ((Subgroup.normalizer _).pow_mem hx 3) h1
    refine h.pow_three_eq_one_of_pow_nine h516 hx ?_
    calc x ^ 9 = (x ^ 3) ^ 3 := by rw [← pow_mul]
      _ = 1 := h2

end Hyp5_1_14

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem centralizer_le_normalizer (h5114 : Stmt5_1_14_first) :
    Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤
      Subgroup.normalizer (oTwoUpper H : Set G) := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hCz := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module
    s.hyp.l34).2.1.2 z (s.Z₁_le_Z hz) hz1
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjClosure Z₁ D₃ hz))).trans hCz

theorem not_le_centralizer (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    ¬ oTwoUpper H ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  intro hKC
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hb : ⁅conjClosure Z₁ D₃, pCoreOf 2 (oTwoUpper H)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp ((pCoreOf_le 2 _).trans hKC))
  rw [s.commutator_eq h5114 hF h521 hnot] at hb
  have : z ∈ (⊥ : Subgroup G) := hb ▸ hz
  exact hz1 (Subgroup.mem_bot.mp this)

theorem not_elemAbelian_nine (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G))
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE9 : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hNX := s.normalizer_le h5114 hF h521 hnot
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  set G₂ := Subgroup.normalizer (V₂ : Set G) with hG₂def
  set P := pCoreOf 2 C with hPdef
  have hCG : G₂ ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer le_rfl
  have hPG : G₂ ≤ Subgroup.normalizer (P : Set G) :=
    hCG.trans (normalizer_le_normalizer_pCoreOf 2 C)
  have hCG₂ : C ≤ G₂ := Subgroup.centralizer_le_normalizer _
  have hD₃G : D₃ ≤ G₂ := le_normalizer_conjClosure Z₁ D₃
  have hPC : P ≤ C := pCoreOf_le 2 C
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 C
  have hPG₂ : P ≤ G₂ := hPC.trans hCG₂
  have hEG : E ≤ G₂ := hEC.trans hCG₂
  have hV₂ne : V₂ ≠ ⊥ := fun hb' => hz1 (by
    have := (le_conjClosure Z₁ D₃) hz
    rw [← hV₂def, hb'] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal G₂ :=
    ⟨V₂, hV₂ne, isPGroup_of_isElemAbelian s.isElemAbelian_V₂, rfl⟩
  have hrank : CFSG.Open.pRank 3 G₂ ≤ 2 :=
    pRank_le_two_of_isTwoLocal hh.qtke Nat.prime_three (by norm_num) hloc
  have hD₃C : ∀ e ∈ D₃, e ∈ C → e = 1 := by
    intro e he heC
    by_contra he1
    apply s.hyp.conj_ne h5114 s.card_D₃ s.not_le (s.Z₁_le_Z hz) hz1 he he1
    rw [← Subgroup.mem_centralizer_iff.mp heC z (le_conjClosure Z₁ D₃ hz), mul_assoc,
      mul_inv_cancel, mul_one]
  set P' := P.subgroupOf G₂ with hP'def
  have hP'n : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPG₂).mpr hPG
  set π := QuotientGroup.mk' P' with hπ
  have hπker : ∀ g : ↥G₂, π g = 1 ↔ (g : G) ∈ P := by
    intro g
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hP'def, Subgroup.mem_subgroupOf]
  set D₃' := D₃.subgroupOf G₂ with hD₃'def
  set E' := E.subgroupOf G₂ with hE'def
  set Dbar := D₃'.map π with hDbar
  have hD₃'card : Nat.card D₃' = Nat.card D₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃G).toEquiv
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  have hDbar3 : Nat.card Dbar = 3 := by
    have hinj : Function.Injective (π.comp D₃'.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : ((a : ↥G₂) : G) ∈ P := (hπker a).mp ha
      have h2 : ((a : ↥G₂) : G) = 1 := hD₃C _ (Subgroup.mem_subgroupOf.mp a.2) (hPC h1)
      exact Subtype.ext (Subtype.ext h2)
    have hr : (π.comp D₃'.subtype).range = Dbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card Dbar = Nat.card D₃' := by
      rw [← hr]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h1, hD₃'card, s.card_D₃]
  have hEN : ∀ e : ↥G₂, (e : G) ∈ E → π e ∈ Subgroup.normalizer (Dbar : Set (↥G₂ ⧸ P')) := by
    intro e he
    apply mem_normalizer_of_forall_conj_mem'
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (e : G) * a * (e : G)⁻¹ ∈ P ⊔ D₃ := by
      rw [sup_comm]
      exact (Subgroup.mem_normalizer_iff.mp (hNX e.2) _).mp
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
    have hset : ((P ⊔ D₃ : Subgroup G) : Set G) = (P : Set G) * (D₃ : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hD₃G.trans hPG)
    have h2 : (e : G) * a * (e : G)⁻¹ ∈ (P : Set G) * (D₃ : Set G) := by
      rw [← hset]; exact h1
    obtain ⟨p, hp, d₁, hd₁, hpd⟩ := Set.mem_mul.mp h2
    have hp' : π ⟨p, hPG₂ hp⟩ = 1 := (hπker _).mpr hp
    have heq : e * a * e⁻¹ = (⟨p, hPG₂ hp⟩ : ↥G₂) * ⟨d₁, hD₃G hd₁⟩ :=
      Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
        exact hpd.symm)
    refine ⟨⟨d₁, hD₃G hd₁⟩, Subgroup.mem_subgroupOf.mpr hd₁, ?_⟩
    rw [← map_inv π, ← map_mul π, ← map_mul π, heq, map_mul π, hp', one_mul]
  have hcomm : ∀ e : ↥G₂, (e : G) ∈ E → ∀ a : ↥G₂, (a : G) ∈ D₃ →
      π e * π a = π a * π e := by
    intro e he a ha
    have hodd : Odd (orderOf (π e)) := by
      have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hE3 _ he)
      have h1 : orderOf (π e) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, he3, map_one])
      exact Odd.of_dvd_nat (by decide) h1
    have key := conj_eq_of_odd_of_card_three hDbar3 (hEN e he) hodd
      (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha))
    calc π e * π a = π e * π a * (π e)⁻¹ * π e := by group
      _ = π a * π e := by rw [key]
  have hcomm' : ∀ (a : ↥D₃') (e : ↥E'),
      Commute ((π.comp D₃'.subtype) a) ((π.comp E'.subtype) e) := fun a e =>
    (hcomm e (Subgroup.mem_subgroupOf.mp e.2) a (Subgroup.mem_subgroupOf.mp a.2)).symm
  set f := MonoidHom.noncommCoprod (π.comp D₃'.subtype) (π.comp E'.subtype) hcomm' with hf
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, e⟩ h1
    rw [hf, MonoidHom.noncommCoprod_apply] at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at h1
    rw [← map_mul] at h1
    have h2 : ((a : ↥G₂) : G) * ((e : ↥G₂) : G) ∈ P := (hπker _).mp h1
    have heE : ((e : ↥G₂) : G) ∈ E := Subgroup.mem_subgroupOf.mp e.2
    have haC : ((a : ↥G₂) : G) ∈ C := by
      have := C.mul_mem (hPC h2) (C.inv_mem (hEC heE))
      simpa using this
    have ha1 : ((a : ↥G₂) : G) = 1 := hD₃C _ (Subgroup.mem_subgroupOf.mp a.2) haC
    have he1 : ((e : ↥G₂) : G) = 1 := by
      rw [ha1, one_mul] at h2
      exact eq_one_of_mem_of_pow_three hP2 h2 (hE3 _ heE)
    exact Prod.ext (Subtype.ext (Subtype.ext ha1)) (Subtype.ext (Subtype.ext he1))
  have hzp : Subgroup.zpowers d = D₃ := zpowers_eq_of_card_prime Nat.prime_three s.card_D₃ hd hd1
  have hD₃comm : ∀ a ∈ D₃, ∀ b ∈ D₃, a * b = b * a := by
    intro a ha b hb
    rw [← hzp] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl d).zpow_zpow i j).eq
  have hAcomm : ∀ x y : ↥D₃' × ↥E', x * y = y * x := by
    rintro ⟨a, e⟩ ⟨a', e'⟩
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
    · exact hD₃comm _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp a'.2)
    · exact hEcomm _ (Subgroup.mem_subgroupOf.mp e.2) _ (Subgroup.mem_subgroupOf.mp e'.2)
  have hpow1 : ∀ a : ↥D₃', a ^ 3 = 1 := fun a => Subtype.ext (Subtype.ext (by
    simpa using pow_three_of_mem_of_card_three s.card_D₃ (Subgroup.mem_subgroupOf.mp a.2)))
  have hpow2 : ∀ e : ↥E', e ^ 3 = 1 := fun e => Subtype.ext (Subtype.ext (by
    simpa using hE3 _ (Subgroup.mem_subgroupOf.mp e.2)))
  have hApow : ∀ x : ↥D₃' × ↥E', x ^ 3 = 1 := fun x =>
    Prod.ext (by rw [Prod.pow_fst, hpow1, Prod.fst_one]) (by rw [Prod.pow_snd, hpow2, Prod.snd_one])
  have hAcard : Nat.card (↥D₃' × ↥E') = 3 ^ 3 := by
    rw [Nat.card_prod, hD₃'card, hE'card, s.card_D₃, hE9]
    norm_num
  have h27 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥G₂ ⧸ P')) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hAcomm hApow hAcard f hf_inj le_top
  have hP'card : ¬ 3 ∣ Nat.card P' := by
    intro h3
    have hP'2 : IsPGroup 2 P' := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPG₂).symm
    obtain ⟨m, hm⟩ := hP'2.exists_card_eq
    rw [hm] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hP'card] at h27
  have h3' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥G₂) ≤ CFSG.Open.pRank 3 G₂ := by
    have := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) G₂.subtype
      G₂.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have := h27.trans (h3'.trans hrank)
  omega

theorem not_nine_dvd_card (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h516 : Stmt5_1_16)
    (h521 : Stmt5_1_21) (hnot : ¬ Concl5_1_14_four T L V B D n) :
    ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) with hCdef
  have hCM := s.centralizer_le_normalizer h5114
  have h9' : 3 ^ 2 ∣ Nat.card ↥C := by
    have h2 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h2]
    exact h9
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9'
  have hEC : Q.map C.subtype ≤ C := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hQcomm : ∀ a b : ↥Q, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm
  refine s.not_elemAbelian_nine h5114 hF h521 hnot hEC ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val (hQcomm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : (⟨a, ha⟩ : ↥Q) ^ 3 ^ 2 = 1 := by
      rw [← hQ]
      exact pow_card_eq_one'
    have h2 : ((a : G)) ^ 3 ^ 2 = 1 := by
      simpa using congrArg (fun q : ↥Q => ((q : ↥C) : G)) h1
    exact s.hyp.pow_three_eq_one_of_pow_three_pow h516 (hCM a.2) h2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hQ]
    norm_num

theorem mem_K_of_pow_three_pow (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h521 : Stmt5_1_21) (hnot : ¬ Concl5_1_14_four T L V B D n) {x : G}
    (hxC : x ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ∈ oTwoUpper H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) with hCdef
  set K := oTwoUpper H with hKdef
  have hCM := s.centralizer_le_normalizer h5114
  have hC3 : ∀ y ∈ C, ∀ j : ℕ, y ^ 3 ^ j = 1 → y ^ 3 = 1 := fun y hy j hj =>
    s.hyp.pow_three_eq_one_of_pow_three_pow h516 (hCM hy) hj
  have hBC := s.B_le_centralizer h5114 hF
  have hB3 := s.hyp.card_B_eq_three h510
  obtain ⟨-, -, -, hBK, -⟩ := h510 G T M L H B D n s.hyp.hyp s.hyp.notation59
  have hBK' : B ≤ K := hBK.1.trans inf_le_right
  have h9C := s.not_nine_dvd_card h5114 hF h516 h521 hnot
  have hsyl : ∀ R : Sylow 3 ↥C, Nat.card (R : Subgroup ↥C) ∣ 3 := by
    intro R
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp R.isPGroup'
    have hdvd : 3 ^ j ∣ Nat.card ↥C := by
      rw [← hj]
      exact Subgroup.card_subgroup_dvd_card (R : Subgroup ↥C)
    have hj1 : j ≤ 1 := by
      by_contra hlt
      apply h9C
      have h1 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
      have h2 : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [h2]
      exact h1.trans hdvd
    rw [hj]
    interval_cases j <;> norm_num
  have hx3 : x ^ 3 = 1 := hC3 x hxC k hk
  by_cases hx1 : x = 1
  · rw [hx1]; exact K.one_mem
  set X₁ := Subgroup.zpowers (⟨x, hxC⟩ : ↥C) with hX₁
  set B₁ := B.subgroupOf C with hB₁
  have hX₁card : Nat.card X₁ = 3 := by
    rw [hX₁, Nat.card_zpowers, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hB₁card : Nat.card B₁ = 3 := by
    rw [hB₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hB3]
  have hX₁3 : IsPGroup 3 X₁ := IsPGroup.of_card (hX₁card.trans (pow_one 3).symm)
  have hB₁3 : IsPGroup 3 B₁ := IsPGroup.of_card (hB₁card.trans (pow_one 3).symm)
  obtain ⟨R₁, hR₁⟩ := hX₁3.exists_le_sylow
  obtain ⟨R₂, hR₂⟩ := hB₁3.exists_le_sylow
  have hR₁eq : X₁ = R₁ := Subgroup.eq_of_le_of_card_ge hR₁
    (by rw [hX₁card]; exact Nat.le_of_dvd (by norm_num) (hsyl R₁))
  have hR₂eq : B₁ = R₂ := Subgroup.eq_of_le_of_card_ge hR₂
    (by rw [hB₁card]; exact Nat.le_of_dvd (by norm_num) (hsyl R₂))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C R₂ R₁
  have hxR : (⟨x, hxC⟩ : ↥C) ∈ (R₁ : Subgroup ↥C) := by
    rw [← hR₁eq]; exact Subgroup.mem_zpowers _
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hR₂eq]
    at hxR
  have hb : (c : G)⁻¹ * x * c ∈ B := by
    have := Subgroup.mem_subgroupOf.mp hxR
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using this
  have := (Subgroup.mem_normalizer_iff.mp (hCM c.2) _).mp (hBK' hb)
  simpa [mul_assoc] using this

end Setup521

theorem stmt5_1_22_one_Y_of (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h520 : Stmt5_1_20) (h521 : Stmt5_1_21) : Stmt5_1_22_one_Y := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp hN hV hK h4 hD₃ h3 hZ₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨h, hD₃, h3, (h520 G T M L V H B D n hyp hN hV hK h4 D₃ hD₃ h3).1, hZ₁⟩
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  set K := oTwoUpper H with hKdef
  set Y := oThreePrimeResidual C with hYdef
  have hYC : Y ≤ C := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hYK : Y ≤ K := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxC, j, hj⟩
    exact s.mem_K_of_pow_three_pow h5114 hF h510 h516 h521 h4 hxC hj
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (s.T_le_normalizer_V₂ hF)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYdef, oThreePrimeResidual, Subgroup.le_normalizer_closure_iff]
    rintro t ht g ⟨hg, j, hj⟩
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hTC ht) g).mp hg, j, ?_⟩
    rw [conj_pow, hj, mul_one, mul_inv_cancel]
  have hYTH : Y ⊔ T ≤ H := sup_le (hYK.trans (oTwoUpper_le H)) hyp.hStar.1.1
  have hYTM : Y ⊔ T ≤ M := by
    by_contra hYTM
    have hO : pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
      intro hb
      apply hyp.hStar.1.2
      have hle := CFSG.Quasithin.pCoreOf_le_pCoreOf_of_sylow hYTH hh.sylow.1 le_sup_right
        (hh.isSylowTwoOf hyp.hStar.1.1).2.2
      rw [hb] at hle
      exact le_bot_iff.mp hle
    have heq := hyp.hStar.2.2 (Y ⊔ T) ⟨le_sup_right, hO⟩ hYTH hYTM
    have hKY : K ≤ Y := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxH, hxo⟩
      exact mem_of_odd_of_mem_sup hh.sylow.1 hTY (by rw [heq]; exact hxH) hxo
    exact s.not_le_centralizer h5114 hF h521 h4 (hKY.trans hYC)
  have hBC := s.B_le_centralizer h5114 hF
  intro y hy
  obtain ⟨t, ht, b, hb, rfl⟩ := hyp.exists_mul_eq_of_mem_inf hN
    ⟨hYTM (Subgroup.mem_sup_left hy), hYTH (Subgroup.mem_sup_left hy)⟩
  have htC : t ∈ C := by
    have := C.mul_mem (hYC hy) (C.inv_mem (hBC hb))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ht, htC⟩) (Subgroup.mem_sup_right hb)

end Setting

end CFSG.Quasithin.H13
