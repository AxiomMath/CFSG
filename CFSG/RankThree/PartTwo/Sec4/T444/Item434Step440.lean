module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Core
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Steps434
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

namespace Item434

theorem commute_of_commutator_pow_eq_one {X : Type*} [Group X] {p : ℕ} {r x : X}
    (hr : Nat.Coprime (orderOf r) p) (hz : Commute r (r * x * r⁻¹ * x⁻¹)) {m : ℕ}
    (hzp : (r * x * r⁻¹ * x⁻¹) ^ (p ^ m) = 1) : Commute r x := by
  set z := r * x * r⁻¹ * x⁻¹ with hzdef
  have hrx : r * x * r⁻¹ = z * x := by rw [hzdef]; group
  have key : ∀ n : ℕ, r ^ n * x * (r ^ n)⁻¹ = z ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : r * z ^ n = z ^ n * r := (hz.pow_right n).eq
      calc r ^ (n + 1) * x * (r ^ (n + 1))⁻¹ = r * (r ^ n * x * (r ^ n)⁻¹) * r⁻¹ := by group
        _ = r * (z ^ n * x) * r⁻¹ := by rw [ih]
        _ = (r * z ^ n) * x * r⁻¹ := by group
        _ = (z ^ n * r) * x * r⁻¹ := by rw [hc]
        _ = z ^ n * (r * x * r⁻¹) := by group
        _ = z ^ (n + 1) * x := by rw [hrx, pow_succ]; group
  have h1 := key (orderOf r)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hzn : z ^ orderOf r = 1 := by
    have h2 : z ^ orderOf r * x * x⁻¹ = x * x⁻¹ := by rw [← h1]
    simpa using h2
  have hd : orderOf z ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m hr)]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn) (orderOf_dvd_of_pow_eq_one hzp)
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have h3 : r * x * r⁻¹ * x⁻¹ = 1 := hz1
  calc r * x = (r * x * r⁻¹ * x⁻¹) * x * r := by group
    _ = x * r := by rw [h3, one_mul]

theorem coprime_orderOf_of_mem {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : ¬ 3 ∣ Nat.card N) {x : X} (hx : x ∈ N) : Nat.Coprime (orderOf x) 3 := by
  refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => ?_))
  exact hN (h3.trans (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _))

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem inf_centralizer_pCore_le (h : Ctx434Core G A M Q) :
    Subgroup.centralizer (layer G : Set G) ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤
      CFSG.pCore 3 G := by
  set C := Subgroup.centralizer (layer G : Set G) with hC
  intro x hx
  have hF := h.rank3II_4_36
  have hmem : (⟨x, hx.1⟩ : C) ∈ Subgroup.centralizer (generalizedFitting C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyP : (y : G) ∈ CFSG.pCore 3 G := by
      rw [← hF]
      exact ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hx.2 y hyP
  have hx' := CFSG.centralizer_generalizedFitting_le C hmem
  rw [← hF]
  exact ⟨_, hx', rfl⟩

theorem commutator_pCore_eq_bot (h : Ctx434Core G A M Q) : ⁅CFSG.pCore 3 G, Q⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hPtop : Subgroup.normalizer (CFSG.pCore 3 G : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (CFSG.pCore 3 G)
  exact Sec5.rank3II_3_7 G 3 Nat.prime_three (by norm_num) A Q (CFSG.pCore 3 G) h.isE27.1 hQ3 hAQ
    CFSG.pCore_isPGroup (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
    fun y hy hy3 => h.rank3II_4_35 hy.2 hy3

theorem inf_centralizer_layer_eq_bot (h : Ctx434Core G A M Q) :
    Q ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hQ3, -⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hPQ : CFSG.pCore 3 G ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_pCore_eq_bot h)
  have hle : Q ⊓ Subgroup.centralizer (layer G : Set G) ≤ CFSG.pCore 3 G := by
    intro x hx
    refine inf_centralizer_pCore_le h (Subgroup.mem_inf.mpr ⟨hx.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hPQ hy) x hx.1).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := G))
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card (CFSG.pCore 3 G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ3))
  have hdisj := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [eq_bot_iff, ← hdisj]
  exact le_inf inf_le_left hle

theorem exists_inf_centralizer_ne_bot (h : Ctx434Core G A M Q) :
    ∃ a ∈ A, a ∉ Subgroup.centralizer (layer G : Set G) ∧
      Q ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  by_contra hall
  push Not at hall
  apply h.ne_bot
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three h.isE27.1
    (by rw [h.isE27.2]; norm_num) hAQ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ3)
    fun H hHA hH9 => ?_
  have hex : ∃ b ∈ H, b ∉ Subgroup.centralizer (layer G : Set G) := by
    by_contra hno
    push Not at hno
    have hle : H ≤ A ⊓ Subgroup.centralizer (layer G : Set G) := le_inf hHA hno
    have h9 : 9 ≤ 3 := by
      calc 9 = Nat.card H := by rw [hH9]; norm_num
        _ ≤ Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) :=
          Subgroup.card_le_of_le hle
        _ ≤ 3 := h.card_inf_centralizer_layer_le
    omega
  obtain ⟨b, hbH, hbC⟩ := hex
  rw [← hall b (hHA hbH) hbC]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbH))

theorem le_centralizer_centralizer_layer (h : Ctx434Core G A M Q) {R : Subgroup G} (hRQ : R ≤ Q) :
    R ≤ Subgroup.centralizer (Subgroup.centralizer (layer G : Set G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (layer G).Characteristic := layer_characteristic
  set C := Subgroup.centralizer (layer G : Set G) with hC
  set P := CFSG.pCore 3 G with hP
  obtain ⟨-, hQ3, -⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hPQ := commutator_pCore_eq_bot h
  have hPR : ⁅P, R⁆ = ⊥ := by
    rw [eq_bot_iff, ← hPQ]
    exact Subgroup.commutator_mono le_rfl hRQ
  have h3 : ⁅⁅R, C⁆, P⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [eq_bot_iff, ← hPR]
      exact Subgroup.commutator_mono (Subgroup.commutator_le_right C P) le_rfl
    · rw [hPR, Subgroup.commutator_bot_left]
  have hRCP : ⁅R, C⁆ ≤ P := by
    intro z hz
    refine inf_centralizer_pCore_le h
      (Subgroup.mem_inf.mpr ⟨Subgroup.commutator_le_right R C hz, ?_⟩)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hz
  have hRP : R ≤ Subgroup.centralizer (P : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm, hPR]
  rw [Subgroup.le_centralizer_iff]
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hzP : r * c * r⁻¹ * c⁻¹ ∈ P := hRCP (Subgroup.commutator_mem_commutator hr hc)
  have hcomm : Commute r (r * c * r⁻¹ * c⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (hRP hr) _ hzP).symm
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 3) (G := G)) ⟨_, hzP⟩
  have hm' : (r * c * r⁻¹ * c⁻¹) ^ (3 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  exact (commute_of_commutator_pow_eq_one (coprime_orderOf_of_mem hQ3 (hRQ hr)) hcomm hm').eq

theorem pRank_le_of_sylow_le {H M : Subgroup G} (P : Sylow 3 H) (hPM : (P : Subgroup H).map
    H.subtype ≤ M) : CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 M := by
  have h1 : CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
    rw [← CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three H H le_rfl,
      Subgroup.subgroupOf_self]
  have h2 := pRank_top_le_of_sylow_le (P := P) (M := (P : Subgroup H)) le_rfl
  have h3 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3 Nat.prime_three
    H.subtype H.subtype_injective (P : Subgroup H)
  have h4 := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three hPM
  omega

theorem zpowers_eq_omegaOneCenterThree_aux (h : Ctx434Core G A M Q) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {Ca : Subgroup G} (hCa : ∀ x : G, x ∈ Ca ↔ x * a = a * x)
    (h3 : 3 < CFSG.Open.pRank 3 Ca) (P : Sylow 3 Ca) :
    Subgroup.zpowers a = omegaOneCenterThree ((P : Subgroup Ca).map Ca.subtype) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup G, P' = (P : Subgroup Ca).map Ca.subtype := ⟨_, rfl⟩
  rw [← hP']
  have haC : a ∈ Ca := (hCa a).mpr rfl
  have ha3 : a ^ 3 = 1 := h.isE27.1.2 a ha
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hACa : A ≤ Ca := fun x hx => (hCa x).mpr (hAc x hx a ha)
  have haP' : a ∈ P' := by
    have hnorm : (Subgroup.zpowers (⟨a, haC⟩ : Ca)).Normal := by
      refine Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hCa y).mp y.2
    have hpg : IsPGroup 3 (Subgroup.zpowers (⟨a, haC⟩ : Ca)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        have : (⟨a, haC⟩ : Ca) ^ 3 = 1 := Subtype.ext ha3
        refine orderOf_eq_prime this ?_
        intro h1
        exact ha1 (congrArg Subtype.val h1))
    rw [hP']
    exact ⟨⟨a, haC⟩, hpg.le_sylow_of_normal P (Subgroup.mem_zpowers _), rfl⟩
  have hP'Ca : P' ≤ Ca := hP' ▸ Subgroup.map_subtype_le _
  have haZ : a ∈ Subgroup.centralizer (P' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hCa y).mp (hP'Ca hy)
  have haW : Subgroup.zpowers a ≤ omegaOneCenterThree P' :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨haP', haZ, ha3⟩)
  refine le_antisymm haW ?_
  by_contra hW
  obtain ⟨P₁, hAP₁⟩ := (h.isE27.isPGroup.comap_subtype (K := Ca)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Ca P₁ P
  obtain ⟨P₁', hP₁'⟩ : ∃ P₁' : Subgroup G, P₁' = (P₁ : Subgroup Ca).map Ca.subtype := ⟨_, rfl⟩
  have hAP₁' : A ≤ P₁' := fun x hx => hP₁' ▸ ⟨⟨x, hACa hx⟩, hAP₁ hx, rfl⟩
  have hmemP' : ∀ x : G, x ∈ P₁' → (c : G) * x * (c : G)⁻¹ ∈ P' := by
    intro x hx
    rw [hP₁'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hP']
    refine ⟨c * y * c⁻¹, ?_, rfl⟩
    rw [← hc]
    change c * y * c⁻¹ ∈ ((c • P₁ : Sylow 3 Ca) : Set Ca)
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
    simpa [mul_assoc] using hy
  set φ : G →* G := (MulAut.conj ((c : G)⁻¹)).toMonoidHom with hφ
  have hφapp : ∀ x, φ x = (c : G)⁻¹ * x * c := fun x => by
    simp [hφ]
  have hgen : ∀ x : G, x ∈ P' → x ∈ Subgroup.centralizer (P' : Set G) → x ^ 3 = 1 →
      φ x ∈ A ∧ φ x ∈ Subgroup.centralizer (P₁' : Set G) := by
    intro x hxP hxC hx3
    have hcent : φ x ∈ Subgroup.centralizer (P₁' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.mp hxC _ (hmemP' y hy)
      rw [hφapp]
      calc y * ((c : G)⁻¹ * x * c) = (c : G)⁻¹ * ((c * y * (c : G)⁻¹) * x) * c := by group
        _ = (c : G)⁻¹ * (x * (c * y * (c : G)⁻¹)) * c := by rw [h1]
        _ = (c : G)⁻¹ * x * c * y := by group
    refine ⟨h.rank3II_4_35 ?_ ?_, hcent⟩
    · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP₁') hcent
    · rw [← map_pow, hx3, map_one]
  set W := omegaOneCenterThree P' with hWdef
  set W₁ := W.map φ with hW₁
  have hW₁gen : W₁ = Subgroup.closure (φ '' {x | x ∈ P' ∧
      x ∈ Subgroup.centralizer (P' : Set G) ∧ x ^ 3 = 1}) := by
    rw [hW₁, hWdef, omegaOneCenterThree, MonoidHom.map_closure]
  have hW₁A : W₁ ≤ A := by
    rw [hW₁gen, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxP, hxC, hx3⟩, rfl⟩
    exact (hgen x hxP hxC hx3).1
  have hW₁C : W₁ ≤ Subgroup.centralizer (P₁' : Set G) := by
    rw [hW₁gen, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxP, hxC, hx3⟩, rfl⟩
    exact (hgen x hxP hxC hx3).2
  have hlt : Subgroup.zpowers a < W := lt_of_le_of_ne haW (fun heq => hW (heq ▸ le_rfl))
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hW₁e : CFSG.Assembly.IsElemAbelian 3 W₁ := Source.isElemAbelian_of_le h.isE27.1 hW₁A
  have hW₁card : Nat.card W₁ = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj ((c : G)⁻¹)).injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.isE27.isPGroup.to_le hW₁A)
  have hk2 : 2 ≤ k := by
    have h1 : 3 < Nat.card W := by
      have := Subgroup.card_lt_of_lt hlt
      omega
    by_contra hk2
    push Not at hk2
    interval_cases k <;> omega
  have hW₁2 : 2 ≤ CFSG.Open.pRank 3 W₁ :=
    hk2.trans (le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
      Nat.prime_three W₁) ⟨W₁, le_rfl, hW₁e, hk⟩)
  have hP₁M : P₁' ≤ M := by
    have hP₁W : P₁' ≤ Subgroup.centralizer (W₁ : Set G) := Subgroup.le_centralizer_iff.mp hW₁C
    exact hP₁W.trans ((Subgroup.centralizer_le_normalizer _).trans
      ((normalizer_le_gamma hW₁A hW₁2).trans h.gamma_le))
  have := pRank_le_of_sylow_le P₁ (hP₁' ▸ hP₁M)
  rw [h.pRank_eq] at this
  omega

theorem zpowers_eq_omegaOneCenterThree (h : Ctx434Core G A M Q) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (h3 : 3 < CFSG.Open.pRank 3 (Subgroup.centralizer {a}))
    (P : Sylow 3 (Subgroup.centralizer {a})) :
    Subgroup.zpowers a =
      omegaOneCenterThree ((P : Subgroup (Subgroup.centralizer {a})).map
        (Subgroup.centralizer {a}).subtype) :=
  zpowers_eq_omegaOneCenterThree_aux h ha ha1 (fun _ => Subgroup.mem_centralizer_singleton_iff)
    h3 P

end Item434

namespace Ctx434Core

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem rank3II_4_40 (h : Ctx434Core G A M Q) :
    haveI : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic;
    ∃ a ∈ A, a ∉ Subgroup.centralizer (layer G : Set G) ∧
      (∃ X ∈ invariantPiSubgroups
          (Subgroup.centralizer
            {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a})
          (A.map (QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)))) (piCompl 3),
        X ≠ ⊥) ∧
      inSubgroup generalizedFitting (Subgroup.centralizer
          {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a}) ≠
        inSubgroup (CFSG.pCore 3) (Subgroup.centralizer
          {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a}) ∧
      (3 < CFSG.Open.pRank 3 (Subgroup.centralizer {a}) →
        ∀ P : Sylow 3 (Subgroup.centralizer {a}),
          Subgroup.zpowers a =
            omegaOneCenterThree ((P : Subgroup (Subgroup.centralizer {a})).map
              (Subgroup.centralizer {a}).subtype)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (layer G).Characteristic := layer_characteristic
  set C := Subgroup.centralizer (layer G : Set G) with hC
  set π := QuotientGroup.mk' C with hπ
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  obtain ⟨a, ha, haC, hR⟩ := Item434.exists_inf_centralizer_ne_bot h
  have ha1 : a ≠ 1 := fun h1 => haC (h1 ▸ Subgroup.one_mem _)
  set R := Q ⊓ Subgroup.centralizer ({a} : Set G) with hRdef
  have hRQ : R ≤ Q := inf_le_left
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le hRQ))
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    have hxCa : x ∈ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a ha))
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hAQ hx, hxCa⟩)
  have hRC : R ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← Item434.inf_centralizer_layer_eq_bot h]
    exact inf_le_inf_right _ hRQ
  have hRstar : R.map π ≠ ⊥ := by
    intro hbot
    apply hR
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    rw [eq_bot_iff, ← hRC]
    exact le_inf le_rfl hbot
  set Cstar := Subgroup.centralizer ({π a} : Set (G ⧸ C)) with hCstar
  have hRCstar : R.map π ≤ Cstar := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hr.2]
  have hACstar : A.map π ≤ Cstar := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hAc a ha x hx]
  refine ⟨a, ha, haC, ⟨R.map π, ⟨hRCstar, ?_, ?_⟩, hRstar⟩, ?_, fun h3 P =>
    Item434.zpowers_eq_omegaOneCenterThree h ha ha1 h3 P⟩
  ·
    rw [isPiSubgroup_piCompl_iff Nat.prime_three]
    exact fun h3 => hR3 (h3.trans (Subgroup.card_map_dvd R π))
  ·
    exact (Subgroup.map_mono hAR).trans (Subgroup.le_normalizer_map π)
  ·
    intro heq
    set Kst := inSubgroup (CFSG.pCore 3) Cstar with hKst
    have hKp : IsPGroup 3 Kst := (CFSG.pCore_isPGroup (p := 3) (G := Cstar)).map _
    have hKn : ∀ x ∈ Cstar, ∀ k ∈ Kst, x * k * x⁻¹ ∈ Kst := by
      rintro x hx _ ⟨k, hk, rfl⟩
      refine ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, ?_, rfl⟩
      exact (CFSG.pCore_normal (p := 3) (G := Cstar)).conj_mem k hk _
    have hKcent : ∀ y ∈ Cstar, (∀ k ∈ Kst, y * k = k * y) → y ∈ Kst := by
      intro y hy hyk
      have hmem : (⟨y, hy⟩ : Cstar) ∈
          Subgroup.centralizer (generalizedFitting Cstar : Set Cstar) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        apply Subtype.ext
        have hzK : (z : G ⧸ C) ∈ Kst := by
          rw [← heq]
          exact ⟨z, hz, rfl⟩
        exact (hyk _ hzK).symm
      have h' := CFSG.centralizer_generalizedFitting_le Cstar hmem
      rw [← heq]
      exact ⟨_, h', rfl⟩
    set D := Subgroup.centralizer (C : Set G) with hD
    have hDn : D.Normal := Subgroup.normal_centralizer
    have hRD : R ≤ D := Item434.le_centralizer_centralizer_layer h hRQ
    set K₀ := D ⊓ Kst.comap π with hK₀
    have hK₀p : IsPGroup 3 K₀ := by
      rintro ⟨x, hxD, hxK⟩
      obtain ⟨m, hm⟩ := hKp ⟨π x, hxK⟩
      have hm' : π (x ^ (3 ^ m)) = 1 := by
        have := congrArg Subtype.val hm
        simpa [map_pow] using this
      have hxC : x ^ (3 ^ m) ∈ C := by
        rw [← QuotientGroup.ker_mk' C, MonoidHom.mem_ker]
        exact hm'
      have hxD' : x ^ (3 ^ m) ∈ D := pow_mem hxD _
      have hxP : x ^ (3 ^ m) ∈ CFSG.pCore 3 G := by
        refine Item434.inf_centralizer_pCore_le h (Subgroup.mem_inf.mpr ⟨hxC, ?_⟩)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_iff.mp hxD' y (pCore_three_le_centralizer_layer hy)
      obtain ⟨m', hm''⟩ := (CFSG.pCore_isPGroup (p := 3) (G := G)) ⟨_, hxP⟩
      refine ⟨m + m', Subtype.ext ?_⟩
      have := congrArg Subtype.val hm''
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul, this]
    have hNK₀ : ∀ x : G, π x ∈ Cstar → x ∈ Subgroup.normalizer (K₀ : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyD, hyK⟩
        refine ⟨hDn.conj_mem y hyD x, ?_⟩
        show π (x * y * x⁻¹) ∈ Kst
        rw [map_mul, map_mul, map_inv]
        exact hKn _ hx _ hyK
      · rintro ⟨hyD, hyK⟩
        refine ⟨?_, ?_⟩
        · have := hDn.conj_mem _ hyD x⁻¹
          simpa [mul_assoc] using this
        · have hyK' : π (x * y * x⁻¹) ∈ Kst := hyK
          have hxinv : π x⁻¹ ∈ Cstar := by rw [map_inv]; exact inv_mem hx
          have := hKn _ hxinv _ hyK'
          simpa [map_mul, map_inv, mul_assoc] using this
    have hAK₀ : A ≤ Subgroup.normalizer (K₀ : Set G) := fun x hx =>
      hNK₀ x (hACstar ⟨x, hx, rfl⟩)
    have hRK₀ : R ≤ Subgroup.normalizer (K₀ : Set G) := fun x hx =>
      hNK₀ x (hRCstar ⟨x, hx, rfl⟩)
    have hB : ⁅K₀, R⁆ = ⊥ :=
      Sec5.rank3II_3_7 G 3 Nat.prime_three (by norm_num) A R K₀ h.isE27.1 hR3 hAR hK₀p hAK₀
        hRK₀ fun y hy hy3 => h.rank3II_4_35 hy.2 hy3
    have hK₀R : K₀ ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hB
    have hcomm : ∀ r ∈ R, ∀ k : G, π k ∈ Kst → r * k = k * r := by
      intro r hr k hk
      have hrD : r ∈ D := hRD hr
      have hw : r * k * r⁻¹ * k⁻¹ ∈ K₀ := by
        refine ⟨?_, ?_⟩
        · have h1 : k * r⁻¹ * k⁻¹ ∈ D := hDn.conj_mem _ (inv_mem hrD) k
          have := D.mul_mem hrD h1
          simpa [mul_assoc] using this
        · show π (r * k * r⁻¹ * k⁻¹) ∈ Kst
          have hrC : π r ∈ Cstar := hRCstar ⟨r, hr, rfl⟩
          have h1 := hKn _ hrC _ hk
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          exact Kst.mul_mem h1 (inv_mem hk)
      have hwr : Commute r (r * k * r⁻¹ * k⁻¹) :=
        Subgroup.mem_centralizer_iff.mp (hK₀R hw) r hr
      obtain ⟨m, hm⟩ := hK₀p ⟨_, hw⟩
      have hm' : (r * k * r⁻¹ * k⁻¹) ^ (3 ^ m) = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      exact (Item434.commute_of_commutator_pow_eq_one
        (Item434.coprime_orderOf_of_mem hQ3 (hRQ hr)) hwr hm').eq
    apply hRstar
    rw [eq_bot_iff]
    rintro _ ⟨r, hr, rfl⟩
    have hrK : π r ∈ Kst := by
      refine hKcent _ (hRCstar ⟨r, hr, rfl⟩) fun k hk => ?_
      obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective C k
      rw [← map_mul, ← map_mul, hcomm r hr k' hk]
    obtain ⟨m, hm⟩ := hKp ⟨_, hrK⟩
    have hm' : (π r) ^ (3 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hco : Nat.Coprime (orderOf (π r)) 3 :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd π r)
        (Item434.coprime_orderOf_of_mem hQ3 (hRQ hr))
    have hd : orderOf (π r) ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m hco)]
      exact Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hm')
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end Ctx434Core

theorem rank3II_4_40 : Item4_40 := fun _ _ _ _ _ _ h => h.toCore.rank3II_4_40

end CFSG.RankThree.PartTwo.Sec4
