module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFacts2
public import CFSG.RankThree.GF2n.Smith81.OrthE1Small
public import CFSG.RankThree.GF2n.Smith81.ERecursion
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.Walter.Statement

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

namespace CaseA3

theorem prod_normal_factor {A B : Type} [Group A] [Group B] [IsSimpleGroup A] [IsSimpleGroup B]
    (hA : Subgroup.center A = ⊥) (hB : Subgroup.center B = ⊥)
    (N : Subgroup (A × B)) [N.Normal] (hN : N ≠ ⊥) :
    Subgroup.prod ⊤ ⊥ ≤ N ∨ Subgroup.prod ⊥ ⊤ ≤ N := by
  classical
  have hNc : ∀ n ∈ N, ∀ g : A × B, g * n * g⁻¹ ∈ N := fun n hn g =>
    Subgroup.Normal.conj_mem ‹N.Normal› n hn g
  let NA : Subgroup A := N.comap (MonoidHom.inl A B)
  let NB : Subgroup B := N.comap (MonoidHom.inr A B)
  haveI hNA : NA.Normal := ⟨fun n hn g => by
    have h := hNc ((MonoidHom.inl A B) n) hn ((MonoidHom.inl A B) g)
    simpa [NA, Subgroup.mem_comap, map_mul, map_inv] using h⟩
  haveI hNB : NB.Normal := ⟨fun n hn g => by
    have h := hNc ((MonoidHom.inr A B) n) hn ((MonoidHom.inr A B) g)
    simpa [NB, Subgroup.mem_comap, map_mul, map_inv] using h⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal NA with hA0 | hA1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal NB with hB0 | hB1
    · exfalso
      obtain ⟨⟨⟨a, b⟩, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
      have hca : ∀ x : A, ⁅a, x⁆ = 1 := by
        intro x
        have h1 := N.mul_mem hf (hNc _ (N.inv_mem hf) ((x, 1) : A × B))
        have h2 : ((⁅a, x⁆, (1 : B)) : A × B) ∈ N := by
          convert h1 using 1
          ext <;> simp [commutatorElement_def, mul_assoc]
        have h3 : ⁅a, x⁆ ∈ NA := h2
        rw [hA0, Subgroup.mem_bot] at h3
        exact h3
      have hac : a ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun g =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hca g)).symm
      rw [hA, Subgroup.mem_bot] at hac
      have hcb : ∀ y : B, ⁅b, y⁆ = 1 := by
        intro y
        have h1 := N.mul_mem hf (hNc _ (N.inv_mem hf) ((1, y) : A × B))
        have h2 : (((1 : A), ⁅b, y⁆) : A × B) ∈ N := by
          convert h1 using 1
          ext <;> simp [commutatorElement_def, mul_assoc]
        have h3 : ⁅b, y⁆ ∈ NB := h2
        rw [hB0, Subgroup.mem_bot] at h3
        exact h3
      have hbc : b ∈ Subgroup.center B := Subgroup.mem_center_iff.mpr fun g =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hcb g)).symm
      rw [hB, Subgroup.mem_bot] at hbc
      exact hf1 (Subtype.ext (by simp [hac, hbc]))
    · right
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
      rw [Subgroup.mem_bot] at ha
      subst ha
      have hbNB : b ∈ NB := by rw [hB1]; exact Subgroup.mem_top b
      exact hbNB
  · left
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
    rw [Subgroup.mem_bot] at hb
    subst hb
    have haNA : a ∈ NA := by rw [hA1]; exact Subgroup.mem_top a
    exact haNA

theorem omega_normal_two_charP_of_dvd (K : Type) [Field K] [Finite K] (h : 2 ∣ Nat.card K) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have h2 : 2 ∣ ringChar K := by
    rw [Nat.card_eq_fintype_card, hn] at h
    exact Nat.prime_two.dvd_of_dvd_pow h
  have h2' : ringChar K = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  exact ringChar.eq_iff.mp h2'

theorem omega_normal_two_card_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, Nat.card K = 2 ^ f := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem omega_normal_two_isPGroup_of_mulEquiv {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (hG : IsPGroup p G) : IsPGroup p H := by
  intro h
  obtain ⟨k, hk⟩ := hG (f.symm h)
  refine ⟨k, ?_⟩
  have := congrArg f hk
  rw [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  exact this

theorem omega_normal_two_isPGroup_of_le {p : ℕ} {G : Type} [Group G] {N S : Subgroup G}
    (hN : IsPGroup p N) (hS : S ≤ N) : IsPGroup p S := by
  intro g
  obtain ⟨k, hk⟩ := hN ⟨g.1, hS g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem omega_normal_two_not_isPGroup {A : Type} [Group A] [Finite A] [Nontrivial A]
    (hA : Subgroup.center A = ⊥) : ¬ IsPGroup 2 A := by
  intro h
  have hnt := h.center_nontrivial
  rw [hA] at hnt
  obtain ⟨x, y, hxy⟩ := hnt
  exact hxy (Subtype.ext ((Subgroup.mem_bot.mp x.2).trans (Subgroup.mem_bot.mp y.2).symm))

theorem omega_normal_two_finite_sl2 (K : Type) [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    Finite ↥(StatedSL 2 K) := by
  apply Nat.finite_of_card_ne_zero
  rw [CFSG.Open.StatedAPI.card_statedSL_two]
  have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem omega_normal_two_sylow_sl2 (F : Type) [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) :
    ∃ H : Subgroup ↥(StatedSL 2 F), IsPGroup 2 H ∧ Nat.card H = Nat.card F := by
  haveI := omega_normal_two_finite_sl2 F h4
  obtain ⟨f, hf⟩ := omega_normal_two_card_two_pow F
  obtain ⟨H, hH⟩ : ∃ H : Subgroup ↥(StatedSL 2 F), Nat.card H = 2 ^ f := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [CFSG.Open.StatedAPI.card_statedSL_two, hf]
    exact dvd_mul_right _ _
  exact ⟨H, IsPGroup.iff_card.mpr ⟨f, hH⟩, hH.trans hf.symm⟩

theorem omega_normal_two_gamma_plus (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (N : Subgroup (↥(StatedSL 2 K) × ↥(StatedSL 2 K))) [N.Normal] :
    (IsPGroup 2 N → N = ⊥) ∧
      (N ≠ ⊥ → ∃ U : Subgroup (↥(StatedSL 2 K) × ↥(StatedSL 2 K)),
        U ≤ N ∧ IsPGroup 2 U ∧ Nat.card K ≤ Nat.card U) := by
  haveI hQ : CFSG.IsQuasisimple ↥(StatedSL 2 K) := statedSL_quasisimple_of_card 2 K le_rfl h4
  haveI hS : IsSimpleGroup ↥(StatedSL 2 K) := isSimpleGroup_statedSL_two hQ
  haveI := omega_normal_two_finite_sl2 K h4
  have hcen : Subgroup.center ↥(StatedSL 2 K) = ⊥ := center_statedSL_two_eq_bot
  obtain ⟨H, hH2, hHc⟩ := omega_normal_two_sylow_sl2 K h4
  constructor
  · intro hP
    by_contra hne
    rcases prod_normal_factor hcen hcen N hne with h | h
    · obtain ⟨φ⟩ := exists_equiv_top_bot ↥(StatedSL 2 K) ↥(StatedSL 2 K)
      exact omega_normal_two_not_isPGroup hcen
        (omega_normal_two_isPGroup_of_mulEquiv φ (omega_normal_two_isPGroup_of_le hP h))
    · obtain ⟨φ⟩ := exists_equiv_bot_top ↥(StatedSL 2 K) ↥(StatedSL 2 K)
      exact omega_normal_two_not_isPGroup hcen
        (omega_normal_two_isPGroup_of_mulEquiv φ (omega_normal_two_isPGroup_of_le hP h))
  · intro hN
    rcases prod_normal_factor hcen hcen N hN with h | h
    · have hinj : Function.Injective (MonoidHom.inl ↥(StatedSL 2 K) ↥(StatedSL 2 K)) :=
        fun a b hab => congrArg Prod.fst hab
      refine ⟨H.map (MonoidHom.inl ↥(StatedSL 2 K) ↥(StatedSL 2 K)), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact h (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top y, Subgroup.mem_bot.mpr rfl⟩)
      · exact omega_normal_two_isPGroup_of_mulEquiv (Subgroup.equivMapOfInjective H _ hinj) hH2
      · have hc : Nat.card (H.map (MonoidHom.inl ↥(StatedSL 2 K) ↥(StatedSL 2 K))) =
            Nat.card H := Subgroup.card_map_of_injective hinj
        exact (hc.trans hHc).ge
    · have hinj : Function.Injective (MonoidHom.inr ↥(StatedSL 2 K) ↥(StatedSL 2 K)) :=
        fun a b hab => congrArg Prod.snd hab
      refine ⟨H.map (MonoidHom.inr ↥(StatedSL 2 K) ↥(StatedSL 2 K)), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact h (Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top y⟩)
      · exact omega_normal_two_isPGroup_of_mulEquiv (Subgroup.equivMapOfInjective H _ hinj) hH2
      · have hc : Nat.card (H.map (MonoidHom.inr ↥(StatedSL 2 K) ↥(StatedSL 2 K))) =
            Nat.card H := Subgroup.card_map_of_injective hinj
        exact (hc.trans hHc).ge

theorem omega_normal_two_gamma_minus (F : Type) [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) (N : Subgroup ↥(StatedSL 2 F)) [N.Normal] :
    (IsPGroup 2 N → N = ⊥) ∧
      (N ≠ ⊥ → ∃ U : Subgroup ↥(StatedSL 2 F), U ≤ N ∧ IsPGroup 2 U ∧
        Nat.card F ≤ Nat.card U) := by
  haveI hQ : CFSG.IsQuasisimple ↥(StatedSL 2 F) := statedSL_quasisimple_of_card 2 F le_rfl h4
  haveI hS : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL_two hQ
  haveI := omega_normal_two_finite_sl2 F h4
  have hcen : Subgroup.center ↥(StatedSL 2 F) = ⊥ := center_statedSL_two_eq_bot
  obtain ⟨H, hH2, hHc⟩ := omega_normal_two_sylow_sl2 F h4
  constructor
  · intro hP
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      subst h
      exact omega_normal_two_not_isPGroup hcen
        (omega_normal_two_isPGroup_of_mulEquiv Subgroup.topEquiv hP)
  · intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hN
    · refine ⟨H, ?_, hH2, hHc.ge⟩
      rw [h]
      exact le_top

theorem omega_normal_two_transfer {q : ℕ} {W Γ : Type} [Group W] [Group Γ] (e : W ≃* Γ)
    (h : ∀ N' : Subgroup Γ, N'.Normal → (IsPGroup 2 N' → N' = ⊥) ∧
      (N' ≠ ⊥ → ∃ U' : Subgroup Γ, U' ≤ N' ∧ IsPGroup 2 U' ∧ q ≤ Nat.card U'))
    (N : Subgroup W) [N.Normal] :
    (IsPGroup 2 N → N = ⊥) ∧
      (N ≠ ⊥ → ∃ U : Subgroup W, U ≤ N ∧ IsPGroup 2 U ∧ q ≤ Nat.card U) := by
  haveI hN' : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹N.Normal› e.toMonoidHom e.surjective
  constructor
  · intro hP
    have hP' : IsPGroup 2 ↥(N.map e.toMonoidHom) :=
      omega_normal_two_isPGroup_of_mulEquiv
        (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective) hP
    exact (Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).mp
      ((h _ hN').1 hP')
  · intro hN
    have hN0 : N.map e.toMonoidHom ≠ ⊥ := fun h0 =>
      hN ((Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).mp h0)
    obtain ⟨U', hU'N, hU'2, hU'q⟩ := (h _ hN').2 hN0
    refine ⟨U'.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp (hU'N hy)
      simpa using hn
    · exact omega_normal_two_isPGroup_of_mulEquiv
        (Subgroup.equivMapOfInjective U' e.symm.toMonoidHom e.symm.injective) hU'2
    · rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
      exact hU'q

theorem omega_normal_two {q : ℕ} (hq : 4 ≤ q) (hq2 : 2 ∣ q) {W : Type} [Group W]
    (hW : IsOmegaPlus 2 q W ∨ IsOmegaMinus 2 q W) (N : Subgroup W) [N.Normal] :
    (IsPGroup 2 N → N = ⊥) ∧
      (N ≠ ⊥ → ∃ U : Subgroup W, U ≤ N ∧ IsPGroup 2 U ∧ q ≤ Nat.card U) := by
  rcases hW with ⟨K, hK, hKfin, hKq, ⟨e⟩⟩ | ⟨K, hK, hKfin, hKq, b, c, hirr, ⟨e⟩⟩
  · subst hKq
    haveI : CharP K 2 := omega_normal_two_charP_of_dvd K hq2
    obtain ⟨eΓ⟩ := statedOmega_plus_four_nonempty_equiv K hq
    exact omega_normal_two_transfer (e.trans eΓ)
      (fun N' hN' => omega_normal_two_gamma_plus K hq N') N
  · subst hKq
    haveI : CharP K 2 := omega_normal_two_charP_of_dvd K hq2
    obtain ⟨F, hF, hFfin, hFcard, ⟨eF⟩⟩ := exists_statedOmega_quadMinus_two_mulEquiv hirr
    have h2F : 2 ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow hq2 two_ne_zero
    haveI : CharP F 2 := omega_normal_two_charP_of_dvd F h2F
    have hqF : Nat.card K ≤ Nat.card F := by
      rw [hFcard]
      nlinarith
    have h4F : 4 ≤ Nat.card F := le_trans hq hqF
    refine omega_normal_two_transfer (e.trans eF) (fun N' hN' => ?_) N
    obtain ⟨h1, h2⟩ := omega_normal_two_gamma_minus F h4F N'
    refine ⟨h1, fun hne => ?_⟩
    obtain ⟨U, hU, hU2, hUc⟩ := h2 hne
    exact ⟨U, hU, hU2, le_trans hqF hUc⟩

theorem card_bar_mul {G : Type} [Group G] [Finite G] {X Q T : Subgroup G}
    [(Q.subgroupOf X).Normal] (hQT : Q ≤ T) (hTX : T ≤ X) :
    Nat.card (bar X Q T) * Nat.card Q = Nat.card T := by
  have hQX : Q ≤ X := hQT.trans hTX
  have hgr : ((QuotientGroup.mk' (Q.subgroupOf X)).comp (T.subgroupOf X).subtype).range
      = bar X Q T := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hinj : Function.Injective (X.subtype.comp (T.subgroupOf X).subtype) :=
    X.subtype_injective.comp (T.subgroupOf X).subtype_injective
  have hgk : (((QuotientGroup.mk' (Q.subgroupOf X)).comp (T.subgroupOf X).subtype).ker).map
      (X.subtype.comp (T.subgroupOf X).subtype) = Q := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : QuotientGroup.mk' (Q.subgroupOf X) k.1 = 1 := MonoidHom.mem_ker.mp hk
      have h3 : k.1 ∈ Q.subgroupOf X :=
        (QuotientGroup.eq_one_iff (N := Q.subgroupOf X) k.1).mp h1
      exact Subgroup.mem_subgroupOf.mp h3
    · intro hx
      have hxX : x ∈ X := hQX hx
      have hxS : (⟨x, hxX⟩ : X) ∈ Q.subgroupOf X := Subgroup.mem_subgroupOf.mpr hx
      refine ⟨⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.mpr (hQT hx)⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr
        ((QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (⟨x, hxX⟩ : X)).mpr hxS)
  have h0 : Nat.card (Subgroup.map (X.subtype.comp (T.subgroupOf X).subtype)
      (((QuotientGroup.mk' (Q.subgroupOf X)).comp (T.subgroupOf X).subtype).ker))
      = Nat.card (((QuotientGroup.mk' (Q.subgroupOf X)).comp (T.subgroupOf X).subtype).ker) :=
    Subgroup.card_map_of_injective hinj
  rw [hgk] at h0
  have hcardL : Nat.card ↥(T.subgroupOf X) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
  have key := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (Q.subgroupOf X)).comp (T.subgroupOf X).subtype)
  rw [hgr, ← h0, hcardL] at key
  exact (mul_comm _ _).trans key

theorem omega_two_group {G : Type} [Group G] [Finite G] {X Q F : Subgroup G} {q : ℕ} (hq : 4 ≤ q)
    (hq2 : 2 ∣ q) (hQX : Q ≤ X) (hQF : Q ≤ F) (hFX : F ≤ X)
    (hFn : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hX : QuotSat X Q (IsOmegaPlus 2 q) ∨ QuotSat X Q (IsOmegaMinus 2 q))
    (h2 : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) ∈ Q) : F ≤ Q := by
  have hn : (Q.subgroupOf X).Normal := by
    rcases hX with ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact hn
  haveI := hn
  have hW : IsOmegaPlus 2 q (↥X ⧸ Q.subgroupOf X) ∨
      IsOmegaMinus 2 q (↥X ⧸ Q.subgroupOf X) := by
    rcases hX with ⟨_, hP⟩ | ⟨_, hP⟩
    · exact Or.inl hP
    · exact Or.inr hP
  have hFn' : (F.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFX]
    intro h k hh hk
    exact hFn k hk h hh
  have hNn : (bar X Q F).Normal :=
    hFn'.map (QuotientGroup.mk' (Q.subgroupOf X)) (QuotientGroup.mk'_surjective (Q.subgroupOf X))
  haveI := hNn
  have hNp : IsPGroup 2 ↥(bar X Q F) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr ?_
    intro g
    have hg : (g : ↥X ⧸ Q.subgroupOf X) ∈
        (F.subgroupOf X).map (QuotientGroup.mk' (Q.subgroupOf X)) := g.2
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
    obtain ⟨k, hk⟩ := h2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨k, Subtype.ext ?_⟩
    have hmem : x ^ 2 ^ k ∈ Q.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hk
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxg,
      ← map_pow (QuotientGroup.mk' (Q.subgroupOf X)) x]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (x ^ 2 ^ k)).mpr hmem
  have hbot : bar X Q F = ⊥ := (omega_normal_two hq hq2 hW (bar X Q F)).1 hNp
  intro f hf
  have hfX : f ∈ X := hFX hf
  have hfS : (⟨f, hfX⟩ : X) ∈ F.subgroupOf X := Subgroup.mem_subgroupOf.mpr hf
  have h1 : QuotientGroup.mk' (Q.subgroupOf X) ⟨f, hfX⟩ ∈ bar X Q F :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf X)) hfS
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (⟨f, hfX⟩ : X)).mp h1)

theorem omega_big {G : Type} [Group G] [Finite G] {X Q F : Subgroup G} {q : ℕ} (hq : 4 ≤ q)
    (hq2 : 2 ∣ q) (hQX : Q ≤ X) (hQF : Q ≤ F) (hFX : F ≤ X)
    (hFn : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hX : QuotSat X Q (IsOmegaPlus 2 q) ∨ QuotSat X Q (IsOmegaMinus 2 q))
    (hF : ∃ f ∈ F, f ∉ Q) :
    ∃ U : Subgroup G, Q ≤ U ∧ U ≤ F ∧ (∀ u ∈ U, ∃ k : ℕ, u ^ (2 ^ k) ∈ Q) ∧
      q * Nat.card Q ≤ Nat.card U := by
  have hn : (Q.subgroupOf X).Normal := by
    rcases hX with ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact hn
  haveI := hn
  have hW : IsOmegaPlus 2 q (↥X ⧸ Q.subgroupOf X) ∨
      IsOmegaMinus 2 q (↥X ⧸ Q.subgroupOf X) := by
    rcases hX with ⟨_, hP⟩ | ⟨_, hP⟩
    · exact Or.inl hP
    · exact Or.inr hP
  have hFn' : (F.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFX]
    intro h k hh hk
    exact hFn k hk h hh
  have hNn : (bar X Q F).Normal :=
    hFn'.map (QuotientGroup.mk' (Q.subgroupOf X)) (QuotientGroup.mk'_surjective (Q.subgroupOf X))
  haveI := hNn
  obtain ⟨f, hfF, hfQ⟩ := hF
  have hfX : f ∈ X := hFX hfF
  have hfS : (⟨f, hfX⟩ : X) ∈ F.subgroupOf X := Subgroup.mem_subgroupOf.mpr hfF
  have hNbot : bar X Q F ≠ ⊥ := by
    intro h
    have h1 : QuotientGroup.mk' (Q.subgroupOf X) ⟨f, hfX⟩ ∈ bar X Q F :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf X)) hfS
    rw [h, Subgroup.mem_bot] at h1
    exact hfQ (Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (⟨f, hfX⟩ : X)).mp h1))
  obtain ⟨Ub, hUbN, hUbp, hUbq⟩ := (omega_normal_two hq hq2 hW (bar X Q F)).2 hNbot
  have hex : ∃ U : Subgroup G, ∀ u : G, u ∈ U ↔
      ∃ x : X, QuotientGroup.mk' (Q.subgroupOf X) x ∈ Ub ∧ (x : G) = u := by
    refine ⟨(Ub.comap (QuotientGroup.mk' (Q.subgroupOf X))).map X.subtype, fun u => ?_⟩
    constructor
    · intro hu
      obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp hu
      exact ⟨x, Subgroup.mem_comap.mp hx, hxu⟩
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr hx, rfl⟩
  obtain ⟨U, hU⟩ := hex
  have hQU : Q ≤ U := by
    intro z hz
    have hzX : z ∈ X := hQX hz
    have hzS : (⟨z, hzX⟩ : X) ∈ Q.subgroupOf X := Subgroup.mem_subgroupOf.mpr hz
    have h1 : QuotientGroup.mk' (Q.subgroupOf X) ⟨z, hzX⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (⟨z, hzX⟩ : X)).mpr hzS
    rw [hU]
    refine ⟨⟨z, hzX⟩, ?_, rfl⟩
    rw [h1]
    exact Ub.one_mem
  have hUF : U ≤ F := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := (hU u).mp hu
    have hxb : QuotientGroup.mk' (Q.subgroupOf X) x ∈ bar X Q F := hUbN hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxb
    obtain ⟨z, hz, hzeq⟩ := (QuotientGroup.mk'_eq_mk' (Q.subgroupOf X)).mp hyx
    have hyF : (y : G) ∈ F := Subgroup.mem_subgroupOf.mp hy
    have hzQ : (z : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz
    rw [← hzeq, Subgroup.coe_mul]
    exact F.mul_mem hyF (hQF hzQ)
  have hUX : U ≤ X := hUF.trans hFX
  have hpow : ∀ u ∈ U, ∃ k : ℕ, u ^ (2 ^ k) ∈ Q := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := (hU u).mp hu
    obtain ⟨k, hk⟩ :=
      (isPGroup_iff_pow_pow_eq_one.mp hUbp) ⟨QuotientGroup.mk' (Q.subgroupOf X) x, hx⟩
    refine ⟨k, ?_⟩
    have hk' : QuotientGroup.mk' (Q.subgroupOf X) x ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    have h4 : QuotientGroup.mk' (Q.subgroupOf X) (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact hk'
    have h5 : x ^ 2 ^ k ∈ Q.subgroupOf X :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf X) (x ^ 2 ^ k)).mp h4
    have h6 : ((x ^ 2 ^ k : X) : G) ∈ Q := Subgroup.mem_subgroupOf.mp h5
    rw [Subgroup.coe_pow] at h6
    exact h6
  have hUbU : Ub ≤ bar X Q U := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf X) z
    have hxU : (x : G) ∈ U := (hU (x : G)).mpr ⟨x, hz, rfl⟩
    have hxS : x ∈ U.subgroupOf X := Subgroup.mem_subgroupOf.mpr hxU
    exact Subgroup.mem_map.mpr ⟨x, hxS, rfl⟩
  have hcard := card_bar_mul hQU hUX
  have hle : Nat.card Ub ≤ Nat.card (bar X Q U) := Subgroup.card_le_of_le hUbU
  refine ⟨U, hQU, hUF, hpow, ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (hUbq.trans hle) le_rfl

theorem card_le_sylow {G : Type} [Group G] [Finite G] (P : Sylow 2 G) {W : Subgroup G}
    (hW : IsPGroup 2 W) : Nat.card W ≤ Nat.card P := by
  obtain ⟨P', hP'⟩ := hW.exists_le_sylow
  have h1 : Nat.card W ≤ Nat.card (P' : Subgroup G) := Subgroup.card_le_of_le hP'
  have h2 : Nat.card P' = Nat.card P :=
    (Sylow.card_eq_multiplicity P').trans (Sylow.card_eq_multiplicity P).symm
  exact le_trans h1 (le_of_eq h2)

theorem sylow_bar {G : Type} [Group G] [Finite G] {D Q S : Subgroup G}
    [(Q.subgroupOf D).Normal] (hQS : Q ≤ S) (hSD : S ≤ D)
    (h2 : ∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) ∈ Q) (hodd : ¬ 2 ∣ S.relIndex D) :
    ∃ P : Sylow 2 (↥D ⧸ Q.subgroupOf D), P.toSubgroup = bar D Q S := by
  have hidx : (bar D Q S).index = S.relIndex D := by
    have hker : (QuotientGroup.mk' (Q.subgroupOf D) : ↥D →* ↥D ⧸ Q.subgroupOf D).ker ≤
        S.subgroupOf D := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp hx))
    exact Subgroup.index_map_eq (S.subgroupOf D) (QuotientGroup.mk'_surjective _) hker
  have hcard : Nat.card (↥D ⧸ Q.subgroupOf D) = S.relIndex D * Nat.card (bar D Q S) := by
    rw [← hidx, Subgroup.index_mul_card]
  have hbar2 : IsPGroup 2 (bar D Q S) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨x, hx⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h2 (s : G) (Subgroup.mem_subgroupOf.mp hs)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (QuotientGroup.mk' (Q.subgroupOf D) s) ^ (2 ^ k) = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hk
  have par : ∀ a b r m : ℕ, ¬ 2 ∣ r → ¬ 2 ∣ m → 2 ^ a * r = 2 ^ b * m → a = b := by
    have key : ∀ c s : ℕ, ¬ 2 ∣ s → (2 ^ c * s).factorization 2 = c := by
      intro c s hs
      have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero 2)
      rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hs0, Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hs,
        add_zero]
    intro a b r m hr hm h
    have h' : (2 ^ a * r).factorization 2 = (2 ^ b * m).factorization 2 := by rw [h]
    rwa [key a r hr, key b m hm] at h'
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hbar2
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hbar2
  have hPcard : Nat.card (P : Subgroup (↥D ⧸ Q.subgroupOf D)) =
      2 ^ (Nat.card (↥D ⧸ Q.subgroupOf D)).factorization 2 := Sylow.card_eq_multiplicity P
  have hPodd : ¬ 2 ∣ (P : Subgroup (↥D ⧸ Q.subgroupOf D)).index := Sylow.not_dvd_index P
  have hPidx : Nat.card (P : Subgroup (↥D ⧸ Q.subgroupOf D)) *
      (P : Subgroup (↥D ⧸ Q.subgroupOf D)).index = Nat.card (↥D ⧸ Q.subgroupOf D) :=
    Subgroup.card_mul_index (P : Subgroup (↥D ⧸ Q.subgroupOf D))
  have e1 : 2 ^ (Nat.card (↥D ⧸ Q.subgroupOf D)).factorization 2 *
      (P : Subgroup (↥D ⧸ Q.subgroupOf D)).index = Nat.card (↥D ⧸ Q.subgroupOf D) := by
    rw [← hPcard]
    exact hPidx
  have e2 : Nat.card (↥D ⧸ Q.subgroupOf D) = S.relIndex D * 2 ^ a := by
    rw [hcard, ha]
  have e3 := e1.trans e2
  have hav : a = (Nat.card (↥D ⧸ Q.subgroupOf D)).factorization 2 :=
    par a _ _ _ hodd hPodd ((Nat.mul_comm _ _).trans e3.symm)
  have hPeq : Nat.card (P : Subgroup (↥D ⧸ Q.subgroupOf D)) = Nat.card (bar D Q S) := by
    rw [hPcard, ha, hav]
  exact ⟨P, (Subgroup.eq_of_le_of_card_ge hP hPeq.le).symm⟩

theorem card_prod_two {G : Type} [Group G] [Finite G] {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ Nat.card W = Nat.card A * Nat.card B := by
  have hcomm : ∀ x : ↥A, ∀ y : ↥B, Commute (A.subtype x) (B.subtype y) :=
    fun x y => hc x x.2 y y.2
  obtain ⟨f, hf⟩ : ∃ f : ↥A × ↥B →* G, ∀ a b, f (a, b) = (a : G) * (b : G) :=
    ⟨MonoidHom.noncommCoprod A.subtype B.subtype hcomm, fun a b => rfl⟩
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : G) * (b : G) = 1 := by rw [← hf]; exact hab
    have hb : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : (a : G) ∈ A ⊓ B := ⟨a.2, by rw [hb]; exact B.inv_mem b.2⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have hb1 : (b : G) = 1 := by rw [hmem, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb1)
  have hprod : IsPGroup 2 (↥A × ↥B) := by
    obtain ⟨ma, hma⟩ := IsPGroup.iff_card.mp hA
    obtain ⟨mb, hmb⟩ := IsPGroup.iff_card.mp hB
    exact IsPGroup.of_card (n := ma + mb) (by rw [Nat.card_prod, hma, hmb, pow_add])
  refine ⟨f.range, hprod.of_surjective f.rangeRestrict f.rangeRestrict_surjective, ?_⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

noncomputable def conjQuot {G : Type} [Group G] {D Q X : Subgroup G} [(Q.subgroupOf D).Normal]
    (hD : X ≤ Subgroup.normalizer (D : Set G)) (hQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    ↥X →* MulAut (↥D ⧸ Q.subgroupOf D) := by
  have hDmem : ∀ x : ↥X, ∀ d : G, d ∈ D ↔ (x : G) * d * (x : G)⁻¹ ∈ D :=
    fun x d => Subgroup.mem_normalizer_iff.1 (hD x.2) d
  have hQmem : ∀ x : ↥X, ∀ d : G, d ∈ Q ↔ (x : G) * d * (x : G)⁻¹ ∈ Q :=
    fun x d => Subgroup.mem_normalizer_iff.1 (hQ x.2) d
  let cD : ↥X → (↥D ≃* ↥D) := fun x =>
    { toFun := fun d => ⟨(x : G) * (d : G) * (x : G)⁻¹, (hDmem x (d : G)).1 d.2⟩
      invFun := fun d => ⟨(x : G)⁻¹ * (d : G) * (x : G), (hDmem x ((x : G)⁻¹ * (d : G) *
        (x : G))).2 (by
          rw [show (x : G) * ((x : G)⁻¹ * (d : G) * (x : G)) * (x : G)⁻¹ = (d : G) by group]
          exact d.2)⟩
      left_inv := fun d => Subtype.ext (by
        show (x : G)⁻¹ * ((x : G) * (d : G) * (x : G)⁻¹) * (x : G) = (d : G)
        group)
      right_inv := fun d => Subtype.ext (by
        show (x : G) * ((x : G)⁻¹ * (d : G) * (x : G)) * (x : G)⁻¹ = (d : G)
        group)
      map_mul' := fun a b => Subtype.ext (by
        show (x : G) * ((a : G) * (b : G)) * (x : G)⁻¹ =
          ((x : G) * (a : G) * (x : G)⁻¹) * ((x : G) * (b : G) * (x : G)⁻¹)
        group) }
  have hcD : ∀ (x : ↥X) (d : ↥D), ((cD x d : ↥D) : G) = (x : G) * (d : G) * (x : G)⁻¹ :=
    fun _ _ => rfl
  have he : ∀ x : ↥X, (Q.subgroupOf D).map ((cD x : ↥D ≃* ↥D) : ↥D →* ↥D) = Q.subgroupOf D := by
    intro x
    rw [Subgroup.map_equiv_eq_comap_symm]
    ext z
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show (x : G)⁻¹ * (z : G) * (x : G) ∈ Q ↔ (z : G) ∈ Q
    have h := hQmem x ((x : G)⁻¹ * (z : G) * (x : G))
    rw [show (x : G) * ((x : G)⁻¹ * (z : G) * (x : G)) * (x : G)⁻¹ = (z : G) by group] at h
    exact h
  let F : ↥X → MulAut (↥D ⧸ Q.subgroupOf D) := fun x =>
    QuotientGroup.congr (Q.subgroupOf D) (Q.subgroupOf D) (cD x) (he x)
  have hF : ∀ (x : ↥X) (d : ↥D), F x (QuotientGroup.mk d) = QuotientGroup.mk (cD x d) :=
    fun x d => QuotientGroup.congr_mk _ _ _ _ _
  refine MonoidHom.mk' F ?_
  intro a b
  apply MulEquiv.ext
  intro y
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAut.mul_apply, hF, hF, hF]
  congr 1
  exact Subtype.ext (by
    simp only [hcD, Subgroup.coe_mul]
    group)

theorem conjQuot_mk {G : Type} [Group G] {D Q X : Subgroup G} [(Q.subgroupOf D).Normal]
    (hD : X ≤ Subgroup.normalizer (D : Set G)) (hQ : X ≤ Subgroup.normalizer (Q : Set G))
    (x : ↥X) (d d' : ↥D) (hd' : (d' : G) = (x : G) * (d : G) * (x : G)⁻¹) :
    conjQuot hD hQ x (QuotientGroup.mk d) = QuotientGroup.mk d' := by
  dsimp only [conjQuot]
  rw [MonoidHom.mk'_apply, QuotientGroup.congr_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext hd'.symm)

theorem inner_pi {G : Type} [Group G] [Finite G] {D Q X : Subgroup G}
    [(Q.subgroupOf D).Normal] (hQD : Q ≤ D)
    (hD : X ≤ Subgroup.normalizer (D : Set G)) (hQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hKF7 : ListNoPerfectOutStatement) (hsimp : IsSimpleGroup (↥D ⧸ Q.subgroupOf D))
    (hlist : ListGroup (↥D ⧸ Q.subgroupOf D))
    (hnab : ∃ a b : ↥D ⧸ Q.subgroupOf D, a * b ≠ b * a)
    (hQX : Q ≤ X) (hperf : ⁅X, X⁆ ⊔ Q = X) :
    (∀ x : ↥X, ∃ g : ↥D ⧸ Q.subgroupOf D, conjQuot hD hQ x = MulAut.conj g) ∧
    ∃ P0 : Subgroup (↥D ⧸ Q.subgroupOf D),
      (∀ g, g ∈ P0 ↔ ∃ x : ↥X, conjQuot hD hQ x = MulAut.conj g) ∧ ⁅P0, P0⁆ = P0 := by
  obtain ⟨ψ, hψeq⟩ : ∃ ψ : ↥X →* MulAut (↥D ⧸ Q.subgroupOf D), ψ = conjQuot hD hQ :=
    ⟨_, rfl⟩
  rw [← hψeq]
  have hψform : ∀ (x : ↥X) (d d' : ↥D), (d' : G) = (x : G) * (d : G) * (x : G)⁻¹ →
      ψ x (QuotientGroup.mk d) = QuotientGroup.mk d' := by
    intro x d d' hd'
    rw [hψeq]
    exact conjQuot_mk hD hQ x d d' hd'
  have hNorm : ∀ (d : ↥D) (r : G), r ∈ Q → (d : G)⁻¹ * r * (d : G) ∈ Q := by
    intro d r hr
    have hrD : (⟨r, hQD hr⟩ : ↥D) ∈ Q.subgroupOf D := Subgroup.mem_subgroupOf.2 hr
    have h := (inferInstance : (Q.subgroupOf D).Normal).conj_mem _ hrD d⁻¹
    simpa using Subgroup.mem_subgroupOf.1 h
  have hψQ : ∀ q : ↥X, (q : G) ∈ Q → ψ q = 1 := by
    intro q hq
    apply MulEquiv.ext
    intro y
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (q : G) * (d : G) * (q : G)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.1 (hD q.2) (d : G)).1 d.2
    rw [hψform q d ⟨_, hmem⟩ rfl, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((q : G) * (d : G) * (q : G)⁻¹)⁻¹ * (d : G) ∈ Q
    have key : ((q : G) * (d : G) * (q : G)⁻¹)⁻¹ * (d : G) =
        (q : G) * ((d : G)⁻¹ * (q : G)⁻¹ * (d : G)) := by group
    rw [key]
    exact Q.mul_mem hq (hNorm d _ (Q.inv_mem hq))
  have hinj : Function.Injective
      (MulAut.conj : (↥D ⧸ Q.subgroupOf D) →* MulAut (↥D ⧸ Q.subgroupOf D)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center (↥D ⧸ Q.subgroupOf D) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 : MulAut.conj g h = h := by rw [hg, MulAut.one_apply]
      rw [MulAut.conj_apply] at h1
      calc h * g = (g * h * g⁻¹) * g := by rw [h1]
        _ = g * h := by group
    have hcen : Subgroup.center (↥D ⧸ Q.subgroupOf D) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (↥D ⧸ Q.subgroupOf D)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        apply hab
        have ha : a ∈ Subgroup.center (↥D ⧸ Q.subgroupOf D) := by
          rw [h]
          exact Subgroup.mem_top a
        exact ((Subgroup.mem_center_iff.1 ha) b).symm
    rw [hcen] at hgc
    exact Subgroup.mem_bot.1 hgc
  have hRperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact ψ.range.mul_mem (ψ.range.mul_mem (ψ.range.mul_mem ha hb) (ψ.range.inv_mem ha))
        (ψ.range.inv_mem hb)
    · let S : Subgroup ↥X := Subgroup.comap ψ ⁅ψ.range, ψ.range⁆
      let S' : Subgroup G := S.map X.subtype
      have hcS : ⁅X, X⁆ ≤ S' := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        have huv : ⁅(⟨x, hx⟩ : ↥X), (⟨y, hy⟩ : ↥X)⁆ ∈ S := by
          show ψ ⁅(⟨x, hx⟩ : ↥X), (⟨y, hy⟩ : ↥X)⁆ ∈ ⁅ψ.range, ψ.range⁆
          rw [map_commutatorElement]
          exact Subgroup.commutator_mem_commutator (MonoidHom.mem_range.2 ⟨_, rfl⟩)
            (MonoidHom.mem_range.2 ⟨_, rfl⟩)
        exact Subgroup.mem_map_of_mem X.subtype huv
      have hQS : Q ≤ S' := by
        intro q hq
        have huq : (⟨q, hQX hq⟩ : ↥X) ∈ S := by
          show ψ ⟨q, hQX hq⟩ ∈ ⁅ψ.range, ψ.range⁆
          rw [hψQ ⟨q, hQX hq⟩ hq]
          exact Subgroup.one_mem _
        exact Subgroup.mem_map_of_mem X.subtype huq
      have hXS : X ≤ S' := by
        have h := sup_le hcS hQS
        rw [hperf] at h
        exact h
      intro r hr
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hr
      obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.1 (hXS x.2)
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hyS
  have hRle : ψ.range ≤
      (MulAut.conj : (↥D ⧸ Q.subgroupOf D) →* MulAut (↥D ⧸ Q.subgroupOf D)).range :=
    hKF7 (↥D ⧸ Q.subgroupOf D) hlist hsimp ψ.range hRperf
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (hRle (MonoidHom.mem_range.2 ⟨x, rfl⟩))
    exact ⟨g, hg.symm⟩
  · refine ⟨Subgroup.comap
      (MulAut.conj : (↥D ⧸ Q.subgroupOf D) →* MulAut (↥D ⧸ Q.subgroupOf D)) ψ.range, ?_, ?_⟩
    · intro g
      rw [Subgroup.mem_comap, MonoidHom.mem_range]
    · have hmap : Subgroup.map
          (MulAut.conj : (↥D ⧸ Q.subgroupOf D) →* MulAut (↥D ⧸ Q.subgroupOf D))
          (Subgroup.comap
            (MulAut.conj : (↥D ⧸ Q.subgroupOf D) →* MulAut (↥D ⧸ Q.subgroupOf D)) ψ.range)
          = ψ.range := by
        rw [Subgroup.map_comap_eq, inf_eq_right.2 hRle]
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, hmap]
      exact hRperf

end CaseA3

open CaseA3

theorem caseA3_conj_conj {G : Type} [Group G] (s g : G) (N : Subgroup G) :
    conjSubgroup (s * g) N = conjSubgroup s (conjSubgroup g N) := by
  ext x
  simp [mem_conjSubgroup, mul_assoc]

theorem caseA3_conj_one {G : Type} [Group G] (N : Subgroup G) : conjSubgroup 1 N = N := by
  ext x
  simp [mem_conjSubgroup]

theorem caseA3_conj_mono {G : Type} [Group G] (s : G) {T U : Subgroup G} (h : T ≤ U) :
    conjSubgroup s T ≤ conjSubgroup s U :=
  Subgroup.map_mono h

theorem caseA3_D_le {G : Type} [Group G] (M Q B : Subgroup G) (t s : G)
    (hs : s ∈ Lgen M (LB M Q B)) :
    conjSubgroup s (E1Dpre M Q B t) ≤ E1Dpre M Q B t := by
  unfold E1Dpre
  rw [conjSubgroup, Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg => ?_
  refine le_iSup₂_of_le (s * g) (mul_mem hs hg) (le_of_eq ?_)
  rw [caseA3_conj_conj]
  rfl

theorem caseA3_D_eq {G : Type} [Group G] (M Q B : Subgroup G) (t s : G)
    (hs : s ∈ Lgen M (LB M Q B)) :
    conjSubgroup s (E1Dpre M Q B t) = E1Dpre M Q B t := by
  apply le_antisymm (caseA3_D_le M Q B t s hs)
  have h1 := caseA3_conj_mono s (caseA3_D_le M Q B t s⁻¹ (inv_mem hs))
  rw [← caseA3_conj_conj, mul_inv_cancel, caseA3_conj_one] at h1
  exact h1

theorem caseA3_N_le_D {G : Type} [Group G] (M Q B : Subgroup G) (t : G) :
    Nt M (LB M Q B) t ≤ E1Dpre M Q B t := by
  unfold E1Dpre
  refine le_iSup₂_of_le (1 : G) (one_mem (Lgen M (LB M Q B))) (le_of_eq ?_)
  exact (caseA3_conj_one (Nt M (LB M Q B) t)).symm


theorem caseA3_pointwise {G : Type} [Group G] {S Q : Subgroup G}
    (hq : QuotSat S Q (fun W _ => IsPGroup 2 W)) : ∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) ∈ Q := by
  obtain ⟨hn, hP⟩ := hq
  haveI := hn
  intro s hs
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hP (QuotientGroup.mk ⟨s, hs⟩)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem caseA3_bar_pgroup {G : Type} [Group G] {D Q S : Subgroup G}
    [(Q.subgroupOf D).Normal] (h2 : ∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) ∈ Q) :
    IsPGroup 2 ↥(bar D Q S) := by
  refine isPGroup_iff_pow_pow_eq_one.mpr ?_
  rintro ⟨y, hy⟩
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨k, hk⟩ := h2 (s : G) hs
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa using hk


theorem caseA3_pow_mem {G : Type} [Group G] {D Q : Subgroup G} [(Q.subgroupOf D).Normal]
    {f : G} (hfD : f ∈ D) {k : ℕ}
    (h : (QuotientGroup.mk ⟨f, hfD⟩ : ↥D ⧸ Q.subgroupOf D) ^ (2 ^ k) = 1) :
    f ^ (2 ^ k) ∈ Q := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  simpa using h

theorem caseA3_bar_comm {G : Type} [Group G] {D Q S T : Subgroup G} [(Q.subgroupOf D).Normal]
    (h : ∀ a ∈ S, ∀ b ∈ T, ⁅a, b⁆ ∈ Q) :
    ∀ x ∈ bar D Q S, ∀ y ∈ bar D Q T, x * y = y * x := by
  rintro _ hx _ hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_subgroupOf] at ha hb
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa [commutatorElement_def, mul_assoc] using
    Q.inv_mem (h a⁻¹ (S.inv_mem ha) b⁻¹ (T.inv_mem hb))


theorem caseA3_perfect_lift {G : Type} [Group G] {D Q : Subgroup G}
    [(Q.subgroupOf D).Normal] (hQD : Q ≤ D) {P0 : Subgroup (↥D ⧸ Q.subgroupOf D)}
    (hP0 : ⁅P0, P0⁆ = P0) {P' : Subgroup ↥D}
    (hP' : ∀ d : ↥D, d ∈ P' ↔ (QuotientGroup.mk d : ↥D ⧸ Q.subgroupOf D) ∈ P0) :
    ⁅P'.map D.subtype, P'.map D.subtype⁆ ⊔ Q = P'.map D.subtype := by
  have hmap : P'.map (QuotientGroup.mk' (Q.subgroupOf D)) = P0 := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (hP' d).mp hd
    · intro hy
      obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨d, (hP' d).mpr hy, rfl⟩
  have e : (⁅P', P'⁆ ⊔ Q.subgroupOf D).map D.subtype =
      ⁅P'.map D.subtype, P'.map D.subtype⁆ ⊔ Q := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQD]
  apply le_antisymm
  · refine sup_le (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · intro q hq
      refine Subgroup.mem_map.mpr ⟨⟨q, hQD hq⟩, (hP' ⟨q, hQD hq⟩).mpr ?_, rfl⟩
      have h1 : (QuotientGroup.mk ⟨q, hQD hq⟩ : ↥D ⧸ Q.subgroupOf D) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hq
      rw [h1]
      exact P0.one_mem
  · intro g hg
    rw [← e]
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hg
    have h1 : (QuotientGroup.mk d : ↥D ⧸ Q.subgroupOf D) ∈
        ⁅P', P'⁆.map (QuotientGroup.mk' (Q.subgroupOf D)) := by
      rw [Subgroup.map_commutator, hmap, hP0]
      exact (hP' d).mp hd
    obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.mp h1
    simp only [QuotientGroup.mk'_apply] at hcd
    rw [QuotientGroup.eq] at hcd
    have hdmem : d ∈ ⁅P', P'⁆ ⊔ Q.subgroupOf D := by
      have h2 : d = c * (c⁻¹ * d) := by group
      rw [h2]
      exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hcd)
    exact Subgroup.mem_map.mpr ⟨d, hdmem, rfl⟩

theorem caseA3_of
    (hA2 : CaseA2Statement) (hKF7 : ListNoPerfectOutStatement)
    (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hSyl : KFacts.CaseASylowStatement) (hAb : KFacts.CaseASylowAbelianStatement)
    (hW : CFSG.Walter.WalterModelsForm) (hWL : KFacts.WalterListLargeSylowStatement)
    (hC : NtCentralStatement) (hEA : NtElemAbelianStatement) : CaseA3Statement := by
  intro G _ _ M Q Z B t hH hE d hd x hx
  have hc : Ctx M Q Z B := hH.ctx
  have htL : t ∈ LB M Q B := hH.mem
  have htQ : t ∉ Q := hH.notQ
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : 2 ∣ Nat.card Z := by
    obtain ⟨n, k, hn, -⟩ := hc.hyp.cp
    rw [hn] at hq4 ⊢
    apply dvd_pow_self
    rintro rfl
    norm_num at hq4
  obtain ⟨hNL, hNX, hNR, hRX, hperf, -, -, hPlus, hMinus⟩ := hSplit G M Q Z B t hH
  have hX : QuotSat (E1Xpre M Q B t) Q (IsOmegaPlus 2 (Nat.card Z)) ∨
      QuotSat (E1Xpre M Q B t) Q (IsOmegaMinus 2 (Nat.card Z)) := by
    obtain ⟨h9, hNc, hPM⟩ := hH.case
    rcases hPM with hP | hM
    · exact Or.inl (hPlus (by unfold CaseE1Plus; exact ⟨h9, hNc, hP⟩))
    · exact Or.inr (hMinus (by unfold CaseE1Minus; exact ⟨h9, hNc, hM⟩))
  have hNcard : Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z := by
    obtain ⟨-, hNc, -⟩ := hH.case
    exact hNc
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQnM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hXLg : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hc htL
  haveI : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hQnM hx
  have hLgM : Lgen M (LB M Q B) ≤ M := Lgen_le_M hc
  have hLgH0 : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hQX : Q ≤ E1Xpre M Q B t := le_sup_right
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t :=
    sup_le (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
        ((Rt M (LB M Q B) t).mul_mem ha hb) ((Rt M (LB M Q B) t).inv_mem ha))
        ((Rt M (LB M Q B) t).inv_mem hb)) (hc.Q_le_Rt htL)
  have hCc : ∀ x ∈ E1Xpre M Q B t, ∀ n ∈ Nt M (LB M Q B) t, ⁅x, n⁆ ∈ Q :=
    fun x hx n hn => hC G M Q Z B t hH x (hXR hx) n hn
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have hEA' := hEA G M Q Z B t hH
  have hNQ : Q ≤ Nt M (LB M Q B) t := Q_le_Nt hc htL
  have hND : Nt M (LB M Q B) t ≤ E1Dpre M Q B t := caseA3_N_le_D M Q B t
  have hQD : Q ≤ E1Dpre M Q B t := hNQ.trans hND
  have hDLg : E1Dpre M Q B t ≤ Lgen M (LB M Q B) := by
    unfold E1Dpre
    refine iSup₂_le fun g hg => ?_
    intro y hy
    have h1 : g⁻¹ * y * g ∈ Nt M (LB M Q B) t := mem_conjSubgroup.mp hy
    have h2 : g⁻¹ * y * g ∈ Lgen M (LB M Q B) :=
      (orthE1_Nt_le_Rt M (LB M Q B) t).trans ((Rt_le_Lgen _ _ _).trans le_rfl) h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) (hLgM hg)) _).mp h2
    simpa [mul_assoc] using h3
  have hXD : ∀ x ∈ E1Xpre M Q B t, ∀ d ∈ E1Dpre M Q B t,
      x * d * x⁻¹ ∈ E1Dpre M Q B t := by
    intro x hx d hd
    have h1 : d ∈ conjSubgroup x⁻¹ (E1Dpre M Q B t) := by
      rw [caseA3_D_eq M Q B t x⁻¹ (inv_mem (hXLg hx))]
      exact hd
    simpa using (mem_conjSubgroup.mp h1)
  have hXDn : ∀ x ∈ E1Xpre M Q B t, x ∈ Subgroup.normalizer (E1Dpre M Q B t : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hXD x hx h hh, fun hh => ?_⟩
    simpa [mul_assoc] using hXD x⁻¹ ((E1Xpre M Q B t).inv_mem hx) _ hh
  have hXQn : E1Xpre M Q B t ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hQnM (hLgM (hXLg hx))
  obtain ⟨hnD, hP⟩ := hA2 G M Q Z B t hH hE
  obtain ⟨hsimp, hlist⟩ := hP
  haveI := hnD
  haveI := hsimp
  have hnab : ∃ a b : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) :=
      ⟨⟨fun a b => hcon a b⟩⟩
    have hprime := (Group.is_simple_iff_prime_card).mp hsimp
    have hbar := card_bar_mul hNQ hND
    rw [hNcard, mul_comm] at hbar
    have hbarcard : Nat.card (bar (E1Dpre M Q B t) Q (Nt M (LB M Q B) t)) = Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos hbar
    have hdvd : Nat.card Z ∣
        Nat.card (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) := by
      rw [← hbarcard]
      exact Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime hprime).mp hdvd with h1 | h1
    · omega
    · have h2 : 2 ∣ Nat.card (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) :=
        h1 ▸ hq2
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h2
      omega
  have hF : ∀ f ∈ E1Xpre M Q B t, f ∈ E1Dpre M Q B t → f ∈ Q := by
    intro f0 hf0X hf0D
    by_contra hf0Q
    obtain ⟨S, hQS, hSD, hSc, hSq, hSodd⟩ := hSyl G M Q Z B t hH hE
    have hSab := hAb G M Q Z B t hH hE ⟨f0, hf0X, hf0D, hf0Q⟩ S hQS hSD hSc hSq hSodd
    have h2S := caseA3_pointwise hSq
    obtain ⟨P, hPS⟩ := sylow_bar hQS hSD h2S hSodd
    have hPab : IsMulCommutative
        (P : Subgroup (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t))) := by
      have hPeq : (P : Subgroup (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t))) =
          bar (E1Dpre M Q B t) Q S := hPS
      rw [hPeq]
      exact ⟨⟨fun a b => Subtype.ext (caseA3_bar_comm hSab a.1 a.2 b.1 b.2)⟩⟩
    have hWal : WalterList (↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) :=
      hW _ hnab P hPab
    have hFn : ∀ x ∈ E1Xpre M Q B t, ∀ f ∈ E1Xpre M Q B t ⊓ E1Dpre M Q B t,
        x * f * x⁻¹ ∈ E1Xpre M Q B t ⊓ E1Dpre M Q B t := fun x hx f hf =>
      ⟨(E1Xpre M Q B t).mul_mem ((E1Xpre M Q B t).mul_mem hx hf.1)
        ((E1Xpre M Q B t).inv_mem hx), hXD x hx f hf.2⟩
    obtain ⟨U, hQU, hUF, hU2, hUcard⟩ := omega_big hq4 hq2 hQX (le_inf hQX hQD) inf_le_left
      hFn hX ⟨f0, ⟨hf0X, hf0D⟩, hf0Q⟩
    have hUD : U ≤ E1Dpre M Q B t := hUF.trans inf_le_right
    have hUX : U ≤ E1Xpre M Q B t := hUF.trans inf_le_left
    have hUbar := card_bar_mul hQU hUD
    have hUb2 : IsPGroup 2 ↥(bar (E1Dpre M Q B t) Q U) := caseA3_bar_pgroup hU2
    have hNb2 : IsPGroup 2 ↥(bar (E1Dpre M Q B t) Q (Nt M (LB M Q B) t)) :=
      caseA3_bar_pgroup (fun s hs => ⟨1, by norm_num; exact hEA'.2 s hs⟩)
    have hNbar := card_bar_mul hNQ hND
    rw [hNcard, mul_comm] at hNbar
    have hNbarcard : Nat.card (bar (E1Dpre M Q B t) Q (Nt M (LB M Q B) t)) = Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos hNbar
    have hUq : Nat.card Z ≤ Nat.card (bar (E1Dpre M Q B t) Q U) := by
      have h1 : Nat.card Z * Nat.card Q ≤ Nat.card (bar (E1Dpre M Q B t) Q U) * Nat.card Q := by
        rw [hUbar]; exact hUcard
      exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    have hcomm : ∀ a ∈ bar (E1Dpre M Q B t) Q (Nt M (LB M Q B) t),
        ∀ b ∈ bar (E1Dpre M Q B t) Q U, a * b = b * a :=
      caseA3_bar_comm (fun n hn u hu => by
        have h1 := Q.inv_mem (hCc u (hUX hu) n hn)
        rw [commutatorElement_inv] at h1
        exact h1)
    have hdisj : bar (E1Dpre M Q B t) Q (Nt M (LB M Q B) t) ⊓ bar (E1Dpre M Q B t) Q U = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyN, hyU⟩
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hyN
      obtain ⟨u, hu, hnu⟩ := Subgroup.mem_map.mp hyU
      rw [Subgroup.mem_subgroupOf] at hn hu
      have hq' : (u : G)⁻¹ * (n : G) ∈ Q := by
        have h1 := QuotientGroup.eq.mp hnu
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      have hnX : (n : G) ∈ E1Xpre M Q B t := by
        have h1 : (n : G) = (u : G) * ((u : G)⁻¹ * (n : G)) := by group
        rw [h1]
        exact (E1Xpre M Q B t).mul_mem (hUX hu) (hQX hq')
      have hnQ : (n : G) ∈ Q := by
        have h1 : (n : G) ∈ Nt M (LB M Q B) t ⊓ E1Xpre M Q B t := ⟨hn, hnX⟩
        rw [hNX] at h1
        exact h1
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact hnQ
    obtain ⟨W, hW2, hWcard⟩ := card_prod_two hNb2 hUb2 hcomm hdisj
    have hWP := card_le_sylow P hW2
    have h16 : 16 ≤ Nat.card P := by
      have h44 : 4 * 4 ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul hq4 hq4
      have h1 : Nat.card Z * Nat.card Z ≤ Nat.card W := by
        rw [hWcard, hNbarcard]
        exact Nat.mul_le_mul_left _ hUq
      omega
    have htN' : t ∈ E1Dpre M Q B t := hND htN
    have hii : (QuotientGroup.mk ⟨t, htN'⟩ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) *
        QuotientGroup.mk ⟨t, htN'⟩ = 1 := by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [sq] using hEA'.2 t htN
    have hi1 : (QuotientGroup.mk ⟨t, htN'⟩ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t))
        ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      exact htQ h
    have hcent := hWL _ hWal P h16 _ hii hi1
    have h2F : ∀ f ∈ E1Xpre M Q B t ⊓ E1Dpre M Q B t, ∃ k : ℕ, f ^ (2 ^ k) ∈ Q := by
      rintro f ⟨hfX, hfD⟩
      have hmem : (QuotientGroup.mk ⟨f, hfD⟩ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t))
          ∈ Subgroup.centralizer
            ({QuotientGroup.mk ⟨t, htN'⟩} : Set (↥(E1Dpre M Q B t) ⧸
              Q.subgroupOf (E1Dpre M Q B t))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hcomm' := hCc f⁻¹ ((E1Xpre M Q B t).inv_mem hfX) t⁻¹
          ((Nt M (LB M Q B) t).inv_mem htN)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        simpa [commutatorElement_def, mul_assoc] using hcomm'
      obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hcent ⟨_, hmem⟩
      refine ⟨k, caseA3_pow_mem hfD ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hFQ := omega_two_group hq4 hq2 hQX (le_inf hQX hQD) inf_le_left hFn hX h2F
    exact hf0Q (hFQ ⟨hf0X, hf0D⟩)
  have hD : E1Xpre M Q B t ≤ Subgroup.normalizer (E1Dpre M Q B t : Set G) :=
    fun x hx => hXDn x hx
  have hQ : E1Xpre M Q B t ≤ Subgroup.normalizer (Q : Set G) := fun x hx => hXQn hx
  have htN' : t ∈ E1Dpre M Q B t := hND htN
  obtain ⟨hinner, P0, hP0char, hP0perf⟩ :=
    inner_pi hQD hXDn hXQn hKF7 hsimp hlist hnab hQX hperf
  have hkey : ∀ ĝ : ↥(E1Dpre M Q B t),
      (QuotientGroup.mk ĝ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) ∈ P0 →
      ⁅(ĝ : G), t⁆ ∈ Q := by
    intro ĝ hĝ
    obtain ⟨⟨y, hyX⟩, hy⟩ := (hP0char _).mp hĝ
    have hA := conjQuot_mk hD hQ ⟨y, hyX⟩ ⟨t, htN'⟩ ⟨y * t * y⁻¹, hXD y hyX t htN'⟩ rfl
    rw [hy, MulAut.conj_apply] at hA
    have E1 : (QuotientGroup.mk ⟨y * t * y⁻¹, hXD y hyX t htN'⟩ :
        ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) = QuotientGroup.mk ⟨t, htN'⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def, mul_assoc] using hCc y hyX t⁻¹ (inv_mem htN)
    have E2 := hA.trans E1
    have hcomm : (QuotientGroup.mk ĝ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) *
        QuotientGroup.mk ⟨t, htN'⟩ = QuotientGroup.mk ⟨t, htN'⟩ *
          QuotientGroup.mk ĝ := mul_inv_eq_iff_eq_mul.mp E2
    have hmk : (QuotientGroup.mk' (Q.subgroupOf (E1Dpre M Q B t)))
        ⁅ĝ, (⟨t, htN'⟩ : ↥(E1Dpre M Q B t))⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
    exact hmk
  obtain ⟨Ph, hPh⟩ : ∃ Ph : Subgroup G,
      Ph = (P0.comap (QuotientGroup.mk' (Q.subgroupOf (E1Dpre M Q B t)))).map
        (E1Dpre M Q B t).subtype := ⟨_, rfl⟩
  have hP'mem : ∀ d : ↥(E1Dpre M Q B t),
      d ∈ P0.comap (QuotientGroup.mk' (Q.subgroupOf (E1Dpre M Q B t))) ↔
        (QuotientGroup.mk d : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) ∈ P0 :=
    fun d => Iff.rfl
  have hperfPh : ⁅Ph, Ph⁆ ⊔ Q = Ph := by
    rw [hPh]
    exact caseA3_perfect_lift hQD hP0perf hP'mem
  have hQPh : Q ≤ Ph := by
    intro q hq
    rw [hPh]
    refine Subgroup.mem_map.mpr ⟨⟨q, hQD hq⟩, (hP'mem ⟨q, hQD hq⟩).mpr ?_, rfl⟩
    have h1 : (QuotientGroup.mk ⟨q, hQD hq⟩ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t))
        = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hq
    rw [h1]
    exact P0.one_mem
  have hPhCt : Ph ≤ E1Ct hH.ctx t := by
    intro g hg
    rw [hPh] at hg
    obtain ⟨ĝ, hĝ, rfl⟩ := Subgroup.mem_map.mp hg
    have hĝD : (ĝ : G) ∈ Lgen M (LB M Q B) := hDLg ĝ.2
    unfold E1Ct
    exact ⟨mem_CommQ.mpr ⟨hLgM hĝD, hkey ĝ hĝ⟩, hLgH0 hĝD⟩
  have hPhX : Ph ≤ E1Xpre M Q B t := (hCt G M Q Z B t hH).2.2 Ph hQPh hPhCt hperfPh
  obtain ⟨g, hg⟩ := hinner ⟨x, hx⟩
  have hgP0 : g ∈ P0 := (hP0char g).mpr ⟨⟨x, hx⟩, hg⟩
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk_surjective g
  have hĝPh : (ĝ : G) ∈ Ph := by
    rw [hPh]
    exact Subgroup.mem_map.mpr ⟨ĝ, hgP0, rfl⟩
  have hĝQ : (ĝ : G) ∈ Q := hF (ĝ : G) (hPhX hĝPh) ĝ.2
  have h1 : (QuotientGroup.mk ĝ : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hĝQ
  rw [h1, map_one] at hg
  have h2 : conjQuot hD hQ ⟨x, hx⟩ (QuotientGroup.mk ⟨d, hd⟩) = QuotientGroup.mk ⟨d, hd⟩ := by
    rw [hg, MulAut.one_apply]
  have h3 := conjQuot_mk hD hQ ⟨x, hx⟩ ⟨d, hd⟩ ⟨x * d * x⁻¹, hXD x hx d hd⟩ rfl
  rw [h3] at h2
  have h4 := QuotientGroup.eq.mp h2
  have h5 := (inferInstance : (Q.subgroupOf (E1Dpre M Q B t)).Normal).conj_mem _ h4 ⟨d, hd⟩
  rw [Subgroup.mem_subgroupOf] at h5
  convert h5 using 1
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  group

end CFSG.RankThree.GF2n.Smith81.Smith23E1
