module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveFourteen

theorem le_centralizer_of_isTI {A U : Subgroup G} (hA : IsElemAbelian 2 A)
    (hU : IsElemAbelian 2 U) (hTI : IsTI A) (hAU : A ≤ normalizer (U : Set G))
    (hbot : A ⊓ U = ⊥) (hcard : Nat.card U ≤ Nat.card A) :
    A ≤ centralizer (U : Set G) := by
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => by
    have h2 := hA.2 a ha
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_left h2
  have hUinv : ∀ x ∈ U, x⁻¹ = x := fun x hx => by
    have h2 := hU.2 x hx
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_left h2
  have hconjU : ∀ a ∈ A, ∀ x ∈ U, a * x * a⁻¹ ∈ U := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAU ha) x).mp hx
  have key : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ U, u * a = a * u → ∀ b ∈ A, u * b = b * u := by
    intro a ha ha1 u hu hua b hb
    have hmem : a ∈ A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup u A := by
      refine ⟨ha, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_⟩
      have h0 : u⁻¹ * a * u = a := by
        calc u⁻¹ * a * u = u⁻¹ * (u * a) := by rw [mul_assoc, ← hua]
          _ = a := by group
      rw [h0]
      exact ha
    have hne : A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup u A ≠ ⊥ := fun h => by
      rw [h] at hmem
      exact ha1 (Subgroup.mem_bot.mp hmem)
    have heq : A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup u A = A := (hTI u).resolve_left hne
    have hbc : b ∈ CFSG.CGT.Timmesfeld75.conjSubgroup u A := by
      have : b ∈ A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup u A := heq.symm ▸ hb
      exact this.2
    have hb' : u⁻¹ * b * u ∈ A := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hbc
    have hcA : b⁻¹ * (u⁻¹ * b * u) ∈ A := A.mul_mem (A.inv_mem hb) hb'
    have hcU : b⁻¹ * (u⁻¹ * b * u) ∈ U := by
      have h1 : b⁻¹ * u⁻¹ * b⁻¹⁻¹ ∈ U := hconjU _ (A.inv_mem hb) _ (U.inv_mem hu)
      have h2 : b⁻¹ * (u⁻¹ * b * u) = (b⁻¹ * u⁻¹ * b⁻¹⁻¹) * u := by group
      rw [h2]
      exact U.mul_mem h1 hu
    have hc1 : b⁻¹ * (u⁻¹ * b * u) = 1 := by
      have : b⁻¹ * (u⁻¹ * b * u) ∈ A ⊓ U := ⟨hcA, hcU⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h3 : u⁻¹ * b * u = b := by
      have := congrArg (fun y => b * y) hc1
      simpa [mul_assoc] using this
    calc u * b = u * (u⁻¹ * b * u) := by rw [h3]
      _ = b * u := by group
  rw [Subgroup.le_centralizer_iff]
  by_contra hnot
  obtain ⟨x, hxU, hxA⟩ := Set.not_subset.mp hnot
  set C : Subgroup G := U ⊓ centralizer (A : Set G) with hCdef
  have hfU : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ U := fun a ha =>
    U.mul_mem (hconjU a ha x hxU) (U.inv_mem hxU)
  have hfcomm : ∀ a ∈ A, (a * x * a⁻¹ * x⁻¹) * a = a * (a * x * a⁻¹ * x⁻¹) := by
    intro a ha
    have hy : a * x * a⁻¹ ∈ U := hconjU a ha x hxU
    have hyx := hUc _ hy x hxU
    rw [hAinv a ha, hUinv x hxU] at *
    have haa : a * a = 1 := by
      have h2 := hA.2 a ha
      rwa [pow_two] at h2
    calc a * x * a * x * a = (a * x * a) * x * a := by group
      _ = x * (a * x * a) * a := by rw [hyx]
      _ = x * a * x * (a * a) := by group
      _ = x * a * x := by rw [haa, mul_one]
      _ = (a * a) * x * a * x := by rw [haa, one_mul]
      _ = a * (a * x * a * x) := by group
  have hfC : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ C := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hfU a ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    by_cases ha1 : a = 1
    · subst ha1
      simp
    · exact (key a ha ha1 _ (hfU a ha) (hfcomm a ha) b hb).symm
  let f : A → C := fun a => ⟨a * x * a⁻¹ * x⁻¹, hfC a a.2⟩
  have hf : Function.Injective f := by
    intro a a' h
    have h1 : (a : G) * x * (a : G)⁻¹ * x⁻¹ = (a' : G) * x * (a' : G)⁻¹ * x⁻¹ :=
      congrArg Subtype.val h
    have h2 : ((a' : G)⁻¹ * a) * x = x * ((a' : G)⁻¹ * a) := by
      have h3 : (a : G) * x * (a : G)⁻¹ = (a' : G) * x * (a' : G)⁻¹ := by
        simpa using h1
      calc ((a' : G)⁻¹ * a) * x = (a' : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * a := by group
        _ = (a' : G)⁻¹ * ((a' : G) * x * (a' : G)⁻¹) * a := by rw [h3]
        _ = x * ((a' : G)⁻¹ * a) := by group
    by_contra hne
    have hc1 : (a' : G)⁻¹ * a ≠ 1 := by
      intro h4
      apply hne
      exact Subtype.ext (inv_mul_eq_one.mp h4).symm
    apply hxA
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact (key _ (A.mul_mem (A.inv_mem a'.2) a.2) hc1 x hxU h2.symm b hb).symm
  have hAC : Nat.card A ≤ Nat.card C := Nat.card_le_card_of_injective f hf
  have hCU : C = U := Subgroup.eq_of_le_of_card_ge inf_le_left (hcard.trans hAC)
  apply hxA
  have : x ∈ C := hCU.symm ▸ hxU
  exact this.2

theorem four_le_and_eq_three {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ 2 = 1) {n : ℕ}
    (hcard : Nat.card W = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ^ 2 ∣ Nat.card (MulAut W)) : 4 ≤ n ∧ (n ≤ 4 → n = 4 ∧ p = 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod] at hdvd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hsq : 9 ≤ p ^ 2 := by nlinarith
  have key : n ≤ 4 → n = 4 ∧ p = 3 := by
    intro hn
    interval_cases n
    · simp at hdvd
      omega
    · simp [Fin.prod_univ_succ] at hdvd
      omega
    · simp [Fin.prod_univ_succ] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · simp [Fin.prod_univ_succ] at hdvd
      have h168 : p ∣ 168 := (dvd_pow_self p two_ne_zero).trans hdvd
      have hp' : p ∣ 2 ^ 3 * 3 * 7 := by norm_num; exact h168
      rcases (Nat.Prime.dvd_mul hp).1 hp' with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
            (hp.dvd_of_dvd_pow h)) hp2
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
          subst this
          norm_num at hdvd
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h
        subst this
        norm_num at hdvd
    · simp [Fin.prod_univ_succ] at hdvd
      have h20160 : p ∣ 20160 := (dvd_pow_self p two_ne_zero).trans hdvd
      have hp' : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num; exact h20160
      refine ⟨rfl, ?_⟩
      rcases (Nat.Prime.dvd_mul hp).1 hp' with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
              (hp.dvd_of_dvd_pow h)) hp2
          · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h
          subst this
          norm_num at hdvd
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h
        subst this
        norm_num at hdvd
  refine ⟨?_, key⟩
  by_contra hlt
  exact absurd (key (by omega)).1 (by omega)

theorem sq_dvd_card_mulAut {p : ℕ} (hp : p.Prime) {M V : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G))
    (h : 1 < F12.pRankMod p M (centralizer (V : Set G))) :
    p ^ 2 ∣ Nat.card (MulAut V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hN : ((centralizer (V : Set G)).subgroupOf M).Normal := kerAct_normal M V hMV
  have hr : 1 < CFSG.Open.pRank p
      (⊤ : Subgroup (↥M ⧸ (centralizer (V : Set G)).subgroupOf M)) := by
    unfold F12.pRankMod at h
    rwa [dif_pos hN] at h
  obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (⊤ : Subgroup (↥M ⧸ (centralizer (V : Set G)).subgroupOf M))
  have hker : (uc22br4_conjAut M V hMV).ker = (centralizer (V : Set G)).subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hm v hv
      have h1 : (m : G) * v * (m : G)⁻¹ = v :=
        congrArg (fun f : MulAut V => ((f ⟨v, hv⟩ : V) : G)) hm
      calc v * (m : G) = (m : G) * v * (m : G)⁻¹ * m := by rw [h1]
        _ = (m : G) * v := by group
    · intro hm
      ext v
      show (m : G) * v * (m : G)⁻¹ = v
      rw [← hm v v.2, mul_inv_cancel_right]
  have hcard : Nat.card (↥M ⧸ (centralizer (V : Set G)).subgroupOf M) =
      Nat.card (uc22br4_conjAut M V hMV).range :=
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv).symm.trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange (uc22br4_conjAut M V hMV)).toEquiv)
  have h1 : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p (by omega)
  exact h1.trans (((Subgroup.card_subgroup_dvd_card E).trans (dvd_of_eq hcard)).trans
    (Subgroup.card_subgroup_dvd_card _))

private theorem frattini_quot {H : Type*} [Group H] [Finite H] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] {K S : Subgroup H} [K.Normal] (hS : CFSG.ABGLocalTools.IsSylowOf q S K)
    {Q : Subgroup (H ⧸ K)} (hQp : IsPGroup p Q) (hnc : ¬ IsCyclic Q) :
    ∃ X : Subgroup H, IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ Subgroup.normalizer (S : Set H) := by
  classical
  obtain ⟨S₀, rfl⟩ := hS
  set N : Subgroup H := Subgroup.normalizer ((S₀.map K.subtype : Subgroup H) : Set H) with hN
  have hF : N ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top S₀
  set π : H →* H ⧸ K := QuotientGroup.mk' K with hπ
  set W : Subgroup H := N ⊓ Q.comap π with hW
  have hπW : W.map π = Q := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro y' hy'
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K y'
      have hy : y ∈ N ⊔ K := hF ▸ Subgroup.mem_top y
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      have hπ1 : π (n * k) = π n := by
        rw [map_mul, hk1, mul_one]
      refine ⟨n, ⟨hn, ?_⟩, hπ1.symm⟩
      show π n ∈ Q
      rw [← hπ1]
      exact hy'
  obtain ⟨X₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥W))
  set X : Subgroup H := (X₀ : Subgroup ↥W).map W.subtype with hX
  have hXW : X ≤ W := Subgroup.map_subtype_le _
  have hWQ : ∀ w : ↥W, π (w : H) ∈ Q := fun w => w.2.2
  let f : ↥W →* ↥Q := (π.comp W.subtype).codRestrict Q hWQ
  have hf : Function.Surjective f := by
    rintro ⟨q', hq'⟩
    rw [← hπW] at hq'
    obtain ⟨w, hw, hwq⟩ := hq'
    exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
  have htop : ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) = ⊤ := by
    symm
    exact (X₀.mapSurjective hf).is_maximal' (hQp.of_equiv Subgroup.topEquiv.symm) le_top
  have hsurj : ∀ q' ∈ Q, ∃ x ∈ X, π x = q' := by
    intro q' hq'
    have h1 : (⟨q', hq'⟩ : ↥Q) ∈ ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) := by
      rw [htop]; trivial
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxq⟩ := h1
    exact ⟨(x : H), ⟨x, hx, rfl⟩, congrArg Subtype.val hxq⟩
  refine ⟨X, X₀.isPGroup'.map W.subtype, ?_, fun x hx => (hXW hx).1⟩
  intro hXc
  apply hnc
  let g : ↥X →* ↥Q := (π.comp X.subtype).codRestrict Q (fun x => (hXW x.2).2)
  have hg : Function.Surjective g := by
    rintro ⟨q', hq'⟩
    obtain ⟨x, hx, hxq⟩ := hsurj q' hq'
    exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
  exact isCyclic_of_surjective g hg

theorem exists_noncyclic_le_normalizer {p : ℕ} (hp : p.Prime) {M V S : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (M ⊓ centralizer (V : Set G)))
    (h : 1 < F12.pRankMod p M (centralizer (V : Set G))) :
    ∃ X : Subgroup G, X ≤ M ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ normalizer (S : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : ((centralizer (V : Set G)).subgroupOf M).Normal := kerAct_normal M V hMV
  have hr : 1 < CFSG.Open.pRank p
      (⊤ : Subgroup (↥M ⧸ (centralizer (V : Set G)).subgroupOf M)) := by
    unfold F12.pRankMod at h
    rwa [dif_pos hN] at h
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (⊤ : Subgroup (↥M ⧸ (centralizer (V : Set G)).subgroupOf M))
  have hEp : IsPGroup p E := uc22p22e_isPGroup_of_elem hE
  have hEc : ¬ IsCyclic E := uc22p22n_not_isCyclic_of_card hp hE (by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos (by omega))
  obtain ⟨hSK, hSp, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSM : S ≤ M := hSK.trans inf_le_left
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf M)
      ((centralizer (V : Set G)).subgroupOf M) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => (hSK hx).2, hSp.comap_subtype, ?_⟩
    rwa [← inf_subgroupOf_left (centralizer (V : Set G)) M,
      Subgroup.relIndex_subgroupOf inf_le_left]
  obtain ⟨X', hX'p, hX'nc, hX'N⟩ := frattini_quot hS' hEp hEc
  refine ⟨X'.map M.subtype, Subgroup.map_subtype_le _, hX'p.map _, ?_, ?_⟩
  · intro hc
    exact hX'nc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective X' M.subtype M.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective X' M.subtype M.subtype_injective).injective)
  · rintro _ ⟨x', hx', rfl⟩
    have hx'N := hX'N hx'
    rw [Subgroup.mem_normalizer_iff] at hx'N ⊢
    intro y
    constructor
    · intro hy
      exact (hx'N ⟨y, hSM hy⟩).1 hy
    · intro hy
      have hyM : y ∈ M := by
        have h1 : (x' : G) * y * (x' : G)⁻¹ ∈ M := hSM hy
        have := M.mul_mem (M.mul_mem (M.inv_mem x'.2) h1) x'.2
        simpa [mul_assoc] using this
      exact (hx'N ⟨y, hyM⟩).2 hy

theorem pCoreOf_ne_bot_of_normal (hchar : IsCharTwoType G) {W X : Subgroup G} (hW : W ≠ ⊥)
    (hW2 : IsPGroup 2 W) (hX : X ≠ ⊥) (hXW : X ≤ normalizer (W : Set G))
    (hWX : normalizer (W : Set G) ≤ normalizer (X : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hO
  have hON : pCoreOf 2 (normalizer (W : Set G)) ≤ normalizer (W : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hNO : normalizer (W : Set G) ≤
      normalizer (pCoreOf 2 (normalizer (W : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hcent : normalizer (W : Set G) ⊓
      centralizer (pCoreOf 2 (normalizer (W : Set G)) : Set G) ≤
        pCoreOf 2 (normalizer (W : Set G)) :=
    hchar _ ⟨W, hW, hW2, rfl⟩
  have hY : X ⊓ pCoreOf 2 (normalizer (W : Set G)) ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyX, hyO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) y).1 hyX,
        (Subgroup.mem_normalizer_iff.1 (hNO (hXW hx)) y).1 hyO⟩
    · rintro ⟨hyX, hyO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) y).2 hyX,
        (Subgroup.mem_normalizer_iff.1 (hNO (hXW hx)) y).2 hyO⟩
  rw [hO] at hY
  have hXC : X ≤ centralizer (pCoreOf 2 (normalizer (W : Set G)) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have h0 : y * x⁻¹ * y⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (hWX (hON hy)) x⁻¹).1 (X.inv_mem hx)
      have h2 := X.mul_mem hx h0
      simpa [mul_assoc] using h2
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (normalizer (W : Set G)) := by
      have h0 : x * y * x⁻¹ ∈ pCoreOf 2 (normalizer (W : Set G)) :=
        (Subgroup.mem_normalizer_iff.1 (hNO (hXW hx)) y).1 hy
      exact Subgroup.mul_mem _ h0 (Subgroup.inv_mem _ hy)
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.1 (hY ⟨h1, h2⟩)
    have h4 : x * y = y * x := by
      have := congrArg (· * (y * x)) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hXO : X ≤ pCoreOf 2 (normalizer (W : Set G)) := (le_inf hXW hXC).trans hcent
  exact hX (eq_bot_iff.2 fun x hx => hY ⟨hx, hXO hx⟩)

end TwelveFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
