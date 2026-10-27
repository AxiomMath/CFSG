module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.GroupTheory.SolvableMinimalNormalNode
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniMaschke
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup
open scoped Pointwise commutatorElement

section Lemmas

variable {G : Type*} [Group G]

theorem exists_minimal_normal_subgroup [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N := by
  classical
  have hfin : ({N : Subgroup G | N.Normal ∧ N ≠ ⊥} : Set (Subgroup G)).Finite := Set.toFinite _
  obtain ⟨N, hN⟩ := hfin.exists_minimal ⟨⊤, normal_top, top_ne_bot⟩
  refine ⟨N, hN.1.1, hN.1.2, fun M hMn hM hMN => ?_⟩
  exact le_antisymm hMN (hN.2 ⟨hMn, hM⟩ hMN)

theorem isPGroup_comap_mk {p : ℕ} {N : Subgroup G} [N.Normal] (hN : IsPGroup p N)
    {M : Subgroup (G ⧸ N)} (hM : IsPGroup p M) :
    IsPGroup p (M.comap (QuotientGroup.mk' N)) := by
  intro ⟨k, hk⟩
  obtain ⟨a, ha⟩ := hM ⟨QuotientGroup.mk' N k, hk⟩
  have h1 : QuotientGroup.mk' N (k ^ p ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨b, hb⟩ := hN ⟨_, h1⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have := congrArg Subtype.val hb
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul, this]

theorem le_normalizer_inf_normal (S : Subgroup G) {K : Subgroup G} (hKn : K.Normal) :
    S ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxS, hxK⟩
    exact ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), hKn.conj_mem x hxK s⟩
  · rintro ⟨hxS, hxK⟩
    refine ⟨?_, ?_⟩
    · have := S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs
      rwa [show s⁻¹ * (s * x * s⁻¹) * s = x by group] at this
    · have := hKn.conj_mem _ hxK s⁻¹
      rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this

theorem normal_map_frattini {P : Subgroup G} [hPn : P.Normal] :
    ((frattini P).map P.subtype).Normal := by
  constructor
  rintro _ ⟨y, hy, rfl⟩ g
  have h1 : (frattini P).map (MulAut.conjNormal g).toMonoidHom ≤ frattini P :=
    (characteristic_iff_map_le.1 inferInstance) _
  refine ⟨MulAut.conjNormal g y, h1 ⟨y, hy, rfl⟩, ?_⟩
  simp [MulAut.conjNormal_apply]

theorem frattini_ne_top_of_nontrivial {P : Type*} [Group P] [Finite P] [Nontrivial P] :
    frattini P ≠ ⊤ := by
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left bot_ne_top
  intro h
  exact hM.1 (top_le_iff.1 (h ▸ frattini_le_coatom hM))

theorem inf_sup_normal_of_le {N S X : Subgroup G} [hN : N.Normal] (hSX : S ≤ X) :
    X ⊓ (N ⊔ S) = (X ⊓ N) ⊔ S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxX, hxNS⟩ := Subgroup.mem_inf.1 hx
    have hxNS' : x ∈ ((N ⊔ S : Subgroup G) : Set G) := hxNS
    rw [normal_mul] at hxNS'
    obtain ⟨n, hn, s, hs, rfl⟩ := hxNS'
    have hnX : n ∈ X := by
      have := X.mul_mem hxX (X.inv_mem (hSX hs))
      simpa using this
    exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hnX, hn⟩)) (mem_sup_right hs)
  · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf hSX le_sup_right)

theorem inf_sup_eq_of_le_of_inf_eq_bot {P W S : Subgroup G} (hWP : W ≤ P)
    (hSW : S ≤ normalizer (W : Set G)) (hPS : P ⊓ S = ⊥) : P ⊓ (W ⊔ S) = W := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxWS⟩ := Subgroup.mem_inf.1 hx
    have hxWS' : x ∈ ((W ⊔ S : Subgroup G) : Set G) := hxWS
    rw [coe_mul_of_right_le_normalizer_left W S hSW] at hxWS'
    obtain ⟨w, hw, s, hs, rfl⟩ := hxWS'
    have hsP : s ∈ P := by
      have := P.mul_mem (P.inv_mem (hWP hw)) hxP
      simpa using this
    have hs1 : s = 1 := by
      have : s ∈ P ⊓ S := Subgroup.mem_inf.2 ⟨hsP, hs⟩
      rwa [hPS, mem_bot] at this
    show w * s ∈ W
    rw [hs1, mul_one]
    exact hw
  · exact le_inf hWP le_sup_left

theorem centralizes_of_trivial_on_frattini_quotient [Finite G] {r : ℕ} [Fact r.Prime]
    {P : Subgroup G} [hPn : P.Normal] (hPr : IsPGroup r P) (hr2 : r ≠ 2) {s : G}
    (hs : IsPGroup 2 (zpowers s))
    (htriv : ∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ (frattini P).map P.subtype) :
    ∀ x ∈ P, s * x * s⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := zpowers s with hAdef
  let α : A →* MulAut P := (MulAut.conjNormal : G →* MulAut P).comp A.subtype
  have hα : ∀ (a : A) (y : P), ((α a y : P) : G) = (a : G) * y * (a : G)⁻¹ := fun _ _ => rfl
  set N := frattini P with hNdef
  have hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    have h1 : N.map (MulAut.conjNormal (a : G)).toMonoidHom ≤ N :=
      (characteristic_iff_map_le.1 inferInstance) _
    exact h1 ⟨n, hn, rfl⟩
  have hcop : ¬ 2 ∣ Nat.card N := by
    intro h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPr
    have h3 : 2 ∣ r ^ k := hk ▸ h2.trans (card_subgroup_dvd_card N)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).1
      (Nat.prime_two.dvd_of_dvd_pow h3)).symm
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hs α N hN hcop
  have hgen : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN
      ⟨s, mem_zpowers s⟩ = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, MulAut.one_apply,
        QuotientGroup.eq]
      obtain ⟨z, hz, hzy⟩ := htriv _ (y⁻¹).2
      have h1 : ((α ⟨s, mem_zpowers s⟩ y)⁻¹ * y : P) = z := by
        apply Subtype.ext
        have : (z : G) = s * ((y⁻¹ : P) : G) * s⁻¹ * ((y⁻¹ : P) : G)⁻¹ := hzy
        rw [this]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hα]
        group
      rw [h1]
      exact hz
  have hall : ∀ a : A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a =
      1 := by
    rintro ⟨_, n, rfl⟩
    have : (⟨s ^ n, n, rfl⟩ : A) = (⟨s, mem_zpowers s⟩ : A) ^ n := Subtype.ext (by simp)
    rw [this, map_zpow, hgen, one_zpow]
  set C : Subgroup P :=
    { carrier := {c | ∀ a : A, α a c = c}
      mul_mem' := fun {a b} ha hb x => by rw [map_mul, ha x, hb x]
      one_mem' := fun x => map_one _
      inv_mem' := fun {a} ha x => by rw [map_inv, ha x] } with hCdef
  have hCN : C ⊔ N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : P ⧸ N) ∈ {q : P ⧸ N | ∀ a : A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a q = q} :=
      fun a => by rw [hall a, MulAut.one_apply]
    rw [hlift] at hy
    obtain ⟨c, hc, hcy⟩ := hy
    have h1 : c⁻¹ * y ∈ N := QuotientGroup.eq.1 hcy
    have : y = c * (c⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left hc) (mem_sup_right h1)
  have hCtop : C = ⊤ := frattini_nongenerating hCN
  intro x hx
  have h1 : (⟨x, hx⟩ : P) ∈ C := hCtop ▸ mem_top _
  have h2 := congrArg Subtype.val (h1 ⟨s, mem_zpowers s⟩)
  rw [hα] at h2
  exact h2

end Lemmas

section Core

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_prime_group (hG : Group.IsSolvable G) (S : Sylow 2 G) {X : Subgroup G}
    (hSX : (S : Subgroup G) ≤ X) (hXtop : X ≠ ⊤)
    (hmax : ∀ K : Subgroup G, (S : Subgroup G) ≤ K → K ≠ ⊤ → K ≤ X) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card G ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = 2 ∨ q = r := by
  classical
  by_contra hcon
  push Not at hcon
  apply hXtop
  rw [← Subgroup.index_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hqX
  have hqG : q ∣ Nat.card G := hqX.trans (Subgroup.index_dvd_card X)
  by_cases hq2 : q = 2
  · subst hq2
    exact S.not_dvd_index (hqX.trans (Subgroup.index_dvd_of_le hSX))
  · set π : Set Nat.Primes := {p | (p : ℕ) = 2 ∨ (p : ℕ) = q} with hπ
    have hSπ : CFSG.IsPiSubgroup π (S : Subgroup G) := by
      intro p hp
      left
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 S.isPGroup'
      rw [hk] at hp
      exact (Nat.prime_dvd_prime_iff_eq p.prop Nat.prime_two).1 (p.prop.dvd_of_dvd_pow hp)
    obtain ⟨K, hK, hSK⟩ := CFSG.SolvableHall.solvable_hall_containment hG π S hSπ
    by_cases hKtop : K = ⊤
    · obtain ⟨q', hq', hq'G, hq'2, hq'q⟩ := hcon q hq hq2 hqG
      have h := hK.p_in_pi_of_p_dvd_card ⟨q', hq'⟩
        (by rw [hKtop, Subgroup.card_top]; exact hq'G)
      rcases h with h | h
      · exact hq'2 h
      · exact hq'q h
    · have hKX := hmax K hSK hKtop
      exact hK.p_in_pi_of_p_dvd_index ⟨q, hq⟩ (hqX.trans (Subgroup.index_dvd_of_le hKX))
        (Or.inr rfl)

theorem pCore_ne_bot_of_two_prime (hG : Group.IsSolvable G) (S : Sylow 2 G)
    (hSn : ¬ (S : Subgroup G).Normal)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {r : ℕ} (hr : r.Prime)
    (hrq : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = 2 ∨ q = r) : CFSG.pCore r G ≠ ⊥ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hStop : (S : Subgroup G) ≠ ⊤ := fun h => hSn (h ▸ normal_top)
  have : Nontrivial G := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hStop (Subsingleton.elim _ _)
  obtain ⟨N, hNn, hN, hNmin⟩ := exists_minimal_normal_subgroup (G := G)
  obtain ⟨q, d, hq, hd, -, hNcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian hG N hN hNmin
  have hqN : q ∣ Nat.card N := hNcard ▸ dvd_pow_self q (by omega)
  have : Fact q.Prime := ⟨hq⟩
  have hNq : IsPGroup q N := IsPGroup.of_card hNcard
  rcases hrq q hq (hqN.trans (card_subgroup_dvd_card N)) with rfl | rfl
  · exact absurd (hO2 N hNn hNq) hN
  · intro hbot
    apply hN
    rw [eq_bot_iff, ← hbot]
    exact le_sSup ⟨hNn, hNq⟩

theorem sup_eq_top_of_two_prime (hG : Group.IsSolvable G) (S : Sylow 2 G)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {X : Subgroup G}
    (hXtop : X ≠ ⊤) (hmax : ∀ K : Subgroup G, (S : Subgroup G) ≤ K → K ≠ ⊤ → K ≤ X) {r : ℕ}
    (hr : r.Prime) (hrq : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = 2 ∨ q = r)
    {P : Subgroup G} [hPn : P.Normal] (hPr : IsPGroup r P)
    (hleP : ∀ K : Subgroup G, K.Normal → IsPGroup r K → K ≤ P) :
    P ⊔ (S : Subgroup G) = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hPS
  have hPSX : P ⊔ (S : Subgroup G) ≤ X := hmax _ le_sup_right hPS
  have hPtop : P ≠ ⊤ := fun h => hPS (by rw [h, top_sup_eq])
  set π := QuotientGroup.mk' P with hπ
  have : Nontrivial (G ⧸ P) := QuotientGroup.nontrivial_iff.2 hPtop
  have hGP : Group.IsSolvable (G ⧸ P) := inferInstance
  obtain ⟨Nb, hNbn, hNb, hNbmin⟩ := exists_minimal_normal_subgroup (G := G ⧸ P)
  obtain ⟨q, d, hq, hd, -, hNbcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian hGP Nb hNb hNbmin
  have : Fact q.Prime := ⟨hq⟩
  have hNbq : IsPGroup q Nb := IsPGroup.of_card hNbcard
  have hqG : q ∣ Nat.card G := by
    have h1 : q ∣ Nat.card Nb := hNbcard ▸ dvd_pow_self q (by omega)
    have h2 : Nat.card (G ⧸ P) ∣ Nat.card G := by
      rw [card_eq_card_quotient_mul_card_subgroup P]
      exact dvd_mul_right _ _
    exact (h1.trans (card_subgroup_dvd_card Nb)).trans h2
  set K := Nb.comap π with hKdef
  have hKn : K.Normal := Normal.comap hNbn π
  have hPK : P ≤ K := by
    intro x hx
    show π x ∈ Nb
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hmapK : K.map π = Nb :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective P) _
  have hNbbot : ∀ L : Subgroup G, K ≤ L → L ≤ P → False := by
    intro L hKL hLP
    apply hNb
    rw [← hmapK, eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hLP (hKL hk)
  rcases hrq q hq hqG with rfl | rfl
  ·
    have hNbS : Nb ≤ ((S.mapSurjective (QuotientGroup.mk'_surjective P) : Sylow 2 (G ⧸ P)) :
        Subgroup (G ⧸ P)) := hNbq.le_sylow_of_normal _
    have hKPS : K ≤ P ⊔ (S : Subgroup G) := by
      intro k hk
      obtain ⟨s, hs, hsk⟩ := hNbS hk
      have h1 : s⁻¹ * k ∈ P := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (s : G ⧸ P) = (k : G ⧸ P) := hsk
        rw [this, inv_mul_cancel]
      have : k = s * (s⁻¹ * k) := by group
      rw [this]
      exact mul_mem (mem_sup_right hs) (mem_sup_left h1)
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup G) ⊓ K) K := by
      refine CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (K := ⊤) ?_ le_top
        (by rw [normalizer_eq_top_iff.2 hKn])
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, S.isPGroup', ?_⟩
      rw [relIndex_top_right]
      exact S.not_dvd_index
    obtain ⟨Q, hQ⟩ := hSyl
    have hfrat := Sylow.normalizer_sup_eq_top (N := K) Q
    rw [hQ] at hfrat
    have hSN := le_normalizer_inf_normal (S : Subgroup G) hKn
    by_cases hNtop : normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) = ⊤
    · have hSK1 : (S : Subgroup G) ⊓ K = ⊥ :=
        hO2 _ (normalizer_eq_top_iff.1 hNtop) (S.isPGroup'.to_le inf_le_left)
      refine hNbbot K le_rfl fun k hk => ?_
      obtain ⟨p, hp, s, hs, rfl⟩ : k ∈ (P : Set G) * ((S : Subgroup G) : Set G) := by
        rw [← normal_mul]
        exact hKPS hk
      have hsK : s ∈ K := by
        have : s = p⁻¹ * (p * s) := by group
        rw [this]
        exact mul_mem (inv_mem (hPK hp)) hk
      have hs1 : s = 1 := by
        have : s ∈ (S : Subgroup G) ⊓ K := ⟨hs, hsK⟩
        rwa [hSK1, mem_bot] at this
      show p * s ∈ P
      rw [hs1, mul_one]
      exact hp
    · have h1 := hmax _ hSN hNtop
      apply hXtop
      rw [eq_top_iff, ← hfrat]
      exact sup_le h1 (hKPS.trans hPSX)
  ·
    exact hNbbot K le_rfl (hleP K hKn (isPGroup_comap_mk hPr hNbq))

theorem inf_eq_frattini_of_unique {r : ℕ} [Fact r.Prime] {P S X : Subgroup G} [hPn : P.Normal]
    (hPr : IsPGroup r P) (hS2 : IsPGroup 2 S) (hr2 : r ≠ 2) (hPS : P ⊔ S = ⊤)
    (hPSbot : P ⊓ S = ⊥) (hSX : S ≤ X) (hXtop : X ≠ ⊤)
    (hmax : ∀ K : Subgroup G, S ≤ K → K ≠ ⊤ → K ≤ X)
    (hΦX : (frattini P).map P.subtype ≤ X) :
    X ⊓ P = (frattini P).map P.subtype := by
  classical
  let α : S →* MulAut P := (MulAut.conjNormal : G →* MulAut P).comp S.subtype
  let : MulDistribMulAction S P := MulDistribMulAction.compHom P α
  have hsmul : ∀ (s : S) (x : P), ((s • x : P) : G) = (s : G) * x * (s : G)⁻¹ :=
    fun _ _ => rfl
  have hcop : Nat.Coprime r (Nat.card S) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out Nat.prime_two).2 hr2)
  set M := (X ⊓ P).subgroupOf P with hM
  have hΦM : frattini P ≤ M := by
    intro y hy
    rw [hM, mem_subgroupOf]
    exact ⟨hΦX ⟨y, hy, rfl⟩, y.2⟩
  have hfratinv : ∀ s : S, ∀ x ∈ frattini P, s • x ∈ frattini P := by
    intro s x hx
    have h1 : (frattini P).map (MulAut.conjNormal (s : G)).toMonoidHom ≤ frattini P :=
      (characteristic_iff_map_le.1 inferInstance) _
    exact h1 ⟨x, hx, rfl⟩
  have hMinv : ∀ s : S, ∀ x ∈ M, s • x ∈ M := by
    intro s x hx
    rw [hM, mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact ⟨X.mul_mem (X.mul_mem (hSX s.2) hx.1) (X.inv_mem (hSX s.2)),
      hPn.conj_mem _ hx.2 _⟩
  obtain ⟨W', hΦW', hW'inv, hMW', hMW'inf⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.exists_invariant_complement_section (p := r) hcop
      hΦM (CFSG.SectionRank.Ccomm.pow_mem_frattini hPr) (fun x y => by
        have := CFSG.SectionRank.Ccomm.commutator_mem_frattini hPr x y
        rwa [commutatorElement_def] at this) hfratinv hMinv
  set W := W'.map P.subtype with hW
  have hWP : W ≤ P := map_subtype_le _
  have hSW : S ≤ normalizer (W : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(⟨s, hs⟩ : S) • y, hW'inv _ y hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨(⟨s, hs⟩⁻¹ : S) • y, hW'inv _ y hy, ?_⟩
      have hyx' : (y : G) = s * x * s⁻¹ := hyx
      show (((⟨s, hs⟩⁻¹ : S) • y : P) : G) = x
      rw [hsmul, hyx']
      change s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x
      group
  by_contra hne
  have hW'top : W' ≠ ⊤ := by
    intro h
    apply hne
    rw [h, inf_top_eq] at hMW'inf
    ext x
    constructor
    · intro hx
      have : (⟨x, hx.2⟩ : P) ∈ M := by rw [hM, mem_subgroupOf]; exact hx
      rw [hMW'inf] at this
      exact ⟨_, this, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hΦX ⟨y, hy, rfl⟩, y.2⟩
  have hWS : W ⊔ S ≠ ⊤ := by
    intro h
    apply hW'top
    have h1 := inf_sup_eq_of_le_of_inf_eq_bot hWP hSW hPSbot
    rw [h, inf_top_eq] at h1
    rw [eq_top_iff]
    intro y _
    have : (y : G) ∈ W := h1 ▸ y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [show z = y from Subtype.ext hzy] at hz
  have hWX : W ≤ X := le_sup_left.trans (hmax _ le_sup_right hWS)
  have hW'M : W' ≤ M := by
    intro y hy
    rw [hM, mem_subgroupOf]
    exact ⟨hWX ⟨y, hy, rfl⟩, y.2⟩
  rw [sup_eq_left.2 hW'M] at hMW'
  apply hXtop
  rw [eq_top_iff, ← hPS]
  refine sup_le (fun x hx => ?_) hSX
  have : (⟨x, hx⟩ : P) ∈ M := by rw [hMW']; exact mem_top _
  rw [hM, mem_subgroupOf] at this
  exact this.1

theorem solvable_unique_overgroup_core (hG : Group.IsSolvable G) (S : Sylow 2 G)
    (hSn : ¬ (S : Subgroup G).Normal)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {X : Subgroup G}
    (hSX : (S : Subgroup G) ≤ X) (hXtop : X ≠ ⊤)
    (hmax : ∀ K : Subgroup G, (S : Subgroup G) ≤ K → K ≠ ⊤ → K ≤ X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ P : Subgroup G, P ≠ ⊥ ∧ P.Normal ∧ IsPGroup p P ∧
      P ⊔ (S : Subgroup G) = ⊤ ∧ P ⊓ (S : Subgroup G) = ⊥ ∧
      (frattini P).map P.subtype ≠ P ∧
      (∀ s ∈ (S : Subgroup G), (∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ (frattini P).map P.subtype) →
        s = 1) ∧
      (∀ W : Subgroup G, (frattini P).map P.subtype ≤ W → W ≤ P →
        (S : Subgroup G) ≤ normalizer (W : Set G) →
        W = (frattini P).map P.subtype ∨ W = P) ∧
      X = (frattini P).map P.subtype ⊔ (S : Subgroup G) ∧
      X.normalCore = (frattini P).map P.subtype := by
  classical
  obtain ⟨r, hr, hr2, -, hrq⟩ := exists_two_prime_group hG S hSX hXtop hmax
  have : Fact r.Prime := ⟨hr⟩
  set P := CFSG.pCore r G with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  have hPr : IsPGroup r P := CFSG.pCore_isPGroup
  have hleP : ∀ K : Subgroup G, K.Normal → IsPGroup r K → K ≤ P := fun K hK hKr =>
    le_sSup ⟨hK, hKr⟩
  have hP1 : P ≠ ⊥ := pCore_ne_bot_of_two_prime hG S hSn hO2 hr hrq
  have hPS : P ⊔ (S : Subgroup G) = ⊤ :=
    sup_eq_top_of_two_prime hG S hO2 hXtop hmax hr hrq hPr hleP
  have hPSbot : P ⊓ (S : Subgroup G) = ⊥ := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hPr
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 S.isPGroup'
    have h1 : Nat.card (P ⊓ (S : Subgroup G) : Subgroup G) ∣ r ^ a :=
      ha ▸ card_dvd_of_le inf_le_left
    have h2 : Nat.card (P ⊓ (S : Subgroup G) : Subgroup G) ∣ 2 ^ b :=
      hb ▸ card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (r ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    exact (card_eq_one).1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  set Φ := (frattini P).map P.subtype with hΦdef
  have hΦn : Φ.Normal := normal_map_frattini
  have hΦP : Φ ≤ P := map_subtype_le _
  have hΦneP : Φ ≠ P := by
    intro h
    have : Nontrivial P := (nontrivial_iff_ne_bot P).2 hP1
    apply frattini_ne_top_of_nontrivial (P := P)
    rw [eq_top_iff]
    intro y _
    have : (y : G) ∈ Φ := by rw [h]; exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [show z = y from Subtype.ext hzy] at hz
  have hsec : ∀ W : Subgroup G, W ≤ P → (S : Subgroup G) ≤ normalizer (W : Set G) → W ≠ P →
      W ≤ X := by
    intro W hWP hSW hne
    have hWS : W ⊔ (S : Subgroup G) ≠ ⊤ := by
      intro h
      apply hne
      have h1 := inf_sup_eq_of_le_of_inf_eq_bot hWP hSW hPSbot
      rw [h, inf_top_eq] at h1
      exact h1.symm
    exact le_sup_left.trans (hmax _ le_sup_right hWS)
  have hΦX : Φ ≤ X := hsec Φ hΦP (fun s _ => normalizer_eq_top_iff.2 hΦn ▸ mem_top s) hΦneP
  have hXP : X ⊓ P = Φ :=
    inf_eq_frattini_of_unique hPr S.isPGroup' hr2 hPS hPSbot hSX hXtop hmax hΦX
  have hfaith : ∀ s ∈ (S : Subgroup G), (∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ Φ) → s = 1 := by
    intro s hs htriv
    have hs2 : IsPGroup 2 (zpowers s) := S.isPGroup'.to_le (zpowers_le.2 hs)
    have hcent := centralizes_of_trivial_on_frattini_quotient hPr hr2 hs2 htriv
    set D := (S : Subgroup G) ⊓ centralizer (P : Set G) with hD
    have hCn : (centralizer (P : Set G)).Normal := inferInstance
    have hDn : D.Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff, ← hPS]
      refine sup_le (fun p hp => ?_) (le_normalizer_inf_normal _ hCn)
      rw [mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        have hdp : p * d = d * p := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 p hp
        rwa [show p * d * p⁻¹ = d by rw [hdp]; group]
      · intro hd
        have hep : p * (p * d * p⁻¹) = (p * d * p⁻¹) * p :=
          mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 p hp
        have : d = p * d * p⁻¹ := by
          calc d = p⁻¹ * ((p * d * p⁻¹) * p) := by group
            _ = p⁻¹ * (p * (p * d * p⁻¹)) := by rw [hep]
            _ = p * d * p⁻¹ := by group
        rw [this]
        exact hd
    have hD1 : D = ⊥ := hO2 D hDn (S.isPGroup'.to_le inf_le_left)
    have hsD : s ∈ D := Subgroup.mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun x hx => by
      have := hcent x hx
      calc x * s = s * x * s⁻¹ * s := by rw [this]
        _ = s * x := by group⟩
    rwa [hD1, mem_bot] at hsD
  have hX : X = Φ ⊔ (S : Subgroup G) := by
    calc X = X ⊓ (P ⊔ (S : Subgroup G)) := by rw [hPS, inf_top_eq]
      _ = (X ⊓ P) ⊔ (S : Subgroup G) := inf_sup_normal_of_le hSX
      _ = Φ ⊔ (S : Subgroup G) := by rw [hXP]
  refine ⟨r, hr, hr2, P, hP1, hPn, hPr, hPS, hPSbot, hΦneP, hfaith, ?_, hX, ?_⟩
  · intro W hΦW hWP hSW
    by_cases hW : W = P
    · exact Or.inr hW
    · have h1 := le_inf (hsec W hWP hSW hW) hWP
      rw [hXP] at h1
      exact Or.inl (le_antisymm h1 hΦW)
  · apply le_antisymm
    · intro d hd
      have hdX : d ∈ X := normalCore_le X hd
      have hdΦS : d ∈ ((Φ ⊔ (S : Subgroup G) : Subgroup G) : Set G) := hX ▸ hdX
      rw [normal_mul] at hdΦS
      obtain ⟨f, hf, s, hs, rfl⟩ := hdΦS
      have hs1 : s = 1 := by
        refine hfaith s hs fun x hx => ?_
        have hc : f * s * x * (f * s)⁻¹ * x⁻¹ ∈ X ⊓ P := by
          refine Subgroup.mem_inf.2 ⟨normalCore_le X ?_, ?_⟩
          · have hcore : (X.normalCore).Normal := normalCore_normal X
            have h1 := hcore.conj_mem _ (inv_mem hd) x
            have h2 := mul_mem hd h1
            simpa [mul_assoc] using h2
          · have h1 := hPn.conj_mem x hx (f * s)
            exact mul_mem h1 (inv_mem hx)
        rw [hXP] at hc
        have hfx : x * f * x⁻¹ ∈ Φ := hΦn.conj_mem f hf x
        have := mul_mem (mul_mem (inv_mem hf) hc) hfx
        have heq : f⁻¹ * (f * s * x * (f * s)⁻¹ * x⁻¹) * (x * f * x⁻¹) =
            s * x * s⁻¹ * x⁻¹ := by group
        rwa [heq] at this
      show f * s ∈ Φ
      rw [hs1, mul_one]
      exact hf
    · exact (normal_le_normalCore).2 hΦX

end Core

theorem A7_solvable_unique_Sylow_overgroup_structure {H : Type*} [Group H] [Finite H]
    (hH : Group.IsSolvable H) (T : Sylow 2 H) (hTn : ¬ (T : Subgroup H).Normal)
    {X : Subgroup H} (hX : IsCoatom X) (hTX : (T : Subgroup H) ≤ X)
    (huniq : ∀ Y : Subgroup H, IsCoatom Y → (T : Subgroup H) ≤ Y → Y = X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ P : Subgroup (H ⧸ CFSG.pCore 2 H), P ≠ ⊥ ∧ P.Normal ∧
      IsPGroup p P ∧
      P ⊔ (T : Subgroup H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) = ⊤ ∧
      P ⊓ (T : Subgroup H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) = ⊥ ∧
      (frattini P).map P.subtype ≠ P ∧
      (∀ s ∈ (T : Subgroup H).map (QuotientGroup.mk' (CFSG.pCore 2 H)),
        (∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ (frattini P).map P.subtype) → s = 1) ∧
      (∀ W : Subgroup (H ⧸ CFSG.pCore 2 H), (frattini P).map P.subtype ≤ W → W ≤ P →
        (T : Subgroup H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ normalizer (W : Set _) →
        W = (frattini P).map P.subtype ∨ W = P) ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
        (frattini P).map P.subtype ⊔ (T : Subgroup H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) ∧
      (X.map (QuotientGroup.mk' (CFSG.pCore 2 H))).normalCore = (frattini P).map P.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.pCore 2 H with hRdef
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup
  have hleR : ∀ K : Subgroup H, K.Normal → IsPGroup 2 K → K ≤ R := fun K hK hK2 =>
    le_sSup ⟨hK, hK2⟩
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hkerπ : π.ker = R := QuotientGroup.ker_mk' R
  have hRT : R ≤ (T : Subgroup H) := hR2.le_sylow_of_normal T
  set SS : Sylow 2 (H ⧸ R) := T.mapSurjective hπs with hSS
  have hSScoe : (SS : Subgroup (H ⧸ R)) = (T : Subgroup H).map π := rfl
  have hO2 : ∀ N : Subgroup (H ⧸ R), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hNn hN2
    have hK := hleR _ (hNn.comap π) (isPGroup_comap_mk hR2 hN2)
    rw [eq_bot_iff, ← map_comap_eq_self_of_surjective hπs N]
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_bot, ← MonoidHom.mem_ker, hkerπ]
    exact hK hk
  have hSn : ¬ (SS : Subgroup (H ⧸ R)).Normal := by
    intro h
    apply hTn
    have h1 := h.comap π
    rw [hSScoe, comap_map_eq, hkerπ, sup_eq_left.2 hRT] at h1
    exact h1
  have hSX : (SS : Subgroup (H ⧸ R)) ≤ X.map π := map_mono hTX
  have hRX : R ≤ X := hRT.trans hTX
  have hXtop : X.map π ≠ ⊤ := by
    intro h
    apply hX.1
    have h1 := congrArg (Subgroup.comap π) h
    rwa [comap_map_eq, hkerπ, sup_eq_left.2 hRX, comap_top] at h1
  have hmax : ∀ K : Subgroup (H ⧸ R), (SS : Subgroup (H ⧸ R)) ≤ K → K ≠ ⊤ → K ≤ X.map π := by
    intro K hSK hKtop
    have hTK : (T : Subgroup H) ≤ K.comap π :=
      (le_comap_map π (T : Subgroup H)).trans (comap_mono hSK)
    have hKtop' : K.comap π ≠ ⊤ := by
      intro h
      apply hKtop
      rw [← map_comap_eq_self_of_surjective hπs K, h, map_top_of_surjective π hπs]
    obtain ⟨Y, hY, hKY⟩ := (eq_top_or_exists_le_coatom (K.comap π)).resolve_left hKtop'
    have hYX : Y = X := huniq Y hY (hTK.trans hKY)
    rw [← map_comap_eq_self_of_surjective hπs K]
    exact map_mono (hYX ▸ hKY)
  exact solvable_unique_overgroup_core inferInstance SS hSn hO2 hSX hXtop hmax

end CFSG.Quasithin.H13.A7
