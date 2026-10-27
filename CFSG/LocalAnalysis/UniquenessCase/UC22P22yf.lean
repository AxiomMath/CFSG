module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ye
import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

namespace P22y

@[expose] def powHomOfComm {A : Type} [Group A] (hA : ∀ a b : A, a * b = b * a) (n : ℕ) : A →* A where
  toFun a := a ^ n
  map_one' := one_pow n
  map_mul' a b := (Commute.mul_pow (hA a b) n)

theorem card_le_card_ker_pow {A E : Type} [Group A] [Finite A] [Group E] {p : ℕ}
    (hA : ∀ a b : A, a * b = b * a) (g : A →* E) (hg : Function.Surjective g)
    (hE : ∀ x : E, x ^ p = 1) : Nat.card E ≤ Nat.card ↥(powHomOfComm hA p).ker := by
  set c := powHomOfComm hA p with hc
  have h1 := Subgroup.card_ker_mul_card_range c
  have h2 := Subgroup.card_ker_mul_card_range g
  have hrange : g.range = ⊤ := MonoidHom.range_eq_top.2 hg
  rw [hrange, Subgroup.card_top] at h2
  have hle : c.range ≤ g.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, hc]
    change g (a ^ p) = 1
    rw [map_pow, hE]
  have h3 : Nat.card c.range ≤ Nat.card g.ker := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card c.range := Nat.card_pos
  have h4 : Nat.card c.range * Nat.card E ≤ Nat.card c.ker * Nat.card c.range := by
    rw [h1, ← h2]
    exact Nat.mul_le_mul_right _ h3
  rw [mul_comm (Nat.card c.ker)] at h4
  exact Nat.le_of_mul_le_mul_left h4 hpos

theorem exists_pow_pPow_map_eq {A B : Type} [Group A] [Finite A] [Group B] {p : ℕ} (hp : p.Prime)
    (f : A →* B) (x : A) (hfx : orderOf (f x) = p) :
    ∃ k : ℕ, (∃ a : ℕ, orderOf (x ^ k) = p ^ a) ∧ f (x ^ k) = f x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, m, hpm, hxm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  have hcop : m.Coprime (orderOf (f x)) := by
    rw [hfx]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨m * j, ?_, ?_⟩
  · have hdvd : orderOf (x ^ (m * j)) ∣ p ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, show m * j * p ^ a = (p ^ a * m) * j by ring, pow_mul, ← hxm, pow_orderOf_eq_one,
        one_pow]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨b, hb⟩
  · rw [map_pow, pow_mul]
    exact hj

theorem closure_comm_of_comm {A : Type} [Group A] {s : Set A} (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
  have hcomm : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set A) := by
    rw [Subgroup.centralizer_closure]
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun b hb => hs b hb a ha
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (hcomm hb) a ha)

theorem card_closure_range_eq {Z : Type} [Group Z] {N : Fin 4 → Subgroup Z}
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) (hNind : iSupIndep N)
    {s : Fin 4 → Z} (hs : ∀ j, s j ∈ N j) (hs3 : ∀ j, orderOf (s j) = 3) :
    Nat.card ↥(Subgroup.closure (Set.range s)) = 81 := by
  have hcl : Subgroup.closure (Set.range s) = ⨆ j, Subgroup.zpowers (s j) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp only [Subgroup.zpowers_eq_closure]
  have hle : ∀ j, Subgroup.zpowers (s j) ≤ N j := fun j => Subgroup.zpowers_le.2 (hs j)
  have hcomm : Pairwise fun j l => ∀ x y : Z, x ∈ Subgroup.zpowers (s j) → y ∈ Subgroup.zpowers (s l) →
      Commute x y := fun j l hjl x y hx hy => hNcomm j l hjl x (hle j hx) y (hle l hy)
  rw [hcl, card_iSup_of_iSupIndep hcomm (hNind.mono hle)]
  simp only [Nat.card_zpowers, hs3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem four_le_pRank_of_layer {Y Z : Type} [Group Y] [Finite Y] [Group Z] (f : Y →* Z)
    (hlayer : CFSG.layer (Y ⧸ CFSG.pCore 2 Y) = ⊤) (hsolv : Group.IsSolvable f.ker)
    (hR : CFSG.pCore 2 Y ≤ f.ker) (N : Fin 4 → Subgroup Z) (hNf : ∀ j, N j ≤ f.range)
    (hNperf : ∀ j, ⁅N j, N j⁆ = N j) (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x)
    (hNind : iSupIndep N) (s : Fin 4 → Z) (hs : ∀ j, s j ∈ N j) (hs3 : ∀ j, orderOf (s j) = 3) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup Y := CFSG.pCore 2 Y with hRdef
  set π : Y →* Y ⧸ R := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  haveI hKn : (f.ker.map π).Normal := (MonoidHom.normal_ker f).map π hπs
  have hKs : Group.IsSolvable ↥(f.ker.map π) := by
    haveI := hsolv
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective f.ker)
  have hKZ : f.ker.map π ≤ Subgroup.center (Y ⧸ R) :=
    (CFSG.SectionRank.semisimple_solvable_quotient hlayer (f.ker.map π) hKs).1
  set fs : Y ⧸ R →* Z := QuotientGroup.lift R f hR with hfs
  have hfsπ : fs.comp π = f := MonoidHom.ext fun y => QuotientGroup.lift_mk' R hR y
  set H : Fin 4 → Subgroup (Y ⧸ R) := fun j => ((N j).comap f).map π with hH
  have hHcomm : ∀ j l, j ≠ l → ⁅H j, H l⁆ ≤ Subgroup.center (Y ⧸ R) := by
    intro j l hjl
    refine le_trans ?_ hKZ
    simp only [hH]
    rw [← Subgroup.map_commutator]
    refine Subgroup.map_mono ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hNcomm j l hjl _ ha _ hb
  have hz : ∀ A B : Subgroup (Y ⧸ R), A ≤ Subgroup.center (Y ⧸ R) → ⁅A, B⁆ = ⊥ := fun A B hA =>
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (hA.trans (Subgroup.center_le_centralizer _))
  have hthree : ∀ j l, j ≠ l → ⁅⁅H j, H j⁆, H l⁆ = ⊥ := by
    intro j l hjl
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact hz _ _ (hHcomm j l hjl)
    · rw [Subgroup.commutator_comm (H l) (H j)]
      exact hz _ _ (hHcomm j l hjl)
  have hfsH : ∀ j, (⁅H j, H j⁆).map fs = N j := by
    intro j
    rw [Subgroup.map_commutator]
    have : (H j).map fs = N j := by
      simp only [hH]
      rw [Subgroup.map_map, hfsπ, Subgroup.map_comap_eq, inf_eq_right.2 (hNf j)]
    rw [this, hNperf]
  have hy : ∀ j, ∃ y ∈ ⁅H j, H j⁆, (∃ a : ℕ, orderOf y = 3 ^ a) ∧ fs y = s j := by
    intro j
    have hsj : s j ∈ (⁅H j, H j⁆).map fs := by rw [hfsH]; exact hs j
    obtain ⟨y₀, hy₀, hy₀s⟩ := hsj
    obtain ⟨k, hk, hks⟩ := exists_pow_pPow_map_eq Nat.prime_three fs y₀ (by rw [hy₀s, hs3])
    exact ⟨y₀ ^ k, Subgroup.pow_mem _ hy₀ k, hk, by rw [hks, hy₀s]⟩
  choose y hyH hy3 hys using hy
  have hycomm : ∀ a ∈ Set.range y, ∀ b ∈ Set.range y, a * b = b * a := by
    rintro _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
    by_cases hjl : j = l
    · rw [hjl]
    · have hmem : ⁅y j, y l⁆ ∈ ⁅⁅H j, H j⁆, H l⁆ :=
        Subgroup.commutator_mem_commutator (hyH j) (commutator_self_le _ (hyH l))
      rw [hthree j l hjl, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.1 hmem
  set A : Subgroup (Y ⧸ R) := Subgroup.closure (Set.range y) with hA
  have hAcomm : ∀ a b : ↥A, a * b = b * a := fun a b =>
    Subtype.ext (closure_comm_of_comm hycomm a a.2 b b.2)
  set E : Subgroup Z := Subgroup.closure (Set.range s) with hE
  have hAE : A.map fs = E := by
    rw [hA, MonoidHom.map_closure, hE, ← Set.range_comp]
    congr 1
    ext z
    simp [hys]
  have hEcard : Nat.card E = 81 := card_closure_range_eq hNcomm hNind hs hs3
  have hEel : IsElemAbelian 3 E := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
      by_cases hjl : j = l
      · rw [hjl]
      · exact hNcomm j l hjl _ (hs j) _ (hs l)
    · rintro _ ⟨j, rfl⟩
      rw [← hs3 j]
      exact pow_orderOf_eq_one _
  set g : ↥A →* ↥E := (fs.comp A.subtype).codRestrict E (fun a => by
    rw [← hAE]
    exact ⟨a, a.2, rfl⟩) with hg
  have hgs : Function.Surjective g := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ A.map fs := hAE ▸ hz
    obtain ⟨a, ha, rfl⟩ := hz'
    exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
  have hcount := card_le_card_ker_pow hAcomm g hgs (fun x => Subtype.ext (hEel.2 x x.2))
  rw [hEcard] at hcount
  set Ω : Subgroup (Y ⧸ R) := (powHomOfComm hAcomm 3).ker.map A.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card ↥(powHomOfComm hAcomm 3).ker :=
    Subgroup.card_map_of_injective A.subtype_injective
  have hΩel : IsElemAbelian 3 Ω := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', -, ha'⟩ := a.2
      obtain ⟨b', -, hb'⟩ := b.2
      change (a : Y ⧸ R) * b = b * a
      rw [← ha', ← hb']
      exact congrArg Subtype.val (hAcomm a' b')
    · rintro _ ⟨a, ha, rfl⟩
      have : (powHomOfComm hAcomm 3) a = 1 := ha
      exact congrArg Subtype.val this
  have hR3 : ¬ 3 ∣ Nat.card R := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Y)))
    rw [hk]
    intro h
    have := (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨S, hSel, -, hScard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift R hR3 hΩel
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hSel.isPGroup
  have hk4 : 3 ^ 4 ≤ 3 ^ k := by
    rw [← hk, hScard, hΩcard]
    norm_num
    exact hcount
  have hk4' : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hk4
  exact hk4'.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hSel hk)

end P22y

end CFSG.LocalAnalysis.UniquenessCase.UC22
