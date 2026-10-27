module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yf
import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22.P22y
open scoped commutatorElement

theorem card_closure_range_eq {Z : Type} [Group Z] {p n : ℕ} {N : Fin n → Subgroup Z}
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) (hNind : iSupIndep N)
    {s : Fin n → Z} (hs : ∀ j, s j ∈ N j) (hsp : ∀ j, orderOf (s j) = p) :
    Nat.card ↥(Subgroup.closure (Set.range s)) = p ^ n := by
  have hcl : Subgroup.closure (Set.range s) = ⨆ j, Subgroup.zpowers (s j) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp only [Subgroup.zpowers_eq_closure]
  have hle : ∀ j, Subgroup.zpowers (s j) ≤ N j := fun j => Subgroup.zpowers_le.2 (hs j)
  have hcomm : Pairwise fun j l => ∀ x y : Z, x ∈ Subgroup.zpowers (s j) →
      y ∈ Subgroup.zpowers (s l) → Commute x y :=
    fun j l hjl x y hx hy => hNcomm j l hjl x (hle j hx) y (hle l hy)
  rw [hcl, card_iSup_of_iSupIndep hcomm (hNind.mono hle)]
  simp only [Nat.card_zpowers, hsp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem le_pRank_of_layer {Y Z : Type} [Group Y] [Finite Y] [Group Z] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (f : Y →* Z) (hlayer : CFSG.layer (Y ⧸ CFSG.pCore 2 Y) = ⊤)
    (hsolv : Group.IsSolvable f.ker) (hR : CFSG.pCore 2 Y ≤ f.ker) (N : Fin n → Subgroup Z)
    (hNf : ∀ j, N j ≤ f.range) (hNperf : ∀ j, ⁅N j, N j⁆ = N j)
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) (hNind : iSupIndep N)
    (s : Fin n → Z) (hs : ∀ j, s j ∈ N j) (hsp : ∀ j, orderOf (s j) = p) :
    n ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
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
  set H : Fin n → Subgroup (Y ⧸ R) := fun j => ((N j).comap f).map π with hH
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
  have hy : ∀ j, ∃ y ∈ ⁅H j, H j⁆, (∃ a : ℕ, orderOf y = p ^ a) ∧ fs y = s j := by
    intro j
    have hsj : s j ∈ (⁅H j, H j⁆).map fs := by rw [hfsH]; exact hs j
    obtain ⟨y₀, hy₀, hy₀s⟩ := hsj
    obtain ⟨k, hk, hks⟩ := exists_pow_pPow_map_eq hp fs y₀ (by rw [hy₀s, hsp])
    exact ⟨y₀ ^ k, Subgroup.pow_mem _ hy₀ k, hk, by rw [hks, hy₀s]⟩
  choose y hyH hyp hys using hy
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
  have hEcard : Nat.card E = p ^ n := card_closure_range_eq hNcomm hNind hs hsp
  have hEel : IsElemAbelian p E := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
      by_cases hjl : j = l
      · rw [hjl]
      · exact hNcomm j l hjl _ (hs j) _ (hs l)
    · rintro _ ⟨j, rfl⟩
      rw [← hsp j]
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
  set Ω : Subgroup (Y ⧸ R) := (powHomOfComm hAcomm p).ker.map A.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card ↥(powHomOfComm hAcomm p).ker :=
    Subgroup.card_map_of_injective A.subtype_injective
  have hΩel : IsElemAbelian p Ω := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', -, ha'⟩ := a.2
      obtain ⟨b', -, hb'⟩ := b.2
      change (a : Y ⧸ R) * b = b * a
      rw [← ha', ← hb']
      exact congrArg Subtype.val (hAcomm a' b')
    · rintro _ ⟨a, ha, rfl⟩
      have : (powHomOfComm hAcomm p) a = 1 := ha
      exact congrArg Subtype.val this
  have hRp : ¬ p ∣ Nat.card R := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Y)))
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨S, hSel, -, hScard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift R hRp hΩel
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hSel.isPGroup
  have hkn : p ^ n ≤ p ^ k := by
    rw [← hk, hScard, hΩcard]
    exact hcount
  have hkn' : n ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hkn
  exact hkn'.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top hSel hk)

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
