module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Rank

variable {τ : Tag} {S : TcrSys}

theorem TcrGood.posFlag_iff_height
    (hG : TcrGood τ S) {i : ℕ} (hi : i < S.tcrN) :
    S.posFlag[i]! = true ↔ 0 < height (tcrRv S τ i) := by
  rw [hG.tcrPos_iff hi]
  constructor
  · intro h
    have h1 : 0 ≤ height (tcrRv S τ i) := Finset.sum_nonneg fun j _ => h j
    exact lt_of_le_of_ne h1 (Ne.symm (hG.rv_spec hi).1.height_ne_zero)
  · intro h
    rcases (hG.rv_spec hi).1.nonneg_or_nonpos with hs | hs
    · exact hs
    · have h2 : height (tcrRv S τ i) ≤ 0 := Finset.sum_nonpos fun j _ => hs j
      exact absurd h (not_lt.2 h2)

theorem tcr_mem_posRoots_iff (psi : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) {g : ℕ}
    (hg : g ∈ psi) :
    tcrRv S τ g ∈ posRoots (tcrSet S τ psi) ↔ 0 < height (tcrRv S τ g) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨⟨g, hg, hlt g hg, rfl⟩, h⟩

theorem tcr_decomp_of_test
    (hG : TcrGood τ S) (psi : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN)
    {g d : ℕ} (hg : g ∈ psi) (hd : d ∈ psi) (hdp : S.posFlag[d]! = true)
    (hip : (S.ip[g]!)[d]! = 1) (he : (S.refl[d]!)[g]! ∈ psi)
    (hep : S.posFlag[(S.refl[d]!)[g]!]! = true) :
    ∃ γ ∈ posRoots (tcrSet S τ psi), ∃ δ ∈ posRoots (tcrSet S τ psi),
      tcrRv S τ g = γ + δ := by
  have hdN := hlt d hd
  have heN := hlt _ he
  have hip1 : iform (tcrRv S τ g) (tcrRv S τ d) = 1 := by
    rw [← hG.ip_eq (hlt g hg) hdN]
    exact hip
  obtain ⟨-, hrf⟩ := hG.refl_spec hdN (hlt g hg)
  rw [hip1, one_smul] at hrf
  refine ⟨tcrRv S τ d, (tcr_mem_posRoots_iff psi hlt hd).2 ((hG.posFlag_iff_height hdN).1 hdp),
    tcrRv S τ ((S.refl[d]!)[g]!), (tcr_mem_posRoots_iff psi hlt he).2
      ((hG.posFlag_iff_height heN).1 hep), ?_⟩
  rw [hrf]
  abel

theorem tcr_test_of_decomp
    (hG : TcrGood τ S) (psi : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) {g : ℕ} (hg : g ∈ psi)
    {γ δ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots (tcrSet S τ psi))
    (hδ : δ ∈ posRoots (tcrSet S τ psi)) (h : tcrRv S τ g = γ + δ) :
    ∃ d, (d ∈ psi ∧ S.posFlag[d]! = true) ∧ (S.ip[g]!)[d]! = 1 ∧
      (S.refl[d]!)[g]! ∈ psi ∧ S.posFlag[(S.refl[d]!)[g]!]! = true := by
  have hγ' : γ ∈ tcrSet S τ psi ∧ 0 < height γ := hγ
  have hδ' : δ ∈ tcrSet S τ psi ∧ 0 < height δ := hδ
  obtain ⟨d, hd, hdN, rfl⟩ := hγ'.1
  obtain ⟨k, hk, hkN, rfl⟩ := hδ'.1
  have hγpos : 0 < height (tcrRv S τ d) := hγ'.2
  have hδpos : 0 < height (tcrRv S τ k) := hδ'.2
  have hgN := hlt g hg
  have hrg := (hG.rv_spec hgN).1
  have hrd := (hG.rv_spec hdN).1
  have hrk := (hG.rv_spec hkN).1
  have E1 : iform (tcrRv S τ d + tcrRv S τ k) (tcrRv S τ d + tcrRv S τ k) = 2 := by
    rw [← h]
    exact hG.iform_self hrg
  rw [iform_add_left, iform_add_right, iform_add_right] at E1
  have Eγ : iform (tcrRv S τ d) (tcrRv S τ d) = 2 := hG.iform_self hrd
  have Eδ : iform (tcrRv S τ k) (tcrRv S τ k) = 2 := hG.iform_self hrk
  have hc : iform (tcrRv S τ k) (tcrRv S τ d) = iform (tcrRv S τ d) (tcrRv S τ k) :=
    iform_comm _ _
  have hab : iform (tcrRv S τ d) (tcrRv S τ k) = -1 := by linarith
  have hip1 : iform (tcrRv S τ g) (tcrRv S τ d) = 1 := by
    rw [h, iform_add_left, Eγ, hc, hab]
    norm_num
  have hrf := hG.refl_spec hdN hgN
  rw [hip1, one_smul, h, add_sub_cancel_left] at hrf
  have hrk' : (S.refl[d]!)[g]! = k := hG.rv_inj hrf.1 hkN hrf.2
  refine ⟨d, ⟨hd, (hG.posFlag_iff_height hdN).2 hγpos⟩, ?_, ?_, ?_⟩
  · rw [hG.ip_eq hgN hdN]
    exact hip1
  · rw [hrk']
    exact hk
  · rw [hrk']
    exact (hG.posFlag_iff_height hkN).2 hδpos

theorem tcrSimpleSys_mem (_hG : TcrGood τ S) (psi : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN)
    {g : ℕ} :
    g ∈ tcrSimpleSys S psi ↔ (g ∈ psi ∧ S.posFlag[g]! = true) ∧
      ¬ ∃ d, (d ∈ psi ∧ S.posFlag[d]! = true) ∧ (S.ip[g]!)[d]! = 1 ∧
        (S.refl[d]!)[g]! ∈ psi ∧ S.posFlag[(S.refl[d]!)[g]!]! = true := by
  have hmask : ∀ x, (tcrMaskOf S.tcrN psi)[x]! = true ↔ x ∈ psi := fun x => by
    rw [tcrMaskOf_getElem!]
    exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩
  unfold tcrSimpleSys tcrPosOf
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true,
    beq_iff_eq, hmask]
  simp only [not_exists, and_assoc, not_and, and_imp]

theorem tcrSet_ncard (hG : TcrGood τ S) (psi : List ℕ) (hnd : psi.Nodup)
    (hlt : ∀ i ∈ psi, i < S.tcrN) : (tcrSet S τ psi).ncard = psi.length := by
  have himg : tcrSet S τ psi = (fun i => tcrRv S τ i) '' ↑(psi.toFinset) := by
    ext γ
    simp only [tcrSet, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨i, hi, -, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, hlt i hi, rfl⟩
  have hinj : Set.InjOn (fun i => tcrRv S τ i) ↑(psi.toFinset) := by
    intro i hi j hj hij
    have hi' : i ∈ psi := by simpa using hi
    have hj' : j ∈ psi := by simpa using hj
    exact hG.rv_inj (hlt i hi') (hlt j hj') hij
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem mem_tcrSimpleSys_iff
    (hG : TcrGood τ S) (psi : List ℕ) (_hnd : psi.Nodup) (hlt : ∀ i ∈ psi, i < S.tcrN)
    (_hΨ : IsRootComponent (tcrSet S τ psi)) {g : ℕ} :
    g ∈ tcrSimpleSys S psi ↔ g ∈ psi ∧ tcrRv S τ g ∈ simpleRoots (tcrSet S τ psi) := by
  rw [tcrSimpleSys_mem hG psi hlt, mem_simpleRoots]
  constructor
  · rintro ⟨⟨hg, hgp⟩, hno⟩
    refine ⟨hg, (hG.rv_spec (hlt g hg)).1,
      (tcr_mem_posRoots_iff psi hlt hg).2 ((hG.posFlag_iff_height (hlt g hg)).1 hgp), ?_⟩
    rintro γ hγ δ hδ hsum
    obtain ⟨d, hd, hip, he, hep⟩ := tcr_test_of_decomp hG psi hlt hg hγ hδ hsum
    exact hno ⟨d, hd, hip, he, hep⟩
  · rintro ⟨hg, -, hpos, hsimp⟩
    have hgp : S.posFlag[g]! = true :=
      (hG.posFlag_iff_height (hlt g hg)).2 ((tcr_mem_posRoots_iff psi hlt hg).1 hpos)
    refine ⟨⟨hg, hgp⟩, ?_⟩
    rintro ⟨d, hd, hip, he, hep⟩
    obtain ⟨γ, hγ, δ, hδ, hsum⟩ := tcr_decomp_of_test hG psi hlt hg hd.1 hd.2 hip he hep
    exact hsimp γ hγ δ hδ hsum

theorem tcrSimpleSys_nodup (_hG : TcrGood τ S) (psi : List ℕ) (hnd : psi.Nodup) :
    (tcrSimpleSys S psi).Nodup := by
  unfold tcrSimpleSys tcrPosOf
  exact List.Nodup.filter _ (List.Nodup.filter _ hnd)

theorem tcrSimpleSys_length
    (hG : TcrGood τ S) (psi : List ℕ) (hnd : psi.Nodup) (hlt : ∀ i ∈ psi, i < S.tcrN)
    (hΨ : IsRootComponent (tcrSet S τ psi)) :
    (tcrSimpleSys S psi).length = compRank (tcrSet S τ psi) := by
  rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ]
  have hinj : ∀ x ∈ tcrSimpleSys S psi, ∀ y ∈ tcrSimpleSys S psi,
      tcrRv S τ x = tcrRv S τ y → x = y := by
    intro x hx y hy hxy
    exact hG.rv_inj (hlt x (((tcrSimpleSys_mem hG psi hlt).1 hx).1.1))
      (hlt y (((tcrSimpleSys_mem hG psi hlt).1 hy).1.1)) hxy
  have hmapnd : ((tcrSimpleSys S psi).map (tcrRv S τ)).Nodup :=
    List.Nodup.map_on hinj (tcrSimpleSys_nodup hG psi hnd)
  have hset : simpleRoots (tcrSet S τ psi) =
      ((tcrSimpleSys S psi).map (tcrRv S τ)).toFinset := by
    ext β
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · intro hβ
      have hβ' := mem_simpleRoots.1 hβ
      obtain ⟨i, hi, hiN, hiβ⟩ : β ∈ tcrSet S τ psi := hβ'.2.1.1
      refine ⟨i, ?_, hiβ⟩
      refine (mem_tcrSimpleSys_iff hG psi hnd hlt hΨ).2 ⟨hi, ?_⟩
      rw [hiβ]
      exact hβ
    · rintro ⟨i, hi, rfl⟩
      exact ((mem_tcrSimpleSys_iff hG psi hnd hlt hΨ).1 hi).2
  rw [hset, List.toFinset_card_of_nodup hmapnd, List.length_map]

end Rank

end CFSG.StandardType.TableCRes

end
