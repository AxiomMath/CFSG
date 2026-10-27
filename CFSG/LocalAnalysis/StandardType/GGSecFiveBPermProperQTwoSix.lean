module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrameClass
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Root
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.RankThree.PartOne.KF.ClsSUUpper

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
  {F : Type} [Field F] {a a' : Fin 6}
  {eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod p))}
  {σ : ↥(unitarySU 2 1 F 6) →* G} {χ : Multiplicative (ZMod p) →* Fˣ}

private theorem injective_comp_blockExtSU (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) {S : Finset (Fin 6)} (hS : ∃ i, i ∉ S) :
    Function.Injective (σ.comp (TableBUE.blockExtSU S hK)) := by
  classical
  let φ : ↥(unitarySU 2 1 F 6) →* ↥L := σ.codRestrict L fun g => by
    rw [← hF.1]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hM : UnitTB.Model φ := by
    refine ⟨hK, ?_, ?_⟩
    · intro l
      have hl : (l : G) ∈ σ.range := by rw [hF.1]; exact l.2
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hl
      exact ⟨g, Subtype.ext hg⟩
    · intro g hg
      exact hF.2.1 g (congrArg Subtype.val hg)
  intro u v huv
  apply hM.injective_comp_blockExtSU S hS
  exact Subtype.ext huv

private theorem card_map_blockSU (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) {S : Finset (Fin 6)} (hS : ∃ i, i ∉ S) :
    Nat.card ↥((TableBUE.blockSU (K := F) (n := 1) S).map σ) =
      Nat.card ↥(unitarySU 2 1 F S.card) := by
  have hinj := injective_comp_blockExtSU hF hK hS
  have hrange : (σ.comp (TableBUE.blockExtSU S hK)).range =
      (TableBUE.blockSU (K := F) (n := 1) S).map σ := by
    rw [MonoidHom.range_comp, TableBUE.range_blockExtSU]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem card_unitarySU_five (hK : UnitaryFieldData 2 1 F) :
    Nat.card ↥(unitarySU 2 1 F 5) = 13685760 := by
  have : CharP F 2 := hK.charP
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hK (n := 5) (by norm_num)
  rw [show Finset.Icc 2 5 = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton] at hc
  have hc' : (Nat.card (unitarySU 2 1 F 5) : ℤ) = ((13685760 : ℕ) : ℤ) := by
    rw [show unitarySU 2 1 F 5 = CFSG.Open.StatedSU 5 (2 ^ 1) F from rfl, hc]
    norm_num
  exact_mod_cast hc'

private theorem mem_inf_centralizer_map_blockSU_iff
    (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ) (hK : UnitaryFieldData 2 1 F)
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    {S : Finset (Fin 6)} (ha : a ∈ S) (ha' : a' ∈ S) (b : ↥Bs) :
    (b : G) ∈ B ⊓ Subgroup.centralizer
        (((TableBUE.blockSU (K := F) (n := 1) S).map σ : Subgroup G) : Set G) ↔
      ∀ i ∈ S, ∀ j ∈ S, eta b i = eta b j := by
  constructor
  · intro hb
    simpa using hF.eq_of_mem_centralizer_map_blockSU hK (by norm_num : 3 ≤ 6) b hb.2
  · intro h
    refine ⟨(hroot b).mpr (h a ha a' ha'), ?_⟩
    simpa using hF.mem_centralizer_map_blockSU_of_const b h

private theorem card_inf_centralizer_map_blockSU
    (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ) (hK : UnitaryFieldData 2 1 F)
    (hBBs : B ≤ Bs) (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    {S : Finset (Fin 6)} (ha : a ∈ S) (ha' : a' ∈ S) (hScard : S.card = 5) :
    Nat.card ↥(B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := 1) S).map σ : Subgroup G) : Set G)) = p ^ 2 := by
  classical
  have hDmem : ∀ b : ↥Bs, (b : G) ∈ B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := 1) S).map σ : Subgroup G) : Set G) ↔
      ∀ i ∈ S, ∀ j ∈ S, eta b i = eta b j :=
    fun b => mem_inf_centralizer_map_blockSU_iff hF hK hroot ha ha' b
  have hcardD : Nat.card ↥(B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := 1) S).map σ : Subgroup G) : Set G)) =
      Nat.card {v : Fin 6 → Multiplicative (ZMod p) // ∀ i ∈ S, ∀ j ∈ S, v i = v j} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun d => ⟨eta ⟨(d : G), hBBs (Subgroup.mem_inf.mp d.2).1⟩,
          fun i hi j hj => ?_⟩
        invFun := fun v => ⟨((eta.symm v.1 : ↥Bs) : G), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact (hDmem ⟨(d : G), hBBs (Subgroup.mem_inf.mp d.2).1⟩).mp d.2 i hi j hj
    · rw [hDmem]
      intro i hi j hj
      simpa only [MulEquiv.apply_symm_apply] using v.2 i hi j hj
    · intro d
      apply Subtype.ext
      simp
    · intro v
      apply Subtype.ext
      simp
  have hcardS : Nat.card {v : Fin 6 → Multiplicative (ZMod p) //
      ∀ i ∈ S, ∀ j ∈ S, v i = v j} = p ^ (6 - S.card + 1) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun f =>
      (forall_aPermutationOn_fix_iff S f).symm)]
    exact card_fix_aPermutationOn ⟨a, ha⟩
  rw [hcardD, hcardS, hScard]

private theorem subset_erase_of_const (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) (hp : p.Prime)
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    {k : Fin 6} (hk : k ∉ ({a, a'} : Finset (Fin 6))) {D : Subgroup G} (hD : D ≤ Bs)
    (hDdef : D = B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := 1) (Finset.univ.erase k)).map σ :
        Subgroup G) : Set G))
    {S : Finset (Fin 6)} (hS4 : 4 ≤ S.card)
    (hconst : ∀ (d : G) (hd : d ∈ D), ∀ i ∈ S, ∀ j ∈ S,
      eta ⟨d, hD hd⟩ i = eta ⟨d, hD hd⟩ j) :
    S ⊆ Finset.univ.erase k := by
  classical
  have hak : a ≠ k := fun h => hk (h ▸ Finset.mem_insert_self a {a'})
  have ha'k : a' ≠ k := fun h =>
    hk (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self a'))
  have haS : a ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hak, Finset.mem_univ a⟩
  have ha'S : a' ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨ha'k, Finset.mem_univ a'⟩
  have hkS : k ∉ S := by
    intro hkS
    obtain ⟨j, hjS, hjk⟩ : ∃ j ∈ S, j ≠ k := by
      have hpos : 0 < (S.erase k).card := by
        rw [Finset.card_erase_of_mem hkS]
        omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      exact ⟨j, Finset.mem_of_mem_erase hj, (Finset.mem_erase.mp hj).1⟩
    let d : ↥Bs := eta.symm (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod p)))
    have hdeta : eta d = Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod p)) :=
      MulEquiv.apply_symm_apply eta _
    have hdi : ∀ i, i ≠ k → eta d i = 1 := by
      intro i hi
      rw [hdeta]
      exact Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p))
        (i := k) (i' := i) hi _
    have hdconst : ∀ i ∈ Finset.univ.erase k, ∀ j ∈ Finset.univ.erase k,
        eta d i = eta d j := by
      intro i hi j hj
      rw [hdi i (Finset.mem_erase.mp hi).1, hdi j (Finset.mem_erase.mp hj).1]
    have hdD : (d : G) ∈ D := by
      rw [hDdef]
      exact (mem_inf_centralizer_map_blockSU_iff hF hK hroot haS ha'S d).mpr hdconst
    have heq : eta d k = eta d j := by
      have hc := hconst (d : G) hdD k hkS j hjS
      rwa [show (⟨(d : G), hD hdD⟩ : ↥Bs) = d from Subtype.ext rfl] at hc
    rw [hdi j hjk, hdeta, Pi.mulSingle_eq_same] at heq
    have h1 : Multiplicative.ofAdd ((1 : ℕ) : ZMod p) = 1 := by simpa using heq
    have h2 : ((1 : ℕ) : ZMod p) = 0 := ofAdd_eq_one.mp h1
    have h3 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h2
    exact hp.ne_one (Nat.dvd_one.mp h3)
  intro i hi
  rw [Finset.mem_erase]
  exact ⟨fun hik => hkS (hik ▸ hi), Finset.mem_univ i⟩

private theorem not_largeEvenSmall_blockSU_erase (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) (k : Fin 6) :
    ¬ LargeEvenSmall
      ((TableBUE.blockSU (K := F) (n := 1) (Finset.univ.erase k)).map σ) := by
  have hcard := card_map_blockSU hF hK (S := Finset.univ.erase k) ⟨k, by simp⟩
  have h5 : (Finset.univ.erase k).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  rw [h5] at hcard
  have hbig : 25920 < Nat.card ↥((TableBUE.blockSU (K := F) (n := 1)
      (Finset.univ.erase k)).map σ) := by
    rw [hcard, card_unitarySU_five hK]
    norm_num
  exact not_largeEvenSmall_of_map_big (MonoidHom.id G) _ (Or.inr (by simpa using hbig))

private theorem exists_stdSubPre_not_largeEvenSmall [Finite G] {D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) (hpq : p ∣ 2 ^ 1 + 1) (haa' : a ≠ a')
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) :
    ∃ D₁ K₁ : Subgroup G, LargeEvenStdSubPre p B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁ := by
  classical
  have : Finite F := hK.finite
  have : CharP F 2 := hK.charP
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hxB : x ∈ B := hcfg.1.2.2.2.2.2.2.1.2.1
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < (({a, a'} : Finset (Fin 6))ᶜ).card by
    rw [Finset.card_compl, Finset.card_pair haa', Fintype.card_fin]
    norm_num)
  have hk' : k ∉ ({a, a'} : Finset (Fin 6)) := by simpa using hk
  let S₁ : Finset (Fin 6) := Finset.univ.erase k
  let K₁ : Subgroup G := (TableBUE.blockSU (K := F) (n := 1) S₁).map σ
  let D₁ : Subgroup G := B ⊓ Subgroup.centralizer (K₁ : Set G)
  have hS₁card : S₁.card = 5 := by
    simp [S₁, Finset.card_erase_of_mem (Finset.mem_univ k)]
  have haS : a ∈ S₁ := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ a⟩
    intro h
    exact hk' (h ▸ Finset.mem_insert_self a {a'})
  have ha'S : a' ∈ S₁ := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ a'⟩
    intro h
    exact hk' (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self a'))
  have hDle : D₁ ≤ Bs := inf_le_left.trans hBBs
  have hDmem : ∀ b : ↥Bs, (b : G) ∈ D₁ ↔ ∀ i ∈ S₁, ∀ j ∈ S₁, eta b i = eta b j :=
    fun b => mem_inf_centralizer_map_blockSU_iff hF hK hroot haS ha'S b
  have hconst : ∀ (d : G) (hd : d ∈ D₁), ∀ i ∈ S₁, ∀ j ∈ S₁,
      eta ⟨d, hDle hd⟩ i = eta ⟨d, hDle hd⟩ j :=
    fun d hd => (hDmem ⟨d, hDle hd⟩).mp hd
  have hsmall : ∀ S : Finset (Fin 6), 4 ≤ S.card →
      (∀ (d : G) (hd : d ∈ D₁), ∀ i ∈ S, ∀ j ∈ S,
        eta ⟨d, hDle hd⟩ i = eta ⟨d, hDle hd⟩ j) → S ⊆ S₁ :=
    fun S hS4 hc => subset_erase_of_const hF hK hp hroot hk' (D := D₁) hDle rfl hS4 hc
  obtain ⟨hcomp, hlayer⟩ :=
    GGSecFiveBPermUniLFrame.layer_eq_map_blockSU_two hF hK hp hpq hDle
      (by rw [hS₁card]; norm_num) hconst hsmall
  have hcardD : Nat.card ↥D₁ = p ^ 2 :=
    card_inf_centralizer_map_blockSU hF hK hBBs hroot haS ha'S hS₁card
  have hxD : x ∈ D₁ := by
    refine ⟨hxB, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hLx ((Subgroup.map_le_range σ _).trans (le_of_eq hF.1) hg))
  have hpre : LargeEvenStdSubPre p B x L D₁ K₁ :=
    ⟨inf_le_left, hBs.mono hDle, hcardD, hxD, hlayer, hcomp, rfl⟩
  exact ⟨D₁, K₁, hpre, not_largeEvenSmall_blockSU_erase hF hK k⟩

private theorem largeEvenSmall_J (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hK : UnitaryFieldData 2 1 F) (haa' : a ≠ a') {J : Subgroup G}
    (hJ : J = (TableBUE.blockSU (K := F) (n := 1) ({a, a'} : Finset (Fin 6))ᶜ).map σ) :
    LargeEvenSmall J := by
  classical
  have : Finite F := hK.finite
  have hScard : (({a, a'} : Finset (Fin 6))ᶜ).card = 4 := by
    rw [Finset.card_compl, Finset.card_pair haa', Fintype.card_fin]
  have hSne : ∃ i, i ∉ (({a, a'} : Finset (Fin 6))ᶜ) := ⟨a, by simp⟩
  have hinj := injective_comp_blockExtSU hF hK hSne
  have hrange : (σ.comp (TableBUE.blockExtSU (({a, a'} : Finset (Fin 6))ᶜ) hK)).range = J := by
    rw [MonoidHom.range_comp, TableBUE.range_blockExtSU]
    exact hJ.symm
  let e : ↥(unitarySU 2 1 F (({a, a'} : Finset (Fin 6))ᶜ).card) ≃* ↥J :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hU : LargeEvenIsU42 ↥(unitarySU 2 1 F (({a, a'} : Finset (Fin 6))ᶜ).card) := by
    rw [hScard]
    exact IOneU52.unitarySU_four_isU42 (by rw [hK.card]; norm_num)
  exact Or.inl (IOneU52.isU42_of_mulEquiv e.symm hU)

theorem GGConfig.false_of_qTwo_six {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hn : n = 6) (hpq : p ∣ 2 ^ 1 + 1) {F : Type} [Field F]
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {σ : ↥(unitarySU 2 1 F n) →* G} {χ : Multiplicative (ZMod p) →* Fˣ}
    (hF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ) (hK : UnitaryFieldData 2 1 F)
    {a a' : Fin n} (haa' : a ≠ a') (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    (hJ : J = (TableBUE.blockSU (K := F) (n := 1) ({a, a'} : Finset (Fin n))ᶜ).map σ) :
    False := by
  subst hn
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hp3 : p = 3 := by
    have h : p ∣ 3 := by simpa using hpq
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h3
    · exact absurd h1 hp.ne_one
    · exact h3
  have hJsmall : LargeEvenSmall J := largeEvenSmall_J hF hK haa' hJ
  obtain ⟨D₁, K₁, hpre, hnot⟩ :=
    exists_stdSubPre_not_largeEvenSmall hcfg hF hK hpq haa' hroot
  exact hcfg.2.2.2 ⟨hp3, D₁, K₁, hpre, hnot⟩ hJsmall

end CFSG.StandardType

end
