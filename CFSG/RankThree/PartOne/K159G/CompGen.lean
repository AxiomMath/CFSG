module

public import CFSG.RankThree.PartOne.K159G.Transfer
public import CFSG.RankThree.PartOne.K159.CompGenFive
public import CFSG.RankThree.PartOne.U5E.Refl
public import CFSG.RankThree.PartOne.K159G.FrameLayer

public section

namespace CFSG.RankThree.PartOne.K159G

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K CFSG.RankThree.PartOne.U5K.Kf
  CFSG.RankThree.PartOne.U5E CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section PlaneIdent

variable {G : Type} [Group G] (I : Subgroup G) {f : ℕ} (hf : 1 ≤ f)
  (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def twistMap
    (P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) : ↥I →* PI f hf :=
  (primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) P⁻¹).toMonoidHom.comp
    (modelMap I hf e)

theorem ker_twistMap_le
    (P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) :
    (twistMap I hf e P).ker ≤ Subgroup.center ↥I := by
  intro y hy
  apply ker_modelMap_le I hf e
  rw [MonoidHom.mem_ker] at hy ⊢
  have h1 : primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) P⁻¹
      (modelMap I hf e y) = 1 := hy
  exact (MulEquiv.map_eq_one_iff _).1 h1

theorem map_subgroupOf_eq_planeP (Z : ZetaData (u5FieldData f hf) p)
    (P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) {K : Subgroup G}
    (hKI : K ≤ I) (hmod : StatedClassicalModel ↥K .PSL 2 2 f) (hf2 : 2 ≤ f) {k l : Fin 5} (hkl : k ≠ l)
    (hB : ∃ b : G, ∃ hb : b ∈ Subgroup.normalizer (I : Set G), (∀ y ∈ K, b * y = y * b) ∧
      Z.par P (genVec p k l) = MulAut.congr (u5Equiv f hf) (U5Act I e ⟨b, hb⟩)) :
    (K.subgroupOf I).map (twistMap I hf e P) = planeP (u5FieldData f hf) k l hkl := by
  obtain ⟨hqs, hcen⟩ := S13K.isQuasisimple_and_center_of_model_psl_two hmod
  refine map_eq_planeP Z hkl (commutator_subgroupOf_eq hKI (Subgroup.isPerfect_iff.1 hqs.1)) ?_ ?_ ?_
  · obtain ⟨b, hb, hbc, hpar⟩ := hB
    intro y hy
    exact fix_modelTwist I hf e Z P _ hb hpar (hbc (y : G) hy)
  · intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥I := ker_twistMap_le I hf e P hx1
    have hxK : (x : G) ∈ K := hx
    have h1 : (⟨(x : G), hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.1 hxc ⟨(g : G), hKI g.2⟩
      exact Subtype.ext (congrArg (fun z : ↥I => (z : G)) this)
    rw [hcen, Subgroup.mem_bot] at h1
    exact Subtype.ext (congrArg (fun z : ↥K => (z : G)) h1)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKI).toEquiv,
      (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl,
      (CFSG.Timmesfeld.card_statedClassicalModel_two (blk_model _ hf2 hkl).2.2).1 rfl]

end PlaneIdent

end CFSG.RankThree.PartOne.K159G

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
  CFSG.RankThree.PartOne.U5K CFSG.RankThree.PartOne.U5K.Kf CFSG.RankThree.PartOne.U5E
  CFSG.RankThree.PartOne.K159G
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem kfCompGenFive_of (hAt : KFU5At) (hEin : U5EInndiag) : KFCompGenFive := by
  intro G _ _ p A c L E h15 hF hout e₀ he₀ he₀1 Q hQle hQc
  classical
  obtain ⟨f, hf, hpf, ⟨e⟩, -, hcardE, -, -⟩ := id hout
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h.three_lt; omega)
    (by have := h.three_lt; omega)
  have hf2 : 2 ≤ f := by
    have h1 := Nat.le_of_dvd (by positivity) hpf
    by_contra hlt
    have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨fd⟩ := exists_frameData hEin h15 hF hout hf hpf e
  obtain ⟨ι, hιlt, hιeq, hιinj, hmem, hsurj⟩ := exists_refl_pairs hAt hEin h15 hF hout hf hpf e fd
  obtain ⟨hD, hel, -⟩ := Ebar_facts hEin h15 hF hout hf e
  have hEN : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) := E_le_lieNormalizer h15
  have hinjE : ∀ x ∈ E, ∀ hx : x ∈ Subgroup.normalizer (lieGenerated p E : Set G),
      U5Act (lieGenerated p E) e ⟨x, hx⟩ = 1 → x = 1 :=
    fun x hxE hxN hρ1 => (hEin G p A c L E h15 hF hout f hf e x hxN hxE).2 hρ1
  have hN₀ := hEN he₀
  have hβ : MulAut.congr (u5Equiv f hf) (U5Act (lieGenerated p E) e ⟨e₀, hN₀⟩) ∈
      EbarOf hf (U5Act (lieGenerated p E) e) E :=
    Subgroup.mem_map.2 ⟨_, mem_rm.2 ⟨e₀, hN₀, he₀, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ := fd.coord hel hD hβ
  have hq : ∀ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2},
      ∃ t ∈ reflectionSet p E, ι (autFixedInG E t) = q.1 := fun q => hsurj q.1 q.2.1
  choose t ht hιt using hq
  have hAtq := fun q => hAt G p A c L E f h15 hF hout hf hpf ⟨e⟩ (t q) (ht q)
  have hKt : ∀ q, IsKt p E (t q) (kZero p E (t q)) := fun q =>
    (isKt_iff_of_nonexceptional (hAtq q).1).2 rfl
  have hKI : ∀ q, kZero p E (t q) ≤ lieGenerated p E := fun q => le_sSup ⟨t q, ht q, hKt q⟩
  have hAtil : ∀ q, fd.Z.Atil fd.P (EbarOf hf (U5Act (lieGenerated p E) e) (autFixedInG E (t q))) =
      Hsub p q.1.1 q.1.2 := fun q => by
    have := hιeq _ (hmem _ (ht q))
    rw [hιt q] at this
    exact this
  have hex : ∀ (q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2}) (b₀ : Fin 5 → ZMod p),
      b₀ q.1.1 = b₀ q.1.2 → ∃ b : G, ∃ hb : b ∈ Subgroup.normalizer (lieGenerated p E : Set G),
        b ∈ E ⊓ Subgroup.centralizer (kZero p E (t q) : Set G) ∧
        fd.Z.par fd.P b₀ = MulAut.congr (u5Equiv f hf) (U5Act (lieGenerated p E) e ⟨b, hb⟩) := by
    intro q b₀ hb₀
    have h1 : Multiplicative.ofAdd b₀ ∈ fd.Z.Atil fd.P
        (EbarOf hf (U5Act (lieGenerated p E) e) (autFixedInG E (t q))) := by
      rw [hAtil q, mem_Hsub]
      exact hb₀
    have h2 := (fd.Z.mem_Atil fd.P _ b₀).1 h1
    obtain ⟨_, hb, hbeq⟩ := Subgroup.mem_map.1 h2
    obtain ⟨b, hbN, hbB, rfl⟩ := mem_rm.1 hb
    refine ⟨b, hbN, ?_, hbeq.symm⟩
    rw [(hAtq q).2.2.1]
    exact hbB
  have he₀B : ∀ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2}, e₀ ∈ autFixedInG E (t q) :=
    fun q => by
    have h1 : Multiplicative.ofAdd a ∈ fd.Z.Atil fd.P
        (EbarOf hf (U5Act (lieGenerated p E) e) (autFixedInG E (t q))) := by
      rw [hAtil q, mem_Hsub]
      exact q.2.2
    have h2 := (fd.Z.mem_Atil fd.P _ a).1 h1
    rw [ha] at h2
    exact mem_of_mem_EbarOf hEN (Subgroup.map_subtype_le _) hinjE he₀ h2
  have hKC : ∀ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2},
      kZero p E (t q) ≤ Subgroup.centralizer ({e₀} : Set G) := fun q y hy => by
    have h1 : e₀ ∈ E ⊓ Subgroup.centralizer (kZero p E (t q) : Set G) := by
      rw [(hAtq q).2.2.1]
      exact he₀B q
    have h2 := Subgroup.mem_centralizer_iff.1 h1.2 y hy
    exact Subgroup.mem_centralizer_iff.2 fun z hz => by
      rw [Set.mem_singleton_iff.1 hz]
      exact h2.symm
  have hT : ∀ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2},
      ((kZero p E (t q)).subgroupOf (lieGenerated p E)).map
          (twistMap (lieGenerated p E) hf e fd.P) =
        planeP (u5FieldData f hf) q.1.1 q.1.2 (ne_of_lt q.2.1) := fun q =>
    map_subgroupOf_eq_planeP (lieGenerated p E) hf e fd.Z fd.P (hKI q) (hAtq q).2.1 hf2
      (ne_of_lt q.2.1) (by
        obtain ⟨b, hb, hbm, hpar⟩ := hex q (genVec p q.1.1 q.1.2) (genVec_self (ne_of_lt q.2.1))
        exact ⟨b, hb, fun y hy => (Subgroup.mem_centralizer_iff.1 hbm.2 y hy).symm, hpar⟩)
  have hQC : Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e₀} : Set G) := hQle
  have hQI : Q ≤ lieGenerated p E := hQle.trans inf_le_left
  have hQp : ⁅Q, Q⁆ = Q := commutator_eq_of_subgroupOf hQC (Subgroup.isPerfect_iff.1 hQc.1.1)
  have hQip := commutator_subgroupOf_eq hQI hQp
  have hfixQ : ∀ y ∈ Q.subgroupOf (lieGenerated p E),
      primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) (fd.Z.dgU a)
          (twistMap (lieGenerated p E) hf e fd.P y) =
        twistMap (lieGenerated p E) hf e fd.P y := by
    intro y hy
    have hyc : (y : G) ∈ Subgroup.centralizer ({e₀} : Set G) := (hQle hy).2
    have := Subgroup.mem_centralizer_iff.1 hyc e₀ rfl
    exact fix_modelTwist (lieGenerated p E) hf e fd.Z fd.P a hN₀ ha this
  have hle := le_iSup_of_fixed_perfect (ker_twistMap_le (lieGenerated p E) hf e fd.P) fd.Z a hT
    hQip hfixQ
  have hQM : Q ≤ ⨆ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2}, kZero p E (t q) := by
    have h1 := Subgroup.map_mono (f := (lieGenerated p E).subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hQI, Subgroup.map_iSup] at h1
    refine h1.trans (iSup_le fun q => ?_)
    rw [Subgroup.map_subgroupOf_eq_of_le (hKI q)]
    exact le_iSup (fun q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2} => kZero p E (t q)) q
  refine hQM.trans (iSup_le fun q => ?_)
  intro x hx
  exact Subgroup.subset_closure ⟨t q, ht q, kZero p E (t q), hKt q, hKC q, hx⟩

theorem kfCompLayerFive_of (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hAt : KFU5At) (hEin : U5EInndiag) :
    KFCompLayerFive :=
  kfCompLayerFive_of_gen hS h82 hAt (kfCompGenFive_of hAt hEin)

end CFSG.RankThree.PartOne.K159
