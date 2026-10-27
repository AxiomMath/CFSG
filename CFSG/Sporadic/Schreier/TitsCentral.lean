module

public import CFSG.Sporadic.Schreier.TitsStab
public import CFSG.Sporadic.Schreier.TitsCentralCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.ChainArrays

theorem commute_closure {G : Type*} [Group G] {g : G} {T : Set G} (h : ∀ t ∈ T, g * t = t * g) :
    ∀ x ∈ Subgroup.closure T, g * x = x * g := by
  have hle : Subgroup.closure T ≤ Subgroup.centralizer {g} :=
    (Subgroup.closure_le _).2 fun t ht => Subgroup.mem_centralizer_singleton_iff.2 (h t ht).symm
  exact fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem mem_centralizer_closure_iff {G : Type*} [Group G] {g : G} {T : Set G} :
    g ∈ Subgroup.centralizer (Subgroup.closure T : Set G) ↔ ∀ t ∈ T, g * t = t * g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · exact fun h t ht => (h t (Subgroup.subset_closure ht)).symm
  · exact fun h x hx => (commute_closure h x hx).symm

theorem extract_get {S : Array (Array ℕ)} {k i : ℕ} (hk : k ≤ S.size) (hi : i < k) :
    (S.extract 0 k)[i]! = S[i]! := by
  rw [getElem!_pos _ i (by simp [Nat.min_eq_left hk]; exact hi), getElem!_pos S i (by omega),
    Array.getElem_extract]
  simp

theorem mem_gens_iff {S : Array (Array ℕ)} {k s : ℕ} (hk : k ≤ S.size) {b : List ℕ}
    {hb : (finList 1755 b).Nodup} {D : List (List ℤ)} {ws : List (List ℤ)}
    (horig : (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
      (wordsArr k s D)).original.toList = ws.map (wordIn 13 titsT)) (g : Equiv.Perm (Fin 1755)) :
    g ∈ {g | ∃ w ∈ ws, wordIn 13 titsT w = g} ↔ ∃ i < k, permOfArr 1755 S[i]! = g := by
  rw [← RawSchreierDatum.mem_ofArrays_original (W := wordsArr k s D) (hk := hk)
    (base := finList 1755 b) (hb := hb) (hn := by norm_num), horig]
  simp

theorem commutesAll_wordGroup_iff {S : Array (Array ℕ)} {k s : ℕ} (hk : k ≤ S.size) {b : List ℕ}
    {hb : (finList 1755 b).Nodup} {D : List (List ℤ)} {ws : List (List ℤ)}
    (hP : allPermsOK 1755 S = true)
    (horig : (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
      (wordsArr k s D)).original.toList = ws.map (wordIn 13 titsT))
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    commutesAll 1755 a (S.extract 0 k) = true ↔
      g ∈ Subgroup.centralizer (titsWordGroup ws : Set (Equiv.Perm (Fin 1755))) := by
  have hsz : (S.extract 0 k).size = k := by simp [Nat.min_eq_left hk]
  rw [commutesAll_iff ha (gs := fun i => permOfArr 1755 S[i]!) (fun i hi => by
      rw [hsz] at hi
      rw [extract_get hk hi]
      exact rep_of_allPermsOK hP (by omega)), titsWordGroup, mem_centralizer_closure_iff, hsz]
  constructor
  · intro h t ht
    obtain ⟨i, hi, rfl⟩ := (mem_gens_iff hk horig t).1 ht
    exact h i hi
  · intro h i hi
    exact h _ ((mem_gens_iff hk horig _).2 ⟨i, hi, rfl⟩)

theorem mem_of_sift_ofArrays {S : Array (Array ℕ)} {k s : ℕ} {hk : k ≤ S.size} {b : List ℕ}
    {hb : (finList 1755 b).Nodup} {D : List (List ℤ)} (hP : allPermsOK 1755 S = true)
    (hc : rawChainOK 1755 (S.extract 0 k) S (baseArr 1755 b) (wordsArr k s D) 4 = true)
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 (rawLevels 1755 S (baseArr 1755 b)) (baseArr 1755 b) 0 a = true) :
    g ∈ (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
      (wordsArr k s D)).originalSubgroup :=
  (siftA_iff_mem_ofArrays hP (by norm_num) hc ha).1 h

theorem mem_titsS_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 a = true) : g ∈ titsS := by
  rw [← titsQS_facts.2.2.1]
  exact mem_of_sift_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsLocalChains_check.2.1 ha h

theorem mem_titsH_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 a = true) : g ∈ titsH := by
  rw [← titsQH_facts.2.2.1]
  exact mem_of_sift_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsLocalChains_check.1 ha h

theorem mem_titsN_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 a = true) : g ∈ titsN := by
  rw [← titsQN_facts.2.2.1]
  exact mem_of_sift_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsLocalChains_check.2.2.1 ha h

theorem mem_titsJ_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 a = true) : g ∈ titsJ := by
  rw [← titsQJ_facts.2.2.1]
  exact mem_of_sift_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsLocalChains_check.2.2.2.1 ha h

theorem mem_titsK_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 a = true) : g ∈ titsK := by
  rw [← titsQK_facts.2.2.1]
  exact mem_of_sift_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsLocalChains_check.2.2.2.2.1 ha h

theorem titsZ_rep :
    Rep 1755 titsZArr titsZ :=
  rep_wordArr_titsT titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsZ_mem_titsS :
    titsZ ∈ titsS :=
  mem_titsS_of_sift titsZ_rep titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsZ_ne_one :
    titsZ ≠ 1 := by
  intro h
  have := (eqA_iff titsZ_rep rep_idA).2 h
  rw [titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem titsZ_mul_self :
    titsZ * titsZ = 1 :=
  eq_of_eqA (rep_compA titsZ_rep titsZ_rep) rep_idA
    titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem orderOf_titsZ :
    orderOf titsZ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact titsZ_mul_self) titsZ_ne_one

theorem titsZ_mem_centralizer_S :
    titsZ ∈ Subgroup.centralizer (titsS : Set (Equiv.Perm (Fin 1755))) :=
  (commutesAll_wordGroup_iff (hk := by rw [titsSArrs_size]; norm_num) (hb := by decide)
    (s := 9) (D := titsSDerivations) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsQS_facts.2.1 titsZ_rep).1 titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsZ_mem_centralizer_H :
    titsZ ∈ Subgroup.centralizer (titsH : Set (Equiv.Perm (Fin 1755))) :=
  (commutesAll_wordGroup_iff (hk := by rw [titsHArrs_size]; norm_num) (hb := by decide)
    (s := 9) (D := titsHDerivations) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsQH_facts.2.1 titsZ_rep).1 titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem titsH_le_centralizer_z :
    titsH ≤ Subgroup.centralizer {titsZ} := fun h hh =>
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 titsZ_mem_centralizer_H h hh)

theorem titsS_chainArrays :
    ChainArrays titsQS (titsSArrs.extract 0 3) titsSArrs (baseArr 1755 titsSBase)
      (wordsArr 3 9 titsSDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsH_chainArrays :
    ChainArrays titsQH (titsHArrs.extract 0 3) titsHArrs (baseArr 1755 titsHBase)
      (wordsArr 3 9 titsHDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsN_chainArrays :
    ChainArrays titsQN (titsNArrs.extract 0 4) titsNArrs (baseArr 1755 titsNBase)
      (wordsArr 4 10 titsNDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsS_center :
    ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) = {1, titsZ} := by
  ext g
  simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Subgroup.coe_subtype,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hcen : (x : Equiv.Perm (Fin 1755)) ∈
        Subgroup.centralizer (titsS : Set (Equiv.Perm (Fin 1755))) :=
      Subgroup.mem_centralizer_iff.2 fun s hs =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨s, hs⟩)
    have hxS : (x : Equiv.Perm (Fin 1755)) ∈ titsQS.originalSubgroup := by
      rw [titsQS_facts.2.2.1]
      exact x.2
    obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.2.1 (by show (finList 1755 titsSBase).length = 5; simp [finList,
        titsCentral_check.1]) titsCentral_check.2.2.2.1 hxS
    have hcomm := (commutesAll_wordGroup_iff (hk := by rw [titsSArrs_size]; norm_num)
      (hb := by decide) (s := 9) (D := titsSDerivations)
      titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 titsQS_facts.2.1 ha).2 hcen
    simp only [hcomm, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
    rcases hp with h1 | h1
    · exact Or.inl (eq_of_eqA ha rep_idA h1)
    · exact Or.inr (eq_of_eqA ha titsZ_rep h1)
  · rintro (rfl | rfl)
    · exact ⟨1, one_mem _, rfl⟩
    · refine ⟨⟨titsZ, titsZ_mem_titsS⟩, Subgroup.mem_center_iff.2 fun s => ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 titsZ_mem_centralizer_S s s.2)

theorem ncard_list_set {α : Type*} [DecidableEq α] {L : List α} (h : L.Nodup) :
    ({g | g ∈ L} : Set α).ncard = L.length := by
  rw [show ({g | g ∈ L} : Set α) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup h]

theorem nodup_map_permOfArr {L : List (Array ℕ)}
    (hinv : ∀ c ∈ L, isInvA 1755 c (invCand 1755 c) = true)
    (hd : L.Pairwise fun a b => eqA 1755 a b = false) :
    (L.map (permOfArr 1755)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine hd.imp_of_mem fun {a b} ha hb hab e => ?_
  have := (eqA_iff (rep_permOfArr (hinv a ha)).1 (rep_permOfArr (hinv b hb)).1).2 e
  rw [hab] at this
  exact Bool.false_ne_true this

theorem titsCHJ_facts {c : Array ℕ} (hc : c ∈ titsCHJ) :
    isInvA 1755 c (invCand 1755 c) = true ∧ commutesAll 1755 c (titsJArrs.extract 0 4) = true ∧
      siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 c = true ∧
      siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 c = true := by
  have := List.all_eq_true.1 titsCentral_check.2.2.2.2.2.2.2.2.1 c hc
  simpa [Bool.and_eq_true, and_assoc] using this

theorem titsCNK_facts {c : Array ℕ} (hc : c ∈ titsCNK) :
    isInvA 1755 c (invCand 1755 c) = true ∧ commutesAll 1755 c (titsKArrs.extract 0 2) = true ∧
      siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 c = true ∧
      siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 c = true := by
  have := List.all_eq_true.1 titsCentral_check.2.2.2.2.2.2.2.2.2.1 c hc
  simpa [Bool.and_eq_true, and_assoc] using this

theorem centralizer_J_iff
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    commutesAll 1755 a (titsJArrs.extract 0 4) = true ↔
      g ∈ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
  commutesAll_wordGroup_iff (hk := by rw [titsJArrs_size]; norm_num) (hb := by decide) (s := 9)
    (D := titsJDerivations) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsQJ_facts.2.1 ha

theorem centralizer_K_iff
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    commutesAll 1755 a (titsKArrs.extract 0 2) = true ↔
      g ∈ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
  commutesAll_wordGroup_iff (hk := by rw [titsKArrs_size]; norm_num) (hb := by decide) (s := 7)
    (D := titsKDerivations) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    titsQK_facts.2.1 ha

theorem titsCHJ_eq :
    ((titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) =
      {g | g ∈ titsCHJ.map (permOfArr 1755)} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hgH, hgC⟩
    have hgQ : g ∈ titsQH.originalSubgroup := by rw [titsQH_facts.2.2.1]; exact hgH
    obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.1 (by show (finList 1755 titsHBase).length = 5; simp [finList,
        titsCentral_check.2.1]) titsCentral_check.2.2.2.2.1 hgQ
    have hcomm := (centralizer_J_iff ha).2 hgC
    simp only [hcomm, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨c, hc, hac⟩ := hp
    refine ⟨c, hc, ?_⟩
    exact (eq_of_eqA ha (rep_permOfArr (titsCHJ_facts hc).1).1 hac).symm
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hinv, hcomm, hH, -⟩ := titsCHJ_facts hc
    have hr := (rep_permOfArr hinv).1
    exact ⟨mem_titsH_of_sift hr hH, (centralizer_J_iff hr).1 hcomm⟩

theorem titsCNK_eq :
    ((titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) =
      {g | g ∈ titsCNK.map (permOfArr 1755)} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hgN, hgC⟩
    have hgQ : g ∈ titsQN.originalSubgroup := by rw [titsQN_facts.2.2.1]; exact hgN
    obtain ⟨a, ha, hp⟩ := all5_spec titsN_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.2.2.1 (by show (finList 1755 titsNBase).length = 5; simp [finList,
        titsCentral_check.2.2.1]) titsCentral_check.2.2.2.2.2.1 hgQ
    have hcomm := (centralizer_K_iff ha).2 hgC
    simp only [hcomm, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨c, hc, hac⟩ := hp
    refine ⟨c, hc, ?_⟩
    exact (eq_of_eqA ha (rep_permOfArr (titsCNK_facts hc).1).1 hac).symm
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hinv, hcomm, hN, -⟩ := titsCNK_facts hc
    have hr := (rep_permOfArr hinv).1
    exact ⟨mem_titsN_of_sift hr hN, (centralizer_K_iff hr).1 hcomm⟩

theorem card_CHJ :
    Nat.card (titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) = 2 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCHJ_eq,
    ncard_list_set (nodup_map_permOfArr (fun c hc => (titsCHJ_facts hc).1)
      titsCentral_check.2.2.2.2.2.2.2.2.2.2.1), List.length_map, titsCentral_check.2.2.2.2.2.2.1]

theorem card_CNK :
    Nat.card (titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) = 4 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCNK_eq,
    ncard_list_set (nodup_map_permOfArr (fun c hc => (titsCNK_facts hc).1)
      titsCentral_check.2.2.2.2.2.2.2.2.2.2.2.1), List.length_map,
    titsCentral_check.2.2.2.2.2.2.2.1]

theorem CHJ_le_J :

    titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) ≤ titsJ := by
  intro g hg
  have hg' : g ∈ ((titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := hg
  rw [titsCHJ_eq] at hg'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨hinv, -, -, hJ⟩ := titsCHJ_facts hc
  exact mem_titsJ_of_sift (rep_permOfArr hinv).1 hJ

theorem CNK_le_K :

    titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) ≤ titsK := by
  intro g hg
  have hg' : g ∈ ((titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := hg
  rw [titsCNK_eq] at hg'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨hinv, -, -, hK⟩ := titsCNK_facts hc
  exact mem_titsK_of_sift (rep_permOfArr hinv).1 hK

theorem AT_Tits_local_center_and_centralizer_checks :
    orderOf titsZ = 2 ∧
    ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) = {1, titsZ} ∧
    titsH ≤ Subgroup.centralizer {titsZ} ∧
    Nat.card (titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) = 2 ∧
    titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) ≤ titsJ ∧
    Nat.card (titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) = 4 ∧
    titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) ≤ titsK :=
  ⟨orderOf_titsZ, titsS_center, titsH_le_centralizer_z, card_CHJ, CHJ_le_J, card_CNK, CNK_le_K⟩

end CFSG.Sporadic.Schreier.Tits
