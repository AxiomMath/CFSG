module

public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheck
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Assembly.Defs
public import CFSG.Monster.B.Fischer.Fi22OuterBase

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer

section Family

theorem exists_famHom {H X : Type*} [Group H] (f : H →* Equiv.Perm X) {m : ℕ}
    {s : Fin m → X} (hs : Function.Injective s) (hinv : ∀ h j, ∃ j', s j' = f h (s j)) :
    ∃ φ : H →* Equiv.Perm (Fin m), ∀ h j, s (φ h j) = f h (s j) := by
  classical
  let act : MulAction H (Fin m) :=
    { smul := fun h j => Classical.choose (hinv h j)
      one_smul := fun j => hs (by
        show s (Classical.choose (hinv 1 j)) = s j
        rw [Classical.choose_spec (hinv 1 j), map_one, Equiv.Perm.one_apply])
      mul_smul := fun h k j => hs (by
        show s (Classical.choose (hinv (h * k) j)) =
          s (Classical.choose (hinv h (Classical.choose (hinv k j))))
        rw [Classical.choose_spec (hinv (h * k) j), Classical.choose_spec (hinv h _),
          Classical.choose_spec (hinv k j), map_mul, Equiv.Perm.mul_apply]) }
  exact ⟨@MulAction.toPermHom H (Fin m) _ act, fun h j => Classical.choose_spec (hinv h j)⟩

theorem famInv_closure {G X : Type*} [Group G] (f : G →* Equiv.Perm X) {m : ℕ}
    {s : Fin m → X} (hs : Function.Injective s) {T : Set G}
    (hT : ∀ t ∈ T, ∀ j, ∃ j', s j' = f t (s j)) {g : G} (hg : g ∈ Subgroup.closure T) :
    ∀ j, ∃ j', s j' = f g (s j) := by
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact hT t ht
  | one => exact fun j => ⟨j, by rw [map_one, Equiv.Perm.one_apply]⟩
  | mul g h _ _ hg hh =>
    intro j
    obtain ⟨j₁, hj₁⟩ := hh j
    obtain ⟨j₂, hj₂⟩ := hg j₁
    exact ⟨j₂, by rw [hj₂, hj₁, map_mul, Equiv.Perm.mul_apply]⟩
  | inv g _ hg =>
    choose σ hσ using hg
    have hσi : Function.Injective σ := fun a b hab => by
      have := (hσ a).symm.trans ((congrArg s hab).trans (hσ b))
      exact hs ((f g).injective this)
    have hσs := Finite.injective_iff_surjective.1 hσi
    intro j
    obtain ⟨i, hi⟩ := hσs j
    refine ⟨i, ?_⟩
    rw [map_inv, eq_comm, Equiv.Perm.inv_eq_iff_eq, ← hi]
    exact hσ i

@[expose] def conjPerm {G : Type*} [Group G] : G →* Equiv.Perm G :=
  MonoidHom.comp (MulAut.toPerm (M := G)) (MulAut.conj (G := G))

theorem conjPerm_apply {G : Type*} [Group G] (g x : G) : conjPerm g x = g * x * g⁻¹ := rfl

end Family

theorem map_getElem! {f : Array ℕ → Array ℕ} {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (S.map f)[j]! = f S[j]! := by
  rw [getElem!_pos (S.map f) j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem rep_conjA {n : ℕ} {g x : Array ℕ} {G X : Equiv.Perm (Fin n)} (hg : Rep n g G)
    (hgi : isInvA n g (invCand n g) = true) (hx : Rep n x X) :
    Rep n (conjA n g x) (G * X * G⁻¹) := by
  rw [mul_assoc]
  exact rep_compA hg (rep_compA hx (rep_inv_of_isInvA hg hgi))

@[expose] def fi24KChain : RawSchreierDatum 504 :=
  RawSchreierDatum.ofArrays 504 (by decide) fi24KStrong (min 2 fi24KStrong.size)
    (Nat.min_le_right _ _) (fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 7, 6]) (by decide)
    fi24KWords

@[expose] def fi24K : Subgroup (Equiv.Perm (Fin 504)) := fi24KChain.originalSubgroup

theorem fi24KChain_facts : fi24KStrong.size = 12 ∧
    rawChainOK 504 (fi24KStrong.extract 0 (min 2 fi24KStrong.size)) fi24KStrong fi24KBase
      fi24KWords 4 = true ∧
    (rawOrbitSizes 504 fi24KStrong fi24KBase).prod = 80263249920 := by
  have h := fi24KChain_certificate
  unfold fi24KChainOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hk : min 2 fi24KStrong.size = 2 := by rw [h1]; rfl
  refine ⟨h1, ?_, h3⟩
  rw [hk]
  exact h2

theorem fi24K_min :
    min 2 fi24KStrong.size = 2 := by rw [fi24KChain_facts.1]; rfl

theorem fi24KChain_arrays : ChainArrays fi24KChain
    (fi24KStrong.extract 0 (min 2 fi24KStrong.size)) fi24KStrong fi24KBase fi24KWords := by
  have h := chainArrays_ofArrays (n := 504) (hn := by decide) (k := min 2 fi24KStrong.size)
    (hk := Nat.min_le_right _ _) (base := fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 7, 6])
    (hb := by decide) (W := fi24KWords) (chainCheckFacts fi24KChain_facts.2.1).strong_inv
  have hb : ((fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 7, 6]).map Fin.val).toArray =
      fi24KBase := rfl
  rw [hb] at h
  exact h

theorem card_fi24K : Nat.card fi24K = 80263249920 := by
  rw [fi24K, card_originalSubgroup_of_chainOK fi24KChain_arrays (by norm_num)
    fi24KChain_facts.2.1, fi24KChain_facts.2.2]

theorem mem_fi24K_of_siftA
    {g : Array ℕ} {G : Equiv.Perm (Fin 504)} (hG : Rep 504 g G)
    (h : siftA 504 (rawLevels 504 fi24KStrong fi24KBase) fi24KBase 0 g = true) : G ∈ fi24K :=
  (siftA_iff_mem_originalSubgroup fi24KChain_arrays (by norm_num) fi24KChain_facts.2.1 hG).1 h

theorem fi24K_isInvA {j : ℕ} (hj : j < 12) :
    isInvA 504 fi24KStrong[j]! (invCand 504 fi24KStrong[j]!) = true := by
  have hj' : j < fi24KStrong.size := by rw [fi24KChain_facts.1]; exact hj
  have h := (chainCheckFacts fi24KChain_facts.2.1).strong_inv j hj'
  rwa [rawInvs, map_getElem! hj'] at h

@[expose] def fi24Sa : Equiv.Perm (Fin 504) := permOfArr 504 fi24KStrong[0]!

@[expose] def fi24Sb : Equiv.Perm (Fin 504) := permOfArr 504 fi24KStrong[1]!

theorem rep_fi24Sa : Rep 504 fi24KStrong[0]! fi24Sa :=
  (rep_permOfArr (fi24K_isInvA (by norm_num))).1

theorem rep_fi24Sb : Rep 504 fi24KStrong[1]! fi24Sb :=
  (rep_permOfArr (fi24K_isInvA (by norm_num))).1

theorem fi24K_eq : fi24K = Subgroup.closure {fi24Sa, fi24Sb} := by
  rw [fi24K, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ fi24KChain.original.toList ↔ _
  rw [fi24KChain, RawSchreierDatum.mem_ofArrays_original, fi24K_min]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem fi24Sa_mem : fi24Sa ∈ fi24K := by
  rw [fi24K_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem fi24Sb_mem : fi24Sb ∈ fi24K := by
  rw [fi24K_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def fi24PChain : RawSchreierDatum 378 :=
  RawSchreierDatum.ofArrays 378 (by decide) fi24PStrong (min 2 fi24PStrong.size)
    (Nat.min_le_right _ _) (fi22FinList 378 (by decide) [0, 1, 2, 5]) (by decide) fi24PWords

@[expose] def fi24P : Subgroup (Equiv.Perm (Fin 378)) := fi24PChain.originalSubgroup

theorem fi24PChain_facts : fi24PStrong.size = 10 ∧
    rawChainOK 378 (fi24PStrong.extract 0 (min 2 fi24PStrong.size)) fi24PStrong fi24PBase
      fi24PWords 4 = true ∧
    (rawOrbitSizes 378 fi24PStrong fi24PBase).prod = 19595520 := by
  have h := fi24PChain_certificate
  unfold fi24PChainOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hk : min 2 fi24PStrong.size = 2 := by rw [h1]; rfl
  refine ⟨h1, ?_, h3⟩
  rw [hk]
  exact h2

theorem fi24P_min :
    min 2 fi24PStrong.size = 2 := by rw [fi24PChain_facts.1]; rfl

theorem fi24PChain_arrays : ChainArrays fi24PChain
    (fi24PStrong.extract 0 (min 2 fi24PStrong.size)) fi24PStrong fi24PBase fi24PWords := by
  have h := chainArrays_ofArrays (n := 378) (hn := by decide) (k := min 2 fi24PStrong.size)
    (hk := Nat.min_le_right _ _) (base := fi22FinList 378 (by decide) [0, 1, 2, 5])
    (hb := by decide) (W := fi24PWords) (chainCheckFacts fi24PChain_facts.2.1).strong_inv
  have hb : ((fi22FinList 378 (by decide) [0, 1, 2, 5]).map Fin.val).toArray = fi24PBase := rfl
  rw [hb] at h
  exact h

theorem card_fi24P : Nat.card fi24P = 19595520 := by
  rw [fi24P, card_originalSubgroup_of_chainOK fi24PChain_arrays (by norm_num)
    fi24PChain_facts.2.1, fi24PChain_facts.2.2]

theorem fi24P_isInvA {j : ℕ} (hj : j < 10) :
    isInvA 378 fi24PStrong[j]! (invCand 378 fi24PStrong[j]!) = true := by
  have hj' : j < fi24PStrong.size := by rw [fi24PChain_facts.1]; exact hj
  have h := (chainCheckFacts fi24PChain_facts.2.1).strong_inv j hj'
  rwa [rawInvs, map_getElem! hj'] at h

@[expose] def fi24Pa : Equiv.Perm (Fin 378) := permOfArr 378 fi24PStrong[0]!

@[expose] def fi24Pb : Equiv.Perm (Fin 378) := permOfArr 378 fi24PStrong[1]!

theorem rep_fi24Pa : Rep 378 fi24PStrong[0]! fi24Pa :=
  (rep_permOfArr (fi24P_isInvA (by norm_num))).1

theorem rep_fi24Pb : Rep 378 fi24PStrong[1]! fi24Pb :=
  (rep_permOfArr (fi24P_isInvA (by norm_num))).1

theorem fi24P_eq : fi24P = Subgroup.closure {fi24Pa, fi24Pb} := by
  rw [fi24P, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ fi24PChain.original.toList ↔ _
  rw [fi24PChain, RawSchreierDatum.mem_ofArrays_original, fi24P_min]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

@[expose] def fi24T : Array (Array ℕ) :=
  treeConj 504 fi24KStrong[0]! fi24KStrong[1]! fi24S0 fi24STree

theorem fi24S_facts : fi24T.size = 378 ∧
    (∀ j < 378, isInvA 504 fi24T[j]! (invCand 504 fi24T[j]!) = true ∧
      siftA 504 (rawLevels 504 fi24KStrong fi24KBase) fi24KBase 0 fi24T[j]! = true ∧
      eqA 504 (conjA 504 fi24KStrong[0]! fi24T[j]!) fi24T[(fi24PStrong[0]!)[j]!]! = true ∧
      eqA 504 (conjA 504 fi24KStrong[1]! fi24T[j]!) fi24T[(fi24PStrong[1]!)[j]!]! = true) ∧
    (∀ j < 378, ∀ k < 378, j = k ∨ eqA 504 fi24T[j]! fi24T[k]! = false) ∧
    (∀ j < 378, ∀ k < 378,
      eqA 504 (compA 504 fi24T[j]! fi24T[k]!) (compA 504 fi24T[k]! fi24T[j]!) = true) := by
  have h := fi24S_certificate
  unfold fi24SOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun j hj => ?_, fun j hj k hk => ?_,
    fun j hj k hk => allLt_spec (allLt_spec h4 hj) hk⟩
  · have := allLt_spec h2 hj
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h3 hj) hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact this

@[expose] def fi24Sj (j : Fin 378) : Equiv.Perm (Fin 504) := permOfArr 504 fi24T[j.1]!

theorem rep_fi24Sj (j : Fin 378) : Rep 504 fi24T[j.1]! (fi24Sj j) :=
  (rep_permOfArr (fi24S_facts.2.1 j j.2).1).1

theorem fi24Sj_injective :
    Function.Injective fi24Sj := fun j k h => by
  rcases fi24S_facts.2.2.1 j j.2 k k.2 with h' | h'
  · exact Fin.ext h'
  · have := (eqA_iff (rep_fi24Sj j) (rep_fi24Sj k)).2 h
    rw [this] at h'
    exact Bool.noConfusion h'

theorem fi24Sj_mem (j : Fin 378) : fi24Sj j ∈ fi24K :=
  mem_fi24K_of_siftA (rep_fi24Sj j) (fi24S_facts.2.1 j j.2).2.1

theorem fi24Sj_comm
    (j k : Fin 378) : fi24Sj j * fi24Sj k = fi24Sj k * fi24Sj j :=
  eq_of_eqA (rep_compA (rep_fi24Sj j) (rep_fi24Sj k)) (rep_compA (rep_fi24Sj k) (rep_fi24Sj j))
    (fi24S_facts.2.2.2 j j.2 k k.2)

theorem fi24Sj_conj_a
    (j : Fin 378) : fi24Sa * fi24Sj j * fi24Sa⁻¹ = fi24Sj (fi24Pa j) := by
  have h1 := rep_conjA rep_fi24Sa (fi24K_isInvA (by norm_num)) (rep_fi24Sj j)
  have e : fi24T[(fi24PStrong[0]!)[j.1]!]! = fi24T[(fi24Pa j).1]! := by
    rw [rep_fi24Pa.apply j.2]
  have h2 := rep_fi24Sj (fi24Pa j)
  rw [← e] at h2
  exact eq_of_eqA h1 h2 (fi24S_facts.2.1 j j.2).2.2.1

theorem fi24Sj_conj_b
    (j : Fin 378) : fi24Sb * fi24Sj j * fi24Sb⁻¹ = fi24Sj (fi24Pb j) := by
  have h1 := rep_conjA rep_fi24Sb (fi24K_isInvA (by norm_num)) (rep_fi24Sj j)
  have e : fi24T[(fi24PStrong[1]!)[j.1]!]! = fi24T[(fi24Pb j).1]! := by
    rw [rep_fi24Pb.apply j.2]
  have h2 := rep_fi24Sj (fi24Pb j)
  rw [← e] at h2
  exact eq_of_eqA h1 h2 (fi24S_facts.2.1 j j.2).2.2.2

theorem fi24K_conj_inv
    {g : Equiv.Perm (Fin 504)} (hg : g ∈ fi24K) (j : Fin 378) :
    ∃ j', fi24Sj j' = conjPerm g (fi24Sj j) := by
  rw [fi24K_eq] at hg
  refine famInv_closure conjPerm fi24Sj_injective ?_ hg j
  rintro t (rfl | rfl) i
  · exact ⟨fi24Pa i, (fi24Sj_conj_a i).symm⟩
  · exact ⟨fi24Pb i, (fi24Sj_conj_b i).symm⟩

theorem fi24K_selfCentralizing :
    ∃ N : Subgroup ↥fi24K, N.Normal ∧ Nat.card N = 4096 ∧
    Subgroup.centralizer (N : Set ↥fi24K) ≤ N := by
  obtain ⟨φ, hφ⟩ := exists_famHom (conjPerm.comp fi24K.subtype) fi24Sj_injective
    (fun h j => fi24K_conj_inv h.2 j)
  have hφ' : ∀ (h : ↥fi24K) j, fi24Sj (φ h j) = (h : Equiv.Perm (Fin 504)) * fi24Sj j *
      (h : Equiv.Perm (Fin 504))⁻¹ := hφ
  have hφa : φ ⟨fi24Sa, fi24Sa_mem⟩ = fi24Pa :=
    Equiv.ext fun j => fi24Sj_injective (by rw [hφ']; exact fi24Sj_conj_a j)
  have hφb : φ ⟨fi24Sb, fi24Sb_mem⟩ = fi24Pb :=
    Equiv.ext fun j => fi24Sj_injective (by rw [hφ']; exact fi24Sj_conj_b j)
  have hrange : φ.range = fi24P := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      have key : ∀ x ∈ Subgroup.closure ({fi24Sa, fi24Sb} : Set (Equiv.Perm (Fin 504))),
          ∀ hx : x ∈ fi24K, φ ⟨x, hx⟩ ∈ fi24P := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem t ht =>
          intro hx
          rcases ht with rfl | rfl
          · rw [hφa, fi24P_eq]
            exact Subgroup.subset_closure (Set.mem_insert _ _)
          · rw [hφb, fi24P_eq]
            exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        | one =>
          intro hx
          rw [show (⟨1, hx⟩ : ↥fi24K) = 1 from rfl, map_one]
          exact fi24P.one_mem
        | mul x y hx' hy' ihx ihy =>
          intro hxy
          have hx2 : x ∈ fi24K := by rw [fi24K_eq]; exact hx'
          have hy2 : y ∈ fi24K := by rw [fi24K_eq]; exact hy'
          rw [show (⟨x * y, hxy⟩ : ↥fi24K) = ⟨x, hx2⟩ * ⟨y, hy2⟩ from rfl, map_mul]
          exact fi24P.mul_mem (ihx hx2) (ihy hy2)
        | inv x hx' ihx =>
          intro hxi
          have hx2 : x ∈ fi24K := by rw [fi24K_eq]; exact hx'
          rw [show (⟨x⁻¹, hxi⟩ : ↥fi24K) = (⟨x, hx2⟩ : ↥fi24K)⁻¹ from rfl, map_inv]
          exact fi24P.inv_mem (ihx hx2)
      have hh : (h : Equiv.Perm (Fin 504)) ∈ Subgroup.closure {fi24Sa, fi24Sb} := by
        rw [← fi24K_eq]
        exact h.2
      exact key h hh h.2
    · rw [fi24P_eq, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨_, hφa⟩
      · exact ⟨_, hφb⟩
  have hcard : Nat.card φ.ker = 4096 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, card_fi24P, card_fi24K] at h
    omega
  have hsN : ∀ j, (⟨fi24Sj j, fi24Sj_mem j⟩ : ↥fi24K) ∈ φ.ker := fun j => by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun k => fi24Sj_injective ?_
    rw [hφ', Equiv.Perm.one_apply]
    show fi24Sj j * fi24Sj k * (fi24Sj j)⁻¹ = fi24Sj k
    rw [fi24Sj_comm j k, mul_inv_cancel_right]
  refine ⟨φ.ker, φ.normal_ker, hcard, fun z hz => ?_⟩
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun j => fi24Sj_injective ?_
  have hc := Subgroup.mem_centralizer_iff.1 hz _ (hsN j)
  have hc' : fi24Sj j * (z : Equiv.Perm (Fin 504)) = (z : Equiv.Perm (Fin 504)) * fi24Sj j :=
    congrArg Subtype.val hc
  rw [hφ', Equiv.Perm.one_apply, ← hc', mul_inv_cancel_right]

end CFSG.Sporadic.FischerOddCore
