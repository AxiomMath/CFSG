module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGen
public import Certificates.Data.Item434SporGenKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!)

variable {n : ℕ}

theorem rep_powN {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    ∀ k : ℕ, Rep n (powN n t k) (g ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [pow_succ']; exact rep_compA h (rep_powN h k)

theorem mul_comm_of_commN {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (hc : commN n t u = true) : g * h = h * g :=
  eq_of_eqA (rep_compA ht hu) (rep_compA hu ht) hc

theorem rep_pN {e₁ e₂ : Array ℕ} {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : Rep n e₁ g₁)
    (h₂ : Rep n e₂ g₂) (ab : ℕ × ℕ) : Rep n (pN n e₁ e₂ ab) (g₁ ^ ab.1 * g₂ ^ ab.2) :=
  rep_compA (rep_powN h₁ _) (rep_powN h₂ _)

section Chain

variable {σ : Array (Array ℕ)} {D : List (List ℤ)} {base : List (Fin n)} {chunks : ℕ}

theorem size_le_pushWords : σ.size ≤ (pushWords n σ D).size := by
  rw [size_pushWords]
  omega

theorem ofArrays_originalSubgroup_eq (hn : 1 ≤ n) (hb : base.Nodup) :
    (RawSchreierDatum.ofArrays n hn (pushWords n σ D) σ.size size_le_pushWords base hb
      (wordsOf σ.size D)).originalSubgroup =
      Subgroup.closure (Set.range fun i : Fin σ.size => permOfArr n σ[(i : ℕ)]!) := by
  rw [ofArrays_originalSubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by rw [pushWords_getElem! _ _ hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, by rw [pushWords_getElem! _ _ i.2]⟩

theorem mem_closure_of_sift (hn : 1 ≤ n) (hb : base.Nodup) (hc : 0 < chunks)
    (hchain : rawChainOK n ((pushWords n σ D).extract 0 σ.size) (pushWords n σ D)
      (base.map Fin.val).toArray (wordsOf σ.size D) chunks = true)
    {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hs : siftA n (rawLevels n (pushWords n σ D) (base.map Fin.val).toArray)
      (base.map Fin.val).toArray 0 t = true) :
    g ∈ Subgroup.closure (Set.range fun i : Fin σ.size => permOfArr n σ[(i : ℕ)]!) := by
  rw [← ofArrays_originalSubgroup_eq (D := D) hn hb]
  exact (ofArrays_mem_iff (hn := hn) (hk := size_le_pushWords) (hb := hb) hc hchain ht).1 hs

theorem closure_eq_of_chain (hn : 1 ≤ n) (hb : base.Nodup) (hc : 0 < chunks)
    (hchain : rawChainOK n ((pushWords n σ D).extract 0 σ.size) (pushWords n σ D)
      (base.map Fin.val).toArray (wordsOf σ.size D) chunks = true)
    {X : Subgroup (Equiv.Perm (Fin n))} {gens : Set (Equiv.Perm (Fin n))}
    (hX : Subgroup.closure gens = X)
    (hcard : (rawOrbitSizes n (pushWords n σ D) (base.map Fin.val).toArray).prod = Nat.card X)
    (hsift : ∀ g ∈ gens, ∃ t : Array ℕ, Rep n t g ∧
      siftA n (rawLevels n (pushWords n σ D) (base.map Fin.val).toArray)
        (base.map Fin.val).toArray 0 t = true) :
    Subgroup.closure (Set.range fun i : Fin σ.size => permOfArr n σ[(i : ℕ)]!) = X := by
  have hQcard := ofArrays_card (hn := hn) (hk := size_le_pushWords) (hb := hb) hc hchain
  rw [ofArrays_originalSubgroup_eq hn hb] at hQcard
  have hle : X ≤ Subgroup.closure (Set.range fun i : Fin σ.size => permOfArr n σ[(i : ℕ)]!) := by
    rw [← hX, Subgroup.closure_le]
    intro g hg
    obtain ⟨t, ht, hs⟩ := hsift g hg
    exact mem_closure_of_sift hn hb hc hchain ht hs
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hcard])).symm

theorem rep_sig_of_chain
    (hchain : rawChainOK n ((pushWords n σ D).extract 0 σ.size) (pushWords n σ D)
      (base.map Fin.val).toArray (wordsOf σ.size D) chunks = true) (i : Fin σ.size) :
    Rep n σ[(i : ℕ)]! (permOfArr n σ[(i : ℕ)]!) := by
  have h := rep_permOfArr_of_chainOK hchain (j := i) (size_le_pushWords.trans_lt' i.2)
  rwa [pushWords_getElem! _ _ i.2] at h

end Chain

theorem eq_of_mem_zpowers_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : x ^ k = x ^ (k % 3) := by
    have e : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
    conv_lhs => rw [e]
    rw [zpow_add, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hx, one_zpow,
      one_mul]
  rw [hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; exact zpow_zero x
  · right; left; exact zpow_one x
  · right; right; exact zpow_natCast x 2

section Model

variable {X : Subgroup (Equiv.Perm (Fin n))}

theorem card_closure_of_e9Check {e₁ e₂ : Array ℕ} {g₁ g₂ : X} (h₁ : Rep n e₁ (g₁ : Equiv.Perm _))
    (h₂ : Rep n e₂ (g₂ : Equiv.Perm _)) (h : e9Check n e₁ e₂ = true) :
    Nat.card (Subgroup.closure ({g₁, g₂} : Set X)) = 9 := by
  simp only [e9Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h13⟩, h23⟩, hc⟩, h1⟩, h21⟩, h2e⟩, h2e2⟩ := h
  have hval : ∀ {a b : X}, (a : Equiv.Perm (Fin n)) = b → a = b := fun h => Subtype.ext h
  have hx : g₁ ^ 3 = 1 := hval (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact eq_of_eqA (rep_powN h₁ 3) rep_idA h13)
  have hy : g₂ ^ 3 = 1 := hval (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact eq_of_eqA (rep_powN h₂ 3) rep_idA h23)
  have hxy : Commute g₁ g₂ := hval (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact mul_comm_of_commN h₁ h₂ hc)
  have hne : ∀ {t u : Array ℕ} {a b : Equiv.Perm (Fin n)}, Rep n t a → Rep n u b →
      eqA n t u = false → a ≠ b := fun ht hu he hab => by
    rw [(eqA_iff ht hu).2 hab] at he
    exact Bool.noConfusion he
  have hx1 : g₁ ≠ 1 := fun h => hne h₁ rep_idA h1 (congrArg Subtype.val h)
  refine Asc83Table.card_closure_pair_eq_nine hx hy hxy hx1 fun hmem => ?_
  rcases eq_of_mem_zpowers_of_pow_three hx hmem with h | h | h
  · exact hne h₂ rep_idA h21 (congrArg Subtype.val h)
  · exact hne h₂ h₁ h2e (congrArg Subtype.val h)
  · exact hne h₂ (rep_powN h₁ 2) h2e2 (by rw [h, Subgroup.coe_pow])

theorem fixGen_of_sigCheck {σ : Array (Array ℕ)}
    (hσX : Subgroup.closure (Set.range fun i : Fin σ.size => permOfArr n σ[(i : ℕ)]!) = X)
    (hσ : ∀ i : Fin σ.size, Rep n σ[(i : ℕ)]! (permOfArr n σ[(i : ℕ)]!))
    {e₁ e₂ : Array ℕ} {g₁ g₂ : X} (h₁ : Rep n e₁ (g₁ : Equiv.Perm _))
    (h₂ : Rep n e₂ (g₂ : Equiv.Perm _)) {ords : List ℕ} {ps : List (ℕ × ℕ)}
    (hsig : sigCheck n σ ords ps e₁ e₂ = true) :
    FixGen (Subgroup.closure ({g₁, g₂} : Set X)) := by
  have hmem : ∀ i : Fin σ.size, permOfArr n σ[(i : ℕ)]! ∈ X := fun i =>
    hσX ▸ Subgroup.subset_closure ⟨i, rfl⟩
  set s : Fin σ.size → X := fun i => ⟨permOfArr n σ[(i : ℕ)]!, hmem i⟩ with hs
  refine ⟨Set.range s, ?_, ?_⟩
  · have htop : Subgroup.closure (Set.range s) = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      exact hσX
    rw [htop]
  · rintro _ ⟨i, rfl⟩
    have hi := allLt_spec hsig i.2
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hi
    obtain ⟨⟨⟨hpow, h3⟩, hcomm⟩, hp1⟩ := hi
    set m := ords.getD i 0
    set ab := ps.getD i (0, 0)
    have hpow' : s i ^ m = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact eq_of_eqA (rep_powN (hσ i) m) rep_idA hpow)
    refine ⟨?_, g₁ ^ ab.1 * g₂ ^ ab.2, ?_, ?_, ?_⟩
    · have hd : orderOf (s i) ∣ m := orderOf_dvd_of_pow_eq_one hpow'
      have h3m : ¬ 3 ∣ m := fun h => h3 (Nat.mod_eq_zero_of_dvd h)
      exact Nat.Coprime.coprime_dvd_left hd
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3m))
    · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · intro h1
      have hrep := rep_pN h₁ h₂ ab
      have h1' : (g₁ : Equiv.Perm (Fin n)) ^ ab.1 * (g₂ : Equiv.Perm (Fin n)) ^ ab.2 = 1 := by
        have := congrArg Subtype.val h1
        rwa [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [(eqA_iff hrep rep_idA).2 h1'] at hp1
      exact Bool.noConfusion hp1
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow,
        Subgroup.coe_pow]
      exact (mul_comm_of_commN (hσ i) (rep_pN h₁ h₂ ab) hcomm).symm

end Model

theorem kill9_of_sylow {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : Nat.card E = 3 ^ (Nat.card Y).factorization 3) (hE9 : Nat.card E = 9)
    (hF : FixGen E) (P : Subgroup Y) (_hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) : FixGen P ∨ NoSignalizer P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hE hPp
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) ≤ Nat.card P := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9, hP9]
  rw [Subgroup.eq_of_le_of_card_ge hg hcard]
  exact Or.inl (hF.map_conj g)

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
