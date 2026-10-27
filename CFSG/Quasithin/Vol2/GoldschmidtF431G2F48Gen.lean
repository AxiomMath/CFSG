module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qTorusCent

public section

namespace CFSG.Quasithin.H13.F431.G2.F48

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48

variable {X : Type} [Group X] {n : ℕ} (R : RankTwoSystem X n)

@[expose] def radList (n : ℕ) : Bool → List ℤ
  | true => intList 2 n
  | false => intList 1 ((n : ℤ) - 1)

theorem radList_nodup (n : ℕ) (b : Bool) : (radList n b).Nodup := by
  cases b <;> exact intList_nodup _ _

theorem prod_pad (hn : 3 ≤ n) (b : Bool) (F : ℤ → X)
    (hF : ∀ k ∈ intList 1 n, k ∉ radList n b → F k = 1) :
    ((intList 1 (n : ℤ)).map F).prod = ((radList n b).map F).prod := by
  cases b
  · have h1 : intList 1 (n : ℤ) = intList 1 ((n : ℤ) - 1) ++ [(n : ℤ)] :=
      intList_snoc (by omega)
    have hn1 : F n = 1 := hF n (mem_intList_iff.2 ⟨by omega, le_rfl⟩) (by
      simp only [radList, mem_intList_iff]
      omega)
    rw [h1, List.map_append, List.prod_append]
    simp [radList, hn1]
  · have h1 : intList 1 (n : ℤ) = 1 :: intList (1 + 1) (n : ℤ) := intList_cons (by omega)
    have hn1 : F 1 = 1 := hF 1 (mem_intList_iff.2 ⟨le_rfl, by omega⟩) (by
      simp only [radList, mem_intList_iff]
      omega)
    rw [h1, List.map_cons, List.prod_cons, hn1, one_mul]
    simp [radList]

theorem mem_Q_iff_chainProd [Finite X] (hU : IsSylowTwoOf R.U ⊤) (b : Bool) (y : X) :
    y ∈ Q R b ↔ y ∈ chainProd R.root (radList n b) := by
  rw [Q_eq_Uplus R hU b]
  cases b
  · exact Iff.of_eq (congrArg (y ∈ ·) (coe_Uplus_false R))
  · exact Iff.of_eq (congrArg (y ∈ ·) (coe_Uplus_true R))

theorem centralizer_Q_trivial [Finite X] (hU : IsSylowTwoOf R.U ⊤) (b : Bool) {h : X}
    (hh : h ∈ R.B ⊓ R.N)
    (hf : ∀ k ∈ radList n b, ∀ x ∈ R.root k, h * x * h⁻¹ = x → x = 1)
    {y : X} (hy : y ∈ Q R b) (hc : h * y * h⁻¹ = y) : y = 1 := by
  have hn := R.three_le
  obtain ⟨g, hg, hprod⟩ := exists_fun_of_mem_chainProd R.root (radList n b) (radList_nodup n b) y
    ((mem_Q_iff_chainProd R hU b y).1 hy)
  classical
  let F : ℤ → X := fun k => if k ∈ radList n b then g k else 1
  have hFg : ∀ k ∈ radList n b, F k = g k := fun k hk => by simp [F, hk]
  have hFone : ∀ k ∈ intList 1 n, k ∉ radList n b → F k = 1 := fun k _ hk => by simp [F, hk]
  have hrad : ∀ k ∈ radList n b, 1 ≤ k ∧ k ≤ n := by
    intro k hk
    cases b <;> simp only [radList, mem_intList_iff] at hk <;> omega
  have hmemF : ∀ k ∈ intList 1 n, F k ∈ R.root k := by
    intro k hk
    by_cases hkr : k ∈ radList n b
    · rw [hFg k hkr]
      exact hg k hkr
    · rw [hFone k hk hkr]
      exact (R.root k).one_mem
  have hmemF' : ∀ k ∈ intList 1 n, h * F k * h⁻¹ ∈ R.root k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    exact R.roots.invariant k ⟨by omega, by omega⟩ h hh (F k) (hmemF k hk)
  have hprodF : ((intList 1 (n : ℤ)).map F).prod = y := by
    rw [prod_pad hn b F hFone, ← hprod]
    exact congrArg List.prod (List.map_congr_left fun k hk => hFg k hk)
  have heq := R.roots.unique (fun k => h * F k * h⁻¹) F hmemF' hmemF (by
    rw [← conj_list_prod_map, hprodF, hc, ← hprodF])
  have hone : ∀ k ∈ radList n b, g k = 1 := fun k hk => by
    have := heq k (mem_intList_iff.2 (hrad k hk))
    rw [hFg k hk] at this
    exact hf k hk (g k) (hg k hk) this
  rw [← hprod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hone k hk

end CFSG.Quasithin.H13.F431.G2.F48
