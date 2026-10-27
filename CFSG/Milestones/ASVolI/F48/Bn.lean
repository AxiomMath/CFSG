module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Gen

public section

namespace CFSG.ASVolI

open CFSG.GH74.BNPair in
open scoped Pointwise in
theorem burnsideF48_dc_step {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
    {S : Finset (WeylGroup B N)} (T : IsTitsSystem B N S) {t : WeylGroup B N} (ht : t ∈ S) {k : ℕ}
    {x y : X} (hx : ∃ w, wordLength (S : Set (WeylGroup B N)) w ≤ k ∧ x ∈ dc B N w)
    (hy : y ∈ B ∨ y ∈ dc B N t) :
    ∃ w, wordLength (S : Set (WeylGroup B N)) w ≤ k + 1 ∧ x * y ∈ dc B N w := by
  obtain ⟨w, hwk, hxw⟩ := hx
  rcases hy with hy | hy
  · exact ⟨w, by omega, mem_dc_of_mem hxw B.one_mem hy (by simp)⟩
  · have hmem : x * y ∈ dc B N w * dc B N t := Set.mem_mul.2 ⟨x, hxw, y, hy, rfl⟩
    rcases T.bnCore.mul_subset_right (Finset.mem_coe.2 ht) w hmem with h | h
    · refine ⟨w * t, ?_, h⟩
      have := wordLength_mul_gen_le T.bnCore.mul_self_eq_one (Finset.mem_coe.2 ht) (T.mem_closure w)
      omega
    · exact ⟨w, by omega, h⟩

open CFSG.GH74.BNPair in
theorem burnsideF48_not_mem_five {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
    {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {n : ℕ} (R : Rank2 B N S a b n) (hn : 6 ≤ n)
    {x : X} (hx : x ∈ dc B N (altWord a b n)) :
    ¬ ∃ k ∈ pgen B N a b true, ∃ l ∈ pgen B N a b false, ∃ k' ∈ pgen B N a b true,
      ∃ l' ∈ pgen B N a b false, ∃ k'' ∈ pgen B N a b true, x = k * l * k' * l' * k'' := by
  rintro ⟨k, hk, l, hl, k', hk', l', hl', k'', hk'', rfl⟩
  have hT := R.tits
  have h0 : ∃ w, wordLength (S : Set (WeylGroup B N)) w ≤ 0 ∧ (1 : X) ∈ dc B N w :=
    ⟨1, by simp [wordLength_one], mem_dc_one.2 B.one_mem⟩
  have h1 := burnsideF48_dc_step hT (R.gen_mem true) h0
    ((mem_parabolic_single_iff hT (R.gen_mem true)).1 hk)
  have h2 := burnsideF48_dc_step hT (R.gen_mem false) h1
    ((mem_parabolic_single_iff hT (R.gen_mem false)).1 hl)
  have h3 := burnsideF48_dc_step hT (R.gen_mem true) h2
    ((mem_parabolic_single_iff hT (R.gen_mem true)).1 hk')
  have h4 := burnsideF48_dc_step hT (R.gen_mem false) h3
    ((mem_parabolic_single_iff hT (R.gen_mem false)).1 hl')
  have h5 := burnsideF48_dc_step hT (R.gen_mem true) h4
    ((mem_parabolic_single_iff hT (R.gen_mem true)).1 hk'')
  obtain ⟨w, hw, hxw⟩ := h5
  rw [one_mul] at hxw
  have heq := dc_eq_of_mem hxw hx
  have hww := hT.dc_injective heq
  subst hww
  have hlen := R.ell_altWord (le_refl n)
  omega

open CFSG.GH74.BNPair in
theorem burnsideF48_w₀_not_mem_five {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    (hn : 6 ≤ n) :
    ¬ ∃ k ∈ D.P₁, ∃ l ∈ D.P₂, ∃ k' ∈ D.P₁, ∃ l' ∈ D.P₂, ∃ k'' ∈ D.P₁,
      ((D.lift D.w₀ : D.N) : X) = k * l * k' * l' * k'' :=
  burnsideF48_not_mem_five D.rank2 hn (by
    have := coe_mem_dc (B := D.B) (N := D.N) (D.lift D.w₀)
    rwa [D.lift_mk] at this)

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF48_bn_mi_not_mem_P₂ {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n) :
    mi D true ∉ D.P₂ := by
  intro h
  have hB : mi D true ∈ D.B := D.rank2.pgen_inter true (mi_mem_P D true) h
  have h1 : dc D.B D.N (gen D.w₁ D.w₂ true) = dc D.B D.N 1 :=
    dc_eq_of_mem (mi_mem_dc D true) (mem_dc_one.2 hB)
  exact D.rank2.tits.gen_ne_one (D.rank2.gen_mem true) (D.rank2.tits.dc_injective h1)

open CFSG.GH74.BNPair in
theorem burnsideF48_bn_conj_mem_B {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n) {m h : X}
    (hm : m ∈ D.N) (hh : h ∈ D.B ⊓ D.N) : m * h * m⁻¹ ∈ D.B := by
  have h1 : (⟨h, hh.2⟩ : D.N) ∈ cartan D.B D.N := Subgroup.mem_subgroupOf.2 hh
  have h2 := D.normal.conj_mem _ h1 ⟨m, hm⟩
  exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h2)).1

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN CFSG.Quasithin.H13.F431.G2.F48 in
theorem burnsideF48_centralizer_Uplus {X : Type} [Group X] {n : ℕ} (R : RankTwoSystem X n) {h : X}
    (hh : h ∈ R.B ⊓ R.N)
    (hf : ∀ k ∈ radList n true, ∀ x ∈ R.root k, h * x * h⁻¹ = x → x = 1)
    {y : X} (hy : y ∈ Uplus R true) (hc : h * y * h⁻¹ = y) : y = 1 := by
  have hn := R.three_le
  have hy' : y ∈ chainProd R.root (radList n true) := by
    rw [← SetLike.mem_coe, coe_Uplus_true] at hy
    exact hy
  obtain ⟨g, hg, hprod⟩ := CFSG.Quasithin.H13.F431.D4q.F48.exists_fun_of_mem_chainProd R.root
    (radList n true) (radList_nodup n true) y hy'
  classical
  let F : ℤ → X := fun k => if k ∈ radList n true then g k else 1
  have hFg : ∀ k ∈ radList n true, F k = g k := fun k hk => by simp [F, hk]
  have hFone : ∀ k ∈ intList 1 n, k ∉ radList n true → F k = 1 := fun k _ hk => by simp [F, hk]
  have hrad : ∀ k ∈ radList n true, 1 ≤ k ∧ k ≤ n := by
    intro k hk
    simp only [radList, mem_intList_iff] at hk
    omega
  have hmemF : ∀ k ∈ intList 1 n, F k ∈ R.root k := by
    intro k hk
    by_cases hkr : k ∈ radList n true
    · rw [hFg k hkr]
      exact hg k hkr
    · rw [hFone k hk hkr]
      exact (R.root k).one_mem
  have hmemF' : ∀ k ∈ intList 1 n, h * F k * h⁻¹ ∈ R.root k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    exact R.roots.invariant k ⟨by omega, by omega⟩ h hh (F k) (hmemF k hk)
  have hprodF : ((intList 1 (n : ℤ)).map F).prod = y := by
    rw [prod_pad hn true F hFone, ← hprod]
    exact congrArg List.prod (List.map_congr_left fun k hk => hFg k hk)
  have heq := R.roots.unique (fun k => h * F k * h⁻¹) F hmemF' hmemF (by
    rw [← CFSG.Quasithin.H13.F431.D4q.F48.conj_list_prod_map, hprodF, hc, ← hprodF])
  have hone : ∀ k ∈ radList n true, g k = 1 := fun k hk => by
    have := heq k (mem_intList_iff.2 (hrad k hk))
    rw [hFg k hk] at this
    exact hf k hk (g k) (hg k hk) this
  rw [← hprod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hone k hk

open CFSG.GH74.BNPair in
theorem burnsideF48_rank2_symm {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
    {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {n : ℕ} (R : Rank2 B N S a b n) :
    Rank2 B N S b a n where
  tits := R.tits
  gens := by rw [R.gens]; exact Set.pair_comm a b
  dih := R.dih.symm

open CFSG.GH74.BNPair in
theorem burnsideF48_w₀_not_mem_five' {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    (hn : 6 ≤ n) :
    ¬ ∃ k ∈ D.P₂, ∃ l ∈ D.P₁, ∃ k' ∈ D.P₂, ∃ l' ∈ D.P₁, ∃ k'' ∈ D.P₂,
      ((D.lift D.w₀ : D.N) : X) = k * l * k' * l' * k'' :=
  burnsideF48_not_mem_five (burnsideF48_rank2_symm D.rank2) hn (by
    have key := coe_mem_dc (B := D.B) (N := D.N) (D.lift D.w₀)
    rw [D.lift_mk] at key
    have hbr : altWord D.w₁ D.w₂ n = altWord D.w₂ D.w₁ n := D.rank2.dih.altWord_eq
    have e : dc D.B D.N D.w₀ = dc D.B D.N (altWord D.w₂ D.w₁ n) :=
      congrArg (dc D.B D.N) hbr
    rw [← e]
    exact key)

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF48_bn_mi_not_mem {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    (i : Bool) : mi D i ∉ P D (!i) := by
  intro h
  have hB : mi D i ∈ D.B := D.rank2.pgen_inter i (mi_mem_P D i) h
  have h1 : dc D.B D.N (gen D.w₁ D.w₂ i) = dc D.B D.N 1 :=
    dc_eq_of_mem (mi_mem_dc D i) (mem_dc_one.2 hB)
  exact D.rank2.tits.gen_ne_one (D.rank2.gen_mem i) (D.rank2.tits.dc_injective h1)

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF48_bn_cartan_data {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    (hn : 6 ≤ n) {h : X} (hh : h ∈ D.B ⊓ D.N) (b : Bool) :
    ∃ m w : X, m ∈ P D b ∧ m ∉ P D (!b) ∧ h ∈ P D b ∧ h ∈ P D (!b) ∧
      m⁻¹ * h * m ∈ P D (!b) ∧ w⁻¹ * h * w ∈ P D b ∧
      (¬ ∃ k ∈ P D b, ∃ l ∈ P D (!b), ∃ k' ∈ P D b, ∃ l' ∈ P D (!b), ∃ k'' ∈ P D b,
        w = k * l * k' * l' * k'') := by
  have hmiN : mi D b ∈ D.N := (D.lift (gen D.w₁ D.w₂ b)).2
  have hwN : ((D.lift D.w₀ : D.N) : X) ∈ D.N := (D.lift D.w₀).2
  refine ⟨(mi D b)⁻¹, ((D.lift D.w₀ : D.N) : X), (P D b).inv_mem (mi_mem_P D b), ?_,
    B_le_P D b hh.1, B_le_P D (!b) hh.1, ?_, ?_, ?_⟩
  · intro hm
    exact burnsideF48_bn_mi_not_mem D b (by simpa using (P D (!b)).inv_mem hm)
  · rw [inv_inv]
    exact B_le_P D (!b) (burnsideF48_bn_conj_mem_B D hmiN hh)
  · have := burnsideF48_bn_conj_mem_B D (D.N.inv_mem hwN) hh
    rw [inv_inv] at this
    exact B_le_P D b this
  · cases b
    · exact burnsideF48_w₀_not_mem_five' D hn
    · exact burnsideF48_w₀_not_mem_five D hn

end CFSG.ASVolI
