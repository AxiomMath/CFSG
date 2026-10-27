module

public import CFSG.Quasithin.H13.A5Z1367d
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AMain

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

theorem autOn_sup {G : Type} [Group G] {U A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (U : Set G)) (hB : B ≤ Subgroup.normalizer (U : Set G)) :
    autOn (A ⊔ B) U = autOn A U ⊔ autOn B U :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hA hB

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem orderOf_dvd_three_of_Lv {x : G} (hx : x ∈ S.Lv) (hodd : Odd (orderOf x)) :
    orderOf x ∣ 3 := by
  have hxV := S.Lv_le_normalizer_V hx
  have hρ3 : S.frame.ρ (⟨x, hxV⟩ ^ 3) = 1 := by
    rw [map_pow]
    rcases S.rho_Lv_cases ⟨x, hxV⟩ hx with h | h | h <;> rw [h]
    · exact one_pow 3
    · decide
    · decide
  have hmem : ((⟨x, hxV⟩ ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.Lv := by
    rw [Subgroup.coe_pow]
    exact S.Lv.pow_mem hx 3
  obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho _ hmem hρ3
  rw [Subgroup.coe_pow, ← pow_mul] at hk
  have h1 : orderOf x ∣ 3 * 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : (orderOf x).Coprime (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact h2.dvd_of_dvd_mul_right h1

theorem Lv_le_closure_three : S.Lv ≤ Subgroup.closure
    {x : G | x ∈ Subgroup.centralizer ({S.v12} : Set G) ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, m, hm, hxm⟩
  have hxLv : x ∈ S.Lv := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
  have hodd : Odd (orderOf x) := by
    have h1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
    exact hm.of_dvd_nat h1
  refine Subgroup.subset_closure ⟨hx.2, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp (S.orderOf_dvd_three_of_Lv hxLv hodd) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem LvS_le_sup
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hnn : ¬ (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.centralizer ({S.v12} : Set G))
    (hg₀K : K.map (MulAut.conj g₀).toMonoidHom ≠ K) :
    autOn S.Lv S.Uv ≤ autOn K S.Uv ⊔ autOn (K.map (MulAut.conj g₀).toMonoidHom) S.Uv := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hO2 := S.pCoreOf_Gv_ne_bot h1222 h517 hF
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hcard : Set.ncard (conjSubgroupsBy Gv K) = 2 := by
    rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK with h | ⟨h, -⟩
    · exact absurd h hnn
    · exact h
  have hK1 : K ∈ conjSubgroupsBy Gv K := ⟨1, Gv.one_mem, by
    rw [map_one]
    exact (Subgroup.map_id K).symm⟩
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  obtain ⟨K', hK'mem, -, hall⟩ : ∃ K' ∈ conjSubgroupsBy Gv K, K' ≠ K ∧
      ∀ X ∈ conjSubgroupsBy Gv K, X = K ∨ X = K' := by
    have hK1' : K ∈ ({x, y} : Set (Subgroup G)) := hset ▸ hK1
    rcases hK1' with h | h
    · refine ⟨y, hset ▸ Or.inr rfl, fun h' => hxy (h.symm.trans h'.symm), fun X hX => ?_⟩
      have hX' : X ∈ ({x, y} : Set (Subgroup G)) := hset ▸ hX
      rcases hX' with h1 | h1
      · exact Or.inl (h1.trans h.symm)
      · exact Or.inr h1
    · refine ⟨x, hset ▸ Or.inl rfl, fun h' => hxy (h'.trans (Set.mem_singleton_iff.mp h)),
        fun X hX => ?_⟩
      have hX' : X ∈ ({x, y} : Set (Subgroup G)) := hset ▸ hX
      rcases hX' with h1 | h1
      · exact Or.inr h1
      · exact Or.inl (h1.trans (Set.mem_singleton_iff.mp h).symm)
  obtain ⟨g, hg, rfl⟩ := hK'mem
  have hg₀eq : K.map (MulAut.conj g₀).toMonoidHom = K.map (MulAut.conj g).toMonoidHom :=
    (hall _ ⟨g₀, hg₀, rfl⟩).resolve_left hg₀K
  rw [hg₀eq]
  have hcl := Vol2Native.lemma122A_of_localSQTK h37 h38 hloc hO2 hK Nat.prime_three
    (by norm_num) hcard h3
  have hKK : conjClosure K Gv ≤ K ⊔ K.map (MulAut.conj g).toMonoidHom := by
    refine conjClosure_le fun h hh k hk => ?_
    rcases hall (K.map (MulAut.conj h).toMonoidHom) ⟨h, hh, rfl⟩ with e | e
    · have : h * k * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨k, hk, rfl⟩
      rw [e] at this
      exact Subgroup.mem_sup_left this
    · have : h * k * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨k, hk, rfl⟩
      rw [e] at this
      exact Subgroup.mem_sup_right this
  have hLvK : S.Lv ≤ K ⊔ K.map (MulAut.conj g).toMonoidHom :=
    S.Lv_le_closure_three.trans (hcl.le.trans hKK)
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (le_of_mem_cComp hK).trans S.Gv_le_normalizer_Uv
  have hgN : g ∈ Subgroup.normalizer (Gv : Set G) := Subgroup.le_normalizer hg
  have hK'U : K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (S.Uv : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ∈ Gv := le_of_mem_cComp hK hk
    exact S.Gv_le_normalizer_Uv (Gv.mul_mem (Gv.mul_mem hg hk') (Gv.inv_mem hg))
  rw [← autOn_sup hKU hK'U]
  exact A4.autOn_mono hLvK

end Setting

end CFSG.Quasithin.H13.A5
