module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts5
public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecD551C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem flag_of_cV (h : Hyp11 G T L I n) (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ ∧
      SecA.IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) 1
        (V₁.subgroupOf (fsuV T I)) := by
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hflag := SecA.isFlagW_of_isVi h hV₁
  rw [hZ] at hflag
  exact ⟨hZ, hflag⟩

theorem conjV_comm_mem (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) {x : G}
    (hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hxS : x ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁))) :
    ∀ k ∈ perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I))),
      SecA.conjV (fsuV T I) x hxV * k * (SecA.conjV (fsuV T I) x hxV)⁻¹ * k⁻¹ ∈
        pCoreOf 2 (perfectCore (autOn L (fsuV T I) ⊓
          SecA.stabW (V₁.subgroupOf (fsuV T I)))) := by
  have hle := SecA.IsVi.le_fsuV hV₁
  have hA : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (SecA.L_le_normalizer_fsuV h)
  rw [SecB.autOn_inf_stabW hle, ← SecB.autOn_perfectCore hA]
  intro k hk
  obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hk
  rw [← SecA.conjV_inv, ← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
  exact SecB.autOn_pCoreOf_le _ _ (SecA.conjV_mem_autOn (hxS.2.2 l hl) _)

theorem isTwo_of_mem_L (hT : Facts44) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {z : G} (hzV₁ : z ∈ V₁) (hz1 : z ≠ 1) {x : G} (hxL : x ∈ L)
    (hxz : x ∈ Subgroup.centralizer ({z} : Set G))
    (hxS : x ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁))) :
    ∃ a : ℕ, x ^ 2 ^ a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab := (SecA.isElemAbelian_fsuV h).1
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hZ, hflag⟩ := flag_of_cV h hcV hV₁
  have hconc : TorusPointConcl (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I)) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
        ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
    · rw [hZ] at hπ
      exact hT.torusSL3 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
    · rw [hZ] at hπ
      exact hT.torusSp4 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
    · rw [hZ] at hπ
      exact hT.torusG2 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
  have hzV := SecA.IsVi.le_fsuV hV₁ hzV₁
  have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h hxL
  obtain ⟨a, ha⟩ := hconc _ (SecA.conjV_mem_autOn hxL hxV) ⟨z, hzV⟩
    (Subgroup.mem_subgroupOf.mpr hzV₁) (fun h0 => hz1 (congrArg Subtype.val h0))
    (Subtype.ext (by
      rw [SecA.conjV_apply_coe]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hxz
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hc]
        _ = z := by group))
    (conjV_comm_mem h hV₁ hxV hxS)
  rw [SecD.conjV_pow] at ha
  have hxa : x ^ 2 ^ a ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    ⟨L.pow_mem hxL _, SecD.mem_centralizer_of_conjV_eq_one _ ha⟩
  rw [SecA.centralizer_eq_pCoreOf h1102 h] at hxa
  obtain ⟨b, hb⟩ := exists_pow_two_pow_eq_one_of_mem
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hxa
  exact ⟨a + b, by rw [pow_add, pow_mul, hb]⟩

theorem mem_centralizer_of_odd (hT : Facts44) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {b : G} (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbV : b ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hbS : b ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)))
    (hbo : ∃ m : ℕ, Odd m ∧ Nat.Coprime m (2 ^ n - 1) ∧ b ^ m = 1) :
    b ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hab := (SecA.isElemAbelian_fsuV h).1
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hZ, hflag⟩ := flag_of_cV h hcV hV₁
  have hconc : CentLeviConcl (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I)) n := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
        ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
    · rw [hZ] at hπ
      exact hT.leviSL3 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
    · rw [hZ] at hπ
      exact hT.leviSp4 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
    · rw [hZ] at hπ
      exact hT.leviG2 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag
  have hle := SecA.IsVi.le_fsuV hV₁
  have hA : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (SecA.L_le_normalizer_fsuV h)
  have hnormH : ∀ k ∈ autOn L (fsuV T I),
      SecA.conjV (fsuV T I) b hbV * k * (SecA.conjV (fsuV T I) b hbV)⁻¹ ∈ autOn L (fsuV T I) := by
    intro k hk
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hk
    rw [← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hbL l).mp hl) _
  have hnormL₁ : ∀ k ∈ perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I))),
      SecA.conjV (fsuV T I) b hbV * k * (SecA.conjV (fsuV T I) b hbV)⁻¹ ∈
        perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I))) := by
    rw [SecB.autOn_inf_stabW hle, ← SecB.autOn_perfectCore hA]
    intro k hk
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hk
    rw [← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hbS.1 l).mp hl) _
  obtain ⟨m, hm, hmc, hbm⟩ := hbo
  have hβm : SecA.conjV (fsuV T I) b hbV ^ m = 1 := by
    rw [SecD.conjV_pow]
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [SecA.conjV_apply_coe]
    simp [hbm]
  have h1 := hconc _ hnormH hnormL₁ (conjV_comm_mem h hV₁ hbV hbS) ⟨m, hm, hmc, hβm⟩
  exact SecD.mem_centralizer_of_conjV_eq_one hbV h1

end CFSG.Quasithin.Vol2.Ch11.SecE
