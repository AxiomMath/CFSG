module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IA
public import CFSG.Quasithin.Vol2.Ch11SecU1Main
public import CFSG.Quasithin.EmptyFaithful.E22PL2PglC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.E22PL2Psl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter

section Four

variable {G : Type} [Group G]

theorem kleinFour_mem_cases {V : Subgroup G} (hV : IsKleinFour ↥V) {v x : G} (hv : v ∈ V)
    (hx : x ∈ V) (hv1 : v ≠ 1) (hx1 : x ≠ 1) (hxv : x ≠ v) :
    ∀ y ∈ V, y = 1 ∨ y = v ∨ y = x ∨ y = x * v := by
  intro y hy
  by_cases h1 : y = 1
  · exact Or.inl h1
  by_cases h2 : y = v
  · exact Or.inr (Or.inl h2)
  by_cases h3 : y = x
  · exact Or.inr (Or.inr (Or.inl h3))
  refine Or.inr (Or.inr (Or.inr ?_))
  have := IsKleinFour.eq_mul_of_ne_all (G := ↥V) (x := ⟨x, hx⟩) (y := ⟨v, hv⟩) (z := ⟨y, hy⟩)
    (fun h => hx1 (congrArg Subtype.val h)) (fun h => hv1 (congrArg Subtype.val h))
    (fun h => hxv (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h3 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem kleinFour_mul_self {V : Subgroup G} (hV : IsKleinFour ↥V) {y : G} (hy : y ∈ V) :
    y * y = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : ↥V)
  rw [hV.exponent_two, pow_two] at h
  exact congrArg Subtype.val h

theorem kleinFour_orderOf {V : Subgroup G} (hV : IsKleinFour ↥V) {y : G} (hy : y ∈ V)
    (hy1 : y ≠ 1) : orderOf y = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self hV hy) hy1

theorem kleinFour_comm {V : Subgroup G} (hV : IsKleinFour ↥V) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  exact congrArg Subtype.val (hV.isMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)

theorem kleinFour_exists_pair {V : Subgroup G} (hV : IsKleinFour ↥V) :
    ∃ v ∈ V, ∃ x ∈ V, v ≠ 1 ∧ x ≠ 1 ∧ x ≠ v := by
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.card_four]; norm_num)
  have h3 : 3 ≤ Nat.card ↥V := by rw [hV.card_four]; norm_num
  obtain ⟨v, hv, hv1, -⟩ := exists_mem_ne_ne h3 1 1
  obtain ⟨x, hx, hx1, hxv⟩ := exists_mem_ne_ne h3 1 v
  exact ⟨v, hv, x, hx, hv1, hx1, hxv⟩

theorem sq_mem_centralizer_of_kleinFour {V : Subgroup G} (hV : IsKleinFour ↥V) {v g : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hgv : g * v * g⁻¹ = v) : g ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨x, hx, hx1, hxv⟩ : ∃ x ∈ V, x ≠ 1 ∧ x ≠ v := by
    have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.card_four]; norm_num)
    obtain ⟨x, hx, h1, h2⟩ := exists_mem_ne_ne (A := V) (by rw [hV.card_four]; norm_num)
      1 v
    exact ⟨x, hx, h1, h2⟩
  have hcases := kleinFour_mem_cases hV hv hx hv1 hx1 hxv
  have hmemV : ∀ y ∈ V, g * y * g⁻¹ ∈ V := fun y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hgx : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * v := by
    rcases hcases _ (hmemV x hx) with h | h | h | h
    · exact absurd (by simpa using h) hx1
    · exact absurd (by rw [← hgv] at h; simpa using h) hxv
    · exact Or.inl h
    · exact Or.inr h
  have hg2x : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
    have hsplit : g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [pow_two]; group
    rcases hgx with h | h
    · rw [hsplit, h, h]
    · rw [hsplit, h]
      have : g * (x * v) * g⁻¹ = (g * x * g⁻¹) * (g * v * g⁻¹) := by group
      rw [this, h, hgv, mul_assoc, kleinFour_mul_self hV hv, mul_one]
  have hg2v : g ^ 2 * v * (g ^ 2)⁻¹ = v := by
    have hsplit : g ^ 2 * v * (g ^ 2)⁻¹ = g * (g * v * g⁻¹) * g⁻¹ := by rw [pow_two]; group
    rw [hsplit, hgv, hgv]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hconj : ∀ w : G, g ^ 2 * w * (g ^ 2)⁻¹ = w → w * g ^ 2 = g ^ 2 * w := fun w hw => by
    calc w * g ^ 2 = (g ^ 2 * w * (g ^ 2)⁻¹) * g ^ 2 := by rw [hw]
      _ = g ^ 2 * w := by group
  rcases hcases y hy with rfl | rfl | rfl | rfl
  · simp
  · exact hconj _ hg2v
  · exact hconj _ hg2x
  · refine hconj _ ?_
    have : g ^ 2 * (x * v) * (g ^ 2)⁻¹ = (g ^ 2 * x * (g ^ 2)⁻¹) * (g ^ 2 * v * (g ^ 2)⁻¹) := by
      group
    rw [this, hg2x, hg2v]

theorem exists_conj_ne_of_kleinFour_sylow {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) (V : Sylow 2 X) (hV : IsKleinFour ↥(V : Subgroup X)) {v : X}
    (hv : v ∈ (V : Subgroup X)) (hv1 : v ≠ 1) :
    ∃ g ∈ Subgroup.normalizer ((V : Subgroup X) : Set X), g * v * g⁻¹ ≠ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVbot : (V : Subgroup X) ≠ ⊥ := fun h => hv1 (by
    rw [h] at hv
    exact Subgroup.mem_bot.mp hv)
  obtain ⟨g, hgN, hgC⟩ :=
    CFSG.ShultStronglyClosedTI.OddPrimeInverters.exists_mem_normalizer_not_mem_centralizer
      hperf V hVbot
  by_contra hcon
  push Not at hcon
  apply hgC
  set N := Subgroup.normalizer ((V : Subgroup X) : Set X) with hN
  have hsq := sq_mem_centralizer_of_kleinFour hV hv hv1 hgN (hcon g hgN)
  have hVC : (V : Subgroup X) ≤ Subgroup.centralizer ((V : Subgroup X) : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => kleinFour_comm hV hy hx
  set W := (V : Subgroup X).subgroupOf N with hW
  have : W.Normal := Subgroup.normal_in_normalizer
  have hm : (⟨g, hgN⟩ : ↥N) ^ W.index ∈ W := Subgroup.pow_index_mem W _
  have hgm : g ^ W.index ∈ (V : Subgroup X) := by
    rw [hW, Subgroup.mem_subgroupOf] at hm
    simpa using hm
  have hodd : ¬ 2 ∣ W.index := by
    intro h2
    exact V.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  obtain ⟨k, hk⟩ : Odd W.index := Nat.odd_iff.mpr (by omega)
  have hge : g = ((g ^ 2)⁻¹) ^ k * g ^ W.index := by
    rw [hk]
    group
  rw [hge]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.inv_mem _ hsq) k) (hVC hgm)

end Four

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem inEFor_psl2_pm_three (hK : Nat.card K = p)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p) {T : Subgroup (PSL2 K)}
    (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hodd : IsOddPrimePower (Nat.card K) :=
    CFSG.Walter.isOddPrimePower_of_card hK1 hpodd one_pos
  have hcard : 3 < Nat.card K := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.not_dvd_relIndex
  have hV : IsKleinFour ↥T := CFSG.Walter.psl2_sylow_two_isKleinFour K hK1 hpodd one_pos
    (by rw [pow_one]; exact hp8) (hT.isPGroup.toSylow hindex)
  obtain ⟨z, hz, z', hz', hz1, hz'1, hzz⟩ := kleinFour_exists_pair hV
  have hz2 := kleinFour_orderOf hV hz hz1
  have hz'2 := kleinFour_orderOf hV hz' hz'1
  have hTC : ∀ {w : PSL2 K}, w ∈ T → T ≤ Subgroup.centralizer ({w} : Set (PSL2 K)) :=
    fun hw t ht => Subgroup.mem_centralizer_singleton_iff.mpr (kleinFour_comm hV ht hw)
  have hnle : ¬ Subgroup.centralizer ({z'} : Set (PSL2 K)) ≤
      Subgroup.centralizer ({z} : Set (PSL2 K)) := by
    intro hle
    have hcen := CFSG.Walter.psl2_center_centralizer_involution K hK1 hpodd one_pos
      (by omega) hz'2
    have hzC : z ∈ Subgroup.centralizer ({z'} : Set (PSL2 K)) := hTC hz' hz
    have hzZ : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z'} : Set (PSL2 K)))) ∈
        Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle c.2))
    have hzp : z ∈ Subgroup.zpowers z' := by
      rw [← hcen]
      exact Subgroup.mem_map_of_mem _ hzZ
    rcases CFSG.Quasithin.E22L2.e22pl2pgl_mem_zpowers_involution (kleinFour_mul_self hV hz')
      hzp with h | h
    · exact hz1 h
    · exact hzz h.symm
  have hcoat := CFSG.Walter.psl2_centralizer_involution_isCoatom K hK1 hpodd one_pos (by omega)
    (by rw [pow_one]; exact hp8) hz2
  have hgen : Subgroup.centralizer ({z} : Set (PSL2 K)) ⊔
      Subgroup.centralizer ({z'} : Set (PSL2 K)) = ⊤ :=
    hcoat.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle (h ▸ le_sup_right))
  exact inEFor_top_of_solvable_pair hT (hTC hz) (hTC hz')
    (CFSG.Quasithin.E22L2.e22pl2psl_centralizer_isSolvable hodd hcard hz2)
    (CFSG.Quasithin.E22L2.e22pl2psl_centralizer_isSolvable hodd hcard hz'2) hgen

theorem nParam_psl2_pm_three (hK : Nat.card K = p)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p) : nParam (⊤ : Subgroup (PSL2 K)) ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PSL2 K))
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PSL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_psl2_pm_three hK hp8 hp11 hT))
  simpa using h

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
