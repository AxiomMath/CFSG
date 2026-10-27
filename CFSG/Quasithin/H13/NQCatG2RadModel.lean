module

public import CFSG.Quasithin.H13.NQCatG2RadCoord

public section

namespace CFSG.Quasithin.H13.NQCat.G2Rad

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.LieType.BorelTits
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem mem_normalizer_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hh x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 hx
      simpa using this
    have := hh _ hx'
    calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * h * g⁻¹ * x := by group
  · intro hh x hx
    have hx' : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hg x).1 hx
    have := hh _ hx'
    calc x * h = g⁻¹ * ((g * x * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * x * g⁻¹)) * g := by rw [this]
      _ = h * x := by group

theorem mem_normalizer_centerOf {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (centerOf X : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hg, mem_normalizer_centralizer hg⟩

theorem pCoreOf_perfectCore_eq [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hL : Q ≤ ⁅Q, perfectCore P⁆ ∧
      ∃ (T : Type) (_ : Group T) (g : ↥(perfectCore P) →* T),
        IsSimpleGroup T ∧ Function.Surjective g ∧ ∀ x, g x = 1 → (x : G) ∈ Q) :
    pCoreOf 2 (perfectCore P) = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, T, _, g, hT, hg, hker⟩ := hL
  have hPC : P ≤ Subgroup.normalizer (perfectCore P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hQC : Q ≤ perfectCore P := by
    refine hQ.trans ((Subgroup.commutator_le).2 fun q hq c hc => ?_)
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hPC (hQP hq)) c).1 hc) (inv_mem hc)
  refine le_antisymm ?_
    (le_pCoreOf_of_le_normalizer 2 hQC ((perfectCore_le P).trans hPQ) hQ2)
  have hAC : pCoreOf 2 (perfectCore P) ≤ perfectCore P := pCoreOf_le 2 (perfectCore P)
  have hn : ((pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).2 (le_normalizer_pCoreOf 2 (perfectCore P))
  have := hn.map g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P)).map g) with h0 | htop
  · intro x hx
    have h1 := Subgroup.mem_map_of_mem g (show (⟨x, hAC hx⟩ : ↥(perfectCore P)) ∈
      (pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P) from hx)
    rw [h0, Subgroup.mem_bot] at h1
    exact hker _ h1
  · exfalso
    have : Finite T := Finite.of_surjective g hg
    have hA2 : IsPGroup 2 ↥(pCoreOf 2 (perfectCore P)) := pCoreOf_isPGroup 2 (perfectCore P)
    have hT2 : IsPGroup 2 T := by
      intro y
      have hy : y ∈ ((pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P)).map g :=
        htop ▸ Subgroup.mem_top y
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
      refine ⟨n, ?_⟩
      have e : a ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [← map_pow, e, map_one]
    have : Group.IsPerfect ↥(perfectCore P) := Subgroup.isPerfect_iff.2 (perfectCore_perfect P)
    have : Group.IsPerfect T := Group.IsPerfect.ofSurjective hg
    exact Group.IsPerfect.not_isNilpotent T hT2.isNilpotent

end Abstract

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem coord_eq_zero_of_commute
    {z : ModGL Tag.G2 K} (hz : z ∈ parabolicRadical Tag.G2 K {i1})
    (hc : ∀ e : K × K × K × K, e = (1, 0, 0, 0) ∨ e = (0, 1, 0, 0) ∨ e = (0, 0, 1, 0) ∨
      e = (0, 0, 0, 1) → z * nf e = nf e * z) : coord z = 0 := by
  obtain ⟨c, hzc⟩ := eq_nf_coord hz
  set t := coord z with ht
  have key : ∀ e : K × K × K × K, z * nf e = nf e * z →
      c + (e.1 * t.2.2.2 + e.2.1 * t.2.2.1) = c + (t.1 * e.2.2.2 + t.2.1 * e.2.2.1) := by
    intro e he
    have h1 : z * nf e = nf (t + e) * gX rC (c + 0 + (e.1 * t.2.2.2 + e.2.1 * t.2.2.1)) := by
      rw [hzc, ← nf_mul_C, gX_zero, mul_one]
    have h2 : nf e * z = nf (e + t) * gX rC (0 + c + (t.1 * e.2.2.2 + t.2.1 * e.2.2.1)) := by
      rw [hzc, ← nf_mul_C, gX_zero, mul_one]
    rw [h1, h2, add_comm e t] at he
    have := (nf_mul_inj he).2
    simpa using this
  have k1 := key _ (hc (1, 0, 0, 0) (Or.inl rfl))
  have k2 := key _ (hc (0, 1, 0, 0) (Or.inr (Or.inl rfl)))
  have k3 := key _ (hc (0, 0, 1, 0) (Or.inr (Or.inr (Or.inl rfl))))
  have k4 := key _ (hc (0, 0, 0, 1) (Or.inr (Or.inr (Or.inr rfl))))
  simp only [one_mul, zero_mul, mul_one, mul_zero, add_zero, zero_add] at k1 k2 k3 k4
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  simp only at k1 k2 k3 k4
  simp only [Prod.mk_eq_zero]
  exact ⟨by linear_combination -k4, by linear_combination -k3, by linear_combination k2,
    by linear_combination k1⟩

theorem centerOf_parabolicRadical_one :
    centerOf (parabolicRadical Tag.G2 K {i1}) = N1 := by
  apply le_antisymm
  · rintro z ⟨hzQ, hzC⟩
    refine (mem_N1_iff hzQ).2 (coord_eq_zero_of_commute hzQ fun e he => ?_)
    have heQ : nf e ∈ parabolicRadical Tag.G2 K {i1} := by
      rcases he with rfl | rfl | rfl | rfl <;>
        exact mul_mem (memA _) (mul_mem (memU _) (mul_mem (memV _) (memB _)))
    exact (Subgroup.mem_centralizer_iff.1 hzC _ heQ).symm
  · intro z hz
    refine ⟨?_, N1_le_centralizer hz⟩
    obtain ⟨c, rfl⟩ := exists_of_mem_N1 hz
    exact memC c

theorem pCoreOf_perfectCore_parabolic
    [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (i : Fin Tag.G2.rank) :
    pCoreOf 2 (perfectCore (parabolicSubgroup Tag.G2 K {i})) = parabolicRadical Tag.G2 K {i} := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rcases G2.fin_two_cases i with rfl | rfl
  · have hF := G2.parabolicFacts_zero hK hf
    exact pCoreOf_perfectCore_eq hF.le hF.normalizes hF.pGroup
      ⟨G2.generated_zero hK4, G2.levi_hom hK4 i0⟩
  · have hF := G2.parabolicFacts_one hK hf
    exact pCoreOf_perfectCore_eq hF.le hF.normalizes hF.pGroup
      ⟨G2.generated_one hK4, G2.levi_hom hK4 i1⟩

theorem xr_mem_perfectCore
    [Finite K] (hK4 : 4 ≤ Nat.card K) (s : K) :
    gX rR s ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1}) := by
  obtain ⟨L, hLP, hL, hx, -, -⟩ := G2.leviL_data hK4 i1
  rw [← rootOne_gX_i1]
  exact le_perfectCore_of_perfect hLP hL (hx s)

theorem weyl_mem_perfectCore
    [Finite K] (hK4 : 4 ≤ Nat.card K) :
    weylElt Tag.G2 K i1 1 ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1}) := by
  obtain ⟨L, hLP, hL, hx, hy, -⟩ := G2.leviL_data hK4 i1
  rw [weylElt_eq_xUnit_mul]
  exact le_perfectCore_of_perfect hLP hL (mul_mem (mul_mem (hx _) (hy _)) (hx _))

theorem commute_yUnit_gX_rC
    (c d : K) : Commute (yUnit Tag.G2 K i1 c) (gX rC d) := by
  have hR : IsRoot Tag.G2 (Pi.single i1 1) := isRoot_single _ _
  have hC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  have eR : reflect Tag.G2 i1 (Pi.single i1 1) = -Pi.single i1 1 := by
    funext k
    fin_cases k <;> decide
  have eC : reflect Tag.G2 i1 rC = rC := by
    funext k
    fin_cases k <;> decide
  have hy : yUnit Tag.G2 K i1 c =
      weylElt Tag.G2 K i1 1 * gX rR c * (weylElt Tag.G2 K i1 1)⁻¹ := by
    have h := weyl_conj (K := K) i1 hR c
    rw [eR] at h
    rw [← single_i1, h]
    exact (pinnedX_neg_single Tag.G2 K i1 c).symm
  have hc : gX rC d = weylElt Tag.G2 K i1 1 * gX rC d * (weylElt Tag.G2 K i1 1)⁻¹ := by
    rw [weyl_conj i1 hC, eC]
  rw [hy, hc]
  show _ * _ = _ * _
  have h := (comm_rc c d).eq
  calc weylElt Tag.G2 K i1 1 * gX rR c * (weylElt Tag.G2 K i1 1)⁻¹ *
        (weylElt Tag.G2 K i1 1 * gX rC d * (weylElt Tag.G2 K i1 1)⁻¹) =
      weylElt Tag.G2 K i1 1 * (gX rR c * gX rC d) * (weylElt Tag.G2 K i1 1)⁻¹ := by group
    _ = weylElt Tag.G2 K i1 1 * (gX rC d * gX rR c) * (weylElt Tag.G2 K i1 1)⁻¹ := by rw [h]
    _ = _ := by group

theorem perfectCore_le_centralizer
    [Finite K] :
    perfectCore (parabolicSubgroup Tag.G2 K {i1}) ≤
      Subgroup.centralizer (N1 (K := K) : Set (ModGL Tag.G2 K)) := by
  set P := parabolicSubgroup Tag.G2 K {i1} with hP
  set Q := parabolicRadical Tag.G2 K {i1} with hQ
  have hPN : P ≤ Subgroup.normalizer (N1 (K := K) : Set (ModGL Tag.G2 K)) := fun x hx => by
    rw [← centerOf_parabolicRadical_one]
    exact mem_normalizer_centerOf (parabolicSubgroup_le_normalizer_parabolicRadical {i1} hx)
  set C := P ⊓ Subgroup.centralizer (N1 (K := K) : Set (ModGL Tag.G2 K)) with hCdef
  have hCN : P ≤ Subgroup.normalizer (C : Set (ModGL Tag.G2 K)) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, mem_normalizer_centralizer (hPN hx)⟩
  have hC : (C.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hCN
  have hcent : ∀ g : ModGL Tag.G2 K, (∀ d : K, Commute g (gX rC d)) →
      g ∈ Subgroup.centralizer (N1 (K := K) : Set (ModGL Tag.G2 K)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨d, rfl⟩ := exists_of_mem_N1 hn
    exact (hg d).eq.symm
  have hQC : Q ≤ C := fun x hx => ⟨(parabolicRadical_le_posUnipotent {i1}).trans
    (posUnipotent_le_parabolicSubgroup {i1}) hx,
    Subgroup.le_centralizer_iff.1 N1_le_centralizer hx⟩
  have hLC : Subgroup.closure {g : ModGL Tag.G2 K | ∃ j ∈ ({i1} : Set (Fin Tag.G2.rank)),
      ∃ c : K, g = xUnit Tag.G2 K j c ∨ g = yUnit Tag.G2 K j c} ≤ C := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨parabolicLevi_le_parabolicSubgroup {i1} (xUnit_mem_parabolicLevi hj c), ?_⟩
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact hcent _ fun d => by rw [rootOne_gX_i1]; exact comm_rc c d
    · refine ⟨parabolicLevi_le_parabolicSubgroup {i1} (yUnit_mem_parabolicLevi hj c), ?_⟩
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact hcent _ fun d => commute_yUnit_gX_rC c d
  have hHP : torusGroup Tag.G2 K ≤ P :=
    (torusGroup_le_parabolicLevi {i1}).trans (parabolicLevi_le_parabolicSubgroup {i1})
  have hPeq : P = C ⊔ torusGroup Tag.G2 K := by
    refine le_antisymm ?_ (sup_le inf_le_left hHP)
    rw [hP, ← parabolicRadical_sup_parabolicLevi, parabolicLevi]
    exact sup_le (hQC.trans le_sup_left)
      (sup_le le_sup_right (hLC.trans le_sup_left))
  have hsolv : Group.IsSolvable ↥(torusGroup Tag.G2 K) := by
    have : IsMulCommutative ↥(torusGroup Tag.G2 K) :=
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_diagonalGroup
        (torusGroup_le_diagonalGroup a.2) (torusGroup_le_diagonalGroup b.2))⟩⟩
    infer_instance
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  exact (perfectCore_le_of_sup_solvable inf_le_left hC hPeq hsolv).trans inf_le_right

theorem eq_or_eq_of_le_normalizer
    [Finite K] (h8 : 8 ≤ Nat.card K) {W : Subgroup (ModGL Tag.G2 K)}
    (hZW : (N1 : Subgroup (ModGL Tag.G2 K)) ≤ W) (hWQ : W ≤ parabolicRadical Tag.G2 K {i1})
    (hKW : perfectCore (parabolicSubgroup Tag.G2 K {i1}) ≤
      Subgroup.normalizer (W : Set (ModGL Tag.G2 K))) :
    W = N1 ∨ W = parabolicRadical Tag.G2 K {i1} := by
  have hK4 : 4 ≤ Nat.card K := by omega
  by_cases hW : W ≤ N1
  · exact Or.inl (le_antisymm hW hZW)
  right
  obtain ⟨w, hwW, hwN⟩ := Set.not_subset.1 hW
  have hwQ := hWQ hwW
  obtain ⟨c, hc⟩ := eq_nf_coord hwQ
  have ht0 : coord w ≠ 0 := fun h => hwN ((mem_N1_iff hwQ).2 h)
  have htD : coord w ∈ coordSet W := ⟨c, hc ▸ hwW⟩
  have hD : ∀ s, ∀ t ∈ coordSet W, tr s t ∈ coordSet W := fun s t ht =>
    tr_mem_coordSet hWQ (hKW (xr_mem_perfectCore hK4 s)) ht
  obtain ⟨u, hu⟩ := G2.exists_units_ne_one hK4
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hu1 : (u : K) ≠ 1 := fun h => hu (Units.ext h)
  obtain ⟨β₀, hβ₀, h0⟩ := exists_b_mem hu0 hu1 hD htD ht0
  have htop := eq_top_of_b h8 hu0 hu1 hD
    (fun β hβ => weyl_mem_coordSet (hKW (weyl_mem_perfectCore hK4)) hβ) hβ₀ h0
  refine le_antisymm hWQ fun g hg => ?_
  obtain ⟨d, hd⟩ := eq_nf_coord hg
  obtain ⟨c', hc'⟩ : coord g ∈ coordSet W := htop ▸ AddSubgroup.mem_top _
  have e : g = nf (coord g) * gX rC c' * gX rC (d - c') := by
    rw [mul_assoc, ← gX_add, add_sub_cancel, ← hd]
  rw [e]
  exact W.mul_mem hc' (hZW (gX_c_mem_N1 _))

theorem centerOf_le_of_le_normalizer
    [Finite K] (hK4 : 4 ≤ Nat.card K) {R : Subgroup (ModGL Tag.G2 K)}
    (hRQ : R ≤ parabolicRadical Tag.G2 K {i1})
    (hKR : perfectCore (parabolicSubgroup Tag.G2 K {i1}) ≤
      Subgroup.normalizer (R : Set (ModGL Tag.G2 K))) :
    centerOf R ≤ N1 := by
  intro z hz
  by_contra hzN
  have hSQ : centerOf R ≤ parabolicRadical Tag.G2 K {i1} := inf_le_left.trans hRQ
  have hKS : perfectCore (parabolicSubgroup Tag.G2 K {i1}) ≤
      Subgroup.normalizer (centerOf R : Set (ModGL Tag.G2 K)) := fun k hk =>
    mem_normalizer_centerOf (hKR hk)
  have hzQ := hSQ hz
  obtain ⟨c, hc⟩ := eq_nf_coord hzQ
  have ht0 : coord z ≠ 0 := fun h => hzN ((mem_N1_iff hzQ).2 h)
  have htD : coord z ∈ coordSet (centerOf R) := ⟨c, hc ▸ hz⟩
  have hD : ∀ s, ∀ t ∈ coordSet (centerOf R), tr s t ∈ coordSet (centerOf R) := fun s t ht =>
    tr_mem_coordSet hSQ (hKS (xr_mem_perfectCore hK4 s)) ht
  obtain ⟨u, hu⟩ := G2.exists_units_ne_one hK4
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hu1 : (u : K) ≠ 1 := fun h => hu (Units.ext h)
  obtain ⟨β, hβ, hb⟩ := exists_b_mem hu0 hu1 hD htD ht0
  obtain ⟨c₂, hc₂⟩ := weyl_mem_coordSet (hKS (weyl_mem_perfectCore hK4)) hb
  obtain ⟨c₁, hc₁⟩ := hb
  have hcomm := Subgroup.mem_centralizer_iff.1 hc₁.2 _ hc₂.1
  rw [nf_mul_C, nf_mul_C, add_comm ((β, (0 : K), (0 : K), (0 : K)) : K × K × K × K)] at hcomm
  have h := (nf_mul_inj hcomm).2
  simp only [mul_zero, add_zero] at h
  have hβ2 : β * β = 0 := by linear_combination -h
  exact hβ (mul_self_eq_zero.1 hβ2)

theorem card_le_card_centerOf_zero
    [Finite K] :
    Nat.card K * Nat.card K ≤ Nat.card (centerOf (parabolicRadical Tag.G2 K {i0})) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hmem : ∀ x y : K, gX rB x * gX rC y ∈ centerOf (parabolicRadical Tag.G2 K {i0}) :=
    fun x y => ⟨mul_mem (mem_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) x)
      (mem_zero (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) y),
      N0_le_centralizer (mul_mem (gX_b_mem_N0 x) (gX_c_mem_N0 y))⟩
  let φ : K × K → ↥(centerOf (parabolicRadical Tag.G2 K {i0})) :=
    fun p => ⟨gX rB p.1 * gX rC p.2, hmem p.1 p.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : gX rB x * gX rC y = gX rB x' * gX rC y' := congrArg Subtype.val h
    have e : gX rB (x' + x) * gX rC (y + y') = 1 := by
      calc gX rB (x' + x) * gX rC (y + y') =
          gX rB x' * (gX rB x * gX rC y) * gX rC y' := by rw [gX_add, gX_add]; group
        _ = gX rB x' * (gX rB x' * gX rC y') * gX rC y' := by rw [h']
        _ = 1 := by
          rw [← mul_assoc, gX_self, one_mul, gX_self]
    obtain ⟨h1, h2⟩ := prod_bc_eq_one e
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [Prod.mk.injEq]
    exact ⟨by linear_combination h1 - x' * h2', by linear_combination h2 - y' * h2'⟩
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod] at this

end Model

end CFSG.Quasithin.H13.NQCat.G2Rad
