module

public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Monster.Schur

theorem false_of_normal_prime_index {E : Type*} [Group E] [Group.IsPerfect E] (K : Subgroup E)
    [K.Normal] {p : ℕ} (hp : p.Prime) (hK : K.index = p) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card (E ⧸ K) = p := hK
  have : IsCyclic (E ⧸ K) := isCyclic_of_prime_card hc
  have : Finite (E ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  have : Nontrivial (E ⧸ K) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; exact hp.one_lt)
  exact Group.IsPerfect.not_isMulCommutative (E ⧸ K) inferInstance

section Kernel

variable {E G : Type*} [Group E] [Group G] (π : E →* G)

theorem card_eq_card_mul_card_ker3 {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) : Nat.card A = Nat.card B * Nat.card f.ker := by
  rw [← Subgroup.index_mul_card f.ker, Subgroup.index_ker]
  congr 1
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]

theorem exists_ker_gen3 (h : Nat.card π.ker = 3) :
    ∃ z : E, z ∈ π.ker ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ k ∈ π.ker, k = 1 ∨ k = z ∨ k = z ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic π.ker := isCyclic_of_prime_card h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := π.ker)
  have hord : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h]
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hg3 : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hord] at this
  refine ⟨g, g.2, fun h1 => hg1 (Subtype.ext h1), congrArg Subtype.val hg3, ?_⟩
  intro k hk
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨k, hk⟩)
  have hmod : g ^ n = g ^ (n % 3) := by
    have := zpow_mod_orderOf g n
    rw [hord] at this
    simpa using this.symm
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hk' : k = ((g ^ n : π.ker) : E) := by rw [hn]
  rcases hr with hr | hr | hr
  · left
    rw [hk', hmod, hr, zpow_zero]
    rfl
  · right; left
    rw [hk', hmod, hr, zpow_one]
  · right; right
    rw [hk', hmod, hr, zpow_two, pow_two]
    rfl

theorem ker_le_center_of_perfect [Group.IsPerfect E] (h : Nat.card π.ker = 3) :
    π.ker ≤ Subgroup.center E := by
  obtain ⟨z, hz, hz1, hz3, hall⟩ := exists_ker_gen3 π h
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzinv : z ^ 2 = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hz3
  have hsub : conjugatesOf z ⊆ {z, z⁻¹} := by
    intro w hw
    obtain ⟨g, hg⟩ := isConj_iff.1 hw
    have hmem : w ∈ π.ker := by
      rw [← hg]
      exact π.normal_ker.conj_mem z hz g
    rcases hall w hmem with h1 | h1 | h1
    · exfalso
      apply hz1
      have : g * z * g⁻¹ = 1 := hg.trans h1
      simpa using this
    · exact Or.inl h1
    · exact Or.inr (h1.trans hzinv)
  have hpair : ({z, z⁻¹} : Set E).Finite := (Set.finite_singleton z⁻¹).insert z
  have hfin : (conjugatesOf z).Finite := hpair.subset hsub
  have hidx : (Subgroup.centralizer {z}).index ≤ 2 := by
    rw [Subgroup.index_centralizer_eq_ncard]
    calc (conjugatesOf z).ncard ≤ ({z, z⁻¹} : Set E).ncard :=
          Set.ncard_le_ncard hsub hpair
      _ ≤ ({z⁻¹} : Set E).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hpos : 0 < (Subgroup.centralizer {z}).index := by
    rw [Subgroup.index_centralizer_eq_ncard]
    exact (Set.ncard_pos hfin).2 ⟨z, IsConj.refl z⟩
  have hzc : z ∈ Subgroup.center E := by
    rcases (by omega : (Subgroup.centralizer {z}).index = 1 ∨
        (Subgroup.centralizer {z}).index = 2) with h1 | h1
    · have htop := Subgroup.index_eq_one.1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({z} : Set E) := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 this z rfl).symm
    · have := Subgroup.normal_of_index_eq_two h1
      exact (false_of_normal_prime_index (Subgroup.centralizer {z}) Nat.prime_two h1).elim
  intro k hk
  rcases hall k hk with h1 | h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact hzc
  · rw [h1]; exact Subgroup.pow_mem _ hzc 2

end Kernel

section Complement

theorem false_of_splits {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {Z K : Subgroup E}
    [Z.Normal] (hZ : Nat.card Z = 3) (hZc : Z ≤ Subgroup.center E) (h1 : Z ⊓ K = ⊥)
    (h2 : Z ⊔ K = ⊤) : False := by
  have hKn : K.Normal := by
    constructor
    intro d hd g
    have hg : g ∈ Z ⊔ K := h2 ▸ Subgroup.mem_top g
    obtain ⟨z, hz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have hzc := Subgroup.mem_center_iff.1 (hZc hz)
    have hcomm : z * (k * d * k⁻¹) * z⁻¹ = k * d * k⁻¹ := by
      rw [← hzc (k * d * k⁻¹), mul_assoc, mul_inv_cancel, mul_one]
    have : z * k * d * (z * k)⁻¹ = k * d * k⁻¹ := by
      rw [← hcomm]
      group
    rw [this]
    exact K.mul_mem (K.mul_mem hk hd) (K.inv_mem hk)
  have hcompl : Z.IsComplement' K := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_iff.2 h1) (by rw [← Subgroup.normal_mul, h2]; simp)
  have hcard := hcompl.card_mul_card
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hidx : K.index = 3 := by
    have h3 := Subgroup.index_mul_card K
    rw [← hcard, hZ] at h3
    exact Nat.eq_of_mul_eq_mul_right hKpos (by rw [h3])
  exact false_of_normal_prime_index K Nat.prime_three hidx

theorem false_of_complement_sylow {E G : Type} [Group E] [Finite E] [Group G] [Finite G]
    [Group.IsPerfect E] (π : E →* G) (hπ : Function.Surjective π) (hk : Nat.card π.ker = 3)
    (S : Subgroup E) (hS : S ⊓ π.ker = ⊥) (hidx : ¬ 3 ∣ (S.map π).index) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZc := ker_le_center_of_perfect π hk
  have hZp : IsPGroup 3 π.ker := IsPGroup.of_card (n := 1) (by rw [hk]; norm_num)
  have : IsMulCommutative π.ker :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hZc a.2) b).symm⟩⟩
  have hE : Nat.card E = Nat.card G * 3 := by
    rw [card_eq_card_mul_card_ker3 π hπ, hk]
  have hSinj : Function.Injective (π.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : E) ∈ S ⊓ π.ker := ⟨x.2, hx⟩
    rw [hS] at h1
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  have hSmap : Nat.card (S.map π) = Nat.card S := by
    have : S.map π = (π.comp S.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hSinj).toEquiv).symm
  have hG : (S.map π).index * Nat.card S = Nat.card G := by
    rw [← hSmap]
    exact Subgroup.index_mul_card _
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hidxpos : 0 < (S.map π).index := Nat.pos_of_ne_zero (fun h0 => hidx (h0 ▸ dvd_zero 3))
  have hfac : (Nat.card E).factorization 3 = (Nat.card S).factorization 3 + 1 := by
    rw [hE, ← hG, Nat.factorization_mul (Nat.mul_pos hidxpos hpos).ne' (by norm_num),
      Nat.factorization_mul hidxpos.ne' hpos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hidx, Nat.Prime.factorization_self Nat.prime_three]
  obtain ⟨R⟩ : Nonempty (Sylow 3 S) := inferInstance
  set R' : Subgroup E := (R : Subgroup S).map S.subtype with hR'
  have hR'p : IsPGroup 3 R' := R.isPGroup'.map S.subtype
  have hR'S : R' ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR'card : Nat.card R' = 3 ^ (Nat.card S).factorization 3 := by
    rw [hR', Subgroup.card_map_of_injective S.subtype_injective]
    exact R.card_eq_multiplicity
  obtain ⟨Q, hQ⟩ := hR'p.exists_le_sylow
  have hZQ : π.ker ≤ Q := hZp.le_sylow_of_normal Q
  have hdisj : π.ker ⊓ R' = ⊥ := by
    rw [eq_bot_iff, ← hS, inf_comm]
    exact inf_le_inf_right _ hR'S
  have hsup : π.ker ⊔ R' = Q := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hZQ hQ)
    rw [Q.card_eq_multiplicity, hfac, pow_succ, ← hR'card, ← hk, mul_comm]
    let f : π.ker × R' → ↥(π.ker ⊔ R') := fun p =>
      ⟨(p.1 : E) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have h2 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = b' * b⁻¹ := by rw [h']; group
      have h3 : a'⁻¹ * a ∈ π.ker ⊓ R' :=
        ⟨π.ker.mul_mem (π.ker.inv_mem ha') ha, h2 ▸ R'.mul_mem hb' (R'.inv_mem hb)⟩
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h3
      subst h3
      have h4 : b = b' := by simpa using h'
      subst h4
      rfl
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod] at this
  obtain ⟨K, hK1, hK2⟩ := (CFSG.Quasithin.gaschutz hZp Q).2 ⟨R', hQ, hdisj, hsup⟩
  exact false_of_splits hk hZc hK1 hK2

end Complement

end CFSG.Monster.Schur
