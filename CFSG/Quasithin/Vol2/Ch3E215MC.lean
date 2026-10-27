module

public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.H13.QRCBenderSection

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups

theorem bruhat_of_injOn {L : Type*} [Group L] [Finite L] {N : Subgroup L} {y : L} (hy : y ∉ N)
    {S : Set L} (hSN : S ⊆ N) (hinj : Set.InjOn (fun s => ((s * y : L) : L ⧸ N)) S)
    (hcard : N.index ≤ S.ncard + 1) (x : L) :
    x ∈ N ∨ ∃ n₁ ∈ N, ∃ n₂ ∈ N, x = n₁ * y * n₂ := by
  classical
  by_cases hx : x ∈ N
  · exact Or.inl hx
  refine Or.inr (by_contra fun hcon => ?_)
  have h1x : ((1 : L) : L ⧸ N) ≠ (x : L ⧸ N) := fun h => hx (by
    have h' := QuotientGroup.eq.mp h
    rwa [inv_one, one_mul] at h')
  have hmaps : ∀ s ∈ S, ((s * y : L) : L ⧸ N) ∈
      ({((1 : L) : L ⧸ N), (x : L ⧸ N)} : Set (L ⧸ N))ᶜ := by
    intro s hs hmem
    have hsN : s ∈ N := hSN hs
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · have h' := QuotientGroup.eq.mp h.symm
      rw [inv_one, one_mul] at h'
      apply hy
      have h2 := N.mul_mem (N.inv_mem hsN) h'
      rwa [inv_mul_cancel_left] at h2
    · have h' := QuotientGroup.eq.mp h
      exact hcon ⟨s, hsN, _, h', by group⟩
  have hle := Set.ncard_le_ncard_of_injOn (fun s => ((s * y : L) : L ⧸ N)) hmaps hinj
  have hcompl := Set.ncard_add_ncard_compl ({((1 : L) : L ⧸ N), (x : L ⧸ N)} : Set (L ⧸ N))
  rw [Set.ncard_pair h1x] at hcompl
  have hidx : N.index = Nat.card (L ⧸ N) := rfl
  omega

theorem bruhat_of_benderData {L : Type*} [Group L] [Finite L] {U : Subgroup L} {n : ℕ}
    (hD : H13.QRC.BenderData L U n)
    (hidx : (Subgroup.normalizer (U : Set L)).index = Nat.card U + 1) {y : L}
    (hy : y ∉ Subgroup.normalizer (U : Set L)) (x : L) :
    x ∈ Subgroup.normalizer (U : Set L) ∨ ∃ n₁ ∈ Subgroup.normalizer (U : Set L),
      ∃ n₂ ∈ Subgroup.normalizer (U : Set L), x = n₁ * y * n₂ := by
  set N := Subgroup.normalizer (U : Set L) with hN
  refine bruhat_of_injOn hy (S := (U : Set L)) (fun u hu => Subgroup.le_normalizer hu) ?_ ?_ x
  · intro u hu u' hu' h
    have h' := QuotientGroup.eq.mp h
    have hzU : u⁻¹ * u' ∈ U := U.mul_mem (U.inv_mem hu) hu'
    have hz : u⁻¹ * u' ∈ N ⊓ N.map (MulAut.conj y⁻¹⁻¹).toMonoidHom := by
      refine ⟨Subgroup.le_normalizer hzU, (u * y)⁻¹ * (u' * y), h', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have hodd := hD.stronglyEmbedded.2.2 y⁻¹ fun h => hy (by simpa using N.inv_mem h)
    obtain ⟨k, hk⟩ := hD.isPGroup ⟨_, hzU⟩
    have h2 : orderOf (u⁻¹ * u') ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk (u⁻¹ * u') hzU]
      exact orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (u⁻¹ * u') ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj y⁻¹⁻¹).toMonoidHom) := by
      rw [← Subgroup.orderOf_mk (u⁻¹ * u') hz]
      exact orderOf_dvd_natCard _
    have hcop := Nat.Coprime.coprime_dvd_left h2
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
    have h1 := Nat.Coprime.eq_one_of_dvd hcop h3
    rwa [orderOf_eq_one_iff, inv_mul_eq_one] at h1
  · have hU : (U : Set L).ncard = Nat.card U := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [hU, hidx]

section PSL2

variable {k : Type} [Field k] [Finite k]

theorem index_psl2Borel {n : ℕ} (hk : Nat.card k = 2 ^ n) :
    (psl2Borel k).index = 2 ^ n + 1 := by
  have hD := H13.QRC.benderData_psl2 hk
  have hN := H13.QRC.psl2_normalizer_rootGroup (k := k)
  have hU := psl2UpperUnipotentSubgroup_card k
  have hB : Nat.card (psl2Borel k) = 2 ^ n * (2 ^ n - 1) := by
    have h1 := Subgroup.relIndex_mul_card (psl2UpperUnipotentSubgroup k)
      (Subgroup.normalizer (psl2UpperUnipotentSubgroup k : Set (PSL2MatrixGroup k)))
    rw [inf_eq_left.2 Subgroup.le_normalizer, hD.relIndex, hU, hk, hN] at h1
    rw [← h1, mul_comm]
  have hL : Nat.card (PSL2MatrixGroup k) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr (H13.QRC.p2PSLEquiv k).toEquiv, Ch3E213M.card_projectiveSL_two_pow hk]
  have h := (psl2Borel k).index_mul_card
  rw [hB, hL] at h
  have hq : 2 ≤ 2 ^ n := by
    rw [← hk]
    exact Finite.one_lt_card
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ n = c + 2 := ⟨2 ^ n - 2, by omega⟩
  rw [hc] at h ⊢
  have e1 : (c + 2) ^ 2 - 1 = (c + 1) * (c + 3) := by
    rw [show (c + 2) ^ 2 = (c + 1) * (c + 3) + 1 by ring, Nat.add_sub_cancel]
  have e2 : c + 2 - 1 = c + 1 := by omega
  rw [e1, e2] at h
  have hpos : 0 < (c + 2) * (c + 1) := by positivity
  have h' : (psl2Borel k).index * ((c + 2) * (c + 1)) = (c + 3) * ((c + 2) * (c + 1)) := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h'

theorem bruhat_psl2Borel {n : ℕ} (hk : Nat.card k = 2 ^ n) {y : PSL2MatrixGroup k}
    (hy : y ∉ psl2Borel k) (x : PSL2MatrixGroup k) :
    x ∈ psl2Borel k ∨ ∃ n₁ ∈ psl2Borel k, ∃ n₂ ∈ psl2Borel k, x = n₁ * y * n₂ := by
  have hN := H13.QRC.psl2_normalizer_rootGroup (k := k)
  rw [← hN] at hy ⊢
  refine bruhat_of_benderData (H13.QRC.benderData_psl2 hk) ?_ hy x
  rw [hN, index_psl2Borel hk, psl2UpperUnipotentSubgroup_card, hk]

end PSL2

section Lift

variable {G₀ L : Type*} [Group G₀] [Group L] {X M : Subgroup G₀}

theorem mem_of_map_mem {ψ : ↥X →* L} (hker : ψ.ker ≤ M.subgroupOf X) {z : X}
    (hz : ψ z ∈ (M.subgroupOf X).map ψ) : (z : G₀) ∈ M := by
  obtain ⟨w, hw, hwz⟩ := hz
  have hk : w⁻¹ * z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwz, inv_mul_cancel]
  have h2 := (M.subgroupOf X).mul_mem hw (hker hk)
  rwa [mul_inv_cancel_left] at h2

theorem bruhat_of_surjective {g : G₀} (hg : g ∈ X) (ψ : ↥X →* L) (hker : ψ.ker ≤ M.subgroupOf X)
    (hBru : ∀ y : L, y ∈ (M.subgroupOf X).map ψ ∨ ∃ n₁ ∈ (M.subgroupOf X).map ψ,
      ∃ n₂ ∈ (M.subgroupOf X).map ψ, y = n₁ * ψ ⟨g, hg⟩ * n₂) :
    ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂ := by
  intro x hx
  rcases hBru (ψ ⟨x, hx⟩) with h | ⟨n₁, ⟨w₁, hw₁, rfl⟩, n₂, ⟨w₂, hw₂, rfl⟩, h⟩
  · exact Or.inl (mem_of_map_mem hker h)
  · right
    set z : X := (w₁ * ⟨g, hg⟩ * w₂)⁻¹ * ⟨x, hx⟩ with hz
    have hzk : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel]
    have hzM : (z : G₀) ∈ M := hker hzk
    refine ⟨w₁, hw₁, w₂ * z, M.mul_mem hw₂ hzM, ?_⟩
    have e : (⟨x, hx⟩ : X) = w₁ * ⟨g, hg⟩ * (w₂ * z) := by
      rw [hz]
      group
    have e' := congrArg Subtype.val e
    simpa [mul_assoc] using e'

theorem relIndex_eq_index_map (ψ : ↥X →* L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ M.subgroupOf X) : M.relIndex X = ((M.subgroupOf X).map ψ).index := by
  rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ hψ, Subgroup.comap_map_eq,
    sup_eq_left.2 hker]

theorem bruhat_map {G : Type*} [Group G] {g : G₀} (f : G₀ →* G)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) :
    ∀ x ∈ X.map f, x ∈ M.map f ∨ ∃ m₁ ∈ M.map f, ∃ m₂ ∈ M.map f, x = m₁ * f g * m₂ := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hBru x hx with h | ⟨m₁, hm₁, m₂, hm₂, rfl⟩
  · exact Or.inl ⟨x, h, rfl⟩
  · exact Or.inr ⟨f m₁, ⟨m₁, hm₁, rfl⟩, f m₂, ⟨m₂, hm₂, rfl⟩, by rw [map_mul, map_mul]⟩

end Lift

end CFSG.Quasithin.Ch3E215M
