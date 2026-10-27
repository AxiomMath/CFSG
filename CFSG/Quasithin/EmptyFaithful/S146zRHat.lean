module

public import CFSG.Quasithin.EmptyFaithful.S146zRPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Hat

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_hatT_sylow (S : Setting146 G T M) :
    IsSylowTwoOf (imageOTwoQuot (mcOf T) T) (⊤ : Subgroup (OTwoQuot (mcOf T))) := by
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTi : ¬ 2 ∣ T.index := S.hyp.sylow.2
  have hT'p : IsPGroup 2 (T.subgroupOf (mcOf T)) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm
  have hT'i : ¬ 2 ∣ (T.subgroupOf (mcOf T)).index := by
    intro hd
    apply hTi
    have h1 : T.relIndex (mcOf T) * (mcOf T).index = T.index := Subgroup.relIndex_mul_index hTG
    rw [← h1]
    exact hd.trans (dvd_mul_right _ _)
  exact isSylowTwoOf_map_quotient (CFSG.Open.pCore 2 ↥(mcOf T)) hT'p hT'i

omit [Finite G] in
theorem q_image_mem_normalizer {G₁ K L : Subgroup G} (hn : L ≤ Subgroup.normalizer (K : Set G))
    {x : OTwoQuot G₁} (hx : x ∈ imageOTwoQuot G₁ L) :
    x ∈ Subgroup.normalizer (imageOTwoQuot G₁ K : Set (OTwoQuot G₁)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact q_image_normalizes hn x hx y hy
  · intro hy
    have := q_image_normalizes hn x⁻¹ ((imageOTwoQuot G₁ L).inv_mem hx) _ hy
    simpa [mul_assoc] using this

omit [Finite G] in
theorem q_hatT_le_hatH (hred : IsRedCE T M H PQ p) :
    imageOTwoQuot (mcOf T) T ≤ imageOTwoQuot (mcOf T) H :=
  q_image_mono hred.isHTM.1.1

theorem q_hat_decomp (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {x : OTwoQuot (mcOf T)} (hx : x ∈ imageOTwoQuot (mcOf T) H) :
    ∃ k ∈ imageOTwoQuot (mcOf T) (oTwoUpper H), ∃ t ∈ imageOTwoQuot (mcOf T) T, x = k * t := by
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨p', hp', t', ht', hpt⟩ := hred.exists_mul_of_mem S (Subgroup.mem_subgroupOf.mp hh)
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hp'K : p' ∈ oTwoUpper H := oTwoUpper_mono hred.le hp'
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  refine ⟨qPi (mcOf T) ⟨p', hHG (oTwoUpper_le H hp'K)⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hp'K, rfl⟩,
    qPi (mcOf T) ⟨t', hTG ht'⟩, ⟨_, Subgroup.mem_subgroupOf.mpr ht', rfl⟩, ?_⟩
  rw [← map_mul]
  congr 1
  exact Subtype.ext hpt

theorem q_card_hatK_dvd (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    Nat.card (imageOTwoQuot (mcOf T) (oTwoUpper H)) ∣ Nat.card H := by
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hKG : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans hHG
  have h1 : Nat.card (imageOTwoQuot (mcOf T) (oTwoUpper H)) ∣
      Nat.card ↥((oTwoUpper H).subgroupOf (mcOf T)) :=
    Subgroup.card_dvd_of_surjective ((qPi (mcOf T)).subgroupMap_surjective _)
  have h2 : Nat.card ↥((oTwoUpper H).subgroupOf (mcOf T)) = Nat.card (oTwoUpper H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv
  exact (h2 ▸ h1).trans (Subgroup.card_dvd_of_le (oTwoUpper_le H))

theorem q_prime_dvd_card_H (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card H) :
    r = 2 ∨ r = 3 ∨ (p = 5 ∧ r = 5) := by
  have hsolv := input14614Solv_proved G T M S H PQ p hred hmax H le_rfl (S.le_mcOf hred.isHTM)
    (hred.isSolvable S)
  rcases S.p_eq_three_or_five_of_isRedCE hred with hp | hp
  · rcases hsolv.1 hp r hr hd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hsolv.2 hp r hr hd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hp, h⟩)

end Hat

end CFSG.Quasithin
