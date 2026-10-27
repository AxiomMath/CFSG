module

public import CFSG.Quasithin.EmptyFaithful.S146zMSol
public import CFSG.Quasithin.EmptyFaithful.S146zRImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Elem

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem q_image_mono {G₁ K K' : Subgroup G} (h : K ≤ K') :
    imageOTwoQuot G₁ K ≤ imageOTwoQuot G₁ K' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem q_normal_image_of_normal {G₁ K : Subgroup G} (hKG : K ≤ G₁)
    (hn : G₁ ≤ Subgroup.normalizer (K : Set G)) : (imageOTwoQuot G₁ K).Normal :=
  Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hn) (qPi G₁)
    (qPi_surjective G₁)

theorem q_forall_comm_eq_one_of_equiv {X : Type*} [Group X] {N : Subgroup X} {L : Type*} [Group L]
    [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a) (e : ↥N ≃* L) :
    ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
  intro n hn hc
  have hcen : e ⟨n, hn⟩ ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨m', rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc m' m'.2).symm
  have hbot : Subgroup.center L = ⊥ := by
    rcases (Subgroup.center L).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  rw [hbot, Subgroup.mem_bot] at hcen
  have : (⟨n, hn⟩ : ↥N) = 1 := e.injective (by rw [hcen, map_one])
  exact congrArg Subtype.val this

theorem q_exists_elemAbelian_image (h12 : Stage14612PartP) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) :
    ∃ E : Subgroup (OTwoQuot (mcOf T)), E ≤ imageOTwoQuot (mcOf T) (oTwoUpper H) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  obtain ⟨-, H₀, H₁, H₂, t, hdecP⟩ := h12 G T M S H PQ p hred hmax
  have : Fact p.Prime := ⟨hred.prime⟩
  obtain ⟨E, hEH, hEK, hEel, hEcard⟩ := hdecP.exists_elemAbelian_sq hred.prime hred.odd
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  obtain ⟨hE', hE'card⟩ := zm_isElemAbelian_subgroupOf (hEH.trans hHG) hEel
  have hRp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T)) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨hEb, hEbcard⟩ := isElemAbelian_map_quotient (CFSG.Open.pCore 2 ↥(mcOf T)) hRp
    hred.odd hE'
  exact ⟨(E.subgroupOf (mcOf T)).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(mcOf T))),
    Subgroup.map_mono (Subgroup.comap_mono hEK), hEb, by rw [hEbcard, hE'card, hEcard]⟩

end Elem

end CFSG.Quasithin
