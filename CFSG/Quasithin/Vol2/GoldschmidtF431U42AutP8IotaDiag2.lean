module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDiag1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂)

theorem grBf_mem_range {z : Ah} (hz : z ∈ Bh) : grBf iso z ∈ (grB iso).range :=
  ⟨⟨z, hz⟩, (grBf_of_mem iso hz).symm⟩

theorem conj1 (x : ↥P1h) {b : Ah} (hb : b ∈ Bh) (hxb : (x : Ah) * b * x ∈ Bh) :
    gr1 iso x * grBf iso b * gr1 iso x = grBf iso ((x : Ah) * b * x) := by
  have h1 : grBf iso b = gr1 iso (Subgroup.inclusion Bh_le_P1h ⟨b, hb⟩) := by
    rw [grBf_of_mem iso hb]
    rfl
  rw [h1, ← map_mul, ← map_mul]
  exact gr1_eq_grBf iso _ hxb

theorem conj2 (x : ↥P2h) {b : Ah} (hb : b ∈ Bh) (hxb : (x : Ah) * b * x ∈ Bh) :
    gr2 iso x * grBf iso b * gr2 iso x = grBf iso ((x : Ah) * b * x) := by
  have h1 : grBf iso b = gr2 iso (Subgroup.inclusion Bh_le_P2h ⟨b, hb⟩) := by
    rw [grBf_of_mem iso hb, ← gr2_incl iso ⟨b, hb⟩]
  rw [h1, ← map_mul, ← map_mul]
  exact gr2_eq_grBf iso _ hxb

theorem bnPair_of_ahBN {s t : Ah} {us ut : List Ah} (H : AhBN s t us ut)
    (hG : ((iso.toG1 ⟨s, H.s1⟩) * iso.toG2 ⟨t, H.t1⟩) ^ 4 = 1) :
    BNPair (grB iso).range (gr1 iso).range (gr2 iso).range (gr1 iso ⟨s, H.s1⟩)
      (gr2 iso ⟨t, H.t1⟩) (us.map (grBf iso)) (ut.map (grBf iso)) := by
  have hs2 : gr1 iso ⟨s, H.s1⟩ * gr1 iso ⟨s, H.s1⟩ = 1 := by
    rw [← map_mul, show (⟨s, H.s1⟩ : ↥P1h) * ⟨s, H.s1⟩ = 1 from Subtype.ext H.s2, map_one]
  have ht2 : gr2 iso ⟨t, H.t1⟩ * gr2 iso ⟨t, H.t1⟩ = 1 := by
    rw [← map_mul, show (⟨t, H.t1⟩ : ↥P2h) * ⟨t, H.t1⟩ = 1 from Subtype.ext H.t2, map_one]
  refine ⟨⟨?_, ⟨_, rfl⟩, hs2, ?_, ?_, ?_⟩, ⟨?_, ⟨_, rfl⟩, ht2, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion Bh_le_P1h b, rfl⟩
  · rintro ⟨b, hb⟩
    have h : (b : Ah) = s := congrArg Prod.fst hb
    exact H.s3 (h ▸ b.2)
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    exact grBf_mem_range iso (H.us_B u hu)
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    rcases H.cos1 x x.2 with hB | ⟨v, hv, b, hb, hvx⟩
    · exact Or.inl ⟨⟨x, hB⟩, rfl⟩
    · refine Or.inr ⟨grBf iso v, List.mem_map_of_mem hv, grBf iso b,
        grBf_mem_range iso hb, ?_⟩
      rw [← gr1_eq_grBf iso ⟨v, Bh_le_P1h (H.us_B v hv)⟩ (H.us_B v hv),
        ← gr1_eq_grBf iso ⟨b, Bh_le_P1h hb⟩ hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hvx
  · rintro _ ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion Bh_le_P2h b, gr2_incl iso b⟩
  · rintro ⟨b, hb⟩
    have h : (b : Ah) = t := congrArg Prod.fst hb
    exact H.t3 (h ▸ b.2)
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    exact grBf_mem_range iso (H.ut_B u hu)
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    rcases H.cos2 x x.2 with hB | ⟨v, hv, b, hb, hvx⟩
    · exact Or.inl ⟨⟨x, hB⟩, (gr2_incl iso ⟨x, hB⟩).symm⟩
    · refine Or.inr ⟨grBf iso v, List.mem_map_of_mem hv, grBf iso b,
        grBf_mem_range iso hb, ?_⟩
      rw [← gr2_eq_grBf iso ⟨v, Bh_le_P2h (H.ut_B v hv)⟩ (H.ut_B v hv),
        ← gr2_eq_grBf iso ⟨b, Bh_le_P2h hb⟩ hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hvx
  ·
    refine Prod.ext ?_ ?_
    · simpa [gr1_apply, gr2_apply] using H.braid
    · have hg1 : iso.toG1 ⟨s, H.s1⟩ * iso.toG1 ⟨s, H.s1⟩ = 1 := by
        rw [← map_mul, show (⟨s, H.s1⟩ : ↥P1h) * ⟨s, H.s1⟩ = 1 from Subtype.ext H.s2, map_one]
      have hg2 : iso.toG2 ⟨t, H.t1⟩ * iso.toG2 ⟨t, H.t1⟩ = 1 := by
        rw [← map_mul, show (⟨t, H.t1⟩ : ↥P2h) * ⟨t, H.t1⟩ = 1 from Subtype.ext H.t2, map_one]
      simpa [gr1_apply, gr2_apply] using braid_of_pow_four hg1 hg2 hG
  ·
    intro u' hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    obtain ⟨c1, c2, c3⟩ := H.us_chain u hu
    have e1 := conj2 iso ⟨t, H.t1⟩ (H.us_B u hu) c1
    have e2 := conj1 iso ⟨s, H.s1⟩ c1 c2
    have e3 := conj2 iso ⟨t, H.t1⟩ c2 c3
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact grBf_mem_range iso c1
    · rw [e1, e2]; exact grBf_mem_range iso c2
    · rw [e1, e2, e3]; exact grBf_mem_range iso c3
  ·
    intro u' hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    obtain ⟨c1, c2, c3⟩ := H.ut_chain u hu
    have e1 := conj1 iso ⟨s, H.s1⟩ (H.ut_B u hu) c1
    have e2 := conj2 iso ⟨t, H.t1⟩ c1 c2
    have e3 := conj1 iso ⟨s, H.s1⟩ c2 c3
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact grBf_mem_range iso c1
    · rw [e1, e2]; exact grBf_mem_range iso c2
    · rw [e1, e2, e3]; exact grBf_mem_range iso c3
  · simpa using H.us_len
  · simpa using H.ut_len

end CFSG.Quasithin.H13.F431.U42Aut
