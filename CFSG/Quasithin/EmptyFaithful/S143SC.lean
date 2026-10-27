module

public import CFSG.Quasithin.EmptyFaithful.S143SB
public import CFSG.Quasithin.EmptyFaithful.S143SA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_into_T {T : Subgroup G} (hT : quasithinIsSylowTwo T) {S : Subgroup G}
    (hS : IsPGroup 2 S) : ∃ g : G, ∀ u ∈ S, g⁻¹ * u * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  obtain ⟨P₀, hP₀⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ P₀
  refine ⟨g, fun u hu => ?_⟩
  have hu' : u ∈ ((g • S₀ : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hP₀ hu
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hu'
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp hu'
  rw [hS₀] at ht'
  have : g⁻¹ * (g * t' * g⁻¹) * g = t' := by group
  show g⁻¹ * (g * t' * g⁻¹) * g ∈ T
  rw [this]; exact ht'

end Generic

section VConj

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c hD hd4 hxL hx3 in
theorem exists_conj_of_mem_V_ne_one {v : G} (hv : v ∈ VZ T M) (hv1 : v ≠ 1) :
    ∃ s : G, s * (d * d) * s⁻¹ = v := by
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  rcases hall v hv with h | h | h | h
  · exact absurd h hv1
  · exact ⟨1, by rw [h]; group⟩
  · exact ⟨x, by rw [h, ha]⟩
  · refine ⟨x * x, ?_⟩
    rw [h, ← hxa, ha]; group

theorem V_sq_eq_one (c : Counter T M g) (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
    (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3) {v : G} (hv : v ∈ VZ T M) : v * v = 1 := by
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hzz : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  rcases hall v hv with h | h | h | h
  · rw [h, mul_one]
  · rw [h]; exact hzz
  · rw [h]; exact haa
  · rw [h]
    calc (d * d) * a * ((d * d) * a) = (d * d) * (a * (d * d)) * a := by group
      _ = (d * d) * ((d * d) * a) * a := by rw [← hza]
      _ = ((d * d) * (d * d)) * (a * a) := by group
      _ = 1 := by rw [hzz, haa, one_mul]

end VConj

section TwSylow

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c18 hD hd4 hxL hx3 in
theorem isSylowTwoOf_Tw
    (hΓ : Subgroup.centralizer (A : Set G) = A) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
      (Subgroup.centralizer ({wOfX d x} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := wOfX d x with hw
  set H' := Subgroup.centralizer ({w} : Set G) with hH'
  set Tw := T ⊓ H' with hTw
  have hTwH : Tw ≤ H' := inf_le_right
  have hTw2 : IsPGroup 2 ↥Tw := c.hyp.sylow.1.to_le inf_le_left
  have hK2 : IsPGroup 2 ↥(Tw.subgroupOf H') :=
    hTw2.of_equiv (Subgroup.subgroupOfEquivOfLe hTwH).symm
  obtain ⟨P, hKP⟩ := hK2.exists_le_sylow
  set S : Subgroup G := (P : Subgroup ↥H').map H'.subtype with hS
  have hS2 : IsPGroup 2 ↥S := P.isPGroup'.map H'.subtype
  have hSH : S ≤ H' := by rintro _ ⟨p, -, rfl⟩; exact p.2
  have hTwS : Tw ≤ S := fun u hu => ⟨⟨u, hTwH hu⟩, hKP (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  have hcard : Nat.card ↥S ≤ Nat.card ↥Tw := by
    obtain ⟨g₀, hg₀⟩ := exists_conj_into_T c.hyp.sylow hS2
    have hwX : w ∈ Xgen T M := wOfX_mem_Xgen c hD hxL
    have hX_le_Tw : Xgen T M ≤ Tw := by
      refine le_inf Xgen_le_T fun ξ hξ => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh; subst hh
      exact Xgen_comm c hD hd4 _ hwX _ hξ
    have hconjX : conjSubgroup (Xgen T M) g₀ ≤ T := by
      intro v hv
      have h1 : g₀ * v * g₀⁻¹ ∈ Xgen T M := mem_conjSubgroup_iff.mp hv
      have := hg₀ _ (hTwS (hX_le_Tw h1))
      simpa [mul_assoc] using this
    have hweak : conjSubgroup (Xgen T M) g₀ = Xgen T M :=
      isWeaklyClosedIn_Wgen_delta (dOf T M) T g₀ hconjX
    have hw'X : g₀⁻¹ * w * g₀ ∈ Xgen T M := by
      have : g₀⁻¹ * w * g₀ ∈ conjSubgroup (Xgen T M) g₀ := by
        rw [mem_conjSubgroup_iff]
        have e : g₀ * (g₀⁻¹ * w * g₀) * g₀⁻¹ = w := by group
        rw [e]; exact hwX
      rwa [hweak] at this
    have hw2 : w * w = 1 := wOfX_sq c hD hd4 hxL hx3
    have hw'2 : (g₀⁻¹ * w * g₀) * (g₀⁻¹ * w * g₀) = 1 := by
      calc (g₀⁻¹ * w * g₀) * (g₀⁻¹ * w * g₀) = g₀⁻¹ * (w * w) * g₀ := by group
        _ = 1 := by rw [hw2]; group
    have hwRU := wOfX_not_mem_RU c c18 hΓ hD hd4 hxL
    have hw1 : w ≠ 1 := by
      intro h
      apply hwRU
      have : wOfX d x = 1 := by rw [← hw]; exact h
      rw [this]; exact (rOf T M ⊔ uOfL22 T M).one_mem
    rcases Xgen_invol c hD hd4 hxL hx3 hw'X hw'2 with hV | ⟨v, hvV, hwv⟩
    · exfalso
      have hv1 : g₀⁻¹ * w * g₀ ≠ 1 := by
        intro h
        apply hw1
        calc w = g₀ * (g₀⁻¹ * w * g₀) * g₀⁻¹ := by group
          _ = 1 := by rw [h]; group
      obtain ⟨s, hs⟩ := exists_conj_of_mem_V_ne_one c hD hd4 hxL hx3 hV hv1
      refine wOfX_not_conj_sq c hD hd4 hxL hx3 (g₀ * s) ?_
      calc (g₀ * s) * (d * d) * (g₀ * s)⁻¹ = g₀ * (s * (d * d) * s⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * w * g₀) * g₀⁻¹ := by rw [hs]
        _ = w := by group
        _ = wOfX d x := hw
    · obtain ⟨e, he, hev⟩ := exists_comm_eq_of_mem_V c c18 hD hd4 hxL hx3 hΓ hvV
      have hvv := V_sq_eq_one c hD hd4 hxL hx3 hvV
      have hvX : v ∈ Xgen T M := VZ_le_Xgen c hvV
      have hvw : v * w = w * v := Xgen_comm c hD hd4 _ hvX _ hwX
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      have hewe : e * w * e⁻¹ = g₀⁻¹ * w * g₀ := by
        have h1 : e * w * e⁻¹ * w⁻¹ = v⁻¹ := by
          calc e * w * e⁻¹ * w⁻¹ = (w * e * w⁻¹ * e⁻¹)⁻¹ := by group
            _ = v⁻¹ := by rw [hev]
        calc e * w * e⁻¹ = (e * w * e⁻¹ * w⁻¹) * w := by group
          _ = v * w := by rw [h1, hvinv]
          _ = w * v := hvw
          _ = g₀⁻¹ * w * g₀ := hwv.symm
      have heT : e ∈ T := rOf_le_T_of_hyp c.h1281 (c18.b.A_le he)
      have hwq : (g₀ * e)⁻¹ * w * (g₀ * e) = w := by
        calc (g₀ * e)⁻¹ * w * (g₀ * e) = e⁻¹ * (g₀⁻¹ * w * g₀) * e := by group
          _ = e⁻¹ * (e * w * e⁻¹) * e := by rw [hewe]
          _ = w := by group
      let F : ↥S → ↥Tw := fun u => ⟨(g₀ * e)⁻¹ * (u : G) * (g₀ * e), by
        refine ⟨?_, ?_⟩
        · have h1 := hg₀ _ u.2
          have e' : (g₀ * e)⁻¹ * (u : G) * (g₀ * e) = e⁻¹ * (g₀⁻¹ * (u : G) * g₀) * e := by group
          rw [e']
          exact T.mul_mem (T.mul_mem (T.inv_mem heT) h1) heT
        · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          rw [Set.mem_singleton_iff] at hh; subst hh
          have huw : w * (u : G) = (u : G) * w :=
            Subgroup.mem_centralizer_iff.mp (hSH u.2) w (Set.mem_singleton w)
          calc w * ((g₀ * e)⁻¹ * (u : G) * (g₀ * e))
              = ((g₀ * e)⁻¹ * w * (g₀ * e)) * ((g₀ * e)⁻¹ * (u : G) * (g₀ * e)) := by rw [hwq]
            _ = (g₀ * e)⁻¹ * (w * (u : G)) * (g₀ * e) := by group
            _ = (g₀ * e)⁻¹ * ((u : G) * w) * (g₀ * e) := by rw [huw]
            _ = ((g₀ * e)⁻¹ * (u : G) * (g₀ * e)) * ((g₀ * e)⁻¹ * w * (g₀ * e)) := by group
            _ = ((g₀ * e)⁻¹ * (u : G) * (g₀ * e)) * w := by rw [hwq]⟩
      refine Nat.card_le_card_of_injective F fun u u' huu' => ?_
      have h1 := congrArg Subtype.val huu'
      simp only [F] at h1
      apply Subtype.ext
      have h2 := mul_left_cancel (mul_right_cancel h1)
      exact h2
  have hSeq : Tw = S := Subgroup.eq_of_le_of_card_ge hTwS hcard
  have hPeq : (P : Subgroup ↥H') = Tw.subgroupOf H' := by
    refine le_antisymm (fun p hp => ?_) hKP
    rw [Subgroup.mem_subgroupOf, hSeq]
    exact ⟨p, hp, rfl⟩
  refine ⟨hTwH, hTw2, ?_⟩
  have := P.not_dvd_index
  rwa [hPeq] at this

end TwSylow

end S143

end CFSG.Quasithin
