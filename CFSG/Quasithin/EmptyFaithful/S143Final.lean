module

public import CFSG.Quasithin.EmptyFaithful.S143Fuse
public import CFSG.Quasithin.EmptyFaithful.S143Invol
public import CFSG.Quasithin.EmptyFaithful.S142Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G]

theorem pResidual_two_eq_top_of_simple (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    pResidual 2 G = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rw [pResidual, Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  intro hN
  rw [Subgroup.mem_iInf]
  intro hpow
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hG N hN with h | h
  · exfalso
    have hp : IsPGroup 2 G := by
      intro x
      obtain ⟨k, hk⟩ := hpow x
      exact ⟨k, by simpa [h] using hk⟩
    have : Nontrivial G := hG.toNontrivial
    have hc : Subgroup.center G ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot]
      exact hp.center_nontrivial
    have hctop : Subgroup.center G = ⊤ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hG (Subgroup.center G) inferInstance with h' | h'
      · exact absurd h' hc
      · exact h'
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (hctop ▸ Subgroup.mem_top b) a)
  · rw [h]; exact Subgroup.mem_top t

theorem exists_g {T M L : Subgroup G} (h : Hyp1281Two G T M L) :
    ∃ g ∈ L, g ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨l, hlL, hlodd, hlC⟩ := h.exists_odd_not_mem_centralizer
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  exact ⟨l, hlL, fun hlZ => hlC (h.mem_centralizer_of_odd (hVred.2.1 (h.le hlL))
    (Subgroup.centralizer_le_normalizer _ hlZ) hlodd)⟩

theorem false_of_transfer {T M : Subgroup G} (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hT : quasithinIsSylowTwo T)
    (hRQ : rOf T M ⊔ qOf T ≤ T) (hidx : (rOf T M ⊔ qOf T).relIndex T = 2)
    (hUQ : uOfL22 T M = qOf T) (c21 : Concl14321 T M) : False := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hRU : rOf T M ⊔ uOfL22 T M = rOf T M ⊔ qOf T := by rw [hUQ]
  obtain ⟨t, htT, htRU, ht2⟩ := c21.exists_invol (by rw [hRU]; exact hidx)
  rw [hRU] at htRU
  have hQ : ∀ x : G, x⁻¹ * t * x ∉ rOf T M ⊔ qOf T := by
    intro x hx
    have hx2 : orderOf (x⁻¹ * t * x) = 2 := by
      have e : x⁻¹ * t * x = (MulAut.conj x⁻¹ : MulAut G) t := by
        simp
      rw [e, MulEquiv.orderOf_eq]
      exact ht2
    obtain ⟨y, z, hz, hz1, hyz⟩ := c21.fused _ (hRU ▸ hx) hx2
    refine c21.not_fused t htT htRU ht2 (x * y) z hz hz1 ?_
    have e : t = x * (y * z * y⁻¹) * x⁻¹ := by rw [hyz]; group
    rw [e]
    group
  have := thompson_transfer_lemma S (Q := rOf T M ⊔ qOf T) (hS ▸ hRQ) (hS ▸ hidx) ht2 hQ
  exact this (by rw [pResidual_two_eq_top_of_simple hsimple hnab]; exact Subgroup.mem_top t)

end S143

open S143 in
theorem stageTheorem14316_of_lemmas (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h15 : Lemma14315) (h18a : Lemma14318a) (h18b : Lemma14318b) (h18c : Lemma14318c)
    (h19b : Lemma14319Rest) (h20 : Lemma14320) (h21b : Lemma14321Two) (h22 : Lemma14322) :
    StageTheorem14316 := by
  intro G _ _ T M hyp hnot
  by_contra hnab
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨g, hgL, hgH⟩ := exists_g h1281
  have c15 := h15 G T M hyp hnot hnab
  have hc : Counter T M g := ⟨hyp, h1281, hnot, hnab, hgL, hgH, c15⟩
  have c18a := h18a G T M g hc
  obtain ⟨A, t, c18b⟩ := h18b G T M g hc c18a
  have c18 : Concl14318 T M g A t := ⟨c18a, c18b, h18c G T M g A t hc c18a c18b⟩
  have c19a := lemma_14_3_19_one hc
  have c19 : Concl14319 T M A := ⟨c19a, h19b G T M g A t hc c18 c19a⟩
  have c20 := h20 G T M g A t hc c18 c19
  have c21 : Concl14321 T M :=
    ⟨lemma_14_3_21_one G T M g A t hc c18 c19 c20, h21b G T M g A t hc c18 c19 c20,
      lemma_14_3_21_three G T M g A t hc c18 c19 c20⟩
  obtain ⟨-, hUQ⟩ := h22 G T M g A t hc c18 c19 c20 c21
  exact false_of_transfer hyp.simple hyp.nonabelian hyp.sylow (rq_le_of_hyp h1281) c18a.rq_index hUQ c21

namespace S143

structure Inputs14316 : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h18a : Lemma14318a
  h18b : Lemma14318b
  h18c : Lemma14318c
  h19b : Lemma14319Rest
  h20 : Lemma14320
  h21b : Lemma14321Two
  h22 : Lemma14322

end S143

theorem stageTheorem14316_of_inputs (h : S143.Inputs14316) : StageTheorem14316 :=
  stageTheorem14316_of_lemmas h.h11 h.h113 h.h15 h.h18a h.h18b h.h18c h.h19b h.h20 h.h21b h.h22

end CFSG.Quasithin
