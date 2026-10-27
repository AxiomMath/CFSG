module

public import CFSG.Quasithin.EmptyFaithful.SzN17Fac

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153L
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem commutator_conj_mem {G : Subgroup Ω} {h : Ω} (hGn : ∀ g ∈ G, h * g * h⁻¹ ∈ G) {n : Ω}
    (hn : n ∈ ⁅G, G⁆) : h * n * h⁻¹ ∈ ⁅G, G⁆ := by
  have hmap : G.map (MulAut.conj h).toMonoidHom ≤ G := by
    rintro _ ⟨g, hg, rfl⟩
    exact hGn g hg
  have hle : ⁅G, G⁆.map (MulAut.conj h).toMonoidHom ≤ ⁅G, G⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact hle ⟨n, hn, rfl⟩

theorem goodFactor_of_perm5 {H P G : Subgroup Ω} (hP : IsSylowTwoOf P H) (hGH : G ≤ H)
    (hGn : ∀ h ∈ H, ∀ g ∈ G, h * g * h⁻¹ ∈ G) (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    GoodFactor H P G ⊥ ∧ CenterTrivial G := by
  set N : Subgroup Ω := ⁅G, G⁆ with hN
  have hNG : N ≤ G := A3.commutator_self_le G
  have hC : N = (commutator ↥G).map G.subtype := by
    rw [hN, _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype]
  have hCe : (commutator ↥G).map e.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective, ← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  have hsub : N.subgroupOf G = commutator ↥G := by
    rw [hC]
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  let eN : ↥N ≃* ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.subgroupCongr hC).trans
      ((Subgroup.equivMapOfInjective _ G.subtype G.subtype_injective).symm.trans
        ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr hCe)))
  have hs : IsSimpleGroup ↥N := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eN.isSimpleGroup
  have hNcard : Nat.card ↥N = 60 := by
    rw [Nat.card_congr eN.toEquiv, card_alternatingGroup1527d 5 (by norm_num)]
    norm_num [Nat.factorial]
  have hGcard : Nat.card ↥G = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hidx : (N.subgroupOf G).index = 2 := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf G)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG).toEquiv, hNcard, hGcard] at h1
    omega
  have hq : CFSG.IsQuasisimple ↥N := comp_quasisimple_of_simple hs (by rw [hNcard]; norm_num)
  have hperf : ⁅N, N⁆ = N := comp_perfect_of_isQuasisimple hq
  have hNcore : N ≤ perfectCore G := le_perfectCore_of_perfect hNG hperf
  have hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun h hh n hn =>
    commutator_conj_mem (fun g hg => hGn h hh g hg) hn
  set g₀ : ↥G := e.symm (Equiv.swap 0 1) with hg₀
  have hg₀N : (g₀ : Ω) ∉ N := by
    intro hmem
    have h1 : g₀ ∈ N.subgroupOf G := hmem
    rw [hsub] at h1
    have h2 : e g₀ ∈ (commutator ↥G).map e.toMonoidHom := ⟨_, h1, rfl⟩
    rw [hCe, hg₀, MulEquiv.apply_symm_apply, Equiv.Perm.mem_alternatingGroup,
      Equiv.Perm.sign_swap (by decide)] at h2
    exact absurd h2 (by decide)
  have hg₀2 : (g₀ : Ω) ^ 2 = 1 := by
    have : g₀ ^ 2 = 1 := by
      rw [hg₀, ← map_pow, sq, Equiv.swap_mul_self, map_one]
    simpa using congrArg Subtype.val this
  have hg₀1 : (g₀ : Ω) ≠ 1 := fun h => hg₀N (h ▸ N.one_mem)
  have hg₀o : orderOf (g₀ : Ω) = 2 := orderOf_eq_prime hg₀2 hg₀1
  have hτp : IsPGroup 2 (Subgroup.zpowers (g₀ : Ω)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg₀o]; norm_num)
  obtain ⟨h, hh, hle⟩ :=
    exists_conj_le_of_isSylowTwoOf hP (Subgroup.zpowers_le.2 (hGH g₀.2)) hτp
  set x : Ω := h * (g₀ : Ω) * h⁻¹ with hx
  have hxP : x ∈ P := by
    refine hle (mem_cjSub.2 ?_)
    have : h⁻¹ * x * h = (g₀ : Ω) := by rw [hx]; group
    rw [this]
    exact Subgroup.mem_zpowers _
  have hxG : x ∈ G := hGn h hh _ g₀.2
  have hxN : x ∉ N := by
    intro hxN
    apply hg₀N
    have := hNn h⁻¹ (H.inv_mem hh) x hxN
    have e1 : h⁻¹ * x * h⁻¹⁻¹ = (g₀ : Ω) := by rw [hx]; group
    rwa [e1] at this
  refine ⟨⟨bot_le, ?_, Or.inl rfl, ?_⟩, ?_⟩
  · intro y hy
    rcases mem_or_mul_mem_of_index_two hidx hxG hxN hy with hyN | hyN
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hNcore hyN))
    · have : y = x * (x⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxP)
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hNcore hyN)))
  · intro Q hQ
    exfalso
    obtain ⟨hQG, hQn, hQc⟩ := hQ
    obtain ⟨z, hzQ, hz1⟩ := exists_ne_one_of_card_three hQc
    obtain ⟨hz3, hQz⟩ := eq_zpowers_of_card_three hQc hzQ hz1
    have hzcube : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
    have hzN : z ∈ N := mem_of_cube_of_index_two hidx (hQG hzQ) hzcube
    have hQN : Q ≤ N := by rw [hQz]; exact Subgroup.zpowers_le.2 hzN
    have hnorm : (Q.subgroupOf N).Normal :=
      ⟨fun n hn' g => Subgroup.mem_subgroupOf.2 (hQn g (hNG g.2) n hn')⟩
    rcases hs.eq_bot_or_eq_top_of_normal (Q.subgroupOf N) with h0 | h0
    · have : (⟨z, hzN⟩ : ↥N) ∈ Q.subgroupOf N := hzQ
      rw [h0, Subgroup.mem_bot] at this
      exact hz1 (congrArg Subtype.val this)
    · have hNQ : N ≤ Q := fun n hn => by
        have : (⟨n, hn⟩ : ↥N) ∈ Q.subgroupOf N := h0 ▸ Subgroup.mem_top _
        exact this
      have := Subgroup.card_le_of_le hNQ
      omega
  · intro a haG hac
    have hcomm : ∀ g' : Equiv.Perm (Fin 5), g' * e ⟨a, haG⟩ = e ⟨a, haG⟩ * g' := by
      intro g'
      obtain ⟨g, rfl⟩ := e.surjective g'
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hac g g.2))
    have h1 : e ⟨a, haG⟩ = 1 := perm_center_trivial (by simp) _ hcomm
    have h2 : (⟨a, haG⟩ : ↥G) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2

end CFSG.Quasithin.SzN17
