module

public import CFSG.OddTranspositions.FourEightBase

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_alternatingGroup_five : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have h := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  rw [← Nat.card_congr (Equiv.ofBijective _ h)]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

namespace Config

theorem conj_mem_K₁_of_commute (hQ : Config D u w v z a K₁ S') {s : G} (hs : Commute s z) :
    ∀ k ∈ K₁, s * k * s⁻¹ ∈ K₁ := by
  obtain ⟨eK⟩ := hQ.K₁_A5
  refine conj_mem_of_conj_mem_sup eK
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hk)) fun t ht => ?_
  rw [← hQ.K_eq] at ht ⊢
  exact conj_mem_thirdK_of_commute hQ.setup.normal hs ht

theorem mem_normalizer_K₁_of_commute (hQ : Config D u w v z a K₁ S') {s : G}
    (hs : Commute s z) : s ∈ Subgroup.normalizer (K₁ : Set G) :=
  mem_normalizer_of_conj (hQ.conj_mem_K₁_of_commute hs)
    (hQ.conj_mem_K₁_of_commute (hs.inv_left))

theorem commute_z_of_mem (hQ : Config D u w v z a K₁ S') {s : G} (hs : s ∈ S') :
    Commute s z :=
  Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hs)

theorem sylow_le_normalizer (hQ : Config D u w v z a K₁ S') :
    S' ≤ Subgroup.normalizer (K₁ : Set G) := fun _ hs =>
  hQ.mem_normalizer_K₁_of_commute (hQ.commute_z_of_mem hs)

theorem z_not_mem_K₁ (hQ : Config D u w v z a K₁ S') : z ∉ K₁ := by
  intro hz
  obtain ⟨-, hz1, -⟩ := hQ.z_facts
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hc : eK ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm m.2))
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hc
  exact hz1 (congrArg Subtype.val hc)

def sylowS (hQ : Config D u w v z a K₁ S') : Sylow 2 G :=
  ⟨S', hQ.sylow.1, fun {P} hP hle => hQ.sylow.2 P hP hle⟩

theorem not_two_dvd_index_sylow (hQ : Config D u w v z a K₁ S') : ¬ 2 ∣ S'.index :=
  (hQ.sylowS).not_dvd_index

theorem card_sylow_inf_K₁ (hQ : Config D u w v z a K₁ S') : Nat.card (S' ⊓ K₁ : Subgroup G) = 4 := by
  classical
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hQ.sylow.1, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (hQ.sylowS).not_dvd_index
  have hS' := hS.of_le hQ.sylow_le_normalizer le_top
  have hT := hS'.inf_of_le_normalizer (Subgroup.le_normalizer) le_rfl
  rw [hT.card_eq, Nat.card_congr eK.toEquiv]
  have : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [this]
  have h60 : (60 : ℕ).factorization 2 = 2 := by
    rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
  rw [h60]; norm_num

theorem card_sylow_eq_sixteen (hQ : Config D u w v z a K₁ S')
    (h48 : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z) :
    Nat.card S' = 16 := by
  classical
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, hz1, -⟩ := hQ.z_facts
  let φ : S' →* MulAut K₁ := K₁.normalizerMonoidHom.comp (Subgroup.inclusion hQ.sylow_le_normalizer)
  have hφ : ∀ s : S', ∀ k : K₁, ((φ s k : K₁) : G) = s * k * (s : G)⁻¹ := fun s k => rfl
  have hker : φ.ker = (Subgroup.zpowers z).subgroupOf S' := by
    rw [← h48]
    ext s
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem,
      true_and]
    have hsz : Commute (s : G) z := hQ.commute_z_of_mem s.2
    constructor
    · intro hs
      have hsK : ∀ k ∈ K₁, (s : G) * k * (s : G)⁻¹ = k := fun k hk => by
        have := congrArg (fun σ : MulAut K₁ => ((σ ⟨k, hk⟩ : K₁) : G)) hs
        simpa [hφ] using this
      have hle : thirdK D z ≤ Subgroup.centralizer ({(s : G)} : Set G) := by
        rw [hQ.K_eq]
        refine sup_le (fun k hk => ?_) ((Subgroup.zpowers_le).mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm.eq))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := hsK k hk
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ht)
    · intro hs
      ext k
      have hk : (k : G) ∈ thirdK D z := by
        rw [hQ.K_eq]; exact Subgroup.mem_sup_left k.2
      have h := Subgroup.mem_centralizer_iff.mp hs k hk
      simp only [hφ, MulAut.one_apply]
      rw [← h]; group
  have hzS : Subgroup.zpowers z ≤ S' := (Subgroup.zpowers_le).mpr hQ.z_central.1
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hkercard : Nat.card φ.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzS).toEquiv, Nat.card_zpowers, hzo]
  set T₁ : Subgroup S' := (S' ⊓ K₁).subgroupOf S' with hT₁
  have hT₁card : Nat.card T₁ = 4 := by
    rw [hT₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hQ.card_sylow_inf_K₁
  have hinj : Function.Injective (φ.comp T₁.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ht
    have ht' : (T₁.subtype t) ∈ φ.ker := ht
    rw [hker, Subgroup.mem_subgroupOf] at ht'
    have htK : ((t : S') : G) ∈ K₁ := (Subgroup.mem_inf.mp t.2).2
    rcases eq_one_or_eq_of_mem_zpowers hz2 ht' with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd (h ▸ htK) hQ.z_not_mem_K₁
  have hmapcard : Nat.card (T₁.map φ) = 4 := by
    rw [← hT₁card, ← Subgroup.range_subtype T₁, ← MonoidHom.range_comp, Subgroup.range_subtype]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hlt : T₁.map φ < φ.range := by
    refine lt_of_le_of_ne (Subgroup.map_le_range φ T₁) fun heq => ?_
    have ha : φ ⟨a, hQ.a_mem⟩ ∈ T₁.map φ := heq ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨t, ht, hta⟩ := ha
    apply hQ.a_outer
    refine ⟨t, (Subgroup.mem_inf.mp ht).2, fun x hx => ?_⟩
    have := congrArg (fun σ : MulAut K₁ => ((σ ⟨x, hx⟩ : K₁) : G)) hta
    simpa [hφ] using this.symm
  have hrange : Nat.card φ.range = 8 := by
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [hmapcard] at h1
    have h2 : Nat.card φ.range ∣ 120 := by
      rw [← card_mulAut_alternatingGroup_five, ← Nat.card_congr (MulAut.congr eK).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk⟩ := (hQ.sylow.1.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).exists_card_eq
    rw [hk] at h1 h2 ⊢
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
      norm_num at this
    interval_cases k <;> simp_all
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hkercard] at this
  exact this

end Config

end CFSG.OddTranspositions.QZ
