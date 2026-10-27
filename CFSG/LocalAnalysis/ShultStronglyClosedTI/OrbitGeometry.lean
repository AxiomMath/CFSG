module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem orbit_map_injective (U : Subgroup G) (β : Ω)
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) :
    Function.Injective (fun u : U => (u : G) • β) := by
  intro u v huv
  change (u : G) • β = (v : G) • β at huv
  have hfix : (v : G)⁻¹ * u ∈ MulAction.stabilizer G β := by
    change ((v : G)⁻¹ * u) • β = β
    rw [mul_smul, huv, inv_smul_smul]
  have hone : (v : G)⁻¹ * u = 1 :=
    Subgroup.mem_bot.mp (hfree ▸
      (show (v : G)⁻¹ * u ∈ U ⊓ MulAction.stabilizer G β from
        ⟨U.mul_mem (U.inv_mem v.property) u.property, hfix⟩))
  exact Subtype.ext (inv_mul_eq_one.mp hone).symm

def pointOrbitEquiv (U : Subgroup G) (β : Ω)
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) : U ≃ MulAction.orbit U β :=
  Equiv.ofBijective (fun u => ⟨(u : G) • β, MulAction.mem_orbit β u⟩) ⟨
    fun _ _ h => orbit_map_injective U β hfree (congrArg Subtype.val h),
    fun ⟨_, u, hu⟩ => ⟨u, Subtype.ext hu⟩⟩

theorem smul_orbit_parameter {β : Ω} {b : G} (hb : b • β = β) (u : G) :
    b • (u • β) = (b * u * b⁻¹) • β := by
  have hinv : b⁻¹ • β = β := by
    simpa only [inv_smul_smul] using
      (congrArg (fun x : Ω => b⁻¹ • x) hb).symm
  rw [mul_smul, mul_smul, hinv]

theorem pointOrbitEquiv_equivariant (U : Subgroup G) (β : Ω)
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥)
    {b : G} (hb : b ∈ MulAction.stabilizer G β)
    (hbn : b ∈ Subgroup.normalizer (U : Set G)) (u : U) :
    b • (pointOrbitEquiv U β hfree u : Ω) =
      (pointOrbitEquiv U β hfree
        ⟨b * u * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbn _).mp u.property⟩ : Ω) :=
  smul_orbit_parameter (MulAction.mem_stabilizer_iff.mp hb) u

theorem triple_stabilizer_eq_centralizer (U : Subgroup G) (α β : Ω)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G} (hu : u ∈ U) :
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        MulAction.stabilizer G (u • β) =
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        Subgroup.centralizer ({u} : Set G) := by
  ext b
  constructor
  · rintro ⟨⟨hbα, hbβ⟩, hbthird⟩
    refine ⟨⟨hbα, hbβ⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hconj : b * u * b⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hnormal hbα) u).mp hu
    have hfixed : (b * u * b⁻¹) • β = u • β := by
      rw [← smul_orbit_parameter (MulAction.mem_stabilizer_iff.mp hbβ)]
      exact MulAction.mem_stabilizer_iff.mp hbthird
    have heq := congrArg Subtype.val
      (orbit_map_injective U β hfree
        (a₁ := ⟨b * u * b⁻¹, hconj⟩) (a₂ := ⟨u, hu⟩) hfixed)
    change b * u * b⁻¹ = u at heq
    calc
      b * u = (b * u * b⁻¹) * b := by group
      _ = u * b := by rw [heq]
  · rintro ⟨⟨hbα, hbβ⟩, hbcomm⟩
    refine ⟨⟨hbα, hbβ⟩, MulAction.mem_stabilizer_iff.mpr ?_⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hbcomm
    calc
      b • (u • β) = (b * u) • β := (mul_smul _ _ _).symm
      _ = (u * b) • β := by rw [hcomm]
      _ = u • β := by rw [mul_smul, MulAction.mem_stabilizer_iff.mp hbβ]

theorem orbit_kernel_eq_centralizer (U : Subgroup G) (α β : Ω)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) :
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        fixingSubgroup G (MulAction.orbit U β) =
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        Subgroup.centralizer (U : Set G) := by
  ext b
  constructor
  · rintro ⟨hb, hker⟩
    refine ⟨hb, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro u hu
    have hthird : b ∈ MulAction.stabilizer G (u • β) :=
      MulAction.mem_stabilizer_iff.mpr
        (hker ⟨u • β, MulAction.mem_orbit β (⟨u, hu⟩ : U)⟩)
    have hc := (triple_stabilizer_eq_centralizer U α β hnormal hfree hu) ▸
      (show b ∈ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        MulAction.stabilizer G (u • β) from ⟨hb, hthird⟩)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
  · rintro ⟨hb, hc⟩
    refine ⟨hb, ?_⟩
    rintro ⟨_, u, rfl⟩
    have hbu : b ∈ Subgroup.centralizer ({(u : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hc _ u.property).symm)
    exact MulAction.mem_stabilizer_iff.mp
      ((triple_stabilizer_eq_centralizer U α β hnormal hfree u.property).symm ▸
        (show b ∈ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
          Subgroup.centralizer ({(u : G)} : Set G) from ⟨hb, hbu⟩)).2

theorem centralizes_triple_stabilizer_subgroup (U : Subgroup G) (α β : Ω)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G} (hu : u ∈ U)
    (K : Subgroup G)
    (hK : K ≤ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
      MulAction.stabilizer G (u • β)) :
    u ∈ Subgroup.centralizer (K : Set G) ∧ u ∈ Subgroup.normalizer (K : Set G) := by
  have hKC : K ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [triple_stabilizer_eq_centralizer U α β hnormal hfree hu] at hK
    exact hK.trans inf_le_right
  have hcomm : u ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  exact ⟨hcomm, Subgroup.centralizer_le_normalizer _ hcomm⟩

theorem mem_zpowers_involution_iff {u x : G} (hu : orderOf u = 2) :
    x ∈ Subgroup.zpowers u ↔ x = 1 ∨ x = u := by
  constructor
  · intro hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    · have hcard : Nat.card (Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hu]
      obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers u)).mp hcard
      have hx' : (⟨x, hx⟩ : Subgroup.zpowers u) ≠ 1 :=
        fun h => hxone (congrArg Subtype.val h)
      have hu' : (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) ≠ 1 := by
        intro h
        have hone : u = 1 := congrArg Subtype.val h
        simp [hone] at hu
      exact Or.inr (congrArg Subtype.val ((hw _ hx').trans (hw _ hu').symm))
  · intro h
    rcases h with h | h
    · rw [h]
      exact (Subgroup.zpowers u).one_mem
    · rw [h]
      exact Subgroup.mem_zpowers u

theorem involution_exchanges_orbit_pair (U : Subgroup G) (β : Ω)
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G}
    (hu : u ∈ U) (huorder : orderOf u = 2) :
    u • β ≠ β ∧ u • (u • β) = β := by
  constructor
  · intro hfix
    have hone : u = 1 := Subgroup.mem_bot.mp
      (hfree ▸ (show u ∈ U ⊓ MulAction.stabilizer G β from
        ⟨hu, MulAction.mem_stabilizer_iff.mpr hfix⟩))
    simp [hone] at huorder
  · have hpow := pow_orderOf_eq_one u
    rw [huorder, pow_two] at hpow
    rw [← mul_smul, hpow, one_smul]

theorem pair_stabilizer_decomposition (U : Subgroup G) (α β : Ω)
    (hUα : U ≤ MulAction.stabilizer G α)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G}
    (hu : u ∈ U) (huorder : orderOf u = 2) :
    let E := (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
      MulAction.stabilizer G (u • β)
    let F := MulAction.stabilizer G α ⊓
      MulAction.stabilizer G ({β, u • β} : Set Ω)
    F = E ⊔ Subgroup.zpowers u ∧ Disjoint E (Subgroup.zpowers u) ∧
      ∀ e ∈ E, ∀ k ∈ Subgroup.zpowers u, Commute e k := by
  classical
  dsimp only
  let E := (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
    MulAction.stabilizer G (u • β)
  let F := MulAction.stabilizer G α ⊓
    MulAction.stabilizer G ({β, u • β} : Set Ω)
  have hpair := involution_exchanges_orbit_pair U β hfree hu huorder
  have hfinite : ({β, u • β} : Set Ω).Finite := (Set.finite_singleton _).insert _
  have hEF : E ≤ F := by
    rintro e ⟨⟨heα, heβ⟩, hethird⟩
    refine ⟨heα, (MulAction.mem_stabilizer_set' hfinite).mpr ?_⟩
    intro δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl
    · rw [MulAction.mem_stabilizer_iff.mp heβ]
      exact Set.mem_insert _ _
    · rw [MulAction.mem_stabilizer_iff.mp hethird]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have huF : u ∈ F := by
    refine ⟨hUα hu, (MulAction.mem_stabilizer_set' hfinite).mpr ?_⟩
    intro δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · rw [hpair.2]
      exact Set.mem_insert _ _
  have hKF : Subgroup.zpowers u ≤ F := Subgroup.zpowers_le.mpr huF
  have hcomm : ∀ e ∈ E, ∀ k ∈ Subgroup.zpowers u, Commute e k := by
    intro e he k hk
    have hecentral : e ∈ Subgroup.centralizer ({u} : Set G) := by
      change e ∈ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
        MulAction.stabilizer G (u • β) at he
      have he' := (triple_stabilizer_eq_centralizer U α β hnormal hfree hu) ▸ he
      exact he'.2
    rcases (mem_zpowers_involution_iff huorder).mp hk with rfl | rfl
    · exact Commute.one_right e
    · exact Subgroup.mem_centralizer_singleton_iff.mp hecentral
  refine ⟨?_, ?_, hcomm⟩
  · apply le_antisymm _ (sup_le hEF hKF)
    intro f hf
    have hβpair : f • β ∈ ({β, u • β} : Set Ω) :=
      (MulAction.mem_stabilizer_set' hfinite).mp hf.2 (Set.mem_insert _ _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβpair
    rcases hβpair with hfix | hswap
    · have hfixthird : f • (u • β) = u • β := by
        have hthirdpair : f • (u • β) ∈ ({β, u • β} : Set Ω) :=
          (MulAction.mem_stabilizer_set' hfinite).mp hf.2
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hthirdpair
        rcases hthirdpair with h | h
        · exact False.elim (hpair.1 (smul_left_cancel f (h.trans hfix.symm)))
        · exact h
      exact (show E ≤ E ⊔ Subgroup.zpowers u from le_sup_left)
        ⟨⟨hf.1, MulAction.mem_stabilizer_iff.mpr hfix⟩,
          MulAction.mem_stabilizer_iff.mpr hfixthird⟩
    · have hfuF : f * u ∈ F := F.mul_mem hf huF
      have hfuβ : (f * u) • β = β := by
        have hthirdpair : f • (u • β) ∈ ({β, u • β} : Set Ω) :=
          (MulAction.mem_stabilizer_set' hfinite).mp hf.2
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        rw [mul_smul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hthirdpair
        rcases hthirdpair with h | h
        · exact h
        · exact False.elim (hpair.1 (smul_left_cancel f (h.trans hswap.symm)))
      have hfuThird : (f * u) • (u • β) = u • β := by
        rw [mul_smul, hpair.2, hswap]
      have hfuE : f * u ∈ E :=
        ⟨⟨hfuF.1, MulAction.mem_stabilizer_iff.mpr hfuβ⟩,
          MulAction.mem_stabilizer_iff.mpr hfuThird⟩
      have hmul := (E ⊔ Subgroup.zpowers u).mul_mem
        ((show E ≤ E ⊔ Subgroup.zpowers u from le_sup_left) hfuE)
        ((show Subgroup.zpowers u ≤ E ⊔ Subgroup.zpowers u from le_sup_right)
          (Subgroup.mem_zpowers u))
      have hpow := pow_orderOf_eq_one u
      rw [huorder, pow_two] at hpow
      simpa only [mul_assoc, hpow, mul_one] using hmul
  · apply Subgroup.disjoint_def.mpr
    intro x hxE hxK
    rcases (mem_zpowers_involution_iff huorder).mp hxK with h | rfl
    · exact h
    · exact False.elim (hpair.1 (MulAction.mem_stabilizer_iff.mp hxE.1.2))

@[expose] def commutingJoinEquiv (E K : Subgroup G) (hdisj : Disjoint E K)
    (hcomm : ∀ e ∈ E, ∀ k ∈ K, Commute e k) : E × K ≃* (E ⊔ K : Subgroup G) := by
  have hcomm' : ∀ (e : E) (k : K), Commute (E.subtype e) (K.subtype k) :=
    fun e k => hcomm e e.property k k.property
  let f := E.subtype.noncommCoprod K.subtype hcomm'
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨E.subtype_injective, K.subtype_injective, by simpa only [Subgroup.range_subtype] using hdisj⟩
  have hrange : f.range = E ⊔ K := by
    exact (MonoidHom.noncommCoprod_range E.subtype K.subtype hcomm').trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)

theorem commutingJoinEquiv_apply (E K : Subgroup G) (hdisj : Disjoint E K)
    (hcomm : ∀ e ∈ E, ∀ k ∈ K, Commute e k) (e : E) (k : K) :
    (commutingJoinEquiv E K hdisj hcomm (e, k) : G) = (e : G) * k := rfl

@[expose] def orbitPairDirectProduct (U : Subgroup G) (α β : Ω)
    (hUα : U ≤ MulAction.stabilizer G α)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G}
    (hu : u ∈ U) (huorder : orderOf u = 2) :
    (((MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
      MulAction.stabilizer G (u • β)) : Subgroup G) × Subgroup.zpowers u ≃*
        (MulAction.stabilizer G α ⊓
          MulAction.stabilizer G ({β, u • β} : Set Ω) : Subgroup G) := by
  have h := pair_stabilizer_decomposition U α β hUα hnormal hfree hu huorder
  exact (commutingJoinEquiv _ _ h.2.1 h.2.2).trans (MulEquiv.subgroupCongr h.1.symm)

theorem orbitPairDirectProduct_apply (U : Subgroup G) (α β : Ω)
    (hUα : U ≤ MulAction.stabilizer G α)
    (hnormal : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ MulAction.stabilizer G β = ⊥) {u : G}
    (hu : u ∈ U) (huorder : orderOf u = 2)
    (e : ((MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
      MulAction.stabilizer G (u • β) : Subgroup G)) (k : Subgroup.zpowers u) :
    (orbitPairDirectProduct U α β hUα hnormal hfree hu huorder (e, k) : G) =
      (e : G) * k := rfl

section NormalizerCosets

variable [Finite G]

omit [Finite G] in
theorem normalizer_ne_top_of_not_normal (U : Subgroup G) (hUnormal : ¬ U.Normal) :
    Subgroup.normalizer (U : Set G) ≠ ⊤ :=
  fun h => hUnormal (Subgroup.normalizer_eq_top_iff.mp h)

omit [Finite G] in
theorem normalizerCoset_stabilizer (U : Subgroup G) (g : G) :
    MulAction.stabilizer G (g : G ⧸ Subgroup.normalizer (U : Set G)) =
      Subgroup.normalizer (U.map (MulAut.conj g).toMonoidHom : Set G) := by
  let H := Subgroup.normalizer (U : Set G)
  have hcoset : (g : G ⧸ H) = g • ((1 : G) : G ⧸ H) := by
    change (g : G ⧸ H) = ((g * 1 : G) : G ⧸ H)
    rw [mul_one]
  change MulAction.stabilizer G (g : G ⧸ H) = _
  rw [hcoset, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient]
  exact Subgroup.map_equiv_normalizer_eq U (MulAut.conj g)

theorem normalizerCoset_free (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (β : G ⧸ Subgroup.normalizer (U : Set G))
    (hβ : β ≠ ((1 : G) : G ⧸ Subgroup.normalizer (U : Set G))) :
    U ⊓ MulAction.stabilizer G β = ⊥ := by
  induction β using Quotient.inductionOn with
  | h g =>
    rw [normalizerCoset_stabilizer]
    apply inf_conjugate_normalizer_eq_bot T U hUT hUel hclosed hTI g
    intro hconj
    have hg : g ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
    apply hβ
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using (Subgroup.normalizer (U : Set G)).inv_mem hg

theorem normalizerCoset_triple_stabilizer (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (β : G ⧸ Subgroup.normalizer (U : Set G))
    (hβ : β ≠ ((1 : G) : G ⧸ Subgroup.normalizer (U : Set G)))
    {u : G} (hu : u ∈ U) :
    (Subgroup.normalizer (U : Set G) ⊓ MulAction.stabilizer G β) ⊓
        MulAction.stabilizer G (u • β) =
      (Subgroup.normalizer (U : Set G) ⊓ MulAction.stabilizer G β) ⊓
        Subgroup.centralizer ({u} : Set G) := by
  have hα := MulAction.stabilizer_quotient (Subgroup.normalizer (U : Set G))
  have hnormal : MulAction.stabilizer G
      (((1 : G) : G ⧸ Subgroup.normalizer (U : Set G))) ≤
        Subgroup.normalizer (U : Set G) := by rw [hα]
  have h := triple_stabilizer_eq_centralizer U
    (((1 : G) : G ⧸ Subgroup.normalizer (U : Set G))) β hnormal
    (normalizerCoset_free T U hUT hUel hclosed hTI β hβ) hu
  simpa only [hα] using h

theorem normalizerCoset_centralizes_subgroup (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (β : G ⧸ Subgroup.normalizer (U : Set G))
    (hβ : β ≠ ((1 : G) : G ⧸ Subgroup.normalizer (U : Set G)))
    {u : G} (hu : u ∈ U) (K : Subgroup G)
    (hK : K ≤ (Subgroup.normalizer (U : Set G) ⊓ MulAction.stabilizer G β) ⊓
      MulAction.stabilizer G (u • β)) :
    u ∈ Subgroup.centralizer (K : Set G) ∧ u ∈ Subgroup.normalizer (K : Set G) := by
  have hKC : K ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [normalizerCoset_triple_stabilizer T U hUT hUel hclosed hTI β hβ hu] at hK
    exact hK.trans inf_le_right
  have hcomm : u ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  exact ⟨hcomm, Subgroup.centralizer_le_normalizer _ hcomm⟩

end NormalizerCosets

end CFSG.ShultStronglyClosedTI
