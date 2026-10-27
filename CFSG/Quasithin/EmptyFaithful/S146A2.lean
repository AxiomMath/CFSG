module

public import CFSG.Quasithin.EmptyFaithful.S146A1
public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146Main
public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_sup_eq_oTwoUpper {A B : Subgroup G} (hB : IsPGroup 2 B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : oTwoUpper (A ⊔ B) = oTwoUpper A := by
  refine le_antisymm ?_ (oTwoUpper_mono le_sup_left)
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBA] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hBA hb) (2 ^ j)
  obtain ⟨i, hi⟩ := exists_pow_mem_oTwoUpper A hy'
  refine ⟨j + i, ?_⟩
  rw [pow_add, pow_mul, hpow, hj', mul_one]
  exact hi

omit [Finite G] in
theorem mul_inv_mem_of_relIndex_two {H₀ H : Subgroup G} (h : H₀.relIndex H = 2) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hx0 : x ∉ H₀) (hy0 : y ∉ H₀) : x * y⁻¹ ∈ H₀ := by
  have h2 : (H₀.subgroupOf H).index = 2 := h
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h2
  have key : ∀ z : H, (z : G) ∉ H₀ → z * c ∈ H₀.subgroupOf H := by
    intro z hz
    rcases hc z with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hz
  have h1 := key ⟨x, hx⟩ hx0
  have h2 := key ⟨y, hy⟩ hy0
  have h3 := (H₀.subgroupOf H).mul_mem h1 ((H₀.subgroupOf H).inv_mem h2)
  have e : (⟨x, hx⟩ * c) * (⟨y, hy⟩ * c)⁻¹ = (⟨x, hx⟩ * ⟨y, hy⟩⁻¹ : H) := by group
  rw [e] at h3
  exact Subgroup.mem_subgroupOf.mp h3

omit [Finite G] in
theorem S146A.le_normalizer_of_forall_conj_mem {L K : Subgroup G}
    (h : ∀ g ∈ L, ∀ x ∈ K, g * x * g⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (L.inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem S146A.le_normalizer_of_commutator_le {A B Q : Subgroup G} (hQA : Q ≤ A) (h : ⁅A, B⁆ ≤ Q) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  refine S146A.le_normalizer_of_forall_conj_mem fun b hb x hx => ?_
  have hc : b * x * b⁻¹ = ⁅b, x⁆ * x := by simp only [commutatorElement_def]; group
  have h1 : ⁅x, b⁆ ∈ Q := h (Subgroup.commutator_mem_commutator hx hb)
  have h2 : ⁅b, x⁆ ∈ A := hQA (by
    have := Q.inv_mem h1
    rwa [commutatorElement_inv] at this)
  rw [hc]
  exact A.mul_mem h2 hx

namespace IsDec12

variable {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G]

theorem H₂_le_normalizer_H₁ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₂ ≤ Subgroup.normalizer (H₁ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₁ h.comm

theorem H₁_le_normalizer_H₂ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₂ (by rw [Subgroup.commutator_comm]; exact h.comm)

theorem H₀_le_normalizer_H₁ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₁ : Set G) := by
  rw [h.sup]
  exact sup_le Subgroup.le_normalizer h.H₂_le_normalizer_H₁

theorem H₀_le_normalizer_H₂ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₂ : Set G) := by
  rw [h.sup]
  exact sup_le h.H₁_le_normalizer_H₂ Subgroup.le_normalizer

theorem conjSub_eq_of_not_mem (h : IsDec12 T M H p H₀ H₁ H₂ t) (htH : t ∈ H) {s : G} (hsH : s ∈ H)
    (hs : s ∉ H₀) : conjSub s H₁ = H₂ := by
  have htH₀ : t ∉ H₀ := fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0)
  have hst : s * t⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index hsH htH hs htH₀
  have e : s = (s * t⁻¹) * t := by group
  rw [e, conjSub_mul, ← h.conj]
  exact conjSub_eq_of_mem_normalizer (h.H₀_le_normalizer_H₂ hst)

theorem inf_normalizer_le (h : IsDec12 T M H p H₀ H₁ H₂ t) (hTH : T ≤ H) :
    T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ H₀ := by
  intro s hs
  by_contra hs0
  have hsconj := h.conjSub_eq_of_not_mem (hTH h.t_mem) (hTH hs.1) hs0
  have h1 : conjSub s H₁ = H₁ := conjSub_eq_of_mem_normalizer hs.2
  have h2 : conjSub t H₁ = H₁ := by rw [← h.conj, ← hsconj, h1]
  exact h.t_not (CosetGeom.mem_normalizer_of_conjSub_eq h2)

end IsDec12

end Aux

section Closing

variable {G : Type} [Group G] [Finite G]

@[expose] def Stage14611H2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∀ u : G, u ∈ uHi T M H H₁ → u ∉ quasithinOmegaOneCenter T →
          T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u →
          H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G)) ≤
              centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
            Nonempty (OTwoQuot (H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G))) ≃*
              Equiv.Perm (Fin 3)) ∧
            ¬ H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G)) ≤ M

theorem stage146BranchACore_of_parts (h4 : Stage1461Four) (h12 : Stage14612) (h15 : Stage14615)
    (h17 : Stage14617) (hrank : Stage14611Rank) (hH2 : Stage14611H2) : Stage146BranchACore := by
  intro G _ _ T M S hex
  obtain ⟨H, PQ, p, hred, hmax⟩ := exists_redCE h4 S hex
  have hp3 : p = 3 := h15 G T M S H PQ p hred hmax
  obtain ⟨-, ⟨H₀, H₁, H₂, t, hdec⟩, hZ⟩ := h12 G T M S H PQ p hred
  obtain ⟨hOF, h17'⟩ := h17 G T M S H PQ p hred hmax
  obtain ⟨-, h3, h4', h5⟩ := h17' H₀ H₁ H₂ t hdec
  have hZ' := hZ H₀ H₁ H₂ t hdec
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.conjClosure_Vp_le_pCoreOf
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hUH₁ : conjClosure (VZ T M) H ≤ H₁ := hUQ.trans hdec.Q₁
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    (le_conjClosure _ _ : quasithinOmegaOneCenter T ≤ VZ T M).trans (le_conjClosure _ _)
  have huHi_le : uHi T M H H₁ ≤ conjClosure (VZ T M) H :=
    sup_le (S145.commutator_le_of_le_normalizer (hH₁H.trans hHU)) hZU
  set T₀ : Subgroup G := T ⊓ Subgroup.normalizer (H₁ : Set G) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le inf_le_left
  have hT₀N₁ : T₀ ≤ Subgroup.normalizer (H₁ : Set G) := inf_le_right
  have hT₀NU : T₀ ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    (inf_le_left.trans hTH).trans hHU
  have hT₀NZ : T₀ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hx.1)
  have hT₀Nuhi : T₀ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) :=
    (le_inf (S145.le_normalizer_commutator hT₀NU hT₀N₁) hT₀NZ).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have huhiT₀ : uHi T M H H₁ ≤ T₀ :=
    le_inf ((huHi_le.trans hUQ).trans hQT) ((huHi_le.trans hUH₁).trans Subgroup.le_normalizer)
  have hlt : quasithinOmegaOneCenter T < uHi T M H H₁ := by
    refine lt_of_le_of_ne le_sup_right fun heq => ?_
    have hr := hdec.rank₁.2 hp3
    have h0 : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 0 := by
      rw [← heq]
      simp [mIdx]
    omega
  obtain ⟨u, hu1, huZ, hu⟩ := exists_fixed_mod hT₀2 huhiT₀ hlt hT₀Nuhi hT₀NZ
  have huU : u ∈ conjClosure (VZ T M) H := huHi_le hu1
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH huU
  have huT₀ : T₀ ≤ tZero T u := fun x hx =>
    (S146T.mem_tZero_iff huG).mpr ⟨hx.1, hu x hx⟩
  have huK : u ∈ uK T M H :=
    ((sup_le (Subgroup.commutator_mono le_rfl hH₁H)
      (hZ'.1.trans (Subgroup.commutator_mono le_rfl ((oTwoUpper_le H₁).trans hH₁H))) :
        uHi T M H H₁ ≤ uK T M H)) hu1
  have hInv := h3 u huK (Or.inl hu1) huZ huT₀
  have hI := h4' u huK (Or.inl hu1) huZ huT₀
  obtain ⟨hr4, hr5⟩ := hrank G T M S H PQ p hred hmax hOF
  obtain ⟨hH₂C, hH₂S3, hH₂M⟩ := hH2 G T M S H PQ p hred hmax hp3 H₀ H₁ H₂ t hdec u hu1 huZ huT₀
  have hE5 : tZero T u ≤ T₀ := by
    intro s hs
    have hsT : s ∈ T := S146T.tZero_le T u hs
    refine ⟨hsT, ?_⟩
    by_contra hsN
    have hs0 : s ∉ H₀ := fun h0 => hsN (hdec.H₀_le_normalizer_H₁ h0)
    have hsconj : conjSub s H₁ = H₂ := hdec.conjSub_eq_of_not_mem (hTH hdec.t_mem) (hTH hsT) hs0
    have hsZ : s ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hsT)
    have hconjU : conjSub s (uHi T M H H₁) = uHi T M H H₂ := by
      unfold uHi
      have e1 : conjSub s ⁅conjClosure (VZ T M) H, H₁⁆ =
          ⁅conjSub s (conjClosure (VZ T M) H), conjSub s H₁⁆ := (conjSub_commutator s _ _).symm
      have e2 : conjSub s (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
        conjSub_eq_of_mem_normalizer (hHU (hTH hsT))
      have e3 : conjSub s (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
        conjSub_eq_of_mem_normalizer hsZ
      rw [show conjSub s (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T) =
          conjSub s ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ conjSub s (quasithinOmegaOneCenter T) from
          Subgroup.map_sup _ _ _, e1, e2, e3, hsconj]
    have h1 : s * u * s⁻¹ ∈ uHi T M H H₂ := by
      have hmem : s * u * s⁻¹ ∈ conjSub s (uHi T M H H₁) :=
        mem_conjSub.mpr (by simpa [mul_assoc] using hu1)
      rwa [hconjU] at hmem
    have hcomm : ⁅s, u⁆ ∈ quasithinOmegaOneCenter T := ((S146T.mem_tZero_iff huG).mp hs).2
    have h2 : s * u * s⁻¹ ∈ uHi T M H H₁ := by
      have e : s * u * s⁻¹ = ⁅s, u⁆ * u := by simp only [commutatorElement_def]; group
      rw [e]
      exact (uHi T M H H₁).mul_mem (Subgroup.mem_sup_right hcomm) hu1
    have h3 : s * u * s⁻¹ ∈ quasithinOmegaOneCenter T := by
      rw [← hdec.dir_inf]
      exact ⟨h2, h1⟩
    apply huZ
    have hz : s⁻¹ * (s * u * s⁻¹) = (s * u * s⁻¹) * s⁻¹ := S146T.comm_Z_T (T.inv_mem hsT) h3
    have e : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [e, hz]
    simpa using h3
  refine ⟨H, u, H₂ ⊔ T₀, hH, hInv, hI, hr4, hr5.ge, ?_, hH₂C, hH₂S3, hH₂M, ?_⟩
  · exact hE5.trans le_sup_right
  · have hT₀H₂ : T₀ ≤ Subgroup.normalizer (H₂ : Set G) :=
      (hdec.inf_normalizer_le hTH).trans hdec.H₀_le_normalizer_H₂
    rw [oTwoUpper_sup_eq_oTwoUpper hT₀2 hT₀H₂]
    exact h5

end Closing

end CFSG.Quasithin
