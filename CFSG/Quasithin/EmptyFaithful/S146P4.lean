module

public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.S146P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_conjSub_P (g : G) (X : Subgroup G) :
    oTwoUpper (conjSub g X) = conjSub g (oTwoUpper X) :=
  oTwoUpper_map (MulAut.conj g).toMonoidHom X

theorem normalizer_le_normalizer_oTwoUpper_P {X : Subgroup G} :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoUpper X : Set G) := by
  intro x hx
  have h1 : conjSub x (oTwoUpper X) = oTwoUpper X := by
    rw [← oTwoUpper_conjSub_P, conjSub_eq_of_mem_normalizer hx]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

omit [Finite G] in
theorem mem_normalizer_sup_P {X Y : Subgroup G} {x : G} (hX : x ∈ Subgroup.normalizer (X : Set G))
    (hY : x ∈ Subgroup.normalizer (Y : Set G)) : x ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have h1 : conjSub x (X ⊔ Y) = X ⊔ Y := by
    rw [show conjSub x (X ⊔ Y) = conjSub x X ⊔ conjSub x Y from Subgroup.map_sup _ _ _,
      conjSub_eq_of_mem_normalizer hX, conjSub_eq_of_mem_normalizer hY]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

omit [Finite G] in
theorem oTwoUpper_idem_P (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_odd_notin (hp : p.Prime) (hp2 : p ≠ 2) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ z ∈ H₁, z ∉ pCoreOf 2 H ∧ Odd (orderOf z) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  have hord : orderOf (e.symm (DihedralGroup.r 1)) = p := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm (DihedralGroup.r 1))
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow (y : G)
  have hzH₁ : (y : G) ^ 2 ^ k ∈ H₁ := H₁.pow_mem y.2 _
  have hmk : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzH₁⟩ : ↥H₁) :
      ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = (e.symm (DihedralGroup.r 1)) ^ 2 ^ k := by
    rw [← hy, ← QuotientGroup.mk_pow]
    rfl
  refine ⟨(y : G) ^ 2 ^ k, hzH₁, ?_, hk⟩
  intro hzQ
  have hone : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzH₁⟩ : ↥H₁) :
      ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
  rw [hmk] at hone
  have hdvd : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hone
  have := Nat.Prime.dvd_of_dvd_pow hp hdvd
  have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
  exact hp2 h2

theorem IsDecP.oTwoUpper_eq (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hAH : oTwoUpper H₁ ⊔ oTwoUpper H₂ ≤ H :=
    sup_le ((oTwoUpper_le _).trans hH₁H) ((oTwoUpper_le _).trans hH₂H)
  have hH₀A : H₀ ≤ Subgroup.normalizer ((oTwoUpper H₁ ⊔ oTwoUpper H₂ : Subgroup G) : Set G) := by
    rw [h.sup]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact mem_normalizer_sup_P (normalizer_le_normalizer_oTwoUpper_P (Subgroup.le_normalizer hx))
        (normalizer_le_normalizer_oTwoUpper_P (h.H₁_le_normalizer_H₂ hx))
    · exact mem_normalizer_sup_P (normalizer_le_normalizer_oTwoUpper_P (h.H₂_le_normalizer_H₁ hx))
        (normalizer_le_normalizer_oTwoUpper_P (Subgroup.le_normalizer hx))
  have hTA : T ≤ Subgroup.normalizer ((oTwoUpper H₁ ⊔ oTwoUpper H₂ : Subgroup G) : Set G) := by
    intro s hsT
    by_cases hs : s ∈ Subgroup.normalizer (H₁ : Set G)
    · have hs2 : s ∈ Subgroup.normalizer (H₂ : Set G) := by
        have : s ∈ T ⊓ Subgroup.normalizer (H₂ : Set G) := by
          rw [h.inf_normalizer_swap_eq]
          exact ⟨hsT, hs⟩
        exact this.2
      exact mem_normalizer_sup_P (normalizer_le_normalizer_oTwoUpper_P hs)
        (normalizer_le_normalizer_oTwoUpper_P hs2)
    · have hs2 : s ∉ Subgroup.normalizer (H₂ : Set G) := by
        intro hs2
        apply hs
        have : s ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
          rw [← h.inf_normalizer_swap_eq]
          exact ⟨hsT, hs2⟩
        exact this.2
      have e1 : conjSub s H₁ = H₂ := h.conjSub_eq_of_not_mem hsT hs
      have e2 : conjSub s H₂ = H₁ := h.swap.conjSub_eq_of_not_mem hsT hs2
      have h1 : conjSub s (oTwoUpper H₁ ⊔ oTwoUpper H₂) = oTwoUpper H₁ ⊔ oTwoUpper H₂ := by
        rw [show conjSub s (oTwoUpper H₁ ⊔ oTwoUpper H₂) =
            conjSub s (oTwoUpper H₁) ⊔ conjSub s (oTwoUpper H₂) from Subgroup.map_sup _ _ _,
          ← oTwoUpper_conjSub_P, ← oTwoUpper_conjSub_P, e1, e2, sup_comm]
      exact CosetGeom.mem_normalizer_of_conjSub_eq h1
  have hHA : H ≤ Subgroup.normalizer ((oTwoUpper H₁ ⊔ oTwoUpper H₂ : Subgroup G) : Set G) := by
    rw [h.eq]
    exact sup_le hH₀A hTA
  obtain ⟨hS₁, -, -⟩ := h.isSylowTwoOf_inf_H₁ S hred
  obtain ⟨hS₂, -, -⟩ := h.swap.isSylowTwoOf_inf_H₁ S hred
  have e₁ : oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁) = H₁ := C1Pack12.oTwoUpper_sup_eq_of_sylow hS₁
  have e₂ : oTwoUpper H₂ ⊔ ((T ⊓ H₀) ⊓ H₂) = H₂ := C1Pack12.oTwoUpper_sup_eq_of_sylow hS₂
  have hH₁AT : H₁ ≤ (oTwoUpper H₁ ⊔ oTwoUpper H₂) ⊔ T := by
    calc H₁ = oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁) := e₁.symm
      _ ≤ (oTwoUpper H₁ ⊔ oTwoUpper H₂) ⊔ T :=
        sup_le_sup le_sup_left (inf_le_left.trans inf_le_left)
  have hH₂AT : H₂ ≤ (oTwoUpper H₁ ⊔ oTwoUpper H₂) ⊔ T := by
    calc H₂ = oTwoUpper H₂ ⊔ ((T ⊓ H₀) ⊓ H₂) := e₂.symm
      _ ≤ (oTwoUpper H₁ ⊔ oTwoUpper H₂) ⊔ T :=
        sup_le_sup le_sup_right (inf_le_left.trans inf_le_left)
  have hHAT : H ≤ (oTwoUpper H₁ ⊔ oTwoUpper H₂) ⊔ T := by
    rw [h.eq, h.sup]
    exact sup_le (sup_le hH₁AT hH₂AT) le_sup_right
  refine le_antisymm ?_ (sup_le (oTwoUpper_mono hH₁H) (oTwoUpper_mono hH₂H))
  exact Der6A.oTwoUpper_le_of_normal_sup hAH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mpr hHA) hTsyl.isPGroup hTH hHAT

theorem IsDecP.setup14615_of_C1 (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (hC1 : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) :
    Setup14615 T M H H₁ H₂ (oTwoUpper H₁) (oTwoUpper H₂) t where
  kz := by rw [hC1]; exact h.oTwoUpper_eq S hred
  s_mem := h.t_mem
  s_not := by
    intro hN
    have h1 : conjSub t (oTwoUpper H₁) = oTwoUpper H₁ := conjSub_eq_of_mem_normalizer hN
    have h2 : oTwoUpper H₂ = oTwoUpper H₁ := by
      rw [← h1, ← oTwoUpper_conjSub_P, ← h.conj]
    obtain ⟨z, hz1, hzQ, hzodd⟩ := h.exists_odd_notin hred.prime hred.odd
    have hz : z ∈ oTwoUpper H₁ := mem_oTwoUpper_of_odd hz1 hzodd
    have hz2 : z ∈ H₂ := (oTwoUpper_le H₂) (h2 ▸ hz)
    exact hzQ (by rw [← h.inf]; exact ⟨hz1, hz2⟩)
  conj := by rw [← oTwoUpper_conjSub_P, ← h.conj]
  oTwo₁ := le_rfl
  oTwo₂ := le_rfl
  cent := (Subgroup.commutator_mono le_rfl (oTwoUpper_le H₂)).trans h.cent₁
  perf₂ := oTwoUpper_idem_P H₂
  shape := Or.inr ⟨rfl, rfl⟩

end Main

@[expose] def Input14615SetupFourP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        Stage14614C4 T H p →
          ∃ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s

theorem input14615SetupP_of_four (iF : Input14615SetupFourP) : Input14615SetupP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx
  rcases hctx.2.2 with hC1 | hC4
  · exact ⟨_, _, t, hdec.setup14615_of_C1 S hred hC1.1⟩
  · exact iF G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx hC4

end CFSG.Quasithin
