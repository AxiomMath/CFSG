module

public import CFSG.Quasithin.EmptyFaithful.S146G2
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146G1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsRedCE.le_oTwoPIn {T M H PQ : Subgroup G} {p : ℕ} (h : IsRedCE T M H PQ p) :
    PQ ≤ oTwoPIn p H := by
  classical
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  have hPQH : PQ ≤ H := h.le
  have hWn : ((PQ.subgroupOf H).map π).Normal :=
    Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hPQH).mpr h.normal) π
      (QuotientGroup.mk'_surjective _)
  have hWp : IsPGroup p ↥((PQ.subgroupOf H).map π) := by
    intro w
    obtain ⟨z, hz, hzw⟩ := w.2
    obtain ⟨k, hk⟩ := h.pSec (z : G) (Subgroup.mem_subgroupOf.mp hz)
    refine ⟨k, Subtype.ext ?_⟩
    obtain ⟨y, hy, hyz⟩ := hk
    have hyz' : y = z ^ p ^ k := Subtype.ext hyz
    have h1 : π (z ^ p ^ k) = 1 := (QuotientGroup.eq_one_iff _).mpr (hyz' ▸ hy)
    show (w : OTwoQuot H) ^ p ^ k = 1
    rw [← hzw, ← map_pow]
    exact h1
  have hWle : (PQ.subgroupOf H).map π ≤ CFSG.pCore p (OTwoQuot H) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hWn hWp
  intro x hx
  exact mem_oTwoPIn_of_mem_pCore (hPQH hx)
    (hWle (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)))

omit [Finite G] in
theorem IsRedCE.oTwoUpper_le_pq {T M H PQ : Subgroup G} {p : ℕ} (h : IsRedCE T M H PQ p)
    (hT2 : IsPGroup 2 T) : oTwoUpper H ≤ PQ := by
  have hTH : T ≤ H := h.isHTM.1.1
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  rw [h.eq] at hx
  exact exists_pow_mem_of_mem_sup_two hT2 (hTH.trans h.normal) hx

theorem stage14611H2_of (h2 : Stage1461Two) : Stage14611H2 := by
  intro G _ _ T M S H PQ p hred hmax hp3 H₀ H₁ H₂ t hdec u hu1 huZ hT₀u
  subst hp3
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hT₀H₀ : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ H₀ := hdec.inf_normalizer_le hTH
  refine ⟨?_, ?_, ?_⟩
  ·
    refine sup_le (fun h hh => ?_) (hT₀u.trans (centralizerMod_mono_left _ hTH))
    refine ⟨hH₂H hh, S.normalizer_Z.ge (S.le_mcOf hH (hH₂H hh)), fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwu : u ^ k ∈ uHi T M H H₁ := Subgroup.zpow_mem _ hu1 k
    have h3 := (quasithinOmegaOneCenter T).inv_mem
      (hdec.cent₁ (Subgroup.commutator_mem_commutator hwu hh))
    rw [commutatorElement_inv] at h3
    simpa [commutatorElement_def] using h3
  ·
    exact oTwoQuot_sup_equiv_perm hdec.H₂_le_normalizer_H₁ inf_le_right
      (hT₀H₀.trans hdec.H₀_le_normalizer_H₂) (hT2.to_le inf_le_left)
      (hdec.sup ▸ hT₀H₀) hdec.inf (pCoreOf_isPGroup 2 H) hdec.dihedral₂
  ·
    intro hXM
    have hH₂M : H₂ ≤ M := le_sup_left.trans hXM
    obtain ⟨hQn, ⟨e₂⟩⟩ := hdec.dihedral₂
    have hord : orderOf (e₂.symm (DihedralGroup.r 1)) = 3 := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e₂.symm (DihedralGroup.r 1))
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H₂ y.2
    have hzH₂ : (y : G) ^ 2 ^ k ∈ H₂ := H₂.pow_mem y.2 _
    have hzPQ : (y : G) ^ 2 ^ k ∈ PQ :=
      ((oTwoUpper_mono hH₂H).trans (hred.oTwoUpper_le_pq hT2)) hk
    have hzQ : (y : G) ^ 2 ^ k ∈ pCoreOf 2 H := by
      rw [← h2 G T M S H hH 3 hred.prime hred.odd]
      exact ⟨hred.le_oTwoPIn hzPQ, hH₂M hzH₂⟩
    have hone : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzH₂⟩ : ↥H₂) : ↥H₂ ⧸ _) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
    have hpow : (e₂.symm (DihedralGroup.r 1)) ^ 2 ^ k = 1 := by
      rw [← hy, ← QuotientGroup.mk_pow]
      exact hone
    have hdvd : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hpow
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega

end CFSG.Quasithin
