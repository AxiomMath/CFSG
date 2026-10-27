module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirPos
public import CFSG.Quasithin.EmptyFaithful.SzC4ChirQ

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.FLc
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem chiC_X (A : ChiAPI) {L S : Subgroup G} {α : ↥L →* SLt 4} {Pbar Rbar : Subgroup (SLt 4)}
    {gb : SLt 4} (h : Hyp6 L S α Pbar) (hpb : (1 : SLt 4) ∈ Pbar) (hPD : ParabData Pbar Rbar gb)
    (hq : IsLnTwoQuot (perfectCore (PP L α Pbar)) 3)
    (hcase : MS93.IsC134Case4Corr (perfectCore (PP L α Pbar) ⊔ S) S (perfectCore (PP L α Pbar)))
    {g : G} (hgK : g ∈ perfectCore (PP L α Pbar)) (hgL : g ∈ L) (hg : α ⟨g, hgL⟩ = gb)
    (hg7 : g ^ 7 = 1) :
    chiC A (pCoreOf 2 L) g = - A.chi ↥Rbar (conjOn Rbar gb hPD.gb_normalizes) := by
  set P := PP L α Pbar with hP
  set K := perfectCore P with hK
  set X := pCoreOf 2 L with hX
  set Q := c134Q (K ⊔ S) K with hQ
  have hKP : K ≤ P := perfectCore_le P
  have hKL : K ≤ L := hKP.trans PP_le
  have hQle := Q_le h
  have hQL : Q ≤ L := fun q hq => (hQle hq).2
  have hQ2 : IsPGroup 2 ↥Q := (pCoreOf_isPGroup 2 (K ⊔ S)).to_le (fun q hq => (hQle hq).1)
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left hl)
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) :=
    SBd5.mem_normalizer_commutator_of (hKO hgK) (Subgroup.le_normalizer hgK)
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := le_normalizer_pCoreOf 2 L (hKL hgK)
  have hgQ0 : g ∈ Subgroup.normalizer ((Q ⊓ X : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgQ, hgX⟩
  have hQ0Q : Q ⊓ X ≤ Q := inf_le_left
  have hQ0X : Q ⊓ X ≤ X := inf_le_right
  have e0 : chiC A Q g = 0 := chiC_c134Q_eq_zero A hq hcase hQ2 hgK hg7
  have hαQ := alphaQ_le h hPD
  have hlift := exists_lift h hPD hgK hgL hg
  let π0 : ↥Q →* SLt 4 := α.comp (Subgroup.inclusion hQL)
  have hπ0 : ∀ q : ↥Q, π0 q ∈ Rbar := fun q => (hαQ q q.2).choose_spec
  let π : ↥Q →* ↥Rbar := π0.codRestrict Rbar hπ0
  have hπs : Function.Surjective π := by
    intro r
    obtain ⟨q, hqQ, hqL, hqr⟩ := hlift r r.2
    exact ⟨⟨q, hqQ⟩, Subtype.ext hqr⟩
  have hker : ∀ y : ↥Q, π y = 1 ↔ (y : G) ∈ Q ⊓ X := by
    intro y
    have h1 : π y = 1 ↔ α ⟨y, hQL y.2⟩ = 1 := by
      constructor
      · intro hy
        have := congrArg Subtype.val hy
        exact this
      · intro hy
        exact Subtype.ext hy
    rw [h1, alpha_eq_one_iff h.ker]
    exact ⟨fun hyX => ⟨y.2, hyX⟩, fun hy => hy.2⟩
  have hφ : ∀ y : ↥Q, π (conjOn Q g hgQ y) =
      conjOn Rbar gb hPD.gb_normalizes (π y) := by
    intro y
    apply Subtype.ext
    show α ⟨g * y * g⁻¹, _⟩ = gb * α ⟨y, hQL y.2⟩ * gb⁻¹
    rw [← hg]
    have : (⟨g * y * g⁻¹, _⟩ : ↥L) = ⟨g, hgL⟩ * ⟨y, hQL y.2⟩ * ⟨g, hgL⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have e1 := chiC_exact A hQ2 hQ0Q hgQ hgQ0 hg7 π hπs hker
    (conjOn Rbar gb hPD.gb_normalizes) hφ
  have hQnorm : ((Q ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    ·
      have hxH : (x : G) ∈ K ⊔ S := (X_le_PP h.ker hpb |>.trans h.PKS) x.2
      have hQN : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
        refine sup_le (fun k hk => ?_) (fun s hs => ?_)
        · exact SBd5.mem_normalizer_commutator_of (hKO hk) (Subgroup.le_normalizer hk)
        · have hSO : s ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) :=
            le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_right hs)
          have hSK : s ∈ Subgroup.normalizer (K : Set G) :=
            normalizer_le_normalizer_perfectCore P (h.SP hs)
          exact SBd5.mem_normalizer_commutator_of hSO hSK
      exact (Subgroup.mem_normalizer_iff.mp (hQN hxH) n).mp hn.1
    · exact X.mul_mem (X.mul_mem x.2 hn.2) (X.inv_mem x.2)
  let π' : ↥X →* ↥X ⧸ (Q ⊓ X).subgroupOf X := QuotientGroup.mk' ((Q ⊓ X).subgroupOf X)
  have hπ's : Function.Surjective π' := QuotientGroup.mk'_surjective _
  have hker' : ∀ y : ↥X, π' y = 1 ↔ (y : G) ∈ Q ⊓ X := by
    intro y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφ' : ∀ y : ↥X, π' (conjOn X g hgX y) = (1 : MulAut (↥X ⧸ (Q ⊓ X).subgroupOf X)) (π' y) := by
    intro y
    show π' (conjOn X g hgX y) = π' y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have := comm_X_K h hpb (x := (y : G)⁻¹) (k := g) (X.inv_mem y.2) hgK
    have e : ((conjOn X g hgX y)⁻¹ * y : ↥X) = ⟨g * (y : G)⁻¹ * g⁻¹ * ((y : G)⁻¹)⁻¹, by
      have h2 : g * (y : G)⁻¹ * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgX _).mp (X.inv_mem y.2)
      exact X.mul_mem h2 (by simp)⟩ := by
      apply Subtype.ext
      simp [conjOn_apply, mul_assoc]
    rw [e]
    exact this
  have e2 := chiC_exact A (pCoreOf_isPGroup 2 L) hQ0X hgX hgQ0 hg7 π' hπ's hker' 1 hφ'
  rw [A.chi_one] at e2
  linarith

end CFSG.Quasithin.SzC4
