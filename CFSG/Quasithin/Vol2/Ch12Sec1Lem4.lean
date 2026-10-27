module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Lem1214Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → n = 4 → T ≤ Subgroup.normalizer (L : Set G) → ∀ v : G,
      V₁ ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v →
        ∀ T₀ : Subgroup G, quasithinIsSylowTwo T₀ → T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ T₀ →
          T₀ ≤ Subgroup.centralizer ({v} : Set G) →
          T₀ ≤ Subgroup.normalizer
            ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) →
          ¬ T₀ ≤ Subgroup.normalizer (L : Set G) → False

open Sec1215 in
theorem lem1214_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hStep : Lem1214Step) : Lem1214 := by
  intro G _ _ T L V V₁ V₂ n hyp hn v hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  have hvmem : v ∈ V₁ ⊓ Subgroup.centralizer (T₁ : Set G) := hv ▸ Subgroup.mem_zpowers v
  have hv1 : v ≠ 1 := by
    intro h1
    apply inf_centralizer_ne_bot hyp hTL
    rw [hv, h1, Subgroup.zpowers_one_eq_bot]
  have hT₁v : T₁ ≤ Subgroup.centralizer ({v} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hvmem.2 t ht
  obtain ⟨hcardT, hSylT₁⟩ := isSylowTwoOf_inf_normalizer hyp hTL
  have hSylM : IsSylowTwoOf T₁
      (Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_le_of_le hSylT₁ (le_inf hT₁v (inf_le_left.trans hTL))
      (fun m hm => ⟨hm.2, mem_normalizer_of_mem_centralizer hyp hvmem.1 hv1 hm.2 hm.1⟩)
  rw [A4.isSylowTwoOf_iff_maximal] at hSylM ⊢
  refine ⟨hT₁v, hSylM.2.1, fun P hPK hP hT₁P => ?_⟩
  by_contra hne
  set T₀ := P ⊓ Subgroup.normalizer (T₁ : Set G) with hT₀
  have hT₁T₀ : T₁ ≤ T₀ := le_inf hT₁P Subgroup.le_normalizer
  have hlt : T₁ < T₀ := by
    refine lt_of_le_of_ne hT₁T₀ fun heq => hne ?_
    have hlt' : T₁.subgroupOf P < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne ?_
      intro x hx
      have : (⟨x, hx⟩ : P) ∈ T₁.subgroupOf P := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have : Group.IsNilpotent P := hP.isNilpotent
    have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
    obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt')
    have hxNorm : (x : G) ∈ Subgroup.normalizer (T₁ : Set G) := by
      have hxsub : x ∈ (Subgroup.normalizer (T₁ : Set G)).subgroupOf P := by
        rw [Subgroup.subgroupOf_normalizer_eq hT₁P]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hxsub
    exact absurd (Subgroup.mem_subgroupOf.mpr (heq ▸ (⟨x.2, hxNorm⟩ : (x : G) ∈ T₀))) hxnot
  have hT₀2 : IsPGroup 2 ↥T₀ := hP.to_le inf_le_left
  have hcard₁ : 2 * Nat.card T₁ ≤ Nat.card T₀ := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hT₁T₀
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hT₁T₀ hm.le)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    rw [hm, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have hTsyl := hyp.sylow
  let S : Sylow 2 G := hTsyl.1.toSylow hTsyl.2
  obtain ⟨Q, hQ⟩ := hT₀2.exists_le_sylow
  have hQT : Nat.card Q = Nat.card T := by
    have e1 := Sylow.card_eq_multiplicity Q
    have e2 := Sylow.card_eq_multiplicity S
    exact e1.trans e2.symm
  have hT₀T : Nat.card T₀ = Nat.card T :=
    le_antisymm ((Subgroup.card_le_of_le hQ).trans hQT.le) (hcardT ▸ hcard₁)
  have hSylT₀ : quasithinIsSylowTwo T₀ := by
    refine ⟨hT₀2, fun h2 => hTsyl.2 ?_⟩
    have e1 := T₀.card_mul_index
    have e2 := T.card_mul_index
    rw [hT₀T] at e1
    have e3 : T₀.index = T.index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.trans e2.symm)
    rwa [← e3]
  refine hStep G T L V V₁ V₂ n hyp hn hTL v hv T₀ hSylT₀ hT₁T₀ (inf_le_left.trans hPK)
    inf_le_right fun hT₀M => ?_
  exact hlt.ne (le_antisymm hT₁T₀
    (hSylM.2.2 T₀ (le_inf (inf_le_left.trans hPK) hT₀M) hT₀2 hT₁T₀))

end CFSG.Quasithin.H13
