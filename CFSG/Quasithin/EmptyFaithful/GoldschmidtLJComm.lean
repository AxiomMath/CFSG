module

public import CFSG.Quasithin.EmptyFaithful.S151S5B

public section

namespace CFSG.Quasithin.LJ

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem mem_of_perfect_central {P : Type*} [Group P] (hP : commutator P = ⊤) (N : Subgroup P)
    [N.Normal] (c : P → P) (hc : ∀ x y, c (x * y) = x * c y * x⁻¹ * c x)
    (hz : ∀ x, (QuotientGroup.mk (c x) : P ⧸ N) ∈ Subgroup.center (P ⧸ N)) :
    ∀ x, c x ∈ N := by
  have h1 : c 1 = 1 := by
    have := hc 1 1
    simp only [one_mul, mul_one, inv_one] at this
    exact (mul_eq_left.mp this.symm)
  let φ : P →* ↥(Subgroup.center (P ⧸ N)) :=
    { toFun := fun x => ⟨QuotientGroup.mk (c x), hz x⟩
      map_one' := by
        apply Subtype.ext
        simp [h1]
      map_mul' := fun x y => by
        apply Subtype.ext
        show (QuotientGroup.mk (c (x * y)) : P ⧸ N) =
          QuotientGroup.mk (c x) * QuotientGroup.mk (c y)
        rw [hc x y, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
        have := Subgroup.mem_center_iff.mp (hz y) (QuotientGroup.mk x)
        calc (QuotientGroup.mk x : P ⧸ N) * QuotientGroup.mk (c y) * (QuotientGroup.mk x)⁻¹ *
              QuotientGroup.mk (c x) = QuotientGroup.mk (c y) * QuotientGroup.mk (c x) := by
              rw [this]; group
          _ = _ := (Subgroup.mem_center_iff.mp (hz x) (QuotientGroup.mk (c y))) }
  have hker : commutator P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro x
  have hx : x ∈ φ.ker := hker (by rw [hP]; trivial)
  have h2 : (QuotientGroup.mk (c x) : P ⧸ N) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact (QuotientGroup.eq_one_iff (c x)).mp h2

variable {G : Type} [Group G] [Finite G]

theorem commutator_thompsonJ_eq_of_le_normalizer {S L M : Subgroup G}
    (hS : IsSylowTwoOf S (L ⊔ S)) (hsub : IsSubnormal L (L ⊔ S))
    (hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hNJ : Subgroup.normalizer (thompsonJ S : Set G) ≤ M) (hLM : ¬ L ≤ M) :
    ⁅L, thompsonJ S⁆ = L := by
  have hLX : L ≤ L ⊔ S := le_sup_left
  have hSX : S ≤ L ⊔ S := le_sup_right
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self151 S
  have hNL : ⁅L, thompsonJ S⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hJN
  by_cases hNP : ⁅L, thompsonJ S⁆ ≤ pCoreOf 2 L
  · exfalso
    have hXQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
      le_normalizer_pCoreOf 2 (L ⊔ S)
    have hPX : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := S151S5.pCoreOf_le_of_isSubnormal' hsub
    have hRS : pCoreOf 2 (L ⊔ S) ≤ S := pCoreOf_le_of_isSylowTwoOf hS
    have hQS : pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S ≤ S := sup_le hRS hJS
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S) := hS.2.1.to_le hQS
    have hJP : thompsonJ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
      hJS.trans (hSX.trans hXQ)
    have hQmem : ∀ x ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S,
        ∃ p ∈ pCoreOf 2 (L ⊔ S), ∃ j ∈ thompsonJ S, p * j = x := fun x hx => by
      have : x ∈ (pCoreOf 2 (L ⊔ S) : Set G) * (thompsonJ S : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 (L ⊔ S)) (thompsonJ S) hJP]
        exact hx
      obtain ⟨p, hp, j, hj, h⟩ := this
      exact ⟨p, hp, j, hj, h⟩
    have hLQ : ∀ l ∈ L, ∀ q ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S,
        l * q * l⁻¹ ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S := by
      intro l hl q hq
      obtain ⟨p, hp, j, hj, rfl⟩ := hQmem q hq
      have h1 : l * p * l⁻¹ ∈ pCoreOf 2 (L ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp (hXQ (hLX hl)) p).mp hp
      have h2 : ⁅l, j⁆ ∈ pCoreOf 2 (L ⊔ S) :=
        hPX (hNP (Subgroup.commutator_mem_commutator hl hj))
      have e : l * (p * j) * l⁻¹ = (l * p * l⁻¹) * ⁅l, j⁆ * j := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_right hj)
    have hSQ : ∀ s ∈ S, ∀ q ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S,
        s * q * s⁻¹ ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S := by
      intro s hs q hq
      obtain ⟨p, hp, j, hj, rfl⟩ := hQmem q hq
      have h1 : s * p * s⁻¹ ∈ pCoreOf 2 (L ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp (hXQ (hSX hs)) p).mp hp
      have h2 : s * j * s⁻¹ ∈ thompsonJ S :=
        (Subgroup.mem_normalizer_iff.mp
          (normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hs)) j).mp hj
      have e : s * (p * j) * s⁻¹ = (s * p * s⁻¹) * (s * j * s⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    have hQN : ∀ g : G, (g ∈ L ∨ g ∈ S) →
        g ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S : Subgroup G) : Set G) := by
      intro g hg
      have hgq : ∀ q ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S,
          g * q * g⁻¹ ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S := by
        rcases hg with hg | hg
        exacts [hLQ g hg, hSQ g hg]
      have hgq' : ∀ q ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S,
          g⁻¹ * q * g ∈ pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S := by
        rcases hg with hg | hg
        · simpa using hLQ g⁻¹ (L.inv_mem hg)
        · simpa using hSQ g⁻¹ (S.inv_mem hg)
      rw [Subgroup.mem_normalizer_iff]
      intro q
      exact ⟨fun hq => hgq q hq, fun hq => by simpa [mul_assoc] using hgq' _ hq⟩
    have hXN : L ⊔ S ≤ Subgroup.normalizer
        ((pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S : Subgroup G) : Set G) :=
      sup_le (fun g hg => hQN g (Or.inl hg)) (fun g hg => hQN g (Or.inr hg))
    have hQR : pCoreOf 2 (L ⊔ S) ⊔ thompsonJ S ≤ pCoreOf 2 (L ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 (hQS.trans hS.1) hXN hQ2
    have hJR : thompsonJ S ≤ pCoreOf 2 (L ⊔ S) := le_sup_right.trans hQR
    have hJeq : thompsonJ (pCoreOf 2 (L ⊔ S)) = thompsonJ S := B6.thompsonJ_eq_of_le hJR hRS
    have hXJ : L ⊔ S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
      rw [← hJeq]
      exact hXQ.trans (normalizer_le_normalizer_thompsonJ _)
    exact hLM ((hLX.trans hXJ).trans hNJ)
  · have hN' : (⁅L, thompsonJ S⁆.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr
        (Subgroup.normalizer_commutator_ge_left L (thompsonJ S))
    let Nbar : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (⁅L, thompsonJ S⁆.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    have hNbar : Nbar.Normal := Subgroup.Normal.map hN' _ (QuotientGroup.mk'_surjective _)
    have hmem : ∀ x (hx : x ∈ L) j (hj : j ∈ thompsonJ S),
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨⁅x, j⁆, hNL (Subgroup.commutator_mem_commutator
          hx hj)⟩ ∈ Nbar := fun x hx j hj =>
      ⟨⟨⁅x, j⁆, hNL (Subgroup.commutator_mem_commutator hx hj)⟩,
        Subgroup.commutator_mem_commutator hx hj, rfl⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNbar with h | h
    · have hall : ∀ x : ↥L, ∃ n ∈ ⁅L, thompsonJ S⁆.subgroupOf L, ∃ p ∈ CFSG.pCore 2 ↥L,
          x = n * p := by
        intro x
        have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Nbar := by rw [h]; trivial
        obtain ⟨n, hn, hnx⟩ := hx
        refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
        exact QuotientGroup.eq.1 hnx
      have hpg : IsPGroup 2 (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H x =>
          obtain ⟨n, hn, p, hp, rfl⟩ := hall x
          obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨p, hp⟩
          refine ⟨k, ?_⟩
          have hp1 : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
          have hn1 : (QuotientGroup.mk n : ↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) = 1 :=
            (QuotientGroup.eq_one_iff n).2 hn
          rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hp1]
          rfl
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := hpg.isNilpotent
      have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
      have hperfQ : Group.IsPerfect (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      have hsub : Subsingleton (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := by
        by_contra hns
        rw [not_subsingleton_iff_nontrivial] at hns
        exact Group.IsPerfect.not_isSolvable (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L)
          (inferInstance : Group.IsSolvable _)
      have hidx : (⁅L, thompsonJ S⁆.subgroupOf L).index = 1 := by
        rw [Subgroup.index]
        exact Nat.card_of_subsingleton (1 : ↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L)
      have htop : ⁅L, thompsonJ S⁆.subgroupOf L = ⊤ := Subgroup.index_eq_one.1 hidx
      exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 htop)
    · exfalso
      apply hNP
      rw [Subgroup.commutator_le]
      intro x hx j hj
      have hperfL : commutator ↥L = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.2 hperf)
      have key := mem_of_perfect_central hperfL (CFSG.pCore 2 ↥L)
        (fun y : ↥L => (⟨⁅(y : G), j⁆, hNL (Subgroup.commutator_mem_commutator y.2 hj)⟩ : ↥L))
        (fun y z => by
          apply Subtype.ext
          show ⁅((y * z : ↥L) : G), j⁆ = (y : G) * ⁅(z : G), j⁆ * (y : G)⁻¹ * ⁅(y : G), j⁆
          simp only [commutatorElement_def, Subgroup.coe_mul]
          group)
        (fun y => h (hmem y y.2 j hj)) ⟨x, hx⟩
      exact ⟨⟨⁅x, j⁆, hNL (Subgroup.commutator_mem_commutator hx hj)⟩,
        by exact key, rfl⟩

end CFSG.Quasithin.LJ
