module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Tr
public import CFSG.Quasithin.EmptyFaithful.T1521SL2Aut
public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.A5S5
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G]

private theorem center_sl2_eq_bot_of_charTwo {K : Type} [Field K] [CharP K 2] :
    Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hchar
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  subst h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz]
  simp

private noncomputable def pslEquivSl2 (K : Type) [Field K] [CharP K 2] :
    PSL(2, K) ≃* SL(2, K) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot_of_charTwo).trans QuotientGroup.quotientBot

theorem nonempty_equiv_alt5_of_isPSL_two_two_two {X : Type} [Group X] (h : IsPSL 2 2 2 X) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by simpa using hK
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hSL : Nat.card SL(2, K) = 60 := by
    rw [CFSG.Quasithin.SL2Model.card_SL2, hK4]
    norm_num
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 K hK4 hSL
  exact ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
    ((pslEquivSl2 K).trans e5)⟩

variable [Finite G]

theorem nrm1521_of_psl2_borel {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hB : oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (thompsonJ S : Set G)) : Nrm1521 S L :=
  ⟨oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)),
    (oTwoUpper_le _).trans le_conjJoin, hB, oTwoUpper_oTwoUpper1521 _,
    fun _ _ hvN hc l hl => L21521.centralizes_of_centralizes_borel_psl2 hn hL hsyl hvN hc l hl⟩

theorem centralizes_two_of_thompsonJ_le {X S L Y : Subgroup G} {p : ℕ} (hStd : Std1521 X S L)
    (hL : IsPSL 2 2 2 ↥L) (hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ thompsonJ S ≤ innerPart1521 S L) (hp : p = 3 ∨ p = 5)
    (hYJ : Y ≤ Subgroup.normalizer (thompsonJ S : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hY : IsPGroup p Y) : ⁅L, Y⁆ = ⊥ := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isPSL_two_two_two hL
  set ρ := CFSG.OddStandard.rhoOf e with hρ
  have hker : ∀ y : ↥(Subgroup.normalizer (L : Set G)), ρ y = 1 →
      (y : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro y hy
    have : y ∈ ρ.ker := hy
    rw [hρ, CFSG.OddStandard.rhoOf_ker e, Subgroup.mem_subgroupOf] at this
    exact this
  have hKL : S ⊓ L ≤ L := inf_le_right
  have hπe : ∀ (ℓ : G) (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ =
      ((e ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := fun ℓ hℓ =>
    CFSG.OddStandard.rhoOf_apply_of_mem e hℓ
  have hKalt : imageUnder ρ (S ⊓ L) ≤ alternatingGroup (Fin 5) :=
    imageUnder_le_alt Subgroup.le_normalizer e.toMonoidHom hπe hKL
  have hKcard : Nat.card (imageUnder ρ (S ⊓ L)) = 4 :=
    card_imageUnder_eq_four Subgroup.le_normalizer e.toMonoidHom hπe e.surjective hKL
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]; exact bot_le) hStd.sylowL.2.1
      hStd.sylowL.2.2
  have hS2 : IsPGroup 2 S := hStd.sylow.2.1
  have hS₁pg : IsPGroup 2 (S ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) :=
    hS2.to_le inf_le_left
  have hKS₁ : S ⊓ L ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
  have hJS₁ : thompsonJ S ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (thompsonJ_le_self S) hJN
  have hS₁J : (S ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) ≤
      Subgroup.normalizer (thompsonJ S : Set G) := fun s hs =>
    normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hs.1)
  have hodd : ∃ j : ↥(Subgroup.normalizer (L : Set G)), (j : G) ∈ thompsonJ S ∧
      Equiv.Perm.sign (ρ j) = -1 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    have := le_sup_of_forall_sign_eq_one (π := ρ) (S := S ⊓ Subgroup.normalizer (L : Set G))
      (J := thompsonJ S) (K := S ⊓ L) (C := Subgroup.centralizer (L : Set G)) inf_le_right hJS₁
      hKS₁ hS₁pg hKalt hKcard hker (fun j hj => (Int.units_eq_one_or _).resolve_right (hcon j hj))
    exact this.trans (sup_le_sup_left (inf_le_inf_right _ inf_le_left) _)
  have key := eq_one_of_normalizes_odd (π := ρ) (S := S ⊓ Subgroup.normalizer (L : Set G))
    (J := thompsonJ S) (K := S ⊓ L) (Y := Y) hp hKS₁ hJS₁ hS₁pg hKalt hKcard hodd hS₁J hYJ hY
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro l hl y hy
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hYL hy
  have h1 := hker ⟨y, hyN⟩ (key ⟨y, hyN⟩ hy)
  exact (Subgroup.mem_centralizer_iff.1 h1 l hl).symm

@[expose] def Dich1521L2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) → IsPSL 2 2 2 ↥L →
    Nrm1521 S L ∨ Exc1521 X S L

theorem dich1521L2_of_two_of_ge_three (h2 : Dich1521L2Two)
    (h3 : ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
      IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
      (∃ n : ℕ, 3 ≤ n ∧ IsPSL 2 2 n ↥L) → Nrm1521 S L ∨ Exc1521 X S L) : Dich1521L2 := by
  intro G _ _ X S L hStd hco hZ hn
  obtain ⟨n, hn2, hL⟩ := hn
  rcases Nat.eq_or_lt_of_le hn2 with h | h
  · subst h
    exact h2 G X S L hStd hco hZ hL
  · exact h3 G X S L hStd hco hZ ⟨n, h, hL⟩

end CFSG.Quasithin
