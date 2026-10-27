module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam
public import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFour

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.SubgroupLists Matrix

namespace AutM12Recog

namespace U34Rank

section General

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def Rel (a c : K) : Prop := c + σ c + a * σ a = 0

theorem unipGL_inj {a c a' c' : K} (h : unipGL σ a c = unipGL σ a' c') : a = a' ∧ c = c' := by
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) h
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp only [coe_unipGL, unipMat] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

@[expose] def uGL : Subgroup (GL (Fin 3) K) where
  carrier := {x | ∃ a c, Rel σ a c ∧ x = unipGL σ a c}
  one_mem' := ⟨0, 0, by simp [Rel], (unipGL_zero_zero σ).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, h, rfl⟩ ⟨a', c', h', rfl⟩
    refine ⟨a + a', c + c' - a * σ a', ?_, unipGL_mul σ a c a' c'⟩
    unfold Rel at *
    simp only [map_sub, map_add, map_mul, hσ]
    linear_combination h + h'
  inv_mem' := by
    rintro _ ⟨a, c, h, rfl⟩
    refine ⟨-a, σ c, ?_, ?_⟩
    · unfold Rel at *
      simp only [map_neg, hσ]
      linear_combination h
    · apply inv_eq_of_mul_eq_one_right
      rw [unipGL_mul]
      have h1 : c + σ c - a * σ (-a) = 0 := by
        unfold Rel at h
        simp only [map_neg]
        linear_combination h
      rw [← unipGL_zero_zero σ]
      exact unipGL_congr σ (by ring) h1

theorem uGL_le_SU : uGL σ hσ ≤ SU σ 3 := by
  rintro _ ⟨a, c, h, rfl⟩
  exact unipGL_mem_SU σ hσ h

omit hσ in
theorem eq_zero_of_sq_eq_one [CharP K 2] {a c : K} (h : unipGL σ a c * unipGL σ a c = 1) :
    a = 0 := by
  rw [unipGL_mul, ← unipGL_zero_zero σ] at h
  have h2 := (unipGL_inj σ h).2
  have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : a * σ a = 0 := by
    have : c + c - a * σ a = 2 * c - a * σ a := by ring
    rw [this, h3, zero_mul, zero_sub, neg_eq_zero] at h2
    exact h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact h5
  · exact σ.injective (by rw [h5, map_zero])

end General

section Concrete

open CFSG.GH74.KGroups CFSG.RankThree.PartTwo.KFacts.KS21.U34

theorem hσ16 : ∀ x, σ16 (σ16 x) = x := unitaryInvolution_involutive card_GF16

@[expose] def RelB (a c : GF16) : Prop := c + frob4 c + a * frob4 a = 0

instance (p : GF16 × GF16) : Decidable (RelB p.1 p.2) := by unfold RelB; infer_instance

theorem rel_iff (a c : GF16) : Rel σ16 a c ↔ RelB a c := by
  unfold Rel RelB
  rw [σ16_apply, σ16_apply]

noncomputable def uSub : Subgroup Y :=
  (uGL σ16 hσ16).subgroupOf Y

theorem card_relB : Fintype.card {p : GF16 × GF16 // RelB p.1 p.2} = 64 := by
  unfold RelB
  decide +kernel

theorem card_uSub : Nat.card uSub = 64 := by
  show Nat.card ((uGL σ16 hσ16).subgroupOf Y) = 64
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uGL_le_SU σ16 hσ16)).toEquiv]
  let e : {p : GF16 × GF16 // RelB p.1 p.2} → ↥(uGL σ16 hσ16) := fun p =>
    ⟨unipGL σ16 p.1.1 p.1.2, p.1.1, p.1.2, (rel_iff _ _).mpr p.2, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      have := unipGL_inj σ16 (congrArg Subtype.val h)
      exact Subtype.ext (Prod.ext this.1 this.2)
    · rintro ⟨_, a, c, h, rfl⟩
      exact ⟨⟨(a, c), (rel_iff _ _).mp h⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card, card_relB]

theorem card_fixed : Fintype.card {c : GF16 // c + frob4 c = 0} = 4 := by
  decide +kernel

theorem card_le_four_of_elemAbelian (E : Subgroup Y) (hE : E ≤ uSub)
    (hEa : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have : CharP GF16 2 := inferInstance
  have key : ∀ x : E, ∃ c, Rel σ16 0 c ∧ ((x : Y) : GL (Fin 3) GF16) = unipGL σ16 0 c := by
    intro x
    obtain ⟨a, c, h, hx0⟩ := hE x.2
    have hx : ((x : Y) : GL (Fin 3) GF16) = unipGL σ16 a c := hx0
    have hx2 : ((x : Y) : GL (Fin 3) GF16) * ((x : Y) : GL (Fin 3) GF16) = 1 := by
      have := hEa.2 (x : Y) x.2
      rw [sq] at this
      exact congrArg (fun y : Y => ((y : Y) : GL (Fin 3) GF16)) this
    rw [hx] at hx2
    have ha := eq_zero_of_sq_eq_one σ16 hx2
    subst ha
    exact ⟨c, h, hx⟩
  let g : E → {c : GF16 // c + frob4 c = 0} := fun x =>
    ⟨(((x : Y) : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) 0 2, by
      obtain ⟨c, h, hx⟩ := key x
      rw [hx]
      have := (rel_iff 0 c).mp h
      simpa [RelB, coe_unipGL, unipMat] using this⟩
  have hg : Function.Injective g := by
    intro x y hxy
    obtain ⟨c, -, hc⟩ := key x
    obtain ⟨c', -, hc'⟩ := key y
    have h1 := congrArg Subtype.val hxy
    simp only [g] at h1
    rw [hc, hc'] at h1
    simp only [coe_unipGL, unipMat] at h1
    have hcc : c = c' := by simpa using h1
    subst hcc
    exact Subtype.ext (Subtype.ext (by rw [hc, hc']))
  calc Nat.card E ≤ Nat.card {c : GF16 // c + frob4 c = 0} := Nat.card_le_card_of_injective g hg
    _ = 4 := by rw [Nat.card_eq_fintype_card, card_fixed]

noncomputable def sylowU : Sylow 2 Y :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard uSub (by
    rw [card_uSub, Nat.factorization_def _ Nat.prime_two, card_Y,
      show (62400 : ℕ) = 2 ^ 6 * 975 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num)

theorem rank_le_four (Q : Sylow 2 Y) (E : Subgroup Y) (hE : E ≤ Q) (hEa : IsElemAbelian 2 E) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : ↥(sylowU : Subgroup Y) ≃* ↥(Q : Subgroup Y) := Sylow.equiv sylowU Q
  let f : ↥(sylowU : Subgroup Y) →* Y := (Q : Subgroup Y).subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := (Q : Subgroup Y).subtype_injective.comp θ.injective
  have hEf : E ≤ f.range := fun x hx => ⟨θ.symm ⟨x, hE hx⟩, by simp [f]⟩
  obtain ⟨E', hE'U, hE'a, hE'c⟩ :=
    exists_elemAbelian_of_embed (sylowU : Subgroup Y) f hf hEf hEa
  rw [← hE'c]
  exact card_le_four_of_elemAbelian E' hE'U hE'a

end Concrete

end U34Rank

theorem excl_psu_three_four {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSU 3 2 2) : Excl S := by
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.KS21.U34.nonempty_equiv_Y h
  have : Finite CFSG.RankThree.PartTwo.KFacts.KS21.U34.Y := Finite.of_equiv S φ.toEquiv
  have hY : Excl CFSG.RankThree.PartTwo.KFacts.KS21.U34.Y :=
    excl_of_rank_le_four
      ⟨975, by decide, by rw [CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_Y]; norm_num⟩
      U34Rank.rank_le_four
  exact Excl.of_equiv hY φ

end AutM12Recog

end CFSG.Quasithin.F6
