module

public import CFSG.Quasithin.EmptyFaithful.A38c15Gl2
public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.A38c15 CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem charP_of_card_sq (hF : Nat.card F = p ^ 2) : CharP F p := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])

omit [Finite F] in
theorem uniData (hF : Nat.card F = p ^ 2) : UnitaryFieldData p 1 F :=
  ⟨Fact.out, le_rfl, by simpa using hF⟩

theorem two_ne_zero_of_card_sq (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : (2 : F) ≠ 0 := by
  have := charP_of_card_sq (p := p) hF
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem exists_su2_equiv (hF : Nat.card F = p ^ 2) :
    Nonempty (SL(2, ZMod p) ≃* ↥(StatedSU 2 (p ^ 1) F)) := by
  have := charP_of_card_sq (p := p) hF
  have hK : Nat.card F = (p ^ 1) ^ 2 := by simpa using hF
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p) (f := 1) hK
  have hfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p 1) = p := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    simp
  exact ⟨(CFSG.ClassicalModels.specialLinearFieldEquiv (fieldEquivZMod hfix).symm (Fin 2)).trans e⟩

theorem toGL_injective_zmod :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p)) :=
  fun a b hab => Subtype.ext (by simpa using congrArg (fun g : GL (Fin 2) (ZMod p) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod p))) hab)

theorem eq_one_or_neg_of_sq_fin_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {A : Matrix (Fin 2) (Fin 2) K} (hdet : A.det = 1) (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, A = !![a, b; c, d] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, Matrix.eta_fin_two A⟩
  simp only [Matrix.det_fin_two_of] at hdet
  have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hA
  have e01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hA
  have e10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hA
  have e11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hA
  simp at e00 e01 e10 e11
  have hsum : a + d ≠ 0 := by
    intro hs
    have : a * (a + d) = 2 := by linear_combination hdet + e00
    rw [hs] at this
    exact h2 (by linear_combination -this)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hsum
  subst hb hc
  have had : a = d := by
    have : (a - d) * (a + d) = 0 := by linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)
  subst had
  have ha : a * a = 1 := by linear_combination e00
  rcases mul_self_eq_one_iff.mp ha with h | h
  · left
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem dickson_su2 (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {Q : Subgroup (GL (Fin 2) F)} (hQ : Q ≤ StatedSU 2 (p ^ 1) F) [Group.IsPerfect ↥Q]
    (hne : Q ≠ ⊥) :
    Nonempty (↥Q ≃* SL(2, ZMod p)) ∨
      ((5 : F) ≠ 0 ∧
        (∀ y : ↥Q, y ∈ Subgroup.center ↥Q ↔
          (y : GL (Fin 2) F) = 1 ∨ (y : GL (Fin 2) F) = -1) ∧
        Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* alternatingGroup (Fin 5))) := by
  classical
  have hcp := charP_of_card_sq (p := p) hF
  have h2 := two_ne_zero_of_card_sq (p := p) hp2 hF
  have hU := uniData (p := p) hF
  obtain ⟨σ⟩ := exists_su2_equiv (p := p) hF
  let Θ : ↥Q →* GL (Fin 2) (ZMod p) :=
    (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p)).comp
      (σ.symm.toMonoidHom.comp (Subgroup.inclusion hQ))
  have hΘinj : Function.Injective Θ := by
    intro a b hab
    have h1 := toGL_injective_zmod hab
    have h2 := σ.symm.injective h1
    exact Subtype.ext (congrArg (fun x : ↥(StatedSU 2 (p ^ 1) F) => (x : GL (Fin 2) F)) h2)
  let ι : ↥Q ≃* ↥Θ.range := MonoidHom.ofInjective hΘinj
  have hperf4 : Group.IsPerfect ↥Θ.range :=
    Group.IsPerfect.ofSurjective (f := ι.toMonoidHom) ι.surjective
  have hne4 : Θ.range ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have : Θ ⟨y, hy⟩ = 1 := by
      have : Θ ⟨y, hy⟩ ∈ Θ.range := ⟨⟨y, hy⟩, rfl⟩
      rw [h] at this
      simpa using this
    have := hΘinj (this.trans (map_one Θ).symm)
    simpa using congrArg Subtype.val this
  obtain ⟨-, hcen4, -, -, hdiv, hndiv⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hp2 Θ.range hne4
  by_cases hpQ : p ∣ Nat.card Θ.range
  · left
    have hQ4eq := (hdiv hpQ).1
    exact ⟨ι.trans ((MulEquiv.subgroupCongr hQ4eq).trans
      (MonoidHom.ofInjective toGL_injective_zmod).symm)⟩
  · right
    obtain ⟨eP⟩ := hndiv hpQ
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨eA⟩ :=
      (CFSG.LinearGroups.five_field_linear_two_alternating_five_model (ZMod 5) (by simp)).1
    have hmapc : (Subgroup.center ↥Q).map ι.toMonoidHom = Subgroup.center ↥Θ.range :=
      Subgroup.map_center_eq ι
    let φ : (↥Q ⧸ Subgroup.center ↥Q) ≃* alternatingGroup (Fin 5) :=
      ((QuotientGroup.congr (Subgroup.center ↥Q) (Subgroup.center ↥Θ.range) ι hmapc).trans
        eP).trans eA
    have hcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 60 := by
      rw [Nat.card_congr φ.toEquiv, card_alt_five_fin]
    have h5 : (5 : F) ≠ 0 := by
      intro h
      have h' : ((5 : ℕ) : F) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff F p] at h'
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp h'
      apply hpQ
      have h60 : 60 ∣ Nat.card Q := hcard ▸ Subgroup.card_quotient_dvd_card _
      have h5dvd : (5 : ℕ) ∣ Nat.card Q := (show 5 ∣ 60 by norm_num).trans h60
      rw [Nat.card_congr ι.toEquiv] at h5dvd
      rwa [← hp5] at h5dvd
    refine ⟨h5, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ⟨φ⟩⟩
    ·
      have hcen' : ι y ∈ Subgroup.center ↥Θ.range := by
        rw [← hmapc]
        exact ⟨y, hy, rfl⟩
      have hΘy : Θ y = 1 ∨ Θ y = -1 := (hcen4 (ι y)).mp hcen'
      have hsq : Θ (y * y) = 1 := by
        rw [map_mul]
        rcases hΘy with h' | h' <;> rw [h'] <;> simp
      have hyy : y * y = 1 := hΘinj (hsq.trans (map_one Θ).symm)
      have hmat : ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        have := congrArg (fun x : ↥Q => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hyy
        simpa using this
      have hdet : ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
        ((mem_unitarySU_iff hU).mp (hQ y.2)).1
      rcases eq_one_or_neg_of_sq_fin_two h2 hdet hmat with h' | h'
      · left
        exact Units.ext h'
      · right
        exact Units.ext (by simpa using h')
    · rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      rcases hy with h' | h' <;> simp [h']

end CFSG.Quasithin.A312U3
