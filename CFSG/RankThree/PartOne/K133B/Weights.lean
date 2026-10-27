module

public import CFSG.RankThree.PartOne.Q1327T.R8Lift
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
  CFSG.RankThree.PartOne.Q1327T

theorem card_torusImage_dvd_factorial {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (M : Subgroup (GL ι K)) {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* StatedProj M) {p : ℕ} [Fact p.Prime] {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hpK : (p : K) ≠ 0) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē) :
    Nat.card ↥(torusImage Ē ⊤) ∣ (Fintype.card ι).factorial := by
  obtain ⟨F, eF, hFel, hFM, -, hW⟩ := R8.exists_lifted_conf M e hd hpd hE hmax
  have := hFel
  obtain ⟨S, hS, φ, hcard, hinj⟩ := N143X.faithfulSmall_normalizer_range F hpK
  have h1 : Nat.card F.normalizerMonoidHom.range ∣ (Fintype.card ι).factorial :=
    N143X.FaithfulSmall.card_dvd_factorial ⟨S, hS, φ, hcard, hinj⟩
  let ρ : MulAut Ē →* MulAut F := (MulAut.congr eF.symm).toMonoidHom
  have hmem : ∀ x : ↥(torusImage Ē ⊤), ρ x ∈ F.normalizerMonoidHom.range := fun x =>
    hW x (by rw [← torusImage_top_eq_range]; exact x.2)
  let ψ : ↥(torusImage Ē ⊤) →* ↥F.normalizerMonoidHom.range :=
    (ρ.comp (torusImage Ē ⊤).subtype).codRestrict _ hmem
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    apply Subtype.ext
    exact (MulAut.congr eF.symm).injective h2
  exact (Subgroup.card_dvd_of_injective ψ hψ).trans h1

theorem oddOrderOneOrThree_of_matrix_four {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (M : Subgroup (GL ι K)) {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* StatedProj M) {p : ℕ} [Fact p.Prime] {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hpK : (p : K) ≠ 0) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē) (hι : Fintype.card ι ≤ 4) : OddOrderOneOrThree ↥(torusImage Ē ⊤) := by
  have h1 := card_torusImage_dvd_factorial M e hd hpd hpK hE hmax
  have h2 : (Fintype.card ι).factorial ∣ 24 := by
    have : Fintype.card ι ≤ 4 := hι
    interval_cases (Fintype.card ι) <;> decide
  exact OddOrderOneOrThree.of_card_dvd (a := 3) (h1.trans h2)

end CFSG.RankThree.PartOne.K133B
