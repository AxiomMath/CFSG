module

public import CFSG.RankThree.PartOne.Q1327T.R8Lift
public import CFSG.RankThree.PartOne.Q1327T.R8Count
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X

theorem row8_weight_numbers {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (M : Subgroup (GL ι K)) {Q : Type} [Group Q]
    (e : Q ≃* StatedProj M) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hpd : ¬ p ∣ d) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē)
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) :
    ∃ (m : ℕ) (u : (ZMod p)ˣ), (u : ZMod p) = ((2 ^ f : ℕ) : ZMod p) ∧ 0 < m ∧
      m ≤ Fintype.card ι ∧ 3 ∣ m ∧ orderOf u ∣ m := by
  classical
  have hp := (Fact.out : p.Prime)
  have : Finite Q := Finite.of_equiv (StatedProj M) e.symm.toEquiv
  obtain ⟨F, eF, hFel, hFM, hFmax, hle⟩ := exists_lifted_conf M e hd hpd hE hmax
  obtain ⟨φ⟩ := hW
  let W : Subgroup (MulAut Ē) := Ē.normalizerMonoidHom.range
  have hWeq : torusImage Ē ⊤ = W := torusImage_top_eq_range Ē
  let φ' : W ≃* Equiv.Perm (Fin 3) := (MulEquiv.subgroupCongr hWeq.symm).trans φ
  have : IsElementaryAbelian p Ē := hE
  obtain ⟨β₀, hβ₀W, hβ₀ord, hβ₀fpf⟩ := exists_order_three_fixedFree hp5 hcard W φ'
  let β : MulAut F := MulAut.congr eF.symm β₀
  have hβrange : β ∈ F.normalizerMonoidHom.range := hle β₀ hβ₀W
  have hβord : orderOf β = 3 := by
    rw [MulEquiv.orderOf_eq, hβ₀ord]
  have hβfpf : ∀ x : F, β x = x → x = 1 := by
    intro x hx
    have h1 : eF.symm (β₀ (eF x)) = x := hx
    have h2 : β₀ (eF x) = eF x := by
      have := congrArg eF h1
      simpa using this
    have := hβ₀fpf _ h2
    simpa using this
  have hKchar : CharP K 2 := charP_two_of_card (g := f) hK
  have : IsElementaryAbelian p F := hFel
  obtain ⟨X, c, hc, hX1, hXsep, hXn, hX3, hXc⟩ :=
    exists_weight_set (K := K) (f := f) hK hp5 F β hβrange hβord hβfpf
  have hμ : ∀ z : rootsOfUnity p (AlgebraicClosure K), z ^ p = 1 := fun z =>
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact (mem_rootsOfUnity p (z : (AlgebraicClosure K)ˣ)).1 z.2)
  have hodvd : orderOf c ∣ X.card := orderOf_dvd_card_of_stable hμ X hX1 c hXc
  have hXpos : 0 < X.card := by
    rw [Finset.card_pos]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ x : F, x = 1 := fun x => hXsep x (by simp [hne])
    have : Nat.card F = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card F = p ^ 2 := by rw [Nat.card_congr eF.toEquiv, hcard]
    have : p ^ 2 = 1 := by rw [← h2, this]
    have := hp.two_le
    nlinarith
  exact ⟨X.card, c, hc, hXpos, hXn, hX3, hodvd⟩

theorem false_of_row8_small {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (M : Subgroup (GL ι K)) {Q : Type} [Group Q]
    (e : Q ≃* StatedProj M) {p g : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpg : p ∣ 2 ^ g + 1)
    {d : ℕ} (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hpd : ¬ p ∣ d) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē)
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) (hn : Fintype.card ι ≤ 11) : False := by
  obtain ⟨m, u, hu, hm0, hmn, hm3, hmo⟩ :=
    row8_weight_numbers (f := 1) (by simpa using hK) M e hp5 hd hpd hE hcard hmax hW
  have hu2 : (u : ZMod p) = 2 := by simpa using hu
  have h12 := twelve_le_of_dvd hp5 hpg u hu2 hm0 hm3 hmo
  omega

end CFSG.RankThree.PartOne.Q1327T.R8
