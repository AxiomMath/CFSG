
module

public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm

section Base

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem centre_of_baseCertS_base (C : LatCtx Γ n Lab) (hk : 0 < C.k) (B : List ℕ)
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ)
    (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ))
    (zn gn gin hn hin : ℕ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k)
    (hsg : C.sg = qp.map fun p => (slpElts a b prog).getD p.1 1) :
    ∃ z₀ : Γ, orderOf z₀ = 2 ∧ centerOf C.S = Subgroup.zpowers z₀ ∧
      (tab n z₀).toArray = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[zn]! := by
  have hcen := cmax_center_of_baseCertS (n := n) B hB hbase a b prog hv qp zn gn gin hn hin Ts par
    cl k hcert
  rw [← hsg, C.hSeq] at hcen
  have hS2 : IsPGroup 2 ↥C.S := IsPGroup.of_card C.S_card
  have hnt : Nontrivial ↥C.S :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [C.S_card]; exact Nat.one_lt_two_pow hk.ne')
  obtain ⟨h2, hZ⟩ := cmax_center_eq_zpowers hS2 hnt hcen
  exact ⟨_, h2, hZ, tab_slpElts_getD a b prog hv hcert.2.1⟩

end Base

theorem he_centre
    [HeOverFacts] :
    ∃ z₀ : CFSG.Sporadic.He.J, orderOf z₀ = 2 ∧ centerOf heCtx.S = Subgroup.zpowers z₀ ∧
      (tab 8330 z₀).toArray = heSLPC[170]! := by
  have hk : 0 < heCtx.k := by
    have : heCtx.k = 10 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS_base heCtx hk heB he_base_lt he_base_property
    CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg he_valid heQp 170 249 253 251 255 heEnum.1
    heEnum.2.1 heEnum.2.2 10 he_cert' rfl
  refine ⟨z₀, hz2, hZ, ?_⟩
  rw [hzT, he_ta, he_tb]
  rfl

end CFSG.Quasithin.S151S9T
