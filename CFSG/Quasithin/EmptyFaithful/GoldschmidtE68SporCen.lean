module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporGr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxCen
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.S151S9T

theorem centre_data_of_baseCertS {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    (B : List ℕ) (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (a b : Γ) (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ))
    (zn gn gin hn hin : ℕ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ) (hk : 0 < k)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    ∃ (S : Subgroup Γ) (z₀ : Γ), Nat.card S = 2 ^ k ∧ orderOf z₀ = 2 ∧
      S ⊓ Subgroup.centralizer (S : Set Γ) = Subgroup.zpowers z₀ ∧
      (tab n z₀).toArray = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[zn]! := by
  have hcen := cmax_center_of_baseCertS (n := n) B hB hbase a b prog hv qp zn gn gin hn hin Ts par
    cl k hcert
  have hcard := (sGens_of_baseCertS (n := n) B hB hbase a b prog hv qp zn gn gin hn hin Ts par cl
    k hcert).2
  have hS2 := IsPGroup.of_card (p := 2) hcard
  have hnt : Nontrivial ↥(Subgroup.closure {x | x ∈ qp.map fun p =>
      (slpElts a b prog).getD p.1 1}) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact Nat.one_lt_two_pow hk.ne')
  obtain ⟨h2, hZ⟩ := cmax_center_eq_zpowers hS2 hnt hcen
  exact ⟨_, _, hcard, h2, hZ, tab_slpElts_getD a b prog hv hcert.2.1⟩

theorem isSylowTwoOf_of_card {Γ : Type*} [Group Γ] [Finite Γ] {S : Subgroup Γ} {k N : ℕ}
    (hN : Odd N) (hS : Nat.card S = 2 ^ k) (hΓ : Nat.card Γ = 2 ^ k * N) :
    IsSylowTwoOf S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card hS, ?_⟩
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S]
  have h1 := Subgroup.card_mul_index S
  rw [hS, hΓ] at h1
  have h2 : S.index = N := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos k) h1
  rw [h2]
  rintro ⟨c, hc⟩
  obtain ⟨d, hd⟩ := hN
  omega

theorem latCtx_isSylowTwoOf {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab) {N : ℕ}
    (hN : C.D.O.lbl.size = N) (hodd : Odd N) : IsSylowTwoOf C.S ⊤ :=
  isSylowTwoOf_of_card hodd C.S_card (by rw [C.hΓ, hN, mul_comm])

theorem faithfulSMul_of_base {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {B : List ℕ}
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) :
    FaithfulSMul Γ (Fin n) where
  eq_of_smul_eq_smul {g h} hgh := by
    have h1 : h⁻¹ * g = 1 := hbase _ fun b hb => by
      have hb' : b < n := hB b hb
      rw [show act n (h⁻¹ * g) b = (((h⁻¹ * g) • (⟨b, hb'⟩ : Fin n) : Fin n) : ℕ) from
        act_eq _ ⟨b, hb'⟩, mul_smul, hgh ⟨b, hb'⟩, inv_smul_smul]
    exact (inv_mul_eq_one.mp h1).symm

end CFSG.Quasithin.E6.Spor
