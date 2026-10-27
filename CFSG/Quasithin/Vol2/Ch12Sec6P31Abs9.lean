module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs5
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs6
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs7
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs8
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs4

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 Equiv

section Aux

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_sylow_eq_of_card {X S : Subgroup Y} (hS : IsSylowTwoOf S X) {k m : ℕ}
    (hm : ¬ 2 ∣ m) (hX : Nat.card X = 2 ^ k * m) : Nat.card S = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hS.2.1.exists_card_eq
  have h1 := Subgroup.card_mul_index (S.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hj, hX] at h1
  have hidx := hS.2.2
  have hjk : j = k := by
    have hodd : ∀ n : ℕ, ¬ 2 ∣ n → Nat.Coprime (2 ^ j) n := fun n hn =>
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hn)
    have hodd' : ∀ n : ℕ, ¬ 2 ∣ n → Nat.Coprime (2 ^ k) n := fun n hn =>
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hn)
    have h2 : 2 ^ j ∣ 2 ^ k := by
      have : 2 ^ j ∣ 2 ^ k * m := ⟨_, h1.symm⟩
      exact Nat.Coprime.dvd_of_dvd_mul_right (hodd m hm) this
    have h3 : 2 ^ k ∣ 2 ^ j := by
      have : 2 ^ k ∣ 2 ^ j * (S.subgroupOf X).index := ⟨m, h1⟩
      exact Nat.Coprime.dvd_of_dvd_mul_right (hodd' _ hidx) this
    exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3)
  rw [hj, hjk]

theorem conjNormal_injective_of_centralizer_eq_bot (X : Subgroup Y) [X.Normal]
    (hC : Subgroup.centralizer (X : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut ↥X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hyC : y ∈ Subgroup.centralizer (X : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut ↥X => (φ ⟨x, hx⟩ : Y)) hy
    simp only [MulAut.conjNormal_val, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  rw [hC] at hyC
  exact hyC

theorem oTwoRes_top_le_of_sq (X : Subgroup Y) (hsq : ∀ y : Y, y ^ 2 ∈ X) :
    oTwoRes (⊤ : Subgroup Y) ≤ X := by
  refine (Subgroup.closure_le X).2 ?_
  rintro x ⟨-, m, ⟨j, rfl⟩, hm⟩
  have e : x = (x ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hm, one_mul]
  rw [e]
  exact X.pow_mem (hsq x) _

theorem ker_conjNormal_eq_centralizer_P31 (X : Subgroup Y) [X.Normal] :
    (MulAut.conjNormal : Y →* MulAut ↥X).ker = Subgroup.centralizer (X : Set Y) := by
  ext y
  rw [MonoidHom.mem_ker]
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut ↥X => (φ ⟨x, hx⟩ : Y)) hy
    simp only [MulAut.conjNormal_val, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro hy
    refine MulEquiv.ext fun n => Subtype.ext ?_
    have hn : (n : Y) * y = y * (n : Y) := Subgroup.mem_centralizer_iff.1 hy (n : Y) n.2
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    calc y * (n : Y) * y⁻¹ = ((n : Y) * y) * y⁻¹ := by rw [hn]
      _ = (n : Y) := by simp [mul_assoc]

end Aux


open CFSG.Quasithin.H13 in
theorem case1L_abs {Y : Type*} [Group Y] [Finite Y]
    (X Ts Ms Bs Ls Rs : Subgroup Y) [X.Normal]
    (hXs : IsSimpleGroup ↥X) (hXn : ¬ ∀ a b : ↥X, a * b = b * a) (hperf : ⁅X, X⁆ = X)
    (hXc : Nat.card X = 20160) (hLie : L34Facts12631 X)
    (hT : IsSylowTwoOf Ts ⊤) (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hsol : ∀ Z : Subgroup Y, Ts ≤ Z → Group.IsSolvable ↥Z → Z ≤ Ms) (hXM : ¬ X ≤ Ms)
    (hTB : Ts ≤ Bs) (hBM : Bs ≤ Ms) (hLB : Ls ≤ Bs)
    (hLn : Ms ≤ Subgroup.normalizer (Ls : Set Y))
    (hsup : X ⊔ Bs = ⊤) (h27 : ¬ 27 ∣ Nat.card Ms) (h9 : 9 ∣ Nat.card Ls)
    (hL23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Ls → p = 2 ∨ p = 3)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ X)
    (hm3 : ∀ A B C : Subgroup Y, Nat.card A = 3 → Nat.card B = 3 → Nat.card C = 3 →
      A ≤ Subgroup.centralizer (B : Set Y) → A ≤ Subgroup.centralizer (C : Set Y) →
      B ≤ Subgroup.centralizer (C : Set Y) → A ⊓ B = ⊥ → (A ⊔ B) ⊓ C = ⊥ → False)
    (hRT : Rs ≤ Ts)
    (hRmax : ∀ N : Subgroup Y, N ≤ Bs → Bs ≤ Subgroup.normalizer (N : Set Y) → IsPGroup 2 N →
      N ≤ Rs)
    (hRidx : 4 ≤ Rs.relIndex Ts) :
    Ms ⊓ X = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ∧
      Nonempty (Y ≃* MulAut ↥X) ∧ Ms = Ts ⊔ borel (oTwoRes (⊤ : Subgroup Y)) Ts := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsupM : X ⊔ Ms = ⊤ := eq_top_iff.2 (hsup ▸ sup_le_sup_left hBM _)
  set S₀ : Subgroup Y := Ts ⊓ X with hS₀
  have hSyl : IsSylowTwoOf S₀ X :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hTX : Ts ≤ Subgroup.normalizer (X : Set Y) := Subgroup.le_normalizer_of_normal
  have hBor : X ⊓ Subgroup.normalizer (S₀ : Set Y) ≤ Ms :=
    le_sup_right.trans (hsol (Ts ⊔ borel X Ts) le_sup_left
      (isSolvable_sup_borel hT.2.1 hTX hSyl))
  have hC : Subgroup.centralizer (X : Set Y) = ⊥ :=
    centralizer_eq_bot_of_three X hXs hXn hcop hO2 hLie.three_rank hm3
  have hinj := conjNormal_injective_of_centralizer_eq_bot X hC
  have hYdvd : Nat.card Y ∣ 241920 := by
    have h1 : Nat.card Y = Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1, ← hLie.card_aut]
    exact Subgroup.card_subgroup_dvd_card _
  have hXidx_mul := Subgroup.card_mul_index X
  rw [hXc] at hXidx_mul
  have hidx12 : X.index ∣ 12 := by
    have : 20160 * X.index ∣ 20160 * 12 := by
      rw [hXidx_mul]
      exact hYdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨hcard, hrel⟩ := card_eq_relIndex_mul X Ls
  have hW : 3 ^ 1 ∣ Nat.card ↥(Ls ⊓ X) := by
    by_contra hno
    rw [pow_one] at hno
    have hcop3 : Nat.Coprime 3 (Nat.card ↥(Ls ⊓ X)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hno
    have hcop9 : Nat.Coprime 9 (Nat.card ↥(Ls ⊓ X)) := by
      have := hcop3.pow_left 2
      simpa using this
    have h9' : 9 ∣ X.relIndex Ls * Nat.card ↥(Ls ⊓ X) := hcard ▸ h9
    have h9r : 9 ∣ X.relIndex Ls := hcop9.dvd_of_dvd_mul_right h9'
    have h912 : 9 ∣ 12 := h9r.trans (hrel.trans hidx12)
    omega
  have hKM : Ms ⊓ X = X ⊓ Subgroup.normalizer (S₀ : Set Y) :=
    eq_borel_of_overgroup X Ts Ms Ls 1 hBor hXM (hLB.trans hBM) hLn hL23
      (fun N W h1 h2 h3 h4 h5 h6 h7 => by
        rw [pow_one]
        exact hLie.overgroup S₀ N W hSyl h1 h2 h3 h4 h5 h6 h7) hW
  refine ⟨hKM, ?_⟩
  obtain ⟨-, hMn, -⟩ := sylow_inf_eq_pCoreOf_borel X Ts Ms hT hKM
  have hS₀R : S₀ ≤ Rs := hRmax S₀ (inf_le_left.trans hTB) (hBM.trans hMn) hSyl.2.1
  have hS₀c : Nat.card S₀ = 2 ^ 6 :=
    card_sylow_eq_of_card hSyl (k := 6) (m := 315) (by norm_num) (by rw [hXc]; norm_num)
  have hRc : 64 ≤ Nat.card Rs := by
    have := Subgroup.card_le_of_le hS₀R
    rw [hS₀c] at this
    simpa using this
  have hTsR : Rs.relIndex Ts * Nat.card Rs = Nat.card Ts := by
    have := Subgroup.relIndex_mul_card Rs Ts
    rwa [inf_of_le_left hRT] at this
  have hTs256 : 256 ≤ Nat.card Ts := by
    rw [← hTsR]
    nlinarith
  have h256 : 256 ∣ Nat.card Ts := by
    obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
    have hk8 : 8 ≤ k := by
      by_contra hlt
      push Not at hlt
      rw [hk] at hTs256
      interval_cases k <;> norm_num at hTs256
    rw [hk]
    have h8 : (2 : ℕ) ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 hk8
    norm_num at h8
    exact h8
  have hY256 : 256 ∣ Nat.card Y := h256.trans (Subgroup.card_subgroup_dvd_card Ts)
  have hMsX : Nat.card ↥(X ⊓ Ms) = 192 := by
    rw [inf_comm, hKM]
    exact hLie.card_borel S₀ hSyl
  have hYMs : Nat.card Y * 192 = 20160 * Nat.card Ms := by
    have := card_mul_card_inf_of_sup_eq_top X Ms hsupM
    rwa [hMsX, hXc] at this
  have hY105 : Nat.card Y = 105 * Nat.card Ms := by omega
  have hMs9 : 9 ∣ Nat.card Ms := h9.trans (Subgroup.card_dvd_of_le (hLB.trans hBM))
  have hY27 : 27 ∣ Nat.card Y := by
    obtain ⟨c, hc⟩ := hMs9
    exact ⟨35 * c, by rw [hY105, hc]; ring⟩
  have hY35 : 35 ∣ Nat.card Y :=
    (show 35 ∣ 20160 by norm_num).trans (hXc ▸ Subgroup.card_subgroup_dvd_card X)
  have hY241920 : 241920 ∣ Nat.card Y := by
    have h1 : 256 * 27 ∣ Nat.card Y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 256 27) hY256 hY27
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (256 * 27) 35) h1 hY35
  have hYeq : Nat.card Y = 241920 := Nat.dvd_antisymm hYdvd hY241920
  have hbij : Function.Bijective (MulAut.conjNormal : Y →* MulAut ↥X) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hYeq.trans hLie.card_aut.symm⟩
  refine ⟨⟨MulEquiv.ofBijective _ hbij⟩, ?_⟩
  obtain ⟨P', hP'n, hP'i, hP'I⟩ := hLie.normal_index_four
  set P : Subgroup Y := P'.comap (MulAut.conjNormal : Y →* MulAut ↥X) with hP
  haveI hPn : P.Normal := hP'n.comap _
  have hPidx : P.index = 4 := by
    rw [hP, Subgroup.index_comap_of_surjective P' hbij.2]
    exact hP'i
  have hXP : X ≤ P := by
    intro x hx
    apply hP'I
    refine ⟨⟨x, hx⟩, ?_⟩
    refine MulEquiv.ext fun n => Subtype.ext ?_
    simp [MulAut.conjNormal_val, MulAut.conj_apply]
  have hXidx : X.index = 12 := by
    rw [hYeq] at hXidx_mul
    omega
  haveI hOn := normal_oTwoRes_top (Y := Y)
  exact eq_sup_borel_of_normal X (oTwoRes (⊤ : Subgroup Y)) Ts Ms hT
    (le_oTwoRes_top_of_perfect X hperf) exists_pow_two_mem_oTwoRes_top
    (inf_oTwoRes_le X P Ts hXP hPidx hXidx hT.2.1) (hTB.trans hBM) hKM hsol


open CFSG.Quasithin.H13 in
theorem case1S_abs {Y : Type*} [Group Y] [Finite Y]
    (X Ts Ms Bs Ls Rs : Subgroup Y) [X.Normal]
    (hperf : ⁅X, X⁆ = X) (hXc : Nat.card X = 60480) (hLie : SL34Facts12631 X)
    (hZ : Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set Y)) = 3)
    (hT : IsSylowTwoOf Ts ⊤) (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hsol : ∀ Z : Subgroup Y, Ts ≤ Z → Group.IsSolvable ↥Z → Z ≤ Ms) (hXM : ¬ X ≤ Ms)
    (hTB : Ts ≤ Bs) (hBM : Bs ≤ Ms) (hLB : Ls ≤ Bs)
    (hLn : Ms ≤ Subgroup.normalizer (Ls : Set Y))
    (hsup : X ⊔ Bs = ⊤) (h27 : ¬ 27 ∣ Nat.card Ms) (h9 : 9 ∣ Nat.card Ls)
    (hL23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Ls → p = 2 ∨ p = 3)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ X)
    (hRT : Rs ≤ Ts)
    (hRmax : ∀ N : Subgroup Y, N ≤ Bs → Bs ≤ Subgroup.normalizer (N : Set Y) → IsPGroup 2 N →
      N ≤ Rs)
    (hRidx : 4 ≤ Rs.relIndex Ts) :
    Ms ⊓ X = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ∧ X.index = 4 ∧
      (∀ y : Y, y ^ 2 ∈ X) ∧ Ms = Ts ⊔ borel (oTwoRes (⊤ : Subgroup Y)) Ts := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsupM : X ⊔ Ms = ⊤ := eq_top_iff.2 (hsup ▸ sup_le_sup_left hBM _)
  set S₀ : Subgroup Y := Ts ⊓ X with hS₀
  have hSyl : IsSylowTwoOf S₀ X :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hTX : Ts ≤ Subgroup.normalizer (X : Set Y) := Subgroup.le_normalizer_of_normal
  have hBor : X ⊓ Subgroup.normalizer (S₀ : Set Y) ≤ Ms :=
    le_sup_right.trans (hsol (Ts ⊔ borel X Ts) le_sup_left
      (isSolvable_sup_borel hT.2.1 hTX hSyl))
  have hBorc : Nat.card ↥(X ⊓ Subgroup.normalizer (S₀ : Set Y)) = 576 :=
    hLie.card_borel S₀ hSyl
  have hXidx_mul := Subgroup.card_mul_index X
  rw [hXc] at hXidx_mul
  have hN9 : 9 ∣ Nat.card ↥(X ⊓ Ms) := by
    have hle : X ⊓ Subgroup.normalizer (S₀ : Set Y) ≤ X ⊓ Ms := le_inf inf_le_left hBor
    have := Subgroup.card_dvd_of_le hle
    rw [hBorc] at this
    exact (show 9 ∣ 576 by norm_num).trans this
  have hYMs : Nat.card Y * Nat.card ↥(X ⊓ Ms) = 60480 * Nat.card Ms := by
    have := card_mul_card_inf_of_sup_eq_top X Ms hsupM
    rwa [hXc] at this
  have hMsidx : X.index * Nat.card ↥(X ⊓ Ms) = Nat.card Ms := by
    rw [← hXidx_mul] at hYMs
    have h60 : 0 < 60480 := by norm_num
    have : 60480 * (X.index * Nat.card ↥(X ⊓ Ms)) = 60480 * Nat.card Ms := by
      rw [← hYMs]; ring
    exact Nat.eq_of_mul_eq_mul_left h60 this
  have h3idx : ¬ 3 ∣ X.index := by
    intro h3
    apply h27
    rw [← hMsidx]
    obtain ⟨a, ha⟩ := h3
    obtain ⟨b, hb⟩ := hN9
    exact ⟨a * b, by rw [ha, hb]; ring⟩
  obtain ⟨hcard, hrel⟩ := card_eq_relIndex_mul X Ls
  have hW : 3 ^ 2 ∣ Nat.card ↥(Ls ⊓ X) := by
    have hcop3 : Nat.Coprime 3 (X.relIndex Ls) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => h3idx (h3.trans hrel)
    have hcop9 : Nat.Coprime 9 (X.relIndex Ls) := by
      have := hcop3.pow_left 2
      simpa using this
    have h9' : 9 ∣ X.relIndex Ls * Nat.card ↥(Ls ⊓ X) := hcard ▸ h9
    simpa using hcop9.dvd_of_dvd_mul_left h9'
  have hKM : Ms ⊓ X = X ⊓ Subgroup.normalizer (S₀ : Set Y) :=
    eq_borel_of_overgroup X Ts Ms Ls 2 hBor hXM (hLB.trans hBM) hLn hL23
      (fun N W h1 h2 h3 h4 h5 h6 h7 => by
        simpa using hLie.overgroup S₀ N W hSyl h1 h2 h3 h4 h5 h6 h7) hW
  refine ⟨hKM, ?_⟩
  obtain ⟨-, hMn, -⟩ := sylow_inf_eq_pCoreOf_borel X Ts Ms hT hKM
  have hS₀R : S₀ ≤ Rs := hRmax S₀ (inf_le_left.trans hTB) (hBM.trans hMn) hSyl.2.1
  have hS₀c : Nat.card S₀ = 2 ^ 6 :=
    card_sylow_eq_of_card hSyl (k := 6) (m := 945) (by norm_num) (by rw [hXc]; norm_num)
  have hRc : 64 ≤ Nat.card Rs := by
    have := Subgroup.card_le_of_le hS₀R
    rw [hS₀c] at this
    simpa using this
  have hTsR : Rs.relIndex Ts * Nat.card Rs = Nat.card Ts := by
    have := Subgroup.relIndex_mul_card Rs Ts
    rwa [inf_of_le_left hRT] at this
  have hTs256 : 256 ≤ Nat.card Ts := by
    rw [← hTsR]
    nlinarith
  have hXTs : X.relIndex Ts * 64 = Nat.card Ts := by
    have := Subgroup.relIndex_mul_card X Ts
    rw [inf_comm] at this
    rwa [hS₀c] at this
  have hidx4 : 4 ≤ X.index := by
    have h1 : 4 ≤ X.relIndex Ts := by omega
    have h2 : X.relIndex Ts ∣ X.index := Subgroup.relIndex_dvd_index_of_normal X Ts
    exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2)
  have h9C : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer (X : Set Y)) := by
    intro h9C
    have h1 := Subgroup.relIndex_mul_card X (Subgroup.centralizer (X : Set Y))
    rw [hZ] at h1
    have h2 : X.relIndex (Subgroup.centralizer (X : Set Y)) ∣ X.index :=
      Subgroup.relIndex_dvd_index_of_normal X _
    apply h3idx
    have h3 : 3 ∣ X.relIndex (Subgroup.centralizer (X : Set Y)) := by omega
    exact h3.trans h2
  have hCX : Subgroup.centralizer (X : Set Y) ≤ X :=
    centralizer_le_of_center_three X hZ hcop hO2 h9C
  have hC3 : Nat.card ↥(Subgroup.centralizer (X : Set Y)) = 3 := by
    rw [← hZ, inf_eq_right.2 hCX]
  have hker := ker_conjNormal_eq_centralizer_P31 X
  have hcardY : Nat.card Y = 3 * Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).range := by
    have : Nat.card Y = Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).ker *
        Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    rwa [hker, hC3] at this
  have hrange : Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).range ∣ 241920 :=
    (Subgroup.card_subgroup_dvd_card _).trans hLie.card_aut
  have hidx12 : X.index ∣ 12 := by
    have h1 : 60480 * X.index ∣ 60480 * 12 := by
      rw [hXidx_mul, hcardY]
      calc 3 * Nat.card (MulAut.conjNormal : Y →* MulAut ↥X).range ∣ 3 * 241920 :=
            mul_dvd_mul_left 3 hrange
        _ = 60480 * 12 := by norm_num
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hidx : X.index = 4 := by
    have hcop3 : Nat.Coprime X.index 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3idx).symm
    have h4 : X.index ∣ 4 := hcop3.dvd_of_dvd_mul_right (show X.index ∣ 4 * 3 from hidx12)
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  have hφX : ∀ (x : Y) (hx : x ∈ X), (MulAut.conjNormal : Y →* MulAut ↥X) x =
      MulAut.conj (⟨x, hx⟩ : ↥X) := fun x hx => by
    refine MulEquiv.ext fun n => Subtype.ext ?_
    simp [MulAut.conjNormal_val, MulAut.conj_apply]
  have hsq : ∀ y : Y, y ^ 2 ∈ X := by
    intro y
    have h4 : y ^ 4 ∈ X := hidx ▸ Subgroup.pow_index_mem X y
    have h1 : (MulAut.conjNormal : Y →* MulAut ↥X) y ^ 4 ∈
        (MulAut.conj : ↥X →* MulAut ↥X).range := by
      rw [← map_pow]
      exact ⟨⟨y ^ 4, h4⟩, (hφX _ h4).symm⟩
    obtain ⟨x₀, hx₀⟩ := hLie.out_exp _ h1
    have h2 : (MulAut.conjNormal : Y →* MulAut ↥X) (y ^ 2 * (x₀ : Y)⁻¹) = 1 := by
      rw [map_mul, map_pow, ← hx₀, map_inv, hφX _ x₀.2]
      simp
    have h3 : y ^ 2 * (x₀ : Y)⁻¹ ∈ Subgroup.centralizer (X : Set Y) := by
      rw [← hker]; exact h2
    have h4' := X.mul_mem (hCX h3) x₀.2
    simpa using h4'
  refine ⟨hidx, hsq, ?_⟩
  rw [le_antisymm (oTwoRes_top_le_of_sq X hsq) (le_oTwoRes_top_of_perfect X hperf)]
  exact eq_sup_borel_of_normal X X Ts Ms hT le_rfl (fun y => ⟨1, by simpa using hsq y⟩)
    inf_le_right (hTB.trans hBM) hKM hsol

end CFSG.Quasithin.H13.S126P31
