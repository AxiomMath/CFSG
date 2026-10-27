module

public import CFSG.Quasithin.Vol2.KGFactInspSp4

public section

namespace CFSG.Quasithin.H13.KGInsp4316.Exc

open CFSG.QuasithinUnique.Setup.X6 (ResidualOvergroupsAt)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect perfectCore_le perfectCore_perfect
  isSolvable_iff_perfectCore_eq_bot)

theorem odd_dvd_card_of_ker {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (ψ : A →* B) (hker : IsPGroup 2 ψ.ker) {d : ℕ} (hd : Odd d) (hdA : d ∣ Nat.card A) :
    d ∣ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
  have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card A := Subgroup.card_mul_index _
  rw [hk, Subgroup.index_ker] at h1
  have hcop : Nat.Coprime d (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hd)
  have h2 : d ∣ Nat.card ψ.range := hcop.dvd_of_dvd_mul_left (h1 ▸ hdA)
  exact h2.trans (Subgroup.card_subgroup_dvd_card _)

theorem odd_dvd_card_of_le {C B : Type*} [Group C] [Group B] [Finite C] [Finite B]
    {D P : Subgroup C} (hDP : D ≤ P) (ψ : ↥P →* B) (hker : IsPGroup 2 ψ.ker) {d : ℕ} (hd : Odd d)
    (hdD : d ∣ Nat.card D) : d ∣ Nat.card B := by
  refine odd_dvd_card_of_ker (ψ.comp (Subgroup.inclusion hDP)) ?_ hd hdD
  rw [← MonoidHom.comap_ker]
  exact hker.comap_of_injective _ (Subgroup.inclusion_injective hDP)

theorem dvd_of_four_pow_sub_one_dvd {n m : ℕ} (hn : 1 ≤ n)
    (h : 4 ^ n - 1 ∣ 2 ^ m * (4 ^ m - 1)) : n ∣ m := by
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      ((Nat.even_pow' (by omega)).mpr (by decide)) odd_one
  have hcop : Nat.Coprime (4 ^ n - 1) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  have h1 : 4 ^ n - 1 ∣ 4 ^ m - 1 := hcop.dvd_of_dvd_mul_left h
  have h2 : Nat.gcd (4 ^ n - 1) (4 ^ m - 1) = 4 ^ n - 1 := Nat.gcd_eq_left h1
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h2
  have h3 : 4 ^ Nat.gcd n m = 4 ^ n := by
    have := Nat.one_le_pow (Nat.gcd n m) 4 (by norm_num)
    have := Nat.one_le_pow n 4 (by norm_num)
    omega
  have h4 : Nat.gcd n m = n := Nat.pow_right_injective (le_refl 2) (by
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] using h3)
  exact Nat.gcd_eq_left_iff_dvd.mp h4

theorem exists_conj_le_perfectCore {C : Type} [Group C] [Finite C]
    (hBT : CFSG.LieType.BorelTits.Holds C 2) {U : Subgroup C}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup C}
    (hP : ResidualOvergroupsAt C U P) {R K : Subgroup C} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hKR : K ≤ Subgroup.normalizer (R : Set C)) (hKp : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    ∃ (j : Fin 2) (c : C), K.map (MulAut.conj c).toMonoidHom ≤ perfectCore (P j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, Pb, hPb, hNR, -, -, hNS⟩ := hBT R hR hR2
  have hUidx : ¬ 2 ∣ U.index := by
    have h := hU.2.2
    rwa [← Subgroup.relIndex_top_right]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S (hU.2.1.toSylow hUidx)
  set φ : C →* C := (MulAut.conj c).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj c).injective
  set M : Subgroup C := Pb.map φ with hM
  have hUM : U ≤ M := by
    have h1 : ((c • S : Sylow 2 C) : Subgroup C) = U := by
      rw [hc]
      exact IsPGroup.toSylow_coe _ _
    rw [← h1, Sylow.coe_subgroup_smul]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hNS)
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply hPb
    have h1 : M.map (MulAut.conj c)⁻¹.toMonoidHom = Pb := by
      rw [hM, Subgroup.map_map]
      have hid : (MulAut.conj c)⁻¹.toMonoidHom.comp φ = MonoidHom.id C := by
        ext x
        simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MulAut.conj_inv_apply, MonoidHom.id_apply]
        group
      rw [hid, Subgroup.map_id]
    rw [← h1, htop, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj c)⁻¹.surjective
  set K' : Subgroup C := K.map φ with hK'
  have hK'M : K' ≤ M := Subgroup.map_mono (hKR.trans hNR)
  have hK'p : ⁅K', K'⁆ = K' := by
    rw [hK', ← Subgroup.map_commutator, hKp]
  have hK'1 : K' ≠ ⊥ := by
    rw [hK', Ne, Subgroup.map_eq_bot_iff_of_injective _ hφinj]
    exact hK1
  have hns : ¬ Group.IsSolvable ↥M := by
    intro hs
    have hs' : Group.IsSolvable ↥K' :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK'M)
        (Subgroup.inclusion_injective _)
    have h1 : perfectCore K' = ⊥ := (isSolvable_iff_perfectCore_eq_bot K').mp hs'
    exact hK'1 (le_bot_iff.mp (h1 ▸ le_perfectCore_of_perfect le_rfl hK'p))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 M hUM hMtop hns
  refine ⟨j, c, ?_⟩
  have h1 : perfectCore M = perfectCore (P j) := by
    rw [← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore,
      ← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hd]
  exact h1 ▸ le_perfectCore_of_perfect hK'M hK'p

section Cfg

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem concl_of_two_le_pRank (h : Cfg4316 S R K n x) (hRS : R ≤ S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (h2 : 2 ≤ CFSG.Open.pRank p S) : n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S) := by
  rcases h.prime p hp hp2 hpn with h1 | ⟨-, s, q, hq, hL⟩
  · omega
  · exact h.of_psleps3q hRS hq hL

theorem four_pow_sub_one_dvd_card (h : Cfg4316 S R K n x) : 4 ^ n - 1 ∣ Nat.card K := by
  obtain ⟨F, _, _, hF, χ, hχ, -⟩ := h.chi
  have h1 := Subgroup.card_dvd_of_surjective hχ
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hF,
    ← pow_mul, mul_comm n 2, pow_mul] at h1
  norm_num at h1
  exact (Dvd.intro_left _ rfl).trans h1

theorem exists_le_perfectCore (h : Cfg4316 S R K n x) (hRS : R ≤ S) {C : Type} [Group C]
    [Finite C] (e : ↥S ≃* C) (hBT : CFSG.LieType.BorelTits.Holds C 2) {U : Subgroup C}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup C}
    (hP : ResidualOvergroupsAt C U P) :
    ∃ (j : Fin 2) (D : Subgroup C), D ≤ perfectCore (P j) ∧ 4 ^ n - 1 ∣ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥S →* C := e.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := e.injective
  have h4K := four_pow_sub_one_dvd_card h
  have hKS : Nat.card ↥(K.subgroupOf S) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hKC : Nat.card ↥((K.subgroupOf S).map ψ) = Nat.card K := by
    rw [Subgroup.card_map_of_injective hψ, hKS]
  have hRC : (R.subgroupOf S).map ψ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
    intro hb
    apply h.ne_bot
    have h1 := congrArg (Subgroup.map S.subtype) hb
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, inf_eq_left.mpr hRS] at h1
  have hRC2 : IsPGroup 2 ↥((R.subgroupOf S).map ψ) :=
    (h.isPGroup.comap_of_injective S.subtype S.subtype_injective).map ψ
  have hKN : K.subgroupOf S ≤ Subgroup.normalizer ((R.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [Subgroup.mem_normalizer_iff]
    intro r
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (h.le_normalizer hk) r
  have hKCN : (K.subgroupOf S).map ψ ≤
      Subgroup.normalizer (((R.subgroupOf S).map ψ : Subgroup C) : Set C) :=
    (Subgroup.map_mono hKN).trans (Subgroup.le_normalizer_map ψ)
  have hKSp : ⁅K.subgroupOf S, K.subgroupOf S⁆ = K.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.le,
      h.perfect]
  have hKCp : ⁅(K.subgroupOf S).map ψ, (K.subgroupOf S).map ψ⁆ = (K.subgroupOf S).map ψ := by
    rw [← Subgroup.map_commutator, hKSp]
  have hKC1 : (K.subgroupOf S).map ψ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hKC
    rw [← hKC, Nat.dvd_one] at h4K
    have : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    omega
  obtain ⟨j, c, hjc⟩ := exists_conj_le_perfectCore hBT hU hP hRC hRC2 hKCN hKCp hKC1
  refine ⟨j, _, hjc, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hKC]
  exact h4K

end Cfg

end CFSG.Quasithin.H13.KGInsp4316.Exc
