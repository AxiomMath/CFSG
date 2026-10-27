module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKAux

public noncomputable section
namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431.G2.OutK

section Main

variable {K : Type} [Field K]

structure OutK (A : LieAmalgamExt (C K)) (N N' T S : Subgroup ↥A.K) (t₀ f z : ↥A.K)
    (I : Finset ↥A.K) (F2 : Subgroup (K ≃+* K)) (n a : ℕ) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le : T ≤ N
  T_le' : T ≤ N'
  S_le : S ≤ T
  S_norm : T ≤ Subgroup.normalizer (S : Set ↥A.K)
  cyc : T = S ⊔ Subgroup.zpowers t₀
  z_mem : z ∈ T
  z_two : orderOf z = 2
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f ^ 2 = 1
  I_le : ∀ i ∈ I, i ∈ S ∧ orderOf i = 2
  Z_sq : ∀ x ∈ centerOf (perfectCore N), x ^ 2 = 1
  S_mem : ∀ x : ↥A.K, x ∈ S ↔ ∃ u ∈ U K, (x : MulAut (C K)) = MulAut.conj u
  T_mem : ∀ x : ↥A.K, x ∈ T ↔ ∃ u ∈ U K, ∃ σ ∈ F2,
    (x : MulAut (C K)) = MulAut.conj u * fieldAut K σ
  N_mem : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
    (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ
  N'_mem : ∀ x : ↥A.K, x ∈ N' ↔ ∃ g ∈ Pmin K ⟨0, by decide⟩, ∃ σ ∈ Fz A,
    (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ
  z_eq : (z : MulAut (C K)) = MulAut.conj (xc (1 : K))
  I_mem : ∀ i : ↥A.K, i ∈ I ↔ ∃ u ∈ ({xa (1 : K), xu 1, xv 1, xb 1, xc 1} : Set (C K)),
    (i : MulAut (C K)) = MulAut.conj u
  t₀_eq : ∃ σ₀ : K ≃+* K, F2 = Subgroup.zpowers σ₀ ∧ (t₀ : MulAut (C K)) = fieldAut K σ₀ ∧
    (f : MulAut (C K)) = fieldAut K (σ₀ ^ 2 ^ (a - 1))
  F2_le : F2 ≤ Fz A
  card_F2 : Nat.card F2 = 2 ^ a
  a_pos : 1 ≤ a
  card_Fz : ∃ e : ℕ, Odd e ∧ Nat.card (Fz A) = 2 ^ a * e
  even_n : Even n
  delta : ∀ σ₀ : K ≃+* K, F2 = Subgroup.zpowers σ₀ → ∀ c : K, (σ₀ ^ 2 ^ (a - 1)) c = c ^ 2 ^ (n / 2)

end Main

end CFSG.Quasithin.H13.F431.G2

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex

section Assemble

variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

abbrev outT (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) (ψ : ↥A.K) :
    Subgroup ↥A.K :=
  spT (iK A hgen) ψ (U K)

abbrev outf (ψ : ↥A.K) : ↥A.K := psi2 ψ ^ 2 ^ (twoExp ψ - 1)

theorem U_stable_pow (σ : K ≃+* K) (k : ℕ) (x : C K) :
    ((fieldAut K σ) ^ k) x ∈ U K ↔ x ∈ U K := by
  rw [← map_pow]
  exact (fieldAut_mem_autStab_U (K := K) (σ ^ k) x).symm

theorem coe_psi2_pow (h : IsNormalized A) {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (s : ℕ) :
    ((psi2 (psiK h hσ₁) ^ s : ↥A.K) : MulAut (C K)) =
      fieldAut K ((σ₁ ^ oddPart (psiK h hσ₁)) ^ s) := by
  rw [psi2_pow_eq, Subgroup.coe_pow, psiK_coe, ← map_pow, pow_mul]

theorem mem_outT_iff {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁)
    (x : ↥A.K) :
    x ∈ outT (h.inn_le_K hn hK) (psiK h hσ₁) ↔
      ∃ u ∈ U K, ∃ σ ∈ Subgroup.zpowers (σ₁ ^ oddPart (psiK h hσ₁)),
        (x : MulAut (C K)) = MulAut.conj u * fieldAut K σ := by
  have hFinK := finite_C (K := K)
  have hFinA : Finite (MulAut (C K)) := finite_mulAut_C (K := K)
  have hFinAut : Finite (K ≃+* K) := finite_ringAut (by omega : 1 ≤ n) hK
  have P := outProps_of_gen hn hK h hσ₁ hgen
  rw [P.mem_spT_iff (fun k x => U_stable_pow σ₁ k x)]
  constructor
  · rintro ⟨u, hu, s, rfl⟩
    refine ⟨u, hu, (σ₁ ^ oddPart (psiK h hσ₁)) ^ s,
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) s, ?_⟩
    rw [Subgroup.coe_mul, iK_coe, coe_psi2_pow]
  · rintro ⟨u, hu, σ, hσ, hx⟩
    obtain ⟨s, rfl⟩ := (mem_zpowers_iff_nat _ σ).1 hσ
    exact ⟨u, hu, s, Subtype.ext (by rw [hx, Subgroup.coe_mul, iK_coe, coe_psi2_pow])⟩

theorem outK_of_gen {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁)
    (hev : Even (orderOf σ₁)) {N N' : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ)
    (hN' : ∀ x : ↥A.K, x ∈ N' ↔ ∃ g ∈ Pmin K ⟨0, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    OutK A N N' (outT (h.inn_le_K hn hK) (psiK h hσ₁)) (outS (h.inn_le_K hn hK))
      (psi2 (psiK h hσ₁)) (outf (psiK h hσ₁)) (iK A (h.inn_le_K hn hK) (xc 1))
      (outI (h.inn_le_K hn hK)) (Subgroup.zpowers (σ₁ ^ oddPart (psiK h hσ₁))) n
      (twoExp (psiK h hσ₁)) := by
  have hFinK := finite_C (K := K)
  have hFinA : Finite (MulAut (C K)) := finite_mulAut_C (K := K)
  have hFinAut : Finite (K ≃+* K) := finite_ringAut (by omega : 1 ≤ n) hK
  have hgenK := h.inn_le_K hn hK
  have P := outProps_of_gen hn hK h hσ₁ hgen
  have hinj : Function.Injective (iK A hgenK) := iK_injective A hgenK center_C_eq_bot'
  have hoψ : orderOf (psiK h hσ₁) = orderOf σ₁ := orderOf_psiK hn hK h hσ₁ hgen
  have hUst : ∀ (k : ℕ) (x : C K), ((fieldAut K σ₁) ^ k) x ∈ U K ↔ x ∈ U K :=
    fun k x => U_stable_pow σ₁ k x
  have ha : 1 ≤ twoExp (psiK h hσ₁) := twoExp_pos (by rw [hoψ]; exact hev)
  have hF2le : Subgroup.zpowers (σ₁ ^ oddPart (psiK h hσ₁)) ≤ Fz A :=
    Subgroup.zpowers_le.2 (Subgroup.pow_mem _ hσ₁ _)
  have hcoe1 : ((psi2 (psiK h hσ₁) : ↥A.K) : MulAut (C K)) =
      fieldAut K (σ₁ ^ oddPart (psiK h hσ₁)) := by
    have := coe_psi2_pow h hσ₁ 1
    simpa using this
  have hordσ₀ : orderOf (σ₁ ^ oddPart (psiK h hσ₁)) = 2 ^ twoExp (psiK h hσ₁) := by
    calc orderOf (σ₁ ^ oddPart (psiK h hσ₁))
        = orderOf (fieldAut K (σ₁ ^ oddPart (psiK h hσ₁))) :=
          (orderOf_injective (fieldAut K) (fieldAut_injective hn hK) _).symm
      _ = orderOf ((psi2 (psiK h hσ₁) : ↥A.K) : MulAut (C K)) := by rw [hcoe1]
      _ = orderOf (psi2 (psiK h hσ₁)) := Subgroup.orderOf_coe _
      _ = 2 ^ twoExp (psiK h hσ₁) := orderOf_psi2 _
  have hFzeq : Fz A = Subgroup.zpowers σ₁ :=
    le_antisymm (fun σ hσ => hgen σ hσ) (Subgroup.zpowers_le.2 hσ₁)
  have hdel := delta_apply hn hK ha hordσ₀
  refine
    { sylow := P.isSylowTwoOf_spT (fun k x => hUst k x) g2_sylow
      T_le := ?_
      T_le' := ?_
      S_le := le_sup_left
      S_norm := sup_le Subgroup.le_normalizer (P.zpowers_psi2_le_normalizer (fun k x => hUst k x))
      cyc := rfl
      z_mem := Subgroup.mem_sup_left ⟨xc 1, xc_mem_U 1, rfl⟩
      z_two := ?_
      f_mem := Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _
      f_not := ?_
      f_sq := ?_
      I_le := ?_
      Z_sq := ?_
      S_mem := mem_outS_iff hgenK
      T_mem := mem_outT_iff hn hK h hσ₁ hgen
      N_mem := hN
      N'_mem := hN'
      z_eq := rfl
      I_mem := mem_outI_iff hgenK
      t₀_eq := ⟨_, rfl, hcoe1, ?_⟩
      F2_le := hF2le
      card_F2 := ?_
      a_pos := ha
      card_Fz := ?_
      even_n := hdel.1
      delta := ?_ }
  · intro x hx
    obtain ⟨u, hu, σ, hσ, hxu⟩ := (mem_outT_iff hn hK h hσ₁ hgen x).1 hx
    exact (hN x).2 ⟨u, U_le_Pmin _ hu, σ, hF2le hσ, hxu⟩
  · intro x hx
    obtain ⟨u, hu, σ, hσ, hxu⟩ := (mem_outT_iff hn hK h hσ₁ hgen x).1 hx
    exact (hN' x).2 ⟨u, U_le_Pmin _ hu, σ, hF2le hσ, hxu⟩
  · rw [orderOf_injective (iK A hgenK) hinj]
    exact orderOf_xe_one rC
  · intro hfS
    have hr : outf (psiK h hσ₁) ∈ (iK A hgenK).range := by
      obtain ⟨u, -, hu⟩ := hfS
      exact ⟨u, hu⟩
    have h1 := (P.psi2_pow_mem_range_iff _).1 hr
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_psi2] at h2
    have h3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2
    omega
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha]
    exact psi2_pow_two_exp _
  · intro i hi
    obtain ⟨u, hu, hiu⟩ := (mem_outI_iff hgenK i).1 hi
    obtain ⟨huU, huo⟩ := mem_roots hu
    have hiu' : i = iK A hgenK u := Subtype.ext hiu
    subst hiu'
    exact ⟨Subgroup.mem_map_of_mem _ huU, by rw [orderOf_injective (iK A hgenK) hinj, huo]⟩
  · intro x hx
    rw [centerOf_perfectCore_eq hn hK hgenK P hN] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, sq_eq_one_of_mem_center_Pr hn hK hy, map_one]
  · have := coe_psi2_pow h hσ₁ (2 ^ (twoExp (psiK h hσ₁) - 1))
    exact this
  · rw [Nat.card_zpowers, hordσ₀]
  · refine ⟨oddPart (psiK h hσ₁), oddPart_odd _, ?_⟩
    rw [hFzeq, Nat.card_zpowers, ← hoψ]
    exact (twoExp_mul_oddPart _).symm
  · intro σ₀' hσ₀'
    have ho : orderOf σ₀' = 2 ^ twoExp (psiK h hσ₁) := by
      rw [← Nat.card_zpowers, ← hσ₀', Nat.card_zpowers, hordσ₀]
    exact (delta_apply hn hK ha ho).2

theorem even_orderOf_of_not_odd {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h : IsNormalized A) {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A)
    (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁)
    (hev : ¬ Odd (Nat.card ↥A.K / Nat.card (C K))) : Even (orderOf σ₁) := by
  have hFinK := finite_C (K := K)
  have hFinA : Finite (MulAut (C K)) := finite_mulAut_C (K := K)
  have P := outProps_of_gen hn hK h hσ₁ hgen
  have h1 : Nat.card ↥A.K / Nat.card (C K) = orderOf (psiK h hσ₁) := by
    rw [P.card_eq]
    exact Nat.mul_div_cancel_left _ Nat.card_pos
  rw [h1] at hev
  rw [← orderOf_psiK hn hK h hσ₁ hgen]
  exact Nat.not_odd_iff_even.1 hev

theorem mem_Mb1_iff {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {i : Fin Tag.G2.rank} (hP : A.P1 = Pmin K i) (x : ↥A.K) :
    x ∈ A.Mb1 ↔ ∃ g ∈ Pmin K i, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ := by
  have := mem_Nj_iff hn hK h hP x
  exact this.trans ⟨fun ⟨g, hg, σ, hσ, hx⟩ => ⟨g, hP ▸ hg, σ, hσ, hx⟩,
    fun ⟨g, hg, σ, hσ, hx⟩ => ⟨g, hP ▸ hg, σ, hσ, hx⟩⟩

theorem mem_Mb2_iff {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {i : Fin Tag.G2.rank} (hP : A.P2 = Pmin K i) (x : ↥A.K) :
    x ∈ A.Mb2 ↔ ∃ g ∈ Pmin K i, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ := by
  have := mem_Nj_iff hn hK h hP x
  exact this.trans ⟨fun ⟨g, hg, σ, hσ, hx⟩ => ⟨g, hP ▸ hg, σ, hσ, hx⟩,
    fun ⟨g, hg, σ, hσ, hx⟩ => ⟨g, hP ▸ hg, σ, hσ, hx⟩⟩

end Assemble

end CFSG.Quasithin.H13.F431.G2.OutK
