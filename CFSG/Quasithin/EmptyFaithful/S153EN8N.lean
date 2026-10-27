module

public import CFSG.Quasithin.EmptyFaithful.S153EN8M
public import CFSG.Quasithin.EmptyFaithful.S153EN8L

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem exists_zpowers_eq_of_card_two {H : Subgroup G} (h : Nat.card H = 2) :
    ∃ z : G, Subgroup.zpowers z = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∃ z ∈ H, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : H = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at h
    omega
  obtain ⟨z, hzH, hz1⟩ := hne
  have hz2 : z ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥H) (x := ⟨z, hzH⟩)
    rw [h] at this
    simpa using congrArg Subtype.val this
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  exact ⟨z, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzH) (by rw [Nat.card_zpowers, hord, h])⟩

theorem le_one_of_three_pow_dvd (a n : ℕ) (h : 3 ^ a ∣ 6 * 2 ^ n) : a ≤ 1 := by
  by_contra ha
  have ha2 : 2 ≤ a := by omega
  have h9 : 9 ∣ 6 * 2 ^ n := by
    have : 3 ^ 2 ∣ 3 ^ a := pow_dvd_pow 3 ha2
    simpa using this.trans h
  have hcop : Nat.Coprime 9 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have := hcop.dvd_of_dvd_mul_right h9
  omega

section Final

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)

include h113 c B hdM hd3 hd1 hbd in
theorem centerOf_TJ : centerOf (T ⊓ Jgp M V₂ d) = Subgroup.zpowers B.a₁.val := by
  have hV := cx.c.hyp.elemAbelian
  have hV₁le : V₁ ≤ VZ T M := cx.c.decomp.le₁
  have hV₁T : V₁ ≤ T := hV₁le.trans cx.c.hyp.VZ_le_T
  have hV₁R : V₁ ≤ T ⊓ Jgp M V₂ d := le_inf hV₁T (V₁_le_Jgp h113 c B hdM hd3 hd1 hbd)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 (show x ∈ (T ⊓ Jgp M V₂ d) ⊓
      Subgroup.centralizer ((T ⊓ Jgp M V₂ d : Subgroup G) : Set G) from hx)
    have hxJ := (Subgroup.mem_inf.1 hxR).2
    have hxM : x ∈ M := (mem_Jgp.1 hxJ).1.1
    have hxV₁ : x ∈ V₁ := mem_V₁_of_centralizes h113 c B hdM hd3 hd1 hbd hxM hxJ (fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hxC w (hV₁R hw)).symm)
    obtain ⟨u, hu, rfl⟩ := exists_mem_commV₁ B hxV₁
    have hs : B.s₁ ∈ autI hV (T ⊓ Jgp M V₂ d) := by
      rw [autI_TJ c B hdM hd3 hd1 hbd]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 B.hF.sylow.s₁_mem_S).1, B.hF.sylow.s₁_mem_L⟩
    obtain ⟨j, hjR, hjs⟩ := (mem_autI hV).1 hs
    have hjcomm := Subgroup.mem_centralizer_iff.1 hxC j hjR
    have hfix : B.s₁ u = u := by
      refine IntMod.val_injective ?_
      rw [← hjs, convI_apply_val]
      calc (j : G) * u.val * (j : G)⁻¹ = (u.val * (j : G)) * (j : G)⁻¹ := by rw [← hjcomm]
        _ = u.val := by group
    rcases (B.hF.sylow.fix₁ u hu).1 hfix with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    have hvV₁ := vOf_mem B
    refine Subgroup.mem_inf.2 ⟨hV₁R hvV₁, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrJ := (Subgroup.mem_inf.1 hr).2
    have hrM : r ∈ M := (mem_Jgp.1 hrJ).1.1
    have hrN := mem_normalizer_V₁ B (show r ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨hrM, (mem_Jgp.1 hrJ).1.2⟩)
    have hrS : r ∈ Sgp153 T V₁ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hr).1, hrN⟩
    have hvZ : B.a₁.val ∈ ZS153 T M V₁ ⊓ V₁ := by
      rw [ZS_inf_V₁_eq B]
      exact Subgroup.mem_zpowers _
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hvZ).1).2 r hrS

include c B hdM hd3 hd1 hbd in
theorem isSylowThree_centralizer_v :
    IsSylowThreeOf153 (Subgroup.zpowers d) (Subgroup.centralizer ({B.a₁.val} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hvV₁ := vOf_mem B
  have hCM : Subgroup.centralizer ({B.a₁.val} : Set G) ≤ M :=
    cx.r46.centralizer_nonsingular _ (vOf_ne_one B) (Or.inl hvV₁)
  have hD3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hDp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD3)
  have hdv : d ∈ Subgroup.centralizer ({B.a₁.val} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact Subgroup.mem_centralizer_iff.1 (d_mem_M₂ B hdM hbd).2 _ hvV₁
  have hdle : Subgroup.zpowers d ≤ Subgroup.centralizer ({B.a₁.val} : Set G) :=
    Subgroup.zpowers_le.2 hdv
  obtain ⟨R, hdR, hRK, hRp, hRi⟩ := S153E.exists_sylow_ge (p := 3) (Q := Subgroup.zpowers d)
    (K := Subgroup.centralizer ({B.a₁.val} : Set G)) hDp hdle
  have hRM2 : R ≤ M ⊓ Subgroup.centralizer (V₁ : Set G) := by
    intro r hr
    have hrM : r ∈ M := hCM (hRK hr)
    obtain ⟨n, hn⟩ := hRp ⟨r, hr⟩
    have hn' : r ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hb1 : (barM cx hrM) ^ 3 ^ n = 1 := by
      have h1 : barM cx (M.pow_mem hrM (3 ^ n)) = 1 :=
        (barM_eq_one_iff _).2 (by rw [hn']; exact Subgroup.one_mem _)
      rwa [barM_pow] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hb1)
    have hodd : Odd (orderOf (barM cx hrM)) := by
      rw [hj]
      exact Odd.pow (by decide)
    have hcomm := Subgroup.mem_centralizer_iff.1 (hRK hr) B.a₁.val rfl
    have hfix : barM cx hrM B.a₁ = B.a₁ := by
      refine IntMod.val_injective ?_
      rw [barM_apply_val]
      calc r * B.a₁.val * r⁻¹ = (B.a₁.val * r) * r⁻¹ := by rw [← hcomm]
        _ = B.a₁.val := by group
    have hL₂ := mem_L₂_of_fix B.hS (barM_mem_autI hrM) hodd B.hF.sylow.a₁_mem B.hF.sylow.a₁_ne hfix
    exact (mem_M₂_iff B).2 ⟨hrM, hL₂⟩
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  obtain ⟨n, hn⟩ := (isPGroup_Q c.toChain15358).exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    Subgroup.card_dvd_of_le hRM2
  rw [ha, card_M₂ B, hn] at hdvd
  have ha1 : a ≤ 1 := le_one_of_three_pow_dvd a n hdvd
  have hge : Nat.card (Subgroup.zpowers d) ≤ Nat.card R := Subgroup.card_le_of_le hdR
  rw [hD3, ha] at hge
  have hRd : R = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge hdR ?_).symm
    rw [hD3, ha]
    interval_cases a <;> simp_all
  rw [hRd] at hRi
  exact ⟨hdle, hDp, hRi⟩

end Final

end S153EN8

namespace S153E

open CFSG.Quasithin.S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_n8 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}
    (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∃ (DM JM : Subgroup G) (v z : G), N8Data153 cx DM JM v z := by
  obtain ⟨B⟩ := nonempty_barModel cx
  obtain ⟨d, hdM, hd3, hd1, hbd, hsyl, hD3⟩ := exists_gen c B
  obtain ⟨z, hz⟩ := exists_zpowers_eq_of_card_two (S153E59.card_Z cx)
  refine ⟨Subgroup.zpowers d, Jgp M V₂ d, B.a₁.val, z, ?_⟩
  exact
    { DM_syl := hsyl
      card_DM := hD3
      v_gen := (ZS_inf_V₁_eq B).symm
      v_ne := vOf_ne_one B
      z_gen := hz
      DM_syl_v := isSylowThree_centralizer_v c B hdM hd3 hd1 hbd
      cent_eq := cent_eq_Jgp c B hdM hd3 hd1 hbd
      inf_eq := inf_eq_Jgp c B hdM hd3 hbd
      comm := fun a ha b hb => comm_Jgp ha hb
      JM_iso := nonempty_equiv_perm_four_Jgp h113 c B hdM hd3 hd1 hbd
      JM_core := pCoreOf_Jgp h113 c B hdM hd3 hd1 hbd
      transv := fun x hx hx2 hxV => transv_Jgp h113 c B hdM hd3 hd1 hbd hx hx2 hxV
      TJ_syl := isSylowTwoOf_TJ h113 c B hdM hd3 hd1 hbd
      TJ_dih := nonempty_dihedral_TJ h113 c B hdM hd3 hd1 hbd
      TJ_center := centerOf_TJ h113 c B hdM hd3 hd1 hbd }

end S153E

end CFSG.Quasithin
