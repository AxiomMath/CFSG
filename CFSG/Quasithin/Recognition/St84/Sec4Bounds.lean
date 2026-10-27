module

public import CFSG.Quasithin.Recognition.St84.Sec4Basic

import CFSG.Quasithin.Recognition.St84.Sec4Local

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

theorem one_le_of_hasB {i : ℤ} {d : ℕ} (hd : X.HasB i d) :
    1 ≤ d := by
  by_contra h
  have hd0 : d = 0 := by omega
  apply hd.2.1
  have hQadj : X.Q i ≤ X.Gi (i - 1) ⊓ X.Gi (i + 1) := X.Q_le_Gi_adj i
  have hZi : X.Z i ≤ X.Gi (i + 1) := (X.Z_le_Q i).trans (hQadj.trans inf_le_right)
  simpa [hd0] using hZi

private theorem fixSet_Qg (H : X.Sec4Hyp s r) :
    X.fixSet (X.Qg r) = Set.Icc (0 : ℤ) (r : ℤ) := by
  have hIcc : Set.Icc (0 : ℤ) (r : ℤ) ⊆ X.fixSet (X.Qg r) := by
    intro j hj
    rw [Set.mem_Icc] at hj
    intro q hq
    have hqarc : q ∈ X.arcStab 0 r := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    rw [Setup.arcStab, Fan86.mem_fixSet] at hqarc
    exact hqarc _ ⟨j, hj, rfl⟩
  have hrpos : (0 : ℤ) < r := H.longReg.1.1
  have hnotR : (r : ℤ) + 1 ∉ X.fixSet (X.Qg r) := by
    intro hmem
    have hstab : X.Qg r ≤ MulAction.stabilizer G (X.vert ((r : ℤ) + 1)) := by
      intro q hq
      exact MulAction.mem_stabilizer_iff.mpr (hmem q hq)
    exact ((X.rightTransAt_iff H hrpos).mp H.longReg.1.2.2.1) hstab
  have hnotL : (-1 : ℤ) ∉ X.fixSet (X.Qg r) := by
    intro hmem
    have hstab : X.Qg r ≤ MulAction.stabilizer G (X.vert (0 - 1)) := by
      intro q hq
      exact MulAction.mem_stabilizer_iff.mpr (hmem q hq)
    exact ((X.leftTransAt_iff H hrpos).mp H.longReg.1.2.1) hstab
  rcases fixSet_trichotomy X.hyp.isTree X.hyp.adj_smul X.hyp.finite_stab X.toTrack
    (X.Qg r) with huniv | hempty | ⟨a, b, hab, hfix⟩
  · exfalso
    have hmem : (r : ℤ) + 1 ∈ X.fixSet (X.Qg r) := by rw [huniv]; trivial
    exact hnotR hmem
  · exfalso
    have hmem : (0 : ℤ) ∈ X.fixSet (X.Qg r) := hIcc ⟨le_rfl, by positivity⟩
    rw [hempty] at hmem
    exact hmem
  · have h0mem : (0 : ℤ) ∈ Set.Icc a b := by
      have h := hIcc ⟨le_rfl, by positivity⟩
      rwa [hfix] at h
    have hrmem : (r : ℤ) ∈ Set.Icc a b := by
      have h := hIcc ⟨by positivity, le_rfl⟩
      rwa [hfix] at h
    rw [hfix] at hnotR hnotL
    rw [Set.mem_Icc] at h0mem hrmem
    rw [Set.mem_Icc] at hnotR hnotL
    have ha0 : a = 0 := by
      have h : ¬ a ≤ -1 := fun ha => hnotL ⟨ha, by omega⟩
      omega
    have hbr : b = r := by
      have h : ¬ (r : ℤ) + 1 ≤ b := fun hb => hnotR ⟨by omega, hb⟩
      omega
    rw [hfix, ha0, hbr]

private theorem trans_of_le_sup_Q {M : Subgroup G} {c : ℤ}
    (hMN : M ≤ Subgroup.normalizer (X.Q c : Set G))
    (hLle : X.L c ≤ M ⊔ X.Q c) :
    ∀ a b : V, Γ.Adj (X.vert c) a → Γ.Adj (X.vert c) b → ∃ g ∈ M, g • a = b := by
  intro a b ha hb
  obtain ⟨g, hgL, hgab⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert c)).trans a b ha hb
  have hgM : g ∈ M ⊔ X.Q c := hLle hgL
  have hcoe : (↑(M ⊔ X.Q c) : Set G) = (M : Set G) * (X.Q c : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right M (X.Q c) hMN
  have hg' : g ∈ (M : Set G) * (X.Q c : Set G) := by rwa [← hcoe]
  obtain ⟨h, hhM, q, hqQ, hhq⟩ := hg'
  refine ⟨h, hhM, ?_⟩
  have hqfix : q • a = a := X.Q_fixes_neighbors_vert c a ha q hqQ
  calc h • a = (h * q) • a := by rw [mul_smul, hqfix]
    _ = g • a := by rw [show h * q = g from hhq]
    _ = b := hgab

private theorem center_of_reflection (H : X.Sec4Hyp s r) {P W₁ W₂ : Subgroup G} {m n c : ℤ}
    (hKP : X.K ≤ Subgroup.normalizer (P : Set G)) (hfix : X.fixSet P = Set.Icc m n)
    (hmn : m ≤ n)
    (h₁ : IsPGroup 2 W₁) (h₂ : IsPGroup 2 W₂)
    (hK₁ : X.K ≤ Subgroup.normalizer (W₁ : Set G))
    (hK₂ : X.K ≤ Subgroup.normalizer (W₂ : Set G))
    (hP₁ : W₁ ≤ Subgroup.normalizer (P : Set G))
    (hP₂ : W₂ ≤ Subgroup.normalizer (P : Set G))
    (hc₁ : W₁ ≤ X.Gi c ⊓ X.Gi (c - 1)) (hc₁' : ¬ W₁ ≤ X.Gi (c + 1))
    (hc₂ : W₂ ≤ X.Gi c ⊓ X.Gi (c + 1)) (hc₂' : ¬ W₂ ≤ X.Gi (c - 1)) :
    m + n = 2 * c := by
  set M : Subgroup G := (W₁ ⊔ W₂) ⊔ X.K with hM
  have hKH : X.K ≤ M := le_sup_right
  have hW1M : W₁ ≤ M := le_sup_left.trans le_sup_left
  have hW2M : W₂ ≤ M := le_sup_right.trans le_sup_left
  have hMGi : M ≤ X.Gi c :=
    sup_le (sup_le (hc₁.trans inf_le_left) (hc₂.trans inf_le_left)) (X.K_le_Gi c)
  have hMN : M ≤ Subgroup.normalizer (X.Q c : Set G) :=
    hMGi.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi c))
  have hleft : Γ.Adj (X.vert c) (X.vert (c - 1)) := X.toTrack.adj_pred c
  have hright : Γ.Adj (X.vert c) (X.vert (c + 1)) := X.adj c
  have hW1edge : W₁ ≤ X.edgeSylow (c - 1) :=
    X.le_edgeSylow_of_le_inf (c - 1) h₁ (by
      rw [show c - 1 + 1 = c by ring]
      exact le_inf (fun x hx => (hc₁ hx).2) (fun x hx => (hc₁ hx).1))
  have hW2edge : W₂ ≤ X.edgeSylow c := X.le_edgeSylow_of_le_inf c h₂ hc₂
  have hQGi : X.Q c ≤ X.Gi (c - 1) := (X.Q_le_Gi_adj c).trans inf_le_left
  have hQGi' : X.Q c ≤ X.Gi (c + 1) := (X.Q_le_Gi_adj c).trans inf_le_right
  have hW1Q : W₁ ⊔ X.Q c = X.edgeSylow (c - 1) := by
    have h := X.sup_Q_eq_edgeSylow_of_gen (c - 1) (inf_le_left.trans hK₁) hW1edge
      (fun hle => hc₁' ((show W₁ ≤ X.Q c by
        simpa [show c - 1 + 1 = c by ring] using hle).trans hQGi'))
    simpa [show c - 1 + 1 = c by ring] using h
  have hW2Q : W₂ ⊔ X.Q c = X.edgeSylow c :=
    X.sup_Q_eq_edgeSylow_of_left_gen c (inf_le_left.trans hK₂) hW2edge
      (fun hle => hc₂' (hle.trans hQGi))
  have hLle : X.L c ≤ M ⊔ X.Q c := by
    refine (X.edgeSylow_sup_edgeSylow c).ge.trans ?_
    refine sup_le ?_ ?_
    · rw [← hW1Q]
      exact sup_le (hW1M.trans le_sup_left) le_sup_right
    · rw [← hW2Q]
      exact sup_le (hW2M.trans le_sup_left) le_sup_right
  have htr := X.trans_of_le_sup_Q hMN hLle
  obtain ⟨x, hxMN, hxmove⟩ := X.exists_normalizer_K_move (i := c) (H := M) hKH hMGi htr
    (w := X.vert (c - 1)) (w' := X.vert (c + 1)) hleft hright
    (fun k hk => X.K_fix k hk (c - 1)) (fun k hk => X.K_fix k hk (c + 1))
  have hxM : x ∈ M := hxMN.1
  have hxN : x ∈ Subgroup.normalizer (X.K : Set G) := hxMN.2
  have hxrefl := X.reflection_of_smul_succ H ⟨hMGi hxM, hxN⟩ hxmove
  have hPnorm : M ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (sup_le hP₁ hP₂) hKP
  have hPconj : conjSub x P = P := by
    have h := hPnorm hxM
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
  have hxjs : ∀ j : ℤ, x • X.vert j = X.vert (2 * c - j) := by
    intro j
    have h := hxrefl (j - c)
    rwa [show c + (j - c) = j by ring, show c - (j - c) = 2 * c - j by ring] at h
  have hsymm := X.mem_fixSet_reflection_iff hPconj hxjs
  have hsm : 2 * c - m ∈ Set.Icc m n := by
    have h := (hsymm m).mp (by rw [hfix]; exact ⟨le_rfl, hmn⟩)
    rwa [hfix] at h
  have hsn : 2 * c - n ∈ Set.Icc m n := by
    have h := (hsymm n).mp (by rw [hfix]; exact ⟨hmn, le_rfl⟩)
    rwa [hfix] at h
  rw [Set.mem_Icc] at hsm hsn
  omega

private theorem two_mul_le_of_hasB (H : X.Sec4Hyp s r) {i : ℤ} {d : ℕ} (hd : X.HasB i d) :
    2 * d ≤ r := by
  have hZ2 : IsPGroup 2 (X.Z i) := (pCoreOf_isPGroup' (X.Gi i)).to_le (X.Z_le_Q i)
  have hne : X.Z i ≠ ⊥ := X.Z_ne_bot_of i (X.Q_ne_bot H.char i)
  have hfix := X.fixSet_Z i hd
  have hle : X.Z i ≤
      X.arcStab (i - (d : ℤ)) ((i - (d : ℤ)) + ((2 * d : ℕ) : ℤ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [hfix]
    rw [Set.mem_Icc] at hj ⊢
    push_cast at hj ⊢
    omega
  have := X.le_r_of_fixes H hZ2 hne hle
  simpa using this

private theorem eq_two_mul_of_hasB (H : X.Sec4Hyp s r) {i : ℤ} {d : ℕ}
    (hd : X.HasB i d) (hi : 0 < i) (hir : i + 2 * (d : ℤ) < (r : ℤ)) :
    (r : ℤ) = 2 * (i + (d : ℤ)) := by
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  have hr : (0 : ℤ) < (r : ℤ) := H.longReg.1.1
  set c : ℤ := i + (d : ℤ) with hcdef
  have hc1 : X.Z i ≤ X.Gi c ⊓ X.Gi (c - 1) := by
    refine le_inf ?_ ?_
    · simpa [hcdef] using hd.1 (d : ℤ) (by simp)
    · have h := hd.1 ((d : ℤ) - 1) (by omega)
      rwa [show i + ((d : ℤ) - 1) = c - 1 by rw [hcdef]; ring] at h
  have hc1' : ¬ X.Z i ≤ X.Gi (c + 1) := by
    simpa [hcdef] using hd.2.1
  have hdW2 : X.HasB (i + 2 * (d : ℤ)) d :=
    (X.hasB_iff_of_even (i := i + 2 * (d : ℤ)) (j := i)
      (show Even (i + 2 * (d : ℤ) - i) by exact ⟨(d : ℤ), by ring⟩) d).mpr hd
  have hc2 : X.Z (i + 2 * (d : ℤ)) ≤ X.Gi c ⊓ X.Gi (c + 1) := by
    refine le_inf ?_ ?_
    · have h := hdW2.1 (-(d : ℤ)) (by simp)
      rwa [show i + 2 * (d : ℤ) + (-(d : ℤ)) = c by rw [hcdef]; ring] at h
    · have h := hdW2.1 (1 - (d : ℤ)) (by omega)
      rwa [show i + 2 * (d : ℤ) + (1 - (d : ℤ)) = c + 1 by rw [hcdef]; ring] at h
  have hc2' : ¬ X.Z (i + 2 * (d : ℤ)) ≤ X.Gi (c - 1) := by
    have h := hdW2.2.2
    rwa [show i + 2 * (d : ℤ) - (d : ℤ) - 1 = c - 1 by rw [hcdef]; ring] at h
  have hKP : X.K ≤ Subgroup.normalizer (X.Qg r : Set G) :=
    (X.K_le_GT.trans (X.GT_le_arcStab 0 r)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hW1 : IsPGroup 2 (X.Z i) := (pCoreOf_isPGroup' (X.Gi i)).to_le (X.Z_le_Q i)
  have hW2 : IsPGroup 2 (X.Z (i + 2 * (d : ℤ))) :=
    (pCoreOf_isPGroup' (X.Gi (i + 2 * (d : ℤ)))).to_le (X.Z_le_Q _)
  have hK1 : X.K ≤ Subgroup.normalizer (X.Z i : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i k (X.K_le_Gi i hk))
  have hK2 : X.K ≤ Subgroup.normalizer (X.Z (i + 2 * (d : ℤ)) : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal _ k (X.K_le_Gi _ hk))
  have hcent : ∀ a : ℤ, 0 < a → a < (r : ℤ) →
      X.Z a ≤ Subgroup.centralizer (X.Qg r : Set G) := by
    intro a ha0 har
    have hQ := X.pCoreOf_arcStab_le_Q_of_lt_of_lt ha0 har
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (X.Z_le_center a hz).2) q (hQ hq)
  have hP1 : X.Z i ≤ Subgroup.normalizer (X.Qg r : Set G) :=
    (hcent i hi (by omega)).trans (Subgroup.centralizer_le_normalizer _)
  have hP2 : X.Z (i + 2 * (d : ℤ)) ≤ Subgroup.normalizer (X.Qg r : Set G) :=
    (hcent (i + 2 * (d : ℤ)) (by omega) hir).trans (Subgroup.centralizer_le_normalizer _)
  have hmain := X.center_of_reflection H hKP (X.fixSet_Qg H) (by omega)
    hW1 hW2 hK1 hK2 hP1 hP2 hc1 hc1' hc2 hc2'
  rw [hcdef] at hmain
  omega

theorem hasB_one_bounds (H : X.Sec4Hyp s r) {d : ℕ} (hd : X.HasB 1 d) :
    2 * d ≤ r ∧ r ≤ 2 * d + 2 := by
  refine ⟨X.two_mul_le_of_hasB H hd, ?_⟩
  by_contra hle
  rw [not_le] at hle
  have hgt : ((2 * d + 2 : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast hle
  push_cast at hgt
  have hir : (1 : ℤ) + 2 * (d : ℤ) < (r : ℤ) := by omega
  have hmain := X.eq_two_mul_of_hasB H hd (by norm_num) hir
  omega

theorem hasB_zero_bounds (H : X.Sec4Hyp s r) {d : ℕ} (hd : X.HasB 0 d) :
    2 * d ≤ r ∧ r ≤ 2 * d + 4 := by
  refine ⟨X.two_mul_le_of_hasB H hd, ?_⟩
  by_contra hle
  rw [not_le] at hle
  have hgt : ((2 * d + 4 : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast hle
  push_cast at hgt
  have hd2 : X.HasB 2 d :=
    (X.hasB_iff_of_even (i := 2) (j := 0)
      (show Even (2 - 0) by exact ⟨(1 : ℤ), by norm_num⟩) d).mpr hd
  have hir : (2 : ℤ) + 2 * (d : ℤ) < (r : ℤ) := by omega
  have hmain := X.eq_two_mul_of_hasB H hd2 (by norm_num) hir
  omega

theorem exists_reflection_oTwoRes (H : X.Sec4Hyp s r) (i : ℤ) :
    ∃ t ∈ oTwoRes (X.L i) ⊓ Subgroup.normalizer (X.K : Set G),
      (∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) ∧ t ^ 2 ∈ X.K := by
  set R : Subgroup G := oTwoRes (X.L i) with hR
  set M : Subgroup G := R ⊔ X.K with hM
  have hKH : X.K ≤ M := le_sup_right
  have hRM : R ≤ M := le_sup_left
  have hMGi : M ≤ X.Gi i :=
    sup_le ((oTwoRes_le (X.L i)).trans (X.L_le_Gi i)) (X.K_le_Gi i)
  have htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b →
      ∃ g ∈ M, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgR, hgab⟩ := oTwoRes_trans X.hyp (X.adj i) a b ha hb
    exact ⟨g, hRM hgR, hgab⟩
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hright : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.adj i
  obtain ⟨x, hxMN, hxmove⟩ := X.exists_normalizer_K_move (i := i) (H := M) hKH hMGi htr
    (w := X.vert (i - 1)) (w' := X.vert (i + 1)) hleft hright
    (fun k hk => X.K_fix k hk (i - 1)) (fun k hk => X.K_fix k hk (i + 1))
  have hxM : x ∈ M := hxMN.1
  have hxN : x ∈ Subgroup.normalizer (X.K : Set G) := hxMN.2
  have hxrefl := X.reflection_of_smul_succ H ⟨hMGi hxM, hxN⟩ hxmove
  have hLnorm : X.Gi i ≤ Subgroup.normalizer (R : Set G) := by
    have hLN : X.Gi i ≤ Subgroup.normalizer (X.L i : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi i)).mp
        (X.hyp.isLocL2_oTwoPrime (X.vert i)).normal
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g R = R
    rw [show R = oTwoRes (X.L i) from rfl, conjSub_oTwoRes]
    have hconj : conjSub g (X.L i) = X.L i := by
      have h := hLN hg
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    rw [hconj]
  have hKN : X.K ≤ Subgroup.normalizer (R : Set G) := (X.K_le_Gi i).trans hLnorm
  have hmem' : x ∈ X.K ⊔ R := by
    rw [sup_comm]
    exact hxM
  have hxset : (x : G) ∈ (↑(X.K ⊔ R) : Set G) := hmem'
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X.K R hKN] at hxset
  obtain ⟨k, hkK, s, hsR, hks⟩ := hxset
  have hseq : s = k⁻¹ * x := by rw [← hks]; group
  have hsN : s ∈ Subgroup.normalizer (X.K : Set G) := by
    rw [hseq]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (X.K.inv_mem hkK)) hxN
  have hrefl : ∀ m : ℤ, s • X.vert (i + m) = X.vert (i - m) := by
    intro m
    calc s • X.vert (i + m) = (k⁻¹ * x) • X.vert (i + m) := by rw [hseq]
      _ = k⁻¹ • (x • X.vert (i + m)) := by rw [mul_smul]
      _ = k⁻¹ • X.vert (i - m) := by rw [hxrefl]
      _ = X.vert (i - m) := X.K_fix k⁻¹ (X.K.inv_mem hkK) (i - m)
  have hs2K : s ^ 2 ∈ X.K := by
    have hs2GT : s ^ 2 ∈ X.GT := by
      rw [Setup.GT, Fan86.mem_fixSet]
      rintro v ⟨j, rfl⟩
      have h1 : s • X.vert j = X.vert (2 * i - j) := by
        have h := hrefl (j - i)
        rwa [show i + (j - i) = j by ring, show i - (j - i) = 2 * i - j by ring] at h
      have h2 : s • X.vert (2 * i - j) = X.vert j := by
        have h := hrefl (i - j)
        rwa [show i + (i - j) = 2 * i - j by ring, show i - (i - j) = j by ring] at h
      rw [pow_two, mul_smul, h1, h2]
    rw [X.GT_eq_K_of_odd H] at hs2GT
    exact hs2GT
  exact ⟨s, ⟨hsR, hsN⟩, hrefl, hs2K⟩

end Setup

end CFSG.Quasithin.St84
