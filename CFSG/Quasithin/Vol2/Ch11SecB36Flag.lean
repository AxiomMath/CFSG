module

public import CFSG.Quasithin.Vol2.Ch11SecB36Setup
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_sup_centralizer_of_pow_U (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4)
    (hyp : Hyp11 G T L I n) {U : Subgroup G} (hVU : fsuV T I ≤ U)
    (hdisj : ∀ y ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U : Set G),
      y ∈ Subgroup.normalizer (fsuV T I : Set G) ∨ L = ⁅L, thompsonJ T⁆ ∨ fsuV T I = VM T L I)
    {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U : Set G))
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ 2 ^ n - 1)
    (hxp : x ^ p ∈ Subgroup.centralizer (U : Set G)) :
    x ∈ L ⊔ Subgroup.centralizer (U : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer (U : Set G) with hCdef
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ a) b :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hb)
  set u := Nat.gcdA (p ^ a) b
  set v := Nat.gcdB (p ^ a) b
  have hbez : ((p ^ a : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by
    have := Nat.gcd_eq_gcd_ab (p ^ a) b
    rw [hcop] at this
    exact_mod_cast this.symm
  have hxe : x = (x ^ (p ^ a)) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hbez, zpow_one]
  have hC1 : x ^ (p ^ a) ∈ C := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h1 : x ∈ Subgroup.zpowers (x ^ p) := by
        have hcp : Nat.Coprime p (orderOf x) := by
          rw [hab, pow_zero, one_mul]
          exact (Nat.Prime.coprime_iff_not_dvd hp).2 hb
        exact A4.mem_zpowers_pow_of_coprime hcp
      simpa using (Subgroup.zpowers_le.mpr hxp) h1
    · have : x ^ (p ^ a) = (x ^ p) ^ (p ^ (a - 1)) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega
      rw [this]
      exact C.pow_mem hxp _
  have hpord : (x ^ b) ^ (p ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hL1 : x ^ b ∈ L := by
    have h04 := h1104 G T L I n hyp
    have hxM : x ^ b ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hx.1 b
    have hres : p ≠ 3 ∨ ¬ KindSL3 L (fsuV T I) n → x ^ b ∈ L := by
      intro hcase
      have hcond : (KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ p ∣ 2 ^ (2 * n) - 1 ∨
          KindSL3 L (fsuV T I) n ∧ p ∣ 2 ^ n - 1 ∧ 3 < p := by
        have hpd2 : p ∣ 2 ^ (2 * n) - 1 := by
          refine hpd.trans ⟨2 ^ n + 1, ?_⟩
          have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          have h3 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
          rw [two_mul, pow_add]
          zify [h1, h3]
          ring
        have hp2 : p ≠ 2 := by
          rintro rfl
          have h4 : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hyp.one_lt
          have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := hyp.one_lt; omega)
          generalize 2 ^ n = y at h4 h2 hpd
          omega
        rcases kind_cases h1102 hyp with hk | hk | hk
        · rcases hcase with h3 | h3
          · refine Or.inr ⟨hk, hpd, ?_⟩
            have := hp.two_le
            omega
          · exact absurd hk h3
        · exact Or.inl ⟨Or.inl hk, hpd2⟩
        · exact Or.inl ⟨Or.inr hk, hpd2⟩
      rw [← h04.1 p hp hcond]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hpord)
      exact Subgroup.subset_closure ⟨hxM, j, hj⟩
    by_cases hcase : p ≠ 3 ∨ ¬ KindSL3 L (fsuV T I) n
    · exact hres hcase
    push Not at hcase
    obtain ⟨rfl, hk⟩ := hcase
    have hev : Even n := even_of_three_dvd hpd
    have hno3 : ∀ y ∈ Subgroup.normalizer (L : Set G), y ∈ C → orderOf y = 3 → False := by
      intro y hyM hyC hy3
      have hyL := h04.2 hk hev y hyM hy3
        (hdisj y ⟨hyM, Subgroup.centralizer_le_normalizer _ hyC⟩)
      have hyO : y ∈ pCoreOf 2 L := by
        rw [← centralizer_eq_pCoreOf h1102 hyp]
        exact ⟨hyL, Subgroup.centralizer_le hVU hyC⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨y, hyO⟩
      have hj' : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h3 : 3 ∣ 2 ^ j := hy3 ▸ orderOf_dvd_of_pow_eq_one hj'
      exact absurd (Nat.le_of_dvd two_pos (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
    have hcube : (x ^ b) ^ 3 = 1 := by
      by_contra hne
      set w := (x ^ b) ^ 3 with hwdef
      have hwC : w ∈ C := by
        rw [hwdef, ← pow_mul, mul_comm, pow_mul]
        exact C.pow_mem hxp b
      have hwM : w ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hxM 3
      have hw3 : w ^ (3 ^ a) = 1 := by
        rw [hwdef, ← pow_mul, mul_comm, pow_mul, hpord, one_pow]
      have hw1 : orderOf w ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hw1
      have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hq.dvd_of_dvd_pow (hqd.trans (orderOf_dvd_of_pow_eq_one hw3)))
      subst hq3
      exact hno3 _ (Subgroup.pow_mem _ hwM _) (C.pow_mem hwC _)
        (orderOf_pow_orderOf_div (orderOf_pos w).ne' hqd)
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hcube) with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact L.one_mem
    · exact h04.2 hk hev _ hxM h3 (hdisj _ ⟨hxM, Subgroup.pow_mem _ hx.2 b⟩)
  rw [hxe]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (C.zpow_mem hC1 u))
    (Subgroup.mem_sup_left (L.zpow_mem hL1 v))

theorem flag36_of (hNF : NatFacts) (hG2o : FactG2DerivedOrder) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (hyp : Hyp11 G T L I n)
    {V₁ V₂ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hk : KindSL3 L (fsuV T I) n) (hVM2 : VMTwoNatural T L I n)
    (hLJ : L = ⁅L, thompsonJ T⁆) : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n := by
  have hR := isTwoReducedIn_VM h1103 hyp
  have hMN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (VM T L I : Set G) := hR.2.1
  have hNM := normalizer_VM_le h331 h1103 hyp
  have hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases (h1103 G T L I n hyp).2.2.1 with ⟨h0, -⟩ | ⟨hk', -⟩
    · exact h0
    · rcases hk' with hk' | hk'
      · exact (kind_not_SL3_Sp4 (by have := hyp.one_lt; omega) hk hk').elim
      · exact (kind_not_SL3_G2 hG2o hyp.one_lt hk hk').elim
  exact
    { toFlag24 := flag24_of hNF h331 h1102 hyp hV₁ hV₂ (Or.inl hk)
      sl3 := hk
      cV := hcV
      elemW := hR.2.2.1
      le_W := le_conjClosure _ _
      L_le_W := Subgroup.le_normalizer.trans hMN
      T_le_W := hyp.normal.trans hMN
      two := hVM2
      normalizer_le_W := inf_le_right.trans hNM
      odd := fun x hx p hp hpd hxp => mem_sup_centralizer_of_pow_U h1102 h1104 hyp
        (le_conjClosure _ _) (fun _ _ => Or.inr (Or.inl hLJ)) ⟨hNM hx.2, hx.2⟩ hp hpd hxp }

theorem autI_top_eq_VM (h331 : Stmt3_3_1) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n)
    (hW : IsElemAbelian 2 (VM T L I)) :
    autI hW ⊤ = autI hW (Subgroup.normalizer (L : Set G)) := by
  refine le_antisymm ?_ (autI_mono hW le_top)
  intro φ hφ
  obtain ⟨g, -, hg⟩ := (mem_autI hW).mp hφ
  exact (mem_autI hW).mpr ⟨g, normalizer_VM_le h331 h1103 hyp g.2, hg⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
