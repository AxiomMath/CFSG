module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [CommGroup V] [Finite V]

theorem s16c167_e9_comps (hsq : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    {P : Subgroup (MulAut V)} (hP9 : Nat.card ↥P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ A B : Subgroup V, Nat.card ↥A = 4 ∧ Nat.card ↥B = 4 ∧ A ⊓ B = ⊥ ∧ A ⊔ B = ⊤ ∧
      (∃ g ∈ P, A = fixV (Subgroup.zpowers g)) ∧ (∃ h ∈ P, B = fixV (Subgroup.zpowers h)) ∧
      ∀ R : Subgroup (MulAut V), R ≤ P → Nat.card ↥(fixV R) = 4 → fixV R = A ∨ fixV R = B := by
  obtain ⟨g, hgP, h, hhP, hg1, hh1, hg4, hh4, hinf, hsup, hgen⟩ :=
    exists_pair hP9 hP3 hPc hV hsq
  have hg3 : g ^ 3 = 1 := hP3 g hgP
  have hh3 : h ^ 3 = 1 := hP3 h hhP
  set A : Subgroup V := fixV (Subgroup.zpowers g) with hA
  set B : Subgroup V := fixV (Subgroup.zpowers h) with hB
  have hAeq : A = fixOf g := by
    rw [hA]
    ext v
    exact mem_fixV_zpowers_iff_apply.trans mem_fixOf.symm
  have hBeq : B = fixOf h := by
    rw [hB]
    ext v
    exact mem_fixV_zpowers_iff_apply.trans mem_fixOf.symm
  have hAcard : Nat.card ↥A = 4 := by rw [hAeq]; exact hg4
  have hBcard : Nat.card ↥B = 4 := by rw [hBeq]; exact hh4
  have hinf' : A ⊓ B = ⊥ := by rw [hAeq, hBeq]; exact hinf
  have hsup' : A ⊔ B = ⊤ := by rw [hAeq, hBeq]; exact hsup
  have hgA : ∀ a ∈ A, g a = a := fun a ha => mem_fixV_zpowers_iff_apply.mp (hA ▸ ha)
  have hhB : ∀ b ∈ B, h b = b := fun b hb => mem_fixV_zpowers_iff_apply.mp (hB ▸ hb)
  have hPA : ∀ x ∈ P, ∀ a ∈ A, x a ∈ A := by
    intro x hxP a ha
    rw [hA, mem_fixV_zpowers_iff_apply]
    have hcomm : g * x = x * g := (hPc x hxP g hgP).symm
    calc
      g (x a) = (g * x) a := rfl
      _ = (x * g) a := by rw [hcomm]
      _ = x (g a) := rfl
      _ = x a := by rw [hgA a ha]
  have hPB : ∀ x ∈ P, ∀ b ∈ B, x b ∈ B := by
    intro x hxP b hb
    rw [hB, mem_fixV_zpowers_iff_apply]
    have hcomm : h * x = x * h := (hPc x hxP h hhP).symm
    calc
      h (x b) = (h * x) b := rfl
      _ = (x * h) b := by rw [hcomm]
      _ = x (h b) := rfl
      _ = x b := by rw [hhB b hb]
  have hgpowA : ∀ i : ℕ, ∀ a ∈ A, (g ^ i) a = a := by
    intro i a ha
    exact mem_fixV.mp (hA ▸ ha) (g ^ i) ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) i)
  have hhpowB : ∀ j : ℕ, ∀ b ∈ B, (h ^ j) b = b := by
    intro j b hb
    exact mem_fixV.mp (hB ▸ hb) (h ^ j) ((Subgroup.zpowers h).pow_mem (Subgroup.mem_zpowers h) j)
  have huniq : ∀ a1 ∈ A, ∀ b1 ∈ B, ∀ a2 ∈ A, ∀ b2 ∈ B,
      a1 * b1 = a2 * b2 → a1 = a2 ∧ b1 = b2 := by
    intro a1 ha1 b1 hb1 a2 ha2 b2 hb2 heq
    have hmem : a2⁻¹ * a1 ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem ha2) ha1, ?_⟩
      have h1 : a2⁻¹ * a1 = b2 * b1⁻¹ := by
        have h := congrArg (fun z => a2⁻¹ * z * b1⁻¹) heq
        simpa [mul_assoc] using h
      rw [h1]
      exact B.mul_mem hb2 (B.inv_mem hb1)
    rw [hinf', Subgroup.mem_bot] at hmem
    have haeq : a1 = a2 := (inv_mul_eq_one.mp hmem).symm
    subst a1
    exact ⟨rfl, mul_left_cancel heq⟩
  have key : ∀ x ∈ P, (∃ a ∈ A, x a ≠ a) → (∃ b ∈ B, x b ≠ b) →
      fixV (Subgroup.zpowers x) = ⊥ := by
    intro x hxP hxA hxB
    obtain ⟨i, j, rfl⟩ := hgen x hxP
    have hi3 : ¬ 3 ∣ i := by
      rintro ⟨k, rfl⟩
      obtain ⟨b, hb, hbne⟩ := hxB
      apply hbne
      rw [pow_mul, hg3, one_pow, one_mul]
      exact hhpowB j b hb
    have hj3 : ¬ 3 ∣ j := by
      rintro ⟨k, rfl⟩
      obtain ⟨a, ha, hane⟩ := hxA
      apply hane
      rw [pow_mul, hh3, one_pow, mul_one]
      exact hgpowA i a ha
    have hpow_fix : ∀ {y : MulAut V} {n : ℕ} {c : V}, y ^ 3 = 1 → y ≠ 1 → ¬ 3 ∣ n →
        (y ^ n) c = c → y c = c := by
      intro y n c hy3 hy1 hn hyc
      have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
      have hmod : y ^ n = y ^ (n % 3) := by
        rw [← hord]
        exact (pow_mod_orderOf y n).symm
      have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by
        have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have hne : n % 3 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
        omega
      rcases hn3 with h1 | h2
      · have hy : y ^ n = y := by simpa [hmod, h1]
        rwa [hy] at hyc
      · have hy : y ^ n = y ^ 2 := by simpa [hmod, h2]
        have h2c : (y ^ 2) c = c := by rwa [hy] at hyc
        have h3c : y ((y ^ 2) c) = c := by
          show y (y (y c)) = c
          exact apply_cube_c4 hy3 c
        rw [h2c] at h3c
        exact h3c
    rw [eq_bot_iff]
    intro v hv
    rw [mem_fixV_zpowers_iff_apply] at hv
    have hvs : v ∈ A ⊔ B := by rw [hsup']; exact Subgroup.mem_top v
    rw [Subgroup.mem_sup] at hvs
    obtain ⟨a, ha, b, hb, hab⟩ := hvs
    have hxa : (g ^ i * h ^ j) a = (h ^ j) a := by
      show (g ^ i) ((h ^ j) a) = (h ^ j) a
      exact hgpowA i ((h ^ j) a) (hPA (h ^ j) (P.pow_mem hhP j) a ha)
    have hxb : (g ^ i * h ^ j) b = (g ^ i) b := by
      show (g ^ i) ((h ^ j) b) = (g ^ i) b
      rw [hhpowB j b hb]
    have heq : (g ^ i * h ^ j) a * (g ^ i * h ^ j) b = a * b := by
      calc
        (g ^ i * h ^ j) a * (g ^ i * h ^ j) b = (g ^ i * h ^ j) (a * b) :=
          (map_mul (g ^ i * h ^ j) a b).symm
        _ = (g ^ i * h ^ j) v := by rw [hab]
        _ = v := hv
        _ = a * b := hab.symm
    have hxaa : (g ^ i * h ^ j) a = a :=
      (huniq ((g ^ i * h ^ j) a) (hPA (g ^ i * h ^ j) hxP a ha)
        ((g ^ i * h ^ j) b) (hPB (g ^ i * h ^ j) hxP b hb) a ha b hb heq).1
    have hxbb : (g ^ i * h ^ j) b = b :=
      (huniq ((g ^ i * h ^ j) a) (hPA (g ^ i * h ^ j) hxP a ha)
        ((g ^ i * h ^ j) b) (hPB (g ^ i * h ^ j) hxP b hb) a ha b hb heq).2
    have hja : (h ^ j) a = a := hxa.symm.trans hxaa
    have hha : h a = a := hpow_fix hh3 hh1 hj3 hja
    have haB : a ∈ B := by
      rw [hBeq]
      exact mem_fixOf.mpr hha
    have ha1 : a = 1 := by
      have hmem : a ∈ A ⊓ B := ⟨ha, haB⟩
      rwa [hinf', Subgroup.mem_bot] at hmem
    have hib : (g ^ i) b = b := hxb.symm.trans hxbb
    have hgb : g b = b := hpow_fix hg3 hg1 hi3 hib
    have hbA : b ∈ A := by
      rw [hAeq]
      exact mem_fixOf.mpr hgb
    have hb1 : b = 1 := by
      have hmem : b ∈ A ⊓ B := ⟨hbA, hb⟩
      rwa [hinf', Subgroup.mem_bot] at hmem
    simpa [← hab, ha1, hb1]
  refine ⟨A, B, hAcard, hBcard, hinf', hsup', ⟨g, hgP, hA⟩, ⟨h, hhP, hB⟩, ?_⟩
  intro R hRP hcardR
  have htriv : ∀ x ∈ R, (∀ a ∈ A, x a = a) ∨ (∀ b ∈ B, x b = b) := by
    intro x hxR
    by_contra hcon
    push Not at hcon
    have hxP : x ∈ P := hRP hxR
    have hbot : fixV (Subgroup.zpowers x) = ⊥ := key x hxP hcon.1 hcon.2
    have hle : fixV R ≤ fixV (Subgroup.zpowers x) := by
      intro v hv
      rw [mem_fixV] at hv ⊢
      intro y hy
      exact hv y (Subgroup.zpowers_le.mpr hxR hy)
    have hcardle : Nat.card ↥(fixV R) ≤ Nat.card ↥(fixV (Subgroup.zpowers x)) :=
      Subgroup.card_le_of_le hle
    rw [hbot, Subgroup.card_bot] at hcardle
    omega
  have htrivAorB : (∀ x ∈ R, ∀ a ∈ A, x a = a) ∨ (∀ x ∈ R, ∀ b ∈ B, x b = b) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x, hxR, hxA⟩, ⟨y, hyR, hyB⟩⟩ := hcon
    have hxP : x ∈ P := hRP hxR
    have hyP : y ∈ P := hRP hyR
    have hxB : ∀ b ∈ B, x b = b := by
      rcases htriv x hxR with h | h
      · obtain ⟨a, ha, hane⟩ := hxA
        exact absurd (h a ha) hane
      · exact h
    have hyA : ∀ a ∈ A, y a = a := by
      rcases htriv y hyR with h | h
      · exact h
      · obtain ⟨b, hb, hbne⟩ := hyB
        exact absurd (h b hb) hbne
    have hzR : x * y ∈ R := R.mul_mem hxR hyR
    rcases htriv (x * y) hzR with hzA | hzB
    · obtain ⟨a, ha, hane⟩ := hxA
      apply hane
      have h1 : x (y a) = a := hzA a ha
      rwa [hyA a ha] at h1
    · obtain ⟨b, hb, hbne⟩ := hyB
      have h1 : x (y b) = b := hzB b hb
      have h2 : x (y b) = y b := hxB (y b) (hPB y hyP b hb)
      exact hbne (h2.symm.trans h1)
  rcases htrivAorB with hAall | hBall
  · left
    have hAle : A ≤ fixV R := by
      intro a ha
      rw [mem_fixV]
      intro x hx
      exact hAall x hx a ha
    exact (Subgroup.eq_of_le_of_card_ge hAle (by omega)).symm
  · right
    have hBle : B ≤ fixV R := by
      intro b hb
      rw [mem_fixV]
      intro x hx
      exact hBall x hx b hb
    exact (Subgroup.eq_of_le_of_card_ge hBle (by omega)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
