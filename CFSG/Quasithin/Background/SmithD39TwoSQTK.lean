module

public import CFSG.Quasithin.EmptyFaithful.S1417Rank

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Open CFSG.LieType.BorelTits

section Elementary

variable {G : Type*} [Group G]

theorem eq_one_of_pow_three_of_two_pow {x : G} (h3 : x ^ 3 = 1) {k : ℕ} (h2 : x ^ 2 ^ k = 1) :
    x = 1 := by
  have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [hc.gcd_eq_one, Nat.dvd_one] at h
  exact orderOf_eq_one_iff.mp h

theorem eq_one_of_two_pow_of_odd_zpow {x : G} {k : ℕ} (hk : x ^ 2 ^ k = 1) {j : ℤ} (hj : Odd j)
    (hx : x ^ j = 1) : x = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, pow_zero] at hm
    exact orderOf_eq_one_iff.mp hm
  · exfalso
    have h1 : (orderOf x : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr hx
    have h2 : (2 : ℤ) ∣ (orderOf x : ℤ) := by
      rw [hm]
      exact_mod_cast dvd_pow_self 2 hpos.ne'
    obtain ⟨i, rfl⟩ := hj
    obtain ⟨l, hl⟩ := h2.trans h1
    omega

theorem eq_one_of_eq_inv_of_pow_three {c : G} (h3 : c ^ 3 = 1) (h : c = c⁻¹) : c = 1 := by
  have h5 : c * c = 1 := by
    nth_rewrite 2 [h]
    exact mul_inv_cancel c
  have h6 : c ^ 3 = c := by rw [pow_succ, pow_two, h5, one_mul]
  rw [← h6]
  exact h3

end Elementary

section Cover

variable {G : Type*} [Group G]

theorem exists_cover_of_le {M H : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M) (hHM : H ≤ M) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S),
      (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥H, Function.Surjective φ := by
  obtain ⟨S, _, _, hSQT, -, φ, hφ⟩ := hMq
  refine ⟨↥((H.subgroupOf M).comap φ), inferInstance, inferInstance, fun q hq hq2 => ?_, ?_⟩
  · exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt _
      ((H.subgroupOf M).comap φ).subtype_injective).trans (hSQT q hq hq2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hHM).toMonoidHom.comp
      (φ.subgroupComap (H.subgroupOf M)), fun g => ?_⟩
    obtain ⟨h, hh⟩ := hφ ⟨(g : G), hHM g.2⟩
    have hmem : h ∈ (H.subgroupOf M).comap φ := by
      rw [Subgroup.mem_comap, hh]
      exact g.2
    refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
    show ((φ h : ↥M) : G) = g
    rw [hh]

end Cover

section Core

variable {H : Type*} [Group H] [Finite H]

theorem false_of_inverted_cube_core {P : Subgroup H} [hPn : P.Normal]
    (hP3 : ∀ z ∈ P, z ^ 3 = 1) (hPc : ∀ z ∈ P, ∀ z' ∈ P, z * z' = z' * z)
    {t : H} {k : ℕ} (htk : t ^ 2 ^ k = 1) (hdec : ∀ h : H, ∃ n ∈ P, ∃ j : ℤ, h = n * t ^ j)
    (ht2 : ∀ g : H, t ^ 2 * g = g * t ^ 2)
    {a b c : H} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hta : t * a = a * t)
    (htb : t * b = b * t) (htc : t * c * t⁻¹ = c⁻¹) (hc1 : c ≠ 1) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a)
    {S : Type} [Group S] [Finite S] (hS : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2)
    (φ : S →* H) (hφ : Function.Surjective φ) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup H := Subgroup.zpowers (t ^ 2) with hZ
  have hZc : ∀ z ∈ Z, ∀ g : H, g * z = z * g := by
    intro z hz g
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute g (t ^ 2) from (ht2 g).symm) i).eq
  have hZn : Z.Normal := ⟨fun z hz g => by rwa [hZc z hz g, mul_inv_cancel_right]⟩
  have hdisj : ∀ z ∈ P, z ∈ Z → z = 1 := by
    intro z hzP hzZ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzZ
    refine eq_one_of_pow_three_of_two_pow (hP3 _ hzP) (k := k) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm,
      pow_mul, htk, one_pow, one_zpow]
  set mk : H →* H ⧸ Z := QuotientGroup.mk' Z with hmk
  have hmk_inj : ∀ x ∈ P, ∀ y ∈ P, mk x = mk y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
    exact inv_mul_eq_one.mp (hdisj _ (P.mul_mem (P.inv_mem hx) hy) h1)
  have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP3 g g.2)⟩
  have hPcore : P.map mk ≤ CFSG.Open.pCore 3 (H ⧸ Z) :=
    (Subgroup.map_mono (le_pCore 3 hPn hPp)).trans
      (map_pCore_le 3 mk (QuotientGroup.mk'_surjective Z))
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 (H ⧸ Z) : Set (H ⧸ Z)) ≤
      CFSG.Open.pCore 3 (H ⧸ Z) := by
    intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z g
    have hcomm : ∀ z ∈ P, h * z = z * h := by
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp hg (mk z) (hPcore ⟨z, hz, rfl⟩)
      have h2 : (z * h)⁻¹ * (h * z) ∈ Z := by
        rw [← QuotientGroup.eq]
        simpa [hmk] using h1
      have h3 : (z * h)⁻¹ * (h * z) ∈ P := by
        have := P.mul_mem (hPn.conj_mem z⁻¹ (P.inv_mem hz) h⁻¹) hz
        convert this using 1
        group
      exact (inv_mul_eq_one.mp (hdisj _ h3 h2)).symm
    obtain ⟨n, hn, j, rfl⟩ := hdec h
    have hcj : t ^ j * c = c * t ^ j := by
      have h1 := hcomm c hc
      have h2 := hPc n hn c hc
      apply mul_left_cancel (a := n)
      calc n * (t ^ j * c) = n * t ^ j * c := by group
        _ = c * (n * t ^ j) := h1
        _ = (c * n) * t ^ j := by group
        _ = n * c * t ^ j := by rw [h2]
        _ = n * (c * t ^ j) := by group
    rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hmem : t ^ (i + i) ∈ Z := by
        refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      have h1 : mk (n * t ^ (i + i)) = mk n := by
        rw [map_mul, show mk (t ^ (i + i)) = 1 from (QuotientGroup.eq_one_iff _).mpr hmem,
          mul_one]
      rw [show (QuotientGroup.mk' Z) (n * t ^ (i + i)) = mk n from h1]
      exact hPcore ⟨n, hn, rfl⟩
    · exfalso
      have hz : (t ^ 2) ^ i ∈ Z := Subgroup.zpow_mem_zpowers _ _
      have e1 : t ^ (2 * i + 1) = (t ^ 2) ^ i * t := by
        rw [zpow_add_one, zpow_mul]
        norm_cast
      rw [e1] at hcj
      have h2 : (t ^ 2) ^ i * (t * c) = (t ^ 2) ^ i * (c * t) := by
        calc (t ^ 2) ^ i * (t * c) = (t ^ 2) ^ i * t * c := by group
          _ = c * ((t ^ 2) ^ i * t) := hcj
          _ = (c * (t ^ 2) ^ i) * t := by group
          _ = ((t ^ 2) ^ i * c) * t := by rw [hZc _ hz c]
          _ = (t ^ 2) ^ i * (c * t) := by group
      have h3 := mul_left_cancel h2
      apply hc1
      refine eq_one_of_eq_inv_of_pow_three (hP3 c hc) ?_
      rw [← htc, h3, mul_inv_cancel_right]
  obtain h131 := A1c.A131Concl_of_surjective (p := 3) (by norm_num) hF _ S (mk.comp φ)
    ((QuotientGroup.mk'_surjective Z).comp hφ) rfl hS
  set T : Subgroup (H ⧸ Z) := Subgroup.zpowers (mk t) with hT
  have hT2 : IsPGroup 2 T := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    show (mk t ^ j) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, htk, map_one,
      one_zpow]
  have hT1 : T ≠ ⊥ := by
    intro hTb
    have hmt : mk t = 1 := by
      have h1 : mk t ∈ T := Subgroup.mem_zpowers (mk t)
      rw [hTb] at h1
      exact Subgroup.mem_bot.mp h1
    have htZ : t ∈ Z := (QuotientGroup.eq_one_iff t).mp hmt
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp htZ
    have h1 : t ^ (2 * i - 1) = 1 := by
      rw [zpow_sub_one, zpow_mul]
      norm_cast
      rw [hi, mul_inv_cancel]
    have ht1 := eq_one_of_two_pow_of_odd_zpow htk ⟨i - 1, by ring⟩ h1
    apply hc1
    refine eq_one_of_eq_inv_of_pow_three (hP3 c hc) ?_
    rw [← htc, ht1, one_mul, inv_one, mul_one]
  have hcyc := h131.1 T hT2 hT1
  have hmem : ∀ x ∈ P, t * x = x * t →
      mk x ∈ CFSG.Open.pCore 3 (H ⧸ Z) ⊓ Subgroup.centralizer (T : Set (H ⧸ Z)) := by
    intro x hx htx
    refine ⟨hPcore ⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro m hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hcm : Commute (mk t) (mk x) := by
      show mk t * mk x = mk x * mk t
      rw [← map_mul, ← map_mul, htx]
    exact (hcm.zpow_left j).eq
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  refine S1417.not_isCyclic_of_four_cubes (α := ⟨mk a, hmem a ha hta⟩)
    (β := ⟨mk b, hmem b hb htb⟩) ?_ ?_ ?_ ?_ ?_ ?_ hcyc
  · exact Subtype.ext (by simp [← map_pow, hP3 a ha])
  · exact Subtype.ext (by simp [← map_pow, hP3 b hb])
  · intro h
    exact ha1 (hmk_inj a ha 1 P.one_mem (by simpa using congrArg Subtype.val h))
  · intro h
    exact hb1 (hmk_inj b hb 1 P.one_mem (by simpa using congrArg Subtype.val h))
  · intro h
    have h1 := hmk_inj b hb a ha (by simpa using congrArg Subtype.val h)
    exact hba (h1 ▸ Subgroup.mem_zpowers a)
  · intro h
    have h1 := hmk_inj b hb a⁻¹ (P.inv_mem ha) (by simpa using congrArg Subtype.val h)
    exact hba (h1 ▸ Subgroup.inv_mem _ (Subgroup.mem_zpowers a))

end Core

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem false_of_inverted_cube {M : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M)
    {a b c t : G} (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) (ht : t ∈ M)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hta : t * a = a * t) (htb : t * b = b * t) (htc : t * c * t⁻¹ = c⁻¹)
    (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) (hc1 : c ≠ 1)
    {k : ℕ} (htk : t ^ 2 ^ k = 1) : False := by
  classical
  set Sg : Set G := {a, b, c} with hSg
  have hcomm : ∀ x ∈ Sg, ∀ y ∈ Sg, x * y = y * x := by
    intro x hx y hy
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | rfl | assumption | exact hab.symm | exact hac.symm | exact hbc.symm
  have hS3 : ∀ x ∈ Sg, x ^ 3 = 1 := by
    intro x hx
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [ha3, hb3, hc3]
  set P : Subgroup G := Subgroup.closure Sg with hP
  have haP : a ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hbP : b ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hcP : c ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hP3 : ∀ z ∈ P, z ^ 3 = 1 := fun z hz => S1417.pow_eq_one_of_mem_closure_comm hS3 hcomm hz
  have hPc : ∀ z ∈ P, ∀ z' ∈ P, z * z' = z' * z := fun z hz z' hz' =>
    S1417.comm_of_mem_closure_comm hcomm hz hz'
  have hconj : ∀ g : G, (∀ x ∈ Sg, g * x * g⁻¹ ∈ P) → ∀ z ∈ P, g * z * g⁻¹ ∈ P := by
    intro g hg z hz
    have hle : P ≤ P.comap (MulAut.conj g).toMonoidHom := by
      rw [hP, Subgroup.closure_le]
      intro x hx
      exact hg x hx
    exact hle hz
  have htc' : t⁻¹ * c * t = c⁻¹ := by
    have h1 : t⁻¹ * (t * c * t⁻¹) * t = t⁻¹ * c⁻¹ * t := by rw [htc]
    have h2 : c = t⁻¹ * c⁻¹ * t := by rw [← h1]; group
    calc t⁻¹ * c * t = (t⁻¹ * c⁻¹ * t)⁻¹ := by group
      _ = c⁻¹ := by rw [← h2]
  have htn : t ∈ Subgroup.normalizer (P : Set G) := by
    have h1 := hconj t (by
      intro x hx
      simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hta, mul_inv_cancel_right]; exact haP
      · rw [htb, mul_inv_cancel_right]; exact hbP
      · rw [htc]; exact P.inv_mem hcP)
    have h2 := hconj t⁻¹ (by
      intro x hx
      simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [inv_inv, mul_assoc, ← hta, inv_mul_cancel_left]; exact haP
      · rw [inv_inv, mul_assoc, ← htb, inv_mul_cancel_left]; exact hbP
      · rw [inv_inv, htc']; exact P.inv_mem hcP)
    refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨fun hz => h1 z hz, fun hz => ?_⟩
    have h3 := h2 _ hz
    simpa [mul_assoc] using h3
  set H : Subgroup G := P ⊔ Subgroup.zpowers t with hH
  have hPH : P ≤ H := le_sup_left
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHM : H ≤ M := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ht)
    rw [hP, Subgroup.closure_le]
    intro x hx
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [ha, hb, hc]
  have hPN : H ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htn)
  have hPn : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hPN
  have htc1 : t * c = c⁻¹ * t := by
    calc t * c = (t * c * t⁻¹) * t := by group
      _ = c⁻¹ * t := by rw [htc]
  have htc2 : t * c⁻¹ = c * t := by
    calc t * c⁻¹ = (t * c * t⁻¹)⁻¹ * t := by group
      _ = c * t := by rw [htc, inv_inv]
  have ht2c : ∀ g ∈ H, t ^ 2 * g = g * t ^ 2 := by
    have hle : H ≤ Subgroup.centralizer {t ^ 2} := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [hP, Subgroup.closure_le]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ((Commute.pow_left (show Commute t x from hta) 2).eq).symm
        · exact ((Commute.pow_left (show Commute t x from htb) 2).eq).symm
        · calc x * t ^ 2 = x * t * t := by rw [pow_two, mul_assoc]
            _ = t * x⁻¹ * t := by rw [← htc2]
            _ = t * (t * x) := by rw [mul_assoc, ← htc1]
            _ = t ^ 2 * x := by rw [pow_two, mul_assoc]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.self_pow t 2).eq
    intro g hg
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
  have hdec : ∀ h : ↥H, ∃ n ∈ P.subgroupOf H, ∃ j : ℤ, h = n * ⟨t, htH⟩ ^ j := by
    intro h
    have h1 : (h : G) ∈ ((P ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := h.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P (Subgroup.zpowers t)
      (Subgroup.zpowers_le.mpr htn)] at h1
    obtain ⟨n, hn, e, he, hne⟩ := h1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨⟨n, hPH hn⟩, hn, j, Subtype.ext (by simp [hne])⟩
  obtain ⟨S, _, _, hSr, φ, hφ⟩ := exists_cover_of_le hMq hHM
  refine false_of_inverted_cube_core (P := P.subgroupOf H) (t := ⟨t, htH⟩) (k := k)
    (a := ⟨a, hPH haP⟩) (b := ⟨b, hPH hbP⟩) (c := ⟨c, hPH hcP⟩)
    (fun z hz => Subtype.ext (hP3 _ hz)) (fun z hz z' hz' => Subtype.ext (hPc _ hz _ hz'))
    (Subtype.ext htk) hdec (fun g => Subtype.ext (ht2c g g.2)) haP hbP hcP (Subtype.ext hta)
    (Subtype.ext htb) (Subtype.ext htc) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => ha1 (congrArg Subtype.val h)) ?_ (hSr 3 Nat.prime_three (by norm_num)) φ hφ
  intro hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hba (Subgroup.mem_zpowers_iff.mpr ⟨j, congrArg Subtype.val hj⟩)

end Ambient

section Centralizer

variable {G : Type*} [Group G] [Finite G]

theorem no_E9_in_centralizer_of_two_elt {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M)
    (hNM : N ≤ M) {u s : G} (hu : u ∈ N) (hs : s ∈ N) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hs2 : ∃ k : ℕ, s ^ 2 ^ k = 1) (hsu : s * u * s⁻¹ = u⁻¹) {x y : G}
    (hx : x ∈ M ⊓ Subgroup.centralizer (N : Set G))
    (hy : y ∈ M ⊓ Subgroup.centralizer (N : Set G)) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) : False := by
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
  have hxN := Subgroup.mem_centralizer_iff.mp hxC
  have hyN := Subgroup.mem_centralizer_iff.mp hyC
  obtain ⟨k, hk⟩ := hs2
  exact false_of_inverted_cube hMq hxM hyM (hNM hu) (hNM hs) hxy (hxN u hu).symm
    (hyN u hu).symm hx3 hy3 hu3 (hxN s hs) (hyN s hs) hsu hx1 hyx hu1 hk

theorem no_E9_in_centralizer {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M) (hNM : N ≤ M)
    {u s : G} (hu : u ∈ N) (hs : s ∈ N) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hs2 : s ^ 2 = 1)
    (hsu : s * u * s⁻¹ = u⁻¹) {x y : G} (hx : x ∈ M ⊓ Subgroup.centralizer (N : Set G))
    (hy : y ∈ M ⊓ Subgroup.centralizer (N : Set G)) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) : False :=
  no_E9_in_centralizer_of_two_elt hMq hNM hu hs hu3 hu1 ⟨1, by rwa [pow_one]⟩ hsu hx hy hx3 hy3
    hxy hx1 hyx

theorem no_inverting_two_elt {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M) (hNM : N ≤ M)
    {u w : G} (hu : u ∈ N) (hw : w ∈ N) (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (huw : u * w = w * u) (hu1 : u ≠ 1) (hwu : w ∉ Subgroup.zpowers u) {x y : G}
    (hx : x ∈ M ⊓ Subgroup.centralizer (N : Set G))
    (hy : y ∈ M ⊓ Subgroup.centralizer (N : Set G)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (hxy : x * y * x⁻¹ = y⁻¹) : False := by
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
  have hxN := Subgroup.mem_centralizer_iff.mp hxC
  have hyN' := Subgroup.mem_centralizer_iff.mp hyC
  obtain ⟨k, hk⟩ := hx2
  exact false_of_inverted_cube hMq (hNM hu) (hNM hw) hyM hxM huw (hyN' u hu) (hyN' w hw)
    hu3 hw3 hy3 (hxN u hu).symm (hxN w hw).symm hxy hu1 hwu hy1 hk

theorem isCyclic_of_noE9 {X : Type*} [Group X] [Finite X] (hX : IsPGroup 3 X)
    (h : ∀ x y : X, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 → y ∈ Subgroup.zpowers x) :
    IsCyclic X := by
  by_contra hnc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 X) := ⟨hX⟩
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := fun e he => CFSG.elemPow_eq_one_of_isElementaryAbelian e he
  have hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' =>
    congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hall
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers x from hall)
    rw [hcard, Nat.card_zpowers] at h1
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE3 x hxE))
    omega
  exact hyx (h x y (hE3 x hxE) (hE3 y hyE) (hEc x hxE y hyE) hx1)

theorem isCyclic_of_isPGroup_three_of_le {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M)
    (hNM : N ≤ M) {u s : G} (hu : u ∈ N) (hs : s ∈ N) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u * s⁻¹ = u⁻¹) {X : Subgroup G} (hX3 : IsPGroup 3 ↥X)
    (hXC : X ≤ M ⊓ Subgroup.centralizer (N : Set G)) : IsCyclic ↥X := by
  refine isCyclic_of_noE9 hX3 fun x y hx3 hy3 hxy hx1 => ?_
  by_contra hyx
  refine no_E9_in_centralizer hMq hNM hu hs hu3 hu1 hs2 hsu (hXC x.2) (hXC y.2)
    (by simpa using congrArg Subtype.val hx3) (by simpa using congrArg Subtype.val hy3)
    (by simpa using congrArg Subtype.val hxy) (fun h => hx1 (Subtype.ext h)) ?_
  intro hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj)⟩)

theorem isCyclic_pCoreOf_three_centralizer {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M)
    (hNM : N ≤ M) {u s : G} (hu : u ∈ N) (hs : s ∈ N) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u * s⁻¹ = u⁻¹) :
    IsCyclic ↥(pCoreOf 3 (M ⊓ Subgroup.centralizer (N : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_isPGroup_three_of_le hMq hNM hu hs hu3 hu1 hs2 hsu
    (pCoreOf_isPGroup 3 _) (pCoreOf_le 3 _)

theorem isCyclic_sylow_three_of_le {M N : Subgroup G} (hMq : IsQuotientOfSQTKTC ↥M)
    (hNM : N ≤ M) {u s : G} (hu : u ∈ N) (hs : s ∈ N) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u * s⁻¹ = u⁻¹) {K : Subgroup G}
    (hK : K ≤ M ⊓ Subgroup.centralizer (N : Set G)) (P : Sylow 3 ↥K) : IsCyclic ↥P := by
  have hle : (P : Subgroup ↥K).map K.subtype ≤ M ⊓ Subgroup.centralizer (N : Set G) :=
    (Subgroup.map_subtype_le _).trans hK
  have hcyc := isCyclic_of_isPGroup_three_of_le hMq hNM hu hs hu3 hu1 hs2 hsu
    (P.isPGroup'.map K.subtype) hle
  let e := (P : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Centralizer

end CFSG.Quasithin.SmithD39Two
