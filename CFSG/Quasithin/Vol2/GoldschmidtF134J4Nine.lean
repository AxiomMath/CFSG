module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal

public section

namespace CFSG.Quasithin.F134.J4E9

open Subgroup

theorem exists_pow_lt_three_of_mem_zpowers {G : Type*} [Group G] {x v : G} (hx : orderOf x = 3)
    (hv : v ∈ zpowers x) : ∃ a < 3, x ^ a = v := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h := zpow_mod_orderOf x k
  rw [hx] at h
  rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← h]
  norm_num

theorem exists_common_eigenvector {G : Type*} [Group G] (N : Subgroup G) (Ē : Set G)
    (hN : Nat.card N = 9) (hN3 : ∀ x ∈ N, x ^ 3 = 1)
    (hnorm : ∀ ε ∈ Ē, ∀ n ∈ N, ε * n * ε⁻¹ ∈ N)
    (hc : ∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a) (h2 : ∀ a ∈ Ē, a * a = 1) :
    ∃ v ∈ N, v ≠ 1 ∧ ∀ ε ∈ Ē, ε * v * ε⁻¹ = v ∨ ε * v * ε⁻¹ = v⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := N)
      (by rw [hN]; norm_num)
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hex : ∃ v ∈ N, v ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card N = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
      rw [h a a.2, h b b.2]
    omega
  by_cases hcase : ∀ ε ∈ Ē, (∀ n ∈ N, ε * n * ε⁻¹ = n) ∨ (∀ n ∈ N, ε * n * ε⁻¹ = n⁻¹)
  · obtain ⟨v, hv, hv1⟩ := hex
    refine ⟨v, hv, hv1, fun ε hε => ?_⟩
    rcases hcase ε hε with h | h
    · exact Or.inl (h v hv)
    · exact Or.inr (h v hv)
  · push Not at hcase
    obtain ⟨σ, hσ, ⟨n₁, hn₁, hn₁'⟩, ⟨n₂, hn₂, hn₂'⟩⟩ := hcase
    have hσσ : σ * σ = 1 := h2 σ hσ
    have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
    have hfix : ∀ n : G, σ * n * σ⁻¹ = n ↔ n ∈ Subgroup.centralizer ({σ} : Set G) := by
      intro n
      rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]
    set F : Subgroup G := N ⊓ Subgroup.centralizer ({σ} : Set G) with hF
    have : Finite F := Finite.of_injective (Subgroup.inclusion (inf_le_left : F ≤ N))
      (Subgroup.inclusion_injective _)
    have hFdvd : Nat.card F ∣ 9 := hN ▸ Subgroup.card_dvd_of_le inf_le_left
    have hF9 : Nat.card F ≠ 9 := by
      intro h9
      have hle : N ≤ F := by
        refine (Subgroup.eq_of_le_of_card_ge (inf_le_left : F ≤ N) ?_).ge
        rw [h9, hN]
      exact hn₁' ((hfix n₁).mpr (hle hn₁).2)
    have hF1 : Nat.card F ≠ 1 := by
      intro h1
      have hbot : F = ⊥ := Subgroup.card_eq_one.mp h1
      have ha : σ * n₂ * σ⁻¹ ∈ N := hnorm σ hσ n₂ hn₂
      have hconj2 : σ * (σ * n₂ * σ⁻¹) * σ⁻¹ = n₂ := by
        rw [hσinv]
        calc σ * (σ * n₂ * σ) * σ = (σ * σ) * n₂ * (σ * σ) := by group
          _ = n₂ := by rw [hσσ]; group
      have hm : n₂ * (σ * n₂ * σ⁻¹) ∈ F := by
        refine ⟨N.mul_mem hn₂ ha, (hfix _).mp ?_⟩
        calc σ * (n₂ * (σ * n₂ * σ⁻¹)) * σ⁻¹
            = (σ * n₂ * σ⁻¹) * (σ * (σ * n₂ * σ⁻¹) * σ⁻¹) := by group
          _ = (σ * n₂ * σ⁻¹) * n₂ := by rw [hconj2]
          _ = n₂ * (σ * n₂ * σ⁻¹) := hcomm _ ha _ hn₂
      rw [hbot, Subgroup.mem_bot] at hm
      exact hn₂' (eq_inv_of_mul_eq_one_right hm)
    have hF3 : Nat.card F = 3 := by
      obtain ⟨i, hi, hiF⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (show Nat.card F ∣ 3 ^ 2 by
        simpa using hFdvd)
      interval_cases i
      · exact absurd (by simpa using hiF) hF1
      · simpa using hiF
      · exact absurd (by simpa using hiF) hF9
    obtain ⟨⟨v, hvF⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := F)).mp
      (fun h => hF1 (by rw [h]; simp))
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvN : v ∈ N := hvF.1
    have hvσ : v * σ = σ * v := Subgroup.mem_centralizer_singleton_iff.mp hvF.2
    have ho3 : orderOf v = 3 := orderOf_eq_prime (hN3 v hvN) hv1'
    have hFeq : Subgroup.zpowers v = F :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvF) (by
        rw [Nat.card_zpowers, ho3, hF3])
    refine ⟨v, hvN, hv1', fun ε hε => ?_⟩
    have hσε : Commute σ ε := hc σ hσ ε hε
    have hw : ε * v * ε⁻¹ ∈ F :=
      ⟨hnorm ε hε v hvN, Subgroup.mem_centralizer_singleton_iff.mpr
        (((hσε.mul_right (show Commute σ v from hvσ.symm)).mul_right hσε.inv_right).eq).symm⟩
    rw [← hFeq] at hw
    obtain ⟨a, ha, hav⟩ := exists_pow_lt_three_of_mem_zpowers ho3 hw
    interval_cases a
    · exfalso
      rw [pow_zero] at hav
      apply hv1'
      have : v = ε⁻¹ * (ε * v * ε⁻¹) * ε := by group
      rw [this, ← hav]
      group
    · exact Or.inl (by rw [← hav, pow_one])
    · refine Or.inr ?_
      rw [← hav]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hN3 v hvN)

theorem no_nine {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω] (w₀ : Ω)
    (Pt E : Subgroup X) (hPt : Nat.card Pt = 9) (hPt3 : ∀ x ∈ Pt, x ^ 3 = 1)
    (hS : IsPGroup 2 (MulAction.stabilizer X w₀))
    (hidx : (MulAction.stabilizer X w₀).index = 9)
    (hPS : ∀ x ∈ Pt, x • w₀ = w₀ → x = 1)
    (hEw : ∀ e ∈ E, e • w₀ = w₀) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1)
    (hE4 : ∀ x : X, x • w₀ ≠ w₀ → 4 ≤ {w : Ω | ∃ e ∈ E, e • (x • w₀) = w}.ncard)
    (hirr : ∀ M : Subgroup X, M.Normal → Nat.card ↥(M ⊓ Pt) ≠ 3) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := MulAction.stabilizer X w₀ with hSdef
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hS
  have hX : Nat.card X = 2 ^ m * 9 := by
    have := S.card_mul_index
    rw [hm, hidx] at this
    exact this.symm
  have hsolv : Group.IsSolvable X := by
    have : Fintype X := Fintype.ofFinite X
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2)
      (q := 3) (a := m) (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hX]; norm_num)
  set K₀ := S.normalCore with hK₀
  have hK₀S : K₀ ≤ S := S.normalCore_le
  have hK₀p : IsPGroup 2 K₀ := hS.to_le hK₀S
  let π : X →* X ⧸ K₀ := QuotientGroup.mk' K₀
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K₀
  have hπker : π.ker = K₀ := QuotientGroup.ker_mk' K₀
  have hπK₀ : ∀ x : X, π x = 1 ↔ x ∈ K₀ := fun x => QuotientGroup.eq_one_iff x
  have hcardX := Subgroup.card_eq_card_quotient_mul_card_subgroup K₀
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hK₀p
  have hXbar : Nat.card (X ⧸ K₀) * 2 ^ k = 2 ^ m * 9 := by rw [← hX, ← hk]; exact hcardX.symm
  have hXbar9 : Nat.card (X ⧸ K₀) ∣ 2 ^ m * 9 := Dvd.intro _ hXbar
  have hnt : Nontrivial (X ⧸ K₀) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hle : Nat.card K₀ ≤ Nat.card S := Subgroup.card_le_of_le hK₀S
    have hprod : Nat.card (X ⧸ K₀) * Nat.card K₀ = 2 ^ m * 9 := by rw [← hX]; exact hcardX.symm
    have hpos : 0 < Nat.card (X ⧸ K₀) := Nat.card_pos
    have hpos2 : 0 < 2 ^ m := Nat.two_pow_pos m
    by_contra hlt
    have h1 : Nat.card (X ⧸ K₀) = 1 := by omega
    rw [h1] at hprod
    rw [hm] at hle
    omega
  have hsolvbar : Group.IsSolvable (X ⧸ K₀) := by
    have := hsolv
    infer_instance
  obtain ⟨N, hNmin⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_minimal_nontrivial_normal (G := X ⧸ K₀)
  have hNn : N.Normal := hNmin.1.1
  have hN1 : N ≠ ⊥ := hNmin.1.2
  obtain ⟨r, hr, -, d, hd, hNcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary N hNmin
      (by have := hsolvbar; infer_instance)
  have hNdvd : Nat.card N ∣ 2 ^ m * 9 := (Subgroup.card_subgroup_dvd_card N).trans hXbar9
  have hrdvd : r ∣ 2 ^ m * 9 := by
    refine (dvd_pow_self r hd.ne').trans ?_
    rw [← hNcard]
    exact hNdvd
  have hr3 : r = 3 := by
    rcases (Nat.Prime.dvd_mul hr).mp hrdvd with h | h
    · exfalso
      have hr2 : r = 2 :=
        (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      subst hr2
      have hNp : IsPGroup 2 N := IsPGroup.of_card hNcard
      have hMp : IsPGroup 2 (N.comap π) :=
        hNp.comap_of_ker_isPGroup π (by rw [hπker]; exact hK₀p)
      have : (N.comap π).Normal := hNn.comap π
      have hMS : N.comap π ≤ S :=
        IsPGroup.le_sylow_of_normal hMp (hS.toSylow (by rw [hidx]; norm_num))
      have hMK : N.comap π ≤ K₀ := Subgroup.normal_le_normalCore.mpr hMS
      apply hN1
      rw [eq_bot_iff]
      intro n hn
      obtain ⟨x, rfl⟩ := hπs n
      have hx : x ∈ N.comap π := Subgroup.mem_comap.mpr hn
      rw [Subgroup.mem_bot]
      exact (hπK₀ x).mpr (hMK hx)
    · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow (show r ∣ 3 ^ 2 by simpa using h))
  subst hr3
  have hNp : IsPGroup 3 N := IsPGroup.of_card hNcard
  set Pb : Subgroup (X ⧸ K₀) := Pt.map π with hPb
  have hPinj : ∀ a ∈ Pt, ∀ b ∈ Pt, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ K₀ := QuotientGroup.eq.mp hab
    have h2 : (a⁻¹ * b) • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp (hK₀S h1)
    exact inv_mul_eq_one.mp (hPS _ (Pt.mul_mem (Pt.inv_mem ha) hb) h2)
  have hPbcard : Nat.card Pb = 9 := by
    rw [← hPt]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : Pt => (⟨π p, Subgroup.mem_map_of_mem π p.2⟩ : Pb))
      ⟨fun a b hab => Subtype.ext (hPinj a a.2 b b.2 (congrArg Subtype.val hab)), ?_⟩)).symm
    rintro ⟨_, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  have hPbp : IsPGroup 3 Pb := IsPGroup.of_card (n := 2) (by rw [hPbcard]; norm_num)
  have hPbidx : ¬ 3 ∣ Pb.index := by
    have h1 := Pb.card_mul_index
    rw [hPbcard] at h1
    have h2 : 9 * Pb.index ∣ 9 * 2 ^ m := by
      rw [h1, mul_comm 9]
      exact hXbar9
    have h3 : Pb.index ∣ 2 ^ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow (h.trans h3)
    omega
  have hNPb : N ≤ Pb := IsPGroup.le_sylow_of_normal hNp (hPbp.toSylow hPbidx)
  have hd2 : d ≤ 2 := by
    have hdvd : 3 ^ d ∣ 9 := by
      rw [← hNcard, ← hPbcard]
      exact Subgroup.card_dvd_of_le hNPb
    by_contra hlt
    have h27 : 3 ^ 3 ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hMn : (N.comap π).Normal := hNn.comap π
  have hMPt : Nat.card ↥(N.comap π ⊓ Pt) = Nat.card N := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(N.comap π ⊓ Pt) => (⟨π x, Subgroup.mem_comap.mp x.2.1⟩ : N)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (hPinj x x.2.2 y y.2.2 (congrArg Subtype.val hxy))
    · intro n
      obtain ⟨p, hp, hpn⟩ := Subgroup.mem_map.mp (hNPb n.2)
      refine ⟨⟨p, Subgroup.mem_comap.mpr (by rw [show π p = n from hpn]; exact n.2), hp⟩,
        Subtype.ext hpn⟩
  have hNcard3 : Nat.card N ≠ 3 := by
    rw [← hMPt]
    exact hirr _ hMn
  have hd2' : d = 2 := by
    interval_cases d
    · exact absurd (by simpa using hNcard) hNcard3
    · rfl
  subst hd2'
  have hNcard9 : Nat.card N = 9 := by rw [hNcard]; norm_num
  have hNPbeq : N = Pb := Subgroup.eq_of_le_of_card_ge hNPb (by rw [hPbcard, hNcard9])
  obtain ⟨v, hvN, hv1, hveig⟩ := exists_common_eigenvector N ((E.map π : Subgroup (X ⧸ K₀)) :
      Set (X ⧸ K₀)) hNcard9
    (fun x hx => by
      rw [hNPbeq] at hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hPt3 p hp, map_one])
    (fun ε _ n hn => hNn.conj_mem n hn ε)
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      rw [← map_mul, ← map_mul, hEc e he e' he'])
    (by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_mul, hE2 e he, map_one])
  obtain ⟨x₀, hx₀, hx₀v⟩ := Subgroup.mem_map.mp (hNPb hvN)
  have hx₀1 : x₀ ≠ 1 := fun h => hv1 (by rw [← hx₀v, h, map_one])
  have hx₀w : x₀ • w₀ ≠ w₀ := fun h => hx₀1 (hPS x₀ hx₀ h)
  have hsub : {w : Ω | ∃ e ∈ E, e • (x₀ • w₀) = w} ⊆ {x₀ • w₀, x₀⁻¹ • w₀} := by
    rintro w ⟨e, he, rfl⟩
    have key : ∀ y : X, π (e * x₀ * e⁻¹) = π y → e • (x₀ • w₀) = y • w₀ := by
      intro y hy
      have h1 : (e * x₀ * e⁻¹)⁻¹ * y ∈ K₀ := QuotientGroup.eq.mp hy
      have h2 : ((e * x₀ * e⁻¹)⁻¹ * y) • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp (hK₀S h1)
      have h3 : y • w₀ = (e * x₀ * e⁻¹) • w₀ := by
        calc y • w₀ = ((e * x₀ * e⁻¹) * ((e * x₀ * e⁻¹)⁻¹ * y)) • w₀ := by
              rw [mul_inv_cancel_left]
          _ = (e * x₀ * e⁻¹) • (((e * x₀ * e⁻¹)⁻¹ * y) • w₀) := by rw [mul_smul]
          _ = (e * x₀ * e⁻¹) • w₀ := by rw [h2]
      calc e • (x₀ • w₀) = (e * x₀ * e⁻¹) • (e • w₀) := by
            rw [smul_smul, smul_smul, inv_mul_cancel_right]
        _ = (e * x₀ * e⁻¹) • w₀ := by rw [hEw e he]
        _ = y • w₀ := h3.symm
    have hcase := hveig (π e) (Subgroup.mem_map_of_mem π he)
    rw [← hx₀v] at hcase
    rcases hcase with h | h
    · exact Or.inl (key x₀ (by rw [map_mul, map_mul, map_inv]; exact h))
    · exact Or.inr (key x₀⁻¹ (by rw [map_mul, map_mul, map_inv, map_inv]; exact h))
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2le : ({x₀ • w₀, x₀⁻¹ • w₀} : Set Ω).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have := hE4 x₀ hx₀w
  omega

end CFSG.Quasithin.F134.J4E9
