module

public import CFSG.RankThree.PartOne.K133.TwoLoc
public import CFSG.RankThree.PartOne.CTP.StrongPSporadic

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.Census3 CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint TauCeti

theorem not_elementaryAbelian_cube_of_noncomm {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hX3 : p ^ 3 ∣ Nat.card X) (hX4 : ¬ p ^ 4 ∣ Nat.card X)
    (hN : StrongP.HasNoncommPair p X) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (hcard : Nat.card A = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card X).factorization p = 3 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp hX0).1 hX3
    have h2 : ¬ 4 ≤ (Nat.card X).factorization p := fun h =>
      hX4 ((Nat.Prime.pow_dvd_iff_le_factorization hp hX0).2 h)
    omega
  let PA : Sylow p X := Sylow.ofCard A (by rw [hcard, hfac])
  obtain ⟨x, y, hx, hy, hxy, hH⟩ := hN
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X PA P
  have hxP : x ∈ (P : Subgroup X) := hHP (Subgroup.subset_closure (by simp))
  have hyP : y ∈ (P : Subgroup X) := hHP (Subgroup.subset_closure (by simp))
  rw [← hg, Sylow.coe_subgroup_smul] at hxP hyP
  have e1 : (MulAut.conj g)⁻¹ • x ∈ A := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hxP
  have e2 : (MulAut.conj g)⁻¹ • y ∈ A := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hyP
  have key : ((MulAut.conj g)⁻¹ • x) * ((MulAut.conj g)⁻¹ • y) =
      ((MulAut.conj g)⁻¹ • y) * ((MulAut.conj g)⁻¹ • x) :=
    congrArg Subtype.val (hA.is_comm.comm ⟨_, e1⟩ ⟨_, e2⟩)
  simp only [MulAut.smul_def] at key
  rw [← map_mul, ← map_mul] at key
  exact hxy ((MulAut.conj g)⁻¹.injective key)


theorem center_eq_bot_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center X := h1 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem exists_elementaryAbelian_of_le_inner {X : Type*} [Group X] {p : ℕ}
    (hZ : Subgroup.center X = ⊥) {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E)
    (hle : E ≤ inner X) (hcard : Nat.card E = p ^ 3) :
    ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = p ^ 3 := by
  set f : X →* MulAut X := MulAut.conj with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hg z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * g = g * z * g⁻¹ * g * 1 := by rw [h1]; group
        _ = g * z := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  refine ⟨E.comap f, ?_, ?_⟩
  · refine
      { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
    · apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hE.is_comm.comm ⟨f (x : X), x.2⟩ ⟨f (y : X), y.2⟩)
      simpa using this
    · apply Subtype.ext
      apply hinj
      have h1 : (⟨f (x : X), x.2⟩ : ↥E) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E) _
      have h2 := congrArg Subtype.val h1
      simpa using h2
  · have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self (by
      intro x hx
      exact hle hx)
    rw [← hcard, ← hmap, Subgroup.card_map_of_injective hinj]
    exact (congrArg Nat.card (by rw [hmap])).symm

theorem cube_M11 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 7920) :
    SporadicPairNC .M11 p ∧ ¬ p ^ 4 ∣ 7920 := by
  have h1 : p ∈ Nat.primeFactors 7920 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_M12 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 95040) :
    SporadicPairNC .M12 p ∧ ¬ p ^ 4 ∣ 95040 := by
  have h1 : p ∈ Nat.primeFactors 95040 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_M22 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 443520) :
    SporadicPairNC .M22 p ∧ ¬ p ^ 4 ∣ 443520 := by
  have h1 : p ∈ Nat.primeFactors 443520 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_M23 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 10200960) :
    SporadicPairNC .M23 p ∧ ¬ p ^ 4 ∣ 10200960 := by
  have h1 : p ∈ Nat.primeFactors 10200960 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_M24 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 244823040) :
    SporadicPairNC .M24 p ∧ ¬ p ^ 4 ∣ 244823040 := by
  have h1 : p ∈ Nat.primeFactors 244823040 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_J1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 175560) :
    SporadicPairNC .J1 p ∧ ¬ p ^ 4 ∣ 175560 := by
  have h1 : p ∈ Nat.primeFactors 175560 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_J2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 604800) :
    SporadicPairNC .J2 p ∧ ¬ p ^ 4 ∣ 604800 := by
  have h1 : p ∈ Nat.primeFactors 604800 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_J3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 50232960) :
    SporadicPairNC .J3 p ∧ ¬ p ^ 4 ∣ 50232960 := by
  have h1 : p ∈ Nat.primeFactors 50232960 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_J4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 86775571046077562880) :
    SporadicPairNC .J4 p ∧ ¬ p ^ 4 ∣ 86775571046077562880 := by
  have h1 : p ∈ Nat.primeFactors 86775571046077562880 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_McL {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 898128000) :
    SporadicPairNC .McL p ∧ ¬ p ^ 4 ∣ 898128000 := by
  have h1 : p ∈ Nat.primeFactors 898128000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_HS {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 44352000) :
    SporadicPairNC .HS p ∧ ¬ p ^ 4 ∣ 44352000 := by
  have h1 : p ∈ Nat.primeFactors 44352000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_He {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 4030387200) :
    SporadicPairNC .He p ∧ ¬ p ^ 4 ∣ 4030387200 := by
  have h1 : p ∈ Nat.primeFactors 4030387200 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h

theorem cube_Suz {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 448345497600) :
    SporadicPairNC .Suz p ∧ ¬ p ^ 4 ∣ 448345497600 := by
  have h1 : p ∈ Nat.primeFactors 448345497600 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_Ru {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 145926144000) :
    SporadicPairNC .Ru p ∧ ¬ p ^ 4 ∣ 145926144000 := by
  have h1 : p ∈ Nat.primeFactors 145926144000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_ONan {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 460815505920) :
    SporadicPairNC .ONan p ∧ ¬ p ^ 4 ∣ 460815505920 := by
  have h1 : p ∈ Nat.primeFactors 460815505920 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_Co3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 495766656000) :
    SporadicPairNC .Co3 p ∧ ¬ p ^ 4 ∣ 495766656000 := by
  have h1 : p ∈ Nat.primeFactors 495766656000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_Co2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 42305421312000) :
    SporadicPairNC .Co2 p ∧ ¬ p ^ 4 ∣ 42305421312000 := by
  have h1 : p ∈ Nat.primeFactors 42305421312000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem cube_Th {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ 90745943887872000) :
    SporadicPairNC .Th p ∧ ¬ p ^ 4 ∣ 90745943887872000 := by
  have h1 : p ∈ Nat.primeFactors 90745943887872000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact ⟨by simp [SporadicPairNC], by norm_num⟩
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sporadic_cube_dvd
    {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3) (hLy : s ≠ .Ly) (hHN : s ≠ .HN) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 3 ∣ Nat.card (NativeSporadic.Carrier s)) :
    SporadicPairNC s p ∧ ¬ p ^ 4 ∣ Nat.card (NativeSporadic.Carrier s) := by
  simp only [Census3.sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl 
  · have hc : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
    rw [hc] at h ⊢
    exact cube_M11 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
    rw [hc] at h ⊢
    exact cube_M12 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [hc] at h ⊢
    exact cube_M22 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .M23) = 10200960 := CFSG.RankThree.PartOne.CTP.card_M23
    rw [hc] at h ⊢
    exact cube_M23 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
    rw [hc] at h ⊢
    exact cube_M24 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
    rw [hc] at h ⊢
    exact cube_J1 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
    rw [hc] at h ⊢
    exact cube_J2 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
    rw [hc] at h ⊢
    exact cube_J3 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
    rw [hc] at h ⊢
    exact cube_J4 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
    rw [hc] at h ⊢
    exact cube_McL hp hp5 h
  · exact absurd rfl hLy
  · have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
    rw [hc] at h ⊢
    exact cube_HS hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
    rw [hc] at h ⊢
    exact cube_He hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
    rw [hc] at h ⊢
    exact cube_Suz hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
    rw [hc] at h ⊢
    exact cube_Ru hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 := CFSG.Sporadic.ON.card_ON_eq
    rw [hc] at h ⊢
    exact cube_ONan hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 := CFSG.Sporadic.Co3.card_Co3
    rw [hc] at h ⊢
    exact cube_Co3 hp hp5 h
  · have hc : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [hc] at h ⊢
    exact cube_Co2 hp hp5 h
  · exact absurd rfl hHN
  · have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 := CFSG.RankThree.PartOne.CTP.card_Th
    rw [hc] at h ⊢
    exact cube_Th hp hp5 h

theorem noRankThree_sporadic
    (hOut : SporadicOuterNoLargePrime) {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3) (hLy : s ≠ .Ly)
    (hHN : s ≠ .HN) {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hne : ∃ a b : X, a * b ≠ b * a)
    (e : X ≃* NativeSporadic.Carrier s) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : NoRankThree p X := by
  rintro ⟨E, hE, hc⟩
  have hOutp : ¬ p ∣ Nat.card (Outer X) := hOut s hs X hne ⟨e⟩ p hp h5
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  have hle := le_inner_of_isPGroup_of_not_dvd_outer hp hOutp hEp
  obtain ⟨A, hA, hAc⟩ := exists_elementaryAbelian_of_le_inner
    (center_eq_bot_of_simple_nonabelian hne) hE hle hc
  have hcard : Nat.card X = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  have h3 : p ^ 3 ∣ Nat.card (NativeSporadic.Carrier s) :=
    hcard ▸ (hAc ▸ Subgroup.card_subgroup_dvd_card A)
  obtain ⟨hNC, h4⟩ := sporadic_cube_dvd hs hLy hHN hp h5 h3
  have hnc : StrongP.HasNoncommPair p X :=
    (hasNoncommPair_carrier hNC).map e.symm.toMonoidHom e.symm.injective
  exact not_elementaryAbelian_cube_of_noncomm hp (hcard ▸ h3) (hcard ▸ h4) hnc A hA hAc

theorem kf133ResMaxAt_leaf6_ne
    (hOut : SporadicOuterNoLargePrime) {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3) (hLy : s ≠ .Ly)
    (hHN : s ≠ .HN) : KF133ResMaxAt (leaf6 s) := by
  refine KF133ResMaxAt.of_dead fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨e0⟩ := hX
  have : IsSimpleGroup (CFSGIndex.sporadic s).Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := nonempty_carrier_mulEquiv_of_mem hs
  exact (noRankThree_sporadic hOut hs hLy hHN hne (e0.trans e1.symm) hp h5).dead

end CFSG.RankThree.PartOne.K133
