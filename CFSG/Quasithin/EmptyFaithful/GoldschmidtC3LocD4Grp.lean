module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace GoldC3

variable {X : Type} [Group X] [Finite X]

theorem mem_normalCore_of_pow {M : Subgroup X} (hidx : M.index = 3) {r : ℕ} (hr : r.Prime)
    (hr6 : ¬ r ∣ 6) {y : X} {j : ℕ} (hy : y ^ r ^ j = 1) : y ∈ M.normalCore := by
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
  set π := MulAction.toPermHom X (X ⧸ M) with hπ
  have hcard : Nat.card (Equiv.Perm (X ⧸ M)) = 6 := by
    classical
    have : Fintype (X ⧸ M) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    show (M.index).factorial = 6
    rw [hidx]
    rfl
  have h1 : orderOf (π y) ∣ 6 := hcard ▸ orderOf_dvd_natCard (π y)
  have h2 : orderOf (π y) ∣ r ^ j := (orderOf_map_dvd π y).trans (orderOf_dvd_of_pow_eq_one hy)
  have hcop : Nat.Coprime 6 (r ^ j) :=
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hr).2 hr6).symm
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem normalCore_le_normalizer_sylow {B : Sylow 2 X} {M : Subgroup X}
    (hM : M = Subgroup.normalizer ((B : Subgroup X) : Set X)) (W : Sylow 2 X) :
    M.normalCore ≤ Subgroup.normalizer (W : Set X) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X B W
  intro k hk
  have hk' : g⁻¹ * k * g ∈ M.normalCore := by
    have := (Subgroup.normalCore_normal M).conj_mem k hk g⁻¹
    simpa using this
  have hk'' : g⁻¹ * k * g ∈ Subgroup.normalizer ((B : Subgroup X) : Set X) :=
    hM ▸ Subgroup.normalCore_le M hk'
  have h1 : (g⁻¹ * k * g) • B = B := Sylow.smul_eq_iff_mem_normalizer.2 hk''
  refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
  calc k • W = k • (g • B) := by rw [hg]
    _ = (k * g) • B := (mul_smul k g B).symm
    _ = g • ((g⁻¹ * k * g) • B) := by rw [← mul_smul]; congr 1; group
    _ = W := by rw [h1, hg]

omit [Finite X] in
theorem pCoreOf_normalizer_of_normal {K : Subgroup X} (hK : K.Normal) (g e : X)
    (he : e ∈ pCoreOf 2 K) : g * e * g⁻¹ ∈ pCoreOf 2 K := by
  have h1 : Subgroup.normalizer (K : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hK
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  rw [h1] at h2
  have hg : g ∈ Subgroup.normalizer (pCoreOf 2 K : Set X) := h2 (Subgroup.mem_top g)
  exact (Subgroup.mem_normalizer_iff.1 hg e).1 he

theorem commutator_two_elt_mem {K : Subgroup X} (hK : K.Normal)
    (hKW : ∀ W : Sylow 2 X, K ≤ Subgroup.normalizer (W : Set X)) {b : X} {j : ℕ}
    (hb : b ^ 2 ^ j = 1) {k : X} (hk : k ∈ K) : b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : IsPGroup 2 ↥(Subgroup.zpowers b) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hb)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨W, hW⟩ := hb2.exists_le_sylow
  have hbW : b ∈ (W : Subgroup X) := hW (Subgroup.mem_zpowers b)
  have hkW : ∀ x : X, x ∈ (W : Subgroup X) ↔ k * x * k⁻¹ ∈ (W : Subgroup X) := fun x =>
    Subgroup.mem_normalizer_iff.1 (hKW W hk) x
  have hmemW : b * k * b⁻¹ * k⁻¹ ∈ (W : Subgroup X) := by
    have h1 : k * b⁻¹ * k⁻¹ ∈ (W : Subgroup X) := (hkW b⁻¹).1 ((W : Subgroup X).inv_mem hbW)
    have := (W : Subgroup X).mul_mem hbW h1
    simpa [mul_assoc] using this
  have hmemK : b * k * b⁻¹ * k⁻¹ ∈ K := K.mul_mem (hK.conj_mem k hk b) (K.inv_mem hk)
  have hKW' : ∀ k' ∈ K, ∀ x ∈ (W : Subgroup X), k' * x * k'⁻¹ ∈ (W : Subgroup X) :=
    fun k' hk' x hx => (Subgroup.mem_normalizer_iff.1 (hKW W hk') x).1 hx
  have hnorm : K ≤ Subgroup.normalizer (((W : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
    fun k' hk' => Subgroup.mem_normalizer_fintype fun x hx =>
      ⟨hKW' k' hk' x hx.1, hK.conj_mem x hx.2 k'⟩
  have hle : (W : Subgroup X) ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      (W.isPGroup'.to_le inf_le_left)
  exact hle ⟨hmemW, hmemK⟩

theorem commutator_mem_pCoreOf {K : Subgroup X} (hK : K.Normal)
    (hKW : ∀ W : Sylow 2 X, K ≤ Subgroup.normalizer (W : Set X))
    (hgen : Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤) {g k : X} (hk : k ∈ K) :
    g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hg : g ∈ Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = 2 ^ k} := hgen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := hx
    exact commutator_two_elt_mem hK hKW (j := j) (by rw [← hj]; exact pow_orderOf_eq_one x) hk
  | one => simp
  | mul a b _ _ ha hb =>
    have h := (pCoreOf 2 K).mul_mem (pCoreOf_normalizer_of_normal hK a _ hb) ha
    have e : a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) = a * b * k * (a * b)⁻¹ * k⁻¹ := by
      group
    rwa [e] at h
  | inv a _ ha =>
    have h := pCoreOf_normalizer_of_normal hK a⁻¹ _ ((pCoreOf 2 K).inv_mem ha)
    have e : a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ := by group
    rwa [e] at h

theorem normalizer_eq_of_three_sylow {B : Subgroup X} (hB : IsSylowTwoOf B ⊤)
    (hgen : Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤)
    (hidx : (Subgroup.normalizer (B : Set X)).index = 3)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.normalizer (B : Set X))) :
    Subgroup.normalizer (B : Set X) = B := by
  by_contra hne
  set M := Subgroup.normalizer (B : Set X) with hM
  have hBM : B ≤ M := Subgroup.le_normalizer
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBi : ¬ 2 ∣ B.index := by
    have h := hB.2.2
    rwa [show (B.subgroupOf ⊤).index = B.index from Subgroup.relIndex_top_right B] at h
  have hm1 : B.relIndex M ≠ 1 := fun h => hne (le_antisymm (Subgroup.relIndex_eq_one.1 h) hBM)
  have hmodd : ¬ 2 ∣ B.relIndex M := by
    intro hd
    apply hBi
    rw [← Subgroup.relIndex_mul_index hBM]
    exact hd.mul_right _
  have hmdvd : B.relIndex M ∣ Nat.card M :=
    Dvd.intro_left _ (Subgroup.card_mul_index (B.subgroupOf M))
  obtain ⟨r, hr, hrm, hr2', hr3'⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ B.relIndex M ∧ r ≠ 2 ∧ r ≠ 3 := by
    refine ⟨(B.relIndex M).minFac, Nat.minFac_prime hm1, Nat.minFac_dvd _, ?_, ?_⟩
    · intro h2'
      apply hmodd
      rw [← h2']
      exact Nat.minFac_dvd _
    · intro h3'
      apply h3
      rw [← h3']
      exact (Nat.minFac_dvd _).trans hmdvd
  have hr6 : ¬ r ∣ 6 := by
    intro hd
    have : r ∣ 2 * 3 := hd
    rcases (Nat.Prime.dvd_mul hr).1 this with h | h
    · exact hr2' ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
    · exact hr3' ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) r (hrm.trans hmdvd)
  set t : X := (t' : X) with ht
  have htr : orderOf t = r := by rw [ht, Subgroup.orderOf_coe]; exact ht'
  have hzp : IsPGroup r ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htr, pow_one])
  obtain ⟨Y, hY⟩ := hzp.exists_le_sylow
  have htY : t ∈ (Y : Subgroup X) := hY (Subgroup.mem_zpowers t)
  set K := M.normalCore with hK
  have hKn : K.Normal := Subgroup.normalCore_normal M
  set BS : Sylow 2 X := hB.2.1.toSylow hBi with hBS
  have hBSc : (BS : Subgroup X) = B := IsPGroup.toSylow_coe _ _
  have hKW : ∀ W : Sylow 2 X, K ≤ Subgroup.normalizer (W : Set X) :=
    normalCore_le_normalizer_sylow (B := BS) (by rw [hBSc])
  have hYK : ∀ y ∈ (Y : Subgroup X), y ∈ K := by
    intro y hy
    obtain ⟨j, hj⟩ := Y.isPGroup' ⟨y, hy⟩
    exact mem_normalCore_of_pow hidx hr hr6 (j := j) (by simpa using congrArg Subtype.val hj)
  have hcop2 : ∀ j i : ℕ, Nat.Coprime (r ^ j) (2 ^ i) := fun j i =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2')
  have hNC : Subgroup.normalizer (Y : Set X) ≤ Subgroup.centralizer (Y : Set X) := by
    intro n hn
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hE := commutator_mem_pCoreOf hKn hKW hgen (g := n) (hYK y hy)
    have hYmem : n * y * n⁻¹ * y⁻¹ ∈ (Y : Subgroup X) :=
      (Y : Subgroup X).mul_mem ((Subgroup.mem_normalizer_iff.1 hn y).1 hy)
        ((Y : Subgroup X).inv_mem hy)
    obtain ⟨j, hj⟩ := Y.isPGroup' ⟨_, hYmem⟩
    obtain ⟨i, hi⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, hE⟩
    have hj' : (n * y * n⁻¹ * y⁻¹) ^ r ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hi' : (n * y * n⁻¹ * y⁻¹) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have h1 : n * y * n⁻¹ * y⁻¹ = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop2 j i)
        (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hi'))
    have h2 : n * y * n⁻¹ = y := mul_inv_eq_one.1 h1
    calc y * n = (n * y * n⁻¹) * n := by rw [h2]
      _ = n * y := by group
  obtain ⟨Kr, hKrn, -, hKridx, -⟩ := CFSG.GroupTheory.burnside_normal_complement Y hNC
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Nat.card ↥(Y : Subgroup X) = r ^ s := Y.isPGroup'.exists_card_eq
  have hKr : ∀ b : X, (∃ j : ℕ, b ^ 2 ^ j = 1) → b ∈ Kr := by
    rintro b ⟨j, hj⟩
    have h1 : orderOf (b : X ⧸ Kr) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hj, QuotientGroup.mk_one])
    have h2 : orderOf (b : X ⧸ Kr) ∣ r ^ s := by
      have := orderOf_dvd_natCard (b : X ⧸ Kr)
      rwa [show Nat.card (X ⧸ Kr) = Kr.index from rfl, hKridx, hs] at this
    exact (QuotientGroup.eq_one_iff b).1
      (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop2 s j).symm h1 h2))
  have hKrtop : Kr = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x ⟨j, hj⟩
    exact hKr x ⟨j, by rw [← hj]; exact pow_orderOf_eq_one x⟩
  rw [hKrtop, Subgroup.index_top] at hKridx
  have hdvd : orderOf (⟨t, htY⟩ : ↥(Y : Subgroup X)) ∣ Nat.card ↥(Y : Subgroup X) :=
    orderOf_dvd_natCard _
  have hord : orderOf (⟨t, htY⟩ : ↥(Y : Subgroup X)) = r := by
    rw [← Subgroup.orderOf_coe]
    exact htr
  rw [hord, ← hKridx] at hdvd
  exact hr.one_lt.ne' (Nat.dvd_one.1 hdvd)

end GoldC3

end CFSG.Quasithin
