module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Inputs
public import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21

open CFSG.Open

private def fixedAdd {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (g : GL n K) : AddSubgroup (n → K) where
  carrier := MulAction.fixedBy (n → K) g
  zero_mem' := by simp [MulAction.mem_fixedBy]
  add_mem' := by
    intro x y hx hy
    rw [MulAction.mem_fixedBy] at hx hy ⊢
    rw [Units.smul_def] at hx hy ⊢
    rw [smul_add, hx, hy]
  neg_mem' := by
    intro x hx
    rw [MulAction.mem_fixedBy] at hx ⊢
    rw [Units.smul_def] at hx ⊢
    rw [smul_neg, hx]

private theorem fixedPoints_zpowers_eq_fixedBy {G V : Type*} [Group G] [MulAction G V] (g : G) :
    MulAction.fixedPoints (Subgroup.zpowers g) V = MulAction.fixedBy V g := by
  ext v
  rw [MulAction.mem_fixedPoints, MulAction.mem_fixedBy]
  constructor
  · intro h
    simpa using h ⟨g, Subgroup.mem_zpowers g⟩
  · intro h j
    rw [Subgroup.smul_def]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp j.2
    rw [← hk]
    exact MulAction.mem_fixedBy_zpow h k

private theorem card_modEq_card_inter_fixedBy {G V : Type*} [Group G] [MulAction G V] [Finite V]
    (g : G) {p : ℕ} [Fact p.Prime] (hg : orderOf g = p) (S : Set V)
    (hS : ∀ s ∈ S, g • s ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ∩ MulAction.fixedBy V g) [MOD p] := by
  classical
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  haveI : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun x => ⟨g • (x : V), hS x.1 x.2⟩
  have hpow : ∀ (m : ℕ) (x : S), ((f ^ m) x : V) = g ^ m • (x : V) := by
    intro m
    induction m with
    | zero => intro x; simp [Function.End.one_def]
    | succ m ih =>
        intro x
        have hrew : f ^ (m + 1) = f^[m + 1] := rfl
        rw [hrew, Function.iterate_succ_apply']
        show g • ((f ^ m) x : V) = g ^ (m + 1) • (x : V)
        rw [ih x, ← mul_smul, ← pow_succ']
  have hfp : f ^ p = 1 := by
    funext x
    apply Subtype.ext
    rw [hpow p x, hgp, one_smul]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) (f := f)
    (by rw [pow_one]; exact hfp)
  have hcard : Nat.card (Function.fixedPoints f) = Nat.card ↥(S ∩ MulAction.fixedBy V g) := by
    apply Nat.card_congr
    have hiff : ∀ x : S, f x = x ↔ g • (x : V) = x :=
      fun x => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    exact (Equiv.subtypeEquivRight hiff).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (· ∈ MulAction.fixedBy V g))
  have hmod' : Nat.card S ≡ Nat.card (Function.fixedPoints f) [MOD p] := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hmod
  rwa [hcard] at hmod'

private theorem card_modEq_card_fixedAdd {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] [Finite K] (g : GL n K) {p : ℕ} [Fact p.Prime] (hg : orderOf g = p) :
    Nat.card (n → K) ≡ Nat.card (fixedAdd g) [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hg, pow_one]
  have h := hP.card_modEq_card_fixedPoints (α := n → K)
  rwa [fixedPoints_zpowers_eq_fixedBy g] at h

private theorem card_modEq_card_inf_fixedAdd {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] [Finite K] (g : GL n K) {p : ℕ} [Fact p.Prime] (hg : orderOf g = p)
    (S : AddSubgroup (n → K)) (hS : ∀ s ∈ S, g • s ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixedAdd g) [MOD p] := by
  have h := card_modEq_card_inter_fixedBy (V := n → K) g hg (S : Set (n → K)) hS
  have hset : (↑(S ⊓ fixedAdd g) : Set (n → K)) = (S : Set (n → K)) ∩
      MulAction.fixedBy (n → K) g := by
    ext x
    simp [fixedAdd, AddSubgroup.mem_inf, MulAction.mem_fixedBy]
  rwa [← hset] at h

private theorem eq_one_of_fixedAdd_eq_top {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] {g : GL n K} (h : fixedAdd g = ⊤) : g = 1 := by
  have hmat : (g : Matrix n n K) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hv : v ∈ fixedAdd g := by rw [h]; exact AddSubgroup.mem_top v
    change v ∈ MulAction.fixedBy (n → K) g at hv
    rw [MulAction.mem_fixedBy, Units.smul_def, Matrix.smul_eq_mulVec] at hv
    rw [hv, Matrix.one_mulVec]
  exact Units.ext hmat

private theorem smul_mem_fixedAdd_of_commute {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] {a b : GL n K} (hab : Commute a b) : ∀ s ∈ fixedAdd b, a • s ∈ fixedAdd b := by
  intro s hs
  change s ∈ MulAction.fixedBy (n → K) b at hs
  change a • s ∈ MulAction.fixedBy (n → K) b
  rw [MulAction.mem_fixedBy] at hs ⊢
  have h1 : b • (a • s) = (b * a) • s := (mul_smul b a s).symm
  have h2 : (b * a) • s = (a * b) • s := by rw [hab.eq]
  have h3 : (a * b) • s = a • (b • s) := mul_smul a b s
  rw [h1, h2, h3, hs]

private lemma eq_four_or_sixtyfour_of_dvd_sixtyfour_modEq_five {m : ℕ} (hdiv : m ∣ 64)
    (hmod : m ≡ 4 [MOD 5]) : m = 4 ∨ m = 64 := by
  obtain ⟨k, hk, hm⟩ :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num) (m := 6) (i := m)).mp (by simpa using hdiv)
  rw [hm] at hmod ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

private lemma eq_one_or_eight_or_sixtyfour_of_dvd_sixtyfour_modEq_seven {m : ℕ} (hdiv : m ∣ 64)
    (hmod : m ≡ 1 [MOD 7]) : m = 1 ∨ m = 8 ∨ m = 64 := by
  obtain ⟨k, hk, hm⟩ :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num) (m := 6) (i := m)).mp (by simpa using hdiv)
  rw [hm] at hmod ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

private lemma eq_of_le_four_of_modEq_four_seven {m : ℕ} (hle : m ≤ 4) (hmod : 4 ≡ m [MOD 7]) :
    m = 4 := by
  interval_cases m <;> simp_all [Nat.ModEq]

theorem false_of_commute_orderOf_five_seven {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    [Finite K] (hV : Nat.card (n → K) = 64) {a b : GL n K} (hab : Commute a b)
    (ha : orderOf a = 5) (hb : orderOf b = 7) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hva : Nat.card (n → K) ≡ Nat.card (fixedAdd a) [MOD 5] :=
    card_modEq_card_fixedAdd (p := 5) a ha
  have hvb : Nat.card (n → K) ≡ Nat.card (fixedAdd b) [MOD 7] :=
    card_modEq_card_fixedAdd (p := 7) b hb
  have hdiva : Nat.card (fixedAdd a) ∣ 64 := by
    have h := AddSubgroup.card_mul_index (fixedAdd a)
    rw [hV] at h
    exact ⟨_, h.symm⟩
  have hdivb : Nat.card (fixedAdd b) ∣ 64 := by
    have h := AddSubgroup.card_mul_index (fixedAdd b)
    rw [hV] at h
    exact ⟨_, h.symm⟩
  have hmoda : Nat.card (fixedAdd a) ≡ 4 [MOD 5] := by
    have h64 : (64 : ℕ) ≡ 4 [MOD 5] := by decide
    rw [hV] at hva
    exact hva.symm.trans h64
  have hmodb : Nat.card (fixedAdd b) ≡ 1 [MOD 7] := by
    have h64 : (64 : ℕ) ≡ 1 [MOD 7] := by decide
    rw [hV] at hvb
    exact hvb.symm.trans h64
  have hCa : Nat.card (fixedAdd a) = 4 := by
    rcases eq_four_or_sixtyfour_of_dvd_sixtyfour_modEq_five hdiva hmoda with h | h
    · exact h
    · exfalso
      have htop : fixedAdd a = ⊤ :=
        AddSubgroup.eq_top_of_card_eq (H := fixedAdd a) (by rw [h, hV])
      rw [eq_one_of_fixedAdd_eq_top htop] at ha
      simp at ha
  have hCb : Nat.card (fixedAdd b) = 1 ∨ Nat.card (fixedAdd b) = 8 := by
    rcases eq_one_or_eight_or_sixtyfour_of_dvd_sixtyfour_modEq_seven hdivb hmodb with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have htop : fixedAdd b = ⊤ :=
        AddSubgroup.eq_top_of_card_eq (H := fixedAdd b) (by rw [h, hV])
      rw [eq_one_of_fixedAdd_eq_top htop] at hb
      simp at hb
  have hstab_a : ∀ s ∈ fixedAdd b, a • s ∈ fixedAdd b := smul_mem_fixedAdd_of_commute hab
  have hstab_b : ∀ s ∈ fixedAdd a, b • s ∈ fixedAdd a := smul_mem_fixedAdd_of_commute hab.symm
  have hsub_b : Nat.card (fixedAdd a) ≡ Nat.card ↥(fixedAdd a ⊓ fixedAdd b) [MOD 7] :=
    card_modEq_card_inf_fixedAdd (p := 7) b hb (fixedAdd a) hstab_b
  rw [hCa] at hsub_b
  have hcardle : Nat.card ↥(fixedAdd a ⊓ fixedAdd b) ≤ 4 := by
    have := AddSubgroup.card_le_of_le (inf_le_left : fixedAdd a ⊓ fixedAdd b ≤ fixedAdd a)
    rwa [hCa] at this
  have hinter : Nat.card ↥(fixedAdd a ⊓ fixedAdd b) = 4 :=
    eq_of_le_four_of_modEq_four_seven hcardle hsub_b
  have hEq : fixedAdd a ⊓ fixedAdd b = fixedAdd a :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinter, hCa])
  have hle_Ca_Cb : fixedAdd a ≤ fixedAdd b := by
    rw [← hEq]
    exact inf_le_right
  have hCb8 : Nat.card (fixedAdd b) = 8 := by
    rcases hCb with h | h
    · have := AddSubgroup.card_le_of_le hle_Ca_Cb
      rw [hCa] at this
      omega
    · exact h
  have hsub_a : Nat.card (fixedAdd b) ≡ Nat.card ↥(fixedAdd b ⊓ fixedAdd a) [MOD 5] :=
    card_modEq_card_inf_fixedAdd (p := 5) a ha (fixedAdd b) hstab_a
  rw [hCb8, inf_comm, hEq, hCa] at hsub_a
  norm_num [Nat.ModEq] at hsub_a

theorem rSp6SmallIndex_holds : RSp6SmallIndex := by
  unfold RSp6SmallIndex
  intro K _ _ hK H hH
  by_contra h3
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hprod : (∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1)) = 2835 := by
    rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
    decide
  have hcardSp : Nat.card (StatedSp 3 K) = 1451520 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 3, hK, hprod]
    norm_num
  have hcardH : Nat.card H * H.index = 1451520 := by
    rw [Subgroup.card_mul_index, hcardSp]
  have hdvd : Nat.card H ∣ 1451520 := ⟨H.index, hcardH.symm⟩
  have hHgt : 5692 < Nat.card H := by
    have hle : 1451520 ≤ Nat.card H * 255 := by
      calc 1451520 = Nat.card H * H.index := hcardH.symm
        _ ≤ Nat.card H * 255 := Nat.mul_le_mul_left _ hH
    omega
  have h3c : Nat.Coprime (Nat.card H) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  have h17920 : Nat.card H ∣ 17920 := by
    have hcop : Nat.Coprime (Nat.card H) (3 ^ 4) := Nat.Coprime.pow_right 4 h3c
    have h145 : Nat.card H ∣ 3 ^ 4 * 17920 := by
      rw [show (3 : ℕ) ^ 4 * 17920 = 1451520 by norm_num]
      exact hdvd
    exact hcop.dvd_of_dvd_mul_left h145
  have h7 : 7 ∣ Nat.card H := by
    by_contra h7
    have h7c : Nat.Coprime (Nat.card H) 7 :=
      ((Nat.prime_seven.coprime_iff_not_dvd).mpr h7).symm
    have h2560 : Nat.card H ∣ 2560 := by
      have h : Nat.card H ∣ 7 * 2560 := by
        rw [show (7 : ℕ) * 2560 = 17920 by norm_num]
        exact h17920
      exact h7c.dvd_of_dvd_mul_left h
    have := Nat.le_of_dvd (by norm_num : 0 < 2560) h2560
    omega
  have h5 : 5 ∣ Nat.card H := by
    by_contra h5
    have h5c : Nat.Coprime (Nat.card H) 5 :=
      ((Nat.prime_five.coprime_iff_not_dvd).mpr h5).symm
    have h3584 : Nat.card H ∣ 3584 := by
      have h : Nat.card H ∣ 5 * 3584 := by
        rw [show (5 : ℕ) * 3584 = 17920 by norm_num]
        exact h17920
      exact h5c.dvd_of_dvd_mul_left h
    have := Nat.le_of_dvd (by norm_num : 0 < 3584) h3584
    omega
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := H)
  have hsq : ¬ 7 ^ 2 ∣ Nat.card H := by
    intro h
    have : 7 ^ 2 ∣ 17920 := h.trans h17920
    norm_num at this
  have hPcard : Nat.card ↥(P : Subgroup H) = 7 :=
    Sylow.card_eq_of_dvd_of_not_sq_dvd P h7 hsq
  have hn7_dvdH : Nat.card (Sylow 7 H) ∣ Nat.card H := by
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.index_dvd_card (Subgroup.normalizer ((P : Subgroup H) : Set H))
  have hn7_dvd : Nat.card (Sylow 7 H) ∣ 17920 := hn7_dvdH.trans h17920
  have hmodn : Nat.card (Sylow 7 H) ≡ 1 [MOD 7] := card_sylow_modEq_one (p := 7) (G := H)
  have hn7_not5 : ¬ 5 ∣ Nat.card (Sylow 7 H) := by
    rintro ⟨c, hc⟩
    have hc_dvd : c ∣ 3584 := by
      have h : 5 * c ∣ 17920 := by
        rw [← hc]
        exact hn7_dvd
      rw [show (17920 : ℕ) = 5 * 3584 by norm_num] at h
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).mp h
    have hc7 : Nat.Coprime c 7 := by
      rw [Nat.coprime_comm]
      refine (Nat.prime_seven.coprime_iff_not_dvd).mpr ?_
      intro h7c
      have hcmod : c % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h7c
      have hzero : Nat.card (Sylow 7 H) % 7 = 0 := by
        rw [hc]
        exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right h7c 5)
      rw [Nat.ModEq, hzero] at hmodn
      norm_num at hmodn
    have hc_dvd512 : c ∣ 2 ^ 9 := by
      have h : c ∣ 7 * 2 ^ 9 := by
        rw [show (7 : ℕ) * 2 ^ 9 = 3584 by norm_num]
        exact hc_dvd
      exact hc7.dvd_of_dvd_mul_left h
    obtain ⟨k, hk, hc2⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hc_dvd512
    rw [hc2] at hc
    rw [hc] at hmodn
    interval_cases k <;> norm_num [Nat.ModEq] at hmodn
  have hcardH_split : Nat.card (Sylow 7 H) * Nat.card
      ↥(Subgroup.normalizer ((P : Subgroup H) : Set H)) = Nat.card H := by
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.index_mul_card (Subgroup.normalizer ((P : Subgroup H) : Set H))
  have h5Norm : 5 ∣ Nat.card ↥(Subgroup.normalizer ((P : Subgroup H) : Set H)) := by
    have h5prod : 5 ∣ Nat.card (Sylow 7 H) * Nat.card
        ↥(Subgroup.normalizer ((P : Subgroup H) : Set H)) := by
      rw [hcardH_split]
      exact h5
    exact (Nat.prime_five.dvd_mul.mp h5prod).resolve_left hn7_not5
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer ((P : Subgroup H) : Set H))) 5 h5Norm
  have h7P : 7 ∣ Nat.card ↥(P : Subgroup H) := by
    simpa [hPcard] using dvd_rfl (7 : ℕ)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup H)) 7 h7P
  let yy : ↥(Subgroup.normalizer ((P : Subgroup H) : Set H)) := y
  have hyy : orderOf yy = 5 := hy
  let φ : MulAut ↥(P : Subgroup H) := Subgroup.normalizerMonoidHom (P : Subgroup H) yy
  have hφ5 : φ ^ 5 = 1 := by
    have hyy5 : yy ^ 5 = 1 := by rw [← hyy]; exact pow_orderOf_eq_one yy
    show (Subgroup.normalizerMonoidHom (P : Subgroup H) yy) ^ 5 = 1
    rw [← map_pow, hyy5, map_one]
  have hφdvd5 : orderOf φ ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hφ5
  haveI hcyc : IsCyclic ↥(P : Subgroup H) := isCyclic_of_prime_card hPcard
  have hAut : Nat.card (MulAut ↥(P : Subgroup H)) = 6 := by
    rw [IsCyclic.card_mulAut (↥(P : Subgroup H)), hPcard]
    decide
  have hφdvd6 : orderOf φ ∣ 6 := by
    have := orderOf_dvd_natCard φ
    rwa [hAut] at this
  have hφ1 : orderOf φ = 1 := by
    have hgcd : Nat.gcd 5 6 = 1 := by norm_num
    exact Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hφdvd5 hφdvd6)
  have hφeq : φ = 1 := orderOf_eq_one_iff.mp hφ1
  have hy_ker : yy ∈ (Subgroup.normalizerMonoidHom (P : Subgroup H)).ker := by
    rw [MonoidHom.mem_ker]
    exact hφeq
  have hy_central : (y : H) ∈ Subgroup.centralizer ((P : Subgroup H) : Set H) := by
    have hker := Subgroup.normalizerMonoidHom_ker (P : Subgroup H)
    rw [hker] at hy_ker
    exact Subgroup.mem_subgroupOf.mp hy_ker
  have hcomm : Commute (x : H) (y : H) :=
    (Subgroup.mem_centralizer_iff.mp hy_central) (x : H) x.2
  have hxH : orderOf (x : H) = 7 := (Subgroup.orderOf_coe x).trans hx
  have hyH : orderOf (y : H) = 5 := (Subgroup.orderOf_coe y).trans hy
  have hxSp : orderOf ((x : H) : ↥(StatedSp 3 K)) = 7 :=
    (Subgroup.orderOf_coe (x : H)).trans hxH
  have hySp : orderOf ((y : H) : ↥(StatedSp 3 K)) = 5 :=
    (Subgroup.orderOf_coe (y : H)).trans hyH
  have hxGL : orderOf (((x : H) : ↥(StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K) = 7 :=
    (Subgroup.orderOf_coe ((x : H) : ↥(StatedSp 3 K))).trans hxSp
  have hyGL : orderOf (((y : H) : ↥(StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K) = 5 :=
    (Subgroup.orderOf_coe ((y : H) : ↥(StatedSp 3 K))).trans hySp
  have hcommSp : Commute ((x : H) : ↥(StatedSp 3 K)) ((y : H) : ↥(StatedSp 3 K)) :=
    hcomm.map (Subgroup.subtype H)
  have hcommGL : Commute (((x : H) : ↥(StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K)
      (((y : H) : ↥(StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K) :=
    hcommSp.map (Subgroup.subtype (StatedSp 3 K))
  have hV : Nat.card (Fin 3 ⊕ Fin 3 → K) = 64 := by
    rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, hK]
    norm_num
  exact false_of_commute_orderOf_five_seven (n := Fin 3 ⊕ Fin 3) (K := K) hV
    hcommGL.symm hyGL hxGL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21
