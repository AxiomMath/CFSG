module

public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXF
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def L3BorelFacts : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Y : Type) [Group Y] [Finite Y] (X U : Subgroup Y),
    Group.IsPerfect ↥X → IsPSL 3 2 n (↥X ⧸ Subgroup.center ↥X) → IsSylowTwoOf U X →
      Nat.card ↥(Subgroup.center ↥X) ∣ Nat.gcd 3 (2 ^ n - 1) ∧
      Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) * Nat.gcd 3 (2 ^ n - 1) =
        Nat.card ↥U * (2 ^ n - 1) ^ 2 * Nat.card ↥(Subgroup.center ↥X) ∧
      (∀ a ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        a * b * a⁻¹ * b⁻¹ ∈ U) ∧
      (∀ A : Subgroup Y, A ≤ X → U ≤ A → Group.IsSolvable ↥A →
        A ≤ X ⊓ Subgroup.normalizer (U : Set Y)) ∧
      (Even n → ¬ 3 ∣ n →
        ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
          (∃ c ∈ X ⊓ Subgroup.normalizer (U : Set Y), c ∉ U ∧ c ^ 3 ∈ U ∧ r * c * r⁻¹ * c ∈ U) →
          ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (n / 2) + 1 →
            ∃ b ∈ X ⊓ Subgroup.normalizer (U : Set Y), b ^ p ∈ U ∧ r * b * r⁻¹ * b⁻¹ ∉ U)

theorem three_dvd_card_isPSL3 {X : Type} [Group X] {n : ℕ} (h : IsPSL 3 2 n X) :
    3 ∣ Nat.card X := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  simp only [show 3 * (3 - 1) / 2 = 3 by norm_num]
  set q : ℕ := 2 ^ n with hq
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have : ∀ m : ℕ, 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
      intro m
      induction m with
      | zero => norm_num
      | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num
    exact this n
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  rcases hq3 with h1 | h1
  ·
    obtain ⟨a, ha⟩ : ∃ a, q = 3 * a + 1 := ⟨q / 3, by omega⟩
    have hg : Nat.gcd 3 (q - 1) = 3 := by
      rw [ha]; exact Nat.gcd_eq_left ⟨a, by omega⟩
    rw [hg]
    have h3 : 3 ∣ (q ^ 2 - 1) := by
      rw [ha]
      have : (3 * a + 1) ^ 2 - 1 = 3 * (3 * a ^ 2 + 2 * a) := by
        have : 1 ≤ (3 * a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this]; ring
      rw [this]; exact Dvd.intro _ rfl
    have h3' : 3 ∣ (q ^ 3 - 1) := by
      rw [ha]
      have : (3 * a + 1) ^ 3 - 1 = 3 * (9 * a ^ 3 + 9 * a ^ 2 + 3 * a) := by
        have : 1 ≤ (3 * a + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        zify [this]; ring
      rw [this]; exact Dvd.intro _ rfl
    have h9 : 3 * 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Dvd.dvd.mul_left (mul_dvd_mul h3 h3') _
    have := Nat.dvd_div_of_mul_dvd (show 3 * 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) from h9)
    exact this
  ·
    obtain ⟨a, ha⟩ : ∃ a, q = 3 * a + 2 := ⟨q / 3, by omega⟩
    have hg : Nat.gcd 3 (q - 1) = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).gcd_eq_one
    rw [hg, Nat.div_one]
    have h3 : 3 ∣ q ^ 2 - 1 := by
      rw [ha]
      have : (3 * a + 2) ^ 2 - 1 = 3 * (3 * a ^ 2 + 4 * a + 1) := by
        have : 1 ≤ (3 * a + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this]; ring
      rw [this]; exact Dvd.intro _ rfl
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _

theorem isSolvable_sup_of_le_normalizer' {Γ : Type*} [Group Γ] {T D : Subgroup Γ}
    (hD : D ≤ Subgroup.normalizer (T : Set Γ)) (hT : Group.IsSolvable T)
    (hD' : Group.IsSolvable D) : Group.IsSolvable ↥(D ⊔ T) := by
  have hnorm : (T.subgroupOf (D ⊔ T)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hD
  have hnormD : (T.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hD
  have hker : (QuotientGroup.mk' (T.subgroupOf (D ⊔ T))).ker ≤
      (T.subgroupOf (D ⊔ T)).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  let e₁ := Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ D ⊔ T)
  have h1 : Group.IsSolvable ↥(T.subgroupOf (D ⊔ T)) :=
    Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient D T hD
  have h2 : Group.IsSolvable (↥(D ⊔ T) ⧸ T.subgroupOf (D ⊔ T)) := by
    have : Group.IsSolvable (↥D ⧸ T.subgroupOf D) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := e₂.toMonoidHom) e₂.surjective
  exact Group.isSolvable_of_ker_le_range _ _ hker

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_inverted_c {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hcB : Ls ⊓ X ≤ borel X Ts) :
    ∃ (r c : Y), r ∈ Tls ∧
      r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ∧
      c ∈ borel X Ts ∧ c ∉ Ts ⊓ X ∧ c ^ 3 = 1 ∧ r * c * r⁻¹ * c ∈ Ts ⊓ X := by
  obtain ⟨hR, hTs, hP, hnormal, hTsMs, hBM, hKM, hLM, -, -, hTlsTs, r, hrTls, S, hSL, hSe, hS9,
    hSinv⟩ := h
  haveI : X.Normal := hnormal
  have hXn : ∀ x : Y, x ∈ Subgroup.normalizer (X : Set Y) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.2 hnormal]
    exact Subgroup.mem_top x
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal hTs le_top Subgroup.le_normalizer_of_normal
  have hUB : Ts ⊓ X ≤ borel X Ts := le_inf inf_le_right Subgroup.le_normalizer
  have hBN : borel X Ts ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := inf_le_right
  have hSylB : IsSylowTwoOf (Ts ⊓ X) (borel X Ts) :=
    A4.isSylowTwoOf_mono hSylX hUB inf_le_left
  have hS3 : ∀ x ∈ S, x ^ 3 = 1 := hSe.2
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hS3 g g.2)⟩
  obtain ⟨y, hyX, hyo, hyc⟩ := exists_centralizes_order_three hSp
    (fun s _ => hXn s) hP
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; omega
  have hyS : y ∈ S := by
    by_contra hyS
    obtain ⟨u, v, huS, hvS, hu1, hu3, hv3, hvu⟩ := exists_indep_pair hSe hS9
    have hcu : Commute u y := by
      have := hyc u huS
      exact (calc u * y = (u * y * u⁻¹) * u := by group
        _ = y * u := by rw [this])
    have hcv : Commute v y := by
      have := hyc v hvS
      exact (calc v * y = (v * y * v⁻¹) * v := by group
        _ = y * v := by rw [this])
    have hcuv : Commute u v := hScomm u huS v hvS
    refine hR u v y hu3 hv3 hy3 hcuv hcu hcv ?_
    intro a b c habc
    have hyc' : y ^ c = (u ^ a * v ^ b)⁻¹ := eq_inv_of_mul_eq_one_right habc
    have hmem : y ^ c ∈ S := by
      rw [hyc']
      exact S.inv_mem (S.mul_mem (S.pow_mem huS a) (S.pow_mem hvS b))
    have h3c : 3 ∣ c := by
      by_contra h3c
      apply hyS
      have hmod : c % 3 = 1 ∨ c % 3 = 2 := by omega
      have hpow : y ^ c = y ^ (c % 3) := by
        conv_lhs => rw [← Nat.div_add_mod c 3, pow_add, pow_mul, hy3, one_pow, one_mul]
      rcases hmod with h1 | h1
      · rw [hpow, h1, pow_one] at hmem
        exact hmem
      · rw [hpow, h1] at hmem
        have : y = (y ^ 2) ^ 2 := by
          calc y = y ^ 3 * y := by rw [hy3, one_mul]
            _ = (y ^ 2) ^ 2 := by group
        rw [this]
        exact S.pow_mem hmem 2
    have hyc1 : y ^ c = 1 := by
      obtain ⟨t, rfl⟩ := h3c
      rw [pow_mul, hy3, one_pow]
    rw [hyc1] at hyc'
    obtain ⟨ha, hb⟩ := indep_of_not_mem_zpowers hu3 hu1 hv3 hvu (inv_eq_one.1 hyc'.symm)
    exact ⟨ha, hb, h3c⟩
  have hcB' : y ∈ borel X Ts := hcB ⟨hSL hyS, hyX⟩
  have hrTs : r ∈ Ts := hTlsTs hrTls
  have hrU : r ∈ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hrTs) x
    have h2 := Subgroup.mem_normalizer_iff.1 (hXn r) x
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  have hO2 : pCoreOf 2 Ls ⊓ X ≤ Ts ⊓ X :=
    le_of_normal_sylow hSylB hBN (fun x hx => hcB ⟨pCoreOf_le 2 Ls hx.1, hx.2⟩)
      (pCoreOf_isPGroup 2 Ls).to_inf_left
  have hcU : y ∉ Ts ⊓ X := fun hh => hy1 (eq_one_of_pow_three hTs.2.1 hh.1 hy3)
  have hinvU : r * y * r⁻¹ * y ∈ Ts ⊓ X := by
    have h1 := hSinv y hyS
    refine hO2 ⟨h1, ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 (hXn r) y).1 hyX
    exact X.mul_mem h2 hyX
  exact ⟨r, y, hrTls, ⟨hXn r, hrU⟩, hcB', hcU, hy3, hinvU⟩

theorem le_borel_of_solvBorel {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hSB : ∀ A : Subgroup Y, A ≤ X → Ts ⊓ X ≤ A → Group.IsSolvable ↥A →
      A ≤ X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y)) :
    Ls ⊓ X ≤ borel X Ts := by
  have hnormal : X.Normal := h.normal
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top Subgroup.le_normalizer_of_normal
  have hUN : Ts ⊓ X ≤ Subgroup.normalizer ((Ls ⊓ X : Subgroup Y) : Set Y) := by
    intro u hu
    have hu1 := h.Ts_norm_Ls hu.1
    have hu2 : u ∈ Subgroup.normalizer (X : Set Y) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hnormal]
      exact Subgroup.mem_top u
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 hu1 x
    have h2 := Subgroup.mem_normalizer_iff.1 hu2 x
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  have hAs : Group.IsSolvable ↥(Ls ⊓ X) := by
    haveI := h.Ls_solvable
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : Ls ⊓ X ≤ Ls))
  have hUs : Group.IsSolvable ↥(Ts ⊓ X) := by
    haveI := hSylX.2.1.isNilpotent
    infer_instance
  have hsol := isSolvable_sup_of_le_normalizer' hUN hAs hUs
  have hle := hSB _ (sup_le inf_le_right inf_le_right) le_sup_left hsol
  exact le_sup_right.trans hle

theorem false_of_single_L3_odd (hL : L3BorelFacts) {n : ℕ} (hn : 3 ≤ n) (hodd : ¬ Even n)
    {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X) (hperf : Group.IsPerfect ↥X)
    (hX : IsPSL 3 2 n (↥X ⧸ Subgroup.center ↥X)) : False := by
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top (by
      haveI := h.normal
      exact Subgroup.le_normalizer_of_normal)
  obtain ⟨hZ, hcard, -, hSB, -⟩ := hL n hn Y X (Ts ⊓ X) hperf hX hSylX
  obtain ⟨r, c, -, -, hcB, hcU, hc3, -⟩ := exists_inverted_c h (le_borel_of_solvBorel h hSB)
  have h3 : ¬ 3 ∣ 2 ^ n - 1 := fun h3 => hodd (P31NT.three_dvd_two_pow_sub_one_iff.1 h3)
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).gcd_eq_one
  rw [hg] at hZ hcard
  have hZ1 : Nat.card ↥(Subgroup.center ↥X) = 1 := Nat.dvd_one.1 hZ
  rw [hZ1, mul_one, mul_one] at hcard
  have hc1 : c ≠ 1 := fun h1 => hcU (h1 ▸ (Ts ⊓ X).one_mem)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hd : 3 ∣ Nat.card ↥(borel X Ts) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hcB
  have hB : Nat.card ↥(borel X Ts) = Nat.card ↥(Ts ⊓ X) * (2 ^ n - 1) ^ 2 := by
    rw [show (borel X Ts) = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) from rfl]
    exact hcard
  rw [hB] at hd
  obtain ⟨a, ha⟩ := hSylX.2.1.exists_card_eq
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h1 | h1
  · rw [ha] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  · exact h3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)

theorem false_of_single_L3_three_dvd (hL : L3BorelFacts) {n : ℕ} (hn : 3 ≤ n) (hev : Even n)
    (h3n : 3 ∣ n) {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hperf : Group.IsPerfect ↥X) (hX : IsPSL 3 2 n (↥X ⧸ Subgroup.center ↥X))
    (h27 : ¬ 27 ∣ Nat.card ↥Ms) : False := by
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top (by
      haveI := h.normal
      exact Subgroup.le_normalizer_of_normal)
  obtain ⟨hZ, hcard, -, -, -⟩ := hL n hn Y X (Ts ⊓ X) hperf hX hSylX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv := P31NT.padicValNat_three_two_pow_sub_one hev (by omega)
  have hv3 : 1 ≤ padicValNat 3 n := one_le_padicValNat_of_dvd (by omega) h3n
  have hpos : 2 ^ n - 1 ≠ 0 := by
    have : 4 ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h9 : 3 ^ 2 ∣ 2 ^ n - 1 := (padicValNat_dvd_iff_le hpos).2 (by omega)
  have h3d : 3 ∣ 2 ^ n - 1 := (dvd_pow_self 3 (by norm_num)).trans h9
  have hg : Nat.gcd 3 (2 ^ n - 1) = 3 := Nat.gcd_eq_left h3d
  rw [hg] at hcard
  have h81 : 3 ^ 4 ∣ (2 ^ n - 1) ^ 2 := by
    have := pow_dvd_pow_of_dvd h9 2
    rwa [← pow_mul] at this
  have h81' : 3 ^ 4 ∣ Nat.card ↥(borel X Ts) * 3 := by
    rw [show (borel X Ts) = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) from rfl, hcard]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h81 _) _
  have h27B : 27 ∣ Nat.card ↥(borel X Ts) := by
    have : 27 * 3 ∣ Nat.card ↥(borel X Ts) * 3 := by simpa using h81'
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  exact h27 (h27B.trans (Subgroup.card_dvd_of_le h.borel_le))

theorem permData_of_single_L3 (hL : L3BorelFacts) {n : ℕ} (hn : 3 ≤ n) (hev : Even n)
    (h3n : ¬ 3 ∣ n) {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X)
    (hperf : Group.IsPerfect ↥X) (hX : IsPSL 3 2 n (↥X ⧸ Subgroup.center ↥X)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ (n / 2) + 1) : PermData Ts Ms Tls := by
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top (by
      haveI := h.normal
      exact Subgroup.le_normalizer_of_normal)
  obtain ⟨hZ, hcard, habel, hSB, hmov⟩ := hL n hn Y X (Ts ⊓ X) hperf hX hSylX
  obtain ⟨r, c, hrTls, hrN, hcB, hcU, hc3, hinv⟩ :=
    exists_inverted_c h (le_borel_of_solvBorel h hSB)
  have hUB : Ts ⊓ X ≤ borel X Ts := le_inf inf_le_right Subgroup.le_normalizer
  have hBN : borel X Ts ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := inf_le_right
  have hc3U : c ^ 3 ∈ Ts ⊓ X := by rw [hc3]; exact (Ts ⊓ X).one_mem
  obtain ⟨b, hbB, hbp, hbr⟩ := hmov hev h3n r hrN ⟨c, hcB, hcU, hc3U, hinv⟩ p hp hp5 hpk
  have hXn : ∀ x : Y, x ∈ Subgroup.normalizer (X : Set Y) := fun x => by
    haveI := h.normal
    rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
    exact Subgroup.mem_top x
  have hbr' : b * r * b⁻¹ * r⁻¹ ∉ Ts ⊓ X := fun hh => hbr (by
    have := (Ts ⊓ X).inv_mem hh
    rwa [show (b * r * b⁻¹ * r⁻¹)⁻¹ = r * b * r⁻¹ * b⁻¹ by group] at this)
  refine permData_build (n := b) hp (by omega) hUB hBN habel h.borel_le ?_ ?_ inf_le_left hbB hbp
    hrTls hbr'
  · intro t ht b' hb
    have htU : t ∈ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) x
      have h2 := Subgroup.mem_normalizer_iff.1 (hXn t) x
      exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hXn t) b').1 hb.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htU (hBN hb)) (Subgroup.inv_mem _ htU)
  · intro t ht u hu
    exact ⟨Ts.mul_mem (Ts.mul_mem ht hu.1) (Ts.inv_mem ht),
      (Subgroup.mem_normalizer_iff.1 (hXn t) u).1 hu.2⟩

end Y

end CFSG.Quasithin.H13.P31X
