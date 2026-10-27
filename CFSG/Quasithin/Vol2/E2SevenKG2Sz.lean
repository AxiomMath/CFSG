module

public import CFSG.Quasithin.Vol2.E2SevenBender
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Dihedral.BrauerSuzuki.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem not_three_dvd_card_suzuki (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize 2 ^ (2 * a + 1) = q at hq hq2
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · omega
    · omega
  · omega

theorem three_dvd_two_pow_mul_sq_sub_one (f : ℕ) : 3 ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have h : ¬ 3 ∣ 2 ^ f := fun h =>
    absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hq : (2 ^ f) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1]
  exact Dvd.dvd.mul_left (by omega) _

theorem three_dvd_card_psu3_model {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F)) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hF (n := 3)
    (by norm_num)
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  have h3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_singleton, h3] at h
  have hq2le : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hA : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ f) ^ 2 - 1 := by
    have : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((2 ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq2le]
      ring
    rw [this, Int.toNat_natCast]
  have hB : (((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ f) ^ 3 + 1 := by
    have : (((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((2 ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [hA, hB] at h
  rw [h]
  have hnd : ¬ 3 ∣ 2 ^ f := fun h =>
    absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hq1 : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by omega
  have hsq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have : (2 ^ f) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      rcases hq1 with h1 | h1 <;> rw [h1]
    omega
  generalize 2 ^ f = q at hq1 hsq hq2le ⊢
  rcases hq1 with hq1 | hq1
  ·
    have hg : Nat.gcd 3 (q + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    rw [hg, Nat.div_one]
    exact (hsq.mul_right _).mul_left _
  ·
    have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg]
    have hcube : 3 ∣ q ^ 3 + 1 := by
      have : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq1]
      omega
    have h9 : 3 * 3 ∣ q ^ 3 * (((q ^ 2) - 1) * (q ^ 3 + 1)) :=
      (mul_dvd_mul hsq hcube).mul_left _
    obtain ⟨c, hc⟩ := h9
    rw [hc, show 3 * 3 * c = 3 * (3 * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact dvd_mul_right 3 c

theorem dvd_of_card_suzuki_dvd {a b : ℕ}
    (h : (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) ∣
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) :
    2 * b + 1 ∣ 2 * a + 1 := by
  set k := 2 * b + 1 with hk
  set n := 2 * a + 1 with hn
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hn1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : Odd (2 ^ k - 1) := by
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    exact Nat.odd_iff.mpr (by omega)
  have h1 : 2 ^ k - 1 ∣ (2 ^ n) ^ 2 * ((2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) := by
    rw [← mul_assoc]
    exact ((dvd_mul_left _ _).mul_right _).trans h
  have hcop : Nat.Coprime (2 ^ k - 1) ((2 ^ n) ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd))
  have h2 := hcop.dvd_of_dvd_mul_left h1
  have h4 : (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣ 2 ^ (4 * n) - 1 := by
    refine ⟨2 ^ n + 1, ?_⟩
    rw [show 4 * n = n * 4 by ring, pow_mul]
    generalize 2 ^ n = q at hn1 ⊢
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : (r + 1) ^ 4 = r * ((r + 1) ^ 2 + 1) * (r + 1 + 1) + 1 := by ring
    omega
  have h5 := h2.trans h4
  have h6 : Nat.gcd (2 ^ k - 1) (2 ^ (4 * n) - 1) = 2 ^ k - 1 := Nat.gcd_eq_left h5
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h6
  have hg1 : 1 ≤ 2 ^ Nat.gcd k (4 * n) := Nat.one_le_two_pow
  have h7 : 2 ^ Nat.gcd k (4 * n) = 2 ^ k := by omega
  have h8 : Nat.gcd k (4 * n) = k := Nat.pow_right_injective le_rfl h7
  have h9 : k ∣ 4 * n := h8 ▸ Nat.gcd_dvd_right k (4 * n)
  have hk4 : Nat.Coprime k 4 := by
    have : Nat.Coprime k (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨b, by omega⟩)
    simpa using this
  exact hk4.dvd_of_dvd_mul_left h9

private theorem mem_of_two_pow_of_odd_index {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hN : Odd N.index) {x : X} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) : x ∈ N := by
  obtain ⟨n, hn⟩ := hx
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) N.index := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 : orderOf (QuotientGroup.mk x : X ⧸ N) = 1 :=
    (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

private theorem eq_one_of_two_pow_mem_odd {X : Type*} [Group X] (M : Subgroup X)
    (hM : Odd (Nat.card M)) {m : X} (hm : m ∈ M) (hn : ∃ n : ℕ, m ^ 2 ^ n = 1) : m = 1 := by
  obtain ⟨n, hn⟩ := hn
  have h1 : orderOf m ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf m ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hm
  have hcop : Nat.Coprime (2 ^ n) (Nat.card M) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hM)
  exact orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

private theorem conj_eq_inv_of_fpf {X : Type*} [Group X] (M : Subgroup X) [M.Normal]
    [Finite M] (w : X) (hw : w * w = 1) (hfix : ∀ m ∈ M, w * m * w⁻¹ = m → m = 1) :
    ∀ m ∈ M, w * m * w⁻¹ = m⁻¹ := by
  classical
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  let ψ : M → M := fun m => ⟨(m : X)⁻¹ * (w * m * w⁻¹),
    mul_mem (inv_mem m.2) (Subgroup.Normal.conj_mem inferInstance _ m.2 w)⟩
  have hψ : Function.Injective ψ := by
    intro m m' h
    have h' : (m : X)⁻¹ * (w * m * w⁻¹) = (m' : X)⁻¹ * (w * m' * w⁻¹) := congrArg Subtype.val h
    have hB : w * (m' : X) * w⁻¹ = m' * ((m : X)⁻¹ * (w * m * w⁻¹)) :=
      inv_mul_eq_iff_eq_mul.1 h'.symm
    have hd : w * ((m' : X) * (m : X)⁻¹) * w⁻¹ = (m' : X) * (m : X)⁻¹ := by
      calc w * ((m' : X) * (m : X)⁻¹) * w⁻¹
          = (w * (m' : X) * w⁻¹) * (w * (m : X) * w⁻¹)⁻¹ := by group
        _ = (m' : X) * ((m : X)⁻¹ * (w * m * w⁻¹)) * (w * (m : X) * w⁻¹)⁻¹ := by rw [hB]
        _ = (m' : X) * (m : X)⁻¹ := by group
    have h1 : (m' : X) * (m : X)⁻¹ = 1 := hfix _ (mul_mem m'.2 (inv_mem m.2)) hd
    exact (Subtype.ext (mul_inv_eq_one.1 h1)).symm
  have hsurj := Finite.injective_iff_surjective.1 hψ
  intro m hm
  obtain ⟨⟨n, hn⟩, hnm⟩ := hsurj ⟨m, hm⟩
  have hn' : (n : X)⁻¹ * (w * n * w⁻¹) = m := congrArg Subtype.val hnm
  rw [← hn', hw']
  simp only [mul_inv_rev, inv_inv, mul_assoc, hw', hw, mul_one]

private theorem stronglyEmbedded_inf {Y : Type*} [Group Y] [Finite Y] {B H : Subgroup Y}
    (hB : fusionStronglyEmbedded B) (hHB : ¬ H ≤ B) (hev : ∃ u ∈ H ⊓ B, orderOf u = 2) :
    fusionStronglyEmbedded ((H ⊓ B).subgroupOf H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hHB (htop.trans inf_le_right)
  · obtain ⟨u, hu, hu2⟩ := hev
    have hmem : (⟨u, hu.1⟩ : H) ∈ (H ⊓ B).subgroupOf H := hu
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, hu2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · intro g hg
    have hgB : (g : Y) ∉ B := fun hgB => hg ⟨g.2, hgB⟩
    have hodd := hB.2.2 (g : Y) hgB
    have hle : ((((H ⊓ B).subgroupOf H) ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ≤
        B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨hy1.2, ?_⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy2
      refine Subgroup.mem_map.mpr ⟨(z : Y), hz.2, ?_⟩
      simp
    have hdvd : Nat.card ↥(((H ⊓ B).subgroupOf H ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ∣
        Nat.card ↥(B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom) :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact hodd.of_dvd_nat hdvd

private theorem eq_of_orderOf_two_of_isCyclic' {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at hcard
  exact Finset.card_le_one.1 hcard.le x (by simp [hx]) y (by simp [hy])

theorem fusionIsBenderGroup_sup_map_conj {Y : Type} [Group Y]
    [Finite Y] {q k : ℕ} (hB : fusionBenderBorel Y q k) (P : Sylow 2 Y) {V : Subgroup Y}
    (hVP : V ≤ (P : Subgroup Y)) (hV : ∀ v ∈ V, v ^ 2 = 1) (hV4 : 4 ≤ Nat.card V)
    (hC : ∀ z : Y, orderOf z = 2 → IsPGroup 2 (Subgroup.centralizer {z}))
    {g : Y} (hg : g ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y)) :
    fusionIsBenderGroup ↥(V ⊔ V.map (MulAut.conj g).toMonoidHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := V.map (MulAut.conj g).toMonoidHom with hW
  set H := V ⊔ W with hH
  set B := Subgroup.normalizer ((P : Subgroup Y) : Set Y) with hBdef
  have hBSE : fusionStronglyEmbedded B := (hB P).1
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV x x.2)⟩
  have hV1 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV4
    omega
  obtain ⟨v₁, hv₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
  have hv₁2 : orderOf (v₁ : Y) = 2 := orderOf_eq_prime (by simpa using hV _ v₁.2)
    (fun h => hv₁1 (Subtype.ext h))
  have hzlt : Subgroup.zpowers (v₁ : Y) < V := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr v₁.2) fun h => ?_
    have := congrArg (fun X : Subgroup Y => Nat.card X) h
    simp only [Nat.card_zpowers, hv₁2] at this
    omega
  obtain ⟨v₂, hv₂V, hv₂z⟩ := IsConcreteLE.exists_of_lt hzlt
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂z (h ▸ Subgroup.one_mem _)
  have hv12 : (v₁ : Y) ≠ v₂ := fun h => hv₂z (h ▸ Subgroup.mem_zpowers _)
  have hv₂2 : orderOf v₂ = 2 := orderOf_eq_prime (hV _ hv₂V) hv₂1
  have hv₁V : (v₁ : Y) ∈ V := v₁.2
  have hv₁₂V : (v₁ : Y) * v₂ ∈ V := V.mul_mem hv₁V hv₂V
  have hv₁₂1 : (v₁ : Y) * v₂ ≠ 1 := by
    intro h
    apply hv12
    have h' : (v₁ : Y) = v₂⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h', inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV _ hv₂V)]
  have hv₁₂2 : orderOf ((v₁ : Y) * v₂) = 2 := orderOf_eq_prime (hV _ hv₁₂V) hv₁₂1
  have hconj : ((g • P : Sylow 2 Y) : Subgroup Y) =
      (P : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hWB : ¬ W ≤ B := by
    intro hle
    have hW2 : IsPGroup 2 W := hV2.map _
    have h1 : W ≤ (P : Subgroup Y) := by
      have h2 := IsPGroup.to_sup_of_normal_right' hW2 P.isPGroup' hle
      have := P.is_maximal' h2 le_sup_right
      rw [← this]
      exact le_sup_left
    have h2 : W ≤ ((g • P : Sylow 2 Y) : Subgroup Y) := by
      rw [hconj]
      exact Subgroup.map_mono hVP
    have h0 := sylow_inf_smul_eq_bot hB P hg
    have hmem : g * v₁ * g⁻¹ ∈ W := ⟨v₁, hv₁V, by simp [MulAut.conj_apply]⟩
    have : g * v₁ * g⁻¹ ∈ (P : Subgroup Y) ⊓ ((g • P : Sylow 2 Y) : Subgroup Y) :=
      ⟨h1 hmem, h2 hmem⟩
    rw [h0, Subgroup.mem_bot] at this
    apply hv₁1
    apply Subtype.ext
    have := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using this
  have hHB : ¬ H ≤ B := fun h => hWB (le_sup_right.trans h)
  have hev : ∃ u ∈ H ⊓ B, orderOf u = 2 :=
    ⟨v₁, ⟨le_sup_left (a := V) hv₁V, Subgroup.le_normalizer (hVP hv₁V)⟩, hv₁2⟩
  have hSE := stronglyEmbedded_inf hBSE hHB hev
  have hVH : V ≤ H := le_sup_left
  let x₁ : ↥H := ⟨v₁, hVH hv₁V⟩
  let x₂ : ↥H := ⟨v₂, hVH hv₂V⟩
  have hx₁2 : orderOf x₁ = 2 := by rw [Subgroup.orderOf_mk]; exact hv₁2
  have hx₂2 : orderOf x₂ = 2 := by rw [Subgroup.orderOf_mk]; exact hv₂2
  have hx₁₂2 : orderOf (x₁ * x₂) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hv₁₂2
  have hx12 : x₁ ≠ x₂ := fun h => hv12 (congrArg Subtype.val h)
  rcases CFSG.Open.bender_strongly_embedded_normal_series ↥H _ hSE with
    hlow | ⟨M, N, hMn, hNn, hMN', -, hMo, hNo, hBen⟩
  ·
    exfalso
    have hV2' : IsPGroup 2 (V.subgroupOf H) :=
      hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
    obtain ⟨Q, hQ⟩ := hV2'.exists_le_sylow
    have hx₁Q : x₁ ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hv₁V)
    have hx₂Q : x₂ ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hv₂V)
    rcases hlow Q with hcyc | ⟨r, -, he⟩
    · have h1 : orderOf (⟨x₁, hx₁Q⟩ : (Q : Subgroup ↥H)) = 2 := by
        rw [Subgroup.orderOf_mk, hx₁2]
      have h2 : orderOf (⟨x₂, hx₂Q⟩ : (Q : Subgroup ↥H)) = 2 := by
        rw [Subgroup.orderOf_mk, hx₂2]
      exact hx12 (congrArg Subtype.val (eq_of_orderOf_two_of_isCyclic' h1 h2))
    · exact hx12 (CFSG.BrauerSuzuki.Helpers.unique_order_two_in_quaternion_sylow r Q he hx₁Q hx₂Q
        hx₁2 hx₂2)
  ·
    have hNtop : N = ⊤ := by
      have hVN : V.subgroupOf H ≤ N := fun x hx =>
        mem_of_two_pow_of_odd_index N hNo ⟨1, Subtype.ext (by
          simpa using hV _ (Subgroup.mem_subgroupOf.mp hx))⟩
      have hWN : W.subgroupOf H ≤ N := by
        intro x hx
        refine mem_of_two_pow_of_odd_index N hNo ⟨1, Subtype.ext ?_⟩
        obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        have : ((x : ↥H) : Y) ^ 2 = 1 := by
          rw [← hvx, ← map_pow, hV v hv, map_one]
        simpa using this
      have hsup : V.subgroupOf H ⊔ W.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      exact top_le_iff.mp (hsup ▸ sup_le hVN hWN)
    have hfpf : ∀ w : ↥H, orderOf w = 2 → ∀ m ∈ M, w * m * w⁻¹ = m → m = 1 := by
      intro w hw m hm hfix
      apply eq_one_of_two_pow_mem_odd M hMo hm
      have hw' : orderOf (w : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
      have hmc : ((m : ↥H) : Y) ∈ Subgroup.centralizer {(w : Y)} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : w * m = m * w := by
          rw [mul_inv_eq_iff_eq_mul] at hfix
          exact hfix
        exact (congrArg Subtype.val h1).symm
      obtain ⟨n, hn⟩ := hC _ hw' ⟨_, hmc⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    have hinv : ∀ w : ↥H, orderOf w = 2 → ∀ m ∈ M, w * m * w⁻¹ = m⁻¹ := fun w hw =>
      conj_eq_inv_of_fpf M w (by rw [← pow_two, ← hw, pow_orderOf_eq_one]) (hfpf w hw)
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      rw [Subgroup.mem_bot]
      apply hfpf _ hx₁₂2 m hm
      calc x₁ * x₂ * m * (x₁ * x₂)⁻¹ = x₁ * (x₂ * m * x₂⁻¹) * x₁⁻¹ := by group
        _ = x₁ * m⁻¹ * x₁⁻¹ := by rw [hinv x₂ hx₂2 m hm]
        _ = (x₁ * m * x₁⁻¹)⁻¹ := by group
        _ = m := by rw [hinv x₁ hx₁2 m hm, inv_inv]
    subst hMbot
    let e : ↥N ⧸ (⊥ : Subgroup ↥H).subgroupOf N ≃* ↥H :=
      ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf N)).trans
        QuotientGroup.quotientBot).trans ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv)
    rcases hBen with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
    · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
    · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
    · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

variable {G : Type} [Group G] [Finite G]

theorem fusionIsBenderGroup_sup_conjSub {K S V : Subgroup G}
    {q k : ℕ} (hB : fusionBenderBorel ↥K q k) (hS : IsSylowTwoOf S K) (hVS : V ≤ S)
    (hV : ∀ v ∈ V, v ^ 2 = 1) (hV4 : 4 ≤ Nat.card V)
    (hC : ∀ z ∈ K, orderOf z = 2 → IsPGroup 2 ↥(K ⊓ Subgroup.centralizer {z}))
    {g : G} (hgK : g ∈ K) (hgN : g ∉ Subgroup.normalizer (S : Set G)) :
    fusionIsBenderGroup ↥(V ⊔ conjSub g V) := by
  have hVK : V ≤ K := hVS.trans hS.1
  set P := toSylow2 hS
  have hPc : (P : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set V' := V.subgroupOf K with hV'
  have hVP : V' ≤ (P : Subgroup ↥K) := by
    rw [hPc]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hVS (Subgroup.mem_subgroupOf.mp hx))
  have hV2' : ∀ v ∈ V', v ^ 2 = 1 := fun v hv =>
    Subtype.ext (by simpa using hV _ (Subgroup.mem_subgroupOf.mp hv))
  have hV4' : 4 ≤ Nat.card V' := by
    rw [hV', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
    exact hV4
  have hC' : ∀ z : ↥K, orderOf z = 2 → IsPGroup 2 (Subgroup.centralizer {z}) := by
    intro z hz x
    have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
    have hxc : (((x : ↥K) : G)) ∈ K ⊓ Subgroup.centralizer {(z : G)} := by
      refine ⟨(x : ↥K).2, ?_⟩
      show ((x : ↥K) : G) ∈ Subgroup.centralizer {(z : G)}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp x.2
      exact congrArg Subtype.val this
    obtain ⟨n, hn⟩ := hC _ z.2 hz' ⟨_, hxc⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  set g' : ↥K := ⟨g, hgK⟩
  have hg' : g' ∉ Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) := by
    intro h
    apply hgN
    rw [Subgroup.mem_normalizer_iff] at h ⊢
    intro z
    constructor
    · intro hz
      have h1 := (h ⟨z, hS.1 hz⟩).mp (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hz
      have hzK : z ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hgK) (hS.1 hz)) hgK
        simpa [mul_assoc] using this
      have h1 := (h ⟨z, hzK⟩).mpr (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h1
      exact Subgroup.mem_subgroupOf.mp h1
  have hBen := fusionIsBenderGroup_sup_map_conj hB P hVP hV2' hV4' hC' hg'
  have hmap : (V' ⊔ V'.map (MulAut.conj g').toMonoidHom).map K.subtype = V ⊔ conjSub g V := by
    rw [Subgroup.map_sup, hV', Subgroup.subgroupOf_map_subtype, inf_of_le_left hVK]
    congr 1
    ext x
    rw [mem_conjSub]
    constructor
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      have hv' := Subgroup.mem_subgroupOf.mp hv
      simpa [MulAut.conj_apply, g', mul_assoc] using hv'
    · intro hx
      have hxK : x ∈ K := by
        have := K.mul_mem (K.mul_mem hgK (hVK hx)) (K.inv_mem hgK)
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxK⟩, ⟨⟨g⁻¹ * x * g, hVK hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩, rfl⟩
      apply Subtype.ext
      simp [MulAut.conj_apply, g', mul_assoc]
  let e : ↥(V' ⊔ V'.map (MulAut.conj g').toMonoidHom) ≃* ↥(V ⊔ conjSub g V) :=
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  rcases hBen with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem kgBenderSubSz_holds :
    KGBenderSubSz := by
  intro G _ _ K S V n g hn hK hS hVS hVC hV hV4 hgK hgN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hB⟩ :=
    exists_fusionBenderBorel_of_isBenderOf (⟨hn, Or.inr (Or.inl hK)⟩ : IsBenderOf n ↥K)
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := hK
  have : Finite ↥(CFSG.Blueprint.suzukiGroup a F) := Finite.of_equiv ↥K e.toEquiv
  have hC : ∀ z ∈ K, orderOf z = 2 → IsPGroup 2 ↥(K ⊓ Subgroup.centralizer {z}) := by
    intro z hzK hz x
    set z' := e ⟨z, hzK⟩
    have hz' : orderOf z' = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hz
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 ↥(CFSG.Blueprint.suzukiGroup a F),
        Subgroup.zpowers z' ≤ Q := by
      refine IsPGroup.exists_le_sylow (IsPGroup.of_card (n := 1) ?_)
      rw [Nat.card_zpowers, hz', pow_one]
    have hcent := CFSG.RankThree.centralizer_eq_sylow hcard hz' Q (hQ (Subgroup.mem_zpowers _))
    have hx : e ⟨(x : G), (x.2 : (x : G) ∈ K ⊓ _).1⟩ ∈ Subgroup.centralizer {z'} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (x.2 : (x : G) ∈ K ⊓ _).2
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    rw [hcent] at hx
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨_, hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (e ⟨(x : G), (x.2 : (x : G) ∈ K ⊓ _).1⟩) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
    simpa using congrArg Subtype.val h1
  have hBen := fusionIsBenderGroup_sup_conjSub hB hS hVS hV.2 hV4 hC hgK hgN
  have hIK : V ⊔ conjSub g V ≤ K := by
    refine sup_le (hVS.trans hS.1) fun x hx => ?_
    rw [mem_conjSub] at hx
    have := K.mul_mem (K.mul_mem hgK (hS.1 (hVS hx))) (K.inv_mem hgK)
    simpa [mul_assoc] using this
  have hdvd : Nat.card ↥(V ⊔ conjSub g V) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hIK
  have hKcard : Nat.card ↥K =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Ree.suzuki_order hcard
  have h3K : ¬ 3 ∣ Nat.card ↥K := hKcard ▸ not_three_dvd_card_suzuki a
  rcases hBen with ⟨f, hf, ⟨eI⟩⟩ | ⟨f, hf, ⟨eI⟩⟩ | ⟨b, hb, ⟨eI⟩⟩
  ·
    exfalso
    apply h3K
    refine dvd_trans ?_ hdvd
    rw [Nat.card_congr eI.toEquiv]
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hc := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField 2 f)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1), hF, mul_one] at hc
    rw [hc]
    exact three_dvd_two_pow_mul_sq_sub_one f
  ·
    exfalso
    apply h3K
    refine dvd_trans ?_ hdvd
    have hF : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) :=
      GaloisField.card 2 (2 * f) (by omega)
    have hF' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
    rw [Nat.card_congr (eI.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative
      (K := GaloisField 2 (2 * f)) f hf hF).symm).toEquiv]
    exact three_dvd_card_psu3_model (by omega) hF'
  ·
    have hF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
      GaloisField.card 2 (2 * b + 1) (by omega)
    let eSz : ↥(CFSG.Blueprint.suzukiGroup b (GaloisField 2 (2 * b + 1))) ≃* ↥(Sz b) :=
      (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup b _)).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative b hb hF)
    have hIcard : Nat.card ↥(V ⊔ conjSub g V) =
        (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) := by
      rw [Nat.card_congr (eI.trans eSz.symm).toEquiv]
      exact CFSG.LieType.Ree.suzuki_order hF
    refine ⟨2 * b + 1, by omega, dvd_of_card_suzuki_dvd (hIcard ▸ hKcard ▸ hdvd), Or.inr ?_⟩
    exact ⟨rfl, b, hb, GaloisField 2 (2 * b + 1), inferInstance, inferInstance, rfl, hF,
      ⟨eI.trans eSz.symm⟩⟩

end E2

end CFSG.Quasithin
