module

public import CFSG.Walter.ReeOrder.JT.Section4C

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups IsMulCommutative Pointwise

section PSL24

variable {L : Type*} [Group L]

theorem card_of_psl24 (e : L ≃* PSL(2, GaloisField 2 2)) : Nat.card L = 60 := by
  rw [Nat.card_congr e.toEquiv]
  have hK : Nat.card (GaloisField 2 2) = 4 := by rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

theorem isSimpleGroup_of_psl24 (e : L ≃* PSL(2, GaloisField 2 2)) : IsSimpleGroup L := by
  have : IsSimpleGroup PSL(2, GaloisField 2 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 2 (by norm_num)]; norm_num)
  exact e.isSimpleGroup

theorem orderOf_dvd_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2)) (x : L) :
    orderOf x ∣ 4 ∨ orderOf x ∣ 3 ∨ orderOf x ∣ 5 := by
  set K := GaloisField 2 2
  have hK : Nat.card K = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  by_cases hx : e x = 1
  · left
    rw [← MulEquiv.orderOf_eq e, hx, orderOf_one]
    exact one_dvd _
  let P : Sylow 2 PSL(2, K) := default
  obtain ⟨U, S, -, hU, -, hS, hpart⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_5_a_psl2_cover (F := K) (p := 2) (f := 2) hK P
  rw [hK] at hU hS
  norm_num at hU hS
  have hP : Nat.card (P : Subgroup PSL(2, K)) = 4 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.symm.toEquiv, card_of_psl24 e,
      show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  obtain ⟨T, ⟨hxT, hT⟩, -⟩ := hpart (e x) hx
  rw [← MulEquiv.orderOf_eq e]
  rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · left
    have := Subgroup.orderOf_dvd_natCard _ hxT
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP] at this
  · right; left
    have := Subgroup.orderOf_dvd_natCard _ hxT
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU] at this
  · right; right
    have := Subgroup.orderOf_dvd_natCard _ hxT
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS] at this

theorem eq_one_of_commute_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2)) {x y : L}
    (hx : Odd (orderOf x)) (hy : orderOf y = 2) (hxy : x * y = y * x) : x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (orderOf y) := by
    rw [hy]
    exact Nat.coprime_two_right.mpr hx
  have hord := Commute.orderOf_mul_eq_mul_orderOf_of_coprime hxy hcop
  rw [hy] at hord
  have hx3 : orderOf x ∣ 15 := by
    have h60 : orderOf x ∣ 60 := card_of_psl24 e ▸ orderOf_dvd_natCard x
    have : Nat.Coprime (orderOf x) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hx)
    exact this.dvd_of_dvd_mul_left (by simpa [show (60 : ℕ) = 4 * 15 by norm_num] using h60)
  rcases orderOf_dvd_of_psl24 e (x * y) with h | h | h <;> rw [hord] at h
  all_goals
    have : orderOf x ∣ 15 := hx3
    have hpos : 0 < orderOf x := orderOf_pos x
    have hle : orderOf x ≤ 15 := Nat.le_of_dvd (by norm_num) hx3
    interval_cases hk : orderOf x <;> first | (exact orderOf_eq_one_iff.mp hk) | omega

theorem card_sylow_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2)) (P : Sylow 2 L) :
    Nat.card (P : Subgroup L) = 4 := by
  rw [Sylow.card_eq_multiplicity, card_of_psl24 e,
    show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem isKleinFour_sylow_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2))
    (P : Sylow 2 L) : IsKleinFour (P : Subgroup L) := by
  have hP := card_sylow_of_psl24 e P
  have hsimple := isSimpleGroup_of_psl24 e
  refine ⟨hP, ?_⟩
  have hncyc : ¬ IsCyclic (P : Subgroup L) := by
    intro hcyc
    have hmin : (Nat.card L).minFac = 2 := by rw [card_of_psl24 e]; norm_num
    have hcomp := IsCyclic.isComplement' hmin hcyc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MonoidHom.transferSylow P _).ker with hb | ht
    · have := hcomp.card_mul_card
      rw [hb, Subgroup.card_bot, one_mul, hP, card_of_psl24 e] at this
      omega
    · have := hcomp.card_mul_card
      rw [ht, Subgroup.card_top, hP, card_of_psl24 e] at this
      omega
  have hpow : ∀ y : (P : Subgroup L), y ^ 2 = 1 := by
    intro y
    have hd : orderOf y ∣ 4 := hP ▸ orderOf_dvd_natCard y
    have hne : orderOf y ≠ 4 := fun h4 =>
      hncyc (isCyclic_of_orderOf_eq_card y (by rw [h4, hP]))
    have : orderOf y ∣ 2 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4] at hd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      interval_cases k
      · rw [hk']; exact one_dvd 2
      · rw [hk']; norm_num
      · exact absurd (by rw [hk']; norm_num) hne
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdvd : Monoid.exponent (P : Subgroup L) ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton (P : Subgroup L) := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := (P : Subgroup L))
    omega
  · exact h2

theorem centralizer_le_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2)) (P : Sylow 2 L)
    {y : L} (hyP : y ∈ P) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set L) = P := by
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by
    rw [pow_two]; exact mul_self_of_isKleinFour' (isKleinFour_sylow_of_psl24 e P) hyP) hy1
  have h2 : IsPGroup 2 (Subgroup.centralizer ({y} : Set L)) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {r} hr hrd => ?_))
    by_contra hr2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({y} : Set L))
      r hrd
    have hxo : orderOf (x : L) = r := by rw [Subgroup.orderOf_coe, hx]
    have := eq_one_of_commute_of_psl24 e (hxo ▸ hr.odd_of_ne_two hr2) hy2
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    rw [this, orderOf_one] at hxo
    exact hr.one_lt.ne hxo
  have hab := (isKleinFour_sylow_of_psl24 e P).isMulCommutative
  have hPC : (P : Subgroup L) ≤ Subgroup.centralizer ({y} : Set L) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hyP⟩))
  exact P.is_maximal' h2 hPC

theorem exists_inv_of_orderOf_three_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2))
    {x : L} (hx : orderOf x = 3) : ∃ y : L, orderOf y = 2 ∧ y * x * y⁻¹ = x⁻¹ := by
  set K := GaloisField 2 2
  have hK : Nat.card K = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨U₀, w, -, hU₀, -, hwU, hww, hwinv, -, -⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := K) hK
  rw [hK] at hU₀
  norm_num at hU₀
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card L).factorization 3 = 1 := by
    rw [card_of_psl24 e, show (60 : ℕ) = 3 * 20 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  set U := U₀.map e.symm.toMonoidHom
  have hUcard : Nat.card U = 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hU₀]
  let P₁ : Sylow 3 L := Sylow.ofCard (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx, hfac]; rfl)
  let P₂ : Sylow 3 L := Sylow.ofCard U (by rw [hUcard, hfac]; rfl)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P₁ P₂
  have hgx : g * x * g⁻¹ ∈ U := by
    have : g * x * g⁻¹ ∈ ((g • P₁ : Sylow 3 L) : Subgroup L) := by
      change g * x * g⁻¹ ∈ MulAut.conj g • (Subgroup.zpowers x)
      exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
    rwa [hg] at this
  obtain ⟨u, hu, hgxu⟩ := hgx
  set w' := e.symm w
  have hw'inv : w' * (g * x * g⁻¹) * w'⁻¹ = (g * x * g⁻¹)⁻¹ := by
    rw [← hgxu]
    simp only [MulEquiv.coe_toMonoidHom, w']
    rw [← map_inv, ← map_mul, ← map_mul, hwinv u hu, map_inv]
  have hw'2 : orderOf w' = 2 := by
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime (by rw [pow_two]; exact hww) (fun h1 => hwU (h1 ▸ U₀.one_mem))
  have hord : orderOf (g⁻¹ * w' * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) w'
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hw'2]
  refine ⟨g⁻¹ * w' * g, hord, ?_⟩
  have := congrArg (fun z => g⁻¹ * z * g) hw'inv
  rw [show g⁻¹ * w' * g * x * (g⁻¹ * w' * g)⁻¹ = g⁻¹ * (w' * (g * x * g⁻¹) * w'⁻¹) * g by group,
    this]
  group

theorem MulAut.smul_sylow_smul {X : Type*} [Group X] {p : ℕ} (σ : MulAut X) (g : X)
    (P : Sylow p X) : σ • (g • P) = σ g • (σ • P) := by
  apply Sylow.ext
  rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
    Sylow.pointwise_smul_def, ← mul_smul, ← mul_smul]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem eq_one_of_mulAut_of_psl24 [Finite L] (e : L ≃* PSL(2, GaloisField 2 2)) (T : Sylow 2 L)
    {l : L} (hl : orderOf l = 3) (hlT : l ∈ Subgroup.normalizer ((T : Subgroup L) : Set L))
    (σ : MulAut L) (hσT : ∀ x ∈ T, σ x = x) (hσl : σ l = l) : σ = 1 := by
  classical
  have hsimple := isSimpleGroup_of_psl24 e
  have hcard := card_of_psl24 e
  have hT4 := card_sylow_of_psl24 e T
  have hTK := isKleinFour_sylow_of_psl24 e T
  set N := Subgroup.normalizer ((T : Subgroup L) : Set L)
  have hCT : Subgroup.centralizer ((T : Subgroup L) : Set L) = T := by
    apply le_antisymm
    · have : Nontrivial (T : Subgroup L) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hT4]; norm_num
      obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : (T : Subgroup L))
      have hy1' : y ≠ 1 := fun h0 => hy1 (Subtype.ext h0)
      calc Subgroup.centralizer ((T : Subgroup L) : Set L)
          ≤ Subgroup.centralizer ({y} : Set L) :=
            Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy)
        _ = T := centralizer_le_of_psl24 e T hy hy1'
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hTK.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hN12 : Nat.card N = 12 := by
    have h6 := relIndex_inf_centralizer_dvd_six hTK ⊤
    simp only [top_inf_eq, hCT] at h6
    have hodd : ¬ 2 ∣ (T : Subgroup L).relIndex N := fun h2 =>
      T.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
    have h1 := Subgroup.relIndex_mul_card (T : Subgroup L) N
    rw [inf_eq_left.mpr Subgroup.le_normalizer, hT4] at h1
    have h3 : 3 ∣ Nat.card N := hl ▸ Subgroup.orderOf_dvd_natCard N hlT
    have h4 : (T : Subgroup L).relIndex N ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases hk : (T : Subgroup L).relIndex N <;> omega
  have hNgen : N = (T : Subgroup L) ⊔ Subgroup.zpowers l := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (sup_le Subgroup.le_normalizer
      ((Subgroup.zpowers_le).mpr hlT))
    rw [hN12]
    have h4 : 4 ∣ Nat.card ((T : Subgroup L) ⊔ Subgroup.zpowers l : Subgroup L) :=
      hT4 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card ((T : Subgroup L) ⊔ Subgroup.zpowers l : Subgroup L) := by
      rw [← hl, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le le_sup_right
    exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3)
  have hσN : ∀ x ∈ N, σ x = x := by
    rw [hNgen]
    intro x hx
    have hle : (T : Subgroup L) ⊔ Subgroup.zpowers l ≤
        (σ.toMonoidHom).eqLocus (MonoidHom.id L) :=
      sup_le (fun y hy => hσT y hy) ((Subgroup.zpowers_le).mpr hσl)
    exact hle hx
  have hSyl5 : Nat.card (Sylow 2 L) = 5 := by
    rw [Sylow.card_eq_index_normalizer T]
    change N.index = 5
    have := N.card_mul_index
    rw [hN12, hcard] at this
    omega
  have hker : ∀ g : L, (∀ P : Sylow 2 L, g • P = P) → g = 1 := by
    intro g hg
    set φ := MulAction.toPermHom L (Sylow 2 L)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · have : g ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact Equiv.ext fun P => hg P
      rw [hb] at this
      exact this
    · exfalso
      have hTn : (T : Subgroup L).Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
        intro x _
        have : x ∈ φ.ker := ht ▸ Subgroup.mem_top x
        rw [MonoidHom.mem_ker] at this
        exact Sylow.smul_eq_iff_mem_normalizer.mp (congrArg (· T) (congrArg DFunLike.coe this))
      have := Sylow.unique_of_normal T hTn
      have := Nat.card_unique (α := Sylow 2 L)
      omega
  have hσTT : σ • T = T := by
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hx
      have h1 := hσT _ hx
      rw [MulAut.smul_def] at h1 hx
      have : x = σ (σ⁻¹ x) := by simp
      rw [this, h1]
      exact hx
    · intro hx
      rw [MulAut.smul_def]
      have h1 := hσT _ hx
      have : σ⁻¹ x = x := by
        conv_lhs => rw [← h1]
        simp
      rw [this]
      exact hx
  have hσP : ∀ P : Sylow 2 L, σ • P = P := by
    intro P
    by_cases hPT : P = T
    · rw [hPT]; exact hσTT
    set Y := N ⊓ Subgroup.normalizer ((P : Subgroup L) : Set L)
    have hYT : ∀ y ∈ Y, y ∈ (T : Subgroup L) → y = 1 := by
      intro y hyY hyT
      by_contra hy1
      have hyP : y ∈ (P : Subgroup L) := by
        have h2 : IsPGroup 2 (Subgroup.zpowers y) := (T.isPGroup'.to_le
          ((Subgroup.zpowers_le).mpr hyT))
        have := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' h2
          ((Subgroup.zpowers_le).mpr hyY.2)) le_sup_left
        rw [← this]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      apply hPT
      apply Sylow.ext
      rw [← centralizer_le_of_psl24 e P hyP hy1, centralizer_le_of_psl24 e T hyT hy1]
    have hYodd : ¬ 2 ∣ Nat.card Y := by
      intro h2
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 h2
      have hy2 : orderOf (y : L) = 2 := by rw [Subgroup.orderOf_coe, hy]
      have hyT : (y : L) ∈ (T : Subgroup L) := by
        have h2 : IsPGroup 2 (Subgroup.zpowers (y : L)) := IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, hy2, pow_one])
        have := T.is_maximal' (IsPGroup.to_sup_of_normal_left' T.isPGroup' h2
          ((Subgroup.zpowers_le).mpr y.2.1)) le_sup_left
        rw [← this]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have := hYT _ y.2 hyT
      rw [this, orderOf_one] at hy2
      omega
    have hY3 : 3 ≤ Nat.card Y := by
      have hstab : MulAction.stabilizer N P = (Subgroup.normalizer
          ((P : Subgroup L) : Set L)).subgroupOf N := by
        ext n
        rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
        exact Sylow.smul_eq_iff_mem_normalizer
      have horb : (MulAction.orbit N P).ncard ≤ 4 := by
        have hsub : MulAction.orbit N P ⊆ {Q | Q ≠ T} := by
          rintro _ ⟨n, rfl⟩ hn
          apply hPT
          have hn' : (n : L) • P = T := hn
          calc P = (n : L)⁻¹ • ((n : L) • P) := (inv_smul_smul _ _).symm
            _ = (n : L)⁻¹ • T := by rw [hn']
            _ = T := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ n.2)
        have h5 : ({Q | Q ≠ T} : Set (Sylow 2 L)).ncard = 4 := by
          have : ({Q | Q ≠ T} : Set (Sylow 2 L)) = Set.univ \ {T} := by ext; simp
          rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hSyl5]
        exact h5 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
      have h1 := (MulAction.stabilizer N P).card_mul_index
      rw [MulAction.index_stabilizer, hN12] at h1
      rw [hstab, ← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm] at h1
      change Nat.card Y * _ = 12 at h1
      by_contra hlt
      push Not at hlt
      have : Nat.card Y * (MulAction.orbit N P).ncard ≤ 2 * 4 :=
        Nat.mul_le_mul (by omega) horb
      omega
    have hYcard : Nat.card Y = 3 := by
      have h12 : Nat.card Y ∣ 12 := hN12 ▸ Subgroup.card_dvd_of_le inf_le_left
      have hle : Nat.card Y ≤ 12 := Nat.le_of_dvd (by norm_num) h12
      interval_cases hk : Nat.card Y <;> omega
    have h3 : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one])
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hmod := h3.card_modEq_card_fixedPoints (Sylow 2 L)
    rw [hSyl5] at hmod
    have hfixT : T ∈ MulAction.fixedPoints Y (Sylow 2 L) := fun y =>
      Sylow.smul_eq_iff_mem_normalizer.mpr y.2.1
    have hfixP : P ∈ MulAction.fixedPoints Y (Sylow 2 L) := fun y =>
      Sylow.smul_eq_iff_mem_normalizer.mpr y.2.2
    have hfixσP : σ • P ∈ MulAction.fixedPoints Y (Sylow 2 L) := by
      intro y
      change (y : L) • (σ • P) = σ • P
      rw [← hσN _ y.2.1, ← MulAut.smul_sylow_smul, Sylow.smul_eq_iff_mem_normalizer.mpr y.2.2]
    by_contra hne
    have hσPT : σ • P ≠ T := by
      intro h0
      apply hPT
      rw [← hσTT] at h0
      exact smul_left_cancel σ h0
    have hthree : 3 ≤ Nat.card (MulAction.fixedPoints Y (Sylow 2 L)) := by
      rw [Nat.card_coe_set_eq]
      have hsub : ({T, P, σ • P} : Set (Sylow 2 L)) ⊆ MulAction.fixedPoints Y (Sylow 2 L) := by
        rintro Q (rfl | rfl | rfl)
        · exact hfixT
        · exact hfixP
        · exact hfixσP
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hPT, Ne.symm hσPT]),
        Set.ncard_insert_of_notMem (by simpa using Ne.symm hne), Set.ncard_singleton] at this
      exact this
    have hle : Nat.card (MulAction.fixedPoints Y (Sylow 2 L)) ≤ 5 := by
      rw [← hSyl5]
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    have hall : Nat.card (MulAction.fixedPoints Y (Sylow 2 L)) = 5 := by
      have : Nat.card (MulAction.fixedPoints Y (Sylow 2 L)) % 3 = 2 := hmod.symm
      omega
    have hY1 : ∀ y : Y, (y : L) = 1 := by
      intro y
      apply hker
      intro Q
      have hQ : Q ∈ MulAction.fixedPoints Y (Sylow 2 L) := by
        by_contra hQ
        have hsub : MulAction.fixedPoints Y (Sylow 2 L) ⊆ Set.univ \ {Q} := by
          intro Q' hQ'
          refine ⟨Set.mem_univ _, fun h0 => hQ ?_⟩
          rw [Set.mem_singleton_iff] at h0
          rwa [h0] at hQ'
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hSyl5,
          ← Nat.card_coe_set_eq, hall] at this
        omega
      exact hQ y
    have : Nat.card Y = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hY1 a).trans (hY1 b).symm)⟩, ⟨1⟩⟩
    omega
  ext g
  rw [MulAut.one_apply]
  have key : g⁻¹ * σ g = 1 := by
    apply hker
    intro P
    rw [mul_smul, ← congrArg (σ g • ·) (hσP P), ← MulAut.smul_sylow_smul, hσP, inv_smul_smul]
  calc σ g = g * (g⁻¹ * σ g) := by group
    _ = g := by rw [key, mul_one]

end PSL24

end CFSG.Walter.JT
