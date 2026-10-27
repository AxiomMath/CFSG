module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
import CFSG.RankThree.PartTwo.KFacts.K71Lift

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter (PSL2)

namespace Item424Proof

theorem mem_closure_pair_zpow {G : Type*} [Group G] {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁) {z : G}
    (hz : z ∈ Subgroup.closure ({y₁, y₂} : Set G)) : ∃ i j : ℤ, z = y₁ ^ i * y₂ ^ j := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    have hcom : y₂ ^ b * y₁ ^ c = y₁ ^ c * y₂ ^ b :=
      (Commute.zpow_zpow (hc : Commute y₁ y₂) c b).eq.symm
    calc y₁ ^ a * y₂ ^ b * (y₁ ^ c * y₂ ^ d) = y₁ ^ a * (y₂ ^ b * y₁ ^ c) * y₂ ^ d := by group
      _ = y₁ ^ a * (y₁ ^ c * y₂ ^ b) * y₂ ^ d := by rw [hcom]
      _ = y₁ ^ (a + c) * y₂ ^ (b + d) := by rw [zpow_add, zpow_add]; group
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    refine ⟨-a, -b, ?_⟩
    have hcom : y₂ ^ (-b) * y₁ ^ (-a) = y₁ ^ (-a) * y₂ ^ (-b) :=
      (Commute.zpow_zpow (hc : Commute y₁ y₂) (-a) (-b)).eq.symm
    calc (y₁ ^ a * y₂ ^ b)⁻¹ = y₂ ^ (-b) * y₁ ^ (-a) := by group
      _ = y₁ ^ (-a) * y₂ ^ (-b) := hcom

theorem nonempty_mulEquiv_perm_three {X : Type*} [Group X] [Finite X] (T : Subgroup (MulAut X))
    (Ω : Set X) (hΩ : Nat.card Ω = 3) (hinv : ∀ σ ∈ T, ∀ x ∈ Ω, σ x ∈ Ω)
    (hfaith : ∀ σ ∈ T, (∀ x ∈ Ω, σ x = x) → σ = 1) (h6 : 6 ∣ Nat.card T) :
    Nonempty (T ≃* Equiv.Perm (Fin 3)) := by
  classical
  let p : SubMulAction T X :=
    { carrier := Ω
      smul_mem' := fun σ x hx => hinv σ σ.2 x hx }
  let φ : T →* Equiv.Perm p := MulAction.toPermHom T p
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply Subtype.ext
    refine hfaith σ σ.2 fun x hx => ?_
    have := congrArg (fun π : Equiv.Perm p => ((π ⟨x, hx⟩ : p) : X)) hσ
    exact this
  have hp : Nat.card p = 3 := hΩ
  have hcardP : Nat.card (Equiv.Perm p) = 6 := by
    rw [Nat.card_perm, hp]
    rfl
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hle : Nat.card T ≤ 6 := hcardP ▸ Nat.card_le_card_of_injective φ hφ
  have hT6 : Nat.card T = 6 := le_antisymm hle (Nat.le_of_dvd hpos h6)
  have hbij : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (by rw [hT6, hcardP])
  exact ⟨(MulEquiv.ofBijective φ hbij).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hp))⟩

end Item424Proof

open Item424Proof

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

theorem center_eq_bot_of_isFieldCent424 {X : Type} [Group X] (hX : IsFieldCent424 X) :
    Subgroup.center X = ⊥ := by
  rcases hX with ⟨K', _, _, -, ⟨e⟩⟩ | ⟨n, hn, hL⟩
  · exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  · exact Sec11.FieldCentRigid82.center_eq_bot_of_isType424
      (Or.inr (Or.inr ⟨3 * n, by omega, hL⟩))

theorem eq_one_of_mem_zpowers_a_of_mem_L (h : Config424 G A L a c K)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {z : G}
    (hza : z ∈ Subgroup.zpowers a) (hzL : z ∈ L) : z = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hza
  refine eq_one_of_mem_of_commute hZ hzL (fun l _ => ?_) ?_
  · exact ((Commute.zpow_left (Commute.symm (h.a_comm l)) k : Commute (a ^ k) l)).eq
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [show a ^ (3 : ℕ) = 1 by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a, one_zpow]

theorem inf_L_eq_of_outer (h : Config424 G A L a c K) (hout : InducesOuterTheta c L)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {d : G}
    (hdK : A ⊓ K = Subgroup.zpowers d) (hd3 : orderOf d = 3) :
    A ⊓ L = Subgroup.zpowers d := by
  obtain ⟨hcN, hcout⟩ := hout
  have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hdL : d ∈ L := h.K_le_L hdAK.2
  set B := Subgroup.closure ({a, c} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.a_mem
    · exact h.c_mem
  have hBL : ∀ z ∈ B, z ∈ L → z = 1 := by
    intro z hz hzL
    obtain ⟨i, j, rfl⟩ := mem_closure_pair_zpow (h.a_comm c).symm hz
    set τ := thetaQuotMulAut L (compAction L ⟨c, hcN⟩) with hτ
    have hτ3 : τ ^ 3 = 1 := by
      have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using h.pow_three c h.c_mem)
      rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hj : 3 ∣ j := by
      by_contra hj
      apply hcout
      have hzN : a ^ i * c ^ j ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hzL
      have haN : a ∈ Subgroup.normalizer (L : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [show a * x * a⁻¹ = x by rw [← h.a_comm x]; group]
      have hτa : thetaQuotMulAut L (compAction L ⟨a, haN⟩) = 1 := by
        ext y
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [thetaQuotMulAut_mk, MulAut.one_apply]
          congr 1
          apply Subtype.ext
          show a * y * a⁻¹ = y
          rw [← h.a_comm y]
          group
      have hz' : (⟨a ^ i * c ^ j, hzN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨a, haN⟩ ^ i * ⟨c, hcN⟩ ^ j := Subtype.ext (by simp)
      have hτz : thetaQuotMulAut L (compAction L ⟨a ^ i * c ^ j, hzN⟩) = τ ^ j := by
        rw [hz', map_mul, map_mul, map_zpow, map_zpow, hτa, one_zpow, one_mul, map_zpow,
          map_zpow]
      have hinn : KFacts.IsInnerAut (τ ^ j) := by
        rw [← hτz]
        exact ⟨_, (KFacts.thetaQuotMulAut_compAction_of_mem hzL hzN).symm⟩
      have hjj : (j * j) % 3 = 1 := by
        have : j % 3 = 1 ∨ j % 3 = 2 := by omega
        rcases this with h1 | h1 <;> simp [Int.mul_emod, h1]
      have hτ3' : τ ^ (3 : ℤ) = 1 := by exact_mod_cast hτ3
      have hτe : τ = (τ ^ j) ^ j := by
        rw [← zpow_mul, zpow_eq_zpow_emod (j * j) hτ3', hjj, zpow_one]
      rw [hτe]
      exact Subgroup.zpow_mem _ hinn j
    obtain ⟨j', rfl⟩ := hj
    have hc3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast h.pow_three c h.c_mem
    rw [zpow_mul, hc3, one_zpow, mul_one] at hzL ⊢
    exact h.eq_one_of_mem_zpowers_a_of_mem_L hZ (Subgroup.zpow_mem_zpowers a i) hzL
  let f : B × ↥(A ⊓ L) → A := fun p => ⟨(p.1 : G) * (p.2 : G), A.mul_mem (hBA p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ hbk
    have e : (b : G) * k = b' * k' := congrArg Subtype.val hbk
    have h1 : (b' : G)⁻¹ * b = k' * (k : G)⁻¹ := by
      calc (b' : G)⁻¹ * b = (b' : G)⁻¹ * (b * k) * (k : G)⁻¹ := by group
        _ = (b' : G)⁻¹ * (b' * k') * (k : G)⁻¹ := by rw [e]
        _ = k' * (k : G)⁻¹ := by group
    have h2 : (b' : G)⁻¹ * b = 1 := hBL _ (B.mul_mem (B.inv_mem b'.2) b.2)
      (h1 ▸ L.mul_mem k'.2.2 (L.inv_mem k.2.2))
    have hbb : (b : G) = b' := by
      calc (b : G) = b' * ((b' : G)⁻¹ * b) := by group
        _ = b' := by rw [h2, mul_one]
    have hkk : (k : G) = k' := by
      have := e
      rw [hbb] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hbb) (Subtype.ext hkk)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, h.card_closure_pair, h.card_eq] at hcard
  have hle : Nat.card (A ⊓ L : Subgroup G) ≤ Nat.card (Subgroup.zpowers d) := by
    rw [Nat.card_zpowers, hd3]
    omega
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩))
    hle).symm

theorem conj_mem_coset (h : Config424 G A L a c K) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    {d : G} (hdK : A ⊓ K = Subgroup.zpowers d) (hAL : A ⊓ L = Subgroup.zpowers d) {l : G}
    (hlL : l ∈ L) (hlN : l ∈ Subgroup.normalizer (A : Set G)) (k : ℤ) :
    ∃ m : ℤ, l * (c * d ^ k) * l⁻¹ = c * d ^ m := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN h.c_mem
  have h1 : c⁻¹ * (l * c * l⁻¹) ∈ A ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem h.c_mem)
      ((Subgroup.mem_normalizer_iff.mp hlN c).mp h.c_mem), ?_⟩
    have hcl : c⁻¹ * l * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) l).mp hlL
      simpa using this
    have e : c⁻¹ * (l * c * l⁻¹) = (c⁻¹ * l * c) * l⁻¹ := by group
    rw [e]
    exact L.mul_mem hcl (L.inv_mem hlL)
  rw [hAL] at h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
  have h2 : l * d * l⁻¹ ∈ Subgroup.zpowers d := by
    have hlK := h.normalizer_le hlN
    rw [hdK] at hlK
    exact (Subgroup.mem_normalizer_iff.mp hlK d).mp (Subgroup.mem_zpowers d)
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp h2
  refine ⟨j + e * k, ?_⟩
  have hcj : l * c * l⁻¹ = c * d ^ j := by
    rw [hj]
    group
  calc l * (c * d ^ k) * l⁻¹ = (l * c * l⁻¹) * (l * d * l⁻¹) ^ k := by
        rw [conj_zpow]
        group
    _ = c * d ^ j * (d ^ e) ^ k := by rw [hcj, he]
    _ = c * d ^ (j + e * k) := by rw [← zpow_mul, mul_assoc, ← zpow_add]

theorem exists_moving_and_inverting (h45 : Item4_5) (h : Config424 G A L a c K)
    (hout : InducesOuterTheta c L) (hFC : IsFieldCent424 (L ⧸ aschbacherSolvableCore 3 L))
    {d : G} (hdK : A ⊓ K = Subgroup.zpowers d) (hd3 : orderOf d = 3)
    (hA : A = Subgroup.closure {a, c, d}) :
    (∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
      ∃ x ∈ A, l * x * l⁻¹ ≠ x) ∧
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 := h.pow_three c h.c_mem
  have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hdL : d ∈ L := h.K_le_L hdAK.2
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hAN := h.le_normalizer h45
  have hLc : ∀ x ∈ L, a * x * a⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype := by
    intro x _
    rw [show a * x * a⁻¹ * x⁻¹ = 1 by rw [← h.a_comm x]; group]
    exact Subgroup.one_mem _
  rcases hFC with ⟨K', _, _, h3K, ⟨e⟩⟩ | ⟨n, hn, hL3⟩
  · have ha := KFacts.inducesKind_field_of_pow_three L hc3 hout e
    exact ⟨KFacts.exists_threeElement_moving_of_inducesKindPSL2 h3K h.isElemAbelian h.a_mem
      h.c_mem hdA hA hLc hdL hd1 e ha,
      KFacts.exists_inverting_of_inducesKindPSL2 h3K h.isElemAbelian h.a_mem h.c_mem hdA hA hLc
        hdL hd1 e ha⟩
  · obtain ⟨hcN, hτout⟩ := hout
    set τ := thetaQuotMulAut L (compAction L ⟨c, hcN⟩) with hτ
    have hτ3 : τ ^ 3 = 1 := by
      have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hc3)
      rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hΩ : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A := fun x hx3 hx =>
      mem_of_maximal_of_commute h.maximal hx3 hx
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    have hcyc := KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hn hL3
    have hab : ∀ Q : Sylow 3 L, ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L),
        x * y = y * x := by
      intro Q x hx y hy
      have hinj : ∀ z ∈ (Q : Subgroup L), π z = 1 → z = 1 := by
        intro z hz hz1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
        obtain ⟨k, hk⟩ := Q.isPGroup' ⟨z, hz⟩
        have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have h1 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
        have h2 : orderOf z ∣ Nat.card (aschbacherSolvableCore 3 L) :=
          Subgroup.orderOf_dvd_natCard _ hz1
        have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      obtain ⟨S, hS⟩ := (Q.isPGroup'.map π).exists_le_sylow
      have := hcyc S
      have hc : π x * π y = π y * π x := by
        have h1 := (IsCyclic.commGroup (α := S)).mul_comm ⟨π x, hS ⟨x, hx, rfl⟩⟩
          ⟨π y, hS ⟨y, hy, rfl⟩⟩
        exact congrArg Subtype.val h1
      have h2 : π (x * y * (y * x)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
      have h3 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hx hy)
        ((Q : Subgroup L).inv_mem ((Q : Subgroup L).mul_mem hy hx))) h2
      exact mul_inv_eq_one.mp h3
    have hQ : ∀ Q : Sylow 3 L, ¬ ∀ y ∈ (Q : Subgroup L), c * (y : G) = y * c := by
      intro Q hQc
      obtain ⟨y, hy, hy'⟩ := Sec11.lThreeMinusPiNoFixedSylow _ n hn hL3 τ hτ3 hτout
        (Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)))
      apply hy'
      rw [Sylow.coe_mapSurjective] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [QuotientGroup.mk'_apply, hτ, thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show c * z * c⁻¹ = z
      rw [hQc z hz, mul_inv_cancel_right]
    refine ⟨KFacts.exists_moving_of_not_centralizes_sylow h.comm h.pow_three hΩ hAN h.c_mem hab
      hQ, ?_⟩
    set db : L ⧸ aschbacherSolvableCore 3 L :=
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hdb
    have hτd : τ db = db := by
      rw [hdb, hτ, thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show c * d * c⁻¹ = d
      rw [h.comm c h.c_mem d hdA, mul_inv_cancel_right]
    have hdb3 : db ^ 3 = 1 := by
      rw [hdb, ← QuotientGroup.mk_pow]
      have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using h.pow_three d hdA)
      rw [this, QuotientGroup.mk_one]
    have hdb1 : db ≠ 1 := by
      intro h1
      rw [hdb, QuotientGroup.eq_one_iff] at h1
      have h2 := Subgroup.orderOf_dvd_natCard _ h1
      rw [Subgroup.orderOf_mk, hd3] at h2
      exact hθ3 h2
    obtain ⟨yb, hybτ, hybd⟩ := Sec11.lThreeMinusPiInverting _ n hn hL3 τ hτ3 hτout db hdb3 hdb1 hτd
    exact KFacts.exists_inverting_of_bar h.isElemAbelian h.a_mem h.c_mem hdA hA hLc hdL hcN yb
      hybτ hybd


theorem autIn_field (h45 : Item4_5) (hF : K424FieldCent) (h : Config424 G A L a c K)
    (hf : KFacts.InducesStdKind L c .field) : Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) := by
  have hc3 := h.pow_three c h.c_mem
  have hout : InducesOuterTheta c L := hf.inducesOuterTheta L (by intro h; cases h)
  have hFC := hF G L K c hf hc3 h.mem_thetaComponentsIn h.isType424
  have hZ := center_eq_bot_of_isFieldCent424 hFC
  obtain ⟨d, hdK, hd3, -, hA⟩ := h.exists_d h45
  have hAL := h.inf_L_eq_of_outer hout hZ hdK hd3
  have hAN := h.le_normalizer h45
  have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  obtain ⟨⟨l₁, hl₁, ⟨k₁, hk₁⟩, x₁, hx₁A, hx₁⟩, l₂, hl₂, hl₂d⟩ :=
    h.exists_moving_and_inverting h45 hout hFC hdK hd3 hA
  set Ω : Set A := {x | ∃ k : ℤ, (x : G) = c * d ^ k} with hΩdef
  have hcdA : ∀ k : ℤ, c * d ^ k ∈ A := fun k => A.mul_mem h.c_mem (A.zpow_mem hdA k)
  have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast h.pow_three d hdA
  have hΩ : Nat.card Ω = 3 := by
    let g : Fin 3 → Ω := fun i => ⟨⟨c * d ^ ((i : ℕ) : ℤ), hcdA _⟩, ⟨_, rfl⟩⟩
    have hg : Function.Bijective g := by
      refine ⟨fun i j hij => ?_, fun x => ?_⟩
      · have e : c * d ^ ((i : ℕ) : ℤ) = c * d ^ ((j : ℕ) : ℤ) :=
          congrArg (fun y : Ω => ((y : A) : G)) hij
        have e' : d ^ (i : ℕ) = d ^ (j : ℕ) := by exact_mod_cast mul_left_cancel e
        rw [pow_inj_mod, hd3] at e'
        exact Fin.ext (by rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at e')
      · obtain ⟨⟨y, hyA⟩, k, hk⟩ := x
        have hk' : y = c * d ^ k := hk
        refine ⟨⟨(k % 3).toNat, by omega⟩, Subtype.ext (Subtype.ext ?_)⟩
        show c * d ^ (((k % 3).toNat : ℕ) : ℤ) = y
        rw [hk', Int.toNat_of_nonneg (by omega), ← zpow_eq_zpow_emod k hd3']
    rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine nonempty_mulEquiv_perm_three (autIn L A) Ω hΩ ?_ ?_ ?_
  ·
    rintro σ hσ x ⟨k, hk⟩
    obtain ⟨l, hlN, hlL, rfl⟩ := mem_autIn_iff.mp hσ
    obtain ⟨m, hm⟩ := h.conj_mem_coset hAN hdK hAL hlL hlN k
    refine ⟨m, ?_⟩
    rw [normalizerMonoidHom_apply_coe, hk, hm]
  ·
    intro σ hσ hfix
    obtain ⟨l, hlN, hlL, rfl⟩ := mem_autIn_iff.mp hσ
    have hc : l * c * l⁻¹ = c := by
      have := hfix ⟨c, h.c_mem⟩ ⟨0, by simp⟩
      have := congrArg Subtype.val this
      rwa [normalizerMonoidHom_apply_coe] at this
    have hcd : l * (c * d) * l⁻¹ = c * d := by
      have := hfix ⟨c * d, A.mul_mem h.c_mem hdA⟩ ⟨1, by simp⟩
      have := congrArg Subtype.val this
      rwa [normalizerMonoidHom_apply_coe] at this
    have hd : l * d * l⁻¹ = d := by
      have e : l * (c * d) * l⁻¹ = (l * c * l⁻¹) * (l * d * l⁻¹) := by group
      rw [e, hc] at hcd
      exact mul_left_cancel hcd
    have hA' : A ≤ Subgroup.centralizer ({l} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hyl : l * y * l⁻¹ = y := by
        rcases hy with rfl | rfl | rfl
        · rw [h.a_comm l, mul_inv_cancel_right]
        · exact hc
        · exact hd
      calc y * l = (l * y * l⁻¹) * l := by rw [hyl]
        _ = l * y := by group
    ext y
    rw [normalizerMonoidHom_apply_coe, MulAut.one_apply]
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hA' y.2), mul_inv_cancel_right]
  ·
    obtain ⟨hl₁L, hl₁N⟩ := Subgroup.mem_inf.mp hl₁
    obtain ⟨hl₂L, hl₂N⟩ := Subgroup.mem_inf.mp hl₂
    set σ₁ : autIn L A := ⟨A.normalizerMonoidHom ⟨l₁, hl₁N⟩, mem_autIn_iff.mpr
      ⟨l₁, hl₁N, hl₁L, rfl⟩⟩ with hσ₁
    set σ₂ : autIn L A := ⟨A.normalizerMonoidHom ⟨l₂, hl₂N⟩, mem_autIn_iff.mpr
      ⟨l₂, hl₂N, hl₂L, rfl⟩⟩ with hσ₂
    have h3 : 3 ∣ orderOf σ₁ := by
      have hpow : σ₁ ^ 3 ^ k₁ = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        show (A.normalizerMonoidHom ⟨l₁, hl₁N⟩) ^ 3 ^ k₁ = 1
        rw [← map_pow]
        have : (⟨l₁, hl₁N⟩ : Subgroup.normalizer (A : Set G)) ^ 3 ^ k₁ = 1 :=
          Subtype.ext (by simpa using hk₁)
        rw [this, map_one]
      obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow)
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exfalso
        rw [pow_zero, orderOf_eq_one_iff] at hio
        apply hx₁
        have := congrArg (fun τ : autIn L A => (((τ : MulAut A) ⟨x₁, hx₁A⟩ : A) : G)) hio
        simpa [hσ₁, normalizerMonoidHom_apply_coe] using this
      · rw [hio]
        exact dvd_pow_self 3 hi0.ne'
    have h2 : 2 ∣ orderOf σ₂ := by
      have hpowd : ∀ k : ℕ, (((σ₂ ^ k : autIn L A) : MulAut A) ⟨d, hdA⟩ : G) =
          d ^ ((-1 : ℤ) ^ k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply]
          have e1 : ((σ₂ : MulAut A) ⟨d, hdA⟩ : A) = ⟨d⁻¹, A.inv_mem hdA⟩ := by
            apply Subtype.ext
            rw [hσ₂, normalizerMonoidHom_apply_coe]
            exact hl₂d
          rw [e1]
          have e2 : (⟨d⁻¹, A.inv_mem hdA⟩ : A) = (⟨d, hdA⟩ : A)⁻¹ := rfl
          rw [e2, map_inv, Subgroup.coe_inv, ih, pow_succ, mul_neg_one, zpow_neg]
      by_contra hodd
      have hodd' : Odd (orderOf σ₂) := Nat.odd_iff.mpr (by omega)
      have h1 := hpowd (orderOf σ₂)
      rw [pow_orderOf_eq_one, hodd'.neg_one_pow, zpow_neg, zpow_one] at h1
      simp only [OneMemClass.coe_one, MulAut.one_apply] at h1
      have hd2 : d ^ 2 = 1 := by
        calc d ^ 2 = d * d := pow_two d
          _ = d * d⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel d
      have : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one hd2
      rw [hd3] at this
      exact absurd this (by norm_num)
    have h6 : 2 * 3 ∣ Nat.card (autIn L A) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (h2.trans (orderOf_dvd_natCard σ₂))
        (h3.trans (orderOf_dvd_natCard σ₁))
    simpa using h6

end Config424

end CFSG.RankThree.PartTwo.Sec4
