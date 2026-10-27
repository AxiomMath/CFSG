module

public import CFSG.RankThree.PartTwo.Sec11.Skeleton
public import CFSG.RankThree.PartTwo.Sec11.DataExistsAct
public import CFSG.RankThree.PartTwo.Sec11.RFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

namespace ChooseG

theorem false_of_surjective_of_isPerfect {T : Type*} [Group T] [Group.IsPerfect T]
    (f : T →* Multiplicative (ZMod 3)) (hf : Function.Surjective f) : False := by
  have : Group.IsPerfect (Multiplicative (ZMod 3)) := Group.IsPerfect.ofSurjective (f := f) hf
  have : Subsingleton (Multiplicative (ZMod 3)) := inferInstance
  exact absurd (Subsingleton.elim (Multiplicative.ofAdd (1 : ZMod 3)) 1) (by decide)

theorem exists_surjective_of_mulEquiv_prod {T M : Type*} [Group T] [Mul M]
    (e : T ≃* Multiplicative (ZMod 3) × M) :
    ∃ f : T →* Multiplicative (ZMod 3), Function.Surjective f :=
  ⟨MonoidHom.mk' (fun x => (e x).1) (fun x y => congrArg Prod.fst (map_mul e x y)),
    fun z => ⟨e.symm (z, (e 1).2), by simp⟩⟩

omit [Finite G] in
theorem mem_centralizer_of_le {D : Subgroup G} {y : G}
    (h : D ≤ Subgroup.centralizer ({y} : Set G)) : y ∈ Subgroup.centralizer (D : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ he => Subgroup.mem_centralizer_singleton_iff.mp (h he)

theorem exists_conj_mem_normalizer {R D W K : Subgroup G} {g : G} (hgW : g ∈ W)
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hRC : R ≤ W ⊓ Subgroup.centralizer (D : Set G)) (hR : IsSylowOf 3 R K)
    (hCK : W ⊓ Subgroup.centralizer (D : Set G) ≤ K) :
    ∃ k ∈ W ⊓ Subgroup.centralizer (D : Set G), k⁻¹ * g * k ∈
      Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := W ⊓ Subgroup.normalizer (D : Set G) with hN
  set C := W ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCN : C ≤ N := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact W.mul_mem (W.mul_mem hn.1 hz.1) (W.inv_mem hn.1)
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : n⁻¹ * e * n⁻¹⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem hn.2) e).mp he
      rw [inv_inv] at he'
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ he'
      calc e * (n * z * n⁻¹) = n * ((n⁻¹ * e * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
        _ = n * z * n⁻¹ * e := by group
  have hgN : g ∈ N := ⟨hgW, hgD⟩
  obtain ⟨k₀, hk₀⟩ := hg3
  have hP : IsPGroup 3 (Subgroup.zpowers g) := by
    rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨k₀, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk₀, one_zpow]
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := N)).exists_le_sylow
  set S := (Q : Subgroup N).map N.subtype with hS
  have hSsyl : IsSylowOf 3 S N := ⟨Q, rfl⟩
  have hgS : g ∈ S :=
    ⟨⟨g, hgN⟩, hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers g)), rfl⟩
  have hT : IsSylowOf 3 (S ⊓ C) C := hSsyl.inf_of_le_normalizer hCN hNC
  have hRC' : IsSylowOf 3 R C := hR.of_le hRC hCK
  obtain ⟨k, hkC, hk⟩ := hRC'.exists_mem_conj hT
  refine ⟨k, hkC, Subgroup.mem_normalizer_fintype fun r hr => ?_⟩
  have h1 : k * r * k⁻¹ ∈ S ⊓ C := (hk _).mpr (by simpa [mul_assoc] using hr)
  have h2 : g * (k * r * k⁻¹) * g⁻¹ ∈ S ⊓ C :=
    ⟨S.mul_mem (S.mul_mem hgS h1.1) (S.inv_mem hgS),
      (Subgroup.mem_normalizer_iff.mp (hNC hgN) _).mp h1.2⟩
  have h3 := (hk _).mp h2
  have e : k⁻¹ * g * k * r * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * (k * r * k⁻¹) * g⁻¹) * k := by group
  rw [e]
  exact h3

theorem sec11K_map_conj {L : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (L : Set G))
    (a : G) : sec11K L (MulAut.conj n a) = (sec11K L a).map (MulAut.conj n).toMonoidHom := by
  unfold sec11K
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
    (MulAut.conj n).injective]
  congr 1
  have hL : L.map (MulAut.conj n).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [Subgroup.map_inf _ _ _ (MulAut.conj n).injective, map_centralizer_singleton, hL]

omit [Finite G] in
theorem coe_normalizerMonoidHom_apply {A : Subgroup G} (w : Subgroup.normalizer (A : Set G))
    (z : A) : ((A.normalizerMonoidHom w z : A) : G) = (w : G) * z * (w : G)⁻¹ :=
  rfl

end ChooseG

open ChooseG

section Std


variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}

theorem Sec11Std.not_mem_of_sec11YA (h : Sec11Std G A c L a R Y) {d : G}
    (hA : A = Subgroup.closure {c, a, d}) (hdY : d ∈ Y)
    (he : ∃ f : sec11YA a Y A →* Multiplicative (ZMod 3), Function.Surjective f) :
    ¬ (a ∈ Y ∧ c ∈ Y) := by
  rintro ⟨haY, hcY⟩
  obtain ⟨f, hf⟩ := he
  have hAY : A ≤ Y := by
    rw [hA, Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    exacts [hcY, haY, hdY]
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hYp : Group.IsPerfect Y :=
    Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hYp' : Group.IsPerfect (Y.subgroupOf (Subgroup.centralizer ({a} : Set G))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hP : Group.IsPerfect (sec11YA a Y A) := by
    unfold sec11YA
    rw [sup_eq_left.mpr hAY]
    exact Group.IsPerfect.map _
  exact false_of_surjective_of_isPerfect f hf

theorem Sec11Std.autIn_facts (h119 : Item119) (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) :
    (Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∧ ¬ (a ∈ Y ∧ c ∈ Y) := by
  obtain ⟨-, hacd, -⟩ := h.not_mem_facts hdL hA
  obtain ⟨-, -, -, -, hdK⟩ := basic_facts_of_conj h45 h hdL hA h.a_mem hacd
  have hdY : d ∈ Y := h.sec11K_le hdK
  rcases h119 _ A c L a R Y h d hdL hA with ⟨hf, hS⟩ | ⟨h2, hD⟩ | ⟨h3, hS⟩ | ⟨h4, -, hD⟩
  · refine ⟨Or.inl hS, ?_⟩
    rintro ⟨-, hcY⟩
    obtain ⟨hcN, hnot⟩ := hf.inducesOuterTheta Y (by intro h; cases h)
    exact hnot ⟨_, (thetaQuotMulAut_compAction_of_mem Y hcY).symm⟩
  · refine ⟨Or.inr hD, ?_⟩
    rcases h2 with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
    · exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
  · refine ⟨Or.inl hS, ?_⟩
    rcases h3 with ⟨p, e', _, -, ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩⟩ | ⟨π, p, f, K, _, -, -, ⟨e⟩⟩
    · exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
    · exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
    · exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
  · refine ⟨Or.inr hD, ?_⟩
    rcases h4 with h4 | h4
    · obtain ⟨e⟩ := h4
      exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)
    · obtain ⟨e⟩ := h4
      exact h.not_mem_of_sec11YA hA hdY (exists_surjective_of_mulEquiv_prod e)

theorem Sec11Std.exists_g_t (h119 : Item119) (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) :
    ∃ g t : G, g ∈ Y ∧ g ∈ Subgroup.normalizer (A : Set G) ∧ t ∈ Y ∧
      t ∈ Subgroup.normalizer (A : Set G) ∧ (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
      (∀ z ∈ A, g ^ 3 * z * (g ^ 3)⁻¹ = z) ∧ (∃ z ∈ A, g * z * g⁻¹ ≠ z) ∧
      ∀ z ∈ A, t * g * t⁻¹ * z * (t * g * t⁻¹)⁻¹ = g⁻¹ * z * g := by
  obtain ⟨hiso, -⟩ := h.autIn_facts h119 h45 hdL hA
  obtain ⟨σ, τ, hσ1, hσ3, hτσ⟩ := ActOnA.exists_pow_three_inv_conj hiso
  obtain ⟨y, hyN, hyY, hyσ⟩ := Sec4.mem_autIn_iff.mp σ.2
  obtain ⟨t, htN, htY, htτ⟩ := Sec4.mem_autIn_iff.mp τ.2
  set N := Subgroup.normalizer (A : Set G) with hN
  have hσ1' : (σ : MulAut A) ≠ 1 := fun h1 => hσ1 (Subtype.ext h1)
  have hσ3' : (σ : MulAut A) ^ 3 = 1 := by
    have := congrArg Subtype.val hσ3
    simpa using this
  have hτσ' : (τ : MulAut A) * σ * (τ : MulAut A)⁻¹ = (σ : MulAut A)⁻¹ := by
    have := congrArg Subtype.val hτσ
    simpa using this
  obtain ⟨e, m, hm3, hmo⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  have hσo : orderOf (σ : MulAut A) = 3 := orderOf_eq_prime hσ3' hσ1'
  have hσm : (σ : MulAut A) ^ m ≠ 1 := by
    intro h1
    apply hm3
    rw [← hσo]
    exact orderOf_dvd_of_pow_eq_one h1
  have hφg : A.normalizerMonoidHom ((⟨y, hyN⟩ : N) ^ m) = (σ : MulAut A) ^ m := by
    rw [map_pow, hyσ]
  refine ⟨y ^ m, t, Y.pow_mem hyY m, N.pow_mem hyN m, htY, htN, ⟨e, ?_⟩, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hmo, pow_orderOf_eq_one]
  · intro z hz
    have h1 : A.normalizerMonoidHom (((⟨y, hyN⟩ : N) ^ m) ^ 3) = 1 := by
      rw [map_pow, hφg, ← pow_mul, mul_comm, pow_mul, hσ3', one_pow]
    have h2 := congrArg (fun ψ : MulAut A => ((ψ ⟨z, hz⟩ : A) : G)) h1
    simpa [coe_normalizerMonoidHom_apply] using h2
  · by_contra hall
    have hall' : ∀ z ∈ A, y ^ m * z * (y ^ m)⁻¹ = z := fun z hz => by
      by_contra hne
      exact hall ⟨z, hz, hne⟩
    apply hσm
    rw [← hφg]
    ext z
    exact hall' z z.2
  · intro z hz
    have h1 : A.normalizerMonoidHom (⟨t, htN⟩ * (⟨y, hyN⟩ : N) ^ m * (⟨t, htN⟩ : N)⁻¹) =
        A.normalizerMonoidHom (((⟨y, hyN⟩ : N) ^ m)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv, hφg, htτ, ← conj_pow, hτσ', inv_pow]
    have h2 : t * y ^ m * t⁻¹ * z * (t * y ^ m * t⁻¹)⁻¹ = (y ^ m)⁻¹ * z * ((y ^ m)⁻¹)⁻¹ :=
      congrArg (fun ψ : MulAut A => ((ψ ⟨z, hz⟩ : A) : G)) h1
    rwa [inv_inv] at h2

theorem Sec11Std.exists_choice_g (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h119 : Item119) (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) :
    ∃ (a' : G) (Y' : Subgroup G) (g : G), Sec11Std G A c L a' R Y' ∧ a' ∈ A ∧
      a' ∉ Subgroup.closure ({c, d} : Set G) ∧ (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
      g ∈ Y' ⊓ Subgroup.normalizer (A : Set G) ∧ g ∈ Subgroup.normalizer (R : Set G) ∧
      g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      g * c * g⁻¹ ∈ Subgroup.closure {c, d} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAL.1
  obtain ⟨-, hacd, hd1⟩ := h.not_mem_facts hdL hA
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdA) hd1
  obtain ⟨-, -, -, -, hdK⟩ := basic_facts_of_conj h45 h hdL hA haA hacd
  have hdY : d ∈ Y := h.sec11K_le hdK
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe haA h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (h117 G A c L a R Y h d hdL (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdA)
      (by rw [Nat.card_zpowers, hd3])).mpr rfl
  have hcad : c ∉ Subgroup.closure ({a, d} : Set G) := by
    intro hc
    have hle : A ≤ Subgroup.closure ({a, d} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro z (rfl | rfl | rfl)
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm a haA d hdA) (hexp a haA) (hexp d hdA)
    rw [h.card_eq] at h1
    omega
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro z (rfl | rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hd
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a haA) (hexp c hcA) (hexp a haA)
    rw [h.card_eq] at h1
    omega
  obtain ⟨-, hacY⟩ := h.autIn_facts h119 h45 hdL hA
  obtain ⟨g₁, t, hg₁Y, hg₁A, htY, htA, ⟨k₁, hk₁⟩, hg₁cube, hg₁ne, hinv⟩ :=
    h.exists_g_t h119 h45 hdL hA
  have hg₁a : g₁ * a = a * g₁ := Subgroup.mem_centralizer_singleton_iff.mp (hYC hg₁Y)
  have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp (hYC htY)
  have hg₁d : g₁ * d = d * g₁ := Sec12.commute_of_conj_mem_zpowers hd3
    ((Subgroup.mem_normalizer_iff.mp (hWd hg₁A) d).mp (Subgroup.mem_zpowers d)) hk₁
  have hu := ActOnA.conj_mul_inv_mem_zpowers hcomm hexp hA hacd hcad hg₁A htA hg₁a hg₁d hta
    (hWd htA) hg₁cube hinv hg₁Y htY hAY hdY hacY
  have hne : g₁ * c * g₁⁻¹ ≠ c := by
    intro he
    obtain ⟨z, hz, hz'⟩ := hg₁ne
    apply hz'
    have hgc : g₁ * c = c * g₁ := mul_inv_eq_iff_eq_mul.mp he
    have hle : A ≤ Subgroup.centralizer ({g₁} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro w (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hg₁a.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hg₁d.symm
    have hzg := Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
    rw [← hzg, mul_inv_cancel_right]
  set D := Subgroup.closure ({c, d} : Set G) with hD
  have hcD : c ∈ D := Subgroup.subset_closure (by simp)
  have hdD : d ∈ D := Subgroup.subset_closure (by simp)
  have hgcD : g₁ * c * g₁⁻¹ ∈ D := by
    have e : g₁ * c * g₁⁻¹ = (g₁ * c * g₁⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact D.mul_mem (Subgroup.zpowers_le.mpr hdD hu) hcD
  have hgcH : g₁ * c * g₁⁻¹ ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.mp hu
    have huc : d ^ β ∈ Subgroup.zpowers c := by
      rw [hβ]
      exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    by_cases h3 : (3 : ℤ) ∣ β
    · apply hne
      have h1 : g₁ * c * g₁⁻¹ * c⁻¹ = 1 := by
        rw [← hβ, ActOnA.zpow_eq_one_of_dvd (hexp d hdA) h3]
      calc g₁ * c * g₁⁻¹ = (g₁ * c * g₁⁻¹ * c⁻¹) * c := by group
        _ = c := by rw [h1, one_mul]
    · exact hdc (ActOnA.mem_of_zpow_mem (hexp d hdA) huc h3)
  have hR3 : IsPGroup 3 R := h.isSylowOf.isPGroup
  have hRH := h.isSylowOf.le
  have hRW : R ≤ Subgroup.normalizer (A : Set G) := by
    have hA113 := (h113 G A c L a R Y h).1
    intro r hr
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, hA113] at hz ⊢
    have hle : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} ≤
        (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).comap (MulAut.conj r).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyR, hy3⟩
      refine Subgroup.subset_closure ⟨R.mul_mem (R.mul_mem hr hyR) (R.inv_mem hr), ?_⟩
      change (r * y * r⁻¹) ^ 3 = 1
      rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    exact hle hz
  have hRCD : R ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) := by
    intro y hy
    refine ⟨hRW hy, ChooseG.mem_centralizer_of_le ?_⟩
    obtain ⟨k, hk⟩ := hR3 ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Sec12.commute_of_conj_mem_zpowers hc3
        ((Subgroup.mem_normalizer_iff.mp (hRH hy) _).mp (Subgroup.mem_zpowers _)) hyk).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Sec12.commute_of_conj_mem_zpowers hd3
        ((Subgroup.mem_normalizer_iff.mp (hWd (hRW hy)) _).mp (Subgroup.mem_zpowers _)) hyk).symm
  have hRsyl : IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G)) := by
    have := h.isSylowOf_inf
    rwa [inf_of_le_left hRW] at this
  have hCK : Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, hz.1⟩
    have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp hz.2 c hcD).symm
    have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzc
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzC
    exact Subgroup.centralizer_le_normalizer _ hzC
  have hg₁D : g₁ ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hle : D ≤ D.comap (MulAut.conj g₁).toMonoidHom := by
      rw [hD, Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hgcD
      · change g₁ * w * g₁⁻¹ ∈ D
        rw [hg₁d, mul_inv_cancel_right]
        exact hdD
    exact hle hz
  obtain ⟨k, hkC, hkR⟩ :=
    ChooseG.exists_conj_mem_normalizer hg₁A hg₁D ⟨k₁, hk₁⟩ hRCD hRsyl hCK
  have hkW : k ∈ Subgroup.normalizer (A : Set G) := hkC.1
  have hkD : ∀ e ∈ D, k * e * k⁻¹ = e := fun e he => by
    have hek := Subgroup.mem_centralizer_iff.mp hkC.2 e he
    rw [← hek, mul_inv_cancel_right]
  have hkD' : ∀ e ∈ D, k⁻¹ * e * k = e := fun e he => by
    calc k⁻¹ * e * k = k⁻¹ * (k * e * k⁻¹) * k := by rw [hkD e he]
      _ = e := by group
  have hkL : k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    h.normalizer_le_normalizer_L h45 (inv_mem (hCK hkC).1)
  set φ := MulAut.conj k⁻¹ with hφ
  have hφapp : ∀ x, φ x = k⁻¹ * x * k := fun x => by rw [hφ, MulAut.conj_apply, inv_inv]
  have ha'A : φ a ∈ A := by
    rw [hφapp]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hkW) a).mp haA
    rwa [inv_inv] at this
  have ha'cd : φ a ∉ D := by
    intro hm
    apply hacd
    have e : a = k * φ a * k⁻¹ := by rw [hφapp]; group
    rw [e, hkD _ hm]
    exact hm
  have hY' : Y.map φ.toMonoidHom ∈ thetaComponentsAt 3 (φ a) :=
    map_mem_thetaComponentsAt φ h.mem_thetaComponentsAt_Y
  have hKY' : sec11K L (φ a) ≤ Y.map φ.toMonoidHom := by
    rw [ChooseG.sec11K_map_conj hkL]
    exact Subgroup.map_mono h.sec11K_le
  have hstd' := h.change_a h45 hdL hA ha'A ha'cd hY' hKY'
  have hgc' : φ g₁ * c * (φ g₁)⁻¹ = g₁ * c * g₁⁻¹ := by
    rw [hφapp]
    calc k⁻¹ * g₁ * k * c * (k⁻¹ * g₁ * k)⁻¹ = k⁻¹ * (g₁ * (k * c * k⁻¹) * g₁⁻¹) * k := by
          group
      _ = k⁻¹ * (g₁ * c * g₁⁻¹) * k := by rw [hkD c hcD]
      _ = g₁ * c * g₁⁻¹ := hkD' _ hgcD
  refine ⟨φ a, Y.map φ.toMonoidHom, φ g₁, hstd', ha'A, ha'cd,
    ⟨k₁, by rw [← map_pow, hk₁, map_one]⟩, ⟨⟨g₁, hg₁Y, rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [hφapp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hkW) hg₁A) hkW
  · rw [hφapp]
    exact hkR
  · intro hH
    apply hgcH
    have := (Subgroup.mem_normalizer_iff.mp hH c).mp (Subgroup.mem_zpowers c)
    rwa [hgc'] at this
  · rw [hgc']
    exact hgcD

end Std

end CFSG.RankThree.PartTwo.Sec11
