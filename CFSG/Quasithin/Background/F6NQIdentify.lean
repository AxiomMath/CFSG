module

public import CFSG.Quasithin.Background.F6NQSetting
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimePrimeCentralizer
public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F6

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    {g : G} (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hS : S.map (MulAut.conj g).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hS

namespace F617Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem exists_sylow_eq (hS : F617Setting G₁ G₂ K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = (pCoreOf 2 G₂ ⊓ K).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := hS.isSylowTwoOf_inf
  exact ⟨(hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow hsyl.2.2, rfl⟩

theorem four_le_card_inf (hS : F617Setting G₁ G₂ K) : 4 ≤ Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
  have hq : CFSG.IsQuasisimple ↥K := hS.component.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_mulEquiv _ hS.odd_card_center P
  have h4 := (not_isCyclic_sylow_two hq.2.2 Q).2
  have hPQ : Nat.card ↥(P : Subgroup ↥K) = Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← hPQ, Nat.card_congr eQ.toEquiv]
  exact Nat.le_of_dvd Nat.card_pos h4

theorem exists_generator (hS : F617Setting G₁ G₂ K) :
    ∃ x ∈ twoResidual G₁, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (K : Set D) ∧
      ∀ q ∈ pCoreOf 2 G₂, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  have h := hS.triple
  set L₁ := twoResidual G₁ with hL₁
  obtain ⟨x, hxL, hx1⟩ : ∃ x ∈ L₁, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have : L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    have h3 := hS.card_left
    rw [← hL₁, this, Subgroup.card_bot] at h3
    omega
  have hord : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hS.card_left ▸ Subgroup.orderOf_dvd_natCard L₁ hxL
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  refine ⟨x, hxL, hord, fun hxC => ?_, fun q hq => ?_⟩
  ·
    apply hS.not_le_inf_centralizer
    intro y hy
    refine ⟨hS.le_left hy, ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxC
    · exact Subgroup.inv_mem _ hxC
  · have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
    have hqN := le_normalizer_twoResidual G₁ (Subgroup.mem_inf.mp hqT).1
    have hmem := (Subgroup.mem_normalizer_iff.mp hqN x).mp hxL
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1

theorem exists_ne_one_commute {P : Subgroup D} (hP : IsElemAbelian 2 P) (h4 : 4 ≤ Nat.card ↥P)
    {x : D} (hx : ∀ q ∈ P, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹) :
    ∃ e ∈ P, e ≠ 1 ∧ e * x = x * e := by
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm : ∀ q : D, q * x * q⁻¹ = x → q * x = x * q := fun q hq => by
    calc q * x = q * x * q⁻¹ * q := by group
      _ = x * q := by rw [hq]
  obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra hne
    push Not at hne
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    rw [this, Subgroup.card_bot] at h4
    omega
  obtain ⟨b, hbP, hbz⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers a := by
    by_contra hne
    push Not at hne
    have hle : P ≤ Subgroup.zpowers a := hne
    have h2 : Nat.card ↥(Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hP.2 a haP)
    have := Subgroup.card_le_of_le hle
    omega
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
  have hba : b ≠ a := fun h => hbz (h ▸ Subgroup.mem_zpowers a)
  rcases hx a haP with ha | ha
  · exact ⟨a, haP, ha1, hcomm a ha⟩
  rcases hx b hbP with hb | hb
  · exact ⟨b, hbP, hb1, hcomm b hb⟩
  refine ⟨a * b, P.mul_mem haP hbP, fun h => hba ?_, hcomm _ ?_⟩
  · have hb2 : b * b = 1 := by rw [← pow_two]; exact hP.2 b hbP
    calc b = a * b * b := by rw [h, one_mul]
      _ = a := by rw [mul_assoc, hb2, mul_one]
  · calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = (a * x * a⁻¹)⁻¹ := by rw [hb]; group
      _ = x := by rw [ha, inv_inv]

theorem exists_psl2
    (hW : WalterModelsStatement) (hS : F617Setting G₁ G₂ K) :
    ∃ (p : ℕ) (F : Type) (_ : Field F) (_ : Finite F), p.Prime ∧ 5 ≤ p ∧
      (p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card F = p ∧ IsL2 p 1 ↥K ∧
      Nonempty (↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn := hS.normal
  have hq : CFSG.IsQuasisimple ↥K := hS.component.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have hnonab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hq.2.2
  have : Group.IsPerfect ↥K := hq.1
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq
  obtain ⟨hEA, hQ8⟩ := hS.elemAbelian
  have hPmem : ∀ y : ↥K, y ∈ (P : Subgroup ↥K) ↔ (y : D) ∈ pCoreOf 2 G₂ := by
    intro y
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hinj : Function.Injective (π.comp (P : Subgroup ↥K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := P.isPGroup' y
    have h1 : orderOf (y : ↥K) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (y : ↥K) ∣ Nat.card ↥(Subgroup.center ↥K) :=
      Subgroup.orderOf_dvd_natCard _ hy
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Subgroup.center ↥K)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hS.odd_card_center)
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  set Q : Sylow 2 (↥K ⧸ Subgroup.center ↥K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hQdef
  have hQ : (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) = (P : Subgroup ↥K).map π := by
    rw [hQdef, Sylow.coe_mapSurjective]
  let ψ : ↥(P : Subgroup ↥K) ≃* ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
      rw [hQ, MonoidHom.range_comp, Subgroup.range_subtype]))
  have hcardPQ : Nat.card ↥(P : Subgroup ↥K) =
      Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    Nat.card_congr ψ.toEquiv
  have hPQ2 : Nat.card ↥(P : Subgroup ↥K) = Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hQle8 : Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤ 8 := by
    rw [← hcardPQ, hPQ2]
    exact (Subgroup.card_le_of_le inf_le_left).trans hQ8
  have h4 := (not_isCyclic_sylow_two hnonab Q).2
  have hQ4 : 4 ≤ Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    Nat.le_of_dvd Nat.card_pos h4
  have hQmem : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)), ∃ y : ↥K,
      (y : D) ∈ pCoreOf 2 G₂ ∧ π y = z := by
    intro z hz
    rw [hQ] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, (hPmem y).mp hy, rfl⟩
  have hQsq : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)), z * z = 1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hQmem z hz
    rw [← map_mul, ← pow_two]
    have : y ^ 2 = 1 := Subtype.ext (by simpa using hEA.2 _ hy)
    rw [this, map_one]
  have hQab : IsMulCommutative (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨y, hy, hya⟩ := hQmem a a.2
    obtain ⟨y', hy', hyb⟩ := hQmem b b.2
    change (a : ↥K ⧸ Subgroup.center ↥K) * b = b * a
    rw [← hya, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have hc := hEA.1.is_comm.comm (⟨(y : D), hy⟩ : ↥(pCoreOf 2 G₂)) ⟨(y' : D), hy'⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥(pCoreOf 2 G₂) → D) hc)
  obtain ⟨x, hxL, hxo, hxC, hxn⟩ := hS.exists_generator
  set xK : ↥K := ⟨x, hS.le_left hxL⟩ with hxK
  have hxbar : orderOf (π xK) = 3 := by
    refine orderOf_eq_prime ?_ fun h1 => hxC ?_
    · rw [← map_pow]
      have : xK ^ 3 = 1 := Subtype.ext (by simpa [hxK] using hxo ▸ pow_orderOf_eq_one x)
      rw [this, map_one]
    · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (h1 ⟨k, hk⟩)
  have hQn : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)),
      z * π xK * z⁻¹ = π xK ∨ z * π xK * z⁻¹ = (π xK)⁻¹ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hQmem z hz
    rcases hxn _ hy with h1 | h1
    · left
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    · right
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext h1
  rcases hW (↥K ⧸ Subgroup.center ↥K) hnonab Q hQab with ⟨f, hf, hm⟩ |
      ⟨p, f, hp, hp2, hf, hq5, h8, hm⟩ | ⟨f, -, hf3, hm⟩ | hJ
  ·
    exfalso
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    obtain ⟨e, heQ, he1, hex⟩ := exists_ne_one_commute (x := π xK)
      (P := (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)))
      ⟨hQab, fun z hz => by rw [pow_two]; exact hQsq z hz⟩ hQ4 hQn
    let ε : ↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      eF.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    have heo : orderOf (ε e) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hQsq e heQ) he1
    have hxo' : orderOf (ε (π xK)) = 3 := by rw [MulEquiv.orderOf_eq, hxbar]
    have hc : Commute (ε e) (ε (π xK)) := by
      change ε e * ε (π xK) = ε (π xK) * ε e
      rw [← map_mul, ← map_mul, hex]
    exact CFSG.GorensteinWalter.psl2_no_commuting_distinct_prime_order (r := 2) (p := 3) hF
      (by norm_num) heo hxo' hc
  ·
    obtain ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    have : Fact p.Prime := ⟨hp⟩
    have hf2 := le_two_of_isStronglyQuasithin hS.sqt hp hp2 hF eF
    have hf1 : f = 1 := by
      interval_cases f
      · rfl
      · have := odd_sq_mod_eight (hp.odd_of_ne_two hp2)
        omega
    subst hf1
    rw [pow_one] at hq5 h8
    have hZ : Subgroup.center ↥K = ⊥ := (center_of_quotient_psl_two hS.isPGroup_center hp2 hF
      eF).1 (by rw [pow_one]; rintro rfl; norm_num at hp)
    let eK : ↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eF
    exact ⟨p, F, inferInstance, inferInstance, hp, hq5, h8, by rw [hF, pow_one],
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨eK⟩⟩, ⟨eK⟩⟩
  ·
    exfalso
    have hree : CFSG.Blueprint.ReeTitsModel (↥K ⧸ Subgroup.center ↥K) .twistedG2 3 f := by
      rcases hm with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
    obtain ⟨-, -, h2f⟩ := CFSG.SectionRank.smallReeModel_rank hree
    have h3 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hS.sqt) 3 Nat.prime_three
      (by norm_num)
    omega
  ·
    exfalso
    obtain ⟨eJ⟩ := hJ
    let ε : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Open.walterJ1 :=
      eJ.trans CFSG.Walter.walterJ1EquivNative.symm
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv ε Q
    have hQ'8 := (CFSG.Walter.J1Props.jankoHyp.sylow_structure Q').1
    have hQcard : Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) = 8 := by
      rw [Nat.card_congr ι.toEquiv, hQ'8]
    set y := ε (π xK) with hy
    have hyo : orderOf y = 3 := by rw [hy, MulEquiv.orderOf_eq, hxbar]
    have hY3 : Nat.card ↥(Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
    have hJcard := CFSG.Walter.J1Props.J1_card
    let P₃ : Sylow 3 CFSG.Open.walterJ1 := Sylow.ofCard (Subgroup.zpowers y) (by
      rw [hY3, hJcard]
      have : (2 ^ 3 * 3 * 5 * 7 * 11 * 19 : ℕ) = 3 ^ 1 * 58520 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num)
    have hN := CFSG.Walter.J1Props.J2_normalizer_two_part (p := 3) (Or.inl rfl) P₃
    have hle : (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)).map ε.toMonoidHom ≤
        Subgroup.normalizer ((P₃ : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1) := by
      rintro _ ⟨z, hz, rfl⟩
      refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
      change w ∈ Subgroup.zpowers y at hw
      change ε z * w * (ε z)⁻¹ ∈ Subgroup.zpowers y
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow]
      refine Subgroup.zpow_mem _ ?_ k
      rcases hQn z hz with h1 | h1
      · rw [hy, ← map_inv, ← map_mul, ← map_mul, h1]
        exact Subgroup.mem_zpowers _
      · rw [hy, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have h8 : 2 ^ 3 ∣ Nat.card ↥(Subgroup.normalizer
        ((P₃ : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1)) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective ε.injective, hQcard] at h1
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h8
    omega

end F617Setting

end F6

end CFSG.Quasithin
