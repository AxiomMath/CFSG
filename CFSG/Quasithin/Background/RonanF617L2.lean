module

public import CFSG.Quasithin.Background.RonanF617Setting

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.GorensteinWalter
  CFSG.Quasithin CFSG.Quasithin.F6

structure L2 {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) (F : Type) [Field F]
    [Finite F] (p f : ℕ) : Prop extends Setting G₁ G₂ K where
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  five_le : 5 ≤ p ^ f
  mod_eight : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5
  card_field : Nat.card F = p ^ f

namespace Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem map_eq_one {A : Type*} [Group A] [Finite A] (hS : Setting G₁ G₂ K) (ψ : D →* A)
    (hcomm : ∀ a b : A, a * b = b * a) (hodd : Odd (Nat.card A)) (d : D) : ψ d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.triple
  have h2 : ∀ x : D, (∃ m : ℕ, x ^ 2 ^ m = 1) → ψ x = 1 := by
    rintro x ⟨m, hm⟩
    have hd1 : orderOf (ψ x) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm, map_one])
    have hd2 : orderOf (ψ x) ∣ Nat.card A := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ m) (Nat.card A) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hK : K ≤ ψ.ker := by
    have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp hS.component.1.1
    have hle : commutator ↥K ≤ (ψ.comp K.subtype).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
        hcomm ((ψ.comp K.subtype) g₁) ((ψ.comp K.subtype) g₂)]
      group
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (ψ.comp K.subtype).ker := hle (by rw [hperf]; trivial)
    exact this
  have hT : G₁ ⊓ G₂ ≤ ψ.ker := fun t ht => by
    obtain ⟨m, hm⟩ := h.isPGroup_inf ⟨t, ht⟩
    exact h2 t ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hL : twoResidual G₂ ≤ ψ.ker := by
    rw [twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun w hw => ?_
    have hw3 : w ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h.symm hw.1 hw.2)
    obtain ⟨t, -, hinv⟩ := F6.F617Setting.exists_inv_mod_pCoreOf h.symm hw.1 hw3
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G₂) ⟨_, hinv⟩
    have h1 := h2 _ ⟨m, by simpa using congrArg Subtype.val hm⟩
    rw [map_mul, map_mul, map_mul, map_inv, hcomm (ψ t) (ψ w), mul_assoc (ψ w),
      mul_inv_cancel, mul_one] at h1
    have h3 : ψ w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
    change ψ w = 1
    calc ψ w = ψ w ^ 3 * (ψ w * ψ w)⁻¹ := by group
      _ = 1 := by rw [h3, h1, inv_one, one_mul]
  have hG₂ : G₂ ≤ ψ.ker := by
    rw [← inf_sup_twoResidual_right h]
    exact sup_le hT hL
  have htop : (⊤ : Subgroup D) ≤ ψ.ker := by
    rw [← hS.sup_eq_top]
    exact sup_le hK hG₂
  exact htop (Subgroup.mem_top d)

end Setting

namespace L2

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D} {F : Type} [Field F]
  [Finite F] {p f : ℕ}

theorem isOddPrimePower (hT : L2 G₁ G₂ K F p f) : IsOddPrimePower (Nat.card F) :=
  ⟨p, f, hT.prime, hT.prime.odd_of_ne_two hT.ne_two, hT.one_le, hT.card_field⟩

theorem odd_card_field (hT : L2 G₁ G₂ K F p f) : Odd (Nat.card F) := by
  rw [hT.card_field]
  exact Odd.pow (hT.prime.odd_of_ne_two hT.ne_two)

theorem odd_exponent (hT : L2 G₁ G₂ K F p f) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, hk⟩ | hf
  · exfalso
    have h1 : p ^ f = (p ^ k) ^ 2 := by rw [← pow_mul, hk]; ring_nf
    have h2 := odd_sq_mod_eight (Odd.pow (n := k) (hT.prime.odd_of_ne_two hT.ne_two))
    have h3 := hT.mod_eight
    rw [h1] at h3
    omega
  · exact hf

theorem card_ringAut (hT : L2 G₁ G₂ K F p f) :
    Nat.card (F ≃+* F) = f ∧ ∀ a b : F ≃+* F, a * b = b * a := by
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hT.prime F
    hT.card_field
  refine ⟨h1, fun a b => ?_⟩
  obtain ⟨g, hg⟩ := h2.exists_generator
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  rw [← zpow_add, ← zpow_add, add_comm]

noncomputable def gamma (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) : D →* PGammaL2 F :=
  have : K.Normal := hT.normal
  have : Fact p.Prime := ⟨hT.prime⟩
  have h3 : 3 < Nat.card F := by rw [hT.card_field]; have := hT.five_le; omega
  (MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hT.isOddPrimePower h3)
    ⟨pGammaL2ToMulAutPSL2_injective F hT.isOddPrimePower h3,
      pGammaL2ToMulAutPSL2_surjective F hT.card_field hT.isOddPrimePower h3⟩).symm.toMonoidHom.comp
    ((MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal)

theorem ker_gamma (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    (hT.gamma eK).ker = Subgroup.centralizer (K : Set D) := by
  have : K.Normal := hT.normal
  ext d
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  unfold gamma
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  constructor
  · intro h1 k hk
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : D)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc k * d = d * k * d⁻¹ * d := by rw [h2]
      _ = d * k := by group
  · intro h1
    ext k
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h1 k k.2]
    group

theorem right_gamma (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) (d : D) :
    (hT.gamma eK d).right = 1 := by
  obtain ⟨hc, hcomm⟩ := hT.card_ringAut
  have hodd : Odd (Nat.card (F ≃+* F)) := by rw [hc]; exact hT.odd_exponent
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hc]; have := hT.one_le; omega)
  exact hT.toSetting.map_eq_one (SemidirectProduct.rightHom.comp (hT.gamma eK)) hcomm hodd d

noncomputable def rho (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) : D →* PGL2 F where
  toFun d := (hT.gamma eK d).left
  map_one' := by rw [map_one, SemidirectProduct.one_left]
  map_mul' a b := by
    rw [map_mul, SemidirectProduct.mul_left, hT.right_gamma eK a, map_one, MulAut.one_apply]

theorem ker_rho (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    (hT.rho eK).ker = Subgroup.centralizer (K : Set D) := by
  rw [← hT.ker_gamma eK]
  ext d
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h1
    exact SemidirectProduct.ext h1 (hT.right_gamma eK d)
  · intro h1
    change (hT.gamma eK d).left = 1
    rw [h1, SemidirectProduct.one_left]

omit [Finite D] in
theorem inf_centralizer_self_eq_bot (eK : ↥K ≃* PSL2 F) :
    K ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzc : eK ⟨z, hz.1⟩ ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 k k.2)
  rw [psl2_center_eq_bot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hzc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzc)

theorem rho_comp_injective (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    Function.Injective ((hT.rho eK).comp K.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_rho] at hk
  have h1 : (k : D) ∈ K ⊓ Subgroup.centralizer (K : Set D) := ⟨k.2, hk⟩
  rw [inf_centralizer_self_eq_bot eK, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)


theorem index_range_rho_comp (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    ((hT.rho eK).comp K.subtype).range.index = 2 := by
  have hodd := hT.isOddPrimePower
  have h1 := ((hT.rho eK).comp K.subtype).range.card_mul_index
  rw [← Nat.card_congr (MonoidHom.ofInjective (hT.rho_comp_injective eK)).toEquiv,
    Nat.card_congr eK.toEquiv, psl2_card_formula F hodd, pgl2_card_formula F] at h1
  have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    obtain ⟨m, hm⟩ : Odd (Nat.card F) := hT.odd_card_field
    rw [hm]
    exact Dvd.dvd.mul_left ⟨2 * m * m + 2 * m, by rw [Nat.sub_eq_of_eq_add]; ring⟩ _
  have hpos : 0 < Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    have : 2 ≤ Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
      have h5 : 5 ≤ Nat.card F := by rw [hT.card_field]; exact hT.five_le
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
      have : 1 ≤ Nat.card F ^ 2 - 1 := by
        have : 25 ≤ Nat.card F ^ 2 := by nlinarith
        omega
      nlinarith
    omega
  have h3 : Nat.card F * (Nat.card F ^ 2 - 1) / 2 * 2 = Nat.card F * (Nat.card F ^ 2 - 1) :=
    Nat.div_mul_cancel h2
  nlinarith

theorem mem_sup_of_odd (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) {d : D}
    (hd : Odd (orderOf d)) : d ∈ K ⊔ Subgroup.centralizer (K : Set D) := by
  have := hT.normal
  set R := ((hT.rho eK).comp K.subtype).range with hR
  have hsq : ∀ g : PGL2 F, g ^ 2 ∈ R := Subgroup.sq_mem_of_index_two (hT.index_range_rho_comp eK)
  obtain ⟨m, hm⟩ := hd
  have hdd : d = (d ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hR' : hT.rho eK d ∈ R := by
    rw [hdd, map_pow, map_pow]
    exact R.pow_mem (hsq _) _
  obtain ⟨k, hk⟩ := hR'
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype] at hk
  have hc : (k : D)⁻¹ * d ∈ Subgroup.centralizer (K : Set D) := by
    rw [← ker_rho hT eK, MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel]
  have : d = k * ((k : D)⁻¹ * d) := by group
  rw [this]
  exact Subgroup.mul_mem_sup k.2 hc

theorem sup_centralizer (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    K ⊔ Subgroup.centralizer (K : Set D) = twoResidual ⊤ := by
  refine le_antisymm (sup_le (le_twoResidual_of_isComponent hT.component)
    hT.centralizer_le_twoResidual) ?_
  rw [twoResidual_eq_oTwoUpper]
  exact (Subgroup.closure_le _).mpr fun d hd => hT.mem_sup_of_odd eK hd.2

theorem card_centralizer (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    Nat.card (Subgroup.centralizer (K : Set D)) = 3 := by
  have h := hT.triple
  have := hT.normal
  set C := Subgroup.centralizer (K : Set D) with hC
  have hL := hT.sup_centralizer eK
  have h1 : K.relIndex (twoResidual ⊤) = Nat.card C := by
    rw [← hL, sup_comm, Subgroup.relIndex_sup_right, Subgroup.relIndex,
      (Subgroup.subgroupOf_eq_bot).mpr (disjoint_iff.mpr ((inf_comm K C).symm.trans
        (inf_centralizer_self_eq_bot eK)) |>.symm), Subgroup.index_bot]
  have hL₂ : K ⊔ twoResidual G₂ = twoResidual ⊤ := by
    refine le_antisymm (sup_le (le_twoResidual_of_isComponent hT.component)
      (twoResidual_mono le_top)) ?_
    rw [twoResidual_top_eq h]
    exact sup_le (hT.le_left.trans le_sup_left) le_sup_right
  have h2 : K.relIndex (twoResidual ⊤) ∣ Nat.card ↥(twoResidual G₂) := by
    rw [← hL₂, sup_comm, Subgroup.relIndex_sup_right]
    exact Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(twoResidual G₂) ∣ Nat.card ↥G₂ :=
    Subgroup.card_dvd_of_le (twoResidual_le G₂)
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have h4 : Nat.card C ∣ 3 * 2 ^ a := by
    rw [← h1, ← ha, ← card_right h]
    exact h2.trans h3
  have hcop : Nat.Coprime (Nat.card C) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hT.odd_card_centralizer)
  have h5 : Nat.card C ∣ 3 := hcop.dvd_of_dvd_mul_right h4
  rcases (Nat.dvd_prime Nat.prime_three).mp h5 with h6 | h6
  · exfalso
    apply hT.not_le_right
    have hCb : Subgroup.centralizer (K : Set D) = ⊥ := Subgroup.eq_bot_of_card_eq _ h6
    rw [hCb, sup_bot_eq] at hL
    rw [hL]
    exact twoResidual_mono le_top
  · exact h6



theorem card_inf (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    Nat.card ↥(pCoreOf 2 G₂ ⊓ K) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := hT.four_le_card_inf
  have hcard : Nat.card ↥K = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [Nat.card_congr eK.toEquiv, psl2_card_formula F hT.isOddPrimePower, hT.card_field]
    have h2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
      obtain ⟨m, hm⟩ : Odd (p ^ f) := hT.card_field ▸ hT.odd_card_field
      rw [hm]
      exact ⟨2 * m * m + 2 * m, by rw [Nat.sub_eq_of_eq_add]; ring⟩
    exact Nat.mul_div_assoc _ h2
  have hdvd : Nat.card ↥(pCoreOf 2 G₂ ⊓ K) ∣ p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      pCoreOf 2 G₂ ⊓ K ≤ K)).toEquiv.symm ▸ Subgroup.card_subgroup_dvd_card _
  have h8 := not_eight_dvd_card_psl_two hT.mod_eight
  obtain ⟨k, hk⟩ := ((pCoreOf_isPGroup 2 G₂).to_le (inf_le_left :
    pCoreOf 2 G₂ ⊓ K ≤ pCoreOf 2 G₂)).exists_card_eq
  rw [hk] at h4 hdvd ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk2
    apply h8
    refine Dvd.dvd.trans ?_ hdvd
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    rw [pow_add]
    exact Dvd.intro _ rfl
  interval_cases k <;> simp_all

theorem mem_inf_of_commute
    (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) {g : D} (hg : g ∈ G₂)
    (hc : ∀ v ∈ pCoreOf 2 G₂ ⊓ K, g * v = v * g) : g ∈ pCoreOf 2 G₂ ⊓ K := by
  have hodd := hT.isOddPrimePower
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  set ρK := (hT.rho eK).comp K.subtype with hρK
  have hinj : Function.Injective ρK := hT.rho_comp_injective eK
  set V : Subgroup ↥K := (Q₂ ⊓ K).subgroupOf K with hV
  have hEA := hT.elemAbelian.1
  have hVcard : Nat.card ↥(V.map ρK) = 4 := by
    rw [← Nat.card_congr (V.equivMapOfInjective ρK hinj).toEquiv, hV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q₂ ⊓ K ≤ K)).toEquiv]
    exact hT.card_inf eK
  have hVK : IsKleinFour ↥(V.map ρK) := by
    refine isKleinFour_of_card_four_of_mul_self hVcard fun ⟨_, v, hv, rfl⟩ => Subtype.ext ?_
    rw [Subgroup.coe_mul, ← map_mul, Subgroup.coe_one]
    have hv2 : v * v = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hEA.2 _ (Subgroup.mem_subgroupOf.mp hv).1)
    rw [hv2, map_one]
  have hcen := pgl2_kleinFour_centralizer_eq_self F hodd (V.map ρK) hVK
  have hgC : hT.rho eK g ∈
      Subgroup.centralizer ((V.map ρK : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    change hT.rho eK v * hT.rho eK g = hT.rho eK g * hT.rho eK v
    rw [← map_mul, ← map_mul, hc _ (Subgroup.mem_subgroupOf.mp hv)]
  rw [hcen] at hgC
  obtain ⟨v, hv, hvg⟩ := hgC
  have hvQ : (v : D) ∈ Q₂ ⊓ K := Subgroup.mem_subgroupOf.mp hv
  have hvc : (v : D)⁻¹ * g ∈ G₂ ⊓ Subgroup.centralizer (K : Set D) := by
    refine Subgroup.mem_inf.mpr ⟨G₂.mul_mem (G₂.inv_mem (pCoreOf_le 2 G₂ hvQ.1)) hg, ?_⟩
    rw [← ker_rho hT eK, MonoidHom.mem_ker, map_mul, map_inv]
    change (ρK v)⁻¹ * hT.rho eK g = 1
    rw [hvg, inv_mul_cancel]
  rw [hT.inf_centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hvc
  rw [← hvc]
  exact hvQ

theorem pCoreOf_le_component
    (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    pCoreOf 2 G₂ ≤ K := fun q hq =>
  (hT.mem_inf_of_commute eK (pCoreOf_le 2 G₂ hq) fun v hv => congrArg
    (Subtype.val : ↥(pCoreOf 2 G₂) → D) (hT.elemAbelian.1.1.is_comm.comm ⟨q, hq⟩ ⟨v, hv.1⟩)).2

theorem inf_inf_eq
    (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    G₁ ⊓ G₂ ⊓ K = pCoreOf 2 G₂ ∧ Nat.card ↥(pCoreOf 2 G₂) = 4 ∧ Nat.card ↥(G₁ ⊓ G₂) = 8 := by
  have h := hT.triple
  have hQK := hT.pCoreOf_le_component eK
  obtain ⟨-, e2, -⟩ := hT.inf_eq
  have hQ : pCoreOf 2 G₂ ⊓ K = pCoreOf 2 G₂ := inf_eq_left.mpr hQK
  have hQ4 : Nat.card ↥(pCoreOf 2 G₂) = 4 := by rw [← hQ]; exact hT.card_inf eK
  refine ⟨?_, hQ4, ?_⟩
  · rw [inf_comm G₁ G₂, ← e2, hQ]
  · have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 G₂) (K := G₁ ⊓ G₂)
    rw [relIndex_pCoreOf_right h, inf_eq_left.mpr (pCoreOf_le_inf_right h), hQ4] at h1
    omega

theorem commute_of_mem_twoResidual (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) {w c : D}
    (hw : w ∈ twoResidual ⊤) (hc : c ∈ Subgroup.centralizer (K : Set D)) : w * c = c * w := by
  have := hT.normal
  rw [← hT.sup_centralizer eK, Subgroup.mem_sup_of_normal_left] at hw
  obtain ⟨k, hk, c', hc', rfl⟩ := hw
  have hcomm : ∀ a ∈ Subgroup.centralizer (K : Set D), ∀ b ∈ Subgroup.centralizer (K : Set D),
      a * b = b * a := by
    have h3 := hT.card_centralizer eK
    intro a ha b hb
    obtain ⟨g, hg⟩ := (isCyclic_of_prime_card (p := 3) (α := Subgroup.centralizer (K : Set D))
      (by rw [h3])).exists_generator
    obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
    obtain ⟨j, hj⟩ := hg ⟨b, hb⟩
    have := congrArg Subtype.val (show (⟨a, ha⟩ : Subgroup.centralizer (K : Set D)) * ⟨b, hb⟩ =
        ⟨b, hb⟩ * ⟨a, ha⟩ by rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc k hk
  calc k * c' * c = k * (c' * c) := by group
    _ = k * (c * c') := by rw [hcomm c' hc' c hc]
    _ = (k * c) * c' := by group
    _ = c * k * c' := by rw [h1]
    _ = c * (k * c') := by group


theorem exists_inv_centralizer
    (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) :
    ∃ τ ∈ G₁ ⊓ G₂, ∀ c ∈ Subgroup.centralizer (K : Set D), τ * c * τ⁻¹ = c⁻¹ := by
  have h := hT.triple
  have hKn := hT.normal
  have hCn := normal_centralizer_of_normal hKn
  have hC3 := hT.card_centralizer eK
  set C := Subgroup.centralizer (K : Set D) with hC
  obtain ⟨w, hwG, hwo, hwK⟩ : ∃ w ∈ G₂, Odd (orderOf w) ∧ w ∉ K := by
    by_contra hne
    push Not at hne
    apply hT.not_le_right
    rw [twoResidual_eq_oTwoUpper]
    exact (Subgroup.closure_le _).mpr fun x hx => hne x hx.1 hx.2
  have hw3 : w ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h.symm hwG hwo)
  have hwL : w ∈ K ⊔ C := by
    rw [hT.sup_centralizer eK]
    exact mem_twoResidual_of_odd (Subgroup.mem_top w) hwo
  rw [Subgroup.mem_sup_of_normal_left] at hwL
  obtain ⟨k, hk, c, hc, rfl⟩ := hwL
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hwK
    exact hwK hk
  obtain ⟨t₀, ht₀, hinv⟩ := F6.F617Setting.exists_inv_mod_pCoreOf h.symm hwG hw3
  have hinvK : t₀ * (k * c) * t₀⁻¹ * (k * c) ∈ K := hT.pCoreOf_le_component eK hinv
  have hcc : t₀ * c * t₀⁻¹ * c ∈ K ⊓ C := by
    refine ⟨?_, C.mul_mem (hCn.conj_mem c hc t₀) hc⟩
    have hk' : t₀ * k * t₀⁻¹ ∈ K := hKn.conj_mem k hk t₀
    have hcomm : (t₀ * c * t₀⁻¹) * k = k * (t₀ * c * t₀⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hCn.conj_mem c hc t₀) k hk).symm
    have heq : t₀ * c * t₀⁻¹ * c = (t₀ * k * t₀⁻¹ * k)⁻¹ * (t₀ * (k * c) * t₀⁻¹ * (k * c)) := by
      calc t₀ * c * t₀⁻¹ * c = k⁻¹ * (k * (t₀ * c * t₀⁻¹)) * c := by group
        _ = k⁻¹ * ((t₀ * c * t₀⁻¹) * k) * c := by rw [hcomm]
        _ = (t₀ * k * t₀⁻¹ * k)⁻¹ * (t₀ * (k * c) * t₀⁻¹ * (k * c)) := by group
    rw [heq]
    exact K.mul_mem (K.inv_mem (K.mul_mem hk' hk)) hinvK
  rw [inf_centralizer_self_eq_bot eK, Subgroup.mem_bot, mul_eq_one_iff_eq_inv] at hcc
  have ht₀' : t₀ ∈ ((G₁ ⊓ G₂ ⊔ twoResidual G₂ : Subgroup D) : Set D) := by
    rw [inf_sup_twoResidual_right h]
    exact ht₀
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (inf_le_right.trans (le_normalizer_twoResidual G₂))] at ht₀'
  obtain ⟨τ, hτ, l, hl, hτl⟩ := ht₀'
  have hlc : l * c = c * l := hT.commute_of_mem_twoResidual eK (twoResidual_mono le_top hl) hc
  have hτc : τ * c * τ⁻¹ = c⁻¹ := by
    rw [← hcc]
    simp only at hτl
    rw [← hτl]
    calc τ * c * τ⁻¹ = τ * (l * c * l⁻¹) * τ⁻¹ := by rw [hlc]; group
      _ = τ * l * c * (τ * l)⁻¹ := by group
  refine ⟨τ, hτ, fun c₀ hc₀ => ?_⟩
  rcases mem_of_card_eq_three hC3 hc hc1 hc₀ with rfl | rfl | rfl
  · simp
  · exact hτc
  · rw [inv_inv]
    calc τ * c⁻¹ * τ⁻¹ = (τ * c * τ⁻¹)⁻¹ := by group
      _ = c := by rw [hτc, inv_inv]

theorem inducesOuterAut
    (hT : L2 G₁ G₂ K F p f) (eK : ↥K ≃* PSL2 F) {t : D}
    (ht : t ∈ G₁ ⊓ G₂) (htK : t ∉ K) :
    InducesOuterAut t K ∧ InducesOuterAut t (Subgroup.centralizer (K : Set D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.triple
  have hKn := hT.normal
  have hCn := normal_centralizer_of_normal hKn
  have hC3 := hT.card_centralizer eK
  set C := Subgroup.centralizer (K : Set D) with hC
  refine ⟨⟨Subgroup.normalizer_eq_top_iff.mpr hKn ▸ Subgroup.mem_top t, fun k hk => ?_⟩,
    ⟨Subgroup.normalizer_eq_top_iff.mpr hCn ▸ Subgroup.mem_top t, fun k hk => ?_⟩⟩
  ·
    by_contra hall
    push Not at hall
    have hcC : k⁻¹ * t ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hall y hy
      calc y * (k⁻¹ * t) = k⁻¹ * (k * y * k⁻¹) * t := by group
        _ = k⁻¹ * (t * y * t⁻¹) * t := by rw [h1]
        _ = k⁻¹ * t * y := by group
    obtain ⟨m, hm⟩ := h.isPGroup_inf ⟨t, ht⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    set c := k⁻¹ * t with hcdef
    have htkc : t = k * c := by rw [hcdef]; group
    have hcomm : Commute k c := Subgroup.mem_centralizer_iff.mp hcC k hk
    have h1 : k ^ 2 ^ m * c ^ 2 ^ m = 1 := by rw [← hcomm.mul_pow, ← htkc, htm]
    have h2 : c ^ 2 ^ m ∈ K ⊓ C := by
      refine ⟨?_, C.pow_mem hcC _⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem hk _)
    rw [inf_centralizer_self_eq_bot eK, Subgroup.mem_bot] at h2
    have h3 : c ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥C) (x := ⟨c, hcC⟩)
      rw [hC3] at this
      simpa using congrArg Subtype.val this
    have hc1 : c = 1 := by
      have hd1 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
      have hd2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left m (by norm_num)) hd1 hd2)
    apply htK
    rw [htkc, hc1, mul_one]
    exact hk
  ·
    obtain ⟨τ, hτ, hτC⟩ := hT.exists_inv_centralizer eK
    obtain ⟨c, hc, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
      by_contra hne
      push Not at hne
      have : C = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
      rw [this, Subgroup.card_bot] at hC3
      omega
    have hcc : c⁻¹ ≠ c := by
      intro h1
      have h2 : c ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h1]; exact inv_mul_cancel c
      have h3 : c ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥C) (x := ⟨c, hc⟩)
        rw [hC3] at this
        simpa using congrArg Subtype.val this
      apply hc1
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [h2, h3, inv_one, one_mul]
    obtain ⟨hTK, -, -⟩ := hT.inf_inf_eq eK
    have hτK : τ ∉ K := by
      intro hτK
      apply hcc
      rw [← hτC c hc]
      have := (Subgroup.mem_centralizer_iff.mp hc τ hτK)
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    have hidx : ((pCoreOf 2 G₂).subgroupOf (G₁ ⊓ G₂)).index = 2 := relIndex_pCoreOf_right h
    have hmem : (⟨t, ht⟩ : ↥(G₁ ⊓ G₂)) * (⟨τ, hτ⟩ : ↥(G₁ ⊓ G₂))⁻¹ ∈
        (pCoreOf 2 G₂).subgroupOf (G₁ ⊓ G₂) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h1 => absurd (hT.pCoreOf_le_component eK h1) htK,
        fun h1 => absurd (hT.pCoreOf_le_component eK h1) hτK⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    have hq : t * τ⁻¹ ∈ K := hT.pCoreOf_le_component eK (by simpa using hmem)
    have htc : t * c * t⁻¹ = c⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.mp (C.inv_mem hc) _ hq
      calc t * c * t⁻¹ = (t * τ⁻¹) * (τ * c * τ⁻¹) * (t * τ⁻¹)⁻¹ := by group
        _ = (t * τ⁻¹) * c⁻¹ * (t * τ⁻¹)⁻¹ := by rw [hτC c hc]
        _ = c⁻¹ := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨c, hc, fun h1 => hcc ?_⟩
    rw [← htc, h1]
    have := hT.commute_of_mem_twoResidual eK (hT.centralizer_le_twoResidual hk) hc
    rw [this, mul_assoc, mul_inv_cancel, mul_one]


end L2

end CFSG.Quasithin.RonanF617
