module

public import CFSG.Quasithin.Vol2.Ch12Sec5KG
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.Quasithin.H13.S125KG

open CFSG.Open CFSG.Quasithin

variable {G H : Type} [Group G] [Group H]

theorem map_inSubgroup_perfectResidual [Finite G] [Finite H] (f : G →* H) (Y : Subgroup G) :
    (CFSG.inSubgroup CFSG.perfectResidual Y).map f =
      CFSG.inSubgroup CFSG.perfectResidual (Y.map f) := by
  have h := (CFSG.perfect_residual_transport (f.comp Y.subtype)).1
  have hr : (f.comp Y.subtype).range = Y.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr] at h
  show ((CFSG.perfectResidual ↥Y).map Y.subtype).map f =
    (CFSG.perfectResidual ↥(Y.map f)).map (Y.map f).subtype
  rw [Subgroup.map_map, h]

theorem map_oTwoUpper_le (f : G →* H) (D : Subgroup G) :
    (oTwoUpper D).map f ≤ oTwoUpper (D.map f) := by
  rw [oTwoUpper, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hxD, hodd⟩, rfl⟩
  exact mem_oTwoUpper_of_odd (Subgroup.mem_map_of_mem f hxD)
    (Odd.of_dvd_nat hodd (orderOf_map_dvd f x))

theorem map_oTwoUpper_eq [Finite G] (f : G →* H) (D : Subgroup G)
    (hk : ∀ x ∈ D, f x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1) :
    (oTwoUpper D).map f = oTwoUpper (D.map f) := by
  refine le_antisymm (map_oTwoUpper_le f D) ?_
  rw [oTwoUpper, Subgroup.closure_le]
  rintro _ ⟨⟨x, hxD, rfl⟩, hodd⟩
  set m := orderOf (f x) with hm
  obtain ⟨n, hn⟩ := hk (x ^ m) (D.pow_mem hxD m) (by rw [map_pow, hm, pow_orderOf_eq_one])
  have hy : (x ^ 2 ^ n) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hn]
  have hyO : x ^ 2 ^ n ∈ oTwoUpper D := mem_oTwoUpper_of_odd (D.pow_mem hxD _)
    (Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hy))
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · obtain ⟨k, -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e : f x = f ((x ^ 2 ^ n) ^ k) := by
      rw [map_pow, map_pow, ← pow_mul, ← pow_mod_orderOf, ← hm, hk', pow_one]
    rw [SetLike.mem_coe, e]
    exact Subgroup.mem_map_of_mem f ((oTwoUpper D).pow_mem hyO k)
  · have hm1 : m = 1 :=
      le_antisymm h1 (Nat.pos_of_dvd_of_pos (orderOf_map_dvd f x) (orderOf_pos x))
    have e : f x = 1 := by rw [← orderOf_eq_one_iff, ← hm, hm1]
    rw [SetLike.mem_coe, e]
    exact Subgroup.one_mem _

theorem map_oTwoUpper_equiv [Finite G] [Finite H] (ψ : G ≃* H) (D : Subgroup G) :
    (oTwoUpper D).map ψ.toMonoidHom = oTwoUpper (D.map ψ.toMonoidHom) :=
  map_oTwoUpper_eq ψ.toMonoidHom D fun x _ hx => ⟨0, by
    rw [pow_zero, pow_one]
    exact (MulEquiv.map_eq_one_iff ψ).mp hx⟩

theorem map_centralizer_equiv (ψ : G ≃* H) (E : Subgroup G) :
    (Subgroup.centralizer (E : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ((E.map ψ.toMonoidHom : Subgroup H) : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    have h1 := congrArg ψ (h e' he')
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  · intro h e he
    have h1 := h (ψ e) (Subgroup.mem_map_of_mem ψ.toMonoidHom he)
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1

theorem config63_map [Finite G] [Finite H] (ψ : G ≃* H) {S N D : Subgroup G}
    (hc : Config63 S N D) :
    Config63 (S.map ψ.toMonoidHom) (N.map ψ.toMonoidHom) (D.map ψ.toMonoidHom) := by
  obtain ⟨hSD, hDN, hN, hD, hnot⟩ := hc
  have hc : ∀ Y : Subgroup G, Nat.card (Y.map ψ.toMonoidHom) = Nat.card Y := fun Y =>
    Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective
  refine ⟨Subgroup.map_mono hSD, Subgroup.map_mono hDN, by rw [hc, hc, hN],
    by rw [hc, hc, hD], fun h => hnot ?_⟩
  rw [← map_inSubgroup_perfectResidual, ← Subgroup.map_sup] at h
  exact (Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp h

theorem oTwoUpper_sup_eq [Finite G] {S D : Subgroup G} (hSD : S ≤ D) (hS : IsPGroup 2 ↥S)
    (hD : Nat.card D = 3 * Nat.card S) : oTwoUpper D ⊔ S = D := by
  set T := oTwoUpper D ⊔ S with hT
  have hTD : T ≤ D := sup_le (oTwoUpper_le D) hSD
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_right : S ≤ T)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hTD
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hkm : k * m = 3 := by
    rw [hk, hD, mul_assoc, mul_comm 3] at hm
    exact (Nat.eq_of_mul_eq_mul_left hpos hm).symm
  have hk3 : k = 1 ∨ k = 3 := by
    have : k ∣ 3 := ⟨m, hkm.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hk3 with rfl | rfl
  · exfalso
    have hTS : T = S := (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hk, mul_one])).symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3 (by rw [hD]; exact Dvd.intro _ rfl)
    have hxO : (x : G) ∈ oTwoUpper D := mem_oTwoUpper_of_odd x.2 (by
      rw [Subgroup.orderOf_coe, hx]; exact ⟨1, rfl⟩)
    have hxS : (x : G) ∈ S := by
      have h1 : (x : G) ∈ T := le_sup_left (a := oTwoUpper D) hxO
      rwa [hTS] at h1
    obtain ⟨n, hn⟩ := hS ⟨x, hxS⟩
    have h2 : orderOf (x : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hn)
    rw [Subgroup.orderOf_coe, hx] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
    omega
  · exact Subgroup.eq_of_le_of_card_ge hTD (by rw [hD, hk, mul_comm])

theorem isSolvable_of_card_eq_two_pow_mul_three [Finite G] {k : ℕ} (h : Nat.card G = 2 ^ k * 3) :
    Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, Nat.primeFactors_mul (by positivity) (by norm_num)]
  refine (Finset.card_union_le _ _).trans ?_
  rw [Nat.Prime.primeFactors Nat.prime_three, Finset.card_singleton]
  have : (2 ^ k).primeFactors.card ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.primeFactors_prime_pow hk.ne' Nat.prime_two, Finset.card_singleton]
  omega

theorem exists_ne_one_mem_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {P E : Subgroup G}
    (hP : IsPGroup p ↥P) (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hpE : p ∣ Nat.card E) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ Subgroup.centralizer (P : Set G) := by
  let _ : MulAction ↥P ↥E :=
    { smul := fun g e => ⟨(g : G) * e * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hPE g.2) e).mp e.2⟩
      one_smul := fun e => Subtype.ext (show ((1 : ↥P) : G) * e * ((1 : ↥P) : G)⁻¹ = e by simp)
      mul_smul := fun g h e => Subtype.ext (show ((g * h : ↥P) : G) * e * ((g * h : ↥P) : G)⁻¹ =
          (g : G) * ((h : G) * e * (h : G)⁻¹) * (g : G)⁻¹ by
        simp only [Subgroup.coe_mul]
        group) }
  have h := hP.card_modEq_card_fixedPoints ↥E
  have hone : (1 : ↥E) ∈ MulAction.fixedPoints ↥P ↥E := fun g =>
    Subtype.ext (show (g : G) * ((1 : ↥E) : G) * (g : G)⁻¹ = ((1 : ↥E) : G) by simp)
  have hmod : p ∣ Nat.card (MulAction.fixedPoints ↥P ↥E) :=
    (Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpE)))
  have h2 : 1 < Nat.card (MulAction.fixedPoints ↥P ↥E) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P ↥E) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
    have := Nat.le_of_dvd hpos hmod
    have hp := (Fact.out : p.Prime).two_le
    omega
  have : Nontrivial ↥(MulAction.fixedPoints ↥P ↥E) := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (⟨1, hone⟩ : ↥(MulAction.fixedPoints ↥P ↥E))
  refine ⟨e, e.2, fun h1 => hne (Subtype.ext (Subtype.ext h1)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h3 : g * e * g⁻¹ = e := congrArg Subtype.val (he ⟨g, hg⟩)
  calc g * e = g * e * g⁻¹ * g := by group
    _ = e * g := by rw [h3]

theorem exists_equiv_sylow {Γ : Type} {inst : Group Γ} [Finite Γ] {T : Subgroup Γ}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {X : Type} [Group X] (hX : Nonempty (X ≃* Γ))
    {S : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ ψ : X ≃* Γ, S.map ψ.toMonoidHom = T := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp
    (CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hS)
  obtain ⟨hp₀, hi₀⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : T = (S.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem alpha_of_sylow {Γ : Type} {inst : Group Γ} [Finite Γ] {T : Subgroup Γ}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (h : ∀ N D : Subgroup Γ, Config63 T N D → Subgroup.normalizer (oTwoUpper D : Set Γ) ≤ N)
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Γ)) {S N D : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) :
    Subgroup.normalizer (oTwoUpper D : Set X) ≤ N := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_sylow hT hX hS
  have hc' := config63_map ψ hc
  rw [hψ] at hc'
  have h1 := h _ _ hc'
  rw [← map_oTwoUpper_equiv, ← Subgroup.map_equiv_normalizer_eq] at h1
  exact (Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp h1

theorem beta_of_sylow {Γ : Type} {inst : Group Γ} [Finite Γ] {T : Subgroup Γ}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (h : ∀ N D E : Subgroup Γ, Config63 T N D → E ≤ pCoreOf 2 N →
      N ≤ Subgroup.normalizer (E : Set Γ) → Nat.card E = 8 →
      ⁅CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set Γ)),
          CFSG.inSubgroup CFSG.perfectResidual N⁆ ≤
          pCoreOf 2 (Subgroup.normalizer (E : Set Γ)) ∧
        oTwoUpper D ≤ CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set Γ)) ⊔
          pCoreOf 2 (Subgroup.normalizer (E : Set Γ)))
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Γ)) {S N D E : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) (hEO : E ≤ pCoreOf 2 N)
    (hNE : N ≤ Subgroup.normalizer (E : Set X)) (hE : Nat.card E = 8) :
    ⁅CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set X)),
        CFSG.inSubgroup CFSG.perfectResidual N⁆ ≤
        pCoreOf 2 (Subgroup.normalizer (E : Set X)) ∧
      oTwoUpper D ≤ CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set X)) ⊔
        pCoreOf 2 (Subgroup.normalizer (E : Set X)) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_sylow hT hX hS
  have hc' := config63_map ψ hc
  rw [hψ] at hc'
  have hEO' : E.map ψ.toMonoidHom ≤ pCoreOf 2 (N.map ψ.toMonoidHom) := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hEO
  have hNE' : N.map ψ.toMonoidHom ≤
      Subgroup.normalizer ((E.map ψ.toMonoidHom : Subgroup Γ) : Set Γ) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNE
  have hE' : Nat.card (E.map ψ.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hE]
  obtain ⟨h1, h2⟩ := h _ _ _ hc' hEO' hNE' hE'
  rw [← map_centralizer_equiv, ← map_inSubgroup_perfectResidual, ← map_inSubgroup_perfectResidual,
    ← Subgroup.map_equiv_normalizer_eq, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv,
    ← Subgroup.map_commutator] at h1
  rw [← map_oTwoUpper_equiv, ← map_centralizer_equiv, ← map_inSubgroup_perfectResidual,
    ← Subgroup.map_equiv_normalizer_eq, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv,
    ← Subgroup.map_sup] at h2
  exact ⟨(Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp h1,
    (Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).mp h2⟩

theorem card_sSup_solvable_eq {Γ : Type} {inst : Group Γ} [Finite Γ] {T : Subgroup Γ}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {X : Type} [Group X] (hX : Nonempty (X ≃* Γ))
    {S : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Nat.card ↥(sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H}) =
      Nat.card ↥(sSup {H : Subgroup Γ | T ≤ H ∧ Group.IsSolvable ↥H}) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_sylow hT hX hS
  have h : (sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H}).map ψ.toMonoidHom =
      sSup {H : Subgroup Γ | T ≤ H ∧ Group.IsSolvable ↥H} := by
    refine CFSG.LieType.SteinbergBR.map_sSup_of_equiv ψ (fun K hK => ⟨?_, ?_⟩)
      (fun K hK => ⟨?_, ?_⟩)
    · rw [← hψ]
      exact Subgroup.map_mono hK.1
    · have := hK.2
      exact CFSG.LieType.SteinbergBR.isSolvable_map _ K
    · rw [← Subgroup.map_le_iff_le_comap, hψ]
      exact hK.1
    · have := hK.2
      exact Group.isSolvable_of_isSolvable_injective (f := (ψ.toMonoidHom.comp
        (K.comap ψ.toMonoidHom).subtype).codRestrict K (fun x => x.2))
        (fun a b hab => Subtype.ext (ψ.injective (congrArg Subtype.val hab)))
  rw [← h, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]

end CFSG.Quasithin.H13.S125KG
