module

public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Inner
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139A5
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin.H13.L139

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native (SQTKHypCat A38ForSQTKCat)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem comp_mem_of_two {Q : Type*} [Group Q] {A B E S : Subgroup Q}
    (hAB : ⁅A, B⁆ = ⊥) (hAB' : A ⊓ B = ⊥) (hEA : E ≤ A) (hES : E ≤ S) (hS : IsPGroup 2 S)
    (hmax : ∀ F : Subgroup Q, F ≤ A → IsPGroup 2 F → E ≤ F → F = E)
    {a b : Q} (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ∈ S) : a ∈ E := by
  have hcomm : ∀ (x : ↥A) (y : ↥B), Commute (A.subtype x) (B.subtype y) := by
    intro x y
    have h := Subgroup.commutator_mem_commutator x.2 y.2
    rw [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm with hφ
  have hφinj : Function.Injective φ := (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
    ⟨A.subtype_injective, B.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
      exact hAB'⟩
  set e := MonoidHom.ofInjective hφinj with he
  set pr : ↥φ.range →* ↥A := (MonoidHom.fst _ _).comp e.symm.toMonoidHom with hpr
  have hpr_apply : ∀ (x : ↥A) (y : ↥B), pr ⟨φ (x, y), ⟨(x, y), rfl⟩⟩ = x := by
    intro x y
    have : e.symm ⟨φ (x, y), ⟨(x, y), rfl⟩⟩ = (x, y) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [MonoidHom.ofInjective_apply]
    simp only [hpr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MonoidHom.coe_fst]
  set S' : Subgroup ↥φ.range := S.comap φ.range.subtype with hS'
  have hS'2 : IsPGroup 2 S' := hS.comap_of_injective _ φ.range.subtype_injective
  set F : Subgroup Q := (S'.map pr).map A.subtype with hF
  have hφapp : ∀ (x : ↥A) (y : ↥B), φ (x, y) = (x : Q) * y := fun x y => rfl
  have hmemF : ∀ (x : ↥A) (y : ↥B), (x : Q) * y ∈ S → (x : Q) ∈ F := by
    intro x y hxy
    refine ⟨x, ⟨⟨φ (x, y), ⟨(x, y), rfl⟩⟩, ?_, hpr_apply x y⟩, rfl⟩
    show φ (x, y) ∈ S
    rw [hφapp]
    exact hxy
  have hEF : E ≤ F := by
    intro x hx
    have := hmemF ⟨x, hEA hx⟩ 1 (by rw [Subgroup.coe_one, mul_one]; exact hES hx)
    exact this
  have hFE := hmax F (Subgroup.map_subtype_le _) ((hS'2.map pr).map A.subtype) hEF
  rw [← hFE]
  exact hmemF ⟨a, ha⟩ ⟨b, hb⟩ hab

section Quot

variable {H : Subgroup G}

theorem map_conjByElt_subgroupOf (X : Subgroup G) {u : G} (hu : u ∈ H) :
    ((conjByElt u X).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      ((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨u, hu⟩)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : u⁻¹ * (z : G) * u ∈ X := mem_conjByElt.mp hz
    refine ⟨QuotientGroup.mk' _ (⟨u, hu⟩⁻¹ * z * ⟨u, hu⟩), ⟨⟨u, hu⟩⁻¹ * z * ⟨u, hu⟩, hz', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    group
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · show (u * (x : G) * u⁻¹) ∈ conjByElt u X
      rw [mem_conjByElt]
      have : u⁻¹ * (u * (x : G) * u⁻¹) * u = x := by group
      rw [this]
      exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

variable [Finite G]

theorem img_injOn {X₁ X₂ : Subgroup G} (h₁ : X₁ ∈ cComp H) (h₂ : X₂ ∈ cComp H)
    (h : (X₁.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      (X₂.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) : X₁ = X₂ := by
  have hsolv : Group.IsSolvable (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact A320.isSolvable_pCore_two ↥H
  have h3 := map_injOn_cComp_top _ hsolv (subgroupOf_mem_cComp h₁) (subgroupOf_mem_cComp h₂) h
  have h4 := Subgroup.subgroupOf_inj.mp h3
  rwa [inf_eq_left.mpr (le_of_mem_cComp h₁), inf_eq_left.mpr (le_of_mem_cComp h₂)] at h4

end Quot

theorem conjByElt_mul (a b : G) (X : Subgroup G) :
    conjByElt (a * b) X = conjByElt a (conjByElt b X) := by
  unfold conjByElt
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjByElt_one (X : Subgroup G) : conjByElt 1 X = X := by
  unfold conjByElt
  rw [map_one]
  exact Subgroup.map_id X

theorem mem_normalizer_iff_conjByElt {a : G} {X : Subgroup G} :
    a ∈ Subgroup.normalizer (X : Set G) ↔ conjByElt a X = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem mem_normalizer_of_conj_le {Q : Type*} [Group Q] [Finite Q] {E : Subgroup Q} {g : Q}
    (h : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨e, he, rfl⟩
    exact h e he
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_eq_four {k m : ℕ} (h : 2 ^ k * m = 60) (hm : ¬ 2 ∣ m) : 2 ^ k = 4 := by
  have hk : k ≤ 6 := by
    by_contra hk
    have h1 : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h; omega
    have h3 : 2 ^ k ≤ 2 ^ k * m := Nat.le_mul_of_pos_right _ h2
    omega
  interval_cases k <;> omega

theorem a5_false_sub {Q : Type} [Group Q] {A : Subgroup Q}
    (φ : ↥A ≃* ↥(alternatingGroup (Fin 5))) {E : Subgroup Q} (hEA : E ≤ A) (hE : Nat.card E = 4)
    {c ℓ : Q} (hcA : c ∈ A) (hℓA : ℓ ∈ A) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hEc : ∀ e ∈ E, ∃ i : ℕ, ∃ e' ∈ E, e * c = c ^ i * e')
    (hℓ : ℓ ∈ Subgroup.normalizer (E : Set Q)) (hℓc : ℓ * c * ℓ⁻¹ = c⁻¹) : False := by
  refine A5F.a5_false φ (E := E.subgroupOf A) (c := ⟨c, hcA⟩) (ℓ := ⟨ℓ, hℓA⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hE]
  · exact fun h => hc1 (congrArg Subtype.val h)
  · exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hc3)
  · intro e he
    obtain ⟨i, e', he', h⟩ := hEc e he
    have he'A : e' ∈ A := by
      have : e' = (c ^ i)⁻¹ * (e * c) := by rw [h]; group
      rw [this]
      exact A.mul_mem (A.inv_mem (A.pow_mem hcA i)) (A.mul_mem e.2 hcA)
    refine ⟨i, ⟨e', he'A⟩, he', Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    exact h
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp hℓ x
  · exact Subtype.ext hℓc

variable [Finite G]

theorem eq_one_of_mem_pCoreOf_two {H : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 H)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨x, hx⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have := pow_gcd_eq_one.mpr ⟨hm', h3⟩
  rwa [show Nat.gcd (2 ^ m) 3 = 1 from Nat.Coprime.pow_left m (by norm_num), pow_one] at this

theorem le_normalizer_of_comm {P U : Subgroup G} (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hUP : U ≤ P) : P ≤ Subgroup.normalizer (U : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_le
  intro u hu
  rw [hPab a ha u (hUP hu), mul_inv_cancel_right]
  exact hu

theorem a5_case_false (h38 : A38ForSQTKCat) (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T X P K : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hX : IsXi T X) (hX9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X) (hP3 : IsPGroup 3 P)
    (hP9 : Nat.card P = 9) (hK : quasithinIsLocal T K) {t : G} (htT : t ∈ T)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hPdec : P = (P ⊓ K) ⊔ conjByElt t (P ⊓ K)) (hPint : (P ⊓ K) ⊓ conjByElt t (P ⊓ K) = ⊥)
    (hA5 : IsAlt 5 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hin : ∀ s ∈ T, s ∈ Subgroup.normalizer (K : Set G) → ∃ ℓ, InnerOn K s ℓ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hpX, hSyl⟩ := NQCore.sylow_of_card_eq_relIndex hX (p := 3) (by norm_num) hPX hP3
    (hP9.trans hX9.symm)
  have hSG : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo hT le_top
  have hirr := NQCore.irr_of_sylow hSG le_top hX (by norm_num) hpX hSyl
  have hmul := NQCore.mul_subset_of_sylow hSG le_top hX (by norm_num) hpX hSyl
  have hexp := NQCore.exp_of_sylow hX (by norm_num) hpX hSyl
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥P)
      (by rw [hP9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hPP : ⁅P, P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hPab a ha b hb
  set H : Subgroup G := K ⊔ T with hHdef
  have hKH : K ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hHne : pCoreOf 2 H ≠ ⊥ := hK.2.2.2
  have hKc : K ∈ cComp H := hK.2.1
  set ρ : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hρ
  have hSQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hHne
  have h38Q := h38 _ hSQ.toCat
  set Kh : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (K.subgroupOf H).map ρ with hKh
  have hKhc : Kh ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    A318.mem_cComp_quotient (subgroupOf_mem_cComp hKc)
  set Th : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (T.subgroupOf H).map ρ with hTh
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  have hTh2 : IsPGroup 2 Th := by
    have : IsPGroup 2 (T.subgroupOf H) :=
      hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact this.map ρ
  have hThS : IsSylowTwoOf Th ⊤ := by
    refine ⟨le_top, hTh2, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact fun h => hTsyl.2.2 (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have htH : t ∈ H := hTH htT
  have hKt : conjByElt t K ∈ cComp H := map_conj_mem_cComp hKc htH
  have hKtne : conjByElt t K ≠ K := fun h => htK (mem_normalizer_iff_conjByElt.mpr h)
  have hmemT : ∀ u ∈ T, ∀ hu : u ∈ H, Kh.map (MulAut.conj (ρ ⟨u, hu⟩)).toMonoidHom ∈
      conjSubgroupsBy Th Kh := fun u huT hu => ⟨ρ ⟨u, hu⟩, ⟨⟨u, hu⟩, huT, rfl⟩, rfl⟩
  rcases (h38Q Kh hKhc).2 Th hThS with ⟨-, hset, -⟩ | ⟨t₀, -, -, hset, -, hcomm, hinter, -, -⟩
  · apply hKtne
    have hm := hmemT t htT htH
    rw [hset] at hm
    exact img_injOn hKt hKc ((map_conjByElt_subgroupOf K htH).trans hm)
  set B : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := Kh.map (MulAut.conj t₀).toMonoidHom with hB
  have horbQ : ∀ u ∈ T, ∀ hu : u ∈ H, ((conjByElt u K).subgroupOf H).map ρ = Kh ∨
      ((conjByElt u K).subgroupOf H).map ρ = B := by
    intro u huT hu
    rw [map_conjByElt_subgroupOf K hu]
    have hm := hmemT u huT hu
    rw [hset] at hm
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hKtB : ((conjByElt t K).subgroupOf H).map ρ = B :=
    (horbQ t htT htH).resolve_left fun h => hKtne (img_injOn hKt hKc h)
  have horb : ∀ u ∈ T, conjByElt u K = K ∨ conjByElt u K = conjByElt t K := by
    intro u huT
    have hu := hTH huT
    have hKu : conjByElt u K ∈ cComp H := map_conj_mem_cComp hKc hu
    rcases horbQ u huT hu with h | h
    · exact Or.inl (img_injOn hKu hKc h)
    · exact Or.inr (img_injOn hKu hKt (h.trans hKtB.symm))
  set PK : Subgroup G := P ⊓ K with hPKdef
  have htPP : conjByElt t P = P := mem_normalizer_iff_conjByElt.mp htP
  have hPKne : PK ≠ ⊥ := by
    intro h
    have hbot : conjByElt t (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _
    have hP : P = ⊥ := by rw [hPdec, h, hbot, bot_sup_eq]
    rw [hP, Subgroup.card_bot] at hP9
    norm_num at hP9
  obtain ⟨⟨c, hcPK⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPKne
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcP : c ∈ P := hcPK.1
  have hcK : c ∈ K := hcPK.2
  have hc3 : c ^ 3 = 1 := hexp c hcP
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1'
  have hPKtP : conjByElt t PK ≤ P :=
    calc conjByElt t PK ≤ conjByElt t P := Subgroup.map_mono inf_le_left
      _ = P := htPP
  have hPKc : Subgroup.zpowers c = PK := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcPK)
    rw [Nat.card_zpowers, hoc]
    have hdvd : Nat.card PK ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP9]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne9 : Nat.card PK ≠ 9 := by
      intro h9
      have hPKP : PK = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hP9])
      have hc : c ∈ PK ⊓ conjByElt t PK := ⟨hcPK, by rw [hPKP, htPP]; exact hcP⟩
      rw [hPint] at hc
      exact hc1' hc
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rcases m with _ | _ | _ | m
    · rw [hm']; norm_num
    · rw [hm']; norm_num
    · exact (hne9 (by rw [hm']; norm_num)).elim
    · omega
  have hpow : ∀ y ∈ PK, ∃ i < 3, c ^ i = y := by
    intro y hy
    rw [← hPKc] at hy
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp
      ((isOfFinOrder_of_finite c).mem_zpowers_iff_mem_range_orderOf.mp hy)
    rw [hoc, Finset.mem_range] at hi
    exact ⟨i, hi, hiy⟩
  set d : G := t * c * t⁻¹ with hd
  have hdP : d ∈ P := (Subgroup.mem_normalizer_iff.mp htP c).mp hcP
  have hdPKt : d ∈ conjByElt t PK := by
    rw [mem_conjByElt, show t⁻¹ * d * t = c by rw [hd]; group]
    exact hcPK
  have hdisj : ∀ x ∈ PK, x ∈ conjByElt t PK → x = 1 := fun x h1 h2 => by
    have : x ∈ PK ⊓ conjByElt t PK := ⟨h1, h2⟩
    rwa [hPint, Subgroup.mem_bot] at this
  have hcd : c ≠ d := fun h => hc1' (hdisj c hcPK (by rw [h]; exact hdPKt))
  have hcd1 : c * d ≠ 1 := fun h => by
    have hc : c = d⁻¹ := eq_inv_of_mul_eq_one_left h
    exact hc1' (hdisj c hcPK (by rw [hc]; exact (conjByElt t PK).inv_mem hdPKt))
  obtain ⟨s, hsT, hsP, hsK, hsc⟩ : ∃ s ∈ T, s ∈ Subgroup.normalizer (P : Set G) ∧
      s ∈ Subgroup.normalizer (K : Set G) ∧ s * c * s⁻¹ = c⁻¹ := by
    by_contra hcon
    have hcen : ∀ s ∈ T, s ∈ Subgroup.normalizer (P : Set G) →
        s ∈ Subgroup.normalizer (K : Set G) → s * c * s⁻¹ = c := by
      intro s hsT hsP hsK
      have hmem : s * c * s⁻¹ ∈ PK :=
        ⟨(Subgroup.mem_normalizer_iff.mp hsP c).mp hcP,
          (Subgroup.mem_normalizer_iff.mp hsK c).mp hcK⟩
      obtain ⟨i, hi, hci⟩ := hpow _ hmem
      interval_cases i
      · exfalso
        rw [pow_zero] at hci
        exact hc1' (conj_eq_one_iff.mp hci.symm)
      · rw [pow_one] at hci
        exact hci.symm
      · exfalso
        apply hcon
        refine ⟨s, hsT, hsP, hsK, ?_⟩
        rw [← hci, eq_inv_iff_mul_eq_one, ← pow_succ]
        exact hc3
    have hf : ∀ w ∈ T, w ∈ Subgroup.normalizer (P : Set G) →
        w * c * w⁻¹ = c ∨ w * c * w⁻¹ = d := by
      intro w hwT hwP
      rcases horb w hwT with h | h
      · exact Or.inl (hcen w hwT hwP (mem_normalizer_iff_conjByElt.mpr h))
      · right
        have h1 : conjByElt (t⁻¹ * w) K = K := by
          rw [conjByElt_mul, h, ← conjByElt_mul, inv_mul_cancel, conjByElt_one]
        have h2 := hcen (t⁻¹ * w) (T.mul_mem (T.inv_mem htT) hwT)
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ htP) hwP) (mem_normalizer_iff_conjByElt.mpr h1)
        calc w * c * w⁻¹ = t * ((t⁻¹ * w) * c * (t⁻¹ * w)⁻¹) * t⁻¹ := by group
          _ = d := by rw [h2, hd]
    have hU : T ⊓ Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers (c * d) : Subgroup G) : Set G) := by
      rintro u ⟨huT, huP⟩
      have hd' : u * d * u⁻¹ = (u * t) * c * (u * t)⁻¹ := by rw [hd]; group
      have hfix : u * (c * d) * u⁻¹ = c * d := by
        have hsplit : u * (c * d) * u⁻¹ = (u * c * u⁻¹) * (u * d * u⁻¹) := by group
        have hne : u * c * u⁻¹ ≠ u * d * u⁻¹ := fun h =>
          hcd (mul_left_cancel (mul_right_cancel h))
        rw [hsplit]
        rcases hf u huT huP with h1 | h1 <;>
          rcases hf (u * t) (T.mul_mem huT htT) (Subgroup.mul_mem _ huP htP) with h2 | h2
        · exact (hne (by rw [h1, hd', h2])).elim
        · rw [h1, hd', h2]
        · rw [h1, hd', h2]
          exact hPab d hdP c hcP
        · exact (hne (by rw [h1, hd', h2])).elim
      rw [mem_normalizer_iff_conjByElt]
      unfold conjByElt
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hfix
    rcases hirr (Subgroup.zpowers (c * d)) (by rw [hPP]; exact bot_le)
        (Subgroup.zpowers_le.mpr (P.mul_mem hcP hdP)) hU with h | h
    · rw [hPP] at h
      apply hcd1
      have : c * d ∈ Subgroup.zpowers (c * d) := Subgroup.mem_zpowers _
      rwa [h, Subgroup.mem_bot] at this
    · have h1 := congrArg (fun U : Subgroup G => Nat.card U) h
      simp only [Nat.card_zpowers, hP9] at h1
      have h3 := orderOf_dvd_of_pow_eq_one (hexp _ (P.mul_mem hcP hdP))
      rw [h1] at h3
      norm_num at h3
  obtain ⟨ℓ, hℓK, hℓ⟩ := hin s hsT hsK
  have hOKH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    SQTKHyp.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hρ1 : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → ρ x = 1 := fun x hx => (mem_pCoreOf_iff x).mp hx
  have hcH : c ∈ H := hKH hcK
  have hℓH : ℓ ∈ H := hKH hℓK
  have hsH : s ∈ H := hTH hsT
  have hconjQ : ∀ k : ↥H, (k : G) ∈ K → ρ ⟨ℓ, hℓH⟩ * ρ k * (ρ ⟨ℓ, hℓH⟩)⁻¹ =
      ρ ⟨s, hsH⟩ * ρ k * (ρ ⟨s, hsH⟩)⁻¹ := by
    intro k hk
    have h1 := hρ1 (((⟨s, hsH⟩ : ↥H) * k * (⟨s, hsH⟩ : ↥H)⁻¹)⁻¹ *
      ((⟨ℓ, hℓH⟩ : ↥H) * k * (⟨ℓ, hℓH⟩ : ↥H)⁻¹)) (hOKH (hℓ k hk))
    simp only [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hsc' : ((⟨s, hsH⟩ : ↥H) * ⟨c, hcH⟩ * (⟨s, hsH⟩ : ↥H)⁻¹ : ↥H) = (⟨c, hcH⟩ : ↥H)⁻¹ :=
    Subtype.ext hsc
  have hsqc : ρ ⟨s, hsH⟩ * ρ ⟨c, hcH⟩ * (ρ ⟨s, hsH⟩)⁻¹ = (ρ ⟨c, hcH⟩)⁻¹ := by
    have := congrArg ρ hsc'
    simpa only [map_mul, map_inv] using this
  have hlqc := (hconjQ ⟨c, hcH⟩ hcK).trans hsqc
  have hcqK : ρ ⟨c, hcH⟩ ∈ Kh := ⟨⟨c, hcH⟩, hcK, rfl⟩
  have hlqK : ρ ⟨ℓ, hℓH⟩ ∈ Kh := ⟨⟨ℓ, hℓH⟩, hℓK, rfl⟩
  have hsqT : ρ ⟨s, hsH⟩ ∈ Th := ⟨⟨s, hsH⟩, hsT, rfl⟩
  have hcq1 : ρ ⟨c, hcH⟩ ≠ 1 := fun h =>
    hc1' (eq_one_of_mem_pCoreOf_two ((mem_pCoreOf_iff (K := H) ⟨c, hcH⟩).mpr h) hc3)
  have hcq3 : ρ ⟨c, hcH⟩ ^ 3 = 1 := by
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hc3)
    rw [← map_pow, this, map_one]
  obtain ⟨eA⟩ := hA5
  set gK : ↥K →* ↥Kh := MonoidHom.codRestrict (ρ.comp (Subgroup.inclusion hKH)) Kh
    (fun x => ⟨Subgroup.inclusion hKH x, x.2, rfl⟩) with hgK
  have hgKsurj : Function.Surjective gK := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : CFSG.pCore 2 ↥K ≤ gK.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show ρ ⟨x, hKH x.2⟩ = 1
    exact hρ1 _ (hOKH ((mem_pCoreOf_iff x).mpr ((QuotientGroup.eq_one_iff x).mpr hx)))
  set f := QuotientGroup.lift (CFSG.pCore 2 ↥K) gK hker with hfdef
  have hfsurj : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ gK hgKsurj hker
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := eA.toEquiv.nontrivial
  have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    IsSimpleGroup.isSimpleGroup_of_surjective eA.symm.toMonoidHom eA.symm.surjective
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      apply hcq1
      have h1 : f (piK K ⟨c, hcK⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      exact congrArg Subtype.val h1
  set φ : ↥Kh ≃* ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).symm.trans eA with hφ
  have hKh60 : Nat.card Kh = 60 := by rw [Nat.card_congr φ.toEquiv, A5F.card_A5]
  have hKhsub : (Kh.subgroupOf ⊤).IsSubnormal :=
    Id2519.subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hKhc)
  have hEsyl : IsSylowTwoOf (Th ⊓ Kh) Kh := E6.isSylowTwoOf_inf_of_subnormal' hThS le_top hKhsub
  have hE4 : Nat.card ↥(Th ⊓ Kh) = 4 := by
    obtain ⟨k, hk⟩ := hEsyl.2.1.exists_card_eq
    have hcm := ((Th ⊓ Kh).subgroupOf Kh).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsyl.1).toEquiv, hk, hKh60] at hcm
    exact hk.trans (card_eq_four hcm hEsyl.2.2)
  have hmax : ∀ F : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), F ≤ Kh → IsPGroup 2 F →
      Th ⊓ Kh ≤ F → F = Th ⊓ Kh := by
    intro F hFK hF2 hEF
    symm
    apply Subgroup.eq_of_le_of_card_ge hEF
    rw [hE4]
    obtain ⟨k, hk⟩ := hF2.exists_card_eq
    have hdvd : Nat.card F ∣ 60 := by
      rw [← hKh60]
      exact Subgroup.card_dvd_of_le hFK
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at h8
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hKBcomm : ∀ a ∈ Kh, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hBorel : ∀ e ∈ Th ⊓ Kh, ∃ i : ℕ, ∃ e' ∈ Th ⊓ Kh,
      e * ρ ⟨c, hcH⟩ = ρ ⟨c, hcH⟩ ^ i * e' := by
    rintro e ⟨⟨x, hxT, rfl⟩, heK⟩
    obtain ⟨y, hyP, s₁, hs₁T, hxy⟩ := hmul (x : G) hxT c hcP
    have hy : y ∈ (PK : Set G) * (conjByElt t PK : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right PK (conjByElt t PK)
        ((inf_le_left : PK ≤ P).trans (le_normalizer_of_comm hPab hPKtP)), ← hPdec]
      exact hyP
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hy
    obtain ⟨i, -, rfl⟩ := hpow y₁ hy₁
    have hy₂K : y₂ ∈ conjByElt t K := Subgroup.map_mono inf_le_right hy₂
    have hy₂H : y₂ ∈ H := by
      have h1 := mem_conjByElt.mp hy₂K
      have h2 : y₂ = t * (t⁻¹ * y₂ * t) * t⁻¹ := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem htH (hKH h1)) (H.inv_mem htH)
    have hs₁H : s₁ ∈ H := hTH hs₁T
    have hxyH : x * ⟨c, hcH⟩ = (⟨c, hcH⟩ : ↥H) ^ i * ⟨y₂, hy₂H⟩ * ⟨s₁, hs₁H⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
      exact hxy
    have hxyq := congrArg ρ hxyH
    simp only [map_mul, map_pow] at hxyq
    obtain ⟨a, ha⟩ : ∃ a, a = (ρ ⟨c, hcH⟩ ^ i)⁻¹ * ρ x * ρ ⟨c, hcH⟩ := ⟨_, rfl⟩
    have haK : a ∈ Kh := by
      rw [ha]
      exact Kh.mul_mem (Kh.mul_mem (Kh.inv_mem (Kh.pow_mem hcqK i)) heK) hcqK
    have ha' : a = ρ ⟨y₂, hy₂H⟩ * ρ ⟨s₁, hs₁H⟩ := by
      rw [ha, mul_assoc, hxyq]
      group
    have hyqB : (ρ ⟨y₂, hy₂H⟩)⁻¹ ∈ B :=
      B.inv_mem (by rw [← hKtB]; exact ⟨⟨y₂, hy₂H⟩, hy₂K, rfl⟩)
    have hab : a * (ρ ⟨y₂, hy₂H⟩)⁻¹ ∈ Th := by
      rw [hKBcomm a haK _ hyqB, ha', inv_mul_cancel_left]
      exact ⟨⟨s₁, hs₁H⟩, hs₁T, rfl⟩
    refine ⟨i, a, comp_mem_of_two hcomm hinter inf_le_right inf_le_left hTh2 hmax haK hyqB hab,
      ?_⟩
    rw [ha]
    group
  have hlqN : ρ ⟨ℓ, hℓH⟩ ∈ Subgroup.normalizer ((Th ⊓ Kh : Subgroup _) : Set _) := by
    apply mem_normalizer_of_conj_le
    rintro e ⟨heT, ⟨k, hk, rfl⟩⟩
    rw [hconjQ k hk]
    refine ⟨Th.mul_mem (Th.mul_mem hsqT heT) (Th.inv_mem hsqT), ?_⟩
    refine ⟨(⟨s, hsH⟩ : ↥H) * k * (⟨s, hsH⟩ : ↥H)⁻¹, conj_mem hsK hk, ?_⟩
    simp only [map_mul, map_inv]
  exact a5_false_sub φ inf_le_right hE4 hcqK hlqK hcq1 hcq3 hBorel hlqN hlqc

end CFSG.Quasithin.H13.L139
