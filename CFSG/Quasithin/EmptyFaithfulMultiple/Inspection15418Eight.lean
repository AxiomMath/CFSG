module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Z2D8
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Facts

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

theorem z2s4_centralizer_three : ∀ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4),
    (∀ h : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), h ^ 3 = 1 → g * h = h * g) →
    g = 1 ∨ g = (Multiplicative.ofAdd 1, 1) := by
  decide

theorem z2d8_not_comm : ∃ a b : Multiplicative (ZMod 2) × DihedralGroup 4, a * b ≠ b * a := by
  decide

theorem card_z2d8 : Nat.card (Multiplicative (ZMod 2) × DihedralGroup 4) = 16 := by
  rw [Nat.card_prod, DihedralGroup.nat_card]
  simp

theorem card_le_two_of_forall {X : Type*} [Group X] [Finite X]
    (h : ∀ a b : X, a ≠ 1 → b ≠ 1 → a = b) : Nat.card X ≤ 2 := by
  classical
  have : Fintype X := Fintype.ofFinite X
  by_cases hX : ∃ a : X, a ≠ 1
  · obtain ⟨a, ha⟩ := hX
    have hsub : (Finset.univ : Finset X) ⊆ {1, a} := by
      intro b _
      by_cases hb : b = 1
      · simp [hb]
      · simp [h b a hb ha]
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  · push Not at hX
    have : Subsingleton X := ⟨fun a b => (hX a).trans (hX b).symm⟩
    rw [Nat.card_unique]
    norm_num

end Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem conj_mem_S {u s : G} (hu : u ∈ T) (hs : s ∈ S) : u * s * u⁻¹ ∈ S := by
  have hn : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two d.relIndex_eq_two
  have := hn.conj_mem ⟨s, d.le_T hs⟩ hs ⟨u, hu⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem inv_mul_mem_S {t u : G} (ht : t ∈ T) (htS : t ∉ S) (hu : u ∈ T) (huS : u ∉ S) :
    t⁻¹ * u ∈ S := by
  have h2 : (S.subgroupOf T).index = 2 := d.relIndex_eq_two
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨t, ht⟩ : ↥T)⁻¹) (b := ⟨u, hu⟩)
  have h1 : (⟨t, ht⟩ : ↥T)⁻¹ ∉ S.subgroupOf T := by
    rw [Subgroup.inv_mem_iff]
    exact htS
  have h3 : (⟨u, hu⟩ : ↥T) ∉ S.subgroupOf T := huS
  have := key.mpr (iff_of_false h1 h3)
  simpa [Subgroup.mem_subgroupOf] using this

theorem sq_mem_S {t : G} (ht : t ∈ T) : t ^ 2 ∈ S := by
  have := Subgroup.sq_mem_of_index_two (H := S.subgroupOf T) d.relIndex_eq_two ⟨t, ht⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem false_of_caseEight (hN : ComponentIndexTwo15418) (hc : ¬ CharTwo I)
    (hD : F6.IsHatSym 6 (↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∨ ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      F6.IsL2FieldExtCat p (↥I ⧸ CFSG.pPrimeCore 3 ↥I))
    (eT : ↥((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
      (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ≃*
        Multiplicative (ZMod 2) × DihedralGroup 4)
    (e₁ : ↥((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  obtain ⟨K, hK⟩ := d.exists_isComponent hc
  have hKc := d.isComponent_map_mk hK
  have hidx : (K.map π).index = 2 := by
    refine hN _ ?_ _ hKc
    rcases hD with h | ⟨p, -, -, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨p, h⟩))
  set P := pCoreOf 2 I with hP
  have hPS : P ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf d.isSylowTwoOf
  have hPI : P ≤ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I
  have hIP : I ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  have hPK : ∀ x ∈ P, ∀ k ∈ K, x * (k : G) = k * x := by
    rintro x ⟨x', hx', rfl⟩ k hk
    have hc' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (d.commutator_pPrimeCore_eq_bot hK) hk
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc' x' (F6.pCore_le_pPrimeCore hx'))
  have hXK := d.oTwoUpper_le_of_index_two hK hidx
  have hPX : ∀ x ∈ P, ∀ y ∈ oTwoUpper G₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := hXK hy
    exact hPK x hx k hk
  have hSG₁ : ∀ {c : G} (hc : c ∈ S), π ⟨c, d.S_le hc⟩ ∈ (G₁.subgroupOf I).map π :=
    fun {c} hc => ⟨⟨c, d.S_le hc⟩, d.S_le_G₁ hc, rfl⟩
  have hC : ∀ {c : G} (hc : c ∈ S), (∀ y ∈ oTwoUpper G₁, c * y = y * c) →
      e₁ ⟨π ⟨c, d.S_le hc⟩, hSG₁ hc⟩ = 1 ∨
        e₁ ⟨π ⟨c, d.S_le hc⟩, hSG₁ hc⟩ = (Multiplicative.ofAdd 1, 1) := by
    intro c hc hcy
    refine Insp15418.z2s4_centralizer_three _ fun h h3 => ?_
    obtain ⟨y, rfl⟩ := e₁.surjective h
    rw [← map_mul, ← map_mul]
    congr 1
    have hy3 : (y : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) ^ 3 = 1 := by
      have : y ^ 3 = 1 := by
        rw [← map_pow, map_eq_one_iff e₁ e₁.injective] at h3
        exact h3
      exact congrArg Subtype.val this
    have hyO : (y : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∈ oTwoUpper ((G₁.subgroupOf I).map π) := by
      refine mem_oTwoUpper_of_odd y.2 ?_
      have := orderOf_dvd_of_pow_eq_one hy3
      exact Odd.of_dvd_nat (by decide) this
    rw [oTwoUpper_map] at hyO
    obtain ⟨g, hg, hgy⟩ := hyO
    have hgG : (g : G) ∈ oTwoUpper G₁ := by
      have : (g : G) ∈ (oTwoUpper (G₁.subgroupOf I)).map I.subtype := ⟨g, hg, rfl⟩
      rwa [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le d.G₁_le] at this
    apply Subtype.ext
    change π ⟨c, d.S_le hc⟩ * (y : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) =
      (y : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) * π ⟨c, d.S_le hc⟩
    rw [← hgy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcy _ hgG)
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ S := by
    by_contra h
    push Not at h
    have h1 : S.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr h
    rw [d.relIndex_eq_two] at h1
    omega
  have hcS : ∀ {u s : G}, u ∈ T → s ∈ S → u * s * u⁻¹ ∈ S := fun hu hs => d.conj_mem_S hu hs
  have htXn : t⁻¹ ∈ Subgroup.normalizer (G₁ : Set G) := (Subgroup.normalizer _).inv_mem
    (d.le_normalizer htT)
  set P' := P.map (MulAut.conj t).toMonoidHom with hP'
  have hmemP' : ∀ x, x ∈ P' ↔ t⁻¹ * x * t ∈ P := by
    intro x
    rw [hP', Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hP'S : P' ≤ S := by
    intro x hx
    have h1 := hcS htT (hPS ((hmemP' x).mp hx))
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h1
  have hP'X : ∀ x ∈ P', ∀ y ∈ oTwoUpper G₁, x * y = y * x := by
    intro x hx y hy
    have h1 := hPX _ ((hmemP' x).mp hx) _ (conj_mem_oTwoUpper htXn hy)
    have e1 : x * y = t * ((t⁻¹ * x * t) * (t⁻¹ * y * t⁻¹⁻¹)) * t⁻¹ := by group
    have e2 : y * x = t * ((t⁻¹ * y * t⁻¹⁻¹) * (t⁻¹ * x * t)) * t⁻¹ := by group
    rw [e1, e2, h1]
  have hRT : ∀ u ∈ T, ∀ r ∈ P ⊓ P', u * r * u⁻¹ ∈ P ⊓ P' := by
    have hS : ∀ u ∈ S, ∀ r ∈ P ⊓ P', u * r * u⁻¹ ∈ P ⊓ P' := by
      rintro u hu r ⟨hrP, hrP'⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hIP (d.S_le hu)) r).mp hrP, (hmemP' _).mpr ?_⟩
      have hu' : t⁻¹ * u * t⁻¹⁻¹ ∈ S := hcS ((T.inv_mem htT)) hu
      have h1 := (Subgroup.mem_normalizer_iff.mp (hIP (d.S_le hu')) _).mp ((hmemP' r).mp hrP')
      have e : t⁻¹ * (u * r * u⁻¹) * t =
          (t⁻¹ * u * t⁻¹⁻¹) * (t⁻¹ * r * t) * (t⁻¹ * u * t⁻¹⁻¹)⁻¹ := by group
      rw [e]
      exact h1
    intro u hu r hr
    by_cases huS : u ∈ S
    · exact hS u huS r hr
    · have hs₀ := d.inv_mul_mem_S htT htS hu huS
      obtain ⟨hwP, hwP'⟩ := hS _ hs₀ r hr
      set w := (t⁻¹ * u) * r * (t⁻¹ * u)⁻¹ with hw
      have e : u * r * u⁻¹ = t * w * t⁻¹ := by rw [hw]; group
      rw [e]
      refine ⟨?_, (hmemP' _).mpr ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hIP (d.S_le (d.sq_mem_S htT))) _).mp
          ((hmemP' w).mp hwP')
        have e2 : t * w * t⁻¹ = t ^ 2 * (t⁻¹ * w * t) * (t ^ 2)⁻¹ := by group
        rw [e2]
        exact h1
      · have e2 : t⁻¹ * (t * w * t⁻¹) * t = w := by group
        rw [e2]
        exact hwP
  have hR : P ⊓ P' = ⊥ := by
    by_contra hne
    have hRle : P ⊓ P' ≤ T := inf_le_left.trans (hPS.trans d.le_T)
    set R' := (P ⊓ P').subgroupOf T with hR'
    have hR'n : R'.Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hRT g g.2 n hn
    have hR'ne : R' ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hRle hx⟩ : ↥T) ∈ R' := hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
    have hTp : IsPGroup 2 ↥T := d.isPGroup
    have : Group.IsNilpotent ↥T := hTp.isNilpotent
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hR'ne
    have hZ2 : IsPGroup 2 ↥(R' ⊓ Subgroup.center ↥T) :=
      hTp.to_subgroup _
    obtain ⟨r, hr⟩ : ∃ r : ↥(R' ⊓ Subgroup.center ↥T), orderOf r = 2 := by
      have hnt : Nontrivial ↥(R' ⊓ Subgroup.center ↥T) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
      obtain ⟨k, hk⟩ := hZ2.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
        exact not_subsingleton _ hk.1
      exact exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
    have hr1 : ((r : ↥T) : G) ≠ 1 := by
      intro h
      have : r = 1 := Subtype.ext (Subtype.ext h)
      rw [this, orderOf_one] at hr
      omega
    have hrZ : ((r : ↥T) : G) ∈ Z := by
      refine d.omegaOneCenter_le (Subgroup.subset_closure
        ⟨⟨(r : ↥T).2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩, ?_⟩)
      · have := Subgroup.mem_center_iff.mp r.2.2 ⟨u, hu⟩
        exact congrArg Subtype.val this
      · have h2 : r ^ 2 = 1 := by rw [← hr, pow_orderOf_eq_one]
        have := congrArg (fun x : ↥(R' ⊓ Subgroup.center ↥T) => ((x : ↥T) : G)) h2
        simpa using this
    have hrP : ((r : ↥T) : G) ∈ P := r.2.1.1
    refine d.not_forall_commute hK hrZ hr1 fun k hk => ?_
    exact (hPK _ hrP k hk).symm
  have hker : ∀ x (hx : x ∈ P'), π ⟨x, d.S_le (hP'S hx)⟩ = 1 → x = 1 := by
    intro x hx h1
    have h2 : (⟨x, d.S_le (hP'S hx)⟩ : ↥I) ∈ Open.pCore 2 ↥I := by
      rw [← d.inf_pPrimeCore_eq]
      exact ⟨hP'S hx, (QuotientGroup.eq_one_iff _).mp h1⟩
    have h3 : x ∈ P ⊓ P' := ⟨⟨_, h2, rfl⟩, hx⟩
    rw [hR] at h3
    exact h3
  have hP'1 : ∀ x ∈ P', ∀ y ∈ P', x ≠ 1 → y ≠ 1 → x = y := by
    intro x hx y hy hx1 hy1
    have hval : ∀ z (hz : z ∈ P'), z ≠ 1 →
        e₁ ⟨π ⟨z, d.S_le (hP'S hz)⟩, hSG₁ (hP'S hz)⟩ = (Multiplicative.ofAdd 1, 1) := by
      intro z hz hz1
      rcases hC (hP'S hz) (hP'X z hz) with h | h
      · exfalso
        rw [map_eq_one_iff e₁ e₁.injective] at h
        exact hz1 (hker z hz (congrArg Subtype.val h))
      · exact h
    have he := (hval x hx hx1).trans (hval y hy hy1).symm
    have he' : π ⟨x, d.S_le (hP'S hx)⟩ = π ⟨y, d.S_le (hP'S hy)⟩ :=
      congrArg Subtype.val (e₁.injective he)
    have hxy : x⁻¹ * y ∈ P' := P'.mul_mem (P'.inv_mem hx) hy
    have h1 : π ⟨x⁻¹ * y, d.S_le (hP'S hxy)⟩ = 1 := by
      have e : (⟨x⁻¹ * y, d.S_le (hP'S hxy)⟩ : ↥I) =
          (⟨x, d.S_le (hP'S hx)⟩ : ↥I)⁻¹ * ⟨y, d.S_le (hP'S hy)⟩ := rfl
      rw [e, map_mul, map_inv, he', inv_mul_cancel]
    have := hker _ hxy h1
    rw [inv_mul_eq_one] at this
    exact this
  have hcardP' : Nat.card ↥P' ≤ 2 :=
    Insp15418.card_le_two_of_forall fun a b ha hb => Subtype.ext (hP'1 a a.2 b b.2
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h)))
  have hcardP : Nat.card ↥P ≤ 2 := by
    rwa [hP', Subgroup.card_map_of_injective (MulAut.conj t).injective] at hcardP'
  obtain ⟨A, hAS, hAe, hA32⟩ := d.rank
  set A' := A.subgroupOf I with hA'
  have hA'card : Nat.card ↥A' = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAS.trans d.S_le)).toEquiv, hA32]
    norm_num
  have hker' : π.ker ⊓ A' ≤ Open.pCore 2 ↥I := by
    rintro x ⟨hx1, hx2⟩
    rw [← d.inf_pPrimeCore_eq]
    refine ⟨hAS hx2, ?_⟩
    rw [hπ, QuotientGroup.ker_mk'] at hx1
    exact hx1
  have hcardker : Nat.card ↥(π.ker ⊓ A') ≤ 2 := by
    refine (Subgroup.card_le_of_le hker').trans ?_
    rw [Nat.card_congr ((Open.pCore 2 ↥I).equivMapOfInjective I.subtype
      I.subtype_injective).toEquiv]
    exact hcardP
  have hmul := Subgroup.relIndex_mul_card (H := π.ker) (K := A')
  rw [Subgroup.relIndex_ker, hA'card] at hmul
  have hge : 16 ≤ Nat.card ↥(A'.map π) := by
    have : 32 ≤ Nat.card ↥(A'.map π) * 2 := hmul ▸ Nat.mul_le_mul_left _ hcardker
    omega
  have hAT : A'.map π ≤ (G₁.subgroupOf I).map π ⊓ (G₂.subgroupOf I).map π := by
    rw [d.isGoldschmidtAmalgam.1]
    exact Subgroup.map_mono fun x hx => hAS hx
  have hTcard : Nat.card ↥((G₁.subgroupOf I).map π ⊓ (G₂.subgroupOf I).map π) = 16 := by
    rw [Nat.card_congr eT.toEquiv, Insp15418.card_z2d8]
  have heq : A'.map π = (G₁.subgroupOf I).map π ⊓ (G₂.subgroupOf I).map π :=
    Subgroup.eq_of_le_of_card_ge hAT (by omega)
  obtain ⟨a, b, hab⟩ := Insp15418.z2d8_not_comm
  apply hab
  obtain ⟨x, rfl⟩ := eT.surjective a
  obtain ⟨y, rfl⟩ := eT.surjective b
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hx : (x : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∈ A'.map π := by rw [heq]; exact x.2
  have hy : (y : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∈ A'.map π := by rw [heq]; exact y.2
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  change (x : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) * y = y * x
  rw [← hxx, ← hyy, ← map_mul, ← map_mul]
  congr 1
  have hcomm : (x' : G) * y' = y' * x' :=
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact Subtype.ext hcomm

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple
