module

public import CFSG.Quasithin.Background.RonanE114Good
public import CFSG.Quasithin.Background.E1ElevenLift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
public import CFSG.Quasithin.EmptyFaithful.ModHM24a
public import CFSG.Quasithin.Background.RonanE114Clauses

public section

namespace CFSG.Quasithin.RonanE114.C5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem nParam_top_le_of_quotient_pGroup {Q : Type} [Group Q] [Finite Q] {N : Subgroup Q}
    [N.Normal] (hN : IsPGroup 2 ↥N) {m : ℕ} (hm : 0 < m)
    (h : E1.nParam (⊤ : Subgroup (Q ⧸ N)) ≤ (m : ℕ∞)) :
    E1.nParam (⊤ : Subgroup Q) ≤ (m : ℕ∞) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup Q)
  have hIH : E1.InE m (⊤ : Subgroup (Q ⧸ N)) := (E1.nParam_le_iff hm).mp h
  have hTs : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hNT : N ≤ T := P7.le_of_normal_pGroup inferInstance hN hTs
  have h' := E1.inEFor_of_quotient hIH hT fun Ω hΩ =>
    hNT.trans (le_sup_of_le_right fun x hx =>
      (⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ hx⟩ :
        x ∈ ⊤ ⊓ Subgroup.normalizer ((E1.weakClosure T Ω : Subgroup Q) : Set Q)))
  exact (E1.nParam_le_iff hm).mpr ((E1.inE_iff_inEFor hT).mpr h')

theorem nParam_le_of_levi {H : Type} [Group H] [Finite H] {K T : Subgroup H}
    (hK : K.Normal) (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (f : ↥K →* X) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) {m : ℕ} (hm : 0 < m)
    (hX : ∀ (G' : Type) [Group G'] [Finite G'] (T' : Subgroup G'), quasithinIsSylowTwo T' →
      CFSG.generalizedFitting G' ⊔ T' = ⊤ → Nonempty (↥(CFSG.generalizedFitting G') ≃* X) →
      E1.nParam (⊤ : Subgroup G') ≤ (m : ℕ∞)) :
    E1.nParam (⊤ : Subgroup H) ≤ (m : ℕ∞) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_eq : CFSG.pCore 2 ↥K = f.ker := pCore_two_eq_ker hnab f hf hker
  set Y := CFSG.pCore 2 H with hY
  haveI hYn : Y.Normal := CFSG.pCore_normal
  refine nParam_top_le_of_quotient_pGroup (CFSG.pCore_isPGroup) hm ?_
  set π := QuotientGroup.mk' Y with hπ
  set N := K.map π with hN
  have hNn : N.Normal := Subgroup.Normal.map hK π (QuotientGroup.mk'_surjective Y)
  have hR : (CFSG.pCore 2 ↥K).map K.subtype ≤ Y :=
    le_sSup ⟨P7.pCore_map_subtype_normal hK, CFSG.pCore_isPGroup.map K.subtype⟩
  have hkerπ : (π.subgroupMap K).ker = f.ker := by
    rw [← hker_eq]
    ext k
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hkY : (k : H) ∈ Y := by
        have h1 : π (k : H) = 1 := by simpa using congrArg Subtype.val hk
        exact (QuotientGroup.eq_one_iff (k : H)).mp h1
      have hp : IsPGroup 2 ↥(Y.subgroupOf K) := by
        intro g
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨(g.1 : H), g.2⟩
        exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
      haveI : (Y.subgroupOf K).Normal := Subgroup.Normal.subgroupOf hYn K
      exact (le_sSup ⟨inferInstance, hp⟩ : Y.subgroupOf K ≤ CFSG.pCore 2 ↥K) hkY
    · intro hk
      apply Subtype.ext
      have h1 : π (k : H) = 1 := (QuotientGroup.eq_one_iff (k : H)).mpr (hR ⟨k, hk, rfl⟩)
      simpa using h1
  have hsurj : Function.Surjective (π.subgroupMap K) := MonoidHom.subgroupMap_surjective π K
  let θ : ↥N ≃* X :=
    (QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap K) hsurj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerπ).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))
  haveI : IsSimpleGroup ↥N := θ.isSimpleGroup
  have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨θ.symm a, θ.symm b, fun h => hab ?_⟩
    simpa using congrArg θ h
  have hcen : ∀ x ∈ N, (∀ n ∈ N, n * x = x * n) → x = 1 := by
    intro x hx hc
    have := P7.eq_one_of_commutes hncN (x := (⟨x, hx⟩ : ↥N)) fun n =>
      Subtype.ext (hc n.1 n.2)
    simpa using congrArg Subtype.val this
  have hC := P7.centralizer_map_eq_bot hK hKT hT.2.1 hcen
  have hFN : CFSG.generalizedFitting (H ⧸ Y) = N :=
    CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot N hncN hC
  have hTsyl : IsSylowIn 2 (T.map π) ⊤ :=
    E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective Y)
      (Good.isSylowIn_of_isSylowTwoOf hT)
  have hT'q : quasithinIsSylowTwo (T.map π) := quasithinIsSylowTwo_of_isSylowIn hTsyl
  have hFT' : CFSG.generalizedFitting (H ⧸ Y) ⊔ T.map π = ⊤ := by
    rw [hFN, hN, ← Subgroup.map_sup, hKT, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Y)
  exact hX (H ⧸ Y) (T.map π) hT'q hFT' ⟨(MulEquiv.subgroupCongr hFN).trans θ⟩

section Alt5

open Equiv Equiv.Perm

theorem alt5_nonabelian : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative ↥(alternatingGroup (Fin 5)) := ⟨⟨fun a b => hcomm a b⟩⟩
  have hp := Group.is_simple_iff_prime_card.1 alternatingGroup.isSimpleGroup_five
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hp
  norm_num [Nat.factorial] at hp

theorem commutator_eq_alt5 {R : Subgroup (Perm (Fin 5))} (h : alternatingGroup (Fin 5) ≤ R) :
    ⁅R, R⁆ = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact Commute.commutator_eq (Commute.all _ _)
  · have hperf : ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ = alternatingGroup (Fin 5) :=
      Subgroup.isPerfect_iff.mp
        (CFSG.TwoRankLowerBound.Helpers.perfect_of_nonabelian_simple
          (↥(alternatingGroup (Fin 5))) alt5_nonabelian)
    calc alternatingGroup (Fin 5) = ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ :=
          hperf.symm
      _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono h h

end Alt5

theorem hX_alt5 (G' : Type) [Group G'] [Finite G'] (T' : Subgroup G')
    (hT : quasithinIsSylowTwo T') (hFT : CFSG.generalizedFitting G' ⊔ T' = ⊤)
    (h : Nonempty (↥(CFSG.generalizedFitting G') ≃* ↥(alternatingGroup (Fin 5)))) :
    E1.nParam (⊤ : Subgroup G') ≤ ((2 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := h
  haveI := alternatingGroup.isSimpleGroup_five
  have hL : IsPSL 2 2 2 ↥(CFSG.generalizedFitting G') :=
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨e⟩
  have hs : IsSimpleGroup ↥(CFSG.generalizedFitting G') := e.isSimpleGroup
  exact Vol2.Ch11.SecE3.nParam_le_of_isPSL22 hL hs hT hFT

theorem hX_sl3
    (G' : Type) [Group G'] [Finite G'] (T' : Subgroup G')
    (_ : quasithinIsSylowTwo T') (_ : CFSG.generalizedFitting G' ⊔ T' = ⊤)
    (h : Nonempty (↥(CFSG.generalizedFitting G') ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    E1.nParam (⊤ : Subgroup G') ≤ ((1 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := h
  have hpsl : IsPSL 3 2 1 ↥(CFSG.generalizedFitting G') :=
    IsPSL.of_mulEquiv e.symm P7.isPSL_sl3_two
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := E22L2.nParam_le_one_of_psl2_prime (G := G') (p := 7) (Or.inr rfl) le_rfl
    (statedClassicalModel_psl_two_seven_of_three_two hpsl)
  exact_mod_cast this

theorem range_inclusion_eq {G : Type*} [Group G] {K Q : Subgroup G} (h : K ≤ Q) :
    (Subgroup.inclusion h).range = K.subgroupOf Q := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact k.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

theorem nParam_le_one_of_levi3
    {H : Type} [Group H] [Finite H] {K T : Subgroup H}
    (hK : K.Normal) (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤)
    (f : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : E1.nParam (⊤ : Subgroup H) ≤ ((1 : ℕ) : ℕ∞) := by
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  haveI := sl_isSimple_of_card_two hK2 (m := 3) le_rfl
  exact nParam_le_of_levi hK hT hKT (sl_nonabelian_of_card_two hK2 (m := 3) le_rfl) f hf hker
    one_pos hX_sl3

open Equiv Equiv.Perm in
theorem nParam_le_two_of_levi5 {H : Type} [Group H] [Finite H]
    {Q T : Subgroup H} (hQ : Q.Normal) (hT : IsSylowTwoOf T ⊤) (hQT : Q ⊔ T = ⊤)
    (ρ : ↥Q →* Perm (Fin 5)) (hker : IsPGroup 2 ρ.ker)
    (hA : alternatingGroup (Fin 5) ≤ ρ.range) : E1.nParam (⊤ : Subgroup H) ≤ ((2 : ℕ) : ℕ∞) := by
  classical
  haveI := hQ
  set K : Subgroup H := ⁅Q, Q⁆ with hKdef
  haveI hKn : K.Normal := Subgroup.commutator_normal Q Q
  have hKQ : K ≤ Q := Subgroup.commutator_le_left Q Q
  have hKsub : K.subgroupOf Q = commutator ↥Q := by
    rw [hKdef, ← Subgroup.map_subtype_commutator]
    ext x
    simp [Subgroup.mem_subgroupOf]
  let fK : ↥K →* Perm (Fin 5) := ρ.comp (Subgroup.inclusion hKQ)
  have hrange : fK.range = alternatingGroup (Fin 5) := by
    rw [MonoidHom.range_comp, range_inclusion_eq hKQ, hKsub, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact commutator_eq_alt5 hA
  let f : ↥K →* ↥(alternatingGroup (Fin 5)) :=
    fK.codRestrict _ (fun k => by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨k, rfl⟩)
  have hf : Function.Surjective f := fun a => by
    have ha : a.1 ∈ fK.range := by rw [hrange]; exact a.2
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, Subtype.ext hk⟩
  have hkerf : IsPGroup 2 f.ker := by
    intro x
    have hx : ρ (Subgroup.inclusion hKQ x.1) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      simpa [f, fK] using this
    obtain ⟨n, hn⟩ := hker ⟨Subgroup.inclusion hKQ x.1, hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥ρ.ker => ((y : ↥Q) : H)) hn
    simpa using this
  have hKT : K ⊔ T = ⊤ := by
    have hSQ : IsSylowTwoOf (T ⊓ Q) Q :=
      B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hQ])
    set S : Subgroup H := T ⊓ Q with hSdef
    have hS' : IsSylowTwoOf (S.subgroupOf Q) ⊤ :=
      K1.isSylowTwoOf_top_iff.mpr ⟨hSQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSQ.1).symm,
        hSQ.2.2⟩
    let σ : ↥Q →* ℤˣ := Equiv.Perm.sign.comp ρ
    have hσidx : σ.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      have h1 : Nat.card σ.range ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
      rwa [h2] at h1
    have hZ : σ.ker ⊔ S.subgroupOf Q = ⊤ := by
      have h1 : (σ.ker ⊔ S.subgroupOf Q).index ∣ σ.ker.index :=
        Subgroup.index_dvd_of_le le_sup_left
      have h2 : (σ.ker ⊔ S.subgroupOf Q).index ∣ (S.subgroupOf Q).index :=
        Subgroup.index_dvd_of_le le_sup_right
      have h3 : ¬ 2 ∣ (S.subgroupOf Q).index := (K1.isSylowTwoOf_top_iff.mp hS').2
      have h4 : (σ.ker ⊔ S.subgroupOf Q).index ∣ 2 := h1.trans hσidx
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exact Subgroup.index_eq_one.mp h
      · exact absurd (h ▸ h2) h3
    have hkerS : ρ.ker ≤ S.subgroupOf Q := P7.le_of_normal_pGroup inferInstance hker hS'
    refine eq_top_iff.mpr ?_
    rw [← hQT]
    refine sup_le ?_ le_sup_right
    intro q hq
    have hqZ : (⟨q, hq⟩ : ↥Q) ∈ σ.ker ⊔ S.subgroupOf Q := by rw [hZ]; trivial
    obtain ⟨a, ha, s, hs, has⟩ := Subgroup.mem_sup_of_normal_left.mp hqZ
    have haA : ρ a ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact MonoidHom.mem_ker.mp ha
    have hfa : ρ a ∈ fK.range := by rw [hrange]; exact haA
    obtain ⟨k, hk⟩ := hfa
    have hrk : a * (Subgroup.inclusion hKQ k)⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : ρ (Subgroup.inclusion hKQ k) = ρ a := hk
      rw [this, mul_inv_cancel]
    have hrkS : a * (Subgroup.inclusion hKQ k)⁻¹ ∈ S.subgroupOf Q := hkerS hrk
    have hq' : q = ((a * (Subgroup.inclusion hKQ k)⁻¹ : ↥Q) : H) * (k : H) * (s : H) := by
      have h1 : ((a * s : ↥Q) : H) = q := congrArg Subtype.val has
      rw [← h1]
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hq']
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left k.2)) ?_
    · exact Subgroup.mem_sup_right (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hrkS)).1
    · exact Subgroup.mem_sup_right (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)).1
  haveI := alternatingGroup.isSimpleGroup_five
  exact nParam_le_of_levi hKn hT hKT alt5_nonabelian f hf hkerf two_pos
    (fun G' _ _ T' hT' hFT h => hX_alt5 G' T' hT' hFT h)

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem typeLevel_of_ambient {Q T : Subgroup G} (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hT : IsSylowTwoOf T (Q ⊔ T)) :
    (Q.subgroupOf (Q ⊔ T)).Normal ∧ IsSylowTwoOf (T.subgroupOf (Q ⊔ T)) ⊤ ∧
      Q.subgroupOf (Q ⊔ T) ⊔ T.subgroupOf (Q ⊔ T) = ⊤ := by
  have hKD : Q ≤ Q ⊔ T := le_sup_left
  have hTD : T ≤ Q ⊔ T := le_sup_right
  refine ⟨?_, ?_, ?_⟩
  · have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTQ
    rwa [sup_comm] at this
  · exact K1.isSylowTwoOf_top_iff.mpr
      ⟨hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm, hT.2.2⟩
  · rw [← Subgroup.subgroupOf_sup hKD hTD, Subgroup.subgroupOf_self]

theorem isPGroup_ker_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C] (e : A ≃* B)
    (f : B →* C) (hker : IsPGroup 2 f.ker) : IsPGroup 2 (f.comp e.toMonoidHom).ker := by
  intro x
  have hx : f (e x.1) = 1 := MonoidHom.mem_ker.mp x.2
  obtain ⟨n, hn⟩ := hker ⟨e x.1, MonoidHom.mem_ker.mpr hx⟩
  refine ⟨n, ?_⟩
  have h1 : (e x.1) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : x.1 ^ 2 ^ n = 1 := by
    apply e.injective
    rw [map_pow, h1, map_one]
  exact Subtype.ext h2

theorem nParam_sup_le_one_of_levi3
    {Q T : Subgroup G} (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hT : IsSylowTwoOf T (Q ⊔ T))
    (f : ↥Q →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : E1.nParam (Q ⊔ T) ≤ ((1 : ℕ) : ℕ∞) := by
  rw [E1.nParam_subgroupOf]
  obtain ⟨hn, hTD, hQT⟩ := typeLevel_of_ambient hTQ hT
  let e : ↥(Q.subgroupOf (Q ⊔ T)) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe le_sup_left
  exact nParam_le_one_of_levi3 hn hTD hQT (f.comp e.toMonoidHom) (hf.comp e.surjective)
    (isPGroup_ker_comp_equiv e f hker)

theorem nParam_sup_le_two_of_levi5 {Q T : Subgroup G}
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hT : IsSylowTwoOf T (Q ⊔ T))
    (ρ : ↥Q →* Equiv.Perm (Fin 5)) (hker : IsPGroup 2 ρ.ker)
    (hA : alternatingGroup (Fin 5) ≤ ρ.range) : E1.nParam (Q ⊔ T) ≤ ((2 : ℕ) : ℕ∞) := by
  rw [E1.nParam_subgroupOf]
  obtain ⟨hn, hTD, hQT⟩ := typeLevel_of_ambient hTQ hT
  let e : ↥(Q.subgroupOf (Q ⊔ T)) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe le_sup_left
  refine nParam_le_two_of_levi5 hn hTD hQT (ρ.comp e.toMonoidHom) (isPGroup_ker_comp_equiv e ρ hker) ?_
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  exact hA

theorem nParam_sup_le_one_of_solvable {Q T : Subgroup G}
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hT : IsPGroup 2 ↥T) (hs : Group.IsSolvable ↥Q) :
    E1.nParam (Q ⊔ T) ≤ ((1 : ℕ) : ℕ∞) :=
  E1.solvable_nParam_le_one (isSolvable_sup_of_normalizes hT hTQ hs)

end Ambient

inductive GoodSub {G : Type} [Group G] (T : Subgroup G) : Subgroup G → Prop
  | solvable {Q : Subgroup G} : T ≤ Subgroup.normalizer (Q : Set G) → Group.IsSolvable ↥Q →
      GoodSub T Q
  | levi3 {Q : Subgroup G} : T ≤ Subgroup.normalizer (Q : Set G) →
      (∃ f : ↥Q →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Function.Surjective f ∧ IsPGroup 2 f.ker) → GoodSub T Q
  | levi5 {Q : Subgroup G} : T ≤ Subgroup.normalizer (Q : Set G) →
      (∃ ρ : ↥Q →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range) →
      GoodSub T Q
  | join {A B : Subgroup G} : GoodSub T A → GoodSub T B → GoodSub T (A ⊔ B)

theorem GoodSub.nParam_le
    {G : Type} [Group G] [Finite G] {T Q : Subgroup G}
    (h : GoodSub T Q) : IsSylowTwoOf T (Q ⊔ T) → E1.nParam (Q ⊔ T) ≤ ((2 : ℕ) : ℕ∞) := by
  induction h with
  | solvable hn hs =>
    intro hT
    exact (nParam_sup_le_one_of_solvable hn hT.2.1 hs).trans (by norm_num)
  | levi3 hn hl =>
    intro hT
    obtain ⟨f, hf, hk⟩ := hl
    exact (nParam_sup_le_one_of_levi3 hn hT f hf hk).trans (by norm_num)
  | levi5 hn hl =>
    intro hT
    obtain ⟨ρ, hk, hA⟩ := hl
    exact nParam_sup_le_two_of_levi5 hn hT ρ hk hA
  | @join A B _ _ ihA ihB =>
    intro hT
    have hTA : IsSylowTwoOf T (A ⊔ T) :=
      B6.isSylowTwoOf_mono hT le_sup_right (sup_le_sup_right le_sup_left T)
    have hTB : IsSylowTwoOf T (B ⊔ T) :=
      B6.isSylowTwoOf_mono hT le_sup_right (sup_le_sup_right le_sup_right T)
    refine E1.nParam_le_of_generated (Δ := {A ⊔ T, B ⊔ T}) (Good.isSylowIn_of_isSylowTwoOf hT)
      ?_ ?_ ?_
    · rw [iSup_insert, iSup_singleton]
      exact (sup_sup_distrib_right A B T).symm
    · intro D hD
      rcases hD with rfl | rfl <;> exact le_sup_right
    · intro D hD
      rcases hD with rfl | rfl
      · exact ihA hTA
      · exact ihB hTB

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
inductive GoodGam {Γ : Type} [Group Γ] (𝒜 : Set (MulAut Γ)) : Subgroup Γ → Prop
  | solvable {P : Subgroup Γ} : (∀ α ∈ 𝒜, P.map α.toMonoidHom = P) → Group.IsSolvable ↥P →
      GoodGam 𝒜 P
  | levi3 {P : Subgroup Γ} : (∀ α ∈ 𝒜, P.map α.toMonoidHom = P) →
      (∃ f : ↥P →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Function.Surjective f ∧ IsPGroup 2 f.ker) → GoodGam 𝒜 P
  | levi5 {P : Subgroup Γ} : (∀ α ∈ 𝒜, P.map α.toMonoidHom = P) →
      (∃ ρ : ↥P →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range) →
      GoodGam 𝒜 P
  | join {A B : Subgroup Γ} : GoodGam 𝒜 A → GoodGam 𝒜 B → GoodGam 𝒜 (A ⊔ B)

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem GoodGam.toGoodSub {Γ : Type} [Group Γ] [Finite Γ] {H : Type} [Group H] [Finite H]
    {K T : Subgroup H} (hK : K.Normal) (e' : ↥K ≃* Γ) {𝒜 : Set (MulAut Γ)}
    (h𝒜 : ∀ t ∈ T, autK e' t ∈ 𝒜) {P : Subgroup Γ} (h : GoodGam 𝒜 P) :
    GoodSub T ((P.map e'.symm.toMonoidHom).map K.subtype) := by
  haveI := hK
  induction h with
  | @solvable P hinv hs =>
    exact GoodSub.solvable (fun t ht => mem_normalizer_pull e' (hinv _ (h𝒜 t ht)))
      (Good.isSolvable_pull e' hs)
  | @levi3 P hinv hl =>
    obtain ⟨f, hf, hk⟩ := hl
    let ι : ↥P ≃* ↥((P.map e'.symm.toMonoidHom).map K.subtype) :=
      (P.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
        ((P.map e'.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)
    exact GoodSub.levi3 (fun t ht => mem_normalizer_pull e' (hinv _ (h𝒜 t ht)))
      ⟨f.comp ι.symm.toMonoidHom, hf.comp ι.symm.surjective, isPGroup_ker_comp_equiv ι.symm f hk⟩
  | @levi5 P hinv hl =>
    obtain ⟨ρ, hk, hA⟩ := hl
    let ι : ↥P ≃* ↥((P.map e'.symm.toMonoidHom).map K.subtype) :=
      (P.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
        ((P.map e'.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)
    refine GoodSub.levi5 (fun t ht => mem_normalizer_pull e' (hinv _ (h𝒜 t ht)))
      ⟨ρ.comp ι.symm.toMonoidHom, isPGroup_ker_comp_equiv ι.symm ρ hk, ?_⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hA
  | join hA hB ihA ihB =>
    rw [pull_sup]
    exact GoodSub.join ihA ihB

section Builders

variable {Γ : Type} [Group Γ] {U P : Subgroup Γ}

open CFSG.Quasithin.E2P.SporB in
theorem inv_of_unique (hUP : U ≤ P)
    (hu : ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card P → Z = P) (𝒜 : Set (MulAut Γ))
    (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : ∀ α ∈ 𝒜, P.map α.toMonoidHom = P :=
  fun α hα => map_eq_of_unique_card hUP hu α (h𝒜 α hα)

theorem map_eq_of_unique_pred (α : MulAut Γ) (hα : U.map α.toMonoidHom = U)
    (Pred : Subgroup Γ → Prop) (hP : Pred P) (hUP : U ≤ P)
    (hpred : ∀ Z, Pred Z → Pred (Z.map α.toMonoidHom))
    (hu : ∀ Z : Subgroup Γ, U ≤ Z → Pred Z → Nat.card Z = Nat.card P → Z = P) :
    P.map α.toMonoidHom = P := by
  refine hu _ ?_ (hpred _ hP) (Subgroup.card_map_of_injective α.injective)
  rw [← hα]
  exact Subgroup.map_mono hUP

theorem map_le_of_inv {A B : Subgroup Γ} (α : MulAut Γ) (hB : B.map α.toMonoidHom = B)
    (hA : A ≤ B) : A.map α.toMonoidHom ≤ B := by
  calc A.map α.toMonoidHom ≤ B.map α.toMonoidHom := Subgroup.map_mono hA
    _ = B := hB

theorem map_le_iff_of_eq (α : MulAut Γ) {A B : Subgroup Γ} (hB : B.map α.toMonoidHom = B) :
    A.map α.toMonoidHom ≤ B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have : α x ∈ B := h ⟨x, hx, rfl⟩
    have h2 : α x ∈ B.map α.toMonoidHom := by rw [hB]; exact this
    obtain ⟨y, hy, hyx⟩ := h2
    have : y = x := α.injective hyx
    exact this ▸ hy
  · intro h
    rw [← hB]
    exact Subgroup.map_mono h

theorem goodGam_solvable_of_unique (hUP : U ≤ P)
    (hu : ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card P → Z = P) (hs : Group.IsSolvable ↥P)
    (𝒜 : Set (MulAut Γ)) (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : GoodGam 𝒜 P :=
  GoodGam.solvable (inv_of_unique hUP hu 𝒜 h𝒜) hs

theorem goodGam_levi3_of_unique (hUP : U ≤ P)
    (hu : ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card P → Z = P)
    (hl : ∃ f : ↥P →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ IsPGroup 2 f.ker)
    (𝒜 : Set (MulAut Γ)) (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : GoodGam 𝒜 P :=
  GoodGam.levi3 (inv_of_unique hUP hu 𝒜 h𝒜) hl

theorem goodGam_levi5_of_unique (hUP : U ≤ P)
    (hu : ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card P → Z = P)
    (hl : ∃ ρ : ↥P →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range)
    (𝒜 : Set (MulAut Γ)) (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : GoodGam 𝒜 P :=
  GoodGam.levi5 (inv_of_unique hUP hu 𝒜 h𝒜) hl

end Builders

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem nParam_le_two_of_goodPair
    {Γ : Type} [Group Γ] [Finite Γ] {U P₀ P₁ : Subgroup Γ}
    (hU : IsSylowTwoOf U ⊤) (hgen : P₀ ⊔ P₁ = ⊤)
    (hgood : ∀ 𝒜 : Set (MulAut Γ), (∀ α ∈ 𝒜, U.map α.toMonoidHom = U) →
      GoodGam 𝒜 P₀ ∧ GoodGam 𝒜 P₁)
    {H : Type} [Group H] [Finite H] {K T : Subgroup H} (hK : K.Normal) (e₀ : ↥K ≃* Γ)
    (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup H) ≤ ((2 : ℕ) : ℕ∞) := by
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e₀ hSK hU
  have hα : ∀ t ∈ T, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (le_normalizer_inf hK ht)
  set 𝒜 : Set (MulAut Γ) := (fun t => autK e' t) '' (T : Set H) with h𝒜
  obtain ⟨g0, g1⟩ := hgood 𝒜 (by rintro _ ⟨t, ht, rfl⟩; exact hα t ht)
  have hmem : ∀ t ∈ T, autK e' t ∈ 𝒜 := fun t ht => ⟨t, ht, rfl⟩
  have hT' : IsSylowIn 2 T ⊤ := Good.isSylowIn_of_isSylowTwoOf hT
  set Q₀ := (P₀.map e'.symm.toMonoidHom).map K.subtype with hQ₀
  set Q₁ := (P₁.map e'.symm.toMonoidHom).map K.subtype with hQ₁
  have hQ : Q₀ ⊔ Q₁ = K := by rw [hQ₀, hQ₁, ← pull_sup, hgen, pull_top]
  have h0 : E1.nParam (Q₀ ⊔ T) ≤ ((2 : ℕ) : ℕ∞) :=
    (g0.toGoodSub hK e' hmem).nParam_le (B6.isSylowTwoOf_mono hT le_sup_right le_top)
  have h1 : E1.nParam (Q₁ ⊔ T) ≤ ((2 : ℕ) : ℕ∞) :=
    (g1.toGoodSub hK e' hmem).nParam_le (B6.isSylowTwoOf_mono hT le_sup_right le_top)
  refine E1.nParam_le_of_generated (Δ := {Q₀ ⊔ T, Q₁ ⊔ T}) hT' ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    refine eq_top_iff.mpr ?_
    rw [← hKT]
    have hK' : K ≤ (Q₀ ⊔ T) ⊔ (Q₁ ⊔ T) := by
      rw [← hQ]
      exact sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left)
    exact sup_le hK' (le_sup_of_le_left le_sup_right)
  · intro D hD
    rcases hD with rfl | rfl <;> exact le_sup_right
  · intro D hD
    rcases hD with rfl | rfl
    · exact h0
    · exact h1

section Inner

variable {Γ : Type} [Group Γ]

@[expose] def innerU (U : Subgroup Γ) : Set (MulAut Γ) := {α | ∃ g ∈ U, α = MulAut.conj g}

theorem inv_of_inner {U P : Subgroup Γ} (hUP : U ≤ P) :
    ∀ α ∈ innerU U, P.map α.toMonoidHom = P := by
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hUP hg))

theorem centralizer_fStar_eq_bot {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a) :
    Subgroup.centralizer ((CFSG.generalizedFitting G : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxF : x ∈ CFSG.generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hx
  have h1 : (⟨x, hxF⟩ : ↥(CFSG.generalizedFitting G)) = 1 :=
    P7.eq_one_of_commutes hnab fun n => Subtype.ext (by
      have := Subgroup.mem_centralizer_iff.mp hx n.1 n.2
      exact this)
  have : x = 1 := congrArg Subtype.val h1
  exact this ▸ Subgroup.one_mem _

end Inner

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem nParam_le_two_of_goodPair_inner
    {Γ : Type} [Group Γ] [Finite Γ] {U P₀ P₁ : Subgroup Γ}
    (hU : IsSylowTwoOf U ⊤) (hgen : P₀ ⊔ P₁ = ⊤)
    (hin : ∀ α : MulAut Γ, ∃ g : Γ, α = MulAut.conj g)
    (hgood : GoodGam (innerU U) P₀ ∧ GoodGam (innerU U) P₁)
    {H : Type} [Group H] [Finite H] {K T : Subgroup H} (hK : K.Normal) (e₀ : ↥K ≃* Γ)
    (hC : Subgroup.centralizer (K : Set H) = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup H) ≤ ((2 : ℕ) : ℕ∞) := by
  have hHK : ∀ h : H, h ∈ K := by
    intro h
    obtain ⟨g, hg⟩ := hin (autK e₀ h)
    set k : ↥K := e₀.symm g with hk
    have key : ∀ y ∈ K, h * y * h⁻¹ = (k : H) * y * (k : H)⁻¹ := by
      intro y hy
      have h1 : autK e₀ h (e₀ ⟨y, hy⟩) = MulAut.conj g (e₀ ⟨y, hy⟩) := by rw [hg]
      have h2 := congrArg (fun c => (e₀.symm c : H)) h1
      simpa [autK_apply, hk] using h2
    have hc : (k : H)⁻¹ * h ∈ Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := key y hy
      calc y * ((k : H)⁻¹ * h) = (k : H)⁻¹ * ((k : H) * y * (k : H)⁻¹) * h := by group
        _ = (k : H)⁻¹ * (h * y * h⁻¹) * h := by rw [this]
        _ = (k : H)⁻¹ * h * y := by group
    rw [hC, Subgroup.mem_bot] at hc
    have : h = k := by
      calc h = (k : H) * ((k : H)⁻¹ * h) := by group
        _ = k := by rw [hc, mul_one]
    rw [this]
    exact k.2
  have hTK : T ≤ K := fun x _ => hHK x
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e₀ hSK hU
  have hmem : ∀ t ∈ T, autK e' t ∈ innerU U := by
    intro t ht
    refine ⟨e' ⟨t, hTK ht⟩, ?_, ?_⟩
    · rw [← he']
      exact ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.mpr ⟨ht, hTK ht⟩, rfl⟩
    · ext c
      rw [MulAut.conj_apply, autK_apply]
      apply e'.symm.injective
      rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      apply Subtype.ext
      simp
  obtain ⟨g0, g1⟩ := hgood
  have hT' : IsSylowIn 2 T ⊤ := Good.isSylowIn_of_isSylowTwoOf hT
  set Q₀ := (P₀.map e'.symm.toMonoidHom).map K.subtype with hQ₀
  set Q₁ := (P₁.map e'.symm.toMonoidHom).map K.subtype with hQ₁
  have hQ : Q₀ ⊔ Q₁ = K := by rw [hQ₀, hQ₁, ← pull_sup, hgen, pull_top]
  have h0 : E1.nParam (Q₀ ⊔ T) ≤ ((2 : ℕ) : ℕ∞) :=
    (g0.toGoodSub hK e' hmem).nParam_le (B6.isSylowTwoOf_mono hT le_sup_right le_top)
  have h1 : E1.nParam (Q₁ ⊔ T) ≤ ((2 : ℕ) : ℕ∞) :=
    (g1.toGoodSub hK e' hmem).nParam_le (B6.isSylowTwoOf_mono hT le_sup_right le_top)
  refine E1.nParam_le_of_generated (Δ := {Q₀ ⊔ T, Q₁ ⊔ T}) hT' ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    refine eq_top_iff.mpr ?_
    rw [← hKT]
    have hK' : K ≤ (Q₀ ⊔ T) ⊔ (Q₁ ⊔ T) := by
      rw [← hQ]
      exact sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left)
    exact sup_le hK' (le_sup_of_le_left le_sup_right)
  · intro D hD
    rcases hD with rfl | rfl <;> exact le_sup_right
  · intro D hD
    rcases hD with rfl | rfl
    · exact h0
    · exact h1

section Helpers

open Equiv Equiv.Perm

theorem isSolvable_of_card_dvd_120 {K : Type} [Group K] [Finite K] (hd : Nat.card K ∣ 120)
    (hlt : Nat.card K < 60) : Group.IsSolvable K := by
  have key : ∀ n < 60, n ∣ 120 → n ∣ 60 ∨ n = 8 ∨ n = 24 ∨ n = 40 := by decide
  rcases key _ hlt hd with h | h | h | h
  · exact A312J2.isSolvable_of_card_dvd_sixty h hlt
  · exact A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3)
      (b := 0) (by rw [h]; norm_num)
  · exact A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 3)
      (b := 1) (by rw [h]; norm_num)
  · exact A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_five (by norm_num) (a := 3)
      (b := 1) (by rw [h]; norm_num)

theorem alt5_le_of_not_isSolvable {R : Subgroup (Perm (Fin 5))} (hns : ¬ Group.IsSolvable ↥R) :
    alternatingGroup (Fin 5) ≤ R := by
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  have h120 : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h1 : R.index * Nat.card ↥R = 120 := by
    rw [← h120]
    exact Subgroup.index_mul_card R
  by_contra hidx
  push Not at hidx
  have hlt : Nat.card ↥R < 60 := by
    by_contra hge
    push Not at hge
    nlinarith
  have hdvd : Nat.card ↥R ∣ 120 := ⟨R.index, by rw [mul_comm]; exact h1.symm⟩
  exact hns (isSolvable_of_card_dvd_120 hdvd hlt)

theorem levi5_of_index_five {Z : Type} [Group Z] [Finite Z] (hns : ¬ Group.IsSolvable Z)
    {Z' : Subgroup Z} {e : ℕ} (hcard : Nat.card Z = 2 ^ e * 3 * 5)
    (hcard' : Nat.card Z' = 2 ^ e * 3) :
    ∃ ρ : Z →* Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  obtain ⟨ρ, hker, -⟩ := A312Ru.exists_hom_perm hns (Y' := Z') (e := e) (p := 5) (by norm_num)
    (by norm_num) hcard hcard'
  refine ⟨ρ, by rw [hker]; exact CFSG.pCore_isPGroup, alt5_le_of_not_isSolvable fun hGs => ?_⟩
  apply hns
  have h2 : IsPGroup 2 ρ.ker := by rw [hker]; exact CFSG.pCore_isPGroup
  have : Group.IsNilpotent ρ.ker := h2.isNilpotent
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem levi3_of_index_seven {Z : Type} [Group Z] [Finite Z] (hns : ¬ Group.IsSolvable Z)
    {Z' : Subgroup Z} {e : ℕ} (hcard : Nat.card Z = 2 ^ e * 3 * 7)
    (hcard' : Nat.card Z' = 2 ^ e * 3) (hO2 : Nat.card (CFSG.pCore 2 Z) * 8 = 2 ^ e) :
    ∃ f : Z →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  classical
  obtain ⟨ρ, hker, htr⟩ := A312Ru.exists_hom_perm hns (Y' := Z') (e := e) (p := 7)
    (by norm_num) (by norm_num) hcard hcard'
  have hcardR : Nat.card ρ.range = 168 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker, hcard] at h1
    have h2 : 0 < Nat.card (CFSG.pCore 2 Z) := Nat.card_pos
    have h3 : 2 ^ e * 3 * 7 = Nat.card ρ.range * Nat.card (CFSG.pCore 2 Z) := h1
    have h4 : 2 ^ e = Nat.card (CFSG.pCore 2 Z) * 8 := hO2.symm
    rw [h4] at h3
    have : Nat.card ρ.range * Nat.card (CFSG.pCore 2 Z) = 168 * Nat.card (CFSG.pCore 2 Z) := by
      rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_right h2 this
  have h2 : IsPGroup 2 ρ.ker := by rw [hker]; exact CFSG.pCore_isPGroup
  have hnsR : ¬ Group.IsSolvable ρ.range := fun hGs => by
    apply hns
    have : Group.IsNilpotent ρ.ker := h2.isNilpotent
    exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hsimple : IsSimpleGroup ρ.range := A312Ru.isSimpleGroup_of_card_168 hcardR hnsR
  have hpsl : IsPSL 3 2 1 ρ.range :=
    A312Ru.isPSL_three_two_of_perm_seven hcardR ρ.range.subtype (Subgroup.subtype_injective _)
      (fun i j => by
        obtain ⟨y, hy⟩ := htr i j
        exact ⟨⟨ρ y, y, rfl⟩, hy⟩)
  obtain ⟨φ⟩ := P7.exists_mulEquiv_sl3_of_isPSL hpsl
  refine ⟨φ.toMonoidHom.comp ρ.rangeRestrict,
    φ.surjective.comp (MonoidHom.rangeRestrict_surjective ρ), ?_⟩
  have hk : (φ.toMonoidHom.comp ρ.rangeRestrict).ker = ρ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff φ φ.injective, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
    rfl
  rw [hk]
  exact h2

end Helpers

theorem levi5_of_quotient {Z : Type} [Group Z] {V : Subgroup Z} [V.Normal] (hV : IsPGroup 2 ↥V)
    (e : (Z ⧸ V) ≃* ↥(alternatingGroup (Fin 5))) :
    ∃ ρ : Z →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  let ρ : Z →* Equiv.Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' V))
  have hρ : ∀ z : Z, ρ z = ((e (z : Z ⧸ V) : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) :=
    fun z => rfl
  have hker : ρ.ker = V := by
    ext z
    rw [MonoidHom.mem_ker, hρ]
    constructor
    · intro h
      have h1 : e (z : Z ⧸ V) = 1 := Subtype.ext h
      have h2 : (z : Z ⧸ V) = 1 := by
        apply e.injective
        rw [h1, map_one]
      exact (QuotientGroup.eq_one_iff z).mp h2
    · intro h
      have h2 : (z : Z ⧸ V) = 1 := (QuotientGroup.eq_one_iff z).mpr h
      rw [h2, map_one]
      rfl
  refine ⟨ρ, by rw [hker]; exact hV, fun a ha => ?_⟩
  obtain ⟨q, hq⟩ := e.surjective ⟨a, ha⟩
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨z, by rw [hρ]; exact congrArg Subtype.val hq⟩

section Hall

theorem hall_card_aux {h k e m p : ℕ} (hp : p.Prime) (hr : h * k = 2 ^ e * m * p)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = p) (hk2 : ¬ 2 ∣ k) (hkp : ¬ p ∣ k)
    (hm2 : ¬ 2 ∣ m) (hmp : ¬ p ∣ m) : h = 2 ^ e * p := by
  have hc2 : Nat.Coprime (2 ^ e) k :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2)
  have hcp : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).2 hkp
  have hc : Nat.Coprime (2 ^ e * p) k := Nat.Coprime.mul_left hc2 hcp
  have hkm : k ∣ m := by
    have hdvd : k ∣ (2 ^ e * p) * m := ⟨h, by rw [show 2 ^ e * p * m = 2 ^ e * m * p by ring, ← hr]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left hc.symm hdvd
  obtain ⟨m', hm'⟩ := hkm
  have hm0 : m ≠ 0 := fun h0 => hm2 (h0 ▸ dvd_zero 2)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 => hm0 (by rw [hm', h0, zero_mul])
  have hh' : h = 2 ^ e * m' * p := by
    have : h * k = (2 ^ e * m' * p) * k := by rw [hr, hm']; ring
    exact Nat.eq_of_mul_eq_mul_right hk0 this
  have hm'1 : m' = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqh : q ∣ h := by rw [hh']; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hqd _) _
    have hqm : q ∣ m := by rw [hm']; exact Dvd.dvd.mul_left hqd _
    rcases hh q hq hqh with rfl | rfl
    · exact hm2 hqm
    · exact hmp hqm
  rw [hh', hm'1]
  ring

theorem exists_hall_overgroup {Γ : Type} [Group Γ] [Finite Γ] {U Z : Subgroup Γ}
    (hZs : Group.IsSolvable ↥Z) (hUZ : U ≤ Z) (hU : IsPGroup 2 ↥U) {e m p : ℕ} (hp : p.Prime)
    (hcard : Nat.card Z = 2 ^ e * m * p) (hm2 : ¬ 2 ∣ m) (hmp : ¬ p ∣ m) :
    ∃ H : Subgroup Γ, U ≤ H ∧ H ≤ Z ∧ Nat.card H = 2 ^ e * p := by
  have hU' : IsPGroup 2 ↥(U.subgroupOf Z) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUZ).symm
  obtain ⟨H, hUH, hHq, hk2, hkp⟩ := ModH.M24a.exists_hall_two_p hZs (U.subgroupOf Z) hU' p hp
  have hHZ : H.map Z.subtype ≤ Z := Subgroup.map_subtype_le H
  have hSH : U ≤ H.map Z.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hUZ]
    exact Subgroup.map_mono hUH
  have hcardH : Nat.card ↥(H.map Z.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Z.subtype Subtype.val_injective).toEquiv).symm
  refine ⟨H.map Z.subtype, hSH, hHZ, ?_⟩
  rw [hcardH]
  exact hall_card_aux hp (by rw [Subgroup.card_mul_index H]; exact hcard) hHq hk2 hkp hm2 hmp

theorem not_isSolvable_of_no_overgroup {Γ : Type} [Group Γ] [Finite Γ] {U Z : Subgroup Γ}
    (hUZ : U ≤ Z) (hU : IsPGroup 2 ↥U) {e m p : ℕ} (hp : p.Prime)
    (hcard : Nat.card Z = 2 ^ e * m * p) (hm2 : ¬ 2 ∣ m) (hmp : ¬ p ∣ m)
    (hno : ∀ H : Subgroup Γ, U ≤ H → H ≤ Z → Nat.card H ≠ 2 ^ e * p) :
    ¬ Group.IsSolvable ↥Z := fun hZs => by
  obtain ⟨H, hUH, hHZ, hH⟩ := exists_hall_overgroup hZs hUZ hU hp hcard hm2 hmp
  exact hno H hUH hHZ hH

end Hall

end CFSG.Quasithin.RonanE114.C5
