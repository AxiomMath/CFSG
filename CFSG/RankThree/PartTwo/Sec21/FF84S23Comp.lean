module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23Basic
public import CFSG.RankThree.PartTwo.Sec21.FF84S23Sub
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc
public import CFSG.RankThree.PartTwo.Sec21.FF84S23Burnside

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_of_order_three (C A B : Subgroup H) (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hidx : ¬ 3 ∣ A.relIndex C) :
    ∃ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAs : Nat.card (A.subgroupOf C) = 3 := by
    rw [← hA]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hBs : Nat.card (B.subgroupOf C) = 3 := by
    rw [← hB]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have hpA : IsPGroup 3 (A.subgroupOf C) := IsPGroup.of_card (n := 1) (by rw [hAs]; simp)
  have hpB : IsPGroup 3 (B.subgroupOf C) := IsPGroup.of_card (n := 1) (by rw [hBs]; simp)
  have hAidx : (A.subgroupOf C).index = A.relIndex C := rfl
  have hBidx : (B.subgroupOf C).index = (A.subgroupOf C).index := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf C)
    have h2 := Subgroup.card_mul_index (B.subgroupOf C)
    rw [hAs] at h1
    rw [hBs] at h2
    omega
  let SA : Sylow 3 C := hpA.toSylow (by rw [hAidx]; exact hidx)
  let SB : Sylow 3 C := hpB.toSylow (by rw [hBidx, hAidx]; exact hidx)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C SA SB
  refine ⟨c, c.2, fun a ha => ?_⟩
  have hmem : (⟨a, hAC ha⟩ : C) ∈ (SA : Subgroup C) := by
    show (⟨a, hAC ha⟩ : C) ∈ A.subgroupOf C
    exact ha
  have h3 : c * (⟨a, hAC ha⟩ : C) * c⁻¹ ∈ ((c • SA : Sylow 3 C) : Subgroup C) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  rw [hc] at h3
  exact h3

noncomputable def mulEquivQuotientOfEqBot {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hN : N = ⊥) : X ≃* X ⧸ N :=
  MulEquiv.ofBijective (QuotientGroup.mk' N)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hN),
      QuotientGroup.mk'_surjective N⟩

theorem comp_simple {C : Subgroup H} (hC : IsComponent C) (hcen : Subgroup.center C = ⊥) :
    IsSimpleGroup C ∧ ∃ a b : C, a * b ≠ b * a := by
  obtain ⟨-, hs, hnab⟩ := hC.1
  haveI : (Subgroup.center C).Normal := inferInstance
  let e : C ≃* C ⧸ Subgroup.center C := mulEquivQuotientOfEqBot _ hcen
  exact ⟨e.isSimpleGroup, KCore.nonabelian_of_mulEquiv e hnab⟩

namespace Red3

variable {P P₁ P₂ : Subgroup H} (h : Red3 P P₁ P₂)
include h

theorem comp_sylow {C : Subgroup H} (hC : IsComponent C) :
    ∃ S : Sylow 3 C, (S : Subgroup C).map C.subtype = P ⊓ C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal h.toSylow hC.2

theorem comp_card {C : Subgroup H} (hO : pPrimeCore 3 H = ⊥) (hC : IsComponent C) :
    Nat.card ↥(P ⊓ C) = 3 ∨ Nat.card ↥(P ⊓ C) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := h.comp_sylow hC
  have hcard : Nat.card ↥(P ⊓ C) = Nat.card S := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv.symm
  have hne : C ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot C).mp (CFSG.LocalCores.isQuasisimple_nontrivial hC.1)
  have hdvd : 3 ∣ Nat.card C :=
    dvd_card_of_isSubnormal' Nat.prime_three hO hC.2 hne
  have hS1 : (S : Subgroup C) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S hdvd
  have hS9 : Nat.card ↥(P ⊓ C) ∣ 9 := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h9 : Nat.card ↥(P ⊓ C) ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hS9, by norm_num⟩
  have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hdiv] at h9
  simp only [Finset.mem_insert, Finset.mem_singleton] at h9
  rcases h9 with h1 | h3 | h9
  · exfalso
    rw [hcard] at h1
    exact hS1 (Subgroup.eq_bot_of_card_eq _ h1)
  · exact Or.inl h3
  · exact Or.inr h9

theorem comp_center_bot {C : Subgroup H} (hO : pPrimeCore 3 H = ⊥) (hC : IsComponent C) :
    Subgroup.center C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := h.comp_sylow hC
  haveI hperf : Group.IsPerfect C := hC.1.1
  haveI hab : IsMulCommutative (S : Subgroup C) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : ((a : C) : H) ∈ P ⊓ C := by
      rw [← hS]; exact ⟨a.1, a.2, rfl⟩
    have hb : ((b : C) : H) ∈ P ⊓ C := by
      rw [← hS]; exact ⟨b.1, b.2, rfl⟩
    exact Subtype.ext (Subtype.ext (h.comm ha.1 hb.1))
  have h1 := CFSG.Quasithin.SBd19F.sylow_inf_center_eq_bot (L := C) (p := 3) S
  have hcz : (Subgroup.center C).map C.subtype ≤ CFSG.pCore 3 H :=
    (CFSG.LocalCores.center_component_le_center_layer hC).trans
      (CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 3 hO)
  have hcen3 : IsPGroup 3 (Subgroup.center C) := by
    intro x
    have hx : ((x : C) : H) ∈ CFSG.pCore 3 H := hcz ⟨x.1, x.2, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg (fun t => ((t : CFSG.pCore 3 H) : H)) hk
  have hle : Subgroup.center C ≤ (S : Subgroup C) := hcen3.le_sylow_of_normal S
  rw [eq_bot_iff]
  intro x hx
  have := h1 ▸ (Subgroup.mem_inf.2 ⟨hle hx, hx⟩ : x ∈ (S : Subgroup C) ⊓ Subgroup.center C)
  exact this

theorem comp_relIndex {C : Subgroup H} (hC : IsComponent C) : ¬ 3 ∣ (P ⊓ C).relIndex C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := h.comp_sylow hC
  have : (P ⊓ C).subgroupOf C = S := by
    rw [← hS]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective S
  show ¬ 3 ∣ ((P ⊓ C).subgroupOf C).index
  rw [this]
  exact S.not_dvd_index

theorem sup_eq_P {Q Q' : Subgroup H} (hQP : Q ≤ P) (hQ'P : Q' ≤ P) (hQ : Nat.card Q = 3)
    (hQ' : Nat.card Q' = 3) (hinf : Q ⊓ Q' = ⊥) : Q ⊔ Q' = P := by
  have hd1 : 3 ∣ Nat.card ↥(Q ⊔ Q') := hQ ▸ Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ Q')
  have hd2 : Nat.card ↥(Q ⊔ Q') ∣ 9 := by
    rw [← h.card]; exact Subgroup.card_dvd_of_le (sup_le hQP hQ'P)
  have h9 : Nat.card ↥(Q ⊔ Q') ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hd2, by norm_num⟩
  have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hdiv] at h9
  simp only [Finset.mem_insert, Finset.mem_singleton] at h9
  rcases h9 with h1 | h3 | h9
  · rw [h1] at hd1; omega
  · exfalso
    have hQeq : Q = Q ⊔ Q' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hQ])
    have hQ'le : Q' ≤ Q := hQeq ▸ le_sup_right
    have : Q' = ⊥ := by
      rw [← hinf]; exact (inf_eq_right.2 hQ'le).symm
    rw [this] at hQ'
    simp at hQ'
  · exact Subgroup.eq_of_le_of_card_ge (sup_le hQP hQ'P) (by rw [h9, h.card])

theorem strongClosed_of_eq {Q : Subgroup H} (hQ : Q = P₁ ∨ Q = P₂) :
    ∀ a ∈ Q, ∀ x : H, x⁻¹ * a * x ∈ P → x⁻¹ * a * x ∈ Q := by
  rcases hQ with rfl | rfl
  · exact h.sc₁.2
  · exact h.sc₂.2

theorem comp_inf_eq_bot {C C' : Subgroup H} (hcen : Subgroup.center C = ⊥)
    (hcomm : ⁅C, C'⁆ = ⊥) : C ⊓ C' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hle : C ≤ Subgroup.centralizer (C' : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hxc : ∀ y ∈ C, y * x = x * y := by
    intro y hy
    have hy' : y ∈ Subgroup.centralizer (C' : Set H) := hle hy
    exact (Subgroup.mem_centralizer_iff.mp hy' x hx.2).symm
  have hxz : (⟨x, hx.1⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxc y y.2)
  rw [hcen, Subgroup.mem_bot] at hxz
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxz)

theorem card_three_of_inf_bot {A B : Subgroup H} (hAP : A ≤ P) (hBP : B ≤ P) (hAB : A ⊓ B = ⊥)
    (hA : Nat.card A = 3 ∨ Nat.card A = 9) (hB : Nat.card B = 3 ∨ Nat.card B = 9) :
    Nat.card A = 3 := by
  rcases hA with hA | hA
  · exact hA
  · exfalso
    have hAeq : A = P := Subgroup.eq_of_le_of_card_ge hAP (by rw [hA, h.card])
    have hBA : B ≤ A := hAeq ▸ hBP
    have hB1 : B = ⊥ := calc B = B ⊓ A := (inf_eq_left.2 hBA).symm
      _ = A ⊓ B := inf_comm _ _
      _ = ⊥ := hAB
    rcases hB with hB | hB <;> (rw [hB1] at hB; simp at hB)

theorem comp_normal (hO : pPrimeCore 3 H = ⊥) {C : Subgroup H} (hC : IsComponent C) :
    C.Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen := h.comp_center_bot hO hC
  have hmain : ∀ g : H, C.map (MulAut.conj g).toMonoidHom = C := by
    intro g
    by_contra hne
    set C' : Subgroup H := C.map (MulAut.conj g).toMonoidHom with hC'def
    have hC' : IsComponent C' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hC
    have hcomm : ⁅C, C'⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hC hC' with h1 | h1
      · exact absurd h1.symm hne
      · exact h1
    have hCC' : C ⊓ C' = ⊥ := h.comp_inf_eq_bot hcen hcomm
    obtain ⟨hCs, hCnab⟩ := comp_simple hC hcen
    have hcardQ := h.comp_card hO hC
    have hcardQ' := h.comp_card hO hC'
    have hQQ' : (P ⊓ C) ⊓ (P ⊓ C') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ C ⊓ C' := ⟨hx.1.2, hx.2.2⟩
      rwa [hCC'] at this
    have hQQ'' : (P ⊓ C') ⊓ (P ⊓ C) = ⊥ := by rw [inf_comm]; exact hQQ'
    have hQ3 : Nat.card ↥(P ⊓ C) = 3 :=
      h.card_three_of_inf_bot inf_le_left inf_le_left hQQ' hcardQ hcardQ'
    have hQ'3 : Nat.card ↥(P ⊓ C') = 3 :=
      h.card_three_of_inf_bot inf_le_left inf_le_left hQQ'' hcardQ' hcardQ
    have hsup := h.sup_eq_P inf_le_left inf_le_left hQ3 hQ'3 hQQ'
    obtain ⟨n, hnC, hnv⟩ := exists_inverting_of_simple C (P ⊓ C) hCs hCnab inf_le_right hQ3
      (h.comp_relIndex hC)
    have hnC' : n ∈ Subgroup.centralizer (C' : Set H) := by
      have hle : C ≤ Subgroup.centralizer (C' : Set H) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact hle hnC
    have hncen : ∀ r ∈ P ⊓ C', n * r * n⁻¹ = r := by
      intro r hr
      have := Subgroup.mem_centralizer_iff.mp hnC' r hr.2
      rw [← this]; group
    have hrefl := h.reflection hQ3 hQ'3 inf_le_left inf_le_left hsup hnv hncen
    have hQsc : ∀ a ∈ P ⊓ C, ∀ x : H, x⁻¹ * a * x ∈ P → x⁻¹ * a * x ∈ P ⊓ C := by
      refine h.strongClosed_of_eq ?_
      rcases hrefl with ⟨a, _⟩ | ⟨_, b⟩
      · exact Or.inl a.symm
      · exact Or.inr b.symm
    let B : Subgroup H := (P ⊓ C').map (MulAut.conj g⁻¹).toMonoidHom
    have hBC : B ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hy.2
      have : (MulAut.conj g⁻¹).toMonoidHom y = z := by
        rw [← hzy]
        show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z
        group
      rw [this]; exact hz
    have hBcard : Nat.card B = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hQ'3]
    obtain ⟨c, hcC, hc⟩ := exists_conj_of_order_three C (P ⊓ C) B inf_le_right hBC hQ3 hBcard
      (h.comp_relIndex hC)
    have hall : ∀ a ∈ P ⊓ C, a = 1 := by
      intro a ha
      obtain ⟨y, hy, hyb⟩ := hc a ha
      have hya : y = g * c * a * c⁻¹ * g⁻¹ := by
        have : g⁻¹ * y * g = c * a * c⁻¹ := by simpa [MulAut.conj_apply] using hyb
        calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          _ = g * (c * a * c⁻¹) * g⁻¹ := by rw [this]
          _ = g * c * a * c⁻¹ * g⁻¹ := by group
      have hyQ : y ∈ P ⊓ C := by
        have hyP : y ∈ P := hy.1
        have := hQsc a ha (g * c)⁻¹ (by
          rw [show ((g * c)⁻¹)⁻¹ * a * (g * c)⁻¹ = y by rw [hya]; group]; exact hyP)
        rwa [show ((g * c)⁻¹)⁻¹ * a * (g * c)⁻¹ = y by rw [hya]; group] at this
      have hy1 : y = 1 := by
        have : y ∈ (P ⊓ C) ⊓ (P ⊓ C') := ⟨hyQ, hy⟩
        rwa [hQQ', Subgroup.mem_bot] at this
      have : a = 1 := by
        rw [hy1] at hya
        have h2 : g * c * a * c⁻¹ * g⁻¹ = 1 := hya.symm
        calc a = (g * c)⁻¹ * (g * c * a * c⁻¹ * g⁻¹) * (g * c) := by group
          _ = 1 := by rw [h2]; group
      exact this
    have : P ⊓ C = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    rw [this] at hQ3
    simp at hQ3
  exact ⟨fun x hx g => by
    have : g * x * g⁻¹ ∈ C.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmain g] at this⟩

end Red3

end CFSG.RankThree.PartTwo.Sec21.FF84
