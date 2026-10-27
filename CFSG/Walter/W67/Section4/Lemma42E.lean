module

import CFSG.Walter.W67.Section4.Lemma42D
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W1GW
public import CFSG.Walter.Cited.CentralSplit
public import CFSG.Walter.Cited.SuzukiCases
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement
open CFSG.GorensteinWalter

theorem isKleinFour_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsKleinFour A) : IsKleinFour B :=
  ⟨by rw [← Nat.card_congr e.toEquiv, hA.card_four],
    (Monoid.exponent_eq_of_mulEquiv e.symm).trans hA.exponent_two⟩

variable {G : Type} [Group G] [Finite G]

abbrev conjSet (X V : Subgroup G) : Set G := {y | ∃ x ∈ X, ∃ v ∈ V, y = x * v * x⁻¹}

omit [Finite G] in
theorem closure_conjSet_le {X V : Subgroup G} (hVX : V ≤ X) :
    Subgroup.closure (conjSet X V) ≤ X := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact X.mul_mem (X.mul_mem hx (hVX hv)) (X.inv_mem hx)

omit [Finite G] in
theorem le_closure_conjSet (X V : Subgroup G) : V ≤ Subgroup.closure (conjSet X V) :=
  fun v hv => Subgroup.subset_closure ⟨1, X.one_mem, v, hv, by group⟩

omit [Finite G] in
theorem conj_mem_closure_conjSet {X V : Subgroup G} {g : G} (hg : g ∈ X) :
    ∀ w ∈ Subgroup.closure (conjSet X V), g * w * g⁻¹ ∈ Subgroup.closure (conjSet X V) := by
  have hle : Subgroup.closure (conjSet X V) ≤
      (Subgroup.closure (conjSet X V)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, hv, rfl⟩
    refine Subgroup.subset_closure ⟨g * x, X.mul_mem hg hx, v, hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  intro w hw
  exact hle hw

omit [Finite G] in
theorem mem_normalizer_closure_conjSet {X V : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    ∀ w ∈ Subgroup.closure (conjSet X V), g * w * g⁻¹ ∈ Subgroup.closure (conjSet X V) := by
  have hle : Subgroup.closure (conjSet X V) ≤
      (Subgroup.closure (conjSet X V)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, hv, rfl⟩
    refine Subgroup.subset_closure ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX x).mp hx,
      g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgV v).mp hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  intro w hw
  exact hle hw

omit [Finite G] in
theorem closure_conjSet_le_of {X V N : Subgroup G} (hVN : V ≤ N)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) : Subgroup.closure (conjSet X V) ≤ N := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hXN hx) v).mp (hVN hv)

omit [Finite G] in
theorem le_centralizer_closure_conjSet {X V O : Subgroup G}
    (hOX : X ≤ Subgroup.normalizer (O : Set G)) (hOV : O ≤ Subgroup.centralizer (V : Set G)) :
    O ≤ Subgroup.centralizer (Subgroup.closure (conjSet X V) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  have h1 : x⁻¹ * o * x⁻¹⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hOX hx)) o).mp ho
  have h2 := Subgroup.mem_centralizer_iff.mp (hOV h1) v hv
  calc x * v * x⁻¹ * o = x * (v * (x⁻¹ * o * x⁻¹⁻¹)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * o * x⁻¹⁻¹) * v) * x⁻¹ := by rw [h2]
    _ = o * (x * v * x⁻¹) := by group

namespace Std

variable (s : Std G) {T₂ : G}

theorem normal_or_psl25
    [Fact (Nat.Prime 5)] (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T)
    (h2 : orderOf T₂ = 2) {X : Subgroup G} (hAX : s.fr.A T₂ ≤ X) (hVX : s.fr.V T₂ ≤ X)
    (hX2 : (Nat.card X).factorization 2 = 2) :
    ((s.fr.V T₂).subgroupOf X).Normal ∨
      (Nonempty (↥(⁅Subgroup.closure (conjSet X (s.fr.V T₂)),
          Subgroup.closure (conjSet X (s.fr.V T₂))⁆ : Subgroup G) ≃* PSL(2, GaloisField 5 1)) ∧
        s.fr.V T₂ ≤ ⁅Subgroup.closure (conjSet X (s.fr.V T₂)),
          Subgroup.closure (conjSet X (s.fr.V T₂))⁆) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 X with hO
  have hOn : O.Normal := CFSG.pPrimeCore_normal (p := 2) (G := X)
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))
  set π := QuotientGroup.mk' O with hπ
  set Vx := (s.fr.V T₂).subgroupOf X with hVx
  have eVx : Vx ≃* s.fr.V T₂ := Subgroup.subgroupOfEquivOfLe hVX
  have hVK := s.fr.isKleinFour_V hT₂ h2
  have hVxK : IsKleinFour Vx := isKleinFour_of_mulEquiv eVx.symm hVK
  have hVx2 : IsPGroup 2 Vx := IsPGroup.of_card (n := 2) (by rw [hVxK.card_four]; norm_num)
  have hOV := s.oddPart_le_centralizer hp hT₂ h2 hAX hVX hX2
  have hVxO : Vx ≤ Subgroup.centralizer (O : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOV o ho) v hv).symm
  have hπinj : Function.Injective (π.comp Vx.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    have hvO : (v : X) ∈ O := (QuotientGroup.eq_one_iff _).mp hv
    exact Subtype.ext (eq_one_of_odd_of_isPGroup hVx2 v.2
      (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hvO)))
  set Vb := Vx.map π with hVb
  have hrange : (π.comp Vx.subtype).range = Vb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eVb : Vx ≃* Vb := (MonoidHom.ofInjective hπinj).trans (MulEquiv.subgroupCongr hrange)
  have hVbK : IsKleinFour Vb := isKleinFour_of_mulEquiv eVb hVxK
  have hQ2 : (Nat.card (X ⧸ O)).factorization 2 = 2 := by
    have h1 : Nat.card O * Nat.card (X ⧸ O) = Nat.card X := by
      rw [← Subgroup.index_eq_card]
      exact O.card_mul_index
    have hO0 : (Nat.card O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hOodd)
        (even_iff_two_dvd.mpr h))
    rw [← h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hO0,
      zero_add] at hX2
    exact hX2
  set Sb : Sylow 2 (X ⧸ O) := Sylow.ofCard Vb (by rw [hVbK.card_four, hQ2]; norm_num)
  have hSb : (Sb : Subgroup (X ⧸ O)) = Vb := Sylow.coe_ofCard _ _
  have hQsyl : ∀ P : Sylow 2 (X ⧸ O), IsKleinFour (P : Subgroup (X ⧸ O)) := by
    intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (X ⧸ O) Sb P
    have e1 : (Sb : Subgroup (X ⧸ O)) ≃* (P : Subgroup (X ⧸ O)) := by
      rw [← hg]
      exact Sb.equivSMul g
    exact isKleinFour_of_mulEquiv e1 (hSb ▸ hVbK)
  have hOQ : CFSG.pPrimeCore 2 (X ⧸ O) = ⊥ := pPrimeCore_quotient_eq_bot
  have hnormal : Vb.Normal → (Vx).Normal := fun hn =>
    Suzuki.normal_of_normal_map O hOodd hVx2 hVxO hn
  by_cases h2Q : IsPGroup 2 (X ⧸ O)
  ·
    left
    apply hnormal
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2Q
    rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hQ2
    rw [hQ2] at hk
    have htop : Vb = ⊤ := Subgroup.eq_top_of_card_eq Vb (by rw [hVbK.card_four, hk]; norm_num)
    rw [htop]
    infer_instance
  · obtain ⟨L, hLn, hLi, p', f', hp', hp'odd, hf', ⟨eL⟩⟩ := exists_psl2_of_kleinFour hOQ hQsyl h2Q
    have hVb2 : IsPGroup 2 Vb := IsPGroup.of_card (n := 2) (by rw [hVbK.card_four]; norm_num)
    have hVbL : Vb ≤ L := by
      intro x hx
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hVb2) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hk
      have h1 : orderOf (QuotientGroup.mk' L x) ∣ 2 ^ k := hk ▸ orderOf_map_dvd _ x
      have h2' : orderOf (QuotientGroup.mk' L x) ∣ L.index := by
        rw [Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) L.index :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hLi)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2'
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact h3
    have hKcard : Nat.card (GaloisField p' f') = p' ^ f' := GaloisField.card _ _ hf'.ne'
    by_cases h3 : p' ^ f' = 3
    ·
      left
      apply hnormal
      obtain ⟨T, hTn, hT4⟩ := Suzuki.exists_normal_of_card_three (GaloisField p' f') hKcard
        hp'odd hf' h3 L hLn eL
      have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
      have hTS : T ≤ (Sb : Subgroup (X ⧸ O)) := hT2.le_sylow_of_normal Sb
      rw [hSb] at hTS
      have hTV : T = Vb := Subgroup.eq_of_le_of_card_ge hTS (by rw [hT4, hVbK.card_four])
      rw [← hTV]
      exact hTn
    by_cases h5 : p' ^ f' = 5
    ·
      right
      obtain ⟨hp5, hf1⟩ := (Nat.prime_five.pow_eq_iff).mp h5
      subst hp5 hf1
      have hPs : IsSimpleGroup PSL(2, GaloisField 5 1) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hKcard]; norm_num)
      have hLs : IsSimpleGroup L := eL.isSimpleGroup
      have hL60 : Nat.card L = 60 := by
        rw [Nat.card_congr eL.toEquiv, Suzuki.card_psl2_of_card _
          (isOddPrimePower_of_card hKcard hp'odd hf') hKcard]
        norm_num
      set W := Subgroup.closure (conjSet X (s.fr.V T₂)) with hW
      have hWX : W ≤ X := closure_conjSet_le hVX
      have hVW : s.fr.V T₂ ≤ W := le_closure_conjSet X _
      set ψ : W →* X ⧸ O := π.comp (Subgroup.inclusion hWX) with hψ
      have hψapp : ∀ w : W, ψ w = π (Subgroup.inclusion hWX w) := fun w => rfl
      have hRL : ψ.range ≤ L := by
        set Lg : Subgroup G := (L.comap π).map X.subtype with hLg
        have hVLg : s.fr.V T₂ ≤ Lg := fun v hv =>
          ⟨⟨v, hVX hv⟩, hVbL ⟨⟨v, hVX hv⟩, hv, rfl⟩, rfl⟩
        have hXLg : X ≤ Subgroup.normalizer (Lg : Set G) := fun x hx =>
          JT.mem_normalizer_of_conj_mem fun y hy => by
            obtain ⟨y', hy', rfl⟩ := hy
            refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
            change π (⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹) ∈ L
            rw [map_mul, map_mul, map_inv]
            exact hLn.conj_mem _ hy' _
        have hWLg := closure_conjSet_le_of hVLg hXLg
        rintro _ ⟨w, rfl⟩
        obtain ⟨y, hy, hyw⟩ := hWLg w.2
        have hyw' : Subgroup.inclusion hWX w = y := Subtype.ext hyw.symm
        rw [hψapp, hyw']
        exact hy
      have hVbR : Vb ≤ ψ.range := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨(x : G), hVW hx⟩, rfl⟩
      have hRn : ψ.range.Normal := ⟨fun y hy q => by
        obtain ⟨w, rfl⟩ := hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O q
        refine ⟨⟨(x : G) * w * (x : G)⁻¹, conj_mem_closure_conjSet x.2 w w.2⟩, ?_⟩
        rw [hψapp, hψapp]
        have : Subgroup.inclusion hWX ⟨(x : G) * w * (x : G)⁻¹,
            conj_mem_closure_conjSet x.2 w w.2⟩ = x * Subgroup.inclusion hWX w * x⁻¹ :=
          Subtype.ext rfl
        rw [this, map_mul, map_mul, map_inv]⟩
      have hψL : ψ.range = L := by
        refine le_antisymm hRL ?_
        have := hRn.subgroupOf L
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.range.subgroupOf L) with h | h
        · exfalso
          have hR : ψ.range = ⊥ := by
            rw [eq_bot_iff]
            intro y hy
            have : (⟨y, hRL hy⟩ : L) ∈ ψ.range.subgroupOf L := hy
            rw [h, Subgroup.mem_bot] at this
            exact congrArg Subtype.val this
          have := Subgroup.card_le_of_le (hVbR.trans hR.le)
          rw [hVbK.card_four, Subgroup.card_bot] at this
          omega
        · intro l hl
          have : (⟨l, hl⟩ : L) ∈ ψ.range.subgroupOf L := h ▸ Subgroup.mem_top _
          exact this
      set Z := ψ.ker with hZ
      have hOg : O.map X.subtype ≤ Subgroup.centralizer (W : Set G) := by
        refine le_centralizer_closure_conjSet (fun x hx => JT.mem_normalizer_of_conj_mem
          fun y hy => ?_) (fun o ho => ?_)
        · obtain ⟨y', hy', rfl⟩ := hy
          exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hOn.conj_mem _ hy' _, rfl⟩
        · obtain ⟨o', ho', rfl⟩ := ho
          exact hOV o' ho'
      have hZO : ∀ z ∈ Z, Subgroup.inclusion hWX z ∈ O := fun z hz =>
        (QuotientGroup.eq_one_iff _).mp hz
      have hZcen : Z ≤ Subgroup.center W := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro w
        have h1 : (z : G) ∈ O.map X.subtype := ⟨_, hZO z hz, rfl⟩
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOg h1) w w.2)
      have hZodd : Odd (Nat.card Z) := by
        have hle : Z.map (Subgroup.inclusion hWX) ≤ O := by
          rintro _ ⟨z, hz, rfl⟩
          exact hZO z hz
        have h1 := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWX)] at h1
        exact Odd.of_dvd_nat hOodd h1
      let eWZ : W ⧸ Z ≃* L :=
        (QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hψL)
      have hWZs : IsSimpleGroup (W ⧸ Z) := eWZ.isSimpleGroup
      have hWZ60 : Nat.card (W ⧸ Z) = 60 := by rw [Nat.card_congr eWZ.toEquiv, hL60]
      have hdisj : commutator W ⊓ Z = ⊥ := Suzuki.commutator_inf_eq_bot Z hZodd hZcen
        (fun p _ hp2 R => Suzuki.isCyclic_sylow_of_card_sixty hWZ60 p hp2 R)
      have hmap : (commutator W).map (QuotientGroup.mk' Z) = ⊤ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
          (QuotientGroup.mk'_surjective Z), ← commutator_def]
        exact Suzuki.commutator_eq_top_of_card_sixty hWZ60
      set f := (QuotientGroup.mk' Z).comp (commutator W).subtype with hf
      have hfinj : Function.Injective f := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro c hc
        have hcZ : (c : W) ∈ Z := (QuotientGroup.eq_one_iff _).mp hc
        have : (c : W) ∈ commutator W ⊓ Z := ⟨c.2, hcZ⟩
        rw [hdisj, Subgroup.mem_bot] at this
        exact Subtype.ext this
      have hfsurj : Function.Surjective f := by
        intro y
        have : y ∈ (commutator W).map (QuotientGroup.mk' Z) := hmap ▸ Subgroup.mem_top y
        obtain ⟨c, hc, rfl⟩ := this
        exact ⟨⟨c, hc⟩, rfl⟩
      let eC : commutator W ≃* W ⧸ Z := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
      have hcomm : ⁅W, W⁆ = (commutator W).map W.subtype := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      refine ⟨⟨(MulEquiv.subgroupCongr hcomm).trans
        ((((commutator W).equivMapOfInjective W.subtype W.subtype_injective).symm.trans
          eC).trans (eWZ.trans eL))⟩, ?_⟩
      intro v hv
      rw [hcomm]
      set w : W := ⟨v, hVW hv⟩ with hw
      have hsup : commutator W ⊔ Z = ⊤ := by
        have h := Subgroup.comap_map_eq (QuotientGroup.mk' Z) (commutator W)
        rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
        exact h.symm
      have hZN : Z ≤ Subgroup.normalizer ((commutator W : Subgroup W) : Set W) := fun z _ =>
        JT.mem_normalizer_of_conj_mem fun c hc =>
          (inferInstance : (commutator W).Normal).conj_mem c hc z
      obtain ⟨c, hc, z, hz, hcz⟩ := (mem_sup_iff_of_le_normalizer hZN).mp
        (hsup ▸ Subgroup.mem_top w : w ∈ commutator W ⊔ Z)
      have hw2 : w * w = 1 := Subtype.ext (s.fr.mul_self_of_mem_S (s.fr.V_le_S hT₂ hv))
      have hzc : c * z = z * c := Subgroup.mem_center_iff.mp (hZcen hz) c
      have hzz : z * z = (c * c)⁻¹ := by
        have h1 : (c * c) * (z * z) = 1 := by
          calc (c * c) * (z * z) = c * (c * z) * z := by group
            _ = c * (z * c) * z := by rw [hzc]
            _ = (c * z) * (c * z) := by group
            _ = 1 := by rw [hcz, hw2]
        exact eq_inv_of_mul_eq_one_right h1
      have hzz1 : z * z = 1 := by
        have : z * z ∈ commutator W ⊓ Z :=
          ⟨hzz ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hc), Subgroup.mul_mem _ hz hz⟩
        rw [hdisj, Subgroup.mem_bot] at this
        exact this
      have hz1 : z = 1 := by
        have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz1)
        have h2' : Odd (orderOf z) := Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hz)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (Nat.coprime_two_right.mpr h2') (dvd_refl _) h1)
      rw [hz1, mul_one] at hcz
      exact ⟨c, hc, by rw [hcz]; rfl⟩
    ·
      exfalso
      have h7 : 7 ≤ p' ^ f' := by
        have h1 : 3 ≤ p' := by
          have := hp'.out.two_le
          rcases hp'odd with ⟨m, hm⟩
          omega
        have h2' : 3 ≤ p' ^ f' := h1.trans (Nat.le_self_pow hf'.ne' p')
        obtain ⟨m, hm⟩ := Odd.pow hp'odd (n := f')
        omega
      have hp'2 : p' ≠ 2 := fun h => by rw [h] at hp'odd; exact absurd hp'odd (by decide)
      have hF := JT.psl2Facts L eL hp'2 (by omega)
      have hLC := hF.kleinFour Vb hVbL hVbK
      have : Nontrivial Vx :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hVxK.card_four]; norm_num)
      obtain ⟨v, hv1⟩ := exists_ne (1 : Vx)
      have hvv : (v : X) * v = 1 := by
        have := hVxK.mul_self v
        exact congrArg Subtype.val this
      have hvG : ((v : X) : G) ∈ s.fr.V T₂ := v.2
      have hvG1 : ((v : X) : G) ≠ 1 := fun h => hv1 (Subtype.ext (Subtype.ext h))
      have hCX : Subgroup.centralizer ({(v : X)} : Set X) ≤ Subgroup.centralizer (Vx : Set X) := by
        intro c hc
        have hcG : (c : G) ∈ Subgroup.centralizer ({((v : X) : G)} : Set G) ⊓ X :=
          ⟨Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)), c.2⟩
        have h1 := s.centralizer_inf_le hp hT₂ h2 hAX hVX hX2 hvG hvG1 hcG
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 w hw)
      have hCq := Suzuki.centralizer_mk_le_map O hOodd hvv
      have hCQ : Subgroup.centralizer ({π v} : Set (X ⧸ O)) ≤
          Subgroup.centralizer (Vb : Set (X ⧸ O)) := by
        intro y hy
        obtain ⟨c, hc, rfl⟩ := hCq hy
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨w, hw, rfl⟩
        have h1 := Subgroup.mem_centralizer_iff.mp (hCX hc) w hw
        rw [← map_mul, ← map_mul, h1]
      have hvL : π v ∈ L := hVbL ⟨v, v.2, rfl⟩
      set v' : L := ⟨π v, hvL⟩ with hv'
      have hv'2 : orderOf v' = 2 := by
        rw [hv', Subgroup.orderOf_mk]
        have h1 : orderOf ((π.comp Vx.subtype) v) = 2 := by
          rw [orderOf_injective _ hπinj]
          exact orderOf_eq_prime (by rw [pow_two]; exact hVxK.mul_self v) hv1
        exact h1
      obtain ⟨n, hn4, -, hncard, -⟩ := psl2_centralizer_involution_dihedral (GaloisField p' f')
        hKcard hp'odd hf' h7 (t := eL v') (by rw [MulEquiv.orderOf_eq, hv'2])
      have hcardL : Nat.card (Subgroup.centralizer ({v'} : Set L)) = 2 * n := by
        rw [hncard, ← CFSG.centralizer_singleton_map eL v',
          Subgroup.card_map_of_injective eL.injective]
      have hle : (Subgroup.centralizer ({v'} : Set L)).map L.subtype ≤ Vb := by
        rw [← hLC]
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨y.2, hCQ (Subgroup.mem_centralizer_singleton_iff.mpr ?_)⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
      have hc := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective L.subtype_injective, hcardL, hVbK.card_four] at hc
      omega

end Std

end CFSG.Walter.W67
