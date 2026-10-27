module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.Quasithin.Recognition.M12AscGlobal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem no_conj_z_eq_of_mem_uvJ (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z)
    {B : Subgroup G} (hBH : B ≤ H z) (hB5 : Nat.card B = 5)
    (hBuv : ∀ b ∈ B, cosetJ (z := z) (uH D * vH D) (b * ((uH D * vH D : ↥(H z)) : G) * b⁻¹))
    {E : Subgroup G} (hEJ : E ≤ J z) (hE : IsExtraspecial2 E) (hEcard : Nat.card E = 2 ^ 5)
    (hwE : ∀ w : G, cosetJ (z := z) (uH D * vH D) w → w ∈ Subgroup.centralizer (B : Set G) →
      ∀ e ∈ E, w * e = e * w)
    (hH' : ∀ g : G, g * z * g⁻¹ ∈ ⁅H z, H z⁆ → g * z * g⁻¹ = z) :
    ∀ x : G, cosetJ (z := z) (uH D * vH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  classical
  intro x hx _hx2 g hg
  obtain ⟨hz2, hJ', hCJ, hJp⟩ : orderOf z = 2 ∧ ⁅J z, J z⁆ = Subgroup.zpowers z ∧
      H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z ∧ IsPGroup 2 (J z) := by
    rcases h with h | h
    · exact ⟨h.1, h.2.2.1, h.2.2.2.1, isPGroup_J h⟩
    · exact ⟨orderOf_z_A h, h.commutator, h.centralizer_le, isPGroup_J_A h⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have huvH : ((uH D * vH D : ↥(H z)) : G) ∈ H z := (uH D * vH D).2
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hzc : ∀ y ∈ H z, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp hy
  have hpres : ∀ {b : G}, b ∈ B → ∀ {w : G}, cosetJ (z := z) (uH D * vH D) w →
      cosetJ (z := z) (uH D * vH D) (b * w * b⁻¹) := by
    intro b hb w hw
    obtain ⟨jb, hjb, hjb_eq⟩ := hBuv b hb
    obtain ⟨j', hj', rfl⟩ := hw
    have hbj' : b * j' * b⁻¹ ∈ J z := (Subgroup.mem_normalizer_iff.mp (hHN (hBH hb)) j').mp hj'
    refine ⟨jb * (b * j' * b⁻¹), (J z).mul_mem hjb hbj', ?_⟩
    calc b * (((uH D * vH D : ↥(H z)) : G) * j') * b⁻¹
        = (b * ((uH D * vH D : ↥(H z)) : G) * b⁻¹) * (b * j' * b⁻¹) := by group
      _ = (((uH D * vH D : ↥(H z)) : G) * jb) * (b * j' * b⁻¹) := by rw [hjb_eq]
      _ = ((uH D * vH D : ↥(H z)) : G) * (jb * (b * j' * b⁻¹)) := by group
  let α := {w : G // cosetJ (z := z) (uH D * vH D) w}
  let _ : MulAction ↥B α :=
    { smul := fun b w => ⟨(b : G) * (w : G) * (b : G)⁻¹, hpres b.2 w.2⟩
      one_smul := fun w => Subtype.ext (by
        change ((1 : ↥B) : G) * (w : G) * ((1 : ↥B) : G)⁻¹ = (w : G)
        simp)
      mul_smul := fun b₁ b₂ w => Subtype.ext (by
        change ((b₁ * b₂ : ↥B) : G) * (w : G) * ((b₁ * b₂ : ↥B) : G)⁻¹ =
          (b₁ : G) * ((b₂ : G) * (w : G) * (b₂ : G)⁻¹) * (b₁ : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcardα : Nat.card α = Nat.card ↥(J z) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨((uH D * vH D : ↥(H z)) : G)⁻¹ * (w : G), ?_⟩
        invFun := fun j => ⟨((uH D * vH D : ↥(H z)) : G) * (j : G), ⟨j, j.2, rfl⟩⟩
        left_inv := fun w => Subtype.ext (mul_inv_cancel_left _ _)
        right_inv := fun j => Subtype.ext (inv_mul_cancel_left _ _) }
    obtain ⟨j', hj', hw⟩ := w.2
    rw [hw, inv_mul_cancel_left]
    exact hj'
  have hnd : ¬ 5 ∣ Nat.card α := by
    rw [hcardα]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hJp
    rw [hn]
    intro h5
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
    norm_num at this
  have hBp : IsPGroup 5 ↥B := IsPGroup.of_card (n := 1) (by rw [hB5, pow_one])
  obtain ⟨⟨w, hw⟩, hwfix⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card α hnd
  have hwB : w ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfix := congrArg Subtype.val ((MulAction.mem_fixedPoints).mp hwfix ⟨b, hb⟩)
    change b * w * b⁻¹ = w at hfix
    calc b * w = (b * w * b⁻¹) * b := by group
      _ = w * b := by rw [hfix]
  have hwE' : ∀ e ∈ E, w * e = e * w := hwE w hw hwB
  obtain ⟨j₁, hj₁, hx_eq⟩ := hx
  obtain ⟨j₂, hj₂, hw_eq⟩ := hw
  obtain ⟨j, hjJ, hxwj⟩ : ∃ j ∈ J z, x = w * j :=
    ⟨j₂⁻¹ * j₁, (J z).mul_mem ((J z).inv_mem hj₂) hj₁, by rw [hx_eq, hw_eq]; group⟩
  have hxH : x ∈ H z := by
    rw [hx_eq]
    exact (H z).mul_mem huvH (J_le_H hj₁)
  have hzpow : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hE' : ⁅E, E⁆ = Subgroup.zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hJ']
      exact Subgroup.commutator_mono hEJ hEJ
    · rw [hzpow, hE.2.2]
  have hz_or : ∀ {y : G}, y ∈ Subgroup.zpowers z → y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← zpow_mod_orderOf, hz2]
      exact_mod_cast (by rw [h0, zpow_zero] : z ^ (k % 2) = 1)
    · right
      rw [← zpow_mod_orderOf, hz2]
      exact_mod_cast (by rw [h1, zpow_one] : z ^ (k % 2) = z)
  have hzE : z ∈ E := Subgroup.commutator_le_self E (hE' ▸ Subgroup.mem_zpowers z)
  have hEH : E ≤ H z := hEJ.trans J_le_H
  have hExt : CFSG.Quasithin.ExtraspecialAt E z :=
    { card_eq := hEcard
      mem := hzE
      ne_one := by
        intro h1
        rw [h1, orderOf_one] at hz2
        norm_num at hz2
      sq_eq := by
        rw [← pow_two, ← hz2]
        exact pow_orderOf_eq_one z
      central := fun q hq => hzc q (hEH hq)
      center_le := by
        intro q hq hcomm
        have hqc : (⟨q, hq⟩ : ↥E) ∈ Subgroup.center ↥E := by
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (hcomm y y.2).symm
        have hqmap : q ∈ (Subgroup.center ↥E).map E.subtype := ⟨⟨q, hq⟩, hqc, rfl⟩
        rw [← hE.2.1, hE'] at hqmap
        exact hz_or hqmap
      sq_mem := by
        intro q hq
        have hsq := IsExtraspecial2.pow_two_mem_center hE ⟨q, hq⟩
        have hqmap : q * q ∈ (Subgroup.center ↥E).map E.subtype :=
          ⟨⟨q, hq⟩ ^ 2, hsq, by simp [pow_two]⟩
        rw [← hE.2.1, hE'] at hqmap
        exact hz_or hqmap
      comm_mem := by
        intro q hq y hy
        have hc : ⁅q, y⁆ ∈ ⁅E, E⁆ := Subgroup.commutator_mem_commutator hq hy
        rw [hE'] at hc
        simpa [commutatorElement_def] using hz_or hc }
  have hcommz : ∀ e ∈ E, ⁅j, e⁆ ∈ Subgroup.zpowers z := fun e he =>
    hJ' ▸ Subgroup.commutator_mem_commutator hjJ (hEJ he)
  have hcentral : ∀ {y : G}, y ∈ Subgroup.zpowers z → ∀ q ∈ H z, q * y = y * q := by
    intro y hy q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute q z from hzc q hq).zpow_right k
  let ψ : ↥E →* ↥(Subgroup.zpowers z) :=
    { toFun := fun e => ⟨⁅j, (e : G)⁆, hcommz e e.2⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun e₁ e₂ => Subtype.ext (by
        change ⁅j, (e₁ : G) * (e₂ : G)⁆ = ⁅j, (e₁ : G)⁆ * ⁅j, (e₂ : G)⁆
        have hc₂ : (e₁ : G)⁻¹ * ⁅j, (e₂ : G)⁆ = ⁅j, (e₂ : G)⁆ * (e₁ : G)⁻¹ :=
          hcentral (hcommz e₂ e₂.2) _ ((H z).inv_mem (hEH e₁.2))
        calc ⁅j, (e₁ : G) * (e₂ : G)⁆
            = j * (e₁ : G) * j⁻¹ * ⁅j, (e₂ : G)⁆ * (e₁ : G)⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = j * (e₁ : G) * j⁻¹ * ((e₁ : G)⁻¹ * ⁅j, (e₂ : G)⁆) := by
              rw [hc₂]; group
          _ = ⁅j, (e₁ : G)⁆ * ⁅j, (e₂ : G)⁆ := by
              simp only [commutatorElement_def]; group) }
  have hmemker : ∀ e : ↥E, e ∈ ψ.ker ↔ j * (e : G) = (e : G) * j := by
    intro e
    rw [MonoidHom.mem_ker]
    change (⟨⁅j, (e : G)⁆, hcommz e e.2⟩ : ↥(Subgroup.zpowers z)) = 1 ↔ _
    rw [← commutatorElement_eq_one_iff_mul_comm, ← Subtype.val_inj]
    rfl
  have hindex : ψ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card ↥ψ.range ≤ Nat.card ↥(Subgroup.zpowers z) :=
          Subgroup.card_le_card_group ψ.range
      _ = 2 := hzpow
  let A : Subgroup G := ψ.ker.map E.subtype
  have hcardA : 16 ≤ Nat.card A := by
    have h1 : Nat.card A = Nat.card ↥ψ.ker := Subgroup.card_map_of_injective E.subtype_injective
    have h2 := Subgroup.card_mul_index ψ.ker
    rw [hEcard] at h2
    rw [h1]
    have h3 : Nat.card ↥ψ.ker * ψ.ker.index ≤ Nat.card ↥ψ.ker * 2 :=
      Nat.mul_le_mul_left _ hindex
    omega
  have hAE : A ≤ E := Subgroup.map_subtype_le _
  have hAx : ∀ a ∈ A, a * x = x * a := by
    rintro a ⟨e, he, rfl⟩
    have hej : j * (e : G) = (e : G) * j := (hmemker e).mp he
    rw [hxwj]
    calc (e : G) * (w * j) = ((e : G) * w) * j := (mul_assoc _ _ _).symm
      _ = (w * (e : G)) * j := by rw [← hwE' e e.2]
      _ = w * ((e : G) * j) := mul_assoc _ _ _
      _ = w * (j * (e : G)) := by rw [← hej]
      _ = w * j * (e : G) := (mul_assoc _ _ _).symm
  obtain ⟨a, haA, b, hbA, hab⟩ : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have := hExt.card_abelian_le hAE hcon
    omega
  have hzab : a * b * a⁻¹ * b⁻¹ = z := by
    rcases hExt.comm_mem a (hAE haA) b (hAE hbA) with h1 | h1
    · exfalso
      apply hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h1
  let M : Subgroup G := H z ⊓ Subgroup.centralizer ({x} : Set G)
  have hAM : A ≤ M := by
    intro a ha
    exact ⟨hEH (hAE ha), Subgroup.mem_centralizer_singleton_iff.mpr (hAx a ha)⟩
  have hAp : IsPGroup 2 A := hE.1.to_le hAE
  obtain ⟨Q, hAQ⟩ := (hAp.comap_subtype : IsPGroup 2 (A.subgroupOf M)).exists_le_sylow
  let X : Subgroup G := (Q : Subgroup ↥M).map M.subtype
  have hX : IsSylowOf 2 X M := ⟨Q, rfl⟩
  have hAX : A ≤ X := by
    calc A = (A.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hAM).symm
      _ ≤ (Q : Subgroup ↥M).map M.subtype := Subgroup.map_mono hAQ
  have hzX : z ∈ ⁅X, X⁆ := by
    rw [← hzab]
    exact Subgroup.commutator_mem_commutator (hAX haA) (hAX hbA)
  have hXH : X ≤ H z := hX.le.trans inf_le_left
  have hNX : ∀ g' ∈ Subgroup.centralizer ({x} : Set G),
      g' ∈ Subgroup.normalizer (X : Set G) → IsPGroup 2 (Subgroup.zpowers g') →
      g' ∈ Subgroup.centralizer ({z} : Set G) := by
    intro g' _ hg'N _
    have hXmap : X.map (MulAut.conj g').toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg'N
    have hmap : (⁅X, X⁆).map (MulAut.conj g').toMonoidHom = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, hXmap]
    have hzg : g' * z * g'⁻¹ ∈ ⁅X, X⁆ := by
      have hmem : (MulAut.conj g') z ∈ (⁅X, X⁆).map (MulAut.conj g').toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj g').toMonoidHom hzX
      simpa [MulAut.conj_apply] using hmap ▸ hmem
    have hzg' : g' * z * g'⁻¹ = z := hH' g' (Subgroup.commutator_mono hXH hXH hzg)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g' * z = (g' * z * g'⁻¹) * g' := by group
      _ = z * g' := by rw [hzg']
  have hJx : ¬ J z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hle
    have hxC : x ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hxJ : x ∈ J z := hCJ ⟨hxH, hxC⟩
    have huvJ : ((uH D * vH D : ↥(H z)) : G) ∈ J z := by
      have huv_eq : ((uH D * vH D : ↥(H z)) : G) = x * j₁⁻¹ := by rw [hx_eq]; group
      rw [huv_eq]
      exact (J z).mul_mem hxJ ((J z).inv_mem hj₁)
    have hPuv : uH D * vH D ∈ P_H D := J_le_P_H D (Subgroup.mem_subgroupOf.mpr huvJ)
    apply vH_not_mem_P_H D
    have hv := (P_H D).mul_mem ((P_H D).inv_mem (uH_mem_P_H D)) hPuv
    rwa [inv_mul_cancel_left] at hv
  have hdvd : 2 ∣ (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)).relIndex (Subgroup.centralizer ({z} : Set G)) :=
    dvd_relIndex_inf_centralizer_of_normal_pGroup (p := 2) (H := H z) (J := J z)
      (J_le_H (z := z)) hHN hJp hJx
  have hnot : ¬ IsConj z x :=
    not_isConj_of_isSylowOf_inf_centralizer (p := 2) (z := z) (y := x) (K := X) hX hNX hdvd
  exact hnot (isConj_iff.mpr ⟨g, hg⟩)

end CFSG.RankThree.GF2n.Parrott
