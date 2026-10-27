module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_orthModel_of_label {R : Type} [Group R] {lab : LargeEvenLabel}
    (hhas : GGHasLabel lab R) (htag : lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1)
    (hr : 4 ≤ lab.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V), Nat.card F = 2 ∧
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank F V = 2 * lab.rank ∧
      Nonempty (R ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  have hraw := hhas
  rcases htag with hD | hD
  · have hr3 : lab.rank ≠ 3 := by omega
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, hD, ite_eq_right hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, hdata⟩ := hraw
    let : Field K := hKfield
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard, hn]; norm_num
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (k := 1) Nat.prime_two (by norm_num) (by rw [hK2]; norm_num)
    have hfin : Module.finrank K (Fin lab.rank ⊕ Fin lab.rank → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card (R := K) (η := Fin lab.rank ⊕ Fin lab.rank)]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact ⟨K, hKfield, hKfin, inferInstance,
      Fin lab.rank ⊕ Fin lab.rank → K, inferInstance, inferInstance, inferInstance,
      TableBOrth.qPlusForm K lab.rank, hK2, TableBOrth.nondegenerate_qPlusForm lab.rank, hfin,
      ⟨hdata.some.trans (OrthTorus.rPlusEquiv K (by omega))⟩⟩
  · have hr2 : lab.rank ≠ 2 := by omega
    have hr3 : lab.rank ≠ 3 := by omega
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, hD, ite_eq_right hr2,
      ite_eq_right hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, hdata⟩ := hraw
    let : Field K := hKfield
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard, hn]; norm_num
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (k := 1) Nat.prime_two (by norm_num) (by rw [hK2]; norm_num)
    have hfin : Module.finrank K (LargeEvenMinusIdx (lab.rank - 1) → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card (R := K) (η := LargeEvenMinusIdx (lab.rank - 1))]
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    exact ⟨K, hKfield, hKfin, inferInstance,
      LargeEvenMinusIdx (lab.rank - 1) → K, inferInstance, inferInstance, inferInstance,
      TableBOrth.qMinusForm K (lab.rank - 1) b c, hK2,
      TableBOrth.nondegenerate_qMinusForm (lab.rank - 1) hirr, hfin,
      ⟨hdata.some.trans (OrthTorus.rMinusEquiv K (lab.rank - 1) b c)⟩⟩

theorem d_scMap_of_central {X R : Type} [Group X] [Finite X] [Group R] {p : ℕ} (hp : p.Prime)
    (ψ : X →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X)
    (hcop : ¬ p ∣ Nat.card ↥ψ.ker) {E : Subgroup X} (hE : IsElemAbelian p E)
    (hsc : ∀ g : X, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    IsElemAbelian p (E.map ψ) ∧
      ∀ g : R, (∀ e ∈ E.map ψ, g * e = e * g) → g ^ p = 1 → g ∈ E.map ψ := by
  refine ⟨hE.map ψ, ?_⟩
  intro g hg hgp
  obtain ⟨g₀, rfl⟩ := hψ g
  have hg₀p : g₀ ^ p ∈ ψ.ker := by
    simpa [MonoidHom.mem_ker, map_pow, hgp]
  have hcopher : Nat.Coprime (Nat.card ↥ψ.ker) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop).symm
  have hbij : Function.Bijective (fun w : ↥ψ.ker => w ^ p) :=
    Nat.Coprime.pow_left_bijective hcopher
  obtain ⟨z, hz⟩ := hbij.surjective ((⟨g₀ ^ p, hg₀p⟩ : ↥ψ.ker))⁻¹
  have hzX_pow : (z : X) ^ p = (g₀ ^ p)⁻¹ := by
    have h := congrArg (fun w : ↥ψ.ker => (w : X)) hz
    simpa using h
  have hz_cent : (z : X) ∈ Subgroup.center X := hker z.2
  have hg₁p : (g₀ * (z : X)) ^ p = 1 := by
    have hcomm : Commute g₀ (z : X) := Subgroup.mem_center_iff.mp hz_cent g₀
    rw [hcomm.mul_pow, hzX_pow, mul_inv_cancel]
  have hψg₁ : ψ (g₀ * (z : X)) = ψ g₀ := by
    rw [map_mul, MonoidHom.mem_ker.mp z.2, mul_one]
  have hcommE : ∀ e ∈ E, (g₀ * (z : X)) * e = e * (g₀ * (z : X)) := by
    intro e he
    have hmem : (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hψg₁]
      rw [hg (ψ e) (Subgroup.mem_map_of_mem ψ he)]
      group
    have hcent : (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹ ∈ Subgroup.center X :=
      hker hmem
    have hsplit : (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ =
        ((g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹) * e := by group
    have hpow1 : (((g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹) * e) ^ p = 1 := by
      rw [← hsplit, ← MulAut.conj_apply, ← map_pow, hE.2 e he, map_one]
    have hhe : Commute ((g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹) e :=
      (Subgroup.mem_center_iff.mp hcent e).symm
    have hhpow : ((g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹) ^ p = 1 := by
      have h1 := hpow1
      rw [hhe.mul_pow, hE.2 e he, mul_one] at h1
      exact h1
    have hw : (⟨(g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹, hmem⟩ : ↥ψ.ker) ^ p = 1 :=
      Subtype.ext hhpow
    have h1 : (⟨(g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹, hmem⟩ : ↥ψ.ker) = 1 :=
      hbij.injective (by simpa using hw)
    have hval : (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹ = 1 := congrArg Subtype.val h1
    have hconj : (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ = e := by
      calc (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹
          = ((g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * e⁻¹) * e := by group
        _ = e := by rw [hval, one_mul]
    calc (g₀ * (z : X)) * e = (g₀ * (z : X)) * e * (g₀ * (z : X))⁻¹ * (g₀ * (z : X)) := by
          group
      _ = e * (g₀ * (z : X)) := by rw [hconj]
  have hg₁E : (g₀ * (z : X)) ∈ E := hsc (g₀ * (z : X)) hcommE hg₁p
  have hmemmap : ψ (g₀ * (z : X)) ∈ E.map ψ := Subgroup.mem_map_of_mem ψ hg₁E
  rwa [hψg₁] at hmemmap

theorem d_centralizer_lift {X R : Type} [Group X] [Group R] (ψ : X →* R)
    (hker : ψ.ker ≤ Subgroup.center X) {J : Subgroup X} (hJ : commutator ↥J = ⊤) {e : X}
    (he : ∀ j ∈ J, ψ e * ψ j = ψ j * ψ e) : ∀ j ∈ J, e * j = j * e := by
  have hU : ∀ j ∈ J, j * e * j⁻¹ * e⁻¹ ∈ Subgroup.center X := by
    intro j hj
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← he j hj]
    group
  let φ : ↥J →* Subgroup.center X :=
    { toFun := fun j => ⟨(j : X) * e * (j : X)⁻¹ * e⁻¹, hU j j.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun m₁ m₂ => by
        apply Subtype.ext
        have hw : ∀ g, g * ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) =
            ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) * g := fun g =>
          Subgroup.mem_center_iff.1 (hU m₂ m₂.2) g
        have hw1 : ∀ g, g * ((m₁ : X) * e * (m₁ : X)⁻¹ * e⁻¹) =
            ((m₁ : X) * e * (m₁ : X)⁻¹ * e⁻¹) * g := fun g =>
          Subgroup.mem_center_iff.1 (hU m₁ m₁.2) g
        show ((m₁ : X) * (m₂ : X)) * e * ((m₁ : X) * (m₂ : X))⁻¹ * e⁻¹ =
          ((m₁ : X) * e * (m₁ : X)⁻¹ * e⁻¹) * ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹)
        calc ((m₁ : X) * (m₂ : X)) * e * ((m₁ : X) * (m₂ : X))⁻¹ * e⁻¹
            = (m₁ : X) * ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) *
                (e * (m₁ : X)⁻¹ * e⁻¹) := by group
          _ = ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) * (m₁ : X) *
                (e * (m₁ : X)⁻¹ * e⁻¹) := by rw [hw (m₁ : X)]
          _ = ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) *
                ((m₁ : X) * e * (m₁ : X)⁻¹ * e⁻¹) := by group
          _ = ((m₁ : X) * e * (m₁ : X)⁻¹ * e⁻¹) *
                ((m₂ : X) * e * (m₂ : X)⁻¹ * e⁻¹) := hw1 _ }
  have htop : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hJ]
    exact Abelianization.commutator_subset_ker φ
  intro j hj
  have h1 : φ ⟨j, hj⟩ = 1 :=
    MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top (⟨j, hj⟩ : ↥J))
  have h2 : j * e * j⁻¹ * e⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : j * e = e * j := by
    calc j * e = (j * e * j⁻¹ * e⁻¹) * (e * j) := by group
      _ = e * j := by rw [h2, one_mul]
  exact h3.symm

theorem d_card_bstar_centralizer_J_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 := by
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hBs_ab : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hcardBs_le : Nat.card ↥Bs ≤ p * Nat.card ↥B := hBs.2.2.1
  have hB_le_Bs : B ≤ Bs := hBs.1
  have hstdPre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hD_le_B : D ≤ B := hstdPre.1
  have hDcard : Nat.card ↥D = p ^ 2 := hstdPre.2.2.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hstdPre.2.2.2.2.2.2
  have : IsMulCommutative ↥Bs := hBs_ab.1
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let BsB : Subgroup ↥Bs := B.subgroupOf Bs
  have : BsB.Normal := Subgroup.normal_of_isMulCommutative BsB
  let f : ↥C →* (↥Bs ⧸ BsB) :=
    (QuotientGroup.mk' BsB).comp (Subgroup.inclusion (inf_le_left : C ≤ Bs))
  have hfker : Nat.card ↥f.ker = Nat.card ↥D := by
    have hkerD : f.ker = D.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hc
        rw [hDeq]
        refine ⟨?_, c.2.2⟩
        have h1 := hc
        change QuotientGroup.mk' BsB
          (Subgroup.inclusion (inf_le_left : C ≤ Bs) c) = 1 at h1
        have h2 : (Subgroup.inclusion (inf_le_left : C ≤ Bs) c : ↥Bs) ∈ BsB := by
          rw [← QuotientGroup.ker_mk' BsB]
          exact MonoidHom.mem_ker.mpr h1
        rwa [Subgroup.mem_subgroupOf] at h2
      · intro hc
        rw [hDeq] at hc
        obtain ⟨hcB, hcCGJ⟩ := hc
        show QuotientGroup.mk' BsB
          (Subgroup.inclusion (inf_le_left : C ≤ Bs) c) = 1
        have h2 : (Subgroup.inclusion (inf_le_left : C ≤ Bs) c : ↥Bs) ∈ BsB := by
          rw [Subgroup.mem_subgroupOf]
          exact hcB
        rw [← QuotientGroup.ker_mk' BsB] at h2
        exact MonoidHom.mem_ker.mp h2
    have hDC : D ≤ C := by
      intro d hd
      refine ⟨hB_le_Bs (hD_le_B hd), ?_⟩
      have hd' := hd
      rw [hDeq] at hd'
      exact hd'.2
    rw [hkerD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have hfrange : Nat.card ↥f.range ≤ p := by
    have h1 : Nat.card ↥f.range ≤ BsB.index := by
      rw [Subgroup.index_eq_card BsB]
      exact Nat.card_le_card_of_injective (fun z : ↥f.range => (z : ↥Bs ⧸ BsB))
        Subtype.coe_injective
    rw [Subgroup.index_eq_card_div BsB] at h1
    have h2 : Nat.card ↥BsB = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_Bs).toEquiv
    rw [h2] at h1
    exact h1.trans (Nat.div_le_of_le_mul (by rw [mul_comm]; exact hcardBs_le))
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hfker, hDcard] at hcard
  calc Nat.card ↥C = p ^ 2 * Nat.card ↥f.range := hcard.symm
    _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ hfrange
    _ = p ^ 3 := by ring

end CFSG.StandardType.HdRo7D
