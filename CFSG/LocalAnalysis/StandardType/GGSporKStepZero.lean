module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly


private theorem gk0_quasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Assembly.IsQuasisimple A) : CFSG.Assembly.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := h
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

theorem ggSporK_pCore_two_eq_bot {W : Type} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H : Subgroup W} (hP' : LargeEvenPPrimeCore p ↥H = ⊥) :
    CFSG.pCore 2 ↥H = ⊥ := by
  have hn : (CFSG.pCore 2 ↥H).Normal := CFSG.BaerSuzuki.Helpers.pCore_normal 2
  have h2 : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  obtain ⟨n, hn2⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card (CFSG.pCore 2 ↥H)) := by
    rw [hn2]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hle : CFSG.pCore 2 ↥H ≤ CFSG.pPrimeCore p ↥H := le_sSup ⟨hn, hcop⟩
  have hP'' : CFSG.pPrimeCore p ↥H = ⊥ := hP'
  rw [hP''] at hle
  exact le_bot_iff.mp hle

theorem ggSporK_component_data {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (h2 : CFSG.pCore 2 ↥H = ⊥) {J : Subgroup W}
    (hJ : IsComponentOf J H) :
    (∀ e ∈ E, ∀ x ∈ J, e * x * e⁻¹ ∈ J) ∧
      StandardType.LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) := by
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', h2]
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
    QuotientGroup.mk'_surjective _
  let Φ : ↥H ≃* GGHypQuot H :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨hinj, hsurj⟩
  have hΦ : ∀ y : ↥H, Φ y = QuotientGroup.mk' (CFSG.pCore 2 ↥H) y := fun _ => rfl
  have hsub : IsSubnormal (J.subgroupOf H) ⊤ :=
    IsSubnormal.of_mathlib ((IsSubnormal.iff_subgroupOf hJ.1).mp hJ.2.1)
  have hqs : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf H) :=
    gk0_quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hJ.1).symm hJ.2.2
  have hcomp : IsComponentOf (J.subgroupOf H) (⊤ : Subgroup ↥H) := ⟨le_top, hsub, hqs⟩
  have hC : IsComponentOf ((J.subgroupOf H).map Φ.toMonoidHom) (⊤ : Subgroup (GGHypQuot H)) := by
    have key : IsComponentOf ((J.subgroupOf H).map Φ.toMonoidHom)
        ((⊤ : Subgroup ↥H).map Φ.toMonoidHom) :=
      ⟨Subgroup.map_mono hcomp.1, hcomp.2.1.map Φ.toMonoidHom,
        gk0_quasisimple_of_equiv ((J.subgroupOf H).equivMapOfInjective Φ.toMonoidHom Φ.injective)
          hcomp.2.2⟩
    rwa [Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective] at key
  obtain ⟨hnorm, hmark⟩ := hyp.2.2.1 _ hC
  refine ⟨?_, ?_⟩
  · intro e he x hx
    have heH : e ∈ H := hEH he
    have hxH : x ∈ H := hJ.1 hx
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, heH⟩ : GGHypQuot H) ∈
        ggHypImage H E :=
      ⟨⟨e, heH⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
    have hxC : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ : GGHypQuot H) ∈
        (J.subgroupOf H).map Φ.toMonoidHom :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp (hnorm hmem) _).mp hxC
    obtain ⟨z, hz, hzeq⟩ := hconj
    have hzeq' : z = ⟨e, heH⟩ * ⟨x, hxH⟩ * ⟨e, heH⟩⁻¹ := by
      apply hinj
      rw [map_mul, map_mul, map_inv]
      exact hzeq
    have := Subgroup.mem_subgroupOf.mp hz
    rw [hzeq'] at this
    simpa using this
  · refine largeEvenMarking_true_of_mulEquiv ?_
      (largeEvenMarking_mono (fun _ _ _ _ _ _ _ => True.intro) hmark)
    exact ((Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans
      ((J.subgroupOf H).equivMapOfInjective Φ.toMonoidHom Φ.injective)).symm

end CFSG.StandardType.SporadicShape
