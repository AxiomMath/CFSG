module

public import CFSG.Quasithin.Background.SzG11B5cRank
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.G11BridgeSQTK
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.Quasithin.G11.SzG11S.B5c

theorem layer_layer_eq_top (Y : Type*) [Group Y] [Finite Y] :
    CFSG.layer ↥(CFSG.layer Y) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

theorem not_three_conjugates (hA21 : CFSG.Quasithin.AsA21SQTKSection) {Y S : Type} [Group Y]
    [Finite Y] [Group S] [Finite S] (hS : CFSG.Quasithin.SQTKGroup S) (φ : S →* Y)
    (hφ : Function.Surjective φ) {K : Subgroup Y} (hK : CFSG.IsComponent K) (y : Fin 3 → Y)
    (hne : ∀ i j, i ≠ j →
      K.map (MulAut.conj (y i)).toMonoidHom ≠ K.map (MulAut.conj (y j)).toMonoidHom) : False := by
  set E : Subgroup Y := CFSG.layer Y with hEdef
  have hlayerE : CFSG.layer ↥E = ⊤ := layer_layer_eq_top Y
  have hlayerQ : CFSG.layer (↥E ⧸ Subgroup.center ↥E) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hlayerE (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hlayerTop : CFSG.layer ↥(⊤ : Subgroup (↥E ⧸ Subgroup.center ↥E)) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hlayerQ
      (Subgroup.topEquiv (G := ↥E ⧸ Subgroup.center ↥E)).symm.toMonoidHom
      (Subgroup.topEquiv (G := ↥E ⧸ Subgroup.center ↥E)).symm.surjective
  let H : Subgroup S := E.comap φ
  let ρ : ↥H →* ↥E := (φ.comp H.subtype).codRestrict E (fun h => h.2)
  have hρ : Function.Surjective ρ := fun e => by
    obtain ⟨s, hs⟩ := hφ (e : Y)
    exact ⟨⟨s, show φ s ∈ E from hs ▸ e.2⟩, Subtype.ext hs⟩
  let π : ↥H →* (↥E ⧸ Subgroup.center ↥E) := (QuotientGroup.mk' (Subgroup.center ↥E)).comp ρ
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp hρ
  have key := hA21 S hS H _ π hπ ⊤ hlayerTop (by
    have : Subsingleton ((↥E ⧸ Subgroup.center ↥E) ⧸ (⊤ : Subgroup (↥E ⧸ Subgroup.center ↥E))) :=
      QuotientGroup.subsingleton_quotient_top
    exact IsPGroup.of_card (n := 0) (by rw [pow_zero]; exact Nat.card_unique))
  have hsqt := (CFSG.SectionRank.isStronglyQuasithin_iff.1
    (CFSG.Quasithin.G11.isStronglyQuasithin_of_tc key.1))
  obtain ⟨r, hr, hr2, a₀, b₀, hab₀, ha₀cen⟩ := B5c.exists_odd_prime_noncentral hK.1
  have : Fact r.Prime := ⟨hr⟩
  have hsq := hsqt r hr hr2
  set A : Y := (a₀ : Y) with hA
  set B : Y := (b₀ : Y) with hB
  let ai : Fin 3 → Y := fun i => y i * A * (y i)⁻¹
  let ti : Fin 3 → Y := fun i => y i * B * (y i)⁻¹
  have hKi : ∀ i, CFSG.IsComponent (K.map (MulAut.conj (y i)).toMonoidHom) := fun i =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (y i)) hK
  have hmemA : ∀ i, ai i ∈ K.map (MulAut.conj (y i)).toMonoidHom := fun i => ⟨A, a₀.2, rfl⟩
  have hmemB : ∀ i, ti i ∈ K.map (MulAut.conj (y i)).toMonoidHom := fun i => ⟨B, b₀.2, rfl⟩
  have hcommK : ∀ i j, i ≠ j → ∀ u ∈ K.map (MulAut.conj (y i)).toMonoidHom,
      ∀ v ∈ K.map (MulAut.conj (y j)).toMonoidHom, u * v = v * u := by
    intro i j hij u hu v hv
    rcases CFSG.LocalCores.distinct_components_commute (hKi i) (hKi j) with h | h
    · exact absurd h (hne i j hij)
    · have h1 := Subgroup.commutator_mem_commutator hu hv
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hEmemA : ∀ i, ai i ∈ E := fun i => CFSG.LocalCores.component_le_layer (hKi i) (hmemA i)
  have hEmemB : ∀ i, ti i ∈ E := fun i => CFSG.LocalCores.component_le_layer (hKi i) (hmemB i)
  have hcen0 : ∀ x ∈ E, A ^ r * x = x * A ^ r := by
    intro x hx
    have hmem : a₀ ^ r ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun g => (ha₀cen g).symm
    have h1 := CFSG.LocalCores.center_component_le_centralizer_layer hK ⟨_, hmem, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 h1 x hx).symm
  have hcenI : ∀ i, ∀ x ∈ E, ai i ^ r * x = x * ai i ^ r := by
    intro i x hx
    have hchar : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
    have hEn : E.Normal := Subgroup.normal_of_characteristic _
    have hnorm : (y i)⁻¹ * x * ((y i)⁻¹)⁻¹ ∈ E := hEn.conj_mem x hx _
    have h := hcen0 _ hnorm
    have hpow : ai i ^ r = y i * A ^ r * (y i)⁻¹ := conj_pow
    rw [hpow]
    calc y i * A ^ r * (y i)⁻¹ * x
        = y i * (A ^ r * ((y i)⁻¹ * x * ((y i)⁻¹)⁻¹)) * (y i)⁻¹ := by group
      _ = y i * (((y i)⁻¹ * x * ((y i)⁻¹)⁻¹) * A ^ r) * (y i)⁻¹ := by rw [h]
      _ = x * (y i * A ^ r * (y i)⁻¹) := by group
  let a : Fin 3 → ↥E := fun i => ⟨ai i, hEmemA i⟩
  let t : Fin 3 → ↥E := fun i => ⟨ti i, hEmemB i⟩
  have hacen : ∀ i, a i ^ r ∈ Subgroup.center ↥E := fun i =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcenI i g g.2).symm
  have hacomm : ∀ i j, Commute (a i) (a j) := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact Subtype.ext (hcommK i j hij _ (hmemA i) _ (hmemA j))
  have htcomm : ∀ i j, i ≠ j → Commute (t i) (a j) := fun i j hij =>
    Subtype.ext (hcommK i j hij _ (hmemB i) _ (hmemA j))
  have hta : ∀ i, ¬ Commute (t i) (a i) := fun i h => by
    have h1 : ti i * ai i = ai i * ti i := congrArg Subtype.val h
    apply hab₀
    apply Subtype.ext
    have h2 : (y i)⁻¹ * (ti i * ai i) * y i = (y i)⁻¹ * (ai i * ti i) * y i := by rw [h1]
    have h3 : B * A = A * B := by
      simpa [ai, ti, mul_assoc] using h2
    exact h3.symm
  have h3 := B5c.three_le_pRank_center_quotient a t hacen hacomm htcomm hta
  omega

end CFSG.Quasithin.G11.SzG11S.B5c
