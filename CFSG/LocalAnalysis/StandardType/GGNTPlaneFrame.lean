module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneNormalForm
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneUntw
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneRetoralExact
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rcf_map_conj_centralizer {G : Type} [Group G] (g : G) (D : Subgroup G) :
    (Subgroup.centralizer (D : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    have h := Subgroup.mem_centralizer_iff.mp hy w hw
    show g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have h := hx (g * w * g⁻¹) (Subgroup.mem_map.2 ⟨w, hw, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩)
      show w * (g⁻¹ * x * g) = g⁻¹ * x * g * w
      calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * x * g * w := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem rcf_ggCompFieldAt_congr {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {Y : Subgroup H} {Q : ℕ}
    (h : GGCompFieldAt Q X) (θ : ↥X ≃* ↥Y) : GGCompFieldAt Q Y := by
  obtain ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas, R, instR, hR, ⟨φ⟩⟩ := h
  letI : Group R := instR
  have hq : (↥X ⧸ Subgroup.center ↥X) ≃* (↥Y ⧸ Subgroup.center ↥Y) :=
    QuotientGroup.congr _ _ θ (Subgroup.map_center_eq θ)
  have hhas' : GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    unfold GGHasLabel at hhas ⊢
    refine largeEvenRawDatum_mono ?_ hhas
    rintro R' _ I F ⟨ψ⟩
    exact ⟨hq.symm.trans ψ⟩
  exact ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas', R, instR, hR, ⟨hq.symm.trans φ⟩⟩

theorem ntp_frame
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (hAlg : S.IsAlgebraic)
    (D : Subgroup (ModGL .E6 L)) (hD : D ≤ S.D.model) (habel : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2)
    (hnt : ¬ ∃ g ∈ adjointGroup .E6 L, ∀ x ∈ D, g⁻¹ * x * g ∈ torusGroup .E6 L)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (D : Set (ModGL .E6 L)))) :
    ∃ (S' : LangSetup .E6 L p₀) (D' : Subgroup (ModGL .E6 L))
      (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) (K' : Subgroup (ModGL .E6 L)),
      S'.D.q = S.D.q ∧ ntpNormalForm S' D' a n ∧
        IsComponentOf K' (S'.Γ ⊓ Subgroup.centralizer (D' : Set (ModGL .E6 L))) ∧
        (GGCompFieldAt S.D.q K ↔ GGCompFieldAt S'.D.q K') ∧
        Nat.card K = Nat.card K' ∧
        Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
  classical
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff S.D.q).1 S.hqpow.1
  have h2dvd : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
  have hp2 : p = 2 := by
    have h2pk : 2 ∣ p ^ k := by rwa [← hpk] at h2dvd
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2pk)).symm
  have hq : S.D.q = 2 ^ k := by rw [← hpk, hp2]
  have hf : 1 ≤ k := hk
  obtain ⟨_, halgZ⟩ := S.exists_charP_isAlgebraic_zmod hAlg Nat.prime_two hk hq
  obtain ⟨Fr, hFr, P, hP, hΦP⟩ := S.D.steinberg
  have hFr2 : ∀ c, Fr c = c ^ (2 ^ k) := fun c => by rw [hFr c, hq]
  obtain ⟨x₀, hx₀D, hx₀1⟩ : ∃ x ∈ D, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one D with hbot | h
    · exfalso
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    · exact h
  have hA : D ≤ adjointGroup Tag.E6 L := fun x hx => ((LangDatum.mem_model S.D).1 (hD hx)).1
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (habel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ D, x ^ 3 = 1 := habel.2
  have hnt' : ¬ ∃ C ∈ adjointGroup Tag.E6 L, ∀ x ∈ D, C * x * C⁻¹ ∈ torusGroup Tag.E6 L := by
    rintro ⟨C, hC, hCD⟩
    exact hnt ⟨C⁻¹, inv_mem hC, fun x hx => by
      have h := hCD x hx
      simpa only [inv_inv] using h⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hC, a, m, ha3, hCx, hCD, hm, hm3, hma, hstab, hnotker⟩ :=
    plane_nontoral_normal_form (p := 3) (ℓ := 2) (τ := Tag.E6)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_E6_three
      (show (2 : ℕ) ≠ 3 by norm_num) halgZ hA hcomm hexp hcard hnt' hx₀D hx₀1
  have hdatum : ∃ D' : LangDatum Tag.E6 L, D'.q = S.D.q ∧ D'.Φ = S.D.Φ ∧ Finite D'.model ∧
      D'.model = S.D.model.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      (D'.g0⁻¹ * S.D.g0) * x₀ * (D'.g0⁻¹ * S.D.g0)⁻¹ = rootDiagUnit Tag.E6 a ∧
      rootDiagUnit Tag.E6 a ∈ D'.torus := by
    rcases hP with hP1 | ⟨t, ht, hPt⟩
    · have hΦ : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext g
        rw [hΦP g, hP1]
        simp
      exact ntp_untw_retoralize_exact k hf S hq hAlg Fr hFr2 hΦ ⟨x₀, hD hx₀D⟩ hC hCx
    · cases t with
      | E6 =>
        have hd : diagramAt Tag.E6 L TwistTag.E6 ht = diagramMap TwistTag.E6 L := by
          cases ht; rfl
        have hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr := by
          ext g
          rw [hΦP g, hPt, hd]
          rfl
        exact twE6_model_retoralize_exact k hf S hq hAlg Fr hFr2 hΦ ⟨x₀, hD hx₀D⟩ hC hCx
      | D4 => exact absurd ht (by decide)
  obtain ⟨D', hD'q, _hD'Φ, hfin, hD'model, hD'Γ, hc'x, hd_torus⟩ := hdatum
  set c' : ModGL Tag.E6 L := D'.g0⁻¹ * S.D.g0 with hc'def
  have hc'C : c' ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem D'.g0_mem) S.D.g0_mem
  set z : ModGL Tag.E6 L := C * c'⁻¹ with hzdef
  have hzC : z ∈ adjointGroup Tag.E6 L := mul_mem hC (inv_mem hc'C)
  have hzc' : z⁻¹ * C = c' := by rw [hzdef]; group
  have hz_da : z * rootDiagUnit Tag.E6 a * z⁻¹ = rootDiagUnit Tag.E6 a := by
    have h1 : c'⁻¹ * rootDiagUnit Tag.E6 a * c' = x₀ := by
      rw [← hc'x]; group
    calc z * rootDiagUnit Tag.E6 a * z⁻¹
        = C * (c'⁻¹ * rootDiagUnit Tag.E6 a * c') * C⁻¹ := by rw [hzdef]; group
      _ = C * x₀ * C⁻¹ := by rw [h1]
      _ = rootDiagUnit Tag.E6 a := hCx
  have hz_da' : z⁻¹ * rootDiagUnit Tag.E6 a * z = rootDiagUnit Tag.E6 a := by
    calc z⁻¹ * rootDiagUnit Tag.E6 a * z
        = z⁻¹ * (z * rootDiagUnit Tag.E6 a * z⁻¹) * z := by rw [hz_da]
      _ = rootDiagUnit Tag.E6 a := by group
  have hz_da_inv : z⁻¹ * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * z⁻¹ := by
    calc z⁻¹ * rootDiagUnit Tag.E6 a = z⁻¹ * rootDiagUnit Tag.E6 a * z * z⁻¹ := by group
      _ = rootDiagUnit Tag.E6 a * z⁻¹ := by rw [hz_da']
  have hz_da_comm : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a := by
    calc rootDiagUnit Tag.E6 a * z = z * (z⁻¹ * rootDiagUnit Tag.E6 a * z) := by group
      _ = z * rootDiagUnit Tag.E6 a := by rw [hz_da']
  let D'' : Subgroup (ModGL Tag.E6 L) := D.map (MulAut.conj c').toMonoidHom
  let n'' : ModGL Tag.E6 L := z⁻¹ * m * z
  let K' : Subgroup (ModGL Tag.E6 L) := K.map (MulAut.conj c').toMonoidHom
  have hD''eq : D'' = Subgroup.zpowers (rootDiagUnit Tag.E6 a) ⊔ Subgroup.zpowers n'' := by
    have hcomp : (MulAut.conj z⁻¹).toMonoidHom.comp (MulAut.conj C).toMonoidHom =
        (MulAut.conj c').toMonoidHom := by
      ext x : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, ← hzc']
      group
    have hzp1 : Subgroup.zpowers ((MulAut.conj z⁻¹) (rootDiagUnit Tag.E6 a)) =
        Subgroup.zpowers (rootDiagUnit Tag.E6 a) := by
      rw [MulAut.conj_apply, inv_inv, hz_da']
    have hzp2 : Subgroup.zpowers ((MulAut.conj z⁻¹) m) = Subgroup.zpowers n'' := by
      rw [MulAut.conj_apply, inv_inv]
    calc D'' = D.map (MulAut.conj c').toMonoidHom := rfl
      _ = D.map ((MulAut.conj z⁻¹).toMonoidHom.comp (MulAut.conj C).toMonoidHom) := by
          rw [hcomp]
      _ = (D.map (MulAut.conj C).toMonoidHom).map (MulAut.conj z⁻¹).toMonoidHom := by
          rw [Subgroup.map_map]
      _ = (Subgroup.zpowers (rootDiagUnit Tag.E6 a) ⊔ Subgroup.zpowers m).map
            (MulAut.conj z⁻¹).toMonoidHom := by rw [hCD]
      _ = Subgroup.zpowers (rootDiagUnit Tag.E6 a) ⊔ Subgroup.zpowers n'' := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
          simp only [MulEquiv.coe_toMonoidHom]
          rw [hzp1, hzp2]
  have hda_ne : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro h
    apply hx₀1
    have h2 : C * x₀ * C⁻¹ = 1 := by rw [hCx, h]
    calc x₀ = C⁻¹ * (C * x₀ * C⁻¹) * C := by group
      _ = 1 := by rw [h2]; group
  have hn''3 : n'' ^ 3 = 1 := by
    have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.conj_pow_eq_one' z⁻¹ hm3
    rwa [inv_inv] at h
  have hcomm'' : rootDiagUnit Tag.E6 a * n'' = n'' * rootDiagUnit Tag.E6 a := by
    change rootDiagUnit Tag.E6 a * (z⁻¹ * m * z) = (z⁻¹ * m * z) * rootDiagUnit Tag.E6 a
    calc rootDiagUnit Tag.E6 a * (z⁻¹ * m * z)
        = (rootDiagUnit Tag.E6 a * z⁻¹) * m * z := by group
      _ = (z⁻¹ * rootDiagUnit Tag.E6 a) * m * z := by rw [hz_da_inv]
      _ = z⁻¹ * (rootDiagUnit Tag.E6 a * m) * z := by group
      _ = z⁻¹ * (m * rootDiagUnit Tag.E6 a) * z := by rw [hma]
      _ = z⁻¹ * m * (rootDiagUnit Tag.E6 a * z) := by group
      _ = z⁻¹ * m * (z * rootDiagUnit Tag.E6 a) := by rw [hz_da_comm]
      _ = (z⁻¹ * m * z) * rootDiagUnit Tag.E6 a := by group
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L D'
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D'.q := by rw [hD'q]; exact S.hq
  have hqpow' : IsPrimePow D'.q ∧ ((D'.q : ℕ) : L) = 0 := by rw [hD'q]; exact S.hqpow
  have hpq' : ¬ p₀ ∣ D'.q := by rw [hD'q]; exact S.hpq
  let S' : LangSetup Tag.E6 L p₀ := D'.toSetup p₀ ρ hρ S.hp hq' hqpow' hpq' hfin
  have hS'q : S'.D.q = S.D.q := by show D'.q = S.D.q; exact hD'q
  have hnormal : ntpNormalForm S' D'' a n'' := by
    refine ⟨fun i => ha3 i, ?_, hda_ne, ?_, hn''3, hcomm'', hD''eq, ?_⟩
    · show rootDiagUnit Tag.E6 a ∈ D'.torus
      exact hd_torus
    · show D'' ≤ D'.model
      rw [hD'model]
      exact Subgroup.map_mono hD
    · exact ⟨z, m, hm, hzC, by change z * (z⁻¹ * m * z) * z⁻¹ = m; group, hz_da, hstab, hnotker⟩
  have hS'Γ : S'.Γ = S.Γ.map (MulAut.conj c').toMonoidHom := by
    rw [show S'.Γ = D'.Γ from rfl, hD'Γ]
  have hK' : IsComponentOf K' (S'.Γ ⊓ Subgroup.centralizer (D'' : Set (ModGL Tag.E6 L))) := by
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj c') hK
    have heq : S'.Γ ⊓ Subgroup.centralizer (D'' : Set (ModGL Tag.E6 L)) =
        (S.Γ ⊓ Subgroup.centralizer (D : Set (ModGL Tag.E6 L))).map
          (MulAut.conj c').toMonoidHom := by
      rw [hS'Γ]
      rw [show D'' = D.map (MulAut.conj c').toMonoidHom from rfl,
        ← rcf_map_conj_centralizer c' D,
        ← Subgroup.map_inf S.Γ (Subgroup.centralizer (D : Set (ModGL Tag.E6 L)))
          (MulAut.conj c').toMonoidHom (MulAut.conj c').injective]
    rw [heq]
    exact h
  have hK'iso : K ≃* K' :=
    K.equivMapOfInjective (MulAut.conj c').toMonoidHom (MulAut.conj c').injective
  have hfield : GGCompFieldAt S.D.q K ↔ GGCompFieldAt S'.D.q K' := by
    rw [hS'q]
    exact ⟨fun h => rcf_ggCompFieldAt_congr h hK'iso,
      fun h => rcf_ggCompFieldAt_congr h hK'iso.symm⟩
  have hcardK : Nat.card K = Nat.card K' := by
    show Nat.card K = Nat.card (K.map (MulAut.conj c').toMonoidHom)
    exact (Subgroup.card_map_of_injective (K := K) (f := (MulAut.conj c').toMonoidHom)
      (MulAut.conj c').injective).symm
  have hcardQ : Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
    refine Nat.card_congr ?_
    exact (QuotientGroup.congr (Subgroup.center K) (Subgroup.center K') hK'iso
      (Subgroup.map_center_eq hK'iso)).toEquiv
  exact ⟨S', D'', a, n'', K', hS'q, hnormal, hK', hfield, hcardK, hcardQ⟩

end CFSG.StandardType.NTPlane

end
