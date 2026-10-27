module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockData
public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.CentralCover


@[expose] def A2BlockTwoInput : Prop :=
  ∀ {Ω : Type} [Field Ω] [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : Ω) = 0) (h3 : 3 ∣ q + 1)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL Tag.E6 Ω)} (hE : IsElemAbelian 3 E)
    (hEθ : E ≤ TwistedDiag.thetaFixed Fr)
    (hEX : E ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 2))),
    ∃ z ∈ TwistedDiag.thetaFixed Fr, ∀ e ∈ E,
      ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v)

theorem exists_zetaVec_eq_of_mem_thetaTorus {Ω : Type} [Field Ω] {q : ℕ}
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ TwistedDiag.thetaTorus Ω q) (hx3 : x ^ 3 = 1) :
    ∃ v, x = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by
  obtain ⟨b, -, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx
  have hb : b ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [← rootDiagUnit_pow, hx3, rootDiagUnit_one]
    exact DiagTorus.rootDiagUnit_injective h1
  obtain ⟨v, rfl⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb
  exact ⟨v, rfl⟩

theorem conj_mem_xHat_zpowers {Ω : Type} [Field Ω] {m x : ModGL Tag.E6 Ω}
    {g w : WeylGroup Tag.E6} (hm : m ∈ monoHat Tag.E6 Ω)
    (hmw : psiHat Tag.E6 Ω ⟨m, hm⟩ = w)
    (hx : x ∈ xHat Tag.E6 Ω (Subgroup.zpowers g)) :
    m * x * m⁻¹ ∈ xHat Tag.E6 Ω (Subgroup.zpowers (w * g * w⁻¹)) := by
  obtain ⟨hxM, hxψ⟩ := mem_xHat.1 hx
  have hmem : m * x * m⁻¹ ∈ monoHat Tag.E6 Ω := mul_mem (mul_mem hm hxM) (inv_mem hm)
  refine mem_xHat.2 ⟨hmem, ?_⟩
  have hsub : (⟨m * x * m⁻¹, hmem⟩ : monoHat Tag.E6 Ω) =
      ⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : monoHat Tag.E6 Ω)⁻¹ := Subtype.ext rfl
  rw [hsub, map_mul, map_mul, map_inv, hmw]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hxψ
  rw [← hn]
  have hcz : w * g ^ n * w⁻¹ = (w * g * w⁻¹) ^ n := by
    rw [show w * g ^ n * w⁻¹ = (MulAut.conj w) (g ^ n) from rfl, map_zpow]
    rfl
  rw [hcz]
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩

theorem exists_zetaVec_conj_inv_of_mem_normalizer {Ω : Type} [Field Ω] [IsAlgClosed Ω] {q : ℕ}
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {m : ModGL Tag.E6 Ω}
    (hm : m ∈ Subgroup.normalizer (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)))
    (v : Fin Tag.E6.rank → ZMod 3) :
    ∃ v', m⁻¹ * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * m =
      rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v') := by
  have hd3 : rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have h1 : TableBExc.E6Three.zetaVec ζ hζ v ^ 3 = 1 := by
      funext k
      show zmodPowHom ζ hζ (Multiplicative.ofAdd (v k)) ^ 3 = 1
      rw [zmodPowHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [h1, rootDiagUnit_one]
  have hTinv : m⁻¹ * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * m ∈
      torusGroup Tag.E6 Ω :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hm) _).1 (rootDiagUnit_mem_torusGroup _)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hTinv
  have hconj3 : (m⁻¹ * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * m) ^ 3 = 1 := by
    have h := conj_pow (a := m⁻¹)
      (b := rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v)) (i := 3)
    rw [inv_inv] at h
    rw [h, hd3, mul_one, inv_mul_cancel]
  rw [hb] at hconj3
  have hb3 : b ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [← rootDiagUnit_pow, hconj3, rootDiagUnit_one]
    exact DiagTorus.rootDiagUnit_injective h1
  obtain ⟨v', hv'⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb3
  exact ⟨v', by rw [hb, hv']⟩

theorem cE6_pow_two_conj_zero : cE6 ^ 2 * gE6 0 * (cE6 ^ 2)⁻¹ = gE6 2 := by
  rw [sq]
  calc cE6 * cE6 * gE6 0 * (cE6 * cE6)⁻¹
      = cE6 * (cE6 * gE6 0 * cE6⁻¹) * cE6⁻¹ := by group
    _ = gE6 2 := by
      rw [cE6_conj, cE6_conj]
      rfl

theorem exists_thetaFixed_conj_of_kernel {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : (q : Ω) = 0) (h3 : 3 ∣ q + 1)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (i : Fin 3)
    {E : Subgroup (ModGL Tag.E6 Ω)} (hE : IsElemAbelian 3 E)
    (hEθ : E ≤ TwistedDiag.thetaFixed Fr)
    (hEX : E ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 i)))
    (hE1 : ∀ e ∈ E, ∀ (he : e ∈ monoHat Tag.E6 Ω), psiHat Tag.E6 Ω ⟨e, he⟩ = 1) :
    ∃ z ∈ TwistedDiag.thetaFixed Fr, ∀ e ∈ E,
      ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by
  have htorus : ∀ e ∈ E, e ∈ TwistedDiag.thetaTorus Ω q := by
    intro e he
    obtain ⟨heM, -⟩ := mem_xHat.1 (hEX he)
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (hE1 e he heM)
    rw [← TwistedDiag.torus_inf_thetaFixed Fr hFr]
    exact ⟨rootDiagUnit_mem_torusGroup b, (hEθ he).1, (hEθ he).2⟩
  refine ⟨1, TwistedDiag.thetaFixed Fr |>.one_mem, ?_⟩
  intro e he
  have hx3 : e ^ 3 = 1 := hE.2 e he
  obtain ⟨v, hv⟩ := exists_zetaVec_eq_of_mem_thetaTorus (q := q) hζ hζo (htorus e he) hx3
  exact ⟨v, by rw [one_mul, inv_one, mul_one, hv]⟩

theorem exists_thetaFixed_conj_of_cyclic (hblock : A2BlockTwoInput)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : Ω) = 0) (h3 : 3 ∣ q + 1)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (i : Fin 3)
    {E : Subgroup (ModGL Tag.E6 Ω)} (hE : IsElemAbelian 3 E)
    (hEθ : E ≤ TwistedDiag.thetaFixed Fr)
    (hEX : E ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 i))) :
    ∃ z ∈ TwistedDiag.thetaFixed Fr, ∀ e ∈ E,
      ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by
  classical
  obtain ⟨mc, hmcM, hmcθ⟩ := TwistedDiag.exists_lift Fr hFr cE6
  have hmcMono : mc ∈ monomialSubgroup Tag.E6 Ω := hmcM.1
  have hmcθF : mc ∈ TwistedDiag.thetaFixed Fr := hmcM.2
  have hmcHat : mc ∈ monoHat Tag.E6 Ω := monomial_le_monoHat hmcMono
  have hmcψ : psiHat Tag.E6 Ω ⟨mc, hmcHat⟩ = cE6 := psiHat_eq hmcθ
  have hnorm : mc ∈ Subgroup.normalizer (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) :=
    mem_normalizer_torusGroup_of_mem_monomialSubgroup hmcMono
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  ·
    set m : ModGL Tag.E6 Ω := mc ^ 2 with hmdef
    have hmθ : m ∈ TwistedDiag.thetaFixed Fr := pow_mem hmcθF 2
    have hmMono : m ∈ monomialSubgroup Tag.E6 Ω := pow_mem hmcMono 2
    have hmHat : m ∈ monoHat Tag.E6 Ω := monomial_le_monoHat hmMono
    have hmψ : psiHat Tag.E6 Ω ⟨m, hmHat⟩ = cE6 ^ 2 := by
      have h1 : (⟨m, hmHat⟩ : monoHat Tag.E6 Ω) = (⟨mc, hmcHat⟩ : monoHat Tag.E6 Ω) ^ 2 := by
        refine Subtype.ext ?_
        change mc ^ 2 = (↑((⟨mc, hmcHat⟩ : monoHat Tag.E6 Ω) ^ 2) : ModGL Tag.E6 Ω)
        rw [Subgroup.coe_pow]
      rw [h1, map_pow, hmcψ]
    have hmNorm : m ∈ Subgroup.normalizer (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) :=
      mem_normalizer_torusGroup_of_mem_monomialSubgroup hmMono
    set E' : Subgroup (ModGL Tag.E6 Ω) := E.map (MulAut.conj m).toMonoidHom with hE'def
    have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE _
    have hE'θ : E' ≤ TwistedDiag.thetaFixed Fr := by
      rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem hmθ (hEθ he)) (inv_mem hmθ)
    have hE'X : E' ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 2)) := by
      rintro _ ⟨e, he, rfl⟩
      have h1 := conj_mem_xHat_zpowers hmHat hmψ (hEX he)
      rwa [cE6_pow_two_conj_zero] at h1
    obtain ⟨z', hz'θ, hz'⟩ := hblock hFr hq h3 hζ hζo hE' hE'θ hE'X
    refine ⟨m⁻¹ * z' * m, mul_mem (mul_mem (inv_mem hmθ) hz'θ) hmθ, ?_⟩
    intro e he
    have hmem : m * e * m⁻¹ ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨v, hv⟩ := hz' _ hmem
    have hconj : m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
        m⁻¹ * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * m := by
      rw [show m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
        m⁻¹ * (z' * (m * e * m⁻¹) * z'⁻¹) * m by group, hv]
    rw [hconj]
    exact exists_zetaVec_conj_inv_of_mem_normalizer (q := q) hζ hζo hmNorm v
  ·
    set m : ModGL Tag.E6 Ω := mc with hmdef
    have hmθ : m ∈ TwistedDiag.thetaFixed Fr := hmcθF
    have hmMono : m ∈ monomialSubgroup Tag.E6 Ω := hmcMono
    have hmHat : m ∈ monoHat Tag.E6 Ω := hmcHat
    have hmψ : psiHat Tag.E6 Ω ⟨m, hmHat⟩ = cE6 := hmcψ
    have hmNorm : m ∈ Subgroup.normalizer (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) := hnorm
    set E' : Subgroup (ModGL Tag.E6 Ω) := E.map (MulAut.conj m).toMonoidHom with hE'def
    have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE _
    have hE'θ : E' ≤ TwistedDiag.thetaFixed Fr := by
      rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem hmθ (hEθ he)) (inv_mem hmθ)
    have hE'X : E' ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 2)) := by
      rintro _ ⟨e, he, rfl⟩
      have h1 := conj_mem_xHat_zpowers hmHat hmψ (hEX he)
      rw [cE6_conj] at h1
      have hpi : TableBExc.Three.piE7 1 = 2 := rfl
      rw [hpi] at h1
      exact h1
    obtain ⟨z', hz'θ, hz'⟩ := hblock hFr hq h3 hζ hζo hE' hE'θ hE'X
    refine ⟨m⁻¹ * z' * m, mul_mem (mul_mem (inv_mem hmθ) hz'θ) hmθ, ?_⟩
    intro e he
    have hmem : m * e * m⁻¹ ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨v, hv⟩ := hz' _ hmem
    have hconj : m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
        m⁻¹ * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * m := by
      rw [show m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
        m⁻¹ * (z' * (m * e * m⁻¹) * z'⁻¹) * m by group, hv]
    rw [hconj]
    exact exists_zetaVec_conj_inv_of_mem_normalizer (q := q) hζ hζo hmNorm v
  ·
    obtain ⟨z, hzθ, hz⟩ := hblock hFr hq h3 hζ hζo hE hEθ hEX
    exact ⟨z, hzθ, hz⟩

end CFSG.StandardType.NoOffTwE6Three
