module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeClass

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.StandardType.Triality CFSG.StandardType.TriBridge

theorem ntpD4_rat_untwisted
    {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 : ℕ) ^ f)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra F L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f))
    (G₀ : Subgroup (ModGL Tag.D4 L))
    (hG₀ : G₀ = adjointGroup Tag.D4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hdesc : G₀ = (adjointGroup Tag.D4 F).map (baseChangeGL (algebraMap F L)))
    (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      Units.map (entrywiseHom Fr) ((g : ModGL Tag.D4 L) *
          (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * Units.map (entrywiseHom Fr) x * (d4P L ^ ε)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹) :
    ∃ (e : ↥G₀ ≃* Om8 F) (γ : Om8 F) (ε' : ℤ), (ε' = 1 ∨ ε' = -1) ∧
      (∀ x : ↥G₀, ∃ y : ↥G₀, (y : ModGL Tag.D4 L) = (g : ModGL Tag.D4 L) *
        (d4P L ^ ε * (x : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) ∧
      ∀ x y : ↥G₀, (y : ModGL Tag.D4 L) = (g : ModGL Tag.D4 L) *
          (d4P L ^ ε * (x : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹ →
        e y = (MulAut.conj γ * theta ^ ε' : MulAut (Om8 F)) (e x) := by
  classical
  have hFr_surj : Function.Surjective Fr := by
    intro y
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos two_pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  let FrE : L ≃+* L := RingEquiv.ofBijective Fr ⟨Fr.injective, hFr_surj⟩
  have hcomp : Fr.comp FrE.symm.toRingHom = RingHom.id L := by
    ext c
    change Fr (FrE.symm c) = c
    exact RingEquiv.apply_symm_apply FrE c
  have hFrSurjA : ∀ y ∈ adjointGroup Tag.D4 L,
      ∃ x ∈ adjointGroup Tag.D4 L, Units.map (entrywiseHom Fr) x = y := by
    intro y hy
    refine ⟨Units.map (entrywiseHom FrE.symm.toRingHom) y, ?_, ?_⟩
    · exact CFSG.LieType.Ree.entrywiseGL_mem (σ := FrE.symm.toRingHom) hy
    · have hmap := units_map_entrywiseHom_comp (t := TwistTag.D4) (K := L) (σ := Fr)
        FrE.symm.toRingHom y
      exact hmap.trans (by rw [hcomp]; exact Units.ext (entrywise_id (τ := Tag.D4) (R := L) y))
  have hFrP : Units.map (entrywiseHom Fr) (d4P L ^ ε) = d4P L ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (K := L) (σ := Fr))
  have hconj : ∀ y ∈ adjointGroup Tag.D4 L,
      Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) *
          (d4P L ^ ε * y * (d4P L ^ ε)⁻¹) *
          (Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L))⁻¹ =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * y * (d4P L ^ ε)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹ := by
    intro y hy
    obtain ⟨x, hx, hxFr⟩ := hFrSurjA y hy
    have h := hcomm x hx
    simp only [map_mul, map_inv, hFrP, hxFr] at h
    exact h
  have hconj_all : ∀ z ∈ adjointGroup Tag.D4 L,
      Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) * z *
          (Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L))⁻¹ =
        (g : ModGL Tag.D4 L) * z * (g : ModGL Tag.D4 L)⁻¹ := by
    intro z hz
    let y : adjointGroup Tag.D4 L := (d4Graph L ε).symm ⟨z, hz⟩
    have hyz : d4P L ^ ε * (y : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹ = z := by
      rw [← coe_d4Graph ε y]
      exact congrArg Subtype.val (MulEquiv.apply_symm_apply (d4Graph L ε) ⟨z, hz⟩)
    have h := hconj y y.2
    rwa [hyz] at h
  have hFr_g : Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) = (g : ModGL Tag.D4 L) := by
    set c : ModGL Tag.D4 L := (g : ModGL Tag.D4 L)⁻¹ *
      Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) with hcdef
    have hc_mem : c ∈ adjointGroup Tag.D4 L :=
      mul_mem (inv_mem g.2) (CFSG.LieType.Ree.entrywiseGL_mem (σ := Fr) g.2)
    have hcen : (⟨c, hc_mem⟩ : adjointGroup Tag.D4 L) ∈
        Subgroup.center (adjointGroup Tag.D4 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      have hz : c * (z : ModGL Tag.D4 L) * c⁻¹ = (z : ModGL Tag.D4 L) := by
        have h := hconj_all (z : ModGL Tag.D4 L) z.2
        calc c * (z : ModGL Tag.D4 L) * c⁻¹ =
            (g : ModGL Tag.D4 L)⁻¹ *
              (Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) * (z : ModGL Tag.D4 L) *
                (Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L))⁻¹) *
              (g : ModGL Tag.D4 L) := by rw [hcdef]; group
          _ = (g : ModGL Tag.D4 L)⁻¹ *
                ((g : ModGL Tag.D4 L) * (z : ModGL Tag.D4 L) * (g : ModGL Tag.D4 L)⁻¹) *
                (g : ModGL Tag.D4 L) := by rw [h]
          _ = (z : ModGL Tag.D4 L) := by group
      have hcz : c * (z : ModGL Tag.D4 L) = (z : ModGL Tag.D4 L) * c := by
        calc c * (z : ModGL Tag.D4 L) =
            (c * (z : ModGL Tag.D4 L) * c⁻¹) * c := by group
          _ = (z : ModGL Tag.D4 L) * c := by rw [hz]
      exact hcz.symm
    rw [center_adjointGroup_eq_bot_field Tag.D4 L, Subgroup.mem_bot] at hcen
    have hc_one : c = 1 := congrArg Subtype.val hcen
    calc Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) =
        (g : ModGL Tag.D4 L) * c := by rw [hcdef]; group
      _ = (g : ModGL Tag.D4 L) * 1 := by rw [hc_one]
      _ = (g : ModGL Tag.D4 L) := mul_one _
  have hg₀ : (g : ModGL Tag.D4 L) ∈ G₀ := by
    rw [hG₀]
    exact Subgroup.mem_inf.2 ⟨g.2, hFr_g⟩
  let ι : ModGL Tag.D4 F →* ModGL Tag.D4 L := baseChangeGL (algebraMap F L)
  let b : Om8 F ≃* adjointGroup Tag.D4 F := bridge (K := F)
  let e₁ : adjointGroup Tag.D4 F ≃* ↥G₀ :=
    ((adjointGroup Tag.D4 F).equivMapOfInjective ι
      (baseChangeGL_injective (algebraMap F L))).trans (MulEquiv.subgroupCongr hdesc.symm)
  let e : ↥G₀ ≃* Om8 F := (b.trans e₁).symm
  have hcoe₁ : ∀ y : adjointGroup Tag.D4 F,
      ((e₁ y : ↥G₀) : ModGL Tag.D4 L) = ι (↑y) := by
    intro y
    rfl
  have hcoe : ∀ z : Om8 F, ((e.symm z : ↥G₀) : ModGL Tag.D4 L) = ι (↑(b z)) := by
    intro z
    have h1 : e.symm z = e₁ (b z) := by
      change (((b.trans e₁).symm).symm) z = e₁ (b z)
      rw [MulEquiv.symm_symm, MulEquiv.trans_apply]
    rw [h1, hcoe₁]
  let γ : Om8 F := e ⟨(g : ModGL Tag.D4 L), hg₀⟩
  have hγcoe : ι (↑(b γ)) = (g : ModGL Tag.D4 L) := by
    rw [← hcoe γ]
    have hγ : e.symm γ = (⟨(g : ModGL Tag.D4 L), hg₀⟩ : ↥G₀) := by
      simp only [γ, MulEquiv.symm_apply_apply]
    rw [hγ]
  have hιP : ι (d4P F) = d4P L := by
    show baseChangeGL (algebraMap F L) (diagramMap TwistTag.D4 F) =
      diagramMap TwistTag.D4 L
    exact baseChangeGL_diagramMap (t := TwistTag.D4) (f := algebraMap F L)
  have hbθ : ∀ z : Om8 F,
      (↑(b (theta z)) : ModGL Tag.D4 F) =
        (bridge (theta z) : ModGL TwistTag.D4.tag F) := fun z => rfl
  have hbz : ∀ z : Om8 F,
      (↑(b z) : ModGL Tag.D4 F) = (bridge z : ModGL TwistTag.D4.tag F) := fun z => rfl
  have hbridge_theta : ∀ z : Om8 F,
      ι (↑(b (theta z))) = d4P L * ι (↑(b z)) * (d4P L)⁻¹ := by
    intro z
    calc ι (↑(b (theta z)))
        = ι (d4P F * (↑(b z) : ModGL Tag.D4 F) * (d4P F)⁻¹) := by
              rw [hbθ z, coe_bridge_theta (K := F) z, ← hbz z]
              rfl
      _ = d4P L * ι (↑(b z)) * (d4P L)⁻¹ := by
              rw [map_mul, map_mul, map_inv, hιP]
  have hpow : ∀ (n : ℕ) (z : Om8 F),
      ι (↑(b ((theta ^ n) z))) =
        d4P L ^ n * ι (↑(b z)) * (d4P L ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp [ι]
    | succ n ih =>
        intro z
        have hθn : ((theta : MulAut (Om8 F)) ^ (n + 1)) z =
            theta (((theta : MulAut (Om8 F)) ^ n) z) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [hθn]
        calc ι (↑(b (theta ((theta ^ n) z))))
            = d4P L * ι (↑(b ((theta ^ n) z))) * (d4P L)⁻¹ := hbridge_theta _
          _ = d4P L * (d4P L ^ n * ι (↑(b z)) * (d4P L ^ n)⁻¹) *
                (d4P L)⁻¹ := by rw [ih z]
          _ = d4P L ^ (n + 1) * ι (↑(b z)) * (d4P L ^ (n + 1))⁻¹ := by
              rw [pow_succ']
              group
  have hb_mem : ∀ z : Om8 F, ι (↑(b z)) ∈ G₀ := by
    intro z
    rw [hdesc]
    exact Subgroup.mem_map_of_mem ι ((b z).2)
  have hfinal : ∀ (n : ℕ) (ε' : ℤ),
      (theta : MulAut (Om8 F)) ^ ε' = (theta : MulAut (Om8 F)) ^ n →
      (∀ x : ↥G₀, ∃ y : ↥G₀, (y : ModGL Tag.D4 L) =
        (g : ModGL Tag.D4 L) * (d4P L ^ n * (x : ModGL Tag.D4 L) * (d4P L ^ n)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹) ∧
      (∀ x y : ↥G₀, (y : ModGL Tag.D4 L) =
        (g : ModGL Tag.D4 L) * (d4P L ^ n * (x : ModGL Tag.D4 L) * (d4P L ^ n)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹ →
        e y = (MulAut.conj γ * theta ^ ε' : MulAut (Om8 F)) (e x)) := by
    intro n ε' hθ
    have hxcoe : ∀ x : ↥G₀, (x : ModGL Tag.D4 L) = ι (↑(b (e x))) := by
      intro x
      rw [← hcoe (e x), MulEquiv.symm_apply_apply]
    have hstep : ∀ x : ↥G₀,
        d4P L ^ n * (x : ModGL Tag.D4 L) * (d4P L ^ n)⁻¹ =
          ι (↑(b ((theta ^ n) (e x)))) := by
      intro x
      rw [hxcoe x]
      exact (hpow n (e x)).symm
    constructor
    · intro x
      have hmem : d4P L ^ n * (x : ModGL Tag.D4 L) * (d4P L ^ n)⁻¹ ∈ G₀ := by
        rw [hstep x]
        exact hb_mem ((theta ^ n) (e x))
      exact ⟨⟨(g : ModGL Tag.D4 L) *
          (d4P L ^ n * (x : ModGL Tag.D4 L) * (d4P L ^ n)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹,
          mul_mem (mul_mem hg₀ hmem) (inv_mem hg₀)⟩, rfl⟩
    · intro x y hy
      have hbridge_conj : (↑(b (MulAut.conj γ ((theta ^ n) (e x)))) :
          ModGL Tag.D4 F) =
          (↑(b γ) : ModGL Tag.D4 F) *
            (↑(b ((theta ^ n) (e x))) : ModGL Tag.D4 F) *
            ((↑(b γ) : ModGL Tag.D4 F))⁻¹ := by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
        rfl
      have hyval : (y : ModGL Tag.D4 L) =
          ι (↑(b (MulAut.conj γ ((theta ^ ε') (e x))))) := by
        rw [hy, hstep x]
        calc (g : ModGL Tag.D4 L) * ι (↑(b ((theta ^ n) (e x)))) *
              (g : ModGL Tag.D4 L)⁻¹
            = ι (↑(b γ)) * ι (↑(b ((theta ^ n) (e x)))) *
                (ι (↑(b γ)))⁻¹ := by rw [← hγcoe]
          _ = ι ((↑(b γ) : ModGL Tag.D4 F) *
                (↑(b ((theta ^ n) (e x))) : ModGL Tag.D4 F) *
                ((↑(b γ) : ModGL Tag.D4 F))⁻¹) := by
                  rw [← map_inv, ← map_mul, ← map_mul]
          _ = ι (↑(b (MulAut.conj γ ((theta ^ n) (e x))))) := by rw [hbridge_conj]
          _ = ι (↑(b (MulAut.conj γ ((theta ^ ε') (e x))))) := by rw [hθ]
      have hsub : y = e.symm (MulAut.conj γ ((theta ^ ε') (e x))) := by
        apply Subtype.ext
        rw [hyval, hcoe (MulAut.conj γ ((theta ^ ε') (e x)))]
      have hw : e y = MulAut.conj γ ((theta ^ ε') (e x)) := by
        rw [hsub, MulEquiv.apply_symm_apply]
      rw [hw, MulAut.mul_apply]
  rcases hε with rfl | rfl
  · have hθ1 : (theta : MulAut (Om8 F)) ^ (1 : ℤ) =
        (theta : MulAut (Om8 F)) ^ (1 : ℕ) := by rw [zpow_one, pow_one]
    exact ⟨e, γ, 1, Or.inl rfl, (hfinal 1 1 hθ1).1, (hfinal 1 1 hθ1).2⟩
  · have hθ2 : (theta : MulAut (Om8 F)) ^ (-1 : ℤ) =
        (theta : MulAut (Om8 F)) ^ (2 : ℕ) := by
      rw [zpow_neg_one]
      have h3 : (theta : MulAut (Om8 F)) ^ 2 * theta = 1 := by
        rw [← pow_succ]
        exact theta_cube (K := F)
      have h4 : (theta : MulAut (Om8 F)) ^ 2 = theta⁻¹ := by
        calc (theta : MulAut (Om8 F)) ^ 2 =
            ((theta : MulAut (Om8 F)) ^ 2 * theta) * theta⁻¹ := by group
          _ = 1 * theta⁻¹ := by rw [h3]
          _ = theta⁻¹ := one_mul _
      exact h4.symm
    exact ⟨e, γ, -1, Or.inr rfl, (hfinal 2 (-1) hθ2).1, (hfinal 2 (-1) hθ2).2⟩

end CFSG.StandardType.NTPlane
