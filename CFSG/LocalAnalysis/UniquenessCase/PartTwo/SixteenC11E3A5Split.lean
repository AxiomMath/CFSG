module

public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.Goldschmidt.Steps.G74Basic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise

section Helpers

variable {W : Type} [CommGroup W]

private lemma s1611e3_smul_eq_map (x : MulAut W) (I : Subgroup W) :
    x • I = I.map x.toMonoidHom := by
  have hf : MulDistribMulAction.toMonoidEnd _ _ x = x.toMonoidHom := by
    ext y
    rfl
  rw [Subgroup.pointwise_smul_def, hf]

private lemma s1611e3_map_one (I : Subgroup W) :
    I.map (1 : MulAut W).toMonoidHom = I := by
  have h : (1 : MulAut W).toMonoidHom = MonoidHom.id W := MonoidHom.ext fun _ => rfl
  rw [h, Subgroup.map_id]

private lemma s1611e3_map_mul_map (a b : MulAut W) (I : Subgroup W) :
    (I.map a.toMonoidHom).map b.toMonoidHom = I.map (b * a).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem s1611e3_isIrr_of_isIrrOn {A : Subgroup (MulAut W)} {J : Subgroup W}
    (h : IsIrrOn A J ⊥) : XMod.IsIrr ↥A J := by
  unfold IsIrrOn StableUnder at h
  unfold XMod.IsIrr XMod.IsIrrSec XMod.IsInv
  obtain ⟨hlt, hstab, -, hmin⟩ := h
  exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
    fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩

private theorem s1611e3_natural_isIrr [Finite W] {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) : XMod.IsIrr ↥L J := by
  have hmem := s16c167_mem_irrSet_alt (n := 5) (by norm_num) hJ
  have hfix := s16c167_cfg2_fix_alt (n := 5) (by norm_num) hJ
  have h2 := hmem.2
  rw [hfix] at h2
  exact s1611e3_isIrr_of_isIrrOn h2

private theorem s1611e3_card_alt_natural {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) : Nat.card ↥J = 16 := by
  obtain ⟨π, hπ⟩ := hJ
  obtain ⟨f, hfs, hfk, -⟩ := CFSG.Quasithin.FFC.RealizesVia.secMap
    (D := FFModel.altDn 5) CFSG.Quasithin.FFC.altDn_ker_five hπ
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  have hcard : Nat.card ↥J = Nat.card ↥(FFModel.altDn 5).sec :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hfs⟩)
  rw [hcard]
  exact CFSG.Quasithin.FFC.card_coreMod_five

private theorem s1611e3_natural_map {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) {z : MulAut W} (hzL : ∀ l ∈ L, z * l = l * z) :
    AlternatingNatural L (J.map z.toMonoidHom) ⊥ 5 := by
  obtain ⟨π, hπ⟩ := hJ
  have he : ∀ (g : ↥L) (w : W), z ((g : MulAut W) w) = (g : MulAut W) (z w) := by
    intro g w
    exact congrArg (fun e : MulAut W => e w) (hzL (g : MulAut W) g.2)
  refine ⟨(MulEquiv.refl ↥L).symm.toMonoidHom.comp π, ?_⟩
  have h := CFSG.Quasithin.FFC.RealizesVia.transport (D := FFModel.altDn 5) z.toMonoidHom
    z.injective (MulEquiv.refl ↥L) he hπ
  simpa [Subgroup.map_bot] using h

private theorem s1611e3_sumOfNat_two {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {L : Subgroup (MulAut W)} {U : Subgroup W} (h : SumOfNat N L U ⊥ 2) :
    ∃ J₀ J₁ : Subgroup W, N L J₀ ⊥ ∧ N L J₁ ⊥ ∧ J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = U := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hrest : ∀ i j : Fin 2, i ≠ j → (⨆ (k : Fin 2) (_ : k ≠ i), I k) = I j := by
    intro i j hij
    refine le_antisymm (iSup₂_le fun k hk => ?_) (le_iSup₂ (f := fun k (_ : k ≠ i) => I k) j
      (Ne.symm hij))
    have : k = j := by omega
    rw [this]
  refine ⟨I 0, I 1, hnat 0, hnat 1, ?_, ?_⟩
  · have h0 := hind 0
    rw [hrest 0 1 (by decide), bot_sup_eq] at h0
    exact le_bot_iff.1 h0
  · have hall : (⨆ i, I i) = I 0 ⊔ I 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [hall, bot_sup_eq] at hsup
    exact hsup

private theorem s1611e3_card_sup_of_disjoint {X Y : Subgroup W} (h : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card ↥X * Nat.card ↥Y :=
  CFSG.Goldschmidt.G74.card_sup_of_inf_eq_bot
    (IsMulCommutative.of_comm fun a b => mul_comm a b) le_top le_top h

private theorem s1611e3_card_sum {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2) :
    Nat.card ↥U = 256 := by
  obtain ⟨J₀, J₁, h₀, h₁, hi, hj⟩ := s1611e3_sumOfNat_two hsum
  rw [← hj, s1611e3_card_sup_of_disjoint hi,
    s1611e3_card_alt_natural h₀, s1611e3_card_alt_natural h₁]

private theorem s1611e3_exists_natural_compl [Finite W] {L : Subgroup (MulAut W)}
    {U J : Subgroup W} {I₀ I₁ : Subgroup W} (h₀ : AlternatingNatural L I₀ ⊥ 5)
    (h₁ : AlternatingNatural L I₁ ⊥ 5) (hi : I₀ ⊓ I₁ = ⊥) (hj : I₀ ⊔ I₁ = U)
    (hJ : AlternatingNatural L J ⊥ 5) (hJU : J ≤ U) :
    ∃ J' : Subgroup W, AlternatingNatural L J' ⊥ 5 ∧ J ⊓ J' = ⊥ ∧ J ⊔ J' = U := by
  have hI0irr := s1611e3_natural_isIrr h₀
  have hI1irr := s1611e3_natural_isIrr h₁
  have hJirr := s1611e3_natural_isIrr hJ
  have hJinv : XMod.IsInv ↥L J := hJirr.1
  have hJne : J ≠ ⊥ := hJirr.2.1.ne'
  rcases hI0irr.2.2 (J ⊓ I₀) (hJinv.inf hI0irr.1) bot_le inf_le_right with hA | hA
  · rcases hI1irr.2.2 (J ⊓ I₁) (hJinv.inf hI1irr.1) bot_le inf_le_right with hB | hB
    · refine ⟨I₀, h₀, hA, ?_⟩
      rw [sup_comm]
      apply le_antisymm
      · exact sup_le (by rw [← hj]; exact le_sup_left) hJU
      · intro u hu
        have hu' : u ∈ I₀ ⊔ I₁ := by rwa [hj]
        obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.1 hu'
        obtain ⟨y, hy, hqy⟩ := Z391.v2f_exists_mul_mem (A := ↥L) hI1irr hI0irr.1 hJinv hJne
          (by rw [sup_comm, hj]; exact hJU) hA q hq
        have hmul : p * q = (p * y⁻¹) * (q * y) := by
          rw [mul_mul_mul_comm, inv_mul_cancel, mul_one]
        rw [hmul]
        exact Subgroup.mul_mem_sup (I₀.mul_mem hp (I₀.inv_mem hy)) hqy
    · have hI1J : I₁ ≤ J := by
        intro x hx
        have hx' : x ∈ J ⊓ I₁ := by rw [hB]; exact hx
        exact hx'.1
      have hJI1 : J = I₁ := by
        rcases hJirr.2.2 I₁ hI1irr.1 bot_le hI1J with h | h
        · exact absurd h hI1irr.2.1.ne'
        · exact h.symm
      refine ⟨I₀, h₀, ?_, ?_⟩
      · rw [hJI1, inf_comm]; exact hi
      · rw [hJI1, sup_comm]; exact hj
  · have hI0J : I₀ ≤ J := by
      intro x hx
      have hx' : x ∈ J ⊓ I₀ := by rw [hA]; exact hx
      exact hx'.1
    have hJI0 : J = I₀ := by
      rcases hJirr.2.2 I₀ hI0irr.1 bot_le hI0J with h | h
      · exact absurd h hI0irr.2.1.ne'
      · exact h.symm
    refine ⟨I₁, h₁, ?_, ?_⟩
    · rw [hJI0]; exact hi
    · rw [hJI0]; exact hj

end Helpers

section Transport

private theorem s1611e3_realizesVia_of_iso {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U U' : Subgroup W} {π : D.Gam →* ↥H}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j)
    (h : D.RealizesVia H U ⊥ π) : D.RealizesVia H U' ⊥ π := by
  obtain ⟨hπs, -, hks, -, hZinv, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨hπs, bot_le, hks, fun h u hu => hU' h h.2 u hu, fun h z hz => ?_,
    hsec, hker, β.comp j.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨j u, by simpa using hu⟩
  · intro u
    show β (j.symm u) = 1 ↔ _
    rw [hβk (j.symm u), Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : j.symm u = 1 := Subtype.ext h
      have h2 : u = 1 := by rw [← j.apply_symm_apply u, h1, map_one]
      exact congrArg Subtype.val h2
    · intro h
      have h1 : u = 1 := Subtype.ext h
      have h2 : j.symm u = 1 := by rw [h1, map_one]
      exact congrArg Subtype.val h2
  · intro γ u m hu hm hβu
    simp only [MonoidHom.comp_apply]
    change β (j.symm ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) = _
    have hjinv : j.symm ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
          hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ := by
      apply Subtype.ext
      have h1 := hj (π γ) (j.symm u)
        ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
          hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ rfl
      have h2 : ((π γ : ↥H) : MulAut W) (u : W) =
          (j ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
            hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ : W) := by
        simpa only [Subgroup.smul_def, MulAut.smul_def, MulEquiv.apply_symm_apply] using h1
      have h3 : (⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : ↥U') =
          j ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
            hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ := Subtype.ext h2
      rw [h3, MulEquiv.symm_apply_apply]
    rw [hjinv]
    exact hβe γ (j.symm u) m _ hm hβu

private theorem s1611e3_realizes_of_iso {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j)
    (h : D.Realizes H U ⊥) : D.Realizes H U' ⊥ := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, s1611e3_realizesVia_of_iso hU hU' j hj hπ⟩

private theorem s1611e3_alternatingNatural_of_iso {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j) {n : ℕ}
    (h : AlternatingNatural H U ⊥ n) : AlternatingNatural H U' ⊥ n :=
  s1611e3_realizes_of_iso (D := FFModel.altDn n) hU hU' j hj h

private theorem s1611e3_alt_of_irr_le_sum {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} {I₀ I₁ : Subgroup W}
    (h₀ : AlternatingNatural L I₀ ⊥ 5) (h₁ : AlternatingNatural L I₁ ⊥ 5)
    (hi : I₀ ⊓ I₁ = ⊥) (hj : I₀ ⊔ I₁ = U)
    {K : Subgroup W} (hKU : K ≤ U) (hKirr : XMod.IsIrr ↥L K) :
    AlternatingNatural L K ⊥ 5 := by
  by_cases hK0 : K = I₀
  · rwa [hK0]
  by_cases hK1 : K = I₁
  · rwa [hK1]
  have hIrr₀ : XMod.IsIrr ↥L I₀ := s1611e3_natural_isIrr h₀
  have hIrr₁ : XMod.IsIrr ↥L I₁ := s1611e3_natural_isIrr h₁
  have hKle : K ≤ I₀ ⊔ I₁ := by rw [hj]; exact hKU
  have hK₀ : K ⊓ I₀ = ⊥ := Z391.v2f_inf_eq_bot hKirr hIrr₀ hK0
  have hK₁ : K ⊓ I₁ = ⊥ := Z391.v2f_inf_eq_bot hKirr hIrr₁ hK1
  obtain ⟨θ, hθe, hθ⟩ :=
    Z391.v2f_exists_graph hIrr₀ hIrr₁ hKirr.1 hKirr.2.1.ne' hKle hK₀ hK₁
  have hψmem : ∀ x : ↥I₀, (x : W) * (θ x : W) ∈ K := fun x => (hθ x (θ x)).2 rfl
  let ψ : ↥I₀ →* ↥K :=
    { toFun := fun x => ⟨(x : W) * (θ x : W), hψmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : W) * (y : W) * (θ (x * y) : W) =
          ((x : W) * (θ x : W)) * ((y : W) * (θ y : W))
        rw [map_mul]
        ac_rfl }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : W) * (θ x : W) = (y : W) * (θ y : W) := congrArg Subtype.val hxy
    have h2 : (y : W)⁻¹ * (x : W) = (θ y : W) * (θ x : W)⁻¹ := by
      calc (y : W)⁻¹ * (x : W) =
            (y : W)⁻¹ * ((x : W) * (θ x : W)) * (θ x : W)⁻¹ := by group
        _ = (y : W)⁻¹ * ((y : W) * (θ y : W)) * (θ x : W)⁻¹ := by rw [h1]
        _ = (θ y : W) * (θ x : W)⁻¹ := by group
    have h3 : (x : W) * (y : W)⁻¹ = (θ y : W) * (θ x : W)⁻¹ := by
      rw [mul_comm]; exact h2
    have hxyI₀ : (x : W) * (y : W)⁻¹ ∈ I₀ := I₀.mul_mem x.2 (I₀.inv_mem y.2)
    have hxyI₁ : (x : W) * (y : W)⁻¹ ∈ I₁ := by
      have hinv : ((x : W) * (y : W)⁻¹)⁻¹ ∈ I₁ := by
        have h4 : ((x : W) * (y : W)⁻¹)⁻¹ = (θ x : W) * (θ y : W)⁻¹ := by
          rw [h3]; group
        rw [h4]
        exact I₁.mul_mem (θ x).2 (I₁.inv_mem (θ y).2)
      simpa using I₁.inv_mem hinv
    have hbot : (x : W) * (y : W)⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← hi]
      exact Subgroup.mem_inf.2 ⟨hxyI₀, hxyI₁⟩
    exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 (hKle k.2)
    have hk : (x : W) * (y : W) ∈ K := hxy ▸ k.2
    have hθx : θ ⟨x, hx⟩ = ⟨y, hy⟩ := (hθ ⟨x, hx⟩ ⟨y, hy⟩).1 hk
    exact ⟨⟨x, hx⟩, Subtype.ext (by
      show (x : W) * (θ ⟨x, hx⟩ : W) = (k : W)
      rw [hθx]
      exact hxy)⟩
  let ψe : ↥I₀ ≃* ↥K := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hψeqv : Z391.V2fEqv ↥L ψe := by
    intro a x x' hxx
    have hθx : θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ = ⟨a • (θ x : W),
        hIrr₁.1 a (θ x : W) (θ x).2⟩ := by
      apply Subtype.ext
      exact (hθe a x ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ rfl).symm
    have hx' : x' = ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ := Subtype.ext hxx.symm
    rw [hx']
    change a • ((x : W) * (θ x : W)) =
      (a • (x : W)) * (θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ : W)
    rw [smul_mul', hθx]
  have hstab₀ : StableUnder L I₀ := fun x hx u hu => hIrr₀.1 ⟨x, hx⟩ u hu
  have hstabK : StableUnder L K := fun x hx u hu => hKirr.1 ⟨x, hx⟩ u hu
  exact s1611e3_alternatingNatural_of_iso hstab₀ hstabK ψe hψeqv h₀

end Transport

section Split

variable {W : Type} [CommGroup W] [Finite W]

private theorem s1611e3_no_fixed_natural {L Z : Subgroup (MulAut W)} {U K K' : Subgroup W}
    {z : MulAut W} (hZL : ∀ z' ∈ Z, ∀ l ∈ L, z' * l = l * z')
    (hZU : ∀ z' ∈ Z, ∀ w ∈ U, z' w ∈ U)
    (hZf : ∀ z' ∈ Z, z' ≠ 1 → ∃ w ∈ U, z' w ≠ w)
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hKnat : AlternatingNatural L K ⊥ 5) (hKU : K ≤ U)
    (hK'nat : AlternatingNatural L K' ⊥ 5) (hinf : K ⊓ K' = ⊥) (hsup : K ⊔ K' = U) :
    K.map z.toMonoidHom ≠ K := by
  intro hKz
  have hzL : ∀ l ∈ L, z * l = l * z := fun l hl => hZL z hz l hl
  have hKirr := s1611e3_natural_isIrr hKnat
  have hK'irr := s1611e3_natural_isIrr hK'nat
  have hKE := s16c167_endUnits_alt (n := 5) (by norm_num) hKnat
  have hK'E := s16c167_endUnits_alt (n := 5) (by norm_num) hK'nat
  have hK'z_nat : AlternatingNatural L (K'.map z.toMonoidHom) ⊥ 5 :=
    s1611e3_natural_map hK'nat hzL
  have hK'z2_nat : AlternatingNatural L ((K'.map z.toMonoidHom).map z.toMonoidHom) ⊥ 5 :=
    s1611e3_natural_map hK'z_nat hzL
  have hK'z_irr := s1611e3_natural_isIrr hK'z_nat
  have hK'z2_irr := s1611e3_natural_isIrr hK'z2_nat
  have hfixK : ∀ x ∈ K, z x = x := by
    have h := Z391.v2f_smul_eq_self (Λ := L) (c := z) hzL hKE hKirr.1 (XMod.Iso.refl K)
      (by rw [s1611e3_smul_eq_map]; exact hKz)
    intro x hx
    simpa [MulAut.smul_def] using h x hx
  have hzUle : U.map z.toMonoidHom ≤ U := by
    rintro x ⟨u, hu, rfl⟩
    exact hZU z hz u hu
  have hK'leU : K' ≤ U := by rw [← hsup]; exact le_sup_right
  have hK'z_le : K'.map z.toMonoidHom ≤ K ⊔ K' := by
    calc K'.map z.toMonoidHom ≤ U.map z.toMonoidHom := Subgroup.map_mono hK'leU
      _ ≤ U := hzUle
      _ = K ⊔ K' := hsup.symm
  have hK'z2_le : (K'.map z.toMonoidHom).map z.toMonoidHom ≤ K ⊔ K' := by
    calc (K'.map z.toMonoidHom).map z.toMonoidHom ≤ U.map z.toMonoidHom :=
          Subgroup.map_mono (hK'z_le.trans (le_of_eq hsup))
      _ ≤ U := hzUle
      _ = K ⊔ K' := hsup.symm
  have hz31 : z * (z * z) = 1 := by
    rw [← pow_two, ← pow_succ']
    exact hz3
  have hz31' : z * z * z = 1 := by
    rw [mul_assoc]; exact hz31
  have hzz_inv : z * z = z⁻¹ := by
    calc z * z = (z * z * z) * z⁻¹ := by group
      _ = 1 * z⁻¹ := by rw [hz31']
      _ = z⁻¹ := one_mul _
  have hKinvm : K.map z⁻¹.toMonoidHom = K := by
    have h1 := congrArg (fun I : Subgroup W => I.map z⁻¹.toMonoidHom) hKz
    rw [s1611e3_map_mul_map z z⁻¹, inv_mul_cancel, s1611e3_map_one] at h1
    exact h1.symm
  have hzK'neK : K'.map z.toMonoidHom ≠ K := by
    intro h
    have h1 : K ⊓ K'.map z.toMonoidHom ≠ ⊥ := by
      rw [h]; simpa [inf_idem] using hKirr.2.1.ne'
    have h2 : K ⊓ K'.map z.toMonoidHom = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxK, hxK'z⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨y, hyK', rfl⟩ := Subgroup.mem_map.1 hxK'z
      have hyK : y ∈ K := by
        have hmem : z y ∈ K.map z.toMonoidHom := by rw [hKz]; exact hxK
        obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.1 hmem
        have hjy' : j = y := z.injective hjy
        rwa [← hjy']
      have hyinf : y ∈ K ⊓ K' := Subgroup.mem_inf.2 ⟨hyK, hyK'⟩
      rw [hinf] at hyinf
      have hy1 : y = 1 := Subgroup.mem_bot.1 hyinf
      rw [hy1, map_one]
    exact h1 h2
  by_cases hK'z : K'.map z.toMonoidHom = K'
  · have hfixK' : ∀ x ∈ K', z x = x := by
      have h := Z391.v2f_smul_eq_self (Λ := L) (c := z) hzL hK'E hK'irr.1 (XMod.Iso.refl K')
        (by rw [s1611e3_smul_eq_map]; exact hK'z)
      intro x hx
      simpa [MulAut.smul_def] using h x hx
    obtain ⟨u, hu, hzu⟩ := hZf z hz hz1
    apply hzu
    have hu' : u ∈ K ⊔ K' := by rw [hsup]; exact hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu'
    rw [map_mul, hfixK a ha, hfixK' b hb]
  · have hz2K'neK : (K'.map z.toMonoidHom).map z.toMonoidHom ≠ K := by
      intro h
      have h2 : ((K'.map z.toMonoidHom).map z.toMonoidHom).map z⁻¹.toMonoidHom =
          K.map z⁻¹.toMonoidHom := by rw [h]
      rw [s1611e3_map_mul_map z z⁻¹, inv_mul_cancel, s1611e3_map_one, hKinvm] at h2
      exact hzK'neK h2
    have hz2K'neK' : (K'.map z.toMonoidHom).map z.toMonoidHom ≠ K' := by
      intro h
      have h1 : ((K'.map z.toMonoidHom).map z.toMonoidHom).map z⁻¹.toMonoidHom =
          K'.map z⁻¹.toMonoidHom := by rw [h]
      rw [s1611e3_map_mul_map z z⁻¹, inv_mul_cancel, s1611e3_map_one] at h1
      have h2 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h1
      rw [s1611e3_map_mul_map z z, s1611e3_map_mul_map z⁻¹ z,
        mul_inv_cancel, s1611e3_map_one] at h2
      rw [hzz_inv] at h2
      have h3 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h2
      rw [s1611e3_map_mul_map z⁻¹ z, mul_inv_cancel, s1611e3_map_one] at h3
      exact hK'z h3.symm
    have heq := Z391.v2f_eq_of_le_sup (A := ↥L) (P := K) (P' := K') hKirr hK'irr hKE
      hK'z_irr hK'z2_irr hK'z_le hK'z2_le hzK'neK hK'z hz2K'neK hz2K'neK'
    have heq' : K'.map z.toMonoidHom = K'.map z⁻¹.toMonoidHom := by
      have hh := heq
      rw [s1611e3_map_mul_map z z, hzz_inv] at hh
      exact hh
    have h2 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) heq'
    rw [s1611e3_map_mul_map z z, s1611e3_map_mul_map z⁻¹ z,
      mul_inv_cancel, s1611e3_map_one] at h2
    rw [hzz_inv] at h2
    have h3 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h2
    rw [s1611e3_map_mul_map z⁻¹ z, mul_inv_cancel, s1611e3_map_one] at h3
    exact hK'z h3.symm

private theorem s1611e3_z_fixed_free {L Z : Subgroup (MulAut W)} {U : Subgroup W} {z : MulAut W}
    (hZL : ∀ z' ∈ Z, ∀ l ∈ L, z' * l = l * z')
    (hZU : ∀ z' ∈ Z, ∀ w ∈ U, z' w ∈ U)
    (hZf : ∀ z' ∈ Z, z' ≠ 1 → ∃ w ∈ U, z' w ≠ w)
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2) :
    ∀ u ∈ U, z u = u → u = 1 := by
  classical
  obtain ⟨I₀, I₁, h₀, h₁, hi, hj⟩ := s1611e3_sumOfNat_two hsum
  have hfix0 : StableUnder L I₀ := s16c167_stable_of_realizes (D := FFModel.altDn 5) h₀
  have hfix1 : StableUnder L I₁ := s16c167_stable_of_realizes (D := FFModel.altDn 5) h₁
  have hUinv : StableUnder L U := by
    intro l hl u hu
    rw [← hj] at hu ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hfix0 l hl a ha) (hfix1 l hl b hb)
  intro u₀ hu₀U hu₀fix
  by_contra hu₀ne
  let Vp : Subgroup W := U ⊓ fixV (Subgroup.zpowers z)
  have hVp_le : Vp ≤ U := inf_le_left
  have hVp_inv : XMod.IsInv ↥L Vp := by
    intro l x hx
    refine Subgroup.mem_inf.2 ⟨hUinv l l.2 x hx.1, ?_⟩
    rw [mem_fixV_zpowers]
    have hxfix : z x = x := (mem_fixV_zpowers z x).1 hx.2
    have hcomm := hZL z hz (l : MulAut W) l.2
    change z ((l : MulAut W) x) = (l : MulAut W) x
    rw [show z ((l : MulAut W) x) = (l : MulAut W) (z x) from
      congrArg (fun e : MulAut W => e x) hcomm, hxfix]
  have hVp_ne : Vp ≠ ⊥ := by
    intro hbot
    have hmem : u₀ ∈ Vp := Subgroup.mem_inf.2 ⟨hu₀U, (mem_fixV_zpowers z u₀).2 hu₀fix⟩
    rw [hbot] at hmem
    exact hu₀ne (Subgroup.mem_bot.1 hmem)
  have hex : ∃ n, ∃ K : Subgroup W, K ≤ Vp ∧ K ≠ ⊥ ∧ XMod.IsInv ↥L K ∧ Nat.card K = n :=
    ⟨Nat.card Vp, Vp, le_rfl, hVp_ne, hVp_inv, rfl⟩
  obtain ⟨K, hKVp, hKne, hKinv, hKcard⟩ := Nat.find_spec hex
  have hKmin : ∀ K' : Subgroup W, K' ≤ Vp → K' ≠ ⊥ → XMod.IsInv ↥L K' →
      Nat.card K ≤ Nat.card K' := by
    intro K' h1 h2 h3
    have hle := Nat.find_min' hex (m := Nat.card K') ⟨K', h1, h2, h3, rfl⟩
    rwa [← hKcard] at hle
  have hKirr : XMod.IsIrr ↥L K := by
    refine ⟨hKinv, bot_lt_iff_ne_bot.mpr hKne, ?_⟩
    intro K' hK'inv _ hK'K
    by_cases h0 : K' = ⊥
    · exact Or.inl h0
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hK'K (hKmin K' (hK'K.trans hKVp) h0 hK'inv))
  have hKnat : AlternatingNatural L K ⊥ 5 :=
    s1611e3_alt_of_irr_le_sum h₀ h₁ hi hj (hKVp.trans hVp_le) hKirr
  obtain ⟨K', hK'nat, hK'inf, hK'sup⟩ :=
    s1611e3_exists_natural_compl h₀ h₁ hi hj hKnat (hKVp.trans hVp_le)
  have hKfix : ∀ x ∈ K, z x = x := fun x hx => (mem_fixV_zpowers z x).1 (hKVp hx).2
  have hKz : K.map z.toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change z y ∈ K
      rw [hKfix y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hKfix x hx⟩
  exact absurd hKz
    (s1611e3_no_fixed_natural hZL hZU hZf hz hz1 hz3 hKnat (hKVp.trans hVp_le)
      hK'nat hK'inf hK'sup)

end Split

theorem s1611e3_a5_split {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L Z : Subgroup (MulAut W)} {U : Subgroup W} (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2)
    (hZ : Nat.card ↥Z = 3) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZU : ∀ z ∈ Z, ∀ w ∈ U, z w ∈ U) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U, z w ≠ w)
    {J : Subgroup W} (hJU : J ≤ U) (hJ : AlternatingNatural L J ⊥ 5) {z : MulAut W}
    (hz : z ∈ Z) (hz1 : z ≠ 1) :
    AlternatingNatural L (J.map z.toMonoidHom) ⊥ 5 ∧ J ⊓ J.map z.toMonoidHom = ⊥ ∧
      J ⊔ J.map z.toMonoidHom = U ∧ ∀ j ∈ J, z (z j) = j * z j := by
  have hzL : ∀ l ∈ L, z * l = l * z := fun l hl => hZL z hz l hl
  have hz3 : z ^ 3 = 1 := by
    have hdvd : orderOf z ∣ 3 := by
      rw [← hZ]; exact Subgroup.orderOf_dvd_natCard Z hz
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · rw [← h]; exact pow_orderOf_eq_one z
  have hJz : AlternatingNatural L (J.map z.toMonoidHom) ⊥ 5 :=
    s1611e3_natural_map hJ hzL
  have hJirr := s1611e3_natural_isIrr hJ
  have hJzirr := s1611e3_natural_isIrr hJz
  have hJE := s16c167_endUnits_alt (n := 5) (by norm_num) hJ
  have hff := s1611e3_z_fixed_free hZL hZU hZf hz hz1 hz3 hsum
  have hJnz : J ⊓ J.map z.toMonoidHom = ⊥ := by
    by_contra hne
    have hle : J ≤ J.map z.toMonoidHom := by
      rcases hJirr.2.2 (J ⊓ J.map z.toMonoidHom) (hJirr.1.inf hJzirr.1) bot_le inf_le_left with
        h | h
      · exact absurd h hne
      · intro x hx
        exact (Subgroup.mem_inf.1 (h ▸ hx)).2
    have heq : J.map z.toMonoidHom = J := by
      rcases hJzirr.2.2 J hJirr.1 bot_le hle with h | h
      · exact absurd h hJirr.2.1.ne'
      · exact h.symm
    have hfixJ : ∀ x ∈ J, z x = x := by
      have h := Z391.v2f_smul_eq_self (Λ := L) (c := z) hzL hJE hJirr.1 (XMod.Iso.refl J)
        (by rw [s1611e3_smul_eq_map]; exact heq)
      intro x hx
      simpa [MulAut.smul_def] using h x hx
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJirr.2.1.ne'
    exact ha (Subtype.ext (hff (a : W) (hJU a.2) (hfixJ (a : W) a.2)))
  refine ⟨hJz, hJnz, ?_, ?_⟩
  · have hcard := s1611e3_card_sup_of_disjoint hJnz
    have h16 := s1611e3_card_alt_natural hJ
    have h16z := s1611e3_card_alt_natural hJz
    have hUc := s1611e3_card_sum hsum
    have hle : J ⊔ J.map z.toMonoidHom ≤ U := sup_le hJU (by
      rintro x ⟨j, hj, rfl⟩
      exact hZU z hz j (hJU hj))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, h16, h16z, hUc]
  · intro j hj
    let w : W := z (z j) * z j * j
    have hwU : w ∈ U := by
      refine U.mul_mem (U.mul_mem ?_ ?_) (hJU hj)
      · exact hZU z hz _ (hZU z hz j (hJU hj))
      · exact hZU z hz j (hJU hj)
    have hz3app : z (z (z j)) = j := by
      have h := congrArg (fun e : MulAut W => e j) hz3
      simpa [pow_succ, pow_two, MulAut.mul_apply] using h
    have hwfix : z w = w := by
      show z (z (z j) * z j * j) = z (z j) * z j * j
      simp only [map_mul, hz3app]
      ac_rfl
    have hw1 : w = 1 := hff w hwU hwfix
    have hw1' : z (z j) * z j * j = 1 := hw1
    have hzj : z j * z j = 1 := by simpa [pow_two] using hW (z j)
    have hj2 : j * j = 1 := by simpa [pow_two] using hW j
    have hkey : z (z j) * z j = j := by
      have h2 : (z (z j) * z j * j) * j = 1 * j := by rw [hw1']
      calc z (z j) * z j = z (z j) * z j * (j * j) := by rw [hj2, mul_one]
        _ = (z (z j) * z j * j) * j := by group
        _ = 1 * j := h2
        _ = j := one_mul j
    calc z (z j) = z (z j) * 1 := (mul_one _).symm
      _ = z (z j) * (z j * z j) := by rw [hzj]
      _ = (z (z j) * z j) * z j := by group
      _ = j * z j := by rw [hkey]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
