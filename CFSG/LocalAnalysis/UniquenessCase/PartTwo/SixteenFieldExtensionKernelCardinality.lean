module

public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.Quasithin.Background.CoprimeFixedCentralizer
public import CFSG.GroupTheory.FixedPointCardinality
public import CFSG.Quasithin.Vol2.Ch3B513NC1SL2
public import CFSG.Quasithin.Vol2.Ch3B513NSpC
public import CFSG.Quasithin.Background.FFC4Five

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Open Subgroup
open scoped Matrix

theorem exists_scalar_hom_of_isCoord
    {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Nontrivial M]
    {W : Type} [CommGroup W] {LM : KGNat.LinModel D K M}
    {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H} {f : W → M}
    (hf : KGNat.IsCoord LM H (fixV H) π f)
    (hcomm : commSub ⊤ H = ⊤)
    (hscal : ∀ T : M →+ M,
      (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ a : K, ∀ x, T x = a • x) :
    ∃ χ : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* Kˣ,
      Function.Injective χ ∧
      ∀ (c : ↥(Subgroup.centralizer (H : Set (MulAut W)))) (w : W),
        f ((c : MulAut W) w) = (χ c : K) • f w := by
  classical
  have hstab : Subgroup.centralizer (H : Set (MulAut W)) ≤ stabSub (fixV H) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer
      (Subgroup.centralizer_le_normalizer (H : Set (MulAut W)))
  let T : ↥(Subgroup.centralizer (H : Set (MulAut W))) → M →+ M :=
    fun c => hf.autMap (c : MulAut W) (fun z hz => (hstab c.2 z).2 hz)
  have hTcomm : ∀ c : ↥(Subgroup.centralizer (H : Set (MulAut W))),
      ∀ (γ : D.Gam) (x : M), T c (LM.lin γ x) = LM.lin γ (T c x) := by
    intro c γ x
    have hc : (c : MulAut W) * ((π γ : ↥H) : MulAut W) =
        ((π γ : ↥H) : MulAut W) * (c : MulAut W) :=
      (Subgroup.mem_centralizer_iff.mp c.2 ((π γ : ↥H) : MulAut W) (π γ).2).symm
    have hconj : (c : MulAut W) * ((π γ : ↥H) : MulAut W) * (c : MulAut W)⁻¹ =
        ((π γ : ↥H) : MulAut W) := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hf.autMap_lin (c : MulAut W) (fun z hz => (hstab c.2 z).2 hz) γ γ hconj x
  choose a ha using fun c => hscal (T c) (hTcomm c)
  have huniq : ∀ (c : ↥(Subgroup.centralizer (H : Set (MulAut W)))) {u v : K},
      (∀ x : M, T c x = u • x) → (∀ x : M, T c x = v • x) → u = v := by
    intro c u v hu hv
    obtain ⟨x0, hx0⟩ := exists_ne (0 : M)
    exact smul_left_injective (R := K) (M := M) hx0 ((hu x0).symm.trans (hv x0))
  have ha_one : a 1 = 1 := by
    refine huniq 1 (ha 1) ?_
    intro x
    rw [one_smul]
    obtain ⟨w, rfl⟩ := hf.surj x
    show hf.autMap (1 : MulAut W)
      (fun z hz => (hstab (Subgroup.one_mem _) z).2 hz) (f w) = f w
    rw [hf.autMap_apply, MulAut.one_apply]
  have ha_mul : ∀ c d : ↥(Subgroup.centralizer (H : Set (MulAut W))),
      a (c * d) = a c * a d := by
    intro c d
    refine huniq (c * d) (ha (c * d)) ?_
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    calc T (c * d) (f w)
        = f (((c * d : ↥(Subgroup.centralizer (H : Set (MulAut W)))) : MulAut W) w) :=
          hf.autMap_apply _ _ w
      _ = f (((c : MulAut W) * (d : MulAut W)) w) := rfl
      _ = f ((c : MulAut W) ((d : MulAut W) w)) := by rw [MulAut.mul_apply]
      _ = T c (f ((d : MulAut W) w)) :=
          (hf.autMap_apply (c : MulAut W) (fun z hz => (hstab c.2 z).2 hz) ((d : MulAut W) w)).symm
      _ = T c (T d (f w)) := by
          rw [show f ((d : MulAut W) w) = T d (f w) from
            (hf.autMap_apply (d : MulAut W) (fun z hz => (hstab d.2 z).2 hz) w).symm]
      _ = (a c) • ((a d) • f w) := by rw [ha c, ha d]
      _ = (a c * a d) • f w := smul_smul (a c) (a d) (f w)
  let lamK : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* K :=
    { toFun := a
      map_one' := ha_one
      map_mul' := ha_mul }
  let lam : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* Kˣ := lamK.toHomUnits
  refine ⟨lam, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro c hc
    have hcK : a c = 1 := by
      have := congrArg Units.val hc
      simpa [lam, lamK] using this
    apply Subtype.ext
    exact s16g_eq_one_of_commSub hcomm
      (fun h hh => (Subgroup.mem_centralizer_iff.mp c.2 h hh).symm)
      (fun w => by
        rw [← hf.eq_iff ((c : MulAut W) w) w]
        rw [show f ((c : MulAut W) w) = a c • f w from
          (hf.autMap_apply (c : MulAut W) (fun z hz => (hstab c.2 z).2 hz) w).symm.trans (ha c (f w))]
        rw [hcK, one_smul])
  · intro c w
    exact (hf.autMap_apply (c : MulAut W) (fun z hz => (hstab c.2 z).2 hz) w).symm.trans (ha c (f w))

theorem card_centralizer_eq_and_modFix_eq_bot_of_extension
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M] [Nontrivial M]
    {D : FFModel} {LM : KGNat.LinModel D K M}
    (hreal : D.Realizes H ⊤ (fixV H))
    (hcomm : commSub ⊤ H = ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : Nat.card K = p + 1) (hpodd : Odd p)
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hscal : ∀ T : M →+ M,
      (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ a : K, ∀ x, T x = a • x) :
    let C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (H : Set (MulAut W))
    Nat.card ↥C = p ∧ modFix C (⊤ : Subgroup W) = ⊥ := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord LM hπ
  obtain ⟨χ, hχinj, hχeq⟩ := exists_scalar_hom_of_isCoord hf hcomm hscal
  let C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (H : Set (MulAut W))
  let ιC : ↥C →* ↥(Subgroup.centralizer (H : Set (MulAut W))) :=
    Subgroup.inclusion (inf_le_right : C ≤ Subgroup.centralizer (H : Set (MulAut W)))
  have hιCinj : Function.Injective ιC := Subgroup.inclusion_injective _
  have hCne : C ≠ ⊥ := hcentral
  have hCcard : Nat.card ↥C = p := by
    have hinj : Function.Injective (χ.comp ιC) := hχinj.comp hιCinj
    have hdvd : Nat.card ↥C ∣ p := by
      have h := Subgroup.card_dvd_of_injective (χ.comp ιC) hinj
      rw [Nat.card_units, hpK] at h
      simpa using h
    have hne1 : Nat.card ↥C ≠ 1 := by
      intro h1
      exact hCne (Subgroup.card_eq_one.mp h1)
    rcases hp.eq_one_or_self_of_dvd (Nat.card ↥C) hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hCodd : Odd (Nat.card ↥C) := by
    rw [hCcard]
    exact hpodd
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  have hχc : χ (ιC c) ≠ 1 := by
    intro h1
    apply hc
    exact hιCinj (hχinj (h1.trans (map_one χ).symm))
  have hmodFixH : modFix H (⊤ : Subgroup W) = fixV H := by
    rw [show modFix H (⊤ : Subgroup W) = XMod.fixed ↥H (⊤ : Subgroup W) from rfl,
      fixed_eq_inf_fixV, top_inf_eq]
  have hfixC_le : modFix C (⊤ : Subgroup W) ≤ modFix H (⊤ : Subgroup W) := by
    rw [hmodFixH]
    intro w hw
    have hwC : (c : MulAut W) w = w := by
      have := hw.2 c
      simpa [Subgroup.smul_def, MulAut.smul_def] using this
    have hsc : f ((c : MulAut W) w) = (χ (ιC c) : K) • f w :=
      hχeq (ιC c) w
    have hw_eq : f w = (χ (ιC c) : K) • f w := by
      rw [← hsc, hwC]
    have hfw : f w = 0 := by
      by_contra hne
      have hval : (χ (ιC c) : K) = 1 := by
        apply smul_left_injective (R := K) (M := M) hne
        calc (χ (ιC c) : K) • f w = f w := hw_eq.symm
          _ = (1 : K) • f w := (one_smul K (f w)).symm
      exact hχc (Units.ext (by simpa using hval))
    exact (hf.ker w).mp hfw
  have hmodcomm : modComm H (⊤ : Subgroup W) = ⊤ := by
    show XMod.commOf ↥H (⊤ : Subgroup W) = ⊤
    rw [commOf_eq_commSub, hcomm]
  have hHnorm : H ≤ Subgroup.normalizer (C : Set (MulAut W)) := by
    have hHC : H ≤ Subgroup.centralizer (C : Set (MulAut W)) :=
      Subgroup.le_centralizer_iff.mpr
        (inf_le_right : C ≤ Subgroup.centralizer (H : Set (MulAut W)))
    exact hHC.trans (Subgroup.centralizer_le_normalizer (C : Set (MulAut W)))
  have hbot : modFix C (⊤ : Subgroup W) = ⊥ :=
    modFix_eq_bot_of_odd_of_modComm_eq_top hW hCodd hHnorm hmodcomm hfixC_le
  change Nat.card ↥C = p ∧ modFix C (⊤ : Subgroup W) = ⊥
  exact ⟨hCcard, hbot⟩

theorem card_fixV_eq_of_extension
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M] [Nontrivial M]
    {D : FFModel} {LM : KGNat.LinModel D K M}
    (hreal : D.Realizes H ⊤ (fixV H))
    (hcomm : commSub ⊤ H = ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : Nat.card K = p + 1) (hpodd : Odd p)
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥)
    (hscal : ∀ T : M →+ M,
      (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ a : K, ∀ x, T x = a • x)
    (hupper : Nat.card ↥(fixV H) ≤ p + 1) :
    Nat.card ↥(fixV H) = Nat.card K := by
  classical
  let C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (H : Set (MulAut W))
  have hmain :=
    card_centralizer_eq_and_modFix_eq_bot_of_extension hW hreal hcomm hp hpK hpodd hcentral hscal
  change Nat.card ↥C = p ∧ modFix C (⊤ : Subgroup W) = ⊥ at hmain
  obtain ⟨hCcard, hbot⟩ := hmain
  have hCnorm : C ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
    (inf_le_right : C ≤ Subgroup.centralizer (H : Set (MulAut W))).trans
      (Subgroup.centralizer_le_normalizer (H : Set (MulAut W)))
  have hCstab : C ≤ stabSub (fixV H) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer hCnorm
  let X : SubMulAction ↥C W :=
    { carrier := (fixV H : Set W)
      smul_mem' := fun c z hz => by
        simpa [Subgroup.smul_def, MulAut.smul_def] using (hCstab c.2 z).2 hz }
  have hXcard : Nat.card X = Nat.card ↥(fixV H) := rfl
  have hfixedX : MulAction.fixedPoints ↥C X = {⟨1, (fixV H).one_mem⟩} := by
    ext x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hx
      have hxmod : (x : W) ∈ modFix C (⊤ : Subgroup W) := by
        refine ⟨trivial, fun c => ?_⟩
        have h := congrArg (fun z : X => (z : W)) (hx c)
        simpa [SubMulAction.val_smul, Subgroup.smul_def, MulAut.smul_def] using h
      rw [hbot, Subgroup.mem_bot] at hxmod
      exact Subtype.ext hxmod
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      intro c
      apply Subtype.ext
      simp
  have hP : IsPGroup p ↥C :=
    isPGroup_iff_card_dvd_pow.mpr ⟨1, by rw [hCcard, pow_one]⟩
  have hXnt : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot (fixV H)).mpr hfix
  have hupperX : Nat.card X ≤ p + 1 := by
    rwa [hXcard]
  have hZcardX : Nat.card X = p + 1 :=
    @CFSG.card_eq_prime_add_one_of_fixedPoints_eq_singleton p (Fact.mk hp) ↥C X
      _ _ hXnt _ hP ⟨1, (fixV H).one_mem⟩ hfixedX hupperX
  have hZcard : Nat.card ↥(fixV H) = p + 1 := by
    rw [← hXcard]
    exact hZcardX
  rw [hZcard, hpK]

theorem card_fixV_and_card_of_sl2_extension
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Nat.card (fixV H) = Nat.card K ∧ Nat.card W = Nat.card K ^ 3 := by
  classical
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  obtain ⟨n, hn, hK2n⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nat.card K = 2 ^ n := by
    rcases hK with h4 | h8
    · exact ⟨2, by norm_num, by rw [h4]; norm_num⟩
    · exact ⟨3, by norm_num, by rw [h8]; norm_num⟩
  have hupper : Nat.card ↥(fixV H) ≤ p + 1 := by
    have hle := B513N.card_fixV_le_of_sl2 (K := K) (n := n) hW H ⊤
      (fun _ _ _ hv => hv)
      (by
        show XMod.commOf ↥H (⊤ : Subgroup W) = ⊤
        rw [commOf_eq_commSub, hcomm])
      hn hK2n (by simpa [inf_top_eq] using hreal)
    have hpow : (2 : ℕ) ^ n = p + 1 := by rw [← hK2n, hpK]
    simpa [inf_top_eq, hpow] using hle
  have hZ : Nat.card (fixV H) = Nat.card K :=
    card_fixV_eq_of_extension (D := FFModel.nat (StatedSL 2 K))
      (LM := KGNat.linModelNat (StatedSL 2 K)) hW hreal hcomm hp hpK hpodd hcentral hfix
      (fun T hT => KGNat.commutant_statedSL (n := 2) (by norm_num) T hT) hupper
  obtain ⟨π, hπ⟩ := hreal
  have hWcard :=
    CFSG.Quasithin.FFC.card_eq_of_realizes
      (D := FFModel.nat (StatedSL 2 K)) rfl hπ
  have hsec : Nat.card (FFModel.nat (StatedSL 2 K)).sec = Nat.card K ^ 2 := by
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) = Nat.card K ^ 2
    rw [Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → K) ≃ (Fin 2 → K)),
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  refine ⟨hZ, ?_⟩
  rw [Subgroup.card_top, hZ, hsec] at hWcard
  rw [hWcard]
  ring

theorem card_fixV_and_card_of_sp4_extension
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Nat.card (fixV H) = Nat.card K ∧ Nat.card W = Nat.card K ^ 5 := by
  classical
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  obtain ⟨n, hn, hK2n⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nat.card K = 2 ^ n := by
    rcases hK with h4 | h8
    · exact ⟨2, by norm_num, by rw [h4]; norm_num⟩
    · exact ⟨3, by norm_num, by rw [h8]; norm_num⟩
  have hupper : Nat.card ↥(fixV H) ≤ p + 1 := by
    have hle := B513N.card_fixV_le_of_sp4 (K := K) (n := n) hW H ⊤
      (fun _ _ _ hv => hv)
      (by
        show XMod.commOf ↥H (⊤ : Subgroup W) = ⊤
        rw [commOf_eq_commSub, hcomm])
      hn hK2n (by simpa [inf_top_eq] using hreal)
    have hpow : (2 : ℕ) ^ n = p + 1 := by rw [← hK2n, hpK]
    simpa [inf_top_eq, hpow] using hle
  have hZ : Nat.card (fixV H) = Nat.card K :=
    card_fixV_eq_of_extension (D := FFModel.nat (StatedSp 2 K))
      (LM := KGNat.linModelNat (StatedSp 2 K)) hW hreal hcomm hp hpK hpodd hcentral hfix
      (fun T hT => KGNat.commutant_statedSp T hT) hupper
  obtain ⟨π, hπ⟩ := hreal
  have hWcard :=
    CFSG.Quasithin.FFC.card_eq_of_realizes
      (D := FFModel.nat (StatedSp 2 K)) rfl hπ
  have hsec : Nat.card (FFModel.nat (StatedSp 2 K)).sec = Nat.card K ^ 4 := by
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) = Nat.card K ^ 4
    rw [Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 ⊕ Fin 2 → K) ≃ (Fin 2 ⊕ Fin 2 → K)),
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2 ⊕ Fin 2),
      Fintype.card_sum, Fintype.card_fin]
  refine ⟨hZ, ?_⟩
  rw [Subgroup.card_top, hZ, hsec] at hWcard
  rw [hWcard]
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
