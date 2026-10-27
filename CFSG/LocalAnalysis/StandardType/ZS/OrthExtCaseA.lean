module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtPartner

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem reflSubgroupIn_top_eq {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ReflGen p F) :
    reflSubgroupIn p F ⊤ = F :=
  le_antisymm (reflSubgroupIn_le F ⊤) (le_reflSubgroupIn (le_refl F) hF le_top)

private theorem ker_sub_one_eq_ker_polarBilin (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {e : U} (hQe : Q e ≠ 0) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) (hti : IsIsom p Q t)
    (hte : t e = -e) :
    LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have hspan : HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {e} :=
    IsRefl.movedSpace_eq_span hp ht hte he0
  have hkey : ∀ y, QuadraticMap.polar Q e (t y) = -QuadraticMap.polar Q e y := by
    intro y
    have hpol : QuadraticMap.polar Q (t e) (t y) = QuadraticMap.polar Q e y :=
      hti.polar_apply e y
    rw [hte, QuadraticMap.polar_neg_left] at hpol
    simpa using congrArg Neg.neg hpol
  have hval : ∀ y, ((t : U →ₗ[ZMod p] U) - 1) y = 0 ↔ t y = y := by
    intro y
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, LinearEquiv.coe_coe]
  ext x
  change ((t : U →ₗ[ZMod p] U) - 1) x = 0 ↔ QuadraticMap.polarBilin Q e x = 0
  rw [hval x, QuadraticMap.polarBilin_apply_apply]
  constructor
  · intro hx
    have h := hkey x
    rw [hx] at h
    exact eq_zero_of_eq_neg h2 h
  · intro hx
    have h := hkey x
    rw [hx, neg_zero] at h
    have hmem : t x - x ∈ HardMathSupport.Kantor79.movedSpace t := ⟨x, rfl⟩
    rw [hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc' : c • e = t x - x := hc
    have hc0 : c = 0 := by
      have hpolar : QuadraticMap.polar Q e (t x - x) = c * (2 * Q e) := by
        rw [← hc', CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
          CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
      rw [QuadraticMap.polar_sub_right, h, hx, sub_zero] at hpolar
      exact (mul_eq_zero.mp hpolar.symm).resolve_right (mul_ne_zero h2 hQe)
    exact sub_eq_zero.mp (by rw [← hc', hc0, zero_smul])

theorem exists_isOrthOn_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) :
    ∃ (Q : QuadraticForm (ZMod p) U) (e : U),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ IsOrthOn p Q H ∧ e ≠ 0 ∧ Q e ≠ 0 ∧
        h e = -e ∧ e ∈ centralizerSpace B ∧
        e ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  have hn : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by
    have := hD.setting.four_le
    omega
  obtain ⟨f, hf, hf0⟩ := hD.setting.sub.2.1.exists_mem_centralizerSpace_ne_zero hn
  obtain ⟨Q, hQ, hoH, -⟩ := exists_isOrthOn_of_isOrthType_movedGroup hp
    hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 hf hf0 one_ne_zero
  obtain ⟨e, hQe, hee⟩ :=
    DimThree.exists_root_of_isRefl_isIsom hp hQ hD.isRefl (hoH.isIsom hD.mem)
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have hem : e ∈ HardMathSupport.Kantor79.movedSpace h :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hee
  have heVH : e ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem hem
  obtain ⟨-, hCB⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  exact ⟨Q, e, hQ, hoH, he0, hQe, hee, by rw [hCB]; exact hem, heVH⟩

private theorem smul_add_apply_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H) {x : U}
    (hx : x ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    (2 : ZMod p)⁻¹ • (x + h x) ∈
      HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
  have hE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    commutatorSpace_reflStab (X := H) (m := Module.finrank (ZMod p) U - 1) hp hQ
      hD.setting.sub.2.1 (by have := hD.setting.four_le; omega) (fun hp3 => by
        have h := hD.setting.five_le_of_eq_three hp3
        omega) hoH hD.mem hD.isRefl
  have hhx : ∀ y, h (h y) = y := by
    intro y
    simpa [LinearEquiv.mul_apply] using congrArg (fun f : U ≃ₗ[ZMod p] U => f y) hD.isRefl.1
  rw [hE]
  refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hx (apply_mem_commutatorSpace hD.mem hx)),
    LinearMap.mem_ker.mpr ?_⟩
  have hfix : h ((2 : ZMod p)⁻¹ • (x + h x)) = (2 : ZMod p)⁻¹ • (x + h x) := by
    rw [map_smul, map_add, hhx, add_comm]
  exact sub_eq_zero.mpr hfix

private theorem smul_sub_apply_mem_movedSpace {x : U} (h2 : (2 : ZMod p) ≠ 0)
    (hh : h * h = 1) :
    (2 : ZMod p)⁻¹ • (x - h x) ∈ HardMathSupport.Kantor79.movedSpace h := by
  have hhx : ∀ y, h (h y) = y := by
    intro y
    simpa [LinearEquiv.mul_apply] using congrArg (fun f : U ≃ₗ[ZMod p] U => f y) hh
  refine HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 ?_
  have hneg : h (x - h x) = -(x - h x) := by
    rw [map_sub, hhx]
    abel
  rw [map_smul, hneg, smul_neg]

private theorem map_commutatorSpace_eq_self_of_apply_eq_smul (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ B) {ζ : ZMod p}
    (hgζ : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), g v = ζ • v) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  obtain ⟨-, hCB⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq g _)
  rintro - ⟨x, hx, rfl⟩
  have hsum : (2 : ZMod p)⁻¹ • (x + h x) + (2 : ZMod p)⁻¹ • (x - h x) = x := by
    rw [← smul_add, show (x + h x) + (x - h x) = (2 : ZMod p) • x by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hy : g ((2 : ZMod p)⁻¹ • (x + h x)) = ζ • ((2 : ZMod p)⁻¹ • (x + h x)) :=
    hgζ _ (smul_add_apply_mem_reflStab hp hD hQ hoH hx)
  have hz : g ((2 : ZMod p)⁻¹ • (x - h x)) = (2 : ZMod p)⁻¹ • (x - h x) :=
    mem_centralizerSpace.mp (by rw [hCB]; exact smul_sub_apply_mem_movedSpace h2 hD.isRefl.1) g hg
  have hgx : g x = ζ • ((2 : ZMod p)⁻¹ • (x + h x)) + (2 : ZMod p)⁻¹ • (x - h x) := by
    calc g x = g ((2 : ZMod p)⁻¹ • (x + h x) + (2 : ZMod p)⁻¹ • (x - h x)) := by rw [hsum]
      _ = ζ • ((2 : ZMod p)⁻¹ • (x + h x)) + (2 : ZMod p)⁻¹ • (x - h x) := by
          rw [map_add, hy, hz]
  change g x ∈ HardMathSupport.Kantor79.commutatorSpace H
  rw [hgx]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
  · exact HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le H _)
      (smul_add_apply_mem_reflStab hp hD hQ hoH hx)
  · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (smul_sub_apply_mem_movedSpace h2 hD.isRefl.1)

private theorem exists_mem_reflStab_ne_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H) {e : U}
    (hQe : Q e ≠ 0) (heVH : e ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hee : h e = -e) :
    ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q w ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have hker := ker_sub_one_eq_ker_polarBilin hp hQe hD.isRefl (hoH.isIsom hD.mem) hee
  have hE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    commutatorSpace_reflStab (X := H) (m := Module.finrank (ZMod p) U - 1) hp hQ
      hD.setting.sub.2.1 (by have := hD.setting.four_le; omega) (fun hp3 => by
        have h := hD.setting.five_le_of_eq_three hp3
        omega) hoH hD.mem hD.isRefl
  have hS1 : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace H) :=
    polarNondegOn_commutatorSpace hQ (fun g hg => hoH.isIsom hg) hD.setting.sub.2.1.1
  have hS2 : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) := by
    rw [hE, hker]
    exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2 hS1 heVH hQe
  have he_ker : e ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro hmem
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
    refine he0 (eq_zero_of_eq_neg h2 ?_)
    exact hmem.symm.trans hee
  have hfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) + 1 =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) := by
    rw [hE]
    exact IsRefl.finrank_inf_ker_sub_one_add_one hp hD.isRefl heVH he_ker
  have hne : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    have hdim := hD.setting.sub.2.1.2.1
    have h4 := hD.setting.four_le
    omega
  exact hS2.exists_map_ne_zero hne

theorem false_of_map_commutatorSpace_eq_of_apply_eq_smul (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ B)
    (hgV : (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H)
    {w : U} (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace H) (hQw : Q w ≠ 0) {ζ : ZMod p}
    (hζ : ζ * ζ ≠ 1) (hgw : g w = ζ • w) : False := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  obtain ⟨e, hQe, hee⟩ :=
    DimThree.exists_root_of_isRefl_isIsom hp hQ hD.isRefl (hoH.isIsom hD.mem)
  have hem : e ∈ HardMathSupport.Kantor79.movedSpace h :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hee
  obtain ⟨-, hCB⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  have heCB : e ∈ centralizerSpace B := by rw [hCB]; exact hem
  have htop : reflSubgroupIn p H ⊤ = H := reflSubgroupIn_top_eq hD.setting.sub.1
  have hY : AbsIrred p (movedGroup (reflSubgroupIn p H ⊤)) := by
    rw [htop]
    exact absIrred_of_reflGen (reflGen_movedGroup hD.setting.sub.1)
      (irred_movedGroup_of_splitSupport hD.setting.sub.2.1)
  have hgV' : (HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H ⊤)).map
      (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H ⊤) := by
    rw [htop]
    exact hgV
  have hu : e ∈ HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H ⊤) := by
    rw [htop]
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem hem
  have hw' : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H ⊤) := by
    rw [htop]
    exact hw
  exact false_of_map_eq_of_apply_eq_smul hp hD.setting hD.mem_of_le hoH (W := ⊤) hY
    (hD.split.1 hg) hgV' hu hw' hQe hQw (mem_centralizerSpace.mp heCB g hg) hζ hgw

theorem false_of_mem_smul (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ B) {ζ : ZMod p}
    (hζ : ζ * ζ ≠ 1)
    (hgζ : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), g v = ζ • v) :
    False := by
  obtain ⟨Q, e, hQ, hoH, -, hQe, hee, -, heVH⟩ := exists_isOrthOn_root hp hD
  obtain ⟨w, hwE, hQw⟩ := exists_mem_reflStab_ne_zero hp hD hQ hoH hQe heVH hee
  exact false_of_map_commutatorSpace_eq_of_apply_eq_smul hp hD hQ hoH hg
    (map_commutatorSpace_eq_self_of_apply_eq_smul hp hD hQ hoH hg hgζ)
    (HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le H _) hwE) hQw hζ
    (hgζ w hwE)

private theorem exists_form_of_isIsom_mem_B (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g) :
    ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      IsOrthOn p Q H ∧ ∀ g ∈ B, IsIsom p Q g :=
  exists_isOrthOn_of_lemmaTwoSevenData hp hD (exists_eq_mul_of_irredOnSection hp hD hirr₁ hψ)

theorem exists_isOrthOvergroup_of_isOrthType_of_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hd₁ : p = 3 → ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (horth : IsOrthType p (movedGroup B)) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    (hBQ : ∀ g ∈ B, IsIsom p Q g) : ∃ K, IsOrthOvergroup p G H K := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  obtain ⟨hVB, -⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  have hoB : IsOrthOn p Q B :=
    isOrthOn_of_isOrthType_movedGroup hp hQ hD.split.2.1 hD.split.2.2.1 hBQ horth
  refine exists_isOrthOvergroup_of_isOrthOn hp hD.setting hQ (X := B) hD.split.1
    hD.split.2.1 hD.split.2.2.1 ?_ hoH hoB ?_
  · intro hp3
    obtain ⟨x, hx, y, hy, hxr, hyr, hlt⟩ := hd₁ hp3
    exact ⟨x, hD.split.2.2.2.2 hx, y, hD.split.2.2.2.2 hy, hxr, hyr, hlt⟩
  · intro v hv
    rw [hVB, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact mem_centralizerSpace.mp hv h hD.mem

theorem exists_isOrthOvergroup_of_isOrthType_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hd₁ : p = 3 → ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (horth : IsOrthType p (movedGroup B)) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨_, e, _, _, he0, _, _, heCB, _⟩ := exists_isOrthOn_root hp hD
  have hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g := by
    obtain ⟨Q₂, hQ₂, hoB₂, -⟩ := exists_isOrthOn_of_isOrthType_movedGroup hp
      hD.split.2.2.1 horth heCB he0 (c := 1) one_ne_zero
    exact ⟨Q₂, hQ₂, fun g hg => hoB₂.isIsom hg⟩
  obtain ⟨Q, hQ, hoH, hBQ⟩ := exists_form_of_isIsom_mem_B hp hD hirr₁ hψ
  exact exists_isOrthOvergroup_of_isOrthType_of_isIsom hp hD hd₁ horth hQ hoH hBQ

private theorem eq_one_of_pow_eq_one_of_not_dvd (hD : LemmaTwoSevenData p G H B h)
    (hdvd : ¬ p ∣ Nat.card (movedGroup B)) : ∀ g ∈ B, g ^ p = 1 → g = 1 := by
  rw [card_movedGroup_of_splitSupport (X := B) hD.split.2.2.1] at hdvd
  intro g hg hgp
  have h1 : orderOf g ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hg
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hgp) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h1
    exact absurd h1 hdvd

theorem exists_isOrthOvergroup_of_not_dvd_card (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hdvd : ¬ p ∣ Nat.card (movedGroup B))
    (hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨Q, hQ, hoH, hBQ⟩ := exists_form_of_isIsom_mem_B hp hD hirr₁ hψ
  have hcop := eq_one_of_pow_eq_one_of_not_dvd hD hdvd
  have hn : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by
    have := hD.setting.four_le
    omega
  obtain ⟨f, hf, hf0⟩ := hD.setting.sub.2.1.exists_mem_centralizerSpace_ne_zero hn
  obtain ⟨b, hb, hbf⟩ := exists_mem_polar_sq_ne hp hD h4 hirr₁ hQ hoH hBQ hcop hf hf0
  exact exists_isOrthOvergroup_of_polar_sq_ne hp hD.setting hQ hoH (hD.split.1 hb) (hBQ b hb)
    hf hbf

theorem exists_isOrthOvergroup_of_card_movedGroup_eq_120 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p ≠ 5)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hcard : Nat.card (movedGroup B) = 120)
    (hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g) :
    ∃ K, IsOrthOvergroup p G H K := by
  have hp3 : p ≠ 3 := by
    intro h3
    have := hD.setting.five_le_of_eq_three h3
    omega
  refine exists_isOrthOvergroup_of_not_dvd_card hp hD h4 hirr₁ ?_ hψ
  rw [hcard, show (120 : ℕ) = 2 ^ 3 * 3 * 5 by norm_num]
  intro hd
  have hpr : p.Prime := Fact.out
  rcases hpr.dvd_mul.mp hd with h | h
  · rcases hpr.dvd_mul.mp h with h2' | h3'
    · exact hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h2'))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp h3')
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hpr (by norm_num : Nat.Prime 5)).mp h)

end CFSG.StandardType.ZS

end
