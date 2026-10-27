module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSixMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSixAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFix3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bc_sumOfNat_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {U : Subgroup W} (h : SumOfNat N H U ⊥ 2) :
    ∃ J₀ J₁ : Subgroup W, N H J₀ ⊥ ∧ N H J₁ ⊥ ∧ J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = U := by
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

private theorem s16c13bc_isIrr_of_isIrrOn {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    {J : Subgroup W} (h : IsIrrOn A J ⊥) : XMod.IsIrr ↥A J := by
  unfold IsIrrOn StableUnder at h
  unfold XMod.IsIrr XMod.IsIrrSec XMod.IsInv
  obtain ⟨hlt, hstab, -, hmin⟩ := h
  exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
    fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩

theorem s16c13bc_six_modules (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h6 : Case168_6 D ⊥ V hV L) :
    _root_.commutator ↥(lBar ⊥ V hV L) = ⊤ ∧ Subgroup.center ↥(lBar ⊥ V hV L) = ⊥ ∧
      ∃ J₀ J₁ : Subgroup (Vtil ⊥ V hV),
        XMod.IsIrr ↥(lBar ⊥ V hV L) J₀ ∧ XMod.IsIrr ↥(lBar ⊥ V hV L) J₁ ∧ J₀ ⊓ J₁ = ⊥ ∧
        J₀ ⊔ J₁ = wTil ⊥ V hV L ∧ J₀ ⊓ fixV (lBar ⊥ V hV L) = ⊥ ∧
        Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₀ ∧ Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₁ ∧
        ∀ n ∈ J₀, n ≠ 1 → ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ n = n := by
  obtain ⟨-, hfam, -, -⟩ := h6
  rcases hfam with ⟨hA, hsum⟩ | ⟨hL3, hsum⟩
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c13bc_sumOfNat_two hsum
    have hf₀ : J₀ ⊓ fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix_alt (by norm_num) hN₀
    have hirr₀ := (s16c167_mem_irrSet_alt (by norm_num) hN₀).2
    have hf₁ : J₁ ⊓ fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix_alt (by norm_num) hN₁
    have hirr₁ := (s16c167_mem_irrSet_alt (by norm_num) hN₁).2
    rw [hf₀] at hirr₀
    rw [hf₁] at hirr₁
    exact ⟨s16c1610_commutator_of_isAlt (by norm_num) hA,
      s16c1610_center_of_isAlt (by norm_num) hA, J₀, J₁, s16c13bc_isIrr_of_isIrrOn hirr₀,
      s16c13bc_isIrr_of_isIrrOn hirr₁, hinf, hsup, hf₀, s16c167_endUnits_alt (by norm_num) hN₀,
      s16c167_endUnits_alt (by norm_num) hN₁, s16c13bc_fix3_alt (by norm_num) hN₀⟩
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c13bc_sumOfNat_two hsum
    have hf₀ : J₀ ⊓ fixV (lBar ⊥ V hV L) = ⊥ :=
      s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by norm_num) hN₀
    have hirr₀ := (s16c167_mem_irrSet_ln (by norm_num) hN₀).2
    have hf₁ : J₁ ⊓ fixV (lBar ⊥ V hV L) = ⊥ :=
      s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by norm_num) hN₁
    have hirr₁ := (s16c167_mem_irrSet_ln (by norm_num) hN₁).2
    rw [hf₀] at hirr₀
    rw [hf₁] at hirr₁
    exact ⟨s16c1610_commutator_of_isL3 hL3, center_eq_bot_of_isL3 hL3, J₀, J₁,
      s16c13bc_isIrr_of_isIrrOn hirr₀, s16c13bc_isIrr_of_isIrrOn hirr₁, hinf, hsup, hf₀,
      s16c167_endUnits_ln (by norm_num) hN₀, s16c167_endUnits_ln (by norm_num) hN₁,
      s16c13bc_fix3_sl (by norm_num) hN₀⟩

private theorem s16c13bc_stab_of_map_eq {T : Type*} [CommGroup T] {W : Subgroup T}
    {e : MulAut T} (h : W.map e.toMonoidHom = W) : e ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := e.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rwa [h] at hu'

private theorem s16c13bc_map_conj_eq_of_commute {Γ : Type*} [Group Γ] {A : Subgroup Γ} {z : Γ}
    (h : ∀ l ∈ A, z * l = l * z) : A.map (MulAut.conj z).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h1 : z * l * z⁻¹ = l := by rw [h l hl]; group
    show z * l * z⁻¹ ∈ A
    rw [h1]
    exact hl
  · intro hx
    refine ⟨x, hx, ?_⟩
    show z * x * z⁻¹ = x
    rw [h x hx]
    group

private theorem s16c13bc_mem_normalizer_of_map_eq {Γ : Type*} [Group Γ] {A : Subgroup Γ} {g : Γ}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at h1
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have hxy : y = x := by simpa using hyx'
    rwa [hxy] at hy

private theorem s16c13bc_map_eq_of_mem_normalizer {Γ : Type*} [Group Γ] {A : Subgroup Γ} {g : Γ}
    (h : g ∈ Subgroup.normalizer (A : Set Γ)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 h y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.1 h x).1 hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

private theorem s16c13bc_wTil_map_conj (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) (x : MulAut (Vtil V₀ V hV)) :
    (wTil V₀ V hV L).map x.toMonoidHom =
      commSub ⊤ ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom) :=
  (s15_Infra_commSub_top_map_conj (lBar V₀ V hV L) x).symm

private theorem s16c13bc_wTil_map_eq (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) {x : MulAut (Vtil V₀ V hV)}
    (h : (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = lBar V₀ V hV L) :
    (wTil V₀ V hV L).map x.toMonoidHom = wTil V₀ V hV L := by
  rw [s16c13bc_wTil_map_conj, h]
  rfl

theorem s16c13bc_six_nonswap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (hp : (3 : ℕ) ∈ D.sig) {Z : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hZM : Z ≤ Mbar D.M ⊥ V hV) (hZc : Nat.card Z = 3)
    (hZn : ∀ m ∈ Mbar D.M ⊥ V hV, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z)
    (hLp : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤) (hLc : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥)
    (hs : s15 D.M ⊥ V hV L = 2) (hψ₀ : ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3)
    (hall : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L) :
    Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hW : wTil ⊥ V hV L ≠ ⊥ := fun h0 => hc.ne_bot (s15_Lin_eq_bot_of_commSub_top_eq_bot h0)
  have hst : barSub ⊥ V hV (E3.wClos V D.k D.T) ≤ stabSub (wTil ⊥ V hV L) := fun w hw =>
    s16c13bc_stab_of_map_eq (s16c13bc_wTil_map_eq ⊥ V hV L (hall w hw))
  obtain ⟨n, hnW, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h hW hst
  obtain ⟨g, hgM, -, hfix⟩ := s16c13bc_exists_other_conj D hV hH hs
  set B : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    (lBar ⊥ V hV L).map (MulAut.conj g).toMonoidHom with hB
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  haveI : Group.IsPerfect ↥(lBar ⊥ V hV L) := Group.isPerfect_def.2 hLp
  have hBp : _root_.commutator ↥B = ⊤ :=
    Group.isPerfect_def.1 (Group.IsPerfect.map (H := lBar ⊥ V hV L) (MulAut.conj g).toMonoidHom)
  have hBc : Subgroup.center ↥B = ⊥ := s16c13bc_center_map_eq_bot _ hinj hLc
  have hBM : B ≤ Mbar D.M ⊥ V hV := by
    rintro _ ⟨a, ha, rfl⟩
    have haM : a ∈ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le ha
    show g * a * g⁻¹ ∈ Mbar D.M ⊥ V hV
    exact (Mbar D.M ⊥ V hV).mul_mem ((Mbar D.M ⊥ V hV).mul_mem hgM haM)
      ((Mbar D.M ⊥ V hV).inv_mem hgM)
  obtain ⟨ψ₀, hψ₀L, hψ₀o⟩ := hψ₀
  have hψB : g * ψ₀ * g⁻¹ ∈ B := ⟨ψ₀, hψ₀L, rfl⟩
  have hψo : orderOf (g * ψ₀ * g⁻¹) = 3 := by
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom hinj ψ₀
    rw [hψ₀o] at h1
    exact h1
  have hψ1 : g * ψ₀ * g⁻¹ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψZ : g * ψ₀ * g⁻¹ ∉ Z :=
    s16c13bc_not_mem_of_perfect (by norm_num) hBp hBc hZc
      (fun m hm x hx => hZn m (hBM hm) x hx) hψB hψ1
  exact s16c13bc_insp_of_normal_prime D h hcomm hp hZM hZc hZn hn1 hnfix (hBM hψB) hψo hψZ
    (hfix _ hψB n hnW)

theorem s16c13bc_swap_fixed {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Lb Wb : Subgroup (MulAut W)} (hP2 : IsPGroup 2 Wb) {t : MulAut W} (htW : t ∈ Wb)
    (hpair : ∀ w ∈ Wb, Lb.map (MulAut.conj w).toMonoidHom = Lb ∨
      Lb.map (MulAut.conj w).toMonoidHom = Lb.map (MulAut.conj t).toMonoidHom)
    (hsq : Lb.map (MulAut.conj (t * t)).toMonoidHom = Lb)
    (hstable : ∀ w ∈ Wb, Lb.map (MulAut.conj w).toMonoidHom = Lb →
      (Lb.map (MulAut.conj t).toMonoidHom).map (MulAut.conj w).toMonoidHom =
        Lb.map (MulAut.conj t).toMonoidHom)
    {Wt J₀ : Subgroup W} (hJW : J₀ ≤ Wt) (hJ₀ : J₀ ≠ ⊥)
    (hfixt : ∀ b ∈ Lb.map (MulAut.conj t).toMonoidHom, ∀ x ∈ Wt, b x = x)
    (hfix₀ : J₀ ⊓ fixV Lb = ⊥)
    (hst : ∀ w ∈ Wb, Lb.map (MulAut.conj w).toMonoidHom = Lb → J₀.map w.toMonoidHom = J₀) :
    ∃ a ∈ J₀, a ≠ 1 ∧ ∃ n : W, n ≠ 1 ∧ (∀ w ∈ Wb, w n = n) ∧
      ∀ ψ ∈ Lb, ψ a = a → ψ n = n := by
  classical
  have hinvt : Lb.map (MulAut.conj t⁻¹).toMonoidHom = Lb.map (MulAut.conj t).toMonoidHom := by
    apply s16c13bc_map_conj_inj t
    rw [← s16c13bc_map_conj_mul, ← s16c13bc_map_conj_mul, mul_inv_cancel, s16c13bc_map_conj_one,
      hsq]
  have hL'inv : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb.map (MulAut.conj t).toMonoidHom := by
    intro l hl
    rw [← hinvt]
    refine ⟨l, hl, ?_⟩
    show t⁻¹ * l * t⁻¹⁻¹ = t⁻¹ * l * t
    rw [inv_inv]
  have hbt : ∀ b ∈ Lb, ∀ x ∈ Wt, b (t x) = t x := by
    intro b hb x hx
    have h1 : (t⁻¹ * b * t) x = x := hfixt _ (hL'inv b hb) x hx
    have e : b * t = t * (t⁻¹ * b * t) := by group
    calc b (t x) = (b * t) x := rfl
      _ = (t * (t⁻¹ * b * t)) x := by rw [e]
      _ = t ((t⁻¹ * b * t) x) := rfl
      _ = t x := by rw [h1]
  set N : Subgroup (MulAut W) := Wb ⊓ Subgroup.normalizer (Lb : Set (MulAut W)) with hN
  have hNmem : ∀ w ∈ Wb, Lb.map (MulAut.conj w).toMonoidHom = Lb → w ∈ N :=
    fun w hw hn => ⟨hw, s16c13bc_mem_normalizer_of_map_eq hn⟩
  have hNWb : ∀ w ∈ N, w ∈ Wb := fun w hw => (Subgroup.mem_inf.1 hw).1
  have hNmap : ∀ w ∈ N, Lb.map (MulAut.conj w).toMonoidHom = Lb :=
    fun w hw => s16c13bc_map_eq_of_mem_normalizer (Subgroup.mem_inf.1 hw).2
  have hNtN : ∀ w ∈ N, t⁻¹ * w * t ∈ N := by
    intro w hw
    refine hNmem _ (Wb.mul_mem (Wb.mul_mem (Wb.inv_mem htW) (hNWb w hw)) htW) ?_
    rw [s16c13bc_map_conj_mul, s16c13bc_map_conj_mul, hstable w (hNWb w hw) (hNmap w hw),
      s16c13bc_map_conj_cancel]
  have htt : t * t ∈ N := hNmem _ (Wb.mul_mem htW htW) hsq
  obtain ⟨a, haJ, ha1, haN⟩ := s16_LemmaP_exists_fixed hW (hP2.to_le (inf_le_left : N ≤ Wb)) hJ₀
    (fun w hw x hx => by
      have h1 : w x ∈ J₀.map w.toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hst w (hNWb w hw) (hNmap w hw)] at h1)
  have hta : ∀ w ∈ N, w (t a) = t a := by
    intro w hw
    have h1 : (t⁻¹ * w * t) a = a := haN _ (hNtN w hw)
    have e : w * t = t * (t⁻¹ * w * t) := by group
    calc w (t a) = (w * t) a := rfl
      _ = (t * (t⁻¹ * w * t)) a := by rw [e]
      _ = t ((t⁻¹ * w * t) a) := rfl
      _ = t a := by rw [h1]
  have hn_t : t (a * t a) = a * t a := by
    have h1 : (t * t) a = a := haN _ htt
    rw [map_mul]
    calc t a * t (t a) = t a * (t * t) a := rfl
      _ = t a * a := by rw [h1]
      _ = a * t a := mul_comm _ _
  have hn_N : ∀ w ∈ N, w (a * t a) = a * t a := by
    intro w hw
    rw [map_mul, haN w hw, hta w hw]
  refine ⟨a, haJ, ha1, a * t a, ?_, ?_, ?_⟩
  · intro hn1
    have hta' : t a = a := by
      have h1 : t a = a⁻¹ := eq_inv_of_mul_eq_one_right hn1
      have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW a)
      rw [h1, h2]
    have hfixa : a ∈ fixV Lb := by
      rw [mem_fixV]
      intro l hl
      calc l a = l (t a) := by rw [hta']
        _ = t a := hbt l hl a (hJW haJ)
        _ = a := hta'
    have hmem : a ∈ J₀ ⊓ fixV Lb := ⟨haJ, hfixa⟩
    rw [hfix₀, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  · intro w hw
    by_cases hwn : Lb.map (MulAut.conj w).toMonoidHom = Lb
    · exact hn_N w (hNmem w hw hwn)
    · have hwt : Lb.map (MulAut.conj w).toMonoidHom = Lb.map (MulAut.conj t).toMonoidHom :=
        (hpair w hw).resolve_left hwn
      have htw : t * w ∈ N := by
        refine hNmem _ (Wb.mul_mem htW hw) ?_
        rw [s16c13bc_map_conj_mul, hwt, ← s16c13bc_map_conj_mul]
        exact hsq
      have h1 := hn_N (t * w) htw
      have h2 : t (w (a * t a)) = t (a * t a) := by
        rw [hn_t]
        exact h1
      exact t.injective h2
  · intro ψ hψ hψa
    rw [map_mul, hψa, hbt ψ hψ a (hJW haJ)]

theorem s16c13bc_six_swap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (hp : (3 : ℕ) ∈ D.sig) {Z : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hZM : Z ≤ Mbar D.M ⊥ V hV) (hZc : Nat.card Z = 3)
    (hZn : ∀ m ∈ Mbar D.M ⊥ V hV, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z)
    (hLp : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤) (hLc : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥)
    (hs : s15 D.M ⊥ V hV L = 2) {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (hJ₀ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₀) (hJ₁ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₁)
    (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = wTil ⊥ V hV L)
    (hfix₀ : J₀ ⊓ fixV (lBar ⊥ V hV L) = ⊥) (hE₀ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₀)
    (hE₁ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₁)
    (hψ₃ : ∀ n ∈ J₀, n ≠ 1 → ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ n = n)
    {t : MulAut (Vtil ⊥ V hV)} (htW : t ∈ barSub ⊥ V hV (E3.wClos V D.k D.T))
    (htne : (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom ≠ lBar ⊥ V hV L) :
    Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  have hWM : barSub ⊥ V hV (E3.wClos V D.k D.T) ≤ Mbar D.M ⊥ V hV :=
    barSub_mono ⊥ V hV (hWT.trans D.sylowM.le)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP2 : IsPGroup 2 ↥(barSub ⊥ V hV (E3.wClos V D.k D.T)) :=
    s15_LP_isPGroup_barSub hV (D.sylowM.isPGroup.to_le hWT)
  have hM2 : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ φ ∈ Mbar D.M ⊥ V hV,
      Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs
    exact hs
  have htM : t ∈ Mbar D.M ⊥ V hV := hWM htW
  have hpair : ∀ w ∈ Mbar D.M ⊥ V hV, (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom =
      lBar ⊥ V hV L ∨ (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom =
        (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom := s16c13bc_conj_mem_pair htM htne hM2
  have hsq := s16c13bc_conj_sq htM htne hM2
  have hfixt : ∀ b ∈ (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom,
      ∀ x ∈ wTil ⊥ V hV L, b x = x := by
    obtain ⟨g, hgM, hgne, hfix⟩ := s16c13bc_exists_other_conj D hV hH hs
    have hgt := (hpair g hgM).resolve_left hgne
    intro b hb x hx
    rw [← hgt] at hb
    exact hfix b hb x hx
  have hVsup : wTil ⊥ V hV L ⊔ (wTil ⊥ V hV L).map t.toMonoidHom = ⊤ := by
    obtain ⟨-, -, -, -, -, hW1, -⟩ := hc.conc
    refine top_le_iff.1 ?_
    rw [← hW1]
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hgM, rfl⟩ := hX
    change (wTil ⊥ V hV L).map g.toMonoidHom ≤ _
    rw [s16c13bc_wTil_map_conj ⊥ V hV L g]
    rcases hpair g hgM with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1, ← s16c13bc_wTil_map_conj ⊥ V hV L t]
      exact le_sup_right
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZc])
  have hzo : orderOf (z : MulAut (Vtil ⊥ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hz3 : (z : MulAut (Vtil ⊥ V hV)) ^ 3 = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one _
  have hZO : Z ≤ oddBar D.M ⊥ V hV := s16c13bc_le_oddBar hV hZM hZn (hZc ▸ ⟨1, rfl⟩)
  have hzw : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (z : MulAut (Vtil ⊥ V hV)) * w = w * (z : MulAut (Vtil ⊥ V hV)) := by
    intro w hw
    have h1 : ⁅(z : MulAut (Vtil ⊥ V hV)), w⁆ ∈
        ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ :=
      Subgroup.commutator_mem_commutator (hZO z.2) hw
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hzL' := s16c13bc_commute_of_perfect Nat.prime_three hLp hZc
    (fun m hm x hx => hZn m (hLM hm) x hx)
  have hzL : ∀ l ∈ lBar ⊥ V hV L, (z : MulAut (Vtil ⊥ V hV)) * l =
      l * (z : MulAut (Vtil ⊥ V hV)) := fun l hl => (hzL' l hl z z.2).symm
  have hzW : (J₀ ⊔ J₁).map (z : MulAut (Vtil ⊥ V hV)).toMonoidHom = J₀ ⊔ J₁ := by
    rw [hsup]
    exact s16c13bc_wTil_map_eq ⊥ V hV L (s16c13bc_map_conj_eq_of_commute hzL)
  have hzne : ∃ u ∈ J₀ ⊔ J₁, (z : MulAut (Vtil ⊥ V hV)) u ≠ u := by
    by_contra hcon
    have hfixW : ∀ u ∈ wTil ⊥ V hV L, (z : MulAut (Vtil ⊥ V hV)) u = u := by
      intro u hu
      by_contra hne
      exact hcon ⟨u, hsup ▸ hu, hne⟩
    have hfixWt : ∀ u ∈ (wTil ⊥ V hV L).map t.toMonoidHom,
        (z : MulAut (Vtil ⊥ V hV)) u = u := by
      rintro _ ⟨x, hx, rfl⟩
      calc (z : MulAut (Vtil ⊥ V hV)) (t x) = ((z : MulAut (Vtil ⊥ V hV)) * t) x := rfl
        _ = (t * (z : MulAut (Vtil ⊥ V hV))) x := by rw [hzw t htW]
        _ = t ((z : MulAut (Vtil ⊥ V hV)) x) := rfl
        _ = t x := by rw [hfixW x hx]
    have hall : ∀ u : Vtil ⊥ V hV, (z : MulAut (Vtil ⊥ V hV)) u = u := by
      intro u
      have hu : u ∈ wTil ⊥ V hV L ⊔ (wTil ⊥ V hV L).map t.toMonoidHom := by
        rw [hVsup]
        exact Subgroup.mem_top u
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
      rw [map_mul, hfixW a ha, hfixWt b hb]
    have hz1 : (z : MulAut (Vtil ⊥ V hV)) = 1 := MulEquiv.ext hall
    rw [hz1, orderOf_one] at hzo
    omega
  have hst : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L →
        J₀.map w.toMonoidHom = J₀ := by
    intro w hw hwn
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨w, hw⟩
    have hwpow : w ^ 2 ^ b = 1 := by
      have h1 : orderOf w = 2 ^ b :=
        (Subgroup.orderOf_coe (⟨w, hw⟩ : ↥(barSub ⊥ V hV (E3.wClos V D.k D.T)))).trans hb
      rw [← h1]
      exact pow_orderOf_eq_one w
    exact s16c13bc_stab_of_cyclic hJ₀ hJ₁ hinf hE₀ hE₁ hz3 hzL hzW hzne
      (s16c13bc_mem_normalizer_of_map_eq hwn)
      (by rw [hsup]; exact s16c13bc_wTil_map_eq ⊥ V hV L hwn) (hzw w hw).symm hwpow
  have hJW : J₀ ≤ wTil ⊥ V hV L := hsup ▸ le_sup_left
  obtain ⟨a, haJ, ha1, n, hn1, hnfix, hψn⟩ := s16c13bc_swap_fixed
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hP2 htW
    (fun w hw => hpair w (hWM hw)) hsq
    (fun w hw hwn => s16c13bc_conj_pair_stable htM htne hM2 (hWM hw) hwn) hJW hJ₀.2.1.ne' hfixt
    hfix₀ hst
  obtain ⟨ψ, hψL, hψo, hψa⟩ := hψ₃ a haJ ha1
  have hψ1 : ψ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψZ : ψ ∉ Z := s16c13bc_not_mem_of_perfect Nat.prime_three hLp hLc hZc
    (fun m hm x hx => hZn m (hLM hm) x hx) hψL hψ1
  exact s16c13bc_insp_of_normal_prime D h hcomm hp hZM hZc hZn hn1 (mem_fixV.2 hnfix) (hLM hψL)
    hψo hψZ (hψn ψ hψL hψa)

theorem s16c13bc_case168_6 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (h6 : Case168_6 D ⊥ V hV L) : Insp1613U D V := by
  have hmods := s16c13bc_six_modules D h6
  obtain ⟨⟨e⟩, -, hs, hσ⟩ := h6
  obtain ⟨hLp, hLc, J₀, J₁, hJ₀, hJ₁, hinf, hsup, hfix₀, hE₀, hE₁, hψ₃⟩ := hmods
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 3
  have hQ : Subgroup.center (↥(lBar ⊥ V hV L) × ↥(lBar ⊥ V hV L)) = ⊥ := by
    rw [Subgroup.center_prod, hLc, Subgroup.bot_prod_bot]
  obtain ⟨Z, -, hZM, hZc, hZn, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 3) hQ e
  obtain ⟨n₀, hn₀J, hn₀1⟩ : ∃ n ∈ J₀, n ≠ 1 := by
    obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hJ₀.2.1.ne'
    exact ⟨n, hn, fun h1 => hn1 (Subtype.ext h1)⟩
  by_cases hall : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L
  · obtain ⟨ψ₀, hψ₀L, hψ₀o, -⟩ := hψ₃ n₀ hn₀J hn₀1
    exact s16c13bc_six_nonswap D hc hcomm hp3 hZM hZc hZn hLp hLc hs ⟨ψ₀, hψ₀L, hψ₀o⟩ hall
  · obtain ⟨t, ht⟩ := not_forall.1 hall
    obtain ⟨htW, htne⟩ := Classical.not_imp.1 ht
    exact s16c13bc_six_swap D hc hcomm hp3 hZM hZc hZn hLp hLc hs hJ₀ hJ₁ hinf hsup hfix₀ hE₀
      hE₁ hψ₃ htW htne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
