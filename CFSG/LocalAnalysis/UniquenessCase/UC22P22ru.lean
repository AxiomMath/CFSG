module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22h
import CFSG.Quasithin.Background.OperatorJordanHolder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

section Basic

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_ru_comm {L : Subgroup H} {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {l : H}
    (hl : l ∈ L) (x : Vmod) : ρ c (ρ l x) = ρ l (ρ c x) := by
  have h1 : l * c = c * l := Subgroup.mem_centralizer_iff.1 hc l hl
  rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]

theorem uc22p22r_ru_commOn_inv (L : Subgroup H) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) := by
  intro a ha u hu
  have h : ρ a u - u ∈ commOn ρ L ⊤ := Submodule.subset_span ⟨a, ha, u, Submodule.mem_top, rfl⟩
  have h' := add_mem h hu
  rwa [sub_add_cancel] at h'

theorem uc22p22r_ru_commOn_cent {L : Subgroup H} {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H))
    {w : Vmod} (hw : w ∈ commOn ρ L ⊤) : ρ c w ∈ commOn ρ L ⊤ := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, u, -, rfl⟩ := hy
    rw [map_sub, uc22p22r_ru_comm ρ hc ha]
    exact Submodule.subset_span ⟨a, ha, ρ c u, Submodule.mem_top, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem uc22p22r_ru_fixOn_sup (U S : Subgroup H) (W : Submodule (ZMod 2) Vmod) :
    fixOn ρ (U ⊔ S) W = fixOn ρ U (fixOn ρ S W) := by
  simp only [fixOn, fixSub_sup]
  rw [inf_comm (fixSub ρ U), ← inf_assoc]

theorem uc22p22r_ru_fixOn_ne_bot [Finite Vmod] {P : Subgroup H} (hP : IsPGroup 2 P)
    {Z : Submodule (ZMod 2) Vmod} (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ P Z) (hZ0 : Z ≠ ⊥) : fixOn ρ P Z ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥Z := Submodule.nontrivial_iff_ne_bot.2 hZ0
  let _ : MulAction ↥P ↥Z :=
    { smul := fun g z => ⟨ρ g z, hZ g g.2 z z.2⟩
      one_smul := fun z => Subtype.ext (by
        show ρ ((1 : ↥P) : H) z = z
        rw [Subgroup.coe_one, map_one, Module.End.one_apply])
      mul_smul := fun g g' z => Subtype.ext (by
        show ρ ((g * g' : ↥P) : H) z = ρ g (ρ g' z)
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) }
  have hdvd : 2 ∣ Nat.card ↥Z := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  have h0 : (0 : ↥Z) ∈ MulAction.fixedPoints ↥P ↥Z := fun g => Subtype.ext (map_zero (ρ g))
  obtain ⟨x, hx, hx0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥Z hdvd h0
  intro hbot
  have hmem : (x : Vmod) ∈ fixOn ρ P Z :=
    mem_fixOn.2 ⟨x.2, fun g hg => congrArg Subtype.val (hx ⟨g, hg⟩)⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx0 (Subtype.ext hmem.symm)

theorem uc22p22r_ru_secSum_one {P : Submodule (ZMod 2) Vmod → Submodule (ZMod 2) Vmod → Prop}
    {W : Submodule (ZMod 2) Vmod} (h : SecSum P 1 W ⊥) : P W ⊥ := by
  obtain ⟨A, hA, hsup, -⟩ := h
  have hA0 : A 0 = W := by
    rw [← hsup]
    exact (iSup_unique (f := A)).symm
  rw [← hA0]
  exact (hA 0).2.2

theorem uc22p22r_ru_secSum_two {P : Submodule (ZMod 2) Vmod → Submodule (ZMod 2) Vmod → Prop}
    {W : Submodule (ZMod 2) Vmod} (h : SecSum P 2 W ⊥) :
    ∃ A₁ A₂ : Submodule (ZMod 2) Vmod, P A₁ ⊥ ∧ P A₂ ⊥ ∧ A₁ ⊔ A₂ = W ∧ A₁ ⊓ A₂ = ⊥ := by
  obtain ⟨A, hA, hsup, hinf⟩ := h
  refine ⟨A 0, A 1, (hA 0).2.2, (hA 1).2.2, ?_, ?_⟩
  · rw [← hsup]
    refine le_antisymm (sup_le (le_iSup A 0) (le_iSup A 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · refine le_bot_iff.1 ((inf_le_inf_left (A 0) ?_).trans (hinf 0))
    exact le_iSup₂_of_le (1 : Fin 2) (show (1 : Fin 2) ∈ {j : Fin 2 | j ≠ 0} from by decide) le_rfl

end Basic

section NatL2

open scoped Matrix

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_ru_natL2_fix {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} {n r : ℕ} (hr : r.Prime)
    (hrn : ¬ r ∣ 2 ^ n - 1) (hnat : NatL2 ρ L W ⊥ n) {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H))
    (hcW : ∀ w ∈ W, ρ c w ∈ W) {k : ℕ} (hck : c ^ (r ^ k) = 1) : ∀ w ∈ W, ρ c w = w := by
  classical
  obtain ⟨F, hF1, hF2, hFcard, hinvW, -, -, φ, ψ, -, hker, hsurj, hψ⟩ := hnat
  have hinj : ∀ x ∈ W, ∀ y ∈ W, ψ x = ψ y → x = y := by
    intro x hx y hy hxy
    have h := hker (x - y) (W.sub_mem hx hy) (by rw [map_sub, hxy, sub_self])
    rwa [Submodule.mem_bot, sub_eq_zero] at h
  let ψW : ↥W →+ (Fin 2 → F) := ψ.comp W.subtype.toAddMonoidHom
  have hbij : Function.Bijective ψW :=
    ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy), fun y => by
      obtain ⟨x, hx, hxy⟩ := hsurj y
      exact ⟨⟨x, hx⟩, hxy⟩⟩
  let ψe : ↥W ≃+ (Fin 2 → F) := AddEquiv.ofBijective ψW hbij
  have hsymm : ∀ x ∈ W, ((ψe.symm (ψ x) : ↥W) : Vmod) = x := fun x hx => by
    rw [show ψe.symm (ψ x) = ⟨x, hx⟩ from ψe.symm_apply_eq.2 rfl]
  let T : (Fin 2 → F) →+ (Fin 2 → F) :=
    ψ.comp ((ρ c).toAddMonoidHom.comp (W.subtype.toAddMonoidHom.comp ψe.symm.toAddMonoidHom))
  have hT : ∀ y, T y = ψ (ρ c (ψe.symm y : Vmod)) := fun y => rfl
  have hTcomm : ∀ g : ↥(StatedSL 2 F), ∀ y,
      T (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T y := by
    intro g y
    obtain ⟨h, rfl⟩ := φ.surjective g
    obtain ⟨x, hx, rfl⟩ := hsurj y
    rw [← hψ h x hx, hT, hT, hsymm _ (hinvW _ h.2 _ hx), hsymm x hx, uc22p22r_ru_comm ρ hc h.2,
      hψ h _ (hcW x hx)]
  obtain ⟨μ, hμ⟩ := CFSG.Quasithin.exists_smul_of_comm_sl (n := 2) le_rfl T hTcomm
  have hψc : ∀ x ∈ W, ψ (ρ c x) = μ • ψ x := by
    intro x hx
    have h := hμ (ψ x)
    rwa [hT, hsymm x hx] at h
  have hψpow : ∀ j : ℕ, ∀ x ∈ W, ψ (ρ (c ^ j) x) = μ ^ j • ψ x ∧ ρ (c ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => intro x hx; simp [hx]
    | succ j ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      rw [pow_succ', map_mul, Module.End.mul_apply]
      refine ⟨?_, hcW _ h2⟩
      rw [hψc _ h2, h1, smul_smul, ← pow_succ']
  have hμ1 : μ ^ (r ^ k) = 1 := by
    obtain ⟨x, hx, hxe⟩ := hsurj ![1, 0]
    have h1 := (hψpow (r ^ k) x hx).1
    rw [hck, map_one, Module.End.one_apply, hxe] at h1
    have h2 := congrFun h1 0
    simp at h2
    exact h2.symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero k hr.ne_zero)] at hμ1
    exact zero_ne_one hμ1
  letI : Fintype F := Fintype.ofFinite F
  have hμ2 : μ ^ (2 ^ n - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hFcard] at h
  have hcop : Nat.Coprime (r ^ k) (2 ^ n - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hrn)
  have hμ3 : μ = 1 := by
    have h := (pow_gcd_eq_one (a := μ)).2 ⟨hμ1, hμ2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  intro w hw
  apply hinj _ (hcW w hw) w hw
  rw [hψc w hw, hμ3, one_smul]

theorem uc22p22r_ru_natL2_card_fix {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} {n : ℕ}
    (hnat : NatL2 ρ L W ⊥ n) {Q : Subgroup ↥L} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    Nat.card ↥(fixOn ρ (Q.map L.subtype) W) = 2 ^ n := by
  classical
  obtain ⟨F, hF1, hF2, hFcard, hinvW, -, -, φ, ψ, -, hker, hsurj, hψ⟩ := hnat
  have hinj : ∀ x ∈ W, ∀ y ∈ W, ψ x = ψ y → x = y := by
    intro x hx y hy hxy
    have h := hker (x - y) (W.sub_mem hx hy) (by rw [map_sub, hxy, sub_self])
    rwa [Submodule.mem_bot, sub_eq_zero] at h
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  let φ' : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F := φ.trans e.symm
  have hφ' : ∀ l : ↥L, ((φ' l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((φ l : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro l
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 F (φ' l)]
    show (((e (e.symm (φ l)) : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [MulEquiv.apply_symm_apply]
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := Q.map φ'.toMonoidHom
  have hP : IsPGroup 2 P := hQ.map _
  have hP1 : P ≠ ⊥ := fun h => hQ1 ((Subgroup.map_eq_bot_iff_of_injective Q φ'.injective).1 h)
  have hF2d : 2 ∣ Nat.card F := by
    have h1 : 1 < 2 ^ n := hFcard ▸ Finite.one_lt_card
    have hn : n ≠ 0 := by
      rintro rfl
      exact lt_irrefl 1 (by simpa using h1)
    rw [hFcard]
    exact dvd_pow_self 2 hn
  obtain ⟨v, hv0, hv⟩ := CFSG.Quasithin.H13.exists_fixed_vector hF2d P hP
  have hfixP : ∀ y : Fin 2 → F,
      (∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ y = y) ↔ ∃ a : F, y = a • v := by
    intro y
    constructor
    · exact fun hy => CFSG.Quasithin.H13.fixed_eq_line P hP1 hv0 hv hy
    · rintro ⟨a, rfl⟩ A hA
      rw [Matrix.mulVec_smul, hv A hA]
  have hmemfix : ∀ x ∈ W, x ∈ fixOn ρ (Q.map L.subtype) W ↔
      ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ψ x = ψ x := by
    intro x hx
    rw [mem_fixOn]
    constructor
    · rintro ⟨-, hfx⟩ A ⟨q, hq, rfl⟩
      show ((φ' q : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ ψ x = ψ x
      rw [hφ', ← hψ q x hx, hfx (q : H) ⟨q, hq, rfl⟩]
    · intro h
      refine ⟨hx, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      apply hinj _ (hinvW _ q.2 _ hx) _ hx
      have h1 := h (φ' q) ⟨q, hq, rfl⟩
      rw [hφ'] at h1
      rw [hψ q x hx]
      exact h1
  have h1 : Nat.card ↥(fixOn ρ (Q.map L.subtype) W) =
      Nat.card {y : Fin 2 → F // ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ y = y} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨ψ x.1, (hmemfix x.1 (mem_fixOn.1 x.2).1).1 x.2⟩) ⟨?_, ?_⟩)
    · intro x x' hxx
      exact Subtype.ext (hinj _ (mem_fixOn.1 x.2).1 _ (mem_fixOn.1 x'.2).1 (congrArg Subtype.val hxx))
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := hsurj y
      exact ⟨⟨x, (hmemfix x hx).2 hy⟩, rfl⟩
  have h2 : Nat.card {y : Fin 2 → F // ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ y = y} =
      Nat.card F := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun a : F => ⟨a • v, (hfixP _).2 ⟨a, rfl⟩⟩) ⟨?_, ?_⟩)
    · intro a b hab
      exact smul_left_injective F hv0 (congrArg Subtype.val hab)
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := (hfixP y).1 hy
      exact ⟨a, rfl⟩
  rw [h1, h2, hFcard]

theorem uc22p22r_ru_card_sylow {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type} [Group X] [Finite X]
    (θ : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (Q : Sylow 2 X) :
    Nat.card (Q : Subgroup X) = Nat.card F := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype F := Fintype.ofFinite F
  let R : Subgroup X := (CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F)).map θ.symm.toMonoidHom
  have hRcard : Nat.card R = Nat.card F := by
    rw [Subgroup.card_map_of_injective θ.symm.injective, CFSG.ASVolI.burnsideK312_card_rootSub]
  obtain ⟨P, hP⟩ :=
    ((CFSG.ASVolI.burnsideK312_isPGroup_rootSub (E := F)).map θ.symm.toMonoidHom).exists_le_sylow
  have hPQ : Nat.card (P : Subgroup X) = Nat.card (Q : Subgroup X) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx⟩ := CFSG.ASVolI.burnsideK312_sylow_conj (E := F) (Q.isPGroup'.map θ.toMonoidHom)
    calc Nat.card (Q : Subgroup X) = Nat.card ((Q : Subgroup X).map θ.toMonoidHom) :=
          (Subgroup.card_map_of_injective θ.injective).symm
      _ ≤ Nat.card ((CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F)).map (MulAut.conj x).toMonoidHom) :=
          Subgroup.card_le_of_le hx
      _ = Nat.card F := by
          rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, CFSG.ASVolI.burnsideK312_card_rootSub]
  · rw [← hPQ, ← hRcard]
    exact Subgroup.card_le_of_le hP

end NatL2

section Core

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_ru_core [Finite Vmod] {L U : Subgroup H} (hUL : U ≤ L) {p : ℕ} (hp : p.Prime)
    {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {j : ℕ} (hcj : c ^ (p ^ j) = 1)
    {W : Submodule (ZMod 2) Vmod} (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W)
    (hcW : ∀ g ∈ Subgroup.centralizer (L : Set H), ∀ w ∈ W, ρ g w ∈ W)
    (hY : ∀ Y : Submodule (ZMod 2) Vmod, Y ≤ W → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y → Y ≠ W →
      ¬ Nat.card ↥(fixOn ρ U W) ≡ Nat.card ↥(fixOn ρ U Y) [MOD p]) :
    ∀ x ∈ W, ρ c x = x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcinv : c⁻¹ ∈ Subgroup.centralizer (L : Set H) := inv_mem hc
  let V₀ := ↥(fixOn ρ U W)
  let mv : (g : H) → g ∈ Subgroup.centralizer (L : Set H) → V₀ → V₀ := fun g hg v =>
    ⟨ρ g v.1, mem_fixOn.2 ⟨hcW g hg v.1 (mem_fixOn.1 v.2).1, fun a ha => by
      rw [← uc22p22r_ru_comm ρ hg (hUL ha) v.1, (mem_fixOn.1 v.2).2 a ha]⟩⟩
  let σ : Equiv.Perm V₀ :=
    { toFun := mv c hc
      invFun := mv c⁻¹ hcinv
      left_inv := fun v => Subtype.ext (by
        show ρ c⁻¹ (ρ c v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun v => Subtype.ext (by
        show ρ c (ρ c⁻¹ v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl) }
  have hform : ∀ (n : ℕ) (v : V₀), ((σ ^ n) v).1 = ρ (c ^ n) v.1 := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  have hσ : σ ^ (p ^ j) = 1 := by
    ext v
    rw [hform, hcj, map_one]
    rfl
  have hPG : IsPGroup p (Subgroup.zpowers σ) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
    rfl
  let Y : Submodule (ZMod 2) Vmod := W ⊓ LinearMap.ker (ρ c - LinearMap.id)
  have hYmem : ∀ x : Vmod, x ∈ Y ↔ x ∈ W ∧ ρ c x = x := fun x => by
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hYinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := by
    intro a ha u hu
    rw [hYmem] at hu ⊢
    exact ⟨hW a ha u hu.1, by rw [uc22p22r_ru_comm ρ hc ha, hu.2]⟩
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) V₀) =
      Nat.card ↥(fixOn ρ U Y) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, mem_fixOn.2 ⟨?_, (mem_fixOn.1 v.1.2).2⟩⟩
        invFun := fun x => ⟨⟨x.1, mem_fixOn.2 ⟨((hYmem x.1).1 (mem_fixOn.1 x.2).1).1,
          (mem_fixOn.1 x.2).2⟩⟩, ?_⟩
        left_inv := fun v => rfl
        right_inv := fun x => rfl }
    · have h1 := MulAction.mem_fixedPoints.1 v.2 ⟨σ, Subgroup.mem_zpowers σ⟩
      have h2 : σ v.1 = v.1 := h1
      exact (hYmem _).2 ⟨(mem_fixOn.1 v.1.2).1, congrArg Subtype.val h2⟩
    · rw [MulAction.mem_fixedPoints]
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      show (σ ^ i) _ = _
      apply Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
      apply Subtype.ext
      exact ((hYmem x.1).1 (mem_fixOn.1 x.2).1).2
  have hcongr := hPG.card_modEq_card_fixedPoints V₀
  rw [hfix] at hcongr
  by_contra hne
  push Not at hne
  obtain ⟨x, hxW, hx⟩ := hne
  have hYW : Y ≠ W := fun h => hx ((hYmem x).1 (h ▸ hxW)).2
  exact hY Y inf_le_left hYinv hYW hcongr

theorem uc22p22r_ru_classify {L U : Subgroup H} (hUL : U ≤ L) {W A₁ A₂ : Submodule (ZMod 2) Vmod}
    (hsup : A₁ ⊔ A₂ = W) (hinf : A₁ ⊓ A₂ = ⊥) (hI₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A₁) (hI₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A₂)
    (hirr₁ : ∀ C : Submodule (ZMod 2) Vmod, C ≤ A₁ → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A₁)
    (hirr₂ : ∀ C : Submodule (ZMod 2) Vmod, C ≤ A₂ → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A₂)
    {q : ℕ} (hq : 0 < q) (hc₁ : Nat.card ↥(fixOn ρ U A₁) = q) (hc₂ : Nat.card ↥(fixOn ρ U A₂) = q) :
    Nat.card ↥(fixOn ρ U W) = q * q ∧
      ∀ Y : Submodule (ZMod 2) Vmod, Y ≤ W → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y → Y ≠ W →
        Y = ⊥ ∨ Nat.card ↥(fixOn ρ U Y) = q := by
  have hA₁W : A₁ ≤ W := by rw [← hsup]; exact le_sup_left
  have hcard : Nat.card ↥(fixOn ρ U W) = q * q := by
    rw [← hsup, uc22p22h_card_fix_sup ρ (uc22p22h_inv_mono ρ hUL hI₁) (uc22p22h_inv_mono ρ hUL hI₂) hinf,
      hc₁, hc₂]
  refine ⟨hcard, fun Y hYW hY hne => ?_⟩
  rcases hirr₁ (Y ⊓ A₁) inf_le_right (uc22p22h_inv_inf ρ hY hI₁) with h1 | h1
  · rcases hirr₂ ((Y ⊔ A₁) ⊓ A₂) inf_le_right
      (uc22p22h_inv_inf ρ (uc22p22h_inv_sup ρ hY hI₁) hI₂) with h2 | h2
    · left
      have hZ : Y ⊔ A₁ = A₁ := by
        have h := sup_inf_assoc_of_le A₂ (le_sup_right : A₁ ≤ Y ⊔ A₁)
        rwa [hsup, inf_eq_right.2 (sup_le hYW hA₁W), inf_comm A₂, h2, sup_bot_eq] at h
      have hYle : Y ≤ A₁ := by rw [← hZ]; exact le_sup_left
      rw [← h1]
      exact (inf_eq_left.2 hYle).symm
    · right
      have hZ : Y ⊔ A₁ = W := by
        refine le_antisymm (sup_le hYW hA₁W) ?_
        rw [← hsup]
        exact sup_le le_sup_right (inf_eq_right.1 h2)
      have h3 := uc22p22h_card_fix_sup ρ (uc22p22h_inv_mono ρ hUL hY) (uc22p22h_inv_mono ρ hUL hI₁) h1
      rw [hZ, hcard, hc₁] at h3
      exact Nat.eq_of_mul_eq_mul_right hq h3.symm
  · right
    have hA₁Y : A₁ ≤ Y := inf_eq_right.1 h1
    rcases hirr₂ (Y ⊓ A₂) inf_le_right (uc22p22h_inv_inf ρ hY hI₂) with h2 | h2
    · have hYeq : Y = A₁ := by
        have h := sup_inf_assoc_of_le A₂ hA₁Y
        rwa [hsup, inf_eq_right.2 hYW, inf_comm A₂ Y, h2, sup_bot_eq] at h
      rw [hYeq, hc₁]
    · refine absurd (le_antisymm hYW ?_) hne
      rw [← hsup]
      exact sup_le hA₁Y (inf_eq_right.1 h2)

end Core

section Main

variable {H : Type} [Group H] [Finite H] {Vmod : Type} [AddCommGroup Vmod]
  [Module (ZMod 2) Vmod] [Finite Vmod] (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_F1W_natL2 {L : Subgroup H} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hnat : NatL2 ρ L (commOn ρ L ⊤) ⊥ n)
    {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {k : ℕ} (hck : c ^ (p ^ k) = 1) :
    ∀ w ∈ commOn ρ L ⊤, ρ c w = w :=
  uc22p22r_ru_natL2_fix ρ hp (uc22p22g_not_dvd_pred hp hp2 hpn) hnat hc
    (fun _ hw => uc22p22r_ru_commOn_cent ρ hc hw) hck

theorem uc22p22r_F2W_natL2 {L : Subgroup H} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hL : IsL2 ↥L n) (hnat : NatL2 ρ L (commOn ρ L ⊤) ⊥ n)
    {U S₂ : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L)
    (hS₂ : S₂ ≤ Subgroup.centralizer (L : Set H)) (hS₂2 : IsPGroup 2 S₂) :
    ¬ Nat.card ↥(fixOn ρ (U ⊔ S₂) (commOn ρ L ⊤)) ≡ 1 [MOD p] := by
  obtain ⟨hn2, F', _, _, hF'card, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hL
  obtain ⟨Q, rfl⟩ := hU
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    intro h3
    omega
  have hS₂W : fixOn ρ S₂ (commOn ρ L ⊤) = commOn ρ L ⊤ := by
    refine le_antisymm (fun x hx => (mem_fixOn.1 hx).1) fun w hw => mem_fixOn.2 ⟨hw, fun s hs => ?_⟩
    obtain ⟨m, hm⟩ := hS₂2 ⟨s, hs⟩
    exact uc22p22r_ru_natL2_fix ρ Nat.prime_two hodd hnat (hS₂ hs)
      (fun _ hx => uc22p22r_ru_commOn_cent ρ (hS₂ hs) hx) (congrArg Subtype.val hm) w hw
  have hQ1 : (Q : Subgroup ↥L) ≠ ⊥ := by
    have hcard := uc22p22r_ru_card_sylow (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo) Q
    intro h
    rw [h, Subgroup.card_bot, hF'card] at hcard
    exact (Nat.one_lt_two_pow (by omega)).ne hcard
  rw [uc22p22r_ru_fixOn_sup, hS₂W, uc22p22r_ru_natL2_card_fix ρ hnat Q.isPGroup' hQ1]
  intro h
  exact uc22p22g_not_dvd_pred hp hp2 hpn ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h.symm)

theorem uc22p22r_F1W_omegaMinus {L : Subgroup H} {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : (2 : ℤ) ^ (2 * k) ≡ -1 [ZMOD (p : ℤ)])
    (hmods : SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
      SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)
    {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {j : ℕ} (hcj : c ^ (p ^ j) = 1) :
    ∀ w ∈ commOn ρ L ⊤, ρ c w = w := by
  obtain ⟨hk, hq1, hq2, hq3⟩ := uc22p22h_numerics hp hp2 hpk
  have hW := uc22p22r_ru_commOn_inv ρ L
  have hcW : ∀ g ∈ Subgroup.centralizer (L : Set H), ∀ w ∈ commOn ρ L ⊤, ρ g w ∈ commOn ρ L ⊤ :=
    fun _ hg _ hw => uc22p22r_ru_commOn_cent ρ hg hw
  rcases hmods with h1 | h2
  · obtain ⟨F, _, _, _, hF, β, θ, hinv, hmem, hinj, hsurj, hact⟩ :=
      uc22p22h_pres ρ L hk (uc22p22r_ru_secSum_one h1)
    have hirr := uc22p22h_irr ρ L hk hF β θ hmem hinj hact
    obtain ⟨U₀, hU₀card, hU₀p⟩ := uc22p22h_exists_U hF θ
    have hc₁ := uc22p22h_card_fix ρ L hk hF β θ hmem hinj hsurj hact hinv U₀ hU₀card hU₀p
    refine uc22p22r_ru_core ρ (map_subtype_le U₀) hp hc hcj hW hcW fun Y hYW hY hne => ?_
    rcases hirr Y hYW hY with h0 | h0
    · rw [h0, uc22p22h_card_fix_bot, hc₁]
      exact hq1
    · exact absurd h0 hne
  · obtain ⟨A₁, A₂, hA₁, hA₂, hsup, hinf⟩ := uc22p22r_ru_secSum_two h2
    obtain ⟨F₁, _, _, _, hF₁, β₁, θ₁, hinv₁, hmem₁, hinj₁, hsurj₁, hact₁⟩ := uc22p22h_pres ρ L hk hA₁
    obtain ⟨F₂, _, _, _, hF₂, β₂, θ₂, hinv₂, hmem₂, hinj₂, hsurj₂, hact₂⟩ := uc22p22h_pres ρ L hk hA₂
    have hirr₁ := uc22p22h_irr ρ L hk hF₁ β₁ θ₁ hmem₁ hinj₁ hact₁
    have hirr₂ := uc22p22h_irr ρ L hk hF₂ β₂ θ₂ hmem₂ hinj₂ hact₂
    obtain ⟨U₀, hU₀card, hU₀p⟩ := uc22p22h_exists_U hF₁ θ₁
    have hc₁ := uc22p22h_card_fix ρ L hk hF₁ β₁ θ₁ hmem₁ hinj₁ hsurj₁ hact₁ hinv₁ U₀ hU₀card hU₀p
    have hc₂ := uc22p22h_card_fix ρ L hk hF₂ β₂ θ₂ hmem₂ hinj₂ hsurj₂ hact₂ hinv₂ U₀ hU₀card hU₀p
    obtain ⟨hctop, hcls⟩ := uc22p22r_ru_classify ρ (map_subtype_le U₀) hsup hinf hinv₁ hinv₂ hirr₁ hirr₂
      (Nat.pos_of_ne_zero (pow_ne_zero k two_ne_zero)) hc₁ hc₂
    refine uc22p22r_ru_core ρ (map_subtype_le U₀) hp hc hcj hW hcW fun Y hYW hY hne => ?_
    rw [hctop]
    rcases hcls Y hYW hY hne with h0 | h0
    · rw [h0, uc22p22h_card_fix_bot]
      exact hq2
    · rw [h0]
      exact hq3

theorem uc22p22r_F2W_omegaMinus {L : Subgroup H} {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : (2 : ℤ) ^ (2 * k) ≡ -1 [ZMOD (p : ℤ)]) (hL : IsL2 ↥L (2 * k))
    (hmods : SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
      SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)
    {U S₂ : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L)
    (hS₂ : S₂ ≤ Subgroup.centralizer (L : Set H)) (hS₂2 : IsPGroup 2 S₂) :
    ¬ Nat.card ↥(fixOn ρ (U ⊔ S₂) (commOn ρ L ⊤)) ≡ 1 [MOD p] := by
  obtain ⟨hk, hq1, hq2, -⟩ := uc22p22h_numerics hp hp2 hpk
  obtain ⟨-, F', _, _, hF'card, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hL
  obtain ⟨Q, rfl⟩ := hU
  have hQ : Nat.card (Q : Subgroup ↥L) = 2 ^ (2 * k) := by
    rw [uc22p22r_ru_card_sylow (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo) Q, hF'card]
  have hW := uc22p22r_ru_commOn_inv ρ L
  have hA : ∀ A : Submodule (ZMod 2) Vmod, NatOmegaMinus4 ρ L A ⊥ k →
      Nat.card ↥(fixOn ρ ((Q : Subgroup ↥L).map L.subtype) A) = 2 ^ k ∧
        (∀ C : Submodule (ZMod 2) Vmod, C ≤ A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A) ∧
        CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A := by
    intro A hA
    obtain ⟨F, _, _, _, hF, β, θ, hinv, hmem, hinj, hsurj, hact⟩ := uc22p22h_pres ρ L hk hA
    exact ⟨uc22p22h_card_fix ρ L hk hF β θ hmem hinj hsurj hact hinv _ hQ Q.isPGroup',
      uc22p22h_irr ρ L hk hF β θ hmem hinj hact, hinv⟩
  have hYW : fixOn ρ S₂ (commOn ρ L ⊤) ≤ commOn ρ L ⊤ := fun x hx => (mem_fixOn.1 hx).1
  have hYinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (fixOn ρ S₂ (commOn ρ L ⊤)) := by
    intro a ha u hu
    refine mem_fixOn.2 ⟨hW a ha u (mem_fixOn.1 hu).1, fun s hs => ?_⟩
    rw [uc22p22r_ru_comm ρ (hS₂ hs) ha, (mem_fixOn.1 hu).2 s hs]
  have hY0 : ∀ A : Submodule (ZMod 2) Vmod, A ≤ commOn ρ L ⊤ →
      Nat.card ↥(fixOn ρ ((Q : Subgroup ↥L).map L.subtype) A) = 2 ^ k →
        fixOn ρ S₂ (commOn ρ L ⊤) ≠ ⊥ := by
    intro A hAW hAc
    refine uc22p22r_ru_fixOn_ne_bot ρ hS₂2 (fun s hs _ hw => uc22p22r_ru_commOn_cent ρ (hS₂ hs) hw) ?_
    intro hW0
    rw [hW0, le_bot_iff] at hAW
    rw [hAW, uc22p22h_card_fix_bot] at hAc
    exact (Nat.one_lt_two_pow (by omega)).ne hAc
  rw [uc22p22r_ru_fixOn_sup]
  rcases hmods with h1 | h2
  · obtain ⟨hc, hirr, -⟩ := hA _ (uc22p22r_ru_secSum_one h1)
    rcases hirr _ hYW hYinv with h0 | h0
    · exact absurd h0 (hY0 _ le_rfl hc)
    · rw [h0, hc]
      exact hq1
  · obtain ⟨A₁, A₂, hA₁, hA₂, hsup, hinf⟩ := uc22p22r_ru_secSum_two h2
    obtain ⟨hc₁, hirr₁, hinv₁⟩ := hA A₁ hA₁
    obtain ⟨hc₂, hirr₂, hinv₂⟩ := hA A₂ hA₂
    have hA₁W : A₁ ≤ commOn ρ L ⊤ := by rw [← hsup]; exact le_sup_left
    obtain ⟨hctop, hcls⟩ := uc22p22r_ru_classify ρ (map_subtype_le _) hsup hinf hinv₁ hinv₂ hirr₁ hirr₂
      (Nat.pos_of_ne_zero (pow_ne_zero k two_ne_zero)) hc₁ hc₂
    by_cases hYe : fixOn ρ S₂ (commOn ρ L ⊤) = commOn ρ L ⊤
    · rw [hYe, hctop]
      exact hq2
    · rcases hcls _ hYW hYinv hYe with h0 | h0
      · exact absurd h0 (hY0 A₁ hA₁W hc₁)
      · rw [h0]
        exact hq1

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
