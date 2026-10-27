module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147LocalLift
import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]


theorem invariants_conj_mul {F H V : Type*} [Field F] [Group H]
    [AddCommGroup V] [Module F V] (ρ : Representation F H V)
    (B : Subgroup H) (g h : H) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp (B.map (MulAut.conj h)).subtype)) :
    ρ g v ∈ Representation.invariants (ρ.comp (B.map (MulAut.conj (g * h))).subtype) := by
  rw [Representation.mem_invariants] at hv ⊢
  intro b
  obtain ⟨a, ha, hba⟩ := Subgroup.mem_map.mp b.property
  change ρ (b : H) (ρ g v) = ρ g v
  rw [← hba]
  have hb' : (g * h) * a * (g * h)⁻¹ * g = g * (h * a * h⁻¹) := by
    group
  calc ρ ((g * h) * a * (g * h)⁻¹) (ρ g v)
      = ρ (((g * h) * a * (g * h)⁻¹) * g) v := by
        rw [← Module.End.mul_apply, ← map_mul]
    _ = ρ (g * (h * a * h⁻¹)) v := by rw [hb']
    _ = ρ g (ρ (h * a * h⁻¹) v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g v := by
      have hv' : ρ (h * a * h⁻¹) v = v := by
        simpa [MonoidHom.comp_apply, MulAut.conj_apply] using
          hv ⟨(MulAut.conj h) a, Subgroup.mem_map_of_mem _ ha⟩
      rw [hv']

theorem exists_conj_eq_of_mem_sup {H : Type*} [Group H] {B K : Subgroup H}
    (hBK : B ≤ normalizer (K : Set H)) {h : H} (hh : h ∈ B ⊔ K) :
    ∃ k ∈ K, B.map (MulAut.conj h : H →* H) = B.map (MulAut.conj k : H →* H) := by
  have hh' : h ∈ (↑(B ⊔ K) : Set H) := hh
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B K hBK] at hh' 
  obtain ⟨b, hb, k, hk, rfl⟩ := Set.mem_mul.mp hh' 
  refine ⟨b * k * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hBK hb) k).mp hk, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨b * x * b⁻¹, B.mul_mem (B.mul_mem hb hx) (B.inv_mem hb), ?_⟩
    change (b * k * b⁻¹) * (b * x * b⁻¹) * (b * k * b⁻¹)⁻¹ =
      (b * k) * x * (b * k)⁻¹
    group
  · rintro ⟨y, hy, rfl⟩
    refine ⟨b⁻¹ * y * b, B.mul_mem (B.mul_mem (B.inv_mem hb) hy) hb, ?_⟩
    change (b * k) * (b⁻¹ * y * b) * (b * k)⁻¹ =
      (b * k * b⁻¹) * y * (b * k * b⁻¹)⁻¹
    group


theorem sup_invariants_conj_eq_top {F H V : Type*} [Field F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (ρ : Representation F H V)
    {K B : Subgroup H} (hKn : K.Normal) (hK : IsMulCommutative ↥K)
    (hBK : B ≤ normalizer (K : Set H))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hH : NeZero (Nat.card H : F)) :
    Representation.invariants (ρ.comp K.subtype) ⊔
      ⨆ h : H, Representation.invariants (ρ.comp (B.map (MulAut.conj h)).subtype) = ⊤ := by
  let C : H → Submodule F V := fun h =>
    Representation.invariants (ρ.comp (B.map (MulAut.conj h)).subtype)
  let U'Sub : Submodule F V :=
    Representation.invariants (ρ.comp K.subtype) ⊔ ⨆ h : H, C h
  have hKmap : ∀ g : H, Representation.invariants (ρ.comp K.subtype) ≤
      Submodule.comap (ρ g) (Representation.invariants (ρ.comp K.subtype)) := by
    intro g w hw
    rw [Submodule.mem_comap] at ⊢
    rw [Representation.mem_invariants] at hw ⊢
    intro k
    change ρ (k : H) (ρ g w) = ρ g w
    have hk : g⁻¹ * (k : H) * g ∈ K := by
      simpa using hKn.conj_mem (k : H) k.2 g⁻¹
    calc ρ (k : H) (ρ g w) = ρ ((k : H) * g) w := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * (g⁻¹ * (k : H) * g)) w := by
          rw [show (k : H) * g = g * (g⁻¹ * (k : H) * g) by group]
      _ = ρ g (ρ (g⁻¹ * (k : H) * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ g w := by
          have hw' : ρ (g⁻¹ * (k : H) * g) w = w := hw ⟨_, hk⟩
          rw [hw']
  have hCmap : ∀ g : H, (⨆ h : H, C h) ≤ Submodule.comap (ρ g) (⨆ h : H, C h) := by
    intro g
    refine iSup_le fun h => ?_
    intro w hw
    exact Submodule.mem_iSup_of_mem (g * h) (invariants_conj_mul ρ B g h hw)
  have hmap : ∀ g : H, U'Sub ≤ Submodule.comap (ρ g) U'Sub := by
    intro g
    exact sup_le (hKmap g |>.trans (Submodule.comap_mono (f := ρ g) le_sup_left))
      (hCmap g |>.trans (Submodule.comap_mono (f := ρ g) le_sup_right))
  let U' : Subrepresentation ρ :=
    { toSubmodule := U'Sub
      apply_mem_toSubmodule := fun g w hw => hmap g hw }
  have hbotSub : (⊥ : Subrepresentation ρ).toSubmodule = (⊥ : Submodule F V) := rfl
  have htopSub : (⊤ : Subrepresentation ρ).toSubmodule = (⊤ : Submodule F V) := rfl
  have hBU : Representation.invariants (ρ.comp B.subtype) ≤ U'Sub := by
    have hB1 : B.map (MulAut.conj (1 : H) : H →* H) = B := by
      ext x
      simp [Subgroup.mem_map]
    have h1 : C 1 = Representation.invariants (ρ.comp B.subtype) := by
      dsimp only [C]
      rw [hB1]
    rw [← h1]
    exact le_sup_of_le_right (le_iSup_of_le (1 : H) le_rfl)
  obtain ⟨U'', hcompl⟩ := exists_isCompl U'
  have hfixK : Representation.invariants (U''.toRepresentation.comp K.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwD : (w : V) ∈ Representation.invariants (ρ.comp K.subtype) := by
      show ∀ k : K, ρ (k : H) (w : V) = (w : V)
      intro k
      have h2 := (Representation.mem_invariants
        (ρ := U''.toRepresentation.comp K.subtype) w).mp hw k
      exact congrArg Subtype.val h2
    have hwU : (w : V) ∈ U'Sub := (le_sup_left : _ ≤ U'Sub) hwD
    have hdisj : U'.toSubmodule ⊓ U''.toSubmodule = ⊥ := by
      have h := congrArg Subrepresentation.toSubmodule hcompl.disjoint.eq_bot
      simpa [hbotSub] using h
    have hmem : (w : V) ∈ U'.toSubmodule ⊓ U''.toSubmodule :=
      ⟨by simpa [U', U'Sub] using hwU, w.property⟩
    rw [hdisj] at hmem
    exact Subtype.ext hmem
  have hfixB : Representation.invariants (U''.toRepresentation.comp B.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwD : (w : V) ∈ Representation.invariants (ρ.comp B.subtype) := by
      show ∀ b : B, ρ (b : H) (w : V) = (w : V)
      intro b
      have h2 := (Representation.mem_invariants
        (ρ := U''.toRepresentation.comp B.subtype) w).mp hw b
      exact congrArg Subtype.val h2
    have hwU : (w : V) ∈ U'Sub := hBU hwD
    have hdisj : U'.toSubmodule ⊓ U''.toSubmodule = ⊥ := by
      have h := congrArg Subrepresentation.toSubmodule hcompl.disjoint.eq_bot
      simpa [hbotSub] using h
    have hmem : (w : V) ∈ U'.toSubmodule ⊓ U''.toSubmodule :=
      ⟨by simpa [U', U'Sub] using hwU, w.property⟩
    rw [hdisj] at hmem
    exact Subtype.ext hmem
  have hcharK : ¬ ringChar F ∣ Nat.card K := by
    intro hdvd
    exact hH.out ((ringChar.spec F (Nat.card H)).mpr
      (hdvd.trans (Subgroup.card_subgroup_dvd_card K)))
  have hcount := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree
    (ρ := U''.toRepresentation) hK hBK hfpf hcharK hfixK
  rw [hfixB, finrank_bot, zero_mul] at hcount
  have hbot : U''.toSubmodule = ⊥ := Submodule.finrank_eq_zero.mp hcount.symm
  have hU'' : U'' = ⊥ := Subrepresentation.toSubmodule_injective (by
    simpa [hbotSub] using hbot)
  have hcompl' : IsCompl U' ⊥ := by rwa [hU''] at hcompl
  have hU' : U' = ⊤ := eq_top_of_isCompl_bot hcompl'
  simpa [U'Sub, C, htopSub] using congrArg Subrepresentation.toSubmodule hU'

structure GroupCopy (W : Type*) where
  toW : W

namespace GroupCopy

variable {W : Type*}

@[ext]
theorem ext {x y : GroupCopy W} (h : x.toW = y.toW) : x = y := by
  cases x; cases y; simpa using h

theorem toW_injective : Function.Injective (toW : GroupCopy W → W) := fun _ _ h => ext h

instance [Finite W] : Finite (GroupCopy W) :=
  Finite.of_injective toW toW_injective

variable [Group W]

@[instance_reducible] def commGroupOfComm (hcomm : ∀ x y : W, x * y = y * x) :
    CommGroup (GroupCopy W) where
  mul x y := ⟨x.toW * y.toW⟩
  one := ⟨1⟩
  inv x := ⟨x.toW⁻¹⟩
  npow := fun n x => ⟨x.toW ^ n⟩
  mul_assoc x y z := ext (mul_assoc x.toW y.toW z.toW)
  one_mul x := ext (one_mul x.toW)
  mul_one x := ext (mul_one x.toW)
  inv_mul_cancel x := ext (inv_mul_cancel x.toW)
  mul_comm x y := ext (hcomm x.toW y.toW)
  npow_zero x := ext (Monoid.npow_zero x.toW)
  npow_succ n x := ext (Monoid.npow_succ n x.toW)

end GroupCopy

theorem closure_fixed_conj_eq_top {H W : Type*} [Group H] [Group W] [Finite H] [Finite W]
    [MulDistribMulAction H W] {q : ℕ} (hq : q.Prime)
    (hc : ∀ a b : W, a * b = b * a) (hp : ∀ w : W, w ^ q = 1)
    (hqH : ¬ q ∣ Nat.card H)
    {K B : Subgroup H} (hKn : K.Normal) (hK : IsMulCommutative ↥K)
    (hBK : B ≤ normalizer (K : Set H))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hsup : B ⊔ K = ⊤) :
    Subgroup.closure ({w : W | ∀ k ∈ K, k • w = w} ∪
      ⋃ x ∈ K, {w : W | ∀ b ∈ B, (x * b * x⁻¹) • w = w}) = ⊤ := by
  classical
  have hFactQ : Fact q.Prime := ⟨hq⟩
  have hqne : NeZero q := ⟨hq.ne_zero⟩
  let Q := GroupCopy W
  let hcommQ : CommGroup Q := GroupCopy.commGroupOfComm hc
  have hpowQ : ∀ x : Q, x ^ q = 1 := by
    intro x
    apply GroupCopy.ext
    show x.toW ^ q = 1
    exact hp x.toW
  have hmod : Module (ZMod q) (Additive Q) :=
    AddCommGroup.zmodModule (n := q) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact hpowQ x.toMul)
  let hactQ : MulDistribMulAction H Q :=
    { smul := fun h x => ⟨h • x.toW⟩
      one_smul := by
        intro x
        apply GroupCopy.ext
        show (1 : H) • x.toW = x.toW
        rw [one_smul]
      mul_smul := by
        intro h₁ h₂ x
        apply GroupCopy.ext
        show (h₁ * h₂) • x.toW = h₁ • (h₂ • x.toW)
        rw [mul_smul]
      smul_mul := by
        intro h x y
        apply GroupCopy.ext
        show h • (x.toW * y.toW) = h • x.toW * h • y.toW
        rw [MulDistribMulAction.smul_mul]
      smul_one := by
        intro h
        apply GroupCopy.ext
        show h • (1 : W) = 1
        rw [MulDistribMulAction.smul_one] }
  let hact : DistribMulAction H (Additive Q) :=
    { smul := fun h x => Additive.ofMul (h • x.toMul)
      one_smul := by
        intro x
        show Additive.ofMul ((1 : H) • x.toMul) = x
        rw [one_smul, ofMul_toMul]
      mul_smul := by
        intro h₁ h₂ x
        show Additive.ofMul ((h₁ * h₂) • x.toMul) = Additive.ofMul (h₁ • (h₂ • x.toMul))
        rw [mul_smul]
      smul_zero := by
        intro h
        show Additive.ofMul (h • (1 : Q)) = 0
        rw [MulDistribMulAction.smul_one, ofMul_one]
      smul_add := by
        intro h x y
        show Additive.ofMul (h • (x + y).toMul) =
          Additive.ofMul (h • x.toMul) + Additive.ofMul (h • y.toMul)
        rw [show (x + y).toMul = x.toMul * y.toMul from rfl,
          MulDistribMulAction.smul_mul]
        rfl }
  have hsmulc : SMulCommClass H (ZMod q) (Additive Q) :=
    ⟨fun h c x => ZMod.map_smul (f := DistribMulAction.toAddMonoidEnd H (Additive Q) h) c x⟩
  have hMul : MulAction H (Additive Q) := hact.toMulAction
  let ρ : Representation (ZMod q) H (Additive Q) :=
    Representation.ofDistribMulAction (ZMod q) H (Additive Q)
  have hHne : NeZero (Nat.card H : ZMod q) := ⟨by
    intro hzero
    exact hqH ((ZMod.natCast_eq_zero_iff (Nat.card H) q).mp hzero)⟩
  have hspan := sup_invariants_conj_eq_top (ρ := ρ) hKn hK hBK hfpf hHne
  let genQ : Set Q := {x : Q | ∀ k ∈ K, k • x = x} ∪
    ⋃ x ∈ K, {y : Q | ∀ b ∈ B, (x * b * x⁻¹) • y = y}
  let T : Subgroup Q := Subgroup.closure genQ
  have hT : T = ⊤ := by
    let MT : Submodule (ZMod q) (Additive Q) :=
      AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup T)
    have hKle : Representation.invariants (ρ.comp K.subtype) ≤ MT := by
      intro x hx
      rw [Representation.mem_invariants] at hx
      change Additive.toMul x ∈ T
      refine Subgroup.subset_closure (Or.inl ?_)
      intro k hk
      have hfix : ρ (k : H) x = x := hx ⟨k, hk⟩
      have hfix' := congrArg Additive.toMul hfix
      have hsm : Additive.toMul (ρ (k : H) x) = (k : H) • Additive.toMul x := rfl
      rwa [hsm] at hfix'
    have hCle : (⨆ h : H, Representation.invariants
        (ρ.comp (B.map (MulAut.conj h)).subtype)) ≤ MT := by
      refine iSup_le fun h => ?_
      intro x hx
      rw [Representation.mem_invariants] at hx
      have hh : h ∈ B ⊔ K := by rw [hsup]; exact Subgroup.mem_top h
      obtain ⟨k, hk, hkconj⟩ := exists_conj_eq_of_mem_sup hBK hh
      rw [hkconj] at hx
      change Additive.toMul x ∈ T
      refine Subgroup.subset_closure (Or.inr ?_)
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, ?_⟩⟩
      intro b hb
      have hb' : (k * b * k⁻¹) ∈ B.map (MulAut.conj k : H →* H) := by
        rw [← MulAut.conj_apply]
        exact Subgroup.mem_map_of_mem _ hb
      have hfix : ρ (k * b * k⁻¹) x = x := hx ⟨k * b * k⁻¹, hb'⟩
      have hfix' := congrArg Additive.toMul hfix
      have hsm : Additive.toMul (ρ (k * b * k⁻¹) x) = (k * b * k⁻¹) • Additive.toMul x := rfl
      rwa [hsm] at hfix'
    have hMT : MT = ⊤ := by
      rw [eq_top_iff]
      rw [← hspan]
      exact sup_le hKle hCle
    rw [eq_top_iff]
    intro x _
    have hx : Additive.ofMul x ∈ MT := by rw [hMT]; exact Submodule.mem_top
    simpa [MT] using hx
  let e : Q ≃* W :=
    { toFun := GroupCopy.toW
      invFun := fun w => ⟨w⟩
      left_inv := fun x => GroupCopy.ext rfl
      right_inv := fun w => rfl
      map_mul' := fun x y => rfl }
  have hsymm : ∀ (h : H) (w : W), e.symm (h • w) = h • e.symm w := by
    intro h w
    apply e.injective
    rw [e.apply_symm_apply]
    change h • w = h • (e.symm w).toW
    rfl
  have hgen : ({w : W | ∀ k ∈ K, k • w = w} ∪
      ⋃ x ∈ K, {w : W | ∀ b ∈ B, (x * b * x⁻¹) • w = w}) =
      e.toMonoidHom '' genQ := by
    ext w
    constructor
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rcases hw with hwK | hwB
      · left
        intro k hk
        have h := congrArg e.symm (hwK k hk)
        rwa [hsymm k w] at h
      · simp only [Set.mem_iUnion] at hwB
        obtain ⟨x, hx, hwx⟩ := hwB
        right
        refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
        intro b hb
        have h := congrArg e.symm (hwx b hb)
        rwa [hsymm (x * b * x⁻¹) w] at h
    · rintro ⟨x, hx, rfl⟩
      rcases hx with hxK | hxB
      · left
        intro k hk
        have h := congrArg e (hxK k hk)
        have hsm : e (k • x) = k • e x := rfl
        rwa [hsm] at h
      · simp only [Set.mem_iUnion] at hxB
        obtain ⟨y, hy, hxy⟩ := hxB
        right
        refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ?_⟩⟩
        intro b hb
        have h := congrArg e (hxy b hb)
        have hsm : e ((y * b * y⁻¹) • x) = (y * b * y⁻¹) • e x := rfl
        rwa [hsm] at h
  have hmap : T.map e.toMonoidHom = Subgroup.closure (e.toMonoidHom '' genQ) :=
    MonoidHom.map_closure e.toMonoidHom genQ
  rw [← hgen] at hmap
  rw [← hmap, hT]
  exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective


theorem zpowers_eq_of_card_three {H : Type*} [Group H] [Finite H] {B : Subgroup H}
    (hB : Nat.card ↥B = 3) {b : H} (hb : b ∈ B) (hb1 : b ≠ 1) :
    Subgroup.zpowers b = B := by
  have hdvd : orderOf b ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B)
    rwa [hB, Subgroup.orderOf_mk] at h
  have hord : orderOf b = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf b) hdvd with h1 | h3
    · exact absurd h1 (orderOf_eq_one_iff.not.mpr hb1)
    · exact h3
  have hcard : Nat.card (↥(Subgroup.zpowers b)) = 3 := by
    rw [Nat.card_zpowers, hord]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) (by rw [hcard, hB])


namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem le_M_of_section_elemAbelian (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀) {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hq7 : q ≠ 7) (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀)
    (hexp : ∀ v ∈ V, v ^ q ∈ V₀) : V ≤ D.M := by
  have hFactQ : Fact q.Prime := ⟨hq⟩
  let R₁ : Subgroup G := R ⊓ L 0
  have hR1card : Nat.card ↥R₁ = 7 := (c.frame.2.2.1 0).1
  have hBR1 : B ≤ normalizer (R₁ : Set G) := (c.frame.2.2.1 0).2
  let H : Subgroup G := B ⊔ R₁
  have hBcomm : IsMulCommutative ↥B := by
    have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (isCyclic_of_prime_card (p := 3) c.card_B).isMulCommutative
  have hdisjBR₁ : B ⊓ R₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ R := hx.2.1
    have hxCB : x ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (congrArg Subtype.val (hBcomm.is_comm.comm ⟨x, hx.1⟩ ⟨b, hb⟩)).symm
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← c.frame.2.2.2.2.1]
      exact ⟨hxR, hxCB⟩
    simpa using hxbot
  have hHcard : Nat.card ↥H = 21 := by
    have h :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.card_sup_mul_card_inf_of_le_normalizer
        (A := B) (N := R₁) hBR1
    rw [hdisjBR₁, c.card_B, hR1card] at h
    simpa [H] using h
  have hqH : ¬ q ∣ Nat.card ↥H := by
    rw [hHcard]
    intro hdvd
    have hdm : q ∣ 3 * 7 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdm with h3 | h7
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3)
    · exact hq7 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp h7)
  have hHV : H ≤ normalizer (V : Set G) := by
    refine sup_le s.hBV ?_
    exact inf_le_left.trans s.hRV
  have hHV₀ : H ≤ normalizer (V₀ : Set G) := by
    refine sup_le s.hBV₀ ?_
    exact inf_le_left.trans s.hRV₀
  have hV0normal : (V₀.subgroupOf V).Normal :=
    normal_subgroupOf_of_le_normalizer (H := V) (N := V₀) s.hVV₀
  let W := ↥V ⧸ (V₀.subgroupOf V)
  have hc : ∀ a b : W, a * b = b * a := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H v =>
      induction y using QuotientGroup.induction_on with
      | H w =>
        show (QuotientGroup.mk' (G := ↥V) (V₀.subgroupOf V) ((v * w : ↥V)) : W) =
          QuotientGroup.mk' (G := ↥V) (V₀.subgroupOf V) ((w * v : ↥V))
        exact QuotientGroup.eq_iff_div_mem.mpr (by
          simpa [div_eq_mul_inv, mul_assoc, Subgroup.mem_subgroupOf] using
            hab (Subtype.val v) v.2 (Subtype.val w) w.2)
  have hp : ∀ a : W, a ^ q = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      show (((v : ↥V) : W)) ^ q = 1
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff (v ^ q)).mpr (hexp (Subtype.val v) v.2)
  have hNorm : Subgroup.Normalizes H V := ⟨hHV⟩
  have hInv : IsInvariant ↥H ↥V (V₀.subgroupOf V) := ⟨by
    intro a x
    change x.1 ∈ V₀ ↔ a.1 * x.1 * a.1⁻¹ ∈ V₀
    exact Subgroup.mem_normalizer_iff.mp (hHV₀ a.property) x.1⟩
  let hact : MulDistribMulAction ↥H W := inferInstance
  let K : Subgroup ↥H := R₁.subgroupOf H
  let B' : Subgroup ↥H := B.subgroupOf H
  have hRcomm : IsMulCommutative ↥R := c.frame.1.1
  have hKcomm : IsMulCommutative ↥K := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    change Subtype.val x.1 * Subtype.val y.1 =
      Subtype.val y.1 * Subtype.val x.1
    exact congrArg Subtype.val (hRcomm.is_comm.comm
      ⟨x.1.1, x.2.1⟩ ⟨y.1.1, y.2.1⟩)
  have hBnorm : B' ≤ normalizer (K : Set ↥H) := by
    have h1 : B' ≤ (normalizer (R₁ : Set G)).subgroupOf H := by
      intro b hb
      exact Subgroup.mem_subgroupOf.mpr (hBR1 hb)
    rwa [Subgroup.subgroupOf_normalizer_eq (H := R₁) (N := H) le_sup_right] at h1
  have hKn : K.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (H := R₁) (K := H) le_sup_right]
    exact sup_le hBR1 Subgroup.le_normalizer
  have hsup : B' ⊔ K = ⊤ := by
    change B.subgroupOf H ⊔ R₁.subgroupOf H = ⊤
    rw [← Subgroup.subgroupOf_sup (A := B) (A' := R₁) (B := H) le_sup_left le_sup_right]
    simp [H]
  have hfpf : ∀ b ∈ B', b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1 := by
    intro b hb hb1 k hk hbk
    have hbB : Subtype.val b ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hb1' : Subtype.val b ≠ 1 := by
      intro h
      exact hb1 (Subtype.ext h)
    have hgen : Subgroup.zpowers (Subtype.val b) = B :=
      zpowers_eq_of_card_three c.card_B hbB hb1'
    have hkR : Subtype.val k ∈ R := (Subgroup.mem_subgroupOf.mp hk).1
    have hcomm : Subtype.val k ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b0 hb0
      have hb0' : b0 ∈ Subgroup.zpowers (Subtype.val b) := by rwa [hgen]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb0'
      have hbkg : Subtype.val b * Subtype.val k =
          Subtype.val k * Subtype.val b := by
        simpa using congrArg Subtype.val hbk
      rw [← hn]
      exact ((show Commute (Subtype.val b)
        (Subtype.val k) from hbkg).zpow_left n).eq
    have hkbot : Subtype.val k ∈ (⊥ : Subgroup G) := by
      rw [← c.frame.2.2.2.2.1]
      exact ⟨hkR, hcomm⟩
    apply Subtype.ext
    simpa using hkbot
  have hcl := closure_fixed_conj_eq_top (H := ↥H) (W := W) hq hc hp hqH
    hKn hKcomm hBnorm hfpf hsup
  let smulW : ↥H → W → W := fun a w => hact.toMulAction.toSMul.smul a w
  have hsmul_mk : ∀ (a : ↥H) (v : ↥V),
      smulW a (QuotientGroup.mk' (V₀.subgroupOf V) v) =
        QuotientGroup.mk' (V₀.subgroupOf V) (a • v) := by
    intro a v
    rfl
  have hsmul_coe : ∀ (a : ↥H) (v : ↥V),
      (a • v : ↥V).1 = a.1 * v.1 * a.1⁻¹ := by
    intro a v
    rfl
  have hcomm_mem : ∀ (a : ↥H) (v : ↥V),
      smulW a (QuotientGroup.mk' (V₀.subgroupOf V) v) =
        QuotientGroup.mk' (V₀.subgroupOf V) v →
      a.1 * v.1 * a.1⁻¹ * v.1⁻¹ ∈ V₀ := by
    intro a v hfix
    have h1 : (QuotientGroup.mk' (V₀.subgroupOf V) (a • v) : W) =
        QuotientGroup.mk' (V₀.subgroupOf V) v := by
      rw [← hsmul_mk a v]
      exact hfix
    have hdiv := (QuotientGroup.eq_iff_div_mem).mp h1
    rw [Subgroup.mem_subgroupOf] at hdiv
    have hz : ((a • v) / v : ↥V) =
        ⟨a.1 * v.1 * a.1⁻¹ * v.1⁻¹, by
          have haV : a.1 * v.1 * a.1⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.mp (hHV a.property) v.1).1 v.2
          exact V.mul_mem haV (V.inv_mem v.2)⟩ := by
      apply Subtype.ext
      simp [hsmul_coe a v, div_eq_mul_inv]
    rw [hz] at hdiv
    simpa using hdiv
  let Γ : Subgroup W :=
    ((V ⊓ D.M).subgroupOf V).map (QuotientGroup.mk' (V₀.subgroupOf V))
  let genW : Set W := {w : W | ∀ k : ↥H, k ∈ K → smulW k w = w} ∪
    ⋃ x : ↥H, ⋃ (_ : x ∈ K),
      {w : W | ∀ b : ↥H, b ∈ B' → smulW (x * b * x⁻¹) w = w}
  have hgenK : ∀ w : W, (∀ k : ↥H, k ∈ K → smulW k w = w) → w ∈ Γ := by
    intro w hw
    revert hw
    induction w using QuotientGroup.induction_on with
    | H v =>
      intro hw
      have hvM : v.1 ∈ D.M := by
        refine c.mem_M_of_commutator_mem_inf hRi s 0 v.2 ?_
        intro y hy
        have hyH : y ∈ H := (le_sup_right : R₁ ≤ H) hy
        let k : K := ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy⟩
        simpa [k] using hcomm_mem k.1 v (hw k.1 k.2)
      exact Subgroup.mem_map.mpr
        ⟨v, Subgroup.mem_subgroupOf.mpr ⟨v.2, hvM⟩, rfl⟩
  have hgenB : ∀ (x : ↥H), x ∈ K → ∀ w : W,
      (∀ b : ↥H, b ∈ B' → smulW (x * b * x⁻¹) w = w) → w ∈ Γ := by
    intro x hx w hw
    revert hw
    induction w using QuotientGroup.induction_on with
    | H v =>
      intro hw
      have hxR : x.1 ∈ R := (Subgroup.mem_subgroupOf.mp hx).1
      have hvM : v.1 ∈ D.M := by
        refine c.mem_M_of_conj_commutator_mem hsp3 s hxR v.2 ?_
        intro b hb
        have hbH : b ∈ H := (le_sup_left : B ≤ H) hb
        let b' : B' := ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb⟩
        have hcomm := hcomm_mem (x * b'.1 * x⁻¹) v (hw b'.1 b'.2)
        simpa [b'] using hcomm
      exact Subgroup.mem_map.mpr
        ⟨v, Subgroup.mem_subgroupOf.mpr ⟨v.2, hvM⟩, rfl⟩
  have htopΓ : Γ = ⊤ := by
    rw [eq_top_iff]
    rw [← hcl]
    change Subgroup.closure genW ≤ Γ
    refine (Subgroup.closure_le (K := Γ)).mpr ?_
    intro w hw
    rcases hw with hwK | hwB
    · exact hgenK w hwK
    · simp only [Set.mem_iUnion] at hwB
      obtain ⟨x, hx, hwx⟩ := hwB
      exact hgenB x hx w hwx
  intro v hv
  have hmk : (QuotientGroup.mk' (V₀.subgroupOf V) ⟨v, hv⟩ : W) ∈ Γ := by
    rw [htopΓ]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hmk
  have huM : u.1 ∈ D.M := (Subgroup.mem_subgroupOf.mp hu).2
  have hd : (u : ↥V) / ⟨v, hv⟩ ∈ V₀.subgroupOf V :=
    QuotientGroup.eq_iff_div_mem.mp hueq
  have hz : u.1 * v⁻¹ ∈ V₀ := by
    simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using hd
  have hz' : v * u.1⁻¹ ∈ V₀ := by
    simpa using V₀.inv_mem hz
  have hv_eq : v = (v * u.1⁻¹) * u.1 := by group
  rw [hv_eq]
  exact D.M.mul_mem (s.hV₀M hz') huM

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
