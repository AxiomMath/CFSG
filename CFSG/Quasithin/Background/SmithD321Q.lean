module

public import CFSG.Quasithin.Background.SmithD39TwoMod
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Background.D2Conj

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

structure D321Base (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W) : Prop where
  hD : D3Std M Mp T L V
  htT : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))
  hMp : Mp = L ⊔ conjAutSub t L
  hA38 : A38Types ↥L
  hsimp : IsSimpleGroup ↥L
  hcomm : ⁅L, conjAutSub t L⁆ = ⊥
  hinf : L ⊓ conjAutSub t L = ⊥
  hTperm : ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L

theorem d321Base_of (hL38 : D3L38) {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} (hD : D3Std M Mp T L V) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L) :
    D321Base M Mp T L V t := by
  obtain ⟨hA, hc, hi, hp⟩ := hL38 W M Mp T L V hD t htT htn hMp
  exact ⟨hD, htT, htn, hMp, hA,
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA, hc, hi, hp⟩

omit [Finite W] in
theorem mem_conjAutSub {X : Subgroup (MulAut W)} {g x : MulAut W} :
    x ∈ conjAutSub g X ↔ g⁻¹ * x * g ∈ X := mem_conjAutSub_iff

omit [Finite W] in
theorem conj_mem_conjAutSub {X : Subgroup (MulAut W)} (g : MulAut W) {x : MulAut W} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ conjAutSub g X := by
  rw [mem_conjAutSub]
  simpa [mul_assoc] using hx

omit [Finite W] in
theorem conjAutSub_mul (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

omit [Finite W] in
theorem mem_normalizer_iff_conjAutSub {X : Subgroup (MulAut W)} {g : MulAut W} :
    g ∈ Subgroup.normalizer (X : Set (MulAut W)) ↔ conjAutSub g X = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq

omit [Finite W] in
theorem map_commV_conjAutSub (g : MulAut W) (X : Subgroup (MulAut W)) :
    (commV X).map g.toMonoidHom = commV (conjAutSub g X) :=
  (CFSG.Quasithin.commV_map_conj_eq X g).symm

omit [Finite W] in
theorem map_fixV_conjAutSub (g : MulAut W) (X : Subgroup (MulAut W)) :
    (fixV X).map g.toMonoidHom = fixV (conjAutSub g X) :=
  (CFSG.Quasithin.fixV_map_conj_eq X g).symm

omit [Finite W] in
theorem commV_sup_le (X Y : Subgroup (MulAut W)) : commV (X ⊔ Y) ≤ commV X ⊔ commV Y :=
  CFSG.Quasithin.FixVLat.commV_sup_le X Y

private theorem eq_one_of_comm_of_simple {X : Subgroup (MulAut W)} (hX : IsSimpleGroup ↥X)
    {M : Subgroup (MulAut W)} (hXc : X ∈ cComp M) {a : MulAut W} (ha : a ∈ X)
    (hac : ∀ y ∈ X, a * y = y * a) : a = 1 := by
  have hZ : Subgroup.center ↥X = ⊥ := by
    rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h0 | h0
    · exact h0
    · exfalso
      refine not_isSolvable_of_mem_cComp hXc (Group.isSolvable_of_comm fun c d => ?_)
      exact Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top d) c
  have hmem : (⟨a, ha⟩ : ↥X) ∈ Subgroup.center ↥X :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (hac y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem exp : ∀ w : W, w ^ 2 = 1 := hB.hD.hyp.exp

theorem L_le : L ≤ M := le_of_mem_cComp hB.hD.hyp.comp

theorem T_le : T ≤ M := hB.hD.hyp.sylow.1

theorem t_mem : t ∈ M := hB.T_le hB.htT

theorem Lt_mem_cComp : conjAutSub t L ∈ cComp M := conjAutSub_mem_cComp hB.hD.hyp.comp hB.t_mem

theorem Lt_le : conjAutSub t L ≤ M := le_of_mem_cComp hB.Lt_mem_cComp

theorem Mp_le : Mp ≤ M := hB.hMp ▸ sup_le hB.L_le hB.Lt_le

theorem L_le_Mp : L ≤ Mp := hB.hMp ▸ le_sup_left

theorem Lt_le_Mp : conjAutSub t L ≤ Mp := hB.hMp ▸ le_sup_right

theorem conj_mem_Mp {g : MulAut W} (hg : g ∈ M) {x : MulAut W} (hx : x ∈ Mp) : g * x * g⁻¹ ∈ Mp :=
  (Subgroup.mem_normalizer_iff.1 (hB.hD.hyp.Mp_normal hg) x).1 hx

theorem quasi : CFSG.IsQuasisimple ↥L := hB.hD.hyp.quasi

theorem Lt_quasi : CFSG.IsQuasisimple ↥(conjAutSub t L) := (hB.hD.hyp.conj hB.htT).quasi

theorem Lt_simp : IsSimpleGroup ↥(conjAutSub t L) :=
  have := hB.hsimp
  MulEquiv.isSimpleGroup
    (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm

theorem perfect : ⁅L, L⁆ = L := perfect_of_mem_cComp hB.hD.hyp.comp

theorem Lt_perfect : ⁅conjAutSub t L, conjAutSub t L⁆ = conjAutSub t L :=
  perfect_of_mem_cComp hB.Lt_mem_cComp

theorem comm : ∀ a ∈ L, ∀ b ∈ conjAutSub t L, a * b = b * a := by
  intro a ha b hb
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hB.hcomm ha
  exact ((Subgroup.mem_centralizer_iff.1 h) b hb).symm

theorem Mp_perfect : ⁅Mp, Mp⁆ = Mp := by
  refine le_antisymm (Subgroup.commutator_le_self Mp) ?_
  have h1 : ⁅L, L⁆ ≤ ⁅Mp, Mp⁆ := Subgroup.commutator_mono hB.L_le_Mp hB.L_le_Mp
  have h2 : ⁅conjAutSub t L, conjAutSub t L⁆ ≤ ⁅Mp, Mp⁆ :=
    Subgroup.commutator_mono hB.Lt_le_Mp hB.Lt_le_Mp
  rw [hB.perfect] at h1
  rw [hB.Lt_perfect] at h2
  calc Mp = L ⊔ conjAutSub t L := hB.hMp
    _ ≤ ⁅Mp, Mp⁆ := sup_le h1 h2

theorem Lt_ne : conjAutSub t L ≠ L := fun h => hB.htn (mem_normalizer_iff_conjAutSub.2 h)

theorem exists_mul_of_mem_Mp {x : MulAut W} (hx : x ∈ Mp) :
    ∃ a ∈ L, ∃ b ∈ conjAutSub t L, x = a * b := by
  rw [hB.hMp] at hx
  exact (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hB.comm)).1 hx

theorem conj_mem_L {x : MulAut W} (hx : x ∈ Mp) {l : MulAut W} (hl : l ∈ L) : x * l * x⁻¹ ∈ L :=
  InternalSec.conj_mem_of_mem_sup_of_commute hB.comm x (hB.hMp ▸ hx) l hl

theorem conj_mem_Lt {x : MulAut W} (hx : x ∈ Mp) {l : MulAut W} (hl : l ∈ conjAutSub t L) :
    x * l * x⁻¹ ∈ conjAutSub t L := by
  have hc : ∀ a ∈ conjAutSub t L, ∀ b ∈ L, a * b = b * a := fun a ha b hb =>
    (hB.comm b hb a ha).symm
  have hx' : x ∈ conjAutSub t L ⊔ L := by rw [sup_comm, ← hB.hMp]; exact hx
  exact InternalSec.conj_mem_of_mem_sup_of_commute hc x hx' l hl

theorem eq_one_of_mem_Mp {x : MulAut W} (hx : x ∈ Mp) (hxc : ∀ y ∈ Mp, x * y = y * x) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hx
  have hac : ∀ y ∈ L, a * y = y * a := by
    intro y hy
    have h1 := hxc y (hB.L_le_Mp hy)
    have h2 : b * y = y * b := (hB.comm y hy b hb).symm
    calc a * y = a * b * y * b⁻¹ := by rw [mul_assoc a b y, h2]; group
      _ = y * (a * b) * b⁻¹ := by rw [h1]
      _ = y * a := by group
  have ha1 : a = 1 := eq_one_of_comm_of_simple hB.hsimp hB.hD.hyp.comp ha hac
  subst ha1
  have hbc : ∀ y ∈ conjAutSub t L, b * y = y * b := by
    intro y hy
    simpa using hxc y (hB.Lt_le_Mp hy)
  rw [eq_one_of_comm_of_simple hB.Lt_simp hB.Lt_mem_cComp hb hbc, mul_one]

theorem cent_inf_Mp : M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ⊓ Mp = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨-, hxc⟩, hxMp⟩
  exact Subgroup.mem_bot.2 (hB.eq_one_of_mem_Mp hxMp fun y hy =>
    ((Subgroup.mem_centralizer_iff.1 hxc) y hy).symm)

theorem conj_cases {g : MulAut W} (hg : g ∈ M) :
    conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L := by
  have hK : conjAutSub g L ∈ cComp M := conjAutSub_mem_cComp hB.hD.hyp.comp hg
  have hKq : CFSG.IsQuasisimple ↥(conjAutSub g L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      hB.quasi
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have h1 : ⁅L, conjAutSub g L⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hB.hD.hyp.comp hK hB.quasi
      hKq).resolve_left fun h => hne1 h.symm
  have h2 : ⁅conjAutSub t L, conjAutSub g L⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hB.Lt_mem_cComp hK hB.Lt_quasi
      hKq).resolve_left fun h => hne2 h.symm
  have hKMp : conjAutSub g L ≤ Mp := by
    intro x hx
    have hx' := hB.conj_mem_Mp hg (hB.L_le_Mp (mem_conjAutSub.1 hx))
    simpa [mul_assoc] using hx'
  have hc : Mp ≤ Subgroup.centralizer (conjAutSub g L : Set (MulAut W)) := by
    rw [hB.hMp]
    exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
  have hab : ⁅conjAutSub g L, conjAutSub g L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKMp.trans hc)
  exact ne_bot_of_mem_cComp hK ((perfect_of_mem_cComp hK).symm.trans hab)

theorem conj_Lt_of_mem_normalizer {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    conjAutSub g (conjAutSub t L) = conjAutSub t L := by
  have hgL' : conjAutSub g L = L := mem_normalizer_iff_conjAutSub.1 hgL
  rcases hB.conj_cases (M.mul_mem hg hB.t_mem) with h | h
  · exfalso
    apply hB.Lt_ne
    have h1 : conjAutSub g (conjAutSub t L) = conjAutSub g L := by rw [← conjAutSub_mul, h, hgL']
    have h2 := congrArg (conjAutSub g⁻¹) h1
    rwa [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at h2
  · rw [← conjAutSub_mul]
    exact h

theorem conj_swap {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    conjAutSub g L = conjAutSub t L ∧ conjAutSub g (conjAutSub t L) = L := by
  have h1 : conjAutSub g L = conjAutSub t L :=
    (hB.conj_cases hg).resolve_left fun h => hgL (mem_normalizer_iff_conjAutSub.2 h)
  refine ⟨h1, ?_⟩
  rcases hB.conj_cases (M.mul_mem hg hB.t_mem) with h | h
  · rw [← conjAutSub_mul]
    exact h
  · exfalso
    apply hB.Lt_ne
    have h2 : conjAutSub g (conjAutSub t L) = conjAutSub g L := by rw [← conjAutSub_mul, h, h1]
    have h3 := congrArg (conjAutSub g⁻¹) h2
    rwa [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at h3

theorem inv_mul_mem_normalizer {g h : MulAut W} (hg : g ∈ M) (hh : h ∈ M)
    (hgL : g ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hhL : h ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    g⁻¹ * h ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [mem_normalizer_iff_conjAutSub, conjAutSub_mul, (hB.conj_swap hh hhL).1]
  have h3 := congrArg (conjAutSub g⁻¹) (hB.conj_swap hg hgL).1
  rw [conjAutSub_inv_conjAutSub] at h3
  exact h3.symm

end D321Base

omit [Finite W] in
private theorem commOf_eq_of_surj {A A' : Type*} [Group A] [Group A'] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction A Q] [MulDistribMulAction A' Q] (φ : A' → A)
    (hφ : Function.Surjective φ) (hact : ∀ (a : A') (q : Q), a • q = φ a • q) (R : Subgroup Q) :
    XMod.commOf A' R = XMod.commOf A R := by
  unfold XMod.commOf
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨φ a, l, hl, by rw [hact]⟩
  · rintro ⟨a, l, hl, rfl⟩
    obtain ⟨a', rfl⟩ := hφ a
    exact ⟨a', l, hl, by rw [hact]⟩

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem Λ_normal : ∀ g : ↥M, ∀ l ∈ Mp.subgroupOf M, g * l * g⁻¹ ∈ Mp.subgroupOf M :=
  fun g _ hl => hB.conj_mem_Mp g.2 hl

theorem commV_eq_top : commV Mp = ⊤ := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hB.hD.hyp.irr
  exact Z391.commV_eq_top (fun m hm l hl => hB.conj_mem_Mp hm hl) hVcomm hB.hD.hyp.gen

theorem quot_sq : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_pow, hB.exp v, QuotientGroup.mk_one]

private theorem surj_Mp :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ φ : ↥(Mp.subgroupOf M) → ↥Mp, Function.Surjective φ ∧
      ∀ (l : ↥(Mp.subgroupOf M)) (x : W ⧸ modFix Mp (⊤ : Subgroup W)), l • x = φ l • x := by
  let _i := qAct hB.hD.hyp.Mp_normal
  refine ⟨fun l => ⟨((l : ↥M) : MulAut W), l.2⟩,
    fun a => ⟨⟨⟨(a : MulAut W), hB.Mp_le a.2⟩, a.2⟩, rfl⟩, fun l x => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H v => rfl

theorem irr :
    letI := qAct hB.hD.hyp.Mp_normal
    XMod.IsIrr ↥(Mp.subgroupOf M) (tilde Mp ⊤ V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨φ, hφ, hact⟩ := hB.surj_Mp
  exact isIrr_of_surj φ hφ hact (isIrr_tilde hB.hD.hyp.irr).1

theorem commOf_tilde :
    letI := qAct hB.hD.hyp.Mp_normal
    XMod.commOf ↥(Mp.subgroupOf M) (tilde Mp ⊤ V) = tilde Mp ⊤ V := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨φ, hφ, hact⟩ := hB.surj_Mp
  rw [commOf_eq_of_surj φ hφ hact]
  exact (isIrr_tilde hB.hD.hyp.irr).2

theorem gen :
    letI := qAct hB.hD.hyp.Mp_normal
    (⨆ g : ↥M, g • tilde Mp ⊤ V) = ⊤ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have e : ∀ g : ↥M, g • tilde Mp ⊤ V = tilde Mp ⊤ ((g : MulAut W) • V) :=
    fun g => smul_tildeQ hB.hD.hyp.Mp_normal g V
  rw [iSup_congr e, ← tilde_biSup M V]
  have : (⨆ y ∈ M, y • V) = ⊤ := hB.hD.hyp.gen
  rw [this]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem commOf_eq (R : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) :
    letI := qAct hB.hD.hyp.Mp_normal
    XMod.IsInv ↥(Mp.subgroupOf M) R → XMod.commOf ↥(Mp.subgroupOf M) R = R := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro hR
  exact SmithD39Two.commOf_eq_of_iSup_smul hB.Λ_normal hB.irr hB.commOf_tilde hB.gen hR

theorem fixed_eq_bot :
    letI := qAct hB.hD.hyp.Mp_normal
    XMod.fixed ↥(Mp.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) = ⊥ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have h1 := hB.commOf_eq _ (XMod.isInv_fixed (A := ↥(Mp.subgroupOf M))
    (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))))
  rw [← h1]
  exact XMod.commOf_eq_bot_iff.2 le_rfl

theorem tilde_ne_bot :
    tilde Mp ⊤ V ≠ (⊥ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  exact hB.irr.2.1.ne'

private theorem not_fix_L :
    letI := qAct hB.hD.hyp.Mp_normal
    ¬ ∀ l (hl : l ∈ L), ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨l, hB.L_le hl⟩ : ↥M) • q = q := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro hL
  have hLt : ∀ y (hy : y ∈ conjAutSub t L), ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
      (⟨y, hB.Lt_le hy⟩ : ↥M) • q = q := by
    intro y hy q
    have hl : t⁻¹ * y * t ∈ L := mem_conjAutSub.1 hy
    have e : (⟨y, hB.Lt_le hy⟩ : ↥M) =
        ⟨t, hB.t_mem⟩ * ⟨t⁻¹ * y * t, hB.L_le hl⟩ * ⟨t, hB.t_mem⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, mul_smul, mul_smul, hL _ hl, smul_inv_smul]
  have hall : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
      q ∈ XMod.fixed ↥(Mp.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
    intro q
    refine ⟨trivial, fun m => ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hB.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 m.2)
    have e : ((m : ↥M)) = ⟨a, hB.L_le ha⟩ * ⟨b, hB.Lt_le hb⟩ := Subtype.ext hab
    show (m : ↥M) • q = q
    rw [e, mul_smul, hLt b hb, hL a ha]
  apply hB.tilde_ne_bot
  rw [eq_bot_iff]
  intro q _
  have h := hall q
  rw [hB.fixed_eq_bot] at h
  exact h

private theorem not_fix_Lt :
    letI := qAct hB.hD.hyp.Mp_normal
    ¬ ∀ y (hy : y ∈ conjAutSub t L), ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
      (⟨y, hB.Lt_le hy⟩ : ↥M) • q = q := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro hLt
  apply hB.not_fix_L
  intro l hl q
  have hy : t * l * t⁻¹ ∈ conjAutSub t L := conj_mem_conjAutSub t hl
  have e : (⟨l, hB.L_le hl⟩ : ↥M) =
      ⟨t, hB.t_mem⟩⁻¹ * ⟨t * l * t⁻¹, hB.Lt_le hy⟩ * ⟨t, hB.t_mem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, mul_smul, mul_smul, hLt _ hy, inv_smul_smul]

private theorem eq_one_of_fix_simple {X : Subgroup (MulAut W)} (hX : IsSimpleGroup ↥X)
    (hXM : X ≤ M) (hnot : letI := qAct hB.hD.hyp.Mp_normal
      ¬ ∀ y (hy : y ∈ X), ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨y, hXM hy⟩ : ↥M) • q = q)
    {y : MulAut W} (hy : y ∈ X)
    (hyq : letI := qAct hB.hD.hyp.Mp_normal
      ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨y, hXM hy⟩ : ↥M) • q = q) : y = 1 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let ρ : ↥X →* MulAut (W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    (MulDistribMulAction.toMulAut ↥M (W ⧸ modFix Mp (⊤ : Subgroup W))).comp
      (Subgroup.inclusion hXM)
  have hρ : ∀ (z : ↥X) (q : W ⧸ modFix Mp (⊤ : Subgroup W)),
      ρ z q = (⟨(z : MulAut W), hXM z.2⟩ : ↥M) • q := fun _ _ => rfl
  rcases hX.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · have hmem : (⟨y, hy⟩ : ↥X) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      ext q
      rw [hρ]
      exact hyq q
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hnot
    intro z hz q
    have hmem : (⟨z, hz⟩ : ↥X) ∈ ρ.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have := congrArg (fun φ : MulAut (W ⧸ modFix Mp (⊤ : Subgroup W)) => φ q) hmem
    simpa [hρ] using this

private theorem eq_one_of_mem_Mp_of_fix {x : MulAut W} (hxMp : x ∈ Mp)
    (hx : letI := qAct hB.hD.hyp.Mp_normal
      ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨x, hB.Mp_le hxMp⟩ : ↥M) • q = q) : x = 1 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have key : ∀ {X : Subgroup (MulAut W)} (hX : IsSimpleGroup ↥X) (hXM : X ≤ M)
      (hXn : ∀ l ∈ X, x * l * x⁻¹ ∈ X)
      (hnot : ¬ ∀ y (hy : y ∈ X), ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
        (⟨y, hXM hy⟩ : ↥M) • q = q), ∀ l ∈ X, x * l = l * x := by
    intro X hX hXM hXn hnot l hl
    have hc : x * l * x⁻¹ * l⁻¹ ∈ X := X.mul_mem (hXn l hl) (X.inv_mem hl)
    have hfix : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
        (⟨x * l * x⁻¹ * l⁻¹, hXM hc⟩ : ↥M) • q = q := by
      intro q
      have e : (⟨x * l * x⁻¹ * l⁻¹, hXM hc⟩ : ↥M) = (⟨x, hB.Mp_le hxMp⟩ : ↥M) *
          (⟨l, hXM hl⟩ : ↥M) * (⟨x, hB.Mp_le hxMp⟩ : ↥M)⁻¹ * (⟨l, hXM hl⟩ : ↥M)⁻¹ := rfl
      have hxinv : (⟨x, hB.Mp_le hxMp⟩ : ↥M)⁻¹ • ((⟨l, hXM hl⟩ : ↥M)⁻¹ • q) =
          (⟨l, hXM hl⟩ : ↥M)⁻¹ • q := by
        rw [inv_smul_eq_iff, hx]
      rw [e, mul_smul, mul_smul, mul_smul, hxinv, smul_inv_smul, hx]
    have h1 := hB.eq_one_of_fix_simple hX hXM hnot hc hfix
    calc x * l = x * l * x⁻¹ * l⁻¹ * l * x := by group
      _ = l * x := by rw [h1]; group
  have hL := key hB.hsimp hB.L_le (fun l hl => hB.conj_mem_L hxMp hl) hB.not_fix_L
  have hLt := key hB.Lt_simp hB.Lt_le (fun l hl => hB.conj_mem_Lt hxMp hl) hB.not_fix_Lt
  refine hB.eq_one_of_mem_Mp hxMp fun y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hy
  rw [← mul_assoc, hL a ha, mul_assoc, hLt b hb, mul_assoc]

theorem faithful {x : MulAut W} (hxM : x ∈ M) :
    letI := qAct hB.hD.hyp.Mp_normal
    (∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨x, hxM⟩ : ↥M) • q = q) → x = 1 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  intro hx
  have hxc : ∀ m ∈ Mp, x * m = m * x := by
    intro m hm
    have hc : x * m * x⁻¹ * m⁻¹ ∈ Mp := Mp.mul_mem (hB.conj_mem_Mp hxM hm) (Mp.inv_mem hm)
    have hfix : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W),
        (⟨x * m * x⁻¹ * m⁻¹, hB.Mp_le hc⟩ : ↥M) • q = q := by
      intro q
      have e : (⟨x * m * x⁻¹ * m⁻¹, hB.Mp_le hc⟩ : ↥M) = (⟨x, hxM⟩ : ↥M) *
          (⟨m, hB.Mp_le hm⟩ : ↥M) * (⟨x, hxM⟩ : ↥M)⁻¹ * (⟨m, hB.Mp_le hm⟩ : ↥M)⁻¹ := rfl
      have hxinv : (⟨x, hxM⟩ : ↥M)⁻¹ • ((⟨m, hB.Mp_le hm⟩ : ↥M)⁻¹ • q) =
          (⟨m, hB.Mp_le hm⟩ : ↥M)⁻¹ • q := by
        rw [inv_smul_eq_iff, hx]
      rw [e, mul_smul, mul_smul, mul_smul, hxinv, smul_inv_smul, hx]
    have h1 := hB.eq_one_of_mem_Mp_of_fix hc hfix
    calc x * m = x * m * x⁻¹ * m⁻¹ * m * x := by group
      _ = m * x := by rw [h1]; group
  refine eq_one_of_fix_quot hB.commV_eq_top hxc fun w => ?_
  have h1 : (QuotientGroup.mk (x w) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk w :=
    hx (QuotientGroup.mk w)
  rw [QuotientGroup.eq, modFix_top_eq] at h1
  have h2 := (fixV Mp).inv_mem h1
  rwa [mul_inv_rev, inv_inv, mul_comm] at h2

theorem nB_le_rkIdx {X : Subgroup (MulAut W)} (hXM : X ≤ M) :
    letI := qAct hB.hD.hyp.Mp_normal
    nB (X.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤ rkIdx (fixV X) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have h := Z391.nB_top_le_rkIdx_fixV (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)))
    (QuotientGroup.mk'_surjective _) (fun g w => rfl) (X.subgroupOf M)
  rwa [Subgroup.map_subgroupOf_eq_of_le hXM] at h

end D321Base

omit [Finite W] in
theorem fix_map {V : Subgroup W} {X : Subgroup (MulAut W)} (hVX : ∀ v ∈ V, ∀ y ∈ X, y v = v)
    (g : MulAut W) : ∀ v ∈ V.map g.toMonoidHom, ∀ y ∈ conjAutSub g X, y v = v := by
  rintro _ ⟨v, hv, rfl⟩ y hy
  have h1 := hVX v hv _ (mem_conjAutSub.1 hy)
  have h2 : y (g v) = g ((g⁻¹ * y * g) v) := by simp [MulAut.mul_apply]
  rw [MulEquiv.coe_toMonoidHom, h2, h1]

omit [Finite W] in
theorem fixV_anti {X Y : Subgroup (MulAut W)} (hXY : X ≤ Y) : fixV Y ≤ fixV X :=
  fun _ hw => mem_fixV.2 fun y hy => (mem_fixV.1 hw) y (hXY hy)

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem Mp_inv_V : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := (mem_irrPlus_top_iff.1 hB.hD.hyp.irr).1

theorem Mp_inv_map {g : MulAut W} (hg : g ∈ M) :
    ∀ x ∈ Mp, ∀ v ∈ V.map g.toMonoidHom, x v ∈ V.map g.toMonoidHom := by
  rintro x hx _ ⟨v, hv, rfl⟩
  have hx' : g⁻¹ * x * g ∈ Mp := by
    have := hB.conj_mem_Mp (M.inv_mem hg) hx
    simpa using this
  refine ⟨(g⁻¹ * x * g) v, hB.Mp_inv_V _ hx' v hv, ?_⟩
  simp [MulAut.mul_apply]

variable (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v)
include hVt

theorem map_le_fixV_Lt {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    V.map g.toMonoidHom ≤ fixV (conjAutSub t L) := by
  intro v hv
  refine mem_fixV.2 fun y hy => ?_
  have h := fix_map hVt g v hv y
  rw [hB.conj_Lt_of_mem_normalizer hg hgL] at h
  exact h hy

theorem map_le_fixV_L {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    V.map g.toMonoidHom ≤ fixV L := by
  intro v hv
  refine mem_fixV.2 fun y hy => ?_
  have h := fix_map hVt g v hv y
  rw [(hB.conj_swap hg hgL).2] at h
  exact h hy

theorem commV_le_iSup :
    commV L ≤ ⨆ g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map g.toMonoidHom := by
  set S := ⨆ g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map g.toMonoidHom with hS
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, rfl⟩
  let δ : W →* W := MonoidHom.mk' (fun w => x w * w⁻¹) (fun a b => by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm b⁻¹ a⁻¹]
    ac_rfl)
  have hle : (⊤ : Subgroup W) ≤ S.comap δ := by
    rw [← hB.hD.hyp.gen]
    refine iSup₂_le fun g hg v hv => ?_
    show x v * v⁻¹ ∈ S
    by_cases hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))
    · have hmem : x v * v⁻¹ ∈ V.map g.toMonoidHom :=
        (V.map g.toMonoidHom).mul_mem (hB.Mp_inv_map hg x (hB.L_le_Mp hx) v hv)
          ((V.map g.toMonoidHom).inv_mem hv)
      exact (le_iSup₂ (f := fun (g : MulAut W)
        (_ : g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W))) => V.map g.toMonoidHom) g
        ⟨hg, hgL⟩) hmem
    · have h1 : x v = v := (mem_fixV.1 (hB.map_le_fixV_L hVt hg hgL hv)) x hx
      rw [h1, mul_inv_cancel]
      exact S.one_mem
  exact hle (Subgroup.mem_top w)

theorem commV_le_fixV : commV L ≤ fixV (conjAutSub t L) :=
  (hB.commV_le_iSup hVt).trans (iSup₂_le fun _ hg => hB.map_le_fixV_Lt hVt hg.1 hg.2)

theorem commV_Lt_le_fixV : commV (conjAutSub t L) ≤ fixV L := by
  have h1 := Subgroup.map_mono (f := t.toMonoidHom) (hB.commV_le_fixV hVt)
  rw [map_commV_conjAutSub, map_fixV_conjAutSub, (hB.conj_swap hB.t_mem hB.htn).2] at h1
  exact h1

omit hVt in
theorem commV_sup_map : commV L ⊔ (commV L).map t.toMonoidHom = ⊤ := by
  rw [map_commV_conjAutSub, eq_top_iff, ← hB.commV_eq_top, hB.hMp]
  exact commV_sup_le L (conjAutSub t L)

theorem isSumMod : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ := by
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ le_top
    rw [← hB.commV_sup_map]
    exact le_sup_left
  · have h1 : commV L ⊔ fixV Mp ≤ fixV (conjAutSub t L) :=
      sup_le (hB.commV_le_fixV hVt) (fixV_anti hB.Lt_le_Mp)
    have h2 : (commV L).map t.toMonoidHom ⊔ fixV Mp ≤ fixV L := by
      rw [map_commV_conjAutSub]
      exact sup_le (hB.commV_Lt_le_fixV hVt) (fixV_anti hB.L_le_Mp)
    calc (commV L ⊔ fixV Mp) ⊓ ((commV L).map t.toMonoidHom ⊔ fixV Mp)
        ≤ fixV (conjAutSub t L) ⊓ fixV L := inf_le_inf h1 h2
      _ = fixV Mp := by rw [hB.hMp, fixV_sup, inf_comm]

theorem V_le_commV : V ≤ commV L := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hB.hD.hyp.irr
  rw [← hVcomm, commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hx
  have hbv : b v = v := hVt v hv b hb
  rw [MulAut.mul_apply, hbv]
  exact Subgroup.subset_closure ⟨a, ha, v, rfl⟩

omit hVt in
theorem not_le_orbSup (htop : orbSup T V ≠ ⊤) : ¬ commV L ≤ orbSup T V ⊔ fixV Mp := by
  intro h
  apply htop
  have hGV : Mp ⊔ T ≤ stabSub (orbSup T V) :=
    (n1_sup_le_stabSub_sec hB.hD.hyp).trans inf_le_left
  have htZ : (fixV Mp).map t.toMonoidHom = fixV Mp := by
    rw [map_fixV_conjAutSub,
      mem_normalizer_iff_conjAutSub.1 (hB.hD.hyp.Mp_normal hB.t_mem)]
  have htV : (orbSup T V).map t.toMonoidHom = orbSup T V :=
    mem_stabSub_iff_map_eq.1 (le_stabSub_orbSup T V hB.htT)
  have h2 : (commV L).map t.toMonoidHom ≤ orbSup T V ⊔ fixV Mp := by
    calc (commV L).map t.toMonoidHom ≤ (orbSup T V ⊔ fixV Mp).map t.toMonoidHom :=
          Subgroup.map_mono h
      _ = orbSup T V ⊔ fixV Mp := by rw [Subgroup.map_sup, htV, htZ]
  have h3 : orbSup T V ⊔ fixV Mp = ⊤ := by
    rw [eq_top_iff, ← hB.commV_sup_map]
    exact sup_le h h2
  rw [eq_top_iff, ← hB.commV_eq_top, commV_eq_commSub, ← h3, commSub_sup_fixV le_rfl]
  exact commSub_le_of_invariant fun x hx w hw => (hGV ((le_sup_left : Mp ≤ Mp ⊔ T) hx) w).2 hw

theorem tildeU_le_fixed :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) ≤ XMod.fixed ↥((conjAutSub t L).subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨trivial, fun y => ?_⟩
  have hy : ((y : ↥M) : MulAut W) ∈ conjAutSub t L := Subgroup.mem_subgroupOf.1 y.2
  change (QuotientGroup.mk (((y : ↥M) : MulAut W) u) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
    QuotientGroup.mk u
  rw [(mem_fixV.1 (hB.commV_le_fixV hVt hu)) _ hy]

omit hVt in
theorem smul_tildeU :
    letI := qAct hB.hD.hyp.Mp_normal
    (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) = tilde Mp ⊤ (commV (conjAutSub t L)) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [smul_tildeQ hB.hD.hyp.Mp_normal, ← map_commV_conjAutSub]
  rfl

omit hVt in
theorem sup_tildeU :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) ⊔ (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) = ⊤ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [hB.smul_tildeU, ← map_commV_conjAutSub]
  unfold tilde
  rw [← Subgroup.map_sup, hB.commV_sup_map]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem inf_tildeU :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) ⊓ (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) = ⊥ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [hB.smul_tildeU, ← map_commV_conjAutSub, eq_bot_iff]
  rintro _ ⟨⟨u, hu, rfl⟩, ⟨u', hu', hq⟩⟩
  have hz : u'⁻¹ * u ∈ fixV Mp := by
    have h1 : (QuotientGroup.mk u' : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk u := hq
    rw [QuotientGroup.eq, modFix_top_eq] at h1
    exact h1
  have hmem : u ∈ (commV L ⊔ fixV Mp) ⊓ ((commV L).map t.toMonoidHom ⊔ fixV Mp) := by
    refine ⟨Subgroup.mem_sup_left hu, ?_⟩
    have e : u = u' * (u'⁻¹ * u) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hu' hz
  have hu0 := (hB.isSumMod hVt).2 hmem
  rw [Subgroup.mem_bot]
  show (QuotientGroup.mk u : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
  rw [QuotientGroup.eq_one_iff, modFix_top_eq]
  exact hu0

theorem tildeV_le_tildeU : tilde Mp ⊤ V ≤ tilde Mp ⊤ (commV L) :=
  tilde_mono (hB.V_le_commV hVt)

theorem tildeU_eq_iSup :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) = ⨆ (g : ↥M) (_ : (g : MulAut W) ∈
      Subgroup.normalizer (L : Set (MulAut W))), g • tilde Mp ⊤ V := by
  let _i := qAct hB.hD.hyp.Mp_normal
  apply le_antisymm
  · refine (tilde_mono (hB.commV_le_iSup hVt)).trans ?_
    unfold tilde
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 : (V.map g.toMonoidHom).map (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) =
        (⟨g, hg.1⟩ : ↥M) • V.map (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) :=
      (smul_tildeQ hB.hD.hyp.Mp_normal ⟨g, hg.1⟩ V).symm
    rw [h1]
    exact le_iSup₂ (f := fun (g : ↥M) (_ : (g : MulAut W) ∈
      Subgroup.normalizer (L : Set (MulAut W))) =>
        g • V.map (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)))) ⟨g, hg.1⟩ hg.2
  · refine iSup₂_le fun g hg => ?_
    rw [smul_tildeQ hB.hD.hyp.Mp_normal]
    refine tilde_mono ?_
    have h1 : (g : MulAut W) • V ≤ (g : MulAut W) • commV L :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (hB.V_le_commV hVt)
    refine h1.trans (le_of_eq ?_)
    change (commV L).map (g : MulAut W).toMonoidHom = commV L
    rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hg]

theorem irr_L :
    letI := qAct hB.hD.hyp.Mp_normal
    XMod.IsIrr ↥(L.subgroupOf M) (tilde Mp ⊤ V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  have hirr := hB.irr
  have htriv : ∀ (y : ↥M), (y : MulAut W) ∈ conjAutSub t L → ∀ q ∈ tilde Mp ⊤ V, y • q = q := by
    rintro y hy _ ⟨v, hv, rfl⟩
    change (QuotientGroup.mk ((y : MulAut W) v) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      QuotientGroup.mk v
    rw [hVt v hv _ hy]
  have key : ∀ J ≤ tilde Mp ⊤ V, XMod.IsInv ↥(L.subgroupOf M) J →
      XMod.IsInv ↥(Mp.subgroupOf M) J := by
    intro J hJ hJinv m j hj
    obtain ⟨a, ha, b, hb, hab⟩ := hB.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 m.2)
    have e : (m : ↥M) = ⟨a, hB.L_le ha⟩ * ⟨b, hB.Lt_le hb⟩ := Subtype.ext hab
    show (m : ↥M) • j ∈ J
    rw [e, mul_smul, htriv _ hb j (hJ hj)]
    exact hJinv ⟨⟨a, hB.L_le ha⟩, ha⟩ j hj
  refine ⟨fun l q hq => ?_, hirr.2.1, fun J hJ hJ0 hJV => hirr.2.2 J (key J hJV hJ) hJ0 hJV⟩
  exact hirr.1 ⟨(l : ↥M), Subgroup.mem_subgroupOf.2
    (hB.L_le_Mp (Subgroup.mem_subgroupOf.1 l.2))⟩ q hq

end D321Base

structure D321Sit (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W)
    (A : Subgroup (MulAut W)) (r : ℚ) : Prop extends D321Base M Mp T L V t where
  hr : qhatOf M = (r : WithTop ℚ)
  hr2 : r ≤ 2
  htop : orbSup T V ≠ ⊤
  hAQ : A ∈ QhatStar M
  hAT : A ≤ T
  hAr : rAV A = r

theorem D321Base.exists_sit {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) : ∃ A r, D321Sit M Mp T L V t A r := by
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf M = (r : WithTop ℚ) := by
    have hne : qhatOf M ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hqM
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨r, hr.symm⟩
  have hr2 : r ≤ 2 := WithTop.coe_le_coe.mp (hr ▸ hqM)
  obtain ⟨A₁, hA₁⟩ := QhatStar_nonempty hr hr2
  have hA₁2 : IsPGroup 2 ↥A₁ := by
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA₁
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hA₁x⟩ := F7.isSylowTwoOf_exists_conj_le hB.hD.hyp.sylow (QhatStar_le hA₁) hA₁2
  set A := conjBy x⁻¹ A₁ with hAdef
  have hAQ : A ∈ QhatStar M := conjBy_mem_QhatStar hA₁ (M.inv_mem hx)
  have hAT : A ≤ T := by
    intro y hy
    rw [mem_conjBy_iff, inv_inv] at hy
    have := hA₁x hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  obtain ⟨r', hr', -, ⟨⟨-, hAr'⟩, -⟩, -⟩ := QhatStar_spec hAQ
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  rw [hrr] at hAr'
  exact ⟨A, r, ⟨hB, hr, hr2, htop, hAQ, hAT, hAr'⟩⟩

namespace D321Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
include hS

theorem A_le : A ≤ M := QhatStar_le hS.hAQ

theorem isA2 : IsA2 M A := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hS.hAQ
  exact hA2

theorem elemAb : IsElemAbelian2 A := hS.isA2.isElemAbelian2

theorem isPGroup : IsPGroup 2 ↥A := hS.elemAb.isPGroup

theorem cubic : commSeries A 3 = ⊥ := by
  obtain ⟨r', -, -, ⟨-, hA3⟩, -⟩ := QhatStar_spec hS.hAQ
  exact hA3

theorem rk_pos : 0 < rk ↥A := hS.isA2.rk_pos

theorem rkIdx_le : rkIdx (fixV A) ≤ 2 * rk ↥A := by
  have h := hS.hAr.le.trans hS.hr2
  unfold rAV at h
  have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hS.rk_pos
  rw [div_le_iff₀ hpos] at h
  exact_mod_cast h

theorem nB_le :
    letI := qAct hS.hD.hyp.Mp_normal
    nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤ 2 * rk ↥A := by
  let _i := qAct hS.hD.hyp.Mp_normal
  exact (hS.nB_le_rkIdx hS.A_le).trans hS.rkIdx_le

end D321Sit

omit [Finite W] in
private theorem relIndex_eq_two {H K : Subgroup (MulAut W)} {a : MulAut W} (haK : a ∈ K)
    (h : ∀ b ∈ K, Xor (b * a ∈ H) (b ∈ H)) : (K ⊓ H).relIndex K = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨a, haK⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul, b.2,
    K.mul_mem b.2 haK, true_and]
  exact h b b.2

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem relIndex_normalizer :
    (M ⊓ Subgroup.normalizer (L : Set (MulAut W))).relIndex M = 2 := by
  have hkey : ∀ b ∈ M, Xor (b * t ∈ Subgroup.normalizer (L : Set (MulAut W)))
      (b ∈ Subgroup.normalizer (L : Set (MulAut W))) := by
    intro b hb
    by_cases hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W))
    · refine Or.inr ⟨hbN, fun h => hB.htn ?_⟩
      have := (Subgroup.normalizer (L : Set (MulAut W))).mul_mem
        ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hbN) h
      simpa using this
    · refine Or.inl ⟨?_, hbN⟩
      rw [mem_normalizer_iff_conjAutSub, conjAutSub_mul, (hB.conj_swap hB.t_mem hB.htn).1,
        (hB.conj_swap hb hbN).2]
  exact relIndex_eq_two hB.t_mem hkey

theorem sylow_T0 : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
    (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) := by
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have hTM : T ≤ M := hB.T_le
  refine ⟨inf_le_inf_right _ hTM, hB.hD.hyp.sylow.2.1.to_le inf_le_left, ?_⟩
  have h2 : (T ⊓ N).relIndex T = 2 := by
    refine relIndex_eq_two hB.htT fun b hb => ?_
    by_cases hbN : b ∈ N
    · refine Or.inr ⟨hbN, fun h => hB.htn ?_⟩
      have := N.mul_mem (N.inv_mem hbN) h
      simpa using this
    · refine Or.inl ⟨?_, hbN⟩
      rw [hN, mem_normalizer_iff_conjAutSub, conjAutSub_mul, (hB.conj_swap hB.t_mem hB.htn).1,
        (hB.conj_swap (hTM hb) hbN).2]
  have h1 := hB.relIndex_normalizer
  have h3 := Subgroup.relIndex_mul_relIndex (T ⊓ N) (M ⊓ N) M (inf_le_inf_right _ hTM)
    inf_le_left
  have h4 := Subgroup.relIndex_mul_relIndex (T ⊓ N) T M inf_le_left hTM
  have hodd : ¬ 2 ∣ T.relIndex M := hB.hD.hyp.sylow.2.2
  have heq : (T ⊓ N).relIndex (M ⊓ N) = T.relIndex M := by
    rw [h1] at h3
    rw [h2] at h4
    omega
  show ¬ 2 ∣ (T ⊓ N).relIndex (M ⊓ N)
  rw [heq]
  exact hodd

end D321Base

end CFSG.Quasithin.SmithD321
