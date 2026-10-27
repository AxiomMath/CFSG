module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzRep2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.X7

variable {G : Type} [Group G] [Finite G]
variable {W : Subgroup G}

abbrev ChiefSubmodule (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) :=
  @Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) (inferInstance : Semiring (ZMod 2))
    (@Additive.addCommGroup (Ch3z.chiefMod ⊥ W) (l2ChiefSectionCommGroup hE)).toAddCommMonoid
    (l2ChiefSectionModule hE)

noncomputable def subZ (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) (Y : Subgroup G) :
    ChiefSubmodule (W := W) hE := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  exact {
    carrier := {x | ((chiefModBotMulEquiv W).symm x.toMul : G) ∈ Y}
    zero_mem' := by
      change ((chiefModBotMulEquiv W).symm (0 : Additive (Ch3z.chiefMod ⊥ W)).toMul : G) ∈ Y
      rw [show (0 : Additive (Ch3z.chiefMod ⊥ W)).toMul = 1 from rfl, map_one]
      exact Y.one_mem
    add_mem' := by
      intro x y hx hy
      change ((chiefModBotMulEquiv W).symm ((x + y).toMul) : G) ∈ Y
      rw [show (x + y).toMul = x.toMul * y.toMul from rfl, map_mul]
      simpa using Y.mul_mem hx hy
    smul_mem' := by
      intro c x hx
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · change ((chiefModBotMulEquiv W).symm ((0 : ZMod 2) • x).toMul : G) ∈ Y
        rw [zero_smul]
        simpa using Y.one_mem
      · change ((chiefModBotMulEquiv W).symm ((1 : ZMod 2) • x).toMul : G) ∈ Y
        rw [one_smul]
        simpa using hx }

theorem mem_subZ_iff {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y : Subgroup G} {w : ↥W} :
    Additive.ofMul (chiefModBotMulEquiv W w) ∈ subZ (W := W) hE Y ↔ (w : G) ∈ Y := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  change ((chiefModBotMulEquiv W).symm
    (Additive.ofMul (chiefModBotMulEquiv W w)).toMul : G) ∈ Y ↔ (w : G) ∈ Y
  rw [show (Additive.ofMul (chiefModBotMulEquiv W w)).toMul =
    chiefModBotMulEquiv W w from rfl, MulEquiv.symm_apply_apply]

theorem mem_subZ_iff' {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y : Subgroup G} {g : G}
    (hg : g ∈ W) :
    Additive.ofMul (chiefModBotMulEquiv W ⟨g, hg⟩) ∈ subZ (W := W) hE Y ↔ g ∈ Y :=
  mem_subZ_iff

theorem subZ_mono {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y Z : Subgroup G} (h : Y ≤ Z) :
    subZ (W := W) hE Y ≤ subZ (W := W) hE Z :=
  fun _ hx => h hx

theorem subZ_le_iff {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y Z : Subgroup G}
    (hYW : Y ≤ W) (hZW : Z ≤ W) :
    subZ (W := W) hE Y ≤ subZ (W := W) hE Z ↔ Y ≤ Z := by
  constructor
  · intro h g hg
    have hgW : g ∈ W := hYW hg
    exact (mem_subZ_iff' hgW).1 (h ((mem_subZ_iff' hgW).2 hg))
  · exact subZ_mono

theorem subZ_inj {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y Z : Subgroup G}
    (hYW : Y ≤ W) (hZW : Z ≤ W) :
    subZ (W := W) hE Y = subZ (W := W) hE Z ↔ Y = Z := by
  constructor
  · intro h
    exact le_antisymm ((subZ_le_iff hYW hZW).1 (le_of_eq h))
      ((subZ_le_iff hZW hYW).1 (le_of_eq h.symm))
  · rintro rfl; rfl

theorem subZ_bot {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} :
    subZ (W := W) hE (⊥ : Subgroup G) = ⊥ := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h1 : ((chiefModBotMulEquiv W).symm x.toMul : G) = 1 := Subgroup.mem_bot.mp hx
  have h2 : (chiefModBotMulEquiv W).symm x.toMul = 1 := Subtype.ext h1
  have hx' : Additive.ofMul (chiefModBotMulEquiv W ((chiefModBotMulEquiv W).symm x.toMul)) =
      x := by
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [← hx', h2, map_one]
  rfl

theorem subZ_top {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} :
    subZ (W := W) hE W = ⊤ := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  ext x
  constructor
  · intro _; exact Submodule.mem_top
  · intro _
    exact (chiefModBotMulEquiv W).symm x.toMul |>.2

noncomputable def subZPre (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (hW : IsElemAbelian 2 W) (U : ChiefSubmodule (W := W) hE) :
    Subgroup G := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  exact {
    carrier := {g | ∃ hg : g ∈ W, Additive.ofMul (chiefModBotMulEquiv W ⟨g, hg⟩) ∈ U}
    one_mem' := by
      refine ⟨W.one_mem, ?_⟩
      have h1 : (⟨(1 : G), W.one_mem⟩ : ↥W) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact U.zero_mem
    mul_mem' := by
      rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
      refine ⟨W.mul_mem haW hbW, ?_⟩
      have hsum : Additive.ofMul (chiefModBotMulEquiv W ⟨a * b, W.mul_mem haW hbW⟩) =
          Additive.ofMul (chiefModBotMulEquiv W ⟨a, haW⟩) +
            Additive.ofMul (chiefModBotMulEquiv W ⟨b, hbW⟩) := by
        apply Additive.ext
        show chiefModBotMulEquiv W ⟨a * b, W.mul_mem haW hbW⟩ =
          (Additive.ofMul (chiefModBotMulEquiv W ⟨a, haW⟩) +
            Additive.ofMul (chiefModBotMulEquiv W ⟨b, hbW⟩)).toMul
        rw [show (Additive.ofMul (chiefModBotMulEquiv W ⟨a, haW⟩) +
            Additive.ofMul (chiefModBotMulEquiv W ⟨b, hbW⟩)).toMul =
            chiefModBotMulEquiv W ⟨a, haW⟩ * chiefModBotMulEquiv W ⟨b, hbW⟩ from rfl,
          ← map_mul]
        congr 1
      rw [hsum]
      exact U.add_mem ha hb
    inv_mem' := by
      rintro a ⟨haW, ha⟩
      refine ⟨W.inv_mem haW, ?_⟩
      have hsq : a * a = 1 := by
        have h := hW.2 a haW
        rwa [pow_two] at h
      have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
      rw [show (⟨a⁻¹, W.inv_mem haW⟩ : ↥W) = ⟨a, haW⟩ from Subtype.ext hinv]
      exact ha }

theorem subZPre_subZ {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y : Subgroup G}
    (hW : IsElemAbelian 2 W) (hYW : Y ≤ W) :
    subZPre (W := W) hE hW (subZ (W := W) hE Y) = Y := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  ext g
  constructor
  · rintro ⟨hgW, hg⟩
    exact (mem_subZ_iff' hgW).1 hg
  · intro hg
    exact ⟨hYW hg, (mem_subZ_iff' (hYW hg)).2 hg⟩

theorem subZ_subZPre {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)}
    (hW : IsElemAbelian 2 W) (U : ChiefSubmodule (W := W) hE) :
    subZ (W := W) hE (subZPre (W := W) hE hW U) = U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  ext x
  set w : ↥W := (chiefModBotMulEquiv W).symm x.toMul with hw
  have hxw : Additive.ofMul (chiefModBotMulEquiv W w) = x := by
    apply Additive.ext
    rw [show (Additive.ofMul (chiefModBotMulEquiv W w)).toMul =
      chiefModBotMulEquiv W w from rfl, hw, MulEquiv.apply_symm_apply]
  have hiff : (Additive.ofMul (chiefModBotMulEquiv W w) ∈
        subZ (W := W) hE (subZPre (W := W) hE hW U)) ↔
      (Additive.ofMul (chiefModBotMulEquiv W w) ∈ U) := by
    rw [mem_subZ_iff]
    constructor
    · rintro ⟨hw', hmem⟩
      rwa [show (⟨(w : G), hw'⟩ : ↥W) = w from Subtype.ext rfl] at hmem
    · intro hx
      exact ⟨w.2, by rwa [show (⟨(w : G), w.2⟩ : ↥W) = w from Subtype.ext rfl]⟩
  simpa [hxw] using hiff

theorem subZPre_mono {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)}
    (hW : IsElemAbelian 2 W)
    {U V : ChiefSubmodule (W := W) hE} (h : U ≤ V) :
    subZPre (W := W) hE hW U ≤ subZPre (W := W) hE hW V := by
  rintro g ⟨hgW, hg⟩
  exact ⟨hgW, h hg⟩

variable {H : Subgroup G} {X : Type} [Group X]

theorem sectionRep_mem_subZ {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)}
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W)
    (e : oTwoQuot ↥H ≃* X) {Y : Subgroup G}
    (hY : H ≤ Subgroup.normalizer (Y : Set G)) (g : X)
    {x : Additive (Ch3z.chiefMod ⊥ W)} (hx : x ∈ subZ (W := W) hE Y) :
    sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e g x ∈
      subZ (W := W) hE Y := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  set w : ↥W := (chiefModBotMulEquiv W).symm x.toMul with hw
  have hxw : Additive.ofMul (chiefModBotMulEquiv W w) = x := by
    apply Additive.ext
    rw [show (Additive.ofMul (chiefModBotMulEquiv W w)).toMul =
      chiefModBotMulEquiv W w from rfl, hw, MulEquiv.apply_symm_apply]
  have hwY : (w : G) ∈ Y := by
    rw [← hxw] at hx
    exact (mem_subZ_iff).1 hx
  obtain ⟨q, rfl⟩ := e.surjective g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) q
  rw [← hxw]
  have hstep := sectionRep_apply (H := H) (X := X) (L := ⊥) (N := W)
    (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e h (chiefModBotMulEquiv W w)
  rw [show e (QuotientGroup.mk' (pCore 2 ↥H) h) = e (QuotientGroup.mk h) from rfl, hstep]
  have hact : sectionAction (D14.le_normalizer_bot H) hHW hE h
      (chiefModBotMulEquiv W w) =
      chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ := by
    have h := sectionAction_bot_apply (H := H) (W := W) (D14.le_normalizer_bot H) hHW hE h w
    exact h
  rw [hact, mem_subZ_iff]
  exact (Subgroup.mem_normalizer_iff.mp (hY h.2) (w : G)).mp hwY

theorem sectionRep_subZPre_mem {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)}
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W)
    (e : oTwoQuot ↥H ≃* X) (hW : IsElemAbelian 2 W)
    {U : ChiefSubmodule (W := W) hE}
    (hU : ∀ (g : X) (x : Additive (Ch3z.chiefMod ⊥ W)), x ∈ U →
      sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e g x ∈ U)
    {h : G} (hh : h ∈ H) {g : G} (hg : g ∈ subZPre (W := W) hE hW U) :
    h * g * h⁻¹ ∈ subZPre (W := W) hE hW U := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  obtain ⟨hgW, hgU⟩ := hg
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hHW hh) g).mp hgW, ?_⟩
  have hstep := sectionRep_apply (H := H) (X := X) (L := ⊥) (N := W)
    (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e ⟨h, hh⟩
    (chiefModBotMulEquiv W ⟨g, hgW⟩)
  have hact := sectionAction_bot_apply (H := H) (W := W) (D14.le_normalizer_bot H) hHW hE
    ⟨h, hh⟩ ⟨g, hgW⟩
  have hact' : sectionAction (D14.le_normalizer_bot H) hHW hE ⟨h, hh⟩
      (chiefModBotMulEquiv W ⟨g, hgW⟩) =
      chiefModBotMulEquiv W
        ⟨h * g * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hHW hh) (g : G)).mp hgW⟩ := by
    exact hact
  have himg : sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e
      (e (QuotientGroup.mk' (pCore 2 ↥H) ⟨h, hh⟩))
      (Additive.ofMul (chiefModBotMulEquiv W ⟨g, hgW⟩)) =
      Additive.ofMul (chiefModBotMulEquiv W
        ⟨h * g * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hHW hh) (g : G)).mp hgW⟩) := by
    rw [show e (QuotientGroup.mk' (pCore 2 ↥H) ⟨h, hh⟩) =
      e (QuotientGroup.mk ⟨h, hh⟩) from rfl, hstep, hact']
  have hUx := hU (e (QuotientGroup.mk' (pCore 2 ↥H) ⟨h, hh⟩))
    (Additive.ofMul (chiefModBotMulEquiv W ⟨g, hgW⟩)) hgU
  rw [himg] at hUx
  simpa using hUx

theorem sectionRep_sub_mem_subZ {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)}
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W)
    (e : oTwoQuot ↥H ≃* X) {Y : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ z ∈ W, h * z * h⁻¹ * z⁻¹ ∈ Y)
    (g : X) (m : Additive (Ch3z.chiefMod ⊥ W)) :
    sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e g m - m ∈
      subZ (W := W) hE Y := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  set w : ↥W := (chiefModBotMulEquiv W).symm m.toMul with hw
  have hmw : Additive.ofMul (chiefModBotMulEquiv W w) = m := by
    apply Additive.ext
    rw [show (Additive.ofMul (chiefModBotMulEquiv W w)).toMul =
      chiefModBotMulEquiv W w from rfl, hw, MulEquiv.apply_symm_apply]
  obtain ⟨q, rfl⟩ := e.surjective g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) q
  rw [← hmw]
  have hstep := sectionRep_apply (H := H) (X := X) (L := ⊥) (N := W)
    (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO e h (chiefModBotMulEquiv W w)
  rw [show e (QuotientGroup.mk' (pCore 2 ↥H) h) = e (QuotientGroup.mk h) from rfl, hstep]
  have hact : sectionAction (D14.le_normalizer_bot H) hHW hE h
      (chiefModBotMulEquiv W w) =
      chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ := by
    have h := sectionAction_bot_apply (H := H) (W := W) (D14.le_normalizer_bot H) hHW hE h w
    exact h
  rw [hact]
  have hmem : (↑((⟨(h : G) * (w : G) * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ : ↥W) * w⁻¹) : G) ∈ Y := by
    have hc := hcomm (h : G) h.2 (w : G) w.2
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hc
  have hdiff : Additive.ofMul (chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩) -
      Additive.ofMul (chiefModBotMulEquiv W w) =
      Additive.ofMul (chiefModBotMulEquiv W
        (⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ * w⁻¹)) := by
    rw [sub_eq_add_neg]
    apply Additive.ext
    change chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ *
        (chiefModBotMulEquiv W w)⁻¹ =
      chiefModBotMulEquiv W
        (⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ * w⁻¹)
    rw [map_mul, map_inv]
  rw [hdiff]
  exact (mem_subZ_iff).2 hmem

theorem natCard_subZ {hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)} {Y : Subgroup G}
    (hYW : Y ≤ W) : Nat.card (subZ (W := W) hE Y) = Nat.card ↥Y := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(chiefModBotMulEquiv W).symm x.1.toMul, x.2⟩
      invFun := fun y => ⟨Additive.ofMul (chiefModBotMulEquiv W ⟨y.1, hYW y.2⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (mem_subZ_iff).2 y.2
  · intro x
    apply Subtype.ext
    apply Additive.ext
    rw [show (Additive.ofMul (chiefModBotMulEquiv W
      ⟨((chiefModBotMulEquiv W).symm x.1.toMul : ↥W), hYW x.2⟩)).toMul =
      chiefModBotMulEquiv W ⟨((chiefModBotMulEquiv W).symm x.1.toMul : ↥W), hYW x.2⟩ from rfl]
    rw [show (⟨((chiefModBotMulEquiv W).symm x.1.toMul : ↥W), hYW x.2⟩ : ↥W) =
      (chiefModBotMulEquiv W).symm x.1.toMul from Subtype.ext rfl]
    rw [MulEquiv.apply_symm_apply]
  · intro y
    apply Subtype.ext
    show ((chiefModBotMulEquiv W).symm
      (Additive.ofMul (chiefModBotMulEquiv W ⟨y.1, hYW y.2⟩)).toMul : ↥W).1 = (y.1 : G)
    rw [show ((chiefModBotMulEquiv W).symm
      (Additive.ofMul (chiefModBotMulEquiv W ⟨y.1, hYW y.2⟩)).toMul : ↥W) =
        ⟨y.1, hYW y.2⟩ from MulEquiv.symm_apply_apply _ _]

theorem map_fixedSub_toRepresentation {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {X : Type} [Group X]
    (ρ : Representation (ZMod 2) X W) (Nsub : Subrepresentation ρ) (A : Subgroup X) :
    (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation A).map Nsub.toSubmodule.subtype =
      CFSG.RankThree.FFModules.fixSub ρ A ⊓ Nsub.toSubmodule := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, u.2⟩
    rw [CFSG.RankThree.FFModules.mem_fixSub]
    intro a ha
    exact (Subrepresentation.toRepresentation_apply_coe).mp
      ((CFSG.RankThree.FFModules.mem_fixSub.mp hu) a ha)
  · rintro ⟨hy, hyN⟩
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    have hy' : ∀ a ∈ A, ρ a y = y := CFSG.RankThree.FFModules.mem_fixSub.mp hy
    change ∀ a ∈ A, Nsub.toRepresentation a ⟨y, hyN⟩ = ⟨y, hyN⟩
    intro a ha
    apply Subtype.ext
    exact hy' a ha

theorem natCard_fixedSub_toRepresentation {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] {X : Type} [Group X]
    (ρ : Representation (ZMod 2) X W) (Nsub : Subrepresentation ρ) (A : Subgroup X) :
    Nat.card (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation A) =
      Nat.card ↥((CFSG.RankThree.FFModules.fixSub ρ A) ⊓
        (Nsub.toSubmodule : Submodule (ZMod 2) W)) := by
  have h := map_fixedSub_toRepresentation (W := W) ρ Nsub A
  rw [← h]
  exact Nat.card_congr (Submodule.equivMapOfInjective (Nsub.toSubmodule).subtype
    (Nsub.toSubmodule).subtype_injective
    (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation A)).toEquiv

end CFSG.Quasithin.Stroth

end
