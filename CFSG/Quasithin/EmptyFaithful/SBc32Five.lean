module

public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.S153D52
public import CFSG.Quasithin.EmptyFaithful.Insp11A5
public import CFSG.Quasithin.EmptyFaithful.SBc32Ortho
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Generic

variable {G : Type} [Group G]

theorem mem_conjBy153_iff {t x : G} {X : Subgroup G} : x ∈ conjBy153 t X ↔ t⁻¹ * x * t ∈ X := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show t⁻¹ * (t * y * t⁻¹) * t ∈ X
    rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group]
  · intro hy
    exact ⟨t⁻¹ * x * t, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          have := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
          exact this
        rw [mul_inv_rev, h1] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem mem_or_mul_inv_mem_of_relIndex_two {S T : Subgroup G} (h : S.relIndex T = 2) {t' : G}
    (ht'T : t' ∈ T) (ht'S : t' ∉ S) {g : G} (hg : g ∈ T) : g ∈ S ∨ g * t'⁻¹ ∈ S := by
  by_cases hgS : g ∈ S
  · exact Or.inl hgS
  · right
    have hidx : (S.subgroupOf T).index = 2 := h
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hg⟩) (b := ⟨t', ht'T⟩⁻¹)).mpr
    have h1 : (⟨g, hg⟩ : ↥T) ∈ S.subgroupOf T ↔ (⟨t', ht'T⟩⁻¹ : ↥T) ∈ S.subgroupOf T := by
      constructor
      · intro h'
        exact absurd (Subgroup.mem_subgroupOf.mp h') hgS
      · intro h'
        exfalso
        apply ht'S
        have h'' := (S.subgroupOf T).inv_mem h'
        simpa using Subgroup.mem_subgroupOf.mp h''
    exact Subgroup.mem_subgroupOf.mp (this h1)

theorem mul_self_mem_of_relIndex_two {S T : Subgroup G} (h : S.relIndex T = 2) {g : G}
    (hg : g ∈ T) : g * g ∈ S := by
  have hidx : (S.subgroupOf T).index = 2 := h
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx ⟨g, hg⟩)

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem conj_V₂_le_V₁_of_not_mem (c : Ctx153 G T Mc M V₁ V₂ t) {t' : G} (ht'T : t' ∈ T)
    (ht'S : t' ∉ Sgp153 T V₁) : ∀ v ∈ V₂, t' * v * t'⁻¹ ∈ V₁ := by
  have hinv : t'⁻¹ ∈ T := T.inv_mem ht'T
  rcases conj_V₁_cases_of_mem_M c (c.hyp.T_le hinv) with h1 | h2
  · exfalso
    apply ht'S
    refine ⟨ht'T, ?_⟩
    have h3 : t'⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := A4.mem_normalizer_of_conj_mem h1
    simpa using (Subgroup.normalizer (V₁ : Set G)).inv_mem h3
  · intro v hv
    have hW : V₁.map (MulAut.conj t'⁻¹).toMonoidHom ≤ V₂ := by
      rintro _ ⟨u, hu, rfl⟩
      exact h2 u hu
    have hcard : Nat.card ↥(V₂) ≤ Nat.card ↥(V₁.map (MulAut.conj t'⁻¹).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj t'⁻¹).injective, c.decomp.card₁,
        c.decomp.card₂]
    have hWeq := Subgroup.eq_of_le_of_card_ge hW hcard
    have hv' : v ∈ V₁.map (MulAut.conj t'⁻¹).toMonoidHom := hWeq ▸ hv
    obtain ⟨u, hu, rfl⟩ := hv'
    have e : t' * (MulAut.conj t'⁻¹).toMonoidHom u * t'⁻¹ = u := by
      simp [mul_assoc]
    rw [e]
    exact hu

theorem isElemAbelian_UL (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : IsElemAbelian 2 (UL153 T I L) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hZ : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
    unfold quasithinOmegaOneCenter
    refine Subgroup.closure_mono fun z hz => ?_
    have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
    exact ⟨⟨S153D.VZ_le_Sgp153 hyp hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩
  obtain ⟨-, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo hZ
  have hLI : L ≤ I := S153H.L_le_I c
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp (hLI.trans hIU)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hel.2 x (hUUI hx)⟩
  have := congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hUUI x.2⟩ ⟨y, hUUI y.2⟩)
  simpa using this

theorem V₂_le_UL (h113 : StageLemma14113) (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) :
    V₂ ≤ UL153 T I L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := c25.facts.case_two.2
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hYI : Yp ≤ I := le_sup_left.trans c25.ctx.inH.1.1
  have h1 : V₂ ≤ UI153 T I := by
    have := hyp.hyp.V₂_le_conjClosure_Yplus h113 hyp.decomp
    rw [← hYp] at this
    exact this.trans (conjClosure_mono le_rfl hYI)
  have h2 : ⁅V₂, Yp⁆ = V₂ := by
    rw [hYp]
    exact hyp.hyp.commutator_V₂_Yplus h113 hyp.decomp
  calc V₂ = ⁅V₂, Yp⁆ := h2.symm
    _ ≤ ⁅UI153 T I, L⁆ := Subgroup.commutator_mono h1 hYL

omit [Finite G] in
theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

theorem input32FiveInter_holds (h113 : StageLemma14113) : Input32FiveInter := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1 h2 h3 h4 t' ht'T ht'S
  by_contra hD
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have D : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hidx : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS hh
  have hSI : Sgp153 T V₁ ≤ I := S153H.Sgp153_le_I c
  have hULN : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hULS : UL153 T I L ≤ Sgp153 T V₁ := S153H.UL_le_Sgp153 c
  have hSD : Sgp153 T V₁ ≤ Subgroup.normalizer
      ((UL153 T I L ⊓ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hULN (hSI hg), S153H.Sgp153_le_normalizer_ULt c ht'T hg⟩
  have ht'sq : t' * t' ∈ Sgp153 T V₁ := mul_self_mem_of_relIndex_two hidx ht'T
  have ht'D : t' ∈ Subgroup.normalizer
      ((UL153 T I L ⊓ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun d hd => ⟨?_, ?_⟩
    · have hd2 : t'⁻¹ * d * t' ∈ UL153 T I L := mem_conjBy153_iff.mp hd.2
      have e : t' * d * t'⁻¹ = (t' * t') * (t'⁻¹ * d * t') * (t' * t')⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hULN (hSI ht'sq)) _).mp hd2
    · have e : t'⁻¹ * (t' * d * t'⁻¹) * t' = d := by group
      exact mem_conjBy153_iff.mpr (by rw [e]; exact hd.1)
  have hTD : T ≤ Subgroup.normalizer
      ((UL153 T I L ⊓ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
    intro g hg
    rcases mem_or_mul_inv_mem_of_relIndex_two hidx ht'T ht'S hg with hgS | hgS
    · exact hSD hgS
    · have e : g = (g * t'⁻¹) * t' := by group
      rw [e]
      exact Subgroup.mul_mem _ (hSD hgS) ht'D
  have hT2 : IsPGroup 2 T := hh.qtfe.sylow.1
  have hD'T : UL153 T I L ⊓ conjBy153 t' (UL153 T I L) ≤ T :=
    inf_le_left.trans (hULS.trans inf_le_left)
  have hD'2 : IsPGroup 2 ↥(UL153 T I L ⊓ conjBy153 t' (UL153 T I L)) := hT2.to_le hD'T
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card ↥(UL153 T I L ⊓ conjBy153 t' (UL153 T I L)) := by
    obtain ⟨k, hk⟩ := hD'2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hD (Subgroup.card_eq_one.mp (by simpa using hk))
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hzD, hzo, hzC⟩ := exists_orderOf_eq_of_isPGroup_normalizer hT2 hTD h2dvd
  have hzT : z ∈ T := hD'T hzD
  have hz2 : z ^ 2 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hzZ : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hzT, hzC⟩, hz2⟩
  have hzV : z ∈ V₁ ⊔ V₂ := D.sup ▸ hh.Z_le_VZ hzZ
  have hVcomm : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x := fun x hx y hy =>
    comm_of_isElemAbelian hh.elemAbelian (D.le₁ hx) (D.le₂ hy)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hVcomm hzV
  have hfix : ∀ s ∈ Sgp153 T V₁, s * a * s⁻¹ = a ∧ s * b * s⁻¹ = b := by
    intro s hs
    have ha' : s * a * s⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hs.2 a).mp ha
    have hb' : s * b * s⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (Hyp153.Sgp153_le_normalizer_V₂ hh D hs) b).mp hb
    have hzs : s * z * s⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hzC s hs.1
      rw [this]
      group
    have e : (s * a * s⁻¹) * (s * b * s⁻¹) = a * b := by
      calc (s * a * s⁻¹) * (s * b * s⁻¹) = s * (a * b) * s⁻¹ := by group
        _ = s * z * s⁻¹ := by rw [hab]
        _ = z := hzs
        _ = a * b := hab.symm
    have e1 : a⁻¹ * (s * a * s⁻¹) = b * (s * b * s⁻¹)⁻¹ := by
      have : a⁻¹ * (s * a * s⁻¹) = a⁻¹ * ((s * a * s⁻¹) * (s * b * s⁻¹)) * (s * b * s⁻¹)⁻¹ := by group
      rw [this, e]
      group
    have hw1 : a⁻¹ * (s * a * s⁻¹) ∈ V₁ := V₁.mul_mem (V₁.inv_mem ha) ha'
    have hw2 : a⁻¹ * (s * a * s⁻¹) ∈ V₂ := by
      rw [e1]
      exact V₂.mul_mem hb (V₂.inv_mem hb')
    have hw : a⁻¹ * (s * a * s⁻¹) = 1 := by
      have : a⁻¹ * (s * a * s⁻¹) ∈ V₁ ⊓ V₂ := ⟨hw1, hw2⟩
      rw [D.inf, Subgroup.mem_bot] at this
      exact this
    have hsa : s * a * s⁻¹ = a := by
      have := congrArg (fun w => a * w) hw
      simpa using this
    refine ⟨hsa, ?_⟩
    rw [hsa] at e
    exact mul_left_cancel e
  have haZS : a ∈ ZS153 T M V₁ ⊓ V₁ := by
    refine ⟨⟨D.le₁ ha, ?_⟩, ha⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro s hs
    have := (hfix s hs).1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have haCL : a ∈ Subgroup.centralizer (L : Set G) := by
    have := h2.1 ▸ haZS
    exact (this : a ∈ ZS153 T M V₁ ⊓ Subgroup.centralizer (L : Set G)).2
  have hbUL : b ∈ UL153 T I L := V₂_le_UL h113 c hb
  have haUL : a ∈ UL153 T I L := by
    have hzUL : z ∈ UL153 T I L := hzD.1
    have : a = z * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact (UL153 T I L).mul_mem hzUL ((UL153 T I L).inv_mem hbUL)
  have haCS : a ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) := haZS.1.2
  have haCI : a ∈ Subgroup.centralizer (I : Set G) := by
    rw [c.I_eq]
    exact S153H.mem_centralizer_sup haCL haCS
  obtain ⟨q, hq, hnd, -, hcard, hautq⟩ := h1
  have hel := isElemAbelian_UL c
  have ha1 : a = 1 := by
    have hfixq : ∀ g ∈ orthogonalGroupOf q, g ⟨a, haUL⟩ = ⟨a, haUL⟩ := by
      intro g hg
      rw [← hautq] at hg
      obtain ⟨i, hiN, hiI, rfl⟩ := mem_autOn_iff_exists.mp hg
      apply Subtype.ext
      rw [conjAct_apply_coe''']
      have := Subgroup.mem_centralizer_iff.mp haCI i hiI
      rw [this]
      group
    have := eq_one_of_fixed_by_isometries hq hnd
      (fun x y => Subtype.ext (comm_of_isElemAbelian hel x.2 y.2))
      (fun v => Subtype.ext (by simpa [pow_two] using hel.2 v v.2))
      (by rw [hcard]; norm_num) hfixq
    exact congrArg Subtype.val this
  have hzb : z = b := by
    rw [← hab, ha1, one_mul]
  have hzV₂ : z ∈ V₂ := hzb ▸ hb
  have hswap := conj_V₂_le_V₁_of_not_mem (⟨hh, D⟩ : Ctx153 G T Mc M V₁ V₂ t) ht'T ht'S z hzV₂
  have hzt : t' * z * t'⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hzC t' ht'T
    rw [this]
    group
  rw [hzt] at hswap
  have hz1 : z ∈ V₁ ⊓ V₂ := ⟨hswap, hzV₂⟩
  rw [D.inf, Subgroup.mem_bot] at hz1
  rw [hz1, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

end Context

end SBc

end CFSG.Quasithin
