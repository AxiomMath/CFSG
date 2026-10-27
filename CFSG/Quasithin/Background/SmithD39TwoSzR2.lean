module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Cent
public import CFSG.Quasithin.Background.A1cModuleSub
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin.SmithD391 CFSG.Quasithin.Z391
open scoped Pointwise commutatorElement

section Abstract

variable {A B : Type*} [Group A] [Group B] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction A Q] [MulDistribMulAction B Q]

private theorem le_of_forall_isIrr_le {ι : Type*} {S : ι → Subgroup Q}
    (hS : ∀ i, XMod.IsIrr A (S i))
    {X F : Subgroup Q} (hX : XMod.IsInv A X) (hXS : X ≤ ⨆ i, S i) (hF : XMod.IsInv A F)
    (h : ∀ J ≤ X, XMod.IsIrr A J → J ≤ F) : X ≤ F := by
  classical
  have hinv : ∀ i, XMod.IsInv A (S i) := fun i => (hS i).1
  set m : Submodule ↥(XMod.opRing A Q) (Additive Q) := ⨆ i, XMod.toSubmod (hinv i) with hm
  have : IsSemisimpleModule ↥(XMod.opRing A Q) ↥m := by
    have h1 := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
      (s := Set.univ) (p := fun i => XMod.toSubmod (hinv i)) (fun i _ => by
        have := (XMod.isIrr_iff (hinv i)).1 (hS i)
        infer_instance)
    have h2 : (⨆ i ∈ Set.univ, XMod.toSubmod (hinv i)) = m := by
      rw [hm]
      exact iSup_congr fun i => iSup_pos (Set.mem_univ i)
    rw [h2] at h1
    exact h1
  have hXm : XMod.toSubmod hX ≤ m := by
    rw [hm, ← XMod.toSubmod_iSup hinv]
    exact XMod.toSubmod_le_iff.2 hXS
  set N := (XMod.toSubmod hX).comap m.subtype with hN
  have key : N ≤ (XMod.toSubmod hF).comap m.subtype := by
    rw [← IsSemisimpleModule.sSup_simples_le N]
    refine sSup_le ?_
    rintro n ⟨hns, hnN⟩
    set s := n.map m.subtype with hs
    have hss : IsSimpleModule ↥(XMod.opRing A Q) ↥s :=
      IsSimpleModule.congr (M := ↥s) (N := ↥n)
        (Submodule.equivMapOfInjective m.subtype m.injective_subtype n).symm
    have hJinv := XMod.isInv_ofSubmod s
    have hJs : XMod.toSubmod hJinv = s := Submodule.ext fun _ => Iff.rfl
    have hJirr : XMod.IsIrr A (XMod.ofSubmod s) := (XMod.isIrr_iff hJinv).2 (by rw [hJs]; exact hss)
    have hJX : XMod.ofSubmod s ≤ X := by
      intro q hq
      have hq' : Additive.ofMul q ∈ s := hq
      obtain ⟨y, hy, hyq⟩ := Submodule.mem_map.1 hq'
      have h1 : y ∈ N := hnN hy
      rw [hN, Submodule.mem_comap] at h1
      have h2 : Additive.ofMul q ∈ XMod.toSubmod hX := by rw [← hyq]; exact h1
      exact h2
    have hJF := h _ hJX hJirr
    intro y hy
    rw [Submodule.mem_comap]
    have h3 : m.subtype y ∈ s := Submodule.mem_map_of_mem hy
    exact hJF h3
  intro x hx
  have hxm : Additive.ofMul x ∈ m := hXm hx
  have h4 : (⟨Additive.ofMul x, hxm⟩ : ↥m) ∈ N := by
    rw [hN, Submodule.mem_comap]
    exact hx
  exact key h4

private theorem isIrrSec_bot_subAction {J : Subgroup Q} (hJ : XMod.IsIrr A J) :
    @XMod.IsIrrSec A _ ↥J _ (XMod.subAction hJ.1) ⊥ ⊤ := by
  let := XMod.subAction hJ.1
  refine ⟨?_, fun K hK _ _ => ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h
    apply hJ.2.1.ne'
    rw [eq_bot_iff]
    intro q hq
    have h1 : (⟨q, hq⟩ : ↥J) ∈ (⊤ : Subgroup ↥J) := trivial
    rw [h] at h1
    have h2 : (⟨q, hq⟩ : ↥J) = 1 := Subgroup.mem_bot.1 h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  · have hKinv : XMod.IsInv A (K.map J.subtype) := by
      rintro a _ ⟨k, hk, rfl⟩
      exact ⟨a • k, hK a k hk, rfl⟩
    rcases hJ.2.2 _ hKinv bot_le (Subgroup.map_subtype_le K) with h1 | h1
    · left
      exact Subgroup.map_injective J.subtype_injective (h1.trans (Subgroup.map_bot _).symm)
    · right
      refine Subgroup.map_injective J.subtype_injective (h1.trans ?_)
      rw [Subgroup.map_top, Subgroup.range_subtype]

private theorem fix_of_isIrr_of_perfect [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hAB : ∀ (a : A) (b : B) (q : Q), a • b • q = b • a • q) (hB : commutator B = ⊤)
    {J : Subgroup Q} (hJ : XMod.IsIrr A J) (hBJ : XMod.IsInv B J) :
    ∀ b : B, ∀ j ∈ J, b • j = j := by
  classical
  let iA : MulDistribMulAction A ↥J := XMod.subAction hJ.1
  let iB : MulDistribMulAction B ↥J := XMod.subAction hBJ
  have hsimple := isIrrSec_bot_subAction hJ
  have hP : ∀ p : ↥J, p ^ 2 = 1 := fun p => Subtype.ext (by simp [hQ])
  obtain ⟨-, hfield, -⟩ := XMod.eqvEnd_isField_charTwo hP hsimple
  have hcomm : ∀ φ ψ : ↥(XMod.eqvAut A ↥J), φ * ψ = ψ * φ := by
    intro φ ψ
    apply XMod.toEqvEnd_injective (A := A) (P := ↥J)
    rw [map_mul, map_mul]
    exact hfield.mul_comm _ _
  let f : B →* ↥(XMod.eqvAut A ↥J) :=
    (MulDistribMulAction.toMulAut B ↥J).codRestrict (XMod.eqvAut A ↥J) fun b a p =>
      Subtype.ext (hAB a b (p : Q)).symm
  have hker : commutator B ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  intro b j hj
  have hb : f b = 1 := by
    have : b ∈ f.ker := hker (by rw [hB]; trivial)
    exact this
  have h1 := congrArg (fun φ : ↥(XMod.eqvAut A ↥J) => (((φ : MulAut ↥J) ⟨j, hj⟩ : ↥J) : Q)) hb
  exact h1

private theorem iso_smul_of_commute (hAB : ∀ (a : A) (b : B) (q : Q), a • b • q = b • a • q) (b : B)
    {J : Subgroup Q} (hJ : XMod.IsInv A J) : XMod.Iso A (b • J) J := by
  refine XMod.Iso.symm hJ ⟨XMod.smulEquiv b J, fun a v v' hvv' => ?_⟩
  show a • b • (v : Q) = b • (v' : Q)
  rw [hAB, hvv']

private theorem normalizes_of_commute (hAB : ∀ (a : A) (b : B) (q : Q), a • b • q = b • a • q) :
    XMod.Normalizes A B Q :=
  fun b a => ⟨a, fun q => (hAB a b q).symm⟩

private theorem fix_of_isHomComp [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hAB : ∀ (a : A) (b : B) (q : Q), a • b • q = b • a • q) (hB : commutator B = ⊤)
    {ι : Type*} {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr A (S i))
    (hHC : ∀ i, XMod.IsHomComp A (⨆ i, S i) (S i)) {X : Subgroup Q}
    (hXA : XMod.IsInv A X) (hXB : XMod.IsInv B X) (hXS : X ≤ ⨆ i, S i) :
    ∀ b : B, ∀ x ∈ X, b • x = x := by
  have hN := normalizes_of_commute hAB
  set F : Subgroup Q := X ⊓ XMod.fixed B ⊤ with hF
  have hFinv : XMod.IsInv A F := by
    intro a q hq
    refine ⟨hXA a q hq.1, trivial, fun b => ?_⟩
    rw [← hAB, hq.2.2 b]
  have hle : X ≤ F := by
    refine le_of_forall_isIrr_le hS hXA hXS hFinv fun J hJX hJ => ?_
    obtain ⟨i, hi⟩ := exists_iso_of_le_iSup hS hJ (hJX.trans hXS)
    have heq : ∀ J' : Subgroup Q, J' ≤ X → XMod.IsIrr A J' → XMod.Iso A J' (S i) → J' = S i := by
      intro J' hJ'X hJ' hJ'i
      have h1 : J' ≤ S i := (hHC i).2.2 J' (hJ'X.trans hXS) hJ' hJ'i
      rcases (hS i).2.2 J' hJ'.1 bot_le h1 with h2 | h2
      · exact absurd h2 hJ'.2.1.ne'
      · exact h2
    have hJi := heq J hJX hJ hi
    have hBJ : XMod.IsInv B J := by
      intro b j hj
      have hbJ : b • J ≤ X := by
        intro q hq
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
        have := hXB b _ (hJX hq)
        rwa [smul_inv_smul] at this
      have h3 := heq (b • J) hbJ (isIrr_smul hN b hJ)
        ((iso_smul_of_commute hAB b hJ.1).trans hi)
      rw [← hJi] at h3
      rw [← h3]
      exact Subgroup.smul_mem_pointwise_smul j b J hj
    intro j hj
    exact ⟨hJX hj, trivial, fun b => fix_of_isIrr_of_perfect hQ hAB hB hJ hBJ b j hj⟩
  intro b x hx
  exact (hle hx).2.2 b

end Abstract


section Groups

variable {G : Type*} [Group G]

private theorem commutator_eq_top_of_perfect {N : Subgroup G} (h : ⁅N, N⁆ = N) :
    commutator ↥N = ⊤ := by
  apply Subgroup.map_injective N.subtype_injective
  rw [map_commutator_eq, Subgroup.range_subtype, h, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private theorem commutator_eq_self_of_isQuasisimple {L : Subgroup G} (hL : CFSG.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  have h1 := hL.1
  rw [Group.isPerfect_def, _root_.commutator_def] at h1
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

private theorem commutatorElement_mul_mul {a b z w : G} (hza : Commute z a) (hzb : Commute z b)
    (hzw : Commute z w) (hwa : Commute w a) (hwb : Commute w b) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have h1 : Commute z (a * w * b * a⁻¹) :=
    ((hza.mul_right hzw).mul_right hzb).mul_right hza.inv_right
  have h2 : Commute w (b * a⁻¹ * b⁻¹) := (hwb.mul_right hwa.inv_right).mul_right hwb.inv_right
  calc ⁅z * a, w * b⁆ = (z * (a * w * b * a⁻¹) * z⁻¹) * b⁻¹ * w⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * (w * (b * a⁻¹ * b⁻¹) * w⁻¹) := by rw [h1.mul_inv_cancel]; group
    _ = ⁅a, b⁆ := by rw [h2.mul_inv_cancel, commutatorElement_def]; group

private theorem commute_of_commutatorElement_central {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    {m : G} (hmn : ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hmZ : ∀ l ∈ L, ∀ x ∈ L, Commute ⁅m, l⁆ x) : ∀ l ∈ L, m * l = l * m := by
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({m} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : ∀ c ∈ L, ⁅m, c⁆ ∈ L := fun c hc => by
      have := L.mul_mem (hmn c hc) (L.inv_mem hc)
      simpa [commutatorElement_def] using this
    have e₁ : ∀ c, m * c * m⁻¹ = ⁅m, c⁆ * c := fun c => by rw [commutatorElement_def]; group
    have hc : m * ⁅a, b⁆ * m⁻¹ = ⁅a, b⁆ := by
      have e : m * ⁅a, b⁆ * m⁻¹ = ⁅m * a * m⁻¹, m * b * m⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, e₁, e₁]
      exact commutatorElement_mul_mul (hmZ a ha a ha) (hmZ a ha b hb) (hmZ a ha _ (hz b hb))
        (hmZ b hb a ha) (hmZ b hb b hb)
    have := mul_inv_eq_iff_eq_mul.1 hc
    exact this.symm
  rw [hperf] at hle
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm

private theorem le_of_conj_mem {L H : Subgroup G} (hLq : CFSG.IsQuasisimple ↥L)
    (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h * l⁻¹ ∈ H) {a : G} (haH : a ∈ H)
    (haL : a ∉ Subgroup.centralizer (L : Set G))
    (hdich : L.map (MulAut.conj a).toMonoidHom = L ∨
      ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥) : L ≤ H := by
  have hLperf := commutator_eq_self_of_isQuasisimple hLq
  rcases hdich with hLa | hcomm
  · have hconj : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl => by
      rw [← hLa]
      exact ⟨l, hl, rfl⟩
    have hKn : (H.subgroupOf L).Normal := by
      refine ⟨fun k hk g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      simpa using hLH g g.2 k hk
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hLq (H.subgroupOf L)
      with hK | hK
    · exfalso
      apply haL
      rw [Subgroup.mem_centralizer_iff]
      have hmZ : ∀ l ∈ L, ∀ x ∈ L, Commute ⁅a, l⁆ x := by
        intro l hl x hx
        have hmem : ⁅a, l⁆ ∈ L := by
          have := L.mul_mem (hconj l hl) (L.inv_mem hl)
          simpa [commutatorElement_def] using this
        have hmemH : ⁅a, l⁆ ∈ H := by
          have := H.mul_mem haH (hLH l hl _ (H.inv_mem haH))
          simpa [commutatorElement_def, mul_assoc] using this
        have hc := Subgroup.mem_center_iff.1
          (hK (show (⟨_, hmem⟩ : ↥L) ∈ H.subgroupOf L from hmemH))
          ⟨x, hx⟩
        exact (congrArg Subtype.val hc).symm
      intro l hl
      exact (commute_of_commutatorElement_central hLperf hconj hmZ l hl).symm
    · intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := by rw [hK]; trivial
      exact this
  · have hcommLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a⁻¹) = (a * y * a⁻¹) * x := by
      intro x hx y hy
      have hmem : ⁅x, a * y * a⁻¹⁆ ∈ ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator hx ⟨y, hy, rfl⟩
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    rw [← hLperf, Subgroup.commutator_le]
    intro k hk k' hk'
    have hc : k * a * k⁻¹ * a⁻¹ ∈ H := H.mul_mem (hLH k hk a haH) (H.inv_mem haH)
    have h1 : ⁅k * a * k⁻¹ * a⁻¹, k'⁆ ∈ H := by
      have := H.mul_mem hc (hLH k' hk' _ (H.inv_mem hc))
      simpa [commutatorElement_def, mul_assoc] using this
    have hm := hcommLa k' hk' k⁻¹ (L.inv_mem hk)
    have e : ⁅k * a * k⁻¹ * a⁻¹, k'⁆ = ⁅k, k'⁆ := by
      calc ⁅k * a * k⁻¹ * a⁻¹, k'⁆
          = k * ((a * k⁻¹ * a⁻¹) * k') * (a * k⁻¹ * a⁻¹)⁻¹ * k⁻¹ * k'⁻¹ := by
            rw [commutatorElement_def]; group
        _ = k * (k' * (a * k⁻¹ * a⁻¹)) * (a * k⁻¹ * a⁻¹)⁻¹ * k⁻¹ * k'⁻¹ := by rw [hm]
        _ = ⁅k, k'⁆ := by rw [commutatorElement_def]; group
    rw [← e]
    exact h1

end Groups


section Ambient

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

private theorem iso_of_iso_map_of_injOn {A : Type*} [Group A] {Q₁ Q₂ : Type*} [CommGroup Q₁]
    [CommGroup Q₂] [MulDistribMulAction A Q₁] [MulDistribMulAction A Q₂] (θ : Q₁ →* Q₂)
    (hθ : ∀ (a : A) (x : Q₁), θ (a • x) = a • θ x) {S : Subgroup Q₁} (hS : XMod.IsInv A S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y) {L₁ L₂ : Subgroup Q₁} (h₁ : L₁ ≤ S)
    (h₂ : L₂ ≤ S) (h : XMod.Iso A (L₁.map θ) (L₂.map θ)) : XMod.Iso A L₁ L₂ := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θ hinj h₁
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θ hinj h₂
  refine ⟨e₁.trans (φ.trans e₂.symm), fun a l l' hll' => ?_⟩
  have hx : ∀ y : ↥(L₂.map θ), θ ((e₂.symm y : ↥L₂) : Q₁) = (y : Q₂) := fun y => by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have h1 : a • ((e₁ l : ↥(L₁.map θ)) : Q₂) = ((e₁ l' : ↥(L₁.map θ)) : Q₂) := by
    rw [he₁, he₁, ← hθ, hll']
  have h2 := hφ a _ _ h1
  apply hinj _ (hS a _ (h₂ (e₂.symm (φ (e₁ l))).2)) _ (h₂ (e₂.symm (φ (e₁ l'))).2)
  show θ (a • ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q₁)) = θ ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q₁)
  rw [hθ, hx, hx, h2]

private theorem mem_irrPlusOn_of_le {X T : Subgroup G} {W W' : Subgroup V}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hWT : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W)
    (hWX : IsModInv X W) (hW'T : ∀ t ∈ T, ∀ w ∈ W', t • w ∈ W') (hWW' : W ≤ W')
    {I : Subgroup V} (hI : I ∈ IrrPlusOn X W T) : I ∈ IrrPlusOn X W' T := by
  have hI' : I ∈ IrrPlus X W' := ⟨hI.1.1.trans hWW', hI.1.2⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX hW'T hI').1 ?_
  rintro t ⟨ht, hiso⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX hWT hI.1).2 hI t ⟨ht, ?_⟩
  have hle : modFix X W ≤ modFix X W' := XMod.fixed_mono hWW'
  let θ : V ⧸ modFix X W →* V ⧸ modFix X W' := QuotientGroup.map _ _ (MonoidHom.id V) hle
  have hθ : ∀ (a : ↥X) (x : V ⧸ modFix X W), θ (a • x) = a • θ x := by
    intro a x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hmap : ∀ J : Subgroup V, tilde X W' J = (tilde X W J).map θ := by
    intro J
    unfold tilde
    rw [Subgroup.map_map]
    rfl
  have hinj : ∀ x ∈ tilde X W W, ∀ y ∈ tilde X W W, θ x = θ y → x = y := by
    intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hx
    obtain ⟨u, hu, rfl⟩ := mem_tilde_iff.1 hy
    have h1 : (QuotientGroup.mk v : V ⧸ modFix X W') = QuotientGroup.mk u := hxy
    rw [QuotientGroup.eq] at h1 ⊢
    exact ⟨W.mul_mem (W.inv_mem hv) hu, h1.2⟩
  have hItW : t • I ≤ W := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x t I).1 hx
    exact hWT t ht i (hI.1.1 hi)
  rw [hmap, hmap] at hiso
  exact iso_of_iso_map_of_injOn θ hθ (isInv_tilde hWX) hinj (tilde_mono hItW)
    (tilde_mono hI.1.1) hiso

end Ambient

private theorem isHomComp_smul {A T : Type*} [Group A] [Group T] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction A Q] [MulDistribMulAction T Q] (h : XMod.Normalizes A T Q)
    {L : Subgroup Q} (hL : XMod.IsHomComp A (⨆ s : T, s • L) L) (t : T) :
    XMod.IsHomComp A (⨆ s : T, s • L) (t • L) := by
  have hM : ∀ g : T, ∀ x ∈ ⨆ s : T, s • L, g • x ∈ ⨆ s : T, s • L := by
    intro g x hx
    refine Subgroup.iSup_induction (fun s : T => s • L)
      (C := fun y => g • y ∈ ⨆ s : T, s • L) hx (fun s y hy => ?_) ?_ ?_
    · have h1 := Subgroup.smul_mem_pointwise_smul y g _ hy
      rw [smul_smul] at h1
      exact Subgroup.mem_iSup_of_mem (g * s) h1
    · rw [smul_one]
      exact one_mem _
    · intro y z hy hz
      rw [smul_mul']
      exact mul_mem hy hz
  refine ⟨isIrr_smul h t hL.1, le_iSup (fun s : T => s • L) t, fun L' hL'M hL' hiso => ?_⟩
  have h1 : t⁻¹ • L' ≤ ⨆ s : T, s • L := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv] at hx
    have h2 := hM t⁻¹ _ (hL'M hx)
    rwa [inv_smul_smul] at h2
  have h2 : XMod.Iso A (t⁻¹ • L') L := by
    have h3 := XMod.iso_smul h t⁻¹ hiso
    rwa [inv_smul_smul] at h3
  have h3 := hL.2.2 _ h1 (isIrr_smul h t⁻¹ hL') h2
  have h4 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t)).2 h3
  rwa [smul_inv_smul] at h4



section Faithful

variable {V : Type} [CommGroup V]

private theorem commV_le_commSub_commV {K : Subgroup (MulAut V)} (hK : ⁅K, K⁆ = K) :
    commV K ≤ commSub (commV K) K := by
  set C := commSub (commV K) K with hC
  have hKc := commutator_eq_top_of_perfect hK
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨k, hk, w, rfl⟩
  let f : ↥K →* V ⧸ C :=
    { toFun := fun g => QuotientGroup.mk ((g : MulAut V) w * w⁻¹)
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hx : (g' : MulAut V) w * w⁻¹ ∈ commV K :=
          Subgroup.subset_closure ⟨g', g'.2, w, rfl⟩
        have hmem : (g : MulAut V) ((g' : MulAut V) w * w⁻¹) * ((g' : MulAut V) w * w⁻¹)⁻¹ ∈ C :=
          Subgroup.subset_closure ⟨g, g.2, _, hx, rfl⟩
        convert C.inv_mem hmem using 1
        simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
        simp only [mul_inv_rev, inv_inv]
        simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left] }
  have h1 : (⟨k, hk⟩ : ↥K) ∈ f.ker :=
    Abelianization.commutator_subset_ker f (by rw [hKc]; trivial)
  rw [MonoidHom.mem_ker] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

private theorem commV_mem_of_normalizes {X : Subgroup (MulAut V)} {h : MulAut V}
    (hX : ∀ g ∈ X, h * g * h⁻¹ ∈ X) : ∀ c ∈ commV X, h c ∈ commV X := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨g, hg, v, rfl⟩ := hc
    have e : h (g v * v⁻¹) = (h * g * h⁻¹) (h v) * (h v)⁻¹ := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.subset_closure ⟨_, hX g hg, h v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem eq_bot_of_fix_comm {N K : Subgroup (MulAut V)} (hNcomm : commV N = ⊤)
    (hKperf : ⁅K, K⁆ = K) (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k) {R : Subgroup V}
    (hKR : commV K ≤ R) (hR : ∀ n ∈ N, ∀ r ∈ R, n r * r⁻¹ ∈ fixV K) : K = ⊥ := by
  have hfix : ∀ n ∈ N, ∀ c ∈ commSub (commV K) K, n c = c := by
    intro n hn c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨k, hk, x, hx, rfl⟩ := hc
      have hd : n x * x⁻¹ ∈ fixV K := hR n hn x (hKR hx)
      have hnk : n (k x) = k (n x) := by
        have h1 := congrArg (fun φ : MulAut V => φ x) (hKN k hk n hn)
        simp only [MulAut.mul_apply] at h1
        exact h1.symm
      have hkd : k (n x * x⁻¹) = n x * x⁻¹ := (mem_fixV.1 hd) k hk
      set d := n x * x⁻¹ with hd'
      have hnx : n x = d * x := by rw [hd']; group
      rw [map_mul, map_inv, hnk, hnx, map_mul, hkd, mul_inv_rev]
      simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel, one_mul]
    | one => exact map_one n
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  refine eq_one_of_fix_quot hNcomm (fun l hl => hKN k hk l hl) fun w => ?_
  have hc : k w * w⁻¹ ∈ commSub (commV K) K :=
    commV_le_commSub_commV hKperf (Subgroup.subset_closure ⟨k, hk, w, rfl⟩)
  exact fun n hn => hfix n hn _ hc

end Faithful


section Module

variable {W : Type} [CommGroup W]

private theorem le_normalizer_of_commute {Y N : Subgroup (MulAut W)}
    (hYN : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y) : N ≤ Subgroup.normalizer (Y : Set (MulAut W)) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hYN y hy n hn, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := hYN _ hy n hn
    have h2 : y = n * y * n⁻¹ := by
      have h3 : n * y = n * (n * y * n⁻¹) := by
        calc n * y = n * y * n⁻¹ * n := by group
          _ = n * (n * y * n⁻¹) := h1
      exact mul_left_cancel h3
    rw [h2]
    exact hy

private theorem orbSup_mem_of_normalizes {Y T : Subgroup (MulAut W)} {I : Subgroup W}
    (hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W))) (hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I) :
    ∀ y ∈ Y, ∀ w ∈ orbSup T I, y w ∈ orbSup T I := by
  intro y hy w hw
  have hsub : orbSup T I ≤ (orbSup T I).comap y.toMonoidHom := by
    refine orbSup_le fun t ht => ?_
    rintro _ ⟨i, hi, rfl⟩
    show y (t i) ∈ orbSup T I
    have hyt : t⁻¹ * y * t ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) y).mp hy
      simpa using this
    have e : y (t i) = t ((t⁻¹ * y * t) i) := by simp [MulAut.mul_apply]
    rw [e]
    exact map_le_orbSup ht ⟨_, hIY _ hyt i hi, rfl⟩
  exact hsub hw

variable [Finite W]

private theorem fixV_of_mem_irrPlusOn (hW : ∀ w : W, w ^ 2 = 1) {Y T N : Subgroup (MulAut W)}
    {I R : Subgroup W} (hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)))
    (hYN : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y) (hNperf : ⁅N, N⁆ = N)
    (hI : I ∈ IrrPlusOn Y ⊤ T) (hRU : R ≤ ⨆ y ∈ T, y • I)
    (hRY : ∀ y ∈ Y, ∀ r ∈ R, y r ∈ R) (hRN : ∀ n ∈ N, ∀ r ∈ R, n r ∈ R) :
    ∀ n ∈ N, ∀ r ∈ R, n r * r⁻¹ ∈ fixV Y := by
  have hNY := le_normalizer_of_commute hYN
  have hWT : ∀ t ∈ T, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) := fun _ _ _ _ => trivial
  let iT := quotAct (X := Y) (T := T) hTY hWT
  let iN := quotAct (X := Y) (T := N) (W := (⊤ : Subgroup W)) hNY (fun _ _ _ _ => trivial)
  have hQ : ∀ q : W ⧸ modFix Y (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hW v, QuotientGroup.mk_one]
  have hAB : ∀ (a : ↥Y) (b : ↥N) (q : W ⧸ modFix Y (⊤ : Subgroup W)),
      a • b • q = b • a • q := by
    intro a b q
    induction q using QuotientGroup.induction_on with
    | H v =>
      change (QuotientGroup.mk ((a : MulAut W) ((b : MulAut W) v)) :
          W ⧸ modFix Y (⊤ : Subgroup W)) = QuotientGroup.mk ((b : MulAut W) ((a : MulAut W) v))
      rw [← MulAut.mul_apply, hYN a a.2 b b.2, MulAut.mul_apply]
  have hnorm := normalizes_quot hTY hWT
  obtain ⟨hirr, -⟩ := isIrr_tilde hI.1
  have hHC := ((mem_irrPlusOn_iff hTY hWT).1 hI).2
  have hXA : XMod.IsInv ↥Y (tilde Y ⊤ R) := isInv_tilde fun a r hr => hRY a a.2 r hr
  have hXB : XMod.IsInv ↥N (tilde Y ⊤ R) := by
    intro b q hq
    obtain ⟨r, hr, rfl⟩ := mem_tilde_iff.1 hq
    exact mem_tilde_iff.2 ⟨(b : MulAut W) r, hRN b b.2 r hr, rfl⟩
  have hXS : tilde Y ⊤ R ≤ ⨆ s : ↥T, s • tilde Y ⊤ I := by
    rw [← tilde_biSup_smul hTY hWT]
    exact tilde_mono hRU
  have key := fix_of_isHomComp hQ hAB (commutator_eq_top_of_perfect hNperf)
    (fun t => isIrr_smul hnorm t hirr) (isHomComp_smul hnorm hHC) hXA hXB hXS
  intro n hn r hr
  have h1 := key ⟨n, hn⟩ _ (mem_tilde_iff.2 ⟨r, hr, rfl⟩)
  have h2 : (QuotientGroup.mk (n r) : W ⧸ modFix Y (⊤ : Subgroup W)) = QuotientGroup.mk r := h1
  rw [QuotientGroup.eq, modFix_top_eq] at h2
  have h3 := (fixV Y).inv_mem h2
  rwa [mul_inv_rev, inv_inv, mul_comm] at h3

theorem sz_false_of_sup_fixV_eq_top (hW : ∀ w : W, w ^ 2 = 1) {N T K A : Subgroup (MulAut W)}
    {I : Subgroup W} (hNperf : ⁅N, N⁆ = N) (hNcomm : commV N = ⊤)
    (hTN : T ≤ Subgroup.normalizer (N : Set (MulAut W))) (hKq : CFSG.IsQuasisimple ↥K)
    (hKne : K ≠ ⊥) (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k)
    (hI : I ∈ IrrPlusOn (conjClosure K T) (orbSup T I) T) (hAT : A ≤ T)
    (hAU : orbSup T I ⊔ fixV A = ⊤) {a : MulAut W} (haA : a ∈ A)
    (haK : a ∉ Subgroup.centralizer (K : Set (MulAut W)))
    (hdich : K.map (MulAut.conj a).toMonoidHom = K ∨
      ⁅K, K.map (MulAut.conj a).toMonoidHom⁆ = ⊥) : False := by
  set Y := conjClosure K T with hYdef
  set U := orbSup T I with hUdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure K T
  have hKY : K ≤ Y := le_conjClosure K T
  have hUT : ∀ t ∈ T, ∀ w ∈ U, t w ∈ U := fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hUY : ∀ y ∈ Y, ∀ w ∈ U, y w ∈ U :=
    orbSup_mem_of_normalizes hTY fun y hy w hw => hI.1.2.1 ⟨y, hy⟩ w hw
  have htop : ∀ g : MulAut W, g ∈ stabSub (⊤ : Subgroup W) := fun g u =>
    ⟨fun _ => trivial, fun _ => trivial⟩
  have hAtriv : ∀ b ∈ A, b ∈ centSec (⊤ : Subgroup W) U := by
    intro b hb
    refine ⟨htop b, fun w _ => ?_⟩
    have hw : w ∈ U ⊔ fixV A := by rw [hAU]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    have hbc : b c = c := (mem_fixV.1 hc) b hb
    have e : b (u * c) * (u * c)⁻¹ = b u * u⁻¹ := by
      rw [map_mul, hbc, mul_inv_rev]
      group
    rw [e]
    exact U.mul_mem (hUT b (hAT hb) u hu) (U.inv_mem hu)
  have hKtriv : K ≤ centSec (⊤ : Subgroup W) U :=
    le_of_conj_mem hKq (fun k hk g hg => centSec_conj hg (htop k) (hUY k (hKY hk)))
      (hAtriv a haA) haK hdich
  have hYN : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y := by
    have hle : Y ≤ Subgroup.centralizer (N : Set (MulAut W)) := by
      refine conjClosure_le fun t ht k hk => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hn' : t⁻¹ * n * t ∈ N := (Subgroup.mem_normalizer_iff''.1 (hTN ht) n).1 hn
      have h1 := hKN k hk _ hn'
      calc n * (t * k * t⁻¹) = t * ((t⁻¹ * n * t) * k) * t⁻¹ := by group
        _ = t * (k * (t⁻¹ * n * t)) * t⁻¹ := by rw [h1]
        _ = t * k * t⁻¹ * n := by group
    intro y hy n hn
    exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) n hn).symm
  set P := Y ⊓ centSec (⊤ : Subgroup W) U with hP
  have hRU : commV P ≤ U := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, rfl⟩
    exact hg.2.2 w trivial
  have hRY : ∀ y ∈ Y, ∀ r ∈ commV P, y r ∈ commV P := fun y hy =>
    commV_mem_of_normalizes fun g hg =>
      ⟨Y.mul_mem (Y.mul_mem hy hg.1) (Y.inv_mem hy), centSec_conj hg.2 (htop y) (hUY y hy)⟩
  have hRN : ∀ n ∈ N, ∀ r ∈ commV P, n r ∈ commV P := fun n hn =>
    commV_mem_of_normalizes fun g hg => by
      rw [← hYN g hg.1 n hn, mul_inv_cancel_right]
      exact hg
  have hKR : commV K ≤ commV P :=
    Subgroup.closure_mono fun _ ⟨g, hg, w, hw⟩ => ⟨g, le_inf hKY hKtriv hg, w, hw⟩
  have hItop : I ∈ IrrPlusOn Y ⊤ T :=
    mem_irrPlusOn_of_le (W' := ⊤) hTY (fun t ht w hw => hUT t ht w hw)
      (fun y w hw => hUY y y.2 w hw) (fun _ _ _ _ => trivial) le_top hI
  have hRU' : commV P ≤ ⨆ y ∈ T, y • I := by
    rw [← orbSup_eq_biSup_smul]
    exact hRU
  have hfix := fixV_of_mem_irrPlusOn hW hTY hYN hNperf hItop hRU' hRY hRN
  exact hKne (eq_bot_of_fix_comm hNcomm (commutator_eq_self_of_isQuasisimple hKq) hKN hKR
    fun n hn r hr x hx => hfix n hn r hr x (hKY hx))

end Module

end CFSG.Quasithin.SmithD39Two
