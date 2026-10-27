module

public import CFSG.Quasithin.Background.InternalSecIrr
public import CFSG.Quasithin.Background.SmithD37Row
public import CFSG.Quasithin.Background.SmithD37ClsDefs
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Open
open scoped commutatorElement

section Sup

private theorem commutator_eq_top_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator X := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet a b)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

private theorem center_eq_bot_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem isQuasisimple_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hs hnc)).trans
      QuotientGroup.quotientBot
  refine ⟨⟨commutator_eq_top_of_simple hs hnc⟩, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

variable {Ω : Type*} [Group Ω] {L B : Subgroup Ω}

theorem le_normalizer_of_conj (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    B ≤ Subgroup.normalizer L := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hBN b hb h, fun hh => ?_⟩
  have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
  rw [← e]
  exact hBN b⁻¹ (B.inv_mem hb) _ hh

theorem conj_mem_of_sup (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    ∀ y ∈ L ⊔ B, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
  intro y hy l hl
  have hle : L ⊔ B ≤ Subgroup.normalizer L :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_conj hBN)
  exact (Subgroup.mem_normalizer_iff.1 (hle hy) l).1 hl

theorem exists_mul_pow_eq (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) {l b : Ω} (hl : l ∈ L)
    (hb : b ∈ B) (n : ℕ) : ∃ l' ∈ L, (l * b) ^ n = l' * b ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    refine ⟨l' * (b ^ n * l * (b ^ n)⁻¹), L.mul_mem hl' (hBN _ (B.pow_mem hb n) l hl), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem two_pow_mem_of_sup (hB : IsPGroup 2 ↥B) (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    ∀ y ∈ L ⊔ B, ∃ e : ℕ, y ^ 2 ^ e ∈ L := by
  intro y hy
  have hy' : y ∈ ((L ⊔ B : Subgroup Ω) : Set Ω) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L B (le_normalizer_of_conj hBN)] at hy'
  obtain ⟨l, hl, b, hb, rfl⟩ := hy'
  obtain ⟨e, he⟩ := hB ⟨b, hb⟩
  have hbe : b ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨l', hl', h'⟩ := exists_mul_pow_eq hBN hl hb (2 ^ e)
  exact ⟨e, by rw [h', hbe, mul_one]; exact hl'⟩

end Sup

section B4

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem pCoreOf_sup_eq_bot (hQ : ∀ v : Q, v ^ 2 = 1) {L B : Subgroup (MulAut Q)}
    (hs : IsSimpleGroup ↥L) (hnc : ∃ a b : ↥L, a * b ≠ b * a)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup Q) ⊤) (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    pCoreOf 2 (L ⊔ B) = ⊥ := by
  have hq := isQuasisimple_of_simple hs hnc
  have hqo : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ B)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ B)
  have hOle : pCoreOf 2 (L ⊔ B) ≤ L ⊔ B := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hnot : ¬ L ≤ pCoreOf 2 (L ⊔ B) := by
    intro hle
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (InternalSec.commute_of_isPGroup_two (hO2.to_le hle) a b)
  have hLO : ∀ l ∈ L, ∀ n ∈ pCoreOf 2 (L ⊔ B), l * n * l⁻¹ ∈ pCoreOf 2 (L ⊔ B) :=
    fun l hl n hn => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ B) (Subgroup.mem_sup_left hl)) n).mp hn
  have hcomm := B1Red.commute_of_normal_not_le hqo
    (fun n hn l hl => conj_mem_of_sup hBN n (hOle hn) l hl) hLO hnot
  have hodd := InternalSec.odd_card_eqvAut_of_irr hQ hirr hnc
  rw [eq_bot_iff]
  intro q hq'
  have hqe : q ∈ XMod.eqvAut ↥L Q := fun a p =>
    congrArg (fun f : MulAut Q => f p) (hcomm q hq' a a.2)
  obtain ⟨k, hk⟩ := hO2 ⟨q, hq'⟩
  have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥L Q)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥L Q)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_natCard _)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (orderOf_eq_one_iff.1 hord))

theorem b4Hyp_sup (hQ : ∀ v : Q, v ^ 2 = 1) [Nontrivial Q]
    {L B : Subgroup (MulAut Q)} (hs : IsSimpleGroup ↥L) (hnc : ∃ a b : ↥L, a * b ≠ b * a)
    (hSQ : SQTKGroup ↥L)
    (hirr : ∀ J : Subgroup Q, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hB : IsPGroup 2 ↥B) (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    B4Hyp (L ⊔ B) L := by
  have hq := isQuasisimple_of_simple hs hnc
  have hqo : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hirrL : XMod.IsIrrSec ↥L (⊥ : Subgroup Q) ⊤ :=
    ⟨bot_lt_top, fun J hJ _ _ => hirr J fun l hl v hv => hJ ⟨l, hl⟩ v hv⟩
  have hn := conj_mem_of_sup hBN
  have h2 := two_pow_mem_of_sup hB hBN
  refine ⟨InternalSec.sqtkGroup_of_two_pow le_sup_left hn h2 hSQ, ?_, hq, hirrL⟩
  exact (InternalSec.quasithinGenFitting_eq_of_two_pow le_sup_left hn hqo h2
    (pCoreOf_sup_eq_bot hQ hs hnc hirrL hBN)).symm

end B4

section NatHelpers

open scoped Matrix

variable {F : Type} [Field F] {d : ℕ}

theorem glAut_injective :
    Function.Injective (glAut : Matrix.GeneralLinearGroup (Fin d) F →* MulAut (natMod F d)) := by
  intro g h hgh
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have hv := congrArg (fun φ : MulAut (natMod F d) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd v))) hgh
  simpa [glAut_apply] using hv

theorem natMod_sq [CharP F 2] (v : natMod F d) : v ^ 2 = 1 := by
  rw [← toAdd_eq_zero, toAdd_pow]
  ext i
  simp [CharTwo.two_eq_zero]

private noncomputable def scalarHom (c : F) : natMod F d →* natMod F d where
  toFun v := Multiplicative.ofAdd (c • Multiplicative.toAdd v)
  map_one' := by simp
  map_mul' u v := by simp [smul_add]

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

theorem natAut_injective (Mm : MatModel L₁ L₂ F d) : Function.Injective (natAut Mm) :=
  glAut_injective.comp Mm.inj₁

end NatHelpers

section NatSub

open scoped Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

noncomputable def natSubEquiv (Mm : MatModel L₁ L₂ F d) : ↥L₁ ≃* ↥(natSub Mm) :=
  MonoidHom.ofInjective (natAut_injective Mm)

theorem irr_natSub (Mm : MatModel L₁ L₂ F d) (J : Subgroup (natMod F d))
    (hJ : ∀ l ∈ natSub Mm, ∀ v ∈ J, l v ∈ J) : J = ⊥ ∨ J = ⊤ := by
  let S : AddSubgroup (Fin d → F) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ J}
      zero_mem' := J.one_mem
      add_mem' := fun ha hb => J.mul_mem ha hb
      neg_mem' := fun ha => J.inv_mem ha }
  have hS : ∀ (l : ↥L₁), ∀ v ∈ S, ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F) *ᵥ v ∈ S := by
    intro l v hv
    have h := hJ (natAut Mm l) ⟨l, rfl⟩ (Multiplicative.ofAdd v) hv
    rw [natAut_apply, toAdd_ofAdd] at h
    exact h
  rcases Mm.irr₁ S hS with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : Multiplicative.toAdd x ∈ S := hx
    rw [h, AddSubgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (toAdd_eq_zero.mp hx')
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : Multiplicative.toAdd x ∈ S := h ▸ AddSubgroup.mem_top _
    exact hx'

theorem endCard_natSub (Mm : MatModel L₁ L₂ F d) (hd : 0 < d) :
    endCard (natSub Mm) = Nat.card F := by
  unfold endCard
  let f : F → {φ : natMod F d →* natMod F d // ∀ l ∈ natSub Mm, ∀ v, φ (l v) = l (φ v)} :=
    fun c => ⟨scalarHom c, by
      rintro _ ⟨l, rfl⟩ v
      simp [scalarHom, natAut_apply, Matrix.mulVec_smul]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' hcc'
      have h := congrArg (fun φ : {φ : natMod F d →* natMod F d //
        ∀ l ∈ natSub Mm, ∀ v, φ (l v) = l (φ v)} =>
          Multiplicative.toAdd (φ.1 (Multiplicative.ofAdd (Pi.single ⟨0, hd⟩ 1))) ⟨0, hd⟩) hcc'
      simpa [f, scalarHom] using h
    · rintro ⟨φ, hφ⟩
      let ψ : (Fin d → F) →+ (Fin d → F) :=
        { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
          map_zero' := by simp
          map_add' := fun u v => by simp [ofAdd_add] }
      obtain ⟨c, hc⟩ := Mm.end₁ ψ fun l v => by
        have h := hφ (natAut Mm l) ⟨l, rfl⟩ (Multiplicative.ofAdd v)
        rw [natAut_apply, natAut_apply, toAdd_ofAdd] at h
        exact congrArg Multiplicative.toAdd h
      refine ⟨c, Subtype.ext (MonoidHom.ext fun v => ?_)⟩
      have h := hc (Multiplicative.toAdd v)
      change Multiplicative.ofAdd (c • Multiplicative.toAdd v) = φ v
      rw [← h]
      rfl
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem b4Hyp_natSub [Fintype F] [CharP F 2] (Mm : MatModel L₁ L₂ F d) (hd : 0 < d)
    (hs : IsSimpleGroup ↥L₁) (hnc : ∃ a b : ↥L₁, a * b ≠ b * a)
    (hSQ : haveI := Finite.of_injective _ Mm.inj₁; SQTKGroup ↥L₁)
    {B : Subgroup (MulAut (natMod F d))} (hB : IsPGroup 2 ↥B)
    (hBN : ∀ b ∈ B, ∀ l ∈ natSub Mm, b * l * b⁻¹ ∈ natSub Mm) :
    B4Hyp (natSub Mm ⊔ B) (natSub Mm) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Finite ↥L₁ := Finite.of_injective _ Mm.inj₁
  have := hs
  refine b4Hyp_sup natMod_sq (natSubEquiv Mm).symm.isSimpleGroup ?_ ?_ (irr_natSub Mm) hB hBN
  · obtain ⟨a, b, hab⟩ := hnc
    refine ⟨natSubEquiv Mm a, natSubEquiv Mm b, fun h => hab ?_⟩
    apply (natSubEquiv Mm).injective
    rw [map_mul, map_mul, h]
  · refine InternalSec.sqtkGroup_of_surjective (natSubEquiv Mm).toMonoidHom
      (natSubEquiv Mm).surjective (fun g => ⟨0, ?_⟩) hSQ
    have hg : (natSubEquiv Mm) (g : ↥L₁) = 1 := MonoidHom.mem_ker.1 g.2
    rw [pow_zero, pow_one]
    exact Subtype.ext ((natSubEquiv Mm).map_eq_one_iff.1 hg)

end NatSub

end CFSG.Quasithin.SmithD37
