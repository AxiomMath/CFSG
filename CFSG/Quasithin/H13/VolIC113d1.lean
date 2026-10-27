module

public import CFSG.Quasithin.H13.VolIC113c2
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.G6
open scoped IsMulCommutative commutatorElement

@[expose] noncomputable def heartHom : ↥(evenWeight 6) →+ Additive (DnQuot 6) where
  toFun x := Additive.ofMul (QuotientGroup.mk
    (⟨Multiplicative.ofAdd (x : Fin 6 → ZMod 2), by
      rw [mem_coreMod]
      have := x.2
      simpa [evenWeight] using this⟩ : ↥(coreMod 6)))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem constWeight_le_ker_heartHom : constWeight 6 ≤ heartHom.ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  have hconst : ∀ i, (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) 0 := fun i => hx i 0
  show (QuotientGroup.mk _ : DnQuot 6) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_⟩
  · rcases (show (x : Fin 6 → ZMod 2) 0 = 0 ∨ (x : Fin 6 → ZMod 2) 0 = 1 by
      generalize (x : Fin 6 → ZMod 2) 0 = a; revert a; decide) with h0 | h1
    · have : Multiplicative.ofAdd (x : Fin 6 → ZMod 2) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        show (x : Fin 6 → ZMod 2) i = 0
        rw [hconst i, h0]
      show Multiplicative.ofAdd (x : Fin 6 → ZMod 2) ∈ Subgroup.zpowers (allOnes 6)
      rw [this]
      exact one_mem _
    · have : Multiplicative.ofAdd (x : Fin 6 → ZMod 2) = allOnes 6 := by
        apply Multiplicative.toAdd.injective
        funext i
        show (x : Fin 6 → ZMod 2) i = 1
        rw [hconst i, h1]
      show Multiplicative.ofAdd (x : Fin 6 → ZMod 2) ∈ Subgroup.zpowers (allOnes 6)
      rw [this]
      exact Subgroup.mem_zpowers _
  · show Multiplicative.ofAdd (x : Fin 6 → ZMod 2) ∈ coreMod 6
    rw [mem_coreMod]
    have := x.2
    simpa [evenWeight] using this

@[expose] noncomputable def heart6 : Multiplicative (AltHeart 6) →* DnQuot 6 :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift (constWeight 6) heartHom constWeight_le_ker_heartHom)

theorem heart6_mk (x : ↥(evenWeight 6)) :
    heart6 (Multiplicative.ofAdd (QuotientAddGroup.mk x)) =
      QuotientGroup.mk (⟨Multiplicative.ofAdd (x : Fin 6 → ZMod 2), by
        rw [mem_coreMod]
        have := x.2
        simpa [evenWeight] using this⟩ : ↥(coreMod 6)) := rfl

theorem heart6_injective : Function.Injective heart6 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd a)
  have ha' : a = Multiplicative.ofAdd (QuotientAddGroup.mk x) := by rw [hx]; rfl
  rw [MonoidHom.mem_ker, ha', heart6_mk] at ha
  have h1 := mk_eq_mk_iff_six.1 (ha.trans (QuotientGroup.mk_one _).symm)
  rw [Subgroup.mem_bot, ha']
  show Multiplicative.ofAdd (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.ofAdd 0
  congr 1
  rw [QuotientAddGroup.eq_zero_iff]
  intro i j
  rcases h1 with h | h
  · have hi := congrFun (congrArg Multiplicative.toAdd h) i
    have hj := congrFun (congrArg Multiplicative.toAdd h) j
    exact hi.symm.trans hj
  · have hall : ∀ k, (x : Fin 6 → ZMod 2) k = 1 := by
      intro k
      have hk := congrFun (congrArg Multiplicative.toAdd h) k
      have : (0 : ZMod 2) = (x : Fin 6 → ZMod 2) k + 1 := hk
      generalize (x : Fin 6 → ZMod 2) k = c at this ⊢
      revert c this
      decide
    rw [hall i, hall j]

theorem heart6_surjective : Function.Surjective heart6 := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ⟨Multiplicative.toAdd (m : PermMod 6), ?_⟩),
    ?_⟩
  · have := m.2
    rw [mem_coreMod] at this
    simpa [evenWeight] using this
  · rw [heart6_mk]
    rfl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def piOf (hL : IsShort2 L) (α : ↥L →* alternatingGroup (Fin 6))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ↥(alternatingGroup (Fin 6)) →* ↥(autOn L (blockU L)) :=
  (QuotientGroup.lift α.ker (actU L) (hαk ▸ pCore_le_ker_actU hL)).comp
    (QuotientGroup.quotientKerEquivOfSurjective α hαs).symm.toMonoidHom

theorem piOf_apply (hL : IsShort2 L) (α : ↥L →* alternatingGroup (Fin 6))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) (l : ↥L) :
    piOf hL α hαs hαk (α l) = actU L l := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective α hαs).symm (α l) =
      (l : ↥L ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [piOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  rfl

@[expose] noncomputable def Cover6.ofBlock [IsMulCommutative ↥(blockU L)] (hL : IsShort2 L)
    (α : ↥L →* alternatingGroup (Fin 6)) (hA : IsAltBlockTypeWith L 6 α) : Cover6 ↥(blockU L) :=
  { H := autOn L (blockU L)
    Z := (blockZ L).subgroupOf (blockU L)
    ρ := (autOn L (blockU L)).subtype.comp (piOf hL α hA.1 hA.2.1)
    β := heart6.comp hA.2.2.choose
    hV2 := fun v => Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact C1.blockU_sq hL v v.2)
    hZ := InternalSec.le_fixV_autOn (Cg := blockZ L) fun _ hx => hx.2.2
    hcomm := InternalSec.commV_autOn_eq_top (C1.le_normalizer_blockU L)
      (C1.commutator_blockU hL)
    hρ := fun σ => (piOf hL α hA.1 hA.2.1 σ).2
    hρs := fun h hh => by
      obtain ⟨l, hl⟩ := actU_surjective (L := L) ⟨h, hh⟩
      exact ⟨α l, by
        show ((piOf hL α hA.1 hA.2.1 (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) = h
        rw [piOf_apply, hl]⟩
    hβs := fun q => by
      obtain ⟨a, rfl⟩ := heart6_surjective q
      obtain ⟨u, rfl⟩ := hA.2.2.choose_spec.1 a
      exact ⟨u, rfl⟩
    hβk := fun v => by
      show heart6 (hA.2.2.choose v) = 1 ↔ v ∈ (blockZ L).subgroupOf (blockU L)
      rw [map_eq_one_iff heart6 heart6_injective, ← MonoidHom.mem_ker]
      exact Iff.of_eq (congrArg (v ∈ ·) hA.2.2.choose_spec.2.1)
    hβe := fun σ v m h => by
      obtain ⟨l, rfl⟩ := hA.1 σ
      set β₆ := hA.2.2.choose with hβ₆
      have hequiv := hA.2.2.choose_spec.2.2
      set x : ↥(evenWeight 6) := ⟨Multiplicative.toAdd (m : PermMod 6), by
        have := m.2
        rw [mem_coreMod] at this
        simpa [evenWeight] using this⟩ with hx
      have hmx : heart6 (Multiplicative.ofAdd (QuotientAddGroup.mk x)) = QuotientGroup.mk m := by
        rw [heart6_mk]
        rfl
      have hβv : β₆ v = Multiplicative.ofAdd (QuotientAddGroup.mk x) :=
        heart6_injective (h.trans hmx.symm)
      set w : ↥(blockU L) := ((((autOn L (blockU L)).subtype.comp
        (piOf hL α hA.1 hA.2.1)) (α l)) v) with hw
      have hwG : (w : G) = l * (v : G) * (l : G)⁻¹ := by
        rw [hw]
        show ((((piOf hL α hA.1 hA.2.1 (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
          v : ↥(blockU L)) : G) = _
        rw [piOf_apply, actU_apply]
      have h1 := hequiv l v w hwG x (by rw [hβv]; rfl)
      show heart6 (β₆ w) = _
      have h2 : β₆ w = Multiplicative.ofAdd (QuotientAddGroup.mk
          (permWeight 6 ((α l : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) x)) := by
        rw [h1]
        rfl
      rw [h2, heart6_mk]
      rfl }

theorem Cover6.ofBlock_ρ [IsMulCommutative ↥(blockU L)] (hL : IsShort2 L)
    {α : ↥L →* alternatingGroup (Fin 6)} (hA : IsAltBlockTypeWith L 6 α) (l : ↥L)
    (v : ↥(blockU L)) :
    (((Cover6.ofBlock hL α hA).ρ (α l) v : ↥(blockU L)) : G) = l * v * (l : G)⁻¹ := by
  show ((((piOf hL α hA.1 hA.2.1 (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
    v : ↥(blockU L)) : G) = _
  rw [piOf_apply, actU_apply]

theorem Cover6.ofBlock_Z [IsMulCommutative ↥(blockU L)] (hL : IsShort2 L)
    {α : ↥L →* alternatingGroup (Fin 6)} (hA : IsAltBlockTypeWith L 6 α) :
    (Cover6.ofBlock hL α hA).Z = (blockZ L).subgroupOf (blockU L) := rfl

theorem comm_eq_one_of_fix_five (hL : IsShort2 L) {α : ↥L →* alternatingGroup (Fin 6)}
    (hA : IsAltBlockTypeWith L 6 α) {l : ↥L}
    (h5 : ((α l : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) 5 = 5) {u : G}
    (hu : u ∈ blockU L) (hz : (l : G) * u * (l : G)⁻¹ * u⁻¹ ∈ blockZ L) :
    (l : G) * u * (l : G)⁻¹ * u⁻¹ = 1 := by
  have : IsMulCommutative ↥(blockU L) := isMulCommutative_blockU hL
  have hY := (Cover6.ofBlock hL α hA).comm_mem_Y h5 ⟨u, hu⟩
  have hρ : (Cover6.ofBlock hL α hA).ρ (α l) ⟨u, hu⟩ =
      (⟨(l : G) * u * (l : G)⁻¹, AppC.conj_mem_blockU l.2 hu⟩ : ↥(blockU L)) :=
    Subtype.ext (Cover6.ofBlock_ρ hL hA l ⟨u, hu⟩)
  rw [hρ] at hY
  have hZ : ((⟨(l : G) * u * (l : G)⁻¹, AppC.conj_mem_blockU l.2 hu⟩ : ↥(blockU L)) *
      (⟨u, hu⟩ : ↥(blockU L))⁻¹ : ↥(blockU L)) ∈ (Cover6.ofBlock hL α hA).Z := by
    rw [Cover6.ofBlock_Z, Subgroup.mem_subgroupOf]
    exact hz
  have h1 : ((⟨(l : G) * u * (l : G)⁻¹, AppC.conj_mem_blockU l.2 hu⟩ : ↥(blockU L)) *
      (⟨u, hu⟩ : ↥(blockU L))⁻¹ : ↥(blockU L)) = 1 := by
    have := Subgroup.mem_inf.2 ⟨hY, hZ⟩
    rw [(Cover6.ofBlock hL α hA).inf_Z] at this
    exact this
  exact congrArg Subtype.val h1

theorem exists_quotient_hom (hL : IsShort2 L) {X : Type} [Group X] (α : ↥L →* X)
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    [((blockU L).subgroupOf L).Normal] :
    ∃ ρ : ↥L ⧸ (blockU L).subgroupOf L →* X, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (↥L ⧸ (blockU L).subgroupOf L) ∧ IsPGroup 2 ρ.ker ∧
      (∀ l : ↥L, (l : ↥L ⧸ (blockU L).subgroupOf L) ∈ ρ.ker ↔ (l : G) ∈ blockQ L) ∧
      ∀ l : ↥L, ρ (l : ↥L ⧸ (blockU L).subgroupOf L) = α l := by
  have hNk : (blockU L).subgroupOf L ≤ α.ker := by
    rw [hαk, pCore_eq_subgroupOf]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (C1.blockU_le_blockQ hL (Subgroup.mem_subgroupOf.mp hx))
  have hker : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ blockQ L := by
    intro l
    rw [← MonoidHom.mem_ker, hαk, pCore_eq_subgroupOf, Subgroup.mem_subgroupOf]
  refine ⟨QuotientGroup.lift _ α hNk, ?_, ?_, ?_, fun l => hker l, fun l => rfl⟩
  · intro σ
    obtain ⟨l, rfl⟩ := hαs σ
    exact ⟨(l : ↥L ⧸ (blockU L).subgroupOf L), rfl⟩
  · intro e he
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    have hlQ : (l : G) ∈ blockQ L := (hker l).1 he
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmem : ⁅(l : G)⁻¹, (k : G)⁻¹⁆ ∈ blockU L :=
      Subgroup.commutator_mem_commutator ((blockQ L).inv_mem hlQ) (L.inv_mem k.2)
    rw [commutatorElement_def, inv_inv, inv_inv] at hmem
    simpa [mul_assoc] using hmem
  · rintro ⟨e, he⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    have hlQ : (l : G) ∈ blockQ L := (hker l).1 he
    obtain ⟨n, hn⟩ := C1.exists_pow_eq_one_of_isPGroup (C1.blockQ_isPGroup L) hlQ
    refine ⟨n, Subtype.ext ?_⟩
    show ((l : ↥L ⧸ (blockU L).subgroupOf L)) ^ 2 ^ n = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hn]
    exact one_mem _

omit [Finite G] in
theorem no2_quotient (hL : IsShort2 L) [((blockU L).subgroupOf L).Normal]
    (I : Subgroup (↥L ⧸ (blockU L).subgroupOf L)) (hI : I.Normal)
    (hpow : ∀ e, ∃ n : ℕ, e ^ 2 ^ n ∈ I) : I = ⊤ := by
  have hI' : (I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L))).Normal := hI.comap _
  have hp : IsPGroup 2 (↥L ⧸ I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L))) := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := hpow (l : ↥L ⧸ (blockU L).subgroupOf L)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap,
      QuotientGroup.mk'_apply, QuotientGroup.mk_pow]
    exact hn
  have htop := hL.1 _ hp
  rw [eq_top_iff]
  intro e _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
  have hl : l ∈ I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L)) := by
    rw [htop]; trivial
  exact hl

theorem exists_surj_lift {E X k : Type} [Group E] [Finite E] [Group X] [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (ρ : E →* X) (hρs : Function.Surjective ρ)
    (hkerc : ρ.ker ≤ Subgroup.center E) (hker2 : IsPGroup 2 ρ.ker)
    (hno2 : ∀ I : Subgroup E, I.Normal → (∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ I) → I = ⊤)
    (ψ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hψs : Function.Surjective ψ) :
    ∃ β : Matrix.SpecialLinearGroup (Fin 2) k →* E, ρ.comp β = ψ ∧ Function.Surjective β := by
  classical
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hρs hkerc hker2 ψ
  have hβx : ∀ g, ρ (β g) = ψ g := fun g => DFunLike.congr_fun hβ g
  have hdecomp : ∀ e : E, ∃ g, (β g)⁻¹ * e ∈ ρ.ker := by
    intro e
    obtain ⟨g, hg⟩ := hψs (ρ e)
    refine ⟨g, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβx, hg, inv_mul_cancel]
  have hIn : β.range.Normal := by
    refine ⟨fun i hi e => ?_⟩
    obtain ⟨g, hg⟩ := hdecomp e
    have he : e = β g * ((β g)⁻¹ * e) := by group
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    obtain ⟨g', rfl⟩ := hi
    rw [he]
    have : β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ = β g * β g' * (β g)⁻¹ := by
      calc β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ =
          β g * (((β g)⁻¹ * e) * β g') * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by group
        _ = β g * (β g' * ((β g)⁻¹ * e)) * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by rw [← hkc]
        _ = β g * β g' * (β g)⁻¹ := by group
    rw [this, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, rfl⟩
  have hpow : ∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ β.range := by
    intro e
    obtain ⟨g, hg⟩ := hdecomp e
    obtain ⟨n, hn⟩ := hker2 ⟨_, hg⟩
    have hn' : ((β g)⁻¹ * e) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    have hcomm : Commute (β g) ((β g)⁻¹ * e) := hkc (β g)
    refine ⟨n, ?_⟩
    have : e = β g * ((β g)⁻¹ * e) := by group
    rw [this, hcomm.mul_pow, hn', mul_one, ← map_pow]
    exact ⟨_, rfl⟩
  have htop := hno2 β.range hIn hpow
  exact ⟨β, hβ, fun e => by
    have : e ∈ β.range := by rw [htop]; trivial
    exact this⟩

end CFSG.Quasithin.H13.VolI
