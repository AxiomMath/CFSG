module

public import CFSG.Quasithin.H13.VolIC113
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem comm_mem_blockZ (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) {q n : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    (hn : n ∈ blockQ L) : q * n * q⁻¹ * n⁻¹ ∈ blockZ L := by
  have hqC : ∀ u ∈ blockU L, q * u = u * q := fun u hu => pCoreOf_comm_blockU hL hT hTN hq hu
  have hnL : n ∈ L := C1.blockQ_le L hn
  set e : G := q * n * q⁻¹ * n⁻¹ with he
  have heU : e ∈ blockU L := commutator_mem_blockU hL hTN hq hnL
  have hcent : ∀ ℓ ∈ L, ℓ * e * ℓ⁻¹ = e := by
    intro ℓ hℓ
    set c : G := q * ℓ * q⁻¹ * ℓ⁻¹ with hc
    have hcU : c ∈ blockU L := commutator_mem_blockU hL hTN hq hℓ
    set m : G := ℓ * n * ℓ⁻¹ with hm
    have hmQ : m ∈ blockQ L := AppC.conj_mem_blockQ hℓ hn
    set w : G := ℓ * e * ℓ⁻¹ with hw
    have hwU : w ∈ blockU L := AppC.conj_mem_blockU hℓ heU
    set u₁ : G := ℓ * n * ℓ⁻¹ * n⁻¹ with hu₁
    have hu₁U : u₁ ∈ blockU L := C1.commutator_mem_blockU' hℓ hn
    have h1 : q * ℓ * q⁻¹ = c * ℓ := by rw [hc]; group
    have h2 : q * n * q⁻¹ = e * n := by rw [he]; group
    have hcw : c * w = w * c := AppC.blockU_comm_blockU hL hcU hwU
    have hcm : c * m = m * c := C1.blockU_comm hL c hcU m hmQ
    have h3 : q * m * q⁻¹ = w * m := by
      calc q * m * q⁻¹ = (q * ℓ * q⁻¹) * (q * n * q⁻¹) * (q * ℓ * q⁻¹)⁻¹ := by
            rw [hm]; group
        _ = (c * ℓ) * (e * n) * (c * ℓ)⁻¹ := by rw [h1, h2]
        _ = c * (ℓ * e * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) * c⁻¹ := by group
        _ = c * w * m * c⁻¹ := rfl
        _ = w * m := by rw [hcw, mul_assoc w c m, hcm]; group
    have hmu : m = u₁ * n := by rw [hm, hu₁]; group
    have hq1 : q * u₁ * q⁻¹ = u₁ := by rw [hqC u₁ hu₁U]; group
    have h4 : q * m * q⁻¹ = u₁ * e * n := by
      calc q * m * q⁻¹ = (q * u₁ * q⁻¹) * (q * n * q⁻¹) := by rw [hmu]; group
        _ = u₁ * (e * n) := by rw [hq1, h2]
        _ = u₁ * e * n := by group
    have h5' : w * (u₁ * n) = u₁ * e * n := by rw [← hmu, ← h3, h4]
    have h6 : w * u₁ = u₁ * e := by
      have := h5'
      rw [← mul_assoc] at this
      exact mul_right_cancel this
    have hwu : w * u₁ = u₁ * w := AppC.blockU_comm_blockU hL hwU hu₁U
    rw [hwu] at h6
    exact mul_left_cancel h6
  exact ⟨heU, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => by
    have := hcent ℓ hℓ
    calc ℓ * e = (ℓ * e * ℓ⁻¹) * ℓ := by group
      _ = e * ℓ := by rw [this]⟩

omit [Finite G] in
theorem isMulCommutative_blockU (hL : IsShort2 L) : IsMulCommutative ↥(blockU L) :=
  ⟨⟨fun a b => Subtype.ext (C1.blockU_comm hL a a.2 b (C1.blockU_le_blockQ hL b.2))⟩⟩

theorem blockU_subgroupOf_normal (hL : IsShort2 L) : ((blockU L).subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((C1.blockU_le_blockQ hL).trans (C1.blockQ_le L))).mpr (C1.le_normalizer_blockU L)

@[expose] noncomputable def actU (L : Subgroup G) : ↥L →* ↥(autOn L (blockU L)) :=
  ((conjAct (blockU L)).comp (Subgroup.inclusion (C1.le_normalizer_blockU L))).codRestrict
    (autOn L (blockU L)) fun l => Subgroup.mem_map_of_mem _
      (show Subgroup.inclusion (C1.le_normalizer_blockU L) l ∈
        L.subgroupOf (Subgroup.normalizer (blockU L : Set G)) from l.2)

theorem actU_apply (l : ↥L) (u : ↥(blockU L)) :
    ((((actU L l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : ↥(blockU L)) : G) =
      l * u * (l : G)⁻¹ := rfl

theorem actU_surjective : Function.Surjective (actU L) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Subgroup.mem_map.1 hφ
  exact ⟨⟨g, hgL⟩, rfl⟩

theorem pCore_le_ker_actU (hL : IsShort2 L) : CFSG.pCore 2 ↥L ≤ (actU L).ker := by
  intro l hl
  have hlQ : (l : G) ∈ blockQ L := (AppC.mem_pCore_iff_mem_blockQ l).1 hl
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [actU_apply]
  show (l : G) * u * (l : G)⁻¹ = u
  rw [← C1.blockU_comm hL u u.2 l hlQ]
  group

theorem alternatingNatural_of_isAltType {m : ℕ} (hm : Odd m) (hL : IsShort2 L)
    (h : IsAltType L m) (hZ : blockZ L = ⊥) :
    ∃ _ : IsMulCommutative ↥(blockU L),
      AlternatingNatural (V := ↥(blockU L)) (autOn L (blockU L)) ⊤ ⊥ m := by
  classical
  have inst : IsMulCommutative ↥(blockU L) := isMulCommutative_blockU hL
  refine ⟨inst, ?_⟩
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  have hker : α.ker ≤ (actU L).ker := hαk ▸ pCore_le_ker_actU hL
  set e := QuotientGroup.quotientKerEquivOfSurjective α hαs with he
  set π : ↥(alternatingGroup (Fin m)) →* ↥(autOn L (blockU L)) :=
    (QuotientGroup.lift α.ker (actU L) hker).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ l : ↥L, π (α l) = actU L l := by
    intro l
    have h1 : e.symm (α l) = (l : ↥L ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hπs : Function.Surjective π := by
    intro φ
    obtain ⟨l, rfl⟩ := actU_surjective φ
    exact ⟨α l, hπα l⟩
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  refine ⟨π, hπs, le_top, inf_le_right, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  · intro φ z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ x hx
    exact G6.permAct_mem_coreMod _ hx
  · intro γ x hx
    rw [L246.altDn_ker_eq_bot hm] at hx ⊢
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx]
    show G6.permAct m _ 1 = 1
    exact map_one _
  · let toQ : Multiplicative ↥(evenWeight m) →*
        ↥(FFModel.altDn m).sec ⧸ (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec :=
      (QuotientGroup.mk' _).comp (L246.coreEquiv m).symm.toMonoidHom
    have hmk_inj : ∀ a b : ↥(FFModel.altDn m).sec,
        (QuotientGroup.mk a : ↥(FFModel.altDn m).sec ⧸
          (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec) = QuotientGroup.mk b →
          a = b := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [L246.altDn_ker_subgroupOf_eq_bot hm, Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact h1
    have htoQ : Function.Injective toQ := fun a b hab =>
      (L246.coreEquiv m).symm.injective (hmk_inj _ _ hab)
    have htoQs : Function.Surjective toQ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨L246.coreEquiv m x, by simp [toQ]⟩
    let β'' : ↥(⊤ : Subgroup ↥(blockU L)) →*
        ↥(FFModel.altDn m).sec ⧸ (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec :=
      toQ.comp (β.comp (⊤ : Subgroup ↥(blockU L)).subtype)
    refine ⟨β'', ?_, ?_, ?_⟩
    · intro q
      obtain ⟨y, rfl⟩ := htoQs q
      obtain ⟨u, rfl⟩ := hβs y
      exact ⟨⟨u, Subgroup.mem_top u⟩, rfl⟩
    · intro w
      rw [Subgroup.mem_bot]
      constructor
      · intro h1
        have h2 : toQ (β (w : ↥(blockU L))) = toQ 1 := by rw [map_one]; exact h1
        exact hβinj ((htoQ h2).trans (map_one β).symm)
      · intro h1
        show toQ (β (w : ↥(blockU L))) = 1
        rw [h1, map_one, map_one]
    · intro γ w x hw hx hwx
      obtain ⟨l, rfl⟩ := hαs γ
      have hxe : x = (L246.coreEquiv m).symm (β (w : ↥(blockU L))) := (hmk_inj _ _ hwx).symm
      have hconj : (((((π (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
          (w : ↥(blockU L))) : ↥(blockU L)) : G) = l * (w : ↥(blockU L)) * (l : G)⁻¹ := by
        rw [hπα l, actU_apply]
      generalize hw₁ : (((π (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
          (w : ↥(blockU L))) = w₁ at hw hconj
      have h1 := hβe l (w : ↥(blockU L)) w₁ hconj
      show (QuotientGroup.mk ((L246.coreEquiv m).symm (β w₁)) :
        ↥(FFModel.altDn m).sec ⧸ (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec) = _
      congr 1
      apply Subtype.ext
      subst hxe
      show Multiplicative.ofAdd ((Multiplicative.toAdd (β w₁) : ↥(evenWeight m)) :
          Fin m → ZMod 2) = G6.permAct m ((α l : ↥(alternatingGroup (Fin m))) : Equiv.Perm (Fin m))
          (Multiplicative.ofAdd ((Multiplicative.toAdd (β (w : ↥(blockU L))) :
            ↥(evenWeight m)) : Fin m → ZMod 2))
      apply Multiplicative.toAdd.injective
      funext i
      exact h1 i

end CFSG.Quasithin.H13.VolI
