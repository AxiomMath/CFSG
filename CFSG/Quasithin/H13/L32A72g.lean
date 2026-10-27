module

public import CFSG.Quasithin.H13.L32A72f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_of_ne_bot {T L V : Subgroup G} (h : Hyp1281One G T L V 3) {W : Subgroup G}
    (hWV : W ≤ V) (hW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) (hne : W ≠ ⊥) : W = V := by
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hne ((Subgroup.eq_bot_iff_forall W).mpr hc)
  refine le_antisymm hWV fun v hv => ?_
  by_cases hv1 : v = 1
  · rw [hv1]
    exact one_mem _
  by_cases hvw : v = w
  · rw [hvw]
    exact hw
  obtain ⟨l, hl, hl1, -⟩ := exists_conj_eq_pair h (hWV hw) hv hv (hWV hw) hw1 hv1 hv1 hw1
    (Ne.symm hvw) hvw
  rw [← hl1]
  exact hW l hl w hw

omit [Finite G] in
theorem le_normalizer_centerOf {T L V : Subgroup G} :
    L ≤ Subgroup.normalizer (centerOf (sL T L V) : Set G) := by
  refine le_normalizer_of_conj_mem' fun l hl z hz => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hl) z).mp
      (Subgroup.mem_inf.mp hz).1
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : l⁻¹ * s * l ∈ sL T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (le_normalizer_conjClosure _ _ hl)) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ hs'
    calc s * (l * z * l⁻¹) = l * ((l⁻¹ * s * l) * z) * l⁻¹ := by group
      _ = l * (z * (l⁻¹ * s * l)) * l⁻¹ := by rw [h1]
      _ = l * z * l⁻¹ * s := by group

omit [Finite G] in
theorem le_normalizer_commutator {L X Y : Subgroup G} (hX : L ≤ Subgroup.normalizer (X : Set G))
    (hY : L ≤ Subgroup.normalizer (Y : Set G)) :
    L ≤ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := fun l hl => by
  rw [← conjSub_eq_self_iff, conjSub, Subgroup.map_commutator,
    show X.map (MulAut.conj l).toMonoidHom = X from conjSub_eq_self_iff.mpr (hX hl),
    show Y.map (MulAut.conj l).toMonoidHom = Y from conjSub_eq_self_iff.mpr (hY hl)]

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem eq_sL_of (hu0 : u0 T V = fsuV1 T V) (h63 : H6.VolI_H_6_3) (h65 : H6.VolI_H_6_5)
    (h71 : Lemma14_7_71) {N : Subgroup G} (hVN : V ≤ N) (hNS : N ≤ sL T L V)
    (hNL : L ≤ Subgroup.normalizer (N : Set G)) (hne : N ≠ V) : N = sL T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, m, hθs, -, hBp, hmU, hmV, hmT, hgen, χ, hχk, hχtr, -, hχe⟩ :=
    C.exists_st hu0 h65 h71
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hBL : (H6.borel.comap θ).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hNp : IsPGroup 2 ↥N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le
      (hNS.trans (sL_le_pCoreOf C.setting C.hF C.hMod))
  obtain ⟨m', hm'N, hm'V, hm'B⟩ := exists_mem_fix_mod hVN (Ne.symm hne) hBp hNp
    (hBL.trans hNL) (hBL.trans hLV) (hNS.trans C.sL_le_normalizer)
  have hmS : m ∈ sL T L V := le_conjClosure _ _ hmU
  have hm'S : m' ∈ sL T L V := hNS hm'N
  have hχ1 : ∀ s : ↥(sL T L V), χ s = 1 ↔ (s : G) ∈ V := fun s => by
    rw [← MonoidHom.mem_ker, hχk, Subgroup.mem_subgroupOf]
  have hfix : ∀ s : ↥(sL T L V),
      (∀ l : ↥L, θ l ∈ H6.borel → (l : G) * s * (l : G)⁻¹ * (s : G)⁻¹ ∈ V) →
      ∀ t ∈ H6.borel, H6.ρSt t ⟨Multiplicative.toAdd (χ s), hχtr s⟩ =
        ⟨Multiplicative.toAdd (χ s), hχtr s⟩ := by
    intro s hs t ht
    obtain ⟨l, rfl⟩ := hθs t
    have hls : (l : G) * s * (l : G)⁻¹ ∈ sL T L V :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ l.2) s).mp s.2
    have h1 := hχe l s ⟨_, hls⟩ rfl
    have h2 : χ ⟨_, hls⟩ = χ s := by
      have hv : (l : G) * s * (l : G)⁻¹ * (s : G)⁻¹ ∈ V := hs l ht
      have e : (⟨_, hls⟩ : ↥(sL T L V)) = ⟨_, hVN.trans hNS hv⟩ * s :=
        Subtype.ext (by simp)
      rw [e, map_mul, (hχ1 _).mpr hv, one_mul]
    apply Subtype.ext
    show RuType.stAct (θ l) (Multiplicative.toAdd (χ s)) = Multiplicative.toAdd (χ s)
    calc RuType.stAct (θ l) (Multiplicative.toAdd (χ s)) =
        Multiplicative.toAdd (χ ⟨_, hls⟩) := by rw [h1, toAdd_ofAdd]
      _ = Multiplicative.toAdd (χ s) := by rw [h2]
  obtain ⟨-, -, -, -, -, ⟨m₀, -, -, huniq⟩, -, -, -⟩ := h63
  have hne0 : ∀ s : ↥(sL T L V), (s : G) ∉ V →
      (⟨Multiplicative.toAdd (χ s), hχtr s⟩ : H6.St) ≠ 0 := fun s hs h0 => hs (by
    rw [← hχ1]
    have h1 := congrArg Subtype.val h0
    exact Multiplicative.toAdd.injective (h1.trans (toAdd_one).symm))
  have e1 := huniq _ (hne0 ⟨m', hm'S⟩ hm'V) (hfix ⟨m', hm'S⟩ fun l hl => hm'B l
    (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩))
  have e2 := huniq _ (hne0 ⟨m, hmS⟩ hmV) (hfix ⟨m, hmS⟩ hmT)
  have hχmm : χ ⟨m', hm'S⟩ = χ ⟨m, hmS⟩ :=
    Multiplicative.toAdd.injective (congrArg Subtype.val (e1.trans e2.symm))
  have hmN : m ∈ N := by
    have h1 : m' * m⁻¹ ∈ V := by
      have := (hχ1 (⟨m', hm'S⟩ * (⟨m, hmS⟩)⁻¹)).mp (by
        rw [map_mul, map_inv, hχmm]
        exact mul_inv_cancel _)
      simpa using this
    rw [show m = (m' * m⁻¹)⁻¹ * m' by group]
    exact mul_mem (inv_mem (hVN h1)) hm'N
  refine le_antisymm hNS fun s hs => ?_
  refine (Subgroup.closure_le N).mpr ?_ (hgen s hs)
  rintro _ (⟨l, rfl⟩ | hv)
  · exact (Subgroup.mem_normalizer_iff.mp (hNL l.2) m).mp hmN
  · exact hVN hv

theorem centerOf_eq (hu0 : u0 T V = fsuV1 T V) (h63 : H6.VolI_H_6_3) (h65 : H6.VolI_H_6_5)
    (h71 : Lemma14_7_71) : centerOf (sL T L V) = V := by
  by_contra hne
  have h1 := C.eq_sL_of hu0 h63 h65 h71 C.v_le_centerOf inf_le_left le_normalizer_centerOf hne
  apply C.not_comm
  intro a ha b hb
  have hb' : b ∈ centerOf (sL T L V) := by rw [h1]; exact hb
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb').2 a ha

theorem commutator_eq_v (hu0 : u0 T V = fsuV1 T V) : ⁅sL T L V, sL T L V⁆ = V := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  refine eq_of_le_of_ne_bot (C.hyp.hyp1281One C.h13322 C.hMod) (C.commutator_le_v hu0)
    (fun l hl w hw => (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator
      (le_normalizer_conjClosure _ _) (le_normalizer_conjClosure _ _) hl) w).mp hw) ?_
  intro hbot
  apply C.not_comm
  intro a ha b hb
  have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) ha
  exact (Subgroup.mem_centralizer_iff.mp this b hb).symm

theorem frattiniOf_eq_v (hu0 : u0 T V = fsuV1 T V) : frattiniOf (sL T L V) = V :=
  C.commutator_eq.1.trans (C.commutator_eq_v hu0)

theorem commutator_sL_eq (hu0 : u0 T V = fsuV1 T V) (h63 : H6.VolI_H_6_3)
    (h65 : H6.VolI_H_6_5) (h71 : Lemma14_7_71) : ⁅sL T L V, L⁆ = sL T L V := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hLS : L ≤ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _
  have hle : ⁅sL T L V, L⁆ ≤ sL T L V := by
    rw [Subgroup.commutator_le]
    intro s hs l hl
    rw [commutatorElement_def, show s * l * s⁻¹ * l⁻¹ = s * (l * s⁻¹ * l⁻¹) by group]
    exact mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hLS hl) _).mp (inv_mem hs))
  have hLL : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hVL : ⁅V, L⁆ = V := by
    refine eq_of_le_of_ne_bot (C.hyp.hyp1281One C.h13322 C.hMod) ?_
      (fun l hl w hw => (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_commutator hLV hLL hl) w).mp hw) ?_
    · rw [Subgroup.commutator_le]
      intro v hv l hl
      rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
      exact mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (inv_mem hv))
    · intro hbot
      obtain ⟨x, hxL1, -, -, hxV⟩ := C.exists_x3
      have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
      apply hxV
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (this hv) x hxL).symm
  have hVS : V ≤ ⁅sL T L V, L⁆ :=
    hVL.symm.le.trans (Subgroup.commutator_mono (v_le_fsuU.trans (le_conjClosure _ _)) le_rfl)
  by_contra hne
  apply hne
  refine C.eq_sL_of hu0 h63 h65 h71 hVS hle (le_normalizer_commutator hLS hLL) ?_
  intro heq
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU hu0
  apply C.comm_not_mem hu0 hxL1 hx3 hx1 hu huV
  have h1 : ⁅u, x⁆ ∈ ⁅sL T L V, L⁆ :=
    Subgroup.commutator_mem_commutator (le_conjClosure _ _ hu) hxL
  rw [heq, commutatorElement_def] at h1
  have := inv_mem h1
  rwa [show (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ by group] at this

theorem isSteinbergSection (hu0 : u0 T V = fsuV1 T V) (h63 : H6.VolI_H_6_3)
    (h65 : H6.VolI_H_6_5) (h71 : Lemma14_7_71) : IsSteinbergSection L (sL T L V) V := by
  obtain ⟨θ₁, -, hθs₁, hθ1₁, -, -, -, -, -, χ, hχk, hχtr, hχs, hχe⟩ := C.exists_st hu0 h65 h71
  intro θ hθs hθk
  have hk1 : θ₁.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, hθ1₁, Subgroup.mem_subgroupOf]
  have hcard168 : Nat.card H6.Γ = 168 := card_SL_three_two'
  have hle : θ.ker ≤ θ₁.ker := by
    rw [hθk, hk1]
    intro l hl
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hv)).2 l hl).symm
  have hkeq : θ.ker = θ₁.ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ₁.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv,
      hcard168] at h1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ₁ hθs₁).toEquiv,
      hcard168] at h2
    omega
  set α : H6.Γ ≃* H6.Γ := ((QuotientGroup.quotientKerEquivOfSurjective θ₁ hθs₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkeq.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs) with hα
  have hαθ : ∀ l : ↥L, α (θ₁ l) = θ l := by
    intro l
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have : (QuotientGroup.quotientKerEquivOfSurjective θ₁ hθs₁).symm (θ₁ l) =
        (QuotientGroup.mk l : ↥L ⧸ θ₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  obtain ⟨-, -, -, h2, -⟩ := h63
  obtain ⟨f, hf, hfe⟩ := h2 α
  set e := AddEquiv.ofBijective f hf with he
  have he' : ∀ (g : H6.Γ) (y : H6.St), e.symm (H6.ρSt g y) = H6.ρSt (α g) (e.symm y) := by
    intro g y
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    show H6.ρSt g y = f (H6.ρSt (α g) (e.symm y))
    have := hfe g (e.symm y)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    rw [this]
    congr 1
    exact (e.apply_symm_apply y).symm
  let stv : ↥(sL T L V) → H6.St := fun s => ⟨Multiplicative.toAdd (χ s), hχtr s⟩
  have hstv1 : stv 1 = 0 := Subtype.ext (show Multiplicative.toAdd (χ 1) = 0 by
    rw [map_one, toAdd_one])
  have hstvm : ∀ a b, stv (a * b) = stv a + stv b := fun a b => Subtype.ext
    (show Multiplicative.toAdd (χ (a * b)) =
      Multiplicative.toAdd (χ a) + Multiplicative.toAdd (χ b) by rw [map_mul, toAdd_mul])
  have hstv0 : ∀ s, stv s = 0 ↔ χ s = 1 := fun s => by
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (χ s) = 0 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)
    · intro h
      exact Subtype.ext (show Multiplicative.toAdd (χ s) = 0 by rw [h, toAdd_one])
  have hstve : ∀ (l : ↥L) (s t : ↥(sL T L V)), (t : G) = l * s * (l : G)⁻¹ →
      stv t = H6.ρSt (θ₁ l) (stv s) := fun l s t hst => Subtype.ext
    (show Multiplicative.toAdd (χ t) = RuType.stAct (θ₁ l) (Multiplicative.toAdd (χ s)) by
      rw [hχe l s t hst, toAdd_ofAdd])
  have hstvs : ∀ y : H6.St, ∃ s, stv s = y := fun y => by
    obtain ⟨s, hs⟩ := hχs y.1 y.2
    exact ⟨s, Subtype.ext (show Multiplicative.toAdd (χ s) = y.1 by rw [hs, toAdd_ofAdd])⟩
  let χ' : ↥(sL T L V) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { toFun := fun s => Multiplicative.ofAdd
        ((e.symm (stv s) : H6.St) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      map_one' := by
        rw [hstv1, map_zero]
        rfl
      map_mul' := fun a b => by rw [hstvm, map_add, AddSubgroup.coe_add, ofAdd_add] }
  have hχ' : ∀ s, χ' s = Multiplicative.ofAdd
      ((e.symm (stv s) : H6.St) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := fun _ => rfl
  refine ⟨χ', ?_, fun s => ?_, fun A hA => ?_, fun l s t hst => ?_⟩
  · ext s
    rw [MonoidHom.mem_ker, hχ', ← hχk, MonoidHom.mem_ker, ← hstv0]
    constructor
    · intro h
      have h1 : e.symm (stv s) = 0 := Subtype.ext (congrArg Multiplicative.toAdd h)
      rw [← e.apply_symm_apply (stv s), h1, map_zero]
    · intro h
      rw [h, map_zero]
      rfl
  · rw [hχ', toAdd_ofAdd]
    exact (e.symm (stv s)).2
  · obtain ⟨s, hs⟩ := hstvs (e ⟨A, hA⟩)
    refine ⟨s, ?_⟩
    rw [hχ', hs, AddEquiv.symm_apply_apply]
  · rw [hχ', hχ', ← hαθ l, hstve l s t hst, he', toAdd_ofAdd]
    rfl

end Ctx72

end CFSG.Quasithin.H13.L32A
