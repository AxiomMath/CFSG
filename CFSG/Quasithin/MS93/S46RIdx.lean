module

public import CFSG.Quasithin.MS93.S46RKC
public import CFSG.Quasithin.MS93.S4A432N

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
  CFSG.Quasithin.MS93.S46.KC2 CFSG.Quasithin.MS93.S46.KCF
open scoped commutatorElement Matrix

section Dual

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] {K W Z : Subgroup 𝔾}
  {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem commutator_mem_natSec (N : NatSec K W Z ψ true) {w : 𝔾} (hw : w ∈ W) (t : ↥K) :
    ⁅w, (t : 𝔾)⁆ ∈ W := by
  have e : ⁅w, (t : 𝔾)⁆ = w * ((t : 𝔾) * w⁻¹ * (t : 𝔾)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact W.mul_mem hw (N.conj_mem t (W.inv_mem hw))

theorem coord_commutator_rootElt (N : NatSec K W Z ψ true) {w : 𝔾} (hw : w ∈ W) {t : ↥K}
    {i : Fin 3} (hi : i ≠ 0) {c : F} (ht : toSL3 ψ t = rootElt i 0 c) :
    N.coord ⁅w, (t : 𝔾)⁆ = Pi.single 0 (c * N.coord w i) := by
  have hm : (t : 𝔾) * w⁻¹ * (t : 𝔾)⁻¹ ∈ W := N.conj_mem t (W.inv_mem hw)
  have e : ⁅w, (t : 𝔾)⁆ = w * ((t : 𝔾) * w⁻¹ * (t : 𝔾)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, N.coord_mul hw hm, N.coord_conj t (W.inv_mem hw), natAct_true, ht, N.coord_inv hw,
    dualMat_rootElt_mulVec hi, Pi.neg_apply, neg_mul_neg, add_neg_cancel_left]

theorem coord_eq_zero_of_commutator_mem (N : NatSec K W Z ψ true) {w : 𝔾} (hw : w ∈ W)
    {t : ↥K} {i : Fin 3} (hi : i ≠ 0) (ht : toSL3 ψ t = rootElt i 0 1)
    (hwt : ⁅w, (t : 𝔾)⁆ ∈ Z) : N.coord w i = 0 := by
  have h1 := (N.coord_eq_zero_iff (commutator_mem_natSec N hw t)).mpr hwt
  rw [coord_commutator_rootElt N hw hi ht, one_mul] at h1
  simpa using congrFun h1 0

end Dual

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

section Orbit

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem conj_mem_vOrb_sup {α x : Vtx X} {k : X.Universal} (hk : k ∈ stab X α) {y : X.Universal}
    (hy : y ∈ vOrb X α x ⊔ ZM X α) : k * y * k⁻¹ ∈ vOrb X α x ⊔ ZM X α := by
  have hle : (vOrb X α x ⊔ ZM X α).map (MulAut.conj k).toMonoidHom ≤ vOrb X α x ⊔ ZM X α := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact le_sup_left (a := vOrb X α x) (conj_mem_vOrb hk hz)
    · rw [← zm_smul, (mem_stab _).mp hk]
      exact le_sup_right
  exact hle ⟨y, hy, rfl⟩

theorem stab_le_normalizer_vOrb_sup (α x : Vtx X) :
    stab X α ≤ Subgroup.normalizer ((vOrb X α x ⊔ ZM X α : Subgroup _) : Set X.Universal) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_vOrb_sup hk, fun hy => ?_⟩
  have := conj_mem_vOrb_sup (Subgroup.inv_mem _ hk) hy
  simpa [mul_assoc] using this

theorem zm_le_vOrb_sup (α x : Vtx X) : ZM X x ≤ vOrb X α x ⊔ ZM X α := by
  have := zm_smul_le_vOrb (X := X) (α := α) (γ := x) (Subgroup.one_mem (stab X α))
  rw [one_smul] at this
  exact this.trans le_sup_left

end Orbit

theorem isSum_vOrb_sup_cfg (h14 : MS14AS) (hSQ : SQTKQuot) (h465 : I465) (h467 : I467)
    (h469 : I469Cfg M T L φ)
    {x : Vtx (puAmalgam c.pu.le)} (d : X3Data c α β x ψ)
    (hKC : ∀ g ∈ stab (puAmalgam c.pu.le) α, ZM (puAmalgam c.pu.le) (g • x) ≤ Qv _ x) :
    IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α)
      (vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α) (ZM _ α) ψ true 1 := by
  set N := vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α with hN
  have hNn := stab_le_normalizer_vOrb_sup α x
  have hNV : N ≤ Vv (puAmalgam c.pu.le) α := sup_le (vOrb_le_vv d) d.lh.zv
  have hNQ : N ≤ Qv (puAmalgam c.pu.le) x := sup_le (iSup₂_le fun g hg => hKC g hg)
    (zm_le_qv_of_dist_le_three c.b4 d.mα (by rw [d.dist_αγ]; omega))
  have hNB : ¬ N ≤ Bloc c.pu.le L α := fun hle => d.zγ ((zm_le_vOrb_sup α x).trans hle)
  obtain ⟨W, hWN, hW⟩ := exists_lastLayer_cfg h14 hSQ h465 h467 h469 c d.mα d.adjαβ d.adjβγ d.zγ
    d.lh d.qvβ hNn le_sup_right (le_inf hNV hNQ) hNB
  have hWS : W ≤ vStar c.pu.le L α :=
    hWN.trans (sup_le (iSup₂_le fun g hg => zm_smul_le_vStar d hg) d.zαstar)
  have hWB : ¬ W ≤ Bloc c.pu.le L α := by
    intro hle
    obtain ⟨w, hw, hwc⟩ := (NatSec.ofIsSum hW.dual).exists_coord_eq (Pi.single (0 : Fin 3) (1 : F))
    have hwZ : w ∈ ZM (puAmalgam c.pu.le) α := d.star ⟨hWS hw, hle hw⟩
    have h0 := ((NatSec.ofIsSum hW.dual).coord_eq_zero_iff hw).mpr hwZ
    rw [hwc] at h0
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun h0 0)
  have hZxW : ZM (puAmalgam c.pu.le) x ≤ W := zm_le_of_normal_cfg h14 hSQ h465 h467 h469 c d.mα
    d.adjαβ d.adjβγ d.zγ d.lh d.qvβ hW.dual.1 hW.zW (hWN.trans (le_inf hNV hNQ)) hWB
  have hNW : N ≤ W := by
    refine sup_le (iSup₂_le fun g hg => ?_) hW.zW
    rw [zm_smul]
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hW.dual.1 hg) z).mp (hZxW hz)
  have hWN' : W = N := le_antisymm hWN hNW
  subst hWN'
  exact hW.dual

section Idx

theorem zm_smul_le_qv_of_kc2_cfg (hKC : KC4612TwoCfg M T L φ) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h467 : I467) (h469 : I469Cfg M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (d : X3Data c α β x ψ) :
    ∀ g ∈ stab (puAmalgam c.pu.le) α, ZM (puAmalgam c.pu.le) (g • x) ≤ Qv _ x := by
  refine zm_smul_le_qv_of_row21_cfg h464 h465 h466a h467 h469 d (fun k hk z hz => ?_)
  by_cases hq : Fintype.card F = 2
  · exact hKC c α β x d.mα d.adjαβ d.adjβγ d.zγ ψ d.lh.surj d.lh.nat d.qvβ hq k hk z hz
  · have hq4 : 4 ≤ Fintype.card F := by
      have := four_le_card_of_isSL3FullVia c.via (by rwa [Nat.card_eq_fintype_card])
      rwa [Nat.card_eq_fintype_card] at this
    exact KC.commutator_mem_of_rootGroup21 d hq4 hk (Subgroup.mem_sup_left hz)

theorem vOrb_sup_le_vv {x : Vtx (puAmalgam c.pu.le)} (d : X3Data c α β x ψ) :
    vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α ≤ Vv (puAmalgam c.pu.le) α :=
  sup_le (vOrb_le_vv d) d.lh.zv

theorem vOrb_sup_le_qv {x : Vtx (puAmalgam c.pu.le)} (d : X3Data c α β x ψ)
    (hKC : ∀ g ∈ stab (puAmalgam c.pu.le) α, ZM (puAmalgam c.pu.le) (g • x) ≤ Qv _ x) :
    vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α ≤ Qv (puAmalgam c.pu.le) x :=
  sup_le (iSup₂_le fun g hg => hKC g hg)
    (zm_le_qv_of_dist_le_three c.b4 d.mα (by rw [d.dist_αγ]; omega))

theorem coord_eq_zero_of_forall_commutator {x : Vtx (puAmalgam c.pu.le)} (d : X3Data c α β x ψ)
    (hd : IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α)
      (vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α) (ZM _ α) ψ true 1)
    {w : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α)
    (hwt : ∀ t ∈ Qv (puAmalgam c.pu.le) β, ⁅w, t⁆ ∈ ZM (puAmalgam c.pu.le) α) :
    (NatSec.ofIsSum hd).coord w 1 = 0 ∧ (NatSec.ofIsSum hd).coord w 2 = 0 := by
  obtain ⟨t₁, ht₁, he₁⟩ := mem_natImage.mp
    (by rw [d.qvβ]; exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 (1 : F)))
  obtain ⟨t₂, ht₂, he₂⟩ := mem_natImage.mp
    (by rw [d.qvβ]; exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 (1 : F)))
  exact ⟨coord_eq_zero_of_commutator_mem _ hw (by decide) he₁ (hwt _ ht₁),
    coord_eq_zero_of_commutator_mem _ hw (by decide) he₂ (hwt _ ht₂)⟩

theorem exists_inv_mul_mem_qv (h466a : I466a) {ρ : Vtx (puAmalgam c.pu.le)}
    (dγ : X3Data c α β γ ψ) (dρ : X3Data c α β ρ ψ)
    (hd : IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α)
      (vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α) (ZM _ α) ψ true 1)
    (hNγQ : vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α ≤ Qv (puAmalgam c.pu.le) γ)
    (hZZ : (ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α) ⊓ (ZM (puAmalgam c.pu.le) ρ ⊔ ZM _ α) ≤
      ZM (puAmalgam c.pu.le) α) :
    ∀ v ∈ Vv (puAmalgam c.pu.le) α, ∃ w ∈ vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α,
      w⁻¹ * v ∈ Qv (puAmalgam c.pu.le) ρ := by
  set Nγ := vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α with hNγdef
  have hNγV : Nγ ≤ Vv (puAmalgam c.pu.le) α := vOrb_sup_le_vv dγ
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := dγ.lh.fin
  have : Finite ↥(Vv (puAmalgam c.pu.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective dγ.lh.vK)
  choose wc hwc hwcc using fun p : F × F => (NatSec.ofIsSum hd).exists_coord_eq ![0, p.1, p.2]
  let f : F × F → ↥(Vv (puAmalgam c.pu.le) α) ⧸
      (Qv (puAmalgam c.pu.le) ρ).subgroupOf (Vv (puAmalgam c.pu.le) α) :=
    fun p => QuotientGroup.mk ⟨wc p, hNγV (hwc p)⟩
  have hf : Function.Injective f := by
    intro p p' hpp
    have h1 := QuotientGroup.eq.mp hpp
    rw [Subgroup.mem_subgroupOf] at h1
    have h1' : (wc p)⁻¹ * wc p' ∈ Qv (puAmalgam c.pu.le) ρ := by simpa using h1
    have huN : (wc p)⁻¹ * wc p' ∈ Nγ := Nγ.mul_mem (Nγ.inv_mem (hwc p)) (hwc p')
    have huV := hNγV huN
    have hut : ∀ t ∈ Qv (puAmalgam c.pu.le) β,
        ⁅(wc p)⁻¹ * wc p', t⁆ ∈ ZM (puAmalgam c.pu.le) α := by
      intro t ht
      refine hZZ ⟨dγ.commutator_qv_le hNγV hNγQ (Subgroup.commutator_mem_commutator huN ht), ?_⟩
      exact dρ.commutator_qv_le (X := Vv (puAmalgam c.pu.le) α ⊓ Qv _ ρ) inf_le_left
        inf_le_right (Subgroup.commutator_mem_commutator ⟨huV, h1'⟩ ht)
    obtain ⟨hu1, hu2⟩ := coord_eq_zero_of_forall_commutator dγ hd huN hut
    rw [(NatSec.ofIsSum hd).coord_mul (Nγ.inv_mem (hwc p)) (hwc p'),
      (NatSec.ofIsSum hd).coord_inv (hwc p), hwcc, hwcc] at hu1 hu2
    simp only [Pi.add_apply, Pi.neg_apply] at hu1 hu2
    simp at hu1 hu2
    exact Prod.ext (neg_add_eq_zero.mp hu1) (neg_add_eq_zero.mp hu2)
  have hcard : Nat.card (↥(Vv (puAmalgam c.pu.le) α) ⧸
      (Qv (puAmalgam c.pu.le) ρ).subgroupOf (Vv (puAmalgam c.pu.le) α)) ≤ Nat.card (F × F) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := F), ← sq]
    show (Qv (puAmalgam c.pu.le) ρ).relIndex (Vv (puAmalgam c.pu.le) α) ≤ _
    rw [← h466a G M T L F φ c ρ β dρ.mγ dρ.adjβγ.symm]
    refine Subgroup.relIndex_le_of_le_right (dγ.lh.vq.trans dγ.qαβ) ?_
    rw [h466a G M T L F φ c ρ β dρ.mγ dρ.adjβγ.symm]
    positivity
  have hsurj := (hf.bijective_of_nat_card_le hcard).2
  intro v hv
  obtain ⟨p, hp⟩ := hsurj (QuotientGroup.mk ⟨v, hv⟩)
  have h1 := QuotientGroup.eq.mp hp
  rw [Subgroup.mem_subgroupOf] at h1
  exact ⟨wc p, hwc p, by simpa using h1⟩

theorem commutator_mem_of_inv_mul {ρ : Vtx (puAmalgam c.pu.le)} (dγ : X3Data c α β γ ψ)
    (dρ : X3Data c α β ρ ψ)
    (hNγQ : vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α ≤ Qv (puAmalgam c.pu.le) γ)
    (hVeq : ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      ∃ w ∈ vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α,
        w⁻¹ * v ∈ Qv (puAmalgam c.pu.le) ρ) :
    ∀ v ∈ Vv (puAmalgam c.pu.le) α, ∀ t ∈ Qv (puAmalgam c.pu.le) β,
      ⁅v, t⁆ ∈ ZM (puAmalgam c.pu.le) γ ⊔ ZM (puAmalgam c.pu.le) ρ ⊔ ZM (puAmalgam c.pu.le) α := by
  set Y := ZM (puAmalgam c.pu.le) γ ⊔ ZM (puAmalgam c.pu.le) ρ ⊔ ZM (puAmalgam c.pu.le) α with hY
  have hYn : Qv (puAmalgam c.pu.le) β ≤ Subgroup.normalizer (Y : Set _) :=
    CFSG.LieType.Steinberg.le_normalizer_sup
      (CFSG.LieType.Steinberg.le_normalizer_sup (dγ.qβKγ.trans (stab_le_normalizer_zm _ γ))
        (dρ.qβKγ.trans (stab_le_normalizer_zm _ ρ)))
      (dγ.qβK.trans (stab_le_normalizer_zm _ α))
  intro v hv t ht
  obtain ⟨w, hw, hwp⟩ := hVeq v hv
  have hwV := vOrb_sup_le_vv dγ hw
  have hpV : w⁻¹ * v ∈ Vv (puAmalgam c.pu.le) α :=
    (Vv (puAmalgam c.pu.le) α).mul_mem ((Vv (puAmalgam c.pu.le) α).inv_mem hwV) hv
  have h1 : ⁅w, t⁆ ∈ Y := by
    have := dγ.commutator_qv_le (vOrb_sup_le_vv dγ) hNγQ (Subgroup.commutator_mem_commutator hw ht)
    exact (show ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α ≤ Y from
      sup_le (le_sup_left.trans le_sup_left) le_sup_right) this
  have h2 : ⁅w⁻¹ * v, t⁆ ∈ Y := by
    have := dρ.commutator_qv_le (X := Vv (puAmalgam c.pu.le) α ⊓ Qv _ ρ) inf_le_left inf_le_right
      (Subgroup.commutator_mem_commutator ⟨hpV, hwp⟩ ht)
    exact (show ZM (puAmalgam c.pu.le) ρ ⊔ ZM _ α ≤ Y from
      sup_le (le_sup_right.trans le_sup_left) le_sup_right) this
  have hwT : w ∈ Qv (puAmalgam c.pu.le) β := dγ.qαβ (dγ.lh.vq hwV)
  have e : ⁅v, t⁆ = w * ⁅w⁻¹ * v, t⁆ * w⁻¹ * ⁅w, t⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYn hwT) _).mp h2) h1

theorem zm_le_of_commutator_mem {x : Vtx (puAmalgam c.pu.le)} (d : X3Data c α β x ψ)
    (hd : IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α)
      (vOrb (puAmalgam c.pu.le) α x ⊔ ZM (puAmalgam c.pu.le) α) (ZM _ α) ψ true 1)
    {Y : Subgroup (puAmalgam c.pu.le).Universal}
    (hVT : ∀ v ∈ Vv (puAmalgam c.pu.le) α, ∀ t ∈ Qv (puAmalgam c.pu.le) β, ⁅v, t⁆ ∈ Y)
    (hZY : ZM (puAmalgam c.pu.le) α ≤ Y) : ZM (puAmalgam c.pu.le) x ≤ Y := by
  intro y hy
  have hyN := zm_le_vOrb_sup α x hy
  have hyt : ∀ t ∈ Qv (puAmalgam c.pu.le) β, ⁅y, t⁆ ∈ ZM (puAmalgam c.pu.le) α :=
    fun t ht => d.commutator_sup_qv_le
      (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hy) ht)
  obtain ⟨hy1, hy2⟩ := coord_eq_zero_of_forall_commutator d hd hyN hyt
  obtain ⟨w', hw', hw'c⟩ := (NatSec.ofIsSum hd).exists_coord_eq (Pi.single 1 1)
  obtain ⟨t, ht, he⟩ := mem_natImage.mp (by
    rw [d.qvβ]
    exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 ((NatSec.ofIsSum hd).coord y 0)))
  have hc := coord_commutator_rootElt (NatSec.ofIsSum hd) hw' (show (1 : Fin 3) ≠ 0 by decide) he
  rw [hw'c, Pi.single_eq_same, mul_one] at hc
  have hm := commutator_mem_natSec (NatSec.ofIsSum hd) hw' t
  have hcy : (NatSec.ofIsSum hd).coord ⁅w', (t : (puAmalgam c.pu.le).Universal)⁆ =
      (NatSec.ofIsSum hd).coord y := by
    rw [hc]
    funext k
    fin_cases k
    · simp
    · simp [hy1]
    · simp [hy2]
  have hyy := (NatSec.ofIsSum hd).inv_mul_mem_of_coord_eq hm hyN hcy
  have e : y = ⁅w', (t : (puAmalgam c.pu.le).Universal)⁆ *
      (⁅w', (t : (puAmalgam c.pu.le).Universal)⁆⁻¹ * y) := by group
  rw [e]
  exact Y.mul_mem (hVT w' (vOrb_sup_le_vv d hw') t ht) (hZY hyy)

end Idx

theorem vv_le_sup_bloc {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {N : Subgroup (puAmalgam h.le).Universal}
    (hNn : ∀ k ∈ stab (puAmalgam h.le) α, ∀ y ∈ N, k * y * k⁻¹ ∈ N)
    (hZ : ∀ x, (puAmalgam h.le).treeGraph.Adj β x → ¬ ZM (puAmalgam h.le) x ≤ Bloc h.le L α →
      ZM (puAmalgam h.le) x ≤ N) :
    Vv (puAmalgam h.le) α ≤ N ⊔ Bloc h.le L α := by
  refine (S4A.vv_le_iSup_nablaSet_sup_bloc h hb hα).trans
    (sup_le (iSup₂_le fun δ hδ => ?_) le_sup_right)
  obtain ⟨hd, hZδ⟩ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have := (even_dist_iff _ α δ).mp (by rw [hd]; exact ⟨1, rfl⟩)
    exact this.mp hα
  rw [zv_of_isMVtx _ hδM] at hZδ
  set β' := geo (puAmalgam h.le) α δ 1 with hβ'
  have hαβ' : (puAmalgam h.le).treeGraph.Adj α β' := adj_geo_one _ (by omega)
  have hβ'δ : (puAmalgam h.le).treeGraph.Adj β' δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by omega)
    rwa [geo_of_le (puAmalgam h.le)
      (by omega : (puAmalgam h.le).treeGraph.dist α δ ≤ 1 + 1)] at this
  obtain ⟨k, hk, hkβ⟩ := I467.exists_mem_stab_smul_eq hα hαβ' hαβ
  have hkα : k • α = α := (mem_stab _).mp hk
  have hβx : (puAmalgam h.le).treeGraph.Adj β (k • δ) := by
    rw [← hkβ]
    exact (adj_smul _ k β' δ).mpr hβ'δ
  have hZx : ¬ ZM (puAmalgam h.le) (k • δ) ≤ Bloc h.le L α := by
    intro hle
    apply hZδ
    rw [zm_smul] at hle
    have h1 : Bloc h.le L α = (Bloc h.le L α).map (MulAut.conj k).toMonoidHom := by
      rw [← bloc_smul h k α, hkα]
    rw [h1] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj k).injective).mp hle
  intro y hy
  have hky : k * y * k⁻¹ ∈ N := hZ (k • δ) hβx hZx (by rw [zm_smul]; exact ⟨y, hy, rfl⟩)
  have := hNn k⁻¹ (Subgroup.inv_mem _ hk) _ hky
  rw [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this
  exact le_sup_left (a := N) this

theorem relIndex_bloc_le (h467 : I467) (d : X3Data c α β γ ψ)
    {N₁ N₂ : Subgroup (puAmalgam c.pu.le).Universal}
    (hd₁ : IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α) N₁ (ZM _ α) ψ true 1)
    (hd₂ : IsSumOfNaturalModulesVia (stab (puAmalgam c.pu.le) α) N₂ (ZM _ α) ψ true 1)
    (hN₁V : N₁ ≤ Vv (puAmalgam c.pu.le) α) (hN₂V : N₂ ≤ Vv (puAmalgam c.pu.le) α)
    (hVle : Vv (puAmalgam c.pu.le) α ≤ N₁ ⊔ N₂ ⊔ Bloc c.pu.le L α) :
    (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α) ≤ Fintype.card F ^ 6 := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := critDist_gt_two c
  have hB := h467 G M T L F φ c α d.mα
  have hZB : ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L α := zm_le_bloc c.pu hb d.mα
  have hBV : Bloc c.pu.le L α ≤ Vv (puAmalgam c.pu.le) α := by
    rw [hB]
    exact inf_le_left
  have hcentB : ∀ b ∈ Bloc c.pu.le L α, ∀ v ∈ Vv (puAmalgam c.pu.le) α, b * v = v * b := by
    intro b hb v hv
    rw [hB] at hb
    exact (Subgroup.mem_centralizer_iff.mp hb.2 v hv).symm
  have hNn : ∀ k ∈ stab (puAmalgam c.pu.le) α, ∀ y ∈ N₁ ⊔ N₂, k * y * k⁻¹ ∈ N₁ ⊔ N₂ := by
    intro k hk y hy
    have hle : (N₁ ⊔ N₂).map (MulAut.conj k).toMonoidHom ≤ N₁ ⊔ N₂ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact le_sup_left (a := N₁) ((Subgroup.mem_normalizer_iff.mp (hd₁.1 hk) y).mp hy)
      · rintro _ ⟨y, hy, rfl⟩
        exact le_sup_right (b := N₂) ((Subgroup.mem_normalizer_iff.mp (hd₂.1 hk) y).mp hy)
    exact hle ⟨y, hy, rfl⟩
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := d.lh.fin
  have : Finite ↥(Vv (puAmalgam c.pu.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective d.lh.vK)
  choose a₁ ha₁ ha₁c using fun y : Fin 3 → F => (NatSec.ofIsSum hd₁).exists_coord_eq y
  choose a₂ ha₂ ha₂c using fun y : Fin 3 → F => (NatSec.ofIsSum hd₂).exists_coord_eq y
  let Φ : (Fin 3 → F) × (Fin 3 → F) → ↥(Vv (puAmalgam c.pu.le) α) ⧸
      (Bloc c.pu.le L α).subgroupOf (Vv (puAmalgam c.pu.le) α) :=
    fun p => QuotientGroup.mk ⟨a₁ p.1 * a₂ p.2,
      (Vv (puAmalgam c.pu.le) α).mul_mem (hN₁V (ha₁ _)) (hN₂V (ha₂ _))⟩
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_conj
      (A := N₁ ⊔ N₂) (B := Bloc c.pu.le L α)
      (fun b hb a ha => hNn b (d.lh.vK (hBV hb)) a ha) (hVle hv)
    obtain ⟨m, hm, m', hm', rfl⟩ := exists_mul_eq_of_mem_sup_of_conj (A := N₁) (B := N₂)
      (fun b hb a ha => (Subgroup.mem_normalizer_iff.mp (hd₁.1 (d.lh.vK (hN₂V hb))) a).mp ha) hy
    refine ⟨((NatSec.ofIsSum hd₁).coord m, (NatSec.ofIsSum hd₂).coord m'), ?_⟩
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have h1 := (NatSec.ofIsSum hd₁).inv_mul_mem_of_coord_eq (ha₁ ((NatSec.ofIsSum hd₁).coord m)) hm
      (ha₁c _)
    have h2 := (NatSec.ofIsSum hd₂).inv_mul_mem_of_coord_eq
      (ha₂ ((NatSec.ofIsSum hd₂).coord m')) hm' (ha₂c _)
    set u₁ := a₁ ((NatSec.ofIsSum hd₁).coord m) with hu₁
    set u₂ := a₂ ((NatSec.ofIsSum hd₂).coord m') with hu₂
    have hm'V : m' ∈ Vv (puAmalgam c.pu.le) α := hN₂V hm'
    show (u₁ * u₂)⁻¹ * (m * m' * b) ∈ Bloc c.pu.le L α
    have e : (u₁ * u₂)⁻¹ * (m * m' * b) = u₂⁻¹ * ((u₁⁻¹ * m) * m') * b := by group
    rw [e, hcentB _ (hZB h1) m' hm'V]
    have e2 : u₂⁻¹ * (m' * (u₁⁻¹ * m)) * b = (u₂⁻¹ * m') * (u₁⁻¹ * m) * b := by group
    rw [e2]
    exact (Bloc c.pu.le L α).mul_mem ((Bloc c.pu.le L α).mul_mem (hZB h2) (hZB h1)) hb
  have hcard := Nat.card_le_card_of_surjective Φ hΦ
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := F)] at hcard
  calc (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α)
      = Nat.card (↥(Vv (puAmalgam c.pu.le) α) ⧸
          (Bloc c.pu.le L α).subgroupOf (Vv (puAmalgam c.pu.le) α)) := rfl
    _ ≤ Fintype.card F ^ 3 * Fintype.card F ^ 3 := hcard
    _ = Fintype.card F ^ 6 := by ring

theorem idx4612Cfg_of_kc2 (hKC : KC4612TwoCfg M T L φ) (h14 : MS14AS) (hSQ : SQTKQuot)
    (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a) (h466b : I466b)
    (h467 : I467) (h469 : I469Cfg M T L φ) : Idx4612Cfg M T L φ := by
  intro c α hα
  have h20 := c.pu.hyp20
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h20 hα
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) :=
    adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hZγ := zm_geo_two_not_le_bloc h43 h467 c hc
  obtain ⟨ψ, hψs, hψU, hψT⟩ := exists_coord_qv h464 h465 h466a c hα hαβ
  have hD : ∀ x, (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) x →
      ¬ ZM (puAmalgam c.pu.le) x ≤ Bloc c.pu.le L α → X3Data c α (geo _ α α' 1) x ψ :=
    fun x hβx hZx => X3Data.ofCfg h463 h464 h465 h466b h467 h469 c hα hαβ hβx hZx hψs hψU hψT
  have hKCx := fun x (d : X3Data c α (geo _ α α' 1) x ψ) =>
    zm_smul_le_qv_of_kc2_cfg hKC h464 h465 h466a h467 h469 d
  have hDual := fun x (d : X3Data c α (geo _ α α' 1) x ψ) =>
    isSum_vOrb_sup_cfg h14 hSQ h465 h467 h469 d (hKCx x d)
  have dγ := hD _ hβγ hZγ
  have hNγB : ¬ vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α ≤
      Bloc c.pu.le L α := fun hle => hZγ ((zm_le_vOrb_sup α _).trans hle)
  obtain ⟨ρ, hβρ, hZρ, z, hz, n, hn, hzn⟩ := exists_adj_not_commute h467 c hα hαβ
    (stab_le_normalizer_vOrb_sup α _) (vOrb_sup_le_vv dγ) hNγB
  have dρ := hD ρ hβρ hZρ
  have hNγρ : (vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α) ⊓
      (vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α) ≤ Bloc c.pu.le L α := by
    by_contra hcon
    have hn' : stab (puAmalgam c.pu.le) α ≤ Subgroup.normalizer
        (((vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α) ⊓
          (vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α) : Subgroup _) :
            Set (puAmalgam c.pu.le).Universal) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_inf]
      rw [Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vOrb_sup α _ hk) y,
        Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vOrb_sup α ρ hk) y]
    have hZN := zm_le_of_normal_cfg h14 hSQ h465 h467 h469 c hα hαβ hβγ hZγ dγ.lh dγ.qvβ hn'
      (le_inf le_sup_right le_sup_right)
      (inf_le_left.trans (le_inf (vOrb_sup_le_vv dγ) (vOrb_sup_le_qv dγ (hKCx _ dγ)))) hcon
    have hle : vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α ≤
        vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α := by
      refine sup_le (iSup₂_le fun g hg => ?_) le_sup_right
      rw [zm_smul]
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vOrb_sup α ρ hg) y).mp
        (hZN hy).2
    exact hzn (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 dρ.mγ hz) n
      (vOrb_sup_le_qv dρ (hKCx ρ dρ) (hle hn))).symm
  have hZZ : (ZM (puAmalgam c.pu.le) (geo _ α α' 2) ⊔ ZM _ α) ⊓
      (ZM (puAmalgam c.pu.le) ρ ⊔ ZM _ α) ≤ ZM (puAmalgam c.pu.le) α := by
    intro y hy
    refine dγ.star ⟨(sup_le dγ.zγstar dγ.zαstar) hy.1, hNγρ ⟨?_, ?_⟩⟩
    · exact (sup_le (zm_le_vOrb_sup α _) le_sup_right) hy.1
    · exact (sup_le (zm_le_vOrb_sup α ρ) le_sup_right) hy.2
  have hVeq := exists_inv_mul_mem_qv h466a dγ dρ (hDual _ dγ) (vOrb_sup_le_qv dγ (hKCx _ dγ)) hZZ
  have hVT := commutator_mem_of_inv_mul dγ dρ (vOrb_sup_le_qv dγ (hKCx _ dγ)) hVeq
  have hVle : Vv (puAmalgam c.pu.le) α ≤
      (vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α) ⊔
        (vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α) ⊔ Bloc c.pu.le L α := by
    refine vv_le_sup_bloc c.pu hb hα hαβ (fun k hk y hy => ?_) (fun x hβx hZx => ?_)
    · have hle : ((vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α) ⊔
          (vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α)).map
            (MulAut.conj k).toMonoidHom ≤
          (vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM (puAmalgam c.pu.le) α) ⊔
            (vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM (puAmalgam c.pu.le) α) := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          exact le_sup_left (a := vOrb (puAmalgam c.pu.le) α (geo _ α α' 2) ⊔ ZM _ α)
            (conj_mem_vOrb_sup hk hy)
        · rintro _ ⟨y, hy, rfl⟩
          exact le_sup_right (b := vOrb (puAmalgam c.pu.le) α ρ ⊔ ZM _ α)
            (conj_mem_vOrb_sup hk hy)
      exact hle ⟨y, hy, rfl⟩
    · refine (zm_le_of_commutator_mem (hD x hβx hZx) (hDual x (hD x hβx hZx)) hVT
        le_sup_right).trans ?_
      exact sup_le (sup_le ((zm_le_vOrb_sup α _).trans le_sup_left)
        ((zm_le_vOrb_sup α ρ).trans le_sup_right)) (le_sup_right.trans le_sup_left)
  exact relIndex_bloc_le h467 dγ (hDual _ dγ) (hDual ρ dρ) (vOrb_sup_le_vv dγ)
    (vOrb_sup_le_vv dρ) hVle

theorem idx4612_of_kc2 (hKC : KC4612Two) (h14 : MS14AS) (hSQ : SQTKQuot) (h43 : S43)
    (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a) (h466b : I466b) (h467 : I467)
    (h469 : I469) : Idx4612 :=
  fun G _ _ M T L F _ _ φ => idx4612Cfg_of_kc2 (hKC G M T L F φ) h14 hSQ h43 h463 h464 h465 h466a
    h466b h467 (h469 G M T L F φ)

end CFSG.Quasithin.MS93.S46R
