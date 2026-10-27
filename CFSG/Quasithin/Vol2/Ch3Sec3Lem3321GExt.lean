module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321D
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_normalized_eq {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hS : IsSylowTwoOf (T ⊓ L) L) {n : ℕ} (hn : 3 ≤ n) (ρ₀ : FLc.SLt n →* MulAut ↥V)
    (hrange : ∀ k ∈ autOn L V, ∃ g, ρ₀ g = k) (hrange' : ∀ g, ρ₀ g ∈ autOn L V)
    (hne : ∃ g, ρ₀ g ≠ 1) :
    ∃ h : FLc.SLt n, Function.Injective (ρ₀.comp (MulAut.conj h).toMonoidHom) ∧
      (∀ k ∈ autOn L V, ∃ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g = k) ∧
      (∀ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g ∈ autOn L V) ∧
      (FLc.Ut n).map (ρ₀.comp (MulAut.conj h).toMonoidHom) = autOn (T ⊓ L) V := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have := FLc.isSimpleGroup_SLt hn
  have hinj : Function.Injective ρ₀ := FLc.injective_of_ne_one ρ₀ hne
  have hsyl := FLc.exists_sylow_autOn hLV hS hrange hrange'
  have hTle : autOn (T ⊓ L) V ≤ ρ₀.range := fun a ha => by
    obtain ⟨x, hx, hxS, rfl⟩ := FLc.mem_autOn_iff.1 ha
    obtain ⟨g, hg⟩ := hrange _ (FLc.mem_autOn_iff.2 ⟨x, hx, hxS.2, rfl⟩)
    exact ⟨g, hg⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, hh⟩ := FLc.exists_rho_conj hn1 hTle hsyl
  obtain ⟨hr1, hr2⟩ := rho_conj_range hrange hrange' h
  exact ⟨h, fun x y hxy => (MulAut.conj h).injective (hinj hxy), hr1, hr2, hh⟩

theorem exists_alpha_of_rho (h : Hyp331 G T M L D) (hGA : GriessAllModelsStatement)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} (hinj : Function.Injective ρ)
    (hr1 : ∀ k ∈ autOn L (vPlus L T), ∃ g, ρ g = k) (hr2 : ∀ g, ρ g ∈ autOn L (vPlus L T))
    (hU : (FLc.Ut 4).map ρ = autOn (T ⊓ L) (vPlus L T)) :
    ∃ α : ↥L →* SL4, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
      ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩ := by
  have hLV := L3317.le_normalizer_vPlus h
  let ρ' : FLc.SLt 4 ≃* ↥(autOn L (vPlus L T)) :=
    MulEquiv.ofBijective (ρ.codRestrict (autOn L (vPlus L T)) hr2)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun k => by
        obtain ⟨g, hg⟩ := hr1 _ k.2
        exact ⟨g, Subtype.ext hg⟩⟩
  have hρ' : ∀ g, ((ρ' g : ↥(autOn L (vPlus L T))) : MulAut ↥(vPlus L T)) = ρ g := fun g => rfl
  let φ := InternalSec.autOnHom hLV
  let α : ↥L →* SL4 := ρ'.symm.toMonoidHom.comp φ
  have hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, hLV l.2⟩ := by
    intro l
    rw [← hρ']
    show ((ρ' (ρ'.symm (φ l)) : ↥(autOn L (vPlus L T))) : MulAut ↥(vPlus L T)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hαs : Function.Surjective α :=
    ρ'.symm.surjective.comp (InternalSec.autOnHom_surjective hLV)
  obtain ⟨α₀, -, hα₀k, hα₀c⟩ := Ln2.exists_modO2Surj h hGA hTL (K := ZMod 2) (Nat.card_zmod 2)
    le_rfl (by norm_num) e
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    rw [← hα₀k]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα₀c]
    constructor
    · intro hl
      have h1 : φ l = 1 := by
        have := congrArg ρ' hl
        rwa [show ρ' (α l) = φ l from ρ'.apply_symm_apply _, map_one] at this
      exact (InternalSec.mem_ker_autOnHom hLV l).1 h1
    · intro hl
      have h1 : φ l = 1 := (InternalSec.mem_ker_autOnHom hLV l).2 hl
      show ρ'.symm (φ l) = 1
      rw [h1, map_one]
  refine ⟨α, hαs, hαk, ?_, hαv⟩
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
    have h1 : ρ (α s) ∈ autOn (T ⊓ L) (vPlus L T) := by
      rw [hαv]
      exact FLc.mem_autOn_iff.2 ⟨s, hLV s.2, hs', rfl⟩
    rw [← hU] at h1
    obtain ⟨u, hu, hρu⟩ := h1
    rw [← hinj hρu]
    exact hu
  · intro hx
    have h1 : ρ x ∈ autOn (T ⊓ L) (vPlus L T) := by
      rw [← hU]
      exact ⟨x, hx, rfl⟩
    obtain ⟨s, hsN, hsTL, hρs⟩ := FLc.mem_autOn_iff.1 h1
    refine ⟨⟨s, hsTL.2⟩, Subgroup.mem_subgroupOf.2 hsTL, hinj ?_⟩
    rw [hαv, ← hρs]

theorem inf_centralizer_ne (hML : mPlus L T = L)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ¬ L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hLZ
  have hVZ : vPlus L T ≤ quasithinOmegaOneCenter T := by
    refine (vPlus_le_conjClosure hML).trans (conjClosure_le fun l hl z hz => ?_)
    rw [← Subgroup.mem_centralizer_iff.1 (hLZ hl) z hz, mul_inv_cancel_right]
    exact hz
  have hLV : L ≤ Subgroup.centralizer (vPlus L T : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.2 fun v hv => (Subgroup.mem_centralizer_iff.1 (hLZ hl) v (hVZ hv))
  have hsub : ∀ k ∈ autOn L (vPlus L T), k = 1 := by
    intro k hk
    obtain ⟨l, hl, hlL, rfl⟩ := FLc.mem_autOn_iff.1 hk
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [FLc.conjAct_coe hl, MulAut.one_apply,
      ← Subgroup.mem_centralizer_iff.1 (hLV hlL) v v.2, mul_inv_cancel_right]
  have h1 : Nat.card ↥(autOn L (vPlus L T)) ≤ 1 := by
    have : Subsingleton ↥(autOn L (vPlus L T)) :=
      ⟨fun a b => Subtype.ext ((hsub a a.2).trans (hsub b b.2).symm)⟩
    exact Finite.card_le_one_iff_subsingleton.2 this
  rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)] at h1
  norm_num at h1

theorem mem_centralizer_of_fix (h9 : Stmt3_3_9) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    {l : G} (hl : l ∈ L)
    (hfix : ∀ v : ↥(vPlus L T), (v : G) ∈ quasithinOmegaOneCenter T → (v : G) ∈ ⁅vPlus L T, L⁆ →
      conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h hl⟩ v = v) :
    l ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have h9' := h9 G T M L D h
  rw [hML] at h9'
  rw [h9']
  refine ⟨hl, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz.1
  have h1 := congrArg (fun w : ↥(vPlus L T) => (w : G)) (hfix ⟨z, hzV⟩ hz.1 hz.2)
  simp only [FLc.conjAct_coe] at h1
  calc z * l = (l * z * l⁻¹) * l := by rw [h1]
    _ = l * z := by group

theorem exists_alpha_ext (h9 : Stmt3_3_9) (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) :
    ∃ α : ↥L →* SL4, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = L3316.liftPre α P2 := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, -, π, hπ⟩ := hmod
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have : Nontrivial ↥(autOn L (vPlus L T)) := Finite.one_lt_card_iff_nontrivial.1
    (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
  obtain ⟨g₀, hg₀⟩ := FLc.rhoOf_surj hπ.1 k k.2
  have hne : ∃ g, FLc.rhoOf π g ≠ 1 := ⟨g₀, by rw [hg₀]; exact fun h1 => hk (Subtype.ext h1)⟩
  have hS := L3317.isSylowTwoOf_inf h hTL
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV hS (by norm_num)
    (FLc.rhoOf π) (FLc.rhoOf_surj hπ.1) (FLc.rhoOf_mem π) hne
  have D₁ := D₀.rtwist h'
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  refine ⟨α, hαs, hαk, hαU, ?_⟩
  have hP2C :
      L3316.liftPre α P2 ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_centralizer_of_fix h9 h hML l.2 fun v hvZ hvW => ?_
    have hvc : v ∈ commV (autOn L (vPlus L T)) := by
      rw [Ln2.commV_autOn_eq h]
      exact hvW
    have key := FLc.fixQ_of_model D₁ hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => FLc.fix_extSq4 a ha i hi hic) hvc
      (fun s hs => fix_of_mem_autOn_inf (by rw [← hU]; exact ⟨s, hs, rfl⟩) hvZ) (α l) hl
    rw [hαv l] at key
    exact key
  set Pz : Subgroup SL4 :=
    ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).subgroupOf L).map α with hPz
  have hUPz : FLc.Ut 4 ≤ Pz := by
    rw [← hαU]
    refine Subgroup.map_mono (Subgroup.subgroupOf_mono L fun t ht => ⟨ht.2, ?_⟩)
    exact CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1
  have hP2Pz : P2 ≤ Pz := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hP2C ⟨l, hg, rfl⟩), rfl⟩
  have hkerC : ∀ l : ↥L, α l = 1 →
      (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    refine mem_centralizer_of_fix h9 h hML l.2 fun v _ _ => ?_
    have key := hαv l
    rw [hl, map_one] at key
    rw [← key, MulAut.one_apply]
  have hcuts : FLc.cuts Pz = {2} := by
    have h1 : FLc.cuts Pz ⊆ {2} := by
      have := hP2Pz
      rw [FLc.eq_QI_cuts hUPz] at this
      exact (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).1 this
    refine Set.Subset.antisymm h1 fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    by_contra h2
    have hempty : FLc.cuts Pz = ∅ := by
      ext j
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hj
      have := h1 hj
      rw [Set.mem_singleton_iff] at this
      subst this
      exact h2 hj
    apply inf_centralizer_ne hML e
    intro l hl
    have hlPz : α ⟨l, hl⟩ ∈ Pz := by
      rw [FLc.eq_QI_cuts hUPz, hempty]
      show α ⟨l, hl⟩ ∈ flagStabilizer 4 (ZMod 2) ∅
      rw [flagStabilizer_empty]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := hlPz
    have h3 := hkerC (c⁻¹ * ⟨l, hl⟩) (by rw [map_mul, map_inv, hcl, inv_mul_cancel])
    have h4 : (c : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mem_subgroupOf.1 hc
    have e1 : l = (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e1]
    exact (Subgroup.mul_mem _ h4 h3).2
  have hPzeq : Pz = P2 := by
    rw [FLc.eq_QI_cuts hUPz, hcuts]
  refine le_antisymm (fun x hx => ?_) hP2C
  have h1 : α ⟨x, hx.1⟩ ∈ Pz := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hPzeq] at h1
  exact ⟨⟨x, hx.1⟩, h1, rfl⟩

end L3321

end CFSG.Quasithin.H13
