module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9b
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2RStruct

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_alpha_model (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D) (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (Z₀ : Subgroup ↥(vPlus L T))
      (Dm : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) Z₀
        (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = L3316.liftPre α P2 ∧
      (∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩) ∧
      Z₀ ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) := by
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
  refine ⟨α, (FLc.rhoOf π).comp (MulAut.conj h').toMonoidHom, Z₀, D₁, hαs, hαk, hαU, ?_, hαv,
    hZ₀⟩
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

end CFSG.Quasithin.H13.L3321

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

namespace E5aL

section Generic

variable {G : Type} [Group G]

theorem e5_exists_mul_sup_comm {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have h := hc a₂ ha₂ b₁ hb₁
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h := hc a ha b hb
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by rw [mul_inv_rev]
      _ = (a * b)⁻¹ := by rw [h]

theorem e5_comm_mul_left {z w n : G} (hzw : z * w = w * z) (hzn : z * n = n * z) :
    ⁅z * w, n⁆ = ⁅w, n⁆ := by
  have hzwi : z * w⁻¹ * z⁻¹ = w⁻¹ := by
    have h : z * w⁻¹ = w⁻¹ * z := by
      calc z * w⁻¹ = w⁻¹ * (w * z) * w⁻¹ := by group
        _ = w⁻¹ * (z * w) * w⁻¹ := by rw [hzw]
        _ = w⁻¹ * z := by group
    rw [h]
    group
  have hstar : z * w * n = w * n * z := by
    calc z * w * n = w * z * n := by rw [hzw]
      _ = w * (z * n) := by rw [mul_assoc]
      _ = w * (n * z) := by rw [hzn]
      _ = w * n * z := by rw [mul_assoc]
  simp only [commutatorElement_def, mul_inv_rev]
  calc z * w * n * (w⁻¹ * z⁻¹) * n⁻¹ = (z * w * n) * w⁻¹ * z⁻¹ * n⁻¹ := by group
    _ = (w * n * z) * w⁻¹ * z⁻¹ * n⁻¹ := by rw [hstar]
    _ = w * n * (z * w⁻¹ * z⁻¹) * n⁻¹ := by group
    _ = w * n * w⁻¹ * n⁻¹ := by rw [hzwi]

theorem e5_eq_zero_or_single (v : Fin 6 → ZMod 2) (hv : ∀ j, j ≠ k₀ → v j = 0) :
    v = 0 ∨ v = Pi.single k₀ 1 := by
  by_cases h : v k₀ = 0
  · left
    funext j
    by_cases hj : j = k₀
    · subst hj
      simp [h]
    · simp [hv j hj]
  · right
    have h1 : v k₀ = 1 := by
      revert h
      generalize v k₀ = a
      revert a
      decide
    funext j
    by_cases hj : j = k₀
    · subst hj
      simp [h1]
    · simp [hv j hj, Pi.single_apply, hj]

end Generic

section Coords

noncomputable abbrev e5wc (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) : Fin 6 → ZMod 2 :=
  B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a)

theorem e5wc_mul (a b : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    e5wc (a * b) = e5wc a + e5wc b := by
  simp only [e5wc, toAdd_mul, map_add]

theorem e5wc_inv (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) : e5wc a⁻¹ = -e5wc a := by
  simp only [e5wc, toAdd_inv, map_neg]

theorem e5wc_one : e5wc 1 = 0 := by
  simp only [e5wc, toAdd_one, map_zero]

theorem e5_eq_of_wc {a b : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))} (h : e5wc a = e5wc b) :
    a = b :=
  Multiplicative.toAdd.injective ((B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1 h)

theorem e5wc_actW_P2 {g : L3321.SL4} (hg : g ∈ L3321.P2)
    (y : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    e5wc (FLc.actW g y) k₁ = e5wc y k₁ :=
  wedge_P2_coord_pair23_actW g hg y

theorem e5wc_actW_U2 {g : L3321.SL4} (hg : g ∈ L3321.P2) (hA : L3321.blkA ⟨g, hg⟩ = 1)
    (hC : L3321.blkC ⟨g, hg⟩ = 1) (y : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))
    (hy : e5wc y k₁ = 0) (j : Fin 6) (hj : j ≠ k₀) : e5wc (FLc.actW g y) j = e5wc y j :=
  wedge_U2_comm_Hz_actW g hg hA hC y hy j hj

end Coords

section Model

variable {G : Type} [Group G] {V L : Subgroup G} [IsMulCommutative ↥V]
  {ρ : FLc.SLt 4 →* MulAut ↥V} {Z₀ : Subgroup ↥V}

theorem e5_mem_commV (hLV : L ≤ Subgroup.normalizer (V : Set G)) {x : G}
    (hx : x ∈ ⁅V, L⁆) : (⟨x, commutator_le_left_of_le_normalizer' hLV hx⟩ : ↥V) ∈
      commV (autOn L V) := by
  rw [AutOn.commV_autOn_eq hLV]
  exact Subgroup.mem_subgroupOf.2 hx

noncomputable def e5Phi (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    ↥(⁅V, L⁆ : Subgroup G) →* Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) :=
  Dm.β.comp
    { toFun := fun x => ⟨⟨x.1, commutator_le_left_of_le_normalizer' hLV x.2⟩,
        e5_mem_commV hLV x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem e5_conj_mem (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) {x : G}
    (hx : x ∈ ⁅V, L⁆) : (l : G) * x * (l : G)⁻¹ ∈ ⁅V, L⁆ :=
  (Subgroup.mem_normalizer_iff.1
    (mem_normalizer_commutator_of (hLV l.2) (Subgroup.le_normalizer l.2)) x).1 hx

theorem e5Phi_equiv (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (α : ↥L →* L3321.SL4) (hαv : ∀ l : ↥L, ρ (α l) = conjAct V ⟨l, hLV l.2⟩)
    (l : ↥L) (x : ↥(⁅V, L⁆ : Subgroup G)) :
    e5Phi hLV Dm ⟨(l : G) * x * (l : G)⁻¹, e5_conj_mem hLV l x.2⟩ =
      FLc.actW (α l) (e5Phi hLV Dm x) := by
  have hxV : x.1 ∈ V := commutator_le_left_of_le_normalizer' hLV x.2
  have hxl : (l : G) * x.1 * (l : G)⁻¹ ∈ V :=
    commutator_le_left_of_le_normalizer' hLV (e5_conj_mem hLV l x.2)
  have hu : ρ (α l) ⟨x.1, hxV⟩ ∈ commV (autOn L V) :=
    Dm.inv (α l) _ (e5_mem_commV hLV x.2)
  have key : ρ (α l) ⟨x.1, hxV⟩ = ⟨(l : G) * x.1 * (l : G)⁻¹, hxl⟩ := by
    apply Subtype.ext
    rw [hαv l, FLc.conjAct_coe]
  have h1 := Dm.equiv (α l) ⟨⟨x.1, hxV⟩, e5_mem_commV hLV x.2⟩ hu
  have h2 : Dm.β ⟨⟨(l : G) * x.1 * (l : G)⁻¹, hxl⟩, e5_mem_commV hLV
      (e5_conj_mem hLV l x.2)⟩ = Dm.β ⟨ρ (α l) ⟨x.1, hxV⟩, hu⟩ :=
    congrArg Dm.β (Subtype.ext key.symm)
  exact h2.trans h1

theorem e5Phi_comm (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (α : ↥L →* L3321.SL4) (hαv : ∀ l : ↥L, ρ (α l) = conjAct V ⟨l, hLV l.2⟩)
    (l : ↥L) (x : ↥(⁅V, L⁆ : Subgroup G)) :
    e5Phi hLV Dm ⟨⁅x.1, (l : G)⁆, Subgroup.commutator_mem_commutator
        (commutator_le_left_of_le_normalizer' hLV x.2) l.2⟩ =
      e5Phi hLV Dm x * FLc.actW (α l) (e5Phi hLV Dm x)⁻¹ := by
  have hxV : x.1 ∈ V := commutator_le_left_of_le_normalizer' hLV x.2
  have hel : (l : G) * x.1⁻¹ * (l : G)⁻¹ ∈ ⁅V, L⁆ := e5_conj_mem hLV l (inv_mem x.2)
  have hsplit : (⟨⁅x.1, (l : G)⁆, Subgroup.commutator_mem_commutator hxV l.2⟩ :
      ↥(⁅V, L⁆ : Subgroup G)) = x * ⟨(l : G) * x.1⁻¹ * (l : G)⁻¹, hel⟩ := by
    apply Subtype.ext
    show ⁅x.1, (l : G)⁆ = x.1 * ((l : G) * x.1⁻¹ * (l : G)⁻¹)
    rw [commutatorElement_def]
    group
  rw [hsplit, map_mul]
  congr 1
  have h2 : e5Phi hLV Dm ⟨(l : G) * x.1⁻¹ * (l : G)⁻¹, hel⟩ = FLc.actW (α l) (e5Phi hLV Dm x⁻¹) :=
    e5Phi_equiv hLV Dm α hαv l x⁻¹
  rw [h2, map_inv]

theorem e5wc_comm_P2 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (α : ↥L →* L3321.SL4) (hαv : ∀ l : ↥L, ρ (α l) = conjAct V ⟨l, hLV l.2⟩)
    (l : ↥L) (hl : α l ∈ L3321.P2) (x : ↥(⁅V, L⁆ : Subgroup G)) :
    e5wc (e5Phi hLV Dm ⟨⁅x.1, (l : G)⁆, Subgroup.commutator_mem_commutator
        (commutator_le_left_of_le_normalizer' hLV x.2) l.2⟩) k₁ = 0 := by
  rw [e5Phi_comm hLV Dm α hαv l x, e5wc_mul, Pi.add_apply, e5wc_actW_P2 hl, e5wc_inv, Pi.neg_apply,
    add_neg_cancel]

theorem e5wc_comm_U2 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (α : ↥L →* L3321.SL4) (hαv : ∀ l : ↥L, ρ (α l) = conjAct V ⟨l, hLV l.2⟩)
    (l : ↥L) (hl : α l ∈ U2) (x : ↥(⁅V, L⁆ : Subgroup G))
    (hx : e5wc (e5Phi hLV Dm x) k₁ = 0) (j : Fin 6) (hj : j ≠ k₀) :
    e5wc (e5Phi hLV Dm ⟨⁅x.1, (l : G)⁆, Subgroup.commutator_mem_commutator
        (commutator_le_left_of_le_normalizer' hLV x.2) l.2⟩) j = 0 := by
  obtain ⟨hgP, hA, hC⟩ := (mem_U2_iff (α l)).1 hl
  have hy : e5wc ((e5Phi hLV Dm x)⁻¹) k₁ = 0 := by
    rw [e5wc_inv, Pi.neg_apply, hx, neg_zero]
  rw [e5Phi_comm hLV Dm α hαv l x, e5wc_mul, Pi.add_apply,
    e5wc_actW_U2 hgP hA hC ((e5Phi hLV Dm x)⁻¹) hy j hj, e5wc_inv, Pi.neg_apply, add_neg_cancel]

noncomputable def e5Sub (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ⁅V, L⁆, e5wc (e5Phi hLV Dm ⟨x, hx⟩) k₁ = 0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha, ha'⟩ := ha
    obtain ⟨hb, hb'⟩ := hb
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have e : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : ↥(⁅V, L⁆ : Subgroup G)) = ⟨a, ha⟩ * ⟨b, hb⟩ :=
      rfl
    rw [e, map_mul, e5wc_mul, Pi.add_apply, ha', hb', add_zero]
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    have e : (⟨1, Subgroup.one_mem _⟩ : ↥(⁅V, L⁆ : Subgroup G)) = 1 := rfl
    rw [e, map_one, e5wc_one]
    rfl
  inv_mem' := by
    intro a ha
    obtain ⟨ha, ha'⟩ := ha
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    have e : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : ↥(⁅V, L⁆ : Subgroup G)) =
        (⟨a, ha⟩ : ↥(⁅V, L⁆ : Subgroup G))⁻¹ := rfl
    rw [e, map_inv, e5wc_inv, Pi.neg_apply, ha', neg_zero]

theorem e5_mem_Sub (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Dm : FLc.VModel 4 ρ (commV (autOn L V)) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) {x : G} :
    x ∈ e5Sub hLV Dm ↔ ∃ hx : x ∈ ⁅V, L⁆, e5wc (e5Phi hLV Dm ⟨x, hx⟩) k₁ = 0 :=
  Iff.rfl

end Model

end E5aL

open E5aL

theorem A2Cfg.comm_comm_R_le_Z
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) :
    ⁅⁅a2V L T, oTwoUpper H⁆, a2R H⁆ ≤ a2Z T := by
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨-, hLV, -, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hVC : vPlus L T ≤ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    (Hyp331.vPlus_reduced c.nf.hyp.toSetup331).1
  obtain ⟨α, ρ, Z₀, Dm, hαs, hαk, -, hCZ, hαv, hZ₀⟩ :=
    L3321.exists_alpha_model h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  have hZ0 : ∀ u ∈ Z₀, (u : G) = 1 := by
    intro u hu
    have hzf : u ∈ fixV (autOn L (vPlus L T)) := (Subgroup.mem_inf.1 (hZ₀ hu)).1
    have hzC : (u : G) ∈ Subgroup.centralizer (L : Set G) :=
      (AutOn.mem_fixV_autOn_iff hLV u).1 hzf
    have h2 : (u : G) ∈ vPlus L T ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨u.2, hzC⟩
    rw [c.inf_centralizer_L_eq_bot h36 h5 h128 h37 h38 h39, Subgroup.mem_bot] at h2
    exact h2
  have hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T := commutator_le_left_of_le_normalizer' hLV
  have hinj : Function.Injective (e5Phi hLV Dm) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hu : (⟨x.1, commutator_le_left_of_le_normalizer' hLV x.2⟩ : ↥(vPlus L T)) ∈ Z₀ :=
      Dm.ker ⟨⟨x.1, commutator_le_left_of_le_normalizer' hLV x.2⟩, e5_mem_commV hLV x.2⟩ hx
    have h1 := hZ0 _ hu
    exact Subtype.ext h1
  obtain ⟨⟨z₀, hz₀⟩, hz₀ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (c.inf_commutator_ne h36 h5 h128 h37 h38 h39)
  have hz₀Z : z₀ ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.1 hz₀).1
  have hz₀W : z₀ ∈ ⁅vPlus L T, L⁆ := (Subgroup.mem_inf.1 hz₀).2
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀ne (Subtype.ext h)
  have hz₁ne : e5Phi hLV Dm ⟨z₀, hz₀W⟩ ≠ 1 := fun h =>
    hz₀1 (congrArg Subtype.val (hinj (h.trans (map_one _).symm)))
  have hPfix : ∀ g ∈ L3321.P2, FLc.actW g (e5Phi hLV Dm ⟨z₀, hz₀W⟩) =
      e5Phi hLV Dm ⟨z₀, hz₀W⟩ := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    have hlC : (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [hCZ]
      exact Subgroup.mem_map.2 ⟨l, hg, rfl⟩
    have hcent : z₀ * (l : G) = (l : G) * z₀ :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hlC).2 z₀ hz₀Z
    have hconj : (l : G) * z₀ * (l : G)⁻¹ = z₀ := by
      rw [← hcent, mul_inv_cancel_right]
    have h2 := e5Phi_equiv hLV Dm α hαv l ⟨z₀, hz₀W⟩
    rw [← h2]
    exact congrArg (e5Phi hLV Dm) (Subtype.ext hconj)
  have hz₁Phi : e5Phi hLV Dm ⟨z₀, hz₀W⟩ = Multiplicative.ofAdd (B5FinWedge.wedgeBasis4 k₀) := by
    rcases wedge_P2_fixed_actW _ hPfix with h | h
    · exact absurd (toAdd_eq_zero.1 h) hz₁ne
    · rw [← h, ofAdd_toAdd]
  have hV : vPlus L T = conjClosure (quasithinOmegaOneCenter T) L := by
    show conjClosure (quasithinOmegaOneCenter T) (mPlus L T) = _
    rw [c.mPlus_eq]
  have hZV : ∀ a ∈ quasithinOmegaOneCenter T, a ∈ vPlus L T := fun a ha => by
    rw [hV]
    exact le_conjClosure _ _ ha
  have hcomm : ∀ a ∈ quasithinOmegaOneCenter T, ∀ b ∈ ⁅vPlus L T, L⁆, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.1 hc ⟨a, hZV a ha⟩ ⟨b, hWV hb⟩)
  have hTZN : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    fun t ht => Subgroup.centralizer_le_normalizer _
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht)
  have hTN : T ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hTL (hTZN.trans (F7.normalizer_le_normalizer_centralizer _))
  have hYC : oTwoUpper H ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    show Subgroup.closure {x | x ∈ H ∧ Odd (orderOf x)} ≤ _
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hyC : y ∈ (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T := by
      rw [← c.hH]
      exact hy.1
    exact mem_of_odd_orderOf_of_le_sup c.nf.hyp.sylow.1 hTN hyC hy.2
  have hαP2 : ∀ n : ↥L, (n : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      α n ∈ L3321.P2 := by
    intro n hn
    have h1 : (n : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mem_inf.2 ⟨n.2, hn⟩
    rw [hCZ] at h1
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.1 h1
    rwa [show y = n from Subtype.ext hyn] at hy
  have hVYS : ⁅vPlus L T, oTwoUpper H⁆ ≤ e5Sub hLV Dm := by
    refine Subgroup.commutator_le.2 fun m hm n hn => ?_
    obtain ⟨hnL, hnCent⟩ := Subgroup.mem_inf.1 (hYC hn)
    obtain ⟨z, hz, w, hw, hzw⟩ := e5_exists_mul_sup_comm hcomm (c.vPlus_le_omegaOne_sup hm)
    have hmn : ⁅z * w, n⁆ = ⁅w, n⁆ :=
      e5_comm_mul_left (hcomm z hz w hw) (Subgroup.mem_centralizer_iff.1 hnCent z hz)
    rw [← hzw, hmn]
    exact e5_mem_Sub hLV Dm |>.2 ⟨Subgroup.commutator_mem_commutator (hWV hw) hnL,
      e5wc_comm_P2 hLV Dm α hαv ⟨n, hnL⟩ (hαP2 ⟨n, hnL⟩ hnCent) ⟨w, hw⟩⟩
  refine Subgroup.commutator_le.2 fun x hx r hr => ?_
  obtain ⟨hxW, hxk⟩ := (e5_mem_Sub hLV Dm).1 (hVYS hx)
  obtain ⟨l, hlU, qq, hqq, rfl⟩ := A2Cfg.R_le_liftU2_mul_Q h9 hGA c hαs hαk hCZ r hr
  have hxV : x ∈ vPlus L T := hWV hxW
  have hcq : Commute qq x := Subgroup.mem_centralizer_iff.1 (hVC hxV).2 qq hqq
  have hqxi : qq * x⁻¹ * qq⁻¹ = x⁻¹ := by
    have h1 := hcq.inv_right.eq
    rw [h1]
    group
  have hcommRes : ⁅x, (l : G) * qq⁆ = ⁅x, (l : G)⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc x * ((l : G) * qq) * x⁻¹ * ((l : G) * qq)⁻¹
        = x * (l : G) * (qq * x⁻¹ * qq⁻¹) * (l : G)⁻¹ := by group
      _ = x * (l : G) * x⁻¹ * (l : G)⁻¹ := by rw [hqxi]
  rw [hcommRes]
  have hmem : ⁅x, (l : G)⁆ ∈ ⁅vPlus L T, L⁆ := Subgroup.commutator_mem_commutator hxV l.2
  have hcoord : ∀ j, j ≠ k₀ →
      e5wc (e5Phi hLV Dm ⟨⁅x, (l : G)⁆, hmem⟩) j = 0 :=
    fun j hj => e5wc_comm_U2 hLV Dm α hαv l hlU ⟨x, hxW⟩ hxk j hj
  rcases e5_eq_zero_or_single _ hcoord with h0 | h1
  · have h2 : e5Phi hLV Dm ⟨⁅x, (l : G)⁆, hmem⟩ = 1 :=
      e5_eq_of_wc (by rw [h0, e5wc_one])
    have h3 : (⟨⁅x, (l : G)⁆, hmem⟩ : ↥(⁅vPlus L T, L⁆ : Subgroup G)) = 1 :=
      hinj (h2.trans (map_one _).symm)
    have h4 : ⁅x, (l : G)⁆ = 1 := congrArg Subtype.val h3
    rw [h4]
    exact (quasithinOmegaOneCenter T).one_mem
  · have h2 : e5Phi hLV Dm ⟨⁅x, (l : G)⁆, hmem⟩ = e5Phi hLV Dm ⟨z₀, hz₀W⟩ := by
      rw [hz₁Phi]
      apply e5_eq_of_wc
      rw [h1]
      show Pi.single k₀ 1 = B5FinWedge.wedgeCoord4
        (Multiplicative.toAdd (Multiplicative.ofAdd (B5FinWedge.wedgeBasis4 k₀)))
      rw [toAdd_ofAdd, B5FinWedge.wedgeCoord4_basis]
    have h3 : (⟨⁅x, (l : G)⁆, hmem⟩ : ↥(⁅vPlus L T, L⁆ : Subgroup G)) = ⟨z₀, hz₀W⟩ :=
      hinj h2
    have h4 : ⁅x, (l : G)⁆ = z₀ := congrArg Subtype.val h3
    rw [h4]
    exact hz₀Z

end CFSG.Quasithin.H13.NFa2
