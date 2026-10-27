module

public import CFSG.Quasithin.MS93.S4A441S
public import CFSG.Quasithin.MS93.S4A432D
public import CFSG.Quasithin.MS93.S4A44U
public import CFSG.Quasithin.MS93.S4A432N
public import CFSG.Quasithin.MS93.S4A44Stmt

public section

namespace CFSG.Quasithin.MS93.S4A.L441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

section Grp

variable {Γ : Type*} [Group Γ]

theorem card_sup_mul_card_inf {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) :
    Nat.card (A ⊔ B : Subgroup Γ) * Nat.card (A ⊓ B : Subgroup Γ) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set Γ)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup Γ, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N)
    (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

end Grp

section Row

variable {F : Type} [Field F]

theorem mem_of_rowLevi_invariant (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ g ∈ (rowLevi : Subgroup (SL3 F)), ∀ v ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ S)
    {v : Fin 3 → F} (hvS : v ∈ S) (hv0 : v 0 ≠ 0) {w : Fin 3 → F} (hw0 : w 0 = 0) : w ∈ S := by
  have hg : rootElt 1 0 (w 1 / v 0) * rootElt 2 0 (w 2 / v 0) ∈ (rowLevi : Subgroup (SL3 F)) :=
    Subgroup.mul_mem _ (rootElt_mem_rowLevi (by decide) (by decide) _)
      (rootElt_mem_rowLevi (by decide) (by decide) _)
  have h1 := hS _ hg v hvS
  have e : ((rootElt 1 0 (w 1 / v 0) * rootElt 2 0 (w 2 / v 0) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + w := by
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, rootElt_mulVec (by decide),
      rootElt_mulVec (by decide)]
    funext k
    fin_cases k
    · simp [hw0]
    · simp
      field_simp
    · simp
      field_simp
  rw [e] at h1
  have := S.sub_mem h1 hvS
  simpa using this

end Row

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem dual_point (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : IsSecD h.le L γ ψ true (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C)
    {x : 𝔘} (hx : x ∈ ZM 𝔛 α) {y₀ : 𝔘} (hy₀ : y₀ ∈ Qv 𝔛 γ) (hxy₀ : ⁅x, y₀⁆ ∉ Dloc h.le L γ) :
    ∃ ψ' : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F), Function.Surjective ψ' ∧
      ∃ hψ' : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ' false 1,
        (∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) ↔
          x⁻¹ * ((k : 𝔘) * x * (k : 𝔘)⁻¹) ∈ C) ∧
        Subgroup.closure {r | ∃ y ∈ Qv 𝔛 γ, ⁅x, y⁆ = r} = Usup 𝔛 α β ∧
        Usup 𝔛 α β ⊓ Dloc h.le L γ = ⊥ ∧
        ∀ u : ↥(Uloc h.le L γ), (u : 𝔘) ∈ Usup 𝔛 α β ⊔ Dloc h.le L γ ↔
          natVec hψ' u ∈ (coordZero 0 : Submodule F (Fin 3 → F)) := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨-, hCG, hWQ, hWC, hCK⟩ := hs
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h (by omega) hγ).trans hQs
  have hZαs : ZM 𝔛 α ≤ stab 𝔛 γ := hZαV.trans hVs
  have hUn : stab 𝔛 γ ≤ Subgroup.normalizer (Uloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hDs : Dloc h.le L γ ≤ stab 𝔛 γ := puTrans_le_stab h.le _ γ
  have hUZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h hfull hγ
  have hUs : Uloc h.le L γ ≤ stab 𝔛 γ := hUZ.trans ((zm_le_qv_self _ hγ hb0).trans hQs)
  have hUDQ := commutator_uloc_sup_dloc_qv_le h hfull hγ
  have hZD : Uloc h.le L γ ⊓ Dloc h.le L γ = ⊥ := by
    have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hφ.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]
  have hβH : ¬ IsMVtx 𝔛 β := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hRZ : Usup 𝔛 α β ≤ ZM 𝔛 α := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))
  have hRfin : Finite ↥(Usup 𝔛 α β) := by
    have := finite_qv _ h20 hβH
    have hle : Usup 𝔛 α β ≤ Qv _ β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact commutator_le_of_le ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hRq2 := card_usup_le_sq h hfull hφ hα hαβ
  have hRq : Nat.card ↥(Usup 𝔛 α β) < Fintype.card F ^ 3 := by
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hRs : Usup 𝔛 α β ≤ stab 𝔛 γ := hRZ.trans hZαs
  have hxR : ∀ y ∈ Qv 𝔛 γ, ⁅x, y⁆ ∈ Usup 𝔛 α β := by
    intro y hy
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator hx (qv_le_qv _ h20 hγ hβγ.symm hy)
  have hxW : x ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) := le_conjCl _ _ hx
  have hxC : x ∉ C := by
    intro hxC
    refine hxy₀ (commutator_mem_dloc_of_conj h hfull hφ hγ (hZαs hx) hUDQ (fun k hk => ?_)
      hRs (fun y hy => Subgroup.mem_sup_left (hxR y hy)) hRq
      (fun y hy => hWQ (Subgroup.commutator_mem_commutator hxW hy)) y₀ hy₀)
    have e : x⁻¹ * (k * x * k⁻¹) = ⁅x⁻¹, k⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    exact hCG (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxC) hk)
  obtain ⟨s₀, hs₀⟩ := exists_conjSL_dual hWC hxW hxC
  set ψ' := conjSL s₀ ψ with hψ'def
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hψ' := isSumOfNaturalModulesVia_conjSL hψ s₀
  refine ⟨ψ', hψ's, hψ', hs₀, ?_⟩
  have hF1 : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : 𝔘) * x * (k : 𝔘)⁻¹) ∈ Uloc h.le L γ ⊔ Dloc h.le L γ := fun k hk =>
    hCK x hxW k k.2 ((hs₀ k).mp hk)
  set R := Subgroup.closure {r | ∃ y ∈ Qv 𝔛 γ, ⁅x, y⁆ = r} with hRdef
  have hRU : R ≤ Usup 𝔛 α β := (Subgroup.closure_le _).mpr fun _ ⟨y, hy, hr⟩ => hr ▸ hxR y hy
  have hfinR : Finite ↥R := Finite.of_injective _ (Subgroup.inclusion_injective hRU)
  have hRsR : R ≤ stab 𝔛 γ := hRU.trans hRs
  have hRUD : R ≤ Uloc h.le L γ ⊔ Dloc h.le L γ := (Subgroup.closure_le _).mpr
    fun _ ⟨y, hy, hr⟩ => hr ▸ hWQ (Subgroup.commutator_mem_commutator hxW hy)
  have hkR : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ r ∈ R, (k : 𝔘) * r * (k : 𝔘)⁻¹ ∈ R ⊔ Dloc h.le L γ := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨y, hy, rfl⟩ := hr
      set k₀ : 𝔘 := (k : 𝔘)
      have hc := hF1 k hk
      have hy' : k₀ * y * k₀⁻¹ ∈ Qv 𝔛 γ :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ γ k.2) y).mp hy
      have hcD : ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ ∈ Dloc h.le L γ :=
        hUDQ (Subgroup.commutator_mem_commutator hc hy')
      have e : k₀ * ⁅x, y⁆ * k₀⁻¹ =
          (x * ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ * x⁻¹) * ⁅x, k₀ * y * k₀⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hDn (hZαs hx)) _).mp hcD)
        (Subgroup.subset_closure ⟨_, hy', rfl⟩)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : (k : 𝔘) * (a * b) * (k : 𝔘)⁻¹ =
          ((k : 𝔘) * a * (k : 𝔘)⁻¹) * ((k : 𝔘) * b * (k : 𝔘)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : (k : 𝔘) * a⁻¹ * (k : 𝔘)⁻¹ = ((k : 𝔘) * a * (k : 𝔘)⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hkRD : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ r ∈ R ⊔ Dloc h.le L γ, (k : 𝔘) * r * (k : 𝔘)⁻¹ ∈ R ⊔ Dloc h.le L γ := by
    intro k hk r hr
    have hle : (R ⊔ Dloc h.le L γ).map (MulAut.conj (k : 𝔘)).toMonoidHom ≤
        R ⊔ Dloc h.le L γ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hkR k hk a ha
      · rintro _ ⟨d, hd, rfl⟩
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDn k.2) d).mp hd)
    exact hle ⟨r, hr, by simp [MulAut.conj_apply]⟩
  set Tt := Uloc h.le L γ ⊓ (R ⊔ Dloc h.le L γ) with hTdef
  let Sc : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : ↥(Uloc h.le L γ), (u : 𝔘) ∈ Tt ∧ natVec hψ' u = v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', Tt.mul_mem hu hu', natVec_mul hψ' u u'⟩
      zero_mem' := ⟨1, Tt.one_mem, natVec_one hψ'⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, Tt.inv_mem hu, natVec_inv hψ' u⟩ }
  have hScinv : ∀ g ∈ (rowLevi : Subgroup (SL3 F)), ∀ v ∈ Sc,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Sc := by
    rintro g hg _ ⟨u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := toSL3_surjective hψ's g
    have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Uloc h.le L γ :=
      (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp u.2
    exact ⟨⟨_, hku⟩, ⟨hku, hkRD k hg _ hu.2⟩, natVec_conj hψ' k u ⟨_, hku⟩ rfl⟩
  have : Finite ↥(stab 𝔛 γ) := finite_stab h hγ
  have hfinT : Finite ↥Tt := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left.trans hUs))
  let f : ↥Tt → ↥Sc := fun t => ⟨natVec hψ' ⟨t, t.2.1⟩, ⟨⟨t, t.2.1⟩, t.2, rfl⟩⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro t t' htt
      have h1 : natVec hψ' ⟨t, t.2.1⟩ = natVec hψ' ⟨t', t'.2.1⟩ := congrArg Subtype.val htt
      have h2 := natVec_injective hψ' h1
      have h3 : (t : 𝔘) = t' := congrArg (fun z : ↥(Uloc h.le L γ) => (z : 𝔘)) h2
      exact Subtype.ext h3
    · rintro ⟨_, ⟨u, hu, rfl⟩⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hScT : Nat.card ↥Sc = Nat.card ↥Tt := (Nat.card_eq_of_bijective f hfbij).symm
  have hTR : Nat.card ↥Tt ≤ Nat.card ↥R := card_uloc_inf_sup_dloc_le h hfull hφ hγ hRsR
  have hRq' : Nat.card ↥R ≤ Fintype.card F ^ 2 := (Subgroup.card_le_of_le hRU).trans hRq2
  have hcard0 : Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)) = Fintype.card F ^ 2 := by
    rw [card_coordZero_zero, Nat.card_eq_fintype_card]
  have hSc0 : ∀ v ∈ Sc, v 0 = 0 := by
    intro v hvS
    by_contra hv0
    have hle : (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup ≤ Sc := fun w hw =>
      mem_of_rowLevi_invariant Sc hScinv hvS hv0 hw
    have hlt : (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup < Sc :=
      lt_of_le_of_ne hle fun heq => hv0 (show v ∈ (coordZero 0 : Submodule F (Fin 3 → F)) from
        (heq ▸ hvS : v ∈ (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup))
    have h1 := AddSubgroup.card_lt_of_lt hlt
    have h2 : Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup =
        Fintype.card F ^ 2 := hcard0
    omega
  have hm : ⁅x, y₀⁆ ∈ ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) :=
    hWQ (Subgroup.commutator_mem_commutator hxW hy₀)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn), Set.mem_mul] at hm
  obtain ⟨u₀, hu₀, d₀, hd₀, hud₀⟩ := hm
  have hu₀T : u₀ ∈ Tt := by
    refine ⟨hu₀, ?_⟩
    have : u₀ = ⁅x, y₀⁆ * d₀⁻¹ := by rw [← hud₀]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨y₀, hy₀, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd₀))
  have hu₀1 : (⟨u₀, hu₀⟩ : ↥(Uloc h.le L γ)) ≠ 1 := by
    intro h1
    have : u₀ = 1 := congrArg Subtype.val h1
    apply hxy₀
    rw [← hud₀, this, one_mul]
    exact hd₀
  have hScne : Sc ≠ ⊥ := by
    intro hbot
    have h1 : natVec hψ' ⟨u₀, hu₀⟩ ∈ Sc := ⟨⟨u₀, hu₀⟩, hu₀T, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at h1
    exact hu₀1 (natVec_injective hψ' (h1.trans (natVec_one hψ').symm))
  have hall := (rowLevi_invariant_cases Sc hScinv hSc0).resolve_left hScne
  have hScEq : Sc = (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup :=
    le_antisymm (fun v hv => hSc0 v hv) (fun v hv => hall v hv)
  have hTq : Nat.card ↥Tt = Fintype.card F ^ 2 := by
    rw [← hScT, hScEq]
    exact hcard0
  have hRUeq : R = Usup 𝔛 α β :=
    Subgroup.eq_of_le_of_card_ge hRU (by omega)
  have hRD : R ⊓ Dloc h.le L γ = ⊥ := by
    have hfinD : Finite ↥(Dloc h.le L γ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hDs)
    have hfinRD : Finite ↥(Dloc h.le L γ ⊔ R) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hDs hRsR))
    have hfinRD' : Finite ↥(R ⊔ Dloc h.le L γ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hRsR hDs))
    have hfinTD : Finite ↥(Tt ⊔ Dloc h.le L γ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le (inf_le_left.trans hUs) hDs))
    have hfinRiD : Finite ↥(R ⊓ Dloc h.le L γ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hDs))
    have h1 := card_sup_mul_card_inf (A := Dloc h.le L γ) (B := R) (hRsR.trans hDn)
    have hTD : Tt ⊓ Dloc h.le L γ = ⊥ := by
      rw [eq_bot_iff, ← hZD]
      exact inf_le_inf_right _ inf_le_left
    have h2 := card_mul_card_le_card_sup' hTD
    have h3 := Subgroup.card_le_of_le (sup_le inf_le_right le_sup_right :
      Tt ⊔ Dloc h.le L γ ≤ R ⊔ Dloc h.le L γ)
    have hcomm : Dloc h.le L γ ⊔ R = R ⊔ Dloc h.le L γ := sup_comm _ _
    have hcomm' : Dloc h.le L γ ⊓ R = R ⊓ Dloc h.le L γ := inf_comm _ _
    rw [hcomm, hcomm'] at h1
    have hpos : 0 < Nat.card ↥(Dloc h.le L γ) := Nat.card_pos
    have h4 : Nat.card ↥(R ⊓ Dloc h.le L γ) * (Nat.card ↥Tt * Nat.card ↥(Dloc h.le L γ)) ≤
        Nat.card ↥R * Nat.card ↥(Dloc h.le L γ) := by
      calc Nat.card ↥(R ⊓ Dloc h.le L γ) * (Nat.card ↥Tt * Nat.card ↥(Dloc h.le L γ))
          ≤ Nat.card ↥(R ⊓ Dloc h.le L γ) * Nat.card ↥(R ⊔ Dloc h.le L γ) :=
            Nat.mul_le_mul_left _ (h2.trans h3)
        _ = Nat.card ↥R * Nat.card ↥(Dloc h.le L γ) := by rw [mul_comm, h1, mul_comm]
    have h4' : Nat.card ↥(R ⊓ Dloc h.le L γ) * Nat.card ↥Tt * Nat.card ↥(Dloc h.le L γ) ≤
        Nat.card ↥R * Nat.card ↥(Dloc h.le L γ) := by
      rw [mul_assoc]
      exact h4
    have h5 : Nat.card ↥(R ⊓ Dloc h.le L γ) * Nat.card ↥Tt ≤ Nat.card ↥R :=
      Nat.le_of_mul_le_mul_right h4' hpos
    have hR2 : Nat.card ↥R = Fintype.card F ^ 2 := by omega
    rw [hTq, hR2] at h5
    have hq2 : 0 < Fintype.card F ^ 2 := by positivity
    have h6 : Nat.card ↥(R ⊓ Dloc h.le L γ) ≤ 1 := by
      by_contra hne
      push Not at hne
      have : 2 * Fintype.card F ^ 2 ≤ Nat.card ↥(R ⊓ Dloc h.le L γ) * Fintype.card F ^ 2 :=
        Nat.mul_le_mul_right _ hne
      omega
    exact Subgroup.eq_bot_of_card_le _ h6
  rw [← hRUeq]
  refine ⟨rfl, hRD, fun u => ?_⟩
  constructor
  · intro hu
    have hT : (u : 𝔘) ∈ Tt := ⟨u.2, hu⟩
    have : natVec hψ' u ∈ Sc := ⟨u, hT, rfl⟩
    rw [hScEq] at this
    exact this
  · intro hu
    have : natVec hψ' u ∈ Sc := by
      rw [hScEq]
      exact hu
    obtain ⟨u', hu'T, hu'v⟩ := this
    have := natVec_injective hψ' hu'v
    rw [this] at hu'T
    exact hu'T.2

theorem dual_local (hC : CentHyp 𝔛) (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : IsSecD h.le L γ ψ true (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C) :
    Usup 𝔛 α β ⊓ Dloc h.le L γ = ⊥ ∧ ⁅Usup 𝔛 α β, Qv 𝔛 γ⁆ = ⊥ ∧
      Usup 𝔛 α β ⊔ Dloc h.le L γ = Usup 𝔛 γ β ⊔ Dloc h.le L γ := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hs' := hs
  obtain ⟨-, -, hWQ, -, -⟩ := hs'
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hUZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h hfull hγ
  have hUs : Uloc h.le L γ ≤ stab 𝔛 γ := hUZ.trans ((zm_le_qv_self _ hγ hb0).trans hQs)
  have hUDQ := commutator_uloc_sup_dloc_qv_le h hfull hγ
  have hTs : Qv 𝔛 β ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hβγ
  have hRZ : Usup 𝔛 α β ≤ ZM 𝔛 α := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))
  have hH' := hH
  rw [Subgroup.commutator_le] at hH'
  push Not at hH'
  obtain ⟨x, hx, y₀, hy₀, hxy₀⟩ := hH'
  obtain ⟨ψ', hψ's, hψ', hs₀, hR, hRD, hcoord⟩ :=
    dual_point h hfull hb hφ hα hγ hαβ hβγ hψs hψ hs hx hy₀ hxy₀
  have hxW : x ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) := le_conjCl _ _ hx
  have hRUD : Usup 𝔛 α β ≤ Uloc h.le L γ ⊔ Dloc h.le L γ := by
    rw [← hR]
    exact (Subgroup.closure_le _).mpr fun _ ⟨y, hy, hr⟩ =>
      hr ▸ hWQ (Subgroup.commutator_mem_commutator hxW hy)
  have hRQ : ⁅Usup 𝔛 α β, Qv 𝔛 γ⁆ = ⊥ := by
    rw [eq_bot_iff, ← hRD]
    refine le_inf ?_ ((Subgroup.commutator_mono hRUD le_rfl).trans hUDQ)
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_qv _ h20 hγ hβγ.symm).trans (qv_le_normalizer_usup h hαβ))
  refine ⟨hRD, hRQ, ?_⟩
  have hRC : Usup 𝔛 α β ≤ C := by
    intro r hr
    refine mem_of_commutator_mem_dloc h hfull hb hφ hα hγ hαβ hβγ hH hψs hs
      (le_conjCl _ _ (hRZ hr)) fun y hy => ?_
    have : ⁅r, y⁆ ∈ ⁅Usup 𝔛 α β, Qv 𝔛 γ⁆ := Subgroup.commutator_mem_commutator hr hy
    rw [hRQ, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  have hTrow : natImage ψ' (Qv 𝔛 β) ≤ (rowLevi : Subgroup (SL3 F)) := by
    intro g hg
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    refine (hs₀ t).mpr (hRC ?_)
    have e : x⁻¹ * ((t : 𝔘) * x * (t : 𝔘)⁻¹) = ⁅x⁻¹, (t : 𝔘)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hx) htT
  have hγβ : 𝔄 γ β := hβγ.symm
  have hcommW : commN (natImage ψ' (Qv 𝔛 β)) ≤ coordZero 0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, v, rfl⟩
    show (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) 0 = 0
    rw [Pi.sub_apply, rowLevi_mulVec_zero (hTrow hg), sub_self]
  have hcardC : Nat.card ↥(commN (natImage ψ' (Qv 𝔛 β))) = Nat.card F ^ 2 := by
    rw [← card_commutator_eq hψ' hTs, ← usup_eq_commutator_uloc h hfull hγ hγβ,
      card_usup_eq_sq h hφ hC hb hγ hγβ, Nat.card_eq_fintype_card]
  have hcommEq : commN (natImage ψ' (Qv 𝔛 β)) = coordZero 0 := by
    apply le_antisymm hcommW
    have hle : ((commN (natImage ψ' (Qv 𝔛 β))).toAddSubgroup) ≤
        (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup := hcommW
    have := AddSubgroup.eq_of_le_of_card_ge hle (by
      rw [show Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup =
        Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)) from rfl, card_coordZero_zero,
        show Nat.card ↥(commN (natImage ψ' (Qv 𝔛 β))).toAddSubgroup =
          Nat.card ↥(commN (natImage ψ' (Qv 𝔛 β))) from rfl, hcardC])
    intro v hv
    have : v ∈ (commN (natImage ψ' (Qv 𝔛 β))).toAddSubgroup := by
      rw [this]
      exact hv
    exact this
  have hiff : ∀ u : ↥(Uloc h.le L γ),
      (u : 𝔘) ∈ Usup 𝔛 α β ⊔ Dloc h.le L γ ↔ (u : 𝔘) ∈ Usup 𝔛 γ β := by
    intro u
    rw [hcoord u, usup_eq_commutator_uloc h hfull hγ hγβ, mem_commutator_iff_natVec hψ' hTs u,
      hcommEq]
  have hγU : Usup 𝔛 γ β ≤ Uloc h.le L γ := by
    rw [usup_eq_commutator_uloc h hfull hγ hγβ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hTs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ))
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) :=
      sup_le hRUD le_sup_right hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn), Set.mem_mul] at hv'
    obtain ⟨u, hu, d, hd, rfl⟩ := hv'
    have huR : u ∈ Usup 𝔛 α β ⊔ Dloc h.le L γ := by
      have : u = u * d * d⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hv (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd))
    exact Subgroup.mul_mem_sup (((hiff ⟨u, hu⟩).mp huR)) hd
  · refine sup_le (fun u hu => ?_) le_sup_right
    exact (hiff ⟨u, hγU hu⟩).mpr hu

end Vertex

end CFSG.Quasithin.MS93.S4A.L441
