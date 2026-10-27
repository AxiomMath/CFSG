module

public import CFSG.Quasithin.MS93.S4A441XS
public import CFSG.Quasithin.MS93.S4A441D
import CFSG.Quasithin.MS93.S46Gen
import CFSG.Quasithin.MS93.S46I463
import CFSG.Quasithin.MS93.S46Ker
import CFSG.Quasithin.MS93.S4A432F
import CFSG.Quasithin.MS93.S4A42Coc
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.Background.HConj
import CFSG.Quasithin.Background.SmithB51SL3A

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

private theorem mem_span_of_le_orthN {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) {y₀ y : Fin 3 → F} (hy₀ : y₀ ≠ 0) (h₀ : P ≤ orthN y₀)
    (h : P ≤ orthN y) : y ∈ Submodule.span F {y₀} := by
  have hP0 : orthN y₀ = P := eq_of_le_of_finrank_eq_two h₀ hP (orthN_ne_top hy₀)
  obtain ⟨i, hi⟩ : ∃ i, y₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy₀ (funext hcon)
  have key : ∀ x : Fin 3 → F, y ⬝ᵥ x = (y i / y₀ i) * (y₀ ⬝ᵥ x) := by
    intro x
    set t := (y₀ ⬝ᵥ x) / y₀ i with ht
    have hx : x - t • Pi.single i 1 ∈ orthN y₀ := by
      show y₀ ⬝ᵥ (x - t • Pi.single i 1) = 0
      rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, ht,
        div_mul_cancel₀ _ hi, sub_self]
    have hx' : y ⬝ᵥ (x - t • Pi.single i 1) = 0 := h (hP0 ▸ hx)
    rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
      sub_eq_zero] at hx'
    rw [hx', ht]
    ring
  rw [Submodule.mem_span_singleton]
  refine ⟨y i / y₀ i, funext fun j => ?_⟩
  have := key (Pi.single j 1)
  rw [dotProduct_single, mul_one, dotProduct_single, mul_one] at this
  rw [Pi.smul_apply, smul_eq_mul, this]

private theorem card_dual_fix_le [Finite F] {A : Subgroup (SL3 F)}
    (hA : 2 ≤ Module.finrank F (commN A)) (S : Set (Fin 3 → F))
    (hS : ∀ y ∈ S, ∀ g ∈ A, dualMat g *ᵥ y = y) : Nat.card S ≤ Nat.card F := by
  by_cases h0 : ∀ y ∈ S, y = 0
  · have hsub : S ⊆ {0} := fun y hy => h0 y hy
    calc Nat.card S ≤ Nat.card ({0} : Set (Fin 3 → F)) :=
          Nat.card_mono (Set.finite_singleton 0) hsub
      _ = 1 := Nat.card_unique
      _ ≤ Nat.card F := Nat.card_pos
  push Not at h0
  obtain ⟨y₀, hy₀S, hy₀⟩ := h0
  have h₀ : commN A ≤ orthN y₀ := commN_le_orthN (hS y₀ hy₀S)
  have hP : Module.finrank F (commN A) = 2 := by
    have h1 := Submodule.finrank_mono h₀
    have h2 : Module.finrank F (orthN y₀) < 3 := by
      have := Submodule.finrank_lt (orthN_ne_top hy₀)
      rwa [Module.finrank_fin_fun] at this
    omega
  have hsub : S ⊆ (Submodule.span F {y₀} : Set (Fin 3 → F)) := fun y hy =>
    mem_span_of_le_orthN hP hy₀ h₀ (commN_le_orthN (hS y hy))
  calc Nat.card S ≤ Nat.card (Submodule.span F {y₀} : Set (Fin 3 → F)) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ = Nat.card F := by
        change Nat.card ↥(Submodule.span F {y₀}) = Nat.card F
        rw [Module.natCard_eq_pow_finrank (K := F), finrank_span_singleton hy₀, pow_one]

end Lin

section Count

variable {Γ : Type} [Group Γ] {F : Type} [Field F] {L V K : Subgroup Γ}
  {α : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}

private theorem card_eq_of_natSec [Finite F] (N : NatSec L V K α dual) :
    Nat.card ↥V = Nat.card ↥K * Nat.card F ^ 3 := by
  have h1 := Subgroup.card_mul_index N.β.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr N.surj, Subgroup.card_top] at h1
  have hker : N.β.ker = K.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, N.ker v, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N.le).toEquiv] at h1
  rw [← h1, show Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (Fin 3 → F) from rfl,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

private theorem card_le_of_coord_mem (N : NatSec L V K α dual) {H : Subgroup Γ}
    (hKH : K ≤ H) (hHV : H ≤ V) {S : Set (Fin 3 → F)} [Finite S]
    (hS : ∀ v ∈ H, N.coord v ∈ S) : Nat.card ↥H ≤ Nat.card ↥K * Nat.card S := by
  set f : ↥H →* Multiplicative (Fin 3 → F) := N.β.comp (Subgroup.inclusion hHV) with hf
  have hker : f.ker = K.subgroupOf H := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact N.ker (Subgroup.inclusion hHV v)
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h1
  rw [← h1]
  refine Nat.mul_le_mul_left _ ?_
  have hmem : ∀ r : ↥f.range, Multiplicative.toAdd (r : Multiplicative (Fin 3 → F)) ∈ S := by
    rintro ⟨_, v, rfl⟩
    have := hS v v.2
    rwa [N.coord_of_mem (hHV v.2)] at this
  refine Nat.card_le_card_of_injective (fun r => ⟨_, hmem r⟩) fun r s hrs => ?_
  have h2 := congrArg (fun t : S => (t : Fin 3 → F)) hrs
  exact Subtype.ext (Multiplicative.toAdd.injective h2)

end Count

section Grp

variable {Γ : Type*} [Group Γ]

private def commSubL (V A B : Subgroup Γ) (hVB : V ≤ Subgroup.normalizer (B : Set Γ)) :
    Subgroup Γ where
  carrier := {v | v ∈ V ∧ ∀ a ∈ A, ⁅v, a⁆ ∈ B}
  mul_mem' := by
    rintro v w ⟨hv, hvA⟩ ⟨hw, hwA⟩
    refine ⟨V.mul_mem hv hw, fun a ha => ?_⟩
    have e : ⁅v * w, a⁆ = v * ⁅w, a⁆ * v⁻¹ * ⁅v, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVB hv) _).mp (hwA a ha)) (hvA a ha)
  one_mem' := ⟨V.one_mem, fun a _ => by rw [commutatorElement_one_left]; exact B.one_mem⟩
  inv_mem' := by
    rintro v ⟨hv, hvA⟩
    refine ⟨V.inv_mem hv, fun a ha => ?_⟩
    have e : ⁅v⁻¹, a⁆ = v⁻¹ * ⁅v, a⁆⁻¹ * v⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hVB (V.inv_mem hv)) _).mp (B.inv_mem (hvA a ha))

private theorem commutator_sup_le_of' {A₁ A₂ Y N : Subgroup Γ}
    (h₁ : A₁ ≤ Subgroup.normalizer (N : Set Γ)) (h₂ : A₂ ≤ Subgroup.normalizer (N : Set Γ))
    (hA₁ : ⁅A₁, Y⁆ ≤ N) (hA₂ : ⁅A₂, Y⁆ ≤ N) : ⁅A₁ ⊔ A₂, Y⁆ ≤ N := by
  have hK : A₁ ⊔ A₂ ≤ commSubL (A₁ ⊔ A₂) Y N (sup_le h₁ h₂) :=
    sup_le (fun v hv => ⟨Subgroup.mem_sup_left hv, fun y hy =>
      hA₁ (Subgroup.commutator_mem_commutator hv hy)⟩) (fun v hv => ⟨Subgroup.mem_sup_right hv,
      fun y hy => hA₂ (Subgroup.commutator_mem_commutator hv hy)⟩)
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hK hv).2 y hy

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

private theorem vv_le_stab_of_dist' {ν ρ : Vtx 𝔛} (hν : IsMVtx 𝔛 ν)
    (hd : (puAmalgam h.le).treeGraph.dist ν ρ + 2 ≤ critDist 𝔛) : Vv 𝔛 ν ≤ stab 𝔛 ρ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm h hν hρ'
  refine hle.trans ?_
  by_cases hQ : ZM 𝔛 γ ≤ Qv 𝔛 ρ
  · exact hQ.trans (qv_le_stab _ ρ)
  · have t := dist_triangle 𝔛 γ ν ρ
    rw [tdist_comm _ γ ν] at t
    have hdγρ : (puAmalgam h.le).treeGraph.dist γ ρ = critDist 𝔛 := by
      by_contra hne
      exact hQ (zm_le_qv_of_dist_lt _ hγ (by omega))
    exact zm_le_stab_right _ h20 hb0 hC ⟨hγ, hdγρ, hQ⟩

include hφ

theorem vcirc_le_of_good (hb : 4 < critDist 𝔛)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    {α₀ β₀ γ₀ : Vtx 𝔛} (hα₀ : IsMVtx 𝔛 α₀) (hγ₀ : IsMVtx 𝔛 γ₀) (hαβ₀ : 𝔄 α₀ β₀)
    (hβγ₀ : 𝔄 β₀ γ₀)
    (hex : ∀ g : 𝔘, ⁅ZM 𝔛 (g • α₀), Qv 𝔛 (g • γ₀)⁆ = Usup 𝔛 (g • α₀) (g • β₀) ∧
      Usup 𝔛 (g • α₀) (g • β₀) = Usup 𝔛 (g • γ₀) (g • β₀))
    {μ μ' : Vtx 𝔛} (hc : IsCritical 𝔛 μ μ')
    (hgood : Qv 𝔛 (geo 𝔛 μ μ' 3) ⊓ Subgroup.centralizer (Usup 𝔛 μ (geo 𝔛 μ μ' 1) : Set 𝔘) ≤
      Qv 𝔛 (geo 𝔛 μ μ' 2))
    {ν : Vtx 𝔛} (hνdef : geo 𝔛 μ μ' 2 = ν)
    {ψ : ↥(stab 𝔛 ν) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 ν) (Uloc h.le L ν) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : L441.IsSecD h.le L ν ψ true (conjCl (stab 𝔛 ν) (ZM 𝔛 μ)) C) :
    Vcirc h.le L ν ≤ conjCl (stab 𝔛 ν) (ZM 𝔛 μ) := by
  classical
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hμ : IsMVtx 𝔛 μ := hc.1
  have hμ' : IsMVtx 𝔛 μ' := hc'.1
  have hd : (puAmalgam h.le).treeGraph.dist μ μ' = critDist 𝔛 := hc.2.1
  have hν : IsMVtx 𝔛 ν := hνdef ▸ isMVtx_geo_two _ h20 hb0 hc
  have hdνμ' : (puAmalgam h.le).treeGraph.dist ν μ' = critDist 𝔛 - 2 := by
    rw [← hνdef, dist_geo_right _ (by omega), hd]
  set W := conjCl (stab 𝔛 ν) (ZM 𝔛 μ)
  obtain ⟨hUC, hCst, -, hWC, -⟩ := hs
  set NC := NatSec.ofIsSum hWC
  obtain ⟨hR3, g₁, g₂, hg₁, hg₂, hn₁, hn₂, hR3le⟩ :=
    card_inf_centralizer_of_good h hφ hb hV hα₀ hγ₀ hαβ₀ hβγ₀ hex hc hgood
  rw [hνdef] at hn₁ hn₂ hR3le
  set R₃ := Uloc h.le L μ' ⊓ Subgroup.centralizer (ZM 𝔛 μ : Set 𝔘)
  have hcrit : ∀ g : 𝔘, g • γ₀ = μ' → ¬ ZM 𝔛 (g • α₀) ≤ Qv 𝔛 ν →
      IsCritical 𝔛 ν (g • α₀) := by
    intro g hgγ hgn
    have hμ'ρ : 𝔄 μ' (g • β₀) := by
      rw [← hgγ]
      exact (adj_smul _ g γ₀ β₀).mpr hβγ₀.symm
    have hρδ : 𝔄 (g • β₀) (g • α₀) := (adj_smul _ g β₀ α₀).mpr hαβ₀.symm
    have hδ : IsMVtx 𝔛 (g • α₀) := (isMVtx_smul _ g α₀).mpr hα₀
    have hdδν : (puAmalgam h.le).treeGraph.dist (g • α₀) ν = critDist 𝔛 := by
      have t := dist_triangle 𝔛 (g • α₀) μ' ν
      have t1 : (puAmalgam h.le).treeGraph.dist (g • α₀) μ' ≤ 2 := by
        have := dist_triangle 𝔛 (g • α₀) (g • β₀) μ'
        rw [dist_eq_one_of_adj _ hρδ.symm, dist_eq_one_of_adj _ hμ'ρ.symm] at this
        exact this
      rw [tdist_comm _ μ' ν, hdνμ'] at t
      by_contra hne
      exact hgn (zm_le_qv_of_dist_lt _ hδ (by omega))
    exact ms22_iii _ h20 hb0 hC ⟨hδ, hdδν, hgn⟩
  have hcδ₁ := hcrit g₁ hg₁ hn₁
  have hcδ₂ := hcrit g₂ hg₂ hn₂
  have hZs : ∀ g : 𝔘, IsCritical 𝔛 ν (g • α₀) → ZM 𝔛 (g • α₀) ≤ stab 𝔛 ν := fun g hcg =>
    (zm_le_qv_geo_one _ h20 hb0 hcg).trans
      (qv_le_stab_of_adj _ (adj_geo_one_of_isCritical _ hb0 hcg).symm)
  have hZ₁s := hZs g₁ hcδ₁
  have hZ₂s := hZs g₂ hcδ₂
  set A := ZM 𝔛 (g₁ • α₀) ⊔ ZM 𝔛 (g₂ • α₀)
  have hAs : A ≤ stab 𝔛 ν := sup_le hZ₁s hZ₂s
  have hνs := finite_stab h hν
  have hQs : Qv 𝔛 ν ≤ stab 𝔛 ν := qv_le_stab _ ν
  have hUs : Uloc h.le L ν ≤ stab 𝔛 ν :=
    (uloc_le_zm h hfull hν).trans ((zm_le_qv_self _ hν hb0).trans hQs)
  have hDn := stab_le_normalizer_dloc h ν
  have hUn := stab_le_normalizer_uloc h ν
  have hVn := stab_le_normalizer_vv h ν
  have hVs : Vv 𝔛 ν ≤ stab 𝔛 ν := (vv_le_qv h (by omega) hν).trans hQs
  have hVab := vv_comm_eq_bot h hb hν
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hVab
  have hdνμ : (puAmalgam h.le).treeGraph.dist ν μ ≤ 2 := by
    rw [← hνdef, tdist_comm, dist_geo _ (by omega)]
  have hZμV : ZM 𝔛 μ ≤ Vv 𝔛 ν := by
    have := zv_le_vv h (α := ν) (ρ := μ) hdνμ
    rwa [zv_of_isMVtx _ hμ] at this
  have hWV : W ≤ Vv 𝔛 ν := L441.conjCl_le_of_le_normalizer' hZμV hVn
  have hWn : stab 𝔛 ν ≤ Subgroup.normalizer (W : Set 𝔘) := le_normalizer_conjCl _ _
  have hCW : C ≤ W := NC.le
  have hCn : stab 𝔛 ν ≤ Subgroup.normalizer (C : Set 𝔘) := by
    have key : ∀ l ∈ stab 𝔛 ν, ∀ c ∈ C, l * c * l⁻¹ ∈ C := by
      intro l hl c hc
      have hcW := hCW hc
      have h1 := NC.coord_conj ⟨l, hl⟩ hcW
      rw [(NC.coord_eq_zero_iff hcW).mpr hc, Matrix.mulVec_zero] at h1
      exact (NC.coord_eq_zero_iff (NC.conj_mem ⟨l, hl⟩ hcW)).mp h1
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key l hl c, fun h' => ?_⟩
    have := key l⁻¹ (inv_mem hl) _ h'
    simpa [mul_assoc] using this
  have hUDW : ∀ x ∈ Uloc h.le L ν ⊔ Dloc h.le L ν, x ∈ W → x ∈ C := by
    intro x hx hxW
    have hDWC := L441.dloc_inf_le_of_isSum h hfull hν hψs hψ hWC
    have hx' : x ∈ ((Uloc h.le L ν ⊔ Dloc h.le L ν : Subgroup 𝔘) : Set 𝔘) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)] at hx'
    obtain ⟨u, hu, d, hd', hud⟩ := hx'
    have hud' : u * d = x := hud
    have hdW : d ∈ W := by
      have e : d = u⁻¹ * x := by rw [← hud']; group
      rw [e]
      exact W.mul_mem (W.inv_mem (hCW (hUC hu))) hxW
    rw [← hud']
    exact C.mul_mem (hUC hu) (hDWC ⟨hd', hdW⟩)
  have hRU : ∀ g : 𝔘, IsCritical 𝔛 ν (g • α₀) → ZM 𝔛 (g • α₀) ≤ A →
      ⁅ZM 𝔛 ν, ZM 𝔛 (g • α₀)⁆ ≤ ⁅Uloc h.le L ν, A⁆ ⊓ Uloc h.le L ν := by
    intro g hcg hgA
    have hZgs := hZs g hcg
    rw [commutator_zm_eq_uloc h hfull hν hZgs]
    exact le_inf (Subgroup.commutator_mono le_rfl hgA)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZgs.trans hUn))
  have hR3U : R₃ ≤ ⁅Uloc h.le L ν, A⁆ ⊓ Uloc h.le L ν :=
    hR3le.trans (sup_le (hRU g₁ hcδ₁ le_sup_left) (hRU g₂ hcδ₂ le_sup_right))
  have hZVQ : ∀ g : 𝔘, g • γ₀ = μ' → IsCritical 𝔛 ν (g • α₀) →
      ⁅ZM 𝔛 (g • α₀), Vv 𝔛 ν ⊓ Qv 𝔛 μ'⁆ ≤ R₃ := by
    intro g hgγ hcg
    have hμ'ρ : 𝔄 μ' (g • β₀) := by
      rw [← hgγ]
      exact (adj_smul _ g γ₀ β₀).mpr hβγ₀.symm
    obtain ⟨hex1, hex2⟩ := hex g
    rw [hgγ] at hex1 hex2
    refine le_inf ?_ ?_
    · calc ⁅ZM 𝔛 (g • α₀), Vv 𝔛 ν ⊓ Qv 𝔛 μ'⁆ ≤ ⁅ZM 𝔛 (g • α₀), Qv 𝔛 μ'⁆ :=
            Subgroup.commutator_mono le_rfl inf_le_right
        _ = Usup 𝔛 μ' (g • β₀) := hex1.trans hex2
        _ ≤ Uloc h.le L μ' := S4A.usup_le_uloc h hφ hμ' hμ'ρ
    · calc ⁅ZM 𝔛 (g • α₀), Vv 𝔛 ν ⊓ Qv 𝔛 μ'⁆ ≤ ⁅ZM 𝔛 (g • α₀), Vv 𝔛 ν⁆ :=
            Subgroup.commutator_mono le_rfl inf_le_left
        _ ≤ Vv 𝔛 ν := by
            rw [Subgroup.commutator_comm]
            exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((hZs g hcg).trans hVn)
        _ ≤ Subgroup.centralizer (ZM 𝔛 μ : Set 𝔘) := hVab.trans (Subgroup.centralizer_le hZμV)
  have hAVQ : ⁅A, Vv 𝔛 ν ⊓ Qv 𝔛 μ'⁆ ≤ C :=
    commutator_sup_le_of' (hZ₁s.trans hCn) (hZ₂s.trans hCn)
      (((hZVQ g₁ hg₁ hcδ₁).trans hR3U).trans (inf_le_right.trans hUC))
      (((hZVQ g₂ hg₂ hcδ₂).trans hR3U).trans (inf_le_right.trans hUC))
  set X := commSubL (Vv 𝔛 ν) A C (hVs.trans hCn)
  have hXV : X ≤ Vv 𝔛 ν := fun v hv => hv.1
  have hVQX : Vv 𝔛 ν ⊓ Qv 𝔛 μ' ≤ X := fun v hv => ⟨hv.1, fun a ha => by
    rw [← commutatorElement_inv]
    exact C.inv_mem (hAVQ (Subgroup.commutator_mem_commutator ha hv))⟩
  have hCX : C ≤ X := fun c hc => ⟨hWV (hCW hc), fun a ha => by
    refine hUDW _ (hCst (Subgroup.commutator_mem_commutator hc (hAs ha))) ?_
    have hcW := hCW hc
    have e : ⁅c, a⁆ = c * (a * c⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hcW ((Subgroup.mem_normalizer_iff.mp (hWn (hAs ha)) _).mp (W.inv_mem hcW))⟩
  set S : Set (Fin 3 → F) := {y | ∀ g ∈ natImage ψ A, dualMat g *ᵥ y = y}
  have hWXS : ∀ w ∈ W ⊓ X, NC.coord w ∈ S := by
    rintro w ⟨hwW, hwX⟩ g hg
    obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
    have h1 := NC.coord_conj a hwW
    rw [natAct_true] at h1
    rw [← h1]
    have hca : ⁅(a : 𝔘), w⁆ ∈ C := by
      rw [← commutatorElement_inv]
      exact C.inv_mem (hwX.2 _ haA)
    have e : (a : 𝔘) * w * (a : 𝔘)⁻¹ = ⁅(a : 𝔘), w⁆ * w := by
      simp only [commutatorElement_def]; group
    have hcaW : ⁅(a : 𝔘), w⁆ ∈ W := hCW hca
    rw [e, NC.coord_mul hcaW hwW, (NC.coord_eq_zero_iff hcaW).mpr hca, zero_add]
  have hrank : 2 ≤ Module.finrank F (commN (natImage ψ A)) := by
    have hinj : Function.Injective (fun x : ↥R₃ =>
        (⟨natVec hψ ⟨x, (hR3U x.2).2⟩, (mem_commutator_iff_natVec hψ hAs
          ⟨x, (hR3U x.2).2⟩).mp (hR3U x.2).1⟩ : ↥(commN (natImage ψ A)))) := by
      intro x y hxy
      have := natVec_injective hψ (congrArg (fun t : ↥(commN (natImage ψ A)) =>
        (t : Fin 3 → F)) hxy)
      exact Subtype.ext (congrArg (fun u : ↥(Uloc h.le L ν) => (u : 𝔘)) this)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hR3, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Fintype.card F ^ Module.finrank F (commN (natImage ψ A)) ≤ Fintype.card F ^ 1 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : Fintype.card F ^ 1 < Fintype.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hfinV : Finite ↥(Vv 𝔛 ν) := Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hfinW : Finite ↥W :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hWV.trans hVs))
  have hfinC : Finite ↥C :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((hCW.trans hWV).trans hVs))
  have hfinX : Finite ↥X :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hXV.trans hVs))
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hμ'
  have hVs' : Vv 𝔛 ν ≤ stab 𝔛 μ' := vv_le_stab_of_dist' h hν (by omega)
  have hrel : (Qv 𝔛 μ').relIndex (Vv 𝔛 ν) ≤ Fintype.card F ^ 2 := by
    rw [← S46.card_natImage_eq_relIndex h hφ hμ' hψ' hVs', ← Nat.card_eq_fintype_card]
    refine S46.card_le_of_elemAb_SL3 (fun g hg => ?_) (fun g hg g' hg' => ?_)
    · obtain ⟨a, haV, rfl⟩ := mem_natImage.mp hg
      have ha2 : a * a = 1 := Subtype.ext (by
        show (a : 𝔘) * a = 1
        rw [← sq]
        exact (S45.isElemAbelian_vi _ h20 hb0 (δ := ν) (i := 2) (by omega)).2 _ haV)
      rw [← map_mul, ha2, map_one]
    · obtain ⟨a, haV, rfl⟩ := mem_natImage.mp hg
      obtain ⟨b, hbV, rfl⟩ := mem_natImage.mp hg'
      have hab : a * b = b * a :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hVab haV) _ hbV).symm
      rw [← map_mul, ← map_mul, hab]
  have hVX : Nat.card ↥(Vv 𝔛 ν) ≤ Fintype.card F ^ 2 * Nat.card ↥X := by
    rw [← Subgroup.relIndex_mul_card (Qv 𝔛 μ') (Vv 𝔛 ν)]
    refine Nat.mul_le_mul hrel (Subgroup.card_le_of_le ?_)
    rw [inf_comm]
    exact hVQX
  have hWcard : Nat.card ↥W = Nat.card ↥C * Fintype.card F ^ 3 := by
    rw [card_eq_of_natSec NC, Nat.card_eq_fintype_card (α := F)]
  have hSq : Nat.card S ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact card_dual_fix_le hrank S fun y hy g hg => hy g hg
  have hWXc : Nat.card ↥(W ⊓ X) ≤ Nat.card ↥C * Fintype.card F :=
    (card_le_of_coord_mem NC (le_inf hCW hCX) inf_le_left hWXS).trans
      (Nat.mul_le_mul_left _ hSq)
  have hsup := L441.card_sup_mul_card_inf (A := W) (B := X) ((hXV.trans hVs).trans hWn)
  have hle : Nat.card ↥(Vv 𝔛 ν) ≤ Nat.card ↥(W ⊔ X) := by
    have hCpos : 0 < Nat.card ↥C := Nat.card_pos
    have key : Nat.card ↥C * Fintype.card F * (Fintype.card F ^ 2 * Nat.card ↥X) ≤
        Nat.card ↥C * Fintype.card F * Nat.card ↥(W ⊔ X) := by
      calc Nat.card ↥C * Fintype.card F * (Fintype.card F ^ 2 * Nat.card ↥X) =
            Nat.card ↥W * Nat.card ↥X := by rw [hWcard]; ring
        _ = Nat.card ↥(W ⊔ X) * Nat.card ↥(W ⊓ X) := hsup.symm
        _ ≤ Nat.card ↥(W ⊔ X) * (Nat.card ↥C * Fintype.card F) := Nat.mul_le_mul_left _ hWXc
        _ = Nat.card ↥C * Fintype.card F * Nat.card ↥(W ⊔ X) := by ring
    exact hVX.trans (Nat.le_of_mul_le_mul_left key (Nat.mul_pos hCpos (by omega)))
  have hWX : W ⊔ X = Vv 𝔛 ν := Subgroup.eq_of_le_of_card_ge (sup_le hWV hXV) hle
  have hVZ : ⁅Vv 𝔛 ν, ZM 𝔛 (g₁ • α₀)⁆ ≤ W := by
    have hY : W ⊔ X ≤ commSubL (Vv 𝔛 ν) (ZM 𝔛 (g₁ • α₀)) W (hVs.trans hWn) := by
      refine sup_le (fun w hw => ⟨hWV hw, fun a ha => ?_⟩) (fun x hx => ⟨hx.1, fun a ha =>
        hCW (hx.2 a ((le_sup_left : ZM 𝔛 (g₁ • α₀) ≤ A) ha))⟩)
      have e : ⁅w, a⁆ = w * (a * w⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hWn (hZ₁s ha)) _).mp (W.inv_mem hw))
    rw [hWX] at hY
    rw [Subgroup.commutator_le]
    intro v hv a ha
    exact (hY hv).2 a ha
  show ⁅Vv 𝔛 ν, Ltil h.le L ν⁆ ≤ W
  exact S46.commutator_ltil_le_of_commutator_le h hfull hν (adj_geo_one_of_isCritical _ hb0 hcδ₁)
    hVn hWn hVZ (zm_le_qv_geo_one _ h20 hb0 hcδ₁) hn₁

end Vertex

end CFSG.Quasithin.MS93.S4A.X441
