module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenD

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def FactH11 : Prop :=
  ∀ {p₀ : Fin 5} {c : Fin 4 → ZMod 2}, c ≠ 0 →
    (∀ y : Perm (Fin 5), Perm.sign y = 1 → y * y = 1 → y p₀ = p₀ → CFSG.Quasithin.F53Mod.natAct y c = c) →
    ∀ {τ : Perm (Fin 5)}, CFSG.Quasithin.F53Mod.natAct τ c = c → τ p₀ = p₀

@[expose] def FactH12 : Prop :=
  ∀ {P : Subgroup (Perm (Fin 5))}, Nat.card P = 8 → ∀ {Y : Subgroup nat.W},
    (∀ σ ∈ P, ∀ y ∈ Y, nat.act σ y ∈ Y) → Nat.card Y ≤ 4 →
      Y ≤ fixW nat (P ⊓ alternatingGroup (Fin 5))

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem four_le_card_R : 4 ≤ Nat.card (⁅Vn β, Vn α'⁆ : Subgroup G) := by
  obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le
  have hys : y ∈ stab β := (hss114_d C.hA C.hb3 C.dist_beta).2.1 hyV
  have h4 := C.four_le_relIndex_commSec C.vtype_beta hys hyQ
  have hle : commSec (Subgroup.zpowers y) (F53B3.Cv β) (Vn β) ≤ ⁅Vn β, Vn α'⁆ ⊔ F53B3.Cv β :=
    sup_le_sup_right (Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hyV)) _
  have h1 := Subgroup.relIndex_le_of_le_right (H := F53B3.Cv β) hle
    (relIndex_ne_zero_of_finite _ _)
  have hCn : F53B3.Cv β ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ : Subgroup G) : Set G) := by
    refine fun c hc => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact isElemAbelian_comm (isElemAbelian_Vn C.hA C.hb3 β) (C.R_le_Vn_beta hx) hc.1
  rw [F112W.relIndex_sup_eq_relIndex_inf hCn] at h1
  have h2 := Subgroup.relIndex_mul_card (H := ⁅Vn β, Vn α'⁆ ⊓ F53B3.Cv β) (K := ⁅Vn β, Vn α'⁆)
  have hpos : 0 < Nat.card ↥(⁅Vn β, Vn α'⁆ ⊓ F53B3.Cv β ⊓ ⁅Vn β, Vn α'⁆) := Nat.card_pos
  nlinarith

theorem seven (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (hH7 : FactH7) (hH6 : FactH6 G) (hstar : StarSpec H M S)
    (hH11 : FactH11) (hH12 : FactH12) (P : CritPath α β α') : Wnn β ≤ stab P.γ := by
  by_contra hW
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hvγ := C.vtype_P_γ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hδγ : P.δ ∈ nbrs P.γ := mem_nbrs_comm hγ
  have hRV := C.R_le_Vn_of_not_le h4 hH8 h6 hI8 hH7 hH6 hstar P hW
  have hRI : ⁅Vn β, Vn α'⁆ ≤ Iv P.γ := by
    rw [← C.Iv_P_γ_eq P]; exact le_inf hRV C.R_le_Vn_alpha'
  obtain ⟨r, hr, hrC⟩ : ∃ r ∈ ⁅Vn β, Vn α'⁆, r ∉ F53B3.Cv P.δ := by
    by_contra hall
    push Not at hall
    have hRZ : ⁅Vn β, Vn α'⁆ ≤ Zv P.δ := by
      rw [← C.Iv_inf_Cv_eq hvγ hδγ]
      exact le_inf hRI hall
    have h1 := Subgroup.card_le_of_le hRZ
    rw [C.card_Zv_false hvδ] at h1
    have h2 := C.four_le_card_R
    omega
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hvδ
  have hD8 := C.card_map_edge hvδ hγ hθk
  obtain ⟨p₀, hp₀, -⟩ := exists_fix_trans_of_card_eight _ hD8
  obtain ⟨w, hwW, hwδ, hwp⟩ := C.exists_moves_point h4 hH8 P hW hθs hθk hp₀
  have hCV : F53B3.Cv P.δ ≤ Vn P.δ := inf_le_left
  have hIV : Iv P.γ ≤ Vn P.δ := Iv_le_Vn hδγ
  set Ibar := ((Iv P.γ).subgroupOf (Vn P.δ)).map
    (QuotientGroup.mk' ((F53B3.Cv P.δ).subgroupOf (Vn P.δ))) with hIbar
  set Y : Subgroup nat.W := Ibar.comap βm with hY
  have hYcard : Nat.card Y ≤ 4 := by
    have hYmap : Y.map βm = Ibar := Subgroup.map_comap_eq_self_of_surjective hsd.surj _
    have h1 : Nat.card Y = Nat.card Ibar := by
      rw [← hYmap, Subgroup.card_map_of_injective hsd.inj]
    rw [h1, hIbar, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
      Subgroup.relIndex_subgroupOf hIV]
    have h2 := Subgroup.relIndex_mul_card (H := F53B3.Cv P.δ) (K := Iv P.γ)
    have h3 : F53B3.Cv P.δ ⊓ Iv P.γ = Zv P.δ := by
      rw [inf_comm]; exact C.Iv_inf_Cv_eq hvγ hδγ
    rw [h3, C.card_Zv_false hvδ] at h2
    have h4' := hI8 C hvγ
    omega
  have hYinv : ∀ σ ∈ ((stab P.δ ⊓ stab P.γ).subgroupOf (stab P.δ)).map θ, ∀ y ∈ Y,
      nat.act σ y ∈ Y := by
    rintro _ ⟨g, hg, rfl⟩ y hy
    obtain ⟨x, hx, hxy⟩ := (show βm y ∈ Ibar from hy)
    have hxI : (x : G) ∈ Iv P.γ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hgx, hact⟩ := hsd.equiv g y x hxy.symm
    show βm (nat.act (θ g) y) ∈ Ibar
    rw [hact]
    have hgγ : (g : G) ∈ stab P.γ := (Subgroup.mem_subgroupOf.mp hg).2
    refine ⟨⟨_, hgx⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Iv P.γ hgγ) _).mp hxI
  have hYfix := hH12 hD8 hYinv hYcard
  have hrV : r ∈ Vn P.δ := hRV hr
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨r, hrV⟩ : ↥(Vn P.δ)))
  have huY : u ∈ Y := by
    show βm u ∈ Ibar
    rw [hu]
    exact ⟨⟨r, hrV⟩, Subgroup.mem_subgroupOf.mpr (hRI hr), rfl⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hu
    have := (QuotientGroup.eq_one_iff _).mp hu.symm
    exact hrC (Subgroup.mem_subgroupOf.mp this)
  have hwr : w * r * w⁻¹ = r := by
    have := (Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hwW)) r
      (C.R_le_Vn_beta hr)
    rw [← this]; group
  have hwu : nat.act (θ ⟨w, hwδ⟩) u = u := by
    obtain ⟨hwx, hact⟩ := hsd.equiv ⟨w, hwδ⟩ u ⟨r, hrV⟩ hu
    apply hsd.inj
    rw [hact, hu]
    congr 1
    exact Subtype.ext hwr
  set c : Fin 4 → ZMod 2 := Multiplicative.toAdd u with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hu1
    have : u = Multiplicative.ofAdd c := rfl
    rw [this, h]; rfl
  have hcT : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y * y = 1 → y p₀ = p₀ → CFSG.Quasithin.F53Mod.natAct y c = c := by
    intro y hs hsq hfix
    have hyT := (hH8 _ hD8 p₀ hp₀ y).mpr ⟨hs, hsq, hfix⟩
    have h := hYfix huY y hyT
    exact congrArg Multiplicative.toAdd h
  have hτ : CFSG.Quasithin.F53Mod.natAct (θ ⟨w, hwδ⟩) c = c := congrArg Multiplicative.toAdd hwu
  exact hwp (hH11 hc0 hcT hτ)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
