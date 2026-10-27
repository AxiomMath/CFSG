module

public import CFSG.Quasithin.Background.C124AsmFrattini
public import CFSG.Quasithin.Background.C124BlockLift
public import CFSG.Quasithin.Background.C124L2PMP
public import CFSG.Quasithin.Background.C124Star

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem Q_le_N : pCoreOf 2 X ≤ X ⊓ Subgroup.normalizer (baum R : Set G) :=
  le_inf (pCoreOf_le 2 X) (E.QR.trans E.R_le_normalizer_baum)

theorem autI_N :
    autI hV (X ⊓ Subgroup.normalizer (baum R : Set G)) =
      autI hV X ⊓ Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV))) := by
  apply le_antisymm
  · exact le_inf (autI_mono hV inf_le_left)
      (L2.autI_le_normalizer_of_le_normalizer hV inf_le_right)
  · intro φ hφ
    obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := (mem_autI hV).1 hφ.1
    obtain ⟨c, hc, n, hn, hxcn⟩ := E.frattini_star hxX hφ.2
    have hcn : convI hV ⟨x, hxN⟩ = convI hV ⟨n, E.hXN hn.1⟩ := by
      have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨c, E.hXN hc.1⟩ * ⟨n, E.hXN hn.1⟩ := Subtype.ext hxcn
      rw [h1, map_mul, (convI_eq_one_iff hV _).2 hc.2, one_mul]
    rw [hcn]
    exact convI_mem_autI hV hn _

theorem gen_lift {Ys : Subgroup (MulAut (IntMod V hV))} {Y : Subgroup G} (hYL : Y ≤ L)
    (hYs : Ys ≤ autI hV Y)
    (hgen : autI hV X = Ys ⊔ (autI hV X ⊓
      Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV))))) :
    X = Y ⊔ (X ⊓ Subgroup.normalizer (baum R : Set G)) := by
  set N₀ := X ⊓ Subgroup.normalizer (baum R : Set G) with hN₀
  set H := Y ⊔ N₀ with hH
  have hYX : Y ≤ X := hYL.trans E.hLX
  have hHX : H ≤ X := sup_le hYX inf_le_left
  have hQH : pCoreOf 2 X ≤ H := E.Q_le_N.trans le_sup_right
  have hautH : autI hV H = autI hV X := by
    apply le_antisymm (autI_mono hV hHX)
    calc autI hV X = Ys ⊔ (autI hV X ⊓
          Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV)))) := hgen
      _ = Ys ⊔ autI hV N₀ := by rw [E.autI_N]
      _ ≤ autI hV Y ⊔ autI hV N₀ := sup_le_sup_right hYs _
      _ = autI hV H := (autI_sup hV (hYX.trans E.hXN) (inf_le_left.trans E.hXN)).symm
  have hdec : ∀ x ∈ X, ∃ h ∈ H, x * h⁻¹ ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have : convI hV ⟨x, E.hXN hx⟩ ∈ autI hV H := hautH ▸ convI_mem_autI hV hx _
    obtain ⟨⟨h, hhN⟩, hhH, hhe⟩ := (mem_autI hV).1 this
    exact ⟨h, hhH, X.mul_mem hx (X.inv_mem (hHX hhH)),
      mul_inv_mem_centralizer (hV := hV) (E.hXN hx) hhN hhe.symm⟩
  have hQL : ((L ⊔ pCoreOf 2 X : Subgroup G) : Set G) = (L : Set G) * (pCoreOf 2 X : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L (pCoreOf 2 X)
      ((pCoreOf_le 2 X).trans E.normal)
  have hQC : pCoreOf 2 X ≤ X ⊓ Subgroup.centralizer (V : Set G) := E.Q_le_C
  have hLH : L ≤ H := by
    have key := L2P.le_of_perfect_of_prod (Y := L) (N := L ⊓ Subgroup.centralizer (V : Set G))
      (K' := L ⊓ H) E.perf inf_le_left ?_ ?_
    · exact fun l hl => (key hl).2
    · refine Subgroup.commutator_le.2 fun d hd l hl => ?_
      have hc := E.comm_C_L d ⟨E.hLX hd.1, hd.2⟩ l hl
      refine ⟨?_, hQH (E.pCoreOf_L_le_Q hc)⟩
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hd.1 hl) (L.inv_mem hd.1)) (L.inv_mem hl)
    · intro y hy
      obtain ⟨h, hhH, hc⟩ := hdec y (E.hLX hy)
      have hmem : y * h⁻¹ ∈ ((L ⊔ pCoreOf 2 X : Subgroup G) : Set G) := E.C_le_sup hc
      rw [hQL] at hmem
      obtain ⟨l₁, hl₁, q, hq, hlq⟩ := hmem
      have hlq' : l₁ * q = y * h⁻¹ := hlq
      have hl₁C : l₁ ∈ Subgroup.centralizer (V : Set G) := by
        have : l₁ = (y * h⁻¹) * q⁻¹ := by rw [← hlq']; group
        rw [this]
        exact Subgroup.mul_mem _ hc.2 (Subgroup.inv_mem _ (hQC hq).2)
      have hyk : y = l₁ * (q * h) := by
        calc y = (y * h⁻¹) * h := by group
          _ = l₁ * (q * h) := by rw [← hlq']; group
      refine ⟨l₁, ⟨hl₁, hl₁C⟩, q * h, ⟨?_, H.mul_mem (hQH hq) hhH⟩, hyk⟩
      have : q * h = l₁⁻¹ * y := by rw [hyk]; group
      rw [this]
      exact L.mul_mem (L.inv_mem hl₁) hy
  apply le_antisymm
  · intro x hx
    obtain ⟨h, hhH, hc⟩ := hdec x hx
    have hmem : x * h⁻¹ ∈ L ⊔ pCoreOf 2 X := E.C_le_sup hc
    have : x = (x * h⁻¹) * h := by group
    rw [this]
    exact H.mul_mem (sup_le hLH hQH hmem) hhH
  · exact hHX

theorem closure_lift {Y : Subgroup G} (hYL : Y ≤ L)
    (hnc : ∃ y ∈ Y, ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ Subgroup.centralizer (V : Set G)) :
    ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal → Y ≤ N → L ≤ N := by
  intro N hNL hNn hYN
  set σ := starHom hV L E.hLN with hσ
  have hσs : Function.Surjective σ := starHom_surjective hV E.hLN
  have hσk : ∀ x : ↥L, σ x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x hx => by
    have : x ∈ σ.ker := hx
    rw [ker_starHom hV E.hLN, Subgroup.mem_subgroupOf] at this
    exact this.2
  have hq := B1Red.isQuasisimple_to_open E.quasi
  set Nb := (N.subgroupOf L).map σ with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map hNn σ hσs
  have hNbtop : Nb = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq Nb with h | h
    · exfalso
      obtain ⟨y, hy, l, hl, hncl⟩ := hnc
      apply hncl
      have hyN : (⟨y, hYL hy⟩ : ↥L) ∈ N.subgroupOf L := hYN hy
      have hcent := Subgroup.mem_center_iff.1 (h ⟨_, hyN, rfl⟩) (σ ⟨l, hl⟩)
      have h2 : σ (⟨y, hYL hy⟩ * ⟨l, hl⟩ * ⟨y, hYL hy⟩⁻¹ * ⟨l, hl⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcent]
        group
      exact hσk _ h2
    · exact h
  have hnt : Nontrivial ↥(autI hV L) := by
    have : Nontrivial (↥(autI hV L) ⧸ Subgroup.center ↥(autI hV L)) := E.quasi.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(autI hV L))).nontrivial
  have hperfL : ⁅(⊤ : Subgroup ↥(autI hV L)), (⊤ : Subgroup ↥(autI hV L))⁆ =
      (⊤ : Subgroup ↥(autI hV L)) := by
    have := E.quasi.1
    rwa [Group.isPerfect_def, commutator_def] at this
  have hpcN : (perfectCore (N.subgroupOf L)).map σ = ⊤ := by
    rw [map_perfectCore σ, ← hNb, hNbtop, perfectCore_eq_self_of_perfect hperfL]
  have hpcN' : perfectCore N ≠ ⊥ := by
    intro h
    have h1 : (perfectCore (N.subgroupOf L)).map L.subtype = perfectCore N := by
      rw [map_perfectCore L.subtype (N.subgroupOf L), Subgroup.map_subgroupOf_eq_of_le hNL]
    rw [h] at h1
    have h2 : perfectCore (N.subgroupOf L) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h1
    rw [h2, Subgroup.map_bot] at hpcN
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(autI hV L))
    apply hx
    have : x ∈ (⊥ : Subgroup ↥(autI hV L)) := by rw [hpcN]; trivial
    exact Subgroup.mem_bot.1 this
  have hNsub : IsSubnormal N X :=
    A3.subnormal_trans (A3.subnormal_of_normal hNL hNn) (subnormal_of_mem_cComp E.comp)
  have hMsub := A3.subnormal_perfectCore hNsub
  by_contra hLN
  have hMlt : perfectCore N < L :=
    lt_of_le_of_ne ((perfectCore_le N).trans hNL) (fun h => hLN (h ▸ perfectCore_le N))
  exact not_subnormal_of_mem_cComp E.comp hMlt hpcN' (perfectCore_perfect N) hMsub

end EntryPlus

end CFSG.Quasithin.C124
