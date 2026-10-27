module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Ent
public import CFSG.Quasithin.EmptyFaithful.S1422Center
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSimple_autI_u33 {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hker : pCoreOf 2 L = L ⊓ centralizer (V : Set G)) : IsSimpleGroup ↥(autI hV L) := by
  have hσs := C124.starHom_surjective hV hLN
  let e : (↥L ⧸ (C124.starHom hV L hLN).ker) ≃* ↥(autI hV L) :=
    QuotientGroup.quotientKerEquivOfSurjective _ hσs
  have hk := C124.ker_starHom_eq_pCore hV hLN hker
  have hs : IsSimpleGroup (↥L ⧸ (C124.starHom hV L hLN).ker) :=
    (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hk)).mpr (isSimple_u33 hlie)
  exact (MulEquiv.isSimpleGroup_congr e).mp hs

theorem center_autI_u33 {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hker : pCoreOf 2 L = L ⊓ centralizer (V : Set G)) : Subgroup.center ↥(autI hV L) = ⊥ := by
  have hs := isSimple_autI_u33 hV hLN hlie hker
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autI hV L)) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative ↥(autI hV L) := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center ↥(autI hV L) := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.1 ha) b).symm⟩⟩
    have hnp : ¬ (Nat.card ↥(autI hV L)).Prime := by
      rw [card_autI_u33 hV hLN hlie hker]
      norm_num
    letI : CommGroup ↥(autI hV L) := { (inferInstance : Group ↥(autI hV L)) with
      mul_comm := fun a b => hc.is_comm.comm a b }
    exact hnp IsSimpleGroup.prime_card

theorem centralizer_U_le {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ normalizer (V : Set G)) (hLX : L ≤ X)
    (hn : X ≤ normalizer (L : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥) (hperf : ⁅L, L⁆ = L)
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hfs : quasithinGenFitting (autI hV X) = autI hV L)
    (hkerL : pCoreOf 2 L = L ⊓ centralizer (V : Set G)) :
    X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G) := by
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hUe : IsElemAbelian 2 ⁅V, L⁆ := B2F.isElemAbelian_mono hUV hV
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  have hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self hperf hLN
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have hUL : ⁅(⁅V, L⁆ : Subgroup G), L⁆ ≠ ⊥ := by rw [hUU]; exact hVL
  have hCU : pCoreOf 2 L = L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    refine pCoreOf_eq_inf_u33 hUe hLU (isSimple_u33 hlie) ?_ hUL
    exact (hkerL.le.trans inf_le_right).trans (Subgroup.centralizer_le hUV)
  intro x hx
  have hxX : x ∈ X := hx.1
  have hxN : x ∈ normalizer (V : Set G) := hXN hxX
  have hxc : ∀ u ∈ (⁅V, L⁆ : Subgroup G), x * u * x⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.1 hx.2 u hu
    rw [← this]
    group
  have hycomm : ∀ φ ∈ autI hV L, convI hV ⟨x, hxN⟩ * φ = φ * convI hV ⟨x, hxN⟩ := by
    intro φ hφ
    obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
    have hlU : ∀ u ∈ (⁅V, L⁆ : Subgroup G), (l : G) * u * (l : G)⁻¹ ∈ (⁅V, L⁆ : Subgroup G) :=
      fun u hu => (Subgroup.mem_normalizer_iff.1 (hLU hl) u).1 hu
    have hlU' : ∀ u ∈ (⁅V, L⁆ : Subgroup G), (l : G)⁻¹ * u * (l : G) ∈ (⁅V, L⁆ : Subgroup G) :=
      fun u hu => by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer ((⁅V, L⁆ : Subgroup G) : Set G)).inv_mem
          (hLU hl)) u).1 hu
        simpa using this
    have hzL : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ L := by
      have h1 : x * (l : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hn hxX) l).1 hl
      exact L.mul_mem h1 (L.inv_mem hl)
    have hzU : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu₁ := hlU' u hu
      have h2 : x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x = (l : G)⁻¹ * u * (l : G) := by
        have := hxc _ hu₁
        calc x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x
            = x⁻¹ * (x * ((l : G)⁻¹ * u * (l : G)) * x⁻¹) * x := by rw [this]
          _ = (l : G)⁻¹ * u * (l : G) := by group
      have key : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ = u := by
        have e1 : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ =
            x * (l : G) * (x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x) * (l : G)⁻¹ * x⁻¹ := by group
        rw [e1, h2]
        have e2 : x * (l : G) * ((l : G)⁻¹ * u * (l : G)) * (l : G)⁻¹ * x⁻¹ = x * u * x⁻¹ := by
          group
        rw [e2, hxc u hu]
      exact (mul_inv_eq_iff_eq_mul.1 key).symm
    have hzV : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer (V : Set G) := by
      have h1 : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L := by
        rw [hCU]
        exact ⟨hzL, hzU⟩
      rw [hkerL] at h1
      exact h1.2
    have hzN : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem
        ((normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hxN l.2)
          ((normalizer (V : Set G)).inv_mem hxN)) ((normalizer (V : Set G)).inv_mem l.2)
    have h1 := (convI_eq_one_iff hV ⟨_, hzN⟩).2 hzV
    have h2 : (⟨x * (l : G) * x⁻¹ * (l : G)⁻¹, hzN⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * l * ⟨x, hxN⟩⁻¹ * l⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hyX : convI hV ⟨x, hxN⟩ ∈ autI hV X := convI_mem_autI hV hxX hxN
  have hycent : convI hV ⟨x, hxN⟩ ∈ centralizer
      ((quasithinGenFitting (autI hV X) : Subgroup (MulAut (IntMod V hV))) : Set _) := by
    rw [hfs, Subgroup.mem_centralizer_iff]
    intro φ hφ
    exact (hycomm φ hφ).symm
  have hyL : convI hV ⟨x, hxN⟩ ∈ autI hV L := by
    rw [← hfs]
    exact centralizer_quasithinGenFitting_le (autI hV X) ⟨hyX, hycent⟩
  have hcenter : (⟨convI hV ⟨x, hxN⟩, hyL⟩ : ↥(autI hV L)) ∈ Subgroup.center ↥(autI hV L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hycomm g g.2).symm
  rw [center_autI_u33 hV hLN hlie hkerL, Subgroup.mem_bot] at hcenter
  have h1 : convI hV ⟨x, hxN⟩ = 1 := congrArg Subtype.val hcenter
  exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 h1

theorem u33_reduce {X T V L : Subgroup G} (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X)
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hVL : ⁅V, L⁆ ≠ ⊥) :
    IsTwoReducedIn X ⁅V, L⁆ ∧ ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ ∧
      X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hcomp
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hUe : IsElemAbelian 2 ⁅V, L⁆ := B2F.isElemAbelian_mono hUV hV
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self hperf hLN
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_u33 hlie
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  obtain ⟨-, -, hfs, -⟩ := C124.B2_10_2 hV hred hQT le_rfl hT hLX hn hprod hVL (Or.inl hLq)
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
      (C124.pCoreOf_le_centralizer hred)
  have hkerL := pCoreOf_eq_inf_u33 hV hLN (isSimple_u33 hlie) hOL hVL
  have hle := centralizer_U_le hV hXN hLX hn hVL hperf hlie hfs hkerL
  have hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left X (Subgroup.centralizer_le hUV))
  refine ⟨⟨hUV.trans hred.1, hXU, hUe, fun D hDX hXD hD => ?_⟩, hUU, hCeq⟩
  have hD' : D ≤ centralizer (V : Set G) := by
    refine hred.2.2.2 D hDX hXD fun d hd => ?_
    obtain ⟨k, hk⟩ := hD d hd
    exact ⟨k, hle ⟨(pow_mem (hDX hd) _ : d ^ 2 ^ k ∈ X), hk⟩⟩
  exact hD'.trans (Subgroup.centralizer_le hUV)

omit [Finite G] in
theorem card_sup_eq_of_le {A D Z : Subgroup G} [Finite G] (hAD : A ≤ centralizer (D : Set G))
    (hZ : A ⊓ D = Z) (hA : Nat.card A = 4 * Nat.card Z) :
    Nat.card ↥(A ⊔ D) = 4 * Nat.card D := by
  have h := card_sup_mul_card_inf_of_le_centralizer hAD
  rw [hZ, hA] at h
  have hpos : 0 < Nat.card ↥Z := Nat.card_pos
  have : Nat.card ↥(A ⊔ D) * Nat.card ↥Z = 4 * Nat.card ↥D * Nat.card ↥Z := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem concl4_of_U {X L V P : Subgroup G} (hred : IsTwoReducedIn X V)
    (hn : X ≤ normalizer (L : Set G)) (hPX : P ≤ X)
    (hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G))
    (hUe : IsElemAbelian 2 ⁅V, L⁆) (hUV : ⁅V, L⁆ ≤ V)
    (hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G))
    (h : Nat.card ↥(autOn X ⁅V, L⁆) = 12096 ∧ ∃ l : Subgroup G,
      ⁅V, L⁆ ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
        Nat.card ↥l = 4 * Nat.card ↥(⁅V, L⁆ ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) :
    Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
      l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      P ≤ normalizer (l : Set G) := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  obtain ⟨hc, l, hZl, hlU, hl4, hPl⟩ := h
  refine ⟨?_, l ⊔ (V ⊓ centralizer (L : Set G)), le_sup_right, sup_le (hlU.trans hUV) inf_le_left,
    ?_, ?_⟩
  · have h1 := card_autI_mul_card_inf hUe hXU
    have h2 := card_autI_mul_card_inf hV hXN
    rw [hCeq] at h1
    have hpos : 0 < Nat.card ↥(X ⊓ centralizer (V : Set G)) := Nat.card_pos
    have h3 : Nat.card ↥(autI hUe X) = Nat.card ↥(autI hV X) :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    have e1 : Nat.card ↥(autOn X ⁅V, L⁆) = Nat.card ↥(autI hUe X) := rfl
    have e2 : Nat.card ↥(autOn X V) = Nat.card ↥(autI hV X) := rfl
    rw [e2, ← h3, ← e1]
    exact hc
  · refine card_sup_eq_of_le (Z := ⁅V, L⁆ ⊓ centralizer (L : Set G)) ?_ ?_ hl4
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (B2F.isElemAbelian_comm hV (hUV (hlU ha)) hd.1).symm
    · refine le_antisymm (fun x hx => ⟨hlU hx.1, hx.2.2⟩) ?_
      intro x hx
      exact ⟨hZl hx, ⟨hUV hx.1, hx.2⟩⟩
  · intro g hg
    have hlE := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPl hg)
    have hVE := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXN (hPX hg))
    have hCE := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (B2F.normalizer_le_normalizer_centralizer L (hn (hPX hg)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hlE,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hVE, hCE]

theorem concl_of_U {X T V L P : Subgroup G} (hred : IsTwoReducedIn X V)
    (hn : X ≤ normalizer (L : Set G)) (hPX : P ≤ X)
    (hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G))
    (hUe : IsElemAbelian 2 ⁅V, L⁆) (hUV : ⁅V, L⁆ ≤ V)
    (hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G))
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (h : Concl X T ⁅V, L⁆ L P) :
    Concl X T V L P := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (concl4_of_U hred hn hPX hCeq hUe hUV hXU h)))
  · exfalso
    rcases h.1 with h1 | h1
    · exact not_a6_of_psu33 hlie h1
    · exact not_hatA6_of_psu33 hlie h1

end CFSG.Quasithin.H13.U3.GC137
