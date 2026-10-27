module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CNorm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_bar2Incl_cond {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) :
    CFSG.pCore 2 ↥L ≤ Subgroup.comap (Subgroup.inclusion hLX) (CFSG.pCore 2 ↥X) := by
  intro x hx
  have hxG : (x : G) ∈ pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := L) x).mpr hx
  rw [uc22r3e5c_pCoreOf_eq_inf hLX hLXn] at hxG
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := X) (Subgroup.inclusion hLX x)).mp hxG.1

private noncomputable def uc22r3e5c_bar2Incl {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) : Bar2 L →* Bar2 X :=
  QuotientGroup.map (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥X) (Subgroup.inclusion hLX)
    (uc22r3e5c_bar2Incl_cond hLX hLXn)

private theorem uc22r3e5c_bar2Incl_mk {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) (x : ↥L) :
    uc22r3e5c_bar2Incl hLX hLXn (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hLX x) := by
  rw [uc22r3e5c_bar2Incl, QuotientGroup.map_mk]

private theorem uc22r3e5c_bar2Incl_range {X L : Subgroup G} (hLX : L ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) :
    (uc22r3e5c_bar2Incl hLX hLXn).range =
      (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H l =>
      rw [uc22r3e5c_bar2Incl_mk]
      exact Subgroup.mem_map.mpr ⟨⟨l, hLX l.2⟩, l.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    rw [uc22r3e5c_bar2Incl_mk]
    rfl

private theorem uc22r3e5c_bar2Incl_comm {X L K : Subgroup G} (hLX : L ≤ X) (hKX : K ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) (hKXn : X ≤ normalizer (K : Set G))
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X) (u : Bar2 L) (v : Bar2 K) :
    Commute (uc22r3e5c_bar2Incl hLX hLXn u) (uc22r3e5c_bar2Incl hKX hKXn v) := by
  induction u using QuotientGroup.induction_on with
  | H l =>
    induction v using QuotientGroup.induction_on with
    | H k =>
      have h1 : QuotientGroup.mk (Subgroup.inclusion hLX l) ∈
          (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion hLX l, l.2, rfl⟩
      have h2 : QuotientGroup.mk (Subgroup.inclusion hKX k) ∈
          (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKX k, k.2, rfl⟩
      have h := uc22r3e5c_bar2_sup_comm hcomm
        (QuotientGroup.mk (Subgroup.inclusion hLX l)) h1
        (QuotientGroup.mk (Subgroup.inclusion hKX k)) h2
      rw [uc22r3e5c_bar2Incl_mk, uc22r3e5c_bar2Incl_mk]
      exact (commute_iff_eq _ _).mpr h

private theorem uc22r3e5c_noncommCoprod_surjective {X L K : Subgroup G} (hLX : L ≤ X)
    (hKX : K ≤ X) (hLXn : X ≤ normalizer (L : Set G)) (hKXn : X ≤ normalizer (K : Set G))
    (hsup : L ⊔ K = X) (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X) :
    Function.Surjective (MonoidHom.noncommCoprod (uc22r3e5c_bar2Incl hLX hLXn)
      (uc22r3e5c_bar2Incl hKX hKXn) (uc22r3e5c_bar2Incl_comm hLX hKX hLXn hKXn hcomm)) := by
  intro z
  let U : Subgroup (Bar2 X) := (L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  let V : Subgroup (Bar2 X) := (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  have hcent : U ≤ Subgroup.centralizer (V : Set (Bar2 X)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (uc22r3e5c_bar2_sup_comm hcomm u hu v hv).symm
  have hnorm : U ≤ Subgroup.normalizer (V : Set (Bar2 X)) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have htop : U ⊔ V = ⊤ := uc22r3e5c_bar2_sup_eq_top hLX hKX hsup
  have hcoe : ((U ⊔ V : Subgroup (Bar2 X)) : Set (Bar2 X)) = U * V :=
    Subgroup.coe_mul_of_left_le_normalizer_right U V hnorm
  have hz : z ∈ (U : Set (Bar2 X)) * (V : Set (Bar2 X)) := by
    rw [← hcoe, htop]
    exact Subgroup.mem_top z
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hz
  have hu' : u ∈ (uc22r3e5c_bar2Incl hLX hLXn).range := by
    rw [uc22r3e5c_bar2Incl_range]; exact hu
  have hv' : v ∈ (uc22r3e5c_bar2Incl hKX hKXn).range := by
    rw [uc22r3e5c_bar2Incl_range]; exact hv
  obtain ⟨u', rfl⟩ := MonoidHom.mem_range.mp hu'
  obtain ⟨v', rfl⟩ := MonoidHom.mem_range.mp hv'
  exact ⟨(u', v'), by rw [MonoidHom.noncommCoprod_apply]; exact huv⟩

private theorem uc22r3e5c_link_fst {A B C : Type} [Group A] [Group B] [Group C]
    (ψ : A × B →* C) (hψ : Function.Bijective ψ) (ιL : A →* C) (ιK : B →* C)
    (hψ_apply : ∀ u v, ψ (u, v) = ιL u * ιK v) {z : C} {a : A} (hz : z = ιL a) :
    (MulEquiv.ofBijective ψ hψ).symm z = (a, 1) := by
  rw [hz, MulEquiv.symm_apply_eq]
  change ιL a = ψ (a, 1)
  rw [hψ_apply, map_one, mul_one]

private theorem uc22r3e5c_link_snd {A B C : Type} [Group A] [Group B] [Group C]
    (ψ : A × B →* C) (hψ : Function.Bijective ψ) (ιL : A →* C) (ιK : B →* C)
    (hψ_apply : ∀ u v, ψ (u, v) = ιL u * ιK v) {z : C} {b : B} (hz : z = ιK b) :
    (MulEquiv.ofBijective ψ hψ).symm z = (1, b) := by
  rw [hz, MulEquiv.symm_apply_eq]
  change ιK b = ψ (1, b)
  rw [hψ_apply, map_one, one_mul]

private structure uc22r3e5c_LinkData (D : Data G) (L K : Subgroup G) where
  ψ : Bar2 L × Bar2 K →* Bar2 (conjClosure D.M L)
  bij : Function.Bijective ψ
  inclL : Bar2 L →* Bar2 (conjClosure D.M L)
  inclK : Bar2 K →* Bar2 (conjClosure D.M L)
  hψ_apply : ∀ u v, ψ (u, v) = inclL u * inclK v
  hL_apply : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
    inclL (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L)) = QuotientGroup.mk x
  hK_apply : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
    inclK (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)) = QuotientGroup.mk x

private noncomputable def uc22r3e5c_linkData {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    uc22r3e5c_LinkData D L K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  have hXsup : X = L ⊔ K := conjClosure_eq_sup_of_conjSetOf_eq hset
  have hLX : L ≤ X := by rw [hXsup]; exact le_sup_left
  have hKX : K ≤ X := by rw [hXsup]; exact le_sup_right
  have hLXn : X ≤ normalizer (L : Set G) := by
    rw [hXsup]
    exact sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne hL hKC hKne.symm)
  have hKXn : X ≤ normalizer (K : Set G) := by
    rw [hXsup]
    exact sup_le (calC_le_normalizer_of_ne hKC hL hKne) Subgroup.le_normalizer
  have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 X :=
    (calC_commutator_le_of_ne hL hKC hKne.symm).trans
      (inf_le_left.trans (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLX hLXn))
  let ψ : Bar2 L × Bar2 K →* Bar2 X :=
    MonoidHom.noncommCoprod (uc22r3e5c_bar2Incl hLX hLXn)
      (uc22r3e5c_bar2Incl hKX hKXn) (uc22r3e5c_bar2Incl_comm hLX hKX hLXn hKXn hcomm)
  have hψsurj : Function.Surjective ψ :=
    uc22r3e5c_noncommCoprod_surjective hLX hKX hLXn hKXn hXsup.symm hcomm
  let e₀ : Bar2 X ≃* Bar2 L × Bar2 K :=
    Classical.choice (uc22r3e5c_bar2_conjClosure_mulEquiv hL hKC hKne hset hSz)
  have hcard : Nat.card (Bar2 L × Bar2 K) = Nat.card (Bar2 X) :=
    (Nat.card_congr e₀.toEquiv).symm
  have hψbij : Function.Bijective ψ := hψsurj.bijective_of_nat_card_le (le_of_eq hcard)
  exact ⟨ψ, hψbij, uc22r3e5c_bar2Incl hLX hLXn, uc22r3e5c_bar2Incl hKX hKXn,
    (fun u v => by rw [MonoidHom.noncommCoprod_apply]),
    (fun x hx => by rw [uc22r3e5c_bar2Incl_mk]; rfl),
    (fun x hx => by rw [uc22r3e5c_bar2Incl_mk]; rfl)⟩

theorem uc22r3e5c_exists_bar2_mulEquiv_link {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    ∃ e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K,
      (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
        e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1)) ∧
      (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
        e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) := by
  let d := uc22r3e5c_linkData hL hKC hKne hset hSz
  refine ⟨(MulEquiv.ofBijective d.ψ d.bij).symm, ?_, ?_⟩
  · intro x hx
    exact uc22r3e5c_link_fst d.ψ d.bij d.inclL d.inclK d.hψ_apply (d.hL_apply x hx).symm
  · intro x hx
    exact uc22r3e5c_link_snd d.ψ d.bij d.inclL d.inclK d.hψ_apply (d.hK_apply x hx).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
