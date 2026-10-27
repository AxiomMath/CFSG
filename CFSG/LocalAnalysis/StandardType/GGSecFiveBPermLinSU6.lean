module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.GroupTheory.CentralKernelImage
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinSU6Block
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKFrame
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrTableP
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Matrix Multiplicative
open scoped MatrixGroups

private theorem congr_apply_s6a {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut X) (y : Y) : (MulAut.congr e f) y = e (f (e.symm y)) := rfl

private theorem fix_of_mem_ggAutomizer_s6a {G : Type} [Group G] {L Bs : Subgroup G} {x : G}
    (hxBs : x ∈ Bs) (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hgen : ∀ φ ∈ ggInduced L Bs, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    rintro φ ⟨g, hgL, -, hg⟩
    refine Subtype.ext ?_
    rw [hg ⟨x, hxBs⟩]
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hxL hgL)
    rw [hgx]
    group
  intro φ hφ
  induction hφ using Subgroup.closure_induction with
  | mem φ hφ => exact hgen φ hφ
  | one => rfl
  | mul φ ψ _ _ ihφ ihψ => simp only [MulAut.mul_apply, ihψ, ihφ]
  | inv φ _ ihφ => simpa only [ihφ] using MulAut.inv_apply_self (M := ↥Bs) φ ⟨x, hxBs⟩

private theorem exists_const_eta_of_mem_ggAutomizer_s6a {G : Type} [Group G] {p : ℕ}
    {L Bs : Subgroup G} {x : G} (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1) (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ d : ZMod p, d ≠ 0 ∧ eta ⟨x, hxBs⟩ = fun _ => ofAdd d := by
  have hxfix := fix_of_mem_ggAutomizer_s6a hxBs hxL
  have hfix : ∀ u ∈ aPermutationFull 4 p, u (eta ⟨x, hxBs⟩) = eta ⟨x, hxBs⟩ := by
    intro u hu
    rw [← hLA] at hu
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hu
    change (MulAut.congr eta) φ (eta ⟨x, hxBs⟩) = eta ⟨x, hxBs⟩
    rw [congr_apply_s6a, MulEquiv.symm_apply_apply, hxfix φ hφ]
  have hconst : ∀ i j : Fin 4, eta ⟨x, hxBs⟩ i = eta ⟨x, hxBs⟩ j :=
    (forall_aPermutationFull_fix_iff (eta ⟨x, hxBs⟩)).mp hfix
  refine ⟨toAdd (eta ⟨x, hxBs⟩ 0), ?_, ?_⟩
  · intro hd0
    have hv : eta ⟨x, hxBs⟩ 0 = 1 :=
      (ofAdd_toAdd (eta ⟨x, hxBs⟩ 0)).symm.trans ((congrArg ofAdd hd0).trans ofAdd_zero)
    have h1 : eta ⟨x, hxBs⟩ = 1 := by
      funext i
      exact (hconst i 0).trans hv
    have hxeq : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      rw [← eta.symm_apply_apply ⟨x, hxBs⟩, h1]
      exact map_one eta.symm
    exact hx1 (congrArg Subtype.val hxeq)
  · funext i
    exact (hconst i 0).trans (ofAdd_toAdd (eta ⟨x, hxBs⟩ 0)).symm

private theorem torus_pow_eq_one_s6a {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    (τ : Multiplicative (Fin 3 → ZMod p) →* S) (v : Fin 3 → ZMod p) :
    τ (ofAdd v) ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← map_pow]
  have hv : (ofAdd v : Multiplicative (Fin 3 → ZMod p)) ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    change p • (ofAdd v).toAdd = 0
    funext i
    change p • ((ofAdd v).toAdd i) = 0
    simp [nsmul_eq_mul]
  rw [hv, map_one]

private theorem torus_action_s6a {G S : Type} [Group G] [Group S] {p : ℕ}
    {τ : Multiplicative (Fin 3 → ZMod p) →* S} {κ : S →* G} {x : G}
    {etaX : Fin 4 → Multiplicative (ZMod p)} {π : Fin 4 ≃ Fin 4} {c d : ZMod p}
    (hd : etaX = fun _ => ofAdd d)
    (hframe : ∀ u, x * κ u * x⁻¹ = κ (τ (ofAdd (fun i => c * toAdd (etaX (π i.succ)))) * u *
      (τ (ofAdd (fun i => c * toAdd (etaX (π i.succ)))))⁻¹)) :
    ∀ u, x * κ u * x⁻¹ = κ (τ (ofAdd (fun _ => c * d)) * u *
      (τ (ofAdd (fun _ => c * d)))⁻¹) := by
  intro u
  have h := hframe u
  have harg : (fun i : Fin 3 => c * toAdd (etaX (π i.succ))) = fun _ => c * d := by
    funext i
    simp only [hd, toAdd_ofAdd]
  rwa [harg] at h

private theorem le_map_centralizer_s6a {S G : Type} [Group S] [Group G] {p : ℕ}
    (hZ : ∀ z ∈ Subgroup.center S, z ^ p = 1 → z = 1) {κ : S →* G}
    (hκ : κ.ker ≤ Subgroup.center S) {x : G} {t : S} (ht : t ^ p = 1)
    (hx : ∀ u, x * κ u * x⁻¹ = κ (t * u * t⁻¹))
    {J : Subgroup G} (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hJK : J ≤ κ.range) :
    J ≤ (Subgroup.centralizer ({t} : Set S)).map κ := by
  intro j hj
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hJK hj)
  refine Subgroup.mem_map.mpr ⟨g, ?_, hg⟩
  refine CFSG.GroupTheory.mem_centralizer_of_commute_of_conj hZ hκ ht hx ?_
  have hjx : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hJx hj)
  rw [hg]
  exact hjx.symm

private theorem perfect_and_card_J_s6a {G : Type} [Group G] {F : Type} [Field F]
    {J : Subgroup G} {σJ : SL(3, F) →* G} (hσJ : Function.Injective σJ)
    (hσJr : σJ.range = J) :
    ⁅J, J⁆ = J ∧ Nat.card ↥J = Nat.card SL(3, F) := by
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
      (by norm_num)
  have h1 : ⁅(⊤ : Subgroup SL(3, F)), (⊤ : Subgroup SL(3, F))⁆ = ⊤ :=
    hperf.commutator_eq_top
  have hmap := Subgroup.map_commutator (⊤ : Subgroup SL(3, F)) (⊤ : Subgroup SL(3, F)) σJ
  simp only [h1, Subgroup.map_top, hσJr] at hmap
  refine ⟨hmap.symm, ?_⟩
  exact (Nat.card_congr ((MonoidHom.ofInjective hσJ).trans
    (MulEquiv.subgroupCongr hσJr)).toEquiv).symm

private theorem ker_eq_bot_of_le_map_s6a {S G : Type} [Group S] [Finite S] [Group G] {p : ℕ}
    {κ : S →* G} {x : G} {t : S} {H : Subgroup S} {J : Subgroup G}
    (hZ : ∀ z ∈ Subgroup.center S, z ^ p = 1 → z = 1) (hκ : κ.ker ≤ Subgroup.center S)
    (hZH : Subgroup.center S ≤ H) (ht : t ^ p = 1)
    (hx : ∀ u, x * κ u * x⁻¹ = κ (t * u * t⁻¹))
    (hCHH : ⁅Subgroup.centralizer ({t} : Set S), Subgroup.centralizer ({t} : Set S)⁆ ≤ H)
    (hJperf : ⁅J, J⁆ = J) (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hJK : J ≤ κ.range) (hcard : Nat.card H ≤ Nat.card ↥J) : κ.ker = ⊥ := by
  have hJCM : J ≤ (Subgroup.centralizer ({t} : Set S)).map κ :=
    le_map_centralizer_s6a hZ hκ ht hx hJx hJK
  have hJmap : J ≤ H.map κ := CFSG.GroupTheory.le_map_of_commutator_le hCHH hJperf hJCM
  exact CFSG.GroupTheory.ker_eq_bot_of_le_map_of_card_le (hκ.trans hZH) hJmap hcard


private theorem exists_su_centralImage_s6a {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {a : ℕ}
    (ha : 2 ≤ a) (hKlab : GGHasLabel ⟨.twA, 5, a⟩ (↥K ⧸ Subgroup.center ↥K)) :
    ∃ ψ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G,
      ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6) ∧
      ψ.range = K := by
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hR.1.1.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hR.1.1.2.2 hnb)
  exact exists_su_centralImage_of_hasLabel hKc.2.2.1 (n := 6) (f := a) (by norm_num) ha
    (by simpa using hKlab)

private theorem nonempty_su6_of_jChart_s6a (hBal : GGLBalanceInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hB : B = Bs) {a : ℕ} (ha : 2 ≤ a) (hpa : p ∣ 2 ^ a - 1) {K : Subgroup G} (hK : K ∈ 𝒦)
    {i0 : Fin 4}
    (hKA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hKlab : GGHasLabel ⟨.twA, 5, a⟩ (↥K ⧸ Subgroup.center ↥K))
    {σJ : SL(3, GaloisField 2 (2 * a)) →* G} (hσJ : Function.Injective σJ)
    (hσJr : σJ.range = J) (hpJ : p ∣ Nat.card ↥J) :
    Nonempty (↥K ≃* ↥(SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6)) := by
  have hp : p.Prime := hR.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hR.1.1.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  obtain ⟨ψ, hψker, hψrange⟩ := exists_su_centralImage_s6a hR hK ha hKlab
  obtain ⟨h, ζ, hζ, -, τ, hτ, π, -, c, hc, κ, hκker, hκrange, -, hframe⟩ :=
    ggSecFiveBPermSU_exists_calibrated_frame_of_centralImage ggInnerDiagMpInput_holds hR (n := 4)
      (a := a) eta (hn := rfl) ha hpa hK hKA hψker hψrange
  have hS : CFSG.Assembly.LargeEvenSStar p B x L := hR.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hB ▸ hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨d, hd0, hd⟩ := exists_const_eta_of_mem_ggAutomizer_s6a eta hLA hxBs hx1 hxL
  have hcd : c * d ≠ 0 := mul_ne_zero hc hd0
  have hZ : ∀ z ∈ Subgroup.center (hypSU h 3 0), z ^ p = 1 → z = 1 := fun z hz hzp =>
    hypSU_eq_one_of_mem_center_of_pow_eq_one (card_galoisField_two_mul 2 a (by omega)) h hp hp2
      hpa hz hzp
  have hxact := torus_action_s6a (τ := τ) (κ := κ) (x := x) (etaX := eta ⟨x, hxBs⟩) (π := π)
    (c := c) (d := d) hd (fun u => hframe ⟨x, hxBs⟩ u)
  have ht : (τ (ofAdd (fun _ => c * d))) ^ p = 1 := torus_pow_eq_one_s6a hp τ (fun _ => c * d)
  obtain ⟨hJperf, hcardJ⟩ := perfect_and_card_J_s6a hσJ hσJr
  have hJleK : J ≤ K := le_of_ggNbr hBal hR.1.1.1 hR.1.1.2.2 hpJ hnb
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) :=
    (hR.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left).trans hxL
  have hJK : J ≤ κ.range := hJleK.trans (le_of_eq hκrange.symm)
  obtain ⟨H, hZH, hHcard, hCHH⟩ :=
    exists_sl_three_of_centralizer_hypEntries_const h hp hp2 hζ hcd (hτ (fun _ => c * d))
  have hcardHJ : Nat.card H ≤ Nat.card ↥J := by rw [hcardJ]; exact hHcard
  have hkerbot : κ.ker = ⊥ :=
    ker_eq_bot_of_le_map_s6a hZ hκker hZH ht hxact hCHH hJperf hJx hJK hcardHJ
  have hκinj : Function.Injective κ := (MonoidHom.ker_eq_bot_iff κ).mp hkerbot
  let eH : hypSU h 3 0 ≃* SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  exact ⟨((MonoidHom.ofInjective hκinj).trans (MulEquiv.subgroupCongr hκrange)).symm.trans eH⟩

theorem ggSecFiveBPermLinSU6Input_of_balance (hBal : GGLBalanceInput) :
    GGSecFiveBPermLinSU6Input := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 e hpres eta hEta hLA hG0 hB a ha hpa hLab
    K hK𝒦 i0 hKA hKl
  obtain ⟨lab, hΛ, ⟨hLin, hnlab⟩, hlabL, -⟩ :=
    GGInnerDiagOnLabel.exists_label_eq
      (S := fun p lab => GGSecFiveBPermLinLabel 4 p lab ∧ lab.n = 2 * a) hLab
  rcases lab with ⟨tag, rank, fn⟩
  obtain ⟨htag, hrank, hpdvd⟩ := hLin
  subst htag
  subst hrank
  subst hnlab
  have hf2 : 2 ≤ 2 * a := by omega
  obtain ⟨ψ, hψker, hψrange⟩ := exists_sl_centralImage_of_hasLabel hLab.1 (n := 4) (f := 2 * a)
    (by norm_num) hf2 hlabL
  obtain ⟨σJ, hσinj, hσrange, -, hpJ⟩ :=
    ggSecFiveBPermLin_J_chart ggInnerDiagMpInput_holds hR (n := 4) (by norm_num) eta hLA
      hf2 hpdvd hψker hψrange hK𝒦 hKA
  exact nonempty_su6_of_jChart_s6a hBal hR eta hLA hB ha hpa hK𝒦 hKA hKl hσinj hσrange hpJ

end CFSG.StandardType

end
