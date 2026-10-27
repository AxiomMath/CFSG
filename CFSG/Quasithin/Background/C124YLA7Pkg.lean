module

public import CFSG.Quasithin.Background.C124YLA7Fix
public import CFSG.Quasithin.Background.C124YLPack
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Min
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Types
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C1PackSolvP
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246.C123
open scoped MatrixGroups

local notation "cjS" => CFSG.QuasithinUnique.L246.C123.conjSub


theorem isSylowTwoOf_of_card_mul {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ B) {a m : ℕ} (ha : Nat.card A = 2 ^ a) (hb : Nat.card B = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) : IsSylowTwoOf A B := by
  refine ⟨hAB, IsPGroup.of_card ha, ?_⟩
  have h := Subgroup.index_mul_card (A.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, ha, hb] at h
  have hpos : 0 < 2 ^ a := by positivity
  have : (A.subgroupOf B).index = m := by
    have h' : (A.subgroupOf B).index * 2 ^ a = m * 2 ^ a := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  show ¬ 2 ∣ (A.subgroupOf B).index
  rw [this]
  exact hm

theorem coord_mul_inv_mem_iff {W : Type*} [CommGroup W] {Q : Type*} [CommGroup Q]
    {U Z : Subgroup W} {c : ↥U →* Q} (h : IsCoord U Z c) (u v : ↥U) :
    (v : W) * (u : W)⁻¹ ∈ Z ↔ c v = c u := by
  have h1 := h.ker (v * u⁻¹)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1.symm

namespace A7Ctx

variable {W : Type*} [CommGroup W] [Finite W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : A7Ctx Ls U Z)

include C in
theorem card_Ls : Nat.card Ls = 2520 := by
  rw [← C.phi_range, ← card_A7]
  exact (Nat.card_congr (MonoidHom.ofInjective C.phi_injective).toEquiv).symm

include C in
theorem sylow_P : IsSylowTwoOf (sylowA.map C.phi) Ls := by
  refine isSylowTwoOf_of_card_mul (C.map_phi_le _) (a := 3) (m := 315) ?_ ?_ (by norm_num)
  · rw [Subgroup.card_map_of_injective C.phi_injective, card_sylowA]
    norm_num
  · rw [C.card_Ls]
    norm_num

include C in
theorem sylow_K_Y : IsSylowTwoOf (kleinA.map C.phi) (Yst.map C.phi) := by
  refine isSylowTwoOf_of_card_mul (Subgroup.map_mono kleinA_le_Yst) (a := 2) (m := 15) ?_ ?_
    (by norm_num)
  · rw [Subgroup.card_map_of_injective C.phi_injective, card_kleinA]
    norm_num
  · rw [Subgroup.card_map_of_injective C.phi_injective, card_Yst]
    norm_num

include C in
theorem sl2_Y : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(Yst.map C.phi) ≃* SL(2, F)) := by
  obtain ⟨F, iF, fF, hF, ⟨e⟩⟩ := sl2_Yst
  exact ⟨F, iF, fF, hF, ⟨(Yst.equivMapOfInjective C.phi C.phi_injective).symm.trans e⟩⟩

include C in
theorem gen_map : Ls = Yst.map C.phi ⊔
    (Ls ⊓ Subgroup.normalizer ((kleinA.map C.phi : Subgroup (MulAut W)) : Set (MulAut W))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ : x ∈ C.phi.range := C.phi_range.ge hx
    have hg : g ∈ Yst ⊔ Subgroup.normalizer (kleinA : Set A7) := by
      rw [gen_A7]
      exact Subgroup.mem_top g
    have hmap : (Yst ⊔ Subgroup.normalizer (kleinA : Set A7)).map C.phi =
        Yst.map C.phi ⊔ (Subgroup.normalizer (kleinA : Set A7)).map C.phi :=
      Subgroup.map_sup _ _ _
    have hmem := Subgroup.mem_map_of_mem C.phi hg
    rw [hmap] at hmem
    have hN : (Subgroup.normalizer (kleinA : Set A7)).map C.phi ≤
        Ls ⊓ Subgroup.normalizer ((kleinA.map C.phi : Subgroup (MulAut W)) : Set (MulAut W)) := by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      refine ⟨C.phi_mem n, Subgroup.mem_normalizer_fintype fun k hk => ?_⟩
      obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hk
      have := (Subgroup.mem_normalizer_iff.1 hn κ).1 hκ
      exact ⟨n * κ * n⁻¹, this, by simp [map_mul, map_inv]⟩
    exact (sup_le_sup_left hN _) hmem
  · exact sup_le (C.map_phi_le _) inf_le_left

include C in
theorem unique_K {B : Subgroup (MulAut W)} (hB : B ≤ sylowA.map C.phi) (hw : WOff U Z B) :
    B = kleinA.map C.phi := by
  have hφ := C.phi_injective
  set B' : Subgroup A7 := B.comap C.phi with hB'
  have hBr : B ≤ C.phi.range := hB.trans (Subgroup.map_le_range _ _)
  have hBmap : B'.map C.phi = B := Subgroup.map_comap_eq_self hBr
  have hB'S : B' ≤ sylowA := by
    have h1 : B' ≤ (sylowA.map C.phi).comap C.phi := Subgroup.comap_mono hB
    rwa [Subgroup.comap_map_eq_self_of_injective hφ] at h1
  rw [← hBmap] at hw
  obtain ⟨hne, hc, hs, h16⟩ := (C.woff_map_iff B').1 hw
  have hK := klein_of_woff (rhoA C.α) card_Q7 (rhoA_injective C.α) sq_Q7 hne hc hs h16
  have heq : B' = kleinA :=
    IsKleinConj.eq_of_le card_sylowA hK isKleinConj_kleinA hB'S kleinA_le_sylowA
  rw [← hBmap, heq]

include C in
theorem woff_klein (hU : ∀ l ∈ Ls, ∀ u, u ∈ U ↔ l u ∈ U) (hZ : ∀ l ∈ Ls, ∀ z, z ∈ Z ↔ l z ∈ Z)
    (hex : ∃ K1, K1 ≤ Ls ∧ WOff U Z K1) : WOff U Z (kleinA.map C.phi) := by
  obtain ⟨K1, hK1L, hw⟩ := hex
  have hK1r : K1 ≤ C.phi.range := hK1L.trans C.phi_range.ge
  set Bk : Subgroup A7 := K1.comap C.phi with hBk
  have hBkm : Bk.map C.phi = K1 := Subgroup.map_comap_eq_self hK1r
  rw [← hBkm] at hw
  obtain ⟨hne, hc, hs, h16⟩ := (C.woff_map_iff Bk).1 hw
  obtain ⟨c, hc'⟩ := klein_of_woff (rhoA C.α) card_Q7 (rhoA_injective C.α) sq_Q7 hne hc hs h16
  have hconj : (cjS c kleinA).map C.phi =
      B1.conjAut (C.phi c) (kleinA.map C.phi) := by
    ext x
    rw [Subgroup.mem_map, B1.mem_conjAut, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨c⁻¹ * b * c, (CFSG.QuasithinUnique.L246.C123.mem_conjSub).1 hb, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨k, hk, hkx⟩
      refine ⟨c * k * c⁻¹, ?_, ?_⟩
      · rw [CFSG.QuasithinUnique.L246.C123.mem_conjSub]
        simpa [mul_assoc] using hk
      · have : x = C.phi c * C.phi k * (C.phi c)⁻¹ := by rw [hkx]; group
        rw [this]
        simp [map_mul, map_inv]
  have hw2 : WOff U Z (B1.conjAut (C.phi c) (kleinA.map C.phi)) := by
    rw [← hconj, ← hc']
    exact hw
  have hl : (C.phi c)⁻¹ ∈ Ls := Ls.inv_mem (C.phi_mem c)
  have hw3 := hw2.conj (C.phi c)⁻¹ (hU _ hl) (hZ _ hl)
  rwa [B1.conjAut_inv_conjAut] at hw3

include C in
theorem card_fixU_kleinA (hw : WOff U Z (kleinA.map C.phi)) :
    Nat.card (fixU (rhoA C.α) kleinA) = 4 := by
  obtain ⟨-, -, -, h16⟩ := (C.woff_map_iff kleinA).1 hw
  exact card_fixU_eq_four (rhoA C.α) card_Q7 (rhoA_injective C.α) sq_Q7 isKleinConj_kleinA h16

include C in
theorem tight (hw : WOff U Z (kleinA.map C.phi)) :
    Nat.card U = Nat.card (kleinA.map C.phi) * Nat.card (liftFix U Z (kleinA.map C.phi)) := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hZB := Z_le_liftFix_real' C.real (C.map_phi_le kleinA)
  rw [hc.card_U, hc.card_liftFix hZB, C.card_fixImg hc hequiv kleinA, C.card_fixU_kleinA hw,
    Subgroup.card_map_of_injective C.phi_injective, card_kleinA, card_Q7]
  ring

include C in
theorem cent (hw : WOff U Z (kleinA.map C.phi)) {x : MulAut W} (hx : x ∈ Ls)
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hN : x ∈ Subgroup.normalizer ((kleinA.map C.phi : Subgroup (MulAut W)) : Set (MulAut W)))
    (hfix : ∀ u ∈ liftFix U Z (kleinA.map C.phi), x u * u⁻¹ ∈ Z) : x ∈ kleinA.map C.phi := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  obtain ⟨σ, rfl⟩ : x ∈ C.phi.range := C.phi_range.ge hx
  have hφ := C.phi_injective
  have hσ2 : ∃ k : ℕ, σ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, hφ (by rw [map_pow, hk, map_one])⟩
  have hσN : σ ∈ Subgroup.normalizer (kleinA : Set A7) := by
    refine mem_normalizer_of_conj_le fun κ hκ => ?_
    have h1 := (Subgroup.mem_normalizer_iff.1 hN (C.phi κ)).1 (Subgroup.mem_map_of_mem C.phi hκ)
    obtain ⟨κ', hκ', hκ'e⟩ := Subgroup.mem_map.1 h1
    have : κ' = σ * κ * σ⁻¹ := hφ (by rw [hκ'e, map_mul, map_mul, map_inv])
    rw [← this]
    exact hκ'
  have hσfix : ∀ q ∈ fixU (rhoA C.α) kleinA, rhoA C.α σ q = q := by
    intro q hq
    have hmem : q ∈ fixImg U Z c (kleinA.map C.phi) := (C.mem_fixImg_iff hc hequiv kleinA q).2 hq
    obtain ⟨u, rfl, hb⟩ := mem_fixImg.1 hmem
    have h1 := hfix u (mem_liftFix.2 ⟨u.2, hb⟩)
    have hu : C.phi σ (u : W) ∈ U := C.phi_stab σ u u.2
    have h3 := (coord_mul_inv_mem_iff hc u ⟨C.phi σ u, hu⟩).1 h1
    exact (hequiv σ u hu).symm.trans h3
  have h4 : 4 ≤ Nat.card (fixU (rhoA C.α) kleinA) := (C.card_fixU_kleinA hw).ge
  exact Subgroup.mem_map_of_mem C.phi
    (mem_kleinA_of_fix (rhoA C.α) card_Q7 (rhoA_injective C.α) hσ2 hσN hσfix h4)

include C in
theorem moves (hw : WOff U Z (kleinA.map C.phi)) :
    ∃ u ∈ liftFix U Z (kleinA.map C.phi), ∃ y ∈ Yst.map C.phi, y u * u⁻¹ ∉ Z := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  obtain ⟨q, hq, y, hy, hyq⟩ := exists_move_Yst (rhoA C.α) card_Q7 (rhoA_injective C.α)
    (C.card_fixU_kleinA hw).ge
  have hmem : q ∈ fixImg U Z c (kleinA.map C.phi) := (C.mem_fixImg_iff hc hequiv kleinA q).2 hq
  obtain ⟨u, rfl, hb⟩ := mem_fixImg.1 hmem
  refine ⟨u, mem_liftFix.2 ⟨u.2, hb⟩, C.phi y, Subgroup.mem_map_of_mem C.phi hy, fun hZ => hyq ?_⟩
  have hu : C.phi y (u : W) ∈ U := C.phi_stab y u u.2
  have h3 := (coord_mul_inv_mem_iff hc u ⟨C.phi y u, hu⟩).1 hZ
  exact (hequiv y u hu).symm.trans h3

include C in
theorem package (hU : ∀ l ∈ Ls, ∀ u, u ∈ U ↔ l u ∈ U) (hZ : ∀ l ∈ Ls, ∀ z, z ∈ Z ↔ l z ∈ Z)
    (hex : ∃ K1, K1 ≤ Ls ∧ WOff U Z K1) :
    Package Ls Ls U Z (kleinA.map C.phi) (Yst.map C.phi) := by
  have hw := C.woff_klein hU hZ hex
  exact ⟨C.map_phi_le _, hw, C.tight hw, fun x hx h2 hN hfix => C.cent hw hx h2 hN hfix,
    C.map_phi_le _, C.sylow_K_Y, C.sl2_Y, C.moves hw, C.gen_map⟩

end A7Ctx

end CFSG.Quasithin.C124.YL.A7
