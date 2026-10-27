module

import CFSG.Quasithin.Background.G119Group2
import CFSG.Quasithin.Background.FFC10A
import CFSG.Quasithin.Background.G116IIIA5
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.Quasithin (fixV)
open CFSG.Quasithin.H (StdMod toAddMap toAddMap_injective toAddMap_natAut natAut natImage natNorm)
open scoped Matrix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

section NatTau

variable {L : Subgroup G} {F : Type} [Field F] {ψ : V →+ (Fin 2 → F)} {σ : (Fin 2 → F) → V}

private theorem psi_apply_sec (hσ : ∀ y, σ y ∈ commOn ρ L ⊤ ∧ ψ (σ y) = y)
    (hψ : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 ↔ x ∈ fixSub ρ L) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : V} (hx : x ∈ commOn ρ L ⊤) :
    ψ (ρ g (σ (ψ x))) = ψ (ρ g x) := by
  have h1 : σ (ψ x) - x ∈ commOn ρ L ⊤ := Submodule.sub_mem _ (hσ _).1 hx
  have h2 : σ (ψ x) - x ∈ fixSub ρ L := (hψ _ h1).1 (by rw [map_sub, (hσ _).2, sub_self])
  have h3 := (hψ _ (commOn_top_mapsTo hg h1)).2 (apply_mem_fixSub_of_mem_normalizer hg h2)
  rw [map_sub, map_sub] at h3
  exact sub_eq_zero.1 h3

private noncomputable def natTau (hσ : ∀ y, σ y ∈ commOn ρ L ⊤ ∧ ψ (σ y) = y)
    (hψ : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 ↔ x ∈ fixSub ρ L) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (StdMod (Fin 2) F) where
  toFun g := AddEquiv.toMultiplicative
    { toFun := fun y => ψ (ρ g (σ y))
      invFun := fun y => ψ (ρ (g : G)⁻¹ (σ y))
      left_inv := fun y => by
        show ψ (ρ (g : G)⁻¹ (σ (ψ (ρ (g : G) (σ y))))) = y
        rw [psi_apply_sec hσ hψ (inv_mem g.2) (commOn_top_mapsTo g.2 (hσ y).1), glRep_inv_apply,
          (hσ y).2]
      right_inv := fun y => by
        show ψ (ρ (g : G) (σ (ψ (ρ (g : G)⁻¹ (σ y))))) = y
        rw [psi_apply_sec hσ hψ g.2 (commOn_top_mapsTo (inv_mem g.2) (hσ y).1), glRep_apply_inv,
          (hσ y).2]
      map_add' := fun y y' => by
        have h := psi_apply_sec hσ hψ g.2 (Submodule.add_mem _ (hσ y).1 (hσ y').1)
        rw [map_add ψ, (hσ y).2, (hσ y').2] at h
        show ψ (ρ (g : G) (σ (y + y'))) = ψ (ρ (g : G) (σ y)) + ψ (ρ (g : G) (σ y'))
        rw [h, map_add, map_add] }
  map_one' := toAddMap_injective fun y => by
    show ψ (ρ 1 (σ y)) = y
    rw [map_one, Module.End.one_apply, (hσ y).2]
  map_mul' g h := toAddMap_injective fun y => by
    show ψ (ρ ((g : G) * h) (σ y)) = ψ (ρ (g : G) (σ (ψ (ρ (h : G) (σ y)))))
    rw [psi_apply_sec hσ hψ g.2 (commOn_top_mapsTo h.2 (hσ y).1), glRep_mul_apply]

variable (hσ : ∀ y, σ y ∈ commOn ρ L ⊤ ∧ ψ (σ y) = y) (hψ : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 ↔ x ∈ fixSub ρ L)
include hσ hψ

private theorem natTau_eq_one_iff (g : ↥(Subgroup.normalizer (L : Set G))) :
    natTau hσ hψ g = 1 ↔ ∀ x ∈ commOn ρ L ⊤, ρ g x - x ∈ fixSub ρ L := by
  constructor
  · intro h x hx
    have h1 : ψ (ρ (g : G) (σ (ψ x))) = ψ x := congrArg (fun t => toAddMap t (ψ x)) h
    rw [psi_apply_sec hσ hψ g.2 hx] at h1
    exact (hψ _ (Submodule.sub_mem _ (commOn_top_mapsTo g.2 hx) hx)).1 (by rw [map_sub, h1, sub_self])
  · intro h
    refine toAddMap_injective fun y => ?_
    show ψ (ρ (g : G) (σ y)) = y
    have h1 := (hψ _ (Submodule.sub_mem _ (commOn_top_mapsTo g.2 (hσ y).1) (hσ y).1)).2 (h _ (hσ y).1)
    rw [map_sub, (hσ y).2, sub_eq_zero] at h1
    exact h1

variable {φ : ↥L ≃* ↥(StatedSL 2 F)}
  (hE : ∀ (h : ↥L) (x : V), x ∈ commOn ρ L ⊤ →
    ψ (ρ (h : G) x) = (((φ h : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ ψ x)
include hE

private theorem natTau_of_mem (l : ↥L) :
    natTau hσ hψ ⟨l, Subgroup.le_normalizer l.2⟩ = natAut (StatedSL 2 F) (φ l) :=
  toAddMap_injective fun y => by
    show ψ (ρ (l : G) (σ y)) = _
    rw [hE l _ (hσ y).1, (hσ y).2, toAddMap_natAut]

private theorem natImage_eq_map_natTau :
    natImage (StatedSL 2 F) = (L.subgroupOf (Subgroup.normalizer (L : Set G))).map (natTau hσ hψ) := by
  ext y
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨l, rfl⟩ := φ.surjective γ
    exact ⟨⟨l, Subgroup.le_normalizer l.2⟩, l.2, natTau_of_mem hσ hψ hE l⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨φ ⟨g, hg⟩, (natTau_of_mem hσ hψ hE ⟨g, hg⟩).symm⟩

end NatTau

theorem exists_eq_apply_of_natL2 [Finite G] [Finite V] {L : Subgroup G} [IsSimpleGroup ↥L]
    (hUL : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤) (hnt : ¬ commOn ρ L ⊤ ≤ fixSub ρ L)
    {n : ℕ} (hn : 1 ≤ n) (hnat : NatL2 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) n)
    {S : Subgroup G} (hSe : CFSG.IsElementaryAbelian 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hoff : Nat.card ↥(commOn ρ L ⊤) * Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) ≤
      Nat.card ↥S * Nat.card ↥(fixOn ρ S (commOn ρ L ⊤))) :
    ∀ s ∈ S, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ s u = ρ l u := by
  classical
  obtain ⟨F, _, _, hF, -, -, -, φ, ψ, hψ0, hψK, hψS, hE⟩ := hnat
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  haveI := hSe
  choose σ hσ using hψS
  have hψ : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 ↔ x ∈ fixSub ρ L := fun x hx =>
    ⟨fun h => (hψK x hx h).2, fun h => hψ0 x ⟨hx, h⟩⟩
  set f : ↥S →* MulAut (StdMod (Fin 2) F) := (natTau hσ hψ).comp (Subgroup.inclusion hSN)
  have hEN : f.range ≤ natNorm (StatedSL 2 F) := by
    rintro _ ⟨s, rfl⟩
    rw [natNorm, natImage_eq_map_natTau hσ hψ hE]
    refine Subgroup.le_normalizer_map (natTau hσ hψ) ⟨Subgroup.inclusion hSN s, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top (H := L.subgroupOf (Subgroup.normalizer (L : Set G)))]
    exact Subgroup.mem_top _
  have hE2 : ∀ x ∈ f.range, x ^ 2 = 1 := by
    rintro _ ⟨s, rfl⟩
    have hs : s ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact elemPow_eq_one_of_isElementaryAbelian (s : G) s.2)
    rw [← map_pow, hs, map_one]
  have hEc : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, hSe.toIsMulCommutative.is_comm.comm s t]
  have hker : ∀ s : ↥S, s ∈ f.ker ↔ (s : G) ∈ cenOn ρ S (commOn ρ L ⊤) := by
    intro s
    rw [MonoidHom.mem_ker]
    change natTau hσ hψ (Subgroup.inclusion hSN s) = 1 ↔ _
    rw [natTau_eq_one_iff hσ hψ]
    exact ⟨fun h => ⟨s.2, apply_eq_self_of_sub_mem_fixSub hUL hnt (hSN s.2) h⟩, fun h x hx => by
      show ρ (s : G) x - x ∈ fixSub ρ L
      rw [h.2 x hx, sub_self]
      exact Submodule.zero_mem _⟩
  have hS : Nat.card ↥S = Nat.card f.range * Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) := by
    have h1 : Nat.card f.ker = Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) := Nat.card_congr
      { toFun := fun s => ⟨s.1, (hker s.1).1 s.2⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, (hker ⟨x, x.2.1⟩).2 x.2⟩
        left_inv := fun s => rfl
        right_inv := fun x => rfl }
    rw [← h1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hU : Nat.card (Fin 2 → F) * Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) ≤ Nat.card ↥(commOn ρ L ⊤) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p => ⟨σ p.1 + p.2, Submodule.add_mem _ (hσ p.1).1 p.2.2.1⟩) ?_
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have h1 : σ y + z = σ y' + z' := congrArg Subtype.val h
    have h2 : y = y' := by
      have h3 := congrArg ψ h1
      rwa [map_add, map_add, (hσ y).2, (hσ y').2, hψ0 z z.2, hψ0 z' z'.2, add_zero, add_zero] at h3
    subst h2
    rw [Subtype.ext (add_left_cancel h1)]
  have hfix : Nat.card ↥(fixOn ρ S (commOn ρ L ⊤)) ≤
      Nat.card ↥(fixV f.range) * Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) := by
    rw [← Nat.card_prod]
    have hmemZ : ∀ x ∈ commOn ρ L ⊤, x - σ (ψ x) ∈ commOn ρ L ⊤ ⊓ fixSub ρ L := fun x hx =>
      have h1 := Submodule.sub_mem _ hx (hσ (ψ x)).1
      ⟨h1, (hψ _ h1).1 (by rw [map_sub, (hσ _).2, sub_self])⟩
    have hmemV : ∀ x ∈ fixOn ρ S (commOn ρ L ⊤), Multiplicative.ofAdd (ψ x) ∈ fixV f.range := by
      rintro x ⟨hxU, hxS⟩ _ ⟨s, rfl⟩
      exact congrArg Multiplicative.ofAdd
        ((psi_apply_sec hσ hψ (hSN s.2) hxU).trans (congrArg ψ (hxS s s.2)))
    refine Nat.card_le_card_of_injective (fun x => (⟨_, hmemV x x.2⟩, ⟨_, hmemZ x x.2.1⟩)) fun x x' h => ?_
    have h1 : ψ x = ψ x' :=
      Multiplicative.ofAdd.injective (congrArg (fun p => (p.1 : StdMod (Fin 2) F)) h)
    have h2 : (x : V) - σ (ψ x) = x' - σ (ψ x') := congrArg (fun p => (p.2 : V)) h
    rw [h1] at h2
    exact Subtype.ext (sub_left_inj.1 h2)
  have hoff' : Nat.card (StdMod (Fin 2) F) ≤ Nat.card f.range * Nat.card ↥(fixV f.range) := by
    have hpos : 0 < Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) * Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card (Fin 2 → F) * (Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) *
          Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)))
        = Nat.card (Fin 2 → F) * Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) *
          Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) := by ring
      _ ≤ Nat.card ↥(commOn ρ L ⊤) * Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) := Nat.mul_le_mul_right _ hU
      _ ≤ Nat.card ↥S * Nat.card ↥(fixOn ρ S (commOn ρ L ⊤)) := hoff
      _ ≤ Nat.card ↥S * (Nat.card ↥(fixV f.range) * Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L)) :=
          Nat.mul_le_mul_left _ hfix
      _ = Nat.card f.range * Nat.card ↥(fixV f.range) * (Nat.card ↥(commOn ρ L ⊤ ⊓ fixSub ρ L) *
          Nat.card ↥(cenOn ρ S (commOn ρ L ⊤))) := by rw [hS]; ring
  have hle := CFSG.Quasithin.B69.le_natImage_of_offender hn hF hEN hE2 hEc hoff'
  intro s hs
  obtain ⟨γ, hγ⟩ := hle (MonoidHom.mem_range.2 ⟨⟨s, hs⟩, rfl⟩)
  obtain ⟨l, rfl⟩ := φ.surjective γ
  rw [← natTau_of_mem hσ hψ hE l] at hγ
  have h1 : natTau hσ hψ (⟨l, Subgroup.le_normalizer l.2⟩⁻¹ * ⟨s, hSN hs⟩) = 1 := by
    rw [map_mul, map_inv, hγ]
    exact inv_mul_cancel _
  rw [natTau_eq_one_iff hσ hψ] at h1
  have h2 := apply_eq_self_of_sub_mem_fixSub hUL hnt
    (mul_mem (inv_mem (Subgroup.le_normalizer l.2)) (hSN hs)) h1
  refine ⟨l, l.2, fun u hu => ?_⟩
  have h3 : ρ (l : G)⁻¹ (ρ s u) = u := by rw [← glRep_mul_apply]; exact h2 u hu
  calc ρ s u = ρ (l : G) (ρ (l : G)⁻¹ (ρ s u)) := (glRep_apply_inv ρ _ _).symm
    _ = ρ l u := by rw [h3]

theorem exists_eq_apply_of_natL2_of_mem_hP [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponentOf L ⊤) [IsSimpleGroup ↥L]
    (hUL : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤) (hnt : ¬ commOn ρ L ⊤ ≤ fixSub ρ L)
    {n : ℕ} (hn : 1 ≤ n) (hnat : NatL2 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) n) :
    ∀ g ∈ hP ρ, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u := by
  let T : Subgroup G :=
    { carrier := {g | ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u}
      mul_mem' := by
        rintro a b ⟨l, hl, ha⟩ ⟨m, hm, hb⟩
        refine ⟨l * m, mul_mem hl hm, fun u hu => ?_⟩
        rw [glRep_mul_apply, glRep_mul_apply, hb u hu,
          ha _ (commOn_top_mapsTo (Subgroup.le_normalizer hm) hu)]
      one_mem' := ⟨1, one_mem _, fun u _ => rfl⟩
      inv_mem' := by
        rintro a ⟨l, hl, ha⟩
        refine ⟨l⁻¹, inv_mem hl, fun u hu => ?_⟩
        have hu' := commOn_top_mapsTo (Subgroup.le_normalizer (inv_mem hl)) hu
        calc ρ a⁻¹ u = ρ a⁻¹ (ρ a (ρ l⁻¹ u)) := by rw [ha _ hu', glRep_apply_inv]
          _ = ρ l⁻¹ u := glRep_inv_apply ρ _ _ }
  have hle : hP ρ ≤ T := iSup₂_le fun A hA s hs =>
    exists_eq_apply_of_natL2 hUL hnt hn hnat (isElementaryAbelian_of_mem_calP hA)
      (le_normalizer_of_mem_calP hρ hL hA) ((isBestOffenderOn_of_mem_calP hρ hA).isOffenderOn_of_le _).2 s hs
  exact fun g hg => hle hg

theorem map_subgroupOf_eq_alternatingGroup {L : Subgroup G} {a : G} (ha2 : a * a = 1)
    (hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L) (haL : a ∉ L) {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (φ : ↥(L ⊔ Subgroup.zpowers a) ≃* Equiv.Perm Ω) :
    (L.subgroupOf (L ⊔ Subgroup.zpowers a)).map φ.toMonoidHom = alternatingGroup Ω := by
  refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
  rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective,
    Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩, fun h => haL h, fun b => ?_⟩
  rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers ha2 hnorm b.2 with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem exists_conj_eq_of_mulEquiv_perm {L : Subgroup G} {a : G} (ha2 : a * a = 1)
    (hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L) (haL : a ∉ L) (φ : ↥(L ⊔ Subgroup.zpowers a) ≃* Equiv.Perm (Fin 5))
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ l ∈ L, g * l * g⁻¹ = h * l * h⁻¹ := by
  have hmap := map_subgroupOf_eq_alternatingGroup ha2 hnorm haL φ
  obtain ⟨eL, heL⟩ : ∃ eL : ↥L ≃* ↥(alternatingGroup (Fin 5)), ∀ x : ↥L,
      (eL x : Equiv.Perm (Fin 5)) = φ (Subgroup.inclusion le_sup_left x) :=
    ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans
      (((L.subgroupOf (L ⊔ Subgroup.zpowers a)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
        (MulEquiv.subgroupCongr hmap)), fun x => rfl⟩
  obtain ⟨π, hπ⟩ := CFSG.Semidihedral.Principal.CyclicAlternatingFive.conjNormal_surjective
    (eL.symm.trans ((L.normalizerMonoidHom ⟨g, hg⟩).trans eL))
  refine ⟨φ.symm π, (φ.symm π).2, fun l hl => ?_⟩
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hπ (eL ⟨l, hl⟩))
  rw [MulAut.conjNormal_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    heL, heL] at h1
  have h2 : φ (φ.symm π * Subgroup.inclusion le_sup_left ⟨l, hl⟩ * (φ.symm π)⁻¹) =
      φ (Subgroup.inclusion le_sup_left ((L.normalizerMonoidHom ⟨g, hg⟩) ⟨l, hl⟩)) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  have h3 : ((L.normalizerMonoidHom ⟨g, hg⟩) ⟨l, hl⟩ : G) = g * l * g⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨g, hg⟩ ⟨l, hl⟩
  rw [← h3]
  exact (congrArg Subtype.val (φ.injective h2)).symm

theorem apply_eq_self_of_commute_of_perm {L : Subgroup G} {U : Submodule (ZMod 2) V}
    (ψ : V →+ (Fin 5 → ZMod 2)) (hK : ∀ x ∈ U, ψ x = 0 → x = 0) (hsum : ∀ x ∈ U, ∑ i, ψ x i = 0)
    (hsurj : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → ∃ x ∈ U, ψ x = y)
    (hA5 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, ∀ x ∈ U,
      ρ l x ∈ U ∧ ψ (ρ l x) = fun i => ψ x (τ.symm i))
    {c : G} (hcU : ∀ u ∈ U, ρ c u ∈ U) (hc : ∀ l ∈ L, c * l = l * c) : ∀ u ∈ U, ρ c u = u := by
  classical
  let ψU : ↥U →ₗ[ZMod 2] ↥(CFSG.Quasithin.permCore 5) :=
    LinearMap.codRestrict _ ((ψ.toZModLinearMap 2).comp U.subtype) fun u => hsum u u.2
  have hinj : Function.Injective ψU := fun u u' h => by
    have h1 : ψ ((u : V) - u') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    exact Subtype.ext (sub_eq_zero.1 (hK _ (Submodule.sub_mem _ u.2 u'.2) h1))
  have hsur : Function.Surjective ψU := fun y => by
    obtain ⟨x, hx, hxy⟩ := hsurj y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : ↥U ≃ₗ[ZMod 2] ↥(CFSG.Quasithin.permCore 5) := LinearEquiv.ofBijective ψU ⟨hinj, hsur⟩
  let cU : ↥U →ₗ[ZMod 2] ↥U := (ρ c).restrict hcU
  let T : ↥(CFSG.Quasithin.permCore 5) →ₗ[ZMod 2] ↥(CFSG.Quasithin.permCore 5) :=
    e.toLinearMap ∘ₗ cU ∘ₗ e.symm.toLinearMap
  have hT : ∀ u : ↥U, T (e u) = e ⟨ρ c u, hcU u u.2⟩ := fun u => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, hb⟩ := CFSG.Quasithin.G11.permCore_five_endo_scalar T (by
    intro τ y y' hyy'
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨l, hl, hlU⟩ := hA5 τ τ.2
    have h1 : y' = e ⟨ρ l u, (hlU u u.2).1⟩ := Subtype.ext (hyy'.trans (hlU u u.2).2.symm)
    subst h1
    rw [hT, hT]
    show ψ (ρ c (ρ l u)) = CFSG.Quasithin.permAct (τ : Equiv.Perm (Fin 5)) (ψ (ρ c u))
    rw [← glRep_mul_apply, hc l hl, glRep_mul_apply]
    exact (hlU _ (hcU u u.2)).2)
  obtain ⟨x₀, hx₀, hψx₀⟩ := hsurj ![1, 1, 0, 0, 0] (by decide)
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with h0 | h1
  · exfalso
    have h2 := hb (e ⟨x₀, hx₀⟩)
    rw [hT, h0, zero_smul, LinearEquiv.map_eq_zero_iff] at h2
    have h3 : ρ c x₀ = 0 := congrArg Subtype.val h2
    have h4 : x₀ = 0 := by
      calc x₀ = ρ c⁻¹ (ρ c x₀) := (glRep_inv_apply ρ c x₀).symm
        _ = 0 := by rw [h3, map_zero]
    rw [h4, map_zero] at hψx₀
    exact absurd (congrFun hψx₀ 0) (by decide)
  · intro u hu
    have h2 := hb (e ⟨u, hu⟩)
    rw [hT, h1, one_smul] at h2
    exact congrArg Subtype.val (e.injective h2)

theorem exists_eq_apply_of_secNatS5 {L : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (haL : a ∉ L)
    (hS5 : SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ h u := by
  obtain ⟨-, -, -, φ, ψ, -, hK, hsum, hsurj, hE⟩ := hS5
  have hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L := fun m hm => (Subgroup.mem_normalizer_iff.1 haN m).1 hm
  have hHN : L ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 haN)
  obtain ⟨h, hh, hconj⟩ := exists_conj_eq_of_mulEquiv_perm ha2 hnorm haL φ hg
  have hmap := map_subgroupOf_eq_alternatingGroup ha2 hnorm haL φ
  have hA5 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, ∀ x ∈ commOn ρ L ⊤,
      ρ l x ∈ commOn ρ L ⊤ ∧ ψ (ρ l x) = fun i => ψ x (τ.symm i) := by
    intro τ hτ
    rw [← hmap, Subgroup.mem_map_equiv] at hτ
    have hτL : ((φ.symm τ : ↥(L ⊔ Subgroup.zpowers a)) : G) ∈ L := Subgroup.mem_subgroupOf.1 hτ
    refine ⟨(φ.symm τ : G), hτL, fun x hx => ⟨commOn_top_mapsTo (Subgroup.le_normalizer hτL) hx, ?_⟩⟩
    rw [hE (φ.symm τ) x hx, MulEquiv.apply_symm_apply]
  have hc : ∀ l ∈ L, h⁻¹ * g * l = l * (h⁻¹ * g) := fun l hl => by
    have h1 := hconj l hl
    calc h⁻¹ * g * l = h⁻¹ * (g * l * g⁻¹) * g := by group
      _ = h⁻¹ * (h * l * h⁻¹) * g := by rw [h1]
      _ = l * (h⁻¹ * g) := by group
  have hfix := apply_eq_self_of_commute_of_perm ψ (fun x hx h0 => (Submodule.mem_bot _).1 (hK x hx h0))
    hsum hsurj hA5 (fun u hu => commOn_top_mapsTo (mul_mem (inv_mem (hHN hh)) hg) hu) hc
  refine ⟨h, hh, fun u hu => ?_⟩
  calc ρ g u = ρ h (ρ (h⁻¹ * g) u) := by rw [glRep_mul_apply, glRep_apply_inv]
    _ = ρ h u := by rw [hfix u hu]

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
