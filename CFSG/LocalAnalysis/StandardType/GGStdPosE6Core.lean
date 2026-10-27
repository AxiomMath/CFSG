module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
import CFSG.LocalAnalysis.StandardType.GGStdPosIsogCore
import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerCube
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.ClassicalInvolution Pointwise

namespace StdPosExc

private theorem exists_mem_centralizer_e6
    {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) {c : G}
    (hcn : c ∈ Subgroup.normalizer (ψ.range : Set G)) {p : ℕ} (hp3 : Nat.Coprime p 3)
    (hcp : c ^ p = 1) (hc : GGPsiInnerDiag (e6Datum k) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hc
  have e3 : ∀ y z : G, (y ^ 3)⁻¹ * z * y ^ 3 = y⁻¹ * (y⁻¹ * (y⁻¹ * z * y) * y) * y :=
    fun y z => by simp only [pow_three, mul_inv_rev, mul_assoc]
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  obtain ⟨u, hu⟩ := PsiDiag.exists_mul_psi_mem_centralizer_cube
    (e6Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E6 k posDef_cartan_E6
      neighbour_E6 O).2 rfl (e6Datum_isCTGroupDatum k).iSup_eq_top
    (fun a' => PsiDiag.exists_prod_zpow_cartan_cube (A := (e6Datum k).cartan) _ (m := 3)
      TableB.cartanE6_adj a') ψ hker (d := (c * g) ^ 3)
    (fun i => ⟨a i, fun t => by
      rw [e3, (ha i t).1, (ha i _).1, (ha i _).1,
        show (a i : k) * ((a i : k) * ((a i : k) * t)) = (a i : k) ^ 3 * t by ring]⟩)
    (fun i => ⟨fun t => (((a i)⁻¹ : kˣ) : k) * ((((a i)⁻¹ : kˣ) : k) * ((((a i)⁻¹ : kˣ) : k) * t)),
      fun t => by rw [e3, (ha i t).2, (ha i _).2, (ha i _).2]⟩)
  have hpw : ∀ m : ℕ, ∃ g' ∈ ψ.range, (c * g) ^ m = c ^ m * g' := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨g', hg', h⟩ := ih
      have h1 : c⁻¹ * g' * c ∈ ψ.range := by
        simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hcn) g').1 hg'
      exact ⟨c⁻¹ * g' * c * g, mul_mem h1 hg, by rw [pow_succ, h, pow_succ]; group⟩
  obtain ⟨g', hg', hgp⟩ := hpw p
  have hp' : (c * g) ^ p ∈ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set G) :=
    Subgroup.mem_sup_left (by rw [hgp, hcp, one_mul]; exact hg')
  have h3 : (c * g) ^ 3 ∈ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set G) := by
    rw [show (c * g) ^ 3 = (c * g) ^ 3 * ψ u * (ψ u)⁻¹ by group]
    exact mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left (inv_mem ⟨u, rfl⟩))
  obtain ⟨u1, v1, h⟩ : IsCoprime (p : ℤ) ((3 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hp3
  have hy : c * g = ((c * g) ^ p) ^ u1 * ((c * g) ^ 3) ^ v1 := by
    rw [← zpow_natCast, ← zpow_natCast (c * g) 3, ← zpow_mul, ← zpow_mul, ← zpow_add,
      mul_comm (p : ℤ) u1, mul_comm ((3 : ℕ) : ℤ) v1, h, zpow_one]
  have hcm : c ∈ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set G) := by
    rw [show c = c * g * g⁻¹ by group, hy]
    exact mul_mem (mul_mem (zpow_mem hp' u1) (zpow_mem h3 v1))
      (Subgroup.mem_sup_left (inv_mem hg))
  have hmul : c ∈ (ψ.range : Set G) * (Subgroup.centralizer (ψ.range : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (Subgroup.centralizer_le_normalizer _)]
    exact hcm
  obtain ⟨x, hx, t, ht, rfl⟩ := Set.mem_mul.1 hmul
  refine ⟨x⁻¹, inv_mem hx, ?_⟩
  rwa [Subgroup.mem_centralizer_iff.1 ht x hx, mul_inv_cancel_right]

private theorem mem_ggTorus_e6Datum
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {h : ↥(e6Data_valid.minGroup F)}
    (hh : ((e6Isogeny F h : adjointGroup .E6 F) : ModGL .E6 F) ∈ torusGroup .E6 F) :
    h ∈ ggTorus (e6Datum F) := by
  have hN : ∀ {γ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ → torusGroup .E6 F ≤
      (Subgroup.normalizer (rootGroup (rootOperatorFamily .E6) F γ :
        Set (adjointGroup .E6 F))).map (adjointGroup .E6 F).subtype := fun hγ => by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨torusElement .E6 F i s, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    refine fun x => ⟨torusElement_conj_mem i s hγ, fun hx => ?_⟩
    have h := torusElement_conj_mem (F := rootOperatorFamily .E6) i s⁻¹ hγ hx
    have e : ∀ t : ↥(adjointGroup .E6 F), t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := fun t => by group
    rwa [show torusElement .E6 F i s⁻¹ = (torusElement .E6 F i s)⁻¹ from
      map_inv (torusHom (τ := .E6) F i) s, e] at h
  have key : ∀ w : ↥(e6Data_valid.minGroup F),
      ((e6Isogeny F w : adjointGroup .E6 F) : ModGL .E6 F) ∈ torusGroup .E6 F →
      ∀ {γ}, IsRoot .E6 γ → ∀ x ∈ e6Data_valid.rootGroup F γ,
        w * x * w⁻¹ ∈ e6Data_valid.rootGroup F γ := by
    intro w hw γ hγ x hx
    have hmap := ModelFacts.map_e6Isogeny_rootGroup F hγ
    obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 (hN hγ hw)
    rw [show v = e6Isogeny F w from Subtype.ext hve] at hv
    obtain ⟨x', hx', he⟩ : e6Isogeny F (w * x * w⁻¹) ∈
        (e6Data_valid.rootGroup F γ).map (e6Isogeny F) := by
      rw [hmap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hv _).1 (hmap ▸ Subgroup.mem_map_of_mem _ hx)
    have hζ : x'⁻¹ * (w * x * w⁻¹) ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hsq : ∀ y ∈ e6Data_valid.rootGroup F γ, y * y = 1 := fun y hy => by
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup F).1 hy
      rw [← MinData.Valid.xm_add, CharTwo.add_self_eq_zero, MinData.Valid.xm_zero]
    have hcomm := Subgroup.mem_center_iff.1
      (ModelFacts.ChevAut.e6Isogeny_ker_le_center F hζ) x'⁻¹
    have h2 : (x'⁻¹ * (w * x * w⁻¹)) ^ 2 = 1 := by
      rw [pow_two]
      calc _ = x'⁻¹ * (x'⁻¹ * (w * x * w⁻¹)) * (w * x * w⁻¹) := by rw [hcomm]; group
        _ = (x' * x')⁻¹ * (w * (x * x) * w⁻¹) := by group
        _ = 1 := by rw [hsq x hx, hsq x' hx']; group
    have h1 : (⟨_, hζ⟩ : (e6Isogeny F).ker) = 1 := orderOf_eq_one_iff.1 <|
      Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker F))
        (orderOf_dvd_of_pow_eq_one (Subtype.ext h2)) (orderOf_dvd_natCard _)
    rw [← inv_mul_eq_one.1 (congrArg Subtype.val h1)]
    exact hx'
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  have hγ' : IsRoot .E6 γ := (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 F).1 hγ
  have hh' : ((e6Isogeny F h⁻¹ : adjointGroup .E6 F) : ModGL .E6 F) ∈ torusGroup .E6 F := by
    rw [map_inv, Subgroup.coe_inv]
    exact inv_mem hh
  rw [Subgroup.mem_normalizer_iff]
  refine fun z => ⟨key h hh hγ' z, fun hz => ?_⟩
  have := key h⁻¹ hh' hγ' _ hz
  rwa [show h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z by group] at this

theorem exists_stdPos_e6
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type} [Group G] [Finite G] {ψ : ↥(e6Data_valid.minGroup F) →* G} {p : ℕ}
    {Bs : Subgroup G} (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F))
    (hp3 : Nat.Coprime p 3) (hBs : IsElemAbelian p Bs)
    (hBN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (e6Datum F) ψ b)
    (hc : p ^ 6 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs)
    (hT : GGExcToralRankInput .E6 F p) :
    ∃ s : ↥(e6Data_valid.minGroup F),
      GGKGPosStdPos (e6Datum F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs :=
  exists_stdPos_of_toral_isog (V := TableBExc.torusPow .E6 F p) (r := 6)
    (e6Isogeny_surjective F) center_adjointGroup_eq_bot
    (ModelFacts.ChevAut.e6Isogeny_ker_le_center F)
    (fun _ hv => mem_ggTorus_e6Datum (TableBExc.mem_torusPow.1 (Subgroup.mem_comap.1 hv)).1)
    hker (fun E hE hE6 => (hT E hE hE6).imp fun _ h => h.le) hBs
    (fun b hb => exists_mem_centralizer_e6 ψ hker (hBN hb) hp3 (hBs.2 b hb) (hinn b hb)) hc

end StdPosExc

end CFSG.StandardType

end
