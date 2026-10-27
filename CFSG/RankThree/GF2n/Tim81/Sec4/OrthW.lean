module

public import CFSG.RankThree.GF2n.Tim81.Sec4.HBarData
public import CFSG.RankThree.GF2n.Tim81.Sec4.MinimalNormal
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelConj

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open RootHyp
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

private theorem subW_self_eq_top
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] :
    subW (hW := hW) (Tim79a.xOf V H) = ⊤ := by
  ext x
  rw [← ofW_toW hW x, mem_subW_iff]
  simp

theorem IsOrthModule.repW_of_subRepW
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F))
    (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
        (Tim79a.H_le_normalizer_xOf V H))) :
    Sec2.IsOrthModule hl (repW (hW := hW) ψ) := by
  obtain ⟨j, β, hβ⟩ := horth
  let U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    subW (hW := hW) (Tim79a.xOf V H)
  have hUt : U = ⊤ := subW_self_eq_top (V := V) (H := H) hW
  let e : U ≃ₗ[ZMod 2] Additive (IntMod (Tim79a.xOf V H) hW) :=
    (LinearEquiv.ofEq U ⊤ hUt).trans Submodule.topEquiv
  let β' : Additive (IntMod (Tim79a.xOf V H) hW) ≃+ ↥(hermA l F) :=
    e.symm.toAddEquiv.trans β
  refine ⟨j, β', ?_⟩
  intro g x
  let u : U := e.symm x
  have hx : e u = x := e.apply_symm_apply x
  have hsub : e (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
      (Tim79a.H_le_normalizer_xOf V H) g u) = repW (hW := hW) ψ g x := by
    change ((CFSG.Quasithin.B45U33.subRep (repW (hW := hW) ψ)
        (subW (hW := hW) (Tim79a.xOf V H))
        ((normalizer_subW_iff hW ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)).mp
          (Tim79a.H_le_normalizer_xOf V H)) g u : U) :
          Additive (IntMod (Tim79a.xOf V H) hW)) = repW (hW := hW) ψ g x
    rw [CFSG.Quasithin.B45U33.subRep_apply]
    rw [← hx, show e u = (u : Additive (IntMod (Tim79a.xOf V H) hW)) from rfl]
  calc β' (repW (hW := hW) ψ g x)
      = β (e.symm (repW (hW := hW) ψ g x)) := rfl
    _ = β (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
          (Tim79a.H_le_normalizer_xOf V H) g u) := by
        rw [← hsub, e.symm_apply_apply]
    _ = hermAct l (sig_sig hl) (fieldAut F j g) (β u) := hβ g u
    _ = hermAct l (sig_sig hl) (fieldAut F j g) (β' x) := by
        rw [show β' x = β u from rfl]

theorem RootHyp.transitiveFixed_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ)) :
    TransitiveFixed (V := V) (H := H) hPH hW ψ (inferInstance) := by
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ.toMonoidHom
  have hs := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hA2 : ∀ a ∈ A, a * a = 1 := hs.1
  have hA : Nat.card A = 2 ^ (2 * l) := by
    rw [hs.2.1, hl]
  intro v hv w hw hv0 hw0
  exact Sec2.IsOrthModule.normalizer_transitive_fixed hl horth A hA2 hA hv hw hv0 hw0

theorem RootHyp.pCore_eq_Pc_and_of_isOrthModule
    (h : RootHyp M V) {H : Subgroup G} (hHmem : IsHMember M V H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ)) :
    inSubgroup (pCore 2) M = Pc M V ∧
      inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V ∧
      inSubgroup frattini (inSubgroup (pCore 2) M) = V ∧
      inSubgroup commutator (inSubgroup (pCore 2) M) = V := by
  have hPH : Pc M V ≤ H := hHmem.2.1
  have hnM : ¬ H ≤ M := hHmem.2.2
  exact RootHyp.pCore_eq_Pc_and_of_transitiveFixed h hHmem hW ψ (inferInstance)
    (RootHyp.transitiveFixed_of_isOrthModule h hPH hVH hH hnM hW ψ hl horth)

private theorem exists_conj_mem_V_of_mem_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ))
    {d : G} (hd : d ∈ Tim79a.xOf V H)
    (hex : ∃ x : G, ∃ v ∈ V, v ≠ 1 ∧ d = x * v * x⁻¹) :
    ∃ k ∈ H, ∃ e ∈ V, e ≠ 1 ∧ k * d * k⁻¹ = e := by
  obtain ⟨x, v, hvV, hv1, rfl⟩ := hex
  let dW : ↥(Tim79a.xOf V H) := ⟨x * v * x⁻¹, hd⟩
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ.toMonoidHom
  have hsA := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hA2 : ∀ a ∈ A, a * a = 1 := hsA.1
  have hA : Nat.card A = 2 ^ (2 * l) := by
    rw [hsA.2.1, hl]
  obtain ⟨g, hg⟩ := Sec2.IsOrthModule.exists_conj_mem_commSub hl horth A hA2 hA
    (ofW hW dW)
  obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm g)
  have hpsi : ψ (piK V H z) = g := by
    rw [hz, MulEquiv.apply_symm_apply]
  have hg' := hg
  rw [← hpsi, repW_apply_piK, toW_ofW] at hg'
  have hsub : ofW hW (conjH V H z dW) ∈ subW (hW := hW) ⁅Tim79a.xOf V H, Pc M V⁆ := by
    rw [← commSub_repW hW ψ hPH]
    exact hg'
  have hconjW : ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) ∈ ⁅Tim79a.xOf V H, Pc M V⁆ :=
    (mem_subW_iff hW).mp hsub
  have hle : ⁅Tim79a.xOf V H, Pc M V⁆ ≤ Tim79a.xOf V H ⊓ Pc M V := by
    simpa [conjSubgroup_one] using commutator_xOf_conj_Pc_le h hPH hVH (x := 1) H.one_mem
  have hconjP : ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) ∈ Pc M V :=
    (Subgroup.mem_inf.mp (hle hconjW)).2
  have hzx : ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) =
      (z : G) * (x * v * x⁻¹) * (z : G)⁻¹ := by
    rw [conjH_apply_coe]
  have hmemV : v ∈ V ⊓ conjSubgroup ((z : G) * x)⁻¹ (Pc M V) := by
    refine ⟨hvV, ?_⟩
    change v ∈ conjSubgroup ((z : G) * x)⁻¹ (Pc M V)
    rw [mem_conjSubgroup]
    rw [inv_inv]
    have hcalc : (z : G) * x * v * (z * x)⁻¹ =
        ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) := by
      rw [hzx]; group
    rw [hcalc]
    exact hconjP
  have hne : V ⊓ conjSubgroup ((z : G) * x)⁻¹ (Pc M V) ≠ ⊥ := by
    intro hbot
    have : v = 1 := Subgroup.mem_bot.mp (hbot ▸ hmemV)
    exact hv1 this
  have hEq : conjSubgroup ((z : G) * x) V = V := by
    have := conj_eq_of_inf_conj_Pc_ne_bot h hne
    have hconj := congrArg (conjSubgroup ((z : G) * x)) this
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CGT.Timmesfeld75.conjSubgroup_one] at hconj
    exact hconj.symm
  refine ⟨z, z.2, (conjH V H z dW : ↥(Tim79a.xOf V H)), ?_, ?_, ?_⟩
  · have heq : ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) =
        ((z : G) * x) * v * ((z : G) * x)⁻¹ := by
      rw [hzx]; group
    rw [heq]
    rw [← hEq]
    exact Subgroup.mem_map_of_mem _ hvV
  · intro h1
    have h2 : (z : G)⁻¹ * ((conjH V H z dW : ↥(Tim79a.xOf V H)) : G) * (z : G) =
        x * v * x⁻¹ := by
      rw [hzx]; group
    rw [h1] at h2
    have h3 : v = 1 := by
      have := congrArg (fun w => x⁻¹ * w * x) h2
      simpa [mul_assoc] using this.symm
    exact hv1 h3
  · exact hzx.symm

theorem RootHyp.mem_conjSubgroup_iff_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ))
    {d : G} (hd : d ∈ Tim79a.xOf V H) :
    (∃ x : G, ∃ v ∈ V, v ≠ 1 ∧ d = x * v * x⁻¹) ↔
      (d ≠ 1 ∧ ∃ g ∈ H, d ∈ conjSubgroup g V) := by
  constructor
  · intro hex
    obtain ⟨k, hkH, e, heV, he1, hke⟩ :=
      exists_conj_mem_V_of_mem_xOf h hPH hVH hH hnM hW ψ hl horth hd hex
    refine ⟨?_, ⟨k⁻¹, H.inv_mem hkH, ?_⟩⟩
    · intro hd1
      apply he1
      rw [← hke, hd1]
      simp
    · rw [mem_conjSubgroup]
      rw [inv_inv, hke]
      exact heV
  · rintro ⟨hd1, g, hgH, hgd⟩
    obtain ⟨v, hvV, hvd⟩ := Subgroup.mem_map.mp hgd
    refine ⟨g, v, hvV, ?_, ?_⟩
    · intro hv1
      apply hd1
      rw [← hvd, hv1]
      simp [MulAut.conj_apply]
    · rw [← hvd]
      rfl

theorem RootHyp.exists_conj_eq_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ))
    {d z : G} (hd : d ∈ Tim79a.xOf V H) (hz : z ∈ V) (hz1 : z ≠ 1)
    (hex : ∃ x : G, ∃ v ∈ V, v ≠ 1 ∧ d = x * v * x⁻¹) :
    ∃ g ∈ H, d = g * z * g⁻¹ := by
  obtain ⟨k, hkH, e, heV, he1, hke⟩ :=
    exists_conj_mem_V_of_mem_xOf h hPH hVH hH hnM hW ψ hl horth hd hex
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ.toMonoidHom
  let eW : ↥(Tim79a.xOf V H) := ⟨e, le_xOf_self V H heV⟩
  let zW : ↥(Tim79a.xOf V H) := ⟨z, le_xOf_self V H hz⟩
  have heFix : ofW hW eW ∈ fixedSub (repW (hW := hW) ψ) A := by
    change ofW hW eW ∈ fixedSub (repW (hW := hW) ψ)
      ((imgK V H (Pc M V)).map ψ)
    rw [fixedSub_repW hW ψ hPH, mem_subW_iff, xOf_inf_centralizer_Pc_eq_V h]
    exact heV
  have hzFix : ofW hW zW ∈ fixedSub (repW (hW := hW) ψ) A := by
    change ofW hW zW ∈ fixedSub (repW (hW := hW) ψ)
      ((imgK V H (Pc M V)).map ψ)
    rw [fixedSub_repW hW ψ hPH, mem_subW_iff, xOf_inf_centralizer_Pc_eq_V h]
    exact hz
  have he0 : ofW hW eW ≠ 0 := by
    intro h0
    have := congrArg (toW hW) h0
    exact he1 (by simpa [eW] using congrArg Subtype.val this)
  have hz0 : ofW hW zW ≠ 0 := by
    intro h0
    have := congrArg (toW hW) h0
    exact hz1 (by simpa [zW] using congrArg Subtype.val this)
  have htrans := RootHyp.transitiveFixed_of_isOrthModule h hPH hVH hH hnM hW ψ hl horth
  obtain ⟨n, -, hnv⟩ := htrans _ heFix _ hzFix he0 hz0
  obtain ⟨y, hy⟩ := piK_surjective V H (ψ.symm n)
  have hpsi : ψ (piK V H y) = n := by
    rw [hy, MulEquiv.apply_symm_apply]
  have hrep : repW (hW := hW) ψ n (ofW hW eW) = ofW hW (conjH V H y eW) := by
    rw [← hpsi, repW_apply_piK, toW_ofW]
  have hinj : Function.Injective (ofW hW) := ofW_injective hW
  have hconj : conjH V H y eW = zW := hinj (by rw [← hrep, hnv])
  have hconj' : (y : G) * e * (y : G)⁻¹ = z := by
    have := congrArg Subtype.val hconj
    simpa [conjH_apply_coe] using this
  have he_eq : e = (y : G)⁻¹ * z * (y : G) := by
    calc e = (y : G)⁻¹ * ((y : G) * e * (y : G)⁻¹) * (y : G) := by group
      _ = (y : G)⁻¹ * z * (y : G) := by rw [hconj']
  have hd_eq : d = k⁻¹ * e * k := by
    rw [← hke]
    group
  refine ⟨k⁻¹ * (y : G)⁻¹, H.mul_mem (H.inv_mem hkH) (H.inv_mem y.2), ?_⟩
  rw [hd_eq, he_eq]
  group

end CFSG.RankThree.GF2n.Tim81
