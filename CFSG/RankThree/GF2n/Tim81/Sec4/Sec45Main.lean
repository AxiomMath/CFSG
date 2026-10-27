module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbTheta
public import CFSG.RankThree.GF2n.Tim81.Sec4.Prop43
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTI
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbEta

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem isNatSumModule_of_subsingleton
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Subsingleton W]
    (ρ : Representation (ZMod 2) SL(2, F) W) : Sec2.IsNatSumModule ρ := by
  letI : Module (ZMod 2) (Fin 0 → Fin 2 → F) :=
    AddCommGroup.zmodModule (fun v => by
      ext i
      exact i.elim0)
  refine ⟨0, (LinearEquiv.ofSubsingleton (R := ZMod 2) W (Fin 0 → Fin 2 → F)).toAddEquiv, ?_⟩
  intro g w i
  exact i.elim0

private theorem kModWNatSum_of_eq_xOf {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (hKW : kOf V H = Tim79a.xOf V H)
    [hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal] :
    KModWNatSum V H ψ := by
  intro hs hmod
  letI := hmod
  haveI : Subsingleton (SecMod hs) :=
    ⟨fun a b => by
      obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs a
      obtain ⟨m, rfl⟩ := SecMod.mk_surjective hs b
      rw [(SecMod.mk_eq_zero_iff hs n).mpr (hKW ▸ n.2),
        (SecMod.mk_eq_zero_iff hs m).mpr (hKW ▸ m.2)]⟩
  exact isNatSumModule_of_subsingleton _

private theorem sec45Shape_of_abelian
    (h : RootHyp M V) (H : Subgroup G) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hmem : IsHMember M V H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    (hL : IsL2OrSz V H)
    (hK : KFactorization M V H h₀)
    (haber : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    Sec45Shape M V H h₀ := by
  classical
  have hPH : Pc M V ≤ H := hH ▸ le_sup_left
  have hnM : ¬ H ≤ M := hmem.2.2
  have hW := h.isElemAbelian_xOf hPH hVH
  letI hmodW := moduleOfElemAbelian hW
  obtain ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, horth, hKW, hcardV, hcardW⟩ :=
    exists_orth_xOf_of_kOf_abelian (hW := hW) h hPH hVH hH hnM hK haber hL
  letI := hField
  letI := hFintype
  letI := hCharP
  have horth' : Sec2.IsOrthModule hl (repW (hW := hW) ψ) := horth
  have hcentW : Tim79a.xOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hW.1
  have hcenterK : kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) =
      Tim79a.xOf V H := by
    rw [hKW]
    exact inf_eq_left.mpr hcentW
  have hcenterPK : Pc M V ⊓ kOf V H ⊓
      Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) =
      Pc M V ⊓ Tim79a.xOf V H := by
    rw [hKW]
    refine inf_eq_left.mpr ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx.2⟩ ⟨y, hy.2⟩)).symm
  have hsq : ∀ k ∈ kOf V H, k * k ∈ Tim79a.xOf V H := by
    intro k hk
    rw [hKW] at hk
    have hk1 : k * k = 1 := by simpa [pow_two] using hW.2 k hk
    rw [hk1]
    exact (Tim79a.xOf V H).one_mem
  refine ⟨hH, hmem, hVH, hK, ⟨F, hField, hFintype, hCharP, l, hl, ψ, ?_⟩⟩
  refine ⟨hl1, hcardV, hcardW, ?_, hcenterK, hcenterPK, hsq, ?_, Or.inl hKW⟩
  · intro hW' hmod'
    exact Sec45ShapeWith.isOrthModule_repW_of_one (hW := hW) (inst := hmodW) ψ hl horth' hW'
      hmod'
  · haveI hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := by
      rw [hKW, Subgroup.subgroupOf_self]
      infer_instance
    exact kModWNatSum_of_eq_xOf (H := H) (V := V) ψ hKW (hWnormal := hWnormal)

private theorem sec45Shape_of_nonabelian
    (h : RootHyp M V) (H : Subgroup G) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hmem : IsHMember M V H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    (hL : IsL2OrSz V H)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) :
    Sec45Shape M V H h₀ := by
  classical
  have hPH : Pc M V ≤ H := hH ▸ le_sup_left
  have hnM : ¬ H ≤ M := hmem.2.2
  have hW := h.isElemAbelian_xOf hPH hVH
  letI hmodW := moduleOfElemAbelian hW
  obtain ⟨F, hField, hFintype, hCharP, ψ, l, hl1, hl, horth, hcardV, hWK'⟩ :=
    exists_orth_and_card_of_nonabelian (hW := hW) h hPH hVH hH hnM hK hnab hL
  letI := hField
  letI := hFintype
  letI := hCharP
  have hcomm := commutator_kOf_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  have hsq := sq_mem_xOf_of_mem_kOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  have hfratt := frattini_kOf_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl horth hWK'
  have hcenterK := inf_kOf_centralizer_eq_xOf (hW := hW) h hPH hVH hH hnM hK hnab hL ψ hl
    horth hWK'
  have hcenterPK := inf_kOf_inf_centralizer_eq_inf_xOf (hW := hW) h hPH hVH hH hnM hK hnab
    ψ hl horth
  haveI hWnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (xOf_le_kOf h hPH hVH)).mpr
      (fun k hk => Subgroup.centralizer_le_normalizer _
        ((mem_kOf_iff.mp hk).2))
  have hnatSum := isNatSumModule_repSec_kOf h hPH hVH hH hnM hK ψ hl horth
  have hcardW : Nat.card (Tim79a.xOf V H) = 2 ^ (4 * l) :=
    card_W0_eq_pow_of_isOrthModule (hW := hW) ψ hl (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H) horth
  have horth' : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW (hW := hW) ψ hl horth
  refine ⟨hH, hmem, hVH, hK, ⟨F, hField, hFintype, hCharP, l, hl, ψ, ?_⟩⟩
  refine ⟨hl1, hcardV, hcardW, ?_, hcenterK, hcenterPK, hsq, hnatSum,
    Or.inr ⟨hcomm, hfratt⟩⟩
  · intro hW' hmod'
    exact Sec45ShapeWith.isOrthModule_repW_of_one (hW := hW) (inst := hmodW) ψ hl horth' hW'
      hmod'

theorem sec45Shape_of_isL2OrSz
    (h : RootHyp M V) {h₀ : G}
    (hmem : IsHMember M V (Pc M V ⊔ conjSubgroup h₀ (Pc M V)))
    (hVH : V ≤ inSubgroup (pCore 2) (Pc M V ⊔ conjSubgroup h₀ (Pc M V)))
    (hL : IsL2OrSz V (Pc M V ⊔ conjSubgroup h₀ (Pc M V))) :
    Sec45Shape M V (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) h₀ := by
  classical
  set H : Subgroup G := Pc M V ⊔ conjSubgroup h₀ (Pc M V) with hHdef
  have hmemH : IsHMember M V H := by rw [hHdef]; exact hmem
  have hVHH : V ≤ inSubgroup (pCore 2) H := by rw [hHdef]; exact hVH
  have hLH : IsL2OrSz V H := by rw [hHdef]; exact hL
  have hPH : Pc M V ≤ H := le_sup_left
  have hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V) := hHdef
  have hK : KFactorization M V H h₀ :=
    h.kFactorization_of_centralTI centralTIStatement hPH hVHH hH hLH
  by_cases haber : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x
  · simpa [hHdef] using sec45Shape_of_abelian h H hHdef hmemH hVHH hLH hK haber
  · have hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact haber hcon
    simpa [hHdef] using sec45Shape_of_nonabelian h H hHdef hmemH hVHH hLH hK hnab

end RootHyp

theorem sec45Statement_of_sec41
    (h79 : Tim79aStatementWCQ) (h41 : Sec41Statement) : Sec45Statement := by
  intro G _ _ M V h h₀ hmem
  have hVH : V ≤ inSubgroup (pCore 2) (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :=
    h.le_pCore_of_isHMember h79 hmem
  have hL : IsL2OrSz V (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :=
    h41 G M V h h₀ hmem
  exact h.sec45Shape_of_isL2OrSz hmem hVH hL

end CFSG.RankThree.GF2n.Tim81
