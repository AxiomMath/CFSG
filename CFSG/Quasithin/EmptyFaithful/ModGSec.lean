module

public import CFSG.Quasithin.EmptyFaithful.ModGSolv
public import CFSG.Quasithin.EmptyFaithful.S146F2

public section

namespace CFSG.Quasithin.ModG

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native.L239

theorem secExt_of_hom {G : Type} [Group G] {M : Type} [Group M] (A Q : Subgroup G) (D E : Subgroup M)
    (χ : ↥A →* M) (hker : χ.ker = Q.subgroupOf A) (hrange : χ.range = D) (halt : Alt2Struct D E 6) :
    SecExt A Q (IsE2 4) (IsAlt 6) := by
  have hN : (Q.subgroupOf A).Normal := hker ▸ χ.normal_ker
  refine ⟨hN, ?_⟩
  let N := Q.subgroupOf A
  let Φ : (↥A ⧸ N) ≃* ↥D :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange χ).trans (MulEquiv.subgroupCongr hrange))
  have hEn : (E.subgroupOf D).Normal := halt.normal
  set V : Subgroup (↥A ⧸ N) := (E.subgroupOf D).map Φ.symm.toMonoidHom with hVdef
  have hV : V.Normal := Subgroup.Normal.map hEn _ Φ.symm.surjective
  refine ⟨V, hV, ?_, ?_⟩
  ·
    obtain ⟨hcomm, hexp⟩ := halt.elem
    have hfin : Finite ↥E := by
      apply Nat.finite_of_card_ne_zero
      rw [halt.card]
      positivity
    let _ : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hcomm.is_comm.comm }
    obtain ⟨e⟩ := nonempty_mulEquiv_of_exp_two (X := ↥E) (n := 4)
      (fun x => by
        have := hexp (x : M) x.2
        apply Subtype.ext
        simpa [pow_two] using this) halt.card
    let e1 : ↥V ≃* ↥(E.subgroupOf D) :=
      (Subgroup.equivMapOfInjective (E.subgroupOf D) Φ.symm.toMonoidHom Φ.symm.injective).symm
    let e2 : ↥(E.subgroupOf D) ≃* ↥E := Subgroup.subgroupOfEquivOfLe halt.le
    exact ⟨e1.trans (e2.trans e)⟩
  ·
    obtain ⟨α, hα, hαker⟩ := halt.hom
    have hmap : V.map Φ.toMonoidHom = E.subgroupOf D := by
      rw [hVdef, Subgroup.map_map]
      have : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id _ := by
        ext x; simp
      rw [this, Subgroup.map_id]
    let e3 : ((↥A ⧸ N) ⧸ V) ≃* (↥D ⧸ E.subgroupOf D) := QuotientGroup.congr V (E.subgroupOf D) Φ hmap
    let e4 : (↥D ⧸ E.subgroupOf D) ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    exact ⟨e3.trans e4⟩

end CFSG.Quasithin.ModG
