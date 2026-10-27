module

public import CFSG.Quasithin.Background.B69Simple
public import CFSG.Quasithin.Background.A3StructureKGroup
public import CFSG.Quasithin.Background.B69E22Link
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace B69

@[expose] def E22FamC (F : Type) [Group F] : Prop :=
  (∃ p e : ℕ, IsPSL 2 p e F) ∨ (∃ n : ℕ, IsSz n F) ∨ (∃ n : ℕ, IsPSU 3 2 n F) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsPSL 3 2 n F) ∨ (∃ n : ℕ, 1 ≤ n ∧ E2.IsSp4Prime n F) ∨
  (∃ p : ℕ, p ≠ 2 ∧ p % 4 = 1 ∧ IsPSU 3 p 1 F) ∨ (∃ p : ℕ, p ≠ 2 ∧ p % 4 = 3 ∧ IsPSL 3 p 1 F)

namespace E22FamC

variable {F : Type} [Group F]

theorem toFam (h : E22FamC F) : E22Fam F := by
  rcases h with h | h | h | h | h | ⟨p, hp, -, h⟩ | ⟨p, hp, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, h⟩)))))

theorem congr {F' : Type} [Group F'] (e : F ≃* F') (h : E22FamC F) : E22FamC F' := by
  have hm : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ},
      CFSG.Assembly.LowTwoRank.StatedClassicalModel F t n p f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel F' t n p f := by
    intro t n p f hF
    obtain ⟨hadm, hF⟩ := hF
    refine ⟨hadm, ?_⟩
    cases t with
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus =>
      obtain ⟨K, x, hfin, hK, ⟨e'⟩⟩ := hF
      exact ⟨K, x, hfin, hK, ⟨e.symm.trans e'⟩⟩
    | POmegaMinus =>
      obtain ⟨K, x, hfin, hK, b, c, hbc, ⟨e'⟩⟩ := hF
      exact ⟨K, x, hfin, hK, b, c, hbc, ⟨e.symm.trans e'⟩⟩
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hF.elim
  have hsz : ∀ {n : ℕ}, IsSz n F → IsSz n F' := by
    intro n hF
    obtain ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨e'⟩⟩ := hF
    exact ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨e.symm.trans e'⟩⟩
  have halt : ∀ {n : ℕ}, IsAlt n F → IsAlt n F' := fun ⟨e'⟩ => ⟨e.symm.trans e'⟩
  have hsp : ∀ {n : ℕ}, E2.IsSp4Prime n F → E2.IsSp4Prime n F' := by
    intro n hF
    unfold E2.IsSp4Prime at hF ⊢
    split_ifs at hF ⊢
    · exact halt hF
    · exact hm hF
  rcases h with ⟨p, e₁, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, hp4, h⟩ |
    ⟨p, hp, hp4, h⟩
  · exact Or.inl ⟨p, e₁, hm h⟩
  · exact Or.inr (Or.inl ⟨n, hsz h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hm h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hm h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hsp h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp4, hm h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hp4, hm h⟩)))))

end E22FamC

theorem e22CasesNoN_famC {Γ : Type} [Group Γ] {H T M K : Subgroup Γ}
    (h : E2.E22CasesNoN H T M K) : E22FamC ↥(E2.star M H K) := by
  unfold E2.E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨-, t, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, -, h1 | h1, -⟩ | ⟨p, -, -, h1, -⟩
    · exact Or.inl ⟨2, n, h1⟩
    · exact Or.inr (Or.inl ⟨n, h1⟩)
    · exact Or.inl ⟨p, 1, h1⟩
  · rcases h2 with ⟨n, ⟨-, h2 | h2 | h2⟩, -⟩ | ⟨n, hn, h2 | h2, -⟩ | ⟨p, e, -, -, -, -, h2, -⟩ |
        ⟨p, -, hp2, h2 | h2, -⟩
    · exact Or.inl ⟨2, n, h2⟩
    · exact Or.inr (Or.inl ⟨n, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩))))
    · exact Or.inl ⟨p, e, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp2, h2.1, h2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp2, h2.1, h2.2.1⟩)))))

variable {H₀ Y : Type} [Group H₀] [Group Y]

theorem exists_quotient_e22C
    (h22 : E2.E22StatementNoN) [Finite H₀] [Finite Y] {S M : Subgroup Y}
    (hmp : MinParabolic (⊤ : Subgroup Y) S M) (hH₀ : SQTKGroup H₀) (φ : H₀ →* Y)
    (hφ : Function.Surjective φ) {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) :
    ∃ (F : Type) (_ : Group F) (π : ↥L →* F), Function.Surjective π ∧ E22FamC F := by
  classical
  obtain ⟨H, T, M', hmp', hHmap, hTS, hM'M, hkerH⟩ := exists_minParabolic_preimage φ hφ hmp
  have hMH : M' ≤ H := hmp'.maximal.1.le
  have hsq : SQTKGroup ↥H := ⟨sqt_subgroup hH₀.1 H, kGroup_subgroup hH₀.2 H⟩
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hYns : ¬ Group.IsSolvable Y := fun hY => by
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (f := L.subtype)
      L.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hφH : Function.Surjective (φ.comp H.subtype) := by
    intro y
    have : y ∈ H.map φ := by rw [hHmap]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hHns : ¬ Group.IsSolvable ↥H := fun hHs => hYns (Group.isSolvable_of_surjective hφH)
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := h22 H₀ H T M' hmp' hsq hHns
  set J : Subgroup Y := kerIn M ⊤ with hJ
  let f : ↥H →* Y ⧸ J := (QuotientGroup.mk' J).comp (φ.comp H.subtype)
  have hfs : Function.Surjective f := (QuotientGroup.mk'_surjective J).comp hφH
  have hfker : f.ker = (kerIn M' H).subgroupOf H := ker_star_hom φ hMH hHmap hM'M hkerH
  let ψ : E2.StarQuot M' H ≃* Y ⧸ J :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hψ : ∀ x : ↥H, ψ (QuotientGroup.mk x) = f x := fun x => rfl
  let Kh : Subgroup (Y ⧸ J) := (K.subgroupOf H).map f
  have hKh : (E2.star M' H K).map ψ.toMonoidHom = Kh := by
    show ((K.subgroupOf H).map (QuotientGroup.mk' _)).map ψ.toMonoidHom = _
    rw [Subgroup.map_map]
    refine congrArg (fun g => (K.subgroupOf H).map g) ?_
    ext x
    rfl
  have hfam : E22FamC ↥(E2.star M' H K) := e22CasesNoN_famC hcases
  have e1 : ↥(E2.star M' H K) ≃* ↥Kh :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr hKh)
  have hfamK : E22FamC ↥Kh := E22FamC.congr e1 hfam
  have hKs : IsSimpleGroup ↥Kh := hfamK.toFam.isSimpleGroup
  have hKsn : (K.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_chain (subnormal_of_mem_cComp hKc)
  have hKhsn : Kh.IsSubnormal := hKsn.map hfs
  let Th : Subgroup (Y ⧸ J) := (T.subgroupOf H).map f
  have hTH : T ≤ H := hmp'.isSylow.1
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hT2 : IsPGroup 2 ↥Th := by
    have hT2' : IsPGroup 2 ↥(T.subgroupOf H) :=
      hmp'.isSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact hT2'.map _
  have hsupH : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hTH, ← hHK, Subgroup.map_top, Subgroup.range_subtype]
  have hsup : Kh ⊔ Th = ⊤ := by
    show (K.subgroupOf H).map f ⊔ (T.subgroupOf H).map f = ⊤
    rw [← Subgroup.map_sup, hsupH, Subgroup.map_top, MonoidHom.range_eq_top.mpr hfs]
  have hJs : Group.IsSolvable ↥J := hmp.isSolvable_kerIn
  have hLf : ¬ L ≤ (QuotientGroup.mk' J).ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hLb := isComponentOf_map_top (QuotientGroup.mk' J) (QuotientGroup.mk'_surjective J) hL hLf
  obtain ⟨z, hz⟩ := exists_conj_eq_of_component hLb hKhsn hKs hT2 hsup
  have e2 : ↥Kh ≃* ↥(L.map (QuotientGroup.mk' J)) :=
    (Kh.equivMapOfInjective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective).trans
      (MulEquiv.subgroupCongr hz.symm)
  refine ⟨↥(L.map (QuotientGroup.mk' J)), inferInstance,
    (QuotientGroup.mk' J).subgroupMap L, (QuotientGroup.mk' J).subgroupMap_surjective L, ?_⟩
  exact E22FamC.congr e2 hfamK

end B69

end CFSG.Quasithin
