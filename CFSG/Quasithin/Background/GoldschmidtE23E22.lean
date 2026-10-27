module

public import CFSG.Quasithin.Background.GoldschmidtE23Count
public import CFSG.Quasithin.Background.B69E22Main
public import CFSG.Quasithin.Background.FFC11G
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.B69Simple

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 B69
open scoped commutatorElement

namespace GE23

theorem e22CasesNoN_fam {Γ : Type} [Group Γ] {H T M K : Subgroup Γ}
    (h : E2.E22CasesNoN H T M K) : B69.E22Fam ↥(E2.star M H K) := by
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp2, h2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp2, h2.2.1⟩)))))

variable {H₀ Y : Type} [Group H₀] [Group Y]

theorem exists_quotient_e22_noN
    (h22 : E2.E22StatementNoN) [Finite H₀] [Finite Y] {S M : Subgroup Y}
    (hmp : MinParabolic (⊤ : Subgroup Y) S M) (hH₀ : SQTKGroup H₀) (φ : H₀ →* Y)
    (hφ : Function.Surjective φ) {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) :
    ∃ (F : Type) (_ : Group F) (π : ↥L →* F), Function.Surjective π ∧ B69.E22Fam F := by
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
  have hfam : B69.E22Fam ↥(E2.star M' H K) := e22CasesNoN_fam hcases
  have e1 : ↥(E2.star M' H K) ≃* ↥Kh :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr hKh)
  have hfamK : B69.E22Fam ↥Kh := hfam.congr e1
  have hKs : IsSimpleGroup ↥Kh := hfamK.isSimpleGroup
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
  exact hfamK.congr e2

section Sym

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem SymBlk.k_ne_three (h22 : E2.E22StatementNoN)
    (hmp : MinParabolic X T M)
    (hsq : ∃ (H₀ : Type) (_ : Group H₀) (_ : Finite H₀),
      CFSG.Open.SQTKTauCeti.StronglyQuasithin H₀ ∧ CFSG.SectionRank.IsKGroupCat H₀ ∧
        ∃ f : H₀ →* ↥X, Function.Surjective f)
    {H : Subgroup (MulAut V)} (h : SymBlk X H 3) : False := by
  obtain ⟨L, A, hL, hA, hLA, hblk, rfl, hk, π, hπs, hreal, hLeq, -⟩ := h
  obtain ⟨H₀, g₀, f₀, hS, hK, φ, hφ⟩ := hsq
  obtain ⟨F, _, πF, hπF, hfam⟩ := exists_quotient_e22_noN h22 hmp.subgroupOf ⟨hS, hK⟩ φ hφ
    (isComponentOf_subgroupOf hL)
  have hFs : IsSimpleGroup F := hfam.isSimpleGroup
  obtain ⟨θ, β, hθ, -⟩ := Ch3z.isSymCore_of_realizes' hreal
  have hπi : Function.Injective π := fun a b hab => by
    have := congrArg θ hab
    rwa [← hθ, ← hθ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have hf : Function.Injective ((L ⊔ A).subtype.comp π) := fun a b hab =>
    hπi (Subtype.ext hab)
  let eL : ↥(alternatingGroup (Fin (2 * 3 + 1))) ≃* ↥L :=
    (Subgroup.equivMapOfInjective _ ((L ⊔ A).subtype.comp π) hf).trans
      (MulEquiv.subgroupCongr hLeq.symm)
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  let g : ↥(alternatingGroup (Fin (2 * 3 + 1))) →* F :=
    πF.comp (e0.symm.toMonoidHom.comp eL.toMonoidHom)
  have hgs : Function.Surjective g :=
    hπF.comp (e0.symm.surjective.comp eL.surjective)
  have hs7 : IsSimpleGroup ↥(alternatingGroup (Fin (2 * 3 + 1))) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hgi : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases CFSG.eq_bot_or_eq_top_of_normal g.ker (MonoidHom.normal_ker g) with hbot | htop
    · have : x ∈ g.ker := MonoidHom.mem_ker.2 hx
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hFs.toNontrivial.exists_pair_ne
      obtain ⟨x', rfl⟩ := hgs a
      obtain ⟨y', rfl⟩ := hgs b
      apply hab
      have h1 : x' ∈ g.ker := by rw [htop]; trivial
      have h2 : y' ∈ g.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp h1, MonoidHom.mem_ker.mp h2]
  have hcard : Nat.card F = 2520 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective g ⟨hgi, hgs⟩).toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup]
    simp [Nat.factorial]
  exact B69.E22Fam.card_ne_2520 hfam hcard

theorem SymBlk.k_eq_two (h22 : E2.E22StatementNoN)
    (hmp : MinParabolic X T M)
    (hsq : ∃ (H₀ : Type) (_ : Group H₀) (_ : Finite H₀),
      CFSG.Open.SQTKTauCeti.StronglyQuasithin H₀ ∧ CFSG.SectionRank.IsKGroupCat H₀ ∧
        ∃ f : H₀ →* ↥X, Function.Surjective f)
    (hX : Ch3z.IsRankTwoQuotient ↥X) {H : Subgroup (MulAut V)} {k : ℕ} (h : SymBlk X H k) :
    k = 2 := by
  have h3 := h.le_three hX
  have h2 : 2 ≤ k := by
    obtain ⟨L, A, -, -, -, -, -, hk, -⟩ := h
    exact hk
  by_contra hne
  have : k = 3 := by omega
  subst this
  exact h.k_ne_three h22 hmp hsq

end Sym

end GE23

end CFSG.Quasithin
