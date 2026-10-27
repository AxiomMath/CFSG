module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExCrit2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInst

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Excl

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

noncomputable def e9ProdEquivSup {X : Type*} [Group X] {P₁ P₂ : Subgroup X}
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hi : P₁ ⊓ P₂ = ⊥) :
    ↥P₁ × ↥P₂ ≃* ↥(P₁ ⊔ P₂) := by
  have hcomm : ∀ (a : ↥P₁) (b : ↥P₂), Commute (P₁.subtype a) (P₂.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod P₁.subtype P₂.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨P₁.subtype_injective, P₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hi
  have hrange : (MonoidHom.noncommCoprod P₁.subtype P₂.subtype hcomm).range = P₁ ⊔ P₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem e9_not_caseL3 (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) {K₁ : Subgroup G} {s : G}
    (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) : False := by
  classical
  obtain ⟨e⟩ := e
  have hshape' := hshape
  obtain rfl := hshape.1
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have hsG : s ∈ mcOf T := hTG hsT
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  let e1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(imageOTwoQuot (mcOf T) K₁) :=
    e.symm.trans eK
  have hs : IsSimpleGroup ↥(imageOTwoQuot (mcOf T) K₁) :=
    haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      GoldS146P.sl_simple 3 le_rfl
    e1.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(imageOTwoQuot (mcOf T) K₁), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := GoldS146P.sl_nonabelian 3 le_rfl
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by simpa using h))⟩
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) = 168 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact SBc15.L3.card_SL32
  have h3 : 3 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by rw [hcard]; norm_num
  have hF := q_caseI_facts h36 hlist iS S hred hmax hK₁ hsG hsN hKz hs hnc h3 h3
  let e₂ : ↥(imageOTwoQuot (mcOf T) (conjSub s K₁)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := (q_equiv_snd hF).trans e1.symm
  let eL : ↥(imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (e9ProdEquivSup hF.comm hF.disj).symm.trans (MulEquiv.prodCongr e1.symm e₂)
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape'
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T :=
    le_of_mem_cComp (conjSub_mem_cComp_of_mem hK₁ hsG)
  have hsup : imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) =
      imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) := by
    rw [hKz, q_image_sup hK₁G hK₂G]
  rw [hsup] at hloc
  exact hloc.false_of_binCrit eL binCrit_sl3_prod

end Excl

end CFSG.Quasithin
