module

public import CFSG.Quasithin.Background.RonanE27S6
public import CFSG.Quasithin.Vol2.E2SevenKG7Member

public section

namespace CFSG.Quasithin.RonanE27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Ch3E213M CFSG.Quasithin.Ch3E213M.P6E
  CFSG.QuasithinUnique.Borel252.A6 CFSG.Quasithin.E2 CFSG.Quasithin B6
open CFSG.Quasithin.ASInputs (rootGroupOf)

variable {G : Type} [Group G] [Finite G]

theorem isInIHTVC_of_permSix {X T M V : Subgroup G} {φ : Equiv.Perm (Fin 6) →* G}
    (hφ : Function.Injective φ) (hφX : (⊤ : Subgroup P6).map φ ≤ X)
    (hT : T.comap φ = S06) (hM : M.comap φ = S06) (hV : V.comap φ = Z6)
    (hVr : V ≤ (⊤ : Subgroup P6).map φ) {g : P6}
    (hgen : (⊤ : Subgroup P6).map φ = V ⊔ conjSub (φ g) V)
    (hS : IsSylowTwoOf S06 (⊤ : Subgroup P6))
    (hSp : ∃ n : ℕ, IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot M X))))
    (hn : ∃ m : ℕ, E1.nParam X = ((1 * m : ℕ) : ℕ∞)) :
    ASInputs.IsInIHTVC X T M V ((⊤ : Subgroup P6).map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup P6 := ⊤ with hYdef
  set I := Y.map φ with hIdef
  have hVI : V ≤ I := hVr
  let eYI : ↥Y ≃* ↥I := Y.equivMapOfInjective φ hφ
  have hTI : T ⊓ I = S06.map φ := by
    rw [inf_map_eq_map_comap_inf hφ, hT, hYdef, inf_top_eq]
  have hMI : M ⊓ I = S06.map φ := by
    rw [inf_map_eq_map_comap_inf hφ, hM, hYdef, inf_top_eq]
  have hMI' : M ⊓ I = I ⊓ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
    rw [hMI, hTI, hIdef, map_inf_normalizer_map hφ Y S06, hYdef, top_inf_eq, normalizer_S06]
  have hSI : IsSylowTwoOf (T ⊓ I) I := by
    rw [hTI, CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf]
    exact CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective φ hφ
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hS)
  have hker : kerIn (M ⊓ I) I = ⊥ := by
    rw [hMI, hIdef]
    refine kerIn_map_eq_bot hφ ?_
    refine eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (core_S06 fun b => ?_)
    exact hx b (Subgroup.mem_top b)
  have hVc : ∀ v ∈ V, ∀ t ∈ T ⊓ I, t * v = v * t := by
    intro v hv t ht
    have hv' := hVI hv
    rw [hTI] at ht
    obtain ⟨w, -, rfl⟩ := hv'
    obtain ⟨u, hu, rfl⟩ := ht
    have hw : w ∈ Z6 := hV ▸ hv
    rw [← map_mul, ← map_mul, Z6_comm hw hu]
  have hS2 : IsPGroup 2 ↥((T ⊓ I).subgroupOf I) :=
    hSI.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSI.1).symm
  set e := starQuotEquivOfBot hker with he
  set ε : StarQuot (M ⊓ I) I ≃* ↥Y := e.trans eYI.symm with hε
  have hεmk : ∀ x : ↥I, ε (QuotientGroup.mk' _ x) = eYI.symm x := fun x => by
    rw [hε, MulEquiv.trans_apply, starQuotEquivOfBot_mk]
  refine ⟨hφX, ⟨φ g, ⟨g, Subgroup.mem_top g, rfl⟩, hgen⟩, hSI, ?_, 1, hn,
    Or.inr (Or.inr ⟨hSp, le_rfl, Or.inr ⟨rfl, ⟨ε.trans Subgroup.topEquiv⟩⟩, ?_, ?_, ?_⟩)⟩
  ·
    rw [hker]
    have hb : pCoreOf 2 (⊥ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)
    rw [hb]
    refine ⟨le_rfl, IsPGroup.of_bot, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  ·
    refine isBorelIn_of_map_equiv e ?_
    rw [map_star_starQuotEquivOfBot hker (M ⊓ I), hMI', Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq inf_le_right]
    refine ⟨(T ⊓ I).subgroupOf I, ⟨le_top, hS2, ?_⟩, by rw [top_inf_eq]⟩
    change ¬ 2 ∣ ((T ⊓ I).subgroupOf I).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hSI.2.2
  ·
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hVc v (Subgroup.mem_subgroupOf.mp hv) t
      (Subgroup.mem_subgroupOf.mp ht)))
  ·
    intro P hP hBP hVP
    set P₂ := (P.map ε.toMonoidHom).map Y.subtype with hP₂
    have hP₂max : IsMaxParabolic2 Y P₂ := by
      refine isMaxParabolic2_map_subtype le_rfl ?_
      rw [Subgroup.subgroupOf_self]
      exact isMaxParabolic2_map_equiv ε hP
    have hB₂ : S06 ≤ P₂ := by
      intro y hy
      have hφy : φ y ∈ M ⊓ I := hMI ▸ ⟨y, hy, rfl⟩
      have h1 : QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨φ y, hφy.2⟩ : ↥I) ∈ P :=
        hBP ⟨⟨φ y, hφy.2⟩, Subgroup.mem_subgroupOf.mpr hφy, rfl⟩
      refine ⟨⟨y, Subgroup.mem_top y⟩, ⟨_, h1, ?_⟩, rfl⟩
      change ε (QuotientGroup.mk' _ ⟨φ y, hφy.2⟩) = ⟨y, Subgroup.mem_top y⟩
      rw [hεmk]
      apply eYI.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hW₂ : V.comap φ ≤ rootGroupOf P₂ := by
      intro w hw
      have hφw : φ w ∈ V := hw
      have h1 : QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨φ w, hVI hφw⟩ : ↥I) ∈
          rootGroupOf P := hVP ⟨⟨φ w, hVI hφw⟩, Subgroup.mem_subgroupOf.mpr hφw, rfl⟩
      have h2 : ε (QuotientGroup.mk' _ ⟨φ w, hVI hφw⟩) ∈ rootGroupOf (P.map ε.toMonoidHom) := by
        rw [← map_rootGroupOf_equiv]
        exact ⟨_, h1, rfl⟩
      rw [hεmk] at h2
      have h3 : eYI.symm ⟨φ w, hVI hφw⟩ = ⟨w, Subgroup.mem_top w⟩ := by
        apply eYI.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [h3] at h2
      exact map_rootGroupOf_subtype_le _ ⟨_, h2, rfl⟩
    exact not_Z6_le_rootGroupOf hS hP₂max hB₂ (hV ▸ hW₂)

end CFSG.Quasithin.RonanE27
