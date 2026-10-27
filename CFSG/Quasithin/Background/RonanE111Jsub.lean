module

public import CFSG.Quasithin.EmptyFaithful.E111RMain
public import CFSG.Quasithin.Background.RonanE111Quot

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

theorem inEFor_of_hom {Q M : Type} [Group Q] [Finite Q] [Group M] [Finite M] {n : ℕ} (hn : 1 ≤ n)
    (Φ : Q →* M) {S' : Subgroup Q} (hS' : IsSylowIn 2 S' ⊤) (hker : IsPGroup 2 Φ.ker)
    (hΦ : E1.nParam Φ.range ≤ (n : ℕ∞)) : E1.InEFor n ⊤ S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_le : Φ.ker ≤ S' := hS'.le_of_normal le_top (Subgroup.normal_subgroupOf) hker
  have hTM : ∀ Ω : Set (Subgroup Q), E1.IsInvColl ⊤ Ω → Φ.ker ≤ E1.eGen n ⊤ S' Ω ⊔
      (⊤ ⊓ Subgroup.normalizer (E1.weakClosure S' Ω : Set Q)) := fun Ω hΩ x hx =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ (hker_le hx)⟩
  have hEq : E1.nParam (⊤ : Subgroup (Q ⧸ Φ.ker)) = E1.nParam Φ.range := by
    rw [E1.nParam_subgroupOf Φ.range]
    exact E1.Eleven.nParam_top_mulEquiv (QuotientGroup.quotientKerEquivRange Φ)
  have hIH : E1.InE n (⊤ : Subgroup (Q ⧸ Φ.ker)) := by
    have : E1.nParam (⊤ : Subgroup (Q ⧸ Φ.ker)) ≤ n := hEq ▸ hΦ
    exact (E1.nParam_le_iff (by omega)).mp this
  exact E1.inEFor_of_quotient hIH hS' hTM

section CompSup

variable {G : Type} [Group G]

@[expose] noncomputable def conjOn {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal) :
    ↥H →* MulAut ↥J :=
  ((MulAut.congr (Subgroup.subgroupOfEquivOfLe hJH)).toMonoidHom).comp
    (MulAut.conjNormal (H := J.subgroupOf H))

theorem conjOn_apply {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    (q : ↥H) (m : ↥J) : ((conjOn hJH hJn q m : ↥J) : G) = (q : G) * (m : G) * (q : G)⁻¹ := by
  simp [conjOn, MulAut.conjNormal_apply, Subgroup.subgroupOfEquivOfLe]

@[expose] noncomputable def botQuotEquiv (J : Subgroup G) :
    ↥J ≃* (↥J ⧸ (⊥ : Subgroup G).subgroupOf J) :=
  MulEquiv.ofBijective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf J))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', Subgroup.bot_subgroupOf]),
      QuotientGroup.mk'_surjective _⟩

theorem botQuotEquiv_apply (J : Subgroup G) (m : ↥J) :
    botQuotEquiv J m = QuotientGroup.mk m := rfl

@[expose] noncomputable def phiOn {H J : Subgroup G} (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) : ↥H →* MulAut (↥J ⧸ (⊥ : Subgroup G).subgroupOf J) :=
  (MulAut.congr (botQuotEquiv J)).toMonoidHom.comp (conjOn hJH hJn)

theorem phiOn_apply_mk {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    (q : ↥H) (m : ↥J) :
    phiOn hJH hJn q (QuotientGroup.mk m) = QuotientGroup.mk (conjOn hJH hJn q m) := by
  have h : (botQuotEquiv J).symm (QuotientGroup.mk m) = m := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp [phiOn, MulAut.congr_apply, botQuotEquiv_apply, h]

theorem induces_phiOn {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal) (q : ↥H) :
    Induces J ⊥ (q : G) (phiOn hJH hJn q) := fun m =>
  ⟨conjOn hJH hJn q m, conjOn_apply hJH hJn q m, phiOn_apply_mk hJH hJn q m⟩

theorem eq_phiOn_of_induces {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    {g : G} (hg : g ∈ H) {α : MulAut (↥J ⧸ (⊥ : Subgroup G).subgroupOf J)}
    (hα : Induces J ⊥ g α) : α = phiOn hJH hJn ⟨g, hg⟩ := by
  ext x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m', hm'1, hm'2⟩ := hα m
  rw [hm'2, phiOn_apply_mk]
  congr 1
  apply Subtype.ext
  rw [hm'1, conjOn_apply]

theorem phiOn_eq_one_iff {H J : Subgroup G} (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    (q : ↥H) : phiOn hJH hJn q = 1 ↔ (q : G) ∈ Subgroup.centralizer (J : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := phiOn_apply_mk hJH hJn q ⟨x, hx⟩
    rw [h, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h2
    have h3 : (x : G)⁻¹ * ((q : G) * x * (q : G)⁻¹) = 1 := by
      simpa [conjOn_apply] using h2
    have h4 : (x : G) = (q : G) * x * (q : G)⁻¹ := inv_mul_eq_one.mp h3
    calc (x : G) * q = ((q : G) * x * (q : G)⁻¹) * q := by rw [← h4]
      _ = q * x := by group
  · intro h
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rw [phiOn_apply_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [conjOn_apply]
    have := Subgroup.mem_centralizer_iff.mp h (m : G) m.2
    calc (q : G) * m * (q : G)⁻¹ = (m * q) * (q : G)⁻¹ := by rw [← this]
      _ = m := by group


theorem center_trivial_of_isComp {X J : Subgroup G} (hJ : IsComp X J) :
    ∀ x ∈ J, x ∈ Subgroup.centralizer (J : Set G) → x = 1 := by
  intro x hx hxc
  have := hJ.simple
  have hZ := Vol2.Ch11.SecE3.center_eq_bot_of_simple hJ.nonabelian
  have hc : (⟨x, hx⟩ : ↥J) ∈ Subgroup.center ↥J :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem isSylowIn_compSup [Finite G] {X T J : Subgroup G} (hR : E111Reduced G X T)
    (hJ : IsComp X J) :
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (J : Set G))
      (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hSN : T ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  refine ⟨le_sup_right, (hT.2.1 : IsPGroup 2 T).to_le inf_le_left, ?_⟩
  have h1 : ¬ 2 ∣ (T ⊓ J).relIndex J := (E111R.isSylowIn_inf hR hJ).2.2
  have h2 := B6.relIndex_inf_eq_relIndex_sup hSN
  have h3 : (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ J = T ⊓ J := by
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)) inf_le_right
  rw [h3] at h2
  rw [sup_comm]
  rw [← h2]
  exact h1

theorem inEFor_compSup [Finite G] {X T J : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hR : E111Reduced G X T) (hH : HypT n G T) (hJ : IsComp X J) :
    E1.InEFor n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
      (T ⊓ Subgroup.normalizer (J : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hS
  set H : Subgroup G := J ⊔ S with hHdef
  have hJH : J ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hHN : H ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSN
  have hJn : (J.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJH]
    exact hHN
  have hSsyl : IsSylowIn 2 S H := isSylowIn_compSup hR hJ
  have hS'syl : IsSylowIn 2 (S.subgroupOf H) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hSH,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hSsyl
  have hnormbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hHeq : J ⊔ (T ⊓ Subgroup.normalizer (J : Set G) ⊓
      Subgroup.normalizer ((⊥ : Subgroup G) : Set G)) = H := by
    rw [hnormbot, inf_top_eq]
  have hJsub : J.IsSubnormal :=
    Subgroup.IsSubnormal.trans hJ.le hJ.2.1.isSubnormal hR.1.isSubnormal
  haveI : Finite (MulAut (↥J ⧸ (⊥ : Subgroup G).subgroupOf J)) := quotFiniteMulAut _
  have hsimple : IsSimpleGroup (↥J ⧸ (⊥ : Subgroup G).subgroupOf J) :=
    (MulEquiv.isSimpleGroup_congr (botQuotEquiv J)).mp hJ.simple
  have hnab : ∃ a b : ↥J ⧸ (⊥ : Subgroup G).subgroupOf J, a * b ≠ b * a :=
    quotNonabelian (botQuotEquiv J).symm hJ.nonabelian
  have hTbot : T ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [hnormbot]
    exact le_top
  have hnP : E1.nParam (innAutInduced T J ⊥) ≤ (n : ℕ∞) :=
    hH J ⊥ bot_le hJsub hTbot hsimple hnab
  have hrange : innAutInduced T J ⊥ = (phiOn hJH hJn).range := by
    rw [innAutInduced_eq, hHeq]
    have : indSet J ⊥ H = ((phiOn hJH hJn).range : Set _) := by
      ext α
      constructor
      · rintro ⟨g, hg, hind⟩
        exact ⟨⟨g, hg⟩, (eq_phiOn_of_induces hJH hJn hg hind).symm⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q : G), q.2, induces_phiOn hJH hJn q⟩
    rw [this]
    exact Subgroup.closure_eq _
  have hker : (phiOn hJH hJn).ker = (Subgroup.centralizer (J : Set G)).subgroupOf H := by
    ext q
    rw [MonoidHom.mem_ker, phiOn_eq_one_iff, Subgroup.mem_subgroupOf]
  have hJS : J.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨j, hj, s, hs, hq⟩ := E111R.exists_mul_of_mem_sup hSN (show (q : G) ∈ J ⊔ S from q.2)
    have e : q = (⟨j, hJH hj⟩ : ↥H) * ⟨s, hSH hs⟩ := Subtype.ext hq
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hj) (Subgroup.mem_subgroupOf.mpr hs)
  have hker2 : IsPGroup 2 (phiOn hJH hJn).ker := by
    intro r
    have hr : (r : ↥H) ∈ J.subgroupOf H ⊔ S.subgroupOf H := hJS ▸ Subgroup.mem_top _
    obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal (N := J.subgroupOf H) (T := S.subgroupOf H)
      hS'syl.2.1 (r : ↥H) hr
    refine ⟨e, ?_⟩
    have h1 : ((r : ↥H) : G) ^ 2 ^ e ∈ J := by
      have := Subgroup.mem_subgroupOf.mp he
      simpa using this
    have h2 : ((r : ↥H) : G) ^ 2 ^ e ∈ Subgroup.centralizer (J : Set G) := by
      have hr' : (r : ↥H) ∈ (Subgroup.centralizer (J : Set G)).subgroupOf H :=
        (SetLike.ext_iff.mp hker (r : ↥H)).mp r.2
      exact (Subgroup.centralizer (J : Set G)).pow_mem (Subgroup.mem_subgroupOf.mp hr') _
    have h3 : ((r : ↥H) : G) ^ 2 ^ e = 1 := center_trivial_of_isComp hJ _ h1 h2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3
  have key : E1.InEFor n ⊤ (S.subgroupOf H) :=
    inEFor_of_hom hn (phiOn hJH hJn) hS'syl hker2 (hrange ▸ hnP)
  have := (E1.inEFor_map_subtype_iff n H (S.subgroupOf H)).mpr key
  rwa [Subgroup.map_subgroupOf_eq_of_le hSH] at this


theorem inEFor_of_simple [Finite G] {X T : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hR : E111Reduced G X T) (hH : HypT n G T) (hXs : IsSimpleGroup ↥X) : E1.InEFor n ⊤ T := by
  have hX : IsComp X X := ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance, hXs,
    hR.2.2.2.1⟩
  have := inEFor_compSup hn hR hH hX
  have hN : Subgroup.normalizer (X : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hR.1
  rwa [hN, inf_top_eq, hR.2.2.2.2.2.2] at this

end CompSup

end CFSG.Quasithin.RonanE111
