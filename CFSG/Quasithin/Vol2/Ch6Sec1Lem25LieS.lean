module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25LieB
public import CFSG.Quasithin.Vol2.Ch6Sec1Residuals
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfInputs
public import CFSG.Quasithin.Background.E2TwoLieQuotLift
public import CFSG.Quasithin.H13.NQCatLieOverRank1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped commutatorElement

namespace Res625LieS

theorem lie_or_small_of_e22CasesNoN {Γ : Type} [Group Γ] {H T M K : Subgroup Γ}
    (h : E2.E22CasesNoN H T M K) :
    (∃ n : ℕ, 2 ≤ n ∧ E2.IsE22LieType n ↥(E2.star M H K)) ∨
      E2.IsE22SmallType ↥(E2.star M H K) := by
  dsimp only [E2.E22CasesNoN] at h
  rcases h with ⟨-, -, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, htype, -⟩ | ⟨p, hp, hp8, hKs, -⟩
    · exact Or.inl ⟨n, hn, Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩⟩
    · exact Or.inr (Or.inl ⟨p, hp, hp8, hKs⟩)
  · rcases h2 with ⟨n, hBen, -⟩ | ⟨n, hn1, htype, -⟩ | ⟨p, e, hp, hp3, he, hpe, hKs, -⟩ |
        ⟨p, hp, hp2, hKs, -⟩
    · exact Or.inl ⟨n, hBen.1, Or.inl hBen⟩
    · by_cases hn2 : 2 ≤ n
      · refine Or.inl ⟨n, hn2, ?_⟩
        rcases htype with h | h
        · exact Or.inr (Or.inl h)
        · right; right
          rw [E2.IsSp4Prime] at h
          split_ifs at h with h1
          · omega
          · exact h
      · have h1 : n = 1 := by omega
        subst h1
        rcases htype with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hKs⟩))
    · rcases hKs with ⟨-, hU⟩ | ⟨-, hL, -⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl hU⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr hL⟩)))

theorem isE22SmallType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : E2.IsE22SmallType Y) : E2.IsE22SmallType X := by
  rcases h with ⟨p, hp, hp8, h⟩ | ⟨p, f, hp, hp3, hf, hpf, h⟩ | ⟨p, hp, hp2, h | h⟩ | h | h
  · exact Or.inl ⟨p, hp, hp8, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp3, hf, hpf,
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp2,
      Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp2,
      Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · simp only [E2.IsSp4Prime, ↓reduceIte] at h
    obtain ⟨e'⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    simp only [E2.IsSp4Prime, ↓reduceIte]
    exact ⟨e.trans e'⟩

variable {G : Type} [Group G] [Finite G]
variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}

theorem le_M_of_act (hI : In625) (d : Dat625 T M L V n l DL K) (kf1 : OutTwoNilpotentFact)
    (h23 : A23SQTKListFact) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom)
    {H₂ : Subgroup G} (hTH : T ≤ H₂) (hH₂ : H₂ ≤ (K ⊔ K.map (MulAut.conj t₀).toMonoidHom) ⊔ T)
    (hact : ∀ y ∈ H₂ ⊓ (K ⊔ K.map (MulAut.conj t₀).toMonoidHom),
      ∀ hyN : y ∈ Subgroup.normalizer (K : Set G),
        ∃ s ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)),
          phiK K ⟨y, hyN⟩ = MulAut.conj s) : H₂ ≤ M := by
  obtain ⟨-, -, -, hTKT, -⟩ := d.KT_facts hI ht₀ ht₀K
  set KT := K ⊔ K.map (MulAut.conj t₀).toMonoidHom with hKT
  set Y := H₂ ⊓ KT with hY
  have hYM : Y ≤ M := by
    intro y hy
    have ht₀H : t₀⁻¹ ∈ H₂ := H₂.inv_mem (hTH ht₀)
    have hyt : t₀⁻¹ * y * t₀ ∈ Y := by
      refine ⟨H₂.mul_mem (H₂.mul_mem ht₀H hy.1) (hTH ht₀), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hTKT (T.inv_mem ht₀)) y).mp hy.2
      simpa using this
    exact d.mem_M_of_mem_KT hI kf1 h23 ht₀ ht₀K hy.2 (hact y hy) (hact _ hyt)
  intro h hh
  obtain ⟨y, hy, t, ht, rfl⟩ := exists_mul_of_mem_sup_ch625 hTKT (hH₂ hh)
  have hyY : y ∈ Y := by
    refine ⟨?_, hy⟩
    have e : y = (y * t) * t⁻¹ := by group
    rw [e]
    exact H₂.mul_mem hh (H₂.inv_mem (hTH ht))
  exact M.mul_mem (hYM hyY) (d.hyp.T_le ht)

end Res625LieS

open Res625LieS

theorem res625Lie_of (h331 : Stmt3_3_1) (he22 : E2.E22StatementNoN)
    (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) (kf4 : LieOvergroupFact)
    (hP : LiePerfOvergroupFactRank2) (hE : ExcRank2NotSmallFact) : Res625Lie := by
  intro G _ _ T M L V n l DL K hI d hLie t₀ ht₀ ht₀K H₂ hH₂ hH₂Y hs _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hK'N, -, hTKT, -⟩ := d.KT_facts hI ht₀ ht₀K
  have hcase' := d.KT_case hI ht₀ ht₀K
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  set KT := K ⊔ K' with hKT
  have hKTN : KT ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  have hTH : T ≤ H₂ := hH₂.1.1
  have hMP : MinParabolic H₂ T (H₂ ⊓ M) :=
    (d.hyp.toHyp611.toHyp5_0_1.minParabolic_of_isHStar h331 hH₂).1
  have hsq : SQTKGroup ↥H₂ := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH d.hyp.qtke d.hyp.simple d.hyp.nonabelian hH₂.1
    exact ⟨hq, hk⟩
  obtain ⟨⟨K₀, hK₀, hH₂K₀, -, hcases⟩, -⟩ := he22 G H₂ T (H₂ ⊓ M) hMP hsq hs
  have hno := d.hyp.toHyp611.noLie H₂ hH₂
  have hK₀H : K₀ ≤ H₂ := le_of_mem_cComp hK₀
  have hsmall : E2.IsE22SmallType ↥(E2.star (H₂ ⊓ M) H₂ K₀) := by
    rcases lie_or_small_of_e22CasesNoN hcases with ⟨m, hm, htype⟩ | h
    · exact absurd (E2.hasE22LieQuot_of_star hK₀H hm htype) (hno K₀ hK₀)
    · exact h
  have hTs : Group.IsSolvable ↥T := by
    have hTn : Group.IsNilpotent ↥T := hMP.isSylow.2.1.isNilpotent
    infer_instance
  have hperfKT : ∀ A : Subgroup G, A ≤ H₂ → ⁅A, A⁆ = A → A ≤ KT := by
    intro A hA hAp
    have hKTn : (KT.subgroupOf (KT ⊔ T)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
      exact sup_le Subgroup.le_normalizer hTKT
    exact (le_perfectCore_of_perfect (hA.trans hH₂Y) hAp).trans
      (perfectCore_le_of_sup_solvable le_sup_left hKTn rfl hTs)
  have hconjKT : ∀ h ∈ H₂, cjSub h K₀ ≤ KT := fun h hh =>
    hperfKT _ (le_of_mem_cComp (E2.cjSub_mem_cComp hK₀ hh))
      (perfect_of_mem_cComp (E2.cjSub_mem_cComp hK₀ hh))
  set Y := H₂ ⊓ KT with hY
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hKTN
  set Nk := Subgroup.normalizer (K : Set G) with hNk
  set Yn : Subgroup ↥Nk := Y.subgroupOf Nk with hYn
  set Img : Subgroup (MulAut (KBar K)) := Yn.map (phiK K) with hImg
  set X : Subgroup (KBar K) := Img.comap (MulAut.conj : KBar K →* MulAut (KBar K)) with hX
  obtain ⟨hsimp, hnc⟩ := isSimpleGroup_KBar d.quasi
  have hSyl := d.isSylowTwoOf_SBar hI.h432
  have hconj_inj : Function.Injective (MulAut.conj : KBar K →* MulAut (KBar K)) :=
    fun a b hab => d.eq_of_conj_eq hab
  have hSX : SBar T L V K ≤ X := by
    rintro _ ⟨⟨sk, hskK⟩, hsk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsk
    have hskN : sk ∈ Nk := Subgroup.le_normalizer hskK
    have hskY : sk ∈ Y := ⟨hTH hsk.1.1, Subgroup.mem_sup_left hskK⟩
    show MulAut.conj (piK K ⟨sk, hskK⟩) ∈ Img
    rw [← phiK_of_mem K ⟨sk, hskK⟩]
    exact ⟨⟨sk, hskN⟩, Subgroup.mem_subgroupOf.mpr hskY, rfl⟩
  have hinner : ∀ y ∈ Y, ∀ hyN : y ∈ Nk,
      ∃ s : KBar K, s ∈ X ∧ phiK K ⟨y, hyN⟩ = MulAut.conj s := by
    intro y hy hyN
    obtain ⟨k, hk, k', -, hφ, -⟩ := d.decomp_KT hK'N hcase' hy.2 hyN
    refine ⟨piK K ⟨k, hk⟩, ?_, hφ⟩
    show MulAut.conj (piK K ⟨k, hk⟩) ∈ Img
    rw [← hφ]
    exact ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hImg_le : Img ≤ (MulAut.conj : KBar K →* MulAut (KBar K)).range := by
    rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
    obtain ⟨s, -, hs⟩ := hinner y (Subgroup.mem_subgroupOf.mp hy) hyN
    exact ⟨s, hs.symm⟩
  by_cases hXN : X ≤ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K))
  · refine hH₂.2.1 (le_M_of_act hI d kf1 h23 ht₀ ht₀K hTH hH₂Y fun y hy hyN => ?_)
    obtain ⟨s, hsX, hφ⟩ := hinner y hy hyN
    exact ⟨s, hXN hsX, hφ⟩
  have hXns : ¬ Group.IsSolvable ↥X := fun hXs => hXN (kf4 (KBar K) hsimp hLie _ hSyl X hSX hXs)
  obtain ⟨h, hh, x, hx, hxN, hxφ⟩ : ∃ h ∈ H₂, ∃ x ∈ cjSub h K₀, ∃ hxN : x ∈ Nk,
      phiK K ⟨x, hxN⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hXns
    set N := conjClosure K₀ H₂ with hN
    have hNH : N ≤ H₂ := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro x ⟨g, hg, z, hz, rfl⟩
      exact H₂.mul_mem (H₂.mul_mem hg (hK₀H hz)) (H₂.inv_mem hg)
    have hgen : ∀ g ∈ H₂, ∀ z ∈ K₀, g * z * g⁻¹ ∈ cjSub g K₀ := fun g _ z hz =>
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have hNKT : N ≤ KT := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro x ⟨g, hg, z, hz, rfl⟩
      exact hconjKT g hg (hgen g hg z hz)
    have hNY : N ≤ Y := le_inf hNH hNKT
    have hNφ : N ≤ ((phiK K).ker).map Nk.subtype := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro x ⟨g, hg, z, hz, rfl⟩
      have hxN' : g * z * g⁻¹ ∈ Nk := hKTN (hconjKT g hg (hgen g hg z hz))
      exact ⟨⟨_, hxN'⟩, hall g hg _ (hgen g hg z hz) hxN', rfl⟩
    have hNn : (N.subgroupOf H₂).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
      intro g hg
      refine Subgroup.mem_normalizer_fintype fun m hm => ?_
      have hmap : N.map (MulAut.conj g).toMonoidHom ≤ N := by
        rw [hN, conjClosure, MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨x, ⟨g', hg', z, hz, rfl⟩, rfl⟩
        exact ⟨g * g', H₂.mul_mem hg hg', z, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact hmap ⟨m, hm, by simp [MulAut.conj_apply]⟩
    have hH₂N : H₂ = N ⊔ T :=
      le_antisymm (hH₂K₀.le.trans (sup_le_sup_right (le_conjClosure K₀ H₂) T)) (sup_le hNH hTH)
    have hcore : perfectCore Y ≤ N :=
      (perfectCore_mono inf_le_left).trans (perfectCore_le_of_sup_solvable hNH hNn hH₂N hTs)
    have hYcore : (perfectCore Yn).map Nk.subtype = perfectCore Y := by
      rw [map_perfectCore, hYn, Subgroup.map_subgroupOf_eq_of_le hYN]
    have hImgcore : perfectCore Img = ⊥ := by
      rw [hImg, ← map_perfectCore, eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      have hz' : (z : G) ∈ perfectCore Y := hYcore ▸ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := hNφ (hcore hz')
      have : w = z := Subtype.ext hwz
      rw [← this]
      exact hw
    have hImgs : Group.IsSolvable ↥Img := (isSolvable_iff_perfectCore_eq_bot Img).mpr hImgcore
    let ψ : ↥X →* ↥Img :=
      { toFun := fun s => ⟨MulAut.conj (s : KBar K), s.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
    exact Group.isSolvable_of_isSolvable_injective (f := ψ) fun a b hab =>
      Subtype.ext (hconj_inj (congrArg Subtype.val hab))
  set K₁ := cjSub h K₀ with hK₁
  have hK₁c : K₁ ∈ cComp H₂ := E2.cjSub_mem_cComp hK₀ hh
  have hK₁Y : K₁ ≤ Y := le_inf (le_of_mem_cComp hK₁c) (hconjKT h hh)
  have hK₁N : K₁ ≤ Nk := hK₁Y.trans hYN
  set K₁n : Subgroup ↥Nk := K₁.subgroupOf Nk with hK₁n
  set φK₁ : Subgroup (MulAut (KBar K)) := K₁n.map (phiK K) with hφK₁
  set X₁ : Subgroup (KBar K) := φK₁.comap (MulAut.conj : KBar K →* MulAut (KBar K)) with hX₁
  have hK₁nY : K₁n ≤ Yn := fun z hz => hK₁Y hz
  have hφK₁le : φK₁ ≤ Img := Subgroup.map_mono hK₁nY
  have hX₁X : X₁ ≤ X := Subgroup.comap_mono hφK₁le
  have hX₁map : X₁.map (MulAut.conj : KBar K →* MulAut (KBar K)) = φK₁ :=
    Subgroup.map_comap_eq_self (hφK₁le.trans hImg_le)
  have hX₁ne : X₁ ≠ ⊥ := by
    intro h0
    obtain ⟨s, -, hs⟩ := hinner x (hK₁Y hx) hxN
    have hsX : s ∈ X₁ := by
      show MulAut.conj s ∈ φK₁
      rw [← hs]
      exact ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at hsX
    exact hxφ (by rw [hs, hsX, map_one])
  have hX₁sub : IsSubnormal X₁ X := by
    have h1 : IsSubnormal K₁ Y :=
      A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hK₁c) hK₁Y inf_le_left
    have h2 : IsSubnormal K₁n Yn := A3.subnormal_comap Nk.subtype h1
    exact A3.subnormal_comap _ (A3.subnormal_map (phiK K) h2)
  have hK₁perf : ⁅K₁n, K₁n⁆ = K₁n := by
    apply Subgroup.map_injective Nk.subtype_injective
    rw [Subgroup.map_commutator, hK₁n, Subgroup.map_subgroupOf_eq_of_le hK₁N]
    exact perfect_of_mem_cComp hK₁c
  have hX₁perf : ⁅X₁, X₁⁆ = X₁ := by
    apply Subgroup.map_injective hconj_inj
    rw [Subgroup.map_commutator, hX₁map, hφK₁, ← Subgroup.map_commutator, hK₁perf]
  have eX₁ : ↥X₁ ≃* ↥φK₁ :=
    (X₁.equivMapOfInjective _ hconj_inj).trans (MulEquiv.subgroupCongr hX₁map)
  set g₀ : ↥K₁ →* ↥φK₁ := ((phiK K).comp (Subgroup.inclusion hK₁N)).codRestrict φK₁
    (fun k => ⟨Subgroup.inclusion hK₁N k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩) with hg₀
  have hg₀s : Function.Surjective g₀ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    show phiK K (Subgroup.inclusion hK₁N ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩) = phiK K y
    exact congrArg (phiK K) (Subtype.ext rfl)
  set g : ↥K₁ →* ↥X₁ := eX₁.symm.toMonoidHom.comp g₀ with hg
  have hgs : Function.Surjective g := eX₁.symm.surjective.comp hg₀s
  obtain ⟨k, hk, htype⟩ := hLie
  rcases eq_or_ne X ⊤ with hXtop | hXtop
  ·
    have hX₁top : X₁ = ⊤ := by
      rw [hXtop] at hX₁sub
      rcases (A3.subnormal_top_iff.mp hX₁sub).eq_bot_or_top_of_isSimpleGroup hsimp with h0 | h0
      · exact absurd h0 hX₁ne
      · exact h0
    set f₁ : ↥K₁ →* KBar K :=
      ((MulEquiv.subgroupCongr hX₁top).trans Subgroup.topEquiv).toMonoidHom.comp g with hf₁
    have hf₁s : Function.Surjective f₁ :=
      ((MulEquiv.subgroupCongr hX₁top).trans Subgroup.topEquiv).surjective.comp hgs
    have hLie₁ : ∀ m : ℕ, 2 ≤ m → E2.IsE22LieType m (KBar K) → False := fun m hm hm' =>
      hno K₁ hK₁c ⟨KBar K, inferInstance, f₁, hf₁s, m, hm, hm'⟩
    have hexc : (IsG2 2 k (KBar K) ∨ Is3D4 2 k (KBar K) ∨ Is2F4 k (KBar K)) → False := by
      intro hexc
      have eK : ↥K₀ ≃* ↥K₁ :=
        K₀.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective
      have := E2.isSimpleGroup_of_isE22SmallType hsmall
      obtain ⟨e⟩ := E2.nonempty_mulEquiv_of_mem_cComp hK₀ (f₁.comp eK.toMonoidHom)
        (hf₁s.comp eK.surjective) (E2.starRestrict (H₂ ⊓ M) hK₀H)
        (E2.surjective_starRestrict (H₂ ⊓ M) hK₀H)
      exact hE (KBar K) ⟨k, hk, hexc⟩ (isE22SmallType_of_mulEquiv e hsmall)
    rcases htype with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact hLie₁ k hk (Or.inl ⟨hk, Or.inl h1⟩)
    · exact hLie₁ k hk (Or.inr (Or.inl h1))
    · exact hLie₁ k hk (Or.inl ⟨hk, Or.inr (Or.inr h1)⟩)
    · exact hLie₁ k hk (Or.inr (Or.inr h1))
    · exact hexc (Or.inl h1)
    · exact hexc (Or.inr (Or.inl h1))
    · exact hLie₁ k hk (Or.inl ⟨hk, Or.inr (Or.inl h1)⟩)
    · exact hexc (Or.inr (Or.inr h1))
  ·
    have hrank1 : (IsPSL 2 2 k (KBar K) ∨ IsPSU 3 2 k (KBar K) ∨ IsSz k (KBar K)) → False := by
      intro h1
      obtain ⟨n', i, e, hB⟩ := NQCat.exists_benderType_of_rank_one hk h1
      have hPodd : ¬ 2 ∣ (SBar T L V K).index := by
        intro hd
        apply hSyl.2.2
        change 2 ∣ (SBar T L V K).relIndex ⊤
        rwa [Subgroup.relIndex_top_right]
      obtain ⟨-, hmax, -⟩ := NQCat.isRankOneSylow_of_benderType hB _ hSyl.2.1 hPodd
      exact hXN (hmax X hSX hXtop)
    have hrank2 : (IsPSL 3 2 k (KBar K) ∨ IsPSp4 2 k (KBar K) ∨ IsG2 2 k (KBar K) ∨
        Is3D4 2 k (KBar K) ∨ Is2F4 k (KBar K)) → False := by
      intro h2
      obtain ⟨B, _, f, hf, m, hB⟩ := hP (KBar K) hsimp ⟨k, hk, h2⟩ _ hSyl X hSX hXtop X₁ hX₁X
        (E2.isSubnormal_subgroupOf_of_open hX₁sub) hX₁perf hX₁ne
      exact hno K₁ hK₁c ⟨B, inferInstance, f.comp g, hf.comp hgs, m, hB.1, Or.inl hB⟩
    rcases htype with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact hrank1 (Or.inl h1)
    · exact hrank2 (Or.inl h1)
    · exact hrank1 (Or.inr (Or.inl h1))
    · exact hrank2 (Or.inr (Or.inl h1))
    · exact hrank2 (Or.inr (Or.inr (Or.inl h1)))
    · exact hrank2 (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact hrank1 (Or.inr (Or.inr h1))
    · exact hrank2 (Or.inr (Or.inr (Or.inr (Or.inr h1))))

end CFSG.Quasithin.H13
