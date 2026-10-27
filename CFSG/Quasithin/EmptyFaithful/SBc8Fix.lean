module

public import CFSG.Quasithin.EmptyFaithful.SBc8V2
public import CFSG.Quasithin.EmptyFaithful.SBc8Fin
public import CFSG.Quasithin.EmptyFaithful.SBc8Plane
public import CFSG.Quasithin.EmptyFaithful.SBc7LDP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc8

section Data

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem blockU_eq_c134Q (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : blockU L = c134Q I L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hle : blockU L ≤ c134Q I L :=
    Subgroup.commutator_mono_left (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L))
  exact le_antisymm hle (SBc4.c134Q_le_blockU c)

theorem case12_data' (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hout : Outcome31 T V₁ I L)
    (h12 : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
      (β : ↥(centerOf (c134Q I L)) →* Multiplicative (Fin k → Fin 3 → F)),
      0 < k ∧ Fintype.card F = 2 ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
        Function.Surjective β ∧ Function.Injective β ∧
        L ≤ Subgroup.normalizer (centerOf (c134Q I L) : Set G) ∧
        ∀ (a : ↥L) (u v : ↥(centerOf (c134Q I L))), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
          Multiplicative.toAdd (β v) i =
            ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
              (Multiplicative.toAdd (β u) i) := by
  obtain ⟨k, F, hF, hFin, α, β, hk, hF2, hαs, hαk, hβs, hβk, hLQ, hβe⟩ :=
    SBc7.case12_data c hout h12
  have hcomm := SBc4.blockU_comm_of_case12 c h12
  rw [blockU_eq_c134Q c] at hcomm
  have hcen : centerOf (c134Q I L) = c134Q I L :=
    le_antisymm inf_le_left (le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr
      fun y hy => hcomm y hy x hx)
  have hle : centerOf (c134Q I L) ≤ c134Q I L := inf_le_left
  have hβi : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hβk
  refine ⟨k, F, hF, hFin, α, β.comp (Subgroup.inclusion hle), hk, hF2, hαs, hαk, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    have hmem : (u : G) ∈ centerOf (c134Q I L) := by
      rw [hcen]
      exact u.2
    exact ⟨⟨u, hmem⟩, hu⟩
  · exact hβi.comp (Subgroup.inclusion_injective hle)
  · rw [hcen]
    exact hLQ
  · intro a u v h i
    exact hβe a (Subgroup.inclusion hle u) (Subgroup.inclusion hle v) h i

theorem case123_data (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hout : Outcome31 T V₁ I L)
    (hcase : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L ∨
      IsC134Case 3 I (Sgp153 T V₁) L) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
      (β : ↥(centerOf (c134Q I L)) →* Multiplicative (Fin k → Fin 3 → F)),
      0 < k ∧ Fintype.card F = 2 ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
        Function.Surjective β ∧ Function.Injective β ∧
        L ≤ Subgroup.normalizer (centerOf (c134Q I L) : Set G) ∧
        ∀ (a : ↥L) (u v : ↥(centerOf (c134Q I L))), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
          Multiplicative.toAdd (β v) i =
            ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
              (Multiplicative.toAdd (β u) i) := by
  rcases hcase with h1 | h2 | h3
  · exact case12_data' c hout (Or.inl h1)
  · exact case12_data' c hout (Or.inr h2)
  · change IsC134Case3 I (Sgp153 T V₁) L at h3
    obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum1, -⟩, -⟩ := h3
    have hF2 : Fintype.card F = 2 := SBc7.card_field_eq_two c hout hcard hmod
    obtain ⟨hLW, -, β, hβs, hβk, hβe⟩ := hsum1
    have hβk' : β.ker = ⊥ := by rw [hβk, Subgroup.bot_subgroupOf]
    refine ⟨1, F, hF, hFin, α, β, Nat.one_pos, hF2, hmod.1, hmod.2, hβs,
      (MonoidHom.ker_eq_bot_iff β).1 hβk', hLW, fun a u v h i => ?_⟩
    simpa [moduleAct] using hβe a u v h i

omit [Finite G] in
theorem exists_hom_SL3 {F : Type} [Field F] (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ∃ α' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F, Function.Surjective α' ∧
      (∀ l : ↥L, ((α' l : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
      (∀ l : ↥L, α' l = 1 ↔ (l : G) ∈ pCoreOf 2 L) := by
  let α' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α
  refine ⟨α', fun g => ?_, fun l => ?_, fun l => ?_⟩
  · obtain ⟨l, hl⟩ := hαs (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F g)
    exact ⟨l, by simp [α', hl]⟩
  · have h : α l = CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F (α' l) := by
      simp [α']
    show _ = ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [h]
    rfl
  · constructor
    · intro h
      have h1 : α l = 1 := by
        have := congrArg (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F) h
        simpa [α'] using this
      have h2 : l ∈ α.ker := h1
      rw [hαk] at h2
      exact (AppC.mem_pCore_iff_mem_blockQ l).1 h2
    · intro h
      have h2 : l ∈ CFSG.pCore 2 ↥L := (AppC.mem_pCore_iff_mem_blockQ l).2 h
      rw [← hαk] at h2
      have h1 : α l = 1 := h2
      simp [α', h1]

end Data

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem centerOf_inf_centralizer_eq_bot (h113 : StageLemma14113)
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hout : Outcome31 T V₁ I L)
    (hcase : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L ∨
      IsC134Case 3 I (Sgp153 T V₁) L) :
    centerOf (c134Q I L) ⊓ Subgroup.centralizer (Yp : Set G) = ⊥ := by
  obtain ⟨k, F, hFfield, hFin, α, β, hk, hF2, hαs, hαk, hβs, hβi, hLW, hβe⟩ :=
    case123_data c hout hcase
  obtain ⟨hV₂UI, hV₂Q, hMN, hV₂card, hV₂fix⟩ := V₂_facts h113 c.toCtx15330
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M ⊓ I := le_inf (inf_le_right.trans c.c29.norm_le) hsyl.1
  have hYM : Yp ≤ M ⊓ I := by
    rw [hF.yp_eq]
    exact SBc5.oPrimeResidualOf_le 3 _
  have hQeq : blockU L = c134Q I L := blockU_eq_c134Q c
  have hQP : c134Q I L ≤ pCoreOf 2 I := by
    rw [← hQeq]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L)).trans
      (SBc6.pCoreOf_le_of_ctx c.toCtx15330).1
  obtain ⟨hUOC, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (SBc5.omegaOneCenter_le_Sgp hh)
  have hV₂Q' : V₂ ≤ c134Q I L := hQeq ▸ hV₂Q
  have hV₂W : V₂ ≤ centerOf (c134Q I L) := fun v hv => ⟨hV₂Q' hv,
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp (hUOC (hV₂UI hv)).2 q (hQP hq)⟩
  obtain ⟨α', hα's, hα'mat, hα'k⟩ := exists_hom_SL3 (L := L) α hαs hαk
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  let Ybar : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := (Yp.subgroupOf L).map α'
  let Tbar : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((Sgp153 T V₁ ⊓ L).subgroupOf L).map α'
  have hTbar : IsSylowTwoOf Tbar ⊤ :=
    SBc5.isSylowTwoOf_map_surjective α' hα's (SBc5.isSylowTwoOf_subgroupOf_top hQsyl)
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := SBc7.Sgp_le_normalizer_Yp c.toCtx15330
  have hN : ∀ τ ∈ Tbar, ∀ y ∈ Ybar, τ * y * τ⁻¹ ∈ Ybar := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨s * y * s⁻¹, ?_, by simp⟩
    show (s : G) * (y : G) * (s : G)⁻¹ ∈ Yp
    exact (Subgroup.mem_normalizer_iff.mp (hSN hs.1) (y : G)).mp hy
  let 𝒱 : AddSubgroup (Fin k → Fin 3 → F) :=
    { carrier := {x | ∃ v : G, ∃ hv : v ∈ V₂, Multiplicative.toAdd (β ⟨v, hV₂W hv⟩) = x}
      zero_mem' := ⟨1, V₂.one_mem, by
        rw [show (⟨1, hV₂W V₂.one_mem⟩ : ↥(centerOf (c134Q I L))) = 1 from rfl, map_one]
        rfl⟩
      add_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
        refine ⟨v * v', V₂.mul_mem hv hv', ?_⟩
        rw [show (⟨v * v', hV₂W (V₂.mul_mem hv hv')⟩ : ↥(centerOf (c134Q I L))) =
          ⟨v, hV₂W hv⟩ * ⟨v', hV₂W hv'⟩ from rfl, map_mul, toAdd_mul]
      neg_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v⁻¹, V₂.inv_mem hv, ?_⟩
        rw [show (⟨v⁻¹, hV₂W (V₂.inv_mem hv)⟩ : ↥(centerOf (c134Q I L))) =
          (⟨v, hV₂W hv⟩ : ↥(centerOf (c134Q I L)))⁻¹ from rfl, map_inv, toAdd_inv] }
  have h𝒱card : Nat.card 𝒱 = 4 := by
    have h1 : Nat.card ↥V₂ = Nat.card 𝒱 := by
      refine Nat.card_congr (Equiv.ofBijective (fun v : ↥V₂ =>
        (⟨Multiplicative.toAdd (β ⟨v, hV₂W v.2⟩), v, v.2, rfl⟩ : ↥𝒱)) ⟨?_, ?_⟩)
      · intro v v' h
        have h1 : β ⟨v, hV₂W v.2⟩ = β ⟨v', hV₂W v'.2⟩ := by
          have := congrArg (fun z : ↥𝒱 => Multiplicative.ofAdd (z : Fin k → Fin 3 → F)) h
          simpa using this
        have h2 := hβi h1
        have h3 : (v : G) = (v' : G) :=
          congrArg (fun z : ↥(centerOf (c134Q I L)) => (z : G)) h2
        exact Subtype.ext h3
      · rintro ⟨x, v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [← h1]
    exact hV₂card
  have hconj : ∀ (l : ↥L) (v : G) (hv : v ∈ V₂) (hlv : (l : G) * v * (l : G)⁻¹ ∈ V₂) (i : Fin k),
      ((α' l : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Multiplicative.toAdd (β ⟨v, hV₂W hv⟩) i) =
      Multiplicative.toAdd (β ⟨(l : G) * v * (l : G)⁻¹, hV₂W hlv⟩) i := by
    intro l v hv hlv i
    rw [hα'mat l]
    exact (hβe l ⟨v, hV₂W hv⟩ ⟨(l : G) * v * (l : G)⁻¹, hV₂W hlv⟩ rfl i).symm
  let 𝒢 : Set (Matrix (Fin 3) (Fin 3) F) :=
    {A | ∃ y : ↥L, (y : G) ∈ Yp ∧ A = ((α' y : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)}
  have hdet : ∀ A ∈ 𝒢, IsUnit A := by
    rintro _ ⟨y, -, rfl⟩
    exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [(α' y).det_coe]; exact isUnit_one)
  have hYV : ∀ y ∈ Yp, ∀ v ∈ V₂, y * v * y⁻¹ ∈ V₂ := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hMN (hYM hy)) v).mp hv
  have hinv : ∀ A ∈ 𝒢, ∀ x ∈ 𝒱, (fun i => A.mulVec (x i)) ∈ 𝒱 := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨(y : G) * v * (y : G)⁻¹, hYV y hy v hv, ?_⟩
    funext i
    exact (hconj y v hv (hYV y hy v hv) i).symm
  have hfix : ∀ x ∈ 𝒱, (∀ A ∈ 𝒢, (fun i => A.mulVec (x i)) = x) → x = 0 := by
    rintro _ ⟨v, hv, rfl⟩ hA
    by_contra hne
    have hv1 : v ≠ 1 := by
      rintro rfl
      apply hne
      rw [show (⟨1, hV₂W V₂.one_mem⟩ : ↥(centerOf (c134Q I L))) = 1 from rfl, map_one]
      rfl
    obtain ⟨y, hy, hyne⟩ := hV₂fix v hv hv1
    have hyL : y ∈ L := hYL hy
    apply hyne
    have h1 := hA _ ⟨⟨y, hyL⟩, hy, rfl⟩
    have h2 : β ⟨y * v * y⁻¹, hV₂W (hYV y hy v hv)⟩ = β ⟨v, hV₂W hv⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      have := congrFun h1 i
      rw [hconj ⟨y, hyL⟩ v hv (hYV y hy v hv) i] at this
      exact this
    have h3 := hβi h2
    exact congrArg Subtype.val h3
  obtain ⟨i, E, hE, hEcard, hCE⟩ := exists_plane_coordinate hF2 𝒱 h𝒱card 𝒢 hdet hinv hfix
  have hET : ∀ τ ∈ Tbar, ∀ e ∈ E, (τ : Matrix (Fin 3) (Fin 3) F).mulVec e ∈ E := by
    rintro _ ⟨s, hs, rfl⟩ e he
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := (hE e).1 he
    have hsS : (s : G) ∈ Sgp153 T V₁ := hs.1
    have hsv : (s : G) * v * (s : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hMN (hSM hsS)) v).mp hv
    rw [hconj s v hv hsv i]
    exact (hE _).2 ⟨_, ⟨(s : G) * v * (s : G)⁻¹, hsv, rfl⟩, rfl⟩
  have hCE' : ∀ e ∈ E, (∀ y ∈ Ybar, (y : Matrix (Fin 3) (Fin 3) F).mulVec e = e) → e = 0 := by
    intro e he hfixe
    refine hCE e he fun A hA => ?_
    obtain ⟨y, hy, rfl⟩ := hA
    exact hfixe (α' y) ⟨y, hy, rfl⟩
  have hnofix := eq_zero_of_fixed_of_plane hF2 hTbar hN E hEcard hET hCE'
  rw [eq_bot_iff]
  rintro w ⟨hwW, hwC⟩
  rw [Subgroup.mem_bot]
  have hβw : β ⟨w, hwW⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    apply hnofix
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hyw : (w : G) = (y' : G) * w * (y' : G)⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hwC (y' : G) hy'
      calc (w : G) = (w * (y' : G)) * (y' : G)⁻¹ := by group
        _ = ((y' : G) * w) * (y' : G)⁻¹ := by rw [this]
        _ = (y' : G) * w * (y' : G)⁻¹ := by group
    rw [hα'mat y']
    have := hβe y' ⟨w, hwW⟩ ⟨w, hwW⟩ hyw j
    exact this.symm
  have : (⟨w, hwW⟩ : ↥(centerOf (c134Q I L))) = 1 := hβi (by rw [hβw, map_one])
  exact congrArg Subtype.val this

end Main


end SBc8

end CFSG.Quasithin
