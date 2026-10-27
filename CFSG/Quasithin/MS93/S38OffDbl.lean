module

public import CFSG.Quasithin.MS93.S38OffDblAlg
public import CFSG.Quasithin.MS93.ML3Bridge
public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Grp
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.H13.Ch4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

namespace S38D

variable {G : Type} [Group G]

section Coord

variable {K : Type} [Field K]

@[expose] def IsDblCoord (L U : Subgroup G) (α : ↥L →* ↥(StatedSL 3 K))
    (β : ↥U ≃* Multiplicative (Fin 2 → Fin 3 → K)) : Prop :=
  ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
    Multiplicative.toAdd (β v) i =
      ((α a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (β u) i

theorem exists_isDblCoord {L U : Subgroup G} {α : ↥L →* ↥(StatedSL 3 K)}
    (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 2) :
    ∃ β : ↥U ≃* Multiplicative (Fin 2 → Fin 3 → K), IsDblCoord L U α β := by
  obtain ⟨-, -, β, hβ, hker, heq⟩ := hnat
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  refine ⟨MulEquiv.ofBijective β ⟨hinj, hβ⟩, fun a u v huv i => ?_⟩
  have := heq a u v huv i
  simp only [moduleAct, Bool.false_eq_true, ↓reduceIte] at this
  exact this

variable {U : Subgroup G} (β : ↥U ≃* Multiplicative (Fin 2 → Fin 3 → K))

open Classical in
@[expose] noncomputable def cG (g : G) : Equiv.Perm (Fin 2 → Fin 3 → K) :=
  if hg : g ∈ Subgroup.normalizer (U : Set G) then cHom β ⟨g, hg⟩ else 1

theorem cG_of_mem {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    cG β g = cHom β ⟨g, hg⟩ :=
  dite_eq_left hg

theorem cG_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hg' : g' ∈ Subgroup.normalizer (U : Set G)) : cG β (g * g') = cG β g * cG β g' := by
  rw [cG_of_mem β (mul_mem hg hg'), cG_of_mem β hg, cG_of_mem β hg', ← map_mul]
  rfl

theorem cG_one : cG β (1 : G) = 1 := by
  rw [cG_of_mem β (one_mem _), ← map_one (cHom β)]
  rfl

theorem cG_inv {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    cG β g⁻¹ = (cG β g)⁻¹ := by
  rw [cG_of_mem β (inv_mem hg), cG_of_mem β hg, ← map_inv]
  rfl

theorem cG_crd {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    cG β g (crd β u) =
      crd β ⟨g * (u : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg _).mp u.2⟩ := by
  rw [cG_of_mem β hg, cHom_apply, cAct_crd]

theorem cG_mem_addPerms (g : G) : cG β g ∈ addPerms K := by
  by_cases hg : g ∈ Subgroup.normalizer (U : Set G)
  · rw [cG_of_mem β hg]
    exact cHom_mem_addPerms β _
  · rw [cG, dite_eq_right hg]
    exact (addPerms K).one_mem

theorem cG_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    cG β g = 1 ↔ g ∈ Subgroup.centralizer (U : Set G) := by
  rw [cG_of_mem β hg]
  exact cHom_eq_one_iff β _

variable {L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 K)} {β}

theorem cG_of_mem_L (hβ : IsDblCoord L U α β) (hLU : L ≤ Subgroup.normalizer (U : Set G))
    {l : G} (hl : l ∈ L) : cG β l = S38D.dHom (toSL3 α ⟨l, hl⟩) := by
  refine Equiv.ext fun v => ?_
  rw [cG_of_mem β (hLU hl), cHom_of_mem (L := L) (α := α) (Q := U) (β := β) hβ ⟨l, hLU hl⟩ hl v,
    dHom_apply, coe_toSL3]

theorem normalizesDact_cG (hβ : IsDblCoord L U α β) (hα : Function.Surjective α)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {g : G}
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    NormalizesDact ⇑(cG β g) := by
  intro X
  obtain ⟨l, hl⟩ := toSL3_surjective hα X
  have hlbl : g * (l : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL _).mp l.2
  refine ⟨toSL3 α ⟨_, hlbl⟩, fun v => ?_⟩
  have h1 : cG β g * cG β l = cG β (g * l * g⁻¹) * cG β g := by
    rw [← cG_mul β hgU (hLU l.2), ← cG_mul β (hLU hlbl) hgU]
    congr 1
    group
  have h2 := congrArg (fun e : Equiv.Perm (Fin 2 → Fin 3 → K) => e v) h1
  simp only [Equiv.Perm.mul_apply] at h2
  rw [cG_of_mem_L hβ hLU l.2, cG_of_mem_L hβ hLU hlbl, dHom_apply, dHom_apply] at h2
  rw [← hl]
  exact h2

variable (β)

@[expose] noncomputable def cImg (A : Subgroup G) : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → K)) :=
  (A.subgroupOf (Subgroup.normalizer (U : Set G))).map (cHom β)

theorem mem_cImg {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G))
    {e : Equiv.Perm (Fin 2 → Fin 3 → K)} : e ∈ cImg β A ↔ ∃ a ∈ A, cG β a = e := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, cG_of_mem β x.2⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA ha⟩, ha, (cG_of_mem β (hA ha)).symm⟩

theorem cG_mem_cImg {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G)) {a : G}
    (ha : a ∈ A) : cG β a ∈ cImg β A :=
  (mem_cImg β hA).mpr ⟨a, ha, rfl⟩

theorem cImg_mono {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (U : Set G)) (hAB : A ≤ B) :
    cImg β A ≤ cImg β B := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_cImg β hB).mpr ⟨x, hAB hx, cG_of_mem β x.2⟩

theorem card_fixPts_cImg {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card (fixPts (cImg β A : Set (Equiv.Perm (Fin 2 → Fin 3 → K)))) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := by
  have hfix : ∀ v : Fin 2 → Fin 3 → K,
      v ∈ fixPts (cImg β A : Set (Equiv.Perm (Fin 2 → Fin 3 → K))) ↔
        ((elt β v : ↥U) : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro v
    constructor
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      have h1 := hv _ (cG_mem_cImg β hA ha)
      rw [← crd_elt β v, cG_crd β (hA ha)] at h1
      have h2 : a * (elt β v : G) * a⁻¹ = elt β v := congrArg Subtype.val (crd_injective β h1)
      calc a * (elt β v : G) = a * (elt β v : G) * a⁻¹ * a := by group
        _ = elt β v * a := by rw [h2]
    · intro hv e he
      obtain ⟨a, ha, rfl⟩ := (mem_cImg β hA).mp he
      conv_lhs => rw [← crd_elt β v]
      rw [cG_crd β (hA ha)]
      conv_rhs => rw [← crd_elt β v]
      congr 1
      apply Subtype.ext
      show a * (elt β v : G) * a⁻¹ = elt β v
      rw [Subgroup.mem_centralizer_iff.mp hv a ha]
      group
  refine Nat.card_congr
    { toFun := fun v => ⟨elt β v.1, (elt β v.1).2, (hfix v.1).mp v.2⟩
      invFun := fun u => ⟨crd β ⟨u, u.2.1⟩, (hfix _).mpr (by rw [elt_crd]; exact u.2.2)⟩
      left_inv := fun v => Subtype.ext (crd_elt β v.1)
      right_inv := fun u => Subtype.ext (by simp only [elt_crd]) }

theorem card_U (β : ↥U ≃* Multiplicative (Fin 2 → Fin 3 → K)) : Nat.card ↥U = Nat.card K ^ 6 := by
  rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]

end Coord

section Off

variable [Finite G] {M T L : Subgroup G} {K : Type} [Field K] [Finite K]
  {α : ↥L →* ↥(StatedSL 3 K)}
  {β : ↥(Uq M T L) ≃* Multiplicative (Fin 2 → Fin 3 → K)}

theorem T_le_normalizer_Uq (h : PUHyp M T L) :
    T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  h.le.trans (le_normalizer_Uq h.le_normalizer)

theorem L_le_normalizer_Uq (h : PUHyp M T L) :
    L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  h.L_le.trans (le_normalizer_Uq h.le_normalizer)

omit [Finite K] in
theorem cG_eq_one_iff_mem_pCoreOf (h : PUHyp M T L) (β : ↥(Uq M T L) ≃*
    Multiplicative (Fin 2 → Fin 3 → K)) {t : G} (htT : t ∈ T) :
    cG β t = 1 ↔ t ∈ pCoreOf 2 M := by
  rw [cG_eq_one_iff β (T_le_normalizer_Uq h htT)]
  constructor
  · intro ht
    refine h.mem_pCoreOf_of_comm_Uq htT fun u hu => ?_
    have h1 : ⁅u, t⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp ht u hu
    rw [h1]
    exact one_mem _
  · intro hq
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp
      ((PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) (h.Uq_le_Xq hu)).2) t hq).symm

omit [Finite K] in
theorem relIndex_pCoreOf_eq_card_cImg (h : PUHyp M T L)
    (β : ↥(Uq M T L) ≃* Multiplicative (Fin 2 → Fin 3 → K)) {F : Subgroup G} (hFT : F ≤ T) :
    (pCoreOf 2 M).relIndex F = Nat.card (cImg β F) := by
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hFT.trans (T_le_normalizer_Uq h)
  let φ : ↥F →* Equiv.Perm (Fin 2 → Fin 3 → K) := (cHom β).comp (Subgroup.inclusion hFN)
  have hφ : ∀ x : ↥F, φ x = cG β x := fun x => (cG_of_mem β (hFN x.2)).symm
  have hker : φ.ker = (pCoreOf 2 M).subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ,
      cG_eq_one_iff_mem_pCoreOf h β (hFT x.2)]
  have hrange : φ.range = cImg β F := by
    ext e
    rw [MonoidHom.mem_range, mem_cImg β hFN]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hφ x).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, hφ ⟨a, ha⟩⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]

omit [Finite K] in
theorem cImg_hyps (h : PUHyp M T L) (hβ : IsDblCoord L (Uq M T L) α β)
    (hα : Function.Surjective α) {F : Subgroup G} (hFT : F ≤ T) (hF : IsElemAbelian 2 F) :
    cImg β F ≤ addPerms K ∧ (∀ e ∈ cImg β F, NormalizesDact ⇑e) ∧
      (∀ e ∈ cImg β F, ∀ f ∈ cImg β F, e * f = f * e) ∧ ∀ e ∈ cImg β F, e * e = 1 := by
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hFT.trans (T_le_normalizer_Uq h)
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, -, rfl⟩ := (mem_cImg β hFN).mp he
    exact cG_mem_addPerms β a
  · intro e he
    obtain ⟨a, ha, rfl⟩ := (mem_cImg β hFN).mp he
    exact normalizesDact_cG hβ hα (L_le_normalizer_Uq h) (hFN ha)
      (h.le_normalizer (h.le (hFT ha)))
  · intro e he f hf
    obtain ⟨a, ha, rfl⟩ := (mem_cImg β hFN).mp he
    obtain ⟨b, hb, rfl⟩ := (mem_cImg β hFN).mp hf
    rw [← cG_mul β (hFN ha) (hFN hb), ← cG_mul β (hFN hb) (hFN ha), hcomm a ha b hb]
  · intro e he
    obtain ⟨a, ha, rfl⟩ := (mem_cImg β hFN).mp he
    rw [← cG_mul β (hFN ha) (hFN ha), ← sq, hF.2 a ha, cG_one]

theorem relIndex_le_relIndex_Uq [CharP K 2] (h : PUHyp M T L)
    (hβ : IsDblCoord L (Uq M T L) α β) (hα : Function.Surjective α) {F : Subgroup G}
    (hFT : F ≤ T) (hF : IsElemAbelian 2 F) :
    (pCoreOf 2 M).relIndex F ≤ (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) := by
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hFT.trans (T_le_normalizer_Uq h)
  obtain ⟨hadd, hn, hc, hinv⟩ := cImg_hyps h hβ hα hFT hF
  have hbound := (card_mul_card_fixPts_le hadd hn hc hinv).1
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (F : Set G)) (Uq M T L)
  rw [card_U β, inf_comm, ← card_fixPts_cImg β hFN] at hmul
  rw [relIndex_pCoreOf_eq_card_cImg h β hFT]
  have hpos : 0 < Nat.card (fixPts (cImg β F : Set (Equiv.Perm (Fin 2 → Fin 3 → K)))) := by
    rw [card_fixPts_cImg β hFN]
    exact Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (hbound.trans hmul.symm.le) hpos

theorem offImg_of_isXOff [CharP K 2] (h : PUHyp M T L) (hβ : IsDblCoord L (Uq M T L) α β)
    (hα : Function.Surjective α) {F : Subgroup G} (hF : IsXOff M T F) :
    (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F ∧
      (pCoreOf 2 M).relIndex F = Nat.card K ^ 2 ∧
      cImg β F ≤ (dHom : SL3 K →* Equiv.Perm (Fin 2 → Fin 3 → K)).range ∧
      (∀ g ∈ (cImg β F).comap dHom, g * g = 1) ∧
      Nat.card ((cImg β F).comap dHom) = Nat.card K ^ 2 ∧
      Module.finrank K (fixN ((cImg β F).comap dHom)) = 2 := by
  obtain ⟨hFT, hFel, hFQ, hoff⟩ := hF
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hFT.trans (T_le_normalizer_Uq h)
  obtain ⟨hadd, hn, hc, hinv⟩ := cImg_hyps h hβ hα hFT hFel
  obtain ⟨-, heq⟩ := card_mul_card_fixPts_le hadd hn hc hinv
  have hidx := relIndex_pCoreOf_eq_card_cImg h β hFT
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (F : Set G)) (Uq M T L)
  rw [card_U β, inf_comm, ← card_fixPts_cImg β hFN] at hmul
  have hUX : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right h.Uq_le_Xq Subgroup.index_ne_zero_of_finite
  have hle := relIndex_le_relIndex_Uq h hβ hα hFT hFel
  have h1 : (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F :=
    le_antisymm hoff (hle.trans hUX)
  have h2 : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) = (pCoreOf 2 M).relIndex F :=
    le_antisymm (hUX.trans hoff) hle
  have hEq6 : Nat.card (cImg β F) *
      Nat.card (fixPts (cImg β F : Set (Equiv.Perm (Fin 2 → Fin 3 → K)))) = Nat.card K ^ 6 := by
    rw [← hidx, ← h2, hmul]
  obtain ⟨hdiag, hcases⟩ := heq hEq6
  have hEne : cImg β F ≠ ⊥ := by
    intro hbot
    apply hFQ
    intro x hx
    have hx1 := cG_mem_cImg β hFN hx
    rw [hbot, Subgroup.mem_bot] at hx1
    exact (cG_eq_one_iff_mem_pCoreOf h β (hFT hx)).mp hx1
  have hfix4 := hcases.resolve_left hEne
  have hq0 : 0 < Nat.card K := Nat.card_pos
  have hcardE : Nat.card (cImg β F) = Nat.card K ^ 2 := by
    rw [hfix4] at hEq6
    have h3 : Nat.card (cImg β F) * Nat.card K ^ 4 = Nat.card K ^ 2 * Nat.card K ^ 4 := by
      rw [hEq6]
      ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 4) h3
  have hrange : cImg β F ≤ (dHom : SL3 K →* Equiv.Perm (Fin 2 → Fin 3 → K)).range :=
    hdiag.trans range_dHom.ge
  have hAE : ((cImg β F).comap dHom).map dHom = cImg β F := Subgroup.map_comap_eq_self hrange
  have hcardA : Nat.card ((cImg β F).comap dHom) = Nat.card K ^ 2 := by
    rw [← hcardE]
    conv_rhs => rw [← hAE]
    rw [Subgroup.card_map_of_injective dHom_injective]
  have hfixA : Nat.card (fixN ((cImg β F).comap dHom)) ^ 2 = Nat.card K ^ 4 := by
    rw [← card_fixPts_map_dHom, hAE, hfix4]
  have hfinrank : Module.finrank K (fixN ((cImg β F).comap dHom)) = 2 := by
    rw [card_fixN, ← pow_mul] at hfixA
    have h4 := Nat.pow_right_injective (two_le_card_field (F := K)) hfixA
    omega
  have hA2 : ∀ g ∈ (cImg β F).comap dHom, g * g = 1 := by
    intro g hg
    apply dHom_injective
    rw [map_mul, map_one]
    exact hinv _ hg
  exact ⟨h1, hidx.trans hcardE, hrange, hA2, hcardA, hfinrank⟩

omit [Finite K] in
theorem isPGroup_comap_dHom_cImg (h : PUHyp M T L)
    (β : ↥(Uq M T L) ≃* Multiplicative (Fin 2 → Fin 3 → K)) :
    IsPGroup 2 ((cImg β T).comap (dHom : SL3 K →* Equiv.Perm (Fin 2 → Fin 3 → K))) :=
  ((h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (T_le_normalizer_Uq h)).symm).map
    (cHom β)).comap_of_injective _ dHom_injective

theorem le_sup_of_isXOff [CharP K 2] (h : PUHyp M T L) (hβ : IsDblCoord L (Uq M T L) α β)
    (hα : Function.Surjective α) {F₁ F₂ : Subgroup G} (hF₁ : IsXOff M T F₁)
    (hF₂ : IsXOff M T F₂) : F₂ ≤ F₁ ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, hd₁, h2₁, hc₁, hf₁⟩ := offImg_of_isXOff h hβ hα hF₁
  obtain ⟨-, -, hd₂, h2₂, hc₂, hf₂⟩ := offImg_of_isXOff h hβ hα hF₂
  have hTN := T_le_normalizer_Uq h
  have hA := eq_of_le_of_isPGroup (isPGroup_comap_dHom_cImg h β)
    (Subgroup.comap_mono (cImg_mono β hTN hF₁.1)) (Subgroup.comap_mono (cImg_mono β hTN hF₂.1))
    h2₁ h2₂ hc₁ hc₂ hf₁ hf₂
  have hE : cImg β F₁ = cImg β F₂ := by
    rw [← Subgroup.map_comap_eq_self hd₁, ← Subgroup.map_comap_eq_self hd₂, hA]
  intro x hx
  have hxT := hF₂.1 hx
  have hxE : cG β x ∈ cImg β F₁ := hE ▸ cG_mem_cImg β (hF₂.1.trans hTN) hx
  obtain ⟨y, hy, hyx⟩ := (mem_cImg β (hF₁.1.trans hTN)).mp hxE
  have hyT := hF₁.1 hy
  have hq : y⁻¹ * x ∈ pCoreOf 2 M := by
    refine (cG_eq_one_iff_mem_pCoreOf h β (T.mul_mem (T.inv_mem hyT) hxT)).mp ?_
    rw [cG_mul β (hTN (T.inv_mem hyT)) (hTN hxT), cG_inv β (hTN hyT), hyx, inv_mul_cancel]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

omit [Finite K] in
theorem mem_pCoreOf_of_commute (h : PUHyp M T L) (hβ : IsDblCoord L (Uq M T L) α β) {t : G}
    (htT : t ∈ T) (ht : ∀ X : SL3 K, cG β t * dHom X = dHom X * cG β t) :
    t ∈ pCoreOf 2 M := by
  have hTN := T_le_normalizer_Uq h
  have hLN := L_le_normalizer_Uq h
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, htT⟩
  refine h.mem_pCoreOf_of_rel (D := Subgroup.centralizer (Uq M T L : Set G))
    (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
    (h.not_le_centralizer_of_Uq_le le_rfl) (h.le htT)
    ⟨e, by simpa using congrArg Subtype.val he⟩ fun l hl => ?_
  have hlN := hLN hl
  have htN := hTN htT
  have hc : ⁅t, l⁆ ∈ Subgroup.normalizer (Uq M T L : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem htN hlN) (inv_mem htN)) (inv_mem hlN)
  rw [← cG_eq_one_iff β hc, commutatorElement_def,
    cG_mul β (mul_mem (mul_mem htN hlN) (inv_mem htN)) (inv_mem hlN),
    cG_mul β (mul_mem htN hlN) (inv_mem htN), cG_mul β htN hlN, cG_inv β htN, cG_inv β hlN,
    cG_of_mem_L hβ hLN hl, ht]
  group

theorem mem_sup_of_mem_centralizer [CharP K 2] (h : PUHyp M T L)
    (hβ : IsDblCoord L (Uq M T L) α β) (hα : Function.Surjective α) {F : Subgroup G}
    (hF : IsXOff M T F) {y : G} (hyT : y ∈ T) (hyC : y ∈ Subgroup.centralizer (F : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, -, h2, hcard, hfix⟩ := offImg_of_isXOff h hβ hα hF
  have hTN := T_le_normalizer_Uq h
  have hFN := hF.1.trans hTN
  have hLN := L_le_normalizer_Uq h
  have hn := normalizesDact_cG hβ hα hLN (hTN hyT) (h.le_normalizer (h.le hyT))
  have hn' : NormalizesDact ⇑(cG β y)⁻¹ := by
    rw [← cG_inv β (hTN hyT)]
    exact normalizesDact_cG hβ hα hLN (hTN (T.inv_mem hyT))
      (h.le_normalizer (h.le (T.inv_mem hyT)))
  have hcomm : ∀ X ∈ (cImg β F).comap dHom, cG β y * dHom X = dHom X * cG β y := by
    intro X hX
    obtain ⟨f, hf, hfX⟩ := (mem_cImg β hFN).mp hX
    rw [← hfX, ← cG_mul β (hTN hyT) (hFN hf), ← cG_mul β (hFN hf) (hTN hyT),
      ← Subgroup.mem_centralizer_iff.mp hyC f hf]
  obtain ⟨X₀, hX₀, hκ⟩ :=
    exists_mem_commute_dHom h2 hcard hfix (cG_mem_addPerms β y) hn hn' hcomm
  obtain ⟨e₀, he₀, he₀X⟩ := (mem_cImg β hFN).mp hX₀
  have he₀T := hF.1 he₀
  have hq : e₀⁻¹ * y ∈ pCoreOf 2 M := by
    refine mem_pCoreOf_of_commute h hβ (T.mul_mem (T.inv_mem he₀T) hyT) fun X => ?_
    rw [cG_mul β (hTN (T.inv_mem he₀T)) (hTN hyT), cG_inv β (hTN he₀T), he₀X]
    exact hκ X
  have e : y = e₀ * (e₀⁻¹ * y) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left he₀) (Subgroup.mem_sup_right hq)

end Off

end S38D

open S38D in
theorem PUHyp.xOffData_of_isDoubleSL3U {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hX : IsDoubleSL3U M T L)
    (_hb : 2 < critDist (puAmalgam h.le)) (_hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (_h1 : ¬ IsSL3U M T L) (_h2 : ¬ IsSp4U M T L) : XOffData M T := by
  obtain ⟨-, -, n, K, _, _, α, hK, hα, hnat⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  obtain ⟨β, hβ⟩ := exists_isDblCoord hnat
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => mem_sup_of_mem_centralizer h hβ hα hF hy hyC)
  · exact le_antisymm (sup_le (le_sup_of_isXOff h hβ hα h₂ h₁) le_sup_right)
      (sup_le (le_sup_of_isXOff h hβ hα h₁ h₂) le_sup_right)
  · exact (offImg_of_isXOff h hβ hα hF).1

section Extra

open S38D

theorem PUHyp.inf_centralizer_le_of_isDoubleSL3U {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} (h : PUHyp M T L) (hX : IsDoubleSL3U M T L) {F : Subgroup G}
    (hF : IsXOff M T F) : T ⊓ Subgroup.centralizer (F : Set G) ≤ F ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, n, K, _, _, α, hK, hα, hnat⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  obtain ⟨β, hβ⟩ := exists_isDblCoord hnat
  exact fun y hy => mem_sup_of_mem_centralizer h hβ hα hF hy.1 hy.2

theorem PUHyp.relIndex_of_isXOff_of_doubleNat {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} (h : PUHyp M T L) {K : Type} [Field K] [Fintype K] {n : ℕ}
    {α : ↥L →* ↥(StatedSL 3 K)} (hK : Fintype.card K = 2 ^ n) (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 2) {F : Subgroup G}
    (hF : IsXOff M T F) : (pCoreOf 2 M).relIndex F = Fintype.card K ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  obtain ⟨β, hβ⟩ := exists_isDblCoord hnat
  rw [(offImg_of_isXOff h hβ hα hF).2.1, Nat.card_eq_fintype_card]

end Extra

end CFSG.Quasithin.MS93
