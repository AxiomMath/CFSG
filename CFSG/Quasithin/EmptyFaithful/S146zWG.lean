module

public import CFSG.Quasithin.EmptyFaithful.S146zWE
public import CFSG.Quasithin.EmptyFaithful.S146zWF
public import CFSG.Quasithin.EmptyFaithful.S146zWS5
import CFSG.Quasithin.EmptyFaithful.S1565M7
public import CFSG.Quasithin.EmptyFaithful.S146zWB2

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Quad

variable {V : Type} [CommGroup V]

theorem commV_apply_mem {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {b : MulAut V} (hb : b ∈ B) {u : V}
    (hu : u ∈ commV A) : b u ∈ commV A := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have h1 : x (b v) = b (x v) := by
      have := congrArg (fun f : MulAut V => f v) (hcomm x hx b hb)
      simpa using this
    rw [map_mul, map_inv, ← h1]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a c _ _ ha hc => rw [map_mul]; exact mul_mem ha hc
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem commV_le_fixV {L₁ L₂ : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hperf : Group.IsPerfect ↥L₂)
    {C W₁ W₂ : Subgroup V} (hC : C ≤ fixV L₂) (hW₁ : commV L₁ ≤ W₁) (hW₂ : commV L₂ ≤ W₂)
    (hCW : W₁ ⊓ W₂ ≤ C) : commV L₁ ≤ fixV L₂ := by
  intro u hu
  have hmem : ∀ b ∈ L₂, (b : MulAut V) u * u⁻¹ ∈ C := by
    intro b hb
    refine hCW ⟨hW₁ ?_, hW₂ (Subgroup.subset_closure ⟨b, hb, u, rfl⟩)⟩
    exact mul_mem (commV_apply_mem hcomm hb hu) (inv_mem hu)
  let f : ↥L₂ →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have hc : (b' : MulAut V) u * u⁻¹ ∈ fixV L₂ := hC (hmem b' b'.2)
        have h1 : (b : MulAut V) ((b' : MulAut V) u * u⁻¹) = (b' : MulAut V) u * u⁻¹ := hc b b.2
        rw [map_mul, map_inv] at h1
        have h2 : (b : MulAut V) ((b' : MulAut V) u) =
            (b' : MulAut V) u * u⁻¹ * (b : MulAut V) u := mul_inv_eq_iff_eq_mul.1 h1
        show ((b : MulAut V) * (b' : MulAut V)) u * u⁻¹ = _
        rw [MulAut.mul_apply, h2]
        ac_rfl }
  have hker : ∀ b : ↥L₂, f b = 1 := by
    intro b
    have : b ∈ commutator ↥L₂ := by rw [hperf.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f this)
  intro b hb
  have := hker ⟨b, hb⟩
  exact mul_inv_eq_one.1 this

end Quad

section Pieces

theorem card_statedSL_three (F : Type) [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

theorem two_le_of_card_sl3 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hcard : 504 ≤ Nat.card ↥(StatedSL 3 K)) : 2 ≤ m := by
  by_contra h
  push Not at h
  rw [card_statedSL_three, hK] at hcard
  interval_cases m
  · have := Finite.one_lt_card (α := K)
    rw [hK] at this
    simp at this
  · norm_num at hcard

theorem one_le_of_card {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    1 ≤ m := by
  by_contra h
  have hm0 : m = 0 := by omega
  have := Finite.one_lt_card (α := K)
  rw [hK, hm0] at this
  simp at this

theorem piece_large {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {W C : Subgroup V} (hcard : 504 ≤ Nat.card ↥L) (h : B56Piece L W C) :
    W = commV L ⊔ C ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ) (π : ↥(StatedSL 2 K) →* ↥L),
          1 ≤ m ∧ Nat.card K = 2 ^ m ∧
            (FFModel.nat (StatedSL 2 K)).RealizesVia L W C π) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ) (π : ↥(StatedSL 3 K) →* ↥L),
          2 ≤ m ∧ Nat.card K = 2 ^ m ∧ Function.Bijective π)) := by
  have hSL3 : ∀ {K : Type} [Field K] [Finite K] {m : ℕ} (π : ↥(StatedSL 3 K) →* ↥L),
      Nat.card K = 2 ^ m → Function.Bijective π →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ) (π : ↥(StatedSL 3 K) →* ↥L),
        2 ≤ m ∧ Nat.card K = 2 ^ m ∧ Function.Bijective π := by
    intro K _ _ m π hK hπ
    refine ⟨K, inferInstance, inferInstance, m, π, ?_, hK, hπ⟩
    refine two_le_of_card_sl3 hK ?_
    rw [Nat.card_congr (Equiv.ofBijective π hπ)]
    exact hcard
  rcases h with ⟨hW, hA⟩ | ⟨hW, hB⟩ | ⟨⟨e⟩, -⟩
  · refine ⟨hW, ?_⟩
    rcases hA with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩
    · exact Or.inl ⟨K, inferInstance, inferInstance, n, π, one_le_of_card hK, hK, hπ⟩
    · exfalso
      have h1 : Nat.card ↥L ≤ Nat.card (Equiv.Perm (Fin 5)) :=
        Nat.card_le_card_of_surjective π hπ.1
      have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        decide
      omega
    · exact Or.inr (hSL3 π hK ⟨natural_realizes_injective _ hπ, hπ.1⟩)
  · refine ⟨hW, ?_⟩
    obtain ⟨m, K, _, _, hK, I, π, -, -, -, hI⟩ := hB
    exact Or.inr (hSL3 π hK ⟨natural_realizes_injective _ (hI 0), (hI 0).1⟩)
  · exfalso
    have h1 : Nat.card ↥L = Nat.card ↥(StatedSL 3 (ZMod 2)) := Nat.card_congr e.toEquiv
    rw [card_statedSL_three, Nat.card_zmod] at h1
    norm_num at h1
    omega

end Pieces

omit [Finite G] in
theorem exists_surj_wAut {J J' R : Subgroup G} (S : Subgroup G) (hS : S ≤ wY J J' R) :
    ∃ f : ↥S →* ↥(wAut J J' R S), Function.Surjective f := by
  let g : ↥S →* MulAut (VMod J J' R) := (actY J J' R).comp (Subgroup.inclusion hS)
  have hrange : g.range = wAut J J' R S := by
    ext φ
    rw [MonoidHom.mem_range, mem_autI]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨(s : G), Y_le_normalizer_V (hS s.2)⟩, s.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨(n : G), hn⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange).toMonoidHom.comp g.rangeRestrict,
    (MulEquiv.subgroupCongr hrange).surjective.comp g.rangeRestrict_surjective⟩

omit [Finite G] in
theorem isSylowTwoOf_conjByElt {S L : Subgroup G} (g : G) (h : IsSylowTwoOf S L) :
    IsSylowTwoOf (conjByElt g S) (conjByElt g L) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) S L
    (MulAut.conj g).injective
  change ¬ 2 ∣ (S.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom)
  rw [this]
  exact h.2.2

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem no_elemAbelian_sq' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hEJ' : E ≤ J') (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) : False := by
  have hJ : conjByElt ρ⁻¹ J' = J := by rw [d.eq, conjByElt_inv_conjByElt_W]
  have hE'J : conjByElt ρ⁻¹ E ≤ J := by
    rw [← hJ]
    exact Subgroup.map_mono hEJ'
  refine d.no_elemAbelian_sq hp hp2 hE'J
    (CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj ρ⁻¹).toMonoidHom) ?_
  rw [← hcard]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj ρ⁻¹).toMonoidHom
    (MulAut.conj ρ⁻¹).injective).toEquiv).symm

theorem false_of_sl3 {S : Subgroup G} (hS : S = J ∨ S = J') {K : Type} [Field K] [Finite K]
    {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (π : ↥(StatedSL 3 K) →* ↥(wAut J J' R S)) (hπ : Function.Bijective π) : False := by
  have hSY : S ≤ wY J J' R := by
    rcases hS with rfl | rfl
    · exact J_le_wY _ _ _
    · exact J'_le_wY _ _ _
  obtain ⟨f, hf⟩ := exists_surj_wAut S hSY
  let e := MulEquiv.ofBijective π hπ
  let f₃ : ↥S →* ↥(StatedSL 3 K) := e.symm.toMonoidHom.comp f
  have hf₃ : Function.Surjective f₃ := e.symm.surjective.comp hf
  obtain ⟨p, hp, hp2, E, hE, hcard⟩ := exists_elemAbelian_sq_of_surjective_SL3 hK hm f₃ hf₃
  have hE' : IsElemAbelian p (E.map S.subtype) := CFSG.SectionRank.isElemAbelian_map hE S.subtype
  have hcard' : Nat.card (E.map S.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hcard]
  have hES : E.map S.subtype ≤ S := Subgroup.map_subtype_le E
  rcases hS with rfl | rfl
  · exact d.no_elemAbelian_sq hp hp2 hES hE' hcard'
  · exact d.no_elemAbelian_sq' hp hp2 hES hE' hcard'


theorem isSylowTwoOf_inf_of_large (h56 : AsB56) (hA21 : AsA21SQTKSection)
    (hcard : 504 ≤ Nat.card ↥(wAut J J' R J)) : IsSylowTwoOf (R ⊓ J) J := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ := d.moduleFacts
  obtain ⟨hff, W₁, W₂, hCW₁, hCW₂, hWtop, hWinf, hp₁, hp₂⟩ := d.twoB56_large h56 hA21 hcard
  have hcard₂ : 504 ≤ Nat.card ↥(wAut J J' R J') := by
    rw [hconj, Subgroup.card_map_of_injective (MulAut.conj (wTau J J' R d.mem_Y)).injective]
    exact hcard
  obtain ⟨hW₁, h₁⟩ := piece_large hcard hp₁
  obtain ⟨hW₂, h₂⟩ := piece_large hcard₂ hp₂
  rcases h₁ with ⟨K₁, _, _, m₁, π₁, hm₁, hK₁, hπ₁⟩ | ⟨K₁, _, _, m₁, π₁, hm₁, hK₁, hπ₁⟩
  swap
  · exact (d.false_of_sl3 (Or.inl rfl) hm₁ hK₁ π₁ hπ₁).elim
  rcases h₂ with ⟨K₂, _, _, m₂, π₂, hm₂, hK₂, hπ₂⟩ | ⟨K₂, _, _, m₂, π₂, hm₂, hK₂, hπ₂⟩
  swap
  · exact (d.false_of_sl3 (Or.inr rfl) hm₂ hK₂ π₂ hπ₂).elim
  have hfix₂ : fixV (wAut J J' R J ⊔ wAut J J' R J') ≤ fixV (wAut J J' R J') := fun c hc b hb =>
    hc b (Subgroup.mem_sup_right hb)
  have hfix₁ : fixV (wAut J J' R J ⊔ wAut J J' R J') ≤ fixV (wAut J J' R J) := fun c hc a ha =>
    hc a (Subgroup.mem_sup_left ha)
  have hcomm₁W : commV (wAut J J' R J) ≤ W₁ := by rw [hW₁]; exact le_sup_left
  have hcomm₂W : commV (wAut J J' R J') ≤ W₂ := by rw [hW₂]; exact le_sup_left
  have hc₁ : commV (wAut J J' R J) ≤ fixV (wAut J J' R J') :=
    commV_le_fixV hc hq₂.1 hfix₂ hcomm₁W hcomm₂W hWinf.le
  have hc₂ : commV (wAut J J' R J') ≤ fixV (wAut J J' R J) :=
    commV_le_fixV (fun a ha b hb => (hc b hb a ha).symm) hq₁.1 hfix₁ hcomm₂W hcomm₁W
      (by rw [inf_comm]; exact hWinf.le)
  have hW₁fix : ∀ b ∈ wAut J J' R J', ∀ x ∈ W₁, b x = x := by
    intro b hb x hx
    have hle : W₁ ≤ fixV (wAut J J' R J') := by
      rw [hW₁]
      exact sup_le hc₁ hfix₂
    exact hle hx b hb
  have hW₂fix : ∀ a ∈ wAut J J' R J, ∀ y ∈ W₂, a y = y := by
    intro a ha y hy
    have hle : W₂ ≤ fixV (wAut J J' R J) := by
      rw [hW₂]
      exact sup_le hc₂ hfix₁
    exact hle hy a ha
  obtain ⟨Φ, Θ, hM⟩ := S146zU.UC2.pairModel_of_realizes hπ₁ hπ₂ hWtop hWinf.le hW₁fix hW₂fix hc
  have hL₁card : Nat.card ↥(wAut J J' R J) = Nat.card ↥(StatedSL 2 K₁) :=
    (Nat.card_congr (Equiv.ofBijective π₁ ⟨natural_realizes_injective _ hπ₁, hπ₁.1⟩)).symm
  have hL₂card : Nat.card ↥(wAut J J' R J') = Nat.card ↥(StatedSL 2 K₂) :=
    (Nat.card_congr (Equiv.ofBijective π₂ ⟨natural_realizes_injective _ hπ₂, hπ₂.1⟩)).symm
  obtain ⟨A, hA, hAR⟩ := d.exists_offender_le_R
  have hAJ : A ≤ wAut J J' R J ⊔ wAut J J' R J' := hff ▸ B6.le_ffJ hA
  rcases pairModel_offender_sylow hM hK₁ hK₂ hm₁ hm₂ hL₁card hL₂card hA.2.1 hAJ hA.2.2.1.2
      (S146zU.UC2.card_le_of_isFFStarOffender hA) with ⟨S, hS, hSA⟩ | ⟨S, hS, hSA⟩
  · exact d.isSylowTwoOf_inf_of_sylow hS (hSA.trans hAR)
  ·
    have hτR : wTau J J' R d.mem_Y ∈ wAut J J' R R :=
      convI_mem_autI _ d.mem (Y_le_normalizer_V d.mem_Y)
    set τ := wTau J J' R d.mem_Y with hτ
    have hS' : IsSylowTwoOf (conjByElt τ⁻¹ S) (wAut J J' R J) := by
      have h1 := isSylowTwoOf_conjByElt τ⁻¹ hS
      have h2 : conjByElt τ⁻¹ (wAut J J' R J') = wAut J J' R J := by
        rw [hconj]
        exact conjByElt_inv_conjByElt_W τ _
      rwa [h2] at h1
    refine d.isSylowTwoOf_inf_of_sylow hS' ?_
    intro x hx
    rw [mem_conjByElt, inv_inv] at hx
    have hy : τ * x * τ⁻¹ ∈ wAut J J' R R := hAR (hSA hx)
    have hx' : x = τ⁻¹ * (τ * x * τ⁻¹) * τ := by group
    rw [hx']
    exact mul_mem (mul_mem (inv_mem hτR) hy) hτR

end WreathData

end CFSG.Quasithin.S146zW
