module

public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs
public import CFSG.Quasithin.EmptyFaithful.SzPS8OvgMap
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4FStar
public import Certificates.Certificate7099

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.A7Mod

namespace SzPS8

section Data

@[expose] def J1list : List (Equiv.Perm (Fin 7)) := [1, y2, y2 * y2]

@[expose] def r1 : Equiv.Perm (Fin 7) := Equiv.swap 1 4 * Equiv.swap 3 5

@[expose] def r2 : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 0 4 * Equiv.swap 2 3 * Equiv.swap 2 5

@[expose] def Dlist : List (Equiv.Perm (Fin 7)) :=
  S0list.filter fun s => decide (Equiv.Perm.sign s = 1)

@[expose] def Jalist : List (Equiv.Perm (Fin 7)) := Dlist.flatMap fun d => [d, d * r1, d * r2]

theorem J1_closed :
    (J1list.all fun a => J1list.all fun b => decide (a * b ∈ J1list)) = true := by
  decide +kernel

theorem J1_inv : (J1list.all fun a => decide (a⁻¹ ∈ J1list)) = true := by decide +kernel

theorem J1_alt : (J1list.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem J1_norm :
    (S0list.all fun s => J1list.all fun j => decide (s * j * s⁻¹ ∈ J1list)) = true := by
  decide +kernel

theorem J1_inf : (J1list.all fun x => !decide (x ∈ S0list) || decide (x = 1)) = true := by
  decide +kernel

theorem J1_nodup : J1list.Nodup := by decide +kernel

theorem J1_len : J1list.length = 3 := by decide +kernel

theorem Ja_closed :
    (Jalist.all fun a => Jalist.all fun b => decide (a * b ∈ Jalist)) = true := by
  decide +kernel

theorem Ja_inv : (Jalist.all fun a => decide (a⁻¹ ∈ Jalist)) = true := by decide +kernel

theorem Ja_alt : (Jalist.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem Ja_norm :
    (S0list.all fun s => Jalist.all fun j => decide (s * j * s⁻¹ ∈ Jalist)) = true := by
  decide +kernel

theorem Ja_inf :
    (S0list.all fun x => !decide (Equiv.Perm.sign x = 1) || decide (x ∈ Jalist)) = true := by
  decide +kernel

theorem Ja_nodup : Jalist.Nodup := by decide +kernel

theorem Ja_len : Jalist.length = 24 := by decide +kernel

theorem J1_move2 : ∃ i : Fin 7, w2 (y2⁻¹ i) ≠ w2 i := by decide +kernel

theorem J1_move3 : ∃ i : Fin 7, w3 (y2⁻¹ i) ≠ w3 i := by decide +kernel

theorem Ja_move1 : ∃ i : Fin 7, w1 (r1⁻¹ i) ≠ w1 i := by decide +kernel

theorem y2_mem : y2 ∈ J1list := by decide +kernel

theorem r1_mem : r1 ∈ Jalist := by decide +kernel

theorem one_mem_Ja : (1 : Equiv.Perm (Fin 7)) ∈ Jalist := by decide +kernel

end Data

section Subgroups

@[expose] def listSubgroup (l : List (Equiv.Perm (Fin 7))) (h1 : 1 ∈ l)
    (hm : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) (hi : ∀ a ∈ l, a⁻¹ ∈ l) :
    Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {x | x ∈ l}
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  one_mem' := h1
  inv_mem' := fun {a} ha => hi a ha

theorem J1_closed' : ∀ a ∈ J1list, ∀ b ∈ J1list, a * b ∈ J1list := by
  simpa [List.all_eq_true] using J1_closed

theorem J1_inv' : ∀ a ∈ J1list, a⁻¹ ∈ J1list := by simpa [List.all_eq_true] using J1_inv

theorem J1_alt' : ∀ a ∈ J1list, Equiv.Perm.sign a = 1 := by simpa [List.all_eq_true] using J1_alt

theorem J1_norm' : ∀ s ∈ S0list, ∀ j ∈ J1list, s * j * s⁻¹ ∈ J1list := by
  simpa [List.all_eq_true] using J1_norm

theorem J1_inf' : ∀ x ∈ J1list, x ∈ S0list → x = 1 := by
  simpa [List.all_eq_true, imp_iff_not_or] using J1_inf

theorem Ja_closed' : ∀ a ∈ Jalist, ∀ b ∈ Jalist, a * b ∈ Jalist := by
  simpa [List.all_eq_true] using Ja_closed

theorem Ja_inv' : ∀ a ∈ Jalist, a⁻¹ ∈ Jalist := by simpa [List.all_eq_true] using Ja_inv

theorem Ja_alt' : ∀ a ∈ Jalist, Equiv.Perm.sign a = 1 := by simpa [List.all_eq_true] using Ja_alt

theorem Ja_norm' : ∀ s ∈ S0list, ∀ j ∈ Jalist, s * j * s⁻¹ ∈ Jalist := by
  simpa [List.all_eq_true] using Ja_norm

theorem Ja_inf' : ∀ x ∈ S0list, Equiv.Perm.sign x = 1 → x ∈ Jalist := by
  simpa [List.all_eq_true, imp_iff_not_or] using Ja_inf

@[expose] def J1 : Subgroup (Equiv.Perm (Fin 7)) :=
  listSubgroup J1list (List.mem_cons_self) J1_closed' J1_inv'

@[expose] def Ja : Subgroup (Equiv.Perm (Fin 7)) :=
  listSubgroup Jalist one_mem_Ja Ja_closed' Ja_inv'

theorem J1_le_alt : J1 ≤ alternatingGroup (Fin 7) := fun x hx =>
  (Equiv.Perm.mem_alternatingGroup).2 (J1_alt' x hx)

theorem Ja_le_alt : Ja ≤ alternatingGroup (Fin 7) := fun x hx =>
  (Equiv.Perm.mem_alternatingGroup).2 (Ja_alt' x hx)

theorem J1_normalized (h : A7Raw) : ∀ s ∈ S0, ∀ j ∈ J1, s * j * s⁻¹ ∈ J1 :=
  fun s hs j hj => J1_norm' s ((mem_S0_iff h s).1 hs) j hj

theorem Ja_normalized (h : A7Raw) : ∀ s ∈ S0, ∀ j ∈ Ja, s * j * s⁻¹ ∈ Ja :=
  fun s hs j hj => Ja_norm' s ((mem_S0_iff h s).1 hs) j hj

theorem card_J1 : Nat.card J1 = 3 := by
  rw [card_eq_length (H := J1) (l := J1list) (fun x => Iff.rfl) J1_nodup, J1_len]

theorem card_Ja : Nat.card Ja = 24 := by
  rw [card_eq_length (H := Ja) (l := Jalist) (fun x => Iff.rfl) Ja_nodup, Ja_len]

theorem relIndex_J1 (h : A7Raw) : S0.relIndex J1 = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := S0) (K := J1)
  have h2 : Nat.card ↥(S0 ⊓ J1) = 1 := by
    have : S0 ⊓ J1 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact J1_inf' x hx.2 ((mem_S0_iff h x).1 hx.1)
    rw [this, Subgroup.card_bot]
  rw [h2, mul_one, card_J1] at h1
  exact h1

theorem relIndex_Ja (h : A7Raw) : S0.relIndex Ja = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := S0) (K := Ja)
  have h2 : S0 ⊓ Ja = S0 ⊓ alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, Ja_le_alt hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, Ja_inf' x ((mem_S0_iff h x).1 hx1) ((Equiv.Perm.mem_alternatingGroup).1 hx2)⟩
  rw [h2, card_S0_inf h, card_Ja] at h1
  omega

theorem exists_datum (h : A7Raw) (w : V7) (hw0 : w ≠ 0)
    (hfix : ∀ s ∈ S0 ⊓ alternatingGroup (Fin 7), pAct s w = w) :
    ∃ J : Subgroup (Equiv.Perm (Fin 7)), J ≤ alternatingGroup (Fin 7) ∧
      (∀ s ∈ S0, ∀ j ∈ J, s * j * s⁻¹ ∈ J) ∧ S0.relIndex J = 3 ∧ ∃ j ∈ J, pAct j w ≠ w := by
  have hv : (w : Fin 7 → ZMod 2) = 0 ∨ (w : Fin 7 → ZMod 2) = w1 ∨
      (w : Fin 7 → ZMod 2) = w2 ∨ (w : Fin 7 → ZMod 2) = w3 := by
    refine h.2.2.1 (w : Fin 7 → ZMod 2) w.2 fun s hs hsign i => ?_
    have h1 := hfix s ⟨(mem_S0_iff h s).2 hs, (Equiv.Perm.mem_alternatingGroup).2 hsign⟩
    exact congrFun (congrArg Subtype.val h1) i
  rcases hv with hv | hv | hv | hv
  · exact absurd (Subtype.ext hv) hw0
  · obtain ⟨i, hi⟩ := Ja_move1
    refine ⟨Ja, Ja_le_alt, Ja_normalized h, relIndex_Ja h, r1, r1_mem, fun hmv => hi ?_⟩
    have := congrFun (congrArg Subtype.val hmv) i
    rw [pAct_apply, hv] at this
    exact this
  · obtain ⟨i, hi⟩ := J1_move2
    refine ⟨J1, J1_le_alt, J1_normalized h, relIndex_J1 h, y2, y2_mem, fun hmv => hi ?_⟩
    have := congrFun (congrArg Subtype.val hmv) i
    rw [pAct_apply, hv] at this
    exact this
  · obtain ⟨i, hi⟩ := J1_move3
    refine ⟨J1, J1_le_alt, J1_normalized h, relIndex_J1 h, y2, y2_mem, fun hmv => hi ?_⟩
    have := congrFun (congrArg Subtype.val hmv) i
    rw [pAct_apply, hv] at this
    exact this

end Subgroups

section Model

theorem relIndex_inf_of_le {G : Type*} [Group G] {S K J : Subgroup G} (hJK : J ≤ K) :
    (S ⊓ K).relIndex J = S.relIndex J := by
  rw [← Subgroup.relIndex_inf_mul_relIndex, inf_of_le_right hJK,
    Subgroup.relIndex_eq_one.mpr hJK, mul_one]

theorem false_of_model (h : A7Raw) {K : Subgroup (Equiv.Perm (Fin 7))}
    (hK : K = alternatingGroup (Fin 7) ∨ K = ⊤) {S' : Subgroup (V7 ≃ₗ[ZMod 2] V7)}
    (hS' : IsSylowTwoOf S' (K.map pAct)) {v' : V7} (hv0 : v' ≠ 0) (hfix : ∀ s ∈ S', s v' = v')
    (hF : OvgFix S' pA7 v') : False := by
  have hAK : alternatingGroup (Fin 7) ≤ K := by
    rcases hK with rfl | rfl
    · exact le_rfl
    · exact le_top
  have hS0K : IsSylowTwoOf (S0 ⊓ K) K := by
    rcases hK with rfl | rfl
    · exact isSylowTwoOf_S0_inf h
    · rw [inf_top_eq]
      exact isSylowTwoOf_S0 h
  have hS0' : IsSylowTwoOf ((S0 ⊓ K).map pAct) (K.map pAct) :=
    isSylowTwoOf_map_of_injective pAct_injective hS0K
  obtain ⟨γ, hγ, hγT⟩ := exists_conj_eq_of_isSylowTwoOf hS' hS0'
  obtain ⟨g, hgK, rfl⟩ := hγ
  have hnorm : ∀ n ∈ pA7, (pAct g)⁻¹ * n * pAct g ∈ pA7 := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨g⁻¹ * τ * g, ?_, by simp [map_mul, map_inv]⟩
    have := (alternatingGroup.normal : (alternatingGroup (Fin 7)).Normal).conj_mem τ hτ g⁻¹
    simpa using this
  have hF' := hF.conj_of hnorm hγT
  have hw0 : pAct g v' ≠ 0 := fun h0 => hv0 ((map_eq_zero_iff (pAct g) (pAct g).injective).mp h0)
  have hwfix : ∀ s ∈ S0 ⊓ alternatingGroup (Fin 7), pAct s (pAct g v') = pAct g v' := by
    intro s hs
    have hs' : pAct s ∈ (S0 ⊓ K).map pAct := ⟨s, ⟨hs.1, hAK hs.2⟩, rfl⟩
    obtain ⟨y, hy, hys⟩ := (hγT _).mp hs'
    have h1 : pAct g (y v') = pAct g v' := by rw [hfix y hy]
    calc pAct s (pAct g v') = (pAct g * y * (pAct g)⁻¹) (pAct g v') := by rw [← hys]
      _ = pAct g (y v') := by simp
      _ = pAct g v' := h1
  obtain ⟨J, hJA, hJn, hidx, j, hj, hmv⟩ := exists_datum h (pAct g v') hw0 hwfix
  have hJn' : ∀ t ∈ (S0 ⊓ K).map pAct, ∀ j' ∈ J.map pAct, t * j' * t⁻¹ ∈ J.map pAct := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨j'', hj'', rfl⟩
    exact ⟨s * j'' * s⁻¹, hJn s hs.1 j'' hj'', by simp [map_mul, map_inv]⟩
  have hidx' : ((S0 ⊓ K).map pAct).relIndex (J.map pAct) = 3 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ pAct_injective,
      relIndex_inf_of_le (hJA.trans hAK), hidx]
  exact hmv (hF' (J.map pAct) (Subgroup.map_mono hJA) hJn' (Or.inl hidx') (pAct j) ⟨j, hj, rfl⟩)

end Model

section Concl4

theorem false_of_concl4 (h : A7Raw) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (S : OvgSetting Γ T0 v) (hC4 : G112Concl4 Γ) :
    False := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, φ, ψ, hψ⟩ := hC4
  set c := conjEquiv ψ with hcdef
  set F := (genFittingFStar ↥Γ).map Γ.subtype with hFdef
  have hcF : ∀ γ : ↥(genFittingFStar ↥Γ),
      c ((γ : ↥Γ) : V ≃ₗ[ZMod 2] V) = pAct (φ γ : Equiv.Perm (Fin 7)) := by
    intro γ
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    rw [conjEquiv_apply]
    have h1 := hψ γ (ψ.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hpA7 : pA7 = F.map c.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨γ, hγ⟩ := φ.surjective ⟨σ, hσ⟩
      refine ⟨((γ : ↥Γ) : V ≃ₗ[ZMod 2] V), ⟨γ, γ.2, rfl⟩, ?_⟩
      show c _ = pAct σ
      rw [hcF, hγ]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨φ ⟨γ, hγ⟩, (φ ⟨γ, hγ⟩).2, (hcF ⟨γ, hγ⟩).symm⟩
  set Γ' := Γ.map c.toMonoidHom with hΓ'def
  have hFΓ : F ≤ Γ := Subgroup.map_subtype_le _
  have hle1 : pA7 ≤ Γ' := hpA7 ▸ Subgroup.map_mono hFΓ
  have hΓF : Γ ≤ Subgroup.normalizer (F : Set (V ≃ₗ[ZMod 2] V)) := by
    have := genFittingFStar_normal' ↥Γ
    have h1 := Subgroup.le_normalizer_map (H := genFittingFStar ↥Γ) Γ.subtype
    rw [Subgroup.normalizer_eq_top (genFittingFStar ↥Γ), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have hle2 : Γ' ≤ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7)) := by
    rw [hpA7]
    exact (Subgroup.map_mono hΓF).trans (Subgroup.le_normalizer_map c.toMonoidHom)
  obtain ⟨K, hK, hΓK⟩ := eq_map_of_le_normalizer (stabCount_of_raw h) hle1 hle2
  obtain ⟨N, hNn, hN1, hF0⟩ := S.exists_normal_subtype
  have hsimple : IsSimpleGroup ↥(genFittingFStar ↥Γ) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact φ.isSimpleGroup
  have hFN : genFittingFStar ↥Γ ≤ N := L1294F.genFittingFStar_le_of_normal hsimple hNn hN1
  have hF1 : OvgFix T0 F v := hF0.mono (Subgroup.map_mono hFN)
  have hF2 : OvgFix (T0.map c.toMonoidHom) pA7 (ψ v) := by
    rw [hpA7]
    exact hF1.map c ψ fun γ x => by rw [conjEquiv_apply, LinearEquiv.symm_apply_apply]
  have hS'syl : IsSylowTwoOf (T0.map c.toMonoidHom) (K.map pAct) := by
    rw [← hΓK]
    exact isSylowTwoOf_map_equiv c S.sylow
  have hv0 : ψ v ≠ 0 := fun h0 => S.ne_zero (ψ.injective (by rw [h0, map_zero]))
  have hfix : ∀ s ∈ T0.map c.toMonoidHom, s (ψ v) = ψ v := by
    rintro _ ⟨t, ht, rfl⟩
    change conjEquiv ψ t (ψ v) = ψ v
    rw [conjEquiv_apply, LinearEquiv.symm_apply_apply, S.fix t ht]
  exact false_of_model h hK hS'syl hv0 hfix hF2

theorem excl4_of_raw (h : A7Raw) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h35 : Lemma1435) : Lemma14315Excl4 := by
  intro G _ _ T M hyp hnot hU D hc
  obtain ⟨v, S⟩ := exists_ovgSetting h11 h113 h35 hyp hnot hU D
  exact (false_of_concl4 h S hc).elim

theorem excl4_of_ovg (h11 : StageLemma14111)
    (h113 : StageLemma14113) (h35 : Lemma1435) : Lemma14315Excl4 :=
  excl4_of_raw Certificates.certificate7099 h11 h113 h35

end Concl4

end SzPS8

end CFSG.Quasithin
