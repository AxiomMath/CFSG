module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqPar
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqOrb
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Alt
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Lem1227Eq

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.End1222.AltDn CFSG.QuasithinUnique CFSG.Open
open scoped IsMulCommutative

@[expose] noncomputable def moveP (γ : Perm (Fin 6)) : PermMod 6 →* PermMod 6 :=
  CFSG.Quasithin.H13.End1222.moveHom (permAct 6 γ)

@[expose] noncomputable def Msub (Γ' : Subgroup Alt6) : Subgroup (PermMod 6) :=
  coreMod 6 ⊓ ⨅ γ ∈ Γ', (kerSub 6).comap (moveP (γ : Perm (Fin 6)))

theorem mem_Msub {Γ' : Subgroup Alt6} {m : PermMod 6} :
    m ∈ Msub Γ' ↔ m ∈ coreMod 6 ∧
      ∀ γ ∈ Γ', permAct 6 (γ : Perm (Fin 6)) m * m⁻¹ ∈ kerSub 6 := by
  simp only [Msub, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact Iff.rfl

theorem Msub_le_coreMod (Γ' : Subgroup Alt6) : Msub Γ' ≤ coreMod 6 := fun _ h => (mem_Msub.1 h).1

@[expose] def PM (x : Fin 6 → ZMod 2) : Prop :=
  (∑ i, x i = 0) ∧ ∀ σ ∈ QA6list, ∃ b : ZMod 2, ∀ i : Fin 6, x (σ⁻¹ i) - x i = b

instance : DecidablePred PM := fun x => by unfold PM; infer_instance

theorem card_PM : (Finset.univ.filter PM).card = 4 := by decide +kernel

theorem mem_Msub_S6 {m : PermMod 6} : m ∈ Msub S6 ↔ PM (Multiplicative.toAdd m) := by
  rw [mem_Msub]
  unfold PM
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun σ hσ => ?_⟩
    have hσA : σ ∈ Dsub := mem_Dsub.2 hσ
    have := h ⟨σ, Dsub_le_alternating hσA⟩ (Subgroup.mem_subgroupOf.2 hσA)
    rw [mem_kerSub_iff] at this
    obtain ⟨-, b, hb⟩ := this
    exact ⟨b, fun i => by rw [← toAdd_permAct_mul_inv]; exact hb i⟩
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun γ hγ => ?_⟩
    have hσ : (γ : Perm (Fin 6)) ∈ QA6list := mem_Dsub.1 (Subgroup.mem_subgroupOf.1 hγ)
    obtain ⟨b, hb⟩ := h _ hσ
    rw [mem_kerSub_iff]
    refine ⟨?_, b, fun i => ?_⟩
    · exact Subgroup.mul_mem _ (permAct_mem_coreMod _ hm) (Subgroup.inv_mem _ hm)
    · rw [toAdd_permAct_mul_inv]
      exact hb i

theorem card_Msub_S6 : Nat.card (Msub S6) = 4 := by
  have h1 : Nat.card (Msub S6) = Nat.card {x : Fin 6 → ZMod 2 // PM x} :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun m => mem_Msub_S6))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_PM

theorem permAct_mem_kerSub (σ : Perm (Fin 6)) {x : PermMod 6} (hx : x ∈ kerSub 6) :
    permAct 6 σ x ∈ kerSub 6 := by
  rw [mem_kerSub_iff] at hx ⊢
  obtain ⟨hc, b, hb⟩ := hx
  exact ⟨permAct_mem_coreMod σ hc, b, fun i => by rw [permAct_apply]; exact hb _⟩

theorem permAct_eq_of_mem_kerSub (σ : Perm (Fin 6)) {x : PermMod 6} (hx : x ∈ kerSub 6) :
    permAct 6 σ x = x := by
  obtain ⟨-, b, hb⟩ := mem_kerSub_iff.1 hx
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply, hb, hb]

theorem kerSub_le_Msub (Γ' : Subgroup Alt6) : kerSub 6 ≤ Msub Γ' := fun x hx => by
  refine mem_Msub.2 ⟨(mem_kerSub_iff.1 hx).1, fun γ _ => ?_⟩
  rw [permAct_eq_of_mem_kerSub _ hx]
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel x
  rw [h1]
  exact Subgroup.one_mem _

theorem permAct_mem_Msub_map (g : Alt6) {Γ : Subgroup Alt6} {m : PermMod 6} (hm : m ∈ Msub Γ) :
    permAct 6 (g : Perm (Fin 6)) m ∈ Msub (Γ.map (MulAut.conj g).toMonoidHom) := by
  rw [mem_Msub] at hm ⊢
  refine ⟨permAct_mem_coreMod _ hm.1, ?_⟩
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 := permAct_mem_kerSub (g : Perm (Fin 6)) (hm.2 γ hγ)
  have hc : (((MulAut.conj g) γ : Alt6) : Perm (Fin 6)) =
      (g : Perm (Fin 6)) * (γ : Perm (Fin 6)) * (g : Perm (Fin 6))⁻¹ := rfl
  have h2 : permAct 6 (((MulAut.conj g) γ : Alt6) : Perm (Fin 6))
        (permAct 6 (g : Perm (Fin 6)) m) * (permAct 6 (g : Perm (Fin 6)) m)⁻¹ =
      permAct 6 (g : Perm (Fin 6)) (permAct 6 (γ : Perm (Fin 6)) m * m⁻¹) := by
    rw [hc]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
    exact congrArg _ (map_inv (permAct 6 (g : Perm (Fin 6))) m).symm
  rw [MulEquiv.coe_toMonoidHom, h2]
  exact h1

theorem exists_conj_eq_of_sylow {X : Type*} [Group X] [Finite X] {T S : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hS : IsSylowTwoOf S ⊤) :
    ∃ g : X, T.map (MulAut.conj g).toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff'.mp hT
  obtain ⟨hp₀, hi₀⟩ := isSylowTwoOf_top_iff'.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hp.toSylow hi) (hp₀.toSylow hi₀)
  exact ⟨g, congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg⟩

theorem card_Msub_le_conj (g : Alt6) (Γ : Subgroup Alt6) :
    Nat.card (Msub Γ) ≤ Nat.card (Msub (Γ.map (MulAut.conj g).toMonoidHom)) := by
  refine Nat.card_le_card_of_injective
    (fun m => (⟨permAct 6 (g : Perm (Fin 6)) m.1, permAct_mem_Msub_map g m.2⟩ :
      Msub (Γ.map (MulAut.conj g).toMonoidHom))) ?_
  intro a b h
  exact Subtype.ext ((permAct 6 (g : Perm (Fin 6))).injective (congrArg Subtype.val h))

theorem map_conj_inv_map_conj (g : Alt6) (Γ : Subgroup Alt6) :
    (Γ.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = Γ := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩

theorem card_Msub_of_sylow {Γ' : Subgroup Alt6} (h : IsSylowTwoOf Γ' ⊤) :
    Nat.card (Msub Γ') = 4 := by
  obtain ⟨g, rfl⟩ := exists_conj_eq_of_sylow isSylowTwoOf_S6 h
  refine le_antisymm ?_ (card_Msub_S6 ▸ card_Msub_le_conj g S6)
  have h2 := card_Msub_le_conj g⁻¹ (S6.map (MulAut.conj g).toMonoidHom)
  rw [map_conj_inv_map_conj, card_Msub_S6] at h2
  exact h2

theorem card_coreMod6 : Nat.card (coreMod 6) = 32 := by
  have h1 : Nat.card (coreMod 6) = Nat.card {x : Fin 6 → ZMod 2 // ∑ i, x i = 0} :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun m => mem_coreMod))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_kerSub6 : Nat.card (kerSub 6) = 2 := by
  have h1 : Nat.card (kerSub 6) = Nat.card
      {x : Fin 6 → ZMod 2 // (∑ i, x i = 0) ∧ ∃ b : ZMod 2, ∀ i, x i = b} :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun m => mem_kerSub_iff))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exists_not_mem_Msub_S6 :
    ∃ (m : PermMod 6) (γ : Alt6), m ∈ Msub S6 ∧ permAct 6 (γ : Perm (Fin 6)) m ∉ Msub S6 := by
  let x0 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]
  let γ0 : Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5
  have hγ0 : γ0 ∈ alternatingGroup (Fin 6) := swap_mul_swap_mem (by decide) (by decide)
  refine ⟨Multiplicative.ofAdd x0, ⟨γ0, hγ0⟩, ?_, ?_⟩
  · rw [mem_Msub_S6]
    show PM x0
    decide +kernel
  · rw [mem_Msub_S6]
    show ¬ PM (fun i => x0 (γ0⁻¹ i))
    decide +kernel

theorem not_invariant_Msub {Γ' : Subgroup Alt6} (h : IsSylowTwoOf Γ' ⊤) :
    ¬ ∀ γ : Alt6, ∀ m ∈ Msub Γ', permAct 6 (γ : Perm (Fin 6)) m ∈ Msub Γ' := by
  obtain ⟨g, rfl⟩ := exists_conj_eq_of_sylow isSylowTwoOf_S6 h
  intro hinv
  obtain ⟨m, γ, hm, hγ⟩ := exists_not_mem_Msub_S6
  apply hγ
  have h1 := permAct_mem_Msub_map g hm
  have h2 := hinv (g * γ * g⁻¹) _ h1
  have h3 := permAct_mem_Msub_map g⁻¹ h2
  rw [map_conj_inv_map_conj] at h3
  have h4 : permAct 6 ((g⁻¹ : Alt6) : Perm (Fin 6))
      (permAct 6 (((g * γ * g⁻¹ : Alt6)) : Perm (Fin 6)) (permAct 6 (g : Perm (Fin 6)) m)) =
      permAct 6 (γ : Perm (Fin 6)) m := by
    simp [map_mul, map_inv, MulAut.mul_apply]
  rwa [h4] at h3

section Abstract

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : Alt6 →* ↥H}

abbrev D6 : Type := ↥(coreMod 6) ⧸ (kerSub 6).subgroupOf (coreMod 6)

@[expose] def WS (Sg : Subgroup (MulAut W)) (Z : Subgroup W) : Subgroup W :=
  ⨅ σ ∈ Sg, Z.comap (CFSG.Quasithin.H13.End1222.moveHom σ)

theorem mem_WS {Sg : Subgroup (MulAut W)} {w : W} :
    w ∈ WS Sg Z ↔ ∀ σ ∈ Sg, σ w * w⁻¹ ∈ Z := by
  simp only [WS, Subgroup.mem_iInf, Subgroup.mem_comap,
    CFSG.Quasithin.H13.End1222.moveHom_apply]

theorem WS_stable {Sg : Subgroup (MulAut W)} {a : MulAut W}
    (haS : ∀ σ ∈ Sg, a⁻¹ * σ * a ∈ Sg) (haZ : ∀ z ∈ Z, a z ∈ Z) {w : W} (hw : w ∈ WS Sg Z) :
    a w ∈ WS Sg Z := by
  rw [mem_WS] at hw ⊢
  intro σ hσ
  have h2 := haZ _ (hw _ (haS σ hσ))
  have h3 : σ (a w) * (a w)⁻¹ = a (((a⁻¹ * σ * a) w) * w⁻¹) := by
    simp [MulAut.mul_apply, map_mul, map_inv]
  rw [h3]
  exact h2

@[expose] noncomputable def Fix6 (Γ' : Subgroup Alt6) : Subgroup D6 :=
  ((Msub Γ').subgroupOf (coreMod 6)).map (QuotientGroup.mk' ((kerSub 6).subgroupOf (coreMod 6)))

theorem mem_Fix6 {Γ' : Subgroup Alt6} {q : D6} :
    q ∈ Fix6 Γ' ↔ ∃ m : ↥(coreMod 6), (m : PermMod 6) ∈ Msub Γ' ∧
      (QuotientGroup.mk m : D6) = q := by
  unfold Fix6
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.1 hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩

theorem mk_eq_mk_iff_D6 (a b : ↥(coreMod 6)) :
    (QuotientGroup.mk a : D6) = QuotientGroup.mk b ↔
      (b : PermMod 6) * (a : PermMod 6)⁻¹ ∈ kerSub 6 :=
  CFSG.Quasithin.H13.End1222.mk_eq_mk_iff (D := FFModel.altDn 6) a b

theorem realizes_unpack (hR : (FFModel.altDn 6).RealizesVia H ⊤ Z π) :
    ∃ β' : W →* D6, Function.Surjective β' ∧ (∀ w, β' w = 1 ↔ w ∈ Z) ∧
      ∀ (γ : Alt6) (w : W) (m : ↥(coreMod 6)), β' w = QuotientGroup.mk m →
        β' ((π γ : MulAut W) w) = QuotientGroup.mk
          ⟨permAct 6 (γ : Perm (Fin 6)) (m : PermMod 6), permAct_mem_coreMod _ m.2⟩ := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hR
  let β' : W →* D6 :=
    { toFun := fun w => β ⟨w, trivial⟩
      map_one' := β.map_one
      map_mul' := fun a b => β.map_mul ⟨a, trivial⟩ ⟨b, trivial⟩ }
  refine ⟨β', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    exact ⟨u.1, hu⟩
  · exact fun w => hβk ⟨w, trivial⟩
  · intro γ w m hm
    exact hβe γ ⟨w, trivial⟩ m trivial (hsec γ (m : PermMod 6) m.2) hm

theorem kerSub_le_coreMod : kerSub 6 ≤ coreMod 6 := fun _ h => (mem_kerSub_iff.1 h).1

theorem card_D6 : Nat.card D6 = 16 := by
  have hN : Nat.card ((kerSub 6).subgroupOf (coreMod 6)) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe kerSub_le_coreMod).toEquiv).trans card_kerSub6
  have h := ((kerSub 6).subgroupOf (coreMod 6)).index_mul_card
  rw [hN, card_coreMod6] at h
  have : Nat.card D6 = ((kerSub 6).subgroupOf (coreMod 6)).index := rfl
  omega

theorem card_W_eq [Finite W] (hR : (FFModel.altDn 6).RealizesVia H ⊤ Z π) :
    Nat.card W = 16 * Nat.card Z := by
  obtain ⟨β', hβs, hβk, -⟩ := realizes_unpack hR
  have hker : β'.ker = Z := by
    ext w
    rw [MonoidHom.mem_ker, hβk]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup β'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β' hβs).toEquiv, card_D6,
    hker] at h
  exact h

theorem mem_WS_iff {Γ' : Subgroup Alt6} {Sg : Subgroup (MulAut W)}
    (hS1 : ∀ γ ∈ Γ', ((π γ : ↥H) : MulAut W) ∈ Sg)
    (hS2 : ∀ σ ∈ Sg, ∃ γ ∈ Γ', ((π γ : ↥H) : MulAut W) = σ) {β' : W →* D6}
    (hβk : ∀ w, β' w = 1 ↔ w ∈ Z)
    (hβe : ∀ (γ : Alt6) (w : W) (m : ↥(coreMod 6)), β' w = QuotientGroup.mk m →
        β' ((π γ : MulAut W) w) = QuotientGroup.mk
          ⟨permAct 6 (γ : Perm (Fin 6)) (m : PermMod 6), permAct_mem_coreMod _ m.2⟩)
    {w : W} : w ∈ WS Sg Z ↔ β' w ∈ Fix6 Γ' := by
  constructor
  · intro hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' w)
    refine mem_Fix6.2 ⟨m, ?_, hm⟩
    refine mem_Msub.2 ⟨m.2, fun γ hγ => ?_⟩
    have h1 : ((π γ : ↥H) : MulAut W) w * w⁻¹ ∈ Z := mem_WS.1 hw _ (hS1 γ hγ)
    have h2 : β' (((π γ : ↥H) : MulAut W) w) = β' w := by
      have := (hβk _).2 h1
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    have h3 := hβe γ w m hm.symm
    rw [h2, ← hm] at h3
    exact (mk_eq_mk_iff_D6 m _).1 h3
  · intro hw
    obtain ⟨m, hm, hmw⟩ := mem_Fix6.1 hw
    rw [mem_WS]
    intro σ hσ
    obtain ⟨γ, hγ, rfl⟩ := hS2 σ hσ
    rw [← hβk, map_mul, map_inv, mul_inv_eq_one, hβe γ w m hmw.symm, ← hmw]
    exact ((mk_eq_mk_iff_D6 m _).2 ((mem_Msub.1 hm).2 γ hγ)).symm

theorem index_Fix6 {Γ' : Subgroup Alt6} (h : IsSylowTwoOf Γ' ⊤) : (Fix6 Γ').index = 8 := by
  set N := (kerSub 6).subgroupOf (coreMod 6) with hN
  set M' := (Msub Γ').subgroupOf (coreMod 6) with hM'
  have hcomap : (Fix6 Γ').comap (QuotientGroup.mk' N) = M' := by
    unfold Fix6
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.2 (Subgroup.subgroupOf_mono _ (kerSub_le_Msub Γ'))
  have h1 : M'.index = (Fix6 Γ').index := by
    rw [← hcomap]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have h2 : M'.index * Nat.card M' = Nat.card (coreMod 6) := M'.index_mul_card
  have h3 : Nat.card M' = 4 := by
    rw [← card_Msub_of_sylow h]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Msub_le_coreMod Γ')).toEquiv
  rw [card_coreMod6, h3] at h2
  omega

theorem card_WS_eq [Finite W] (hR : (FFModel.altDn 6).RealizesVia H ⊤ Z π) {Γ' : Subgroup Alt6}
    (hΓ : IsSylowTwoOf Γ' ⊤) {Sg : Subgroup (MulAut W)}
    (hS1 : ∀ γ ∈ Γ', ((π γ : ↥H) : MulAut W) ∈ Sg)
    (hS2 : ∀ σ ∈ Sg, ∃ γ ∈ Γ', ((π γ : ↥H) : MulAut W) = σ) :
    Nat.card (WS Sg Z) = 2 * Nat.card Z := by
  obtain ⟨β', hβs, hβk, hβe⟩ := realizes_unpack hR
  have hWS : WS Sg Z = (Fix6 Γ').comap β' := by
    ext w
    exact mem_WS_iff hS1 hS2 hβk hβe
  have h1 : (WS Sg Z).index = 8 := by
    rw [hWS, Subgroup.index_comap_of_surjective _ hβs]
    exact index_Fix6 hΓ
  have h2 := (WS Sg Z).index_mul_card
  rw [h1, card_W_eq hR] at h2
  omega

theorem not_invariant_WS (hR : (FFModel.altDn 6).RealizesVia H ⊤ Z π) {Γ' : Subgroup Alt6}
    (hΓ : IsSylowTwoOf Γ' ⊤) {Sg : Subgroup (MulAut W)}
    (hS1 : ∀ γ ∈ Γ', ((π γ : ↥H) : MulAut W) ∈ Sg)
    (hS2 : ∀ σ ∈ Sg, ∃ γ ∈ Γ', ((π γ : ↥H) : MulAut W) = σ) :
    ¬ ∀ h ∈ H, ∀ w ∈ WS Sg Z, h w ∈ WS Sg Z := by
  intro hinv
  apply not_invariant_Msub hΓ
  intro γ m hm
  obtain ⟨β', hβs, hβk, hβe⟩ := realizes_unpack hR
  have hmc : m ∈ coreMod 6 := Msub_le_coreMod _ hm
  obtain ⟨w, hw⟩ := hβs (QuotientGroup.mk ⟨m, hmc⟩)
  have hwS : w ∈ WS Sg Z := (mem_WS_iff hS1 hS2 hβk hβe).2
    (by rw [hw]; exact mem_Fix6.2 ⟨⟨m, hmc⟩, hm, rfl⟩)
  have h1 := hinv _ (π γ).2 w hwS
  have h2 := (mem_WS_iff hS1 hS2 hβk hβe).1 h1
  rw [hβe γ w ⟨m, hmc⟩ hw] at h2
  obtain ⟨m'', hm'', hmm⟩ := mem_Fix6.1 h2
  have h3 := (mk_eq_mk_iff_D6 m'' _).1 hmm
  have h4 : permAct 6 (γ : Perm (Fin 6)) m =
      (permAct 6 (γ : Perm (Fin 6)) m * (m'' : PermMod 6)⁻¹) * m'' :=
    (inv_mul_cancel_right _ _).symm
  rw [h4]
  exact Subgroup.mul_mem _ (kerSub_le_Msub Γ' h3) hm''

theorem injective_of_realizes (hR : (FFModel.altDn 6).RealizesVia H ⊤ Z π) :
    Function.Injective π := by
  obtain ⟨β', hβs, hβk, hβe⟩ := realizes_unpack hR
  have : IsSimpleGroup Alt6 := alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact h
  · exfalso
    obtain ⟨m, γ, hm, hγ⟩ := exists_not_mem_Msub_S6
    have hmc : m ∈ coreMod 6 := Msub_le_coreMod _ hm
    obtain ⟨w, hw⟩ := hβs (QuotientGroup.mk ⟨m, hmc⟩)
    have hπ : π γ = 1 := by
      have : γ ∈ π.ker := by rw [h]; trivial
      exact this
    have h2 := hβe γ w ⟨m, hmc⟩ hw
    rw [hπ] at h2
    simp only [Subgroup.coe_one, MulAut.one_apply] at h2
    rw [hw] at h2
    have h3 := (mk_eq_mk_iff_D6 _ _).1 h2
    apply hγ
    have h4 : permAct 6 (γ : Perm (Fin 6)) m =
        (permAct 6 (γ : Perm (Fin 6)) m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
    rw [h4]
    exact Subgroup.mul_mem _ (kerSub_le_Msub _ h3) hm

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G] {K V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def imS (K V S : Subgroup G)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) : Subgroup (MulAut ↥V) :=
  (S.subgroupOf K).map (A4.actionOn V K hKV)

omit [Finite G] [IsMulCommutative ↥V] in
theorem mem_imS {S : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G)) {σ : MulAut ↥V} :
    σ ∈ imS K V S hKV ↔ ∃ s : ↥K, (s : G) ∈ S ∧ A4.actionOn V K hKV s = σ := by
  unfold imS
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨s, hs, h⟩ => ⟨s, Subgroup.mem_subgroupOf.1 hs, h⟩,
    fun ⟨s, hs, h⟩ => ⟨s, Subgroup.mem_subgroupOf.2 hs, h⟩⟩

@[expose] noncomputable def resAct (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    ↥K →* ↥(autOn K V) :=
  (A4.actionOn V K hKV).codRestrict (autOn K V) fun l => (A4.mem_autOn_iff hKV).mpr ⟨l, rfl⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem resAct_surjective (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (resAct hKV) := by
  rintro ⟨a, ha⟩
  obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hKV).mp ha
  exact ⟨l, rfl⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem imS_le_autOn {S : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    imS K V S hKV ≤ autOn K V := by
  intro σ hσ
  obtain ⟨s, -, rfl⟩ := (mem_imS hKV).1 hσ
  exact (A4.mem_autOn_iff hKV).2 ⟨s, rfl⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem exists_sylow_corr {S : Subgroup G} (hS : IsSylowTwoOf S K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {π : Alt6 →* ↥(autOn K V)}
    (hπ : Function.Injective π) (hπs : Function.Surjective π) :
    ∃ Γ' : Subgroup Alt6, IsSylowTwoOf Γ' ⊤ ∧
      (∀ γ ∈ Γ', ((π γ : ↥(autOn K V)) : MulAut ↥V) ∈ imS K V S hKV) ∧
      (∀ σ ∈ imS K V S hKV, ∃ γ ∈ Γ', ((π γ : ↥(autOn K V)) : MulAut ↥V) = σ) := by
  set Sg := imS K V S hKV with hSg
  have hSgH : Sg ≤ autOn K V := imS_le_autOn hKV
  set X : Subgroup ↥(autOn K V) := Sg.subgroupOf (autOn K V) with hX
  refine ⟨X.comap π, ?_, fun γ hγ => hγ, fun σ hσ => ?_⟩
  · rw [isSylowTwoOf_top_iff']
    constructor
    · have hS' : IsPGroup 2 ↥(S.subgroupOf K) :=
        hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      have hSg2 : IsPGroup 2 ↥Sg := hS'.map (A4.actionOn V K hKV)
      have hX2 : IsPGroup 2 ↥X := hSg2.of_equiv (Subgroup.subgroupOfEquivOfLe hSgH).symm
      refine hX2.of_injective ((π.comp (X.comap π).subtype).codRestrict X fun g => g.2) ?_
      intro a b h
      exact Subtype.ext (hπ (congrArg Subtype.val h))
    · rw [Subgroup.index_comap_of_surjective _ hπs]
      have h1 : X = (S.subgroupOf K).map (resAct hKV) := by
        ext ⟨a, ha⟩
        simp only [hX, Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · intro hmem
          obtain ⟨s, hs, h⟩ := (mem_imS hKV).1 hmem
          exact ⟨s, Subgroup.mem_subgroupOf.2 hs, Subtype.ext h⟩
        · rintro ⟨s, hs, h⟩
          exact (mem_imS hKV).2 ⟨s, Subgroup.mem_subgroupOf.1 hs, congrArg Subtype.val h⟩
      have h2 := Subgroup.index_map_dvd (S.subgroupOf K) (resAct_surjective hKV)
      rw [← h1] at h2
      exact fun h3 => hS.2.2 (h3.trans h2)
  · have hσH := hSgH hσ
    obtain ⟨γ, hγ⟩ := hπs ⟨σ, hσH⟩
    refine ⟨γ, ?_, congrArg Subtype.val hγ⟩
    show π γ ∈ X
    rw [hγ]
    exact hσ

omit [Finite G] [IsMulCommutative ↥V] in
theorem conj_inv_mul_mem_imS {T : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    {t : G} (ht : t ∈ T) {σ : MulAut ↥V} (hσ : σ ∈ imS K V (T ⊓ K) hKV) :
    (conjAct V ⟨t, hTV ht⟩)⁻¹ * σ * conjAct V ⟨t, hTV ht⟩ ∈ imS K V (T ⊓ K) hKV := by
  obtain ⟨s, hs, rfl⟩ := (mem_imS hKV).1 hσ
  have hsT := (Subgroup.mem_inf.1 hs).1
  have hK' : t⁻¹ * (s : G) * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (hTK (T.inv_mem ht)) s).1 s.2
    simpa using this
  refine (mem_imS hKV).2 ⟨⟨t⁻¹ * s * t, hK'⟩,
    Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hsT) ht, hK'⟩, ?_⟩
  have h1 : (conjAct V ⟨t, hTV ht⟩)⁻¹ = conjAct V ⟨t⁻¹, hTV (T.inv_mem ht)⟩ := by
    rw [← map_inv]
    rfl
  rw [h1]
  refine MulEquiv.ext fun v => Subtype.ext ?_
  show (t⁻¹ * s * t) * (v : G) * (t⁻¹ * s * t)⁻¹ =
    t⁻¹ * ((s : G) * (t * (v : G) * t⁻¹) * (s : G)⁻¹) * t⁻¹⁻¹
  group

omit [Finite G] [IsMulCommutative ↥V] in
theorem conj_mem_Z {T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {t : G} (ht : t ∈ T) {z : ↥V}
    (hz : z ∈ (Subgroup.centralizer (K : Set G)).subgroupOf V) :
    conjAct V ⟨t, hTV ht⟩ z ∈ (Subgroup.centralizer (K : Set G)).subgroupOf V := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz ⊢
  intro k hk
  have hk' : t⁻¹ * k * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (hTK (T.inv_mem ht)) k).1 hk
    simpa using this
  have h1 := hz _ hk'
  show k * (t * (z : G) * t⁻¹) = t * (z : G) * t⁻¹ * k
  calc k * (t * (z : G) * t⁻¹) = t * ((t⁻¹ * k * t) * (z : G)) * t⁻¹ := by group
    _ = t * ((z : G) * (t⁻¹ * k * t)) * t⁻¹ := by rw [h1]
    _ = t * (z : G) * t⁻¹ * k := by group

omit [IsMulCommutative ↥V] in
theorem relIndex_le_fifteen (hKV : K ≤ Subgroup.normalizer (V : Set G)) {C W : Subgroup G}
    (hCK : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k) (hCW : C ≤ W) (hWV : W ≤ V)
    (hW : Nat.card W = 2 * Nat.card C) (hV : Nat.card V = 16 * Nat.card C) :
    (K ⊓ Subgroup.normalizer (W : Set G)).relIndex K ≤ 15 := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let F : Set (Subgroup G) := {U | C ≤ U ∧ U ≤ V ∧ Nat.card U = 2 * Nat.card C}
  have : Finite F := inferInstance
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hWF : W ∈ F := ⟨hCW, hWV, hW⟩
  have hF : ∀ k ∈ K, ∀ U ∈ F, cjSub k U ∈ F := by
    intro k hk U hU
    obtain ⟨hCU, hUV, hUc⟩ := hU
    have hkV := hKV hk
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_cjSub]
      have hx' : k⁻¹ * x * k = x := by
        have := hCK x hx k hk
        calc k⁻¹ * x * k = k⁻¹ * (x * k) := by group
          _ = k⁻¹ * (k * x) := by rw [this]
          _ = x := by group
      rw [hx']
      exact hCU hx
    · rw [mem_cjSub] at hx
      have := (Subgroup.mem_normalizer_iff.1 hkV _).1 (hUV hx)
      simpa [mul_assoc] using this
    · rw [← hUc]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        (MulAut.conj k).injective
  have hdisj : ∀ U ∈ F, ∀ U' ∈ F, U ≠ U' → U ⊓ U' = C := by
    intro U hU U' hU' hne
    obtain ⟨hCU, hUV, hUc⟩ := hU
    obtain ⟨hCU', hU'V, hU'c⟩ := hU'
    have hCle : C ≤ U ⊓ U' := le_inf hCU hCU'
    obtain ⟨a, ha⟩ : Nat.card C ∣ Nat.card ↥(U ⊓ U') := Subgroup.card_dvd_of_le hCle
    have hdvd2 : Nat.card ↥(U ⊓ U') ∣ 2 * Nat.card C :=
      hUc ▸ Subgroup.card_dvd_of_le (inf_le_left : U ⊓ U' ≤ U)
    have ha2 : a ∣ 2 := by
      rw [ha, mul_comm 2] at hdvd2
      exact Nat.dvd_of_mul_dvd_mul_left hpos hdvd2
    have ha_le : a ≤ 2 := Nat.le_of_dvd (by norm_num) ha2
    have hnpos : 0 < Nat.card ↥(U ⊓ U') := Nat.card_pos
    interval_cases a
    · omega
    · exact (Subgroup.eq_of_le_of_card_ge hCle (by omega)).symm
    · exfalso
      apply hne
      have h1 : U ⊓ U' = U :=
        Subgroup.eq_of_le_of_card_ge (H := U ⊓ U') (K := U) inf_le_left (by omega)
      have h2 : U ⊓ U' = U' :=
        Subgroup.eq_of_le_of_card_ge (H := U ⊓ U') (K := U') inf_le_right (by omega)
      rw [← h1, h2]
  have hcard := card_family_le C V (hCW.trans hWV) F (2 * Nat.card C)
    (fun U hU => ⟨hU.1, hU.2.1⟩) (fun U hU => hU.2.2) hdisj
  have h2c : 2 * Nat.card C - Nat.card C = Nat.card C := by omega
  rw [h2c, hV] at hcard
  have h1 : (Nat.card F + 1) * Nat.card C ≤ 16 * Nat.card C := by
    calc (Nat.card F + 1) * Nat.card C = Nat.card F * Nat.card C + Nat.card C := by ring
      _ ≤ 16 * Nat.card C := hcard
  have h2 := Nat.le_of_mul_le_mul_right h1 hpos
  have h21 := relIndex_inf_normalizer_le K W F hWF hF
  omega

theorem not_isDiagramNontrivial_of_alt6 {T H M₀ : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hAN : AlternatingNatural (V := ↥V) (autOn K V) ⊤
      ((Subgroup.centralizer (K : Set G)).subgroupOf V) 6)
    (hiso : Nonempty (↥(E2.star M₀ H K) ≃* Alt6)) :
    ¬ E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)) := by
  obtain ⟨π, hR⟩ := hAN
  have hπs : Function.Surjective π := hR.1
  have hπ : Function.Injective π := injective_of_realizes hR
  have hTK' : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hmin.isSylow hKH hHK
  obtain ⟨Γ', hΓ, hS1, hS2⟩ := exists_sylow_corr hTK' hKV hπ hπs
  set Z : Subgroup ↥V := (Subgroup.centralizer (K : Set G)).subgroupOf V with hZ
  set Wt : Subgroup G := (WS (imS K V (T ⊓ K) hKV) Z).map V.subtype with hWt
  have hWtV : Wt ≤ V := Subgroup.map_subtype_le _
  have hTW : T ≤ Subgroup.normalizer (Wt : Set G) := by
    intro t ht
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨conjAct V ⟨t, hTV ht⟩ w, WS_stable
      (fun σ hσ => conj_inv_mul_mem_imS hKV hTK hTV ht hσ)
      (fun z hz => conj_mem_Z hTK hTV ht hz) hw, rfl⟩
  have hcen : Subgroup.center ↥(autOn K V) = ⊥ := by
    let e : Alt6 ≃* ↥(autOn K V) := MulEquiv.ofBijective π ⟨hπ, hπs⟩
    exact Lem8.center_eq_bot_of_mulEquiv e.symm (Lem8.center_alternatingGroup_eq_bot (by norm_num))
  have hJC : K ⊓ kerIn M₀ H ≤ Subgroup.centralizer (V : Set G) := by
    rintro n ⟨hnK, hnker⟩
    have hz := (mem_kerIn_iff_central hKH hHK hker ⟨n, hnK⟩).1 hnker
    have hcomm : ∀ k : ↥K, A4.actionOn V K hKV (⟨n, hnK⟩ * k * ⟨n, hnK⟩⁻¹ * k⁻¹) = 1 := by
      intro k
      rw [A4.actionOn_eq_one_iff]
      have h1 := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk k)
      have h2 := (mk_comm_iff (CFSG.pCore 2 ↥K) ⟨n, hnK⟩ k).1 h1.symm
      exact hO ((mem_pCore_iff_coe _).1 h2)
    have hmem : resAct hKV ⟨n, hnK⟩ ∈ Subgroup.center ↥(autOn K V) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨k, rfl⟩ := resAct_surjective hKV b
      have h3 : resAct hKV (⟨n, hnK⟩ * k * ⟨n, hnK⟩⁻¹ * k⁻¹) = 1 :=
        Subtype.ext (hcomm k)
      have h4 : (⟨n, hnK⟩ * k : ↥K) =
          (⟨n, hnK⟩ * k * ⟨n, hnK⟩⁻¹ * k⁻¹) * (k * ⟨n, hnK⟩) := by group
      calc resAct hKV k * resAct hKV ⟨n, hnK⟩ = resAct hKV (k * ⟨n, hnK⟩) := (map_mul _ _ _).symm
        _ = resAct hKV (⟨n, hnK⟩ * k * ⟨n, hnK⟩⁻¹ * k⁻¹) * resAct hKV (k * ⟨n, hnK⟩) := by
          rw [h3, one_mul]
        _ = resAct hKV (⟨n, hnK⟩ * k) := by rw [← map_mul, ← h4]
        _ = resAct hKV ⟨n, hnK⟩ * resAct hKV k := map_mul _ _ _
    rw [hcen, Subgroup.mem_bot] at hmem
    have h5 : A4.actionOn V K hKV ⟨n, hnK⟩ = 1 := congrArg Subtype.val hmem
    exact (A4.actionOn_eq_one_iff hKV _).1 h5
  have hJW : K ⊓ kerIn M₀ H ≤ Subgroup.normalizer (Wt : Set G) := by
    intro n hn
    have hnC := hJC hn
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    have hxV : x ∈ V := hWtV hx
    have h1 : n * x * n⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.1 hnC x hxV
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    rw [h1]
    exact hx
  have hKW : ¬ K ≤ Subgroup.normalizer (Wt : Set G) := by
    intro hK
    refine not_invariant_WS hR hΓ hS1 hS2 ?_
    intro h hh w hw
    obtain ⟨k, rfl⟩ := (A4.mem_autOn_iff hKV).1 hh
    have hmem : (k : G) * (w : G) * (k : G)⁻¹ ∈ Wt :=
      (Subgroup.mem_normalizer_iff.1 (hK k.2) _).1 ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hw'e⟩ := Subgroup.mem_map.1 hmem
    have h6 : A4.actionOn V K hKV k w = w' :=
      Subtype.ext (by rw [A4.actionOn_apply_coe]; exact hw'e.symm)
    rw [h6]
    exact hw'
  set C : Subgroup G := Z.map V.subtype with hC
  have hCZ : Nat.card C = Nat.card Z :=
    Nat.card_congr (Subgroup.equivMapOfInjective Z V.subtype V.subtype_injective).symm.toEquiv
  have hWtc : Nat.card Wt = 2 * Nat.card C := by
    have h1 : Nat.card Wt = Nat.card (WS (imS K V (T ⊓ K) hKV) Z) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ V.subtype V.subtype_injective).symm.toEquiv
    rw [h1, hCZ]
    exact card_WS_eq hR hΓ hS1 hS2
  have hVc : Nat.card V = 16 * Nat.card C := by
    rw [hCZ]
    exact card_W_eq hR
  have hCK : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k := by
    rintro _ ⟨z, hz, rfl⟩ k hk
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hz) k hk
  have hCW : C ≤ Wt := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, mem_WS.2 fun σ hσ => ?_, rfl⟩
    obtain ⟨s, -, rfl⟩ := (mem_imS hKV).1 hσ
    have h7 : A4.actionOn V K hKV s z = z := by
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hz) s s.2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    rw [h7, mul_inv_cancel]
    exact Z.one_mem
  have hidx := relIndex_le_fifteen hKV hCK hCW hWtV hWtc hVc
  exact not_isDiagramNontrivial_of_stable_subgroup hKH hHK hmin hTK hiso hTW hJW hKW
    (hidx.trans (by norm_num))

end GLevel

end CFSG.Quasithin.H13.Lem1227Eq
