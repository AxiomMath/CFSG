module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec6L26b
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

namespace S126KG

open Matrix

theorem inj_of_pf : ∀ x : Fin 6 → ZMod 2, pf x = 1 → ∀ w : Fin 4 → ZMod 2,
    alt4 x *ᵥ w = 0 → w = 0 := by decide +kernel

theorem gBlk_fix_eq_zero {x y : Fin 6 → ZMod 2} (hx : pf x = 1) (hy : pf y = 1)
    {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hγ : gBlk x y *ᵥ γ = γ) : γ = 0 := by
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have hl := congrArg (fun f => f ∘ Sum.inl) hγ
  have hr := congrArg (fun f => f ∘ Sum.inr) hγ
  simp only [gBlk, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at hl hr
  have h1 : alt4 y *ᵥ (γ ∘ Sum.inl) = 0 := by
    funext j
    have := congrFun hr j
    simp only [Pi.add_apply, one_mulVec] at this
    have h3 : ∀ s t : ZMod 2, s + t = t → s = 0 := by decide
    exact h3 _ _ this
  have hγ1 := inj_of_pf y hy _ h1
  have h4 : alt4 x *ᵥ (γ ∘ Sum.inr) = 0 := by
    funext j
    have := congrFun hl j
    simp only [Pi.add_apply, hγ1, mulVec_zero, Pi.zero_apply, zero_add] at this
    exact this
  have hγ2 := inj_of_pf x hx _ h4
  funext k
  cases k with
  | inl j => exact congrFun hγ1 j
  | inr j => exact congrFun hγ2 j

end S126KG

namespace S126Crd.Setup

open S126KG

variable {G : Type*} [Group G] [Finite G] {Z A B : Subgroup G} {v i : G} (h : Setup Z A B v i)
include h

omit [Finite G] in
theorem mem_Z_of_mem_inf {x : G} (hxA : x ∈ A) (hxB : x ∈ B) : x ∈ Z :=
  h.nondeg x hxB fun a ha => h.comm_A a ha x hxA

theorem rel_coord_eq (cA : Coords Z A) {w : G} {γ γ' : Fin 4 ⊕ Fin 4 → ZMod 2}
    (hw : h.Rel cA w γ) (hw' : h.Rel cA w γ') : γ = γ' := by
  obtain ⟨a, b, ha, hb, hc⟩ := hw
  obtain ⟨a', b', ha', hb', hc'⟩ := hw'
  have h1 : (b : G)⁻¹ * ((a : G)⁻¹ * a') * b' ∈ Z := by
    have := Z.mul_mem (Z.inv_mem hc) hc'
    convert this using 1
    group
  generalize hxdef : (a : G)⁻¹ * a' = x at h1
  have hxA : x ∈ A := by rw [← hxdef]; exact A.mul_mem (A.inv_mem a.2) a'.2
  have hxB : x ∈ B := by
    have e : x = b * ((b : G)⁻¹ * x * b') * (b' : G)⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem b.2 (h.Z_le_B h1)) (B.inv_mem b'.2)
  have hxZ := h.mem_Z_of_mem_inf hxA hxB
  have hbZ : (b : G)⁻¹ * b' ∈ Z := by
    have e : (b : G)⁻¹ * b' = ((b : G)⁻¹ * x * b') * ((b' : G)⁻¹ * x⁻¹ * b') := by group
    have hx' : (b' : G)⁻¹ * x⁻¹ * b' = x⁻¹ := by
      rw [mul_assoc, h.Z_comm_B (Z.inv_mem hxZ) b'.2, inv_mul_cancel_left]
    rw [e, hx']
    exact Z.mul_mem h1 (Z.inv_mem hxZ)
  have hva : cA.vec a = cA.vec a' := by
    have : cA.vec (a⁻¹ * a') = 0 := (cA.vec_eq_zero _).2 (by rw [← hxdef] at hxZ; exact hxZ)
    rw [cA.vec_mul, Coords.vec, Coords.vec, map_inv, toAdd_inv] at this
    exact (neg_add_eq_zero.1 this)
  have hvb : (h.coordsB cA).vec b = (h.coordsB cA).vec b' := by
    have : (h.coordsB cA).vec (b⁻¹ * b') = 0 := ((h.coordsB cA).vec_eq_zero _).2 hbZ
    rw [(h.coordsB cA).vec_mul, Coords.vec, Coords.vec, map_inv, toAdd_inv] at this
    exact (neg_add_eq_zero.1 this)
  funext k
  cases k with
  | inl j =>
    have e1 := congrFun ha j
    have e2 := congrFun ha' j
    simp only [Function.comp_apply] at e1 e2
    rw [← e1, ← e2, hva]
  | inr j =>
    have e1 := congrFun hb j
    have e2 := congrFun hb' j
    simp only [Function.comp_apply] at e1 e2
    rw [← e1, ← e2, hvb]

theorem fix_coords {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (hfix : (a * b)⁻¹ * ((v * i) * (a * b) * (v * i)⁻¹) ∈ Z) : a ∈ Z ∧ b ∈ Z := by
  obtain ⟨cA⟩ := exists_coords h.comm_A h.sq_A h.Z_le_A (by rw [h.card_A, h.card_Z])
  set γ : Fin 4 ⊕ Fin 4 → ZMod 2 := Sum.elim (cA.vec ⟨a, ha⟩) ((h.coordsB cA).vec ⟨b, hb⟩)
    with hγdef
  have hrel : h.Rel cA (a * b) γ := ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl, rfl, by simp⟩
  have hrel2 := h.rel_g cA hrel
  have hrel3 : h.Rel cA ((v * i) * (a * b) * (v * i)⁻¹) γ := by
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl, rfl, ?_⟩
    have := Z.inv_mem hfix
    convert this using 1
    group
  have hγ := h.rel_coord_eq cA hrel2 hrel3
  have h0 := gBlk_fix_eq_zero (h.pf_xs cA) (h.pf_ys cA) hγ
  refine ⟨(cA.vec_eq_zero ⟨a, ha⟩).1 ?_, ((h.coordsB cA).vec_eq_zero ⟨b, hb⟩).1 ?_⟩
  · have := congrArg (fun f => f ∘ Sum.inl) h0
    simpa [hγdef] using this
  · have := congrArg (fun f => f ∘ Sum.inr) h0
    simpa [hγdef] using this

end S126Crd.Setup

namespace S126L26

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_of_comm {S : Type*} [Group S] [Finite S] {A B : Subgroup S}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    hAB a a.2 b b.2
  let f := MonoidHom.noncommCoprod A.subtype B.subtype hc
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : S) * b = 1 := hab
    have hba : (a : S) = (b : S)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have ha : (a : S) ∈ A ⊓ B := ⟨a.2, by rw [hba]; exact B.inv_mem b.2⟩
    rw [hinf, Subgroup.mem_bot] at ha
    have hb : (b : S) = 1 := by rw [ha, one_mul] at hab'; exact hab'
    rw [Subgroup.mem_bot, Prod.ext_iff]
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  have hrange : f.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

omit [Finite G] in
theorem mem_sup_of_comm {S : Type*} [Group S] {A B : Subgroup S}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : S} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hle : A ≤ Subgroup.normalizer (B : Set S) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hAB a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have e := hAB a ha _ hb
      have : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [← e]
          _ = a * b * a⁻¹ := by group
      rw [this]
      exact hb
  have hx' : x ∈ ((A ⊔ B : Subgroup S) : Set S) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hle] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite G] in
theorem card_tildeOf_mul {V₁ X : Subgroup G} (hV₁ : Nat.card V₁ = 2) (hV₁X : V₁ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V₁ : Set G)) : Nat.card ↥(tildeOf V₁ X) * 2 = Nat.card X := by
  have h := relIndex_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (T := V₁) (H := X)
    le_rfl hV₁X hXN
  have hbot : secImg (Subgroup.normalizer (V₁ : Set G)) V₁ V₁ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
    exact Subgroup.mem_bot.mpr (secMk_eq_one_iff.mpr hx)
  rw [hbot, Subgroup.relIndex_bot_left] at h
  have e := Subgroup.relIndex_mul_card V₁ X
  rw [inf_eq_left.2 hV₁X, hV₁] at e
  change Nat.card ↥(secImg (Subgroup.normalizer (V₁ : Set G)) V₁ X) * 2 = Nat.card X
  rw [h]
  exact e

section Hyp

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem toTilde_mem_normalizer (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    toTilde h.H_normalizes_V₁ x ∈
      Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) : Set (SecQuot
        (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
  secMk_mem_normalizer_secImg (le_normalizer_conjClosure Vp H x.2)

@[expose] noncomputable def rhoU (h : HypF91 T V L V₁ Vp H) :
    ↥H →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
  (tildeOf V₁ (conjClosure Vp H)).normalizerMonoidHom.comp
    ((toTilde h.H_normalizes_V₁).codRestrict _ (toTilde_mem_normalizer h))

omit [Finite G] in
theorem rhoU_apply (h : HypF91 T V L V₁ Vp H) (x : ↥H)
    (w : ↥(tildeOf V₁ (conjClosure Vp H))) :
    ((rhoU h x w : ↥(tildeOf V₁ (conjClosure Vp H))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      toTilde h.H_normalizes_V₁ x * w * (toTilde h.H_normalizes_V₁ x)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

omit [Finite G] in
theorem quot_facts (h : HypF91 T V L V₁ Vp H) {v y : G} (hv : v ∈ V) (hy : y ∈ H)
    (hy5 : y ^ 5 ∈ pCoreOf 2 H) (hyQ : y ∉ pCoreOf 2 H)
    (hinv : v * y * v⁻¹ * y ∈ pCoreOf 2 H) :
    v * ((y ^ 2)⁻¹ * v * y ^ 2) * y ∈ pCoreOf 2 H ∧
      ¬ ∀ x ∈ V ⊔ conjSub (y ^ 2)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H := by
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hvH : v ∈ H := h.V_le_H hv
  let N : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H
  have : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr (le_normalizer_pCoreOf 2 H)
  have hmem : ∀ z : ↥H, ((z : ↥H ⧸ N) = 1) ↔ (z : G) ∈ pCoreOf 2 H := fun z =>
    (QuotientGroup.eq_one_iff z).trans Subgroup.mem_subgroupOf
  let a : ↥H := ⟨v, hvH⟩
  let b : ↥H := ⟨y, hy⟩
  set A : ↥H ⧸ N := (a : ↥H ⧸ N) with hA
  set B : ↥H ⧸ N := (b : ↥H ⧸ N) with hB
  have hA2 : A * A = 1 := by
    rw [hA, ← QuotientGroup.mk_mul, hmem]
    show v * v ∈ pCoreOf 2 H
    rw [← pow_two, isElemAbelian_pow_eq_one h.elemAbelian hv]
    exact (pCoreOf 2 H).one_mem
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have hAB : A * B * A⁻¹ = B⁻¹ := by
    have h1 : A * B * A⁻¹ * B = 1 := by
      rw [hA, hB, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hmem]
      exact hinv
    exact eq_inv_of_mul_eq_one_left h1
  have hB5 : B ^ 5 = 1 := by
    rw [hB, ← QuotientGroup.mk_pow, hmem]
    exact hy5
  have hY : ((a * ((b ^ 2)⁻¹ * a * b ^ 2) : ↥H) : ↥H ⧸ N) = B⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, ← hA, ← hB]
    have h0 : A * B⁻¹ * A⁻¹ = B := by
      calc A * B⁻¹ * A⁻¹ = (A * B * A⁻¹)⁻¹ := by group
        _ = B := by rw [hAB, inv_inv]
    have h1 : A * (B ^ 2)⁻¹ * A⁻¹ = B ^ 2 := by
      rw [← inv_pow, ← conj_pow, h0]
    calc A * ((B ^ 2)⁻¹ * A * B ^ 2) = A * (B ^ 2)⁻¹ * A⁻¹ * B ^ 2 := by
          rw [hAinv]; simp only [mul_assoc]
      _ = B⁻¹ := by
          rw [h1, ← pow_add, eq_inv_iff_mul_eq_one, ← pow_succ]
          exact hB5
  have hyG : ((a * ((b ^ 2)⁻¹ * a * b ^ 2) : ↥H) : G) = v * ((y ^ 2)⁻¹ * v * y ^ 2) := rfl
  refine ⟨?_, ?_⟩
  · have : ((a * ((b ^ 2)⁻¹ * a * b ^ 2) * b : ↥H) : ↥H ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, hY, ← hB, inv_mul_cancel]
    exact (hmem _).1 this
  · intro hall
    have hiI : (y ^ 2)⁻¹ * v * y ^ 2 ∈ V ⊔ conjSub (y ^ 2)⁻¹ V := by
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjSub]
      have e : (y ^ 2)⁻¹⁻¹ * ((y ^ 2)⁻¹ * v * y ^ 2) * (y ^ 2)⁻¹ = v := by group
      rw [e]
      exact hv
    obtain ⟨n, hn⟩ := hall _ ((V ⊔ conjSub (y ^ 2)⁻¹ V).mul_mem (Subgroup.mem_sup_left hv) hiI)
    rw [← hyG, ← SubgroupClass.coe_pow, ← hmem, QuotientGroup.mk_pow, hY, inv_pow,
      inv_eq_one] at hn
    have hcop : Nat.Coprime (2 ^ n) 5 := Nat.Coprime.pow_left n (by norm_num)
    have ho : orderOf B = 1 :=
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) hcop).eq_one_of_dvd
        (orderOf_dvd_of_pow_eq_one hB5)
    rw [orderOf_eq_one_iff, hB, hmem] at ho
    exact hyQ ho

theorem card_fix_eight (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    (hcard : Nat.card Vp = 32)
    (hC : Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G))
    {v : G} (hv : v ∈ V) (hvp : v ∉ Vp) {y : G} (hy : y ∈ H) (hy5 : y ^ 5 ∈ pCoreOf 2 H)
    (hyQ : y ∉ pCoreOf 2 H) (hinv : v * y * v⁻¹ * y ∈ pCoreOf 2 H) :
    Nat.card {w : ↥(tildeOf V₁ (conjClosure Vp H)) // rhoU h ⟨y, hy⟩ w = w} * 2 ^ 8 =
      Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) := by
  obtain ⟨hu, hI⟩ := quot_facts h hv hy hy5 hyQ hinv
  have hH := h.H_normalizes_V₁
  have hgH : y ^ 2 ∈ H := H.pow_mem hy 2
  have hF := h.F95_5 hidx hV hyp5 hgH hI
  have hS := setup h hidx hV hyp5 hcard hC hgH hI hv hvp
  have hab := h.isElemAbelian_tilde
  have hcomm : ∀ a ∈ tildeOf V₁ (conjClosure Vp H), ∀ b ∈ tildeOf V₁ (conjClosure Vp H),
      a * b = b * a := fun a ha b hb => isElemAbelian_comm hab ha hb
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub (y ^ 2)⁻¹ Vp ≤ conjClosure Vp H := HypF91.conjSub_inv_le_U hgH hVpU
  have hUIU : Vp ⊔ conjSub (y ^ 2)⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  have hCU : centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V) ≤
      conjClosure Vp H := centralizerMod_le_left _ _ _
  have hVpN : Vp ≤ Subgroup.normalizer (V₁ : Set G) := h.Vp_le_H.trans hH
  have hVpgN : conjSub (y ^ 2)⁻¹ Vp ≤ Subgroup.normalizer (V₁ : Set G) :=
    hVpgU.trans (hUH.trans hH)
  have hc1 : Nat.card ↥(tildeOf V₁ Vp) = 16 := by
    have := card_tildeOf_mul h.card_V₁ h.V₁_le_Vp hVpN
    rw [hcard] at this
    omega
  have hc2 : Nat.card ↥(tildeOf V₁ (conjSub (y ^ 2)⁻¹ Vp)) = 16 := by
    have := card_tildeOf_mul h.card_V₁ hS.Z_le_B hVpgN
    rw [card_conjSub, hcard] at this
    omega
  have hcI : Nat.card ↥(tildeOf V₁ (Vp ⊔ conjSub (y ^ 2)⁻¹ Vp)) = 256 := by
    rw [hF.tilde_UI_sup, card_sup_of_comm (A := tildeOf V₁ Vp)
      (B := tildeOf V₁ (conjSub (y ^ 2)⁻¹ Vp)) (fun a ha b hb => hcomm a (secImg_mono hVpU ha) b
      (secImg_mono hVpgU hb)) hF.tilde_Vp_inf, hc1, hc2]
  have hcU : Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) = 256 *
      Nat.card ↥(tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V))) := by
    rw [hF.tilde_UH_sup, card_sup_of_comm (A := tildeOf V₁ (Vp ⊔ conjSub (y ^ 2)⁻¹ Vp))
      (B := tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V)))
      (fun a ha b hb => hcomm a (secImg_mono hUIU ha) b (secImg_mono hCU hb)) hF.tilde_UH_inf,
      hcI]
  set u := v * ((y ^ 2)⁻¹ * v * y ^ 2) with hudef
  have huH : u ∈ H := H.mul_mem (h.V_le_H hv)
    (H.mul_mem (H.mul_mem (H.inv_mem hgH) (h.V_le_H hv)) hgH)
  have huI : u ∈ V ⊔ conjSub (y ^ 2)⁻¹ V := by
    refine (V ⊔ conjSub (y ^ 2)⁻¹ V).mul_mem (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right ?_)
    rw [mem_conjSub]
    have e : (y ^ 2)⁻¹⁻¹ * ((y ^ 2)⁻¹ * v * y ^ 2) * (y ^ 2)⁻¹ = v := by group
    rw [e]
    exact hv
  set t := toTilde hH ⟨y, hy⟩ with htdef
  set tu := toTilde hH ⟨u, huH⟩ with htudef
  set tq := toTilde hH ⟨u * y, H.mul_mem huH hy⟩ with htqdef
  have htt : t = tu⁻¹ * tq := by
    rw [htdef, htudef, htqdef, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp
  have htq : ∀ s ∈ tildeOf V₁ (conjClosure Vp H), tq * s = s * tq := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := (mem_tildeOf_iff hH hUH).mp hs
    exact h.toTilde_comm_Q hu hx
  have hfixC : ∀ s ∈ tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V)),
      t * s = s * t := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := (mem_tildeOf_iff hH (hCU.trans hUH)).mp hs
    have h1 : tu * toTilde hH c = toTilde hH c * tu := by
      rw [toTilde_comm_iff]
      have := V₁.inv_mem (hc.2.2 u huI)
      convert this using 1
      group
    have h2 := htq _ ((mem_tildeOf_iff hH hUH).mpr ⟨c, hCU hc, rfl⟩)
    rw [htt]
    exact ((show Commute tu (toTilde hH c) from h1).inv_left.mul_left
      (show Commute tq (toTilde hH c) from h2)).eq
  have key : ∀ s ∈ tildeOf V₁ (conjClosure Vp H), t * s * t⁻¹ = s →
      s ∈ tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V)) := by
    intro s hs hfix
    rw [hF.tilde_UH_sup] at hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := mem_sup_of_comm
      (A := tildeOf V₁ (Vp ⊔ conjSub (y ^ 2)⁻¹ Vp))
      (B := tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V)))
      (fun a ha b hb => hcomm a (secImg_mono hUIU ha) b (secImg_mono hCU hb)) hs
    have hfix₂ := hfixC s₂ hs₂
    have hfix₁ : t * s₁ * t⁻¹ = s₁ := by
      calc t * s₁ * t⁻¹ = t * (s₁ * s₂) * t⁻¹ * (t * s₂ * t⁻¹)⁻¹ := by group
        _ = s₁ * s₂ * s₂⁻¹ := by rw [hfix, hfix₂, mul_inv_cancel_right]
        _ = s₁ := by group
    rw [hF.tilde_UI_sup] at hs₁
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := mem_sup_of_comm (A := tildeOf V₁ Vp)
      (B := tildeOf V₁ (conjSub (y ^ 2)⁻¹ Vp))
      (fun a ha b hb => hcomm a (secImg_mono hVpU ha) b (secImg_mono hVpgU hb)) hs₁
    obtain ⟨a, haV, rfl⟩ := (mem_tildeOf_iff hH h.Vp_le_H).mp hr₁
    obtain ⟨b, hbV, rfl⟩ := (mem_tildeOf_iff hH (hVpgU.trans hUH)).mp hr₂
    have hwU : toTilde hH a * toTilde hH b ∈ tildeOf V₁ (conjClosure Vp H) :=
      Subgroup.mul_mem _ (secImg_mono hVpU hr₁) (secImg_mono hVpgU hr₂)
    have htu : tu = tq * t⁻¹ := by rw [htt]; group
    have hfixu : tu * (toTilde hH a * toTilde hH b) * tu⁻¹ = toTilde hH a * toTilde hH b := by
      have e1 : t⁻¹ * (toTilde hH a * toTilde hH b) * t = toTilde hH a * toTilde hH b := by
        calc t⁻¹ * (toTilde hH a * toTilde hH b) * t =
            t⁻¹ * (t * (toTilde hH a * toTilde hH b) * t⁻¹) * t := by rw [hfix₁]
          _ = _ := by group
      calc tu * (toTilde hH a * toTilde hH b) * tu⁻¹ =
          tq * (t⁻¹ * (toTilde hH a * toTilde hH b) * t) * tq⁻¹ := by rw [htu]; group
        _ = tq * (toTilde hH a * toTilde hH b) * tq⁻¹ := by rw [e1]
        _ = toTilde hH a * toTilde hH b := by rw [htq _ hwU, mul_inv_cancel_right]
    have hG : ((a : G) * b)⁻¹ * (u * (a * b) * u⁻¹) ∈ V₁ := by
      have e : toTilde hH ((a * b)⁻¹ * (⟨u, huH⟩ * (a * b) * ⟨u, huH⟩⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [← htudef, hfixu, inv_mul_cancel]
      exact (toTilde_eq_one_iff hH).mp e
    obtain ⟨ha1, hb1⟩ := hS.fix_coords haV hbV hG
    rw [(toTilde_eq_one_iff hH).mpr ha1, (toTilde_eq_one_iff hH).mpr hb1, one_mul, one_mul]
    exact hs₂
  have hfixset : ∀ w : ↥(tildeOf V₁ (conjClosure Vp H)), rhoU h ⟨y, hy⟩ w = w ↔
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
        tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V)) := by
    intro w
    constructor
    · intro hw
      refine key w w.2 ?_
      have := congrArg Subtype.val hw
      rw [rhoU_apply] at this
      exact this
    · intro hw
      apply Subtype.ext
      rw [rhoU_apply]
      show t * w * t⁻¹ = w
      rw [hfixC _ hw, mul_inv_cancel_right]
  have hcF : Nat.card {w : ↥(tildeOf V₁ (conjClosure Vp H)) // rhoU h ⟨y, hy⟩ w = w} =
      Nat.card ↥(tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub (y ^ 2)⁻¹ V))) :=
    Nat.card_congr
      { toFun := fun w => ⟨w.1.1, (hfixset w.1).1 w.2⟩
        invFun := fun c => ⟨⟨c.1, secImg_mono hCU c.2⟩, (hfixset _).2 c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcF, hcU]
  ring

end Hyp

end S126L26

end CFSG.Quasithin.H13
