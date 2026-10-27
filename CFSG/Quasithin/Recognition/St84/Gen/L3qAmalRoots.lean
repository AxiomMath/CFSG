module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabC
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA
import CFSG.GroupTheory.PermSylowTwo.Sym
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxM
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabB

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Fin257.L3
open CFSG.Quasithin.H13.F431.L3.P3
open CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem eq_V2_or_eq_V1_of_le_projUnitriangular {E : Subgroup (projectiveSL 3 F)}
    (hEU : E ≤ projUnitriangular 3 F) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = Nat.card F ^ 2) :
    E = (V2 : Subgroup (projectiveSL 3 F)) ∨
      E = (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨-, hexp⟩ := hE
  have hmem : ∀ g ∈ E, g ∈ (V1 : Subgroup (projectiveSL 3 F)) ∨
      g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
    intro g hg
    have hgU : g ∈ projUnitriangular 3 F := hEU hg
    have hsq : g * g = 1 := by
      have h2 := hexp g hg
      rwa [pow_two] at h2
    exact involution_mem_V1_or_V2 (F := F) ⟨g, hgU⟩ (Subtype.ext hsq)
  have hV1 : Nat.card (V1 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 :=
    CFSG.GH74.QTGen4.DSGen4.L34.card_V1
  have hV2 : Nat.card (V2 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 :=
    CFSG.GH74.QTGen4.DSGen4.L34.card_V2
  rcases le_or_le_of_forall_mem_or_mem (V1 : Subgroup (projectiveSL 3 F))
      (V2 : Subgroup (projectiveSL 3 F)) E hmem with hEV1 | hEV2
  · right
    exact Subgroup.eq_of_le_of_card_ge hEV1 (hV1.trans hcard.symm).le
  · left
    exact Subgroup.eq_of_le_of_card_ge hEV2 (hV2.trans hcard.symm).le

private def rootX : Subgroup (projectiveSL 3 F) where
  carrier := Set.range xP
  one_mem' := ⟨0, xP_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, xP_add a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (xP_inv a).symm⟩

private def rootY : Subgroup (projectiveSL 3 F) where
  carrier := Set.range yP
  one_mem' := ⟨0, yP_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, yP_add a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (yP_inv a).symm⟩

private def rootW : Subgroup (projectiveSL 3 F) where
  carrier := Set.range wP
  one_mem' := ⟨0, wP_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, wP_add a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (wP_inv a).symm⟩

private theorem rootX_mem (a : F) : xP a ∈ rootX (F := F) := ⟨a, rfl⟩

private theorem rootY_mem (a : F) : yP a ∈ rootY (F := F) := ⟨a, rfl⟩

private theorem rootW_mem (a : F) : wP a ∈ rootW (F := F) := ⟨a, rfl⟩

private theorem rootX_le_V1 : rootX (F := F) ≤ (V1 : Subgroup (projectiveSL 3 F)) := by
  rintro _ ⟨a, rfl⟩
  exact mem_V1.mpr ⟨a, 0, by rw [wP_zero, mul_one]⟩

private theorem rootY_le_V2 : rootY (F := F) ≤ (V2 : Subgroup (projectiveSL 3 F)) := by
  rintro _ ⟨b, rfl⟩
  exact mem_V2.mpr ⟨b, 0, by rw [wP_zero, mul_one]⟩

private theorem rootW_le_V1 : rootW (F := F) ≤ (V1 : Subgroup (projectiveSL 3 F)) := by
  rintro _ ⟨c, rfl⟩
  exact mem_V1.mpr ⟨0, c, by rw [xP_zero, one_mul]⟩

private theorem rootW_eq_Wg : rootW (F := F) = (Wg : Subgroup (projectiveSL 3 F)) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact mem_Wg.mpr ⟨c, rfl⟩
  · intro hx
    obtain ⟨c, hc⟩ := mem_Wg.mp hx
    exact ⟨c, hc.symm⟩

private theorem xP_injective {a b : F} (h : xP a = xP b) : a = b := by
  have h1 : xP (a + b) = 1 := by rw [xP_add, h, xP_mul_self]
  have h2 : a + b = 0 := (xP_eq_one_iff (a + b)).mp h1
  have h3 : a - b = 0 := by linear_combination h2 - CharTwo.add_self_eq_zero b
  exact sub_eq_zero.mp h3

private theorem yP_injective {a b : F} (h : yP a = yP b) : a = b := by
  have h1 : yP (a + b) = 1 := by rw [yP_add, h, yP_mul_self]
  have h2 : a + b = 0 := (yP_eq_one_iff (a + b)).mp h1
  have h3 : a - b = 0 := by linear_combination h2 - CharTwo.add_self_eq_zero b
  exact sub_eq_zero.mp h3

private theorem card_rootX : Nat.card (rootX (F := F)) = Nat.card F := by
  let e : F → rootX (F := F) := fun a => ⟨xP a, rootX_mem a⟩
  have he : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · rintro a b h
      exact xP_injective (congrArg Subtype.val h)
    · rintro ⟨x, ⟨a, rfl⟩⟩
      exact ⟨a, rfl⟩
  rw [← Nat.card_eq_of_bijective e he]

private theorem card_rootY : Nat.card (rootY (F := F)) = Nat.card F := by
  let e : F → rootY (F := F) := fun a => ⟨yP a, rootY_mem a⟩
  have he : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · rintro a b h
      exact yP_injective (congrArg Subtype.val h)
    · rintro ⟨x, ⟨a, rfl⟩⟩
      exact ⟨a, rfl⟩
  rw [← Nat.card_eq_of_bijective e he]

private noncomputable def v1Fst (v : V1 (F := F)) : F := Classical.choose (mem_V1.mp v.2)

private theorem v1Fst_spec (v : V1 (F := F)) :
    ∃ c : F, (v : projectiveSL 3 F) = xP (v1Fst v) * wP c :=
  Classical.choose_spec (mem_V1.mp v.2)

private noncomputable def v1Snd (v : V1 (F := F)) : F := Classical.choose (v1Fst_spec v)

private theorem v1_eq (v : V1 (F := F)) :
    (v : projectiveSL 3 F) = xP (v1Fst v) * wP (v1Snd v) :=
  Classical.choose_spec (v1Fst_spec v)

private theorem v1Fst_eq_of_eq {v : V1 (F := F)} {a c : F}
    (h : (v : projectiveSL 3 F) = xP a * wP c) : v1Fst v = a := by
  have h2 : xP (v1Fst v) * wP (v1Snd v) = xP a * wP c := (v1_eq v).symm.trans h
  exact (xP_mul_wP_inj h2).1

private theorem v1Fst_one : v1Fst (1 : V1 (F := F)) = 0 := by
  refine v1Fst_eq_of_eq (a := 0) (c := 0) ?_
  rw [xP_zero, wP_zero, mul_one]
  rfl

private theorem v1Fst_mul (v w : V1 (F := F)) : v1Fst (v * w) = v1Fst v + v1Fst w := by
  refine v1Fst_eq_of_eq (a := v1Fst v + v1Fst w) (c := v1Snd v + v1Snd w) ?_
  calc ((v * w : V1) : projectiveSL 3 F) = (v : projectiveSL 3 F) * (w : projectiveSL 3 F) := rfl
    _ = (xP (v1Fst v) * wP (v1Snd v)) * (xP (v1Fst w) * wP (v1Snd w)) := by
        rw [v1_eq v, v1_eq w]
    _ = xP (v1Fst v + v1Fst w) * wP (v1Snd v + v1Snd w) :=
        V1_mul (v1Fst v) (v1Snd v) (v1Fst w) (v1Snd w)

private noncomputable def piX : V1 (F := F) →* Multiplicative F where
  toFun v := Multiplicative.ofAdd (v1Fst v)
  map_one' := by rw [v1Fst_one]; rfl
  map_mul' v w := by rw [v1Fst_mul]; rfl

private theorem piX_eq_one_iff (v : V1 (F := F)) :
    piX v = 1 ↔ (v : projectiveSL 3 F) ∈ (Wg : Subgroup (projectiveSL 3 F)) := by
  constructor
  · intro h
    have h' : Multiplicative.ofAdd (v1Fst v) = (1 : Multiplicative F) := by
      simpa [piX] using h
    have hfst : v1Fst v = 0 := Multiplicative.ofAdd.injective (by simpa using h')
    refine mem_Wg.mpr ⟨v1Snd v, ?_⟩
    rw [v1_eq v, hfst, xP_zero, one_mul]
  · rintro ⟨c, hc⟩
    have hfst : v1Fst v = 0 := by
      refine v1Fst_eq_of_eq (a := 0) (c := c) ?_
      rw [xP_zero, one_mul]
      exact hc
    simp [piX, hfst]

private noncomputable def v2Fst (v : V2 (F := F)) : F := Classical.choose (mem_V2.mp v.2)

private theorem v2Fst_spec (v : V2 (F := F)) :
    ∃ c : F, (v : projectiveSL 3 F) = yP (v2Fst v) * wP c :=
  Classical.choose_spec (mem_V2.mp v.2)

private noncomputable def v2Snd (v : V2 (F := F)) : F := Classical.choose (v2Fst_spec v)

private theorem v2_eq (v : V2 (F := F)) :
    (v : projectiveSL 3 F) = yP (v2Fst v) * wP (v2Snd v) :=
  Classical.choose_spec (v2Fst_spec v)

private theorem v2Fst_eq_of_eq {v : V2 (F := F)} {a c : F}
    (h : (v : projectiveSL 3 F) = yP a * wP c) : v2Fst v = a := by
  have h2 : yP (v2Fst v) * wP (v2Snd v) = yP a * wP c := (v2_eq v).symm.trans h
  exact (yP_mul_wP_inj h2).1

private theorem v2Fst_one : v2Fst (1 : V2 (F := F)) = 0 := by
  refine v2Fst_eq_of_eq (a := 0) (c := 0) ?_
  rw [yP_zero, wP_zero, mul_one]
  rfl

private theorem v2Fst_mul (v w : V2 (F := F)) : v2Fst (v * w) = v2Fst v + v2Fst w := by
  refine v2Fst_eq_of_eq (a := v2Fst v + v2Fst w) (c := v2Snd v + v2Snd w) ?_
  calc ((v * w : V2) : projectiveSL 3 F) = (v : projectiveSL 3 F) * (w : projectiveSL 3 F) := rfl
    _ = (yP (v2Fst v) * wP (v2Snd v)) * (yP (v2Fst w) * wP (v2Snd w)) := by
        rw [v2_eq v, v2_eq w]
    _ = yP (v2Fst v + v2Fst w) * wP (v2Snd v + v2Snd w) :=
        V2_mul (v2Fst v) (v2Snd v) (v2Fst w) (v2Snd w)

private noncomputable def piY : V2 (F := F) →* Multiplicative F where
  toFun v := Multiplicative.ofAdd (v2Fst v)
  map_one' := by rw [v2Fst_one]; rfl
  map_mul' v w := by rw [v2Fst_mul]; rfl

private theorem piY_eq_one_iff (v : V2 (F := F)) :
    piY v = 1 ↔ (v : projectiveSL 3 F) ∈ (Wg : Subgroup (projectiveSL 3 F)) := by
  constructor
  · intro h
    have h' : Multiplicative.ofAdd (v2Fst v) = (1 : Multiplicative F) := by
      simpa [piY] using h
    have hfst : v2Fst v = 0 := Multiplicative.ofAdd.injective (by simpa using h')
    refine mem_Wg.mpr ⟨v2Snd v, ?_⟩
    rw [v2_eq v, hfst, yP_zero, one_mul]
  · rintro ⟨c, hc⟩
    have hfst : v2Fst v = 0 := by
      refine v2Fst_eq_of_eq (a := 0) (c := c) ?_
      rw [yP_zero, one_mul]
      exact hc
    simp [piY, hfst]

private theorem eq_rootX_of_complement (V : Subgroup (projectiveSL 3 F))
    (hVle : V ≤ (V1 : Subgroup (projectiveSL 3 F)))
    (hcard : Nat.card V = Nat.card F)
    (hdisj : V ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥)
    (hP : projectiveSL 3 F) (lam : F)
    (hPx : ∀ a, hP * xP a * hP⁻¹ = xP a)
    (hPw : ∀ c, hP * wP c * hP⁻¹ = wP (lam * c))
    (hlam : lam ≠ 1) (hVinv : ∀ v ∈ V, hP * v * hP⁻¹ ∈ V) :
    V = rootX (F := F) := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  let pV : V →* Multiplicative F := (piX (F := F)).comp (Subgroup.inclusion hVle)
  have hpV_one : ∀ v : V, pV v = 1 ↔ v = 1 := by
    intro v
    constructor
    · intro h
      have hW : ((Subgroup.inclusion hVle v : V1 (F := F)) :
          projectiveSL 3 F) ∈ (Wg : Subgroup (projectiveSL 3 F)) :=
        (piX_eq_one_iff _).mp h
      have hmem : (v : projectiveSL 3 F) ∈ V ⊓ (Wg : Subgroup (projectiveSL 3 F)) :=
        ⟨v.2, hW⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro h
      subst h
      simp [pV]
  have hinj : Function.Injective pV := by
    intro v w h
    have h1 : pV (v * w⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp ((hpV_one (v * w⁻¹)).mp h1)
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Multiplicative F) := Fintype.ofFinite (Multiplicative F)
  have hcard' : Nat.card V = Nat.card (Multiplicative F) := by
    rw [show Nat.card (Multiplicative F) = Nat.card F from rfl]
    exact hcard
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card V = Fintype.card (Multiplicative F) := by
    simpa [Nat.card_eq_fintype_card] using hcard'
  let e : V ≃ Multiplicative F := Fintype.equivOfCardEq hcardF
  have hsurj : Function.Surjective pV :=
    (Finite.injective_iff_surjective_of_equiv e).mp hinj
  have hex : ∀ a : F, ∃ c : F, xP a * wP c ∈ V := by
    intro a
    let v : V := (hsurj (Multiplicative.ofAdd a)).choose
    have hv : pV v = Multiplicative.ofAdd a := (hsurj (Multiplicative.ofAdd a)).choose_spec
    have hfst : v1Fst (Subgroup.inclusion hVle v) = a := by
      have h' : Multiplicative.ofAdd (v1Fst (Subgroup.inclusion hVle v)) =
          Multiplicative.ofAdd a := by simpa [pV, piX] using hv
      exact Multiplicative.ofAdd.injective h'
    refine ⟨v1Snd (Subgroup.inclusion hVle v), ?_⟩
    have hv_eq := v1_eq (Subgroup.inclusion hVle v)
    have hval : (v : projectiveSL 3 F) = xP a * wP (v1Snd (Subgroup.inclusion hVle v)) := by
      simpa [hfst] using hv_eq
    exact hval ▸ v.2
  let φ : F → F := fun a => Classical.choose (hex a)
  have hφmem : ∀ a : F, xP a * wP (φ a) ∈ V := fun a => Classical.choose_spec (hex a)
  have hsame : ∀ (a c c' : F), xP a * wP c ∈ V → xP a * wP c' ∈ V → c = c' := by
    intro a c c' hc hc'
    have hmul : (xP a * wP c) * (xP a * wP c')⁻¹ ∈ V := V.mul_mem hc (V.inv_mem hc')
    have hinv : (xP a * wP c')⁻¹ = xP a * wP c' := by
      rw [mul_inv_rev, wP_inv, xP_inv, wP_mul_xP]
    have hval : (xP a * wP c) * (xP a * wP c')⁻¹ = wP (c + c') := by
      rw [hinv, V1_mul, CharTwo.add_self_eq_zero, xP_zero, one_mul]
    have hmemW : wP (c + c') ∈ V ⊓ (Wg : Subgroup (projectiveSL 3 F)) :=
      ⟨hval ▸ hmul, mem_Wg.mpr ⟨c + c', rfl⟩⟩
    have hbot : wP (c + c') = 1 := by
      rw [hdisj, Subgroup.mem_bot] at hmemW
      exact hmemW
    have hsum : c + c' = 0 := (wP_eq_one_iff _).mp hbot
    have hcc : c - c' = 0 := by linear_combination hsum - CharTwo.add_self_eq_zero c'
    exact sub_eq_zero.mp hcc
  have hzero : ∀ a : F, φ a = 0 := by
    intro a
    have hconj_mem : hP * (xP a * wP (φ a)) * hP⁻¹ ∈ V := hVinv _ (hφmem a)
    have hconj_val : hP * (xP a * wP (φ a)) * hP⁻¹ = xP a * wP (lam * φ a) := by
      calc hP * (xP a * wP (φ a)) * hP⁻¹ =
          (hP * xP a * hP⁻¹) * (hP * wP (φ a) * hP⁻¹) := by group
        _ = xP a * wP (lam * φ a) := by rw [hPx, hPw]
    have hsame_eq : lam * φ a = φ a :=
      hsame a (lam * φ a) (φ a) (hconj_val ▸ hconj_mem) (hφmem a)
    have hfac : (lam - 1) * φ a = 0 := by linear_combination hsame_eq
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hlam)
  have hXle : rootX (F := F) ≤ V := by
    rintro _ ⟨a, rfl⟩
    have hmem := hφmem a
    rwa [hzero a, wP_zero, mul_one] at hmem
  exact (Subgroup.eq_of_le_of_card_ge hXle (by rw [hcard, card_rootX])).symm

private theorem eq_rootY_of_complement (V : Subgroup (projectiveSL 3 F))
    (hVle : V ≤ (V2 : Subgroup (projectiveSL 3 F)))
    (hcard : Nat.card V = Nat.card F)
    (hdisj : V ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥)
    (hP : projectiveSL 3 F) (lam : F)
    (hPy : ∀ b, hP * yP b * hP⁻¹ = yP b)
    (hPw : ∀ c, hP * wP c * hP⁻¹ = wP (lam * c))
    (hlam : lam ≠ 1) (hVinv : ∀ v ∈ V, hP * v * hP⁻¹ ∈ V) :
    V = rootY (F := F) := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  let pV : V →* Multiplicative F := (piY (F := F)).comp (Subgroup.inclusion hVle)
  have hpV_one : ∀ v : V, pV v = 1 ↔ v = 1 := by
    intro v
    constructor
    · intro h
      have hW : ((Subgroup.inclusion hVle v : V2 (F := F)) :
          projectiveSL 3 F) ∈ (Wg : Subgroup (projectiveSL 3 F)) :=
        (piY_eq_one_iff _).mp h
      have hmem : (v : projectiveSL 3 F) ∈ V ⊓ (Wg : Subgroup (projectiveSL 3 F)) :=
        ⟨v.2, hW⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro h
      subst h
      simp [pV]
  have hinj : Function.Injective pV := by
    intro v w h
    have h1 : pV (v * w⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp ((hpV_one (v * w⁻¹)).mp h1)
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Multiplicative F) := Fintype.ofFinite (Multiplicative F)
  have hcard' : Nat.card V = Nat.card (Multiplicative F) := by
    rw [show Nat.card (Multiplicative F) = Nat.card F from rfl]
    exact hcard
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card V = Fintype.card (Multiplicative F) := by
    simpa [Nat.card_eq_fintype_card] using hcard'
  let e : V ≃ Multiplicative F := Fintype.equivOfCardEq hcardF
  have hsurj : Function.Surjective pV :=
    (Finite.injective_iff_surjective_of_equiv e).mp hinj
  have hex : ∀ a : F, ∃ c : F, yP a * wP c ∈ V := by
    intro a
    let v : V := (hsurj (Multiplicative.ofAdd a)).choose
    have hv : pV v = Multiplicative.ofAdd a := (hsurj (Multiplicative.ofAdd a)).choose_spec
    have hfst : v2Fst (Subgroup.inclusion hVle v) = a := by
      have h' : Multiplicative.ofAdd (v2Fst (Subgroup.inclusion hVle v)) =
          Multiplicative.ofAdd a := by simpa [pV, piY] using hv
      exact Multiplicative.ofAdd.injective h'
    refine ⟨v2Snd (Subgroup.inclusion hVle v), ?_⟩
    have hv_eq := v2_eq (Subgroup.inclusion hVle v)
    have hval : (v : projectiveSL 3 F) = yP a * wP (v2Snd (Subgroup.inclusion hVle v)) := by
      simpa [hfst] using hv_eq
    exact hval ▸ v.2
  let φ : F → F := fun a => Classical.choose (hex a)
  have hφmem : ∀ a : F, yP a * wP (φ a) ∈ V := fun a => Classical.choose_spec (hex a)
  have hsame : ∀ (a c c' : F), yP a * wP c ∈ V → yP a * wP c' ∈ V → c = c' := by
    intro a c c' hc hc'
    have hmul : (yP a * wP c) * (yP a * wP c')⁻¹ ∈ V := V.mul_mem hc (V.inv_mem hc')
    have hinv : (yP a * wP c')⁻¹ = yP a * wP c' := by
      rw [mul_inv_rev, wP_inv, yP_inv, wP_mul_yP]
    have hval : (yP a * wP c) * (yP a * wP c')⁻¹ = wP (c + c') := by
      rw [hinv, V2_mul, CharTwo.add_self_eq_zero, yP_zero, one_mul]
    have hmemW : wP (c + c') ∈ V ⊓ (Wg : Subgroup (projectiveSL 3 F)) :=
      ⟨hval ▸ hmul, mem_Wg.mpr ⟨c + c', rfl⟩⟩
    have hbot : wP (c + c') = 1 := by
      rw [hdisj, Subgroup.mem_bot] at hmemW
      exact hmemW
    have hsum : c + c' = 0 := (wP_eq_one_iff _).mp hbot
    have hcc : c - c' = 0 := by linear_combination hsum - CharTwo.add_self_eq_zero c'
    exact sub_eq_zero.mp hcc
  have hzero : ∀ a : F, φ a = 0 := by
    intro a
    have hconj_mem : hP * (yP a * wP (φ a)) * hP⁻¹ ∈ V := hVinv _ (hφmem a)
    have hconj_val : hP * (yP a * wP (φ a)) * hP⁻¹ = yP a * wP (lam * φ a) := by
      calc hP * (yP a * wP (φ a)) * hP⁻¹ =
          (hP * yP a * hP⁻¹) * (hP * wP (φ a) * hP⁻¹) := by group
        _ = yP a * wP (lam * φ a) := by rw [hPy, hPw]
    have hsame_eq : lam * φ a = φ a :=
      hsame a (lam * φ a) (φ a) (hconj_val ▸ hconj_mem) (hφmem a)
    have hfac : (lam - 1) * φ a = 0 := by linear_combination hsame_eq
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hlam)
  have hXle : rootY (F := F) ≤ V := by
    rintro _ ⟨a, rfl⟩
    have hmem := hφmem a
    rwa [hzero a, wP_zero, mul_one] at hmem
  exact (Subgroup.eq_of_le_of_card_ge hXle (by rw [hcard, card_rootY])).symm

private theorem exists_unit_cube_ne_one (hq : 8 ≤ Nat.card F) :
    ∃ t : Fˣ, (t : F) ^ 3 ≠ 1 := by
  by_contra h
  push Not at h
  let p : Polynomial F := Polynomial.X ^ 3 - 1
  have hdeg : p.natDegree = 3 := by
    simpa [p] using (Polynomial.natDegree_X_pow_sub_C (n := 3) (r := (1 : F)))
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.natDegree_zero] at hdeg
    omega
  haveI : DecidableEq F := Classical.decEq F
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  let S : Finset F := Finset.univ.image (fun t : Fˣ => (t : F))
  have hSsub : S.val ⊆ p.roots := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image
      (fun t : Fˣ => (t : F)) from hx)
    rw [Polynomial.mem_roots hp0]
    change Polynomial.eval (t : F) p = 0
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    rw [h t]
    ring
  have hcardS : S.card = Nat.card Fˣ := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  have hupper : S.card ≤ 3 := by
    have := Polynomial.card_le_degree_of_subset_roots hSsub
    omega
  have hlower : 7 ≤ Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  omega

private theorem exists_addEquiv_of_root_maps (B S : Subgroup (projectiveSL 3 F))
    (hSB : S ≤ B) (f : F → projectiveSL 3 F)
    (hf_zero : f 0 = 1) (hf_add : ∀ a b, f (a + b) = f a * f b)
    (hf_inj : Function.Injective f)
    (hS : ∀ x, x ∈ S ↔ ∃ a, f a = x)
    (τ : MulAut ↥B) (hτ : (S.subgroupOf B).map τ.toMonoidHom = S.subgroupOf B) :
    ∃ l : F ≃+ F, ∀ a : F,
      (τ ⟨f a, hSB ((hS (f a)).mpr ⟨a, rfl⟩)⟩ : projectiveSL 3 F) = f (l a) := by
  let elt : F → S.subgroupOf B := fun a =>
    ⟨⟨f a, hSB ((hS (f a)).mpr ⟨a, rfl⟩)⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact (hS (f a)).mpr ⟨a, rfl⟩⟩
  have elt_add : ∀ a b, elt (a + b) = elt a * elt b := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    simp [elt, hf_add]
  have hex : ∀ a, ∃ b, (τ (elt a) : projectiveSL 3 F) = f b := by
    intro a
    let y : ↥B := (elt a : ↥B)
    have hmem' : τ y ∈ (S.subgroupOf B).map τ.toMonoidHom :=
      Subgroup.mem_map_of_mem τ.toMonoidHom (show y ∈ S.subgroupOf B from (elt a).2)
    have hmem : τ y ∈ S.subgroupOf B := by
      have h := hmem'
      rwa [hτ] at h

    obtain ⟨b, hb⟩ := (hS _).mp (Subgroup.mem_subgroupOf.mp hmem)
    exact ⟨b, hb.symm⟩
  let l : F → F := fun a => Classical.choose (hex a)
  have hl : ∀ a, (τ (elt a) : projectiveSL 3 F) = f (l a) := fun a =>
    Classical.choose_spec (hex a)
  have hl_zero : l 0 = 0 := by
    have h1 : elt 0 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp [elt, hf_zero]
    have h2 : f (l 0) = f 0 := by
      rw [← hl 0, h1]
      simp [hf_zero]
    exact hf_inj h2
  have elt_add_B : ∀ a b, ((elt (a + b) : S.subgroupOf B) : ↥B) =
      (elt a : ↥B) * (elt b : ↥B) := by
    intro a b
    rw [elt_add]
    rfl
  have hl_add : ∀ a b, l (a + b) = l a + l b := by
    intro a b
    apply hf_inj
    rw [hf_add]
    calc f (l (a + b)) = (τ (elt (a + b)) : projectiveSL 3 F) := (hl (a + b)).symm
      _ = (τ ((elt a : ↥B) * (elt b : ↥B)) : projectiveSL 3 F) := by rw [elt_add_B]
      _ = (((τ (elt a) : ↥B) * (τ (elt b) : ↥B)) : projectiveSL 3 F) := by
          rw [map_mul]
          simp
      _ = f (l a) * f (l b) := by rw [hl a, hl b]
  let lHom : F →+ F :=
    { toFun := l, map_zero' := hl_zero, map_add' := hl_add }
  have hlHom_inj : Function.Injective lHom := by
    intro a b hab
    change l a = l b at hab
    have h1 : f (l a) = f (l b) := by rw [hab]
    have h2 : (τ (elt a) : projectiveSL 3 F) = (τ (elt b) : projectiveSL 3 F) := by
      rw [hl a, hl b, h1]
    have h3 : (elt a : ↥B) = (elt b : ↥B) := τ.injective (Subtype.ext h2)
    have h4 : f a = f b := congrArg (fun x : ↥B => (x : projectiveSL 3 F)) h3
    exact hf_inj h4
  have hlHom_bij : Function.Bijective lHom :=
    ⟨hlHom_inj, Finite.injective_iff_surjective.mp hlHom_inj⟩
  refine ⟨AddEquiv.ofBijective lHom hlHom_bij, ?_⟩
  intro a
  exact hl a

private theorem rootX_le_U : rootX (F := F) ≤ projUnitriangular 3 F :=
  rootX_le_V1.trans V1_le_U

private theorem rootY_le_U : rootY (F := F) ≤ projUnitriangular 3 F :=
  rootY_le_V2.trans V2_le_U

private theorem rootW_le_U : rootW (F := F) ≤ projUnitriangular 3 F :=
  rootW_le_V1.trans V1_le_U

private theorem conj_mem_rootX_of_mem_torus {h : projectiveSL 3 F}
    (hh : h ∈ torus3 F) {a : F} : h * xP a * h⁻¹ ∈ rootX (F := F) := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hh
  exact ⟨(t₁ : F) * (t₂ : F)⁻¹ * a, (dP_conj_xP t₁ t₂ a).symm⟩

private theorem conj_mem_rootY_of_mem_torus {h : projectiveSL 3 F}
    (hh : h ∈ torus3 F) {a : F} : h * yP a * h⁻¹ ∈ rootY (F := F) := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hh
  exact ⟨(t₁ : F) * t₂ * t₂ * a, (dP_conj_yP t₁ t₂ a).symm⟩

private theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (hg : g ∈ S) : S.map (MulAut.conj g).toMonoidHom = S :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hg)

private theorem map_subtype_injective {B : Subgroup (projectiveSL 3 F)}
    {S T : Subgroup ↥B} (h : S.map B.subtype = T.map B.subtype) : S = T := by
  ext x
  rw [← Subgroup.mem_map_iff_mem (f := B.subtype) B.subtype_injective (K := S) (x := x),
    ← Subgroup.mem_map_iff_mem (f := B.subtype) B.subtype_injective (K := T) (x := x)]
  exact Iff.of_eq (congrArg (fun U : Subgroup (projectiveSL 3 F) => (x : projectiveSL 3 F) ∈ U) h)

theorem exists_rootData_of_mulAut (hq : 8 ≤ Nat.card F)
    (σ : MulAut ↥(Ln F ⊓ Pt F))
    (hσ : ∀ b : ↥(Ln F ⊓ Pt F), (b : projectiveSL 3 F) ∈ pCoreOf 2 (Ln F) ↔
      ((σ b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) ∈ pCoreOf 2 (Ln F)) :
    ∃ u ∈ projUnitriangular 3 F, ∃ l m n : F ≃+ F,
      (∀ a b : F, n (a * b) = l a * m b) ∧
      (∀ (x : ↥(Ln F ⊓ Pt F)) (a : F), (x : projectiveSL 3 F) = xP a →
        ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = u * xP (l a) * u⁻¹) ∧
      (∀ (x : ↥(Ln F ⊓ Pt F)) (b : F), (x : projectiveSL 3 F) = yP b →
        ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = u * yP (m b) * u⁻¹) ∧
      (∀ (x : ↥(Ln F ⊓ Pt F)) (c : F), (x : projectiveSL 3 F) = wP c →
        ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = u * wP (n c) * u⁻¹) ∧
      ∀ x : ↥(Ln F ⊓ Pt F), (x : projectiveSL 3 F) ∈ torus3 F →
        u⁻¹ * ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) * u ∈ torus3 F := by
  let B : Subgroup (projectiveSL 3 F) := Ln F ⊓ Pt F
  let U : Subgroup (projectiveSL 3 F) := projUnitriangular 3 F
  let H : Subgroup (projectiveSL 3 F) := torus3 F
  let UB : Subgroup ↥B := U.subgroupOf B
  let V1B : Subgroup ↥B := (V1 : Subgroup (projectiveSL 3 F)).subgroupOf B
  let V2B : Subgroup ↥B := (V2 : Subgroup (projectiveSL 3 F)).subgroupOf B
  let HB : Subgroup ↥B := H.subgroupOf B
  have hB : B = Subgroup.normalizer (U : Set (projectiveSL 3 F)) := by
    dsimp [B, U]
    exact B0_eq_normalizer
  have hUB : U ≤ B := by rw [hB]; exact Subgroup.le_normalizer
  have hV1B : (V1 : Subgroup (projectiveSL 3 F)) ≤ B := V1_le_U.trans hUB
  have hV2B : (V2 : Subgroup (projectiveSL 3 F)) ≤ B := V2_le_U.trans hUB
  have hHleB : H ≤ B := fun x hx => torus_mem_B0 hx
  have hWgleB : (Wg : Subgroup (projectiveSL 3 F)) ≤ B := by
    rw [← rootW_eq_Wg]
    exact rootW_le_U.trans hUB
  haveI : Finite (projectiveSL 3 F) := inferInstance
  have hSylU : IsSylowTwoOf U B := by
    rw [hB]
    exact isSylowTwoOf_U_normalizer (F := F) (N :=
      Subgroup.normalizer (U : Set (projectiveSL 3 F))) Subgroup.le_normalizer
  have hUp : IsPGroup 2 UB :=
    hSylU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUB).symm
  have hUN : UB.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mpr (by rw [hB])
  haveI : UB.Normal := hUN
  have hF_le_U : (((UB.map σ.toMonoidHom).map B.subtype) : Subgroup (projectiveSL 3 F)) ≤ U := by
    have hFp : IsPGroup 2 (((UB.map σ.toMonoidHom).map B.subtype) :
        Subgroup (projectiveSL 3 F)) := (hUp.map σ.toMonoidHom).map B.subtype
    obtain ⟨g, hgB, hle⟩ := CFSG.GroupTheory.PermSylowTwo.exists_mem_conj_ge
      (G := projectiveSL 3 F) (A := B) (S := U)
      (F := ((UB.map σ.toMonoidHom).map B.subtype)) hSylU (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hFp
    have hconj : U.map (MulAut.conj g).toMonoidHom = U :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (by
        rw [hB] at hgB
        exact hgB)
    rwa [hconj] at hle
  have hσU_le : UB.map σ.toMonoidHom ≤ UB := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hF_le_U (Subgroup.mem_map_of_mem B.subtype hy))
  have hσU : UB.map σ.toMonoidHom = UB :=
    Subgroup.eq_of_le_of_card_ge hσU_le (by
      rw [Subgroup.card_map_of_injective σ.injective])
  have hcoreV2 : pCoreOf 2 (Ln F) = (V2 : Subgroup (projectiveSL 3 F)) := by
    dsimp [Ln]
    exact core_V2
  have hσV2 : ∀ b : ↥B, (b : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) ↔
      ((σ b : ↥B) : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
    intro b
    rw [← hcoreV2]
    exact hσ b
  have hV2B_le : V2B.map σ.toMonoidHom ≤ V2B := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mpr ((hσV2 x).mp (Subgroup.mem_subgroupOf.mp hx))
  have hV2B_map : V2B.map σ.toMonoidHom = V2B :=
    Subgroup.eq_of_le_of_card_ge hV2B_le (by
      rw [Subgroup.card_map_of_injective σ.injective])
  let EB : Subgroup ↥B := V1B.map σ.toMonoidHom
  let E : Subgroup (projectiveSL 3 F) := EB.map B.subtype
  have hEB_le_UB : EB ≤ UB := by
    rw [← hσU]
    exact Subgroup.map_mono (by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (V1_le_U (Subgroup.mem_subgroupOf.mp hx)))
  have hEU : E ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hEB_le_UB hy)
  have hEea : IsElemAbelian 2 E := by
    have h1 : IsElemAbelian 2 ((V1 : Subgroup (projectiveSL 3 F)).subgroupOf B) :=
      IsElemAbelian.subgroupOf (isElemAbelian_V1 (F := F)) B
    have h2 : IsElemAbelian 2 (V1B.map σ.toMonoidHom) :=
      IsElemAbelian.map h1 σ.toMonoidHom
    exact IsElemAbelian.map h2 B.subtype
  have hEcard : Nat.card E = Nat.card F ^ 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective σ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1B).toEquiv,
      CFSG.GH74.QTGen4.DSGen4.L34.card_V1]
  have hV1B_map : V1B.map σ.toMonoidHom = V1B := by
    rcases eq_V2_or_eq_V1_of_le_projUnitriangular hEU hEea hEcard with hE2 | hE1
    · exfalso
      have hEB_eq : EB = V2B := by
        ext x
        constructor
        · intro hx
          have hxP : (x : projectiveSL 3 F) ∈ E := Subgroup.mem_map_of_mem B.subtype hx
          rw [hE2] at hxP
          exact Subgroup.mem_subgroupOf.mpr hxP
        · intro hx
          have hxP : (x : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) :=
            Subgroup.mem_subgroupOf.mp hx
          have hxE : (x : projectiveSL 3 F) ∈ E := by rw [hE2]; exact hxP
          have hxE' : (x : projectiveSL 3 F) ∈ EB.map B.subtype := by simpa [E] using hxE
          exact (Subgroup.mem_map_iff_mem (f := B.subtype) B.subtype_injective (K := EB)
            (x := x)).mp hxE'
      have hV1B_eq_V2B : V1B = V2B := by
        have h1 : V1B.map σ.toMonoidHom = V2B := hEB_eq
        have hcomp : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id ↥B := by
          ext x
          simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
          change ((σ.symm (σ x) : ↥B) : projectiveSL 3 F) =
            ((x : ↥B) : projectiveSL 3 F)
          exact congrArg (fun z : ↥B => (z : projectiveSL 3 F)) (σ.symm_apply_apply x)
        have h2 : V2B.map σ.symm.toMonoidHom = V2B := by
          have h := congrArg (fun S : Subgroup ↥B => S.map σ.symm.toMonoidHom) hV2B_map
          rw [Subgroup.map_map] at h
          rw [hcomp, Subgroup.map_id] at h
          exact h.symm
        have h := congrArg (fun S : Subgroup ↥B => S.map σ.symm.toMonoidHom) h1
        rw [Subgroup.map_map, h2] at h
        simpa using h
      have hV1V2 : (V1 : Subgroup (projectiveSL 3 F)) = V2 := by
        have h := congrArg (fun S : Subgroup ↥B => S.map B.subtype) hV1B_eq_V2B
        rwa [Subgroup.map_subgroupOf_eq_of_le hV1B,
          Subgroup.map_subgroupOf_eq_of_le hV2B] at h
      exact V1_ne_V2 hV1V2
    · have hEB_eq : EB = V1B := by
        ext x
        constructor
        · intro hx
          have hxP : (x : projectiveSL 3 F) ∈ E := Subgroup.mem_map_of_mem B.subtype hx
          rw [hE1] at hxP
          exact Subgroup.mem_subgroupOf.mpr hxP
        · intro hx
          have hxP : (x : projectiveSL 3 F) ∈ (V1 : Subgroup (projectiveSL 3 F)) :=
            Subgroup.mem_subgroupOf.mp hx
          have hxE : (x : projectiveSL 3 F) ∈ E := by rw [hE1]; exact hxP
          have hxE' : (x : projectiveSL 3 F) ∈ EB.map B.subtype := by simpa [E] using hxE
          exact (Subgroup.mem_map_iff_mem (f := B.subtype) B.subtype_injective (K := EB)
            (x := x)).mp hxE'
      exact hEB_eq
  have hBN1 : B ≤ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
    rw [hB]
    exact normalizer_U_le_normalizer_V1
  have hBN2 : B ≤ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
    rw [hB]
    exact normalizer_U_le_normalizer_V2
  haveI : V1B.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV1B).mpr hBN1
  haveI : V2B.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV2B).mpr hBN2
  have hEZ : Disjoint UB HB := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxH
    apply Subtype.ext
    have : (x : projectiveSL 3 F) ∈ U ⊓ H :=
      ⟨Subgroup.mem_subgroupOf.mp hxU, Subgroup.mem_subgroupOf.mp hxH⟩
    rw [show U ⊓ H = ⊥ by
      dsimp [U, H]
      exact projUnitriangular_inf_torus3] at this
    exact Subgroup.mem_bot.mp this
  let Y : Subgroup ↥B := HB.map σ.toMonoidHom
  have hEY : Disjoint UB Y := by
    have h := congrArg (fun S : Subgroup ↥B => S.map σ.toMonoidHom) (disjoint_iff.mp hEZ)
    rw [Subgroup.map_inf _ _ _ σ.injective, hσU, Subgroup.map_bot] at h
    exact disjoint_iff.mpr h
  have htop1 : UB ⊔ HB = ⊤ := by
    have hBsup : B = U ⊔ H := by
      dsimp [B, U, H]
      rw [B0_eq_normalizer]
      exact normalizer_U_eq_sup_torus3
    rw [← Subgroup.subgroupOf_sup hUB hHleB, hBsup, Subgroup.subgroupOf_self]
  have htop2 : UB ⊔ Y = ⊤ := by
    have htopσ : (⊤ : Subgroup ↥B).map σ.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact σ.surjective
    have h := congrArg (fun S : Subgroup ↥B => S.map σ.toMonoidHom) htop1
    rw [Subgroup.map_sup, hσU, htopσ] at h
    simpa [Y] using h
  have hUB_solv : Group.IsSolvable ↥UB := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥UB := hUp.isNilpotent
    infer_instance
  have hHBcomm : IsMulCommutative ↥HB := IsMulCommutative.of_comm (fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    change (a : projectiveSL 3 F) * (b : projectiveSL 3 F) =
      (b : projectiveSL 3 F) * (a : projectiveSL 3 F)
    obtain ⟨t₁, t₂, ha⟩ := mem_torus3.mp (Subgroup.mem_subgroupOf.mp a.2)
    obtain ⟨s₁, s₂, hb⟩ := mem_torus3.mp (Subgroup.mem_subgroupOf.mp b.2)
    rw [ha, hb, ← map_mul, ← map_mul, dMat_mul, dMat_mul]
    congr 2 <;> rw [mul_comm])
  have hHB_solv : Group.IsSolvable ↥HB := by
    haveI : IsMulCommutative ↥HB := hHBcomm
    infer_instance
  have hHnormU : HB ≤ Subgroup.normalizer (UB : Set ↥B) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxN : (x : projectiveSL 3 F) ∈
        Subgroup.normalizer (U : Set (projectiveSL 3 F)) :=
      torus3_le_normalizer (Subgroup.mem_subgroupOf.mp hx)
    constructor
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hxN (y : projectiveSL 3 F)).mp
          (Subgroup.mem_subgroupOf.mp hy))
    · intro hy
      have hyU : ((x * y * x⁻¹ : ↥B) : projectiveSL 3 F) ∈ U :=
        Subgroup.mem_subgroupOf.mp hy
      have hconv : ((x * y * x⁻¹ : ↥B) : projectiveSL 3 F) =
          (x : projectiveSL 3 F) * (y : projectiveSL 3 F) * (x : projectiveSL 3 F)⁻¹ := rfl
      rw [hconv] at hyU
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hxN (y : projectiveSL 3 F)).mpr hyU)
  have hBsolv : Group.IsSolvable ↥B := by
    have hsup : HB ⊔ UB = ⊤ := by rw [sup_comm]; exact htop1
    have h := CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.isSolvable_sup_of_le_normalizer
      (T := UB) (D := HB) hHnormU hUB_solv hHB_solv
    rw [hsup] at h
    let e : ↥(⊤ : Subgroup ↥B) ≃* ↥B := Subgroup.topEquiv
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let π : Set Nat.Primes := {p | p.val ≠ 2}
  have hcardHB : Nat.card HB = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleB).toEquiv
  have hoddHB : Odd (Nat.card HB) := by rw [hcardHB]; exact torus3_odd
  have hcardY : Nat.card Y = Nat.card HB := Subgroup.card_map_of_injective σ.injective
  have hoddY : Odd (Nat.card Y) := by rw [hcardY]; exact hoddHB
  have hcompUBHB : UB.IsComplement' HB :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hEZ (by
      rw [← Subgroup.normal_mul, htop1]
      simp)
  have hcompUBY : UB.IsComplement' Y :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hEY (by
      rw [← Subgroup.normal_mul, htop2]
      simp)
  have hHallHB : IsHallSubgroup π HB := by
    refine isHallSubgroup_of π HB ?_ ?_
    · intro p hp
      have hpodd : Odd p.val := hoddHB.of_dvd_nat hp
      intro h2
      rw [h2] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    · intro p hp hpdvd
      rw [hcompUBHB.index_eq_card] at hpdvd
      obtain ⟨k, hk⟩ := hUp.exists_card_eq
      rw [hk] at hpdvd
      have hp2 : p.val = 2 := (Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow p.property hpdvd)
      exact hp hp2
  have hHallY : IsHallSubgroup π Y := by
    refine isHallSubgroup_of π Y ?_ ?_
    · intro p hp
      have hpodd : Odd p.val := hoddY.of_dvd_nat hp
      intro h2
      rw [h2] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    · intro p hp hpdvd
      rw [hcompUBY.index_eq_card] at hpdvd
      obtain ⟨k, hk⟩ := hUp.exists_card_eq
      rw [hk] at hpdvd
      have hp2 : p.val = 2 := (Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow p.property hpdvd)
      exact hp hp2
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable
    (G := ↥B) hBsolv hHallY hHallHB
  obtain ⟨⟨uE, yE⟩, huy⟩ := hcompUBY.2 g
  let uB : ↥B := (uE : ↥B)
  let yB : ↥B := (yE : ↥B)
  have huE : uB ∈ UB := by simpa [uB] using uE.2
  have hyY : yB ∈ Y := by simpa [yB] using yE.2
  have huy' : uB * yB = g := by simpa [uB, yB] using huy
  have hconj_mul : MulAut.conj g = MulAut.conj uB * MulAut.conj yB := by
    ext x
    rw [← huy']
    simp [MulAut.conj_apply]
  have hprod : (MulAut.conj uB * MulAut.conj yB).toMonoidHom =
      (MulAut.conj uB).toMonoidHom.comp (MulAut.conj yB).toMonoidHom := by
    ext x
    rfl
  have hmap : Y.map (MulAut.conj g).toMonoidHom =
      Y.map (MulAut.conj uB).toMonoidHom := by
    rw [hconj_mul, hprod, ← Subgroup.map_map, map_conj_eq_self_of_mem hyY]
  have hYconj : Y.map (MulAut.conj uB).toMonoidHom = HB := by
    calc Y.map (MulAut.conj uB).toMonoidHom = Y.map (MulAut.conj g).toMonoidHom := hmap.symm
      _ = HB := hg.symm
  let eB : ↥B := uB
  have heE : eB ∈ UB := by simpa [eB] using huE
  have heY : Y.map (MulAut.conj eB).toMonoidHom = HB := by
    simpa [eB] using hYconj
  let u : projectiveSL 3 F := ((eB)⁻¹ : ↥B)
  have huU : u ∈ U := by
    have h : (eB)⁻¹ ∈ UB := by
      simpa [eB] using (Subgroup.inv_mem (H := UB) heE)
    exact Subgroup.mem_subgroupOf.mp h
  let τ : MulAut ↥B := (MulAut.conj eB) * σ
  have hτcomp : τ.toMonoidHom = (MulAut.conj eB).toMonoidHom.comp σ.toMonoidHom := by
    ext x
    rfl
  have hτU : UB.map τ.toMonoidHom = UB := by
    rw [hτcomp, ← Subgroup.map_map, hσU]
    exact Subgroup.Normal.map_conj_eq (H := UB) eB
  have hτV1 : V1B.map τ.toMonoidHom = V1B := by
    rw [hτcomp, ← Subgroup.map_map, hV1B_map]
    exact Subgroup.Normal.map_conj_eq (H := V1B) eB
  have hτV2 : V2B.map τ.toMonoidHom = V2B := by
    rw [hτcomp, ← Subgroup.map_map, hV2B_map]
    exact Subgroup.Normal.map_conj_eq (H := V2B) eB
  have hτH : HB.map τ.toMonoidHom = HB := by
    rw [hτcomp, ← Subgroup.map_map, heY]
  have hWgB_eq : (Wg : Subgroup (projectiveSL 3 F)).subgroupOf B = V1B ⊓ V2B := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : (x : projectiveSL 3 F) ∈ (V1 : Subgroup (projectiveSL 3 F)) ⊓
          (V2 : Subgroup (projectiveSL 3 F)) := by
        rwa [V1_inf_V2]
      exact ⟨hx'.1, hx'.2⟩
    · rintro ⟨h1, h2⟩
      have hx' : (x : projectiveSL 3 F) ∈ (V1 : Subgroup (projectiveSL 3 F)) ⊓
          (V2 : Subgroup (projectiveSL 3 F)) := ⟨h1, h2⟩
      rwa [V1_inf_V2] at hx'
  have hτWg : ((Wg : Subgroup (projectiveSL 3 F)).subgroupOf B).map τ.toMonoidHom =
      (Wg : Subgroup (projectiveSL 3 F)).subgroupOf B := by
    rw [hWgB_eq]
    rw [Subgroup.map_inf _ _ _ τ.injective, hτV1, hτV2]
  let XaB : Subgroup ↥B := (rootX (F := F)).subgroupOf B
  let XbB : Subgroup ↥B := (rootY (F := F)).subgroupOf B
  let WgB : Subgroup ↥B := (Wg : Subgroup (projectiveSL 3 F)).subgroupOf B
  have hXaB_le_V1B : XaB ≤ V1B := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (rootX_le_V1 (Subgroup.mem_subgroupOf.mp hx))
  have hXbB_le_V2B : XbB ≤ V2B := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (rootY_le_V2 (Subgroup.mem_subgroupOf.mp hx))
  have hrootW_eq : rootW (F := F) = (Wg : Subgroup (projectiveSL 3 F)) := rootW_eq_Wg
  obtain ⟨t, ht⟩ := exists_unit_cube_ne_one (F := F) hq
  let hP : projectiveSL 3 F := proj 3 F (dMat t t)
  have hPH : hP ∈ H := dP_mem_torus3 t t
  have hPB : hP ∈ B := hHleB hPH
  let hB0 : ↥B := ⟨hP, hPB⟩
  have hPx : ∀ a : F, hP * xP a * hP⁻¹ = xP a := by
    intro a
    dsimp [hP]
    rw [dP_conj_xP]
    congr 1
    field_simp
  have hPw : ∀ c : F, hP * wP c * hP⁻¹ = wP ((t : F) ^ 3 * c) := by
    intro c
    dsimp [hP]
    rw [dP_conj_wP]
    congr 1
    ring
  have hXaWgP : rootX (F := F) ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := hx.1
    obtain ⟨c, hc⟩ := mem_Wg.mp hx.2
    have h : xP a * wP 0 = yP 0 * wP c := by
      rw [wP_zero, yP_zero, one_mul, mul_one]
      exact ha.trans hc
    obtain ⟨ha0, -, -⟩ := xP_wP_eq_yP_wP h
    rw [Subgroup.mem_bot, ← ha, ha0, xP_zero]
  have hXaWgB : XaB ⊓ WgB = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    apply Subtype.ext
    have hxP : (x : projectiveSL 3 F) ∈ rootX (F := F) ⊓
        (Wg : Subgroup (projectiveSL 3 F)) :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    rw [hXaWgP, Subgroup.mem_bot] at hxP
    exact hxP
  have hτWgB : WgB.map τ.toMonoidHom = WgB := by
    dsimp [WgB]
    exact hτWg
  have hXaB_map : XaB.map τ.toMonoidHom = XaB := by
    have hτdisj : (XaB.map τ.toMonoidHom) ⊓ WgB = ⊥ := by
      have h := congrArg (fun S : Subgroup ↥B => S.map τ.toMonoidHom) hXaWgB
      rw [Subgroup.map_inf _ _ _ τ.injective, hτWgB, Subgroup.map_bot] at h
      exact h
    let VX : Subgroup (projectiveSL 3 F) := (XaB.map τ.toMonoidHom).map B.subtype
    have hVXle : VX ≤ (V1 : Subgroup (projectiveSL 3 F)) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyV1 : y ∈ V1B := by
        rw [← hτV1]
        exact Subgroup.map_mono hXaB_le_V1B hy
      exact Subgroup.mem_subgroupOf.mp hyV1
    have hcardXaB : Nat.card XaB = Nat.card F := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootX_le_U.trans hUB)).toEquiv,
        card_rootX]
    have hcardVX : Nat.card VX = Nat.card F := by
      rw [Subgroup.card_map_of_injective B.subtype_injective,
        Subgroup.card_map_of_injective τ.injective, hcardXaB]
    have hVXdisj : VX ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥ := by
      have hWgB_map : WgB.map B.subtype = (Wg : Subgroup (projectiveSL 3 F)) := by
        dsimp [WgB]
        exact Subgroup.map_subgroupOf_eq_of_le hWgleB
      have h := congrArg (fun S : Subgroup ↥B => S.map B.subtype) hτdisj
      rw [Subgroup.map_inf _ _ _ B.subtype_injective, hWgB_map, Subgroup.map_bot] at h
      exact h
    have hVXinv : ∀ v ∈ VX, hP * v * hP⁻¹ ∈ VX := by
      rintro v ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hB0_mem : hB0 ∈ HB := Subgroup.mem_subgroupOf.mpr hPH
      have hB0_map : hB0 ∈ HB.map τ.toMonoidHom := by
        rw [hτH]
        exact hB0_mem
      obtain ⟨h', hh', hτh'⟩ := Subgroup.mem_map.mp hB0_map
      obtain ⟨a, ha⟩ := (show ∃ a : F, xP a = (x : projectiveSL 3 F) from
        Subgroup.mem_subgroupOf.mp hx)
      have hx_eq : x = ⟨xP a, (rootX_le_U.trans hUB) (rootX_mem a)⟩ := Subtype.ext ha.symm
      have hx_conj : h' * x * h'⁻¹ ∈ XaB := by
        rw [hx_eq]
        exact Subgroup.mem_subgroupOf.mpr
          (conj_mem_rootX_of_mem_torus (Subgroup.mem_subgroupOf.mp hh') (a := a))
      have hconj_eq : (hB0 * τ x * hB0⁻¹ : ↥B) = τ (h' * x * h'⁻¹) := by
        rw [← hτh', map_mul, map_mul, map_inv]
        rfl
      have : hP * (τ x : projectiveSL 3 F) * hP⁻¹ =
          ((τ (h' * x * h'⁻¹) : ↥B) : projectiveSL 3 F) := by
        have := congrArg (fun z : ↥B => (z : projectiveSL 3 F)) hconj_eq
        simpa [hB0] using this
      change hP * (τ x : projectiveSL 3 F) * hP⁻¹ ∈ VX
      rw [this]
      exact Subgroup.mem_map_of_mem B.subtype
        (Subgroup.mem_map_of_mem τ.toMonoidHom hx_conj)
    have hVXeq : VX = rootX (F := F) :=
      eq_rootX_of_complement VX hVXle hcardVX hVXdisj hP ((t : F) ^ 3) hPx hPw ht hVXinv
    apply map_subtype_injective (B := B)
    calc (XaB.map τ.toMonoidHom).map B.subtype = VX := rfl
      _ = rootX (F := F) := hVXeq
      _ = XaB.map B.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (rootX_le_U.trans hUB)).symm
  have hXbB_map : XbB.map τ.toMonoidHom = XbB := by
    let t1 : Fˣ := t⁻¹ * t⁻¹
    let hP' : projectiveSL 3 F := proj 3 F (dMat t1 t)
    have hP'H : hP' ∈ H := dP_mem_torus3 t1 t
    have hP'B : hP' ∈ B := hHleB hP'H
    let hB1 : ↥B := ⟨hP', hP'B⟩
    have hP'y : ∀ b : F, hP' * yP b * hP'⁻¹ = yP b := by
      intro b
      have ht1 : (t1 : F) = (t : F)⁻¹ * (t : F)⁻¹ := by
        dsimp [t1]
        simp
      dsimp [hP']
      rw [dP_conj_yP]
      congr 1
      rw [ht1]
      field_simp
    have hP'w : ∀ c : F, hP' * wP c * hP'⁻¹ = wP (((t : F) ^ 3)⁻¹ * c) := by
      intro c
      have ht1 : (t1 : F) = (t : F)⁻¹ * (t : F)⁻¹ := by
        dsimp [t1]
        simp
      dsimp [hP']
      rw [dP_conj_wP]
      congr 1
      rw [ht1]
      field_simp
    have hτdisj : (XbB.map τ.toMonoidHom) ⊓ WgB = ⊥ := by
      have hXbWgP : rootY (F := F) ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨a, ha⟩ := hx.1
        obtain ⟨c, hc⟩ := mem_Wg.mp hx.2
        have h : xP 0 * wP c = yP a * wP 0 := by
          rw [xP_zero, wP_zero, one_mul, mul_one]
          exact hc.symm.trans ha.symm
        obtain ⟨-, ha0, -⟩ := xP_wP_eq_yP_wP h
        rw [Subgroup.mem_bot, ← ha, ha0, yP_zero]
      have hXbWgB : XbB ⊓ WgB = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        apply Subtype.ext
        have hxP : (x : projectiveSL 3 F) ∈ rootY (F := F) ⊓
            (Wg : Subgroup (projectiveSL 3 F)) :=
          ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
        rw [hXbWgP, Subgroup.mem_bot] at hxP
        exact hxP
      have h := congrArg (fun S : Subgroup ↥B => S.map τ.toMonoidHom) hXbWgB
      rw [Subgroup.map_inf _ _ _ τ.injective, hτWgB, Subgroup.map_bot] at h
      exact h
    let VY : Subgroup (projectiveSL 3 F) := (XbB.map τ.toMonoidHom).map B.subtype
    have hVYle : VY ≤ (V2 : Subgroup (projectiveSL 3 F)) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyV2 : y ∈ V2B := by
        rw [← hτV2]
        exact Subgroup.map_mono hXbB_le_V2B hy
      exact Subgroup.mem_subgroupOf.mp hyV2
    have hcardXbB : Nat.card XbB = Nat.card F := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootY_le_U.trans hUB)).toEquiv,
        card_rootY]
    have hcardVY : Nat.card VY = Nat.card F := by
      rw [Subgroup.card_map_of_injective B.subtype_injective,
        Subgroup.card_map_of_injective τ.injective, hcardXbB]
    have hVYdisj : VY ⊓ (Wg : Subgroup (projectiveSL 3 F)) = ⊥ := by
      have hWgB_map : WgB.map B.subtype = (Wg : Subgroup (projectiveSL 3 F)) := by
        dsimp [WgB]
        exact Subgroup.map_subgroupOf_eq_of_le hWgleB
      have h := congrArg (fun S : Subgroup ↥B => S.map B.subtype) hτdisj
      rw [Subgroup.map_inf _ _ _ B.subtype_injective, hWgB_map, Subgroup.map_bot] at h
      exact h
    have hVYinv : ∀ v ∈ VY, hP' * v * hP'⁻¹ ∈ VY := by
      rintro v ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hB1_mem : hB1 ∈ HB := Subgroup.mem_subgroupOf.mpr hP'H
      have hB1_map : hB1 ∈ HB.map τ.toMonoidHom := by
        rw [hτH]
        exact hB1_mem
      obtain ⟨h', hh', hτh'⟩ := Subgroup.mem_map.mp hB1_map
      obtain ⟨a, ha⟩ := (show ∃ a : F, yP a = (x : projectiveSL 3 F) from
        Subgroup.mem_subgroupOf.mp hx)
      have hx_eq : x = ⟨yP a, (rootY_le_U.trans hUB) (rootY_mem a)⟩ := Subtype.ext ha.symm
      have hx_conj : h' * x * h'⁻¹ ∈ XbB := by
        rw [hx_eq]
        exact Subgroup.mem_subgroupOf.mpr
          (conj_mem_rootY_of_mem_torus (Subgroup.mem_subgroupOf.mp hh') (a := a))
      have hconj_eq : (hB1 * τ x * hB1⁻¹ : ↥B) = τ (h' * x * h'⁻¹) := by
        rw [← hτh', map_mul, map_mul, map_inv]
        rfl
      have : hP' * (τ x : projectiveSL 3 F) * hP'⁻¹ =
          ((τ (h' * x * h'⁻¹) : ↥B) : projectiveSL 3 F) := by
        have := congrArg (fun z : ↥B => (z : projectiveSL 3 F)) hconj_eq
        simpa [hB1] using this
      change hP' * (τ x : projectiveSL 3 F) * hP'⁻¹ ∈ VY
      rw [this]
      exact Subgroup.mem_map_of_mem B.subtype
        (Subgroup.mem_map_of_mem τ.toMonoidHom hx_conj)
    have hlam' : ((t : F) ^ 3)⁻¹ ≠ 1 := by
      intro h
      exact ht (inv_eq_one.mp h)
    have hVYeq : VY = rootY (F := F) :=
      eq_rootY_of_complement VY hVYle hcardVY hVYdisj hP' ((t : F) ^ 3)⁻¹ hP'y hP'w hlam' hVYinv
    apply map_subtype_injective (B := B)
    calc (XbB.map τ.toMonoidHom).map B.subtype = VY := rfl
      _ = rootY (F := F) := hVYeq
      _ = XbB.map B.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (rootY_le_U.trans hUB)).symm
  obtain ⟨l, hl⟩ := exists_addEquiv_of_root_maps B (rootX (F := F))
    (rootX_le_U.trans hUB) xP xP_zero xP_add (fun a b h => xP_injective h) (fun x => Iff.rfl)
    τ hXaB_map
  obtain ⟨m, hm⟩ := exists_addEquiv_of_root_maps B (rootY (F := F))
    (rootY_le_U.trans hUB) yP yP_zero yP_add (fun a b h => yP_injective h) (fun x => Iff.rfl)
    τ hXbB_map
  have hWgB_map : WgB.map B.subtype = (Wg : Subgroup (projectiveSL 3 F)) := by
    dsimp [WgB]
    exact Subgroup.map_subgroupOf_eq_of_le hWgleB
  have hXw_map : ((rootW (F := F)).subgroupOf B).map τ.toMonoidHom =
      (rootW (F := F)).subgroupOf B := by
    rw [hrootW_eq]
    exact hτWg
  obtain ⟨n, hn⟩ := exists_addEquiv_of_root_maps B (rootW (F := F))
    (rootW_le_U.trans hUB) wP wP_zero wP_add (fun a b h => wP_injective h) (fun x => Iff.rfl)
    τ hXw_map
  have hrel : ∀ a b : F, n (a * b) = l a * m b := by
    intro a b
    let xaB : ↥B := ⟨xP a, (rootX_le_U.trans hUB) ((show xP a ∈ rootX (F := F) from ⟨a, rfl⟩))⟩
    let xbB : ↥B := ⟨yP b, (rootY_le_U.trans hUB) ((show yP b ∈ rootY (F := F) from ⟨b, rfl⟩))⟩
    let xwB : ↥B := ⟨wP (a * b), (rootW_le_U.trans hUB)
      ((show wP (a * b) ∈ rootW (F := F) from ⟨a * b, rfl⟩))⟩
    have hxyB : xbB * xaB = xwB * xaB * xbB := by
      apply Subtype.ext
      dsimp [xaB, xbB, xwB]
      exact yP_mul_xP a b
    have hmap := congrArg τ hxyB
    rw [map_mul, map_mul, map_mul] at hmap
    have hla : (τ xaB : projectiveSL 3 F) = xP (l a) := hl a
    have hmb : (τ xbB : projectiveSL 3 F) = yP (m b) := hm b
    have hnab : (τ xwB : projectiveSL 3 F) = wP (n (a * b)) := hn (a * b)
    have h1 : yP (m b) * xP (l a) = wP (n (a * b)) * xP (l a) * yP (m b) := by
      have h := congrArg (fun z : ↥B => (z : projectiveSL 3 F)) hmap
      simpa [Subgroup.coe_mul, hla, hmb, hnab] using h
    have h2 : yP (m b) * xP (l a) = wP (l a * m b) * xP (l a) * yP (m b) :=
      yP_mul_xP (l a) (m b)
    have h3 : wP (n (a * b)) * xP (l a) * yP (m b) =
        wP (l a * m b) * xP (l a) * yP (m b) := h1.symm.trans h2
    exact (U_ext h3).1
  have hστ (x : ↥B) : ((σ x : ↥B) : projectiveSL 3 F) = u * (τ x : projectiveSL 3 F) * u⁻¹ := by
    have hτx : τ x = eB * σ x * eB⁻¹ := by
      simp [τ, MulAut.mul_apply, MulAut.conj_apply]
    rw [hτx]
    dsimp [u]
    group
  refine ⟨u, huU, l, m, n, hrel, ?_, ?_, ?_, ?_⟩
  · intro x a hx
    have hxB : x = ⟨xP a, (rootX_le_U.trans hUB) (rootX_mem a)⟩ := Subtype.ext hx
    rw [hστ x, hxB]
    rw [show (τ ⟨xP a, (rootX_le_U.trans hUB) (rootX_mem a)⟩ : projectiveSL 3 F) = xP (l a)
      from hl a]
  · intro x b hx
    have hxB : x = ⟨yP b, (rootY_le_U.trans hUB) (rootY_mem b)⟩ := Subtype.ext hx
    rw [hστ x, hxB]
    rw [show (τ ⟨yP b, (rootY_le_U.trans hUB) (rootY_mem b)⟩ : projectiveSL 3 F) = yP (m b)
      from hm b]
  · intro x c hx
    have hxB : x = ⟨wP c, (rootW_le_U.trans hUB) (rootW_mem c)⟩ := Subtype.ext hx
    rw [hστ x, hxB]
    rw [show (τ ⟨wP c, (rootW_le_U.trans hUB) (rootW_mem c)⟩ : projectiveSL 3 F) = wP (n c)
      from hn c]
  · intro x hx
    have hxHB : x ∈ HB := Subgroup.mem_subgroupOf.mpr hx
    have hτxHB : τ x ∈ HB := by
      have h : τ x ∈ HB.map τ.toMonoidHom := Subgroup.mem_map_of_mem τ.toMonoidHom hxHB
      rwa [hτH] at h
    have hτxH : (τ x : projectiveSL 3 F) ∈ H := Subgroup.mem_subgroupOf.mp hτxHB
    rw [hστ x]
    rw [show u⁻¹ * (u * (τ x : projectiveSL 3 F) * u⁻¹) * u = (τ x : projectiveSL 3 F) by
      group]
    exact hτxH

end CFSG.Quasithin.F112R.St84
