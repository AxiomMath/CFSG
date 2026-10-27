module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APair
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem c23a_rk_subgroupOf_eq {U V : Subgroup G} (h : U ≤ V) :
    rk ↥(U.subgroupOf V) = rk ↥U := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

private theorem c23a_mQuot_eq_rk_sub {V U : Subgroup G} (hUV : U ≤ V) :
    E3.mQuot V U = rk ↥V - rk ↥U := by
  have h1 := rk_add_rkIdx (U.subgroupOf V)
  have h2 : rk ↥(U.subgroupOf V) = rk ↥U := c23a_rk_subgroupOf_eq hUV
  have h3 : rkIdx (U.subgroupOf V) = E3.mQuot V U := (E3.mQuot_eq_rkIdx V U).symm
  rw [h2, h3] at h1
  omega

private theorem c23a_mul_inv_hom_of_comm {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (σ : A →* A) (a b : A) :
    (a * b)⁻¹ * σ (a * b) = (a⁻¹ * σ a) * (b⁻¹ * σ b) := by
  rw [map_mul, mul_inv_rev]
  calc b⁻¹ * a⁻¹ * (σ a * σ b)
      = a⁻¹ * b⁻¹ * (σ a * σ b) := by rw [hcomm b⁻¹ a⁻¹]
    _ = a⁻¹ * (b⁻¹ * (σ a * σ b)) := by rw [mul_assoc (a⁻¹) (b⁻¹) (σ a * σ b)]
    _ = a⁻¹ * ((b⁻¹ * σ a) * σ b) := by rw [← mul_assoc (b⁻¹) (σ a) (σ b)]
    _ = a⁻¹ * ((σ a * b⁻¹) * σ b) := by rw [hcomm b⁻¹ (σ a)]
    _ = a⁻¹ * (σ a * (b⁻¹ * σ b)) := by rw [mul_assoc (σ a) (b⁻¹) (σ b)]
    _ = (a⁻¹ * σ a) * (b⁻¹ * σ b) := by rw [← mul_assoc (a⁻¹) (σ a) (b⁻¹ * σ b)]

theorem c23a_mSub_commElt_add {V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ normalizer (V : Set G)) :
    mSub (commElt V t) + mSub (V ⊓ centralizer ({t} : Set G)) = mSub V := by
  have htinv : t⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem ht
  have hconj : conjSubgroup V t⁻¹ = V := conjSubgroup_eq_iff_mem_normalizer.2 htinv
  have hmem : ∀ v : V, t⁻¹ * (v : G) * t ∈ V := by
    intro v
    have h : (v : G) ∈ conjSubgroup V t⁻¹ := by rw [hconj]; exact v.2
    simpa using mem_conjSubgroup_iff.1 h
  let σ : V →* V :=
    { toFun := fun v => ⟨t⁻¹ * (v : G) * t, hmem v⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext (by
        show t⁻¹ * ((v : G) * (w : G)) * t =
          (t⁻¹ * (v : G) * t) * (t⁻¹ * (w : G) * t)
        group) }
  let φ : V →* V :=
    { toFun := fun v => v⁻¹ * σ v
      map_one' := by simp
      map_mul' := fun v w =>
        c23a_mul_inv_hom_of_comm (fun a b => Subtype.ext (hV.comm a.2 b.2)) σ v w }
  have hσcoe : ∀ v : V, ((σ v : V) : G) = t⁻¹ * (v : G) * t := fun v => rfl
  have hcoe : ∀ v : V, (φ v : G) = (v : G)⁻¹ * t⁻¹ * (v : G) * t := by
    intro v
    calc (φ v : G) = ((v⁻¹ : V) : G) * ((σ v : V) : G) := rfl
      _ = (v : G)⁻¹ * (t⁻¹ * (v : G) * t) := by rw [hσcoe v]; rfl
      _ = (v : G)⁻¹ * t⁻¹ * (v : G) * t := by group
  have hmem_ker : ∀ v : V, v ∈ φ.ker ↔ (v : G) ∈ centralizer ({t} : Set G) := by
    intro v
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h1 : (v : G)⁻¹ * t⁻¹ * (v : G) * t = 1 := by
        rw [← hcoe v, h, Subgroup.coe_one]
      have htv : t⁻¹ * (v : G) * t = (v : G) := by
        calc t⁻¹ * (v : G) * t
            = (v : G) * ((v : G)⁻¹ * t⁻¹ * (v : G) * t) := by group
          _ = (v : G) * 1 := by rw [h1]
          _ = (v : G) := by group
      calc t * (v : G) = t * (t⁻¹ * (v : G) * t) := by rw [htv]
        _ = (v : G) * t := by group
    · intro h
      apply Subtype.ext
      rw [hcoe v, Subgroup.coe_one]
      have htv : t⁻¹ * (v : G) * t = (v : G) := by
        calc t⁻¹ * (v : G) * t = t⁻¹ * ((v : G) * t) := by rw [mul_assoc]
          _ = t⁻¹ * (t * (v : G)) := by rw [← h]
          _ = (t⁻¹ * t) * (v : G) := by rw [← mul_assoc]
          _ = (v : G) := by rw [inv_mul_cancel, one_mul]
      calc (v : G)⁻¹ * t⁻¹ * (v : G) * t
          = (v : G)⁻¹ * (t⁻¹ * (v : G) * t) := by group
        _ = (v : G)⁻¹ * (v : G) := by rw [htv]
        _ = 1 := by group
  have hker : φ.ker = (V ⊓ centralizer ({t} : Set G)).subgroupOf V := by
    ext v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hmem_ker v]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hrange : φ.range.map V.subtype = commElt V t := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [MonoidHom.mem_range] at hy
      obtain ⟨v, rfl⟩ := hy
      change (φ v : G) ∈ commElt V t
      rw [hcoe v]
      exact Subgroup.subset_closure ⟨v, v.2, rfl⟩
    · change Subgroup.closure {x | ∃ w ∈ V, x = w⁻¹ * t⁻¹ * w * t} ≤
        φ.range.map V.subtype
      rw [Subgroup.closure_le]
      rintro x ⟨w, hw, rfl⟩
      change ∃ a ∈ φ.range, V.subtype a = w⁻¹ * t⁻¹ * w * t
      exact ⟨φ ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, hcoe ⟨w, hw⟩⟩
  have hcardElt : Nat.card (commElt V t) = Nat.card φ.range := by
    rw [← hrange, Subgroup.card_map_of_injective V.subtype_injective]
  have hcardKer : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card φ.ker := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have hcard' : Nat.card (commElt V t) * Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G)
      = Nat.card V := by
    rw [hcardElt, hcardKer, mul_comm]
    exact Subgroup.card_ker_mul_card_range φ
  have hmain : rk V = rk (commElt V t) + rk (V ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    unfold rk
    rw [← hcard',
      padicValNat.mul (card_subgroup_pos (commElt V t)).ne'
        (card_subgroup_pos (V ⊓ centralizer ({t} : Set G) : Subgroup G)).ne']
  exact hmain.symm

theorem c23a_step12 {M V W W' U D₀ I : Subgroup G} {b : G} {n : ℕ} (hn : n ≤ 2)
    (hP : C23APair M V W W') (hUV : U ≤ V) (hIU : I ≤ U) (hbM : b ∈ M) (hb2 : b ^ 2 = 1)
    (hbV : ¬ V ≤ centralizer ({b} : Set G)) (hIb : ∀ i ∈ I, b * i = i * b)
    (hmI : E3.mQuot V I ≤ n) (hmU : E3.mQuot V U ≤ n)
    (hcomm : ∀ u ∈ U, u * b * u⁻¹ * b⁻¹ ∈ D₀) (hD : D₀ ⊓ W = ⊥ ∧ D₀ ⊓ W' = ⊥) :
    ∃ X Y : Subgroup G, ((X = W ∧ Y = W') ∨ (X = W' ∧ Y = W)) ∧
      (∀ y ∈ Y, b * y = y * b) ∧ commElt V b ≤ X ∧ 2 ≤ mSub (commElt V b) ∧
      U = V ⊓ centralizer ({b} : Set G) ∧ Y ≤ U := by
  have hb1 : b ≠ 1 := by
    intro h
    apply hbV
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    rw [h]
    simp
  have hbinv : b⁻¹ = b := by
    have h : b * b = 1 := by simpa [pow_two] using hb2
    exact inv_eq_of_mul_eq_one_right h
  have hord : orderOf b = 2 := by
    simpa using orderOf_eq_prime hb2 hb1
  have hbN : b ∈ normalizer (V : Set G) := hP.norm hbM
  let C := V ⊓ centralizer ({b} : Set G)
  have hCsub : C ≤ V := inf_le_left
  have hIC : I ≤ C := by
    intro i hi
    rw [Subgroup.mem_inf]
    exact ⟨hUV (hIU hi), by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hIb i hi⟩
  have hmC : E3.mQuot V C ≤ n := (E3.mQuot_mono hIC).trans hmI
  have hmadd : rk (commElt V b) + rk ↥C = rk ↥V := c23a_mSub_commElt_add hP.elem hbN
  have hq := c23a_mQuot_eq_rk_sub (V := V) (U := C) hCsub
  have hle : rk ↥C ≤ rk ↥V := rk_mono hCsub
  have hmCeq : rk (commElt V b) = E3.mQuot V C := by
    rw [hq]
    omega
  have hmcomm : mSub (commElt V b) ≤ 2 := by
    show rk (commElt V b) ≤ 2
    rw [hmCeq]
    exact hmC.trans hn
  obtain ⟨hside, hge2⟩ :=
    hP.oneSided b hbM ⟨1, by rw [hord, pow_one]⟩ hbV hmcomm
  have hC_pgroup : IsPGroup 2 C := hP.elem.isPGroup.to_le hCsub
  have h2C : 2 ≤ E3.mQuot V C := by
    have h : 2 ≤ rk (commElt V b) := hge2
    rwa [hmCeq] at h
  have hUC_of : ∀ X : Subgroup G, commElt V b ≤ X → D₀ ⊓ X = ⊥ → U ≤ C := by
    intro X hXcomm hXD u hu
    have huV : u ∈ V := hUV hu
    refine Subgroup.mem_inf.2 ⟨huV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hgen : (u⁻¹)⁻¹ * b⁻¹ * u⁻¹ * b ∈ commElt V b :=
      Subgroup.subset_closure ⟨u⁻¹, V.inv_mem huV, rfl⟩
    rw [inv_inv, hbinv] at hgen
    have hc : u * b * u⁻¹ * b⁻¹ ∈ commElt V b := by
      rw [hbinv]
      exact hgen
    have hcinf : u * b * u⁻¹ * b⁻¹ ∈ D₀ ⊓ X := ⟨hcomm u hu, hXcomm hc⟩
    rw [hXD, Subgroup.mem_bot] at hcinf
    have h1 : u * b * u⁻¹ = b := by
      calc u * b * u⁻¹ = u * b * u⁻¹ * (b⁻¹ * b) := by rw [inv_mul_cancel, mul_one]
        _ = (u * b * u⁻¹ * b⁻¹) * b := by group
        _ = 1 * b := by rw [hcinf]
        _ = b := one_mul b
    calc b * u = (u * b * u⁻¹) * u := by rw [h1]
      _ = u * b := by group
  have hCU_of : U ≤ C → C ≤ U := by
    intro hUC
    have hmC_le_mU : E3.mQuot V C ≤ E3.mQuot V U := E3.mQuot_mono hUC
    have heq : E3.mQuot V U = E3.mQuot V C :=
      le_antisymm ((hmU.trans hn).trans h2C) hmC_le_mU
    have hadd := E3.mQuot_add hUC hCsub
    have hzero : E3.mQuot C U = 0 := by omega
    have hUeq : U = C := (E3.mQuot_eq_zero_iff hC_pgroup hUC).1 hzero
    rw [hUeq]
  rcases hside with ⟨hcentW', hcommW⟩ | ⟨hcentW, hcommW'⟩
  · have hUC : U ≤ C := hUC_of W hcommW hD.1
    have hUeq : U = C := le_antisymm hUC (hCU_of hUC)
    have hW'U : W' ≤ U := by
      rw [hUeq]
      intro y hy
      exact Subgroup.mem_inf.2 ⟨hP.le' hy, by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hcentW' y hy⟩
    refine ⟨W, W', Or.inl ⟨rfl, rfl⟩, hcentW', hcommW, hge2, ?_, hW'U⟩
    change U = C
    exact hUeq
  · have hUC : U ≤ C := hUC_of W' hcommW' hD.2
    have hUeq : U = C := le_antisymm hUC (hCU_of hUC)
    have hWU : W ≤ U := by
      rw [hUeq]
      intro y hy
      exact Subgroup.mem_inf.2 ⟨hP.le hy, by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hcentW y hy⟩
    refine ⟨W', W, Or.inr ⟨rfl, rfl⟩, hcentW, hcommW', hge2, ?_, hWU⟩
    change U = C
    exact hUeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
