
module

public import CFSG.Quasithin.Vol2.KGFactC31OrbSound
public import CFSG.Quasithin.MS93.ASIrrHeart
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.KGC31.Hex

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

@[expose] def ovMasks : Fin 6 → List ℕ :=
  ![[1, 2, 6, 11, 14], [1, 3, 7, 10, 15], [2, 3, 4, 9, 12], [4, 6, 7, 8, 13], [5, 8, 12, 14, 15],
    [5, 9, 10, 11, 13]]

@[expose] def ovoid (i : Fin 6) : Finset (Fin 4 → ZMod 2) :=
  ((ovMasks i).map (maskVec 4)).toFinset

@[expose] def ind (c : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 := fun k => if c ∈ ovoid k then 1 else 0

theorem ind_sum : ∀ c : Fin 4 → ZMod 2, ∑ k, ind c k = 0 := by decide

theorem ind_add : ∀ c d : Fin 4 → ZMod 2, ∀ k : Fin 6,
    ind (c + d) k + ind c k + ind d k = ind (c + d) 0 + ind c 0 + ind d 0 := by decide

theorem ind_const : ∀ c : Fin 4 → ZMod 2, (∀ k : Fin 6, ind c k = ind c 0) → c = 0 := by decide

theorem ind_surj : ∀ x : Fin 6 → ZMod 2, ∑ k, x k = 0 →
    ∃ c : Fin 4 → ZMod 2, ∀ k, x k + ind c k = x 0 + ind c 0 := by decide

theorem ovoid_injective : Function.Injective ovoid := by
  intro i j h
  revert i j
  decide

theorem exists_inter_eq : ∀ c : Fin 4 → ZMod 2, c ≠ 0 → ∃ i j : Fin 6,
    c ∈ ovoid i ∧ c ∈ ovoid j ∧ ∀ d, d ∈ ovoid i → d ∈ ovoid j → d = c := by decide

@[expose] def indW (c : Fin 4 → ZMod 2) : ↥(evenWeight 6) :=
  ⟨ind c, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact ind_sum c⟩

theorem mk_eq_mk_iff {x y : ↥(evenWeight 6)} :
    (QuotientAddGroup.mk x : AltHeart 6) = QuotientAddGroup.mk y ↔
      ∀ k : Fin 6, (x : Fin 6 → ZMod 2) k + (y : Fin 6 → ZMod 2) k =
        (x : Fin 6 → ZMod 2) 0 + (y : Fin 6 → ZMod 2) 0 := by
  rw [QuotientAddGroup.eq]
  have hneg : ∀ z : Fin 6 → ZMod 2, -z = z := fun z => by
    funext i
    simp only [Pi.neg_apply]
    generalize z i = a
    revert a
    decide
  have hc : ∀ z : Fin 6 → ZMod 2, (∀ i j, z i = z j) ↔ ∀ k, z k = z 0 :=
    fun z => ⟨fun h k => h k 0, fun h i j => by rw [h i, h j]⟩
  have e : ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = (x : Fin 6 → ZMod 2) + y := by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    congr 1
    exact hneg _
  change (∀ i j, ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i =
    ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) j) ↔ _
  rw [hc, e]
  simp only [Pi.add_apply]

@[expose] def hmap : (Fin 4 → ZMod 2) →+ AltHeart 6 where
  toFun c := QuotientAddGroup.mk (indW c)
  map_zero' := by
    rw [← QuotientAddGroup.mk_zero, mk_eq_mk_iff]
    intro k
    revert k
    decide
  map_add' c d := by
    rw [← QuotientAddGroup.mk_add, mk_eq_mk_iff]
    intro k
    have h := ind_add c d k
    have h2 : ∀ a b c d e f : ZMod 2, a + b + c = d + e + f → a + (b + c) = d + (e + f) := by
      decide
    exact h2 _ _ _ _ _ _ h

theorem hmap_apply (c : Fin 4 → ZMod 2) : hmap c = QuotientAddGroup.mk (indW c) := rfl

theorem hmap_injective : Function.Injective hmap := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [hmap_apply, ← QuotientAddGroup.mk_zero, mk_eq_mk_iff] at hc
  apply ind_const
  intro k
  have := hc k
  simpa [indW] using this

theorem hmap_surjective : Function.Surjective hmap := by
  intro u
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  have hx : ∑ k, (x : Fin 6 → ZMod 2) k = 0 := by
    have := x.2
    simpa [evenWeight] using this
  obtain ⟨c, hc⟩ := ind_surj x hx
  refine ⟨c, ?_⟩
  rw [hmap_apply, mk_eq_mk_iff]
  intro k
  have := hc k
  change ind c k + (x : Fin 6 → ZMod 2) k = ind c 0 + (x : Fin 6 → ZMod 2) 0
  rw [add_comm, this, add_comm]

theorem ind_mulVec {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} {σ : Equiv.Perm (Fin 6)}
    (hA : Function.Injective (A *ᵥ ·)) (hσ : ∀ i, (ovoid i).image (A *ᵥ ·) = ovoid (σ i))
    (c : Fin 4 → ZMod 2) : ind (A *ᵥ c) = fun k => ind c (σ⁻¹ k) := by
  funext k
  have hk : ovoid k = (ovoid (σ⁻¹ k)).image (A *ᵥ ·) := by
    rw [hσ]
    simp
  have hmem : A *ᵥ c ∈ ovoid k ↔ c ∈ ovoid (σ⁻¹ k) := by
    rw [hk, hA.mem_finset_image]
  unfold ind
  exact if_congr hmem rfl rfl

variable {Γ : Type} [Group Γ] {v : Fin 4 → Γ} (hv : EBasis v)

theorem mulVec_injective (g : ↥(eNorm hv)) : Function.Injective (eMat hv g *ᵥ ·) := by
  intro c d h
  have h2 := congrArg (eMat hv g⁻¹ *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, ← eMat_mul, inv_mul_cancel, eMat_one,
    Matrix.one_mulVec] at h2
  exact h2

@[expose] noncomputable def ovImg (g : ↥(eNorm hv)) (i : Fin 6) : Finset (Fin 4 → ZMod 2) :=
  (ovoid i).image (eMat hv g *ᵥ ·)

theorem ovImg_mul (g k : ↥(eNorm hv)) (i : Fin 6) :
    ovImg hv (g * k) i = (ovImg hv k i).image (eMat hv g *ᵥ ·) := by
  unfold ovImg
  rw [Finset.image_image, eMat_mul]
  congr 1
  funext c
  simp [Matrix.mulVec_mulVec]

@[expose] def ovStab : Subgroup Γ where
  carrier := {g | ∃ hg : g ∈ eNorm hv, ∀ i, ∃ j, ovImg hv ⟨g, hg⟩ i = ovoid j}
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    refine ⟨(eNorm hv).mul_mem ha hb, fun i => ?_⟩
    obtain ⟨j, hj⟩ := hbi i
    obtain ⟨l, hl⟩ := hai j
    refine ⟨l, ?_⟩
    have : (⟨a * b, (eNorm hv).mul_mem ha hb⟩ : ↥(eNorm hv)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, ovImg_mul, hj]
    exact hl
  one_mem' := ⟨(eNorm hv).one_mem, fun i => ⟨i, by
    have : (⟨1, (eNorm hv).one_mem⟩ : ↥(eNorm hv)) = 1 := rfl
    rw [this, ovImg, eMat_one]
    simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha, hai⟩
    refine ⟨(eNorm hv).inv_mem ha, fun i => ?_⟩
    choose f hf using hai
    have hfi : Function.Injective f := by
      intro j j' hjj'
      apply ovoid_injective
      have h1 := hf j
      have h2 := hf j'
      rw [hjj'] at h1
      rw [← h1] at h2
      exact Finset.image_injective (mulVec_injective hv ⟨a, ha⟩) h2.symm
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hfi) i
    refine ⟨j, ?_⟩
    have hinv : (⟨a⁻¹, (eNorm hv).inv_mem ha⟩ : ↥(eNorm hv)) = (⟨a, ha⟩ : ↥(eNorm hv))⁻¹ := rfl
    have h1 := hf j
    rw [hj] at h1
    rw [hinv]
    calc ovImg hv (⟨a, ha⟩ : ↥(eNorm hv))⁻¹ i =
        (ovImg hv ⟨a, ha⟩ j).image (eMat hv (⟨a, ha⟩ : ↥(eNorm hv))⁻¹ *ᵥ ·) := by
          rw [h1]; rfl
      _ = ovImg hv ((⟨a, ha⟩ : ↥(eNorm hv))⁻¹ * ⟨a, ha⟩) j := (ovImg_mul hv _ _ j).symm
      _ = ovoid j := by
          rw [inv_mul_cancel, ovImg, eMat_one]
          simp

theorem exists_ovImg (g : ↥(ovStab hv)) (i : Fin 6) :
    ∃ j, ovImg hv ⟨g, g.2.1⟩ i = ovoid j := g.2.2 i

@[expose] noncomputable def ovFun (g : ↥(ovStab hv)) (i : Fin 6) : Fin 6 :=
  (exists_ovImg hv g i).choose

theorem ovFun_spec (g : ↥(ovStab hv)) (i : Fin 6) :
    ovImg hv ⟨g, g.2.1⟩ i = ovoid (ovFun hv g i) :=
  (exists_ovImg hv g i).choose_spec

theorem ovFun_eq {g : ↥(ovStab hv)} {i j : Fin 6} (h : ovImg hv ⟨g, g.2.1⟩ i = ovoid j) :
    ovFun hv g i = j :=
  ovoid_injective ((ovFun_spec hv g i).symm.trans h)

theorem ovFun_mul (g k : ↥(ovStab hv)) (i : Fin 6) :
    ovFun hv (g * k) i = ovFun hv g (ovFun hv k i) := by
  apply ovFun_eq
  have : (⟨((g * k : ↥(ovStab hv)) : Γ), (g * k).2.1⟩ : ↥(eNorm hv)) =
      ⟨g, g.2.1⟩ * ⟨k, k.2.1⟩ := rfl
  rw [this, ovImg_mul, ovFun_spec hv k i]
  exact ovFun_spec hv g (ovFun hv k i)

theorem ovFun_one (i : Fin 6) : ovFun hv 1 i = i := by
  apply ovFun_eq
  have : (⟨((1 : ↥(ovStab hv)) : Γ), (1 : ↥(ovStab hv)).2.1⟩ : ↥(eNorm hv)) = 1 := rfl
  rw [this, ovImg, eMat_one]
  simp

@[expose] noncomputable def ovPerm : ↥(ovStab hv) →* Equiv.Perm (Fin 6) where
  toFun g :=
    { toFun := ovFun hv g
      invFun := ovFun hv g⁻¹
      left_inv := fun i => by rw [← ovFun_mul, inv_mul_cancel, ovFun_one]
      right_inv := fun i => by rw [← ovFun_mul, mul_inv_cancel, ovFun_one] }
  map_one' := Equiv.ext fun i => ovFun_one hv i
  map_mul' g k := Equiv.ext fun i => ovFun_mul hv g k i

theorem ovPerm_apply (g : ↥(ovStab hv)) (i : Fin 6) : ovPerm hv g i = ovFun hv g i := rfl

theorem image_ovoid (g : ↥(ovStab hv)) (i : Fin 6) :
    (ovoid i).image (eMat hv ⟨g, g.2.1⟩ *ᵥ ·) = ovoid (ovPerm hv g i) :=
  ovFun_spec hv g i

theorem eMat_eq_one_of_ovPerm (g : ↥(ovStab hv)) (h1 : ovPerm hv g = 1) :
    eMat hv ⟨g, g.2.1⟩ = 1 := by
  apply matrix_ext_mulVec
  intro c
  rw [Matrix.one_mulVec]
  by_cases hc : c = 0
  · rw [hc, Matrix.mulVec_zero]
  obtain ⟨i, j, hi, hj, huniq⟩ := exists_inter_eq c hc
  have hfix : ∀ l, (ovoid l).image (eMat hv ⟨g, g.2.1⟩ *ᵥ ·) = ovoid l := fun l => by
    rw [image_ovoid, h1, Equiv.Perm.one_apply]
  refine huniq _ ?_ ?_
  · rw [← hfix i]; exact Finset.mem_image_of_mem _ hi
  · rw [← hfix j]; exact Finset.mem_image_of_mem _ hj

theorem eq_top_of_isPGroup_quot' {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (N : Subgroup X) [N.Normal] (h : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← QuotientGroup.subsingleton_iff]
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  have : Group.IsNilpotent (X ⧸ N) := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

theorem pCoreOf_subgroupOf' {G : Type*} [Group G] (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

theorem eq_or_eq_of_section' {G : Type*} [Group G] {L V Z : Subgroup G} {B : Type*} [Group B]
    (β : ↥V →* B) (hker : β.ker = Z.subgroupOf V) (act : ↥L → B → B)
    (hact : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ → β v = act ℓ (β u))
    (hirr : ∀ Y : Subgroup B, (∀ (ℓ : ↥L) (y : B), y ∈ Y → act ℓ y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {W : Subgroup G} (hZW : Z ≤ W) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = Z ∨ W = V := by
  set Y : Subgroup B := (W.subgroupOf V).map β with hY
  have hinv : ∀ (ℓ : ↥L) (y : B), y ∈ Y → act ℓ y ∈ Y := by
    rintro ℓ y ⟨u, hu, rfl⟩
    replace hu : (u : G) ∈ W := hu
    have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) u).mp u.2
    have hvW : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW ℓ.2) u).mp hu
    refine ⟨⟨_, hv⟩, Subgroup.mem_subgroupOf.mpr hvW, ?_⟩
    exact hact ℓ u ⟨_, hv⟩ rfl
  rcases hirr Y hinv with hbot | htop
  · left
    refine le_antisymm (fun w hw => ?_) hZW
    have hβw : β ⟨w, hWV hw⟩ ∈ Y := ⟨⟨w, hWV hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hβw
    have : (⟨w, hWV hw⟩ : ↥V) ∈ β.ker := hβw
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  · right
    refine le_antisymm hWV fun v hv => ?_
    have hβv : β ⟨v, hv⟩ ∈ Y := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwv⟩ := hβv
    replace hw : (w : G) ∈ W := hw
    have hk : w⁻¹ * ⟨v, hv⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have hvw : v = (w : G) * ((w : G)⁻¹ * v) := by group
    rw [hvw]
    exact W.mul_mem hw (hZW (by simpa using hk))

theorem isQuasisimple_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ x y : X, x * y ≠ y * x) : CFSG.IsQuasisimple X := by
  have hcent : Subgroup.center X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have : x ∈ Subgroup.center X := by rw [h]; trivial
      exact hxy (Subgroup.mem_center_iff.mp this y).symm
  have hperf : Group.IsPerfect X := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : x * y * x⁻¹ * y⁻¹ ∈ commutator X := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot] at this
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [this, one_mul]
    · exact ⟨h⟩
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
  have := hs
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
  have := congrArg e h
  simpa using this

theorem alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6_nonabelian : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

variable [Finite Γ]

@[expose] noncomputable def coords : ↥(eSub hv) ≃* Multiplicative (Fin 4 → ZMod 2) :=
  (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c = Multiplicative.toAdd d))).symm

omit [Finite Γ] in
theorem eElt_coords (x : ↥(eSub hv)) :
    eElt v (Multiplicative.toAdd (coords hv x)) = (x : Γ) := by
  have h := (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c =
      Multiplicative.toAdd d))).apply_symm_apply x
  exact congrArg Subtype.val h

omit [Finite Γ] in
theorem coords_eElt (c : Fin 4 → ZMod 2) :
    Multiplicative.toAdd (coords hv ⟨eElt v c, eElt_mem hv c⟩) = c := by
  apply eElt_injective hv
  rw [eElt_coords]

omit [Finite Γ] in
theorem ovPerm_eq_one_iff (g : ↥(ovStab hv)) :
    ovPerm hv g = 1 ↔ (g : Γ) ∈ Subgroup.centralizer (eSub hv : Set Γ) := by
  constructor
  · intro h
    exact (eMat_eq_one_iff hv ⟨g, g.2.1⟩).mp (eMat_eq_one_of_ovPerm hv g h)
  · intro hc
    have h1 := (eMat_eq_one_iff hv ⟨g, g.2.1⟩).mpr hc
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    apply ovFun_eq
    rw [ovImg, h1]
    simp

theorem eq_alt6_of_card {H : Subgroup (Equiv.Perm (Fin 6))} (h : Nat.card H = 360) :
    H = alternatingGroup (Fin 6) := by
  have hi : H.index = 2 := by
    have h1 := H.card_mul_index
    rw [h, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    have : Nat.factorial 6 = 720 := by decide
    omega
  have hle : alternatingGroup (Fin 6) ≤ H := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    have h3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
    have hc4 : c = (c ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [SetLike.mem_coe, hc4]
    exact Subgroup.sq_mem_of_index_two hi _
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, card_alt6])).symm

omit [Finite Γ] in
theorem exists_ovAlt {L : Subgroup Γ} (hLs : L ≤ ovStab hv) (hVL : eSub hv ≤ L)
    (hC : L ⊓ Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv) (hcard : Nat.card L = 360 * 16) :
    ∃ α : ↥L →* alternatingGroup (Fin 6), Function.Surjective α ∧
      α.ker = (eSub hv).subgroupOf L ∧
      ∀ x, ((α x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        ovPerm hv (Subgroup.inclusion hLs x) := by
  let α₀ : ↥L →* Equiv.Perm (Fin 6) := (ovPerm hv).comp (Subgroup.inclusion hLs)
  have hker₀ : α₀.ker = (eSub hv).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact hC ⟨x.2, (ovPerm_eq_one_iff hv _).mp h1⟩
    · intro hx
      refine (ovPerm_eq_one_iff hv _).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact eSub_comm hv _ _ hy hx
  have hcardV : Nat.card (eSub hv) = 16 := by rw [card_eSub]; norm_num
  have hrange : α₀.range = alternatingGroup (Fin 6) := by
    apply eq_alt6_of_card
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α₀).toEquiv, hker₀,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv, hcardV, hcard] at h1
    omega
  refine ⟨α₀.codRestrict (alternatingGroup (Fin 6)) fun x => hrange ▸ ⟨x, rfl⟩, ?_, ?_,
    fun _ => rfl⟩
  · rintro ⟨σ, hσ⟩
    rw [← hrange] at hσ
    obtain ⟨x, hx⟩ := hσ
    exact ⟨x, Subtype.ext hx⟩
  · rw [← hker₀]
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h

theorem isAltBlockType_of_ovoids {L : Subgroup Γ} (hLs : L ≤ ovStab hv) (hperf : ⁅L, L⁆ = L)
    (hO : pCoreOf 2 L = eSub hv) (hcomm : ⁅eSub hv, L⁆ = eSub hv)
    (hC : L ⊓ Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv) (hcard : Nat.card L = 360 * 16) :
    IsAltBlockType L 6 ∧ IsExt ↥L (fun N _ => IsE2 4 N) (fun Y _ => IsAlt 6 Y) := by
  have hVL : eSub hv ≤ L := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLN : L ≤ eNorm hv := fun x hx => (hLs hx).1
  have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨α, hsurj, hker, hα⟩ := exists_ovAlt hv hLs hVL hC hcard
  have hpk : α.ker = CFSG.pCore 2 ↥L := by rw [hker, ← hO, pCoreOf_subgroupOf']
  have hU : blockU L = eSub hv := by rw [blockU, blockQ, hO, hcomm]
  let β₀ : ↥(eSub hv) →* Multiplicative (AltHeart 6) :=
    (AddMonoidHom.toMultiplicative hmap).comp (coords hv).toMonoidHom
  have hβ₀ : ∀ x, Multiplicative.toAdd (β₀ x) = hmap (Multiplicative.toAdd (coords hv x)) :=
    fun _ => rfl
  have hβ₀inj : Function.Injective β₀ :=
    (Multiplicative.ofAdd.injective.comp hmap_injective).comp (coords hv).injective
  have hβ₀surj : Function.Surjective β₀ := by
    intro y
    obtain ⟨c, hc⟩ := hmap_surjective (Multiplicative.toAdd y)
    refine ⟨(coords hv).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ₀, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hequiv : ∀ (ℓ : ↥L) (u w : ↥(eSub hv)), (w : Γ) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β₀ w) =
        SBc9.heartAct (α ℓ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (β₀ u)) := by
    intro ℓ u w hw
    set g : ↥(ovStab hv) := Subgroup.inclusion hLs ℓ
    have hcw : Multiplicative.toAdd (coords hv w) =
        eMat hv ⟨g, g.2.1⟩ *ᵥ Multiplicative.toAdd (coords hv u) := by
      apply eElt_injective hv
      rw [eElt_coords, ← conj_eq_eElt_mulVec, eElt_coords]
      exact hw
    rw [hβ₀, hβ₀, hcw, hmap_apply, hmap_apply, SBc9.heartAct_mk]
    congr 1
    apply Subtype.ext
    change ind _ = fun i =>
      ind (Multiplicative.toAdd (coords hv u)) ((α ℓ : Equiv.Perm (Fin 6))⁻¹ i)
    rw [hα]
    exact ind_mulVec (mulVec_injective hv _) (image_ovoid hv g) _
  have hZ : blockZ L = ⊥ := by
    rw [blockZ, hU]
    refine eq_bot_iff.mpr fun x ⟨hxV, hxC⟩ => ?_
    have hfix : ∀ σ ∈ alternatingGroup (Fin 6),
        SBc9.heartAct σ (Multiplicative.toAdd (β₀ ⟨x, hxV⟩)) =
          Multiplicative.toAdd (β₀ ⟨x, hxV⟩) := by
      intro σ hσ
      obtain ⟨ℓ, hℓ⟩ := hsurj ⟨σ, hσ⟩
      have h1 := hequiv ℓ ⟨x, hxV⟩ ⟨x, hxV⟩ (by
        show x = (ℓ : Γ) * x * (ℓ : Γ)⁻¹
        rw [Subgroup.mem_centralizer_iff.mp hxC ℓ ℓ.2, mul_inv_cancel_right])
      rw [hℓ] at h1
      exact h1.symm
    set y := Multiplicative.toAdd (β₀ ⟨x, hxV⟩) with hydef
    have hyy : ∀ z : AltHeart 6, z + z = 0 := fun z => by
      obtain ⟨c, rfl⟩ := hmap_surjective z
      rw [← map_add, add_self_zmod2, map_zero]
    have hneg : ∀ z : AltHeart 6, -z = z := fun z => neg_eq_of_add_eq_zero_right (hyy z)
    let Y : AddSubgroup (AltHeart 6) :=
      { carrier := {0, y}
        add_mem' := by
          rintro a b (rfl | rfl) (rfl | rfl)
          · left; exact add_zero 0
          · right; exact zero_add y
          · right; exact add_zero y
          · left; exact hyy y
        zero_mem' := Or.inl rfl
        neg_mem' := by
          rintro a (rfl | rfl)
          · left; exact neg_zero
          · right; exact hneg y }
    have hY : ∀ σ ∈ alternatingGroup (Fin 6), ∀ z ∈ Y, SBc9.heartAct σ z ∈ Y := by
      rintro σ hσ z (rfl | rfl)
      · left; exact map_zero _
      · right; exact hfix σ hσ
    rcases MS93.heart6_irreducible Y hY with hb | ht
    · have : y ∈ Y := Or.inr rfl
      rw [hb, AddSubgroup.mem_bot] at this
      have h0 : β₀ ⟨x, hxV⟩ = 1 := this
      have := hβ₀inj (h0.trans (map_one β₀).symm)
      exact congrArg Subtype.val this
    · exfalso
      have hmem : ∀ z : AltHeart 6, z = 0 ∨ z = y := fun z => by
        have hz : z ∈ Y := ht ▸ AddSubgroup.mem_top z
        exact hz
      have hne : ∀ c : Fin 4 → ZMod 2, c ≠ 0 → hmap c ≠ 0 := fun c hc h =>
        hc (hmap_injective (h.trans hmap.map_zero.symm))
      have h01 : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ Pi.single 1 1 := by decide
      have h0 : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by decide
      have h1 : (Pi.single 1 1 : Fin 4 → ZMod 2) ≠ 0 := by decide
      rcases hmem (hmap (Pi.single 0 1)) with e0 | e0
      · exact hne _ h0 e0
      rcases hmem (hmap (Pi.single 1 1)) with e1 | e1
      · exact hne _ h1 e1
      exact h01 (hmap_injective (e0.trans e1.symm))
  let β : ↥(blockU L) →* Multiplicative (AltHeart 6) :=
    β₀.comp (MulEquiv.subgroupCongr hU).toMonoidHom
  have hβ : ∀ x : ↥(blockU L), β x = β₀ ⟨x, hU ▸ x.2⟩ := fun _ => rfl
  have hβsurj : Function.Surjective β :=
    hβ₀surj.comp (MulEquiv.subgroupCongr hU).surjective
  have hβker : β.ker = (blockZ L).subgroupOf (blockU L) := by
    rw [hZ, Subgroup.bot_subgroupOf]
    refine (MonoidHom.ker_eq_bot_iff β).mpr ?_
    exact hβ₀inj.comp (MulEquiv.subgroupCongr hU).injective
  have hβeq : ∀ (ℓ : ↥L) (u w : ↥(blockU L)), (w : Γ) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α ℓ : Equiv.Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β w) := by
    intro ℓ u w hw x hx
    rw [hβ, hequiv ℓ ⟨u, hU ▸ u.2⟩ ⟨w, hU ▸ w.2⟩ hw, ← hβ, ← hx, SBc9.heartAct_mk]
  let act : ↥L → Multiplicative (AltHeart 6) → Multiplicative (AltHeart 6) :=
    fun ℓ y => Multiplicative.ofAdd
      (SBc9.heartAct ((α ℓ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
        (Multiplicative.toAdd y))
  have hact : ∀ (ℓ : ↥L) (u w : ↥(blockU L)), (w : Γ) = ℓ * u * ℓ⁻¹ → β w = act ℓ (β u) := by
    intro ℓ u w hw
    apply Multiplicative.toAdd.injective
    rw [hβ, hβ, hequiv ℓ ⟨u, hU ▸ u.2⟩ ⟨w, hU ▸ w.2⟩ hw]
    rfl
  have hirr : ∀ Y : Subgroup (Multiplicative (AltHeart 6)),
      (∀ (ℓ : ↥L) (y : Multiplicative (AltHeart 6)), y ∈ Y → act ℓ y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    let Ya : AddSubgroup (AltHeart 6) :=
      { carrier := {a | Multiplicative.ofAdd a ∈ Y}
        add_mem' := fun {a b} ha hb => by
          show Multiplicative.ofAdd (a + b) ∈ Y
          rw [ofAdd_add]
          exact Y.mul_mem ha hb
        zero_mem' := by
          show Multiplicative.ofAdd (0 : AltHeart 6) ∈ Y
          rw [ofAdd_zero]
          exact Y.one_mem
        neg_mem' := fun {a} ha => by
          show Multiplicative.ofAdd (-a) ∈ Y
          rw [ofAdd_neg]
          exact Y.inv_mem ha }
    have hYa : ∀ σ ∈ alternatingGroup (Fin 6), ∀ y ∈ Ya, SBc9.heartAct σ y ∈ Ya := by
      intro σ hσ y hy
      obtain ⟨ℓ, hℓ⟩ := hsurj ⟨σ, hσ⟩
      have := hY ℓ _ hy
      show Multiplicative.ofAdd (SBc9.heartAct σ y) ∈ Y
      have e : (((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))) = σ := by
        rw [hℓ]
      rw [← e]
      exact this
    rcases MS93.heart6_irreducible Ya hYa with hb | ht
    · left
      refine eq_bot_iff.mpr fun y hy => ?_
      have : Multiplicative.toAdd y ∈ Ya := hy
      rw [hb, AddSubgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact this
    · right
      refine eq_top_iff.mpr fun y _ => ?_
      have : Multiplicative.toAdd y ∈ Ya := ht ▸ AddSubgroup.mem_top _
      exact this
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set Γ) := by rw [hU]; exact hLN
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have hshort : IsShort2 L := by
    refine ⟨fun N _ hN => eq_top_of_isPGroup_quot' N hN, ?_, ⟨?_, ?_⟩, Or.inl ?_, ?_⟩
    · unfold CharTwo
      rw [hO]
      exact hC
    · rw [hU, blockQ, hO]
      exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        eSub_comm hv _ _ hy hx
    · intro x hx
      rw [hU] at hx
      rw [sq]
      exact eSub_sq hv x hx
    · have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
        have := alt6_simple
        exact eQ.isSimpleGroup
      refine isQuasisimple_of_simple hs ?_
      obtain ⟨x, y, hxy⟩ := alt6_nonabelian
      refine ⟨eQ.symm x, eQ.symm y, fun h => hxy ?_⟩
      have := congrArg eQ h
      simpa using this
    · refine ⟨?_, fun W hZW hWV hLW => ?_⟩
      · rw [hZ, hU]
        refine bot_lt_iff_ne_bot.mpr fun h => ?_
        have := card_eSub hv
        rw [h, Subgroup.card_bot] at this
        norm_num at this
      · exact eq_or_eq_of_section' β hβker act hact hirr hLU hZW hWV hLW
  refine ⟨⟨hshort, α, hsurj, hpk, β, hβsurj, hβker, hβeq⟩, ?_⟩
  have hn : ((eSub hv).subgroupOf L).Normal := by rw [← hker]; exact α.normal_ker
  exact ⟨(eSub hv).subgroupOf L, hn, ⟨(Subgroup.subgroupOfEquivOfLe hVL).trans (coords hv)⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)⟩⟩

end CFSG.Quasithin.KGC31.Hex

end
