module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneCent

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem

namespace CFSG.StandardType.A11

private lemma a11r9_viaFintypeEmbedding_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e₁ e₂ : Equiv.Perm α) (f : α ↪ β) :
    (e₁ * e₂).viaFintypeEmbedding f =
      e₁.viaFintypeEmbedding f * e₂.viaFintypeEmbedding f := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
    rw [show (e₁ * e₂) a = e₁ (e₂ a) from rfl]
    rw [show (e₁.viaFintypeEmbedding f * e₂.viaFintypeEmbedding f) (f a) =
      e₁.viaFintypeEmbedding f (e₂.viaFintypeEmbedding f (f a)) from rfl]
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
  · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range (e₁ * e₂) f hb]
    rw [show (e₁.viaFintypeEmbedding f * e₂.viaFintypeEmbedding f) b =
      e₁.viaFintypeEmbedding f (e₂.viaFintypeEmbedding f b) from rfl]
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range e₂ f hb,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range e₁ f hb]

private lemma a11r9_viaFintypeEmbedding_one {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α ↪ β) : (1 : Equiv.Perm α).viaFintypeEmbedding f = 1 := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
    rfl
  · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range (1 : Equiv.Perm α) f hb]
    rfl

private lemma a11r9_ext9_mul (σ τ : Equiv.Perm (Fin 9)) :
    ext9 (σ * τ) = ext9 σ * ext9 τ :=
  a11r9_viaFintypeEmbedding_mul σ τ (Fin.castLEEmb (by omega : 9 ≤ 12))

private lemma a11r9_ext9_one : ext9 (1 : Equiv.Perm (Fin 9)) = 1 :=
  a11r9_viaFintypeEmbedding_one (Fin.castLEEmb (by omega : 9 ≤ 12))

private lemma a11r9_swap_congr {α : Type*} [DecidableEq α] {x y x' y' : α}
    (hx : x = x') (hy : y = y') : Equiv.swap x y = Equiv.swap x' y' := by
  subst hx
  subst hy
  rfl

private lemma a11r9_ext9_swap (i j : Fin 9) :
    ext9 (Equiv.swap i j) = Equiv.swap (Fin.castLE (by omega : 9 ≤ 12) i)
      (Fin.castLE (by omega : 9 ≤ 12) j) := by
  let f : Fin 9 ↪ Fin 12 := Fin.castLEEmb (by omega : 9 ≤ 12)
  change (Equiv.swap i j).viaFintypeEmbedding f = Equiv.swap (f i) (f j)
  ext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hx
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image, Function.Embedding.swap_apply]
  · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range (Equiv.swap i j) f hx,
      Equiv.swap_apply_of_ne_of_ne (fun h => hx ⟨i, h.symm⟩) (fun h => hx ⟨j, h.symm⟩)]

private lemma a11r9_blk_ne_three_aux : ∀ a : Fin 12, a.val < 9 → blk a ≠ 3 := by
  decide

private lemma a11r9_blk_ne_three (a : Fin 12) (ha : a.val < 9) : blk a ≠ 3 :=
  a11r9_blk_ne_three_aux a ha

private lemma a11r9_swapBlocks_val_lt_aux :
    ∀ (l : Fin 4) (a : Fin 12), blk a ≠ l → (swapBlocks l a).val < 9 := by
  decide

private lemma a11r9_swapBlocks_three : swapBlocks 3 = 1 := by
  ext a
  simp [swapBlocks]

private lemma a11r9_swapBlocks_apply_three (a : Fin 12) : swapBlocks 3 a = a := by
  rw [a11r9_swapBlocks_three]
  rfl

private lemma a11r9_trAt_eq (l : Fin 4) (a b : Fin 12)
    (ha : (swapBlocks l a).val < 9) (hb : (swapBlocks l b).val < 9) (hab : a ≠ b) :
    trAt l a b = permSL 8 (Equiv.swap (⟨(swapBlocks l a).val, ha⟩ : Fin 9)
      (⟨(swapBlocks l b).val, hb⟩ : Fin 9)) := by
  rw [trAt, dif_pos ⟨ha, hb, hab⟩]

private lemma a11r9_tv9_eq (a b : Fin 12) (ha : a.val < 9) (hb : b.val < 9) (hab : a ≠ b) :
    tv9 a b = SpecialLinearGroup.transvection (i := (⟨a.val, ha⟩ : Fin 9))
      (j := (⟨b.val, hb⟩ : Fin 9))
      (fun e => hab (Fin.ext (by simpa using congrArg Fin.val e))) (1 : F2) := by
  rw [tv9, dif_pos ⟨ha, hb, hab⟩]

private noncomputable def a11r9_extCoeHom :
    Equiv.Perm (Fin 9) →* Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.SpecialLinearGroup.coeMonoidHom.comp (permSL 8)

private noncomputable def a11r9_signedPermHom :
    Equiv.Perm (Fin 9) →* Matrix (Fin 9) (Fin 9) F2 where
  toFun π := signedPerm π 1
  map_one' := by
    rw [signedPerm_one]
    ext i j
    simp
  map_mul' π π' := by
    rw [signedPerm_mul_signedPerm]
    apply congrArg (signedPerm (π * π'))
    funext s
    simp

private lemma a11r9_permSL_swap_adj (k : Fin 8) :
    (permSL 8 (Equiv.swap k.castSucc k.succ) : Matrix (Fin 9) (Fin 9) F2) =
      signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin 9 → F2) := by
  have hsimple : typeAWeylHom 8 (Equiv.swap k.castSucc k.succ) =
      (coxeterMatrix (isFiniteType_A 8)).toCoxeterSystem.simple k :=
    typeARealizes_inj 8 (typeAWeylOf_spec 8 (Equiv.swap k.castSucc k.succ))
      (typeARealizes_simple 8 k)
  calc (permSL 8 (Equiv.swap k.castSucc k.succ) : Matrix (Fin 9) (Fin 9) F2)
      = (slWeylLift 8 two_eq_zero
          (typeAWeylHom 8 (Equiv.swap k.castSucc k.succ)) : Matrix (Fin 9) (Fin 9) F2) := rfl
    _ = (slWeylLift 8 two_eq_zero
          ((coxeterMatrix (isFiniteType_A 8)).toCoxeterSystem.simple k) :
            Matrix (Fin 9) (Fin 9) F2) := by rw [hsimple]
    _ = (weylRep 8 F2 k : Matrix (Fin 9) (Fin 9) F2) := by rw [slWeylLift_simple]
    _ = signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin 9 → F2) :=
        coe_weylRep_of_two 8 two_eq_zero k

private lemma a11r9_permSL_coe (π : Equiv.Perm (Fin 9)) :
    (permSL 8 π : Matrix (Fin 9) (Fin 9) F2) = signedPerm π 1 := by
  have hS : Submonoid.closure (Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)) =
      (⊤ : Submonoid (Equiv.Perm (Fin 9))) :=
    Equiv.Perm.mclosure_swap_castSucc_succ 8
  have hmem : ∀ σ ∈ Submonoid.closure (Set.range (fun i : Fin 8 =>
        Equiv.swap i.castSucc i.succ)),
      a11r9_extCoeHom σ = a11r9_signedPermHom σ := by
    intro σ hσ
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa [a11r9_extCoeHom, a11r9_signedPermHom, MonoidHom.comp_apply]
        using a11r9_permSL_swap_adj k
    | one => rw [map_one, map_one]
    | mul x y _ _ ihx ihy => rw [map_mul, map_mul, ihx, ihy]
  have hπ : π ∈ Submonoid.closure (Set.range (fun i : Fin 8 =>
      Equiv.swap i.castSucc i.succ)) := by
    rw [hS]
    exact Submonoid.mem_top π
  simpa [a11r9_extCoeHom, a11r9_signedPermHom, MonoidHom.comp_apply] using hmem π hπ

private lemma a11r9_permSL_swap_comm {u v p q : Fin 9} (huv : u ≠ v) (hpq : p ≠ q)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (c : F2) :
    permSL 8 (Equiv.swap u v) * SpecialLinearGroup.transvection hpq c =
      SpecialLinearGroup.transvection hpq c * permSL 8 (Equiv.swap u v) := by
  have hcoe : ((permSL 8 (Equiv.swap u v)) : Matrix (Fin 9) (Fin 9) F2) =
      signedPerm (Equiv.swap u v) (1 : Fin 9 → F2) := a11r9_permSL_coe _
  have hε : ∀ s : Fin 9, (1 : Fin 9 → F2) s * (1 : Fin 9 → F2) s = 1 := by
    intro s
    simp
  have key := conj_transvection_of_coe_eq_signedPerm (g := permSL 8 (Equiv.swap u v))
    hcoe hε hpq c
  simp only [Pi.one_apply, one_mul] at key
  rw [transvection_eq_of_eq ((Equiv.swap u v).injective.ne hpq) hpq
    (Equiv.swap_apply_of_ne_of_ne hpu hpv) (Equiv.swap_apply_of_ne_of_ne hqu hqv) c] at key
  exact mul_inv_eq_iff_eq_mul.mp key

private lemma a11r9_trAt_comm_tvAt (l : Fin 4) (a b c d : Fin 12)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hla : blk a ≠ l) (hlb : blk b ≠ l) (hlc : blk c ≠ l) (hld : blk d ≠ l) :
    trAt l c d * tvAt l a b = tvAt l a b * trAt l c d := by
  have ha9 : (swapBlocks l a).val < 9 := a11r9_swapBlocks_val_lt_aux l a hla
  have hb9 : (swapBlocks l b).val < 9 := a11r9_swapBlocks_val_lt_aux l b hlb
  have hc9 : (swapBlocks l c).val < 9 := a11r9_swapBlocks_val_lt_aux l c hlc
  have hd9 : (swapBlocks l d).val < 9 := a11r9_swapBlocks_val_lt_aux l d hld
  have hp : (⟨(swapBlocks l a).val, ha9⟩ : Fin 9) ≠ ⟨(swapBlocks l b).val, hb9⟩ :=
    fun h => hab ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h)))
  have hu : (⟨(swapBlocks l c).val, hc9⟩ : Fin 9) ≠ ⟨(swapBlocks l d).val, hd9⟩ :=
    fun h => hcd ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h)))
  have hpu : (⟨(swapBlocks l a).val, ha9⟩ : Fin 9) ≠ ⟨(swapBlocks l c).val, hc9⟩ :=
    fun h => hca ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))).symm
  have hpv : (⟨(swapBlocks l a).val, ha9⟩ : Fin 9) ≠ ⟨(swapBlocks l d).val, hd9⟩ :=
    fun h => hda ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))).symm
  have hqu : (⟨(swapBlocks l b).val, hb9⟩ : Fin 9) ≠ ⟨(swapBlocks l c).val, hc9⟩ :=
    fun h => hcb ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))).symm
  have hqv : (⟨(swapBlocks l b).val, hb9⟩ : Fin 9) ≠ ⟨(swapBlocks l d).val, hd9⟩ :=
    fun h => hdb ((swapBlocks l).injective
      (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))).symm
  rw [tvAt, a11r9_tv9_eq (swapBlocks l a) (swapBlocks l b) ha9 hb9
        (fun h => hab ((swapBlocks l).injective h)),
      a11r9_trAt_eq l c d hc9 hd9 hcd]
  rw [transvection_eq_of_eq _ hp rfl rfl (1 : F2)]
  exact a11r9_permSL_swap_comm hu hp hpu hpv hqu hqv 1

private lemma a11r9_rho_swap {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hρ : RhoEval Φ ρ) (i j : Fin 9) (hij : i ≠ j) :
    ρ (ext9 (Equiv.swap i j)) = Φ 3 (permSL 8 (Equiv.swap i j)) := by
  rw [a11r9_ext9_swap i j]
  have hnd : (Fin.castLE (by omega : 9 ≤ 12) i) ≠ (Fin.castLE (by omega : 9 ≤ 12) j) :=
    fun h => hij (Fin.ext (congrArg (fun x : Fin 12 => x.val) h))
  have htr : trAt 3 (Fin.castLE (by omega : 9 ≤ 12) i) (Fin.castLE (by omega : 9 ≤ 12) j)
      = permSL 8 (Equiv.swap i j) := by
    rw [a11r9_trAt_eq 3 _ _ (by rw [a11r9_swapBlocks_apply_three]; exact i.isLt)
        (by rw [a11r9_swapBlocks_apply_three]; exact j.isLt) hnd]
    apply congrArg (permSL 8)
    apply a11r9_swap_congr
    · apply Fin.ext
      simp [a11r9_swapBlocks_apply_three]
    · apply Fin.ext
      simp [a11r9_swapBlocks_apply_three]
  rw [hρ 3 _ _ hnd (a11r9_blk_ne_three _ (by simpa using i.isLt))
      (a11r9_blk_ne_three _ (by simpa using j.isLt)), htr]

private def a11r9_goodB (a b c d : Fin 12) : Prop :=
  ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l ∧ blk d ≠ l

private instance (a b c d : Fin 12) : Decidable (a11r9_goodB a b c d) := by
  unfold a11r9_goodB
  infer_instance

private def a11r9_hasMid (a b c d : Fin 12) : Prop :=
  ∃ e : Fin 12, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧
    a11r9_goodB a b c e ∧ a11r9_goodB a b e d

private instance (a b c d : Fin 12) : Decidable (a11r9_hasMid a b c d) := by
  unfold a11r9_hasMid
  infer_instance

private lemma a11r9_good_two_step_aux :
    ∀ (a b c d : Fin 12),
      (a.val < 8 ∧ b.val < 8 ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d) →
      (a11r9_goodB a b c d ∨ a11r9_hasMid a b c d) := by
  decide

private lemma a11r9_good_two_step (a b c d : Fin 12) (ha : a.val < 8) (hb : b.val < 8)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    (∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l ∧ blk d ≠ l) ∨
      ∃ e : Fin 12, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧
        (∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l ∧ blk e ≠ l) ∧
        (∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk e ≠ l ∧ blk d ≠ l) := by
  rcases a11r9_good_two_step_aux a b c d ⟨ha, hb, hab, hca, hcb, hda, hdb, hcd⟩ with
    hgood | hmid
  · exact Or.inl hgood
  · unfold a11r9_hasMid at hmid
    rcases hmid with ⟨e, hea, heb, hec, hed, hce, hde⟩
    exact Or.inr ⟨e, hea, heb, hec, hed, hce, hde⟩

theorem a11RhoS9Input_holds :
    ∀ (G : Type) [Group G] (Φ : Fin 4 → SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G),
      Coherent Φ → RhoEval Φ ρ → RhoOn9 (Φ 3) ρ ∧ RhoStab (Φ 3) ρ := by
  intro G _ Φ ρ hcoh hρeval
  constructor
  ·
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one => simp only [a11r9_ext9_one, map_one]
    | swap_mul f x y hxy ih =>
      simp only [a11r9_ext9_mul, map_mul]
      rw [a11r9_rho_swap Φ ρ hρeval x y hxy, ih]
  ·
    intro a b ha hb hab w hwa hwb
    let Good : Set (Equiv.Perm (Fin 12)) :=
      {s | ∃ c d : Fin 12, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
        s = Equiv.swap c d ∧ ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l ∧ blk d ≠ l}
    have hgen : ∀ c d : Fin 12, c ≠ a → c ≠ b → d ≠ a → d ≠ b → c ≠ d →
        Equiv.swap c d ∈ Subgroup.closure Good := by
      intro c d hca hcb hda hdb hcd
      rcases a11r9_good_two_step a b c d ha hb hab hca hcb hda hdb hcd with
        hgood | ⟨e, hea, heb, hec, hed, hcegood, hedgood⟩
      · exact Subgroup.subset_closure ⟨c, d, hcd, hca, hcb, hda, hdb, rfl, hgood⟩
      · have hce : Equiv.swap c e ∈ Subgroup.closure Good :=
          Subgroup.subset_closure ⟨c, e, hec.symm, hca, hcb, hea, heb, rfl, hcegood⟩
        have hed' : Equiv.swap e d ∈ Subgroup.closure Good :=
          Subgroup.subset_closure ⟨e, d, hed, hea, heb, hda, hdb, rfl, hedgood⟩
        have hswap : Equiv.swap c d = Equiv.swap c e * Equiv.swap e d * Equiv.swap c e := by
          have key := Equiv.swap_mul_swap_mul_swap (x := d) (y := e) (z := c)
            hed.symm hcd.symm
          rw [Equiv.swap_comm c e, Equiv.swap_comm e d]
          exact key.symm
        rw [hswap]
        exact mul_mem (mul_mem hce hed') hce
    have hgood_comm : ∀ s ∈ Good, ρ s * Φ 3 (tv9 a b) = Φ 3 (tv9 a b) * ρ s := by
      rintro s ⟨c, d, hcd, hca, hcb, hda, hdb, rfl, l, hla, hlb, hlc, hld⟩
      have hρs : ρ (Equiv.swap c d) = Φ l (trAt l c d) := hρeval l c d hcd hlc hld
      have htv : tvAt 3 a b = tv9 a b := by
        rw [tvAt, a11r9_swapBlocks_apply_three a, a11r9_swapBlocks_apply_three b]
      have hT : Φ 3 (tv9 a b) = Φ l (tvAt l a b) := by
        rw [← htv]
        exact hcoh 3 l a b hab (a11r9_blk_ne_three a (by omega)) (a11r9_blk_ne_three b (by omega))
          hla hlb
      rw [hρs, hT, ← map_mul, ← map_mul]
      exact congrArg (Φ l) (a11r9_trAt_comm_tvAt l a b c d hab hcd hca hcb hda hdb
        hla hlb hlc hld)
    have hclosure : Subgroup.closure Good ≤
        (Subgroup.centralizer ({Φ 3 (tv9 a b)} : Set G)).comap ρ :=
      (Subgroup.closure_le _).mpr (fun s hs => by
        show ρ s ∈ Subgroup.centralizer ({Φ 3 (tv9 a b)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hgood_comm s hs)
    have hwmem : w ∈ Subgroup.closure Good := by
      have hAll : Subgroup.closure {σ : Equiv.Perm (Fin 12) | ∃ c d, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧
          d ≠ a ∧ d ≠ b ∧ σ = Equiv.swap c d} ≤ Subgroup.closure Good :=
        (Subgroup.closure_le _).mpr (fun s hs => by
          obtain ⟨c, d, hcd, hca, hcb, hda, hdb, rfl⟩ := hs
          exact hgen c d hca hcb hda hdb hcd)
      exact hAll (mem_closure_swap_of_fix hwa hwb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hclosure hwmem)

end CFSG.StandardType.A11

end
