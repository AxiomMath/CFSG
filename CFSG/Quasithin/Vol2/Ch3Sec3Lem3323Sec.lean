module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Chief

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ChiefCount

namespace Sec3323

variable {G : Type} [Group G] {F : Type} [Field F]

@[expose] def coord {k : ℕ} (i : Fin k) :
    Multiplicative (Fin k → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i)

theorem toAdd_coord {k : ℕ} (i : Fin k) (x : Multiplicative (Fin k → Fin 3 → F)) :
    Multiplicative.toAdd (coord i x) = Multiplicative.toAdd x i := rfl

omit [Field F] in
theorem card_vec [Fintype F] (hF : Fintype.card F = 2) :
    Nat.card (Multiplicative (Fin 3 → F)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun, hF,
    Fintype.card_fin]
  norm_num

theorem index_ker_eq [Fintype F] (hF : Fintype.card F = 2) {X : Type} [Group X]
    (f : X →* Multiplicative (Fin 3 → F)) (hf : Function.Surjective f) : f.ker.index = 8 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, card_vec hF]

section One

variable {L W H : Subgroup G}

theorem ker_coord_zero (β : ↥W →* Multiplicative (Fin 1 → Fin 3 → F)) :
    ((coord 0).comp β).ker = β.ker := by
  ext w
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h0
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact congrArg Multiplicative.toAdd h0
  · intro h0
    rw [h0, map_one]

theorem coord_zero_surj {β : ↥W →* Multiplicative (Fin 1 → Fin 3 → F)}
    (hβs : Function.Surjective β) : Function.Surjective ((coord 0).comp β) := by
  intro y
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd fun _ => Multiplicative.toAdd y)
  exact ⟨w, by rw [MonoidHom.comp_apply, hw]; rfl⟩

theorem isTwoChiefFactor_one [Fintype F] (hF : Fintype.card F = 2) (hHW : H ≤ W) (hWL : W ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hLH : L ≤ Subgroup.normalizer (H : Set G))
    (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      act x = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥W →* Multiplicative (Fin 1 → Fin 3 → F))
    (hβs : Function.Surjective β) (hβk : β.ker = H.subgroupOf W)
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i)) :
    IsTwoChiefFactor L W H ∧ ¬ ⁅W, L⁆ ≤ H :=
  Chief3323.isTwoChiefFactor_of_coords hF hHW hWL hLW hLH act hsurj ((coord 0).comp β)
    (coord_zero_surj hβs) ((ker_coord_zero β).trans hβk) fun a u v huv => hβe a u v huv 0

theorem relIndex_one [Fintype F] (hF : Fintype.card F = 2)
    (β : ↥W →* Multiplicative (Fin 1 → Fin 3 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = H.subgroupOf W) : H.relIndex W = 8 := by
  rw [Subgroup.relIndex, ← hβk, ← ker_coord_zero β]
  exact index_ker_eq hF _ (coord_zero_surj hβs)

end One

section Two

variable {L W H : Subgroup G} (β : ↥W →* Multiplicative (Fin 2 → Fin 3 → F))

@[expose] def sumFst : Subgroup G := ((coord 1).comp β).ker.map W.subtype

theorem mem_sumFst {g : G} :
    g ∈ sumFst β ↔ ∃ hg : g ∈ W, Multiplicative.toAdd (β ⟨g, hg⟩) 1 = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, congrArg Multiplicative.toAdd hw⟩
  · rintro ⟨hg, h0⟩
    exact ⟨⟨g, hg⟩, Multiplicative.toAdd.injective h0, rfl⟩

theorem sumFst_le : sumFst β ≤ W := fun _ hg => ((mem_sumFst β).mp hg).1

theorem le_sumFst (hHW : H ≤ W) (hβk : β.ker = H.subgroupOf W) : H ≤ sumFst β := by
  intro g hg
  have h1 : β ⟨g, hHW hg⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hβk]
    exact hg
  refine (mem_sumFst β).mpr ⟨hHW hg, ?_⟩
  rw [h1]
  rfl

theorem le_normalizer_sumFst (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i)) :
    L ≤ Subgroup.normalizer (sumFst β : Set G) := by
  have key : ∀ a : ↥L, ∀ g ∈ sumFst β, (a : G) * g * (a : G)⁻¹ ∈ sumFst β := by
    intro a g hg
    obtain ⟨hgW, h0⟩ := (mem_sumFst β).mp hg
    have hm : (a : G) * g * (a : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW a.2) g).mp hgW
    refine (mem_sumFst β).mpr ⟨hm, ?_⟩
    rw [hβe a ⟨g, hgW⟩ ⟨_, hm⟩ rfl 1, h0, Matrix.mulVec_zero]
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key ⟨a, ha⟩ g, fun hg => ?_⟩
  have := key ⟨a, ha⟩⁻¹ _ hg
  simpa [mul_assoc] using this

@[expose] noncomputable def fstHom : ↥(sumFst β) →* Multiplicative (Fin 3 → F) :=
  (coord 0).comp (β.comp (Subgroup.inclusion (sumFst_le β)))

theorem fstHom_surj (hβs : Function.Surjective β) : Function.Surjective (fstHom β) := by
  intro y
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (Multiplicative.toAdd y)))
  have hwF : (w : G) ∈ sumFst β := (mem_sumFst β).mpr ⟨w.2, by
    rw [show (⟨(w : G), w.2⟩ : ↥W) = w from rfl, hw]
    simp⟩
  refine ⟨⟨w, hwF⟩, ?_⟩
  show coord 0 (β (Subgroup.inclusion (sumFst_le β) ⟨w, hwF⟩)) = y
  rw [show Subgroup.inclusion (sumFst_le β) ⟨(w : G), hwF⟩ = w from rfl, hw]
  rfl

theorem fstHom_ker (hβk : β.ker = H.subgroupOf W) :
    (fstHom β).ker = H.subgroupOf (sumFst β) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨huW, h1⟩ := (mem_sumFst β).mp u.2
  have hiff : (u : G) ∈ H ↔ β ⟨u, huW⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  rw [hiff]
  constructor
  · intro h0
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact congrArg Multiplicative.toAdd h0
    · exact h1
  · intro h0
    show coord 0 (β ⟨u, huW⟩) = 1
    rw [h0, map_one]

theorem isTwoChiefFactor_fst [Fintype F] (hF : Fintype.card F = 2) (hHW : H ≤ W) (hWL : W ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hLH : L ≤ Subgroup.normalizer (H : Set G))
    (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      act x = (g : Matrix (Fin 3) (Fin 3) F))
    (hβs : Function.Surjective β) (hβk : β.ker = H.subgroupOf W)
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i)) :
    IsTwoChiefFactor L (sumFst β) H ∧ ¬ ⁅sumFst β, L⁆ ≤ H :=
  Chief3323.isTwoChiefFactor_of_coords hF (le_sumFst β hHW hβk) ((sumFst_le β).trans hWL)
    (le_normalizer_sumFst β act hLW hβe) hLH act hsurj (fstHom β) (fstHom_surj β hβs)
    (fstHom_ker β hβk) fun a u v huv => hβe a ⟨u, sumFst_le β u.2⟩ ⟨v, sumFst_le β v.2⟩ huv 0

theorem relIndex_fst [Fintype F] (hF : Fintype.card F = 2) (hβs : Function.Surjective β)
    (hβk : β.ker = H.subgroupOf W) : H.relIndex (sumFst β) = 8 := by
  rw [Subgroup.relIndex, ← fstHom_ker β hβk]
  exact index_ker_eq hF _ (fstHom_surj β hβs)

@[expose] noncomputable def sndHom : ↥W →* Multiplicative (Fin 3 → F) := (coord 1).comp β

theorem sndHom_surj (hβs : Function.Surjective β) : Function.Surjective (sndHom β) := by
  intro y
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd (Pi.single (1 : Fin 2) (Multiplicative.toAdd y)))
  refine ⟨w, ?_⟩
  show coord 1 (β w) = y
  rw [hw]
  apply Multiplicative.toAdd.injective
  rw [toAdd_coord]
  simp

theorem sndHom_ker : (sndHom β).ker = (sumFst β).subgroupOf W := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sumFst]
  constructor
  · intro h0
    exact ⟨w.2, congrArg Multiplicative.toAdd h0⟩
  · rintro ⟨hg, h0⟩
    exact Multiplicative.toAdd.injective h0

theorem isTwoChiefFactor_snd [Fintype F] (hF : Fintype.card F = 2) (hWL : W ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      act x = (g : Matrix (Fin 3) (Fin 3) F))
    (hβs : Function.Surjective β)
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i)) :
    IsTwoChiefFactor L W (sumFst β) ∧ ¬ ⁅W, L⁆ ≤ sumFst β :=
  Chief3323.isTwoChiefFactor_of_coords hF (sumFst_le β) hWL hLW
    (le_normalizer_sumFst β act hLW hβe) act hsurj (sndHom β) (sndHom_surj β hβs)
    (sndHom_ker β) fun a u v huv => hβe a u v huv 1

theorem relIndex_snd [Fintype F] (hF : Fintype.card F = 2) (hβs : Function.Surjective β) :
    (sumFst β).relIndex W = 8 := by
  rw [Subgroup.relIndex, ← sndHom_ker β]
  exact index_ker_eq hF _ (sndHom_surj β hβs)

end Two

end Sec3323

end CFSG.Quasithin.H13
