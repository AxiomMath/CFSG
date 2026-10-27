module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45N2AAux
public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped BigOperators

section Main

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

abbrev orbitSet (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W) : Set W :=
  Set.range fun g : Alt5 => ρ g w₀

@[instance_reducible]
def orbitAction (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W) :
    MulAction Alt5 (↥(orbitSet ρ w₀)) where
  smul g x := ⟨ρ g (x : W), by
    obtain ⟨h, hh⟩ := x.2
    exact ⟨g * h, by
      show ρ (g * h) w₀ = ρ g (x : W)
      change ρ h w₀ = (x : W) at hh
      rw [map_mul, LinearEquiv.mul_apply, hh]⟩⟩
  one_smul x := Subtype.ext (by
    show ρ 1 (x : W) = (x : W)
    simp)
  mul_smul g h x := Subtype.ext (by
    show ρ (g * h) (x : W) = ρ g (ρ h (x : W))
    rw [map_mul, LinearEquiv.mul_apply])

lemma orbit_ncard_of_stab_twelve (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W)
    (hstab : Nat.card {g : Alt5 // ρ g w₀ = w₀} = 12) :
    (orbitSet ρ w₀).ncard = 5 := by
  have hcard : Nat.card (stab ρ w₀) = 12 := (card_stab ρ w₀).trans hstab
  have hmul : Nat.card (stab ρ w₀) * (stab ρ w₀).index = 60 := by
    rw [Subgroup.card_mul_index, card_alt5]
  rw [hcard] at hmul
  have hidx : (stab ρ w₀).index = 5 := by omega
  rw [orbit_ncard_eq_index, hidx]

lemma exists_orbit_hom (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W)
    (hO : (orbitSet ρ w₀).ncard = 5) :
    ∃ (b : Fin 5 ≃ ↥(orbitSet ρ w₀)) (η : Alt5 →* Equiv.Perm (Fin 5)),
      ∀ g i, ρ g ((b i : ↥(orbitSet ρ w₀)) : W) = ((b (η g i) : ↥(orbitSet ρ w₀)) : W) := by
  classical
  letI : Fintype (↥(orbitSet ρ w₀)) := Fintype.ofFinite _
  letI : MulAction Alt5 (↥(orbitSet ρ w₀)) := orbitAction ρ w₀
  have hbcard : Fintype.card (↥(orbitSet ρ w₀)) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact hO
  let b : Fin 5 ≃ ↥(orbitSet ρ w₀) := (Fintype.equivFinOfCardEq hbcard).symm
  let η : Alt5 →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom b.symm).toMonoidHom.comp (MulAction.toPermHom Alt5 (↥(orbitSet ρ w₀)))
  refine ⟨b, η, ?_⟩
  intro g i
  have hη : (η g) i = b.symm (g • (b i)) := by
    change (b.symm.permCongr (MulAction.toPermHom Alt5 (↥(orbitSet ρ w₀)) g)) i = _
    rw [Equiv.permCongr_apply]
    rfl
  rw [hη, Equiv.apply_symm_apply]
  rfl

lemma eta_ker_le_stab (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W)
    (b : Fin 5 ≃ ↥(orbitSet ρ w₀)) (η : Alt5 →* Equiv.Perm (Fin 5))
    (hb : ∀ g i, ρ g ((b i : ↥(orbitSet ρ w₀)) : W)
      = ((b (η g i) : ↥(orbitSet ρ w₀)) : W)) :
    η.ker ≤ stab ρ w₀ := by
  have hw0O : w₀ ∈ orbitSet ρ w₀ := ⟨1, by simp⟩
  let i₀ : Fin 5 := b.symm ⟨w₀, hw0O⟩
  have hbi₀ : (b i₀ : W) = w₀ := by
    have h1 : (b i₀ : ↥(orbitSet ρ w₀)) = ⟨w₀, hw0O⟩ := by simp [i₀]
    simpa using congrArg Subtype.val h1
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [mem_stab]
  have hfix : (η g) i₀ = i₀ := by rw [hg]; rfl
  have h2 : ρ g (b i₀ : W) = (b i₀ : W) := by
    rw [hb g i₀]
    exact congrArg Subtype.val (congrArg b hfix)
  rwa [hbi₀] at h2

lemma eta_injective_of_stab_twelve (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W)
    (hstab : Nat.card {g : Alt5 // ρ g w₀ = w₀} = 12)
    (η : Alt5 →* Equiv.Perm (Fin 5)) (hker_le : η.ker ≤ stab ρ w₀) :
    Function.Injective η := by
  have hηker_card : Nat.card η.ker ≤ 12 := by
    have hle : Nat.card η.ker ≤ Nat.card (stab ρ w₀) :=
      Nat.card_le_card_of_injective (fun x : η.ker => (⟨(x : Alt5), hker_le x.2⟩ : stab ρ w₀))
        (by intro x y hxy
            exact Subtype.ext (congrArg (fun z : stab ρ w₀ => (z : Alt5)) hxy))
    have hstab' : Nat.card (stab ρ w₀) = 12 := (card_stab ρ w₀).trans hstab
    omega
  have hker_bot : η.ker = ⊥ := by
    haveI : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
    have hne : η.ker ≠ ⊤ := by
      intro htop
      have : Nat.card η.ker = 60 := by rw [htop, Subgroup.card_top, card_alt5]
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal η.ker with h | h
    · exact h
    · exact absurd h hne
  exact (MonoidHom.ker_eq_bot_iff η).mp hker_bot

lemma eta_range_le_alternating (η : Alt5 →* Equiv.Perm (Fin 5)) :
    η.range ≤ alternatingGroup (Fin 5) := by
  intro x hx
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [Equiv.Perm.mem_alternatingGroup]
  have hker : (Equiv.Perm.sign.comp η).ker = ⊤ := by
    have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp η)
    rwa [commutator_alternatingGroup_eq_top (by simp : 5 ≤ Nat.card (Fin 5)),
      top_le_iff] at h
  have hgker : g ∈ (Equiv.Perm.sign.comp η).ker := by
    rw [hker]; exact Subgroup.mem_top g
  simpa using MonoidHom.mem_ker.mp hgker

lemma eta_range_eq_alternating (η : Alt5 →* Equiv.Perm (Fin 5))
    (hηinj : Function.Injective η) : η.range = alternatingGroup (Fin 5) := by
  refine Subgroup.eq_of_le_of_card_ge (eta_range_le_alternating η) ?_
  have hcard : Nat.card η.range = 60 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hηinj, Subgroup.card_top, card_alt5]
  rw [card_alt5, hcard]

lemma exists_equivariant_map (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w₀ : W)
    (b : Fin 5 ≃ ↥(orbitSet ρ w₀)) (η : Alt5 →* Equiv.Perm (Fin 5))
    (hb : ∀ g i, ρ g ((b i : ↥(orbitSet ρ w₀)) : W)
      = ((b (η g i) : ↥(orbitSet ρ w₀)) : W)) :
    ∃ F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W,
      (∀ i, F (Pi.single i (1 : ZMod 2) : Fin 5 → ZMod 2) = (b i : W)) ∧
      ∀ g v, ρ g (F v) = F (fun i => v ((η g)⁻¹ i)) :=
  ⟨linComb (fun i => (b i : W)), fun i => linComb_single _ i,
    fun g v => linComb_equivariant _ ρ η g (fun i => hb g i) v⟩

lemma range_eq_top_of_equivariant_map (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (hW : Nat.card W = 16)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0) {w₀ : W} (hw₀ : w₀ ≠ 0)
    (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W) (η : Alt5 →* Equiv.Perm (Fin 5))
    (hF_equiv : ∀ g v, ρ g (F v) = F (fun i => v ((η g)⁻¹ i)))
    (hw0mem : w₀ ∈ LinearMap.range F) : LinearMap.range F = ⊤ := by
  have hInvRange : ∀ g, (LinearMap.range F).map (ρ g : W →ₗ[ZMod 2] W) ≤ LinearMap.range F := by
    intro g y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨v, rfl⟩ := hx
    exact ⟨fun i => v ((η g)⁻¹ i), (hF_equiv g v).symm⟩
  have hRange_bot : LinearMap.range F ≠ ⊥ := by
    intro hbot
    have := hw0mem
    rw [hbot, Submodule.mem_bot] at this
    exact hw₀ this
  exact (invariant_eq_bot_or_top ρ hW h0 (LinearMap.range F) hInvRange).resolve_left hRange_bot

def onesVec : Fin 5 → ZMod 2 := fun _ => 1

lemma onesVec_ne_zero : onesVec ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [onesVec] at this

lemma onesVec_mem_kernel (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W))
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (η : Alt5 →* Equiv.Perm (Fin 5))
    (hF_equiv : ∀ g v, ρ g (F v) = F (fun i => v ((η g)⁻¹ i))) :
    onesVec ∈ LinearMap.ker F := by
  rw [LinearMap.mem_ker]
  apply h0
  intro g
  rw [hF_equiv g]
  exact congrArg F (funext fun i => by simp [onesVec])

lemma kernel_card_two (hW : Nat.card W = 16) (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (hsurj : Function.Surjective F) : Nat.card (LinearMap.ker F) = 2 := by
  change Nat.card (AddMonoidHom.ker (F : (Fin 5 → ZMod 2) →+ W)) = 2
  have hM : Nat.card (Fin 5 → ZMod 2) = 32 := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  have h := AddSubgroup.card_ker_mul_card_of_surjective
    (f := (F : (Fin 5 → ZMod 2) →+ W)) hsurj
  rw [hM, hW] at h
  omega

lemma kernel_mem_zero_or_ones (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (hW : Nat.card W = 16)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (η : Alt5 →* Equiv.Perm (Fin 5))
    (hF_equiv : ∀ g v, ρ g (F v) = F (fun i => v ((η g)⁻¹ i)))
    (hFtop : LinearMap.range F = ⊤) :
    ∀ v, v ∈ LinearMap.ker F → v = 0 ∨ v = onesVec := by
  classical
  have hker_card : Nat.card (LinearMap.ker F) = 2 :=
    kernel_card_two hW F (LinearMap.range_eq_top.mp hFtop)
  have hones_mem : onesVec ∈ LinearMap.ker F := onesVec_mem_kernel ρ h0 F η hF_equiv
  intro v hv
  have hfilter_card :
      (Finset.univ.filter (fun v : Fin 5 → ZMod 2 => v ∈ LinearMap.ker F)).card = 2 := by
    rw [← Fintype.card_subtype (fun v : Fin 5 → ZMod 2 => v ∈ LinearMap.ker F),
      ← Nat.card_eq_fintype_card]
    exact hker_card
  have hsub : ({0, onesVec} : Finset (Fin 5 → ZMod 2)) ⊆
      Finset.univ.filter (fun v : Fin 5 → ZMod 2 => v ∈ LinearMap.ker F) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (LinearMap.ker F).zero_mem
    · exact hones_mem
  have hpair : ({0, onesVec} : Finset (Fin 5 → ZMod 2)).card = 2 := by
    rw [Finset.card_pair]
    exact fun h => onesVec_ne_zero h.symm
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hpair, hfilter_card])
  have hv' : v ∈ ({0, onesVec} : Finset (Fin 5 → ZMod 2)) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  simpa [Finset.mem_insert, Finset.mem_singleton] using hv'

@[expose] def coreModHom (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W) :
    CFSG.Quasithin.G6.coreMod 5 →* Multiplicative W :=
  { toFun := fun x => Multiplicative.ofAdd
      (F (Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5)))
    map_one' := by
      show Multiplicative.ofAdd (F (Multiplicative.toAdd
        ((1 : CFSG.Quasithin.G6.coreMod 5) : CFSG.Quasithin.G6.PermMod 5))) = 1
      rw [show Multiplicative.toAdd ((1 : CFSG.Quasithin.G6.coreMod 5) :
        CFSG.Quasithin.G6.PermMod 5) = 0 from rfl, map_zero]
      rfl
    map_mul' := by
      intro x y
      show Multiplicative.ofAdd (F (Multiplicative.toAdd
          (((x * y : CFSG.Quasithin.G6.coreMod 5) : CFSG.Quasithin.G6.PermMod 5)))) =
        Multiplicative.ofAdd (F (Multiplicative.toAdd
          (x : CFSG.Quasithin.G6.PermMod 5))) *
        Multiplicative.ofAdd (F (Multiplicative.toAdd
          (y : CFSG.Quasithin.G6.PermMod 5)))
      rw [Subgroup.coe_mul, toAdd_mul, map_add, ofAdd_add] }

@[simp]
lemma coreModHom_apply (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (x : CFSG.Quasithin.G6.coreMod 5) :
    coreModHom F x = Multiplicative.ofAdd
      (F (Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5))) := rfl

lemma coreModHom_injective (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (hker : ∀ v, v ∈ LinearMap.ker F → v = 0 ∨ v = onesVec) :
    Function.Injective (coreModHom F) := by
  intro x y hxy
  have hxyeq : F (Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5)) =
      F (Multiplicative.toAdd (y : CFSG.Quasithin.G6.PermMod 5)) := by
    have := congrArg Multiplicative.toAdd hxy
    simpa [toAdd_ofAdd] using this
  have hF : F (Multiplicative.toAdd
      (((x * y⁻¹ : CFSG.Quasithin.G6.coreMod 5) : CFSG.Quasithin.G6.PermMod 5))) = 0 := by
    have hsplit : Multiplicative.toAdd
        (((x * y⁻¹ : CFSG.Quasithin.G6.coreMod 5) : CFSG.Quasithin.G6.PermMod 5)) =
        Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5) -
        Multiplicative.toAdd (y : CFSG.Quasithin.G6.PermMod 5) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv]
      abel
    rw [hsplit, map_sub, hxyeq, sub_self]
  have hsum := CFSG.Quasithin.G6.mem_coreMod.mp (x * y⁻¹).2
  rcases hker _ hF with h | h
  · have hxy1 : (x * y⁻¹ : CFSG.Quasithin.G6.coreMod 5) = 1 := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [h]
      rfl
    exact mul_inv_eq_one.mp hxy1
  · rw [h] at hsum
    simp only [onesVec] at hsum
    exact absurd hsum (by decide)

lemma coreModHom_bijective (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (hker : ∀ v, v ∈ LinearMap.ker F → v = 0 ∨ v = onesVec)
    (hcore : Nat.card (CFSG.Quasithin.G6.coreMod 5) = 16) (hW : Nat.card W = 16) :
    Function.Bijective (coreModHom F) := by
  have hcard : Nat.card (CFSG.Quasithin.G6.coreMod 5) = Nat.card (Multiplicative W) := by
    rw [hcore, Nat.card_congr Multiplicative.toAdd, hW]
  exact (Nat.bijective_iff_injective_and_card (coreModHom F)).mpr
    ⟨coreModHom_injective F hker, hcard⟩

lemma coreModHom_coreAct (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W)
    (η : Alt5 →* Equiv.Perm (Fin 5))
    (hF_equiv : ∀ g v, ρ g (F v) = F (fun i => v ((η g)⁻¹ i)))
    (g : Alt5) (x : CFSG.Quasithin.G6.coreMod 5) :
    coreModHom F (CFSG.Quasithin.G6.coreAct 5 (η g) x) =
      Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (coreModHom F x))) := by
  have hL : coreModHom F (CFSG.Quasithin.G6.coreAct 5 (η g) x) =
      Multiplicative.ofAdd (F (fun i => Multiplicative.toAdd
        (x : CFSG.Quasithin.G6.PermMod 5) ((η g)⁻¹ i))) := by
    change Multiplicative.ofAdd (F (Multiplicative.toAdd
      ((CFSG.Quasithin.G6.coreAct 5 (η g) x : CFSG.Quasithin.G6.coreMod 5) :
        CFSG.Quasithin.G6.PermMod 5))) = _
    have h2 : Multiplicative.toAdd
        ((CFSG.Quasithin.G6.coreAct 5 (η g) x : CFSG.Quasithin.G6.coreMod 5) :
          CFSG.Quasithin.G6.PermMod 5) =
        fun i => Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5) ((η g)⁻¹ i) := by
      rw [CFSG.Quasithin.G6.coreAct_coe]
      funext i
      rw [CFSG.Quasithin.G6.permAct_apply]
    rw [h2]
  have hR : Multiplicative.toAdd (coreModHom F x) =
      F (Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5)) := by
    change Multiplicative.toAdd (Multiplicative.ofAdd
      (F (Multiplicative.toAdd (x : CFSG.Quasithin.G6.PermMod 5)))) = _
    rw [toAdd_ofAdd]
  rw [hL, hR, hF_equiv]

theorem a5_module_iso (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    (hW : Nat.card W = 16) (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hd : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Nat.card {w : W // ρ g w = w} = 4) :
    ∃ (η : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (Fin 5))
      (f : CFSG.Quasithin.G6.coreMod 5 ≃* Multiplicative W),
      Function.Injective η ∧ η.range = alternatingGroup (Fin 5) ∧
      ∀ (g : ↥(alternatingGroup (Fin 5))) (x : CFSG.Quasithin.G6.coreMod 5),
        f (CFSG.Quasithin.G6.coreAct 5 (η g) x) =
          Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (f x))) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  obtain ⟨w₀, hw₀, hstab12⟩ := a5_exists_vector_stab_twelve W ρ hW h0 hd
  have hOcard := orbit_ncard_of_stab_twelve ρ w₀ hstab12
  obtain ⟨b, η, hb⟩ := exists_orbit_hom ρ w₀ hOcard
  have hηker_le := eta_ker_le_stab ρ w₀ b η hb
  have hηinj := eta_injective_of_stab_twelve ρ w₀ hstab12 η hηker_le
  have hηrange := eta_range_eq_alternating η hηinj
  obtain ⟨F, hF_single, hF_equiv⟩ := exists_equivariant_map ρ w₀ b η hb
  let i₀ : Fin 5 := b.symm ⟨w₀, ⟨1, by simp⟩⟩
  have hbi₀ : (b i₀ : W) = w₀ := by
    have h1 : (b i₀ : ↥(orbitSet ρ w₀)) = ⟨w₀, ⟨1, by simp⟩⟩ := by simp [i₀]
    simpa using congrArg Subtype.val h1
  have hw0mem : w₀ ∈ LinearMap.range F := ⟨Pi.single i₀ 1, by rw [hF_single i₀, hbi₀]⟩
  have hFtop := range_eq_top_of_equivariant_map ρ hW h0 hw₀ F η hF_equiv hw0mem
  have hker := kernel_mem_zero_or_ones ρ hW h0 F η hF_equiv hFtop
  have hcore : Nat.card (CFSG.Quasithin.G6.coreMod 5) = 16 := by
    have h := CFSG.CGT.PushingUpLit.BHS.card_coreMod_mul_two (n := 5) (by decide)
    omega
  have hbij := coreModHom_bijective F hker hcore hW
  let f : CFSG.Quasithin.G6.coreMod 5 ≃* Multiplicative W :=
    MulEquiv.ofBijective (coreModHom F) hbij
  exact ⟨η, f, hηinj, hηrange, fun g x => coreModHom_coreAct ρ F η hF_equiv g x⟩

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
