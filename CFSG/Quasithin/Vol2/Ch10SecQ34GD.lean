module

public import CFSG.Quasithin.Vol2.Ch10SecQ34GB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem comm_pairwise (I : Fin 4 → Subgroup V) :
    Pairwise fun i j : Fin 4 => ∀ x y : V, x ∈ I i → y ∈ I j → Commute x y :=
  fun _ _ _ x y _ _ => Commute.all x y

noncomputable abbrev sumMap (I : Fin 4 → Subgroup V) : (∀ i, ↥(I i)) →* V :=
  Subgroup.noncommPiCoprod (comm_pairwise I)

theorem sumMap_apply (I : Fin 4 → Subgroup V) (x : ∀ i, ↥(I i)) :
    sumMap I x = ∏ i, (x i : V) := by
  rw [sumMap, Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]

variable {I : Fin 4 → Subgroup V} {U : Subgroup V}

theorem sumMap_injective (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 4) (_ : j ≠ i), I j) = ⊥) :
    Function.Injective (sumMap I) := by
  apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
  intro i
  rw [disjoint_iff]
  have h := hind i
  rwa [bot_sup_eq] at h

theorem sumMap_range (hsup : (⊥ ⊔ ⨆ i, I i) = U) : (sumMap I).range = U := by
  rw [Subgroup.noncommPiCoprod_range, ← hsup, bot_sup_eq]

variable {H : Subgroup (MulAut V)} {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}

theorem mul_self_eq_one (hsup : (⊥ ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H (I i) ⊥ π) {u : V}
    (hu : u ∈ U) : u * u = 1 := by
  have hI : ∀ i, ∀ w : ↥(I i), w * w = 1 := by
    intro i w
    obtain ⟨e, -⟩ := B5.exists_linModel (hreal i)
    apply e.injective
    rw [map_mul, map_one, ← ofAdd_toAdd (e w), ← ofAdd_add]
    show Multiplicative.ofAdd (Multiplicative.toAdd (e w) + Multiplicative.toAdd (e w)) =
      Multiplicative.ofAdd 0
    congr 1
    funext k
    show (Multiplicative.toAdd (e w)) k + (Multiplicative.toAdd (e w)) k = 0
    generalize (Multiplicative.toAdd (e w)) k = c
    revert c
    decide
  rw [← sumMap_range hsup] at hu
  obtain ⟨x, rfl⟩ := hu
  rw [← map_mul]
  have : x * x = 1 := funext fun i => hI i (x i)
  rw [this, map_one]

theorem eq_bot_of_centralized (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 4) (_ : j ≠ i), I j) = ⊥)
    (hsup : (⊥ ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H (I i) ⊥ π)
    {S : Subgroup V} (hSU : S ≤ U) (hSH : ∀ h ∈ H, ∀ s ∈ S, h s ∈ S)
    (hSτ : ∀ s ∈ S, ((π tau32 : ↥H) : MulAut V) s = s) : S = ⊥ := by
  have hstab : ∀ (h : ↥H) (i : Fin 4), ∀ w ∈ I i, (h : MulAut V) w ∈ I i :=
    fun h i w hw => (hreal i).2.2.2.1 h w hw
  let act : ↥H → (∀ i, ↥(I i)) → (∀ i, ↥(I i)) :=
    fun h x i => ⟨(h : MulAut V) (x i), hstab h i _ (x i).2⟩
  have hact : ∀ h x, sumMap I (act h x) = (h : MulAut V) (sumMap I x) := by
    intro h x
    rw [sumMap_apply, sumMap_apply, map_prod]
  rw [eq_bot_iff]
  intro s hs
  have hsU : s ∈ (sumMap I).range := by rw [sumMap_range hsup]; exact hSU hs
  obtain ⟨x, hx⟩ := hsU
  suffices hx1 : x = 1 by rw [Subgroup.mem_bot, ← hx, hx1, map_one]
  funext i
  set Si : Subgroup V :=
    ((S.comap (sumMap I)).map (Pi.evalMonoidHom (fun j => ↥(I j)) i)).map (I i).subtype with hSi
  have hSiI : Si ≤ I i := Subgroup.map_subtype_le _
  have hSiinv : XMod.IsInv ↥H Si := by
    rintro h _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨act h y i, ⟨act h y, ?_, rfl⟩, rfl⟩
    show sumMap I (act h y) ∈ S
    rw [hact]
    exact hSH h h.2 _ hy
  rcases (B5.isIrr_of_realizes (by norm_num) (hreal i)).2.2 Si hSiinv bot_le hSiI with h | h
  · have hxi : (x i : V) ∈ Si :=
      ⟨x i, ⟨x, show sumMap I x ∈ S from hx ▸ hs, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hxi
    exact Subtype.ext hxi
  · exfalso
    obtain ⟨w, hw, hτw⟩ := exists_tau_ne (hreal i)
    apply hτw
    rw [← h] at hw
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hw
    have h1 : sumMap I (act (π tau32) y) = sumMap I y := by
      rw [hact]
      exact hSτ _ hy
    exact congrArg Subtype.val (congrFun (sumMap_injective hind h1) i)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
