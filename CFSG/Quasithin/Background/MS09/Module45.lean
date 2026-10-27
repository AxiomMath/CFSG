module

public import CFSG.Quasithin.Background.MS09.Minimal
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B6

namespace Mod

variable {P : Type} [Group P] {V : Type} [CommGroup V] (ρ : P →* MulAut V)

@[expose] def fixIn (K : Subgroup P) (U : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ g ∈ K, ρ g u = u}
  one_mem' := ⟨U.one_mem, fun g _ => map_one (ρ g)⟩
  mul_mem' := fun ha hb =>
    ⟨U.mul_mem ha.1 hb.1, fun g hg => by rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
  inv_mem' := fun ha => ⟨U.inv_mem ha.1, fun g hg => by rw [map_inv, ha.2 g hg]⟩

@[expose] def stabIn (U : Subgroup V) : Subgroup P where
  carrier := {g | ∀ u, ρ g u ∈ U ↔ u ∈ U}
  one_mem' := fun u => by simp
  mul_mem' := fun {a b} ha hb u => by rw [map_mul, MulAut.mul_apply, ha, hb]
  inv_mem' := fun {g} hg u => by
    have := hg (ρ g⁻¹ u)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
    exact this.symm

@[expose] def cenIn (U : Subgroup V) : Subgroup P where
  carrier := {g | ∀ u ∈ U, ρ g u = u}
  one_mem' := fun u _ => by simp
  mul_mem' := fun {a b} ha hb u hu => by rw [map_mul, MulAut.mul_apply, hb u hu, ha u hu]
  inv_mem' := fun {g} hg u hu => by
    have := congrArg (ρ g⁻¹) (hg u hu)
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
      eq_comm] at this

@[expose] def fixer (v : V) : Subgroup P where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show ρ (a * b) v = v
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' := fun {g} hg => by
    show ρ g⁻¹ v = v
    have := congrArg (ρ g⁻¹) hg
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
      eq_comm] at this

@[expose] def commIn (c : P) (U : Subgroup V) : Subgroup V :=
  U.map ((ρ c).toMonoidHom / MonoidHom.id V)

variable {ρ}

theorem mem_fixIn {K : Subgroup P} {U : Subgroup V} {u : V} :
    u ∈ fixIn ρ K U ↔ u ∈ U ∧ ∀ g ∈ K, ρ g u = u := Iff.rfl

theorem mem_cenIn {U : Subgroup V} {g : P} : g ∈ cenIn ρ U ↔ ∀ u ∈ U, ρ g u = u := Iff.rfl

theorem mem_commIn {c : P} {U : Subgroup V} {w : V} :
    w ∈ commIn ρ c U ↔ ∃ u ∈ U, ρ c u * u⁻¹ = w := by
  simp [commIn, Subgroup.mem_map, MonoidHom.div_apply, div_eq_mul_inv]

theorem fixIn_le (K : Subgroup P) (U : Subgroup V) : fixIn ρ K U ≤ U := fun _ h => h.1

theorem fixIn_anti {K K' : Subgroup P} (h : K ≤ K') (U : Subgroup V) :
    fixIn ρ K' U ≤ fixIn ρ K U := fun _ hu => ⟨hu.1, fun g hg => hu.2 g (h hg)⟩

theorem le_fixer_of_mem_fixIn {K : Subgroup P} {U : Subgroup V} {u : V}
    (hu : u ∈ fixIn ρ K U) : K ≤ fixer ρ u := fun g hg => hu.2 g hg

theorem mem_fixIn_of_le_fixer {K : Subgroup P} {U : Subgroup V} {u : V} (hu : u ∈ U)
    (h : K ≤ fixer ρ u) : u ∈ fixIn ρ K U := ⟨hu, fun g hg => h hg⟩

theorem mem_stabIn_of [Finite V] {g : P} {U : Subgroup V} (h : ∀ u ∈ U, ρ g u ∈ U) :
    g ∈ stabIn ρ U := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  let f : U → U := fun x => ⟨ρ g x, h x x.2⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext ((ρ g).injective (congrArg Subtype.val hxy))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hf ⟨ρ g u, hu⟩
  have hxu : (x : V) = u := (ρ g).injective (congrArg Subtype.val hx)
  exact hxu ▸ x.2

theorem mem_of_mem_stabIn {g : P} {U : Subgroup V} (hg : g ∈ stabIn ρ U) {u : V} (hu : u ∈ U) :
    ρ g u ∈ U := (hg u).mpr hu

theorem commIn_le {c : P} {U : Subgroup V} (hc : c ∈ stabIn ρ U) : commIn ρ c U ≤ U := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_commIn.mp hw
  exact U.mul_mem (mem_of_mem_stabIn hc hu) (U.inv_mem hu)

theorem le_stabIn_of_le_cenIn [Finite V] {K : Subgroup P} {U : Subgroup V}
    (h : K ≤ cenIn ρ U) : K ≤ stabIn ρ U := fun g hg =>
  mem_stabIn_of fun u hu => by rw [h hg u hu]; exact hu

theorem apply_conj (l g : P) (v : V) :
    ρ (l⁻¹ * g * l) ((ρ l)⁻¹ v) = (ρ l)⁻¹ (ρ g v) := by
  simp [map_mul, map_inv, MulAut.mul_apply]

theorem apply_conj' (l g : P) (v : V) : ρ (l * g * l⁻¹) (ρ l v) = ρ l (ρ g v) := by
  simp [map_mul, map_inv, MulAut.mul_apply]

theorem map_fixIn {l : P} {A : Subgroup P} {U : Subgroup V} (hl : l ∈ stabIn ρ U) :
    (fixIn ρ A U).map (ρ l).toMonoidHom = fixIn ρ (B6.conjSub l A) U := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
    refine ⟨mem_of_mem_stabIn hl hxU, fun a' ha' => ?_⟩
    have h1 := hxA _ (mem_conjSub.mp ha')
    have e : a' = l * (l⁻¹ * a' * l) * l⁻¹ := by group
    rw [e, apply_conj', h1]
  · rintro ⟨hyU, hyA⟩
    refine ⟨(ρ l)⁻¹ y, ⟨?_, fun a ha => ?_⟩, by simp⟩
    · rw [← map_inv]
      exact mem_of_mem_stabIn ((stabIn ρ U).inv_mem hl) hyU
    · have h1 := hyA (l * a * l⁻¹) (mem_conjSub.mpr (by group; exact ha))
      have e : a = l⁻¹ * (l * a * l⁻¹) * l := by group
      rw [e, apply_conj, h1]

theorem card_map_fixIn {l : P} {A : Subgroup P} {U : Subgroup V} :
    Nat.card ((fixIn ρ A U).map (ρ l).toMonoidHom) = Nat.card (fixIn ρ A U) :=
  Subgroup.card_map_of_injective (ρ l).injective

theorem quad_conjSub {l : P} {A : Subgroup P} {U : Subgroup V} (hl : l ∈ stabIn ρ U)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ u ∈ U, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹) :
    ∀ a ∈ B6.conjSub l A, ∀ b ∈ B6.conjSub l A, ∀ u ∈ U, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹ := by
  intro a ha b hb u hu
  have hw : (ρ l)⁻¹ u ∈ U := by
    rw [← map_inv]
    exact mem_of_mem_stabIn ((stabIn ρ U).inv_mem hl) hu
  have key := hquad _ (mem_conjSub.mp ha) _ (mem_conjSub.mp hb) _ hw
  have e : (ρ l)⁻¹ (ρ b u) * ((ρ l)⁻¹ u)⁻¹ = (ρ l)⁻¹ (ρ b u * u⁻¹) := by
    rw [map_mul, map_inv]
  rw [apply_conj, e, apply_conj] at key
  exact (ρ l)⁻¹.injective key

theorem commIn_le_fixIn {A : Subgroup P} {U : Subgroup V} {c : P} (hc : c ∈ A)
    (hcU : c ∈ stabIn ρ U)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ u ∈ U, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹) :
    commIn ρ c U ≤ fixIn ρ A U := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_commIn.mp hw
  exact ⟨commIn_le hcU hw, fun a ha => hquad a ha c hc u hu⟩

end Mod

namespace Mod

variable {P : Type} [Group P] {V : Type} [CommGroup V] {ρ : P →* MulAut V}

theorem card_sup_mul_card_inf [Finite V] (H K : Subgroup V) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K :=
  (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K fun x _ y _ => mul_comm x y).1

end Mod

namespace Mod

variable {P : Type} [Group P] {V : Type} [CommGroup V] {ρ : P →* MulAut V}

section Setting

variable [Finite P] [Finite V] {L A S L₀ : Subgroup P} {U : Subgroup V}
  (hS : IsSylowTwoOf S L) (hAS : A ⊔ pCoreOf 2 L ≤ S)
  (hmin : IsUniqueMaxSub L (A ⊔ pCoreOf 2 L) L₀)
  (hUL : L ≤ stabIn ρ U) (hO : pCoreOf 2 L ≤ cenIn ρ U)
  (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ u ∈ U, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹)
  (hgen : ∀ W : Subgroup V, W ≤ U → L ≤ stabIn ρ W → fixIn ρ A U ≤ W → W = U)

include hS hAS in
theorem A_le_L : A ≤ L := (le_sup_left.trans hAS).trans hS.1

include hS hAS in
theorem conjSub_A_le {g : P} (hg : g ∈ L) : B6.conjSub g A ≤ L := by
  have := (B6.conjSub g).monotone (A_le_L hS hAS)
  rwa [conjSub_eq_self (Subgroup.le_normalizer hg)] at this

include hS hAS hmin in
theorem le_of_gen {g c : P} (hg : g ∈ L) (hcA : c ∈ A) (hc : c ∉ B6.conjSub g L₀)
    {K : Subgroup P} (h1 : B6.conjSub g A ≤ K) (h2 : c ∈ K) (h3 : pCoreOf 2 L ≤ K) : L ≤ K := by
  have hAL := A_le_L hS hAS
  have hgL : B6.conjSub g L = L := conjSub_eq_self (Subgroup.le_normalizer hg)
  have hgO : B6.conjSub g (pCoreOf 2 L) = pCoreOf 2 L :=
    conjSub_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg)
  have h := hmin.conjSub g
  rw [hgL, (B6.conjSub g).map_sup, hgO] at h
  have heq : B6.conjSub g A ⊔ Subgroup.zpowers c ⊔ pCoreOf 2 L = L :=
    h.eq_of_not_le (sup_le_sup_right le_sup_left _)
      (sup_le (sup_le (conjSub_A_le hS hAS hg) ((Subgroup.zpowers_le).mpr (hAL hcA)))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
      fun hle => hc (hle (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers c))))
  rw [← heq]
  exact sup_le (sup_le h1 (Subgroup.zpowers_le.mpr h2)) h3

include hS hAS hmin hUL hO hquad hgen in
theorem sup_commIn_eq {g c : P} (hg : g ∈ L) (hcA : c ∈ A) (hc : c ∉ B6.conjSub g L₀) :
    fixIn ρ (B6.conjSub g A) U ⊔ commIn ρ c U = U := by
  have hAL := A_le_L hS hAS
  have hcU : c ∈ stabIn ρ U := hUL (hAL hcA)
  have hquad' := quad_conjSub (hUL hg) hquad
  have hWU : fixIn ρ (B6.conjSub g A) U ⊔ commIn ρ c U ≤ U :=
    sup_le (fixIn_le _ _) (commIn_le hcU)
  have hLW : L ≤ stabIn ρ (fixIn ρ (B6.conjSub g A) U ⊔ commIn ρ c U) := by
    refine le_of_gen hS hAS hmin hg hcA hc (fun a' ha' => mem_stabIn_of fun w hw => ?_)
      (mem_stabIn_of fun w hw => ?_) (le_stabIn_of_le_cenIn fun o ho u hu => hO ho u (hWU hu))
    ·
      obtain ⟨u, hu, y, hy, rfl⟩ := Subgroup.mem_sup.mp hw
      have hyU : y ∈ U := commIn_le hcU hy
      have ha'U : a' ∈ stabIn ρ U := hUL (conjSub_A_le hS hAS hg ha')
      have hcy : ρ a' y * y⁻¹ ∈ fixIn ρ (B6.conjSub g A) U :=
        ⟨U.mul_mem (mem_of_mem_stabIn ha'U hyU) (U.inv_mem hyU),
          fun a'' ha'' => hquad' a'' ha'' a' ha' y hyU⟩
      have e : ρ a' (u * y) = (u * (ρ a' y * y⁻¹)) * y := by
        rw [map_mul, hu.2 a' ha']
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ hu hcy))
        (Subgroup.mem_sup_right hy)
    ·
      obtain ⟨u, hu, y, hy, rfl⟩ := Subgroup.mem_sup.mp hw
      have hyU : y ∈ U := commIn_le hcU hy
      have h1 : ρ c u * u⁻¹ ∈ commIn ρ c U := mem_commIn.mpr ⟨u, hu.1, rfl⟩
      have h2 : ρ c y * y⁻¹ ∈ commIn ρ c U := mem_commIn.mpr ⟨y, hyU, rfl⟩
      have e : ρ c (u * y) = (ρ c u * u⁻¹) * u * ((ρ c y * y⁻¹) * y) := by
        rw [map_mul]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
        (Subgroup.mem_sup_left hu)) (Subgroup.mem_sup_right (Subgroup.mul_mem _ h2 hy))
  refine hgen _ hWU hLW fun x hx => ?_
  have hgx : ρ g x ∈ fixIn ρ (B6.conjSub g A) U := by
    rw [← map_fixIn (hUL hg)]
    exact ⟨x, hx, rfl⟩
  exact (hLW hg x).mp (Subgroup.mem_sup_left hgx)

include hS hAS hmin hO in
theorem mem_fixIn_L {g c : P} (hg : g ∈ L) (hcA : c ∈ A) (hc : c ∉ B6.conjSub g L₀) {y : V}
    (hy : y ∈ fixIn ρ (B6.conjSub g A) U) (hcy : ρ c y = y) : y ∈ fixIn ρ L U :=
  mem_fixIn_of_le_fixer hy.1 (le_of_gen hS hAS hmin hg hcA hc (le_fixer_of_mem_fixIn hy) hcy
    fun o ho => hO ho y hy.1)

include hS hAS hmin hUL hO hquad hgen in
theorem card_eq (hAO : ¬ A ≤ pCoreOf 2 L) :
    Nat.card U * Nat.card (fixIn ρ L U) = Nat.card (fixIn ρ A U) * Nat.card (fixIn ρ A U) := by
  have hAL := A_le_L hS hAS
  obtain ⟨a, haA, haO⟩ := SetLike.not_le_iff_exists.mp hAO
  obtain ⟨g, hg, hga⟩ := hmin.exists_not_mem_conjSub hS hAS (hAS (Subgroup.mem_sup_left haA)) haO
  have h := sup_commIn_eq hS hAS hmin hUL hO hquad hgen hg haA hga
  have hU1 : fixIn ρ (B6.conjSub g A) U ⊔ fixIn ρ A U = U := by
    refine le_antisymm (sup_le (fixIn_le _ _) (fixIn_le _ _)) ?_
    calc U = fixIn ρ (B6.conjSub g A) U ⊔ commIn ρ a U := h.symm
      _ ≤ _ := sup_le_sup_left (commIn_le_fixIn haA (hUL (hAL haA)) hquad) _
  have hU2 : fixIn ρ (B6.conjSub g A) U ⊓ fixIn ρ A U = fixIn ρ L U := by
    refine le_antisymm (fun y hy => mem_fixIn_L hS hAS hmin hO hg haA hga hy.1 (hy.2.2 a haA))
      (le_inf (fixIn_anti (conjSub_A_le hS hAS hg) U) (fixIn_anti hAL U))
  have hc := card_sup_mul_card_inf (fixIn ρ (B6.conjSub g A) U) (fixIn ρ A U)
  rw [hU1, hU2, ← map_fixIn (hUL hg), card_map_fixIn] at hc
  exact hc

include hS hAS hmin hUL hO hquad hgen in
theorem commIn_sup_eq (hAO : ¬ A ≤ pCoreOf 2 L) {c : P} (hcA : c ∈ A)
    (hcO : c ∉ pCoreOf 2 L) : commIn ρ c U ⊔ fixIn ρ L U = fixIn ρ A U := by
  have hAL := A_le_L hS hAS
  obtain ⟨g, hg, hgc⟩ := hmin.exists_not_mem_conjSub hS hAS (hAS (Subgroup.mem_sup_left hcA)) hcO
  have hcX : commIn ρ c U ≤ fixIn ρ A U := commIn_le_fixIn hcA (hUL (hAL hcA)) hquad
  have hDX : fixIn ρ L U ≤ fixIn ρ A U := fixIn_anti hAL U
  have hDXg : fixIn ρ L U ≤ fixIn ρ (B6.conjSub g A) U := fixIn_anti (conjSub_A_le hS hAS hg) U
  have hle : commIn ρ c U ⊔ fixIn ρ L U ≤ fixIn ρ A U := sup_le hcX hDX
  have h := sup_commIn_eq hS hAS hmin hUL hO hquad hgen hg hcA hgc
  have hU1 : fixIn ρ (B6.conjSub g A) U ⊔ (commIn ρ c U ⊔ fixIn ρ L U) = U := by
    refine le_antisymm (sup_le (fixIn_le _ _) (hle.trans (fixIn_le _ _))) ?_
    calc U = fixIn ρ (B6.conjSub g A) U ⊔ commIn ρ c U := h.symm
      _ ≤ _ := sup_le_sup_left le_sup_left _
  have hU2 : fixIn ρ (B6.conjSub g A) U ⊓ (commIn ρ c U ⊔ fixIn ρ L U) = fixIn ρ L U := by
    refine le_antisymm (fun y hy => ?_) (le_inf hDXg le_sup_right)
    obtain ⟨w, hw, d, hd, rfl⟩ := Subgroup.mem_sup.mp hy.2
    have hwXg : w ∈ fixIn ρ (B6.conjSub g A) U := by
      have : w = w * d * d⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hy.1 (Subgroup.inv_mem _ (hDXg hd))
    have hwc : ρ c w = w := (hcX hw).2 c hcA
    exact Subgroup.mul_mem _ (mem_fixIn_L hS hAS hmin hO hg hcA hgc hwXg hwc) hd
  have hc := card_sup_mul_card_inf (fixIn ρ (B6.conjSub g A) U) (commIn ρ c U ⊔ fixIn ρ L U)
  rw [hU1, hU2, ← map_fixIn (hUL hg), card_map_fixIn] at hc
  have h2 := card_eq hS hAS hmin hUL hO hquad hgen hAO
  have hpos : 0 < Nat.card (fixIn ρ A U) := Nat.card_pos
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h3 : Nat.card (fixIn ρ A U) * Nat.card ↥(commIn ρ c U ⊔ fixIn ρ L U) =
      Nat.card (fixIn ρ A U) * Nat.card (fixIn ρ A U) := by
    rw [← hc, h2]
  exact (Nat.eq_of_mul_eq_mul_left hpos h3).ge

include hS hAS hmin hUL hO hquad hgen in
theorem mem_of_comm_mem (hAO : ¬ A ≤ pCoreOf 2 L) {c : P} (hcA : c ∈ A)
    (hcO : c ∉ pCoreOf 2 L) {x : V} (hxU : x ∈ U) (hx : ρ c x * x⁻¹ ∈ fixIn ρ L U) :
    x ∈ fixIn ρ A U := by
  have hAL := A_le_L hS hAS
  set f : V →* V := (ρ c).toMonoidHom / MonoidHom.id V with hf
  have hfx : ∀ v, f v = ρ c v * v⁻¹ := fun v => by
    simp [hf, MonoidHom.div_apply, div_eq_mul_inv]
  set D := fixIn ρ L U with hD
  set X := fixIn ρ A U with hX
  set K := (D.comap f) ⊓ U with hK
  have hXK : X ≤ K := fun y hy => ⟨by
    show f y ∈ D
    rw [hfx, hy.2 c hcA, mul_inv_cancel]
    exact D.one_mem, hy.1⟩
  have hDX : D ≤ X := fixIn_anti hAL U
  have h1 := Subgroup.relIndex_mul_card (D.comap f) U
  rw [Subgroup.relIndex_comap] at h1
  have h2 := Subgroup.relIndex_mul_card D (U.map f)
  have h3 := card_sup_mul_card_inf (U.map f) D
  have hcomm : U.map f = commIn ρ c U := rfl
  rw [hcomm, commIn_sup_eq hS hAS hmin hUL hO hquad hgen hAO hcA hcO] at h3
  rw [hcomm] at h1 h2
  have h4 := card_eq hS hAS hmin hUL hO hquad hgen hAO
  set r := D.relIndex (commIn ρ c U) with hr
  have hipos : 0 < Nat.card ↥(D ⊓ commIn ρ c U) := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have h5 : r * Nat.card D = Nat.card X := by
    have e : r * Nat.card ↥(D ⊓ commIn ρ c U) * Nat.card D =
        Nat.card X * Nat.card ↥(D ⊓ commIn ρ c U) := by
      rw [h2, ← h3, inf_comm]
    have e' : (r * Nat.card D) * Nat.card ↥(D ⊓ commIn ρ c U) =
        Nat.card X * Nat.card ↥(D ⊓ commIn ρ c U) := by
      rw [← e]
      ring
    exact Nat.eq_of_mul_eq_mul_right hipos e'
  have h6 : Nat.card U = r * Nat.card X := by
    have e : Nat.card U * Nat.card D = (r * Nat.card X) * Nat.card D := by
      rw [h4, ← h5]
      ring
    exact Nat.eq_of_mul_eq_mul_right hDpos e
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, zero_mul] at h5
      omega
    · exact h0
  have hKX : K = X := by
    refine (Subgroup.eq_of_le_of_card_ge hXK ?_).symm
    have e : r * Nat.card K = r * Nat.card X := by rw [← h6, hK, h1]
    exact (Nat.eq_of_mul_eq_mul_left hrpos e).le
  have hxK : x ∈ K := ⟨by show f x ∈ D; rw [hfx]; exact hx, hxU⟩
  rw [hKX] at hxK
  exact hxK

include hS hAS hmin hUL hO hquad hgen in
theorem relIndex_mul_card_fixIn_le (hnt : ¬ A ≤ cenIn ρ U) :
    (A ⊓ cenIn ρ U).relIndex A * Nat.card (fixIn ρ A U) ≤ Nat.card U := by
  have hAL := A_le_L hS hAS
  have hAO : ¬ A ≤ pCoreOf 2 L := fun h => hnt (h.trans hO)
  obtain ⟨a, haA, hac⟩ := SetLike.not_le_iff_exists.mp hnt
  rw [mem_cenIn] at hac
  push Not at hac
  obtain ⟨x₀, hx₀U, hx₀a⟩ := hac
  have hx₀X : x₀ ∉ fixIn ρ A U := fun h => hx₀a (h.2 a haA)
  let φ : ↥A →* V :=
    { toFun := fun c => ρ c x₀ * x₀⁻¹
      map_one' := by simp
      map_mul' := fun c c' => by
        have hq := hquad c c.2 c' c'.2 x₀ hx₀U
        simp only [Subgroup.coe_mul, map_mul, MulAut.mul_apply]
        calc ρ c (ρ c' x₀) * x₀⁻¹ = ρ c ((ρ c' x₀ * x₀⁻¹) * x₀) * x₀⁻¹ := by group
          _ = (ρ c' x₀ * x₀⁻¹) * ρ c x₀ * x₀⁻¹ := by rw [map_mul, hq]
          _ = ρ c x₀ * x₀⁻¹ * (ρ c' x₀ * x₀⁻¹) := by rw [mul_assoc, mul_comm] }
  have hφX : φ.range ≤ fixIn ρ A U := by
    rintro _ ⟨c, rfl⟩
    exact ⟨U.mul_mem (mem_of_mem_stabIn (hUL (hAL c.2)) hx₀U) (U.inv_mem hx₀U),
      fun b hb => hquad b hb c c.2 x₀ hx₀U⟩
  have hker : (fixIn ρ L U).comap φ ≤ (A ⊓ cenIn ρ U).subgroupOf A := by
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    refine ⟨c.2, ?_⟩
    by_cases hcO : (c : P) ∈ pCoreOf 2 L
    · exact hO hcO
    · exact absurd (mem_of_comm_mem hS hAS hmin hUL hO hquad hgen hAO c.2 hcO hx₀U hc) hx₀X
  have h1 : (A ⊓ cenIn ρ U).relIndex A ≤ ((fixIn ρ L U).comap φ).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  rw [Subgroup.index_comap] at h1
  have h2 : (fixIn ρ L U).relIndex φ.range ≤ (fixIn ρ L U).relIndex (fixIn ρ A U) :=
    Subgroup.relIndex_le_of_le_right hφX
      (Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)))
  have h3 : (fixIn ρ L U).relIndex (fixIn ρ A U) * Nat.card (fixIn ρ L U) =
      Nat.card (fixIn ρ A U) := by
    have := Subgroup.relIndex_mul_card (fixIn ρ L U) (fixIn ρ A U)
    rwa [inf_eq_left.mpr (fixIn_anti hAL U)] at this
  have h4 := card_eq hS hAS hmin hUL hO hquad hgen hAO
  have h5 : Nat.card U = (fixIn ρ L U).relIndex (fixIn ρ A U) * Nat.card (fixIn ρ A U) := by
    have hDpos : 0 < Nat.card (fixIn ρ L U) := Nat.card_pos
    have e : Nat.card U * Nat.card (fixIn ρ L U) =
        ((fixIn ρ L U).relIndex (fixIn ρ A U) * Nat.card (fixIn ρ A U)) *
          Nat.card (fixIn ρ L U) := by
      rw [h4, ← h3]
      ring
    exact Nat.eq_of_mul_eq_mul_right hDpos e
  rw [h5]
  exact Nat.mul_le_mul_right _ (h1.trans h2)

end Setting

end Mod

end CFSG.Quasithin.MS09

end
