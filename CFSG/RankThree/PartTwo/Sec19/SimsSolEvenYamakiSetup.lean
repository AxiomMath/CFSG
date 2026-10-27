module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiD

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv

theorem mem_centralizer_self' {G : Type*} [Group G] (z : G) :
    z ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

structure YData {G : Type} [Group G] (z : G) where
  ϑ : ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥Wsub
  ϑ_z : (ϑ ⟨z, mem_centralizer_self' z⟩ : Wr 6) = Wr.allOnes 6

namespace YData

variable {G : Type} [Group G] {z : G} (Y : YData z)

@[expose] noncomputable def ι : ↥Wsub →* G :=
  (Subgroup.centralizer ({z} : Set G)).subtype.comp Y.ϑ.symm.toMonoidHom

theorem ι_injective : Function.Injective Y.ι := fun a b h =>
  Y.ϑ.symm.injective (Subtype.ext h)

theorem ι_mem_C (a : ↥Wsub) : Y.ι a ∈ Subgroup.centralizer ({z} : Set G) := (Y.ϑ.symm a).2

theorem ϑ_ι (a : ↥Wsub) : Y.ϑ ⟨Y.ι a, Y.ι_mem_C a⟩ = a := by
  show Y.ϑ (Y.ϑ.symm a) = a
  exact MulEquiv.apply_symm_apply _ _

theorem ι_ϑ (x : ↥(Subgroup.centralizer ({z} : Set G))) : Y.ι (Y.ϑ x) = x := by
  show ((Y.ϑ.symm (Y.ϑ x) : ↥(Subgroup.centralizer ({z} : Set G))) : G) = x
  rw [MulEquiv.symm_apply_apply]

theorem ι_allOnes : Y.ι ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ = z := by
  have h : (⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ : ↥Wsub) = Y.ϑ ⟨z, mem_centralizer_self' z⟩ :=
    Subtype.ext Y.ϑ_z.symm
  rw [h, ι_ϑ]

@[expose] noncomputable def lift (X : Subgroup (Wr 6)) : Subgroup G := (X.subgroupOf Wsub).map Y.ι

theorem mem_lift {X : Subgroup (Wr 6)} {x : G} :
    x ∈ Y.lift X ↔ ∃ hx : x ∈ Subgroup.centralizer ({z} : Set G), (Y.ϑ ⟨x, hx⟩ : Wr 6) ∈ X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Y.ι_mem_C a, ?_⟩
    rw [Y.ϑ_ι]
    exact ha
  · rintro ⟨hx, hX⟩
    refine ⟨Y.ϑ ⟨x, hx⟩, hX, ?_⟩
    show Y.ι (Y.ϑ ⟨x, hx⟩) = x
    rw [Y.ι_ϑ]

theorem ι_mem_lift {X : Subgroup (Wr 6)} {a : ↥Wsub} (ha : (a : Wr 6) ∈ X) : Y.ι a ∈ Y.lift X :=
  ⟨a, ha, rfl⟩

theorem lift_le_C (X : Subgroup (Wr 6)) : Y.lift X ≤ Subgroup.centralizer ({z} : Set G) :=
  fun _ hx => (Y.mem_lift.mp hx).1

theorem lift_mono {X X' : Subgroup (Wr 6)} (h : X ≤ X') : Y.lift X ≤ Y.lift X' := by
  intro x hx
  obtain ⟨hxC, hX⟩ := Y.mem_lift.mp hx
  exact Y.mem_lift.mpr ⟨hxC, h hX⟩

theorem card_lift {X : Subgroup (Wr 6)} (hX : X ≤ Wsub) : Nat.card (Y.lift X) = Nat.card X := by
  rw [lift, Subgroup.card_map_of_injective Y.ι_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem lift_inf (X X' : Subgroup (Wr 6)) : Y.lift (X ⊓ X') = Y.lift X ⊓ Y.lift X' := by
  ext x
  simp only [Subgroup.mem_inf, mem_lift]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨hx, h1⟩, ⟨hx, h2⟩⟩
  · rintro ⟨⟨hx, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hx, h1, h2⟩

theorem lift_bot : Y.lift ⊥ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨hxC, h⟩ := Y.mem_lift.mp hx
  have h1 : Y.ϑ ⟨x, hxC⟩ = 1 := Subtype.ext ((Subgroup.mem_bot).mp h)
  have h2 := Y.ι_ϑ ⟨x, hxC⟩
  rw [h1, map_one] at h2
  exact h2.symm

theorem lift_sup {X X' : Subgroup (Wr 6)} (hX : X ≤ Wsub) (hX' : X' ≤ Wsub) :
    Y.lift (X ⊔ X') = Y.lift X ⊔ Y.lift X' := by
  rw [lift, lift, lift, Subgroup.subgroupOf_sup hX hX', Subgroup.map_sup]

@[expose] noncomputable def A : Subgroup G := Y.lift SW

@[expose] noncomputable def T : Subgroup G := Y.lift DW

@[expose] noncomputable def U : Subgroup G := Y.lift UW

theorem card_A : Nat.card Y.A = 64 := (Y.card_lift SW_le_Wsub).trans card_SW

theorem card_T : Nat.card Y.T = 512 := (Y.card_lift DW_le_Wsub).trans card_DW

theorem A_le_T : Y.A ≤ Y.T := Y.lift_mono SW_le_DW

theorem A_le_C : Y.A ≤ Subgroup.centralizer ({z} : Set G) := Y.lift_le_C SW

theorem T_le_C : Y.T ≤ Subgroup.centralizer ({z} : Set G) := Y.lift_le_C DW

theorem compl_A : Y.U ≤ Y.T ∧ Y.U ⊓ Y.A = ⊥ ∧ Y.U ⊔ Y.A = Y.T :=
  ⟨Y.lift_mono UW_le_DW, by rw [U, A, ← Y.lift_inf, UW_inf_SW, Y.lift_bot],
    by rw [U, A, T, ← Y.lift_sup (UW_le_DW.trans DW_le_Wsub) SW_le_Wsub, UW_sup_SW]⟩

theorem z_mem_A : z ∈ Y.A := by
  have h : Y.ι ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ ∈ Y.A := Y.ι_mem_lift (show Wr.allOnes 6 ∈ SW by
    rw [show Wr.allOnes 6 = cSp (1, 0) by decide]
    exact cSp_mem_SW _)
  rwa [Y.ι_allOnes] at h

theorem A_comm {a b : G} (ha : a ∈ Y.A) (hb : b ∈ Y.A) : a * b = b * a := by
  obtain ⟨ha', ha⟩ := Y.mem_lift.mp ha
  obtain ⟨hb', hb⟩ := Y.mem_lift.mp hb
  have h := SW_comm ha hb
  have h' : Y.ϑ ⟨a, ha'⟩ * Y.ϑ ⟨b, hb'⟩ = Y.ϑ ⟨b, hb'⟩ * Y.ϑ ⟨a, ha'⟩ := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  exact congrArg Subtype.val (Y.ϑ.injective h')

theorem centralizer_A_le : Subgroup.centralizer (Y.A : Set G) ≤ Y.A := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) z Y.z_mem_A).symm
  refine Y.mem_lift.mpr ⟨hxC, mem_SW_of_commute fun s => ?_⟩
  have hs : Y.ι ⟨cSp s, SW_le_Wsub (cSp_mem_SW s)⟩ ∈ Y.A := Y.ι_mem_lift (cSp_mem_SW s)
  have h1 := (Subgroup.mem_centralizer_iff.mp hx) _ hs
  have h2 : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
      ⟨Y.ι ⟨cSp s, _⟩, Y.ι_mem_C _⟩ = ⟨Y.ι ⟨cSp s, _⟩, Y.ι_mem_C _⟩ * ⟨x, hxC⟩ :=
    Subtype.ext h1.symm
  have h3 := congrArg (fun c => (Y.ϑ c : Wr 6)) h2
  simp only [map_mul, Subgroup.coe_mul] at h3
  have h4 : Y.ϑ ⟨Y.ι ⟨cSp s, SW_le_Wsub (cSp_mem_SW s)⟩, Y.ι_mem_C _⟩ =
      ⟨cSp s, SW_le_Wsub (cSp_mem_SW s)⟩ := Y.ϑ_ι _
  rw [h4] at h3
  exact h3

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
