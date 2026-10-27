module

public import CFSG.Quasithin.Background.ONanE68LieCase1

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Basic

variable {G : Type} [Group G] {T V L : Subgroup G}

theorem isPGroup_two_of_center_eq_bot (h : Subgroup.center ↥L = ⊥) :
    IsPGroup 2 (Subgroup.center ↥L) := by
  intro g
  refine ⟨0, ?_⟩
  have : (g : ↥L) = 1 := Subgroup.mem_bot.1 (h ▸ g.2)
  apply Subtype.ext
  simp [this]

theorem card_sylowBar_of_center_eq_bot (h : Subgroup.center ↥L = ⊥) :
    Nat.card (sylowBar T V L) = Nat.card (pgOf T V L) := by
  have hinj : Function.Injective (piBar L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_piBar, h]
  rw [sylowBar_eq, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe pgOf_le_left).toEquiv

theorem inf_le_borOf_of_bender (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    (hbender : ∀ Y : Subgroup (Bar.Qbar L), sylowBar T V L ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)))
    {X : Subgroup G} (hPX : pgOf T V L ≤ X) (hXL : X ≤ L) (hXne : X ≠ L) :
    X ≤ borOf T V L := by
  have hZX : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ X := fun z hz => hPX (hZ z hz)
  set Y : Subgroup (Bar.Qbar L) := (X.subgroupOf L).map (piBar L) with hY
  have hPY : sylowBar T V L ≤ Y := by
    rw [sylowBar_eq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hPX)
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hXne
    have h1 : Fin257.pre (piBar L) Y = X := pre_img_eq hXL hZX
    rw [htop, Fin257.pre_top] at h1
    exact h1.symm
  intro x hx
  have hxL : x ∈ L := hXL hx
  have hxY : piBar L ⟨x, hxL⟩ ∈ Y := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have := hbender Y hPY hYne hxY
  exact (mem_borOf_iff hZ).2 ⟨hxL, this⟩

end Basic

section Core

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem case_of_rankOne (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ0L : Subgroup.center ↥L = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hdata : E68RankOneData (sylowBar T V L) n)
    (hBM : borOf T V L ≤ M ∨ (Nat.card (pgOf T V L) = 4 ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2))
    (hmodel : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n))
    (hexc : Nat.card (pgOf T V L) = 4 →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 → E68Case5 M V U L) :
    E68Case1 hV T M U L ∨ E68Case5 M V U L := by
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hZ := center_le_sylow h hU hL hZ2
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  rcases hBM with hBM | ⟨h4, hsmall⟩
  · left
    have hPX : pgOf T V L ≤ L ⊓ M :=
      le_inf pgOf_le_left (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
    have hXB : L ⊓ M ≤ borOf T V L :=
      inf_le_borOf_of_bender hZ hdata.bender hPX inf_le_left fun hh => hLM (hh ▸ inf_le_right)
    exact case1_of_borel hInn hmod hV h hU hL hZ2 hBM hXB hn hdata.quot_comm hdata.card_root
      hdata.singer hmodel
  · exact Or.inr (hexc h4 hsmall)

end Core

end E68Proof

end E6

end CFSG.Quasithin
