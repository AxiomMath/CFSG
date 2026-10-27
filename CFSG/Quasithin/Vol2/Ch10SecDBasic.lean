module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.Vol2.Ch10SecDL3
public import CFSG.Quasithin.Vol2.Ch10SecDPerfect
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem isSylowTwoOf_autOn [Finite G] {V P S : Subgroup G} (hSP : IsSylowTwoOf S P)
    (hP : P ≤ Subgroup.normalizer (V : Set G)) : IsSylowTwoOf (autOn S V) (autOn P V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hSP hP

variable {T L I : Subgroup G}

theorem L_le_normalizer_V : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  ((le_conjClosure L T).trans Subgroup.le_normalizer).trans (le_normalizer_conjClosure _ _)

theorem L_le_normalizer_V1 : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  le_normalizer_commutator L_le_normalizer_V

theorem V1_le_V : fsuUL T L I ≤ fsuVM T L I :=
  commutator_le_left_of_le_normalizer L_le_normalizer_V

theorem cV1_eq_bot (hc : fsuCVM T L I = ⊥) : cV1 T L I = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have : (x : G) ∈ fsuCVM T L I := ⟨V1_le_V x.2, hx⟩
  rw [hc, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (Subtype.ext this)

theorem nonempty_l3Data (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) :
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      Nonempty (L3Data (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥) := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  rw [cV1_eq_bot hc] at hnat
  exact ⟨hcomm, hnat.toL3Coord⟩

theorem card_V1 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) :
    Nat.card (fsuUL T L I) = 8 := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have := D.card_U
  rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at this

theorem mem_centralizer_iff_autOn {V S : Subgroup G} (hS : S ≤ Subgroup.normalizer (V : Set G))
    (x : ↥V) : (x : G) ∈ Subgroup.centralizer (S : Set G) ↔ ∀ σ ∈ autOn S V, σ x = x := by
  constructor
  · rintro hx _ ⟨⟨s, hsN⟩, hs, rfl⟩
    apply Subtype.ext
    show s * (x : G) * s⁻¹ = x
    have := (Subgroup.mem_centralizer_iff.mp hx) s (Subgroup.mem_subgroupOf.mp hs)
    rw [this]
    group
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := congrArg Subtype.val (h _ ⟨⟨s, hS hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩)
    have h2 : s * (x : G) * s⁻¹ = x := h1
    calc s * (x : G) = s * (x : G) * s⁻¹ * s := by group
      _ = x * s := by rw [h2]

variable [Finite G]

theorem card_inf_centralizer_of_isSylowTwoOf (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {S : Subgroup G} (hS : IsSylowTwoOf S L) :
    Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (S : Set G)) = 2 := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hLN : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1
  have hSN : S ≤ Subgroup.normalizer (fsuUL T L I : Set G) := hS.1.trans hLN
  have hP8 : Nat.card (autOn S (fsuUL T L I)) = 8 := D.card_sylow (isSylowTwoOf_autOn hS hLN)
  set P' := (autOn S (fsuUL T L I)).comap D.rho with hP'
  have hrange : autOn S (fsuUL T L I) ≤ D.rho.range := fun σ hσ => by
    obtain ⟨γ, hγ⟩ := D.exists_rho (A4.autOn_mono hS.1 hσ)
    exact ⟨γ, hγ⟩
  have hP'8 : Nat.card P' = 8 := by
    rw [← hP8, ← Subgroup.map_comap_eq_self hrange,
      Subgroup.card_map_of_injective D.rho_injective]
  have hfix := L3.card_fix_of_card_eq_eight hP'8
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hfixed : ∀ x : ↥(fsuUL T L I ⊓ Subgroup.centralizer (S : Set G)), ∀ γ ∈ P',
      L3.act γ (Multiplicative.toAdd (D.β ⟨⟨x, x.2.1⟩, trivial⟩)) =
        Multiplicative.toAdd (D.β ⟨⟨x, x.2.1⟩, trivial⟩) := by
    intro x γ hγ
    have h1 := (mem_centralizer_iff_autOn hSN ⟨x, x.2.1⟩).mp x.2.2 (D.rho γ) hγ
    have h2 := D.β_rho γ (⟨x, x.2.1⟩ : ↥(fsuUL T L I)) trivial trivial
    have h3 : (⟨D.rho γ ⟨x, x.2.1⟩, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
        ⟨⟨x, x.2.1⟩, trivial⟩ := Subtype.ext h1
    rw [h3] at h2
    exact (Multiplicative.ofAdd.injective h2).symm
  let f : ↥(fsuUL T L I ⊓ Subgroup.centralizer (S : Set G)) →
      {w : L3.Vec // ∀ γ ∈ P', L3.act γ w = w} :=
    fun x => ⟨Multiplicative.toAdd (D.β ⟨⟨x, x.2.1⟩, trivial⟩), hfixed x⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun w => ?_⟩
    · have h1 := hβinj (Multiplicative.toAdd.injective (congrArg Subtype.val hxy))
      exact Subtype.ext (congrArg
        (fun u : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((u : ↥(fsuUL T L I)) : G)) h1)
    · obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w.1)
      have hC : ((u : ↥(fsuUL T L I)) : G) ∈ Subgroup.centralizer (S : Set G) := by
        refine (mem_centralizer_iff_autOn hSN (u : ↥(fsuUL T L I))).mpr fun σ hσ => ?_
        obtain ⟨γ, hγ⟩ := hrange hσ
        have hγP : γ ∈ P' := by rw [hP', Subgroup.mem_comap, hγ]; exact hσ
        have h2 := D.β_rho γ (u : ↥(fsuUL T L I)) trivial trivial
        have hu' : (⟨(u : ↥(fsuUL T L I)), trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = u := rfl
        rw [hu', hu] at h2
        simp only [toAdd_ofAdd] at h2
        rw [w.2 γ hγP] at h2
        rw [← hu] at h2
        have h4 := hβinj h2
        rw [← hγ]
        exact congrArg Subtype.val h4
      refine ⟨⟨(u : ↥(fsuUL T L I)), (u : ↥(fsuUL T L I)).2, hC⟩, Subtype.ext ?_⟩
      show Multiplicative.toAdd (D.β ⟨⟨_, _⟩, trivial⟩) = w.1
      have hu' : (⟨⟨((u : ↥(fsuUL T L I)) : G), (u : ↥(fsuUL T L I)).2⟩, trivial⟩ :
          ↥(⊤ : Subgroup ↥(fsuUL T L I))) = u := rfl
      rw [hu', hu, toAdd_ofAdd]
  rw [Nat.card_congr (Equiv.ofBijective f hf), hfix]

end CFSG.Quasithin.Vol2.Ch10.SecD
