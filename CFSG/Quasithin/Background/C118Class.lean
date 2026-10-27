module

public import CFSG.Quasithin.Background.C118Partner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNormalHull

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization commutatorElement

structure SeedData (T : Type) [Group T] where
  G : Type
  [grp : Group G]
  [fin : Finite G]
  k : Type
  [fld : Field k]
  [fink : Finite k]
  S : Sylow 2 G
  e : T ≃* ↥(S : Subgroup G)
  ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k
  ψ : Ecore G →* Multiplicative (Fin 2 → k)
  seed : IsSeed S ρ (Ecore G) ψ

namespace SeedData

attribute [instance] SeedData.grp SeedData.fin SeedData.fld SeedData.fink

variable {T : Type} [Group T] (X : SeedData T)

@[expose] def f : T →* X.G := (X.S : Subgroup X.G).subtype.comp X.e.toMonoidHom

theorem f_injective : Function.Injective X.f := fun _ _ h =>
  X.e.injective (Subtype.ext h)

theorem map_top : (⊤ : Subgroup T).map X.f = (X.S : Subgroup X.G) := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact (X.e t).2
  · intro hx
    exact ⟨X.e.symm ⟨x, hx⟩, trivial, by simp [f]⟩

theorem range_f : X.f.range = (X.S : Subgroup X.G) := by
  rw [MonoidHom.range_eq_map, map_top]

theorem comap_map {Y : Subgroup X.G} (hY : Y ≤ X.S) : (Y.comap X.f).map X.f = Y :=
  Subgroup.map_comap_eq_self (by rw [X.range_f]; exact hY)

@[expose] def Fh : Subgroup T := (Fcore X.G).comap X.f

@[expose] def Vh : Subgroup T := (Vmod X.G).comap X.f

@[expose] def Qh : Subgroup T := (CFSG.pCore 2 X.G).comap X.f

@[expose] def Zh : Subgroup T := (Zfix X.S).comap X.f

theorem map_Fh : X.Fh.map X.f = Fcore X.G := X.comap_map (Fcore_le_sylow (S := X.S))

theorem map_Vh : X.Vh.map X.f = Vmod X.G := X.comap_map (Vmod_le_sylow (S := X.S))

theorem map_Qh : X.Qh.map X.f = CFSG.pCore 2 X.G := X.comap_map (core_le_sylow X.S)

theorem map_Zh : X.Zh.map X.f = Zfix X.S := X.comap_map (Zfix_le_sylow (S := X.S))

theorem partnerData :
    PartnerData (⊤ : Subgroup T) X.Qh X.Fh X.Vh X.Zh (Nat.card X.k) := by
  apply PartnerData.of_map X.f_injective
  rw [X.map_top, X.map_Qh, X.map_Fh, X.map_Vh, X.map_Zh]
  exact PartnerData.ofSeed X.seed

theorem card_Fh : Nat.card X.Fh = Nat.card (Fcore X.G) := by
  rw [← Subgroup.card_map_of_injective X.f_injective (K := X.Fh), X.map_Fh]

theorem equiv_injective (β : T ≃* T) : Function.Injective β.toMonoidHom :=
  fun _ _ hab => β.injective (by simpa using hab)

theorem map_top_equiv (φ : T ≃* T) : (⊤ : Subgroup T).map φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr φ.surjective

theorem exists_max [Finite T] (hne : Nonempty (SeedData T)) :
    ∃ X₁ : SeedData T, ∀ X : SeedData T, Nat.card X.Fh ≤ Nat.card X₁.Fh := by
  classical
  obtain ⟨X₀⟩ := hne
  let s : Set ℕ := {n | ∃ X : SeedData T, Nat.card X.Fh = n}
  have hfin : s.Finite := by
    refine (Set.finite_Iic (Nat.card T)).subset ?_
    rintro n ⟨X, rfl⟩
    exact Subgroup.card_le_card_group _
  obtain ⟨a, ⟨X₁, rfl⟩, hmax⟩ := Set.exists_max_image s id hfin ⟨_, X₀, rfl⟩
  exact ⟨X₁, fun X => hmax _ ⟨X, rfl⟩⟩

theorem partnerData_at (X₁ X₂ : SeedData T) (β : T ≃* T) :
    PartnerData (X₂.S : Subgroup X₂.G) ((X₁.Qh.map β.toMonoidHom).map X₂.f)
      ((X₁.Fh.map β.toMonoidHom).map X₂.f) ((X₁.Vh.map β.toMonoidHom).map X₂.f)
      ((X₁.Zh.map β.toMonoidHom).map X₂.f) (Nat.card X₁.k) := by
  have h := (X₁.partnerData.map (equiv_injective β)).map X₂.f_injective
  rwa [map_top_equiv, X₂.map_top] at h

theorem aimg_map_equiv (β : T ≃* T) (Y : Subgroup T) :
    aimg (X.S : Subgroup X.G) (X.e.symm.trans (β.trans X.e)) (Y.map X.f) =
      (Y.map β.toMonoidHom).map X.f := by
  have h1 : Y.map X.f = (Y.map X.e.toMonoidHom).map (X.S : Subgroup X.G).subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, aimg_map_subtype]
  simp only [Subgroup.map_map]
  congr 1
  ext y
  simp [SeedData.f]

theorem exists_conj (α : ↥(X.S : Subgroup X.G) ≃* ↥(X.S : Subgroup X.G)) :
    ∃ β : T ≃* T, α = X.e.symm.trans (β.trans X.e) :=
  ⟨X.e.trans (α.trans X.e.symm), by ext x; simp⟩

@[expose] def cstarT : Subgroup T := ⨆ β : T ≃* T, X.Fh.map β.toMonoidHom

@[expose] def cenT : Subgroup T := ⨆ β : T ≃* T, X.Zh.map β.toMonoidHom

theorem map_cstarT : X.cstarT.map X.f = Cstar X.S := by
  unfold cstarT Cstar
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun β => ?_
    have := X.aimg_map_equiv β X.Fh
    rw [X.map_Fh] at this
    rw [← this]
    exact le_iSup (fun γ : ↥(X.S : Subgroup X.G) ≃* ↥(X.S : Subgroup X.G) =>
      aimg (X.S : Subgroup X.G) γ (Fcore X.G)) _
  · refine iSup_le fun γ => ?_
    obtain ⟨β, rfl⟩ := X.exists_conj γ
    have := X.aimg_map_equiv β X.Fh
    rw [X.map_Fh] at this
    rw [this]
    exact le_iSup (fun β : T ≃* T => (X.Fh.map β.toMonoidHom).map X.f) β

theorem cstarT_eq_of_orbit {X₁ X₂ : SeedData T} (β₀ : T ≃* T)
    (h : X₂.Fh = X₁.Fh.map β₀.toMonoidHom) : X₂.cstarT = X₁.cstarT := by
  unfold cstarT
  rw [h]
  apply le_antisymm
  · refine iSup_le fun β => ?_
    refine le_iSup_of_le (β₀.trans β) (le_of_eq ?_)
    rw [Subgroup.map_map]
    rfl
  · refine iSup_le fun β => ?_
    refine le_iSup_of_le (β₀.symm.trans β) (le_of_eq ?_)
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp

@[expose] def BlockType : Prop :=
  ∃ V' : Subgroup X.G, V' ≤ (X.S : Subgroup X.G) ∧
    (∀ s ∈ (X.S : Subgroup X.G), ∀ x ∈ V', s * x * s⁻¹ ∈ V') ∧
    CFSG.Open.IsElemAbelian 2 V' ∧
    ⁅(X.S : Subgroup X.G), V'⁆ ≤ Subgroup.centralizer ((X.S : Subgroup X.G) : Set X.G) ∧
    (X.S : Subgroup X.G) = CFSG.pCore 2 X.G ⊔ V'

theorem dichotomy [Finite T] (X₁ X₂ : SeedData T) (hmax : Nat.card X₂.Fh ≤ Nat.card X₁.Fh) :
    X₂.BlockType ∨ (X₁.cstarT.map X₂.f).Normal ∨ X₁.cenT.map X₂.f ≤ Subgroup.center X₂.G := by
  classical
  by_cases hblock : ∃ β : T ≃* T, ¬ X₁.Vh.map β.toMonoidHom ≤ X₂.Qh
  · left
    obtain ⟨β, hβ⟩ := hblock
    have hn₁ : NatLike (⊤ : Subgroup T) (X₁.Qh.map β.toMonoidHom) (X₁.Vh.map β.toMonoidHom)
        (X₁.Zh.map β.toMonoidHom) (Nat.card X₁.k) := by
      have := X₁.partnerData.nat.map (equiv_injective β)
      rwa [map_top_equiv] at this
    obtain ⟨-, -, hsup⟩ := hn₁.outside X₂.partnerData.nat hβ
    have hN := (X₁.partnerData_at X₂ β).nat
    refine ⟨(X₁.Vh.map β.toMonoidHom).map X₂.f, hN.V_le, hN.V_normal, hN.V_elem, ?_, ?_⟩
    · refine le_trans hN.comm_le ?_
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr fun s hs => hN.Z_central s hs z hz
    · have := congrArg (Subgroup.map X₂.f) hsup
      rw [Subgroup.map_sup, X₂.map_Qh, X₂.map_top] at this
      exact this.symm
  · push Not at hblock
    have hpd := X₁.partnerData_at X₂
    have hVQ : ∀ β : T ≃* T, (X₁.Vh.map β.toMonoidHom).map X₂.f ≤ CFSG.pCore 2 X₂.G := by
      intro β
      rw [← X₂.map_Qh]
      exact Subgroup.map_mono (hblock β)
    have hFQ : ∀ β : T ≃* T, (X₁.Fh.map β.toMonoidHom).map X₂.f ≤ CFSG.pCore 2 X₂.G :=
      fun β => PartnerData.fp_le_core X₂.seed (hpd β) (hVQ β)
    by_cases horbit : ∃ β₀ : T ≃* T, X₁.Fh.map β₀.toMonoidHom = X₂.Fh
    · right
      left
      obtain ⟨β₀, hβ₀⟩ := horbit
      have hcs : X₂.cstarT = X₁.cstarT := cstarT_eq_of_orbit β₀ hβ₀.symm
      rw [← hcs, X₂.map_cstarT]
      refine (X₂.seed.contained_translates_force_normal_hull ?_).2.1
      intro α
      obtain ⟨β, rfl⟩ := X₂.exists_conj α
      have hVF : Vmod X₂.G ≤ Fcore X₂.G := Vmod_le_Ecore.trans X₂.seed.Ecore_le_Fcore
      calc aimg (X₂.S : Subgroup X₂.G) (X₂.e.symm.trans (β.trans X₂.e)) (Vmod X₂.G)
          ≤ aimg (X₂.S : Subgroup X₂.G) (X₂.e.symm.trans (β.trans X₂.e)) (Fcore X₂.G) :=
            aimg_mono hVF
        _ = (X₂.Fh.map β.toMonoidHom).map X₂.f := by
            rw [← X₂.map_Fh]
            exact X₂.aimg_map_equiv β X₂.Fh
        _ = (X₁.Fh.map (β₀.trans β).toMonoidHom).map X₂.f := by
            rw [← hβ₀]
            simp only [Subgroup.map_map]
            rfl
        _ ≤ CFSG.pCore 2 X₂.G := hFQ (β₀.trans β)
    · right
      right
      unfold cenT
      rw [Subgroup.map_iSup]
      refine iSup_le fun β => ?_
      have hF : ¬ (X₁.Fh.map β.toMonoidHom).map X₂.f ≤ Fcore X₂.G := by
        intro hle
        apply horbit
        refine ⟨β, ?_⟩
        have h1 : X₁.Fh.map β.toMonoidHom ≤ X₂.Fh := by
          rw [← X₂.map_Fh] at hle
          exact (Subgroup.map_le_map_iff_of_injective X₂.f_injective).mp hle
        refine Subgroup.eq_of_le_of_card_ge h1 ?_
        rw [Subgroup.card_map_of_injective (equiv_injective β)]
        exact hmax
      have hZ := PartnerCore.partner_centrality X₂.seed (hpd β).core (hFQ β) hF
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Hone X₂.S ⊔ CFSG.pCore 2 X₂.G := by
        rw [X₂.seed.Hone_sup_core]
        trivial
      obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      have hzj : j * z = z * j := Subgroup.mem_centralizer_iff.mp (hZ hz).2 j hj
      have hzq : q * z = z * q := (hpd β).core.zcentral q (core_le_sylow X₂.S hq) z hz
      calc j * q * z = j * (q * z) := by group
        _ = j * (z * q) := by rw [hzq]
        _ = (j * z) * q := by group
        _ = (z * j) * q := by rw [hzj]
        _ = z * (j * q) := by group

end SeedData

end CFSG.Quasithin
