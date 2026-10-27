module

public import CFSG.Quasithin.EmptyFaithful.S153NBa4
public import CFSG.Quasithin.EmptyFaithful.S153NBb6
public import CFSG.Quasithin.EmptyFaithful.S153NBcRank
public import CFSG.Quasithin.EmptyFaithful.S153NBcO2
public import CFSG.Quasithin.EmptyFaithful.S153NBdFrat
public import CFSG.Quasithin.EmptyFaithful.S153NBdIdx
public import CFSG.Quasithin.EmptyFaithful.S153NMTop
public import CFSG.Quasithin.Background.S1567Z5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

theorem input15367Inspect_of_module (h113 : StageLemma14113) (hM : S153N.Input15367Module) :
    Input15367Inspect := by
  intro G _ _ T Mc M V₁ V₂ E t k hcount hex hH3 h3 hN
  obtain ⟨F⟩ := S153N.formHyp_of_ctx67 h113 k hcount
  obtain ⟨W, hcg, hfin, φ, w, hW, hker, hw1, hgen, hstab, hoff⟩ := S153N.bridge_forms_of_formHyp F
  have hAC : ∀ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A →
      A ≤ Subgroup.centralizer (E : Set G) := fun A hA =>
    (((le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ (TE153 T E)).trans
      (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66)).trans
        (Subgroup.centralizer_le k.L.le_V))
  have h3' : ¬ 3 ∣ Nat.card ↥(S153N.stabAt φ.range w) := by
    intro hdvd
    apply h3
    refine hdvd.trans ?_
    let ψ : ↥(M ⊓ Subgroup.centralizer (E : Set G)) →* ↥(S153N.stabAt φ.range w) :=
      ((φ.comp (Subgroup.inclusion (inf_le_right : M ⊓ Subgroup.centralizer (E : Set G) ≤
        Subgroup.centralizer (E : Set G)))).codRestrict (S153N.stabAt φ.range w) (fun c =>
          ⟨⟨_, rfl⟩, (S153N.mem_stabAt.1 ((hstab _).2 c.2.1)).2⟩))
    have hψ : Function.Surjective ψ := by
      rintro ⟨g, hg⟩
      obtain ⟨hgr, hgw⟩ := S153N.mem_stabAt.1 hg
      obtain ⟨c, rfl⟩ := hgr
      have hcM : (c : G) ∈ M := (hstab c).1 hg
      exact ⟨⟨c, hcM, c.2⟩, rfl⟩
    exact Subgroup.card_dvd_of_surjective hψ
  let 𝒪 : Set (Subgroup (MulAut W)) := {B | ∃ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A ∧
    B = (A.subgroupOf (Subgroup.centralizer (E : Set G))).map φ}
  have hD : S153N.Insp67Data φ.range w 𝒪 :=
    { sqtk := S153N.bridgeC_sqtk h113 k φ
      o2 := S153N.bridgeC_o2 h113 k φ hker hH3
      rank3 := S153N.bridgeC_rank h113 k φ hker h3
      w_ne := hw1
      gen := hgen
      three_prime := h3'
      offender := by
        rintro B ⟨A, hA, rfl⟩
        obtain ⟨hel, hle⟩ := hoff A hA
        exact ⟨Subgroup.map_le_range _ _, hel, hle⟩
      nontrivial := by
        obtain ⟨A, hA, hAK⟩ := hex
        refine ⟨_, ⟨A, hA, rfl⟩, ?_⟩
        intro hbot
        apply hAK
        intro a ha
        have haC : a ∈ Subgroup.centralizer (E : Set G) := hAC A hA ha
        have h1 : φ ⟨a, haC⟩ ∈ (A.subgroupOf (Subgroup.centralizer (E : Set G))).map φ :=
          ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
        rw [hbot] at h1
        have h2 : (⟨a, haC⟩ : ↥(Subgroup.centralizer (E : Set G))) ∈ φ.ker :=
          (Subgroup.mem_bot).1 h1
        rw [hker, Subgroup.mem_subgroupOf] at h2
        exact h2
      frattini := fun N hNle hNn hAll =>
        S153N.bridgeD_frattini h113 k hN φ hker w hstab N hNle hNn
          (fun A hA => hAll _ ⟨A, hA, rfl⟩) }
  rw [S153N.bridgeD_relIndex h113 k φ hker w hstab]
  exact hM W hW φ.range w 𝒪 hD

theorem input15367Inspect_holds
    (h113 : StageLemma14113) (h56 : AsB56) : Input15367Inspect :=
  input15367Inspect_of_module h113 (S153N.input15367Module_of_b56 h56)

end CFSG.Quasithin
