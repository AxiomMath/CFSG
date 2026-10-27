module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ10
public import CFSG.Quasithin.Background.B15P4Layer2Orbit

public section

namespace CFSG.Quasithin.B15P4

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique
open scoped commutatorElement

universe v

section Main

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem false_of_irreducible_diag [CharP k 2] [Finite V]
    {s : ℕ} (hs : 2 ≤ s) (L : Fin s → Subgroup (V ≃ₗ[k] V))
    (hinj : Function.Injective L) (hq : ∀ i, CFSG.IsQuasisimple ↥(L i))
    (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥)
    (A : Subgroup (V ≃ₗ[k] V)) [hAel : CFSG.IsElementaryAbelian 2 A]
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (L i) = L j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (L i) = L j)
    (hcommV : commGL (⨆ i, L i) ⊤ = ⊤)
    (hirr : IsIrrQuot (MonoidHom.id (V ≃ₗ[k] V)) (⨆ i, L i) ⊤)
    (B : Subgroup (V ≃ₗ[k] V)) (hBA : B ≤ A) (hB0 : B ≠ ⊥)
    (hBfix : ∀ b ∈ B, ∀ i, conjSub b (L i) = L i)
    (hBq : ∀ a ∈ A, ∀ b ∈ B, ∀ v, b (a v - v) = a v - v)
    (hmaxB : ∀ D : Subgroup (V ≃ₗ[k] V), D ≤ B →
      weight (MonoidHom.id (V ≃ₗ[k] V)) D ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) B) : False := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨hAnH, hHA, hperf, hno, hch⟩ := product_facts hs L hinj hq hcomm hperm htrans
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (V ≃ₗ[k] V), H = ⨆ i, L i := ⟨_, rfl⟩
  rw [← hH] at hAnH hHA hperf hno hch hcommV hirr
  have hLle : ∀ i, L i ≤ H := fun i => hH ▸ le_iSup L i
  have hinv : ∀ S : Subgroup (V ≃ₗ[k] V),
      QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) S
        (⊤ : Submodule k V) :=
    fun _ _ _ _ _ => Submodule.mem_top
  have hHA' := hinv (H ⊔ A)
  have hX : H ⊔ A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)) :=
    sup_le Subgroup.le_normalizer hAnH
  have hBle : B ≤ H ⊔ A := hBA.trans le_sup_right
  have hBH : B ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)) := hBA.trans hAnH
  have hinvB : QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) B
      (⊤ : Submodule k V) := hinv B
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥(H ⊔ A) →* ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k]
      (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤)), θ = actW H A ⊤ hAnH hHA' := ⟨_, rfl⟩
  have hθinj : ∀ x : ↥(H ⊔ A), θ x = 1 → (x : V ≃ₗ[k] V) = 1 := by
    intro x hx
    rw [hθ] at hx
    have key := detect_of_trivial_mod (MonoidHom.id (V ≃ₗ[k] V)) H (H ⊔ A) hX hno hch ⊤
      (hinv H) hHA' hcommV x.2 (disp_mem_fix_of_actW_eq_one hAnH hHA' hx)
    apply LinearEquiv.ext
    intro w
    exact key w Submodule.mem_top
  obtain ⟨Lbar, hLbar⟩ : ∃ Lbar : Fin s → Subgroup ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k]
      (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤)), ∀ i, Lbar i = ((L i).subgroupOf (H ⊔ A)).map θ :=
    ⟨fun i => ((L i).subgroupOf (H ⊔ A)).map θ, fun i => rfl⟩
  obtain ⟨Abar, hAbar⟩ : ∃ Abar : Subgroup ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k]
      (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤)), Abar = (A.subgroupOf (H ⊔ A)).map θ := ⟨_, rfl⟩
  obtain ⟨Bbar, hBbar⟩ : ∃ Bbar : Subgroup ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k]
      (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤)), Bbar = (B.subgroupOf (H ⊔ A)).map θ := ⟨_, rfl⟩
  have hLleHA : ∀ i, L i ≤ H ⊔ A := fun i => (hLle i).trans le_sup_left
  have hact : ∀ (S : Subgroup (V ≃ₗ[k] V)) (hS : S ≤ H ⊔ A),
      (actOn H A ⊤ hAnH hHA' S hS).range = (S.subgroupOf (H ⊔ A)).map θ := fun S hS => by
    rw [hθ]
    exact actOn_range hAnH hHA' S hS
  have hperfL : ∀ i, Group.IsPerfect ↥(Lbar i) := by
    intro i
    rw [hLbar i, ← hact (L i) (hLleHA i)]
    have := (hq i).1
    exact Group.IsPerfect.range _
  have hcommL : ∀ i j, i ≠ j → ∀ x ∈ Lbar i, ∀ y ∈ Lbar j, x * y = y * x := by
    intro i j hij x hx y hy
    rw [hLbar] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i j hij)
      (Subgroup.mem_subgroupOf.1 hx')
    have h2 := Subgroup.mem_centralizer_iff.1 h1 (y' : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hy')
    exact h2.symm
  have hbarH : (H.subgroupOf (H ⊔ A)).map θ = ⨆ i, Lbar i := by
    have hsub : H.subgroupOf (H ⊔ A) = ⨆ i, (L i).subgroupOf (H ⊔ A) := by
      apply Subgroup.map_injective (H ⊔ A).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_iSup]
      calc H = ⨆ i, L i := hH
        _ = _ := iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hLleHA i)).symm
    rw [hsub, Subgroup.map_iSup]
    exact iSup_congr fun i => (hLbar i).symm
  have hHbar_ne : (H.subgroupOf (H ⊔ A)).map θ ≠ ⊥ := by
    intro h
    apply hirr.1
    have h1 : ∀ (l : V ≃ₗ[k] V) (hl : l ∈ H), θ ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by
      intro l hl
      have hm : (⟨l, Subgroup.mem_sup_left hl⟩ : ↥(H ⊔ A)) ∈ H.subgroupOf (H ⊔ A) := hl
      have h2 := Subgroup.mem_map_of_mem θ hm
      rw [h] at h2
      exact Subgroup.mem_bot.1 h2
    calc (⊤ : Submodule k V) = commSub (MonoidHom.id (V ≃ₗ[k] V)) H ⊤ := hcommV.symm
      _ ≤ fixSub (MonoidHom.id (V ≃ₗ[k] V)) H := by
        rw [commSub_le_iff]
        intro l hl u hu
        exact disp_mem_fix_of_actW_eq_one hAnH hHA'
          (x := ⟨l, Subgroup.mem_sup_left hl⟩) (by rw [← hθ]; exact h1 l hl) u hu
  have hrel : ∀ i j, (∃ a ∈ A, conjSub a (L i) = L j) → ∃ g, conjSub g (Lbar i) = Lbar j := by
    rintro i j ⟨a, ha, h⟩
    refine ⟨θ ⟨a, Subgroup.mem_sup_right ha⟩, ?_⟩
    rw [hLbar, hLbar]
    exact conjSub_map_subgroupOf θ _ h
  have hLbar_ne : ∀ i, Lbar i ≠ ⊥ := by
    intro j hj
    apply hHbar_ne
    rw [hbarH, eq_bot_iff]
    refine iSup_le fun i => ?_
    obtain ⟨g, hg⟩ := hrel i j (htrans i j)
    have : Lbar i = ⊥ := by
      apply (conjSub g).injective
      rw [hg, hj, (conjSub g).map_bot]
    exact this.le
  have hntL : ∀ i, Nontrivial ↥(Lbar i) := fun i =>
    (Subgroup.nontrivial_iff_ne_bot _).2 (hLbar_ne i)
  have hirrL : IsIrrAct (⨆ i, Lbar i) := by
    rw [← hbarH, hθ]
    exact isIrrAct_actW hAnH hHA' (hinv H) hirr
  have hAbel : CFSG.IsElementaryAbelian 2 ↥Abar := by
    rw [hAbar, ← hact A le_sup_right]
    exact isElementaryAbelian_range _ hAel
  have hpermL : ∀ b ∈ Abar, ∀ i, ∃ j, conjSub b (Lbar i) = Lbar j := by
    intro b hb i
    rw [hAbar] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨j, hj⟩ := hperm (x : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hx) i
    refine ⟨j, ?_⟩
    rw [hLbar, hLbar]
    exact conjSub_map_subgroupOf θ x.2 hj
  have htransL : ∀ i j, ∃ b ∈ Abar, conjSub b (Lbar i) = Lbar j := by
    intro i j
    obtain ⟨a, ha, h⟩ := htrans i j
    refine ⟨θ ⟨a, Subgroup.mem_sup_right ha⟩, ?_, ?_⟩
    · rw [hAbar]
      exact ⟨⟨a, Subgroup.mem_sup_right ha⟩, ha, rfl⟩
    · rw [hLbar, hLbar]
      exact conjSub_map_subgroupOf θ _ h
  have hWnt : Nontrivial (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) := by
    by_contra hcon
    have hsub : Subsingleton (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) :=
      not_nontrivial_iff_subsingleton.1 hcon
    apply hirr.1
    intro u hu l hl
    have h0 : (Submodule.Quotient.mk (⟨u, hu⟩ : ↥(⊤ : Submodule k V)) :
        ↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) = 0 := Subsingleton.elim _ _
    exact ((Submodule.Quotient.mk_eq_zero _).1 h0) l hl
  have hBbarA : Bbar ≤ Abar := by
    rw [hBbar, hAbar]
    exact Subgroup.map_mono fun x hx => hBA hx
  have hBbar0 : Bbar ≠ ⊥ := by
    intro h
    apply hB0
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    have hm : (⟨b, Subgroup.mem_sup_right (hBA hb)⟩ : ↥(H ⊔ A)) ∈ B.subgroupOf (H ⊔ A) := hb
    have h2 := Subgroup.mem_map_of_mem θ hm
    rw [← hBbar, h] at h2
    exact hθinj _ (Subgroup.mem_bot.1 h2)
  have hBfixL : ∀ b ∈ Bbar, ∀ i, conjSub b (Lbar i) = Lbar i := by
    intro b hb i
    rw [hBbar] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    rw [hLbar]
    exact conjSub_map_subgroupOf θ x.2 (hBfix (x : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hx) i)
  have hBqL : ∀ a ∈ Abar, ∀ b ∈ Bbar, ∀ w, b (a w - w) = a w - w := by
    intro a ha b hb w
    rw [hAbar] at ha
    rw [hBbar] at hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hq' : resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) ⊤ hHA' y
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) ⊤ hHA' x u - u) =
        resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) ⊤ hHA' x u - u := by
      apply Subtype.ext
      rw [resSub_apply, Submodule.coe_sub, resSub_apply]
      exact hBq (x : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hx) (y : V ≃ₗ[k] V)
        (Subgroup.mem_subgroupOf.1 hy) (u : V)
    have hq'' := congrArg (Submodule.Quotient.mk (p := fixIn H ⊤)) hq'
    rw [map_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub] at hq''
    show θ y (θ x (Submodule.Quotient.mk u) - Submodule.Quotient.mk u) =
      θ x (Submodule.Quotient.mk u) - Submodule.Quotient.mk u
    rw [map_sub, hθ, actW_mk hAnH hHA', actW_mk hAnH hHA', actW_mk hAnH hHA']
    exact hq''
  have hBmk : ∀ (b : ↥B) (u : ↥(⊤ : Submodule k V)),
      θ ⟨b, hBle b.2⟩ (Submodule.Quotient.mk u) =
        Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB b u) := by
    intro b u
    have e : resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) ⊤ hHA' ⟨b, hBle b.2⟩ u =
        resSub (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB b u :=
      Subtype.ext (by rw [resSub_apply, resSub_apply])
    rw [hθ, actW_mk hAnH hHA', e]
  have hBoffW : Nat.card (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≤
      weight (MonoidHom.id ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k] _)) Bbar := by
    let BI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB).range
    have h1 : Nat.card ↥(⊤ : Submodule k V) ≤
        weight (MonoidHom.id (↥(⊤ : Submodule k V) ≃ₗ[k] ↥(⊤ : Submodule k V))) BI :=
      natCard_le_weight_res (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB hmaxB
    let ρ' : ↥BI →* (↥(⊤ : Submodule k V) ≃ₗ[k] ↥(⊤ : Submodule k V)) :=
      (MonoidHom.id (↥(⊤ : Submodule k V) ≃ₗ[k] ↥(⊤ : Submodule k V))).comp BI.subtype
    have hρ'w : weight ρ' ⊤ =
        weight (MonoidHom.id (↥(⊤ : Submodule k V) ≃ₗ[k] ↥(⊤ : Submodule k V))) BI := by
      show weight ((MonoidHom.id (↥(⊤ : Submodule k V) ≃ₗ[k] ↥(⊤ : Submodule k V))).comp
        BI.subtype) ⊤ = _
      rw [weight_comp_subtype, map_subtype_top]
    have hZ' : ∀ x : ↥BI, ∀ z ∈ fixIn H ⊤, ρ' x z ∈ fixIn H ⊤ := by
      rintro ⟨_, a, rfl⟩ z hz
      exact fixIn_invariant hBH hinvB a z hz
    have h2 := natCard_quotient_le_weight ρ' (fixIn H ⊤) hZ' (by rw [hρ'w]; exact h1)
    let π := quotHom ρ' (fixIn H ⊤) hZ'
    let s : ↥B →* ↥BI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB).rangeRestrict
    have hs : Function.Surjective s := MonoidHom.rangeRestrict_surjective _
    have hcomp : ∀ b : ↥B, π (s b) = θ ⟨b, hBle b.2⟩ := by
      intro b
      apply LinearEquiv.ext
      intro w
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      rw [hBmk, quotHom_mk]
      rfl
    have hπinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro y hy
      obtain ⟨b, rfl⟩ := hs y
      have h3 : θ ⟨b, hBle b.2⟩ = 1 := by rw [← hcomp]; exact hy
      have h5 := hθinj _ h3
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      show ((resSub (MonoidHom.id (V ≃ₗ[k] V)) B ⊤ hinvB b w : ↥(⊤ : Submodule k V)) : V) = w
      rw [resSub_apply]
      exact congrArg (fun g : V ≃ₗ[k] V => g (w : V)) h5
    have hrange : π.range = Bbar := by
      have hcompM : π.comp s = actOn H A ⊤ hAnH hHA' B hBle := by
        refine MonoidHom.ext fun b => ?_
        show π (s b) = actW H A ⊤ hAnH hHA' ⟨b, hBle b.2⟩
        rw [← hθ]
        exact hcomp b
      rw [hBbar, ← hact B hBle, ← hcompM, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs]
      exact MonoidHom.range_eq_map π
    calc Nat.card (↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≤ weight π ⊤ := h2
      _ = weight (MonoidHom.id ((↥(⊤ : Submodule k V) ⧸ fixIn H ⊤) ≃ₗ[k] _)) π.range :=
        (weight_range_of_injective π hπinj).symm
      _ = _ := by rw [hrange]
  exact no_transitive_perfect_orbit_k_diag hs Lbar hcommL hperfL hntL hirrL Abar hpermL htransL
    Bbar hBbarA hBbar0 hBfixL hBqL hBoffW

end Main

end CFSG.Quasithin.B15P4
