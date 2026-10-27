module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147LocalLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
public import CFSG.Timmesfeld.Bridge.Asc72WreathStruct
public import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHWeakCoreMinimalNormalFactors
public import CFSG.Certificates.Kernel.Misc.F7MatSound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

open scoped Pointwise commutatorElement

theorem exists_mul_conj_eq_of_inf_centralizer_eq_bot {X : Type*} [Group X] [Finite X]
    {R : Subgroup X} {b : X} (hbR : b ∈ Subgroup.normalizer (R : Set X))
    (hfix : ∀ x ∈ R, b * x * b⁻¹ = x → x = 1) :
    ∀ r ∈ R, ∃ y ∈ R, r = y * (b * y⁻¹ * b⁻¹) := by
  have hmem : ∀ y : ↥R, b * (y : X)⁻¹ * b⁻¹ ∈ R := fun y =>
    (Subgroup.mem_normalizer_iff.mp hbR (y : X)⁻¹).mp (R.inv_mem y.2)
  set θ : ↥R → ↥R := fun y => y * ⟨b * (y : X)⁻¹ * b⁻¹, hmem y⟩ with hθ
  have hinj : Function.Injective θ := by
    intro y₁ y₂ h
    have h' : (y₁ : X) * (b * (y₁ : X)⁻¹ * b⁻¹) = (y₂ : X) * (b * (y₂ : X)⁻¹ * b⁻¹) :=
      congrArg Subtype.val h
    have h1 : (y₂ : X)⁻¹ * (y₁ : X) = b * ((y₂ : X)⁻¹ * (y₁ : X)) * b⁻¹ := by
      calc (y₂ : X)⁻¹ * (y₁ : X)
          = (y₂ : X)⁻¹ * ((y₁ : X) * (b * (y₁ : X)⁻¹ * b⁻¹)) *
              (b * (y₁ : X) * b⁻¹) := by group
        _ = (y₂ : X)⁻¹ * ((y₂ : X) * (b * (y₂ : X)⁻¹ * b⁻¹)) *
              (b * (y₁ : X) * b⁻¹) := by rw [h']
        _ = b * ((y₂ : X)⁻¹ * (y₁ : X)) * b⁻¹ := by group
    have hone : (y₂ : X)⁻¹ * (y₁ : X) = 1 :=
      hfix _ (R.mul_mem (R.inv_mem y₂.2) y₁.2) h1.symm
    refine Subtype.ext ?_
    show (y₁ : X) = (y₂ : X)
    calc (y₁ : X) = (y₂ : X) * ((y₂ : X)⁻¹ * (y₁ : X)) := by group
      _ = (y₂ : X) := by rw [hone, mul_one]
  have hsurj : Function.Surjective θ :=
    Finite.injective_iff_surjective.mp hinj
  intro r hr
  obtain ⟨y, hy⟩ := hsurj ⟨r, hr⟩
  refine ⟨(y : X), y.2, ?_⟩
  have hval : (y : X) * (b * (y : X)⁻¹ * b⁻¹) = r := by
    have h2 := congrArg Subtype.val hy
    rw [hθ] at h2
    exact h2
  exact hval.symm

theorem diag_mem_and_centralizer {X : Type*} [Group X] {W S : Subgroup X} [hW : W.Normal] {h : X}
    (hh : h ^ 3 = 1) (hS : S ≤ W)
    (hc₁ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj h).toMonoidHom, Commute x y)
    (hc₂ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj (h * h)).toMonoidHom, Commute x y) :
    ∀ s ∈ S, s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) ∈ W ∧
      h * (s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) * h⁻¹ =
        s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) ∧
      s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s⁻¹ ∈
        Subgroup.centralizer (S : Set X) := by
  intro s hs
  have haW : h * s * h⁻¹ ∈ W := hW.conj_mem s (hS hs) h
  have hbW : h * (h * s * h⁻¹) * h⁻¹ ∈ W := hW.conj_mem _ haW h
  have haS : h * s * h⁻¹ ∈ S.map (MulAut.conj h).toMonoidHom := by
    simpa using Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hs
  have hbS : h * (h * s * h⁻¹) * h⁻¹ ∈ S.map (MulAut.conj (h * h)).toMonoidHom := by
    have hconj : MulAut.conj (h * h) s = h * (h * s * h⁻¹) * h⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [← hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj (h * h)).toMonoidHom hs
  have has : Commute s (h * s * h⁻¹) := hc₁ s hs _ haS
  have hbs : Commute s (h * (h * s * h⁻¹) * h⁻¹) := hc₂ s hs _ hbS
  refine ⟨W.mul_mem (W.mul_mem (hS hs) haW) hbW, ?_, ?_⟩
  · have hb : h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹ = s := by
      have hhh : h * h * h = 1 := by rw [← pow_three', hh]
      have h3 : h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹ = (h * h * h) * s * (h * h * h)⁻¹ := by
        group
      rw [h3, hhh, one_mul, inv_one, mul_one]
    have hsab : Commute s ((h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) := has.mul_right hbs
    calc h * (s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) * h⁻¹
        = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) *
            (h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹) := by group
      _ = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s := by rw [hb]
      _ = s * ((h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) := hsab.eq.symm
      _ = s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) := by group
  · have hds : s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s⁻¹
        = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) := by
      have hsab : Commute s ((h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) := has.mul_right hbs
      calc s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s⁻¹
          = s * ((h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) * s⁻¹ := by group
        _ = ((h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) * s * s⁻¹ := by rw [hsab.eq]
        _ = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) := by group
    rw [hds, Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((hc₁ x hx _ haS).mul_right (hc₂ x hx _ hbS)).eq

theorem le_normalizer_inf_of_forall_mul_mem_centralizer {X : Type*} [Group X] {S Γ : Subgroup X}
    (h : ∀ s ∈ S, ∃ γ ∈ Γ, γ * s⁻¹ ∈ Subgroup.centralizer (S : Set X)) :
    S ≤ Subgroup.normalizer ((Γ ⊓ S : Subgroup X) : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs t ht
  obtain ⟨γ, hγ, hcS⟩ := h s hs
  set c : X := γ * s⁻¹ with hc
  have hγeq : γ = c * s := by rw [hc]; group
  have hmem : s * t * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs ht.2) (S.inv_mem hs)
  have hc' := (Subgroup.mem_centralizer_iff.mp hcS) (s * t * s⁻¹) hmem
  have heq : γ * t * γ⁻¹ = s * t * s⁻¹ := by
    rw [hγeq]
    calc c * s * t * (c * s)⁻¹ = c * (s * t * s⁻¹) * c⁻¹ := by group
      _ = s * t * s⁻¹ := by rw [← hc']; group
  refine Subgroup.mem_inf.mpr ⟨?_, hmem⟩
  rw [← heq]
  exact Γ.mul_mem (Γ.mul_mem hγ ht.1) (Γ.inv_mem hγ)

theorem commutator_mul_mul_eq {X : Type*} [Group X] {s u s' u' : X}
    (h1 : Commute u s') (h2 : Commute u u') (h3 : Commute s u') :
    ⁅s * u, s' * u'⁆ = ⁅s, s'⁆ := by
  have h1' : ⁅u, s'⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr h1
  have h2' : ⁅u, u'⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr h2
  have h3' : ⁅s, u'⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr h3
  rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_mul_left_eq_conj_mul, h1', h2', h3']
  group

theorem exists_fixed_point_of_prime_order_aut {X : Type*} [Group X] [Finite X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) {r : ℕ} (hr : r.Prime)
    {α : MulAut X} (hα : orderOf α = r) :
    ∃ x : X, x ≠ 1 ∧ α x = x := by
  by_contra h
  have hfix : ∀ g : X, α g = g → g = 1 := by
    intro g hg
    by_contra hg1
    exact h ⟨g, hg1, hg⟩
  have hntriv : Nontrivial X := hX.toNontrivial
  have hnil : Group.IsNilpotent X :=
    CFSG.StronglyEmbedded.prime_order_fixed_point_free_automorphism_nilpotent α hr hα hfix
  have hZ : Subgroup.center X ≠ ⊥ := Group.IsNilpotent.center_ne_bot X
  rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hZ hc
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top a) b).symm)

theorem exists_mem_map_conj_of_mem_sup {X : Type*} [Group X] [Finite X] {B R : Subgroup X}
    (hBR : B ≤ Subgroup.normalizer (R : Set X))
    (hfix : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ R, x * y * x⁻¹ = y → y = 1)
    {g : X} (hg : g ∈ B ⊔ R) (hgr : g ∉ R) :
    ∃ y ∈ R, g ∈ B.map (MulAut.conj y).toMonoidHom := by
  have hset : (↑(R ⊔ B) : Set X) = (R : Set X) * (B : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R B hBR
  have hg' : g ∈ (↑(R ⊔ B) : Set X) := by rwa [sup_comm] at hg
  rw [hset] at hg'
  obtain ⟨r, hr, β, hβ, rfl⟩ := hg'
  have hβne : β ≠ 1 := by
    intro h
    exact hgr (h ▸ (by simpa using hr))
  have hβR : β ∈ Subgroup.normalizer (R : Set X) := hBR hβ
  obtain ⟨y, hy, hyr⟩ :=
    exists_mul_conj_eq_of_inf_centralizer_eq_bot hβR
      (fun x hx hxfix => hfix β hβ hβne x hx hxfix) r hr
  refine ⟨y, hy, ?_⟩
  show r * β ∈ B.map (MulAut.conj y).toMonoidHom
  have heq : r * β = y * β * y⁻¹ := by rw [hyr]; group
  rw [heq]
  exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hβ

theorem sup_le_of_forall_map_conj_le {X : Type*} [Group X] [Finite X] {B R Q : Subgroup X}
    (hBR : B ≤ Subgroup.normalizer (R : Set X)) (hBne : ∃ b ∈ B, b ≠ 1)
    (hfix : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ R, x * y * x⁻¹ = y → y = 1)
    (hall : ∀ y ∈ R, B.map (MulAut.conj y).toMonoidHom ≤ Q) :
    B ⊔ R ≤ Q := by
  obtain ⟨b, hbB, hbne⟩ := hBne
  have hBQ : B ≤ Q := fun x hx => hall 1 R.one_mem
    (by simpa using Subgroup.mem_map_of_mem (MulAut.conj (1 : X)).toMonoidHom hx)
  refine sup_le hBQ ?_
  intro r hr
  obtain ⟨y, hy, hyr⟩ :=
    exists_mul_conj_eq_of_inf_centralizer_eq_bot (hBR hbB)
      (fun x hx hxfix => hfix b hbB hbne x hx hxfix) r hr
  have hyb : y * b * y⁻¹ ∈ Q := by
    have hmem : MulAut.conj y b ∈ B.map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hbB
    exact hall y hy (by simpa using hmem)
  rw [hyr, show y * (b * y⁻¹ * b⁻¹) = (y * b * y⁻¹) * b⁻¹ from by group]
  exact Q.mul_mem hyb (Q.inv_mem (hBQ hbB))

theorem not_le_normalizer_factor {X : Type*} [Group X] {W T : Subgroup X} {r : ℕ}
    {S : Fin r → Subgroup X} (hr : 2 ≤ r) (hSW : ⨆ i, S i = W)
    (hcomm : Pairwise fun i j : Fin r => ∀ x y : X, x ∈ S i → y ∈ S j → Commute x y)
    (hdisj : Pairwise fun i j : Fin r => S i ⊓ S j = ⊥) (hne : ∀ i, S i ≠ ⊥)
    (hmin : ∀ N : Subgroup X, N.Normal → N ≤ W → N = ⊥ ∨ N = W) (hT : W ⊔ T = ⊤) (i : Fin r) :
    ¬ T ≤ Subgroup.normalizer (S i : Set X) := by
  intro hTle
  have hle : ∀ j, S j ≤ Subgroup.normalizer (S i : Set X) := by
    intro j
    by_cases hj : j = i
    · rw [hj]
      exact Subgroup.le_normalizer
    · rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      have hc : Commute x y := hcomm hj x y hx hy
      have hxy : x * y * x⁻¹ = y := by rw [hc.eq]; group
      rw [hxy]
      exact hy
  have htop : Subgroup.normalizer (S i : Set X) = ⊤ := by
    rw [eq_top_iff, ← hT]
    exact sup_le (hSW ▸ iSup_le hle) hTle
  have hnorm : (S i).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hmin (S i) hnorm (hSW ▸ le_iSup S i) with hbot | hWeq
  · exact hne i hbot
  · have hntFin : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
    obtain ⟨j, hji⟩ := @exists_ne (Fin r) hntFin i
    have hlej : S j ≤ S i := by
      rw [hWeq]
      exact hSW ▸ le_iSup S j
    have hb : S j = ⊥ := by
      rw [eq_bot_iff]
      calc S j ≤ S i ⊓ S j := le_inf hlej le_rfl
        _ = ⊥ := hdisj hji.symm
    exact hne j hb

theorem le_of_inf_ne_bot_of_map_conj_ne {X : Type*} [Group X] {W S Γ K : Subgroup X} [W.Normal]
    (hSW : S ≤ W) (hS : IsSimpleGroup S)
    (hcm : ∀ g g' : X, S.map (MulAut.conj g).toMonoidHom ≠ S.map (MulAut.conj g').toMonoidHom →
      ∀ x ∈ S.map (MulAut.conj g).toMonoidHom, ∀ y ∈ S.map (MulAut.conj g').toMonoidHom,
        Commute x y)
    {h : X} (hh : h ^ 3 = 1) (hmove : S.map (MulAut.conj h).toMonoidHom ≠ S)
    (hK : K ≤ Subgroup.zpowers h)
    (hfix : ∀ w ∈ W, w ∈ Subgroup.centralizer (K : Set X) → w ∈ Γ) (hne : Γ ⊓ S ≠ ⊥) :
    S ≤ Γ := by
  have hmap1 : S.map (MulAut.conj (1 : X)).toMonoidHom = S := by
    rw [map_one]
    change S.map (MonoidHom.id X) = S
    exact Subgroup.map_id S
  have h3 : h * h * h = 1 := by rw [← pow_three', hh]
  have hmap2 : S.map (MulAut.conj (h * h)).toMonoidHom ≠ S := by
    intro heq
    apply hmove
    have hone : (S.map (MulAut.conj (h * h)).toMonoidHom).map
        (MulAut.conj h).toMonoidHom = S.map (MulAut.conj h).toMonoidHom := by rw [heq]
    rw [Subgroup.map_map] at hone
    have hcomp : (MulAut.conj h).toMonoidHom.comp (MulAut.conj (h * h)).toMonoidHom =
        (MulAut.conj (1 : X)).toMonoidHom := by
      ext x
      have hone1 : MulAut.conj (1 : X) x = x := by
        rw [show MulAut.conj (1 : X) = 1 from map_one _]
        rfl
      show h * ((h * h) * x * (h * h)⁻¹) * h⁻¹ = MulAut.conj (1 : X) x
      rw [hone1]
      calc h * ((h * h) * x * (h * h)⁻¹) * h⁻¹
          = (h * h * h) * x * (h * h * h)⁻¹ := by group
        _ = x := by rw [h3, one_mul, inv_one, mul_one]
    rw [hcomp, hmap1] at hone
    exact hone.symm
  have hc₁ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj h).toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 h (by rw [hmap1]; exact hmove.symm) x (hmap1.symm ▸ hx) y hy
  have hc₂ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj (h * h)).toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 (h * h) (by rw [hmap1]; exact hmap2.symm) x (hmap1.symm ▸ hx) y hy
  have hdiag := diag_mem_and_centralizer (W := W) (S := S) (h := h) hh hSW hc₁ hc₂
  have hforall : ∀ s ∈ S, ∃ γ ∈ Γ, γ * s⁻¹ ∈ Subgroup.centralizer (S : Set X) := by
    intro s hs
    obtain ⟨hdW, hdfix, hdcent⟩ := hdiag s hs
    refine ⟨_, hfix _ hdW ?_, hdcent⟩
    have hcomm : Commute h (s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) := by
      have h4 := congrArg (fun x => x * h) hdfix
      show h * (s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹)) =
        s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * h
      simpa [mul_assoc] using h4
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hK hk)
    exact (hcomm.zpow_left m).eq
  have hnorm : S ≤ Subgroup.normalizer ((Γ ⊓ S : Subgroup X) : Set X) :=
    le_normalizer_inf_of_forall_mul_mem_centralizer hforall
  have hnormal : ((Γ ⊓ S).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hnorm
  have hneSub : (Γ ⊓ S).subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hne
    have h1 : (Γ ⊓ S).subgroupOf S = (⊥ : Subgroup X).subgroupOf S := by
      rw [hbot, Subgroup.bot_subgroupOf]
    have h' := Subgroup.subgroupOf_inj.mp h1
    simpa using h'
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥S _ hS ((Γ ⊓ S).subgroupOf S) hnormal with
    hbot | htop
  · exact absurd hbot hneSub
  · intro s hs
    have hs' : (⟨s, hs⟩ : ↥S) ∈ (Γ ⊓ S).subgroupOf S := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hs').1

theorem inf_ne_bot_of_le_normalizer {X : Type*} [Group X] [Finite X] {W S Γ H : Subgroup X}
    (hSW : S ≤ W) (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hH : H ≤ Subgroup.normalizer (S : Set X)) (hHp : H = ⊥ ∨ (Nat.card H).Prime)
    (hfix : ∀ w ∈ W, w ∈ Subgroup.centralizer (H : Set X) → w ∈ Γ) : Γ ⊓ S ≠ ⊥ := by
  have hSne : S ≠ ⊥ := by
    intro hSbot
    obtain ⟨a, b, hab⟩ := hnab
    have hsub : Subsingleton ↥S := by rw [hSbot]; infer_instance
    exact hab (@Subsingleton.elim ↥S hsub (a * b) (b * a))
  rcases hHp with hbot | hp
  · have hWΓ : W ≤ Γ := by
      intro w hw
      refine hfix w hw ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [hbot] at hk
      rw [Subgroup.mem_bot.mp hk, one_mul, mul_one]
    have hΓ : Γ ⊓ S = S := inf_eq_right.mpr (hSW.trans hWΓ)
    rw [hΓ]
    exact hSne
  · have hntH : Nontrivial ↥H := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
    obtain ⟨h₀, h0ne⟩ := @exists_ne ↥H hntH (1 : ↥H)
    have hconjy : ∀ y : ↥H, ∀ x : X, x ∈ S ↔ (y : X) * x * (y : X)⁻¹ ∈ S :=
      fun y => Subgroup.mem_normalizer_iff.mp (hH y.2)
    let Φ : ↥H →* MulAut ↥S :=
      { toFun := fun y =>
          { toFun := fun s => ⟨(y : X) * (s : X) * (y : X)⁻¹, (hconjy y (s : X)).mp s.2⟩
            invFun := fun s =>
              ⟨(y : X)⁻¹ * (s : X) * (y : X), by
                exact (hconjy y ((y : X)⁻¹ * (s : X) * (y : X))).mpr (by
                  have h : (y : X) * ((y : X)⁻¹ * (s : X) * (y : X)) * (y : X)⁻¹ =
                      (s : X) := by group
                  rw [h]
                  exact s.2)⟩
            left_inv := fun s => by apply Subtype.ext; group
            right_inv := fun s => by apply Subtype.ext; group
            map_mul' := fun a b => by
              apply Subtype.ext
              simp only [Subgroup.coe_mul]
              group }
        map_one' := by
          apply MulEquiv.ext
          intro s
          apply Subtype.ext
          simp
        map_mul' := fun y z => by
          apply MulEquiv.ext
          intro s
          apply Subtype.ext
          show (y : X) * (z : X) * (s : X) * ((y : X) * (z : X))⁻¹ =
            (y : X) * ((z : X) * (s : X) * (z : X)⁻¹) * (y : X)⁻¹
          group }
    have horder : orderOf (h₀ : X) = Nat.card H := by
      have hdvd : orderOf (h₀ : X) ∣ Nat.card H := by
        simpa using orderOf_dvd_natCard h₀
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
      · exact absurd h1 (by
          intro h
          exact h0ne (by
            have h' : (h₀ : X) = 1 := orderOf_eq_one_iff.mp h
            exact Subtype.ext h'))
      · exact hpp
    have hgen : H = Subgroup.zpowers (h₀ : X) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h₀.2) ?_).symm
      rw [Nat.card_zpowers, horder]
    have hh0p : (h₀ : X) ^ Nat.card H = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one (h₀ : X)
    have hh0p' : h₀ ^ Nat.card H = 1 := Subtype.ext (by simp)
    have hαp : (Φ h₀) ^ Nat.card H = 1 := by
      rw [← map_pow, hh0p', map_one]
    have hdvdα : orderOf (Φ h₀) ∣ Nat.card H := orderOf_dvd_of_pow_eq_one hαp
    have key : ∀ s : ↥S, s ≠ 1 → Φ h₀ s = s → Γ ⊓ S ≠ ⊥ := by
      intro s hs hfixs
      have h5 : (h₀ : X) * (s : X) * (h₀ : X)⁻¹ = (s : X) := congrArg Subtype.val hfixs
      have hcomm : Commute (h₀ : X) (s : X) := by
        show (h₀ : X) * (s : X) = (s : X) * (h₀ : X)
        calc (h₀ : X) * (s : X) = ((h₀ : X) * (s : X) * (h₀ : X)⁻¹) * (h₀ : X) := by group
          _ = (s : X) * (h₀ : X) := by rw [h5]
      have hcent : (s : X) ∈ Subgroup.centralizer (H : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hk' : k ∈ Subgroup.zpowers (h₀ : X) := hgen ▸ hk
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
        exact (hcomm.zpow_left m).eq
      have hmem : (s : X) ∈ Γ ⊓ S := ⟨hfix (s : X) (hSW s.2) hcent, s.2⟩
      intro hb
      rw [hb] at hmem
      exact hs (Subtype.ext (Subgroup.mem_bot.mp hmem))
    rcases (Nat.dvd_prime hp).mp hdvdα with h1 | hpp
    · have hΦ1 : Φ h₀ = 1 := orderOf_eq_one_iff.mp h1
      obtain ⟨s, hs⟩ : ∃ s : ↥S, s ≠ 1 := by
        by_contra h
        push Not at h
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (by rw [h a, h b])
      exact key s hs (by rw [hΦ1]; rfl)
    · obtain ⟨s, hs, hfixs⟩ := exists_fixed_point_of_prime_order_aut hS hnab hp hpp
      exact key s hs hfixs

theorem inf_ne_bot_of_disjoint_orbits {X : Type*} [Group X] {W S Γ K K' : Subgroup X} [W.Normal]
    (hSW : S ≤ W) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hcm : ∀ g g' : X, S.map (MulAut.conj g).toMonoidHom ≠ S.map (MulAut.conj g').toMonoidHom →
      ∀ x ∈ S.map (MulAut.conj g).toMonoidHom, ∀ y ∈ S.map (MulAut.conj g').toMonoidHom,
        Commute x y)
    {h h' : X} (hh : h ^ 3 = 1) (hh' : h' ^ 3 = 1)
    (hdist : ∀ j k : ℕ, j < 3 → k < 3 → (j ≠ 0 ∨ k ≠ 0) →
      S.map (MulAut.conj (h ^ j)).toMonoidHom ≠ S.map (MulAut.conj (h' ^ k)).toMonoidHom)
    (hK : K ≤ Subgroup.zpowers h) (hK' : K' ≤ Subgroup.zpowers h')
    (hfix : ∀ w ∈ W, w ∈ Subgroup.centralizer (K : Set X) → w ∈ Γ)
    (hfix' : ∀ w ∈ W, w ∈ Subgroup.centralizer (K' : Set X) → w ∈ Γ) : Γ ⊓ S ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := hnab
  have hmap1 : S.map (MulAut.conj (1 : X)).toMonoidHom = S := by
    rw [map_one]
    change S.map (MonoidHom.id X) = S
    exact Subgroup.map_id S
  have hmap1' : S.map (↑(1 : MulAut X)) = S := by simpa using hmap1
  have hch : S.map (MulAut.conj h).toMonoidHom ≠ S := by
    simpa [hmap1'] using hdist 1 0 (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hch2 : S.map (MulAut.conj (h * h)).toMonoidHom ≠ S := by
    simpa [hmap1', pow_two] using hdist 2 0 (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hch' : S.map (MulAut.conj h').toMonoidHom ≠ S := by
    simpa [hmap1'] using (hdist 0 1 (by norm_num) (by norm_num) (Or.inr (by norm_num))).symm
  have hch2' : S.map (MulAut.conj (h' * h')).toMonoidHom ≠ S := by
    simpa [hmap1', pow_two] using
      (hdist 0 2 (by norm_num) (by norm_num) (Or.inr (by norm_num))).symm
  have hc₁ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj h).toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 h (by rw [hmap1]; exact hch.symm) x (hmap1.symm ▸ hx) y hy
  have hc₂ : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj (h * h)).toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 (h * h) (by rw [hmap1]; exact hch2.symm) x (hmap1.symm ▸ hx) y hy
  have hc₁' : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj h').toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 h' (by rw [hmap1]; exact hch'.symm) x (hmap1.symm ▸ hx) y hy
  have hc₂' : ∀ x ∈ S, ∀ y ∈ S.map (MulAut.conj (h' * h')).toMonoidHom, Commute x y := by
    intro x hx y hy
    exact hcm 1 (h' * h') (by rw [hmap1]; exact hch2'.symm) x (hmap1.symm ▸ hx) y hy
  let u₁ : X := h * (a : X) * h⁻¹
  let u₂ : X := h * (h * (a : X) * h⁻¹) * h⁻¹
  let u₁' : X := h' * (b : X) * h'⁻¹
  let u₂' : X := h' * (h' * (b : X) * h'⁻¹) * h'⁻¹
  have hu1 : u₁ ∈ S.map (MulAut.conj h).toMonoidHom := by
    show h * (a : X) * h⁻¹ ∈ S.map (MulAut.conj h).toMonoidHom
    simp
  have hu2 : u₂ ∈ S.map (MulAut.conj (h * h)).toMonoidHom := by
    show h * (h * (a : X) * h⁻¹) * h⁻¹ ∈ S.map (MulAut.conj (h * h)).toMonoidHom
    have hconj : MulAut.conj (h * h) (a : X) = h * (h * (a : X) * h⁻¹) * h⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [← hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj (h * h)).toMonoidHom a.2
  have hu1' : u₁' ∈ S.map (MulAut.conj h').toMonoidHom := by
    show h' * (b : X) * h'⁻¹ ∈ S.map (MulAut.conj h').toMonoidHom
    simp
  have hu2' : u₂' ∈ S.map (MulAut.conj (h' * h')).toMonoidHom := by
    show h' * (h' * (b : X) * h'⁻¹) * h'⁻¹ ∈ S.map (MulAut.conj (h' * h')).toMonoidHom
    have hconj : MulAut.conj (h' * h') (b : X) = h' * (h' * (b : X) * h'⁻¹) * h'⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [← hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj (h' * h')).toMonoidHom b.2
  have hdiag := diag_mem_and_centralizer (W := W) (S := S) (h := h) hh hSW hc₁ hc₂
  have hdiag' := diag_mem_and_centralizer (W := W) (S := S) (h := h') hh' hSW hc₁' hc₂'
  obtain ⟨hdW, hdfix, -⟩ := hdiag (a : X) a.2
  obtain ⟨hdW', hdfix', -⟩ := hdiag' (b : X) b.2
  have hdΓ : (a : X) * u₁ * u₂ ∈ Γ := by
    refine hfix _ hdW ?_
    have hcomm : Commute h ((a : X) * u₁ * u₂) := by
      show h * ((a : X) * u₁ * u₂) = ((a : X) * u₁ * u₂) * h
      calc h * ((a : X) * u₁ * u₂)
          = (h * ((a : X) * u₁ * u₂) * h⁻¹) * h := by group
        _ = ((a : X) * u₁ * u₂) * h := by rw [hdfix]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hK hk)
    exact (hcomm.zpow_left m).eq
  have hdΓ' : (b : X) * u₁' * u₂' ∈ Γ := by
    refine hfix' _ hdW' ?_
    have hcomm : Commute h' ((b : X) * u₁' * u₂') := by
      show h' * ((b : X) * u₁' * u₂') = ((b : X) * u₁' * u₂') * h'
      calc h' * ((b : X) * u₁' * u₂')
          = (h' * ((b : X) * u₁' * u₂') * h'⁻¹) * h' := by group
        _ = ((b : X) * u₁' * u₂') * h' := by rw [hdfix']
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hK' hk)
    exact (hcomm.zpow_left m).eq
  have h1 : Commute (u₁ * u₂) (b : X) := by
    exact (hc₁ (b : X) b.2 u₁ hu1).symm.mul_left (hc₂ (b : X) b.2 u₂ hu2).symm
  have h3 : Commute (a : X) (u₁' * u₂') := by
    exact (hc₁' (a : X) a.2 u₁' hu1').mul_right (hc₂' (a : X) a.2 u₂' hu2')
  have h2 : Commute (u₁ * u₂) (u₁' * u₂') := by
    have hne11 : S.map (MulAut.conj h).toMonoidHom ≠ S.map (MulAut.conj h').toMonoidHom := by
      simpa using hdist 1 1 (by norm_num) (by norm_num) (Or.inl (by norm_num))
    have h11 : Commute u₁ u₁' := hcm h h' hne11 u₁ hu1 u₁' hu1'
    have hne12 : S.map (MulAut.conj h).toMonoidHom ≠
        S.map (MulAut.conj (h' * h')).toMonoidHom := by
      simpa [pow_two] using hdist 1 2 (by norm_num) (by norm_num) (Or.inl (by norm_num))
    have h12 : Commute u₁ u₂' := hcm h (h' * h') hne12 u₁ hu1 u₂' hu2'
    have hne21 : S.map (MulAut.conj (h * h)).toMonoidHom ≠
        S.map (MulAut.conj h').toMonoidHom := by
      simpa [pow_two] using hdist 2 1 (by norm_num) (by norm_num) (Or.inl (by norm_num))
    have h21 : Commute u₂ u₁' := hcm (h * h) h' hne21 u₂ hu2 u₁' hu1'
    have hne22 : S.map (MulAut.conj (h * h)).toMonoidHom ≠
        S.map (MulAut.conj (h' * h')).toMonoidHom := by
      simpa [pow_two] using hdist 2 2 (by norm_num) (by norm_num) (Or.inr (by norm_num))
    have h22 : Commute u₂ u₂' := hcm (h * h) (h' * h') hne22 u₂ hu2 u₂' hu2'
    exact (h11.mul_right h12).mul_left (h21.mul_right h22)
  have hcomm_eq : ⁅(a : X) * (u₁ * u₂), (b : X) * (u₁' * u₂')⁆ = ⁅(a : X), (b : X)⁆ :=
    commutator_mul_mul_eq h1 h2 h3
  have hmemΓ : ⁅(a : X), (b : X)⁆ ∈ Γ := by
    rw [← hcomm_eq]
    have hd_eq : (a : X) * (u₁ * u₂) = (a : X) * u₁ * u₂ := by group
    have hd'_eq : (b : X) * (u₁' * u₂') = (b : X) * u₁' * u₂' := by group
    rw [hd_eq, hd'_eq]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hdΓ hdΓ') (Γ.inv_mem hdΓ)) (Γ.inv_mem hdΓ')
  have hmemS : ⁅(a : X), (b : X)⁆ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem a.2 b.2) (S.inv_mem a.2)) (S.inv_mem b.2)
  have hne : ⁅(a : X), (b : X)⁆ ≠ 1 := by
    intro h1
    exact hab (Subtype.ext (commutatorElement_eq_one_iff_commute.mp h1).eq)
  intro hbot
  have hmem : ⁅(a : X), (b : X)⁆ ∈ Γ ⊓ S := ⟨hmemΓ, hmemS⟩
  rw [hbot] at hmem
  exact hne (Subgroup.mem_bot.mp hmem)

theorem inv_conj_pow_mul_pow_not_mem {X : Type*} [Group X] [Finite X] {B R R₀ Q : Subgroup X}
    {b x₀ : X} (hBcard : Nat.card B = 3) (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hBR : B ≤ Subgroup.normalizer (R : Set X))
    (hfix : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ R, x * y * x⁻¹ = y → y = 1)
    (hR₀R : R₀ ≤ R) (hBR₀ : B ≤ Subgroup.normalizer (R₀ : Set X)) (hR₀ : (Nat.card R₀).Prime)
    (hx₀ : x₀ ∈ R₀) (hx₀1 : x₀ ≠ 1)
    (hBQ : ∀ y ∈ R, ¬ B.map (MulAut.conj y).toMonoidHom ≤ Q) (hR₀Q : ¬ R₀ ≤ Q)
    {j k : ℕ} (hj : j < 3) (hk : k < 3) (hjk : j ≠ 0 ∨ k ≠ 0) :
    (x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j ∉ Q := by
  have hb3 : orderOf b = 3 := by
    have hdvd : orderOf b ∣ 3 := by
      rw [← hBcard]
      simpa using orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
    rcases (Nat.dvd_prime (by norm_num : (3 : ℕ).Prime)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hbjne : ∀ {n : ℕ}, n < 3 → n ≠ 0 → b ^ n ≠ 1 := by
    intro n hn hn0 h
    have hdvd : 3 ∣ n := by rwa [← hb3, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨c, rfl⟩ := hdvd
    omega
  have hBdisj : B ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    exact hz1 (hfix z (Subgroup.mem_inf.mp hz).1 hz1 z (Subgroup.mem_inf.mp hz).2 (by group))
  have hR₀gen : ∀ g ∈ R₀, g ≠ 1 → R₀ = Subgroup.zpowers g := by
    intro g hg hg1
    have hdvd : orderOf g ∣ Nat.card R₀ := by
      simpa using orderOf_dvd_natCard (⟨g, hg⟩ : ↥R₀)
    have hord : orderOf g = Nat.card R₀ := by
      rcases (Nat.dvd_prime hR₀).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
    rw [Nat.card_zpowers, hord]
  by_cases hjk_eq : j = k
  ·
    rw [← hjk_eq]
    have hjne0 : j ≠ 0 := by
      rcases hjk with h | h
      · exact h
      · intro hj0
        exact h (hjk_eq ▸ hj0)
    have hbjN : b ^ j ∈ Subgroup.normalizer (R₀ : Set X) :=
      (Subgroup.normalizer (R₀ : Set X)).pow_mem (hBR₀ hbB) j
    have hconj : (b ^ j)⁻¹ * x₀⁻¹ * b ^ j ∈ R₀ := by
      have h1 : (b ^ j)⁻¹ ∈ Subgroup.normalizer (R₀ : Set X) :=
        (Subgroup.normalizer (R₀ : Set X)).inv_mem hbjN
      simpa using (Subgroup.mem_normalizer_iff.mp h1 x₀⁻¹).mp (R₀.inv_mem hx₀)
    have hgR₀ : (x₀ * b ^ j * x₀⁻¹)⁻¹ * b ^ j ∈ R₀ := by
      have heq : (x₀ * b ^ j * x₀⁻¹)⁻¹ * b ^ j =
          x₀ * ((b ^ j)⁻¹ * x₀⁻¹ * b ^ j) := by group
      rw [heq]
      exact R₀.mul_mem hx₀ hconj
    have hgne : (x₀ * b ^ j * x₀⁻¹)⁻¹ * b ^ j ≠ 1 := by
      intro hg1
      have h2 : b ^ j = x₀ * b ^ j * x₀⁻¹ := by
        have h := congrArg (fun z => (x₀ * b ^ j * x₀⁻¹) * z) hg1
        simpa [mul_assoc] using h
      have hfixeq : b ^ j * x₀ * (b ^ j)⁻¹ = x₀ := by
        calc b ^ j * x₀ * (b ^ j)⁻¹ = (x₀ * b ^ j * x₀⁻¹) * x₀ * (b ^ j)⁻¹ := by
              rw [← h2]
          _ = x₀ := by group
      exact hx₀1 (hfix (b ^ j) (B.pow_mem hbB j) (hbjne hj hjne0) x₀ (hR₀R hx₀) hfixeq)
    have hR0eq : R₀ = Subgroup.zpowers ((x₀ * b ^ j * x₀⁻¹)⁻¹ * b ^ j) :=
      hR₀gen _ hgR₀ hgne
    intro hgQ
    apply hR₀Q
    rw [hR0eq]
    exact Subgroup.zpowers_le.mpr hgQ
  ·
    have hgR : (x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j ∉ R := by
      intro hgR
      have hbkN : b ^ k ∈ Subgroup.normalizer (R : Set X) :=
        (Subgroup.normalizer (R : Set X)).pow_mem (hBR hbB) k
      have hbjR : b ^ j * (b ^ k)⁻¹ ∈ R := by
        have h1 : b ^ k * x₀⁻¹ * (b ^ k)⁻¹ ∈ R := by
          simpa using (Subgroup.mem_normalizer_iff.mp hbkN x₀⁻¹).mp (R.inv_mem (hR₀R hx₀))
        have h2 : b ^ k * ((x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j) * (b ^ k)⁻¹ ∈ R := by
          simpa using (Subgroup.mem_normalizer_iff.mp hbkN _).mp hgR
        have heq : b ^ j * (b ^ k)⁻¹ =
            x₀ * (b ^ k * x₀⁻¹ * (b ^ k)⁻¹) *
              (b ^ k * ((x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j) * (b ^ k)⁻¹) := by group
        rw [heq]
        exact R.mul_mem (R.mul_mem (hR₀R hx₀) h1) h2
      have hbjB : b ^ j * (b ^ k)⁻¹ ∈ B :=
        B.mul_mem (B.pow_mem hbB j) (B.inv_mem (B.pow_mem hbB k))
      have h1 : b ^ j * (b ^ k)⁻¹ = 1 := by
        have hmem : b ^ j * (b ^ k)⁻¹ ∈ B ⊓ R := Subgroup.mem_inf.mpr ⟨hbjB, hbjR⟩
        rw [hBdisj] at hmem
        exact Subgroup.mem_bot.mp hmem
      have h2 : b ^ j = b ^ k := by
        have h := congrArg (fun z => z * b ^ k) h1
        simpa [mul_assoc] using h
      exact hjk_eq (pow_injOn_Iio_orderOf (by rw [hb3]; exact hj) (by rw [hb3]; exact hk) h2)
    have hgBsup : (x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j ∈ B ⊔ R := by
      have hbk_inv_N : (b ^ k)⁻¹ ∈ Subgroup.normalizer (R : Set X) :=
        (Subgroup.normalizer (R : Set X)).inv_mem
          ((Subgroup.normalizer (R : Set X)).pow_mem (hBR hbB) k)
      have hconjR : (b ^ k)⁻¹ * x₀⁻¹ * b ^ k ∈ R := by
        have h := (Subgroup.mem_normalizer_iff.mp hbk_inv_N x₀⁻¹).mp (R.inv_mem (hR₀R hx₀))
        simpa using h
      have hr : x₀ * ((b ^ k)⁻¹ * x₀⁻¹ * b ^ k) ∈ R :=
        R.mul_mem (hR₀R hx₀) hconjR
      have hmemB : (b ^ k)⁻¹ * b ^ j ∈ B :=
        B.mul_mem (B.inv_mem (B.pow_mem hbB k)) (B.pow_mem hbB j)
      have heq : (x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j =
          (x₀ * ((b ^ k)⁻¹ * x₀⁻¹ * b ^ k)) * ((b ^ k)⁻¹ * b ^ j) := by group
      rw [heq]
      exact sup_comm R B ▸ Subgroup.mul_mem_sup hr hmemB
    obtain ⟨y, hyR, hgy⟩ := exists_mem_map_conj_of_mem_sup hBR hfix hgBsup hgR
    have hgne : (x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j ≠ 1 := fun h => hgR (h ▸ R.one_mem)
    have hHcard : Nat.card ↥(B.map (MulAut.conj y).toMonoidHom) = 3 := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective B (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective).toEquiv, hBcard]
    have horderg : orderOf ((x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j) = 3 := by
      have hdvd : orderOf ((x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j) ∣ 3 := by
        rw [← hHcard]
        have h := orderOf_dvd_natCard
          (⟨(x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j, hgy⟩ : ↥(B.map (MulAut.conj y).toMonoidHom))
        rwa [orderOf_mk] at h
      rcases (Nat.dvd_prime (by norm_num : (3 : ℕ).Prime)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hgne
      · exact h
    have hHeq : B.map (MulAut.conj y).toMonoidHom =
        Subgroup.zpowers ((x₀ * b ^ k * x₀⁻¹)⁻¹ * b ^ j) := by
      refine (Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hgy) ?_).symm
      rw [Nat.card_zpowers, horderg, hHcard]
    intro hgQ
    apply hBQ y hyR
    rw [hHeq]
    exact Subgroup.zpowers_le.mpr hgQ

abbrev uc147Ambient (V B R : Subgroup G) : Subgroup G := V ⊔ B ⊔ R

abbrev uc147Section (V B R V₀ : Subgroup G) : Type :=
  ↥(uc147Ambient V B R) ⧸ (V₀.subgroupOf (uc147Ambient V B R))

abbrev uc147Quot (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    ↥(uc147Ambient V B R) →* uc147Section V B R V₀ :=
  QuotientGroup.mk' _

abbrev uc147Image (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    Subgroup (uc147Section V B R V₀) :=
  (V.subgroupOf (uc147Ambient V B R)).map (uc147Quot V B R V₀)

abbrev uc147Map (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    ↥V →* uc147Section V B R V₀ :=
  (uc147Quot V B R V₀).comp (Subgroup.inclusion (le_sup_left.trans le_sup_left))

abbrev uc147MapImage (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    ↥V →* ↥(uc147Image V B R V₀) :=
  { toFun := fun v => ⟨uc147Map V B R V₀ v, Subgroup.mem_map_of_mem _ v.2⟩
    map_one' := Subtype.ext (map_one (uc147Map V B R V₀))
    map_mul' := fun a b => Subtype.ext (map_mul (uc147Map V B R V₀) a b) }

omit [Finite G] in
@[simp]
theorem uc147MapImage_apply (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (v : ↥V) :
    ((uc147MapImage V B R V₀ v : ↥(uc147Image V B R V₀)) : uc147Section V B R V₀) =
      uc147Map V B R V₀ v :=
  rfl

omit [Finite G] in
theorem uc147Map_eq_one (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (v : ↥V) :
    uc147Map V B R V₀ v = 1 ↔ (v : G) ∈ V₀ := by
  rw [show uc147Map V B R V₀ v =
      uc147Quot V B R V₀
        ⟨(v : G), (le_sup_left.trans le_sup_left : V ≤ uc147Ambient V B R) v.2⟩ from rfl,
    ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact Subgroup.mem_subgroupOf

omit [Finite G] in
theorem uc147Map_mem_image (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal] (v : ↥V) :
    uc147Map V B R V₀ v ∈ uc147Image V B R V₀ :=
  Subgroup.mem_map_of_mem _ v.2

omit [Finite G] in
theorem uc147MapImage_ker (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    (uc147MapImage V B R V₀).ker = V₀.subgroupOf V := by
  ext v
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact Subgroup.mem_subgroupOf.mpr ((uc147Map_eq_one V B R V₀ v).1 (congrArg Subtype.val h))
  · intro h
    exact Subtype.ext ((uc147Map_eq_one V B R V₀ v).2 (Subgroup.mem_subgroupOf.mp h))

omit [Finite G] in
theorem uc147MapImage_surjective (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal] :
    Function.Surjective (uc147MapImage V B R V₀) := by
  intro w
  obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp w.2
  refine ⟨⟨(y : G), hy⟩, Subtype.ext ?_⟩
  exact hyw

noncomputable def uc147SectionIso (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal] [(V₀.subgroupOf V).Normal] :
    (↥V ⧸ (V₀.subgroupOf V)) ≃* ↥(uc147Image V B R V₀) :=
  (QuotientGroup.quotientMulEquivOfEq (uc147MapImage_ker V B R V₀)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (uc147MapImage V B R V₀)
      (uc147MapImage_surjective V B R V₀))

omit [Finite G] in
theorem uc147Image_normal (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (hV : uc147Ambient V B R ≤ Subgroup.normalizer (V : Set G)) :
    (uc147Image V B R V₀).Normal := by
  have hVn : (V.subgroupOf (uc147Ambient V B R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left.trans le_sup_left)).2 hV
  exact hVn.map _ (QuotientGroup.mk'_surjective _)

structure Uc147Factors (E : Type) [Group E] (W : Subgroup E) where
  r : ℕ
  S : Fin r → Subgroup E
  one_le_r : 1 ≤ r
  le_W : ∀ i, S i ≤ W
  simple : ∀ i, IsSimpleGroup (S i)
  conjugate : ∀ i j, ∃ g : E, S j = CFSG.conjugate (S i) g
  normal_in_W : ∀ i, ((S i).subgroupOf W).Normal
  e : ((i : Fin r) → S i) ≃* W
  e_single : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : E) = x i

namespace Uc147Factors

variable {E : Type} [Group E] {W : Subgroup E} (F : Uc147Factors E W)

theorem card_eq (i j : Fin F.r) : Nat.card ↥(F.S i) = Nat.card ↥(F.S j) := by
  obtain ⟨g, hg⟩ := F.conjugate i j
  rw [hg, CFSG.conjugate]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (F.S i) ((MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective).toEquiv

theorem not_isMulCommutative (hWnab : ¬ IsMulCommutative ↥W) (i : Fin F.r) :
    ¬ IsMulCommutative ↥(F.S i) := by
  intro hab
  have hp : (Nat.card ↥(F.S i)).Prime :=
    (Group.is_simple_iff_prime_card).mp (F.simple i)
  have hcard : ∀ j, Nat.card ↥(F.S j) = Nat.card ↥(F.S i) := fun j => F.card_eq j i
  have hj : ∀ j, IsMulCommutative ↥(F.S j) := fun j =>
    (isCyclic_of_prime_card (p := Nat.card ↥(F.S j)) (hp := ⟨hcard j ▸ hp⟩)
      rfl).isMulCommutative
  apply hWnab
  refine IsMulCommutative.of_comm fun a b => ?_
  obtain ⟨x, rfl⟩ := F.e.surjective a
  obtain ⟨y, rfl⟩ := F.e.surjective b
  rw [← map_mul, ← map_mul]
  congr 1
  funext j
  exact (hj j).is_comm.comm (x j) (y j)

theorem exists_not_commute (hWnab : ¬ IsMulCommutative ↥W) (i : Fin F.r) :
    ∃ a b : ↥(F.S i), a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact F.not_isMulCommutative hWnab i (IsMulCommutative.of_comm h)

theorem not_dvd_three (h3W : ¬ 3 ∣ Nat.card ↥W) (i : Fin F.r) :
    ¬ 3 ∣ Nat.card ↥(F.S i) := by
  intro h3
  apply h3W
  have h1 : Nat.card ↥(F.S i) ∣ Nat.card ↥W := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.le_W i)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card ((F.S i).subgroupOf W)
  exact h3.trans h1

theorem isKGroup (hWK : CFSG.Open.IsKGroup ↥W) (i : Fin F.r) :
    CFSG.Open.IsKGroup ↥(F.S i) :=
  hWK.of_le (F.le_W i)

theorem suzuki [Finite E]
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    (hWnab : ¬ IsMulCommutative ↥W) (hWK : CFSG.Open.IsKGroup ↥W)
    (h3W : ¬ 3 ∣ Nat.card ↥W) (i : Fin F.r) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel ↥(F.S i) 2 f :=
  hSz ↥(F.S i) (F.simple i) (fun h => F.not_isMulCommutative hWnab i (isMulCommutative_iff.mpr h))
    (F.isKGroup hWK i) (F.not_dvd_three h3W i)

theorem center_eq_bot [Finite E] (F : Uc147Factors E W) (hWnab : ¬ IsMulCommutative ↥W) :
    Subgroup.center ↥W = ⊥ := by
  have hcenterS : ∀ i, Subgroup.center ↥(F.S i) = ⊥ := by
    intro i
    have := F.simple i
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥(F.S i)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := F.exists_not_commute hWnab i
      have ha : a ∈ Subgroup.center ↥(F.S i) := h.ge (Subgroup.mem_top a)
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := F.e.surjective z
  have hx : x = 1 := by
    funext i
    have hxi : x i ∈ Subgroup.center ↥(F.S i) := by
      rw [Subgroup.mem_center_iff]
      intro t
      have h1 : F.e (Pi.mulSingle i t) * F.e x = F.e x * F.e (Pi.mulSingle i t) :=
        Subgroup.mem_center_iff.mp hz _
      rw [← map_mul, ← map_mul, F.e.injective.eq_iff] at h1
      have h2 := congrFun h1 i
      simpa using h2
    rw [hcenterS i] at hxi
    exact Subgroup.mem_bot.mp hxi
  rw [hx, map_one]
  rfl

end Uc147Factors

noncomputable def uc147_factors {E : Type} [Group E] [Finite E] {W : Subgroup E} [W.Normal]
    (hWne : W ≠ ⊥)
    (hWmin : ∀ M' : Subgroup E, M'.Normal → M' ≤ W → M' = ⊥ ∨ M' = W) :
    Uc147Factors E W :=
  Classical.choice <| by
    obtain ⟨r₀, S, hr₀, hSle, hSsimple, hSconj, hSnormal, e, he⟩ :=
      CFSG.LocalCores.minimal_normal_simple_factors (N := W) ‹W.Normal› hWne hWmin
    exact ⟨⟨r₀, S, hr₀, hSle, hSsimple, hSconj, hSnormal, e, he⟩⟩

omit [Finite G] in
theorem uc147Image_not_isMulCommutative (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (hnab : ∃ v ∈ V, ∃ w ∈ V, v * w * v⁻¹ * w⁻¹ ∉ V₀) :
    ¬ IsMulCommutative ↥(uc147Image V B R V₀) := by
  intro hab
  obtain ⟨v, hv, w, hw, hvw⟩ := hnab
  have h1 : uc147MapImage V B R V₀
      (⟨v, hv⟩ * ⟨w, hw⟩ * ⟨v, hv⟩⁻¹ * ⟨w, hw⟩⁻¹ : ↥V) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [(IsMulCommutative.is_comm (M := ↥(uc147Image V B R V₀))).comm
      (uc147MapImage V B R V₀ ⟨v, hv⟩) (uc147MapImage V B R V₀ ⟨w, hw⟩)]
    group
  have h2 : ((⟨v, hv⟩ * ⟨w, hw⟩ * ⟨v, hv⟩⁻¹ * ⟨w, hw⟩⁻¹ : ↥V) : G) ∈ V₀ :=
    (uc147Map_eq_one V B R V₀ _).1 (congrArg Subtype.val h1)
  exact hvw (by simpa using h2)

omit [Finite G] in
theorem uc147Image_ne_bot (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (hnab : ∃ v ∈ V, ∃ w ∈ V, v * w * v⁻¹ * w⁻¹ ∉ V₀) :
    uc147Image V B R V₀ ≠ ⊥ := by
  intro hbot
  apply uc147Image_not_isMulCommutative V B R V₀ hnab
  rw [hbot]
  exact IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _

omit [Finite G] in
theorem uc147Image_minimal_normal (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (hVnorm : uc147Ambient V B R ≤ Subgroup.normalizer (V : Set G))
    (hV₀V : V₀ ≤ V)
    (hmin : ∀ U : Subgroup G, V₀ ≤ U → U ≤ V → V ≤ normalizer (U : Set G) →
      B ≤ normalizer (U : Set G) → R ≤ normalizer (U : Set G) → U = V₀ ∨ U = V) :
    ∀ M' : Subgroup (uc147Section V B R V₀), M'.Normal → M' ≤ uc147Image V B R V₀ →
      M' = ⊥ ∨ M' = uc147Image V B R V₀ := by
  classical
  have hVn : (V.subgroupOf (uc147Ambient V B R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left.trans le_sup_left)).2 hVnorm
  intro M' hM'n hM'W
  set U : Subgroup ↥(uc147Ambient V B R) := M'.comap (uc147Quot V B R V₀) with hUdef
  have hUn : U.Normal := hM'n.comap _
  have hcomapW : (uc147Image V B R V₀).comap (uc147Quot V B R V₀) =
      V.subgroupOf (uc147Ambient V B R) := by
    show ((V.subgroupOf (uc147Ambient V B R)).map (uc147Quot V B R V₀)).comap
      (uc147Quot V B R V₀) = V.subgroupOf (uc147Ambient V B R)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono _ hV₀V)
  have hUle : U ≤ V.subgroupOf (uc147Ambient V B R) :=
    (Subgroup.comap_mono hM'W).trans_eq hcomapW
  have hV₀U : V₀.subgroupOf (uc147Ambient V B R) ≤ U := by
    intro x hx
    show uc147Quot V B R V₀ x ∈ M'
    have hx1 : uc147Quot V B R V₀ x = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact M'.one_mem
  set U' : Subgroup G := U.map (uc147Ambient V B R).subtype with hU'def
  have hV₀Vt : V₀ ≤ uc147Ambient V B R := hV₀V.trans (le_sup_left.trans le_sup_left)
  have hV₀U' : V₀ ≤ U' := fun x hx =>
    Subgroup.mem_map_of_mem _ (hV₀U (show (⟨x, hV₀Vt hx⟩ : ↥(uc147Ambient V B R)) ∈
      V₀.subgroupOf (uc147Ambient V B R) from hx))
  have hU'V : U' ≤ V := by
    refine (Subgroup.map_mono hUle).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hVtU' : uc147Ambient V B R ≤ Subgroup.normalizer (U' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem _ (hUn.conj_mem u hu ⟨g, hg⟩)
  rcases hmin U' hV₀U' hU'V ((le_sup_left.trans le_sup_left).trans hVtU')
    ((le_sup_right.trans le_sup_left).trans hVtU') (le_sup_right.trans hVtU') with h | h
  · left
    have hUeq : U = V₀.subgroupOf (uc147Ambient V B R) := by
      rw [← Subgroup.comap_map_eq_self_of_injective (uc147Ambient V B R).subtype_injective U,
        ← hU'def, h]
      rfl
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (V₀.subgroupOf (uc147Ambient V B R)) x
    have hy : y ∈ U := Subgroup.mem_comap.mpr hx
    rw [hUeq] at hy
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  · right
    have hUeq : U = V.subgroupOf (uc147Ambient V B R) := by
      rw [← Subgroup.comap_map_eq_self_of_injective (uc147Ambient V B R).subtype_injective U,
        ← hU'def, h]
      rfl
    refine le_antisymm hM'W ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyU : y ∈ U := hUeq ▸ hy
    exact Subgroup.mem_comap.mp (hUdef ▸ hyU)

abbrev uc147SubgroupImage (V B R V₀ : Subgroup G) [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (H : Subgroup G) : Subgroup (uc147Section V B R V₀) :=
  (H.subgroupOf (uc147Ambient V B R)).map (uc147Quot V B R V₀)

abbrev uc147Gamma (D : Data G) (V B R V₀ : Subgroup G)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal] : Subgroup (uc147Section V B R V₀) :=
  ((V ⊓ D.M).subgroupOf V).map (uc147Map V B R V₀)

theorem uc147_centralizer_conjB_le {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ}
    {r p : ℕ} {A X B R : Subgroup G}
    (c : Ctx147 D L n r p A X B R) (hsp3 : IsStronglyPEmbedded 3 D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (x : ↥R) (v : ↥V)
    (hv : (uc147MapImage V B R V₀ v : uc147Section V B R V₀) ∈
      Subgroup.centralizer (uc147SubgroupImage V B R V₀
        (B.map (MulAut.conj x.1).toMonoidHom) : Set (uc147Section V B R V₀))) :
    uc147Map V B R V₀ v ∈ uc147Gamma D V B R V₀ := by
  classical
  let E := uc147Section V B R V₀
  let φ : ↥V →* E := uc147Map V B R V₀
  let φW : ↥V →* ↥(uc147Image V B R V₀) := uc147MapImage V B R V₀
  let mk : ↥(uc147Ambient V B R) →* E := uc147Quot V B R V₀
  let Vt : Subgroup G := uc147Ambient V B R
  let Γ : Subgroup E := uc147Gamma D V B R V₀
  let Hx : ↥R → Subgroup E := fun x =>
    uc147SubgroupImage V B R V₀ (B.map (MulAut.conj x.1).toMonoidHom)
  let Hi : Fin 2 → Subgroup E := fun i => uc147SubgroupImage V B R V₀ (R ⊓ L i)
  have hφ_one : ∀ v : ↥V, φ v = 1 ↔ (v : G) ∈ V₀ := uc147Map_eq_one V B R V₀
  have hVVt : V ≤ Vt := le_sup_left.trans le_sup_left
  have hRVt : R ≤ Vt := le_sup_right
  have hBVt : B ≤ Vt := le_sup_right.trans le_sup_left
  refine Subgroup.mem_map.mpr ⟨v, ?_, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ⟨v.2, ?_⟩
  refine Ctx147.mem_M_of_conj_commutator_mem c hsp3 s (x := x.1) x.2 (v := (v : G)) v.2
    (fun b hb => ?_)
  have hyVt : x.1 * b * x.1⁻¹ ∈ Vt :=
    Vt.mul_mem (Vt.mul_mem (hRVt x.2) (hBVt hb)) (Vt.inv_mem (hRVt x.2))
  have hmemB : x.1 * b * x.1⁻¹ ∈ B.map (MulAut.conj x.1).toMonoidHom := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj x.1).toMonoidHom hb
    simpa [MulAut.conj_apply] using h
  have hmemHx : mk ⟨x.1 * b * x.1⁻¹, hyVt⟩ ∈ Hx x :=
    Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hmemB)
  have hcomm : (mk ⟨x.1 * b * x.1⁻¹, hyVt⟩ : E) * (φW v : E) =
      (φW v : E) * mk ⟨x.1 * b * x.1⁻¹, hyVt⟩ :=
    (Subgroup.mem_centralizer_iff.mp hv) _ hmemHx
  have hyN : x.1 * b * x.1⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (s.hRV x.2) (s.hBV hb))
      ((Subgroup.normalizer (V : Set G)).inv_mem (s.hRV x.2))
  have hyv : x.1 * b * x.1⁻¹ * (v : G) * (x.1 * b * x.1⁻¹)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hyN (v : G)).mp v.2
  have h1 : φ (⟨x.1 * b * x.1⁻¹ * (v : G) * (x.1 * b * x.1⁻¹)⁻¹, hyv⟩ : ↥V) = φ v := by
    show mk ⟨_, hVVt hyv⟩ = mk ⟨v, hVVt v.2⟩
    have h2 : (⟨x.1 * b * x.1⁻¹ * (v : G) * (x.1 * b * x.1⁻¹)⁻¹, hVVt hyv⟩ : ↥Vt) =
        ⟨x.1 * b * x.1⁻¹, hyVt⟩ * ⟨v, hVVt v.2⟩ * ⟨x.1 * b * x.1⁻¹, hyVt⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, map_mul, map_mul, map_inv]
    show (mk ⟨x.1 * b * x.1⁻¹, hyVt⟩ : E) * (φW v : E) *
      (mk ⟨x.1 * b * x.1⁻¹, hyVt⟩)⁻¹ = (φW v : E)
    rw [hcomm]
    group
  have h2 : ((⟨x.1 * b * x.1⁻¹ * (v : G) * (x.1 * b * x.1⁻¹)⁻¹, hyv⟩ : ↥V) * v⁻¹ : ↥V).1
      ∈ V₀ := by
    refine (hφ_one _).1 ?_
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

theorem uc147_centralizer_Ri_le {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ}
    {r p : ℕ} {A X B R : Subgroup G}
    (c : Ctx147 D L n r p A X B R) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    [(V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (i : Fin 2) (v : ↥V)
    (hv : (uc147MapImage V B R V₀ v : uc147Section V B R V₀) ∈
      Subgroup.centralizer (uc147SubgroupImage V B R V₀ (R ⊓ L i) :
        Set (uc147Section V B R V₀))) :
    uc147Map V B R V₀ v ∈ uc147Gamma D V B R V₀ := by
  classical
  let E := uc147Section V B R V₀
  let φ : ↥V →* E := uc147Map V B R V₀
  let φW : ↥V →* ↥(uc147Image V B R V₀) := uc147MapImage V B R V₀
  let mk : ↥(uc147Ambient V B R) →* E := uc147Quot V B R V₀
  let Vt : Subgroup G := uc147Ambient V B R
  let Γ : Subgroup E := uc147Gamma D V B R V₀
  let Hx : ↥R → Subgroup E := fun x =>
    uc147SubgroupImage V B R V₀ (B.map (MulAut.conj x.1).toMonoidHom)
  let Hi : Fin 2 → Subgroup E := fun i => uc147SubgroupImage V B R V₀ (R ⊓ L i)
  have hφ_one : ∀ v : ↥V, φ v = 1 ↔ (v : G) ∈ V₀ := uc147Map_eq_one V B R V₀
  have hVVt : V ≤ Vt := le_sup_left.trans le_sup_left
  have hRVt : R ≤ Vt := le_sup_right
  have hBVt : B ≤ Vt := le_sup_right.trans le_sup_left
  refine Subgroup.mem_map.mpr ⟨v, ?_, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ⟨v.2, ?_⟩
  refine Ctx147.mem_M_of_commutator_mem_inf c hRi s i (v := (v : G)) v.2 (fun y hy => ?_)
  have hyR : y ∈ R := (inf_le_left : R ⊓ L i ≤ R) hy
  have hyVt : y ∈ Vt := hRVt hyR
  have hmemHi : mk ⟨y, hyVt⟩ ∈ Hi i :=
    Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hy)
  have hcomm : (mk ⟨y, hyVt⟩ : E) * (φW v : E) = (φW v : E) * mk ⟨y, hyVt⟩ :=
    (Subgroup.mem_centralizer_iff.mp hv) _ hmemHi
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := s.hRV hyR
  have hyv : y * (v : G) * y⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hyN (v : G)).mp v.2
  have h1 : φ (⟨y * (v : G) * y⁻¹, hyv⟩ : ↥V) = φ v := by
    show mk ⟨_, hVVt hyv⟩ = mk ⟨v, hVVt v.2⟩
    have h2 : (⟨y * (v : G) * y⁻¹, hVVt hyv⟩ : ↥Vt) =
        ⟨y, hyVt⟩ * ⟨v, hVVt v.2⟩ * ⟨y, hyVt⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, map_mul, map_mul, map_inv]
    show (mk ⟨y, hyVt⟩ : E) * (φW v : E) * (mk ⟨y, hyVt⟩)⁻¹ = (φW v : E)
    rw [hcomm]
    group
  have h2 : ((⟨y * (v : G) * y⁻¹, hyv⟩ : ↥V) * v⁻¹ : ↥V).1 ∈ V₀ := by
    refine (hφ_one _).1 ?_
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

omit [Finite G] in
theorem uc147WSimpleFactor
    {V V₀ : Subgroup G}
    [hV₀n : (V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (F : Uc147Factors (uc147Section V B R V₀) (uc147Image V B R V₀))
    [NeZero F.r] (h1 : F.r = 1) :
    F.S 0 = uc147Image V B R V₀ := by
  have hsub1 : Subsingleton (Fin F.r) := by rw [h1]; infer_instance
  refine le_antisymm (F.le_W 0) ?_
  refine CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.le_of_forall_factor_le F.e_single
    (H := F.S 0) fun i => ?_
  rw [Subsingleton.elim i 0]

theorem uc147_section_simple_case
    (c : Ctx147 D L n r p A X B R) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    [hV₀n : (V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (F : Uc147Factors (uc147Section V B R V₀) (uc147Image V B R V₀))
    (hSsz : ∀ i, ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (F.S i) 2 f)
    (hBRVt : B ⊔ R ≤ uc147Ambient V B R)
    (hcenterW : Subgroup.center ↥(uc147Image V B R V₀) = ⊥)
    (hVnorm : uc147Ambient V B R ≤ Subgroup.normalizer (V : Set G))
    (hr1 : F.r = 1) : V ≤ D.M := by
  classical
  let Vt : Subgroup G := uc147Ambient V B R
  let E := uc147Section V B R V₀
  let mk : ↥Vt →* E := uc147Quot V B R V₀
  let W : Subgroup E := uc147Image V B R V₀
  let φ : ↥V →* E := uc147Map V B R V₀
  have hφ_one : ∀ v : ↥V, φ v = 1 ↔ (v : G) ∈ V₀ := uc147Map_eq_one V B R V₀
  have hφmem : ∀ v : ↥V, φ v ∈ W := uc147Map_mem_image V B R V₀
  have hVVt : V ≤ Vt := le_sup_left.trans le_sup_left
  have hRVt : R ≤ Vt := le_sup_right
  have hWn : W.Normal := uc147Image_normal V B R V₀ hVnorm
  have : NeZero F.r := ⟨by omega⟩
  have hS0W : F.S 0 = W := uc147WSimpleFactor (hV₀n := hV₀n) F hr1
  obtain ⟨f, hf⟩ := hSsz 0
  have hszW : CFSG.Blueprint.SuzukiModel ↥W 2 f := hS0W ▸ hf
  let cj : ↥W →* MulAut ↥W := MulAut.conj
  let actBR : ↥(B ⊔ R) →* MulAut ↥W :=
    (MulAut.conjNormal).comp (mk.comp (Subgroup.inclusion hBRVt))
  let actR : ↥R →* MulAut ↥W := actBR.comp (Subgroup.inclusion (le_sup_right : R ≤ B ⊔ R))
  have hactR_val : ∀ r : ↥R, actR r = actBR ⟨(r : G), Subgroup.mem_sup_right r.2⟩ :=
    fun r => rfl
  have hInn : commutator (MulAut ↥W) ≤ cj.range :=
    CFSG.RankThree.PartTwo.KFacts.commutator_le_inner_of_suzukiModel hszW
  have hRB' : ⁅R.subgroupOf (B ⊔ R), B.subgroupOf (B ⊔ R)⁆ = R.subgroupOf (B ⊔ R) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (B ⊔ R))
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right : R ≤ B ⊔ R),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : B ≤ B ⊔ R), c.hRB]
  have hRangeEq : actR.range = (R.subgroupOf (B ⊔ R)).map actBR := by
    ext m
    constructor
    · rintro ⟨r, rfl⟩
      exact Subgroup.mem_map_of_mem actBR (Subgroup.mem_subgroupOf.mpr r.2)
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩,
        congrArg actBR (Subtype.ext rfl)⟩
  have hRangeInn : actR.range ≤ cj.range := by
    rw [hRangeEq, ← hRB', Subgroup.map_commutator]
    exact (Subgroup.commutator_mono le_top le_top).trans hInn
  have hinjConj : Function.Injective cj := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : ∀ z : ↥W, x * z * x⁻¹ = z := fun z => by
      simpa only [cj, MulAut.conj_apply, MulAut.one_apply] using
        congrArg (fun f : MulAut ↥W => f z) hx
    have h1 : x ∈ Subgroup.center ↥W := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h2 : x * z = z * x := by
        calc x * z = (x * z * x⁻¹) * x := by group
          _ = z * x := by rw [hx' z]
      exact h2.symm
    rw [hcenterW] at h1
    exact Subgroup.mem_bot.mp h1
  let Q : Subgroup ↥W := actR.range.comap cj
  have hQmap : Q.map cj = actR.range := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hRangeInn
  have hRtop : CFSG.Open.IsElemAbelian 7 (⊤ : Subgroup ↥R) := by
    obtain ⟨hc, hp⟩ := c.frame.1
    refine ⟨⟨⟨fun a b => Subtype.ext (hc.is_comm.comm a.1 b.1)⟩⟩, fun x _ => ?_⟩
    exact Subtype.ext (hp x.1 x.2)
  have hRangeEa : CFSG.Open.IsElemAbelian 7 actR.range := by
    simpa only [MonoidHom.range_eq_map] using
      CFSG.SectionRank.isElemAbelian_map (E := ⊤) hRtop actR
  have hQea : CFSG.Open.IsElemAbelian 7 Q := by
    obtain ⟨hc, hp⟩ := hRangeEa
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinjConj
      simpa only [map_mul, Subgroup.coe_mul] using
        Subtype.ext_iff.mp (hc.is_comm.comm (⟨cj (a.1 : ↥W), a.2⟩ : ↥actR.range)
          ⟨cj (b.1 : ↥W), b.2⟩)
    · refine hinjConj ?_
      rw [map_pow, map_one]
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
        hp (cj x) hx
  have hcardQ : Nat.card ↥Q = Nat.card ↥actR.range := by
    rw [← hQmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Q cj hinjConj).toEquiv
  have hQle : Nat.card ↥Q ≤ 7 := by
    obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hQea).exists_card_eq
    have hk1 : k ≤ 1 := (CFSG.SectionRank.le_pRank (by norm_num : 1 < 7) le_top hQea hk).trans
      (CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hszW
        (show (7:ℕ).Prime by norm_num) (by norm_num))
    calc Nat.card ↥Q = 7 ^ k := hk
      _ ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 7 := pow_one 7
  have hcardR : Nat.card ↥R = 49 := c.frame.2.1
  have hcard := card_ker_mul_card_range actR
  have hKne : actR.ker ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥actR.ker = 1 := by rw [hbot]; simp
    have h2 : Nat.card ↥actR.range = 49 := by
      rw [h1, one_mul, hcardR] at hcard
      exact hcard
    have h3 : Nat.card ↥actR.range ≤ 7 := hcardQ ▸ hQle
    omega
  have hKne' : (actR.ker.map R.subtype : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hKne
    have h1 : actR.ker.map R.subtype = ⊥ := hbot
    rwa [Subgroup.map_eq_bot_iff_of_injective actR.ker R.subtype_injective] at h1
  have hKinv : B ≤ Subgroup.normalizer ((actR.ker.map R.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    have hbR : (b : G) ∈ Subgroup.normalizer (R : Set G) := c.frame.2.2.2.1 hb
    have hmemR : b * (r : G) * b⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hbR (r : G)).mp r.2
    have hker : (⟨b * (r : G) * b⁻¹, hmemR⟩ : ↥R) ∈ actR.ker := by
      have hbeq : (⟨b * (r : G) * b⁻¹, Subgroup.mem_sup_right hmemR⟩ : ↥(B ⊔ R)) =
          ⟨b, Subgroup.mem_sup_left hb⟩ * ⟨(r : G), Subgroup.mem_sup_right r.2⟩ *
            ⟨b, Subgroup.mem_sup_left hb⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
      have hρ : actBR ⟨(r : G), Subgroup.mem_sup_right r.2⟩ = actR r := rfl
      rw [MonoidHom.mem_ker]
      show actBR ⟨b * (r : G) * b⁻¹, Subgroup.mem_sup_right hmemR⟩ = 1
      rw [hbeq, map_mul, map_mul, map_inv, hρ, MonoidHom.mem_ker.mp hr, mul_one,
        mul_inv_cancel]
    exact Subgroup.mem_map_of_mem R.subtype hker
  have hstep : ∀ i : Fin 2, R ⊓ L i ≤ actR.ker.map R.subtype → V ≤ D.M := by
    intro i hi v hv
    refine Ctx147.mem_M_of_commutator_mem_inf c hRi s i hv (fun y hy => ?_)
    have hyR : y ∈ R := (inf_le_left : R ⊓ L i ≤ R) hy
    obtain ⟨r, hr, hrval⟩ := Subgroup.mem_map.mp (hi hy)
    have hact : actR r = 1 := MonoidHom.mem_ker.mp hr
    have hyv : y * v * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (s.hRV hyR) v).mp hv
    have hactBR : actBR ⟨(r : G), Subgroup.mem_sup_right r.2⟩ =
        MulAut.conjNormal ((QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨(r : G), hRVt r.2⟩) := rfl
    have h2 : ((QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨(r : G), hRVt r.2⟩) *
        φ ⟨v, hv⟩ * ((QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨(r : G), hRVt r.2⟩)⁻¹
        = φ ⟨v, hv⟩ := by
      have h3 : MulAut.conjNormal ((QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨(r : G), hRVt r.2⟩)
          ⟨φ ⟨v, hv⟩, hφmem ⟨v, hv⟩⟩ = ⟨φ ⟨v, hv⟩, hφmem ⟨v, hv⟩⟩ := by
        rw [← hactBR, ← hactR_val, hact, MulAut.one_apply]
      have h4 := congrArg Subtype.val h3
      rwa [MulAut.conjNormal_apply] at h4
    have h5 : φ (⟨y * v * y⁻¹, hyv⟩ : ↥V) = φ ⟨v, hv⟩ := by
      have hcast : (⟨y * v * y⁻¹, hVVt hyv⟩ : ↥Vt) =
          ⟨(r : G), hRVt r.2⟩ * ⟨v, hVVt hv⟩ * ⟨(r : G), hRVt r.2⟩⁻¹ := by
        apply Subtype.ext
        show y * v * y⁻¹ = (r : G) * v * (r : G)⁻¹
        rw [← hrval]
        rfl
      show (QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨y * v * y⁻¹, hVVt hyv⟩ = φ ⟨v, hv⟩
      rw [hcast, map_mul, map_mul, map_inv]
      exact h2
    have h6 : φ ((⟨y * v * y⁻¹, hyv⟩ : ↥V) * ⟨v, hv⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h5, mul_inv_cancel]
    have h7 : ((⟨y * v * y⁻¹, hyv⟩ : ↥V) * ⟨v, hv⟩⁻¹ : ↥V).1 ∈ V₀ := (hφ_one _).1 h6
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h7
  rcases c.frame.2.2.2.2.2 (actR.ker.map R.subtype) (Subgroup.map_subtype_le _) hKinv
    hKne' with hcase | hcase
  · exact hstep 0 hcase
  · exact hstep 1 hcase

theorem uc147_section_composite_case
    (c : Ctx147 D L n r p A X B R) (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    [hV₀n : (V₀.subgroupOf (uc147Ambient V B R)).Normal]
    (F : Uc147Factors (uc147Section V B R V₀) (uc147Image V B R V₀))
    (hWnab : ¬ IsMulCommutative ↥(uc147Image V B R V₀))
    (hWmin : ∀ M' : Subgroup (uc147Section V B R V₀), M'.Normal →
      M' ≤ uc147Image V B R V₀ → M' = ⊥ ∨ M' = uc147Image V B R V₀)
    (hVnorm : uc147Ambient V B R ≤ Subgroup.normalizer (V : Set G))
    (hr2 : 2 ≤ F.r) : V ≤ D.M := by
  classical
  let Vt : Subgroup G := uc147Ambient V B R
  let E := uc147Section V B R V₀
  let mk : ↥Vt →* E := uc147Quot V B R V₀
  let W : Subgroup E := uc147Image V B R V₀
  let φ : ↥V →* E := uc147Map V B R V₀
  let φW : ↥V →* ↥W := uc147MapImage V B R V₀
  let r₀ : ℕ := F.r
  let S : Fin r₀ → Subgroup E := F.S
  have hφ_one : ∀ v : ↥V, φ v = 1 ↔ (v : G) ∈ V₀ := uc147Map_eq_one V B R V₀
  have hφmem : ∀ v : ↥V, φ v ∈ W := uc147Map_mem_image V B R V₀
  have hφW_val : ∀ v : ↥V, ((φW v : ↥W) : E) = φ v := uc147MapImage_apply V B R V₀
  have hker : φW.ker = V₀.subgroupOf V := uc147MapImage_ker V B R V₀
  have hφW_surj : Function.Surjective φW := uc147MapImage_surjective V B R V₀
  have hVVt : V ≤ Vt := le_sup_left.trans le_sup_left
  have hRVt : R ≤ Vt := le_sup_right
  have hBVt : B ≤ Vt := le_sup_right.trans le_sup_left
  have hBRVt : B ⊔ R ≤ Vt := sup_le hBVt hRVt
  have hWn : W.Normal := uc147Image_normal V B R V₀ hVnorm
  have hSle : ∀ i, S i ≤ W := F.le_W
  have hSsimple : ∀ i, IsSimpleGroup (S i) := F.simple
  let e : ((i : Fin r₀) → S i) ≃* W := F.e
  have he : ∀ (i : Fin r₀) (x : (j : Fin r₀) → S j),
      (∀ j, j ≠ i → x j = 1) → (e x : E) = x i := by
    intro i x hx
    exact F.e_single i x hx
  have hSnab : ∀ i, ∃ a b : ↥(S i), a * b ≠ b * a := F.exists_not_commute hWnab
  have hTN : ⨆ i, S i = W := by
    refine le_antisymm (iSup_le hSle) ?_
    exact CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.le_of_forall_factor_le he
      (H := ⨆ i, S i) fun i => le_iSup S i
  have hTcomm : Pairwise fun i j : Fin r₀ => ∀ x y : E, x ∈ S i → y ∈ S j → Commute x y :=
    fun i j hij x y hx hy =>
      CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.commute_of_mem_of_ne he hij hx hy
  have hperm : ∀ (g : E) (i : Fin r₀), ∃ k, (S i).map (MulAut.conj g).toMonoidHom = S k := by
    intro g i
    refine CFSG.LocalAnalysis.GorensteinLyons.SteinbergCH.exists_map_conj_eq_of_mem_normalizer
      hTN hTcomm hSsimple hSnab ?_ i
    exact (Subgroup.normalizer_eq_top_iff.mpr hWn).ge (Subgroup.mem_top g)
  have hconj_comm : ∀ (g g' : E) (i : Fin r₀),
      (S i).map (MulAut.conj g).toMonoidHom ≠ (S i).map (MulAut.conj g').toMonoidHom →
      ∀ x ∈ (S i).map (MulAut.conj g).toMonoidHom,
        ∀ y ∈ (S i).map (MulAut.conj g').toMonoidHom, Commute x y := by
    intro g g' i hne x hx y hy
    obtain ⟨k, hk⟩ := hperm g i
    obtain ⟨k', hk'⟩ := hperm g' i
    have hkk' : k ≠ k' := by
      intro h
      exact hne (by rw [hk, hk', h])
    rw [hk] at hx
    rw [hk'] at hy
    exact hTcomm hkk' x y hx hy
  let Γ : Subgroup E := ((V ⊓ D.M).subgroupOf V).map φ
  have hΓle : Γ ≤ W := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hφmem v
  have hΓ_final : Γ = W → V ≤ D.M := by
    intro hΓeq v hv
    have hvW : φ ⟨v, hv⟩ ∈ W := hφmem _
    rw [← hΓeq] at hvW
    obtain ⟨q, hq, hqv⟩ := Subgroup.mem_map.mp hvW
    have hqM : (q : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp hq).2
    have hkerV : (⟨v, hv⟩ * q⁻¹ : ↥V) ∈ V₀.subgroupOf V := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
      have hq' : φW q = φW ⟨v, hv⟩ := Subtype.ext hqv
      rw [hq', mul_inv_cancel]
    have hVM : ((⟨v, hv⟩ * q⁻¹ : ↥V) : G) ∈ D.M := s.hV₀M (Subgroup.mem_subgroupOf.mp hkerV)
    have hveq : (v : G) = ((⟨v, hv⟩ * q⁻¹ : ↥V) : G) * (q : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hveq]
    exact D.M.mul_mem hVM hqM
  let Hx : ↥R → Subgroup E := fun x =>
    ((B.map (MulAut.conj x.1).toMonoidHom).subgroupOf Vt).map mk
  let Hi : Fin 2 → Subgroup E := fun i => ((R ⊓ L i).subgroupOf Vt).map mk
  have hΓ_Cx : ∀ (x : ↥R) (v : ↥V),
      (φW v : E) ∈ Subgroup.centralizer (Hx x : Set E) → φ v ∈ Γ :=
    fun x v hv => uc147_centralizer_conjB_le c hsp3 s x v hv
  have hΓ_Ci : ∀ (i : Fin 2) (v : ↥V),
      (φW v : E) ∈ Subgroup.centralizer (Hi i : Set E) → φ v ∈ Γ :=
    fun i v hv => uc147_centralizer_Ri_le c hRi s i v hv
  have hbcard : Nat.card B = 3 := c.card_B
  obtain ⟨b, hbB, hbne⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      exact hx1 (h x hx)
    rw [hbot, card_bot] at hbcard
    exact absurd hbcard (by norm_num)
  have hfixb : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ R, x * y * x⁻¹ = y → y = 1 := by
    intro x hx hx1 y hy hxy
    have hx3 : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        rw [← c.card_B]
        simpa using orderOf_dvd_natCard (⟨x, hx⟩ : ↥B)
      rcases (Nat.dvd_prime (show (3 : ℕ).Prime by norm_num)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hgen : B = Subgroup.zpowers x := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_).symm
      rw [Nat.card_zpowers, hx3, c.card_B]
    have hxy' : Commute x y := by
      rw [commute_iff_eq]
      have h2 : x * y = y * x := by
        have h3 := congrArg (fun w => w * x) hxy
        simpa [mul_assoc] using h3
      exact h2
    have hcy : y ∈ Subgroup.centralizer (B : Set G) := by
      rw [hgen, Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hxy'.zpow_left m).eq
    have h1 : y ∈ R ⊓ Subgroup.centralizer (B : Set G) := Subgroup.mem_inf.mpr ⟨hy, hcy⟩
    rw [c.frame.2.2.2.2.1] at h1
    exact Subgroup.mem_bot.mp h1
  have hTtop : W ⊔ ((B ⊔ R).subgroupOf Vt).map mk = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (V₀.subgroupOf Vt) g
    have hy : (y : G) ∈ (↑(V ⊔ (B ⊔ R)) : Set G) := by
      rw [← sup_assoc]
      exact y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V (B ⊔ R) (sup_le s.hBV s.hRV)] at hy
    obtain ⟨vv, hvv, tt, htt, hvt⟩ := hy
    have httVt : tt ∈ Vt := hBRVt htt
    have hvvVt : vv ∈ Vt := hVVt hvv
    have heq : (QuotientGroup.mk' (V₀.subgroupOf Vt)) y =
        (QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨vv, hvvVt⟩ *
          (QuotientGroup.mk' (V₀.subgroupOf Vt)) ⟨tt, httVt⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hvt.symm)
    rw [heq]
    exact (W ⊔ ((B ⊔ R).subgroupOf Vt).map mk).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hvv)))
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr htt)))
  have hSΓ : ∀ i, S i ≤ Γ := by
    intro i
    let Q : Subgroup G := ((Subgroup.normalizer (S i : Set E)).comap mk).map Vt.subtype
    have hQ_mem (g : G) (hg : g ∈ Vt) :
        mk ⟨g, hg⟩ ∈ Subgroup.normalizer (S i : Set E) ↔ g ∈ Q := by
      constructor
      · intro h
        exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr h, rfl⟩
      · intro h
        obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp h
        have hxval : x = ⟨g, hg⟩ := Subtype.ext hxg
        rw [← hxval]
        exact Subgroup.mem_comap.mp hx
    have hQ_trans (H : Subgroup G) (hHVt : H ≤ Vt) :
        (H.subgroupOf Vt).map mk ≤ Subgroup.normalizer (S i : Set E) ↔ H ≤ Q := by
      constructor
      · intro h g hg
        have hx : (⟨g, hHVt hg⟩ : ↥Vt) ∈ H.subgroupOf Vt := Subgroup.mem_subgroupOf.mpr hg
        exact (hQ_mem g (hHVt hg)).mp (h (Subgroup.mem_map_of_mem mk hx))
      · intro h y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact (hQ_mem (x : G) x.2).mpr (h (Subgroup.mem_subgroupOf.mp hx))
    have hdisj : Pairwise fun i j : Fin r₀ => S i ⊓ S j = ⊥ := by
      intro i j hij
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.eq_one_of_mem_of_mem he hij
        (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
    have hne : ∀ i, S i ≠ ⊥ := by
      intro i hbot
      have h2 : 2 ≤ Nat.card ↥(S i) := by
        exact Finite.one_lt_card_iff_nontrivial.mpr (hSsimple i).toNontrivial
      rw [hbot] at h2
      simp at h2
    obtain ⟨y, hyR, hyQ⟩ : ∃ y ∈ R, ¬ B.map (MulAut.conj y).toMonoidHom ≤ Q := by
      by_contra h
      push Not at h
      have hBRQ : B ⊔ R ≤ Q :=
        sup_le_of_forall_map_conj_le c.frame.2.2.2.1 ⟨b, hbB, hbne⟩ hfixb h
      have hle : ((B ⊔ R).subgroupOf Vt).map mk ≤ Subgroup.normalizer (S i : Set E) :=
        (hQ_trans (B ⊔ R) hBRVt).mpr hBRQ
      exact not_le_normalizer_factor hr2 hTN hTcomm hdisj hne hWmin hTtop i hle
    have hfixHx : ∀ (x : ↥R) (w : E), w ∈ W →
        w ∈ Subgroup.centralizer (Hx x : Set E) → w ∈ Γ := by
      intro x w hw hc
      obtain ⟨v, hv⟩ := hφW_surj ⟨w, hw⟩
      have hval : (φW v : E) = w := congrArg Subtype.val hv
      rw [← hval] at hc ⊢
      exact hΓ_Cx x v hc
    have hfixHi : ∀ (j : Fin 2) (w : E), w ∈ W →
        w ∈ Subgroup.centralizer (Hi j : Set E) → w ∈ Γ := by
      intro j w hw hc
      obtain ⟨v, hv⟩ := hφW_surj ⟨w, hw⟩
      have hval : (φW v : E) = w := congrArg Subtype.val hv
      rw [← hval] at hc ⊢
      exact hΓ_Ci j v hc
    have hyVt : y ∈ Vt := hRVt hyR
    have hbVt : b ∈ Vt := hBVt hbB
    have hmem : y * b * y⁻¹ ∈ Vt :=
      Vt.mul_mem (Vt.mul_mem hyVt hbVt) (Vt.inv_mem hyVt)
    let h : E := mk ⟨y * b * y⁻¹, hmem⟩
    have hb3ord : orderOf b = 3 := by
      have hdvd : orderOf b ∣ 3 := by
        rw [← c.card_B]
        simpa using orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
      rcases (Nat.dvd_prime (by norm_num : (3 : ℕ).Prime)).mp hdvd with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hbne
      · exact h'
    have hb3 : b ^ 3 = 1 := by
      rw [← hb3ord]
      exact pow_orderOf_eq_one b
    have hh : h ^ 3 = 1 := by
      have h3 : (⟨y * b * y⁻¹, hmem⟩ : ↥Vt) ^ 3 = 1 := by
        apply Subtype.ext
        show (y * b * y⁻¹) ^ 3 = 1
        calc (y * b * y⁻¹) ^ 3 = (y * b * y⁻¹) * (y * b * y⁻¹) * (y * b * y⁻¹) := by
              rw [pow_three']
          _ = y * b ^ 3 * y⁻¹ := by
              rw [pow_three']
              group
          _ = 1 := by rw [hb3]; group
      calc h ^ 3 = mk ((⟨y * b * y⁻¹, hmem⟩ : ↥Vt) ^ 3) := by rw [← map_pow]
        _ = 1 := by rw [h3, map_one]
    have hgenB : B = Subgroup.zpowers b := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_).symm
      rw [Nat.card_zpowers, hb3ord, c.card_B]
    have hHx_le : Hx ⟨y, hyR⟩ ≤ Subgroup.zpowers h := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨b', hb'B, hb'eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      rw [hgenB] at hb'B
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'B
      have hx' : x = (⟨y * b * y⁻¹, hmem⟩ : ↥Vt) ^ k := by
        apply Subtype.ext
        rw [← hb'eq]
        have hpow : MulAut.conj y (b ^ k) = (MulAut.conj y b) ^ k :=
          map_zpow (MulAut.conj y) b k
        simp [MulAut.conj_apply]
      have hxk : mk x = h ^ k := by
        rw [hx']
        exact map_zpow mk (⟨y * b * y⁻¹, hmem⟩ : ↥Vt) k
      rw [hxk]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    have hmapVt : B.map (MulAut.conj y).toMonoidHom ≤ Vt := by
      intro z hz
      obtain ⟨b', hb'B, rfl⟩ := Subgroup.mem_map.mp hz
      simpa [MulAut.conj_apply] using
        Vt.mul_mem (Vt.mul_mem hyVt (hBVt hb'B)) (Vt.inv_mem hyVt)
    have hmove : (S i).map (MulAut.conj h).toMonoidHom ≠ S i := by
      intro heq
      apply hyQ
      have hN : h ∈ Subgroup.normalizer (S i : Set E) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
      have hzN : Subgroup.zpowers h ≤ Subgroup.normalizer (S i : Set E) :=
        Subgroup.zpowers_le.mpr hN
      have hHxN : Hx ⟨y, hyR⟩ ≤ Subgroup.normalizer (S i : Set E) := hHx_le.trans hzN
      exact (hQ_trans (B.map (MulAut.conj y).toMonoidHom) hmapVt).mp hHxN
    have hstep2 : Γ ⊓ S i ≠ ⊥ → S i ≤ Γ := by
      intro hne
      exact le_of_inf_ne_bot_of_map_conj_ne (W := W) (S := S i) (Γ := Γ)
        (K := Hx ⟨y, hyR⟩) (hSW := hSle i) (hS := hSsimple i)
        (hcm := fun g g' => hconj_comm g g' i) (hh := hh) (hmove := hmove)
        (hK := hHx_le) (hfix := hfixHx ⟨y, hyR⟩) (hne := hne)
    by_cases hcaseA : (∃ y' ∈ R, B.map (MulAut.conj y').toMonoidHom ≤ Q) ∨
        (∃ j : Fin 2, R ⊓ L j ≤ Q)
    ·
      rcases hcaseA with ⟨y', hy'R, hy'Q⟩ | ⟨j, hjQ⟩
      · have hmapVt' : B.map (MulAut.conj y').toMonoidHom ≤ Vt := by
          intro z hz
          obtain ⟨b', hb'B, rfl⟩ := Subgroup.mem_map.mp hz
          simpa [MulAut.conj_apply] using
            Vt.mul_mem (Vt.mul_mem (hRVt hy'R) (hBVt hb'B)) (Vt.inv_mem (hRVt hy'R))
        have hN : Hx ⟨y', hy'R⟩ ≤ Subgroup.normalizer (S i : Set E) :=
          (hQ_trans (B.map (MulAut.conj y').toMonoidHom) hmapVt').mpr hy'Q
        have hcard_map : Nat.card ↥(B.map (MulAut.conj y').toMonoidHom) = 3 := by
          rw [← Nat.card_congr (Subgroup.equivMapOfInjective B (MulAut.conj y').toMonoidHom
            (MulAut.conj y').injective).toEquiv]
          exact hbcard
        have hcard_sub :
            Nat.card ↥((B.map (MulAut.conj y').toMonoidHom).subgroupOf Vt) = 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmapVt').toEquiv, hcard_map]
        have hdvd : Nat.card ↥(Hx ⟨y', hy'R⟩) ∣ 3 := by
          have h := Subgroup.card_map_dvd
            (H := (B.map (MulAut.conj y').toMonoidHom).subgroupOf Vt) mk
          rwa [hcard_sub] at h
        have hHp : Hx ⟨y', hy'R⟩ = ⊥ ∨ (Nat.card ↥(Hx ⟨y', hy'R⟩)).Prime := by
          rcases (Nat.dvd_prime (by norm_num : (3 : ℕ).Prime)).mp hdvd with h1 | hp
          · left
            exact Subgroup.eq_bot_of_card_eq (H := Hx ⟨y', hy'R⟩) h1
          · right
            rw [hp]
            norm_num
        exact hstep2 (inf_ne_bot_of_le_normalizer (W := W) (S := S i) (Γ := Γ)
          (H := Hx ⟨y', hy'R⟩) (hSle i) (hSsimple i) (hSnab i) hN hHp
          (hfixHx ⟨y', hy'R⟩))
      · have hRVt' : R ⊓ L j ≤ Vt := (inf_le_left : R ⊓ L j ≤ R).trans hRVt
        have hN : Hi j ≤ Subgroup.normalizer (S i : Set E) :=
          (hQ_trans (R ⊓ L j) hRVt').mpr hjQ
        have hcard_R : Nat.card ↥(R ⊓ L j) = 7 := (c.frame.2.2.1 j).1
        have hcard_sub : Nat.card ↥((R ⊓ L j).subgroupOf Vt) = 7 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRVt').toEquiv, hcard_R]
        have hdvd : Nat.card ↥(Hi j) ∣ 7 := by
          have h := Subgroup.card_map_dvd (H := (R ⊓ L j).subgroupOf Vt) mk
          rwa [hcard_sub] at h
        have hHp : Hi j = ⊥ ∨ (Nat.card ↥(Hi j)).Prime := by
          rcases (Nat.dvd_prime (by norm_num : (7 : ℕ).Prime)).mp hdvd with h1 | hp
          · left
            exact Subgroup.eq_bot_of_card_eq (H := Hi j) h1
          · right
            rw [hp]
            norm_num
        exact hstep2 (inf_ne_bot_of_le_normalizer (W := W) (S := S i) (Γ := Γ)
          (H := Hi j) (hSle i) (hSsimple i) (hSnab i) hN hHp (hfixHi j))
    ·
      push Not at hcaseA
      obtain ⟨hnoB, hnoL⟩ := hcaseA
      have hcardR0 : Nat.card ↥(R ⊓ L 0) = 7 := (c.frame.2.2.1 0).1
      have hntR0 : Nontrivial ↥(R ⊓ L 0) := by
        apply Finite.one_lt_card_iff_nontrivial.mp
        rw [hcardR0]
        norm_num
      obtain ⟨x₀, hx₀ne⟩ := @exists_ne ↥(R ⊓ L 0) hntR0 (1 : ↥(R ⊓ L 0))
      have hx₀R : (x₀ : G) ∈ R := (Subgroup.mem_inf.mp x₀.2).1
      have hx₀Vt : (x₀ : G) ∈ Vt := hRVt hx₀R
      have hx₀1 : (x₀ : G) ≠ 1 := fun h => hx₀ne (Subtype.ext h)
      have hmem2 : (x₀ : G) * b * (x₀ : G)⁻¹ ∈ Vt :=
        Vt.mul_mem (Vt.mul_mem hx₀Vt hbVt) (Vt.inv_mem hx₀Vt)
      let h₁ : E := mk ⟨b, hbVt⟩
      let h₂ : E := mk ⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩
      have hh₁ : h₁ ^ 3 = 1 := by
        have h3 : (⟨b, hbVt⟩ : ↥Vt) ^ 3 = 1 := by
          apply Subtype.ext
          show b ^ 3 = 1
          exact hb3
        calc h₁ ^ 3 = mk ((⟨b, hbVt⟩ : ↥Vt) ^ 3) := by rw [← map_pow]
          _ = 1 := by rw [h3, map_one]
      have hh₂ : h₂ ^ 3 = 1 := by
        have h3 : (⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩ : ↥Vt) ^ 3 = 1 := by
          apply Subtype.ext
          show ((x₀ : G) * b * (x₀ : G)⁻¹) ^ 3 = 1
          calc ((x₀ : G) * b * (x₀ : G)⁻¹) ^ 3 =
              ((x₀ : G) * b * (x₀ : G)⁻¹) * ((x₀ : G) * b * (x₀ : G)⁻¹) *
                ((x₀ : G) * b * (x₀ : G)⁻¹) := by rw [pow_three']
            _ = (x₀ : G) * b ^ 3 * (x₀ : G)⁻¹ := by
                  rw [pow_three']; group
            _ = 1 := by rw [hb3]; group
        calc h₂ ^ 3 = mk ((⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩ : ↥Vt) ^ 3) := by
              rw [← map_pow]
          _ = 1 := by rw [h3, map_one]
      have hmemx : ∀ x : ↥R, x.1 * b * x.1⁻¹ ∈ Vt := fun x =>
        Vt.mul_mem (Vt.mul_mem (hRVt x.2) hbVt) (Vt.inv_mem (hRVt x.2))
      have hHx_zpow : ∀ (x : ↥R),
          Hx x ≤ Subgroup.zpowers (mk ⟨x.1 * b * x.1⁻¹, hmemx x⟩) := by
        intro x z hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
        obtain ⟨b', hb'B, hb'eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hw)
        rw [hgenB] at hb'B
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'B
        have hw' : w = (⟨x.1 * b * x.1⁻¹, hmemx x⟩ : ↥Vt) ^ k := by
          apply Subtype.ext
          rw [← hb'eq]
          have hpow : MulAut.conj x.1 (b ^ k) = (MulAut.conj x.1 b) ^ k :=
            map_zpow (MulAut.conj x.1) b k
          simp [MulAut.conj_apply]
        rw [hw', map_zpow]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      have hK : Hx ⟨1, R.one_mem⟩ ≤ Subgroup.zpowers h₁ := by
        have h := hHx_zpow ⟨1, R.one_mem⟩
        have heq : (mk ⟨(1 : G) * b * (1 : G)⁻¹, hmemx ⟨1, R.one_mem⟩⟩ : E) = h₁ := by
          apply congrArg mk
          apply Subtype.ext
          group
        rwa [heq] at h
      have hK' : Hx ⟨x₀, hx₀R⟩ ≤ Subgroup.zpowers h₂ := by
        have h := hHx_zpow ⟨x₀, hx₀R⟩
        have heq : (mk ⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmemx ⟨x₀, hx₀R⟩⟩ : E) = h₂ := rfl
        rwa [heq] at h
      have hdist : ∀ j k : ℕ, j < 3 → k < 3 → (j ≠ 0 ∨ k ≠ 0) →
          (S i).map (MulAut.conj (h₁ ^ j)).toMonoidHom ≠
            (S i).map (MulAut.conj (h₂ ^ k)).toMonoidHom := by
        intro j k hj hk hjk hEq
        have hN : (h₂ ^ k)⁻¹ * h₁ ^ j ∈ Subgroup.normalizer (S i : Set E) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          calc (S i).map (MulAut.conj ((h₂ ^ k)⁻¹ * h₁ ^ j)).toMonoidHom
              = (S i).map (((MulAut.conj (h₂ ^ k))⁻¹ * MulAut.conj (h₁ ^ j)).toMonoidHom) := by
                  rw [map_mul, map_inv]
            _ = ((S i).map (MulAut.conj (h₁ ^ j)).toMonoidHom).map
                  ((MulAut.conj (h₂ ^ k))⁻¹).toMonoidHom := by
                  rw [Subgroup.map_map]
                  rfl
            _ = ((S i).map (MulAut.conj (h₂ ^ k)).toMonoidHom).map
                  ((MulAut.conj (h₂ ^ k))⁻¹).toMonoidHom := by rw [hEq]
            _ = S i :=
                  (Subgroup.map_symm_eq_iff_map_eq (K := S i)
                    (H := (S i).map (MulAut.conj (h₂ ^ k)).toMonoidHom)
                    (e := MulAut.conj (h₂ ^ k))).mpr rfl
        let g : G := ((x₀ : G) * b ^ k * (x₀ : G)⁻¹)⁻¹ * b ^ j
        have hgVt : g ∈ Vt :=
          Vt.mul_mem (Vt.inv_mem (Vt.mul_mem (Vt.mul_mem hx₀Vt (Vt.pow_mem hbVt k))
            (Vt.inv_mem hx₀Vt))) (Vt.pow_mem hbVt j)
        have ha2pow : ((⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩ : ↥Vt) ^ k : G) =
            (x₀ : G) * b ^ k * (x₀ : G)⁻¹ := by
          simp
        have h1pow : h₁ ^ j = mk ((⟨b, hbVt⟩ : ↥Vt) ^ j) :=
          (map_pow mk ⟨b, hbVt⟩ j).symm
        have h2pow : h₂ ^ k = mk ((⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩ : ↥Vt) ^ k) :=
          (map_pow mk ⟨(x₀ : G) * b * (x₀ : G)⁻¹, hmem2⟩ k).symm
        have hNmk : mk ⟨g, hgVt⟩ ∈ Subgroup.normalizer (S i : Set E) := by
          have heq : mk ⟨g, hgVt⟩ = (h₂ ^ k)⁻¹ * h₁ ^ j := by
            rw [h1pow, h2pow, ← map_inv, ← map_mul]
            congr 1
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
            rw [ha2pow]
          rw [heq]
          exact hN
        have hgQ : g ∈ Q := (hQ_mem g hgVt).mp hNmk
        have hnotmem := inv_conj_pow_mul_pow_not_mem (X := G) (B := B) (R := R)
          (R₀ := R ⊓ L 0) (Q := Q) (b := b) (x₀ := (x₀ : G))
          (hBcard := hbcard) (hbB := hbB) (hb1 := hbne) (hBR := c.frame.2.2.2.1)
          (hfix := hfixb) (hR₀R := inf_le_left) (hBR₀ := (c.frame.2.2.1 0).2)
          (hR₀ := by rw [(c.frame.2.2.1 0).1]; norm_num)
          (hx₀ := x₀.2) (hx₀1 := hx₀1) (hBQ := hnoB) (hR₀Q := hnoL 0)
          (hj := hj) (hk := hk) (hjk := hjk)
        exact hnotmem hgQ
      exact hstep2 (inf_ne_bot_of_disjoint_orbits (W := W) (S := S i) (Γ := Γ)
        (K := Hx ⟨1, R.one_mem⟩) (K' := Hx ⟨x₀, hx₀R⟩)
        (hSW := hSle i) (hnab := hSnab i) (hcm := fun g g' => hconj_comm g g' i)
        (hh := hh₁) (hh' := hh₂) (hdist := hdist) (hK := hK) (hK' := hK')
        (hfix := hfixHx ⟨1, R.one_mem⟩) (hfix' := hfixHx ⟨x₀, hx₀R⟩))
  have hWΓ : W ≤ Γ := by
    rw [← hTN]
    exact iSup_le hSΓ
  exact hΓ_final (le_antisymm hΓle hWΓ)

theorem le_M_of_section_nonabelian
    (c : Ctx147 D L n r p A X B R) (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    (hmin : ∀ U : Subgroup G, V₀ ≤ U → U ≤ V → V ≤ normalizer (U : Set G) →
      B ≤ normalizer (U : Set G) → R ≤ normalizer (U : Set G) → U = V₀ ∨ U = V)
    (hnab : ∃ v ∈ V, ∃ w ∈ V, v * w * v⁻¹ * w⁻¹ ∉ V₀) : V ≤ D.M := by
  classical
  let Vt : Subgroup G := uc147Ambient V B R
  have hVVt : V ≤ Vt := le_sup_left.trans le_sup_left
  have hBVt : B ≤ Vt := le_sup_right.trans le_sup_left
  have hRVt : R ≤ Vt := le_sup_right
  have hV₀V : V₀ ≤ V := s.hle
  have hV₀Vt : V₀ ≤ Vt := hV₀V.trans hVVt
  have hVnorm : Vt ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer s.hBV) s.hRV
  have hV₀norm : Vt ≤ Subgroup.normalizer (V₀ : Set G) :=
    sup_le (sup_le s.hVV₀ s.hBV₀) s.hRV₀
  have hV₀n : (V₀.subgroupOf Vt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀Vt).2 hV₀norm
  have hVn : (V.subgroupOf Vt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVVt).2 hVnorm
  let E := uc147Section V B R V₀
  let mk : ↥Vt →* E := uc147Quot V B R V₀
  let W : Subgroup E := uc147Image V B R V₀
  have hWn : W.Normal := uc147Image_normal V B R V₀ hVnorm
  have hFinE : Finite E := Quotient.finite _
  let φ : ↥V →* E := uc147Map V B R V₀
  have hφ_one : ∀ v : ↥V, φ v = 1 ↔ (v : G) ∈ V₀ := uc147Map_eq_one V B R V₀
  have hφmem : ∀ v : ↥V, φ v ∈ W := uc147Map_mem_image V B R V₀
  let φW : ↥V →* ↥W := uc147MapImage V B R V₀
  have hφW_val : ∀ v : ↥V, ((φW v : ↥W) : E) = φ v := uc147MapImage_apply V B R V₀
  have hker : φW.ker = V₀.subgroupOf V := uc147MapImage_ker V B R V₀
  have hφW_surj : Function.Surjective φW := uc147MapImage_surjective V B R V₀
  have hV₀Vn : (V₀.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀V).2 s.hVV₀
  let iso : (↥V ⧸ (V₀.subgroupOf V)) ≃* ↥W := uc147SectionIso V B R V₀
  have h3dvd : 3 ∣ Nat.card G := c.card_B ▸ Subgroup.card_subgroup_dvd_card B
  have h3Vnot : ¬ 3 ∣ Nat.card ↥V :=
    (Nat.Prime.coprime_iff_not_dvd (p := 3) (n := Nat.card ↥V) Nat.prime_three).mp s.hV
  have hVproper : V ≠ ⊤ := by
    intro h
    apply h3Vnot
    rw [h]
    simpa using h3dvd
  have hVK : CFSG.Open.IsKGroup ↥V := D.standing.kProper.isKGroup V hVproper
  have hWK : CFSG.Open.IsKGroup ↥W :=
    CFSG.Open.IsKGroup.of_injective (hVK.quotient (V₀.subgroupOf V)) iso.symm.toMonoidHom
      iso.symm.injective
  have h3W : ¬ 3 ∣ Nat.card ↥W := by
    intro h3
    apply h3Vnot
    have h2 : Nat.card ↥W ∣ Nat.card ↥V := by
      rw [Nat.card_congr iso.symm.toEquiv]
      exact Subgroup.card_quotient_dvd_card (V₀.subgroupOf V)
    exact h3.trans h2
  have hWnab : ¬ IsMulCommutative ↥W := uc147Image_not_isMulCommutative V B R V₀ hnab
  have hWne : W ≠ ⊥ := uc147Image_ne_bot V B R V₀ hnab
  have hWmin : ∀ M' : Subgroup E, M'.Normal → M' ≤ W → M' = ⊥ ∨ M' = W :=
    uc147Image_minimal_normal V B R V₀ hVnorm hV₀V hmin
  let F : Uc147Factors E W := uc147_factors hWne hWmin
  let r₀ : ℕ := F.r
  let S : Fin r₀ → Subgroup E := F.S
  have hr₀ : 1 ≤ r₀ := F.one_le_r
  have hSle : ∀ i, S i ≤ W := F.le_W
  have hSsimple : ∀ i, IsSimpleGroup (S i) := F.simple
  have hSconj : ∀ i j, ∃ g : E, S j = CFSG.conjugate (S i) g := F.conjugate
  have hSnormal : ∀ i, ((S i).subgroupOf W).Normal := F.normal_in_W
  let e : ((i : Fin r₀) → S i) ≃* W := F.e
  have he : ∀ (i : Fin r₀) (x : (j : Fin r₀) → S j),
      (∀ j, j ≠ i → x j = 1) → (e x : E) = x i := by
    intro i x hx
    exact F.e_single i x hx
  have hSnabC : ∀ i, ¬ IsMulCommutative ↥(S i) := F.not_isMulCommutative hWnab
  have hSnab : ∀ i, ∃ a b : ↥(S i), a * b ≠ b * a := F.exists_not_commute hWnab
  have h3S : ∀ i, ¬ 3 ∣ Nat.card ↥(S i) := F.not_dvd_three h3W
  have hSkill : ∀ i, CFSG.Open.IsKGroup ↥(S i) := F.isKGroup hWK
  have hSsz : ∀ i, ∃ f : ℕ, CFSG.Blueprint.SuzukiModel ↥(S i) 2 f := F.suzuki hSz hWnab hWK h3W
  have hBRVt : B ⊔ R ≤ Vt := sup_le hBVt hRVt
  have hcenterW : Subgroup.center ↥W = ⊥ := F.center_eq_bot hWnab
  have hNeZero : NeZero r₀ := ⟨by omega⟩
  by_cases hr1 : r₀ = 1
  ·
    exact uc147_section_simple_case c hRi s F hSsz hBRVt hcenterW hVnorm hr1
  ·
    have hr2 : 2 ≤ r₀ := by omega
    exact uc147_section_composite_case c hsp3 hRi s F hWnab hWmin hVnorm hr2

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
