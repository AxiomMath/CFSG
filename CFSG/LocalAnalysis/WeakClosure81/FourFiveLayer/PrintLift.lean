module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintDiag
import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintTen
public import CFSG.Quasithin.Background.RonanE111LSG
public import CFSG.Quasithin.Background.RonanE111WrAct

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R CFSG.Quasithin.RonanE111
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem le_tauOf_liftP {T T₀ A : Subgroup G} (hT₀T : T₀ ≤ T)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t) : T₀ ≤ E1.tauOf ⊤ T A := by
  intro t ht
  rw [E1.mem_tauOf_of_le le_top]
  refine ⟨hT₀T ht, fun a ha => ?_⟩
  have h1 : ⁅t, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hT₀A t ht a ha)
  rw [h1]
  exact Subgroup.one_mem _

private theorem map_comm_liftP {G' : Type} [Group G'] (f : G →* G') {T₀ A : Subgroup G}
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t) :
    ∀ t ∈ T₀.map f, ∀ a ∈ A.map f, t * a = a * t := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
  simpa only [map_mul] using congrArg f (hT₀A t ht a ha)

private theorem isSolvable_centMod_liftP [Finite G] {T₀ D Y : Subgroup G} [Y.Normal] [D.Normal]
    (hT₀2 : IsPGroup 2 T₀) (hDT₀ : D ⊔ T₀ = ⊤)
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥) :
    Group.IsSolvable ↥(RonanE111.centMod D Y) := by
  have hπs : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  haveI : (D.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map ‹D.Normal› _ hπs
  have hsup : D.map (QuotientGroup.mk' Y) ⊔ T₀.map (QuotientGroup.mk' Y) = ⊤ := by
    rw [← Subgroup.map_sup, hDT₀, Subgroup.map_top_of_surjective _ hπs]
  have h2 : IsPGroup 2 (T₀.map (QuotientGroup.mk' Y)) := hT₀2.map _
  have hP : IsPGroup 2 ↥(RonanE111.centMod D Y) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro c
    have hc : (c : G ⧸ Y) ∈ D.map (QuotientGroup.mk' Y) ⊔ T₀.map (QuotientGroup.mk' Y) := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, t, ht, hdt⟩ := Subgroup.mem_sup_of_normal_left.mp hc
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp h2 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    have hd1 : QuotientGroup.mk' (D.map (QuotientGroup.mk' Y)) (c : G ⧸ Y) =
        QuotientGroup.mk' (D.map (QuotientGroup.mk' Y)) t := by
      rw [← hdt, map_mul]
      have hd0 : QuotientGroup.mk' (D.map (QuotientGroup.mk' Y)) d = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hd
      rw [hd0, one_mul]
    have hmem : (c : G ⧸ Y) ^ 2 ^ k ∈ D.map (QuotientGroup.mk' Y) := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change QuotientGroup.mk' (D.map (QuotientGroup.mk' Y)) ((c : G ⧸ Y) ^ 2 ^ k) = 1
      rw [map_pow, hd1, ← map_pow, hk', map_one]
    have hmemC : (c : G ⧸ Y) ^ 2 ^ k ∈ RonanE111.centMod D Y :=
      (RonanE111.centMod D Y).pow_mem c.2 (2 ^ k)
    have hbot : (c : G ⧸ Y) ^ 2 ^ k = 1 :=
      Subgroup.mem_bot.mp (hZ ▸ Subgroup.mem_inf.mpr ⟨hmem, hmemC⟩)
    simpa using hbot
  have := hP.isNilpotent
  infer_instance

private theorem isEP_of_isEG_liftP {n : ℕ} {T T₀ A K : Subgroup G} (hT₀T : T₀ ≤ T)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t) (hτ : E1.tauOf ⊤ T A ≤ T₀)
    (hK : IsEG n ⊤ T A T₀ K) : UniquenessCase.UC22.F12.IsEP n ⊤ T A K := by
  rw [isEP_iff_isEG, ← le_antisymm (le_tauOf_liftP hT₀T hT₀A) hτ]
  exact hK

private theorem reduced_quot_liftP [Finite G] {T T₀ D Y : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T)
    (hDT₀ : D ⊔ T₀ = ⊤) (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) :
    CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced ((G ⧸ Y) ⧸ RonanE111.centMod D Y)
      ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))) := by
  have hπ₁s : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  haveI hDn' : (D.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map ‹D.Normal› _ hπ₁s
  have hsf := hSM.semiFam_map
  have hDs := hSM.sSup_map
  have hTs : IsSylowIn 2 (T.map (QuotientGroup.mk' Y)) ⊤ := E1.isSylowIn_two_map_top hπ₁s hT
  have hDT : D ⊔ T = ⊤ := by
    rw [eq_top_iff, ← hDT₀]
    exact sup_le_sup le_rfl hT₀T
  have hQs : D.map (QuotientGroup.mk' Y) ⊔ T.map (QuotientGroup.mk' Y) = ⊤ := by
    rw [← Subgroup.map_sup, hDT, Subgroup.map_top_of_surjective _ hπ₁s]
  have hconj : ∀ Ŝ ∈ ((fun S : Subgroup G => S.map (QuotientGroup.mk' Y)) '' 𝒟),
      ∀ t' ∈ T.map (QuotientGroup.mk' Y),
        A1b.conjSub t' Ŝ ∈ ((fun S : Subgroup G => S.map (QuotientGroup.mk' Y)) '' 𝒟) := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨A1b.conjSub t S, hSM.conj_of_sup_top hDT₀ t hS, E1.map_conjSub _ t S⟩
  have htr : ∀ Ŝ ∈ ((fun S : Subgroup G => S.map (QuotientGroup.mk' Y)) '' 𝒟),
      ∀ Ŝ' ∈ ((fun S : Subgroup G => S.map (QuotientGroup.mk' Y)) '' 𝒟),
        ∃ t' ∈ T.map (QuotientGroup.mk' Y), A1b.conjSub t' Ŝ = Ŝ' := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩
    obtain ⟨t, ht, hts⟩ := hSM.trans S hS S' hS'
    exact ⟨QuotientGroup.mk' Y t, ⟨t, hT₀T ht, rfl⟩, by rw [← E1.map_conjSub, hts]⟩
  exact reduced_quot_of_semiFam (Q' := G ⧸ Y) (T := T.map (QuotientGroup.mk' Y))
    (D := D.map (QuotientGroup.mk' Y)) (C := RonanE111.centMod D Y) rfl hTs hsf hDs hQs
    ⟨_, ⟨S₀, hS₀, rfl⟩⟩ hconj htr

private theorem centMod_inf_liftP [Finite G] {T₀ D Y : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟) :
    D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥ := by
  have hsf := hSM.semiFam_map
  have hDs := hSM.sSup_map
  show D.map (QuotientGroup.mk' Y) ⊓ Subgroup.centralizer
    ((D.map (QuotientGroup.mk' Y) : Subgroup (G ⧸ Y)) : Set (G ⧸ Y)) = ⊥
  rw [← hDs]
  exact inf_centralizer_eq_bot hsf

private theorem comp_map_liftP {T₀ D Y : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥) :
    IsComp ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))) := by
  have hsf := hSM.semiFam_map
  have hDs := hSM.sSup_map
  have hS₀D : S₀.map (QuotientGroup.mk' Y) ≤ D.map (QuotientGroup.mk' Y) :=
    Subgroup.map_mono (hSM.le_D S₀ hS₀)
  have hS₀n : ((S₀.map (QuotientGroup.mk' Y)).subgroupOf (D.map (QuotientGroup.mk' Y))).Normal := by
    have := hsf.normal ⟨S₀, hS₀, rfl⟩
    rwa [hDs] at this
  have hS₀simple : IsSimpleGroup ↥(S₀.map (QuotientGroup.mk' Y)) := hsf.simple _ ⟨S₀, hS₀, rfl⟩
  have hS₀nab : ∃ a b : ↥(S₀.map (QuotientGroup.mk' Y)), a * b ≠ b * a :=
    hsf.nonabelian _ ⟨S₀, hS₀, rfl⟩
  have hinj : ∀ x ∈ S₀.map (QuotientGroup.mk' Y),
      QuotientGroup.mk' (RonanE111.centMod D Y) x = 1 → x = 1 := by
    intro x hx h1
    have h2 : x ∈ D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y :=
      ⟨hS₀D hx, (QuotientGroup.eq_one_iff x).mp h1⟩
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  exact ⟨Subgroup.map_mono hS₀D, normal_subgroupOf_map _ hS₀n hS₀D,
    isSimpleGroup_map_of_injOn _ hinj hS₀simple, nonabelian_map_of_injOn _ hinj hS₀nab⟩

private theorem comp_one_liftP {T₀ D Y : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) :
    IsComp (D.map (QuotientGroup.mk' Y)) (S₀.map (QuotientGroup.mk' Y)) := by
  have hsf := hSM.semiFam_map
  have hDs := hSM.sSup_map
  refine ⟨Subgroup.map_mono (hSM.le_D S₀ hS₀), ?_,
    hsf.simple _ ⟨S₀, hS₀, rfl⟩, hsf.nonabelian _ ⟨S₀, hS₀, rfl⟩⟩
  have := hsf.normal ⟨S₀, hS₀, rfl⟩
  rwa [hDs] at this

private theorem not_le_centralizer_map_liftP {T₀ D Y A : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥)
    (hAS₀ : ¬ A ≤ RonanE111.Cmod S₀ Y) :
    ¬ (A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ≤
      Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) := by
  intro h
  apply hAS₀
  intro a ha
  exact (mem_centralizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mp
    (h ⟨_, ⟨a, ha, rfl⟩, rfl⟩)

private theorem card_actOn_map_liftP {T₀ D Y A : Subgroup G} [Y.Normal] [D.Normal]
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) {n : ℕ}
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥)
    (hrank : ∀ S ∈ 𝒟, ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ RonanE111.Cmod S Y →
      (A ⊓ Subgroup.normalizer (S : Set G) ⊓ RonanE111.Cmod S Y).relIndex
        (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n)
    (hnot : ¬ (A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊓
      Subgroup.normalizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) ≤
      Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y)))) :
    Nat.card ↥(RonanE111.actOn ((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))) ≤ 2 ^ n := by
  rw [card_actOn_quot hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) A]
  apply hrank S₀ hS₀
  intro hle
  apply hnot
  rintro _ ⟨hx1, hx2⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hx1
  have ha' : a ∈ Subgroup.normalizer (S₀ : Set G) :=
    (mem_normalizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mp hx2
  exact (mem_centralizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mpr (hle ⟨ha, ha'⟩)

private theorem chain_tail_liftP [Finite G] {n : ℕ} {T T₀ D Y A : Subgroup G} [Y.Normal]
    [D.Normal] {𝒟 : Set (Subgroup G)} {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hDT₀ : D ⊔ T₀ = ⊤)
    (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced ((G ⧸ Y) ⧸ RonanE111.centMod D Y)
      ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))))
    (hSb : IsComp ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))))
    (hSb₀ : IsComp (D.map (QuotientGroup.mk' Y)) (S₀.map (QuotientGroup.mk' Y)))
    {Kb : Subgroup ((G ⧸ Y) ⧸ RonanE111.centMod D Y)} {J₁ : Subgroup (G ⧸ Y)}
    {J : Subgroup G}
    (hKb : IsEG n ⊤ ((T.map (QuotientGroup.mk' Y)).map
      (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((T₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))) Kb)
    (hcov : ∀ x ∈ (S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)),
      ∃ y ∈ Kb, x⁻¹ * y ∈ Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))))
    (hJ₁ : IsEG n ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y))
      (T₀.map (QuotientGroup.mk' Y)) J₁)
    (hJ₁K : twoResidual Kb =
      (twoResidual J₁).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
    (hJ : IsEG n ⊤ T A T₀ J)
    (hJJ₁ : twoResidual J₁ = (twoResidual J).map (QuotientGroup.mk' Y)) :
    (twoResidual J ⊔ T) ⊔ Y = ⊤ := by
  have hπ₁s : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  have hTs : IsSylowIn 2 (T.map (QuotientGroup.mk' Y)) ⊤ := E1.isSylowIn_two_map_top hπ₁s hT
  have hSbH : (S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ≤
      twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) := by
    refine le_of_diag hSb.2.2.1 (inf_ne_bot hR hSb (exists_involution_of_isComp hSb))
      le_sup_right ?_
    intro x hx
    obtain ⟨y, hy, hc⟩ := hcov x hx
    exact ⟨y, (E1.le_twoResidual_sup_of_isSylowIn hKb.2.2.1).trans
      (sup_le_sup le_rfl inf_le_left) hy, hc⟩
  have hTS₀ : (T.map (QuotientGroup.mk' Y)) ⊓ S₀.map (QuotientGroup.mk' Y) ≠ ⊥ := by
    have hTD : IsSylowIn 2 ((T.map (QuotientGroup.mk' Y)) ⊓ D.map (QuotientGroup.mk' Y))
        (D.map (QuotientGroup.mk' Y)) := hTs.inf_normal le_top inferInstance
    have hTS : IsSylowIn 2 ((T.map (QuotientGroup.mk' Y)) ⊓ D.map (QuotientGroup.mk' Y) ⊓
        S₀.map (QuotientGroup.mk' Y)) (S₀.map (QuotientGroup.mk' Y)) :=
      hTD.inf_normal hSb₀.1 hSb₀.2.1
    have hne := ne_bot_of_isSylowIn hTS (exists_involution_of_isComp hSb₀)
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (T.map (QuotientGroup.mk' Y)) ⊓ S₀.map (QuotientGroup.mk' Y) := ⟨hx.1.1, hx.2⟩
    rw [hbot] at this
    exact this
  have hS₀H₁ : S₀.map (QuotientGroup.mk' Y) ≤ twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) := by
    refine le_of_diag hSb₀.2.2.1 hTS₀ le_sup_right ?_
    intro x hx
    have hx' : QuotientGroup.mk' (RonanE111.centMod D Y) x ∈
        twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (RonanE111.centMod D Y)) := hSbH ⟨x, hx, rfl⟩
    have hHbeq : twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (RonanE111.centMod D Y)) =
        (twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (RonanE111.centMod D Y)) := by
      rw [Subgroup.map_sup, hJ₁K]
    rw [hHbeq] at hx'
    obtain ⟨h, hh, hhx⟩ := hx'
    refine ⟨h, hh, ?_⟩
    have hker : x⁻¹ * h ∈ RonanE111.centMod D Y := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (RonanE111.centMod D Y) (x⁻¹ * h) = 1
      rw [map_mul, map_inv, hhx, inv_mul_cancel]
    exact Subgroup.centralizer_le (by exact_mod_cast hSb₀.1) hker
  have hDH₁ : D.map (QuotientGroup.mk' Y) ≤ twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) := by
    have hDs := hSM.sSup_map
    rw [← hDs]
    refine sSup_le ?_
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨t, ht, hts⟩ := hSM.trans S₀ hS₀ S hS
    rw [← hts]
    beta_reduce
    rw [E1.map_conjSub]
    intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    have hπt : QuotientGroup.mk' Y t ∈ twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) :=
      Subgroup.mem_sup_right ⟨t, hT₀T ht, rfl⟩
    have h1 := hS₀H₁ hx
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hπt h1) (Subgroup.inv_mem _ hπt)
    simpa [mul_assoc] using h2
  have hH₁eq : twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) =
      (twoResidual J ⊔ T).map (QuotientGroup.mk' Y) := by
    rw [Subgroup.map_sup, hJJ₁]
  have hDH : D ≤ (twoResidual J ⊔ T) ⊔ Y := by
    intro d hd
    have h1 : QuotientGroup.mk' Y d ∈ (twoResidual J ⊔ T).map (QuotientGroup.mk' Y) :=
      hH₁eq ▸ hDH₁ ⟨d, hd, rfl⟩
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' Y) (twoResidual J ⊔ T)
    rw [QuotientGroup.ker_mk'] at h2
    have hmem : d ∈ ((twoResidual J ⊔ T).map (QuotientGroup.mk' Y)).comap (QuotientGroup.mk' Y) :=
      h1
    rwa [h2] at hmem
  rw [eq_top_iff, ← hDT₀]
  exact sup_le hDH ((hT₀T.trans le_sup_right).trans le_sup_left)

private theorem lift_chain_liftP [Finite G] {n : ℕ} (hn : 1 ≤ n) {T T₀ D Y A : Subgroup G}
    [Y.Normal] [D.Normal] {𝒟 : Set (Subgroup G)} {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t) (hDT₀ : D ⊔ T₀ = ⊤)
    (hYs : Group.IsSolvable ↥Y) (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced ((G ⧸ Y) ⧸ RonanE111.centMod D Y)
      ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))))
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ RonanE111.centMod D Y = ⊥)
    (hSb : IsComp ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
      ((S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y))))
    (hSb₀ : IsComp (D.map (QuotientGroup.mk' Y)) (S₀.map (QuotientGroup.mk' Y)))
    (hAS : ¬ (A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ≤
      Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))))
    (hrank' : ¬ (A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊓
      Subgroup.normalizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) ≤
      Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) →
      Nat.card ↥(RonanE111.actOn ((S₀.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (RonanE111.centMod D Y)))
        ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))) ≤ 2 ^ n) :
    ∃ J : Subgroup G, IsEG n ⊤ T A T₀ J ∧ (twoResidual J ⊔ T) ⊔ Y = ⊤ := by
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hπ₁s : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  have hTs : IsSylowIn 2 (T.map (QuotientGroup.mk' Y)) ⊤ := E1.isSylowIn_two_map_top hπ₁s hT
  have hT₀2 : IsPGroup 2 T₀ := hT.2.1.to_le hT₀T
  have hAsT : A.map (QuotientGroup.mk' Y) ≤ T.map (QuotientGroup.mk' Y) := Subgroup.map_mono hAT
  have hAsab : IsElemAbelian 2 (A.map (QuotientGroup.mk' Y)) :=
    CFSG.SectionRank.isElemAbelian_map hAab _
  have hAbab : IsElemAbelian 2 ((A.map (QuotientGroup.mk' Y)).map
      (QuotientGroup.mk' (RonanE111.centMod D Y))) :=
    CFSG.SectionRank.isElemAbelian_map hAsab _
  have hΓT : (T₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ≤
      (T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊓
        Subgroup.centralizer ((((A.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
            RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) := by
    refine le_inf (Subgroup.map_mono (Subgroup.map_mono hT₀T)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (map_comm_liftP _ (map_comm_liftP _ hT₀A) x hx a ha).symm
  have hΓX : (T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊓
      Subgroup.centralizer ((((A.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (RonanE111.centMod D Y)) : Subgroup ((G ⧸ Y) ⧸
          RonanE111.centMod D Y)) : Set ((G ⧸ Y) ⧸ RonanE111.centMod D Y))) ≤
      (D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊔
        (T₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) := by
    have htop : (D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) ⊔
        (T₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)) = ⊤ := by
      rw [← Subgroup.map_sup, ← Subgroup.map_sup, hDT₀,
        Subgroup.map_top_of_surjective _ hπ₁s,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [htop]
    exact le_top
  obtain ⟨Kb, hKb, hcov⟩ := exists_memberG_comp hR hn (Subgroup.map_mono hAsT) hAbab hSb hAS hrank'
    (Γ := (T₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (RonanE111.centMod D Y)))
    hΓT hΓX
  obtain ⟨J₁, hJ₁, hJ₁K⟩ := isEG_ten_seven (G := G ⧸ Y) (T := T.map (QuotientGroup.mk' Y))
    (A := A.map (QuotientGroup.mk' Y)) (Γ := T₀.map (QuotientGroup.mk' Y))
    (Y := RonanE111.centMod D Y) hTs hAsT hAsab
    (le_tauOf_liftP (Subgroup.map_mono hT₀T) (map_comm_liftP _ hT₀A))
    (isSolvable_centMod_liftP hT₀2 hDT₀ hZ) hKb
  obtain ⟨J, hJ, hJJ₁⟩ := isEG_ten_seven (Γ := T₀) hT hAT hAab
    (le_tauOf_liftP hT₀T hT₀A) hYs hJ₁
  exact ⟨J, hJ, chain_tail_liftP hS₀ hT hT₀T hDT₀ hSM hR hSb hSb₀ hKb hcov hJ₁ hJ₁K hJ hJJ₁⟩

private theorem absorb_liftP [Finite G] {n : ℕ} (hn : 1 ≤ n) {T T₀ D Y A J : Subgroup G}
    [Y.Normal] [D.Normal] (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀)
    (hAab : IsElemAbelian 2 A) (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hDperf : ⁅D, D⁆ = D) (hDT₀ : D ⊔ T₀ = ⊤) (hYs : Group.IsSolvable ↥Y)
    {𝒟 : Set (Subgroup G)} (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟)
    {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) (hAS₀ : ¬ A ≤ RonanE111.Cmod S₀ Y)
    (hJ : IsEG n ⊤ T A T₀ J) (hJY : (twoResidual J ⊔ T) ⊔ Y = ⊤) :
    D ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | IsEG n ⊤ T A T₀ K}, K := by
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hT₀2 : IsPGroup 2 T₀ := hT.2.1.to_le hT₀T
  have hYD : Y ≤ D := (hSM.Y_le S₀ hS₀).trans (hSM.le_D S₀ hS₀)
  obtain ⟨hres_D, hcore_D⟩ := twoResidual_top_of_perfect hDperf hT₀2 hDT₀
  have hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
    rw [hres_D, hcore_D]
  have hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆ := by
    rw [hcore_D]
    exact eq_commutator_of_le_sup hDperf hYD hYs
      (D_le_commutator_sup hAab hAT₀ hT₀A hSM ⟨S₀, hS₀, hAS₀⟩)
  have h8 := ten_eight_auxS (T := T) (A := A) (Y := Y) (J := twoResidual J ⊔ T)
    hT hAT hAab hres hcomm hYs le_sup_right hJY
  have hD8 : D ≤ (twoResidual J ⊔ T) ⊔
      ⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K := by
    rw [h8]
    exact le_top
  refine hD8.trans (sup_le (sup_le ?_ ?_) ?_)
  · exact le_sup_of_le_right ((twoResidual_le J).trans (le_iSup₂_of_le J hJ le_rfl))
  · exact le_sup_left
  · exact le_sup_of_le_right (iSup₂_le fun K hK =>
      le_iSup₂_of_le K (isEG_of_isE_of_isSolvable (isE_mono_of_one_le hn hK.1) hK.2) le_rfl)

theorem lift_semisimpleG [Finite G] {n : ℕ} (hn : 1 ≤ n)
    {T T₀ D Y A : Subgroup G} {𝒟 : Set (Subgroup G)} [Y.Normal] [D.Normal]
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hDperf : ⁅D, D⁆ = D) (hDT₀ : D ⊔ T₀ = ⊤) (hYs : Group.IsSolvable ↥Y)
    (hSM : RonanE111.SemisimpleMod T₀ D Y 𝒟) (hmove : ∃ S ∈ 𝒟, ¬ A ≤ RonanE111.Cmod S Y)
    (hrank : ∀ S ∈ 𝒟, ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ RonanE111.Cmod S Y →
      (A ⊓ Subgroup.normalizer (S : Set G) ⊓ RonanE111.Cmod S Y).relIndex
        (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    D ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | IsEG n ⊤ T A T₀ K}, K := by
  classical
  obtain ⟨S₀, hS₀, hAS₀⟩ := hmove
  have hR := reduced_quot_liftP hT hT₀T hDT₀ hSM hS₀
  have hZ := centMod_inf_liftP hSM
  have hSb := comp_map_liftP hSM hS₀ hZ
  have hSb₀ := comp_one_liftP hSM hS₀
  have hAS := not_le_centralizer_map_liftP hSM hS₀ hZ hAS₀
  obtain ⟨J, hJ, hJ''Y⟩ := lift_chain_liftP (hrank' := fun hnot =>
      card_actOn_map_liftP hSM hS₀ hZ hrank hnot) hn hS₀ hT hT₀T hAT₀ hAab hT₀A hDT₀ hYs
    hSM hR hZ hSb hSb₀ hAS
  exact absorb_liftP hn hT hT₀T hAT₀ hAab hT₀A hDperf hDT₀ hYs hSM hS₀ hAS₀ hJ hJ''Y

private theorem rank_inf_liftP [Finite G] {n : ℕ} {K N T₀ Y A : Subgroup G}
    [hYKn : (Y.subgroupOf K).Normal] {𝒟 : Set (Subgroup G)} (hK : K = N ⊔ T₀)
    (hSM : RonanE111.SemisimpleMod T₀ N Y 𝒟) (hAK : A ≤ K)
    (hrank : ∀ S ∈ 𝒟, (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
        a * s * a⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    ∀ S' ∈ (fun S : Subgroup G => S.subgroupOf K) '' 𝒟,
      ¬ A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K) ≤
          RonanE111.Cmod S' (Y.subgroupOf K) →
      (A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K) ⊓
          RonanE111.Cmod S' (Y.subgroupOf K)).relIndex
        (A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K)) ≤ 2 ^ n := by
  subst hK
  have hmemK : ∀ S ∈ 𝒟, S ≤ N ⊔ T₀ := fun S hS => (hSM.le_D S hS).trans le_sup_left
  rintro _ ⟨S, hS, rfl⟩ hnot
  have hSK : S ⊓ (N ⊔ T₀) = S := inf_eq_left.mpr (hmemK S hS)
  have hex : ∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y := by
    by_contra hc
    push Not at hc
    apply hnot
    intro x hx
    obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxG : (x : G) ∈ A ⊓ Subgroup.normalizer (S : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxA, ?_⟩
      have h1 := (E111R.mem_normalizer_subgroupOf_iff (D := S)).mp hxN
      rwa [hSK] at h1
    rw [RonanE111.mem_Cmod_iff]
    intro s hs
    have key := hc (x : G) hxG (s : G) (Subgroup.mem_subgroupOf.mp hs)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using key)
  obtain ⟨B, hBsub, hBcent, hBidx⟩ := hrank S hS hex
  have hM : A.subgroupOf (N ⊔ T₀) ⊓
      Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
        Set ↥(N ⊔ T₀)) =
      (A ⊓ Subgroup.normalizer (S : Set G)).subgroupOf (N ⊔ T₀) := by
    ext k
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, E111R.mem_normalizer_subgroupOf_iff,
      hSK]
  have hBK : B.subgroupOf (N ⊔ T₀) ≤ A.subgroupOf (N ⊔ T₀) ⊓
      Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
        Set ↥(N ⊔ T₀)) := by
    rw [hM]
    exact Subgroup.subgroupOf_mono (N ⊔ T₀) hBsub
  have hBC : B.subgroupOf (N ⊔ T₀) ≤
      RonanE111.Cmod (S.subgroupOf (N ⊔ T₀)) (Y.subgroupOf (N ⊔ T₀)) := by
    intro k hk
    rw [RonanE111.mem_Cmod_iff]
    intro s hs
    have hkB : (k : G) ∈ B := Subgroup.mem_subgroupOf.mp hk
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hBcent (k : G) hkB (s : G) hsS)
  have hne : (B.subgroupOf (N ⊔ T₀)).relIndex (A.subgroupOf (N ⊔ T₀) ⊓
      Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
        Set ↥(N ⊔ T₀))) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  calc (A.subgroupOf (N ⊔ T₀) ⊓
        Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
          Set ↥(N ⊔ T₀)) ⊓
        RonanE111.Cmod (S.subgroupOf (N ⊔ T₀)) (Y.subgroupOf (N ⊔ T₀))).relIndex
        (A.subgroupOf (N ⊔ T₀) ⊓
          Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
            Set ↥(N ⊔ T₀)))
      ≤ (B.subgroupOf (N ⊔ T₀)).relIndex (A.subgroupOf (N ⊔ T₀) ⊓
          Subgroup.normalizer ((S.subgroupOf (N ⊔ T₀) : Subgroup ↥(N ⊔ T₀)) :
            Set ↥(N ⊔ T₀))) :=
        Subgroup.relIndex_le_of_le_left (le_inf hBK hBC) hne
    _ = (B.subgroupOf (N ⊔ T₀)).relIndex
          ((A ⊓ Subgroup.normalizer (S : Set G)).subgroupOf (N ⊔ T₀)) := by rw [hM]
    _ = B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) :=
        Subgroup.relIndex_subgroupOf
          ((inf_le_left : A ⊓ Subgroup.normalizer (S : Set G) ≤ A).trans hAK)
    _ ≤ 2 ^ n := hBidx

private theorem lift_in_sup_liftP [Finite G] {n : ℕ} (hn : 1 ≤ n) {T T₀ N Y A : Subgroup G}
    {𝒟 : Set (Subgroup G)} {K : Subgroup G} (hK : K = N ⊔ T₀)
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) (hT₀Y : T₀ ≤ Subgroup.normalizer (Y : Set G))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hYN : Y ≤ N) (hperf : ⁅N, N⁆ = N)
    (hYs : Group.IsSolvable ↥Y) (hSM : RonanE111.SemisimpleMod T₀ N Y 𝒟)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀))
    (hmove : ∃ S ∈ 𝒟, ∃ a ∈ A, ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y)
    (hrank : ∀ S ∈ 𝒟, (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
        a * s * a⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    N.subgroupOf K ≤ (T ⊓ K).subgroupOf K ⊔
      ⨆ K' ∈ {K' : Subgroup ↥K | IsEG n ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K)
        (T₀.subgroupOf K) K'}, K' := by
  subst hK
  have hNK : N ≤ N ⊔ T₀ := le_sup_left
  have hT₀K : T₀ ≤ N ⊔ T₀ := le_sup_right
  have hYK : Y ≤ N ⊔ T₀ := hYN.trans hNK
  have hAK : A ≤ N ⊔ T₀ := hAT₀.trans hT₀K
  have hKN : N ⊔ T₀ ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT₀N
  have hKY : N ⊔ T₀ ≤ Subgroup.normalizer (Y : Set G) := sup_le hNY hT₀Y
  haveI hNn : (N.subgroupOf (N ⊔ T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI hYn : (Y.subgroupOf (N ⊔ T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY
  have hmemK : ∀ S ∈ 𝒟, S ≤ N ⊔ T₀ := fun S hS => (hSM.le_D S hS).trans hNK
  have hSylK : IsSylowIn 2 ((T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀)) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective (N ⊔ T₀).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ (N ⊔ T₀) ≤ N ⊔ T₀),
      Subgroup.map_top, Subgroup.range_subtype]
    exact hSyl
  have hT₀T' : T₀.subgroupOf (N ⊔ T₀) ≤ (T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀) :=
    Subgroup.subgroupOf_mono (N ⊔ T₀) (le_inf hT₀T hT₀K)
  have hAT₀' : A.subgroupOf (N ⊔ T₀) ≤ T₀.subgroupOf (N ⊔ T₀) :=
    Subgroup.subgroupOf_mono (N ⊔ T₀) hAT₀
  have hAab' : IsElemAbelian 2 (A.subgroupOf (N ⊔ T₀)) :=
    ronanE111_isElemAbelian_subgroupOf hAab _
  have hT₀A' : ∀ t ∈ T₀.subgroupOf (N ⊔ T₀), ∀ a ∈ A.subgroupOf (N ⊔ T₀), t * a = a * t :=
    fun t ht a ha => Subtype.ext (hT₀A _ (Subgroup.mem_subgroupOf.mp ht) _
      (Subgroup.mem_subgroupOf.mp ha))
  have hDperf : ⁅N.subgroupOf (N ⊔ T₀), N.subgroupOf (N ⊔ T₀)⁆ = N.subgroupOf (N ⊔ T₀) := by
    rw [E111R.commutator_subgroupOf hNK hNK, hperf]
  have hDT₀' : N.subgroupOf (N ⊔ T₀) ⊔ T₀.subgroupOf (N ⊔ T₀) = ⊤ := by
    apply Subgroup.map_injective (f := (N ⊔ T₀).subtype) (N ⊔ T₀).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNK,
      Subgroup.map_subgroupOf_eq_of_le hT₀K, Subgroup.map_top, Subgroup.range_subtype]
  have hYsK : Group.IsSolvable ↥(Y.subgroupOf (N ⊔ T₀)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYK).symm.surjective
  have hSMK := hSM.subgroupOf hT₀K hNK hYK
  have hmove' : ∃ S ∈ (fun S : Subgroup G => S.subgroupOf (N ⊔ T₀)) '' 𝒟,
      ¬ A.subgroupOf (N ⊔ T₀) ≤ RonanE111.Cmod S (Y.subgroupOf (N ⊔ T₀)) := by
    obtain ⟨S, hS, a, ha, s, hs, hnot⟩ := hmove
    refine ⟨S.subgroupOf (N ⊔ T₀), ⟨S, hS, rfl⟩, fun hle => hnot ?_⟩
    have hmem := hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, hAK ha⟩ : ↥(N ⊔ T₀)) ∈ A.subgroupOf (N ⊔ T₀))
    rw [RonanE111.mem_Cmod_iff] at hmem
    have key := Subgroup.mem_subgroupOf.mp (hmem ⟨s, hmemK S hS hs⟩
      (Subgroup.mem_subgroupOf.mpr hs))
    simpa using key
  have hrank' := rank_inf_liftP (n := n) (K := N ⊔ T₀) rfl hSM hAK hrank
  exact lift_semisimpleG (G := ↥(N ⊔ T₀)) hn hSylK hT₀T' hAT₀' hAab' hT₀A' hDperf hDT₀'
    hYsK hSMK hmove' hrank'

private theorem mem_members_liftP [Finite G] {n : ℕ} {T T₀ N A : Subgroup G} {K : Subgroup G}
    (hK : K = N ⊔ T₀) (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀)) (hτ : E1.tauOf ⊤ T A ≤ T₀)
    {K' : Subgroup ↥K} (hK' : IsEG n ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K)
      (T₀.subgroupOf K) K') :
    UniquenessCase.UC22.F12.IsEP n ⊤ T A (K'.map K.subtype) := by
  subst hK
  have hAK : A ≤ N ⊔ T₀ := hAT₀.trans le_sup_right
  have hT₀K : T₀ ≤ N ⊔ T₀ := le_sup_right
  have h1 := (isEG_map_subtype (N ⊔ T₀)).mpr hK'
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ (N ⊔ T₀) ≤ N ⊔ T₀),
    Subgroup.map_subgroupOf_eq_of_le hAK, Subgroup.map_subgroupOf_eq_of_le hT₀K] at h1
  exact isEP_of_isEG_liftP hT₀T hT₀A hτ (isEG_eight_two hT hAT hAab le_top
    (hτ.trans (le_inf hT₀T hT₀K)) hSyl h1)

theorem lift_semisimple_subP [Finite G] {n : ℕ} (hn : 1 ≤ n) {T T₀ N Y A : Subgroup G}
    {𝒟 : Set (Subgroup G)}
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) (hT₀Y : T₀ ≤ Subgroup.normalizer (Y : Set G))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hYN : Y ≤ N) (hperf : ⁅N, N⁆ = N)
    (hYs : Group.IsSolvable ↥Y) (hSM : RonanE111.SemisimpleMod T₀ N Y 𝒟)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀)) (hτ : E1.tauOf ⊤ T A ≤ T₀)
    (hmove : ∃ S ∈ 𝒟, ∃ a ∈ A, ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y)
    (hrank : ∀ S ∈ 𝒟,
      (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (S : Set G), (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
        B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    N ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K := by
  set K : Subgroup G := N ⊔ T₀ with hKdef
  have hNK : N ≤ K := le_sup_left
  have hAT : A ≤ T := hAT₀.trans hT₀T
  haveI hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr (sup_le Subgroup.le_normalizer hT₀N)
  have hLift := lift_in_sup_liftP hn hKdef hT hT₀T hAT₀ hAab hT₀A hT₀N hT₀Y hNY hYN hperf hYs
    hSM hSyl hmove hrank
  have hfin : (N.subgroupOf K).map K.subtype ≤
      T ⊔ ⨆ X ∈ {X : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A X}, X := by
    refine (Subgroup.map_mono hLift).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K)]
    simp only [Subgroup.map_iSup]
    exact sup_le_sup inf_le_left (iSup_le fun K' => iSup_le fun hK' =>
      le_iSup₂_of_le (K'.map K.subtype) (mem_members_liftP hKdef hT hAT hAab hT₀T hAT₀ hT₀A
        hSyl hτ hK') le_rfl)
  rwa [Subgroup.map_subgroupOf_eq_of_le hNK] at hfin

theorem cover_diagP [Finite G] {n : ℕ} (hn : 1 ≤ n) {X T A J C : Subgroup G} [Fintype ↥C]
    (h : E111R.DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : RonanE111.JData (RonanE111.actE T A J) J D Y 𝒟) (hSylD : IsSylowIn 2 (T ⊓ D) D)
    (hmove : (∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ Y) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ S ∈ 𝒟,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓
            Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    RonanE111.dimg h.diagComm D ≤
      T ⊔ ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K := by
  obtain ⟨S₀, hS₀⟩ := hJD.nonempty
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wreath_struct h hJD hS₀ hSylD
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hT₀A : ∀ t ∈ RonanE111.actT T A, ∀ a ∈ A, t * a = a * t := fun t ht a ha =>
    (Subgroup.mem_centralizer_iff.mp ht.2 a ha).symm
  have hAT₀ : A ≤ RonanE111.actT T A := fun a ha =>
    ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm hb ha⟩
  have hτ : E1.tauOf ⊤ T A ≤ RonanE111.actT T A :=
    E111R.tauOf_le (E111R.pCoreOf_two_eq_bot h.red) T A
  exact h1.trans (lift_semisimple_subP hn hT inf_le_left hAT₀ h.elem hT₀A h4 h5 h6 h3 h7 h8 h9
    h11 hτ (wreath_move h hJD hS₀ hmove) (wreath_rank h hJD hS₀ n hrank))







