module

public import CFSG.Quasithin.Vol2.Ch10SecKRTb
public import CFSG.Quasithin.Background.A3Structure318Star
public import CFSG.Quasithin.Vol2.Ch10SecKIK2b
public import CFSG.Quasithin.Vol2.Ch10SecKIK2c
public import CFSG.Quasithin.Vol2.Ch10SecKIK2d
public import CFSG.Quasithin.Vol2.Ch10SecKIK4a
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

theorem exists_pi (cfg : B0KConfig G T L I H K M₁ J n m) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hJN : J ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G)) :
    ∃ π : ↥(modO2Image M₁ J) →* ↥(autI hV J), Function.Surjective π := by
  obtain ⟨e⟩ := modO2_mulEquiv cfg.hJ
  exact ⟨(SecC.C10KH.piJ hV hJN hO).comp e.symm.toMonoidHom,
    (SecC.C10KH.piJ_surjective hV hJN hO).comp e.symm.surjective⟩

omit [Finite G] in
theorem exists_ne_one_autI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hnt : ¬ J ≤ Subgroup.centralizer (V : Set G)) :
    ∃ x : ↥(autI hV J), x ≠ 1 := by
  obtain ⟨j, hj, hjC⟩ : ∃ j ∈ J, j ∉ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hnt h
  exact ⟨SecC.C10KH.rhoJ hV hJN ⟨j, hj⟩,
    fun h => hjC ((SecC.C10KH.rhoJ_eq_one_iff hV hJN ⟨j, hj⟩).mp h)⟩

omit [Finite G] in
theorem card_eq_or_of_quasisimple {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hq : CFSG.IsQuasisimple Y)
    (hZ : Nat.card (Subgroup.center Y) = 1 ∨ Nat.card (Subgroup.center Y) = 3)
    {x : X} (hx : x ≠ 1) : Nat.card Y = Nat.card X ∨ Nat.card Y = 3 * Nat.card X := by
  obtain ⟨y, rfl⟩ := hπ x
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq ⟨y, hx⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hπ
  have hdvd : Nat.card π.ker ∣ Nat.card (Subgroup.center Y) := Subgroup.card_dvd_of_le hker
  rcases hZ with h1 | h3
  · rw [h1, Nat.dvd_one] at hdvd
    left
    rw [← hcard, hdvd, one_mul]
  · rw [h3] at hdvd
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · left
      rw [← hcard, h, one_mul]
    · right
      rw [← hcard, h]

theorem card_center_Jbar (h36' : A36ForSQTK) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hq : CFSG.IsQuasisimple ↥(modO2Image M₁ J)) :
    Nat.card (Subgroup.center ↥(modO2Image M₁ J)) = 1 ∨
      Nat.card (Subgroup.center ↥(modO2Image M₁ J)) = 3 := by
  have h := ((h36' _ (sqtkHyp_of_cat (sqtkHypCat_bar cfg))) _ (Jbar_mem_cComp cfg)).1
  rcases h with ⟨-, hs, -⟩ | ⟨-, h3, -⟩ | h3 | h4
  · left
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(modO2Image M₁ J)) with
      h | h
    · rw [h, Subgroup.card_bot]
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      have : Subsingleton (↥(modO2Image M₁ J) ⧸ Subgroup.center ↥(modO2Image M₁ J)) :=
        QuotientGroup.subsingleton_iff.mpr h
      exact hab (Subsingleton.elim _ _)
  · exact Or.inr h3
  · exact absurd (Or.inl h3) (A318.not_case34_of_quasisimple hq)
  · exact absurd (Or.inr h4) (A318.not_case34_of_quasisimple hq)

theorem card_of_normal (h56 : AsB56) (h36' : A36ForSQTK) (h1022 : Stmt10_2_2)
    (cfg : B0KConfig G T L I H K M₁ J n m) (hTJ : T ≤ Subgroup.normalizer (J : Set G))
    (hq : CFSG.IsQuasisimple ↥(modO2Image M₁ J)) :
    ∃ M : ℕ, SecC.C10KH.B56Card M ∧
      (Nat.card ↥(modO2Image M₁ J) = M ∨ Nat.card ↥(modO2Image M₁ J) = 3 * M) := by
  have hH₀ : J ⊔ T ≤ M₁ := sup_le (J_le cfg) (T_le cfg)
  have hJH₀ : J ⊔ T ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTJ
  have hKT : conjClosure K T ≤ J := conjClosure_le fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTJ ht) k).mp (cfg.hKJ hk)
  have ff := ffSet h1022 cfg le_sup_right hH₀ (H_le_of cfg le_sup_right (hKT.trans le_sup_left))
  have hJN := (le_sup_left : J ≤ J ⊔ T).trans ff.red.2.1
  have hO := SecC.C10KH.pCoreOf_le_centralizer ff.red le_sup_left hJH₀
  have hnt := fun h => ff.K_not (cfg.hKJ.trans h)
  obtain ⟨π, hπ⟩ := exists_pi cfg ff.elem hJN hO
  obtain ⟨x, hx⟩ := exists_ne_one_autI ff.elem hJN hnt
  obtain ⟨y, rfl⟩ := hπ x
  have hJq : CFSG.IsQuasisimple ↥(autI ff.elem J) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hπ ⟨y, hx⟩
  have h2 := InternalSec.two_of_sup cfg.hyp.fsu.sylow.1 hTJ
  have hlist := SecC.C10KH.b56List_autI h56 ff.elem ff.sqtk ff.sylow ff.red le_sup_left hJH₀ h2
    hJq ff.thompson
  exact ⟨_, SecC.C10KH.b56Card_of_list hlist,
    card_eq_or_of_quasisimple π hπ hq (card_center_Jbar h36' cfg hq) hx⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
