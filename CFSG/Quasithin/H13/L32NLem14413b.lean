module

public import CFSG.Quasithin.H13.L32ARuOne
public import CFSG.Quasithin.H13.L32NLem14332h
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative
open CFSG.Quasithin.H13.L32A

variable {G : Type} [Group G] [Finite G]

theorem quasithinO2QuotientIso_SL3_of_surj {X V : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2))
    (hsurj : Function.Surjective (repV hXV e))
    (h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    quasithinO2QuotientIso X (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := repV_ker hXV e
  refine ⟨repV hXV e, hsurj, le_antisymm ?_ ?_⟩
  ·
    have hnorm : ((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal := by
      rw [← hker]
      exact MonoidHom.normal_ker _
    have hp : IsPGroup 2 ↥((Subgroup.centralizer (V : Set G)).subgroupOf X) := by
      rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := h2 ⟨x, x.2, Subgroup.mem_subgroupOf.mp hx⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hn
    rw [hker]
    exact CFSG.LieType.BorelTits.le_pCore 2 hnorm hp
  ·
    have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      Vol2Native.A312L.Seven.slThree_isSimple
    have hN : ((CFSG.Open.pCore 2 ↥X).map (repV hXV e)).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal (G := ↥X) (r := 2)).map _ hsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((CFSG.Open.pCore 2 ↥X).map (repV hXV e)) with h | h
    · intro x hx
      have : repV hXV e x ∈ (CFSG.Open.pCore 2 ↥X).map (repV hXV e) := ⟨x, hx, rfl⟩
      rw [h] at this
      exact this
    · exfalso
      have hP : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥X).map (repV hXV e)) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) (r := 2)).map _
      rw [h] at hP
      have hcardS : Nat.card ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) =
          168 := by
        rw [Subgroup.card_top, Matrix.card_SL_field]
        simp [Fin.prod_univ_three]
      obtain ⟨k, hk⟩ := hP.exists_card_eq
      rw [hcardS] at hk
      have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : (7 : ℕ) ∣ 168)
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)

theorem quasithinO2QuotientIso_SL3_of {X V : Subgroup G} [IsMulCommutative ↥V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hsq : ∀ v ∈ V, v ^ 2 = 1)
    (hcard : Nat.card ↥V = 2 ^ 3) (htop : autOn X V = ⊤)
    (h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    quasithinO2QuotientIso X (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  exact quasithinO2QuotientIso_SL3_of_surj hXV e (repV_surjective hXV e htop) h2

theorem quasithinO2QuotientIso_LT (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) {T L V V₂ : Subgroup G} (h : Hyp14310One G T L V)
    (hV₂ : IsL32NPlane T V V₂) :
    quasithinO2QuotientIso (L ⊔ T) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨_, S'⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
  have htop : autOn (L ⊔ T) V = ⊤ := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S'.h1281
    rw [eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  exact quasithinO2QuotientIso_SL3_of (sup_le S'.LV S'.TV) (fun v hv => S'.sq_V hv)
    (by rw [S'.card_V]; norm_num) htop S'.isPGroup_cent_sup

end CFSG.Quasithin.H13.L14413
