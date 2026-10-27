module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dict
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Rho
public import CFSG.Quasithin.EmptyFaithful.S146zHWsub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

theorem rk_inf_fixV_of_involution_plane (h : E9Z4Str X Tb P) {t : MulAut V} (htX : t ∈ X)
    (ht2 : orderOf t = 2) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3)
    (hrk : rk (commV Q) = 2) : rk ↥(commV Q ⊓ fixV (Subgroup.zpowers t)) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hn := h.zpowers_le_normalizer_of_le htX ht2 hQ
  have hW : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commV Q, x w ∈ commV Q := fun x hx w hw =>
    commV_smul_mem (fun p hp => (Subgroup.mem_normalizer_iff.mp (hn hx) p).mp hp) hw
  have hsum := rk_commSub_add_rk_inf_fixV hW
  have hle : commSub (commV Q) (Subgroup.zpowers t) ≤ commV Q ⊓ fixV (Subgroup.zpowers t) :=
    commSub_zpowers_le_inf_fixV h.sq htsq hW
  have hle' := rk_mono hle
  have hne : rk ↥(commV Q ⊓ fixV (Subgroup.zpowers t)) ≠ 2 := by
    intro h2
    have hbot : commSub (commV Q) (Subgroup.zpowers t) = ⊥ :=
      (rk_eq_zero_iff h.sq).mp (by omega)
    have hfix : ∀ v ∈ commV Q, t v = v := fun v hv =>
      (commSub_eq_bot_iff.mp hbot) hv t (Subgroup.mem_zpowers t)
    obtain ⟨g, hgQ, hg1, -, hg3⟩ := exists_generator_of_prime_card hQ3
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ commV Q, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      rw [(Subgroup.eq_bot_iff_forall _).2 hcon, rk_bot] at hrk
      omega
    have hgv : g v ∈ commV Q :=
      commV_smul_mem (fun q hq => Q.mul_mem (Q.mul_mem hgQ hq) (Q.inv_mem hgQ)) hv
    have e1 : t (g v) = g v := hfix _ hgv
    have e2 : t (g v) = g⁻¹ v := by
      have htg : t * g = g⁻¹ * t := by
        calc t * g = (t * g * t⁻¹) * t := by group
          _ = g⁻¹ * t := by rw [h.inverts_of_involution htX ht2 g (hQ hgQ)]
      calc t (g v) = (t * g) v := rfl
        _ = (g⁻¹ * t) v := by rw [htg]
        _ = g⁻¹ (t v) := rfl
        _ = g⁻¹ v := by rw [hfix v hv]
    have e3 : (g * g) v = v := by
      calc (g * g) v = g (g v) := rfl
        _ = g (g⁻¹ v) := by rw [e1.symm.trans e2]
        _ = v := by simp
    have hgg1 : g * g ≠ 1 := by
      intro e
      have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact e
      have := orderOf_dvd_of_pow_eq_one hg2
      rw [hg3] at this
      omega
    exact hv1 (h.eq_one_of_fix_plane hQ3 (Q.mul_mem hgQ hgQ) hgg1 hv e3)
  omega

theorem exists_move_of_involution_plane (h : E9Z4Str X Tb P) {t : MulAut V} (htX : t ∈ X)
    (ht2 : orderOf t = 2) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3)
    (hrk : rk (commV Q) = 2) : ∃ v ∈ commV Q, t v ≠ v := by
  by_contra hall
  push Not at hall
  have hle : commV Q ≤ fixV (Subgroup.zpowers t) := fun v hv => mem_fixV_zpowers_iff.mpr (hall v hv)
  have h1 := h.rk_inf_fixV_of_involution_plane htX ht2 hQ hQ3 hrk
  rw [inf_eq_left.mpr hle, hrk] at h1
  omega

end E9Z4Str

section Rho

variable {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W] {ρ : Hh →* MulAut W}
  {Tb P : Subgroup (MulAut ↥(kOf ρ))}

theorem exists_move_plane_rho (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (h : E9Z4Str (resBeta ρ).range Tb P) {x : Hh} (hx2 : orderOf (ρ x) = 2)
    {Q : Subgroup (MulAut ↥(kOf ρ))} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3) (hrk : rk (commV Q) = 2) :
    ∃ k ∈ commV Q, ρ x (k : W) ≠ (k : W) := by
  obtain ⟨k, hk, hne⟩ := h.exists_move_of_involution_plane (t := resBeta ρ x) ⟨x, rfl⟩
    ((orderOf_resBeta_eq hsplit x).trans hx2) hQ hQ3 hrk
  exact ⟨k, hk, fun e => hne (Subtype.ext (by rw [resBeta_apply]; exact e))⟩

end Rho

section Group

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Wsub_uHi_HLb
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range) :
    Wsub h (uHi T M H (HLb (resBeta (rhoH h)) Q)) = (commV Q).map (kOf (rhoH h)).subtype := by
  have h1 := tildeOf_comm_HLb h hsplit hQ
  ext w
  rw [mem_Wsub]
  change w.val ∈ tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H,
    HLb (resBeta (rhoH h)) Q⁆ ⊔ quasithinOmegaOneCenter T) ↔ _
  rw [h1]
  constructor
  · rintro ⟨k, hk, hkw⟩
    refine ⟨k, hk, valW_injective h ?_⟩
    exact hkw
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem exists_comm_not_mem_Z
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range) {x : ↥H}
    {k : ↥(kOf (rhoH h))} (hk : k ∈ commV Q) (hmove : rhoH h x (k : UMod h) ≠ (k : UMod h)) :
    ∃ u ∈ uHi T M H (HLb (resBeta (rhoH h)) Q),
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T := by
  have hw : (k : UMod h) ∈ Wsub h (uHi T M H (HLb (resBeta (rhoH h)) Q)) := by
    rw [Wsub_uHi_HLb h hsplit hQ]
    exact ⟨k, hk, rfl⟩
  obtain ⟨u, hu, huX, hcls⟩ :=
    exists_clsU_of_mem_Wsub h (uHi_le_conjClosure (HLb_le Q)) hw
  refine ⟨u, huX, fun hZ => hmove ?_⟩
  rw [← hcls]
  exact (rhoH_clsU_eq_iff h x hu).mpr hZ

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq' {y : G} {X : Subgroup G} (hX : conjSub y X = X) :
    y ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← hX]
    exact mul_mem_conjSub hz
  · intro hz
    have : y * z * y⁻¹ ∈ conjSub y X := by rwa [hX]
    rw [mem_conjSub] at this
    have e : y⁻¹ * (y * z * y⁻¹) * y = z := by group
    rwa [e] at this

theorem mem_normalizer_uHi_HLb (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} {y : ↥H}
    (hQ : conjBy (resBeta (rhoH h) y) Q = Q) :
    (y : G) ∈ Subgroup.normalizer (uHi T M H (HLb (resBeta (rhoH h)) Q) : Set G) := by
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hU : conjSub (y : G) (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
    conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure _ _ y.2)
  have hZ : conjSub (y : G) (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
    conjSub_eq_of_mem_normalizer (hHN y.2)
  have hP : conjSub (y : G) (HLb (resBeta (rhoH h)) Q) = HLb (resBeta (rhoH h)) Q :=
    conjSub_HLb_of_conjBy h hQ
  refine mem_normalizer_of_conjSub_eq' ?_
  unfold uHi
  rw [conjSub_sup, ← conjSub_commutator, hU, hP, hZ]

end Group

end CFSG.Quasithin
