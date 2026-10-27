module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4S3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section H2

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_tZero_le_normalizer (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s)
    {u : G} (hu : u ∈ uHi T M H R₁) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ tZero T u) :
    tZero T u ≤ T ⊓ Subgroup.normalizer (R₁ : Set G) := by
  classical
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, -⟩ := hdat.setup h35 S hred hshape
  subst hR₁
  have hQ₁P : Q₁ ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) := hpp.1
  have hr₁ : Q₁ ≤ (resBeta (rhoH h98.toHypF91)).range := hQ₁P.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  have hnot : ¬ T ≤ tZero T u := by
    intro hT
    obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h98.toHypF91 hsplit hr₁ hUu hu
    have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h98.toHypF91 hUu).mp (by
      rw [← hkc, e]
      rfl))
    have hfix : ∀ y ∈ (T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)), y k = k := by
      intro y hy
      obtain ⟨x, hxT', rfl⟩ := Subgroup.mem_map.mp hy
      have hc := (hT (Subgroup.mem_subgroupOf.mp hxT')).2.2 u (Subgroup.mem_zpowers u)
      have hρ := (rhoH_clsU_eq_iff h98.toHypF91 x hUu).mpr hc
      refine Subtype.ext ((resBeta_apply _ _ _).trans ?_)
      rw [hkc]
      exact hρ
    exact ((hstr.fixV_Tb hpp).2 k hfix hk1).1 hk
  have hA : tZero T u ≤ T := centralizerMod_le_left _ _ _
  have hdvd : (tZero T u).relIndex T ∣ (T ⊓ Subgroup.normalizer (HLb (resBeta
      (rhoH h98.toHypF91)) Q₁ : Set G)).relIndex T := Subgroup.relIndex_dvd_of_le_left T huT
  rw [hdat.indexT] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.mp h1) hnot
  · have hmul := Subgroup.relIndex_mul_relIndex _ _ _ huT hA
    rw [h2, hdat.indexT] at hmul
    have h1 : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)).relIndex
        (tZero T u) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1

theorem e9z4_H₂ (h35 : Lemma1435) (h2 : Stage1461Two) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s)
    {u : G} (hu : u ∈ uHi T M H R₁) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ tZero T u) :
    tZero T u ≤ R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G)) ∧
      R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G)) ≤
        centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
      Nonempty (OTwoQuot (R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G))) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G)) ≤ M := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hR₂PQ : R₂ ≤ PQ := hdat.plane₂.2.1
  have hR₂H : R₂ ≤ H := hR₂PQ.trans hred.le
  refine ⟨(e9z4_tZero_le_normalizer h35 S hred hshape hdat hu huZ huT).trans le_sup_right, ?_,
    e9z4_oTwoQuot_equiv_perm h35 S hred hshape hdat, ?_⟩
  ·
    refine sup_le (fun h hh => ?_) (huT.trans (centralizerMod_mono_left _ hTH))
    refine ⟨hR₂H hh, S.normalizer_Z.ge (S.le_mcOf hH (hR₂H hh)), fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwu : u ^ k ∈ uHi T M H R₁ := Subgroup.zpow_mem _ hu k
    have h3 := (quasithinOmegaOneCenter T).inv_mem
      (hdat.cent₁ (Subgroup.commutator_mem_commutator hwu hh))
    rw [commutatorElement_inv] at h3
    simpa [commutatorElement_def] using h3
  ·
    intro hXM
    have hR₂M : R₂ ≤ M := le_sup_left.trans hXM
    have hz : R₂ ≤ pCoreOf 2 H := by
      rw [← h2 G T M S H hH p hred.prime hred.odd]
      exact fun x hx => ⟨hred.le_oTwoPIn (hR₂PQ hx), hR₂M hx⟩
    have hrel := hdat.plane₂.2.2.1
    rw [Subgroup.relIndex_eq_one.mpr hz] at hrel
    omega

end H2

end CFSG.Quasithin
