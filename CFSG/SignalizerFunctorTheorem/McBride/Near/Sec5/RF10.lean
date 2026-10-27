module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxQuot
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxSmear

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem cenIn_kOf_le_kOf_cenIn
    {p : ℕ} {A Y : Subgroup Γ} (hp : p.Prime) (hA : IsElemAbelian p A)
    (hY : Admits A Y) (hnear : signalizerNearPSolvable p ↥Y) {b : Γ} (hb : b ∈ A)
    (_hb1 : b ≠ 1) : cenIn (kOf Y) {b} ≤ kOf (cenIn Y {b}) := by
  have hcopY : Nat.Coprime p (Nat.card Y) := hnear.1
  have hbp : b ^ p = 1 := hA.2 b hb
  have hbY : b ∈ Subgroup.normalizer (Y : Set Γ) := hY hb
  have hzE : IsElemAbelian p (Subgroup.zpowers b) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA (Subgroup.zpowers_le.mpr hb)
  have hR : Group.IsSolvable (sol Y) := isSolvable_sol Y
  have hYN : Y ≤ AChief.nrm (sol Y) := SolQuot.le_nrm_sol Y
  have hbN : b ∈ AChief.nrm (sol Y) := SolQuot.normalizer_le_nrm_sol Y hbY
  have hzN : Subgroup.zpowers b ≤ AChief.nrm (sol Y) := Subgroup.zpowers_le.mpr hbN
  have hzY : Subgroup.zpowers b ≤ Subgroup.normalizer (Y : Set Γ) := Subgroup.zpowers_le.mpr hbY
  have hzK : Subgroup.zpowers b ≤ Subgroup.normalizer (kOf Y : Set Γ) :=
    hzY.trans (Thm52Aux.normalizer_le_normalizer_kOf Y)
  set b' : AChief.QG (sol Y) := AChief.qmap (sol Y) ⟨b, hbN⟩ with hb'
  have hqz : AChief.qimg (sol Y) (Subgroup.zpowers b) = Subgroup.zpowers b' :=
    SolQuot.qimg_zpowers hbN
  have hsolZ : sol (AChief.qimg (sol Y) Y) = ⊥ := by
    rw [SolQuot.sol_qimg hR hYN]
    exact SolQuot.qimg_self
  have hb'Z : b' ∈ Subgroup.normalizer ((AChief.qimg (sol Y) Y : Subgroup _) : Set _) := by
    have := AChief.qimg_le_normalizer (N := sol Y) hzY
    rw [hqz] at this
    exact Subgroup.zpowers_le.mp this
  have hb'p : b' ^ p = 1 := by
    rw [hb', ← map_pow]
    have : (⟨b, hbN⟩ : AChief.nrm (sol Y)) ^ p = 1 := Subtype.ext (by simpa using hbp)
    rw [this, map_one]
  have hcopZ : Nat.Coprime p (Nat.card (AChief.qimg (sol Y) Y)) :=
    hcopY.coprime_dvd_right (Subgroup.card_dvd_of_surjective (SolQuot.qres_surjective hYN))
  have hfix := fun (J : Subgroup (AChief.QG (sol Y))) (hJ : J ∈ lcal (AChief.qimg (sol Y) Y))
    (hbJ : b' ∈ Subgroup.normalizer (J : Set (AChief.QG (sol Y)))) (hnc : ¬ J ≤
      Subgroup.centralizer {b'}) =>
    Thm52Aux.isSolvable_inf_centralizer_qimg hp hYN hnear hb'p hJ hbJ hnc
  have key := Thm52Aux.kOf_inf_centralizer_le_kOf_inf_centralizer hp hsolZ hb'Z hb'p hcopZ hfix
  have hcenK : AChief.qimg (sol Y) (cenIn (kOf Y) {b}) =
      kOf (AChief.qimg (sol Y) Y) ⊓ Subgroup.centralizer {b'} := by
    unfold cenIn
    have hcopK : Nat.Coprime p (Nat.card (kOf Y)) :=
      hcopY.coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le Y))
    rw [← Thm52Aux.centralizer_zpowers_eq, SolQuot.kOf_qimg hR hYN,
      AChief.qimg_inf_centralizer hp hzE hzK hzN ((kOf_le Y).trans hYN) hcopK, hqz,
      Thm52Aux.centralizer_zpowers_eq]
  have hcenY : AChief.qimg (sol Y) (cenIn Y {b}) =
      AChief.qimg (sol Y) Y ⊓ Subgroup.centralizer {b'} := by
    unfold cenIn
    rw [← Thm52Aux.centralizer_zpowers_eq,
      AChief.qimg_inf_centralizer hp hzE hzY hzN hYN hcopY, hqz,
      Thm52Aux.centralizer_zpowers_eq]
  have hΓ₀N : cenIn Y {b} ≤ AChief.nrm (sol Y) := inf_le_left.trans hYN
  have hkΓ₀ : kOf (AChief.qimg (sol Y) (cenIn Y {b})) =
      AChief.qimg (sol Y) (kOf (cenIn Y {b})) := SolQuot.kOf_qimg hR hΓ₀N
  intro x hx
  have hxΓ₀ : x ∈ cenIn Y {b} := inf_le_inf_right _ (kOf_le Y) hx
  have hmem : AChief.qmap (sol Y) ⟨x, hΓ₀N hxΓ₀⟩ ∈ AChief.qimg (sol Y) (kOf (cenIn Y {b})) := by
    rw [← hkΓ₀, hcenY]
    have : AChief.qmap (sol Y) ⟨x, hΓ₀N hxΓ₀⟩ ∈ AChief.qimg (sol Y) (cenIn (kOf Y) {b}) :=
      (AChief.mem_qimg_iff _ _ _).mpr ⟨⟨x, hΓ₀N hxΓ₀⟩, hx, rfl⟩
    rw [hcenK] at this
    exact key this
  exact SolQuot.mem_of_qmap_mem_qimg (kOf_le _)
    ((SolQuot.inf_le_sol hR hΓ₀N).trans (sol_le_kOf _)) hxΓ₀ hmem

section Functor

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem kOf_apply_inf_centralizer_le
    (hθ : NearFunctor p A θ) {a b : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    kOf (θ a) ⊓ Subgroup.centralizer {b} ≤
      kOf (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := by
  have h := cenIn_kOf_le_kOf_cenIn hθ.prime hθ.elemAbelian (hθ.isFunctor.normalized a ha ha1)
    (hθ.near a ha ha1).1 hb hb1
  have heq : cenIn (θ a) {b} = thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    unfold cenIn
    rw [← centralizer_zpowers_eq_singleton b]
    exact hθ.isFunctor.inf_centralizer_eq_thetaOf ha ha1 (Subgroup.zpowers_le.mpr hb)
  rwa [heq] at h

theorem kOf_apply_inf_centralizer_le_thetaOf
    (hθ : NearFunctor p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    kOf (θ a) ⊓ Subgroup.centralizer (B : Set G) ≤ kOf (thetaOf θ B) := by
  have ha : a ∈ A := hB.1 haB
  have hza := zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian ha ha1
  have hnle : ¬ B ≤ Subgroup.zpowers a := fun hle => by
    have h1 := Subgroup.card_le_of_le hle
    rw [hB.2, hza.2] at h1
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hθ.prime.one_lt (by norm_num)
    omega
  obtain ⟨b, hbB, hbna⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hb1 : b ≠ 1 := fun h1 => hbna (h1 ▸ one_mem _)
  have hzb := zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian (hB.1 hbB) hb1
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hθ.prime (by rw [hzb.2, pow_one])
      (fun hle => hbna (hle (Subgroup.mem_zpowers b)))
  have hsup : Subgroup.zpowers a ⊔ Subgroup.zpowers b ∈ signalizerFunctorEk p 2 A := by
    simpa using CFSG.SignalizerFunctorTheorem.sup_mem_Ek_succ hθ.elemAbelian hza hzb hdisj
  have hBeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = B :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haB)
      (Subgroup.zpowers_le.mpr hbB)) (by rw [hB.2, hsup.2])
  calc kOf (θ a) ⊓ Subgroup.centralizer (B : Set G)
      ≤ kOf (θ a) ⊓ Subgroup.centralizer {b} :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    _ ≤ kOf (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :=
        kOf_apply_inf_centralizer_le hθ ha ha1 (hB.1 hbB) hb1
    _ = kOf (thetaOf θ B) := by rw [hBeq]

end Functor

end CFSG.SignalizerFunctorTheorem.McBride.Near
