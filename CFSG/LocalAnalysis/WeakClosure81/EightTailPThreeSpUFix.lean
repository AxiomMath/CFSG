module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

section RootData

variable {S : Type} [Group S] {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S}
  {R Sy : Subgroup S} {e : ℕ}

private theorem wc85fx_map_rho_barSub (D : RootData V H T S ψ ρ R Sy e) {a : G} (ha : a ∈ H)
    {A : Subgroup G} (hA : A ≤ kGenIn V H) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom (barSub (kGenIn V H) ψ A) =
      barSub (kGenIn V H) ψ (conjSubgroup A a⁻¹) := by
  classical
  have hN : a ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup ha
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hs
    have hxK : a * (k : G) * a⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp hN (k : G)).mp k.2
    have hxA : a * (k : G) * a⁻¹ ∈ conjSubgroup A a⁻¹ :=
      (mem_conjSubgroup_iff (A := A) (g := a⁻¹) (x := a * (k : G) * a⁻¹)).mpr (by
        simpa [mul_assoc] using hkA)
    refine mem_barSub.mpr ⟨⟨a * (k : G) * a⁻¹, hxK⟩, hxA, ?_⟩
    exact (D.act ⟨a, ha⟩ k ⟨a * (k : G) * a⁻¹, hxK⟩ rfl).symm
  · intro hy
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hy
    have hk' : a⁻¹ * (k : G) * a ∈ A := by
      simpa only [inv_inv] using
        (mem_conjSubgroup_iff (A := A) (g := a⁻¹) (x := (k : G))).mp hkA
    have hk'K : a⁻¹ * (k : G) * a ∈ kGenIn V H := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) (k : G)).mp k.2
    refine mem_map.mpr ⟨ψ ⟨a⁻¹ * (k : G) * a, hk'K⟩,
      mem_barSub.mpr ⟨_, hk', rfl⟩, ?_⟩
    exact D.act ⟨a, ha⟩ ⟨a⁻¹ * (k : G) * a, hk'K⟩ k
      (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)

private theorem wc85fx_eq_one_of_mem_center_of_sq_eq_one {Y : Type} [Group Y] [Finite Y]
    (hodd : Odd (Nat.card (Subgroup.center Y))) {z : Y}
    (hz : z ∈ Subgroup.center Y) (hz2 : z * z = 1) : z = 1 := by
  have hz2' : z ^ 2 = 1 := by rwa [pow_two]
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2'
  have hodd' : Odd (orderOf z) := by
    rw [← Subgroup.orderOf_mk z hz]
    exact hodd.of_dvd_nat (orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center Y))
  have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 1 ≤ orderOf z := orderOf_pos z
  have h1 : orderOf z = 1 := by
    rcases Nat.eq_or_lt_of_le hle with h | h
    · rw [h] at hodd'
      norm_num at hodd'
    · omega
  exact orderOf_eq_one_iff.mp h1

private theorem wc85fx_barSub_mem_center_iff {K N : Subgroup G} {Y : Type} [Group Y]
    {φ : ↥K →* Y} (hφ : IsBarMap K N φ) (k : ↥K) :
    φ k ∈ Subgroup.center Y ↔ (k : G) ∈ centerPre K (N : Set G) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hk
    refine ⟨k.2, fun x hx => ?_⟩
    have h1 : φ (k * (⟨x, hx⟩ : ↥K) * k⁻¹ * (⟨x, hx⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
      group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe] using
      (hφ.ker_iff _).mp h1
  · rintro ⟨-, hx⟩ g
    obtain ⟨y, rfl⟩ := hφ.surjective g
    have h1 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
      refine (hφ.ker_iff _).mpr ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe] using hx (y : G) y.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

private theorem wc85fx_eq_of_involutions_of_map_eq {A B : Type} [Group A] [Group B]
    (π : A →* B) (hcen : ∀ z ∈ π.ker, z ∈ Subgroup.center A)
    (hinv : ∀ z ∈ π.ker, z * z = 1 → z = 1) {t s : A}
    (ht : t * t = 1) (hs : s * s = 1) (hts : π t = π s) : t = s := by
  have hz : t * s⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hts, mul_inv_cancel]
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  set z := t * s⁻¹ with hzdef
  have hcomm : s * z = z * s := Subgroup.mem_center_iff.mp (hcen _ hz) s
  have hzs : z * s = t := by rw [hzdef, inv_mul_cancel_right]
  have hzz : z * z = 1 := by
    calc z * z = z * z * (s * s) := by rw [hs, mul_one]
      _ = z * (z * s) * s := by simp only [mul_assoc]
      _ = z * (s * z) * s := by rw [hcomm]
      _ = (z * s) * (z * s) := by simp only [mul_assoc]
      _ = t * t := by rw [hzs]
      _ = 1 := ht
  have h1 := hinv z hz hzz
  rw [hzdef, hs'] at h1
  exact mul_inv_eq_one.mp (by rw [hs']; exact h1)

theorem wc85fx_conjSubgroup_eq_of_barSub_eq (D : RootData V H T S ψ ρ R Sy e) {a a' : G}
    (ha : a ∈ H) (ha' : a' ∈ H)
    (hbar : barSub (kGenIn V H) ψ (conjSubgroup V a) =
      barSub (kGenIn V H) ψ (conjSubgroup V a')) :
    conjSubgroup V a = conjSubgroup V a' := by
  obtain ⟨X₀, hX₀grp, φ₀, hφ₀⟩ := exists_barMap_eCent D.hyp D.eq_sup
  letI := hX₀grp
  haveI : Finite X₀ := Finite.of_surjective φ₀ hφ₀.surjective
  have hts : TailSetup V H T φ₀ := ⟨D.hyp, D.eq_sup, hφ₀⟩
  have hle : φ₀.ker ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [hφ₀.ker_iff] at hk
    rw [D.ker, D.hyp.centerPre_eCentSet_eq D.eq_sup]
    exact ⟨k.2, D.hyp.comm_mem_pCoreOf_of_mem_inf_centralizer D.eq_sup hk⟩
  let π : X₀ →* S := MonoidHom.liftOfSurjective φ₀ hφ₀.surjective ⟨ψ, hle⟩
  have hπ : ∀ k, π (φ₀ k) = ψ k := fun k => by simp [π]
  have hcen : ∀ z ∈ π.ker, z ∈ Subgroup.center X₀ := by
    intro z hz
    obtain ⟨k, rfl⟩ := hφ₀.surjective z
    have hψk : ψ k = 1 := by
      have h := MonoidHom.mem_ker.mp hz
      rwa [hπ] at h
    have hkC : (k : G) ∈ centerPre (kGenIn V H) (eCentSet V H T) := (D.ker k).mp hψk
    exact (wc85fx_barSub_mem_center_iff hφ₀ k).mpr (by simpa only [eCentSet] using hkC)
  have hinv : ∀ z ∈ π.ker, z * z = 1 → z = 1 := fun z hz hz2 =>
    wc85fx_eq_one_of_mem_center_of_sq_eq_one (odd_card_center_bar hts) (hcen z hz) hz2
  have hstep : ∀ {b b' : G}, barSub (kGenIn V H) ψ (conjSubgroup V b) ≤
      barSub (kGenIn V H) ψ (conjSubgroup V b') →
      barSub (kGenIn V H) φ₀ (conjSubgroup V b) ≤
        barSub (kGenIn V H) φ₀ (conjSubgroup V b') := by
    intro b b' hleψ w hw
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hw
    have hψk : ψ k ∈ barSub (kGenIn V H) ψ (conjSubgroup V b') :=
      hleψ (mem_barSub.mpr ⟨k, hkA, rfl⟩)
    obtain ⟨k', hkA', hk'ψ⟩ := mem_barSub.mp hψk
    have hk2 : k * k = 1 := Subtype.ext (by
      have h := (isElemAbelian_conjSubgroup' D.hyp.elemAbelian b).2 (k : G) hkA
      simpa [pow_two] using h)
    have hk'2 : k' * k' = 1 := Subtype.ext (by
      have h := (isElemAbelian_conjSubgroup' D.hyp.elemAbelian b').2 (k' : G) hkA'
      simpa [pow_two] using h)
    have ht : φ₀ k * φ₀ k = 1 := by rw [← map_mul, hk2, map_one]
    have hs : φ₀ k' * φ₀ k' = 1 := by rw [← map_mul, hk'2, map_one]
    have heqπ : π (φ₀ k) = π (φ₀ k') := by rw [hπ k, hπ k', hk'ψ]
    have heq := wc85fx_eq_of_involutions_of_map_eq π hcen hinv ht hs heqπ
    exact mem_barSub.mpr ⟨k', hkA', heq.symm⟩
  have heq₀ : barSub (kGenIn V H) φ₀ (conjSubgroup V a) =
      barSub (kGenIn V H) φ₀ (conjSubgroup V a') :=
    le_antisymm (hstep hbar.le) (hstep hbar.ge)
  exact conjSubgroup_eq_of_barSub_eq hts ha ha' heq₀

theorem wc85fx_exists_conjSubgroup_le_T_barSub_eq (D : RootData V H T S ψ ρ R Sy e)
    {X : Subgroup S} (hX : X ∈ rootGroupsIn R Sy) :
    ∃ a : G, a ∈ H ∧ conjSubgroup V a ≤ T ∧
      barSub (kGenIn V H) ψ (conjSubgroup V a) = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := hX.1
  obtain ⟨k, hk⟩ := D.surj s
  have hkH : (k : G) ∈ H := (kGenIn_le_H D.hyp.le_H) k.2
  have hW0K : conjSubgroup V (k : G) ≤ kGenIn V H :=
    conjSubgroup_le_kGenIn_of_mem_H D.hyp D.eq_sup hkH
  have hbar0 : barSub (kGenIn V H) ψ (conjSubgroup V (k : G)) = X := by
    rw [barSub_conjSubgroup ψ V k, D.root, hk]
    exact hs.symm
  have hW0Y : conjSubgroup V (k : G) ≤ barPre (kGenIn V H) ψ Sy := by
    intro w hw
    refine mem_barPre.mpr ⟨hW0K hw, ?_⟩
    have hmem : ψ ⟨w, hW0K hw⟩ ∈ barSub (kGenIn V H) ψ (conjSubgroup V (k : G)) :=
      mem_barSub.mpr ⟨⟨w, hW0K hw⟩, hw, rfl⟩
    rw [hbar0] at hmem
    exact hX.2 hmem
  have hW0p : IsPGroup 2 (conjSubgroup V (k : G)) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
      (isElemAbelian_conjSubgroup' D.hyp.elemAbelian k)
  have hSylK : IsSylowIn 2 (T ⊓ kGenIn V H) (kGenIn V H) :=
    D.hyp.sylow_H.inf_normal (kGenIn_le_H D.hyp.le_H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (kGenIn_le_H D.hyp.le_H)).mpr
        (D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup))
  have hTKY : T ⊓ kGenIn V H ≤ barPre (kGenIn V H) ψ Sy := by
    intro x hx
    obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.mp hx
    refine mem_barPre.mpr ⟨hxK, ?_⟩
    have hmem : ψ ⟨x, hxK⟩ ∈ barSub (kGenIn V H) ψ T :=
      mem_barSub.mpr ⟨⟨x, hxK⟩, hxT, rfl⟩
    rwa [D.sylow] at hmem
  have hYK : barPre (kGenIn V H) ψ Sy ≤ kGenIn V H := barPre_le _ _ _
  have hSylY : IsSylowTwoOf (T ⊓ kGenIn V H) (barPre (kGenIn V H) ψ Sy) := by
    refine ⟨hTKY, hSylK.isPGroup, ?_⟩
    change ¬ 2 ∣ (T ⊓ kGenIn V H).relIndex (barPre (kGenIn V H) ψ Sy)
    intro h2
    have hdvd : 2 ∣ (T ⊓ kGenIn V H).relIndex (kGenIn V H) := by
      rw [← Subgroup.relIndex_mul_relIndex (T ⊓ kGenIn V H)
        (barPre (kGenIn V H) ψ Sy) (kGenIn V H) hTKY hYK]
      exact dvd_mul_of_dvd_left h2 _
    exact hSylK.not_dvd_relIndex hdvd
  obtain ⟨y, hyY, hyT⟩ := exists_conj_le_of_isSylowTwoOf hSylY hW0Y hW0p
  set c : G := y⁻¹ with hc
  have hcY : c ∈ barPre (kGenIn V H) ψ Sy := by
    rw [hc]
    exact (barPre (kGenIn V H) ψ Sy).inv_mem hyY
  have hcj : cjSub y (conjSubgroup V (k : G)) = conjSubgroup (conjSubgroup V (k : G)) c := by
    simp only [cjSub, conjSubgroup, hc, inv_inv]
  have hcT : conjSubgroup (conjSubgroup V (k : G)) c ≤ T ⊓ kGenIn V H := hcj ▸ hyT
  obtain ⟨hcK, hcSy⟩ := mem_barPre.mp hcY
  have hmemT : ψ ⟨c, hcK⟩ ∈ barSub (kGenIn V H) ψ T := by
    rw [D.sylow]
    exact hcSy
  obtain ⟨t, htT, htψ⟩ := mem_barSub.mp hmemT
  have htH : (t : G) ∈ H := D.hyp.T_le_H htT
  have hctK : c * (t : G)⁻¹ ∈ kGenIn V H :=
    (kGenIn V H).mul_mem hcK ((kGenIn V H).inv_mem t.2)
  set k' : ↥(kGenIn V H) := ⟨c * (t : G)⁻¹, hctK⟩ with hk'def
  have hcH : c ∈ H := (kGenIn_le_H D.hyp.le_H) hcK
  have hk'H : (k' : G) ∈ H := by
    rw [show (k' : G) = c * (t : G)⁻¹ from rfl]
    exact H.mul_mem hcH (H.inv_mem htH)
  have haH : (k : G) * (k' : G) ∈ H := H.mul_mem hkH hk'H
  have ha_eq : conjSubgroup V ((k : G) * (k' : G)) =
      conjSubgroup (conjSubgroup V (k : G)) (k' : G) := by
    rw [conjSubgroup_conjSubgroup]
  have haT : conjSubgroup V ((k : G) * (k' : G)) ≤ T := by
    rw [ha_eq]
    have h1 : conjSubgroup (conjSubgroup V (k : G)) (k' : G) =
        conjSubgroup (conjSubgroup (conjSubgroup V (k : G)) c) (t : G)⁻¹ := by
      rw [show (k' : G) = c * (t : G)⁻¹ from rfl]
      exact (conjSubgroup_conjSubgroup (conjSubgroup V (k : G)) c (t : G)⁻¹).symm
    rw [h1]
    exact conjSubgroup_le_of_le (hcT.trans inf_le_left) (T.inv_mem htT)
  have hbar_a : barSub (kGenIn V H) ψ (conjSubgroup V ((k : G) * (k' : G))) = X := by
    rw [ha_eq, barSub_conjSubgroup ψ (conjSubgroup V (k : G)) k', hbar0]
    have hψk' : ψ k' = 1 := by
      have hk'eq : k' = (⟨c, hcK⟩ : ↥(kGenIn V H)) * t⁻¹ := Subtype.ext (by rfl)
      rw [hk'eq, map_mul, map_inv, htψ, mul_inv_cancel]
    rw [hψk', conjSubgroup_one]
  exact ⟨(k : G) * (k' : G), haH, haT, hbar_a⟩

theorem rootData_fix_const (D : RootData V H T S ψ ρ R Sy e) {U : Subgroup G}
    (hU : ∃ g : G, U = conjSubgroup V g) (hUT : U ≤ T) {u : G} (hu : u ∈ U) (huH : u ∈ H)
    (hu1 : u ≠ 1) {X : Subgroup S} (hX : X ∈ rootGroupsIn R Sy)
    (hfix : Subgroup.map (ρ ⟨u, huH⟩).toMonoidHom X = X) :
    ∀ (u' : G), u' ∈ U → ∀ hu'H : u' ∈ H, Subgroup.map (ρ ⟨u', hu'H⟩).toMonoidHom X = X := by
  obtain ⟨g, rfl⟩ := hU
  obtain ⟨Y, hYH, hYT, hYbar⟩ := wc85fx_exists_conjSubgroup_le_T_barSub_eq D hX
  have hYK : conjSubgroup V Y ≤ kGenIn V H :=
    conjSubgroup_le_kGenIn_of_mem_H D.hyp D.eq_sup hYH
  have hfixY : Subgroup.map (ρ ⟨u, huH⟩).toMonoidHom
      (barSub (kGenIn V H) ψ (conjSubgroup V Y)) =
        barSub (kGenIn V H) ψ (conjSubgroup V Y) := by
    rw [hYbar, hfix]
  have hConj : barSub (kGenIn V H) ψ (conjSubgroup (conjSubgroup V Y) u⁻¹) =
      barSub (kGenIn V H) ψ (conjSubgroup V Y) := by
    rw [← wc85fx_map_rho_barSub D huH hYK]
    exact hfixY
  have huT : u ∈ T := hUT hu
  have hu'H : u⁻¹ ∈ H := H.inv_mem huH
  have hImg : barSub (kGenIn V H) ψ (conjSubgroup V (Y * u⁻¹)) =
      barSub (kGenIn V H) ψ (conjSubgroup V Y) := by
    rw [← conjSubgroup_conjSubgroup]
    exact hConj
  have hYeq : conjSubgroup V (Y * u⁻¹) = conjSubgroup V Y :=
    (wc85fx_conjSubgroup_eq_of_barSub_eq (a := Y) (a' := Y * u⁻¹) D hYH
      (H.mul_mem hYH hu'H) hImg.symm).symm
  have hNinv : u⁻¹ ∈ Subgroup.normalizer (conjSubgroup V Y : Set G) := by
    refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
    rw [conjSubgroup_conjSubgroup]
    exact hYeq
  have huN : u ∈ Subgroup.normalizer (conjSubgroup V Y : Set G) := by
    simpa using (Subgroup.normalizer _).inv_mem hNinv
  have hNbot : conjSubgroup V g ⊓ Subgroup.normalizer (conjSubgroup V Y : Set G) ≠ ⊥ := by
    intro hbot
    have : u ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hu, huN⟩
    exact hu1 (Subgroup.mem_bot.mp this)
  have hP : IsPGroup 2 ↥(conjSubgroup V g ⊔ conjSubgroup V Y) :=
    D.hyp.sylow_H.isPGroup.to_le (sup_le hUT hYT)
  have hcomm := commute_of_isPGroup_sup D.hyp.elemAbelian D.hyp.isTI ⟨g, rfl⟩ ⟨Y, rfl⟩ hNbot hP
  intro u' hu' hu'H
  have hcomm' : ∀ v ∈ conjSubgroup V Y, u' * v = v * u' := fun v hv => hcomm u' hu' v hv
  have hu'C : u' ∈ Subgroup.centralizer (conjSubgroup V Y : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm' v hv).symm
  have hu'N : u' ∈ Subgroup.normalizer (conjSubgroup V Y : Set G) :=
    Subgroup.centralizer_le_normalizer _ hu'C
  have hNfix : conjSubgroup (conjSubgroup V Y) u'⁻¹ = conjSubgroup V Y :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((Subgroup.normalizer _).inv_mem hu'N)
  rw [← hYbar, wc85fx_map_rho_barSub D hu'H hYK, hNfix]

end RootData

end CFSG.LocalAnalysis.WeakClosure81

end
