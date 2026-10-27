module

public import CFSG.Quasithin.Background.C116Three.Swap
public import CFSG.Milestones.ASVolI.B610.FamD

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem rk_cent_add [Finite G] [Finite F] {L : Subgroup G} {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (DL : NatData L V F) :
    rk ↥(⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) + 2 * n = rk ↥(⁅V, L⁆ : Subgroup G) := by
  have e1 := Subgroup.card_ker_mul_card_range DL.β
  rw [MonoidHom.range_eq_top.mpr DL.βsurj, Subgroup.card_top, DL.βker] at e1
  have e2 : Nat.card ↥((⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆) =
      Nat.card ↥(⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [e2] at e1
  have h := burnsideB610_rk_of_card_eq_mul e1.symm
  rw [burnsideB610_rk_stdMod hF] at h
  omega

theorem rk_commutator_inf_ge [Finite G] (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {i : ι} (hi : i ∈ S) {B : Subgroup G} {n : ℕ}
    (hB : rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (B : Set G)) + n) :
    rk ↥(⁅V, X i⁆ : Subgroup G) ≤
      rk ↥((⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (B : Set G)) + n := by
  have hVi := hFam.commutator_le hHV hi
  have hc : ∀ a ∈ (⁅V, X i⁆ : Subgroup G), ∀ b ∈ V ⊓ Subgroup.centralizer (B : Set G),
      a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV (hVi ha) hb.1
  have h1 := B2F.rk_sup_add_rk_inf_of_commute hc
  have h2 : (⁅V, X i⁆ : Subgroup G) ⊓ (V ⊓ Subgroup.centralizer (B : Set G)) =
      (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hVi]
  have h3 : rk ↥((⁅V, X i⁆ : Subgroup G) ⊔ (V ⊓ Subgroup.centralizer (B : Set G))) ≤ rk ↥V :=
    rk_mono (sup_le hVi inf_le_left)
  rw [h2] at h1
  omega

theorem le_centralizer_thompsonJ (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (Bf : ι → Subgroup G)
    (hBc : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G))
    (hJ : thompsonJ T ≤ (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    {i : ι} (hi : i ∈ S) :
    (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (Bf i : Set G) ≤
      Subgroup.centralizer (thompsonJ T : Set G) := by
  rintro u ⟨huV, huB⟩
  have hle : (⨆ j ∈ S, Bf j) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (iSup₂_le fun j hj => ?_) ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      by_cases hji : j = i
      · subst hji
        exact (Subgroup.mem_centralizer_iff.mp huB b hb).symm
      · exact Subgroup.mem_centralizer_iff.mp (hBc j hj i hi (Ne.symm hji) hb) _ huV
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp hc.2 _ (hFam.commutator_le hHV hi huV)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact (Subgroup.mem_centralizer_iff.mp (hle (hJ hj)) u rfl).symm

theorem baum_le_normalizer [Finite G] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hFam : burnsideB610_Fam H T V hV F S X D) (hred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) (Bf : ι → Subgroup G)
    (hBc : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G))
    (hBr : ∀ i ∈ S, rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n)
    (hJ : thompsonJ T ≤ (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    {i : ι} (hi : i ∈ S) :
    baum T ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hVi := hFam.commutator_le hHV hi
  have h1 := hFam.rk_commutator_inf_ge hHV hi (hBr i hi)
  have h2 := rk_cent_add hF (D i)
  obtain ⟨u, hu, hux⟩ : ∃ u ∈ (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (Bf i : Set G),
      u ∉ Subgroup.centralizer ((X i : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (Bf i : Set G) ≤
        (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer ((X i : Subgroup G) : Set G) :=
      fun u hu => ⟨hu.1, hcon u hu⟩
    have := rk_mono hle
    omega
  have huJ := hFam.le_centralizer_thompsonJ hHV Bf hBc hJ hi hu
  obtain ⟨l, hl, hlu⟩ : ∃ l ∈ X i, l * u ≠ u * l := by
    by_contra hcon
    push Not at hcon
    exact hux (Subgroup.mem_centralizer_iff.mpr fun l hl => hcon l hl)
  refine C116Three.baum_le_normalizer_of_fixedVector hV hVT ⟨u, hVi hu.1, ⟨l, hl, hlu⟩,
    fun j hj => Subgroup.mem_centralizer_iff.mp huJ j hj, fun x hx hxN l' hl' => ?_⟩
  obtain ⟨j, hj, hxj⟩ := hFam.conj i hi x (hT.1 hx)
  have hji : i ≠ j := by
    rintro rfl
    apply hxN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hxj
  have hmem : x * l' * x⁻¹ ∈ X j := by
    rw [← hxj, mem_cjSub]
    simpa [mul_assoc] using hl'
  exact (Subgroup.mem_centralizer_iff.mp (hFam.triv i hi j hj hji hmem) u hu.1).symm

theorem _root_.CFSG.Quasithin.B610T.burnsideB610_mem_centralizer_of_autI_le {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {X B B' : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hB'V : B' ≤ Subgroup.normalizer (V : Set G))
    (hgen : autI hV X ≤ autI hV B ⊔ autI hV B') {w : G} (hw : w ∈ V)
    (hwB : w ∈ Subgroup.centralizer (B : Set G)) (hwB' : w ∈ Subgroup.centralizer (B' : Set G)) :
    w ∈ Subgroup.centralizer (X : Set G) := by
  rw [← autI_sup hV hBV hB'V] at hgen
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨y, hyBB, hyx⟩ := (mem_autI hV).1 (hgen (convI_mem_autI hV hx (hXV hx)))
  have hc : (y : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : convI hV (y⁻¹ * ⟨x, hXV hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have := (convI_eq_one_iff hV _).1 h1
    simpa using this
  have hle : B ⊔ B' ≤ Subgroup.centralizer ({w} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp hwB b hb).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp hwB' b hb).symm
  have hy : (y : G) * w = w * y := (Subgroup.mem_centralizer_iff.mp (hle hyBB) w rfl).symm
  have hcw : ((y : G)⁻¹ * x) * w = w * ((y : G)⁻¹ * x) :=
    (Subgroup.mem_centralizer_iff.mp hc w hw).symm
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  calc (y : G) * ((y : G)⁻¹ * x) * w = (y : G) * (((y : G)⁻¹ * x) * w) := by group
    _ = (y : G) * (w * ((y : G)⁻¹ * x)) := by rw [hcw]
    _ = ((y : G) * w) * ((y : G)⁻¹ * x) := by group
    _ = (w * y) * ((y : G)⁻¹ * x) := by rw [hy]
    _ = w * ((y : G) * ((y : G)⁻¹ * x)) := by group

theorem le_sup_centralizer [Finite G] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hFam : burnsideB610_Fam H T V hV F S X D) (hred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) (Bf : ι → Subgroup G)
    (hBf : ∀ i ∈ S, Bf i ≤ thompsonJ T ∧ Bf i ≤ X i ∧
      (∀ j ∈ S, j ≠ i → Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img (Bf i)) = 2 ^ n ∧
      rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n)
    (hJ : thompsonJ T ≤ (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    {i : ι} (hi : i ∈ S) :
    V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤
      ((⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ⊓
          Subgroup.centralizer ((X i : Subgroup G) : Set G)) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHV
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  obtain ⟨hBJ, hBX, -, hBq, hBr⟩ := hBf i hi
  have hBc : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G) :=
    fun i hi => (hBf i hi).2.2.1
  have hXV : X i ≤ Subgroup.normalizer (V : Set G) := (hFam.le i hi).trans hHV
  have hB2 : IsPGroup 2 (Bf i) := hT.2.1.to_le (hBJ.trans hJT)
  obtain ⟨k, hk, hgen⟩ := hFam.gen i hi (Bf i) hBX hB2 (by rw [hBq, hF])
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := hXV hk.1
  have hBV : Bf i ≤ Subgroup.normalizer (V : Set G) := hBX.trans hXV
  have hB'V : cjSub k (Bf i) ≤ Subgroup.normalizer (V : Set G) := cjSub_le (Subgroup.le_normalizer hkV) hBV
  have hVi := hFam.commutator_le hHV hi
  set CBi : Subgroup G := (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (Bf i : Set G) with hCBi
  set CB' : Subgroup G := V ⊓ Subgroup.centralizer (cjSub k (Bf i) : Set G) with hCB'
  have r1 : rk ↥(⁅V, X i⁆ : Subgroup G) ≤ rk ↥CBi + n := hFam.rk_commutator_inf_ge hHV hi hBr
  have r2 : rk ↥CB' = rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) :=
    B2F.rk_inf_centralizer_cjSub hkV (Bf i)
  have r3 : CBi ⊓ CB' ≤ (⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer ((X i : Subgroup G) : Set G) :=
    fun w hw => ⟨hw.1.1, burnsideB610_mem_centralizer_of_autI_le hXV hBV hB'V hgen (hVi hw.1.1)
      hw.1.2 hw.2.2⟩
  have r4 := rk_cent_add hF (D i)
  have hc : ∀ a ∈ CBi, ∀ b ∈ CB', a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hVi ha.1) hb.1
  have r5 := B2F.rk_sup_add_rk_inf_of_commute hc
  have r6 := rk_mono r3
  have hVeq : CBi ⊔ CB' = V :=
    B2F.eq_of_le_of_rk_le_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
      (sup_le (inf_le_left.trans hVi) inf_le_left) (by omega)
  rintro v ⟨hvV, hvJ⟩
  have hv : v ∈ ((CBi ⊔ CB' : Subgroup G) : Set G) := by rw [hVeq]; exact hvV
  have hCN : CBi ≤ Subgroup.normalizer ((CB' : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hv
  obtain ⟨u, hu, c, hcc, rfl⟩ := hv
  have huJ := hFam.le_centralizer_thompsonJ hHV Bf hBc hJ hi hu
  have hcJ : c ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
    have : c = u⁻¹ * (u * c) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huJ) hvJ
  have hcB : c ∈ Subgroup.centralizer (Bf i : Set G) := Subgroup.centralizer_le hBJ hcJ
  have hcX := burnsideB610_mem_centralizer_of_autI_le hXV hBV hB'V hgen hcc.1 hcB hcc.2
  exact Subgroup.mul_mem_sup ⟨hu.1, huJ⟩ ⟨⟨hcc.1, hcJ⟩, hcX⟩

end burnsideB610_Fam

end CFSG.Quasithin.B610T
