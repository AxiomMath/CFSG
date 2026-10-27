module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.StarB
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.StarS4
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.StarPerfect

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

private theorem perm5_even_order : ∀ y : Perm (Fin 5), Perm.sign y = 1 →
    y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 5 = 1 := by
  decide +kernel

theorem perm5_sq_of_even_two_pow {y : Perm (Fin 5)} (hs : Perm.sign y = 1) {m : ℕ}
    (hm : y ^ 2 ^ m = 1) : y * y = 1 := by
  rcases perm5_even_order y hs with h | h | h
  · rw [← pow_two]; exact h
  · have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hc : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have : orderOf y ∣ 1 := hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
    rw [Nat.dvd_one, orderOf_eq_one_iff] at this
    rw [this, mul_one]
  · have h1 : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hc : Nat.Coprime 5 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have : orderOf y ∣ 1 := hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
    rw [Nat.dvd_one, orderOf_eq_one_iff] at this
    rw [this, mul_one]

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem sq_mem_Qv_of_decomp {δ l : Geo H M} (hδ : vtype δ = false) {a q s : G}
    (haL : a ∈ oTwoRes (stab δ)) (hq : q ∈ Qv δ) (hs : s ∈ Qv l) (hs' : s ∈ stab δ)
    (hdec : q = a * s) : a * a ∈ Qv δ := by
  obtain ⟨-, θ, -, -, hθk, -⟩ := C.exists_secData hδ
  obtain ⟨has, hA5⟩ := psi_mem_alt_of_mem_oTwoRes θ haL
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup (r := 2) (stab l)) ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hqst : q ∈ stab δ := pCoreOf_le 2 (stab δ) hq
  have hθq : θ ⟨q, hqst⟩ = 1 := by
    have : (⟨q, hqst⟩ : ↥(stab δ)) ∈ θ.ker := by
      rw [hθk, Subgroup.mem_subgroupOf]; exact hq
    exact this
  have hae : (⟨a, has⟩ : ↥(stab δ)) = ⟨q, hqst⟩ * (⟨s, hs'⟩ : ↥(stab δ))⁻¹ := by
    apply Subtype.ext
    simp [hdec]
  have hy : θ ⟨a, has⟩ = (θ ⟨s, hs'⟩)⁻¹ := by
    rw [hae, map_mul, map_inv, hθq, one_mul]
  have hy2 : (θ ⟨a, has⟩) ^ 2 ^ m = 1 := by
    rw [hy, inv_pow, ← map_pow]
    have : (⟨s, hs'⟩ : ↥(stab δ)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hsm)
    rw [this, map_one, inv_one]
  have hsign : Perm.sign (θ ⟨a, has⟩) = 1 := Equiv.Perm.mem_alternatingGroup.mp hA5
  have hsq := perm5_sq_of_even_two_pow hsign hy2
  have : (⟨a, has⟩ * ⟨a, has⟩ : ↥(stab δ)) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul]; exact hsq
  rw [hθk, Subgroup.mem_subgroupOf] at this
  exact this

theorem comm_Vn_zpowers_le_centralizer {δ : Geo H M} {a : G} (ha : a ∈ stab δ)
    (hV : IsElemAbelian 2 (Vn δ)) (hsq : ∀ v ∈ Vn δ, (a * a) * v = v * (a * a)) :
    ⁅Vn δ, Subgroup.zpowers a⁆ ≤ Subgroup.centralizer ({a} : Set G) := by
  have hVc := fun {x y : G} (hx : x ∈ Vn δ) (hy : y ∈ Vn δ) =>
    (CFSG.Quasithin.isMulCommutative_subgroup_iff.mp hV.1) x hx y hy
  have hV2 : ∀ x ∈ Vn δ, x * x = 1 := fun x hx => by
    have := hV.2 x hx
    rwa [pow_two] at this
  have haN : a ∈ Subgroup.normalizer (Vn δ : Set G) := stab_le_normalizer_Vn δ ha
  have hconj : ∀ v ∈ Vn δ, a * v * a⁻¹ ∈ Vn δ := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp haN v).mp hv
  have hcase : ∀ v ∈ Vn δ, ∀ g ∈ Subgroup.zpowers a, g * v * g⁻¹ = v ∨ g * v * g⁻¹ = a * v * a⁻¹ := by
    intro v hv g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      have hg2 : a ^ (2 * m) = (a * a) ^ m := by rw [zpow_mul, zpow_two]
      have hc : Commute (a * a) v := hsq v hv
      rw [hg2]
      have hc' : Commute ((a * a) ^ m) v := hc.zpow_left m
      rw [hc'.eq]
      group
    · right
      have hg2 : a ^ (2 * m + 1) = (a * a) ^ m * a := by
        rw [zpow_add, zpow_mul, zpow_two, zpow_one]
      have hc : Commute (a * a) (a * v * a⁻¹) := by
        have : a * v * a⁻¹ ∈ Vn δ := hconj v hv
        exact hsq _ this
      have hc' : Commute ((a * a) ^ m) (a * v * a⁻¹) := hc.zpow_left m
      rw [hg2]
      calc (a * a) ^ m * a * v * ((a * a) ^ m * a)⁻¹
          = (a * a) ^ m * (a * v * a⁻¹) * ((a * a) ^ m)⁻¹ := by group
        _ = a * v * a⁻¹ := by rw [hc'.eq]; group
  rw [Subgroup.commutator_le]
  intro v hv g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hu : a * v * a⁻¹ ∈ Vn δ := hconj v hv
  have e : ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]; group
  have hinv : ∀ x ∈ Vn δ, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hV2 x hx)
  rcases hcase v hv g hg with h | h
  · have h' : g * v⁻¹ * g⁻¹ = v⁻¹ := by
      have := congrArg (fun t => t⁻¹) h
      simpa [mul_assoc] using this
    rw [e, h', mul_inv_cancel, one_mul, mul_one]
  · have h' : g * v⁻¹ * g⁻¹ = (a * v * a⁻¹)⁻¹ := by
      rw [← h]; group
    rw [e, h', hinv _ hu]
    have hau : a * (a * v * a⁻¹) * a⁻¹ = v := by
      have h1 := hsq v hv
      calc a * (a * v * a⁻¹) * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
        _ = v := by rw [h1]; group
    have hk : a * (v * (a * v * a⁻¹)) * a⁻¹ = v * (a * v * a⁻¹) := by
      calc a * (v * (a * v * a⁻¹)) * a⁻¹ = (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) := by group
        _ = (a * v * a⁻¹) * v := by rw [hau]
        _ = v * (a * v * a⁻¹) := (hVc hu hv)
    have := mul_inv_eq_iff_eq_mul.mp hk
    exact this.symm

theorem star_of_inter {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ)
    (hS4 : oTwoRes (stab δ) ⊓ Qv δ ≤ Qv l) (hQL : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l) : False := by
  have hb2 : 2 ≤ bMin H M := C.hb1
  have hvl := vtype_true_of_mem_nbrs_false hl hδ
  have hδl : δ ∈ nbrs l := mem_nbrs_comm hl
  have hLs : oTwoRes (stab δ) ≤ stab δ := oTwoRes_le _
  have hQδs : Qv δ ≤ stab δ ⊓ stab l := Qv_le_inf C.hA hl
  have hQls : Qv l ≤ stab l ⊓ stab δ := Qv_le_inf C.hA hδl
  have hQl_stδ : Qv l ≤ stab δ := fun x hx => (hQls hx).2
  obtain ⟨q₀, hq₀Q, hq₀l⟩ := Set.not_subset.mp (C.not_Qv_le_Qv hvl hδl)
  have hcen := centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hvl)
  obtain ⟨z, hzZ, hzne⟩ : ∃ z ∈ Zv l, z * q₀ ≠ q₀ * z := by
    by_contra h
    push Not at h
    apply hq₀l
    rw [← hcen]
    exact ⟨(hQδs hq₀Q).2, Subgroup.mem_centralizer_iff.mpr fun z hz => h z hz⟩
  have hLn : stab δ ≤ Subgroup.normalizer ((oTwoRes (stab δ) : Subgroup G) : Set G) :=
    le_normalizer_oTwoRes _
  have h28 := C.h28 C.hb1 l δ hδl (C.bAt_eq_of_true hvl)
  have hcov : (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ = stab δ := by
    refine le_antisymm (sup_le (sup_le hLs hQl_stδ) ((pCoreOf_le 2 (stab δ)))) fun g hg => ?_
    obtain ⟨x, hxL, hxl⟩ := C.exists_oTwoRes_smul hl (smul_mem_nbrs_stab (g := ⟨g, stab_le δ hg⟩)
      (ν := δ) hg hl)
    have hxs : (x : G) ∈ stab δ := hLs hxL
    have hfix : (x⁻¹ * (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M))) • l = l := by
      rw [mul_smul, ← hxl, inv_smul_smul]
    have hy1 : (x : G)⁻¹ * g ∈ stab l := by
      have := mem_stab_of_smul_eq hfix
      simpa using this
    have hy2 : (x : G)⁻¹ * g ∈ stab δ := (stab δ).mul_mem ((stab δ).inv_mem hxs) hg
    have hy : (x : G)⁻¹ * g ∈ Qv l ⊔ Qv δ := by rw [h28]; exact ⟨hy1, hy2⟩
    have e : g = (x : G) * ((x : G)⁻¹ * g) := by group
    rw [e]
    have hx' : (x : G) ∈ (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hxL)
    have hsub : Qv l ⊔ Qv δ ≤ (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ :=
      sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have hy' : (x : G)⁻¹ * g ∈ (oTwoRes (stab δ) ⊔ Qv l) ⊔ Qv δ := hsub hy
    exact Subgroup.mul_mem _ hx' hy'
  have hU : oTwoRes (stab δ) ⊔ Qv l = stab δ :=
    C.eq_stab_of_cover hδ hl (sup_le hLs hQl_stδ) le_sup_right hcov
  obtain ⟨a, haL, s, hsQ, hq₀as⟩ := mem_sup_of_le_normalizer (N := oTwoRes (stab δ))
    (K := Qv l) (fun x hx => hLn (hQl_stδ hx)) (hU ▸ ((hQδs hq₀Q).1))
  have hs_st : s ∈ stab l ⊓ stab δ := hQls hsQ
  have ha_eq : a = q₀ * s⁻¹ := by rw [hq₀as]; group
  have ha_st : a ∈ stab δ := hLs haL
  have ha_stl : a ∈ stab l := by
    rw [ha_eq]
    exact (stab l).mul_mem (hQδs hq₀Q).2 ((stab l).inv_mem hs_st.1)
  have haQ : a ∉ Qv δ := by
    intro haQ
    exact hq₀l (by rw [hq₀as]; exact (Qv l).mul_mem (hS4 ⟨haL, haQ⟩) hsQ)
  have haa : a * a ∈ Qv δ := C.sq_mem_Qv_of_decomp hδ haL hq₀Q hsQ hs_st.2 hq₀as
  have hN2 := C.relIndex_Qv_inf_Qv hδ hl
  have hnorm := C.star_normal hl hQL
  have hq₀N : q₀ ∉ Qv δ ⊓ Qv l := fun h => hq₀l h.2
  have hsδ : s ∈ stab δ := hs_st.2
  have hq₀' : s⁻¹ * q₀ * s ∈ Qv δ := by
    have h : s⁻¹ * q₀ * s⁻¹⁻¹ ∈ Qv δ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) ((stab δ).inv_mem hsδ))
        q₀).mp hq₀Q
    rwa [inv_inv] at h
  have hq₀'N : s⁻¹ * q₀ * s ∉ Qv δ ⊓ Qv l := by
    intro h
    have := hnorm s hsδ _ h
    apply hq₀N
    simpa [mul_assoc] using this
  have hn1 : q₀⁻¹ * (s⁻¹ * q₀ * s) ∈ Qv δ ⊓ Qv l :=
    inv_mul_mem_of_relIndex_two hN2 hq₀Q hq₀' hq₀N hq₀'N
  have hn2 : q₀ * q₀ ∈ Qv δ ⊓ Qv l := by
    have := inv_mul_mem_of_relIndex_two hN2 ((Qv δ).inv_mem hq₀Q) hq₀Q
      (fun h => hq₀N (by simpa using (Qv δ ⊓ Qv l).inv_mem h)) hq₀N
    simpa using this
  have haaN : a * a ∈ Qv l := by
    have e : a * a = (q₀ * q₀) * (q₀⁻¹ * (s⁻¹ * q₀ * s)) * s⁻¹ * s⁻¹ := by
      rw [ha_eq]; group
    rw [e]
    exact (Qv l).mul_mem ((Qv l).mul_mem ((Qv l).mul_mem hn2.2 hn1.2) ((Qv l).inv_mem hsQ))
      ((Qv l).inv_mem hsQ)
  have hZδl : Zv δ ≤ Zv l := C.Zv_le_Zv_of_mem_nbrs hvl hδl
  have hrelZ : (Zv δ).relIndex (Zv l) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Zv δ) (K := Zv l)
    rw [inf_of_le_left hZδl, C.card_Zv_false hδ, C.card_Zv_true hvl] at h
    omega
  have hZc : ∀ c ∈ Zv δ, ∀ g ∈ stab δ, g * c = c * g := fun c hc g hg =>
    Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hδ hc).2 g hg
  have hzQ : z ∈ Qv δ := Zv_le_Qv_of_mem_nbrs hδl hb2 hzZ
  have hz_st : z ∈ stab δ := (hQδs hzQ).1
  have hzZδ : z ∉ Zv δ := fun h => hzne (hZc z h q₀ (hQδs hq₀Q).1).symm
  have hgz : ∀ g ∈ stab δ ⊓ stab l, g * z * g⁻¹ * z⁻¹ ∈ Zv δ := by
    intro g hg
    have hgzl : g * z * g⁻¹ ∈ Zv l :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA l hg.2) z).mp hzZ
    have hgzn : g * z * g⁻¹ ∉ Zv δ := by
      intro hc
      apply hzZδ
      have h1 := hZc _ hc g hg.1
      have h2 : g⁻¹ * (g * z * g⁻¹) * g = g * z * g⁻¹ := by
        calc g⁻¹ * (g * z * g⁻¹) * g = g⁻¹ * ((g * z * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * z * g⁻¹)) := by rw [h1]
          _ = g * z * g⁻¹ := by group
      have h3 : z = g * z * g⁻¹ := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = g * z * g⁻¹ := h2
      rw [h3]; exact hc
    have hmul := inv_mul_mem_of_relIndex_two hrelZ hzZ hgzl hzZδ hgzn
    have h4 := hZc _ hmul z hz_st
    have e : g * z * g⁻¹ * z⁻¹ = z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ := by group
    have hfin : z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = z⁻¹ * (g * z * g⁻¹) := by
      calc z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = ((z⁻¹ * (g * z * g⁻¹)) * z) * z⁻¹ := by rw [h4]
        _ = z⁻¹ * (g * z * g⁻¹) := by group
    rw [e, hfin]
    exact hmul
  have hzfix : z ∈ fixSecIn (Subgroup.zpowers a) (F53B3.Cv δ) (Vn δ) := by
    refine Subgroup.subset_closure ⟨Zv_le_Vn_of_mem_nbrs hl hzZ, fun a' ha' => ?_⟩
    have hmem : a' ∈ stab δ ⊓ stab l := (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨ha_st, ha_stl⟩)) ha'
    exact C.Zv_le_Cv hδ (hgz a' hmem)
  rw [C.fixSecIn_eq_commSec hδ ha_st haQ haa] at hzfix
  have hVA : ⁅Vn δ, Subgroup.zpowers a⁆ ≤ Vn δ := by
    rw [Subgroup.commutator_le]
    intro v hv g hg
    have hgst : g ∈ stab δ := (Subgroup.zpowers_le.mpr ha_st) hg
    have h1 : g * v⁻¹ * g⁻¹ ∈ Vn δ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hgst) v⁻¹).mp ((Vn δ).inv_mem hv)
    have e : ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Vn δ).mul_mem hv h1
  have hVAN : ⁅Vn δ, Subgroup.zpowers a⁆ ≤ Subgroup.normalizer ((F53B3.Cv δ : Subgroup G) : Set G) :=
    fun x hx => stab_le_normalizer_Cv' δ ((Qv_le_inf C.hA hl ((C.Vn_le_Qv_self hδ) (hVA hx))).1)
  have hzfix' : z ∈ F53B3.Cv δ ⊔ ⁅Vn δ, Subgroup.zpowers a⁆ := by
    have : commSec (Subgroup.zpowers a) (F53B3.Cv δ) (Vn δ) =
        F53B3.Cv δ ⊔ ⁅Vn δ, Subgroup.zpowers a⁆ := by
      unfold commSec; exact sup_comm _ _
    rwa [this] at hzfix
  obtain ⟨c, hcC, w, hwK, hcw⟩ := mem_sup_of_le_normalizer hVAN hzfix'
  have hac : a * c = c * a := Subgroup.mem_centralizer_iff.mp hcC.2 a haL
  have hsqV : ∀ v ∈ Vn δ, (a * a) * v = v * (a * a) :=
    C.star_centralizes hδ hl hQL (a * a) ⟨haa, haaN⟩
  have hwa : w * a = a * w :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (C.comm_Vn_zpowers_le_centralizer ha_st (isElemAbelian_Vn C.hA C.hb3 δ) hsqV hwK))
  have haz : a * z = z * a := by
    rw [hcw]
    calc a * (c * w) = (a * c) * w := by group
      _ = (c * a) * w := by rw [hac]
      _ = c * (a * w) := by group
      _ = c * (w * a) := by rw [hwa]
      _ = c * w * a := by group
  have hsz : s * z = z * s := by
    have := C.Qv_centralizes_Zv hvl hsQ hzZ
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  apply hzne
  calc z * q₀ = z * (a * s) := by rw [hq₀as]
    _ = (z * a) * s := by group
    _ = (a * z) * s := by rw [haz]
    _ = a * (z * s) := by group
    _ = a * (s * z) := by rw [hsz]
    _ = (a * s) * z := by group
    _ = q₀ * z := by rw [hq₀as]

theorem star {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    ¬ ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l := by
  intro hQL
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData hδ
  have hperf : ⁅oTwoRes (stab δ), oTwoRes (stab δ)⁆ = oTwoRes (stab δ) :=
    oTwoRes_perfect hθs hθk
  exact C.star_of_inter hδ hl (C.inter_le_of_perfect hδ hl hperf hQL) hQL

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
