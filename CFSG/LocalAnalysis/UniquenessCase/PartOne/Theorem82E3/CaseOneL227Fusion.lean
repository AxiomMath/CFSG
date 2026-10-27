module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227
import CFSG.GroupTheory.IndexThreeCosets
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.CentralizerMap
import CFSG.GroupTheory.TransvectionInversion
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
import CFSG.HardMathSupport.Lang.TwE6Step3.Glue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811L227

variable {c : Ctx82E3 D}

abbrev S (h : Case811L227 c) : Subgroup G := h.P ⊓ c.L

variable (h : Case811L227 c)

theorem S_le_P : h.S ≤ h.P := inf_le_left

theorem S_le_L : h.S ≤ c.L := inf_le_right

theorem S_le_M : h.S ≤ D.M := h.S_le_P.trans h.sylow.le

theorem P_le_M : h.P ≤ D.M := h.sylow.le

theorem P_le_normalizer_L : h.P ≤ Subgroup.normalizer (c.L : Set G) :=
  h.P_le_M.trans c.le_normalizer_L

theorem z_mem : h.z ∈ h.P ⊓ c.L := by
  have hzy := h.inf_centralizer_eq h.y h.y_mem h.y_not_mem_L h.orderOf_y
  have hle : Subgroup.zpowers h.z ≤ h.S := by
    rw [← hzy]
    exact inf_le_left
  exact hle (Subgroup.mem_zpowers h.z)

theorem z_mem_center : h.z ∈ h.P ⊓ Subgroup.centralizer (h.P : Set G) := by
  rw [h.center_eq]
  exact Subgroup.mem_zpowers h.z

theorem z_central : h.z ∈ Subgroup.centralizer (h.P : Set G) := h.z_mem_center.2

theorem z_ne_one : h.z ≠ 1 := by
  intro hz
  have h1 : orderOf h.z = 1 := by rw [hz]; exact orderOf_one
  rw [h.orderOf_z] at h1
  norm_num at h1

theorem zpowers_z_le_S : Subgroup.zpowers h.z ≤ h.S :=
  Subgroup.zpowers_le.mpr h.z_mem

theorem zpowers_z_ne_bot : Subgroup.zpowers h.z ≠ ⊥ := fun hbot =>
  h.z_ne_one ((Subgroup.zpowers_eq_bot).mp hbot)

theorem y_pow_three : h.y ^ 3 = 1 := by
  rw [← h.orderOf_y]
  exact pow_orderOf_eq_one h.y

theorem y_ne_one : h.y ≠ 1 := by
  intro hy
  have h1 : orderOf h.y = 1 := by rw [hy]; exact orderOf_one
  rw [h.orderOf_y] at h1
  norm_num at h1

theorem y_not_mem_S : h.y ∉ h.S := fun hy => h.y_not_mem_L hy.2

theorem y_inv_mem_P : h.y⁻¹ ∈ h.P := h.P.inv_mem h.y_mem

theorem y_inv_not_mem_L : h.y⁻¹ ∉ c.L := fun hy =>
  h.y_not_mem_L (by simpa using c.L.inv_mem hy)

theorem orderOf_y_inv : orderOf h.y⁻¹ = 3 := by
  rw [orderOf_inv, h.orderOf_y]

theorem S_comm {a b : G} (ha : a ∈ h.S) (hb : b ∈ h.S) : a * b = b * a :=
  h.elemAbelian_S.comm ha hb

theorem S_pow_three {a : G} (ha : a ∈ h.S) : a ^ 3 = 1 :=
  h.elemAbelian_S.2 a ha

theorem S_isPGroup : IsPGroup 3 h.S := h.elemAbelian_S.isPGroup

theorem P_le_normalizer_S : h.P ≤ Subgroup.normalizer (h.S : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hPmap : Subgroup.map (MulAut.conj p).toMonoidHom h.P = h.P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hp)
  have hLmap : Subgroup.map (MulAut.conj p).toMonoidHom c.L = c.L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.P_le_normalizer_L hp)
  calc Subgroup.map (MulAut.conj p).toMonoidHom (h.P ⊓ c.L)
      = Subgroup.map (MulAut.conj p).toMonoidHom h.P ⊓
          Subgroup.map (MulAut.conj p).toMonoidHom c.L :=
        Subgroup.map_inf _ _ _ (MulAut.conj p).injective
    _ = h.P ⊓ c.L := by rw [hPmap, hLmap]

theorem S_normal_in_P : (h.S.subgroupOf h.P).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.S_le_P).mpr h.P_le_normalizer_S

theorem relIndex_S : h.S.relIndex h.P = 3 := by
  have hmul := Subgroup.relIndex_mul_card h.S h.P
  rw [inf_of_le_left h.S_le_P, h.card_S, h.card_P] at hmul
  omega

theorem S_ne_bot : h.S ≠ ⊥ := by
  rw [← Subgroup.one_lt_card_iff_ne_bot, h.card_S]
  norm_num

theorem false_of_z_eq_conj_mul (g m : G) (hm : m ∈ D.M) {s t : G}
    (hs : s ∈ h.S) (hy : h.y = g * s * g⁻¹) (ht : t ∈ h.S)
    (hz : h.z = (g * m) * t * (g * m)⁻¹) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let k : G := g * m
  let S' : Subgroup G := Subgroup.map (MulAut.conj k).toMonoidHom h.S
  have hzS' : h.z ∈ S' := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom ht
    have hmem' : (MulAut.conj k) t ∈ S' := hmem
    rw [MulAut.conj_apply] at hmem'
    rwa [← hz] at hmem'
  have hS'_ab : CFSG.Open.IsElemAbelian 3 S' :=
    h.elemAbelian_S.map (MulAut.conj k).toMonoidHom
  have hS'_card : Nat.card S' = 27 := by
    dsimp only [S']
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, h.card_S]
  have hS'_leCz : S' ≤ Subgroup.centralizer (Subgroup.zpowers h.z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : x * h.z = h.z * x := hS'_ab.comm hx hzS'
    exact (Commute.zpow_right hxz n).eq.symm
  have hS'_leM : S' ≤ D.M :=
    (hS'_leCz.trans (Subgroup.centralizer_le_normalizer _)).trans
      (h.normalizer_le (Subgroup.zpowers h.z) h.zpowers_z_le_S h.zpowers_z_ne_bot)
  have hS'_pg : IsPGroup 3 S' := hS'_ab.isPGroup
  obtain ⟨T, hS'T, hT⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hS'_pg hS'_leM
  obtain ⟨m', hm'M, hm'conj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj h.sylow hT
  let E : Subgroup G := Subgroup.map (MulAut.conj m'⁻¹).toMonoidHom S'
  have hE_le_P : E ≤ h.P := by
    intro x hx
    rw [Subgroup.mem_map_equiv] at hx
    have hx' : (MulAut.conj m') x ∈ S' := by
      simpa [MulAut.conj_symm_apply] using hx
    have hxT : (MulAut.conj m') x ∈ T := hS'T hx'
    have hmem := (hm'conj ((MulAut.conj m') x)).mp hxT
    rw [MulAut.conj_apply] at hmem
    rwa [show m'⁻¹ * (m' * x * m'⁻¹) * m' = x by group] at hmem
  have hE_ab : CFSG.Open.IsElemAbelian 3 E :=
    hS'_ab.map (MulAut.conj m'⁻¹).toMonoidHom
  have hE_card : Nat.card E = 27 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective (MulAut.conj m'⁻¹).injective, hS'_card]
  have hE_eq : E = h.S := h.unique E hE_le_P hE_ab hE_card
  let n : G := m'⁻¹ * g * m
  have hcomp : (MulAut.conj m'⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj n).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    dsimp [k, n]
    group
  have hS'map : Subgroup.map (MulAut.conj n).toMonoidHom h.S = h.S := by
    calc Subgroup.map (MulAut.conj n).toMonoidHom h.S
        = Subgroup.map ((MulAut.conj m'⁻¹).toMonoidHom.comp
            (MulAut.conj k).toMonoidHom) h.S := by rw [hcomp]
      _ = Subgroup.map (MulAut.conj m'⁻¹).toMonoidHom
            (Subgroup.map (MulAut.conj k).toMonoidHom h.S) := by rw [Subgroup.map_map]
      _ = E := rfl
      _ = h.S := hE_eq
  have hnN : n ∈ Subgroup.normalizer (h.S : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hS'map
  have hnM : n ∈ D.M := h.normalizer_le h.S le_rfl h.S_ne_bot hnN
  have hgM : g ∈ D.M := by
    have hgn : g = m' * n * m⁻¹ := by dsimp [n]; group
    rw [hgn]
    exact D.M.mul_mem (D.M.mul_mem hm'M hnM) (D.M.inv_mem hm)
  have hyL : h.y ∈ c.L := by
    rw [hy]
    exact (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hgM) s).mp (h.S_le_L hs)
  exact h.y_not_mem_L hyL

theorem mem_or_mem_or_mem {x : G} (hx : x ∈ h.P) :
    x ∈ h.P ⊓ c.L ∨ h.y⁻¹ * x ∈ h.P ⊓ c.L ∨ h.y * x ∈ h.P ⊓ c.L :=
  CFSG.GroupTheory.mem_or_inv_mul_mem_or_mul_mem_of_relIndex_eq_three
    h.S_normal_in_P h.relIndex_S h.y_mem h.y_not_mem_S hx

abbrev E (h : Case811L227 c) : Subgroup G :=
  Subgroup.closure ({h.y, h.z} : Set G)

theorem y_mem_E : h.y ∈ h.E := Subgroup.subset_closure (by simp)

theorem z_mem_E : h.z ∈ h.E := Subgroup.subset_closure (by simp)

theorem E_isElemAbelian : CFSG.Open.IsElemAbelian 3 h.E := by
  apply CFSG.Open.IsElemAbelian.closure_of_commute
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have hzy : h.y * h.z = h.z * h.y :=
      Subgroup.mem_centralizer_iff.mp h.z_central h.y h.y_mem
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hzy
    · exact hzy.symm
    · rfl
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact h.y_pow_three
    · rw [← h.orderOf_z]
      exact pow_orderOf_eq_one h.z

theorem E_isPGroup : IsPGroup 3 h.E := h.E_isElemAbelian.isPGroup

theorem E_le_centralizer_y : h.E ≤ Subgroup.centralizer ({h.y} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h.E_isElemAbelian.comm hx h.y_mem_E

theorem E_le_centralizer_z : h.E ≤ Subgroup.centralizer ({h.z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h.E_isElemAbelian.comm hx h.z_mem_E

theorem zpowers_z_le_E : Subgroup.zpowers h.z ≤ h.E :=
  Subgroup.zpowers_le.mpr h.z_mem_E

theorem zpowers_z_lt_E : Subgroup.zpowers h.z < h.E := by
  refine lt_of_le_of_ne h.zpowers_z_le_E ?_
  intro heq
  have hy : h.y ∈ Subgroup.zpowers h.z := heq ▸ h.y_mem_E
  exact h.y_not_mem_S (h.zpowers_z_le_S hy)

theorem E_card : Nat.card h.E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hle : Nat.card h.E ≤ 9 := by
    have := CFSG.HardMathSupport.Lang.TwE6Step3.card_closure_pair_le_sq
      (show h.y * h.z = h.z * h.y from
        Subgroup.mem_centralizer_iff.mp h.z_central h.y h.y_mem)
      h.y_pow_three (by rw [← h.orderOf_z]; exact pow_orderOf_eq_one h.z)
    simpa [E, pow_two] using this
  have hgt : 3 < Nat.card h.E := by
    have hlt := Subgroup.card_lt_of_lt h.zpowers_z_lt_E
    rwa [Nat.card_zpowers, h.orderOf_z] at hlt
  obtain ⟨n, hn⟩ := h.E_isPGroup.exists_card_eq
  have hn2 : n = 2 := by
    have h1 : 3 ^ 1 < 3 ^ n := by
      rw [← hn]
      simpa using hgt
    have h2 : 3 ^ n ≤ 3 ^ 2 := by
      rw [← hn]
      simpa using hle
    rw [Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)] at h1
    have hnle : n ≤ 2 := by
      by_contra h
      have h2' : 3 ≤ n := by omega
      have hle' : 3 ^ 2 < 3 ^ n := by
        rw [Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)]
        omega
      omega
    omega
  rw [hn, hn2]
  norm_num

theorem relIndex_zpowers_E : (Subgroup.zpowers h.z).relIndex h.E = 3 := by
  have hmul := Subgroup.relIndex_mul_card (Subgroup.zpowers h.z) h.E
  rw [inf_of_le_left h.zpowers_z_le_E, Nat.card_zpowers, h.orderOf_z, h.E_card] at hmul
  omega

theorem false_of_centralizing_z {u : G}
    (huC : u ∈ Subgroup.centralizer ({h.y} : Set G))
    (huN : u ∈ Subgroup.normalizer (h.E : Set G))
    (huE : u ∉ h.E) (hu3 : ∃ k, orderOf u = 3 ^ k)
    (huz : u * h.z = h.z * u) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let F : Subgroup G := h.E ⊔ Subgroup.zpowers u
  have hE_le_F : h.E ≤ F := le_sup_left
  have hu_zp_F : Subgroup.zpowers u ≤ F := le_sup_right
  have huF : u ∈ F := hu_zp_F (Subgroup.mem_zpowers u)
  have hF_ne_E : h.E ≠ F := by
    intro hFE
    exact huE (hFE ▸ huF)
  have hlt : h.E < F := lt_of_le_of_ne hE_le_F hF_ne_E
  have hF_pg : IsPGroup 3 F := by
    dsimp only [F]
    refine IsPGroup.to_sup_of_normal_left' h.E_isPGroup ?_ ?_
    · obtain ⟨k, hk⟩ := hu3
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    · exact Subgroup.zpowers_le.mpr huN
  have hF_ge : 27 ≤ Nat.card F := by
    have hgt : 9 < Nat.card F := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [h.E_card] at this
    obtain ⟨n, hn⟩ := hF_pg.exists_card_eq
    have hn3 : 3 ≤ n := by
      by_contra hlt'
      have hnle : n ≤ 2 := by omega
      have hle : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hnle
      rw [hn] at hgt
      norm_num at hle
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hn3
  have hF_le_Cy : F ≤ Subgroup.centralizer ({h.y} : Set G) := by
    refine sup_le h.E_le_centralizer_y ?_
    rw [Subgroup.zpowers_le]
    exact huC
  have hF_le_Cz : F ≤ Subgroup.centralizer (Subgroup.zpowers h.z : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxz : x * h.z = h.z * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer_z hx)
      exact (Commute.zpow_right hxz k).eq.symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute h.z u from huz.symm) k).eq
  have hF_le_M : F ≤ D.M :=
    (hF_le_Cz.trans (Subgroup.centralizer_le_normalizer _)).trans
      (h.normalizer_le (Subgroup.zpowers h.z) h.zpowers_z_le_S h.zpowers_z_ne_bot)
  let CMz : Subgroup G :=
    D.M ⊓ Subgroup.centralizer (Subgroup.zpowers h.z : Set G)
  have hF_le_CMz : F ≤ CMz := by
    intro x hx
    exact ⟨hF_le_M hx, hF_le_Cz hx⟩
  have hP_le_CMz : h.P ≤ CMz := by
    intro p hp
    refine ⟨h.P_le_M hp, ?_⟩
    change p ∈ Subgroup.centralizer (Subgroup.zpowers h.z : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp h.z_central p hp) k).eq.symm
  have hP_sylow : CFSG.ABGLocalTools.IsSylowOf 3 h.P CMz :=
    h.sylow.of_le hP_le_CMz inf_le_left
  obtain ⟨T', hF_T', hT'⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hF_pg hF_le_CMz
  obtain ⟨m, hmCMz, hmconj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hP_sylow hT'
  have hmF_le_P : Subgroup.map (MulAut.conj m⁻¹).toMonoidHom F ≤ h.P := by
    intro x hx
    rw [Subgroup.mem_map_equiv] at hx
    have hx' : (MulAut.conj m) x ∈ F := by
      simpa [MulAut.conj_symm_apply] using hx
    have hxT' : (MulAut.conj m) x ∈ T' := hF_T' hx'
    have hmem := (hmconj ((MulAut.conj m) x)).mp hxT'
    rw [MulAut.conj_apply] at hmem
    rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at hmem
  let my : G := m⁻¹ * h.y * m
  have hmF_le_Cmy : Subgroup.map (MulAut.conj m⁻¹).toMonoidHom F ≤
      Subgroup.centralizer ({my} : Set G) := by
    intro x hx
    rw [Subgroup.mem_map_equiv] at hx
    have hx' : (MulAut.conj m) x ∈ F := by
      simpa [MulAut.conj_symm_apply] using hx
    have hcomm : (MulAut.conj m) x * h.y = h.y * (MulAut.conj m) x :=
      ((Subgroup.mem_centralizer_iff.mp (hF_le_Cy hx')) h.y (by simp)).symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    change x * my = my * x
    dsimp only [my]
    calc x * (m⁻¹ * h.y * m) = m⁻¹ * ((MulAut.conj m) x * h.y) * m := by
          rw [MulAut.conj_apply]; group
      _ = m⁻¹ * (h.y * (MulAut.conj m) x) * m := by rw [hcomm]
      _ = (m⁻¹ * h.y * m) * x := by rw [MulAut.conj_apply]; group
  have hmF_le_inf : Subgroup.map (MulAut.conj m⁻¹).toMonoidHom F ≤
      h.P ⊓ Subgroup.centralizer ({my} : Set G) :=
    le_inf hmF_le_P hmF_le_Cmy
  have hmy_eq : my = MulAut.conj m⁻¹ h.y := by
    rw [MulAut.conj_apply, inv_inv]
  have hmyP : my ∈ h.P := by
    apply hmF_le_P
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj m⁻¹).toMonoidHom
      (hE_le_F h.y_mem_E)
    rwa [hmy_eq]
  have hmyL : my ∉ c.L := by
    intro hL
    have hmM : m ∈ D.M := hmCMz.1
    have hyL : h.y ∈ c.L := by
      have hmy_eq : my = m⁻¹ * h.y * m := rfl
      rw [hmy_eq] at hL
      have := (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hmM)
        (m⁻¹ * h.y * m)).mp hL
      rwa [show m * (m⁻¹ * h.y * m) * m⁻¹ = h.y by group] at this
    exact h.y_not_mem_L hyL
  have hmy_ord : orderOf my = 3 := by
    have hconj : my = MulAut.conj m⁻¹ h.y := hmy_eq
    calc orderOf my = orderOf ((MulAut.conj m⁻¹) h.y) := by rw [hconj]
      _ = orderOf h.y := by
          simpa using orderOf_injective (MulAut.conj m⁻¹).toMonoidHom
            (MulAut.conj m⁻¹).injective h.y
      _ = 3 := h.orderOf_y
  have hcard_inf :
      Nat.card (h.P ⊓ Subgroup.centralizer ({my} : Set G) : Subgroup G) = 9 :=
    h.card_inf_centralizer my hmyP hmyL hmy_ord
  have hF_le_9 : Nat.card F ≤ 9 := by
    have := Subgroup.card_le_of_le hmF_le_inf
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hcard_inf] at this
    exact this
  omega

theorem conj_ne_y (g : G) {s : G} (hs : s ∈ h.P ⊓ c.L) : g * s * g⁻¹ ≠ h.y := by
  classical
  intro hconj
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hs_ne : s ≠ 1 := by
    intro hs1
    have hy1 : h.y = 1 := by rw [← hconj, hs1]; group
    exact h.y_ne_one hy1
  have hs_ord : orderOf s = 3 := orderOf_eq_prime (h.S_pow_three hs) hs_ne
  set w : G := g⁻¹ * h.z * g with hwdef
  have hs_eq : s = g⁻¹ * h.y * g := by rw [← hconj]; group
  have hzy : h.z * h.y = h.y * h.z :=
    (Subgroup.mem_centralizer_iff.mp h.z_central h.y h.y_mem).symm
  have hw_s : w ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * s = g⁻¹ * (h.z * h.y) * g := by rw [hwdef, hs_eq]; group
      _ = g⁻¹ * (h.y * h.z) * g := by rw [hzy]
      _ = s * w := by rw [hs_eq, hwdef]; group
  have hw_zp_cz : w ∈ Subgroup.centralizer (Subgroup.zpowers s : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hws : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp hw_s
    exact (Commute.zpow_right hws k).eq.symm
  have hwN : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Subgroup.centralizer_le_normalizer _ hw_zp_cz
  have hwM : w ∈ D.M :=
    h.normalizer_le (Subgroup.zpowers s) (Subgroup.zpowers_le.mpr hs)
      (fun hbot => hs_ne ((Subgroup.zpowers_eq_bot).mp hbot)) hwN
  have hw_ord : orderOf w = 3 := by
    have hwconj : w = MulAut.conj g⁻¹ h.z := by simp [hwdef, MulAut.conj_apply]
    calc orderOf w = orderOf ((MulAut.conj g⁻¹) h.z) := by rw [hwconj]
      _ = orderOf h.z := by
          simpa using orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective h.z
      _ = 3 := h.orderOf_z
  have hw3 : w ^ 3 = 1 := by
    rw [← hw_ord]
    exact pow_orderOf_eq_one w
  let C : Subgroup G := D.M ⊓ Subgroup.centralizer ({s} : Set G)
  have hwC : w ∈ C := ⟨hwM, hw_s⟩
  have hw_zp : IsPGroup 3 (Subgroup.zpowers (⟨w, hwC⟩ : C)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk w hwC, hw_ord, pow_one]
  obtain ⟨Q, hQle⟩ := hw_zp.exists_le_sylow
  let T : Subgroup G := Subgroup.map C.subtype Q
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 T C := ⟨Q, rfl⟩
  have hwT : w ∈ T := Subgroup.mem_map_of_mem C.subtype (hQle (Subgroup.mem_zpowers _))
  have hS_C : h.S ≤ C := by
    intro x hx
    exact ⟨h.S_le_M hx, Subgroup.mem_centralizer_singleton_iff.mpr (h.S_comm hx hs)⟩
  have hT_ge : 27 ≤ Nat.card T := by
    have := CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_card_le hT h.S_isPGroup hS_C
    rwa [h.card_S] at this
  have hT_le : Nat.card T ≤ 81 := by
    have hTM : T ≤ D.M := hT.le.trans inf_le_left
    have := CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_card_le h.sylow hT.isPGroup hTM
    rwa [h.card_P] at this
  obtain ⟨n, hn⟩ := hT.isPGroup.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hnle : n ≤ 2 := by omega
    have hle : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hnle
    norm_num at hle
    rw [hn] at hT_ge
    omega
  have hn4 : n ≤ 4 := by
    by_contra hgt
    have hnge : 5 ≤ n := by omega
    have hle : 3 ^ 5 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hnge
    norm_num at hle
    rw [hn] at hT_le
    omega
  have hn_cases : n = 3 ∨ n = 4 := by omega
  rcases hn_cases with hn3eq | hn4eq
  ·
    have hTcard : Nat.card T = 27 := by rw [hn, hn3eq]; norm_num
    have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 h.S C := by
      obtain ⟨T', hST', hT'⟩ :=
        CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge h.S_isPGroup hS_C
      have hcardT' : Nat.card T' = Nat.card T := by rw [hT'.card_eq, hT.card_eq]
      have hT'eq : h.S = T' :=
        Subgroup.eq_of_le_of_card_ge hST' (by rw [hcardT', hTcard, h.card_S])
      rwa [← hT'eq] at hT'
    obtain ⟨m, hmC, hmconj⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hS_sylow hT
    have hwmS : m⁻¹ * w * m ∈ h.S := (hmconj w).mp hwT
    have hz_eq : h.z = (g * m) * (m⁻¹ * w * m) * (g * m)⁻¹ := by
      rw [hwdef]; group
    exact h.false_of_z_eq_conj_mul g m hmC.1 hs hconj.symm hwmS hz_eq
  ·
    have hTcard : Nat.card T = 81 := by rw [hn, hn4eq]; norm_num
    have hTM : T ≤ D.M := hT.le.trans inf_le_left
    have hT_M : CFSG.ABGLocalTools.IsSylowOf 3 T D.M := by
      obtain ⟨T', hTT', hT'⟩ :=
        CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hT.isPGroup hTM
      have hcardT' : Nat.card T' = Nat.card T := by
        rw [hT'.card_eq, ← h.sylow.card_eq, h.card_P, hTcard]
      have hT'eq : T = T' := Subgroup.eq_of_le_of_card_ge hTT' (by rw [hcardT'])
      rwa [← hT'eq] at hT'
    obtain ⟨m, hmM, hmconj⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj h.sylow hT_M
    by_cases hCaseA : ∃ t ∈ h.S, w = m * t * m⁻¹
    ·
      obtain ⟨t, ht, hwt⟩ := hCaseA
      have hz_eq : h.z = (g * m) * t * (g * m)⁻¹ := by
        rw [show h.z = g * w * g⁻¹ by rw [hwdef]; group, hwt]
        group
      exact h.false_of_z_eq_conj_mul g m hmM hs hconj.symm ht hz_eq
    ·
      have hsp : IsPGroup 3 (Subgroup.zpowers s) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hs_ord, pow_one]
      have hzp_le_C : Subgroup.zpowers s ≤ C := by
        intro x hx
        have hxS : x ∈ h.S := (Subgroup.zpowers_le.mpr hs) hx
        exact ⟨h.S_le_M hxS, Subgroup.mem_centralizer_singleton_iff.mpr (h.S_comm hxS hs)⟩
      have hC_cz : C ≤ Subgroup.centralizer (Subgroup.zpowers s : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
        exact (Commute.zpow_left (show Commute s x from hxs.symm) j).eq
      have hC_norm : C ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
        hC_cz.trans (Subgroup.centralizer_le_normalizer _)
      have hzp_le_T : Subgroup.zpowers s ≤ T :=
        CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_le_of_le_normalizer
          hT hsp hzp_le_C hC_norm
      have hsT : s ∈ T := hzp_le_T (Subgroup.mem_zpowers s)
      have hs_central_T : s ∈ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hT.le hx).2
      let p : G := m⁻¹ * s * m
      have hpP : p ∈ h.P := by
        have := (hmconj s).mp hsT
        simpa [p] using this
      have hp_central : p ∈ Subgroup.centralizer (h.P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxT : m * x * m⁻¹ ∈ T := by
          apply (hmconj (m * x * m⁻¹)).mpr
          rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group]
        have hsx : s * (m * x * m⁻¹) = (m * x * m⁻¹) * s :=
          (Subgroup.mem_centralizer_iff.mp hs_central_T (m * x * m⁻¹) hxT).symm
        calc x * p = m⁻¹ * ((m * x * m⁻¹) * s) * m := by dsimp [p]; group
          _ = m⁻¹ * (s * (m * x * m⁻¹)) * m := by rw [← hsx]
          _ = p * x := by dsimp [p]; group
      have hp_z : p ∈ Subgroup.zpowers h.z := by
        have hmem : p ∈ h.P ⊓ Subgroup.centralizer (h.P : Set G) := ⟨hpP, hp_central⟩
        rwa [h.center_eq] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp_z
      have hs_eq_k : s = m * h.z ^ k * m⁻¹ := by
        rw [show s = m * p * m⁻¹ by dsimp [p]; group, ← hk]
      have hp_ne : p ≠ 1 := by
        intro hp1
        have hs1 : s = 1 := by
          rw [show s = m * p * m⁻¹ by dsimp [p]; group, hp1]; group
        exact hs_ne hs1
      have hp_ord : orderOf p = 3 := by
        have hpc : p = MulAut.conj m⁻¹ s := by simp [p, MulAut.conj_apply]
        calc orderOf p = orderOf ((MulAut.conj m⁻¹) s) := by rw [hpc]
          _ = orderOf s := by
              simpa using orderOf_injective (MulAut.conj m⁻¹).toMonoidHom
                (MulAut.conj m⁻¹).injective s
          _ = 3 := hs_ord
      have hz3n : h.z ^ 3 = 1 := by
        rw [← h.orderOf_z]
        exact pow_orderOf_eq_one h.z
      have hz3 : h.z ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact hz3n
      rw [zpow_eq_zpow_emod (x := h.z) k hz3] at hk
      have hk_ne_one : h.z ^ (k % 3) ≠ 1 := by
        intro h1
        apply hp_ne
        rw [← hk, h1]
      have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
      have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hcases : k % 3 = 1 ∨ k % 3 = 2 := by
        have hne0 : k % 3 ≠ 0 := by
          intro h0
          exact hk_ne_one (by rw [h0]; simp)
        omega
      have hz2 : h.z ^ 2 = h.z⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← pow_succ', show 2 + 1 = 3 by norm_num]
        exact hz3n
      let u : G := (g * m) * h.z * (g * m)⁻¹
      have hu_eq : u = h.y ∨ u = h.y⁻¹ := by
        rcases hcases with h1 | h2
        · left
          have hzk : h.z ^ k = h.z := by
            rw [show h.z ^ k = h.z ^ (k % 3) from zpow_eq_zpow_emod (x := h.z) k hz3,
              h1]
            simp
          have hus : u = g * s * g⁻¹ := by
            rw [hs_eq_k, hzk]
            dsimp [u]
            group
          rw [hus, hconj]
        · right
          have hzk : h.z ^ k = h.z⁻¹ := by
            rw [show h.z ^ k = h.z ^ (k % 3) from zpow_eq_zpow_emod (x := h.z) k hz3,
              h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
            exact hz2
          have hus : u⁻¹ = g * s * g⁻¹ := by
            rw [hs_eq_k]
            dsimp [u]
            rw [hzk]
            group
          have huy : u⁻¹ = h.y := by rw [hus, hconj]
          simpa using congrArg (fun x : G => x⁻¹) huy
      have huP : u ∈ h.P := by
        rcases hu_eq with hu | hu
        · rw [hu]; exact h.y_mem
        · rw [hu]; exact h.y_inv_mem_P
      have huL : u ∉ c.L := by
        rcases hu_eq with hu | hu
        · rw [hu]; exact h.y_not_mem_L
        · rw [hu]; exact h.y_inv_not_mem_L
      have hu_ord : orderOf u = 3 := by
        rcases hu_eq with hu | hu
        · rw [hu]; exact h.orderOf_y
        · rw [hu]; exact h.orderOf_y_inv
      let w' : G := (g * m)⁻¹ * h.z * (g * m)
      have hw'_eq : w' = m⁻¹ * w * m := by
        rw [hwdef]
        dsimp [w']
        rw [mul_inv_rev]
        group
      have hw'P : w' ∈ h.P := by
        simpa [hw'_eq] using (hmconj w).mp hwT
      have hw'_notS : w' ∉ h.S := by
        intro hw'S
        apply hCaseA
        exact ⟨w', hw'S, by rw [hw'_eq]; group⟩
      have hw'L : w' ∉ c.L := fun hL => hw'_notS ⟨hw'P, hL⟩
      have hw'_ord : orderOf w' = 3 := by
        have hw'conj : w' = MulAut.conj (g * m)⁻¹ h.z := by
          rw [MulAut.conj_apply, inv_inv]
        calc orderOf w' = orderOf ((MulAut.conj (g * m)⁻¹) h.z) := by rw [hw'conj]
          _ = orderOf h.z := by
              simpa using orderOf_injective (MulAut.conj (g * m)⁻¹).toMonoidHom
                (MulAut.conj (g * m)⁻¹).injective h.z
          _ = 3 := h.orderOf_z
      obtain ⟨s₁, hs₁S, hs₁⟩ := h.exists_conj_eq_mul u huP huL hu_ord
      obtain ⟨s₂, hs₂S, hs₂⟩ := h.exists_conj_eq_mul w' hw'P hw'L hw'_ord
      have hs₁z : s₁ * h.z * s₁⁻¹ = h.z := by
        rw [show s₁ * h.z = h.z * s₁ from h.S_comm hs₁S h.z_mem]
        group
      have hs₂z : s₂ * h.z * s₂⁻¹ = h.z := by
        rw [show s₂ * h.z = h.z * s₂ from h.S_comm hs₂S h.z_mem]
        group
      let kk : G := g * m
      let v : G := kk * s₂ * kk⁻¹
      have hv_fix_u : v * u * v⁻¹ = u := by
        have hv : v = kk * s₂ * kk⁻¹ := rfl
        have hu : u = kk * h.z * kk⁻¹ := rfl
        calc v * u * v⁻¹ = kk * (s₂ * h.z * s₂⁻¹) * kk⁻¹ := by
              rw [hv, hu]; group
          _ = kk * h.z * kk⁻¹ := by rw [hs₂z]
          _ = u := by rw [hu]
      have hv_z : v * h.z * v⁻¹ = h.z * u ∨ v * h.z * v⁻¹ = h.z * u⁻¹ := by
        have hz_w' : h.z = kk * w' * kk⁻¹ := by dsimp [w', kk]; group
        rcases hs₂ with h2 | h2
        · left
          calc v * h.z * v⁻¹ = kk * (s₂ * w' * s₂⁻¹) * kk⁻¹ := by
                rw [hz_w', show v = kk * s₂ * kk⁻¹ from rfl]
                group
            _ = kk * (w' * h.z) * kk⁻¹ := by rw [h2]
            _ = h.z * u := by
                rw [show kk * (w' * h.z) * kk⁻¹ =
                  (kk * w' * kk⁻¹) * (kk * h.z * kk⁻¹) by group, ← hz_w']
        · right
          calc v * h.z * v⁻¹ = kk * (s₂ * w' * s₂⁻¹) * kk⁻¹ := by
                rw [hz_w', show v = kk * s₂ * kk⁻¹ from rfl]
                group
            _ = kk * (w' * h.z⁻¹) * kk⁻¹ := by rw [h2]
            _ = h.z * u⁻¹ := by
                rw [show kk * (w' * h.z⁻¹) * kk⁻¹ =
                  (kk * w' * kk⁻¹) * (kk * h.z⁻¹ * kk⁻¹) by group, ← hz_w']
                change h.z * (kk * h.z⁻¹ * kk⁻¹) = h.z * (kk * h.z * kk⁻¹)⁻¹
                group
      have hzu : Commute h.z u := by
        have hcomm : u * h.z = h.z * u :=
          Subgroup.mem_centralizer_iff.mp h.z_central u huP
        exact hcomm.symm
      obtain ⟨t, -, ht_z, ht_u⟩ :=
        CFSG.GroupTheory.exists_mem_closure_conj_eq_inv_of_transvections
          (u := h.z) (v := u) (s₁ := s₁) (s₂ := v) hzu hs₁z hs₁ hv_fix_u hv_z
      have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers h.z : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
        have htz : (MulAut.conj t) h.z = h.z⁻¹ := by
          simpa [MulAut.conj_apply] using ht_z
        change Subgroup.zpowers ((MulAut.conj t) h.z) = Subgroup.zpowers h.z
        rw [htz, Subgroup.zpowers_inv]
      have htM : t ∈ D.M :=
        h.normalizer_le (Subgroup.zpowers h.z) h.zpowers_z_le_S h.zpowers_z_ne_bot htN
      have hty : t * h.y * t⁻¹ = h.y⁻¹ := by
        rcases hu_eq with hu | hu
        · have ht_u' : t * h.y * t⁻¹ = h.y⁻¹ := by
            simpa [hu] using ht_u
          exact ht_u'
        · have hty' : t * h.y⁻¹ * t⁻¹ = h.y := by
            rw [← hu, ht_u, hu, inv_inv]
          calc t * h.y * t⁻¹ = (t * h.y⁻¹ * t⁻¹)⁻¹ := by group
            _ = h.y⁻¹ := by rw [hty']
      have hzero : h.y * (t * h.y * t⁻¹) = 1 := by rw [hty]; group
      exact h.not_conj_inv t htM (by rw [hzero]; exact h.S.one_mem)

theorem false_of_noncentralizing_z {u : G}
    (huC : u ∈ Subgroup.centralizer ({h.y} : Set G))
    (huN : u ∈ Subgroup.normalizer (h.E : Set G))
    (huE : u ∉ h.E) (hu3 : ∃ k, orderOf u = 3 ^ k)
    (huz : u * h.z ≠ h.z * u) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let t : G := u * h.z * u⁻¹
  have htE : t ∈ h.E := by
    have hmem := (Subgroup.mem_normalizer_iff.mp huN h.z).mp h.z_mem_E
    simpa [t] using hmem
  have ht_ord : orderOf t = 3 := by
    have ht_conj : t = MulAut.conj u h.z := by
      rw [MulAut.conj_apply]
    calc orderOf t = orderOf ((MulAut.conj u) h.z) := by rw [ht_conj]
      _ = orderOf h.z := by
          simpa using orderOf_injective (MulAut.conj u).toMonoidHom
            (MulAut.conj u).injective h.z
      _ = 3 := h.orderOf_z
  have ht_ne_one : t ≠ 1 := by
    intro h1
    have hord1 : orderOf t = 1 := by rw [h1]; exact orderOf_one
    rw [ht_ord] at hord1
    norm_num at hord1
  have hE_le_Czp : h.E ≤ Subgroup.centralizer (Subgroup.zpowers h.z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : x * h.z = h.z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer_z hx)
    exact (Commute.zpow_right hxz j).eq.symm
  have hE_le_Nzp : h.E ≤ Subgroup.normalizer (Subgroup.zpowers h.z : Set G) :=
    hE_le_Czp.trans (Subgroup.centralizer_le_normalizer _)
  have hzp_normal : ((Subgroup.zpowers h.z).subgroupOf h.E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.zpowers_z_le_E).mpr hE_le_Nzp
  have hy_not_zp : h.y ∉ Subgroup.zpowers h.z := fun hy =>
    h.y_not_mem_S (h.zpowers_z_le_S hy)
  have ht_cases := CFSG.GroupTheory.mem_or_inv_mul_mem_or_mul_mem_of_relIndex_eq_three
    hzp_normal h.relIndex_zpowers_E h.y_mem_E hy_not_zp htE
  rcases ht_cases with ht_zp | ht_yinv | ht_y
  ·
    have htzw := CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
      h.orderOf_z ht_zp ht_ne_one
    rcases htzw with htzw | htzw
    ·
      apply huz
      have htz : u * h.z * u⁻¹ = h.z := by simpa [t] using htzw
      calc u * h.z = (u * h.z * u⁻¹) * u := by group
        _ = h.z * u := by rw [htz]
    ·
      have htz : u * h.z * u⁻¹ = h.z⁻¹ := by simpa [t] using htzw
      have hu2_z : u ^ 2 * h.z * (u ^ 2)⁻¹ = h.z := by
        rw [pow_two, mul_inv_rev]
        calc (u * u) * h.z * (u⁻¹ * u⁻¹)
            = u * (u * h.z * u⁻¹) * u⁻¹ := by group
          _ = u * h.z⁻¹ * u⁻¹ := by rw [htz]
          _ = (u * h.z * u⁻¹)⁻¹ := by group
          _ = (h.z⁻¹)⁻¹ := by rw [htz]
          _ = h.z := by rw [inv_inv]
      have huy : u * h.y = h.y * u :=
        Subgroup.mem_centralizer_singleton_iff.mp huC
      have hu2_y : u ^ 2 * h.y * (u ^ 2)⁻¹ = h.y := by
        rw [pow_two, mul_inv_rev]
        calc (u * u) * h.y * (u⁻¹ * u⁻¹) = u * (u * h.y) * (u⁻¹ * u⁻¹) := by group
          _ = u * (h.y * u) * (u⁻¹ * u⁻¹) := by rw [huy]
          _ = h.y := by
              rw [show u * (h.y * u) * (u⁻¹ * u⁻¹) = u * h.y * u⁻¹ by group, huy]
              group
      have hu2_central : u ^ 2 ∈ Subgroup.centralizer (h.E : Set G) := by
        rw [E, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        have hy_comm : u ^ 2 * h.y = h.y * u ^ 2 := by
          calc u ^ 2 * h.y = (u ^ 2 * h.y * (u ^ 2)⁻¹) * u ^ 2 := by group
            _ = h.y * u ^ 2 := by rw [hu2_y]
        have hz_comm : u ^ 2 * h.z = h.z * u ^ 2 := by
          calc u ^ 2 * h.z = (u ^ 2 * h.z * (u ^ 2)⁻¹) * u ^ 2 := by group
            _ = h.z * u ^ 2 := by rw [hu2_z]
        rcases ha with rfl | rfl
        · exact hy_comm.symm
        · exact hz_comm.symm
      let φ : MulAut h.E := Subgroup.normalizerMonoidHom h.E ⟨u, huN⟩
      have hu2N : u ^ 2 ∈ Subgroup.normalizer (h.E : Set G) := Subgroup.pow_mem _ huN 2
      have hφ2 : φ ^ 2 = 1 := by
        have hmap : Subgroup.normalizerMonoidHom h.E (⟨u, huN⟩ ^ 2) =
            Subgroup.normalizerMonoidHom h.E ⟨u ^ 2, hu2N⟩ := by
          congr 1
        calc φ ^ 2 = Subgroup.normalizerMonoidHom h.E (⟨u, huN⟩ ^ 2) := by
              dsimp only [φ]
              rw [map_pow]
          _ = Subgroup.normalizerMonoidHom h.E ⟨u ^ 2, hu2N⟩ := hmap
          _ = 1 := by
              rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
              exact (Subgroup.mem_subgroupOf).mpr hu2_central
      have hφ_ord2 : orderOf φ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hφ2
      have hφ_ord_u : orderOf φ ∣ orderOf u := by
        have hdvd := orderOf_map_dvd (Subgroup.normalizerMonoidHom h.E) ⟨u, huN⟩
        have hcoe : orderOf (⟨u, huN⟩ : Subgroup.normalizer (h.E : Set G)) = orderOf u :=
          (Subgroup.orderOf_coe ⟨u, huN⟩).symm
        rw [hcoe] at hdvd
        simpa [φ] using hdvd
      obtain ⟨j, hj⟩ := hu3
      have hφ_ord3 : orderOf φ ∣ 3 ^ j := by rw [← hj]; exact hφ_ord_u
      have hcop : Nat.Coprime 2 (3 ^ j) := (by norm_num : Nat.Coprime 2 3).pow_right j
      have hφ_ord1 : orderOf φ = 1 := by
        have hdvd : orderOf φ ∣ Nat.gcd 2 (3 ^ j) := Nat.dvd_gcd hφ_ord2 hφ_ord3
        rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hdvd
        exact Nat.dvd_one.mp hdvd
      have hφ_eq_one : φ = 1 := orderOf_eq_one_iff.mp hφ_ord1
      have huz_eq : u * h.z * u⁻¹ = h.z := by
        have hφz := congrArg (fun ψ : MulAut h.E => ψ ⟨h.z, h.z_mem_E⟩) hφ_eq_one
        simp only [MulAut.one_apply] at hφz
        have hφz_coe : ((φ ⟨h.z, h.z_mem_E⟩ : h.E) : G) = u * h.z * u⁻¹ := by
          dsimp only [φ]
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        have : ((φ ⟨h.z, h.z_mem_E⟩ : h.E) : G) = h.z := by rw [hφz]
        rwa [hφz_coe] at this
      apply huz
      calc u * h.z = (u * h.z * u⁻¹) * u := by group
        _ = h.z * u := by rw [huz_eq]
  ·
    obtain ⟨s, hsS, hst⟩ := h.exists_conj h.y h.y_mem h.y_not_mem_L h.orderOf_y t
      (h.zpowers_z_le_S ht_yinv) ht_ord
    have hy_conj : (s⁻¹ * u) * h.z * (s⁻¹ * u)⁻¹ = h.y := by
      rw [show (s⁻¹ * u) * h.z * (s⁻¹ * u)⁻¹ = s⁻¹ * t * s by dsimp [t]; group,
        hst]
      group
    exact h.conj_ne_y (s⁻¹ * u) h.z_mem hy_conj
  ·
    obtain ⟨s, hsS, hst⟩ := h.exists_conj h.y⁻¹ h.y_inv_mem_P h.y_inv_not_mem_L
      h.orderOf_y_inv t (by simpa using h.zpowers_z_le_S ht_y) ht_ord
    have hconj_yinv : (s⁻¹ * u) * h.z * (s⁻¹ * u)⁻¹ = h.y⁻¹ := by
      rw [show (s⁻¹ * u) * h.z * (s⁻¹ * u)⁻¹ = s⁻¹ * t * s by dsimp [t]; group,
        hst]
      group
    have hy_conj : (s⁻¹ * u) * h.z⁻¹ * (s⁻¹ * u)⁻¹ = h.y := by
      calc (s⁻¹ * u) * h.z⁻¹ * (s⁻¹ * u)⁻¹
          = ((s⁻¹ * u) * h.z * (s⁻¹ * u)⁻¹)⁻¹ := by group
        _ = h.y := by rw [hconj_yinv, inv_inv]
    exact h.conj_ne_y (s⁻¹ * u) (h.S.inv_mem h.z_mem) hy_conj

theorem false_of_normalizes_E_inverts_y {n : G}
    (hnN : n ∈ Subgroup.normalizer (h.E : Set G))
    (hny : n * h.y * n⁻¹ = h.y⁻¹) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let t : G := n * h.z * n⁻¹
  have htE : t ∈ h.E := by
    have hmem := (Subgroup.mem_normalizer_iff.mp hnN h.z).mp h.z_mem_E
    simpa [t] using hmem
  have ht_ord : orderOf t = 3 := by
    have ht_conj : t = MulAut.conj n h.z := by
      rw [MulAut.conj_apply]
    calc orderOf t = orderOf ((MulAut.conj n) h.z) := by rw [ht_conj]
      _ = orderOf h.z := by
          simpa using orderOf_injective (MulAut.conj n).toMonoidHom
            (MulAut.conj n).injective h.z
      _ = 3 := h.orderOf_z
  have ht_ne_one : t ≠ 1 := by
    intro h1
    have hord1 : orderOf t = 1 := by rw [h1]; exact orderOf_one
    rw [ht_ord] at hord1
    norm_num at hord1
  have hE_le_Czp : h.E ≤ Subgroup.centralizer (Subgroup.zpowers h.z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : x * h.z = h.z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer_z hx)
    exact (Commute.zpow_right hxz j).eq.symm
  have hE_le_Nzp : h.E ≤ Subgroup.normalizer (Subgroup.zpowers h.z : Set G) :=
    hE_le_Czp.trans (Subgroup.centralizer_le_normalizer _)
  have hzp_normal : ((Subgroup.zpowers h.z).subgroupOf h.E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.zpowers_z_le_E).mpr hE_le_Nzp
  have hy_not_zp : h.y ∉ Subgroup.zpowers h.z := fun hy =>
    h.y_not_mem_S (h.zpowers_z_le_S hy)
  have ht_cases := CFSG.GroupTheory.mem_or_inv_mul_mem_or_mul_mem_of_relIndex_eq_three
    hzp_normal h.relIndex_zpowers_E h.y_mem_E hy_not_zp htE
  rcases ht_cases with ht_zp | ht_yinv | ht_y
  ·
    have hzp_t : Subgroup.zpowers t = Subgroup.zpowers h.z := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht_zp)
      rw [Nat.card_zpowers, Nat.card_zpowers, ht_ord, h.orderOf_z]
    have hn_zp : n ∈ Subgroup.normalizer (Subgroup.zpowers h.z : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj n) h.z) = Subgroup.zpowers h.z
      have hnt : (MulAut.conj n) h.z = t := by
        rw [MulAut.conj_apply]
      rw [hnt, hzp_t]
    have hnM : n ∈ D.M :=
      h.normalizer_le (Subgroup.zpowers h.z) h.zpowers_z_le_S h.zpowers_z_ne_bot hn_zp
    exact h.not_conj_inv n hnM (by rw [hny]; simpa using h.S.one_mem)
  ·
    obtain ⟨s, hsS, hst⟩ := h.exists_conj h.y h.y_mem h.y_not_mem_L h.orderOf_y t
      (h.zpowers_z_le_S ht_yinv) ht_ord
    have hy_conj : (s⁻¹ * n) * h.z * (s⁻¹ * n)⁻¹ = h.y := by
      rw [show (s⁻¹ * n) * h.z * (s⁻¹ * n)⁻¹ = s⁻¹ * t * s by dsimp [t]; group,
        hst]
      group
    exact h.conj_ne_y (s⁻¹ * n) h.z_mem hy_conj
  ·
    obtain ⟨s, hsS, hst⟩ := h.exists_conj h.y⁻¹ h.y_inv_mem_P h.y_inv_not_mem_L
      h.orderOf_y_inv t (by simpa using h.zpowers_z_le_S ht_y) ht_ord
    have hconj_yinv : (s⁻¹ * n) * h.z * (s⁻¹ * n)⁻¹ = h.y⁻¹ := by
      rw [show (s⁻¹ * n) * h.z * (s⁻¹ * n)⁻¹ = s⁻¹ * t * s by dsimp [t]; group,
        hst]
      group
    have hy_conj : (s⁻¹ * n) * h.z⁻¹ * (s⁻¹ * n)⁻¹ = h.y := by
      calc (s⁻¹ * n) * h.z⁻¹ * (s⁻¹ * n)⁻¹
          = ((s⁻¹ * n) * h.z * (s⁻¹ * n)⁻¹)⁻¹ := by group
        _ = h.y := by rw [hconj_yinv, inv_inv]
    exact h.conj_ne_y (s⁻¹ * n) (h.S.inv_mem h.z_mem) hy_conj

theorem E_isSylow_centralizer :
    CFSG.ABGLocalTools.IsSylowOf 3 h.E (Subgroup.centralizer ({h.y} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hnot
  have hEC : h.E ≤ Subgroup.centralizer ({h.y} : Set G) := h.E_le_centralizer_y
  obtain ⟨T, hET, hT⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge h.E_isPGroup hEC
  have hne : h.E ≠ T := by
    intro heq
    exact hnot (by rwa [← heq] at hT)
  have hlt := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.lt_inf_normalizer_of_lt
    Nat.prime_three hT.isPGroup hET hne
  obtain ⟨u, hu, huE⟩ := IsConcreteLE.exists_of_lt hlt
  have huT : u ∈ T := hu.1
  have huN : u ∈ Subgroup.normalizer (h.E : Set G) := hu.2
  have huC : u ∈ Subgroup.centralizer ({h.y} : Set G) := hT.le huT
  have hu3 : ∃ k, orderOf u = 3 ^ k := by
    obtain ⟨k, hk⟩ := hT.isPGroup.exists_orderOf_eq_pow ⟨u, huT⟩
    have hcoe : orderOf (⟨u, huT⟩ : T) = orderOf u :=
      (Subgroup.orderOf_coe ⟨u, huT⟩).symm
    exact ⟨k, by rwa [hcoe] at hk⟩
  by_cases huz : u * h.z = h.z * u
  · exact h.false_of_centralizing_z huC huN huE hu3 huz
  · exact h.false_of_noncentralizing_z huC huN huE hu3 huz

theorem mul_conj_not_mem (g : G) : h.y * (g * h.y * g⁻¹) ∉ h.P ⊓ c.L := by
  classical
  intro hmem
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let x : G := g * h.y * g⁻¹
  have hx_ord : orderOf x = 3 := by
    have hxconj : x = MulAut.conj g h.y := by
      rw [MulAut.conj_apply]
    calc orderOf x = orderOf ((MulAut.conj g) h.y) := by rw [hxconj]
      _ = orderOf h.y := by
          simpa using orderOf_injective (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective h.y
      _ = 3 := h.orderOf_y
  have hxP : x ∈ h.P := by
    have h := h.P.mul_mem (h.P.inv_mem h.y_mem) hmem.1
    simpa [x, mul_assoc] using h
  have hxL : x ∉ c.L := by
    intro hxL
    have hyL : h.y ∈ c.L := by
      have h := c.L.mul_mem hmem.2 (c.L.inv_mem hxL)
      simpa [x, mul_assoc] using h
    exact h.y_not_mem_L hyL
  obtain ⟨s, hsS, hsx⟩ := h.exists_conj h.y⁻¹ h.y_inv_mem_P h.y_inv_not_mem_L
    h.orderOf_y_inv x (by simpa [x] using hmem) hx_ord
  let g' : G := s⁻¹ * g
  have hg'y : g' * h.y * g'⁻¹ = h.y⁻¹ := by
    have hg'eq : g' * h.y * g'⁻¹ = s⁻¹ * x * s := by
      dsimp [g', x]; group
    rw [hg'eq, hsx]
    group
  let M : Subgroup G := Subgroup.normalizer (Subgroup.zpowers h.y : Set G)
  let L : Subgroup G := Subgroup.centralizer ({h.y} : Set G)
  have hg'M : g' ∈ M := by
    change g' ∈ Subgroup.normalizer (Subgroup.zpowers h.y : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hg'y' : (MulAut.conj g') h.y = h.y⁻¹ := by
      simpa [MulAut.conj_apply] using hg'y
    change Subgroup.zpowers ((MulAut.conj g') h.y) = Subgroup.zpowers h.y
    rw [hg'y', Subgroup.zpowers_inv]
  have hL_eq : L = Subgroup.centralizer (Subgroup.zpowers h.y : Set G) := by
    change Subgroup.centralizer ({h.y} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers h.y : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hLM : L ≤ M :=
    hL_eq ▸ Subgroup.centralizer_le_normalizer (Subgroup.zpowers h.y : Set G)
  have hL_normal : (L.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM]
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj m).toMonoidHom
      (Subgroup.centralizer ({h.y} : Set G)) = Subgroup.centralizer ({h.y} : Set G)
    rw [CFSG.centralizer_singleton_map]
    have hm_mem : m * h.y * m⁻¹ ∈ Subgroup.zpowers h.y := by
      have hmap : Subgroup.map (MulAut.conj m).toMonoidHom (Subgroup.zpowers h.y) =
          Subgroup.zpowers h.y := Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
      have hmem' : (MulAut.conj m) h.y ∈ Subgroup.zpowers h.y := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers h.y)
      simpa [MulAut.conj_apply] using hmem'
    have hm_ord : orderOf (m * h.y * m⁻¹) = 3 := by
      have hmconj : m * h.y * m⁻¹ = MulAut.conj m h.y := by
        rw [MulAut.conj_apply]
      calc orderOf (m * h.y * m⁻¹) = orderOf ((MulAut.conj m) h.y) := by rw [hmconj]
        _ = orderOf h.y := by
            simpa using orderOf_injective (MulAut.conj m).toMonoidHom
              (MulAut.conj m).injective h.y
        _ = 3 := h.orderOf_y
    have hm_ne_one : m * h.y * m⁻¹ ≠ 1 := by
      intro h1
      have hord1 : orderOf (m * h.y * m⁻¹) = 1 := by rw [h1]; exact orderOf_one
      rw [hm_ord] at hord1
      norm_num at hord1
    have hm_y : m * h.y * m⁻¹ = h.y ∨ m * h.y * m⁻¹ = h.y⁻¹ :=
      CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
        h.orderOf_y hm_mem hm_ne_one
    rcases hm_y with hm_y | hm_y
    · rw [MulAut.conj_apply, hm_y]
    · rw [MulAut.conj_apply, hm_y]
      have hc_inv : Subgroup.centralizer ({h.y⁻¹} : Set G) =
          Subgroup.centralizer ({h.y} : Set G) := by
        conv_lhs => rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        conv_rhs => rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        rw [Subgroup.zpowers_inv]
      exact hc_inv
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hL_normal
  have hg'L : g' ∈ Subgroup.normalizer (L : Set G) := hML hg'M
  have hmapL : Subgroup.map (MulAut.conj g').toMonoidHom L = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg'L
  have hE_sylow_L : CFSG.ABGLocalTools.IsSylowOf 3 h.E L := h.E_isSylow_centralizer
  have hg'E_sylow : CFSG.ABGLocalTools.IsSylowOf 3
      (Subgroup.map (MulAut.conj g').toMonoidHom h.E) L := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨?_, ?_, ?_⟩
    · rw [← hmapL]
      exact Subgroup.map_mono hE_sylow_L.le
    · exact hE_sylow_L.isPGroup.map _
    · have hEr : ¬ 3 ∣ h.E.relIndex L :=
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hE_sylow_L).2.2
      rw [← hmapL, Subgroup.relIndex_map_map_of_injective h.E L
        (MulAut.conj g').injective]
      exact hEr
  obtain ⟨c, hcL, hc_conj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hg'E_sylow hE_sylow_L
  have hc_map : Subgroup.map (MulAut.conj c).toMonoidHom
      (Subgroup.map (MulAut.conj g').toMonoidHom h.E) = h.E := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      rw [Subgroup.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      refine (hc_conj (c * (g' * b * g'⁻¹) * c⁻¹)).mpr ?_
      rw [show c⁻¹ * (c * (g' * b * g'⁻¹) * c⁻¹) * c = (MulAut.conj g') b by
        rw [MulAut.conj_apply]; group]
      exact Subgroup.mem_map_of_mem (MulAut.conj g').toMonoidHom hb
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
        Subgroup.card_map_of_injective (MulAut.conj g').injective, h.E_card]
  let n : G := c * g'
  have hn_y : n * h.y * n⁻¹ = h.y⁻¹ := by
    have hc_y : c * h.y = h.y * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcL
    calc n * h.y * n⁻¹ = c * (g' * h.y * g'⁻¹) * c⁻¹ := by dsimp [n]; group
      _ = c * h.y⁻¹ * c⁻¹ := by rw [hg'y]
      _ = h.y⁻¹ := by
          have hc_yinv : c * h.y⁻¹ = h.y⁻¹ * c :=
            (show Commute c h.y from hc_y).inv_right.eq
          rw [hc_yinv]
          group
  have hn_E : Subgroup.map (MulAut.conj n).toMonoidHom h.E = h.E := by
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj g').toMonoidHom =
        (MulAut.conj n).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      dsimp [n]
      group
    calc Subgroup.map (MulAut.conj n).toMonoidHom h.E
        = Subgroup.map ((MulAut.conj c).toMonoidHom.comp
            (MulAut.conj g').toMonoidHom) h.E := by rw [hcomp]
      _ = Subgroup.map (MulAut.conj c).toMonoidHom
            (Subgroup.map (MulAut.conj g').toMonoidHom h.E) := by rw [Subgroup.map_map]
      _ = h.E := hc_map
  have hnN : n ∈ Subgroup.normalizer (h.E : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hn_E
  exact h.false_of_normalizes_E_inverts_y hnN hn_y

theorem inv_mul_conj_mem (g : G) (hg : g * h.y * g⁻¹ ∈ h.P) :
    h.y⁻¹ * (g * h.y * g⁻¹) ∈ h.P ⊓ c.L := by
  let x : G := g * h.y * g⁻¹
  have hxP : x ∈ h.P := hg
  rcases h.mem_or_mem_or_mem hxP with hxS | hyinv | hyx
  ·
    exfalso
    apply h.conj_ne_y g⁻¹ hxS
    dsimp [x]
    group
  · exact hyinv
  ·
    exact absurd hyx (h.mul_conj_not_mem g)

end Case811L227

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
