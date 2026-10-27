module

public import CFSG.Sporadic.SuzRecog.SuzL34.NormalizerL
public import CFSG.Sporadic.SuzRecog.SuzL34.Transfer
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] {z : G} (D : LocalData G z)

noncomputable abbrev TG : Subgroup G := D.pull (tabSubgroup v0Tabs)

noncomputable abbrev T0G : Subgroup G := D.pull (tabSubgroup t0Tabs)

noncomputable abbrev M2G : Subgroup G := D.pull (decSubgroup m21Decs)

noncomputable def T1G : Subgroup G :=
  D.T0G ⊔ Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem)

noncomputable abbrev tauG : G := D.elt (decPerm tauDec) (D.decPerm_mem tauDec (by decide))

noncomputable abbrev lamG : G := D.elt (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide))

noncomputable abbrev aG : G := D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide))

private theorem t0Tabs_le_invE (D : LocalData G z) : tabSubgroup t0Tabs ≤ invE 1 :=
  le_trans D.tabSubgroup_t0Tabs_le (by rw [D.tabSubgroup_v0Tabs]; exact inf_le_right)

theorem TG_eq :
    D.TG = centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G) ⊓
      centralizer ({z} : Set G) := by
  rw [TG, D.tabSubgroup_v0Tabs, D.pull_inf,
    D.pull_centralizer_singleton D.w0_mem, D.pull_invE, inf_assoc, inf_idem]

theorem TG_le_centralizer :
    D.TG ≤ centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G) := by
  rw [TG_eq]
  exact inf_le_left

theorem fixedCard_w0 (hF3 : F3Prop) : fixedCard (permC 1782 w0T) = 42 := by
  simp only [F3Prop] at hF3
  obtain ⟨-, -, -, h4, -⟩ := hF3
  exact h4 _ ⟨1, Subgroup.one_mem _, by group⟩

theorem not_isConj_t0 (hF3 : F3Prop) :
    ¬ IsConj (D.elt (permC 1782 w0T) D.w0_mem) z := by
  rw [D.not_isConj_elt_iff D.w0_mem D.w0_mul_self D.w0_ne_one]
  exact fixedCard_w0 hF3

theorem card_TG (hF3 : F3Prop) : Nat.card D.TG = 512 := by
  rw [TG_eq]
  exact D.card_inf _ (D.elt_mem_centralizer (permC 1782 w0T) D.w0_mem)
    (D.t0_mul_self) (D.t0_ne_one) (not_isConj_t0 D hF3)

theorem isPGroup_TG (hF3 : F3Prop) : IsPGroup 2 D.TG :=
  IsPGroup.of_card (n := 9) (by rw [card_TG D hF3]; norm_num)

theorem not_two_dvd_relIndex_TG [Finite G] (hF3 : F3Prop) :
    ¬ 2 ∣ D.TG.relIndex (centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) := by
  have hS := D.isSylowOf_inf _ (D.elt_mem_centralizer (permC 1782 w0T) D.w0_mem)
    (D.t0_mul_self) (D.t0_ne_one) (not_isConj_t0 D hF3)
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have h := Q.not_dvd_index
  rw [TG_eq]
  rw [hQ] at h
  exact h

theorem t0_mem_TG : D.elt (permC 1782 w0T) D.w0_mem ∈ D.TG := by
  rw [TG_eq]
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    D.elt_mem_centralizer (permC 1782 w0T) D.w0_mem⟩

theorem t0_not_mem_T0G (hF3 : F3Prop) (hF4 : F4Prop) :
    D.elt (permC 1782 w0T) D.w0_mem ∉ D.T0G := by
  intro h
  have hW : permC 1782 w0T ∈ tabSubgroup t0Tabs :=
    (D.elt_mem_pull_iff D.w0_mem).mp h
  have h4 := hF4
  simp only [F4Prop] at h4
  obtain ⟨-, -, -, hlast⟩ := h4
  have h2 : (⟨permC 1782 w0T, hW⟩ : ↥(tabSubgroup t0Tabs)) *
      ⟨permC 1782 w0T, hW⟩ = 1 := Subtype.ext (D.w0_mul_self)
  have h1 : (⟨permC 1782 w0T, hW⟩ : ↥(tabSubgroup t0Tabs)) ≠ 1 := by
    intro hc
    exact D.w0_ne_one (congrArg Subtype.val hc)
  have hfix := hlast ⟨permC 1782 w0T, hW⟩ h2 h1
  change fixedCard (permC 1782 w0T) = 54 at hfix
  rw [fixedCard_w0 hF3] at hfix
  exact absurd hfix (by norm_num)

theorem T0G_le_TG : D.T0G ≤ D.TG :=
  D.pull_mono D.tabSubgroup_t0Tabs_le

theorem card_T0G : Nat.card D.T0G = 64 := by
  rw [T0G, D.card_pull (t0Tabs_le_invE D), D.card_T0]


private theorem l1_card (hF1 : F1Prop) :
    Nat.card ↥(decSubgroup l1Decs) = 16 := by
  simp only [F1Prop] at hF1
  obtain ⟨-, -, -, -, -, h, -⟩ := hF1
  exact h

private theorem l1_elemAbelian (hF1 : F1Prop) :
    CFSG.Open.IsElemAbelian 2 (decSubgroup l1Decs) := by
  simp only [F1Prop] at hF1
  obtain ⟨-, -, -, -, h, -⟩ := hF1
  exact h

private theorem map_conj_tau_le_M21 (hF5 : F5Prop) :
    (decSubgroup l1Decs).map (MulAut.conj (decPerm tauDec)).toMonoidHom ≤
      decSubgroup m21Decs := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, htau, -, -⟩ := h5
  rw [decSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  rcases hx with ⟨d, hd, rfl⟩
  obtain ⟨k, hk, hdk⟩ := List.mem_iff_getElem.mp hd
  have hk4 : k < 4 := by simpa [l1Decs] using hk
  rw [← hdk]
  have hb : l1BasisPerm k = decPerm (l1Decs[k]'hk) := by
    unfold l1BasisPerm
    exact congrArg decPerm (List.getD_eq_getElem l1Decs ([], 1) hk)
  rw [← hb]
  simpa [MulAut.conj_apply] using htau ⟨k, hk4⟩

private theorem setMul_L1_M21_le_T0 (hF5 : F5Prop) :
    ((decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) *
      (decSubgroup m21Decs : Set (Equiv.Perm (Fin 1782)))) ⊆
      (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, hL1, hM21, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  rintro x ⟨a, ha, b, hb, rfl⟩
  exact (tabSubgroup t0Tabs).mul_mem (hL1 ha) (hM21 hb)

private theorem card_M21_le (hF1 : F1Prop) (hF5 : F5Prop)
    (hT0 : Nat.card ↥(tabSubgroup t0Tabs) = 64) :
    Nat.card ↥(decSubgroup m21Decs) ≤ 16 := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨hZT, -, -, -, hLM, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  have hprod := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf
    (decSubgroup l1Decs) (decSubgroup m21Decs)
  have hinf : Nat.card ↥(decSubgroup l1Decs ⊓ decSubgroup m21Decs) = 4 := by
    rw [hLM, hZT]
  have hcardset : Nat.card ↥((decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) *
      (decSubgroup m21Decs : Set (Equiv.Perm (Fin 1782)))) ≤ 64 := by
    rw [← hT0]
    exact Nat.card_le_card_of_injective
      (f := fun x => (⟨x.1, setMul_L1_M21_le_T0 hF5 x.2⟩ : ↥(tabSubgroup t0Tabs)))
      (fun x y hxy => Subtype.ext (congrArg
        (fun t : ↥(tabSubgroup t0Tabs) => (t : Equiv.Perm (Fin 1782))) hxy))
  rw [l1_card hF1, hinf] at hprod
  omega

private theorem card_M21 (hF1 : F1Prop) (hF5 : F5Prop)
    (hT0 : Nat.card ↥(tabSubgroup t0Tabs) = 64) :
    Nat.card ↥(decSubgroup m21Decs) = 16 := by
  have hle := card_M21_le hF1 hF5 hT0
  have hge : 16 ≤ Nat.card ↥(decSubgroup m21Decs) := by
    have hcard := Subgroup.card_le_of_le (map_conj_tau_le_M21 hF5)
    have hmapcard : Nat.card ↥((decSubgroup l1Decs).map
        (MulAut.conj (decPerm tauDec)).toMonoidHom) = Nat.card ↥(decSubgroup l1Decs) :=
      Subgroup.card_map_of_injective (MulAut.conj (decPerm tauDec)).injective
    rw [hmapcard, l1_card hF1] at hcard
    exact hcard
  omega

private theorem M21_eq_map (hF1 : F1Prop) (hF5 : F5Prop)
    (hT0 : Nat.card ↥(tabSubgroup t0Tabs) = 64) :
    decSubgroup m21Decs =
      (decSubgroup l1Decs).map (MulAut.conj (decPerm tauDec)).toMonoidHom := by
  refine (Subgroup.eq_of_le_of_card_ge (map_conj_tau_le_M21 hF5) ?_).symm
  have hmapcard : Nat.card ↥((decSubgroup l1Decs).map
      (MulAut.conj (decPerm tauDec)).toMonoidHom) = Nat.card ↥(decSubgroup l1Decs) :=
    Subgroup.card_map_of_injective (MulAut.conj (decPerm tauDec)).injective
  rw [card_M21 hF1 hF5 hT0, hmapcard, l1_card hF1]

private theorem T0_eq_sup_model (hF1 : F1Prop) (hF5 : F5Prop)
    (hT0 : Nat.card ↥(tabSubgroup t0Tabs) = 64) :
    tabSubgroup t0Tabs = decSubgroup l1Decs ⊔ decSubgroup m21Decs := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨hZT, hL1, hM21, -, hLM, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  have hsup : decSubgroup l1Decs ⊔ decSubgroup m21Decs ≤ tabSubgroup t0Tabs :=
    sup_le hL1 hM21
  have hprod := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf
    (decSubgroup l1Decs) (decSubgroup m21Decs)
  have hinf : Nat.card ↥(decSubgroup l1Decs ⊓ decSubgroup m21Decs) = 4 := by
    rw [hLM, hZT]
  have hset : Nat.card ↥((decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) *
      (decSubgroup m21Decs : Set (Equiv.Perm (Fin 1782)))) = 64 := by
    rw [l1_card hF1, card_M21 hF1 hF5 hT0, hinf] at hprod
    omega
  have hlecard : Nat.card ↥(tabSubgroup t0Tabs) ≤
      Nat.card ↥(decSubgroup l1Decs ⊔ decSubgroup m21Decs) := by
    rw [hT0, ← hset]
    exact Nat.card_le_card_of_injective
      (f := fun x => (⟨x.1, by
        obtain ⟨a, ha, b, hb, hxab⟩ := x.2
        rw [← hxab]
        exact Subgroup.mul_mem_sup ha hb⟩ :
          ↥(decSubgroup l1Decs ⊔ decSubgroup m21Decs)))
      (fun x y hxy => Subtype.ext (congrArg
        (fun t : ↥(decSubgroup l1Decs ⊔ decSubgroup m21Decs) =>
          (t : Equiv.Perm (Fin 1782))) hxy))
  exact (Subgroup.eq_of_le_of_card_ge hsup hlecard).symm

private theorem l1_le_invE (D : LocalData G z) (hF5 : F5Prop) :
    decSubgroup l1Decs ≤ invE 1 := by
  have h5 := hF5
  simp only [F5Prop] at h5
  exact le_trans h5.2.1 (t0Tabs_le_invE D)

private theorem m21_le_invE (D : LocalData G z) (hF5 : F5Prop) :
    decSubgroup m21Decs ≤ invE 1 := by
  have h5 := hF5
  simp only [F5Prop] at h5
  exact le_trans h5.2.2.1 (t0Tabs_le_invE D)

theorem tauG_mem_TG (hF5 : F5Prop) : D.tauG ∈ D.TG := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, htau, -, -, -⟩ := h5
  exact (D.elt_mem_pull_iff (D.decPerm_mem tauDec (by decide))).mpr htau

theorem M2G_eq_map (hF1 : F1Prop) (hF5 : F5Prop) :
    D.M2G = (D.pull (decSubgroup l1Decs)).map (MulAut.conj D.tauG).toMonoidHom := by
  have hmodel := M21_eq_map hF1 hF5 D.card_T0
  have hL1inv := l1_le_invE D hF5
  have hsmul : (decSubgroup l1Decs).map (MulAut.conj (decPerm tauDec)).toMonoidHom =
      MulAut.conj (decPerm tauDec) • decSubgroup l1Decs := by
    rw [Subgroup.pointwise_smul_def]
    rfl
  change D.pull (decSubgroup m21Decs) =
    (D.pull (decSubgroup l1Decs)).map (MulAut.conj D.tauG).toMonoidHom
  calc
    D.pull (decSubgroup m21Decs) =
        D.pull ((decSubgroup l1Decs).map
          (MulAut.conj (decPerm tauDec)).toMonoidHom) := by rw [hmodel]
    _ = D.pull (MulAut.conj (decPerm tauDec) • decSubgroup l1Decs) := by rw [hsmul]
    _ = MulAut.conj (D.elt (decPerm tauDec) (D.decPerm_mem tauDec (by decide))) •
          D.pull (decSubgroup l1Decs) :=
          D.pull_conj (D.decPerm_mem tauDec (by decide)) hL1inv
    _ = (D.pull (decSubgroup l1Decs)).map (MulAut.conj D.tauG).toMonoidHom := by
          rw [Subgroup.pointwise_smul_def]
          rfl

theorem T0G_eq_sup (hF1 : F1Prop) (hF5 : F5Prop) :
    D.T0G = D.pull (decSubgroup l1Decs) ⊔ D.M2G := by
  have hmodel := T0_eq_sup_model hF1 hF5 D.card_T0
  have hL := l1_le_invE D hF5
  have hM := m21_le_invE D hF5
  change D.pull (tabSubgroup t0Tabs) =
    D.pull (decSubgroup l1Decs) ⊔ D.pull (decSubgroup m21Decs)
  rw [← D.pull_sup hL hM, hmodel]

theorem L_le_T0G (hF5 : F5Prop) : D.pull (decSubgroup l1Decs) ≤ D.T0G := by
  have h5 := hF5
  simp only [F5Prop] at h5
  exact D.pull_mono h5.2.1

theorem M2G_le_T0G (hF5 : F5Prop) : D.M2G ≤ D.T0G := by
  have h5 := hF5
  simp only [F5Prop] at h5
  exact D.pull_mono h5.2.2.1

theorem card_M2G (hF1 : F1Prop) (hF5 : F5Prop) : Nat.card D.M2G = 16 := by
  rw [M2G, D.card_pull (m21_le_invE D hF5), card_M21 hF1 hF5 D.card_T0]

theorem isElemAbelian_M2G (hF1 : F1Prop) (hF5 : F5Prop) :
    CFSG.Open.IsElemAbelian 2 D.M2G :=
  (D.isElemAbelian_pull_iff (m21_le_invE D hF5)).mpr (by
    rw [M21_eq_map hF1 hF5 D.card_T0]
    exact CFSG.Open.IsElemAbelian.map (l1_elemAbelian hF1) _)

theorem card_inf_M2G (hF5 : F5Prop) :
    Nat.card ↥(D.pull (decSubgroup l1Decs) ⊓ D.M2G) = 4 := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨hZT, -, -, -, hLM, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  have hinf : decSubgroup l1Decs ⊓ decSubgroup m21Decs ≤ invE 1 :=
    le_trans inf_le_left (l1_le_invE D hF5)
  rw [M2G, ← D.pull_inf, D.card_pull hinf, hLM, hZT]

theorem inf_M2G_le_centralizer (hF5 : F5Prop) :
    D.pull (decSubgroup l1Decs) ⊓ D.M2G ≤ centralizer (D.T0G : Set G) := by
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, -, -, -, hLM, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  have hZ : Subgroup.centralizer (tabSubgroup t0Tabs :
      Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs ≤
      Subgroup.centralizer (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) :=
    inf_le_left
  have hp := D.pull_mono hZ
  rw [D.pull_centralizer (t0Tabs_le_invE D)] at hp
  have hgoal : D.pull (decSubgroup l1Decs) ⊓ D.M2G =
      D.pull (Subgroup.centralizer (tabSubgroup t0Tabs :
        Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs) := by
    rw [M2G, ← D.pull_inf, hLM]
  rw [hgoal]
  exact hp.trans inf_le_left

theorem mul_self_mem_inf_M2G (hF5 : F5Prop) :
    ∀ x ∈ D.T0G, x * x ∈ D.pull (decSubgroup l1Decs) ⊓ D.M2G := by
  intro x hx
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, -, -, -, hLM, -, -, -, -, -, -, -, -, -, hsq, -⟩ := h5
  set g : ↥(centralizer ({z} : Set G)) := ⟨x, D.pull_le_centralizer _ hx⟩ with hg
  have hxT : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup t0Tabs :=
    (D.coe_mem_pull_iff g).mp hx
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hxeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = x :=
    D.elt_coe_σ g
  rw [← hxeq, ← D.elt_mul _ _ (D.σ g).2 (D.σ g).2]
  rw [M2G, ← D.pull_inf]
  refine (D.elt_mem_pull_iff (mul_mem hu hu)).mpr ?_
  rw [hLM]
  exact hsq _ hxT

theorem mem_or_mem_M2G (hF5 : F5Prop) :
    ∀ x ∈ D.T0G, x * x = 1 → x ∈ D.pull (decSubgroup l1Decs) ∨ x ∈ D.M2G := by
  intro x hx hx2
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, -, -, -, -, hinv, -, -, -, -, -, -, -, -, -, -⟩ := h5
  by_cases hx1 : x = 1
  · left
    rw [hx1]
    exact (D.pull (decSubgroup l1Decs)).one_mem
  set g : ↥(centralizer ({z} : Set G)) := ⟨x, D.pull_le_centralizer _ hx⟩ with hg
  have hxT : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup t0Tabs :=
    (D.coe_mem_pull_iff g).mp hx
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hxeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = x :=
    D.elt_coe_σ g
  have h2 : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := by
    apply D.elt_injective
    trans D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2
    · exact D.elt_mul _ _ (D.σ g).2 (D.σ g).2
    · rw [hxeq, hx2]
      exact (D.elt_one).symm
  have hu1 : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    apply hx1
    exact hxeq.symm.trans ((D.elt_eq_of_eq (D.σ g).2 (one_mem (invE 1)) h).trans
      D.elt_one)
  rcases hinv _ hxT h2 hu1 with huL | huM
  · left
    rw [← hxeq]
    exact (D.elt_mem_pull_iff hu).mpr huL
  · right
    rw [← hxeq]
    exact (D.elt_mem_pull_iff hu).mpr huM


private theorem orderOf_t0 (D : LocalData G z) :
    orderOf (D.elt (permC 1782 w0T) D.w0_mem) = 2 := by
  rw [orderOf_eq_prime_iff]
  exact ⟨by rw [pow_two]; exact D.t0_mul_self, D.t0_ne_one⟩

private theorem mem_zpowers_of_sq_eq_one {u x : G} (h2 : u * u = 1) (h1 : u ≠ 1) :
    x ∈ Subgroup.zpowers u ↔ x = 1 ∨ x = u := by
  have horder : orderOf u = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact h2, h1⟩
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hz : u ^ (k % (2 : ℤ)) = u ^ k := by
      have h := zpow_mod_orderOf u k
      rwa [horder] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1'
    · left
      rw [← hk, ← hz, h0]
      simp
    · right
      rw [← hk, ← hz, h1']
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.mem_zpowers_iff.mpr ⟨0, by simp⟩
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

private theorem commute_T0G_zpowers (D : LocalData G z) (a : G) (ha : a ∈ D.T0G)
    (b : G) (hb : b ∈ Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem)) :
    a * b = b * a := by
  have hat : Commute a (D.elt (permC 1782 w0T) D.w0_mem) :=
    mem_centralizer_singleton_iff.mp (D.TG_le_centralizer (T0G_le_TG D ha))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right hat k).eq

theorem mem_T1G_iff (x : G) :
    x ∈ D.T1G ↔ x ∈ D.T0G ∨ ∃ s ∈ D.T0G,
      x = D.elt (permC 1782 w0T) D.w0_mem * s := by
  have hcomm : ∀ a ∈ D.T0G, ∀ b ∈ Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem),
      a * b = b * a := fun a ha b hb => commute_T0G_zpowers D a ha b hb
  have hzp : ∀ {b : G}, b ∈ Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem) ↔
      b = 1 ∨ b = D.elt (permC 1782 w0T) D.w0_mem :=
    fun {b} => mem_zpowers_of_sq_eq_one (D.t0_mul_self) (D.t0_ne_one)
  constructor
  · intro hx
    rw [T1G] at hx
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
    rcases hzp.mp hb with hb1 | hbt
    · left
      rw [← hab, hb1, mul_one]
      exact ha
    · right
      subst hbt
      refine ⟨a, ha, ?_⟩
      rw [← hab]
      exact hcomm a ha _ hb
  · rintro (hx | ⟨s, hs, rfl⟩)
    · rw [T1G]
      exact Subgroup.mem_sup_left hx
    · rw [T1G]
      rw [show D.elt (permC 1782 w0T) D.w0_mem * s =
          s * D.elt (permC 1782 w0T) D.w0_mem from (hcomm s hs _ (Subgroup.mem_zpowers _)).symm]
      exact Subgroup.mul_mem_sup hs (Subgroup.mem_zpowers _)

private theorem pull_zpowers_w0 (D : LocalData G z) :
    D.pull (Subgroup.zpowers (permC 1782 w0T)) =
      Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem) := by
  apply le_antisymm
  · intro g hg
    have hgC : g ∈ centralizer ({z} : Set G) := (D.mem_pull.mp hg).1
    have hσ : ((D.σ ⟨g, hgC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈
        Subgroup.zpowers (permC 1782 w0T) := (D.mem_pull.mp hg).2
    have hgeq : D.elt ((D.σ ⟨g, hgC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))
        (D.σ ⟨g, hgC⟩).2 = g := D.elt_coe_σ ⟨g, hgC⟩
    rcases (mem_zpowers_of_sq_eq_one D.w0_mul_self D.w0_ne_one).mp hσ with h1 | hW
    · rw [Subgroup.mem_zpowers_iff]
      refine ⟨0, ?_⟩
      rw [zpow_zero]
      calc (1 : G) = D.elt 1 (one_mem (invE 1)) := D.elt_one.symm
        _ = D.elt ((D.σ ⟨g, hgC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))
              (D.σ ⟨g, hgC⟩).2 :=
            (D.elt_eq_of_eq (D.σ ⟨g, hgC⟩).2 (one_mem (invE 1)) h1).symm
        _ = g := hgeq
    · rw [Subgroup.mem_zpowers_iff]
      refine ⟨1, ?_⟩
      rw [zpow_one]
      calc D.elt (permC 1782 w0T) D.w0_mem =
            D.elt ((D.σ ⟨g, hgC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))
              (D.σ ⟨g, hgC⟩).2 :=
            (D.elt_eq_of_eq (D.σ ⟨g, hgC⟩).2 D.w0_mem hW).symm
        _ = g := hgeq
  · intro g hg
    have ht0mem : D.elt (permC 1782 w0T) D.w0_mem ∈
        D.pull (Subgroup.zpowers (permC 1782 w0T)) :=
      (D.elt_mem_pull_iff D.w0_mem).mpr
        (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    exact (Subgroup.zpowers_le.mpr ht0mem) hg

private theorem elt_mem_T1G_iff (D : LocalData G z)
    {x : Equiv.Perm (Fin 1782)} (hx : x ∈ invE 1) :
    D.elt x hx ∈ D.T1G ↔
      x ∈ tabSubgroup t0Tabs ∨ ∃ s ∈ tabSubgroup t0Tabs, x = permC 1782 w0T * s := by
  have hzpow : Subgroup.zpowers (permC 1782 w0T) ≤ invE 1 :=
    Subgroup.zpowers_le.mpr D.w0_mem
  have hcomm : ∀ a ∈ tabSubgroup t0Tabs,
      ∀ b ∈ Subgroup.zpowers (permC 1782 w0T), a * b = b * a := by
    intro a ha b hb
    have hWcomm : a * permC 1782 w0T = permC 1782 w0T * a := by
      have hav : a ∈ tabSubgroup v0Tabs := D.tabSubgroup_t0Tabs_le ha
      exact mem_centralizer_singleton_iff.mp
        (mem_inf.mp (D.tabSubgroup_v0Tabs ▸ hav)).1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right hWcomm k).eq
  have hpull : D.T1G =
      D.pull (tabSubgroup t0Tabs ⊔ Subgroup.zpowers (permC 1782 w0T)) := by
    change D.pull (tabSubgroup t0Tabs) ⊔
      Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem) = _
    rw [D.pull_sup (t0Tabs_le_invE D) hzpow, pull_zpowers_w0 D]
  rw [hpull, D.elt_mem_pull_iff hx]
  constructor
  · intro hmem
    obtain ⟨u, hu, v, hv, huv⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (A := tabSubgroup t0Tabs)
        (B := Subgroup.zpowers (permC 1782 w0T)) hcomm hmem
    rcases (mem_zpowers_of_sq_eq_one D.w0_mul_self D.w0_ne_one).mp hv with hv1 | hvW
    · left
      rw [← huv, hv1, mul_one]
      exact hu
    · right
      refine ⟨u, hu, ?_⟩
      rw [← huv, hvW]
      exact hcomm u hu (permC 1782 w0T) (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  · rintro (hxT | ⟨s, hs, rfl⟩)
    · exact Subgroup.mem_sup_left hxT
    · have hsW : s * permC 1782 w0T = permC 1782 w0T * s :=
        hcomm s hs (permC 1782 w0T) (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
      rw [← hsW]
      exact Subgroup.mul_mem_sup hs (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)

theorem T1G_le_TG : D.T1G ≤ D.TG := by
  rw [T1G]
  exact sup_le (T0G_le_TG D) (Subgroup.zpowers_le.mpr (t0_mem_TG D))

private theorem card_T1G (hF3 : F3Prop) (hF4 : F4Prop) : Nat.card D.T1G = 128 := by
  have hcardz : Nat.card ↥(Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem)) = 2 := by
    rw [Nat.card_zpowers, orderOf_t0 D]
  have hdisj : Disjoint D.T0G
      (Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem)) := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr ?_
    intro x hx
    obtain ⟨hxT, hxz⟩ := mem_inf.mp hx
    rcases (mem_zpowers_of_sq_eq_one (D.t0_mul_self) (D.t0_ne_one)).mp hxz with h1 | ht
    · rwa [Subgroup.mem_bot, h1]
    · exfalso
      have ht' : x = D.elt (permC 1782 w0T) D.w0_mem := ht
      exact t0_not_mem_T0G D hF3 hF4 (ht' ▸ hxT)
  have hnorm : Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem) ≤
      Subgroup.normalizer (D.T0G : Set G) := by
    refine Subgroup.zpowers_le.mpr ((Subgroup.centralizer_le_normalizer _)
      (Subgroup.mem_centralizer_iff.mpr ?_))
    intro h hh
    exact mem_centralizer_singleton_iff.mp
      (D.TG_le_centralizer (T0G_le_TG D hh))
  change Nat.card ↥(D.T0G ⊔
    Subgroup.zpowers (D.elt (permC 1782 w0T) D.w0_mem)) = 128
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    card_T0G D, hcardz]

theorem relIndex_T1G (hF3 : F3Prop) (hF4 : F4Prop) : D.T1G.relIndex D.TG = 4 := by
  have hcard := Subgroup.relIndex_mul_card D.T1G D.TG
  rw [inf_eq_left.mpr (T1G_le_TG D), card_T1G D hF3 hF4, card_TG D hF3] at hcard
  omega

private theorem f8_lam_data (hF8 : F8Prop) :
    decPerm lam0Dec ∈ tabSubgroup v0Tabs ∧
      decPerm lam0Dec * decPerm lam0Dec = permC 1782 w0T := by
  have h8 := hF8
  simp only [F8Prop] at h8
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hV, h2⟩ := h8
  exact ⟨hV, h2⟩

private theorem f8_a_data (hF8 : F8Prop) :
    decPerm aDec ∈ tabSubgroup v0Tabs ∧ decPerm aDec * decPerm aDec = 1 ∧
      decPerm aDec ≠ 1 ∧ decPerm aDec ≠ permC 1782 w0T ∧
      fixedCard (decPerm aDec) = 42 ∧
      fixedCard (decPerm aDec * permC 1782 w0T) = 42 := by
  have h8 := hF8
  simp only [F8Prop] at h8
  obtain ⟨-, -, -, -, hV, h2, h1, hW, hfix, hfixW, -, -⟩ := h8
  exact ⟨hV, h2, h1, hW, hfix, hfixW⟩

theorem lamG_mem_TG (hF8 : F8Prop) : D.lamG ∈ D.TG :=
  (D.elt_mem_pull_iff (D.decPerm_mem lam0Dec (by decide))).mpr (f8_lam_data hF8).1

theorem lamG_mul_self (hF8 : F8Prop) :
    D.lamG * D.lamG = D.elt (permC 1782 w0T) D.w0_mem := by
  have h := (f8_lam_data hF8).2
  have hmem : decPerm lam0Dec * decPerm lam0Dec ∈ invE 1 :=
    mul_mem (D.decPerm_mem lam0Dec (by decide)) (D.decPerm_mem lam0Dec (by decide))
  change D.elt (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide)) *
      D.elt (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide)) =
      D.elt (permC 1782 w0T) D.w0_mem
  rw [← D.elt_mul (decPerm lam0Dec) (decPerm lam0Dec)
    (D.decPerm_mem lam0Dec (by decide)) (D.decPerm_mem lam0Dec (by decide))]
  exact D.elt_eq_of_eq hmem D.w0_mem h

theorem mul_lamG_inv_mem_T1G (hF8 : F8Prop) :
    ∀ x ∈ D.TG, x * x = D.elt (permC 1782 w0T) D.w0_mem → x * D.lamG⁻¹ ∈ D.T1G := by
  intro x hx hx2
  have h8 := hF8
  simp only [F8Prop] at h8
  have hthird := h8.2.2.1
  have hxC : x ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup v0Tabs) hx
  set g : ↥(centralizer ({z} : Set G)) := ⟨x, hxC⟩ with hg
  have hxV : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup v0Tabs :=
    (D.coe_mem_pull_iff g).mp hx
  have hxeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = x :=
    D.elt_coe_σ g
  have hsq : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = permC 1782 w0T := by
    apply D.elt_injective
    trans D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2
    · exact D.elt_mul _ _ (D.σ g).2 (D.σ g).2
    · rw [hxeq, hx2]
  have h11 : (D.σ g : ↥(invE 1)) * (D.σ g : ↥(invE 1)) = ⟨permC 1782 w0T, D.w0_mem⟩ :=
    Subtype.ext hsq
  have hthird' := hthird (D.σ g) hxV hsq
  have hmem_lam : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      (decPerm lam0Dec)⁻¹ ∈ invE 1 :=
    mul_mem (D.σ g).2 (inv_mem (D.decPerm_mem lam0Dec (by decide)))
  have hxlam : x * D.lamG⁻¹ =
      D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        (decPerm lam0Dec)⁻¹) hmem_lam := by
    rw [← hxeq]
    change D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        (D.elt (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide)))⁻¹ = _
    rw [← D.elt_inv (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide))]
    rw [← D.elt_mul _ _ (D.σ g).2 (inv_mem (D.decPerm_mem lam0Dec (by decide)))]
  rw [hxlam]
  exact (D.elt_mem_T1G_iff hmem_lam).mpr hthird'

theorem aG_mem_TG (hF8 : F8Prop) : D.aG ∈ D.TG :=
  (D.elt_mem_pull_iff (D.decPerm_mem aDec (by decide))).mpr (f8_a_data hF8).1

theorem aG_mul_self (hF8 : F8Prop) : D.aG * D.aG = 1 := by
  have h := (f8_a_data hF8).2.1
  have hmem : decPerm aDec * decPerm aDec ∈ invE 1 :=
    mul_mem (D.decPerm_mem aDec (by decide)) (D.decPerm_mem aDec (by decide))
  change D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide)) *
      D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide)) = 1
  rw [← D.elt_mul (decPerm aDec) (decPerm aDec)
    (D.decPerm_mem aDec (by decide)) (D.decPerm_mem aDec (by decide))]
  exact (D.elt_eq_of_eq hmem (one_mem (invE 1)) h).trans D.elt_one

theorem aG_ne_one (hF8 : F8Prop) : D.aG ≠ 1 := by
  intro h
  have h' : D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide)) =
      D.elt 1 (one_mem (invE 1)) := by
    rw [D.elt_one]
    exact h
  exact (f8_a_data hF8).2.2.1 (D.elt_injective h')

theorem aG_ne_t0 (hF8 : F8Prop) :
    D.aG ≠ D.elt (permC 1782 w0T) D.w0_mem := by
  intro h
  have h' : D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide)) =
      D.elt (permC 1782 w0T) D.w0_mem := h
  exact (f8_a_data hF8).2.2.2.1 (D.elt_injective h')

theorem not_isConj_aG (hF8 : F8Prop) : ¬ IsConj D.aG z := by
  rw [D.not_isConj_elt_iff (D.decPerm_mem aDec (by decide))
    (f8_a_data hF8).2.1 (f8_a_data hF8).2.2.1]
  exact (f8_a_data hF8).2.2.2.2.1

theorem not_isConj_aG_mul_t0 (hF8 : F8Prop) :
    ¬ IsConj (D.aG * D.elt (permC 1782 w0T) D.w0_mem) z := by
  have hdata := f8_a_data hF8
  have hmem : decPerm aDec * permC 1782 w0T ∈ invE 1 :=
    mul_mem (D.decPerm_mem aDec (by decide)) D.w0_mem
  have hsq : (decPerm aDec * permC 1782 w0T) * (decPerm aDec * permC 1782 w0T) = 1 := by
    have hcomm : decPerm aDec * permC 1782 w0T = permC 1782 w0T * decPerm aDec := by
      exact mem_centralizer_singleton_iff.mp
        (mem_inf.mp (D.tabSubgroup_v0Tabs ▸ hdata.1)).1
    calc (decPerm aDec * permC 1782 w0T) * (decPerm aDec * permC 1782 w0T)
        = decPerm aDec * (permC 1782 w0T * decPerm aDec) * permC 1782 w0T := by group
      _ = decPerm aDec * (decPerm aDec * permC 1782 w0T) * permC 1782 w0T := by
          rw [hcomm.symm]
      _ = (decPerm aDec * decPerm aDec) * (permC 1782 w0T * permC 1782 w0T) := by group
      _ = 1 := by rw [hdata.2.1, D.w0_mul_self, mul_one]
  have hne : decPerm aDec * permC 1782 w0T ≠ 1 := by
    intro h
    apply hdata.2.2.2.1
    calc decPerm aDec = (decPerm aDec * permC 1782 w0T) * permC 1782 w0T := by
          rw [mul_assoc, D.w0_mul_self, mul_one]
      _ = permC 1782 w0T := by rw [h, one_mul]
  have hprod : D.aG * D.elt (permC 1782 w0T) D.w0_mem =
      D.elt (decPerm aDec * permC 1782 w0T) hmem := by
    change D.elt (decPerm aDec) (D.decPerm_mem aDec (by decide)) *
        D.elt (permC 1782 w0T) D.w0_mem = _
    rw [← D.elt_mul (decPerm aDec) (permC 1782 w0T)
      (D.decPerm_mem aDec (by decide)) D.w0_mem]
  rw [hprod, D.not_isConj_elt_iff hmem hsq hne]
  exact hdata.2.2.2.2.2

theorem not_mem_T1G_of_not_isConj (hF8 : F8Prop) :
    ∀ y ∈ D.TG, y * y = 1 → y ≠ 1 → y ≠ D.elt (permC 1782 w0T) D.w0_mem →
      ¬ IsConj y z → ¬ IsConj (y * D.elt (permC 1782 w0T) D.w0_mem) z →
      y ∉ D.T1G ∧ y * D.lamG⁻¹ ∉ D.T1G := by
  intro y hy hy2 hy1 hyt hyP hyPt
  have h8 := hF8
  simp only [F8Prop] at h8
  have hfourth := h8.2.2.2.1
  have hyC : y ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup v0Tabs) hy
  set g : ↥(centralizer ({z} : Set G)) := ⟨y, hyC⟩ with hg
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hyV : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup v0Tabs :=
    (D.coe_mem_pull_iff g).mp hy
  have hyeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = y :=
    D.elt_coe_σ g
  have hy2' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := by
    apply D.elt_injective
    trans D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2
    · exact D.elt_mul _ _ (D.σ g).2 (D.σ g).2
    · rw [hyeq, hy2]
      exact (D.elt_one).symm
  have hy1' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    apply hy1
    exact hyeq.symm.trans ((D.elt_eq_of_eq (D.σ g).2 (one_mem (invE 1)) h).trans
      D.elt_one)
  have hyt' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ permC 1782 w0T := by
    intro h
    apply hyt
    exact hyeq.symm.trans (D.elt_eq_of_eq (D.σ g).2 D.w0_mem h)
  have hyP' : ¬ IsConj (D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))
      (D.σ g).2) z := by rwa [hyeq]
  have hfix : fixedCard ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 42 :=
    (D.not_isConj_elt_iff hu hy2' hy1').mp hyP'
  have hfixW : fixedCard (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      permC 1782 w0T) = 42 := by
    have hup : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        permC 1782 w0T ∈ invE 1 := mul_mem hu D.w0_mem
    have hcommW : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T =
        permC 1782 w0T * ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := by
      exact mem_centralizer_singleton_iff.mp
        (mem_inf.mp (D.tabSubgroup_v0Tabs ▸ hyV)).1
    have hsqW : (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) *
        (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) = 1 := by
      calc (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) *
          (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T)
          = ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
              (permC 1782 w0T * ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))) *
            permC 1782 w0T := by group
        _ = ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
              (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) *
            permC 1782 w0T := by rw [hcommW.symm]
        _ = (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
              ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))) *
            (permC 1782 w0T * permC 1782 w0T) := by group
        _ = 1 := by rw [hy2', D.w0_mul_self, mul_one]
    have hneW : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T ≠ 1 := by
      intro h
      apply hyt'
      calc ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))
          = (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) *
              permC 1782 w0T := by rw [mul_assoc, D.w0_mul_self, mul_one]
        _ = permC 1782 w0T := by rw [h, one_mul]
    have hprodeq : D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * permC 1782 w0T) hup =
        y * D.elt (permC 1782 w0T) D.w0_mem := by
      rw [← hyeq]
      rw [← D.elt_mul ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))
        (permC 1782 w0T) (D.σ g).2 D.w0_mem]
    have hyPt' : ¬ IsConj (D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        permC 1782 w0T) hup) z := by rwa [hprodeq]
    exact (D.not_isConj_elt_iff hup hsqW hneW).mp hyPt'
  have hinv := hfourth _ hyV hy2' hy1' hyt' hfix hfixW
  constructor
  · intro hmem
    exact hinv.1 ((D.elt_mem_T1G_iff hu).mp (hyeq.symm ▸ hmem))
  · intro hmem
    have hmem_lam : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        (decPerm lam0Dec)⁻¹ ∈ invE 1 :=
      mul_mem hu (inv_mem (D.decPerm_mem lam0Dec (by decide)))
    have hmem' : D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        (decPerm lam0Dec)⁻¹) hmem_lam ∈ D.T1G := by
      have hconv : D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
          (decPerm lam0Dec)⁻¹) hmem_lam = y * D.lamG⁻¹ := by
        rw [← hyeq]
        change D.elt (((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
            (decPerm lam0Dec)⁻¹) hmem_lam =
          D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
            (D.elt (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide)))⁻¹
        rw [← D.elt_inv (decPerm lam0Dec) (D.decPerm_mem lam0Dec (by decide))]
        rw [← D.elt_mul _ _ (D.σ g).2 (inv_mem (D.decPerm_mem lam0Dec (by decide)))]
      rw [hconv]
      exact hmem
    exact hinv.2 ((D.elt_mem_T1G_iff hmem_lam).mp hmem')


theorem conj_mem_T1G (hF8 : F8Prop) :
    ∀ g ∈ D.TG, ∀ x ∈ D.T1G, g * x * g⁻¹ ∈ D.T1G := by
  intro g hg x hx
  have h8 := hF8
  simp only [F8Prop] at h8
  have hconj := h8.1
  have hgC : g ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup v0Tabs) hg
  have hxC : x ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup v0Tabs) (T1G_le_TG D hx)
  set u : ↥(invE 1) := D.σ ⟨g, hgC⟩ with hu
  set y : ↥(invE 1) := D.σ ⟨x, hxC⟩ with hy
  have hgV : (u : Equiv.Perm (Fin 1782)) ∈ tabSubgroup v0Tabs :=
    (D.coe_mem_pull_iff ⟨g, hgC⟩).mp hg
  have hxT : (y : Equiv.Perm (Fin 1782)) ∈
      {w | w ∈ tabSubgroup t0Tabs ∨ ∃ t ∈ tabSubgroup t0Tabs,
        w = permC 1782 w0T * t} :=
    (D.elt_mem_T1G_iff y.2).mp (by rw [D.elt_coe_σ ⟨x, hxC⟩]; exact hx)
  have hconj' := hconj u hgV y hxT
  have hmem : (u : Equiv.Perm (Fin 1782)) * (y : Equiv.Perm (Fin 1782)) *
      ((u : Equiv.Perm (Fin 1782)))⁻¹ ∈ invE 1 :=
    mul_mem (mul_mem u.2 y.2) (inv_mem u.2)
  have hgeq : D.elt (u : Equiv.Perm (Fin 1782)) u.2 = g := by
    rw [hu]
    exact D.elt_coe_σ ⟨g, hgC⟩
  have hxeq : D.elt (y : Equiv.Perm (Fin 1782)) y.2 = x := by
    rw [hy]
    exact D.elt_coe_σ ⟨x, hxC⟩
  have hc : g * x * g⁻¹ = D.elt ((u : Equiv.Perm (Fin 1782)) *
      (y : Equiv.Perm (Fin 1782)) * ((u : Equiv.Perm (Fin 1782)))⁻¹) hmem := by
    rw [← hgeq, ← hxeq]
    rw [← D.elt_mul (u : Equiv.Perm (Fin 1782)) (y : Equiv.Perm (Fin 1782)) u.2 y.2]
    rw [← D.elt_inv (u : Equiv.Perm (Fin 1782)) u.2]
    rw [← D.elt_mul ((u : Equiv.Perm (Fin 1782)) * (y : Equiv.Perm (Fin 1782)))
      ((u : Equiv.Perm (Fin 1782)))⁻¹ (mul_mem u.2 y.2) (inv_mem u.2)]
  rw [hc]
  exact (D.elt_mem_T1G_iff hmem).mpr hconj'

theorem centralizer_inf_T0G_L (hF1 : F1Prop) (hF5 : F5Prop) :
    ∀ x ∈ D.pull (decSubgroup l1Decs),
      x ∉ D.pull (decSubgroup l1Decs) ⊓ D.M2G →
      centralizer ({x} : Set G) ⊓ D.T0G = D.pull (decSubgroup l1Decs) := by
  intro x hxL hxinf
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, hL1T0, -, -, hLM, -, -, hcentL, -, -, -, -, -, -, -, -⟩ := h5
  have hxC : x ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup t0Tabs) (L_le_T0G D hF5 hxL)
  set g : ↥(centralizer ({z} : Set G)) := ⟨x, hxC⟩ with hg
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ decSubgroup l1Decs :=
    (D.coe_mem_pull_iff g).mp hxL
  have huinv : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hxeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = x :=
    D.elt_coe_σ g
  have huNot : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∉
      decSubgroup l1Decs ⊓ decSubgroup m21Decs := by
    intro h
    apply hxinf
    rw [M2G, ← D.pull_inf, ← hxeq]
    exact (D.elt_mem_pull_iff huinv).mpr h
  have huZT : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∉
      Subgroup.centralizer (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) ⊓
        tabSubgroup t0Tabs := by
    rwa [← hLM]
  have hcent := hcentL _ hu huZT
  haveI : IsMulCommutative ↥(decSubgroup l1Decs) := (l1_elemAbelian hF1).1
  have hL1le : decSubgroup l1Decs ≤
      Subgroup.centralizer ({((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))} :
        Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs := by
    refine le_inf ?_ hL1T0
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨l, hl⟩ : ↥(decSubgroup l1Decs))
      ⟨_, hu⟩)
  have hEq : decSubgroup l1Decs =
      Subgroup.centralizer ({((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))} :
        Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs :=
    Subgroup.eq_of_le_of_card_ge hL1le (by rw [hcent, l1_card hF1])
  have hpull : D.pull (decSubgroup l1Decs) =
      D.pull (Subgroup.centralizer ({((D.σ g : ↥(invE 1)) :
        Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓
        tabSubgroup t0Tabs) := by rw [hEq]
  rw [hpull, D.pull_inf, D.pull_centralizer_singleton huinv]
  rw [inf_assoc, inf_eq_right.mpr (D.pull_le_centralizer (tabSubgroup t0Tabs))]
  rw [← hxeq]

theorem centralizer_inf_T0G_M2G (hF1 : F1Prop) (hF5 : F5Prop) :
    ∀ y ∈ D.M2G, y ∉ D.pull (decSubgroup l1Decs) ⊓ D.M2G →
      centralizer ({y} : Set G) ⊓ D.T0G = D.M2G := by
  intro y hyM hyinf
  have h5 := hF5
  simp only [F5Prop] at h5
  obtain ⟨-, hL1T0, hM21T0, -, hLM, -, -, -, hcentM, -, -, -, -, -, -, -⟩ := h5
  have hM21ea : CFSG.Open.IsElemAbelian 2 (decSubgroup m21Decs) := by
    rw [M21_eq_map hF1 hF5 D.card_T0]
    exact CFSG.Open.IsElemAbelian.map (l1_elemAbelian hF1) _
  have hyC : y ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup t0Tabs) (M2G_le_T0G D hF5 hyM)
  set g : ↥(centralizer ({z} : Set G)) := ⟨y, hyC⟩ with hg
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ decSubgroup m21Decs :=
    (D.coe_mem_pull_iff g).mp hyM
  have huinv : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hyeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = y :=
    D.elt_coe_σ g
  have huNot : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∉
      decSubgroup l1Decs ⊓ decSubgroup m21Decs := by
    intro h
    apply hyinf
    rw [M2G, ← D.pull_inf, ← hyeq]
    exact (D.elt_mem_pull_iff huinv).mpr h
  have huZT : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∉
      Subgroup.centralizer (tabSubgroup t0Tabs : Set (Equiv.Perm (Fin 1782))) ⊓
        tabSubgroup t0Tabs := by
    rwa [← hLM]
  have hcent := hcentM _ hu huZT
  haveI : IsMulCommutative ↥(decSubgroup m21Decs) := hM21ea.1
  have hMle : decSubgroup m21Decs ≤
      Subgroup.centralizer ({((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))} :
        Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs := by
    refine le_inf ?_ hM21T0
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨l, hl⟩ : ↥(decSubgroup m21Decs))
      ⟨_, hu⟩)
  have hEq : decSubgroup m21Decs =
      Subgroup.centralizer ({((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))} :
        Set (Equiv.Perm (Fin 1782))) ⊓ tabSubgroup t0Tabs :=
    Subgroup.eq_of_le_of_card_ge hMle (by rw [hcent, card_M21 hF1 hF5 D.card_T0])
  have hpull : D.M2G =
      D.pull (Subgroup.centralizer ({((D.σ g : ↥(invE 1)) :
        Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓
        tabSubgroup t0Tabs) := by rw [M2G, hEq]
  rw [hpull, D.pull_inf, D.pull_centralizer_singleton huinv]
  rw [inf_assoc, inf_eq_right.mpr (D.pull_le_centralizer (tabSubgroup t0Tabs))]
  rw [← hyeq]

theorem mem_T0G_of_isConj (hF4 : F4Prop) :
    ∀ y ∈ D.TG, y * y = 1 → y ≠ 1 → IsConj y z → y ∈ D.T0G := by
  intro y hy hy2 hy1 hyP
  have h4 := hF4
  simp only [F4Prop] at h4
  obtain ⟨-, hsecond, -, -⟩ := h4
  have hyC : y ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup v0Tabs) hy
  set g : ↥(centralizer ({z} : Set G)) := ⟨y, hyC⟩ with hg
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup v0Tabs :=
    (D.coe_mem_pull_iff g).mp hy
  have huE : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hyeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = y :=
    D.elt_coe_σ g
  have hy2' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := by
    apply D.elt_injective
    trans D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2
    · exact D.elt_mul _ _ (D.σ g).2 (D.σ g).2
    · rw [hyeq, hy2]
      exact (D.elt_one).symm
  have hy1' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    apply hy1
    exact hyeq.symm.trans ((D.elt_eq_of_eq (D.σ g).2 (one_mem (invE 1)) h).trans
      D.elt_one)
  have hP' : IsConj (D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782))
      (D.σ g).2) z := by rwa [hyeq]
  have hfix : fixedCard ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 54 :=
    (D.isConj_elt_iff huE hy2' hy1').mp hP'
  have hfix' := hsecond (⟨_, hu⟩ : ↥(tabSubgroup v0Tabs)) (Subtype.ext hy2')
    (by intro hc; exact hy1' (congrArg Subtype.val hc)) hfix
  rw [← hyeq]
  exact (D.elt_mem_pull_iff huE).mpr hfix'

theorem isConj_of_mem_T0G (hF4 : F4Prop) :
    ∀ x ∈ D.T0G, x * x = 1 → x ≠ 1 → IsConj x z := by
  intro x hx hx2 hx1
  have h4 := hF4
  simp only [F4Prop] at h4
  obtain ⟨-, -, -, hlast⟩ := h4
  have hxC : x ∈ centralizer ({z} : Set G) :=
    D.pull_le_centralizer (tabSubgroup t0Tabs) hx
  set g : ↥(centralizer ({z} : Set G)) := ⟨x, hxC⟩ with hg
  have hu : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup t0Tabs :=
    (D.coe_mem_pull_iff g).mp hx
  have huE : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ invE 1 := (D.σ g).2
  have hxeq : D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 = x :=
    D.elt_coe_σ g
  have hx2' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := by
    apply D.elt_injective
    trans D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2 *
        D.elt ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) (D.σ g).2
    · exact D.elt_mul _ _ (D.σ g).2 (D.σ g).2
    · rw [hxeq, hx2]
      exact (D.elt_one).symm
  have hx1' : ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    apply hx1
    exact hxeq.symm.trans ((D.elt_eq_of_eq (D.σ g).2 (one_mem (invE 1)) h).trans
      D.elt_one)
  have hfix : fixedCard ((D.σ g : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 54 :=
    hlast (⟨_, hu⟩ : ↥(tabSubgroup t0Tabs)) (Subtype.ext hx2')
      (by intro hc; exact hx1' (congrArg Subtype.val hc))
  have hconj := (D.isConj_elt_iff huE hx2' hx1').mpr hfix
  rwa [hxeq] at hconj

theorem T0G_le_closure (hF1 : F1Prop) (hF4 : F4Prop) (hF5 : F5Prop) :
    D.T0G ≤ Subgroup.closure {y | y ∈ D.T0G ∧ y * y = 1 ∧ IsConj y z} := by
  have hLea : CFSG.Open.IsElemAbelian 2 (D.pull (decSubgroup l1Decs)) :=
    (D.isElemAbelian_pull_iff (l1_le_invE D hF5)).mpr (l1_elemAbelian hF1)
  have hMea : CFSG.Open.IsElemAbelian 2 D.M2G := isElemAbelian_M2G D hF1 hF5
  have hL : D.pull (decSubgroup l1Decs) ≤
      Subgroup.closure {y | y ∈ D.T0G ∧ y * y = 1 ∧ IsConj y z} := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact (Subgroup.closure _).one_mem
    · have hxT := L_le_T0G D hF5 hx
      have hx2 : x * x = 1 := by
        have h := hLea.2 x hx
        rwa [pow_two] at h
      exact Subgroup.subset_closure ⟨hxT, hx2, isConj_of_mem_T0G D hF4 x hxT hx2 hx1⟩
  have hM : D.M2G ≤ Subgroup.closure {y | y ∈ D.T0G ∧ y * y = 1 ∧ IsConj y z} := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact (Subgroup.closure _).one_mem
    · have hxT := M2G_le_T0G D hF5 hx
      have hx2 : x * x = 1 := by
        have h := hMea.2 x hx
        rwa [pow_two] at h
      exact Subgroup.subset_closure ⟨hxT, hx2, isConj_of_mem_T0G D hF4 x hxT hx2 hx1⟩
  calc D.T0G = D.pull (decSubgroup l1Decs) ⊔ D.M2G := T0G_eq_sup D hF1 hF5
    _ ≤ Subgroup.closure {y | y ∈ D.T0G ∧ y * y = 1 ∧ IsConj y z} := sup_le hL hM

theorem eq_or_eq_of_le_T0G (hF1 : F1Prop) (hF5 : F5Prop) {E : Subgroup G}
    (hE : E ≤ D.T0G) (hEa : CFSG.Open.IsElemAbelian 2 E) (hE16 : Nat.card E = 16) :
    E = D.pull (decSubgroup l1Decs) ∨ E = D.M2G := by
  haveI : Finite ↥(D.pull (decSubgroup l1Decs)) :=
    Finite.of_equiv ↥(decSubgroup l1Decs) (D.pullEquiv (l1_le_invE D hF5)).symm.toEquiv
  haveI : Finite ↥D.M2G :=
    Finite.of_equiv ↥(decSubgroup m21Decs) (D.pullEquiv (m21_le_invE D hF5)).symm.toEquiv
  have hLcard : Nat.card ↥(D.pull (decSubgroup l1Decs)) = 16 := by
    rw [D.card_pull (l1_le_invE D hF5), l1_card hF1]
  have hMcard : Nat.card ↥D.M2G = 16 := card_M2G D hF1 hF5
  have hunion : ∀ x ∈ E, x ∈ D.pull (decSubgroup l1Decs) ∨ x ∈ D.M2G := by
    intro x hxE
    have hxT := hE hxE
    have hx2 : x * x = 1 := by
      have h := hEa.2 x hxE
      rwa [pow_two] at h
    exact mem_or_mem_M2G D hF5 x hxT hx2
  have hle_or : E ≤ D.pull (decSubgroup l1Decs) ∨ E ≤ D.M2G := by
    by_contra h
    push Not at h
    obtain ⟨hEL, hEM⟩ := h
    have hEnotL : ¬ E ≤ D.pull (decSubgroup l1Decs) := hEL
    have hEnotM : ¬ E ≤ D.M2G := hEM
    obtain ⟨x, hxE, hxL⟩ := Set.not_subset.mp hEnotL
    obtain ⟨y, hyE, hyM⟩ := Set.not_subset.mp hEnotM
    have hxM : x ∈ D.M2G := (hunion x hxE).resolve_left hxL
    have hyL : y ∈ D.pull (decSubgroup l1Decs) := (hunion y hyE).resolve_right hyM
    have hxyE : x * y ∈ E := E.mul_mem hxE hyE
    have hxyL : x * y ∉ D.pull (decSubgroup l1Decs) := by
      intro h
      apply hxL
      rw [show x = (x * y) * y⁻¹ from by group]
      exact (D.pull (decSubgroup l1Decs)).mul_mem h
        ((D.pull (decSubgroup l1Decs)).inv_mem hyL)
    have hxyM : x * y ∉ D.M2G := by
      intro h
      apply hyM
      rw [show y = x⁻¹ * (x * y) from by group]
      exact D.M2G.mul_mem (D.M2G.inv_mem hxM) h
    exact (hunion (x * y) hxyE).elim hxyL hxyM
  rcases hle_or with hle | hle
  · left
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hLcard, hE16])
  · right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hMcard, hE16])

theorem L_le_centralizer_t0 (hF1M : F1MProp) (hF3 : F3Prop) :
    D.pull (decSubgroup l1Decs) ≤
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G) := by
  have h3 := hF3
  simp only [F3Prop] at h3
  obtain ⟨-, hM1, -, -, -⟩ := h3
  have hW1M : permC 1782 w0T ∈ decSubgroup m1Decs :=
    hM1 _ ⟨1, Subgroup.one_mem _, by group⟩
  have h1m := hF1M
  simp only [F1MProp] at h1m
  have hcen := h1m.2
  have hL1le : decSubgroup l1Decs ≤
      Subgroup.centralizer ({permC 1782 w0T} : Set (Equiv.Perm (Fin 1782))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hcen x).mp hx).2 _ hW1M
  have h := D.pull_mono hL1le
  rw [D.pull_centralizer_singleton D.w0_mem] at h
  exact h.trans inf_le_left

private theorem map_conj_centralizer_singleton (a s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj a).toMonoidHom =
      Subgroup.centralizer ({a * s * a⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc a * y * a⁻¹ * (a * s * a⁻¹) = a * (y * s) * a⁻¹ := by group
      _ = a * (s * y) * a⁻¹ := by rw [hy']
      _ = a * s * a⁻¹ * (a * y * a⁻¹) := by group
  · intro hx
    have hx' : x * (a * s * a⁻¹) = a * s * a⁻¹ * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨a⁻¹ * x * a, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (a⁻¹ * x * a) * s = a⁻¹ * (x * (a * s * a⁻¹)) * a := by group
        _ = a⁻¹ * (a * s * a⁻¹ * x) * a := by rw [hx']
        _ = s * (a⁻¹ * x * a) := by group
    · change a * (a⁻¹ * x * a) * a⁻¹ = x
      group

theorem card_centralizer_inf_of_isConj [Finite G] (hF3 : F3Prop) {e : G}
    (he : e ∈ centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G))
    (he2 : e * e = 1) (he1 : e ≠ 1) (hez : IsConj e z) :
    Nat.card ↥(centralizer ({e} : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) = 512 := by
  obtain ⟨a, ha⟩ := _root_.isConj_iff.mp hez.symm
  set s : G := a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a with hs
  have hsC : s ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he' : e * D.elt (permC 1782 w0T) D.w0_mem =
        D.elt (permC 1782 w0T) D.w0_mem * e :=
      mem_centralizer_singleton_iff.mp he
    have ht0e : D.elt (permC 1782 w0T) D.w0_mem * e =
        e * D.elt (permC 1782 w0T) D.w0_mem := he'.symm
    have hz : a⁻¹ * e * a = z := by rw [← ha]; group
    calc (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a) * z
        = a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * (a * z * a⁻¹) * a := by group
      _ = a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * e * a := by rw [ha]
      _ = a⁻¹ * (D.elt (permC 1782 w0T) D.w0_mem * e) * a := by group
      _ = a⁻¹ * (e * D.elt (permC 1782 w0T) D.w0_mem) * a := by rw [ht0e]
      _ = (a⁻¹ * e * a) * (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a) := by group
      _ = z * (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a) := by rw [hz]
  have hs2 : s * s = 1 := by
    rw [hs]
    calc (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a) *
        (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a)
        = a⁻¹ * (D.elt (permC 1782 w0T) D.w0_mem *
            D.elt (permC 1782 w0T) D.w0_mem) * a := by group
      _ = 1 := by rw [D.t0_mul_self]; group
  have hs1 : s ≠ 1 := by
    intro h
    apply D.t0_ne_one
    calc D.elt (permC 1782 w0T) D.w0_mem = a * s * a⁻¹ := by rw [hs]; group
      _ = 1 := by rw [h]; group
  have hsnot : ¬ IsConj s z := by
    intro hsc
    apply not_isConj_t0 D hF3
    have hmap : IsConj (a * s * a⁻¹) (a * z * a⁻¹) :=
      MonoidHom.map_isConj ((MulAut.conj a : G ≃* G) : G →* G) hsc
    have hsconj : a * s * a⁻¹ = D.elt (permC 1782 w0T) D.w0_mem := by
      rw [hs]; group
    have h1 : IsConj (D.elt (permC 1782 w0T) D.w0_mem) e := by
      have hmap' := hmap
      rw [hsconj, ha] at hmap'
      exact hmap'
    exact h1.trans hez
  have hcard := D.card_inf s hsC hs2 hs1 hsnot
  have hEq : (Subgroup.centralizer ({s} : Set G) ⊓
      Subgroup.centralizer ({z} : Set G)).map (MulAut.conj a).toMonoidHom =
      Subgroup.centralizer ({e} : Set G) ⊓
        Subgroup.centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective,
      map_conj_centralizer_singleton, map_conj_centralizer_singleton, ha]
    rw [show a * (a⁻¹ * D.elt (permC 1782 w0T) D.w0_mem * a) * a⁻¹ =
      D.elt (permC 1782 w0T) D.w0_mem from by group]
    rw [inf_comm]
  rw [← hEq, Subgroup.card_map_of_injective (MulAut.conj a).injective]
  exact hcard

theorem isPGroup_centralizer_inf_of_isConj [Finite G] (hF3 : F3Prop) {e : G}
    (he : e ∈ centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G))
    (he2 : e * e = 1) (he1 : e ≠ 1) (hez : IsConj e z) :
    IsPGroup 2 ↥(centralizer ({e} : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) :=
  IsPGroup.of_card (n := 9) (by
    rw [card_centralizer_inf_of_isConj D hF3 he he2 he1 hez]
    norm_num)

theorem oddOrderClosure_inf_TG [Finite G] (hF1 : F1Prop) (hF1M : F1MProp)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {f : G}
    (hfN : f ∈ normalizer (D.pull (decSubgroup l1Decs) : Set G)) (hf5 : orderOf f = 5)
    (hffix : ∀ l ∈ D.pull (decSubgroup l1Decs), f * l = l * f → l = 1)
    (hft : f * D.elt (permC 1782 w0T) D.w0_mem =
      D.elt (permC 1782 w0T) D.w0_mem * f) :
    CFSG.GroupTheory.oddOrderClosure
        (centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) ⊓ D.TG = D.T0G := by
  let P : G → Prop := fun g => IsConj g z
  have hP : ∀ g y : G, P (g * y * g⁻¹) ↔ P y := by
    intro g y
    constructor
    · intro h
      obtain ⟨c, hc⟩ := _root_.isConj_iff.mp h
      refine _root_.isConj_iff.mpr ⟨c * g, ?_⟩
      calc (c * g) * y * (c * g)⁻¹ = c * (g * y * g⁻¹) * c⁻¹ := by group
        _ = z := hc
    · intro h
      obtain ⟨c, hc⟩ := _root_.isConj_iff.mp h
      refine _root_.isConj_iff.mpr ⟨c * g⁻¹, ?_⟩
      calc (c * g⁻¹) * (g * y * g⁻¹) * (c * g⁻¹)⁻¹ = c * y * c⁻¹ := by group
        _ = z := hc
  have hLea : CFSG.Open.IsElemAbelian 2 (D.pull (decSubgroup l1Decs)) :=
    (D.isElemAbelian_pull_iff (l1_le_invE D hF5)).mpr (l1_elemAbelian hF1)
  haveI : IsMulCommutative ↥(D.pull (decSubgroup l1Decs)) := hLea.1
  have hL : ∀ x ∈ D.pull (decSubgroup l1Decs),
      ∀ y ∈ D.pull (decSubgroup l1Decs), x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(D.pull (decSubgroup l1Decs)))
      ⟨y, hy⟩)
  have hT0L : D.T0G ≤ D.pull (decSubgroup l1Decs) ⊔
      (D.pull (decSubgroup l1Decs)).map (MulAut.conj D.tauG).toMonoidHom := by
    rw [T0G_eq_sup D hF1 hF5, M2G_eq_map D hF1 hF5]
  exact oddOrderClosure_inf_eq P hP (TG_le_centralizer D) (isPGroup_TG D hF3)
    (not_two_dvd_relIndex_TG D hF3)
    (fun g hg => mem_centralizer_singleton_iff.mp hg) (t0_mem_TG D)
    (D.t0_mul_self) (t0_not_mem_T0G D hF3 hF4) (not_isConj_t0 D hF3)
    (T0G_le_TG D) (mem_T1G_iff D) (T1G_le_TG D) (conj_mem_T1G D hF8)
    (relIndex_T1G D hF3 hF4) (lamG_mem_TG D hF8) (lamG_mul_self D hF8)
    (mul_lamG_inv_mem_T1G D hF8) (aG_mem_TG D hF8) (aG_mul_self D hF8)
    (aG_ne_one D hF8) (aG_ne_t0 D hF8) (not_isConj_aG D hF8)
    (not_isConj_aG_mul_t0 D hF8) (not_mem_T1G_of_not_isConj D hF8)
    (mem_T0G_of_isConj D hF4) (T0G_le_closure D hF1 hF4 hF5)
    (L_le_centralizer_t0 D hF1M hF3) hL
    (mem_centralizer_singleton_iff.mpr hft) (by rw [hf5]; decide)
    (fun l hl => (Subgroup.mem_normalizer_iff.mp hfN l).mp hl) hffix
    (TG_le_centralizer D (tauG_mem_TG D hF5)) hT0L

end CFSG.Sporadic.SuzRecog.SuzL34.LocalData
