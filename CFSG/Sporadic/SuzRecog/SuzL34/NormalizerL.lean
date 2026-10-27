module

public import CFSG.Sporadic.SuzRecog.SuzL34.LocalData
public import CFSG.Sporadic.SuzRecog.SuzL34.ModelPi
public import CFSG.Sporadic.SuzRecog.LocalRFusion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] {z : G} (D : LocalData G z)

theorem decSubgroup_le_invE (D : LocalData G z) {l : List Dec}
    (h : ∀ d ∈ l, ∀ k ∈ d.1, k < 10) : decSubgroup l ≤ invE 1 := by
  rw [decSubgroup, Subgroup.closure_le]
  rintro _ ⟨d, hd, rfl⟩
  exact D.decPerm_mem d (h d hd)

noncomputable abbrev S : Subgroup G := D.pull (decSubgroup s1pDecs)

noncomputable abbrev M : Subgroup G := D.pull (decSubgroup m1Decs)

noncomputable abbrev L : Subgroup G := D.pull (decSubgroup l1Decs)

noncomputable abbrev t0 : G := D.elt (permC 1782 w0T) D.w0_mem

noncomputable def push (H : Subgroup G) : Subgroup (Equiv.Perm (Fin 1782)) :=
  (H.subgroupOf (centralizer ({z} : Set G))).map ((invE 1).subtype.comp D.σ.toMonoidHom)

theorem mem_push {H : Subgroup G} {x : Equiv.Perm (Fin 1782)} :
    x ∈ D.push H ↔ ∃ (g : G) (hg : g ∈ centralizer ({z} : Set G)), g ∈ H ∧
      ((D.σ ⟨g, hg⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = x := by
  rw [push, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨g, hg, hgH, hx⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgH, hx⟩

private theorem injective_subtype_comp :
    Function.Injective ((invE 1).subtype.comp D.σ.toMonoidHom) := by
  intro a b h
  exact D.σ.injective (Subtype.ext h)

theorem push_le_invE (H : Subgroup G) : D.push H ≤ invE 1 := by
  rintro _ ⟨y, -, rfl⟩
  exact (D.σ y).2

theorem pull_inf_invE (H : Subgroup (Equiv.Perm (Fin 1782))) :
    D.pull (H ⊓ invE 1) = D.pull H := by
  rw [D.pull_inf, D.pull_invE, inf_eq_left.mpr (D.pull_le_centralizer H)]

theorem card_pull_inf (H : Subgroup (Equiv.Perm (Fin 1782))) :
    Nat.card ↥(D.pull H) = Nat.card ↥(H ⊓ invE 1) := by
  rw [← D.pull_inf_invE H, D.card_pull inf_le_right]

theorem pull_push {H : Subgroup G} (hH : H ≤ centralizer ({z} : Set G)) :
    D.pull (D.push H) = H := by
  ext g
  rw [D.mem_pull]
  constructor
  · rintro ⟨hg, hx⟩
    obtain ⟨g', hg', hgH, heq⟩ := (D.mem_push).mp hx
    have h1 : (⟨g', hg'⟩ : ↥(centralizer ({z} : Set G))) = ⟨g, hg⟩ :=
      D.σ.injective (Subtype.ext heq)
    have h2 : g = g' := congrArg Subtype.val h1.symm
    rwa [h2]
  · intro hg
    exact ⟨hH hg, (D.mem_push).mpr ⟨g, hH hg, hg, rfl⟩⟩

theorem card_S (hF1 : F1Prop) : Nat.card D.S = 8192 := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨hS1card, -⟩ := h
  rw [D.card_pull (D.decSubgroup_le_invE (l := s1pDecs) (by decide))]
  exact hS1card

theorem card_M (hF1M : F1MProp) : Nat.card D.M = 1024 := by
  have h := hF1M
  dsimp only [F1MProp] at h
  rw [D.card_pull (D.decSubgroup_le_invE (l := m1Decs) (by decide))]
  exact h.1

theorem card_L (hF1 : F1Prop) : Nat.card D.L = 16 := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, -, -, -, -, hL1card, -, -⟩ := h
  rw [D.card_pull (D.decSubgroup_le_invE (l := l1Decs) (by decide))]
  exact hL1card

theorem isElemAbelian_L (hF1 : F1Prop) : IsElemAbelian 2 D.L := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, -, -, -, hL1ea, -⟩ := h
  exact (D.isElemAbelian_pull_iff (D.decSubgroup_le_invE (l := l1Decs) (by decide))).mpr hL1ea

theorem t1_central (D : LocalData G z) (hF1 : F1Prop) (y : Equiv.Perm (Fin 1782))
    (hy : y ∈ decSubgroup s1pDecs) :
    permC 1782 tTab * y = y * permC 1782 tTab := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, ht1S, hcent, -⟩ := h
  exact (hcent _ ht1S).mpr (Or.inr rfl) y hy

theorem t1_ne_one (D : LocalData G z) (hF1 : F1Prop) : permC 1782 tTab ≠ 1 := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨hcard, ht1S, hcent, -⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥(decSubgroup s1pDecs) :=
    IsPGroup.of_card (n := 13) (by rw [hcard]; norm_num)
  haveI : Nontrivial ↥(decSubgroup s1pDecs) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  haveI hcentn : Nontrivial ↥(Subgroup.center ↥(decSubgroup s1pDecs)) :=
    IsPGroup.center_nontrivial hpg
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center ↥(decSubgroup s1pDecs)))
  have hc1 : ((c : ↥(decSubgroup s1pDecs)) : Equiv.Perm (Fin 1782)) ≠ 1 :=
    fun h1 => hc (Subtype.ext (Subtype.ext h1))
  have hcomm : ∀ y ∈ decSubgroup s1pDecs,
      ((c : ↥(decSubgroup s1pDecs)) : Equiv.Perm (Fin 1782)) * y =
        y * ((c : ↥(decSubgroup s1pDecs)) : Equiv.Perm (Fin 1782)) := by
    intro y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩)).symm
  rcases (hcent _ (c : ↥(decSubgroup s1pDecs)).2).mp hcomm with h1 | h1
  · exact absurd h1 hc1
  · rw [← h1]
    exact hc1

theorem t1_mul_self (D : LocalData G z) (hF1 : F1Prop) :
    permC 1782 tTab * permC 1782 tTab = 1 := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, ht1S, hcent, -⟩ := h
  have hmem : permC 1782 tTab * permC 1782 tTab ∈ decSubgroup s1pDecs := mul_mem ht1S ht1S
  have hcomm : ∀ y ∈ decSubgroup s1pDecs,
      (permC 1782 tTab * permC 1782 tTab) * y =
        y * (permC 1782 tTab * permC 1782 tTab) := by
    intro y hy
    have hy1 := D.t1_central hF1 y hy
    calc (permC 1782 tTab * permC 1782 tTab) * y
        = permC 1782 tTab * (permC 1782 tTab * y) := by group
      _ = permC 1782 tTab * (y * permC 1782 tTab) := by rw [hy1]
      _ = (permC 1782 tTab * y) * permC 1782 tTab := by group
      _ = (y * permC 1782 tTab) * permC 1782 tTab := by rw [hy1]
      _ = y * (permC 1782 tTab * permC 1782 tTab) := by group
  rcases (hcent _ hmem).mp hcomm with h1 | h1
  · exact h1
  · exfalso
    have ht1 : permC 1782 tTab = 1 := by
      have h2 : permC 1782 tTab * permC 1782 tTab = 1 * permC 1782 tTab := by
        rw [one_mul]
        exact h1
      exact mul_right_cancel h2
    exact D.t1_ne_one hF1 ht1

theorem z_ne_one (D : LocalData G z) (hF1 : F1Prop) : z ≠ 1 := by
  intro h
  apply D.t1_ne_one hF1
  have h' : (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({z} : Set G))) = 1 :=
    Subtype.ext h
  have h4 : ((D.σ (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ :
      ↥(centralizer ({z} : Set G))) : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 :=
    (congrArg (fun t : ↥(invE 1) => (t : Equiv.Perm (Fin 1782))) (congrArg D.σ h')).trans
      (by rw [map_one]; rfl)
  rwa [D.map_z] at h4

theorem z_mem_L (hF1 : F1Prop) : z ∈ D.L := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, ht1S, -, -, -, -, -, hclass9⟩ := h
  have ht1L : permC 1782 tTab ∈ decSubgroup l1Decs := by
    by_contra hnot
    have h9 := hclass9 _ ht1S (D.t1_mul_self hF1) (D.t1_ne_one hF1) hnot
    have hset : {x : Equiv.Perm (Fin 1782) |
        ∃ g ∈ decSubgroup s1pDecs, x = g * permC 1782 tTab * g⁻¹} =
        {permC 1782 tTab} := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        rw [show g * permC 1782 tTab * g⁻¹ = permC 1782 tTab from ?_]
        · exact Set.mem_singleton _
        · calc g * permC 1782 tTab * g⁻¹ = permC 1782 tTab * g * g⁻¹ := by
                rw [← D.t1_central hF1 g hg]
            _ = permC 1782 tTab := by group
      · rintro rfl
        exact ⟨1, one_mem _, by group⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_singleton] at h9
    omega
  rw [← D.map_z] at ht1L
  exact (D.mem_pull).mpr ⟨mem_centralizer_singleton_iff.mpr rfl, ht1L⟩

theorem z_mem_S (hF1 : F1Prop) : z ∈ D.S := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, ht1S, -⟩ := h
  rw [← D.map_z] at ht1S
  exact (D.mem_pull).mpr ⟨mem_centralizer_singleton_iff.mpr rfl, ht1S⟩

theorem z_mem_center_S (hF1 : F1Prop) :
    (⟨z, D.z_mem_S hF1⟩ : ↥D.S) ∈ Subgroup.center ↥D.S := by
  rw [Subgroup.mem_center_iff]
  intro t
  apply Subtype.ext
  show (t : G) * z = z * (t : G)
  exact Subgroup.mem_centralizer_singleton_iff.mp (D.pull_le_centralizer _ t.2)

theorem center_S (hF1 : F1Prop) (s : ↥D.S) (hs : s ∈ Subgroup.center ↥D.S) :
    (s : G) = 1 ∨ (s : G) = z := by
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, ht1S, hcent, -⟩ := h
  have hS : decSubgroup s1pDecs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hcent' : D.pullEquiv hS s ∈ Subgroup.center ↥(decSubgroup s1pDecs) := by
    rw [Subgroup.mem_center_iff]
    intro t
    have hcomm : (D.pullEquiv hS).symm t * s = s * (D.pullEquiv hS).symm t :=
      Subgroup.mem_center_iff.mp hs _
    have := congrArg (D.pullEquiv hS) hcomm
    simpa using this
  have hcen : ∀ y ∈ decSubgroup s1pDecs,
      ((D.pullEquiv hS s : ↥(decSubgroup s1pDecs)) : Equiv.Perm (Fin 1782)) * y =
        y * ((D.pullEquiv hS s : ↥(decSubgroup s1pDecs)) : Equiv.Perm (Fin 1782)) := by
    intro y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent' ⟨y, hy⟩)).symm
  rcases (hcent _ (D.pullEquiv hS s).2).mp hcen with he | he
  · left
    have h' : D.pullEquiv hS s = D.pullEquiv hS 1 := by
      rw [show D.pullEquiv hS s = 1 from Subtype.ext he, map_one]
    have hs1 : s = 1 := (D.pullEquiv hS).injective h'
    rw [hs1]
    rfl
  · right
    have hz : D.pullEquiv hS ⟨z, D.z_mem_S hF1⟩ = ⟨permC 1782 tTab, ht1S⟩ := by
      apply Subtype.ext
      rw [D.coe_pullEquiv]
      exact D.map_z
    have h' : D.pullEquiv hS s = D.pullEquiv hS ⟨z, D.z_mem_S hF1⟩ := by
      rw [hz]
      exact Subtype.ext he
    have hs' : s = ⟨z, D.z_mem_S hF1⟩ := (D.pullEquiv hS).injective h'
    rw [hs']

theorem isSylow_S [Finite G] (hF1 : F1Prop) : ∃ P : Sylow 2 G, (P : Subgroup G) = D.S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : D.S ≤ centralizer ({z} : Set G) := D.pull_le_centralizer _
  have hScard : Nat.card D.S = 8192 := D.card_S hF1
  have hS2 : IsPGroup 2 (D.S : Subgroup G) :=
    IsPGroup.of_card (n := 13) (by rw [hScard]; norm_num)
  have hzS : z ∈ D.S := D.z_mem_S hF1
  refine ⟨⟨D.S, hS2, ?_⟩, rfl⟩
  intro Q hQ hSQ
  by_contra hne
  have hlt : D.S < Q := lt_of_le_of_ne hSQ (Ne.symm hne)
  obtain ⟨l, hlQ, hlS, hlN⟩ :=
    CFSG.Sporadic.SuzRecog.LocalR.exists_mem_normalizer_of_lt hQ hlt
  have hlnorm : l ∈ Subgroup.normalizer (D.S : Set G) :=
    Subgroup.mem_normalizer_fintype (fun v hv => hlN v hv)
  have hnorm := Subgroup.mem_normalizer_iff.mp hlnorm
  have hzcenter : (⟨l * z * l⁻¹, hlN z hzS⟩ : ↥D.S) ∈ Subgroup.center ↥D.S := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show (t : G) * (l * z * l⁻¹) = (l * z * l⁻¹) * (t : G)
    have ht' : l⁻¹ * (t : G) * l ∈ D.S := by
      refine (hnorm _).mpr ?_
      have h2 : l * (l⁻¹ * (t : G) * l) * l⁻¹ = (t : G) := by group
      rw [h2]
      exact t.2
    have hzcomm : (l⁻¹ * (t : G) * l) * z = z * (l⁻¹ * (t : G) * l) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp (D.z_mem_center_S hF1) ⟨_, ht'⟩)
    calc (t : G) * (l * z * l⁻¹) = l * ((l⁻¹ * (t : G) * l) * z) * l⁻¹ := by group
      _ = l * (z * (l⁻¹ * (t : G) * l)) * l⁻¹ := by rw [hzcomm]
      _ = (l * z * l⁻¹) * (t : G) := by group
  have hlz : l * z * l⁻¹ = z := by
    rcases D.center_S hF1 ⟨l * z * l⁻¹, hlN z hzS⟩ hzcenter with h1 | h1
    · exfalso
      have h1' : l * z * l⁻¹ = 1 := h1
      have hz1 : z = 1 := by
        calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
          _ = l⁻¹ * 1 * l := by rw [h1']
          _ = 1 := by group
      exact D.z_ne_one hF1 hz1
    · exact h1
  have hlC : l ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * z = l * z * l⁻¹ * l := by group
      _ = z * l := by rw [hlz]
  have hTQ : D.S ⊔ Subgroup.zpowers l ≤ Q :=
    sup_le hSQ (Subgroup.zpowers_le.mpr hlQ)
  have hT2 : IsPGroup 2 ↥(D.S ⊔ Subgroup.zpowers l) := hQ.to_le hTQ
  have hTC : D.S ⊔ Subgroup.zpowers l ≤ centralizer ({z} : Set G) :=
    sup_le hSle (Subgroup.zpowers_le.mpr hlC)
  have hCcard : Nat.card ↥(centralizer ({z} : Set G)) = 3317760 := by
    rw [← D.pull_invE, D.card_pull (le_refl (invE 1)), D.card_invE]
  have hdvd : Nat.card ↥(D.S ⊔ Subgroup.zpowers l) ∣ 3317760 := by
    rw [← hCcard]
    calc Nat.card ↥(D.S ⊔ Subgroup.zpowers l)
        = Nat.card ↥((D.S ⊔ Subgroup.zpowers l).subgroupOf (centralizer ({z} : Set G))) :=
          (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).symm
      _ ∣ Nat.card ↥(centralizer ({z} : Set G)) := Subgroup.card_subgroup_dvd_card _
  have hle : Nat.card ↥(D.S ⊔ Subgroup.zpowers l) ≤ 8192 := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hkdvd : 2 ^ k ∣ 3317760 := hk ▸ hdvd
    have hk13 : k ≤ 13 := by
      by_contra hk'
      have h14 : 14 ≤ k := by omega
      have hd : 2 ^ 14 ∣ 3317760 := (pow_dvd_pow 2 h14).trans hkdvd
      exact absurd hd (by norm_num)
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 13 := pow_le_pow_right' (by norm_num) hk13
      _ = 8192 := by norm_num
  have hltT : D.S < D.S ⊔ Subgroup.zpowers l := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact hlS (heq.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers l))
  have hgt : 8192 < Nat.card ↥(D.S ⊔ Subgroup.zpowers l) := by
    rw [← hScard]
    exact Subgroup.card_lt_of_lt hltT
  omega

theorem eq_M_of_isPi (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) {P : Subgroup G}
    (hP : P ≤ D.S) (hPi : IsPi P) : P = D.M := by
  have hs1p : decSubgroup s1pDecs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hPC : P ≤ centralizer ({z} : Set G) := hP.trans (D.pull_le_centralizer _)
  have hpushS : D.push P ≤ decSubgroup s1pDecs := by
    rintro x hx
    obtain ⟨g, hg, hgP, hxeq⟩ := (D.mem_push).mp hx
    rw [← hxeq]
    exact (D.coe_mem_pull_iff ⟨g, hg⟩).mp (hP hgP)
  have hPiPush : IsPi (D.push P) := by
    have h1 : IsPi (P.subgroupOf (centralizer ({z} : Set G))) :=
      (isPi_iff_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPC)).mpr hPi
    exact (isPi_map_iff D.injective_subtype_comp _).mpr h1
  have hMeq : D.push P = decSubgroup m1Decs :=
    eq_m1_of_isPi hF1 hF1M hF2 hs1p hm1 hpushS hPiPush
  rw [← D.pull_push hPC, hMeq]

theorem centralizer_L_le (hF1 : F1Prop) :
    centralizer (D.L : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hx z (D.z_mem_L hF1)).symm

theorem le_M_of_isPGroup (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) {P : Subgroup G}
    (hP : P ≤ centralizer (D.L : Set G)) (h2 : IsPGroup 2 P) : P ≤ D.M := by
  have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hl1 : decSubgroup l1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hPC : P ≤ centralizer ({z} : Set G) := hP.trans (D.centralizer_L_le hF1)
  have hpush1 : D.push P ≤
      Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
    rw [← D.pull_le_pull_iff (D.push_le_invE P), D.pull_push hPC, D.pull_centralizer hl1]
    exact le_inf hP hPC
  have hpush := le_inf hpush1 (D.push_le_invE P)
  have h2push : IsPGroup 2 (D.push P) := by
    rw [← D.isPGroup_pull_iff (D.push_le_invE P), D.pull_push hPC]
    exact h2
  have hle := le_m1_of_isPGroup hF1M hF2 hm1 hpush h2push
  calc P = D.pull (D.push P) := (D.pull_push hPC).symm
    _ ≤ D.pull (decSubgroup m1Decs) := D.pull_mono hle

theorem card_centralizer_L (hF1 : F1Prop) (hF2 : F2Prop) :
    Nat.card ↥(centralizer (D.L : Set G)) = 3072 := by
  have hl1 : decSubgroup l1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have h := hF2
  dsimp only [F2Prop] at h
  obtain ⟨-, -, hCLeq, hCLcard, -, -⟩ := h
  have hCL : D.pull (centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782)))) =
      centralizer (D.L : Set G) := by
    rw [D.pull_centralizer hl1, inf_eq_left.mpr (D.centralizer_L_le hF1)]
  rw [← hCL, D.card_pull_inf, hCLeq]
  exact hCLcard

theorem mem_L_iff (hF1M : F1MProp) {x : G} :
    x ∈ D.L ↔ x ∈ D.M ∧ ∀ y ∈ D.M, x * y = y * x := by
  have hm := hF1M
  dsimp only [F1MProp] at hm
  obtain ⟨-, hiff⟩ := hm
  have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  constructor
  · intro hx
    obtain ⟨hxC, hxL⟩ := D.mem_pull.mp hx
    refine ⟨(D.mem_pull).mpr ⟨hxC, ((hiff _).mp hxL).1⟩, ?_⟩
    intro y hy
    obtain ⟨hyC, hyM⟩ := D.mem_pull.mp hy
    have hcomm : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ ⟨y, hyC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        ((D.σ ⟨y, hyC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
          ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
      ((hiff _).mp hxL).2 _ hyM
    have hσeq : D.σ ((⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) * ⟨y, hyC⟩) =
        D.σ (⟨y, hyC⟩ * ⟨x, hxC⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hcomm
    have hCe : (⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) * ⟨y, hyC⟩ =
        ⟨y, hyC⟩ * ⟨x, hxC⟩ := D.σ.injective hσeq
    exact congrArg Subtype.val hCe
  · rintro ⟨hxM, hcomm⟩
    obtain ⟨hxC, hxM1⟩ := D.mem_pull.mp hxM
    refine (D.mem_pull).mpr ⟨hxC, (hiff _).mpr ⟨hxM1, ?_⟩⟩
    intro v hv
    have hvE : v ∈ invE 1 := hm1 hv
    have hmem : D.elt v hvE ∈ D.M := (D.elt_mem_pull_iff hvE).mpr hv
    have hvσ : ((D.σ ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ : ↥(invE 1)) :
        Equiv.Perm (Fin 1782)) = v := D.coe_σ_elt v hvE
    have hc := hcomm _ hmem
    have hCe : (⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) *
        ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ =
        ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ * ⟨x, hxC⟩ := by
      apply Subtype.ext
      show x * D.elt v hvE = D.elt v hvE * x
      exact hc
    have hσeq : D.σ ((⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) *
        ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩) =
        D.σ (⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ * ⟨x, hxC⟩) :=
      congrArg D.σ hCe
    rw [map_mul, map_mul] at hσeq
    have hperm : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
        ((D.σ ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) =
        ((D.σ ⟨D.elt v hvE, D.elt_mem_centralizer v hvE⟩ : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) *
          ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := by
      have h5 := congrArg (fun t : ↥(invE 1) => (t : Equiv.Perm (Fin 1782))) hσeq
      simpa only [Subgroup.coe_mul] using h5
    rwa [hvσ] at hperm

theorem elt_eq_of_eq {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ invE 1) (hy : y ∈ invE 1)
    (h : x = y) : D.elt x hx = D.elt y hy := by
  have h1 : (⟨D.elt x hx, D.elt_mem_centralizer x hx⟩ :
      ↥(centralizer ({z} : Set G))) = D.σ.symm ⟨x, hx⟩ := by
    apply D.σ.injective
    rw [D.σ.apply_symm_apply]
    exact Subtype.ext (D.coe_σ_elt x hx)
  have h2 : (⟨D.elt y hy, D.elt_mem_centralizer y hy⟩ :
      ↥(centralizer ({z} : Set G))) = D.σ.symm ⟨y, hy⟩ := by
    apply D.σ.injective
    rw [D.σ.apply_symm_apply]
    exact Subtype.ext (D.coe_σ_elt y hy)
  exact congrArg Subtype.val (h1.trans ((congrArg D.σ.symm (Subtype.ext h)).trans h2.symm))

theorem t0_mul_self : D.t0 * D.t0 = 1 := by
  have h1 : D.t0 * D.t0 =
      D.elt (permC 1782 w0T * permC 1782 w0T) (mul_mem D.w0_mem D.w0_mem) :=
    (D.elt_mul _ _ D.w0_mem D.w0_mem).symm
  rw [h1, ← D.elt_one]
  exact D.elt_eq_of_eq _ _ D.w0_mul_self

theorem t0_ne_one : D.t0 ≠ 1 := by
  intro h
  apply D.w0_ne_one
  have h2 : D.elt (permC 1782 w0T) D.w0_mem = D.elt 1 (one_mem (invE 1)) := by
    rw [show D.elt (permC 1782 w0T) D.w0_mem = (1 : G) from h, D.elt_one]
  exact D.elt_injective h2

theorem w0_mem_orbit (D : LocalData G z) (hF3 : F3Prop) :
    permC 1782 w0T ∈ {x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ decSubgroup nl1Decs, x = g * permC 1782 w0T * g⁻¹} :=
  ⟨1, one_mem _, by group⟩

theorem t0_mem_M (hF3 : F3Prop) : D.t0 ∈ D.M := by
  have h := hF3
  dsimp only [F3Prop] at h
  obtain ⟨-, horbM, -, -⟩ := h
  exact (D.elt_mem_pull_iff D.w0_mem).mpr (horbM _ (D.w0_mem_orbit hF3))

theorem t0_not_mem_L (hF3 : F3Prop) : D.t0 ∉ D.L := by
  have h := hF3
  dsimp only [F3Prop] at h
  obtain ⟨-, -, horbL, -⟩ := h
  intro hL
  exact horbL _ (D.w0_mem_orbit hF3) ((D.elt_mem_pull_iff D.w0_mem).mp hL)

private theorem conj_comp (a b : G) :
    (((MulAut.conj a : MulAut G) : G →* G)).comp
        (((MulAut.conj b : MulAut G) : G →* G)) =
      ((MulAut.conj (a * b) : MulAut G) : G →* G) := by
  ext x
  show MulAut.conj a (MulAut.conj b x) = MulAut.conj (a * b) x
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

theorem isPi_pull {H : Subgroup (Equiv.Perm (Fin 1782))} (hH : H ≤ invE 1) (hPi : IsPi H) :
    IsPi (D.pull H) :=
  (isPi_iff_of_mulEquiv (D.pullEquiv hH)).mpr hPi

theorem map_conj_eq_M_of_le_S (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) {m : G}
    (hm : D.M.map ((MulAut.conj m : MulAut G) : G →* G) ≤ D.S) :
    D.M.map ((MulAut.conj m : MulAut G) : G →* G) = D.M := by
  have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hPiM : IsPi (D.M : Subgroup G) := D.isPi_pull hm1 (isPi_m1 hF1 hF1M)
  have hconjinj : Function.Injective ((MulAut.conj m : MulAut G) : G →* G) :=
    fun a b h => (MulAut.conj m).injective h
  have hPi : IsPi (D.M.map ((MulAut.conj m : MulAut G) : G →* G)) :=
    (isPi_map_iff hconjinj D.M).mpr hPiM
  exact D.eq_M_of_isPi hF1 hF1M hF2 hm hPi

theorem exists_mem_normalizer_M [Finite G] (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    {x y g : G} (hx : x ∈ D.L) (hy : y ∈ D.L) (hxy : g * x * g⁻¹ = y) :
    ∃ n ∈ normalizer (D.M : Set G), n * x * n⁻¹ = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMcard : Nat.card D.M = 1024 := D.card_M hF1M
  have hM2 : IsPGroup 2 (D.M : Subgroup G) :=
    IsPGroup.of_card (n := 10) (by rw [hMcard]; norm_num)
  have hyL := (D.mem_L_iff hF1M).mp hy
  have hxL := (D.mem_L_iff hF1M).mp hx
  have hML : D.M ≤ centralizer ({y} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hyL.2 m hm).symm
  have hMgK : D.M.map ((MulAut.conj g : MulAut G) : G →* G) ≤ centralizer ({y} : Set G) := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxm : x * m = m * x := hxL.2 m hm
    show (MulAut.conj g) m * y = y * (MulAut.conj g) m
    calc (MulAut.conj g) m * y = (g * m * g⁻¹) * (g * x * g⁻¹) := by
          rw [MulAut.conj_apply, ← hxy]
      _ = g * (m * x) * g⁻¹ := by group
      _ = g * (x * m) * g⁻¹ := by rw [hxm]
      _ = (g * x * g⁻¹) * (g * m * g⁻¹) := by group
      _ = y * (MulAut.conj g) m := by
          rw [MulAut.conj_apply, ← hxy]
  obtain ⟨P, hPK, hMP⟩ := CFSG.Sporadic.SuzRecog.LocalR.exists_isSylowOf_le hML hM2
  obtain ⟨P₂, hP₂K, hMgP₂⟩ :=
    CFSG.Sporadic.SuzRecog.LocalR.exists_isSylowOf_le hMgK (hM2.map _)
  obtain ⟨c, hcK, hconj⟩ := hPK.exists_mem_conj hP₂K
  have hcM : ∀ m ∈ (D.M : Subgroup G), c⁻¹ * (g * m * g⁻¹) * c ∈ P := fun m hm =>
    (hconj _).mp (hMgP₂ ⟨m, hm, rfl⟩)
  obtain ⟨Pstar, hPstar, hPPstar⟩ :=
    CFSG.Sporadic.SuzRecog.LocalR.exists_isSylowOf_le (K := ⊤) le_top hPK.isPGroup
  obtain ⟨P₁, hP₁⟩ := D.isSylow_S hF1
  have hSstar : IsSylowOf 2 (D.S : Subgroup G) ⊤ := by
    refine ⟨P₁.subtype le_top, ?_⟩
    rw [Sylow.coe_subtype, hP₁, Subgroup.subgroupOf_map_subtype]
    simp
  obtain ⟨h, -, hconjG⟩ := hSstar.exists_mem_conj hPstar
  have hconjM : D.M.map ((MulAut.conj h⁻¹ : MulAut G) : G →* G) ≤ D.S := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
    change MulAut.conj h⁻¹ m ∈ D.S
    rw [MulAut.conj_apply]
    simpa [inv_inv] using (hconjG m).mp (hPPstar (hMP hm))
  have hMeq1 : D.M.map ((MulAut.conj h⁻¹ : MulAut G) : G →* G) = D.M :=
    D.map_conj_eq_M_of_le_S hF1 hF1M hF2 hconjM
  have hkey : ∀ m ∈ (D.M : Subgroup G),
      (MulAut.conj h⁻¹) ((MulAut.conj (c⁻¹ * g)) m) ∈ D.S := by
    intro m hm
    have hxP : (MulAut.conj (c⁻¹ * g)) m ∈ P := by
      have h1 : (MulAut.conj (c⁻¹ * g)) m = c⁻¹ * (g * m * g⁻¹) * c := by
        rw [MulAut.conj_apply]
        group
      rw [h1]
      exact hcM m hm
    have hxPstar : (MulAut.conj (c⁻¹ * g)) m ∈ Pstar := hPPstar hxP
    have h3 := (hconjG _).mp hxPstar
    change MulAut.conj h⁻¹ ((MulAut.conj (c⁻¹ * g)) m) ∈ D.S
    simpa [MulAut.conj_apply] using h3
  have hleN : (D.M.map ((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G)).map
      ((MulAut.conj h⁻¹ : MulAut G) : G →* G) ≤ D.S := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    exact hkey m hm
  have hMeqN : (D.M.map ((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G)).map
      ((MulAut.conj h⁻¹ : MulAut G) : G →* G) = D.M := by
    have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
    have hPiM : IsPi (D.M : Subgroup G) := D.isPi_pull hm1 (isPi_m1 hF1 hF1M)
    have hinj : Function.Injective
        (((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G)) :=
      fun a b hab => (MulAut.conj (c⁻¹ * g)).injective hab
    have hinv : Function.Injective (((MulAut.conj h⁻¹ : MulAut G) : G →* G)) :=
      fun a b hab => (MulAut.conj h⁻¹).injective hab
    have hPi1 : IsPi (D.M.map ((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G)) :=
      (isPi_map_iff hinj D.M).mpr hPiM
    have hPi2 : IsPi ((D.M.map ((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G)).map
        ((MulAut.conj h⁻¹ : MulAut G) : G →* G)) :=
      (isPi_map_iff hinv _).mpr hPi1
    exact D.eq_M_of_isPi hF1 hF1M hF2 hleN hPi2
  have hhN : h⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq1
  have hhM : D.M.map ((MulAut.conj h : MulAut G) : G →* G) = D.M := by
    have hN : h ∈ Subgroup.normalizer (D.M : Set G) := by
      simpa using inv_mem hhN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
  have hstep : D.M.map ((MulAut.conj (c⁻¹ * g) : MulAut G) : G →* G) = D.M := by
    have h2 := congrArg (fun K : Subgroup G =>
      K.map ((MulAut.conj h : MulAut G) : G →* G)) hMeqN
    rw [Subgroup.map_map, conj_comp, mul_inv_cancel,
      show MulAut.conj (1 : G) = (1 : MulAut G) from map_one MulAut.conj,
      show ((1 : MulAut G) : G →* G) = MonoidHom.id G from rfl, Subgroup.map_id] at h2
    rw [hhM] at h2
    exact h2
  have hnNmem : c⁻¹ * g ∈ Subgroup.normalizer (D.M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hstep
  refine ⟨c⁻¹ * g, hnNmem, ?_⟩
  have hcy : c⁻¹ * y * c = y := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hcK
    calc c⁻¹ * y * c = c⁻¹ * (y * c) * 1 := by group
      _ = c⁻¹ * (c * y) := by rw [hc]; group
      _ = y := by group
  calc c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
    _ = c⁻¹ * y * c := by rw [hxy]
    _ = y := hcy

theorem normalizer_L_eq [Finite G] (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) :
    normalizer (D.L : Set G) = normalizer (D.M : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMcard : Nat.card D.M = 1024 := D.card_M hF1M
  have hM2 : IsPGroup 2 (D.M : Subgroup G) :=
    IsPGroup.of_card (n := 10) (by rw [hMcard]; norm_num)
  apply le_antisymm
  ·
    have key : ∀ m ∈ Subgroup.normalizer (D.L : Set G), ∀ x ∈ (D.M : Subgroup G),
        m * x * m⁻¹ ∈ D.M := by
      intro m hm x hx
      have hmL : ∀ l ∈ D.L, m * l * m⁻¹ ∈ D.L := fun l hl =>
        (Subgroup.mem_normalizer_iff.mp hm l).mp hl
      have hle : D.M.map (MulAut.conj m) ≤ D.M := by
        refine D.le_M_of_isPGroup hF1 hF1M hF2 ?_ (hM2.map _)
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hml' : m⁻¹ * l * m ∈ D.L := by
          simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hm) l).mp hl
        have hcomm := (D.mem_L_iff hF1M).mp hml' |>.2 y hy
        calc l * (MulAut.conj m) y = m * ((m⁻¹ * l * m) * y) * m⁻¹ := by
              rw [MulAut.conj_apply]
              group
          _ = m * (y * (m⁻¹ * l * m)) * m⁻¹ := by rw [hcomm]
          _ = (MulAut.conj m) y * l := by
              rw [MulAut.conj_apply]
              group
      have hthis := hle (Subgroup.mem_map_of_mem ((MulAut.conj m : MulAut G) : G →* G) hx)
      simpa [MulAut.conj_apply] using hthis
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact key n hn x hx
    · intro hx
      have h1 := key n⁻¹ (inv_mem hn) (n * x * n⁻¹) hx
      rw [show n⁻¹⁻¹ = n from inv_inv n] at h1
      have h2 : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      rwa [h2] at h1
  ·
    have key : ∀ m ∈ Subgroup.normalizer (D.M : Set G), ∀ l ∈ D.L, m * l * m⁻¹ ∈ D.L := by
      intro m hm l hl
      have hlm := (D.mem_L_iff hF1M).mp hl
      have hmn := Subgroup.mem_normalizer_iff.mp hm
      have hmn' := Subgroup.mem_normalizer_iff.mp (inv_mem hm)
      rw [D.mem_L_iff hF1M]
      refine ⟨(hmn l).mp hlm.1, ?_⟩
      intro y hy
      have hy' : m⁻¹ * y * m ∈ D.M := by
        simpa [inv_inv] using (hmn' y).mp hy
      have hcomm := hlm.2 (m⁻¹ * y * m) hy'
      calc m * l * m⁻¹ * y = m * (l * (m⁻¹ * y * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * y * m) * l) * m⁻¹ := by rw [hcomm]
        _ = y * (m * l * m⁻¹) := by group
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact key n hn x hx
    · intro hx
      have h1 := key n⁻¹ (inv_mem hn) (n * x * n⁻¹) hx
      rw [show n⁻¹⁻¹ = n from inv_inv n] at h1
      have h2 : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      rwa [h2] at h1

theorem isConj_z_of_mem_L (hF1 : F1Prop) (hF4 : F4Prop) (hF5 : F5Prop) {x : G}
    (hx : x ∈ D.L) (hx1 : x ≠ 1) : IsConj x z := by
  obtain ⟨hxC, hxL⟩ := D.mem_pull.mp hx
  have h := hF1
  dsimp only [F1Prop] at h
  obtain ⟨-, -, -, -, hL1ea, -, -, -⟩ := h
  set v : Equiv.Perm (Fin 1782) := ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))
    with hv
  have hvE : v ∈ invE 1 := (D.σ ⟨x, hxC⟩).2
  have hxe : D.elt v hvE = x := D.elt_coe_σ ⟨x, hxC⟩
  have hsq : v * v = 1 := by
    have h2 := hL1ea.2 v hxL
    simpa [pow_two] using h2
  have hne : v ≠ 1 := by
    intro h1
    apply hx1
    rw [← hxe]
    exact (D.elt_eq_of_eq hvE (one_mem (invE 1)) h1).trans D.elt_one
  rw [← hxe]
  exact (D.isConj_elt_iff hvE hsq hne).mpr (fixedCard_of_mem_l1 hF1 hF4 hF5 hxL hne)

theorem exists_conj_L [Finite G] (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) {x y : G} (hx : x ∈ D.L) (hy : y ∈ D.L) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ n ∈ normalizer (D.L : Set G), n * x * n⁻¹ = y := by
  have hxy : IsConj x y :=
    (D.isConj_z_of_mem_L hF1 hF4 hF5 hx hx1).trans
      (D.isConj_z_of_mem_L hF1 hF4 hF5 hy hy1).symm
  obtain ⟨g, hg⟩ := _root_.isConj_iff.mp hxy
  obtain ⟨n, hn, hnxy⟩ := D.exists_mem_normalizer_M hF1 hF1M hF2 hx hy hg
  exact ⟨n, (D.normalizer_L_eq hF1 hF1M hF2).symm ▸ hn, hnxy⟩

@[instance_reducible] private def conjActionOf (D : LocalData G z) (K : Subgroup G) :
    MulAction ↥(Subgroup.normalizer (K : Set G)) ↥K where
  smul k l := ⟨(k : G) * (l : G) * (k : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp k.2 (l : G)).mp l.2⟩
  one_smul l := by
    apply Subtype.ext
    show (1 : G) * (l : G) * (1 : G)⁻¹ = (l : G)
    group
  mul_smul a b l := by
    apply Subtype.ext
    show ((a * b : ↥(Subgroup.normalizer (K : Set G))) : G) * (l : G) *
      (((a * b : ↥(Subgroup.normalizer (K : Set G))) : G))⁻¹ =
      (a : G) * ((b : G) * (l : G) * (b : G)⁻¹) * (a : G)⁻¹
    rw [Subgroup.coe_mul]
    group

theorem card_normalizer_L [Finite G] (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) : Nat.card (normalizer (D.L : Set G)) = 1105920 := by
  classical
  let K : Subgroup G := Subgroup.normalizer (D.L : Set G)
  letI : MulAction ↥K ↥D.L := D.conjActionOf (D.L)
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  haveI : Fintype ↥D.L := Fintype.ofFinite ↥D.L
  haveI : Fintype (MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) := Fintype.ofFinite _
  have hz : (⟨z, D.z_mem_L hF1⟩ : ↥D.L) ∈
      MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L) :=
    MulAction.mem_orbit_self _
  have horb : MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L) = {x : ↥D.L | x ≠ 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hx
      rw [← hk]
      intro h
      apply D.z_ne_one hF1
      have h' : (k : G) * z * (k : G)⁻¹ = 1 := congrArg Subtype.val h
      calc z = (k : G)⁻¹ * ((k : G) * z * (k : G)⁻¹) * (k : G) := by group
        _ = 1 := by rw [h']; group
    · intro hx
      obtain ⟨n, hn, hnz⟩ := D.exists_conj_L hF1 hF1M hF2 hF4 hF5 (D.z_mem_L hF1) x.2
        (D.z_ne_one hF1) (fun h => hx (Subtype.ext h))
      refine MulAction.mem_orbit_iff.mpr ⟨⟨n, hn⟩, ?_⟩
      apply Subtype.ext
      show n * z * n⁻¹ = (x : G)
      exact hnz
  have hstab : MulAction.stabilizer ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L) =
      (K ⊓ centralizer ({z} : Set G)).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      have hk' : (k : G) * z * (k : G)⁻¹ = z := congrArg Subtype.val hk
      refine ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (k : G) * z = (k : G) * z * (k : G)⁻¹ * (k : G) := by group
        _ = z * (k : G) := by rw [hk']
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      show (k : G) * z * (k : G)⁻¹ = z
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
  have h15 : Nat.card ↥{x : ↥D.L | x ≠ 1} = 15 := by
    have hset : {x : ↥D.L | x ≠ 1} = (Set.univ : Set ↥D.L) \ {1} := by
      ext x
      simp
    have hL : Nat.card ↥D.L = 16 := D.card_L hF1
    rw [hset, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : ↥D.L)), Set.ncard_univ, hL]
  have horbcard : Fintype.card (MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) = 15 := by
    rw [← Nat.card_eq_fintype_card,
      show Nat.card ↥(MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) =
        Nat.card ↥{x : ↥D.L | x ≠ 1} from
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [horb]))]
    exact h15
  have hstabcard : Fintype.card (MulAction.stabilizer ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) = 73728 := by
    rw [← Nat.card_eq_fintype_card]
    have h1 : Nat.card ↥(MulAction.stabilizer ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) =
        Nat.card ↥(K ⊓ centralizer ({z} : Set G)) := by
      rw [hstab]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : K ⊓ centralizer ({z} : Set G) ≤ K)).toEquiv
    have hl1 : decSubgroup l1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
    have h2 : Nat.card ↥(K ⊓ centralizer ({z} : Set G)) = 73728 := by
      have hK : K ⊓ centralizer ({z} : Set G) =
          D.pull (Subgroup.normalizer
            (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782)))) :=
        (D.pull_normalizer hl1).symm
      rw [hK, D.card_pull_inf]
      exact card_normalizer_l1 hF1 hF2 D.card_invE hl1
    rw [h1, h2]
  have hmain : Fintype.card (MulAction.orbit ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) *
      Fintype.card (MulAction.stabilizer ↥K (⟨z, D.z_mem_L hF1⟩ : ↥D.L)) = Fintype.card ↥K :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥K)
      (b := (⟨z, D.z_mem_L hF1⟩ : ↥D.L))
  have hKcard : Fintype.card ↥K = 1105920 := by
    rw [← hmain, horbcard, hstabcard]
  rw [Nat.card_eq_fintype_card]
  exact hKcard

private theorem conj_t0_of_mem (hF1 : F1Prop) (hF2 : F2Prop) (hF3 : F3Prop)
    {u : Equiv.Perm (Fin 1782)} (huE : u ∈ invE 1) (huM : u ∈ decSubgroup m1Decs)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huL : u ∉ decSubgroup l1Decs) :
    ∃ n ∈ normalizer (D.L : Set G) ⊓ centralizer ({z} : Set G), D.elt u huE = n * D.t0 * n⁻¹ := by
  have hl1 : decSubgroup l1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hnl1 : decSubgroup nl1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  obtain ⟨g, hgNL, hgu⟩ := exists_conj_w0 hF3 D.w0_mul_self huM hu2 hu1 huL
  have hgE : g ∈ invE 1 := hnl1 hgNL
  have wE : permC 1782 w0T ∈ invE 1 := D.w0_mem
  have hcompE : g * permC 1782 w0T * g⁻¹ ∈ invE 1 :=
    mul_mem (mul_mem hgE wE) (inv_mem hgE)
  have hprod : D.elt g hgE * D.elt (permC 1782 w0T) wE * (D.elt g hgE)⁻¹ =
      D.elt u huE := by
    have e1 : D.elt g hgE * D.elt (permC 1782 w0T) wE =
        D.elt (g * permC 1782 w0T) (mul_mem hgE wE) := (D.elt_mul g _ hgE wE).symm
    have e2 : D.elt g⁻¹ (inv_mem hgE) = (D.elt g hgE)⁻¹ := D.elt_inv g hgE
    have e3 : D.elt (g * permC 1782 w0T) (mul_mem hgE wE) * D.elt g⁻¹ (inv_mem hgE) =
        D.elt (g * permC 1782 w0T * g⁻¹) (mul_mem (mul_mem hgE wE) (inv_mem hgE)) :=
      (D.elt_mul (g * permC 1782 w0T) g⁻¹ (mul_mem hgE wE) (inv_mem hgE)).symm
    rw [e1, ← e2, e3]
    exact D.elt_eq_of_eq hcompE huE hgu.symm
  have hgN : g ∈ Subgroup.normalizer
      (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
    have h := hF2
    dsimp only [F2Prop] at h
    obtain ⟨-, -, -, -, -, hNLnorm⟩ := h
    exact hNLnorm hgNL
  have hnK : D.elt g hgE ∈ Subgroup.normalizer (D.L : Set G) ⊓
      centralizer ({z} : Set G) := by
    have hmem : D.elt g hgE ∈ D.pull (Subgroup.normalizer
        (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782)))) :=
      (D.elt_mem_pull_iff hgE).mpr hgN
    rw [D.pull_normalizer hl1] at hmem
    exact hmem
  refine ⟨D.elt g hgE, hnK, ?_⟩
  rw [hprod]

theorem exists_conj_t0 (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    {x : G} (hxM : x ∈ D.M) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxL : x ∉ D.L) :
    ∃ n ∈ normalizer (D.L : Set G) ⊓ centralizer ({z} : Set G), x = n * D.t0 * n⁻¹ := by
  obtain ⟨hxC, hxM1⟩ := D.mem_pull.mp hxM
  have hl1 : decSubgroup l1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have hu2 : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) *
      ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := by
    have h : (⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) * ⟨x, hxC⟩ = 1 := Subtype.ext hx2
    have h2 : (D.σ ⟨x, hxC⟩ : ↥(invE 1)) * D.σ ⟨x, hxC⟩ = 1 := by
      calc D.σ ⟨x, hxC⟩ * D.σ ⟨x, hxC⟩ = D.σ (⟨x, hxC⟩ * ⟨x, hxC⟩) := (map_mul _ _ _).symm
        _ = 1 := by rw [h, map_one]
    exact congrArg Subtype.val h2
  have hu1 : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h1
    apply hx1
    have h2 : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 1 := h1
    have h3 : (D.σ ⟨x, hxC⟩ : ↥(invE 1)) = 1 := Subtype.ext h2
    have h4 : (⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) = 1 := by
      apply D.σ.injective
      rw [h3, map_one]
    exact congrArg Subtype.val h4
  have huL : ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∉
      decSubgroup l1Decs := fun h1 => hxL ((D.mem_pull).mpr ⟨hxC, h1⟩)
  have hxe : D.elt ((D.σ ⟨x, hxC⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))
      (D.σ ⟨x, hxC⟩).2 = x := D.elt_coe_σ ⟨x, hxC⟩
  obtain ⟨n, hn, hnu⟩ := D.conj_t0_of_mem hF1 hF2 hF3 (D.σ ⟨x, hxC⟩).2 hxM1 hu2 hu1 huL
  exact ⟨n, hn, hxe.symm.trans hnu⟩

theorem card_involutions_M (hF3 : F3Prop) :
    Nat.card {x : D.M // x * x = 1 ∧ x ≠ 1 ∧ (x : G) ∉ D.L} = 288 := by
  have hm1 : decSubgroup m1Decs ≤ invE 1 := D.decSubgroup_le_invE (by decide)
  have h := hF3
  dsimp only [F3Prop] at h
  obtain ⟨-, -, -, -, hinvcard⟩ := h
  have hDL : ∀ x : ↥D.M, ((x : G) ∈ D.L ↔
      (((D.pullEquiv hm1 x : ↥(decSubgroup m1Decs)) : ↥(decSubgroup m1Decs)) :
        Equiv.Perm (Fin 1782)) ∈ decSubgroup l1Decs) := by
    intro x
    have hxC : (x : G) ∈ centralizer ({z} : Set G) := D.pull_le_centralizer _ x.2
    rw [D.coe_mem_pull_iff (H := decSubgroup l1Decs) ⟨x, hxC⟩, D.coe_pullEquiv]
  refine (Nat.card_congr (Equiv.subtypeEquiv (D.pullEquiv hm1).toEquiv (fun x => ?_))).trans
    hinvcard
  have hsq : (x * x = 1) ↔
      ((D.pullEquiv hm1) x * (D.pullEquiv hm1) x = 1) := by
    constructor
    · intro h2
      have h5 : D.pullEquiv hm1 (x * x) = D.pullEquiv hm1 1 := by rw [h2, map_one]
      simpa [map_mul] using h5
    · intro h2
      have h5 : D.pullEquiv hm1 (x * x) = D.pullEquiv hm1 1 := by
        rw [map_mul, h2, map_one]
      exact (D.pullEquiv hm1).injective h5
  have hne : (x ≠ 1) ↔ ((D.pullEquiv hm1) x ≠ 1) := by
    constructor
    · intro h1 h3
      exact h1 ((D.pullEquiv hm1).injective (by rw [h3, map_one]))
    · intro h1 h3
      exact h1 (by rw [h3, map_one])
  exact and_congr hsq (and_congr hne (not_congr (hDL x)))

theorem exists_five [Finite G] (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) :
    ∃ f ∈ normalizer (D.L : Set G), orderOf f = 5 ∧ (∀ l ∈ D.L, f * l = l * f → l = 1) ∧
      f * D.t0 = D.t0 * f := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Nat.card ↥(Subgroup.normalizer (D.L : Set G)) = 1105920 :=
    D.card_normalizer_L hF1 hF1M hF2 hF4 hF5
  obtain ⟨f₀, hf₀ord⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hN]; norm_num)
  have hf₀L : (f₀ : G) ∈ Subgroup.normalizer (D.L : Set G) := f₀.2
  have hf₀M : (f₀ : G) ∈ Subgroup.normalizer (D.M : Set G) := by
    rw [← D.normalizer_L_eq hF1 hF1M hF2]
    exact f₀.2
  have hf₀order : orderOf (f₀ : G) = 5 := by
    rw [Subgroup.orderOf_coe, hf₀ord]
  have hCL : Nat.card ↥(centralizer (D.L : Set G)) = 3072 := D.card_centralizer_L hF1 hF2
  have hf₀notC : (f₀ : G) ∉ centralizer (D.L : Set G) := by
    intro hmem
    have hdvd : orderOf (f₀ : G) ∣ Nat.card ↥(centralizer (D.L : Set G)) := by
      have h := orderOf_dvd_natCard (⟨(f₀ : G), hmem⟩ : ↥(centralizer (D.L : Set G)))
      rw [← Subgroup.orderOf_coe] at h
      exact h
    rw [hf₀order, hCL] at hdvd
    norm_num at hdvd
  letI : MulAction ↥(Subgroup.normalizer (D.L : Set G)) ↥D.L := D.conjActionOf (D.L)
  letI : MulAction ↥(Subgroup.normalizer (D.M : Set G)) ↥D.M := D.conjActionOf (D.M)
  letI : MulAction ↥(Subgroup.zpowers (f₀ : G)) ↥D.L :=
    MulAction.compHom _ (Subgroup.inclusion (Subgroup.zpowers_le.mpr hf₀L))
  letI : MulAction ↥(Subgroup.zpowers (f₀ : G)) ↥D.M :=
    MulAction.compHom _ (Subgroup.inclusion (Subgroup.zpowers_le.mpr hf₀M))
  have hpg : IsPGroup 5 ↥(Subgroup.zpowers (f₀ : G)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hf₀order]
    norm_num
  have hfixL : MulAction.fixedPoints ↥(Subgroup.zpowers (f₀ : G)) ↥D.L =
      ((Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L).subgroupOf D.L : Set ↥D.L) := by
    ext x
    rw [MulAction.mem_fixedPoints]
    change (∀ m : ↥(Subgroup.zpowers (f₀ : G)), m • x = x) ↔
      (x : G) ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (h ⟨(f₀ : G), Subgroup.mem_zpowers (f₀ : G)⟩)
      have h2 : (f₀ : G) * (x : G) * (f₀ : G)⁻¹ = (x : G) := by
        rwa [show (((⟨(f₀ : G), Subgroup.mem_zpowers (f₀ : G)⟩ : ↥(Subgroup.zpowers (f₀ : G))) •
          x : ↥D.L) : G) = (f₀ : G) * (x : G) * (f₀ : G)⁻¹ from rfl] at h1
      exact ⟨by
        calc (x : G) * (f₀ : G) = ((f₀ : G) * (x : G) * (f₀ : G)⁻¹) * (f₀ : G) := by rw [h2]
          _ = (f₀ : G) * (x : G) := by group, x.2⟩
    · rintro ⟨hx, -⟩ k
      apply Subtype.ext
      show (k : G) * (x : G) * (k : G)⁻¹ = (x : G)
      rw [show (k : G) * (x : G) = (x : G) * (k : G) from ?_]
      · group
      · have hle : Subgroup.zpowers (f₀ : G) ≤ Subgroup.centralizer ({(x : G)} : Set G) :=
          Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle k.2)
  have hCL_eq : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers (f₀ : G)) ↥D.L) =
      Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) := by
    rw [hfixL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L ≤ D.L)).toEquiv
  have hmodL : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers (f₀ : G)) ↥D.L) ≡ 1 [MOD 5] := by
    have h := hpg.card_modEq_card_fixedPoints ↥D.L
    rw [D.card_L hF1] at h
    exact h.symm.trans (by norm_num)
  have hcardL : Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) = 1 := by
    have hmod : Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) ≡ 1 [MOD 5] := by
      rw [← hCL_eq]
      exact hmodL
    have hdvd : Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) ∣ 16 := by
      have h := Subgroup.card_subgroup_dvd_card
        ((Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L).subgroupOf D.L)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L ≤ D.L)).toEquiv,
        D.card_L hF1] at h
      exact h
    have hne : Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) ≠ 16 := by
      intro h16
      have heq : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L = D.L :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h16, D.card_L hF1])
      apply hf₀notC
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : l ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L := heq.symm ▸ hl
      exact Subgroup.mem_centralizer_singleton_iff.mp hl'.1
    obtain ⟨k, hk4, hk⟩ := Nat.dvd_prime_pow Nat.prime_two (m := 4) (i :=
      Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L)) |>.mp (by
        rw [show (2 : ℕ) ^ 4 = 16 from by norm_num]
        exact hdvd)
    interval_cases k
    · rw [hk]
      norm_num
    · exfalso
      rw [hk] at hmod
      revert hmod
      norm_num
    · exfalso
      rw [hk] at hmod
      revert hmod
      norm_num
    · exfalso
      rw [hk] at hmod
      revert hmod
      norm_num
    · exfalso
      exact hne hk
  have hfixM : MulAction.fixedPoints ↥(Subgroup.zpowers (f₀ : G)) ↥D.M =
      ((Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M).subgroupOf D.M : Set ↥D.M) := by
    ext x
    rw [MulAction.mem_fixedPoints]
    change (∀ m : ↥(Subgroup.zpowers (f₀ : G)), m • x = x) ↔
      (x : G) ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (h ⟨(f₀ : G), Subgroup.mem_zpowers (f₀ : G)⟩)
      have h2 : (f₀ : G) * (x : G) * (f₀ : G)⁻¹ = (x : G) := by
        rwa [show (((⟨(f₀ : G), Subgroup.mem_zpowers (f₀ : G)⟩ : ↥(Subgroup.zpowers (f₀ : G))) •
          x : ↥D.M) : G) = (f₀ : G) * (x : G) * (f₀ : G)⁻¹ from rfl] at h1
      exact ⟨by
        calc (x : G) * (f₀ : G) = ((f₀ : G) * (x : G) * (f₀ : G)⁻¹) * (f₀ : G) := by rw [h2]
          _ = (f₀ : G) * (x : G) := by group, x.2⟩
    · rintro ⟨hx, -⟩ k
      apply Subtype.ext
      show (k : G) * (x : G) * (k : G)⁻¹ = (x : G)
      rw [show (k : G) * (x : G) = (x : G) * (k : G) from ?_]
      · group
      · have hle : Subgroup.zpowers (f₀ : G) ≤ Subgroup.centralizer ({(x : G)} : Set G) :=
          Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle k.2)
  have hCM_eq : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers (f₀ : G)) ↥D.M) =
      Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M) := by
    rw [hfixM]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M ≤ D.M)).toEquiv
  have hCMne1 : Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M) ≠ 1 := by
    intro h1
    have h := hpg.card_modEq_card_fixedPoints ↥D.M
    rw [D.card_M hF1M, hCM_eq, h1] at h
    revert h
    norm_num
  have hCM2 : IsPGroup 2 ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M) := by
    have hM2 : IsPGroup 2 (D.M : Subgroup G) :=
      IsPGroup.of_card (n := 10) (by rw [D.card_M hF1M]; norm_num)
    exact hM2.to_le inf_le_right
  obtain ⟨k, hk⟩ := hCM2.exists_card_eq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hCMne1
      rw [hk, h0]
      norm_num
    · exact h0
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.M) := by
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨u₀, hu₀ord⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have huM : (u₀ : G) ∈ D.M := u₀.2.2
  have huC : (u₀ : G) ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) := u₀.2.1
  have huGord : orderOf (u₀ : G) = 2 := by
    rw [Subgroup.orderOf_coe, hu₀ord]
  have hu2 : (u₀ : G) * (u₀ : G) = 1 := by
    have h : u₀ ^ 2 = 1 := by rw [← hu₀ord, pow_orderOf_eq_one]
    simpa [pow_two] using congrArg Subtype.val h
  have hu1 : (u₀ : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huGord
    exact absurd huGord (by norm_num)
  have huL : (u₀ : G) ∉ D.L := by
    intro hL
    have hmem : (u₀ : G) ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L := ⟨huC, hL⟩
    have hbot : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L = ⊥ :=
      Subgroup.eq_bot_of_card_eq (H := Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) hcardL
    rw [hbot] at hmem
    exact hu1 (Subgroup.mem_bot.mp hmem)
  obtain ⟨n, hn, hnu⟩ := D.exists_conj_t0 hF1 hF1M hF2 hF3 huM hu2 hu1 huL
  have hnL : n ∈ Subgroup.normalizer (D.L : Set G) := hn.1
  have hconjN : n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹ ∈ Subgroup.normalizer (D.L : Set G) := by
    have hnn : ∀ l : G, (l ∈ D.L ↔ n⁻¹ * l * n ∈ D.L) := by
      intro l
      have h := Subgroup.mem_normalizer_iff.mp hnL (n⁻¹ * l * n)
      rw [show n * (n⁻¹ * l * n) * n⁻¹ = l from by group] at h
      exact h.symm
    rw [Subgroup.mem_normalizer_iff]
    intro l
    rw [show (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) * l * (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹)⁻¹ =
        n⁻¹ * ((f₀ : G) * (n * l * n⁻¹) * (f₀ : G)⁻¹) * n from by group,
      ← hnn, ← Subgroup.mem_normalizer_iff.mp f₀.2 (n * l * n⁻¹)]
    exact Subgroup.mem_normalizer_iff.mp hnL l
  have hford : orderOf (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) = 5 := by
    have h1 : n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹ = (MulAut.conj n⁻¹) (f₀ : G) := by
      rw [MulAut.conj_apply]
    rw [h1, MulEquiv.orderOf_eq, hf₀order]
  have hffpf : ∀ l ∈ D.L, (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) * l = l * (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) →
      l = 1 := by
    intro l hl hcomm
    have hl' : n * l * n⁻¹ ∈ D.L := (Subgroup.mem_normalizer_iff.mp hnL l).mp hl
    have hcomm' : (f₀ : G) * (n * l * n⁻¹) = (n * l * n⁻¹) * (f₀ : G) := by
      calc (f₀ : G) * (n * l * n⁻¹) = n * ((n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) * l) * n⁻¹ := by group
        _ = n * (l * (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹)) * n⁻¹ := by rw [hcomm]
        _ = (n * l * n⁻¹) * (f₀ : G) := by group
    have hmem : n * l * n⁻¹ ∈ Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm'.symm, hl'⟩
    have hbot : Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L = ⊥ :=
      Subgroup.eq_bot_of_card_eq (H := Subgroup.centralizer ({(f₀ : G)} : Set G) ⊓ D.L) hcardL
    rw [hbot] at hmem
    have h1 : n * l * n⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : l = n⁻¹ * (n * l * n⁻¹) * n := by group
    rw [h1] at h2
    simpa using h2
  have hcu : (f₀ : G) * (u₀ : G) = (u₀ : G) * (f₀ : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
  have hft0 : (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) * D.t0 = D.t0 * (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) := by
    have ht0 : D.t0 = n⁻¹ * (u₀ : G) * n := by
      rw [hnu]
      group
    rw [ht0]
    calc (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) * (n⁻¹ * (u₀ : G) * n) =
          n⁻¹ * ((f₀ : G) * (u₀ : G)) * n := by group
      _ = n⁻¹ * ((u₀ : G) * (f₀ : G)) * n := by rw [hcu]
      _ = (n⁻¹ * (u₀ : G) * n) * (n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹) := by group
  exact ⟨n⁻¹ * (f₀ : G) * (n⁻¹)⁻¹, hconjN, hford, hffpf, hft0⟩
