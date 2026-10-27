module

public import CFSG.Sporadic.SuzRecog.SuzL34.NormalizerD
public import CFSG.Sporadic.SuzRecog.SuzL34.TransferData
public import CFSG.Quasithin.Recognition.L34CIT.Config

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} (D : LocalData G z)

noncomputable abbrev AG : Subgroup G :=
  CFSG.GroupTheory.oddOrderClosure (centralizer ({D.t0} : Set G))

theorem AG_le_centralizer : D.AG ≤ centralizer ({D.t0} : Set G) :=
  CFSG.GroupTheory.oddOrderClosure_le _

private theorem centralizer_t0_le_normalizer_AG :
    centralizer ({D.t0} : Set G) ≤ normalizer (D.AG : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer D.AG_le_centralizer).mp
    (CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf _)

private theorem isSylow_TG_centralizer (hF3 : F3Prop) :
    IsSylowOf 2 D.TG (centralizer ({D.t0} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  exact ⟨D.TG_le_centralizer, D.isPGroup_TG hF3, D.not_two_dvd_relIndex_TG hF3⟩

theorem AG_inf_TG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : D.AG ⊓ D.TG = D.T0G := by
  obtain ⟨f, hfN, hf5, hffix, hft⟩ := exists_five D hF1 hF1M hF2 hF3 hF4 hF5
  exact oddOrderClosure_inf_TG D hF1 hF1M hF3 hF4 hF5 hF8 hfN hf5 hffix hft

private theorem isSylow_T0G_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    IsSylowOf 2 D.T0G D.AG := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylow_TG_centralizer D hF3).inf_of_le_normalizer
    D.AG_le_centralizer (centralizer_t0_le_normalizer_AG D)
  rw [inf_comm, AG_inf_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8] at h
  exact h

theorem T0G_le_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : D.T0G ≤ D.AG := by
  rw [← AG_inf_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8]
  exact inf_le_left

theorem z_mem_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : z ∈ D.AG :=
  T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 (L_le_T0G D hF5 (z_mem_L D hF1))

theorem L_le_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : D.L ≤ D.AG :=
  (L_le_T0G D hF5).trans (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)

theorem M2G_le_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : D.M2G ≤ D.AG :=
  (M2G_le_T0G D hF5).trans (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)

theorem tauG_mem_normalizer_AG (hF5 : F5Prop) : D.tauG ∈ normalizer (D.AG : Set G) :=
  CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure _
    ((Subgroup.le_normalizer (H := centralizer ({D.t0} : Set G)))
      (D.TG_le_centralizer (D.tauG_mem_TG hF5)))

theorem not_two_dvd_relIndex_T0G (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ¬ 2 ∣ D.T0G.relIndex D.AG := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_iff.mp (isSylow_T0G_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)).2.2

private theorem commutator_mem_inf_M2G (hF5 : F5Prop) {t l : G}
    (ht : t ∈ D.T0G) (hl : l ∈ D.T0G) :
    t * l * t⁻¹ * l⁻¹ ∈ D.pull (decSubgroup l1Decs) ⊓ D.M2G := by
  have h5 := hF5
  simp only [F5Prop] at h5
  have hcomm := h5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLM := h5.2.2.2.2.1
  let gt : ↥(centralizer ({z} : Set G)) := ⟨t, D.pull_le_centralizer _ ht⟩
  let gl : ↥(centralizer ({z} : Set G)) := ⟨l, D.pull_le_centralizer _ hl⟩
  have hu : ((D.σ gt : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup t0Tabs :=
    (D.coe_mem_pull_iff gt).mp ht
  have hv : ((D.σ gl : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ tabSubgroup t0Tabs :=
    (D.coe_mem_pull_iff gl).mp hl
  have hz := hcomm ((D.σ gt : ↥(invE 1)) : Equiv.Perm (Fin 1782)) hu
    ((D.σ gl : ↥(invE 1)) : Equiv.Perm (Fin 1782)) hv
  have hmem : t * l * t⁻¹ * l⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (mul_mem (D.pull_le_centralizer _ ht)
      (D.pull_le_centralizer _ hl)) (inv_mem (D.pull_le_centralizer _ ht)))
      (inv_mem (D.pull_le_centralizer _ hl))
  rw [show D.pull (decSubgroup l1Decs) ⊓ D.M2G =
      D.pull (decSubgroup l1Decs ⊓ decSubgroup m21Decs) by rw [D.pull_inf]]
  rw [hLM, D.mem_pull]
  refine ⟨hmem, ?_⟩
  have harg : (⟨t * l * t⁻¹ * l⁻¹, hmem⟩ : ↥(centralizer ({z} : Set G))) =
      gt * gl * gt⁻¹ * gl⁻¹ := Subtype.ext rfl
  rw [harg, map_mul, map_mul, map_mul, map_inv, map_inv]
  simpa using hz

private theorem conj_mem_L_of_mem_T0G (hF5 : F5Prop) {t l : G} (ht : t ∈ D.T0G)
    (hl : l ∈ D.L) : t * l * t⁻¹ ∈ D.L := by
  have hz := commutator_mem_inf_M2G D hF5 ht (L_le_T0G D hF5 hl)
  have hmem : (t * l * t⁻¹ * l⁻¹) * l ∈ D.L :=
    D.L.mul_mem (Subgroup.mem_inf.mp hz).1 hl
  rwa [show t * l * t⁻¹ = (t * l * t⁻¹ * l⁻¹) * l from by group]

theorem T0G_le_normalizer_L (hF1 : F1Prop) (hF5 : F5Prop) :
    D.T0G ≤ normalizer (D.L : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨l, hl, rfl⟩
    exact conj_mem_L_of_mem_T0G D hF5 ht hl
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

theorem centralizer_L_inf_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    centralizer (D.L : Set G) ⊓ D.AG = D.L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K1 : Subgroup G := normalizer (D.L : Set G) ⊓ D.AG
  let C : Subgroup G := centralizer (D.L : Set G) ⊓ D.AG
  change C = D.L
  have hL_le_C : D.L ≤ C := by
    refine le_inf ?_ (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    haveI : IsMulCommutative ↥D.L := (D.isElemAbelian_L hF1).1
    exact (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D.L) ⟨y, hy⟩)).symm
  have hC_le_inter : C ≤ centralizer (D.L : Set G) ⊓ centralizer ({D.t0} : Set G) :=
    le_inf inf_le_left (inf_le_right.trans D.AG_le_centralizer)
  have hC2 : IsPGroup 2 ↥C := by
    have hcard : Nat.card ↥(centralizer (D.L : Set G) ⊓
        centralizer ({D.t0} : Set G)) = 64 :=
      card_centralizer_L_inf_centralizer_t0 D hF6 (z_mem_L D hF1)
    have hInter2 : IsPGroup 2 ↥(centralizer (D.L : Set G) ⊓
        centralizer ({D.t0} : Set G)) :=
      IsPGroup.of_card (p := 2) (n := 6) (by rw [hcard]; norm_num)
    exact hInter2.to_le hC_le_inter
  have hCK1 : C ≤ K1 :=
    le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer (D.L : Set G))) inf_le_right
  have hCnormal : (C.subgroupOf K1).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCK1).mpr ?_
    refine (le_inf ?_ ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := centralizer (D.L : Set G)) (K := D.AG))
    · exact inf_le_left.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer (D.L : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer (D.L : Set G)))
    · intro k hk
      exact Subgroup.le_normalizer (H := D.AG) hk.2
  have hT0K1 : D.T0G ≤ K1 :=
    le_inf (T0G_le_normalizer_L D hF1 hF5) (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  have hT0_sylow : IsSylowOf 2 D.T0G K1 :=
    (isSylow_T0G_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8).of_le hT0K1 inf_le_right
  have hC_le_T0 : C ≤ D.T0G := by
    obtain ⟨Q, hQ⟩ := hT0_sylow.exists_sylow_eq_subgroupOf
    haveI : (Subgroup.comap K1.subtype C).Normal := by
      simpa [Subgroup.comap_subtype] using hCnormal
    have hCsub_le : C.subgroupOf K1 ≤ Q :=
      IsPGroup.le_sylow_of_normal hC2.comap_subtype Q
    intro x hx
    have hx' : (⟨x, hCK1 hx⟩ : ↥K1) ∈ C.subgroupOf K1 := hx
    have hx'' := hCsub_le hx'
    rwa [hQ] at hx''
  have hnot_le : ¬ D.L ≤ D.L ⊓ D.M2G := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [card_inf_M2G D hF5, card_L D hF1] at hcard
    norm_num at hcard
  obtain ⟨x, hxL, hxZ⟩ := SetLike.not_le_iff_exists.mp hnot_le
  have hxsub : ({x} : Set G) ⊆ (D.L : Set G) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rwa [hy]
  have hC_le_xT : C ≤ centralizer ({x} : Set G) ⊓ D.T0G :=
    le_inf (inf_le_left.trans (Subgroup.centralizer_le hxsub)) hC_le_T0
  rw [centralizer_inf_T0G_L D hF1 hF5 x hxL hxZ] at hC_le_xT
  exact le_antisymm hC_le_xT hL_le_C

private theorem permC_zero_of_isInvA {n : ℕ} (hn : 0 < n) {t r : Array ℕ}
    (h : CFSG.Monster.B.Co2.Native.isInvA n t r = true) (h0 : t[0]! = 0) :
    permC n t ⟨0, hn⟩ = ⟨0, hn⟩ := by
  have hrep : CFSG.Monster.B.Co2.Rep n t (permC n t) :=
    (CFSG.Sporadic.SuzOddCore.rep_permC h).1
  have happ := hrep.apply hn
  rw [h0] at happ
  exact Fin.ext happ.symm

private theorem tabPerm16_xA_zero : tabPerm16 xA (0 : Fin 16) = 0 := by
  simpa [tabPerm16] using permC_zero_of_isInvA (n := 16) (by norm_num)
    CFSG.Sporadic.SuzRecog.SuzL34Cert.isInvA_xA
    (by decide : xA[0]! = 0)

private theorem tabPerm16_xBs_zero {i : ℕ} (hi : i < 4) :
    tabPerm16 xBs[i]! (0 : Fin 16) = 0 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi' with rfl | rfl | rfl | rfl
  · simpa [tabPerm16] using permC_zero_of_isInvA (n := 16) (by norm_num)
      CFSG.Sporadic.SuzRecog.SuzL34Cert.isInvA_xB0
      (by decide : (xBs[0]!)[0]! = 0)
  · simpa [tabPerm16] using permC_zero_of_isInvA (n := 16) (by norm_num)
      CFSG.Sporadic.SuzRecog.SuzL34Cert.isInvA_xB1
      (by decide : (xBs[1]!)[0]! = 0)
  · simpa [tabPerm16] using permC_zero_of_isInvA (n := 16) (by norm_num)
      CFSG.Sporadic.SuzRecog.SuzL34Cert.isInvA_xB2
      (by decide : (xBs[2]!)[0]! = 0)
  · simpa [tabPerm16] using permC_zero_of_isInvA (n := 16) (by norm_num)
      CFSG.Sporadic.SuzRecog.SuzL34Cert.isInvA_xB3
      (by decide : (xBs[3]!)[0]! = 0)

private theorem X16_zero_fixed {i : ℕ} (hi : i < 4) {g : Equiv.Perm (Fin 16)}
    (hg : g ∈ X16 i) : g 0 = 0 := by
  let S : Subgroup (Equiv.Perm (Fin 16)) :=
    MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16)
  have hgenA : tabPerm16 xA ∈ S := by
    rw [MulAction.mem_stabilizer_iff]
    simpa [Equiv.Perm.smul_def] using tabPerm16_xA_zero
  have hgenB : tabPerm16 xBs[i]! ∈ S := by
    rw [MulAction.mem_stabilizer_iff]
    simpa [Equiv.Perm.smul_def] using tabPerm16_xBs_zero hi
  have hXleS : X16 i ≤ S := by
    rw [X16]
    apply (Subgroup.closure_le (K := S)).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact hgenA
    · exact hgenB
  have hgS : g ∈ S := hXleS hg
  simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp hgS)

private theorem X16_exists_smul_of_ne_zero (hF9 : F9Prop) {i : ℕ} (hi : i < 4)
    {j k : Fin 16} (hj : j ≠ 0) (hk : k ≠ 0) : ∃ g ∈ X16 i, g j = k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let X : Subgroup (Equiv.Perm (Fin 16)) := X16 i
  letI : MulAction ↥X (Fin 16) := MulAction.compHom (Fin 16) (Subgroup.subtype X)
  let O : Set (Fin 16) := MulAction.orbit ↥X j
  have hXcard : Nat.card ↥X = 60 := (hF9.1 i hi).1
  have hO_subset : O ⊆ {x : Fin 16 | x ≠ 0} := by
    rintro x ⟨g, rfl⟩ hx
    have hg0' : ((g⁻¹ : ↥X) : Equiv.Perm (Fin 16)) 0 = 0 := X16_zero_fixed hi (g⁻¹).2
    have hmem : ((g : ↥X) : Equiv.Perm (Fin 16)) j = 0 := hx
    have h1 : j = ((g⁻¹ : ↥X) : Equiv.Perm (Fin 16)) 0 := by
      rw [← hmem]
      simp [Subgroup.coe_inv]
    rw [hg0'] at h1
    exact hj h1
  letI : Fintype ↥X := Fintype.ofFinite ↥X
  letI : Fintype O := Fintype.ofFinite O
  letI : Fintype (MulAction.stabilizer ↥X j) := Fintype.ofFinite _
  have hmain : Nat.card O * Nat.card (MulAction.stabilizer ↥X j) = Nat.card ↥X := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥X) (b := j)
  have hstab_dvd : Nat.card (MulAction.stabilizer ↥X j) ∣ 60 := by
    have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer ↥X j)
    rwa [hXcard] at this
  have h3not : ¬ 3 ∣ Nat.card (MulAction.stabilizer ↥X j) := by
    intro h3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    let gX : ↥X := g
    have hfix : gX • j = j := MulAction.mem_stabilizer_iff.mp g.2
    have hfix' : ((gX : ↥X) : Equiv.Perm (Fin 16)) j = j := by
      have h : (Subgroup.subtype X gX) • j = j := hfix
      simpa [Equiv.Perm.smul_def] using h
    have hordX : orderOf gX = 3 := by
      rw [Subgroup.orderOf_coe, hg]
    have hordP : orderOf (((gX : ↥X) : Equiv.Perm (Fin 16))) = 3 := by
      rw [Subgroup.orderOf_coe, hordX]
    have hzero := (hF9.1 i hi).2.2 ((gX : ↥X) : Equiv.Perm (Fin 16)) gX.2
      (Or.inl hordP) j hfix'
    exact hj hzero
  have h5not : ¬ 5 ∣ Nat.card (MulAction.stabilizer ↥X j) := by
    intro h5
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 h5
    let gX : ↥X := g
    have hfix : gX • j = j := MulAction.mem_stabilizer_iff.mp g.2
    have hfix' : ((gX : ↥X) : Equiv.Perm (Fin 16)) j = j := by
      have h : (Subgroup.subtype X gX) • j = j := hfix
      simpa [Equiv.Perm.smul_def] using h
    have hordX : orderOf gX = 5 := by
      rw [Subgroup.orderOf_coe, hg]
    have hordP : orderOf (((gX : ↥X) : Equiv.Perm (Fin 16))) = 5 := by
      rw [Subgroup.orderOf_coe, hordX]
    have hzero := (hF9.1 i hi).2.2 ((gX : ↥X) : Equiv.Perm (Fin 16)) gX.2
      (Or.inr hordP) j hfix'
    exact hj hzero
  have h15dvdO : 15 ∣ Nat.card O := by
    obtain ⟨k', hk'⟩ := hstab_dvd
    have h3k : 3 ∣ k' := by
      have h3 : 3 ∣ Nat.card (MulAction.stabilizer ↥X j) * k' := by
        rw [← hk']
        norm_num
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not |>.dvd_of_dvd_mul_left h3
    have h5k : 5 ∣ k' := by
      have h5 : 5 ∣ Nat.card (MulAction.stabilizer ↥X j) * k' := by
        rw [← hk']
        norm_num
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5not |>.dvd_of_dvd_mul_left h5
    have h15k : 15 ∣ k' :=
      ((Nat.coprime_primes Nat.prime_three Nat.prime_five).mpr (by norm_num)).mul_dvd_of_dvd_of_dvd
        h3k h5k
    have ho : Nat.card O = k' := by
      have h : Nat.card (MulAction.stabilizer ↥X j) * Nat.card O =
          Nat.card (MulAction.stabilizer ↥X j) * k' := by
        calc Nat.card (MulAction.stabilizer ↥X j) * Nat.card O
            = Nat.card O * Nat.card (MulAction.stabilizer ↥X j) := by rw [mul_comm]
          _ = Nat.card ↥X := hmain
          _ = 60 := hXcard
          _ = Nat.card (MulAction.stabilizer ↥X j) * k' := hk'
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(MulAction.stabilizer ↥X j))) h
    rw [ho]
    exact h15k
  have hO_card : Nat.card O = 15 := by
    have hle : Nat.card O ≤ 15 := by
      have hle' : O.ncard ≤ ({x : Fin 16 | x ≠ 0} : Set (Fin 16)).ncard :=
        Set.ncard_le_ncard hO_subset
      have hcardnz : Nat.card {x : Fin 16 | x ≠ 0} = 15 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardnz] at hle'
    obtain ⟨m, hm⟩ := h15dvdO
    have hmpos : 0 < m := by
      by_contra h
      have h0 : m = 0 := by omega
      rw [h0, mul_zero] at hm
      have hposO : 0 < Nat.card O :=
        Nat.card_pos_iff.mpr ⟨⟨j, MulAction.mem_orbit_self j⟩, inferInstance⟩
      exact hposO.ne' hm
    have hle' : 15 * m ≤ 15 := by rw [← hm]; exact hle
    have hm1 : m = 1 := by omega
    rw [hm, hm1, mul_one]
  have hO_eq : O = {x : Fin 16 | x ≠ 0} := by
    apply Set.eq_of_subset_of_ncard_le hO_subset
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have hcardnz : Nat.card {x : Fin 16 | x ≠ 0} = 15 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hcardnz, hO_card]
  have hkO : k ∈ O := by
    rw [hO_eq]
    exact hk
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hkO
  refine ⟨(g : Equiv.Perm (Fin 16)), g.2, ?_⟩
  have h : (Subgroup.subtype X g) • j = k := hg
  simpa [Equiv.Perm.smul_def] using h

private theorem inf_T0G_centralizer_L (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    D.T0G ⊓ centralizer (D.L : Set G) = D.L := by
  apply le_antisymm
  · intro x hx
    have hxAG : x ∈ D.AG := T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hx.1
    have hxL : x ∈ centralizer (D.L : Set G) ⊓ D.AG := ⟨hx.2, hxAG⟩
    rwa [centralizer_L_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8] at hxL
  · intro x hx
    refine ⟨L_le_T0G D hF5 hx, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      haveI : IsMulCommutative ↥D.L := (D.isElemAbelian_L hF1).1
      exact (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D.L) ⟨y, hy⟩)).symm

private theorem exists_X16_map_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    ∃ i < 4,
      (((normalizer (D.L : Set G) ⊓ D.AG).subgroupOf (normalizer (D.L : Set G))).map
        (bitAction (D.lEquiv hF1))) = X16 i := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let N : Subgroup G := normalizer (D.L : Set G)
  let K1 : Subgroup G := N ⊓ D.AG
  let ρ : ↥N →* Equiv.Perm (Fin 16) := bitAction (D.lEquiv hF1)
  let X : Subgroup (Equiv.Perm (Fin 16)) := (K1.subgroupOf N).map ρ
  obtain ⟨f, hfN, hf5, hffix, hft⟩ := exists_five D hF1 hF1M hF2 hF3 hF4 hF5
  have hNLM : N = normalizer (D.M : Set G) := normalizer_L_eq D hF1 hF1M hF2
  have hcardN : Nat.card ↥N = 1105920 := card_normalizer_L D hF1 hF1M hF2 hF4 hF5
  have ht0M : D.t0 ∈ D.M := t0_mem_M D hF3
  have ht0L : D.t0 ∉ D.L := t0_not_mem_L D hF3
  have hconj : ∀ x ∈ D.M, x * x = 1 → x ≠ 1 → x ∉ D.L →
      ∃ n ∈ N ⊓ centralizer ({z} : Set G), x = n * D.t0 * n⁻¹ :=
    fun x hx hx2 hx1 hxL => exists_conj_t0 D hF1 hF1M hF2 hF3 hx hx2 hx1 hxL
  have hcard288 : Nat.card {x : D.M // x * x = 1 ∧ x ≠ 1 ∧ (x : G) ∉ D.L} = 288 :=
    card_involutions_M D hF3
  obtain ⟨i, hi, hX16⟩ := exists_map_eq_X16 D hF1 hF6 hF6b hF9 hF11 (z_mem_L D hF1)
    hNLM hcardN ht0M ht0L hconj hcard288 hfN hf5 hffix hft
  refine ⟨i, hi, ?_⟩
  have hX_le : X ≤ X16 i := by
    rw [← hX16]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono N (inf_le_inf_left N D.AG_le_centralizer))
  have hT0K1 : D.T0G ≤ K1 :=
    le_inf (T0G_le_normalizer_L D hF1 hF5)
      (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  have hT0img : Nat.card ↥((D.T0G.subgroupOf N).map ρ) = 4 := by
    have hmul := card_map_bitAction_mul (L := D.L) (e := D.lEquiv hF1) (H := D.T0G)
      (T0G_le_normalizer_L D hF1 hF5)
    have hmul' : Nat.card ↥((D.T0G.subgroupOf N).map ρ) * 16 = 64 := by
      simpa [inf_T0G_centralizer_L D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8,
        card_T0G D, card_L D hF1] using hmul
    omega
  have h4 : 4 ∣ Nat.card ↥X := by
    have hle : (D.T0G.subgroupOf N).map ρ ≤ X :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono N hT0K1)
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [hT0img] at hdvd
  have hfAG : f ∈ D.AG :=
    CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd
      (Subgroup.mem_centralizer_singleton_iff.mpr hft) (by rw [hf5]; decide)
  have hfK1 : f ∈ K1 := ⟨hfN, hfAG⟩
  have hρf5 : orderOf (ρ ⟨f, hfN⟩) = 5 := by
    have hdvd : orderOf (ρ ⟨f, hfN⟩) ∣ 5 := by
      have h := orderOf_map_dvd ρ ⟨f, hfN⟩
      rw [← Subgroup.orderOf_coe] at h
      rwa [hf5] at h
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5'
    · exfalso
      have h1' : ρ ⟨f, hfN⟩ = 1 := orderOf_eq_one_iff.mp h1
      have hfC : f ∈ centralizer (D.L : Set G) :=
        (bitAction_eq_one_iff (D.lEquiv hF1) ⟨f, hfN⟩).mp h1'
      have hLbot : D.L = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro l hl
        exact hffix l hl (Subgroup.mem_centralizer_iff.mp hfC l hl).symm
      have hcardL := card_L D hF1
      rw [hLbot, Subgroup.card_bot] at hcardL
      norm_num at hcardL
    · exact h5'
  have hρfX : ρ ⟨f, hfN⟩ ∈ X := by
    rw [Subgroup.mem_map]
    exact ⟨⟨f, hfN⟩, Subgroup.mem_subgroupOf.mpr hfK1, rfl⟩
  have h5 : 5 ∣ Nat.card ↥X :=
    hρf5 ▸ Subgroup.orderOf_dvd_natCard X hρfX
  have h20 : 20 ∣ Nat.card ↥X := by
    have := Nat.lcm_dvd h4 h5
    norm_num at this ⊢
    exact this
  have hdvd60 : Nat.card ↥X ∣ 60 := by
    have := Subgroup.card_dvd_of_le hX_le
    rwa [(hF9.1 i hi).1] at this
  have hne20 : Nat.card ↥X ≠ 20 := card_ne_twenty hF11 hi hX_le
  have hcardX : Nat.card ↥X = 60 := by
    obtain ⟨k, hk⟩ := h20
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      exact Nat.card_pos.ne' hk
    have hle : 20 * k ≤ 60 := Nat.le_of_dvd (by norm_num) (hk ▸ hdvd60)
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · exact absurd (by simpa using hk) hne20
    · rw [hk] at hdvd60
      norm_num at hdvd60
    · omega
  exact Subgroup.eq_of_le_of_card_ge hX_le (by rw [hcardX, (hF9.1 i hi).1])

theorem exists_conj_L_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) {x y : G} (hx : x ∈ D.L)
    (hy : y ∈ D.L) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ k ∈ normalizer (D.L : Set G) ⊓ D.AG, k * x * k⁻¹ = y := by
  classical
  obtain ⟨i, hi, hX16⟩ := exists_X16_map_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  let e := D.lEquiv hF1
  let jx : Fin 16 := e.symm ⟨x, hx⟩
  let jy : Fin 16 := e.symm ⟨y, hy⟩
  have hzero : e 0 = (1 : ↥D.L) := by
    apply Subtype.ext
    exact (D.elt_eq_of_eq (D.l1Decs_le_invE (l1Elt_mem 0)) (one_mem (invE 1))
      l1Elt_zero).trans D.elt_one
  have hex : ((e jx : ↥D.L) : G) = x := by
    simp [jx]
  have hey : ((e jy : ↥D.L) : G) = y := by
    simp [jy]
  have hx0 : jx ≠ 0 := by
    intro h
    apply hx1
    have h1 : ((e jx : ↥D.L) : G) = ((e 0 : ↥D.L) : G) := by rw [h]
    rw [hzero, hex] at h1
    exact h1
  have hy0 : jy ≠ 0 := by
    intro h
    apply hy1
    have h1 : ((e jy : ↥D.L) : G) = ((e 0 : ↥D.L) : G) := by rw [h]
    rw [hzero, hey] at h1
    exact h1
  obtain ⟨g, hgX, hgj⟩ := X16_exists_smul_of_ne_zero hF9 hi hx0 hy0
  let N : Subgroup G := normalizer (D.L : Set G)
  let K1 : Subgroup G := N ⊓ D.AG
  let ρ : ↥N →* Equiv.Perm (Fin 16) := bitAction e
  have hgX' : g ∈ (K1.subgroupOf N).map ρ := by
    rw [show ((K1.subgroupOf N).map ρ) = X16 i from hX16]
    exact hgX
  obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp hgX'
  refine ⟨(n : G), (Subgroup.mem_subgroupOf.mp hn), ?_⟩
  have h := coe_bitAction_apply e n jx
  rw [hnk, hgj] at h
  rw [hex, hey] at h
  exact h.symm

theorem exists_conj_mem_T0G (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {e : G}
    (he : e ∈ D.AG) (he2 : e * e = 1) :
    ∃ a ∈ D.AG, a * e * a⁻¹ ∈ D.T0G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eA : ↥D.AG := ⟨e, he⟩
  let P : Subgroup ↥D.AG := Subgroup.zpowers eA
  have hP2 : IsPGroup 2 ↥P := by
    have hsq : eA * eA = 1 := Subtype.ext he2
    have hdvd : orderOf eA ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hcard : Nat.card ↥P = orderOf eA := Nat.card_zpowers eA
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (p := 2) (n := 0) (by rw [hcard, h1]; norm_num)
    · exact IsPGroup.of_card (p := 2) (n := 1) (by rw [hcard, h2]; norm_num)
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  have hQsyl : IsSylowOf 2 (Q.map D.AG.subtype) D.AG := ⟨Q, rfl⟩
  have hT0syl : IsSylowOf 2 D.T0G D.AG :=
    isSylow_T0G_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8
  obtain ⟨k, hkAG, hconj⟩ := hT0syl.exists_mem_conj hQsyl
  have heQ : e ∈ Q.map D.AG.subtype := by
    rw [Subgroup.mem_map]
    exact ⟨eA, hPQ (Subgroup.mem_zpowers eA), rfl⟩
  have hmem : k⁻¹ * e * k ∈ D.T0G := (hconj e).mp heQ
  refine ⟨k⁻¹, D.AG.inv_mem hkAG, ?_⟩
  simpa [mul_assoc] using hmem

theorem isConj_z_of_mem_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {e : G}
    (he : e ∈ D.AG) (he2 : e * e = 1) (he1 : e ≠ 1) : IsConj e z := by
  obtain ⟨a, ha, hae⟩ := exists_conj_mem_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 he he2
  set b : G := a * e * a⁻¹ with hb
  have hb2 : b * b = 1 := by
    rw [hb]
    calc (a * e * a⁻¹) * (a * e * a⁻¹) = a * (e * e) * a⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply he1
    calc e = a⁻¹ * (a * e * a⁻¹) * a := by group
      _ = 1 := by rw [← hb]; rw [h]; group
  have hT := isConj_of_mem_T0G D hF4 b hae hb2 hb1
  obtain ⟨c, hc⟩ := _root_.isConj_iff.mp hT
  exact _root_.isConj_iff.mpr ⟨c * a, by
    calc (c * a) * e * (c * a)⁻¹ = c * (a * e * a⁻¹) * c⁻¹ := by group
      _ = z := hc⟩

theorem isPGroup_centralizer_inf_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {e : G}
    (he : e ∈ D.AG) (he2 : e * e = 1) (he1 : e ≠ 1) :
    IsPGroup 2 ↥(centralizer ({e} : Set G) ⊓ D.AG) := by
  have hez : IsConj e z := isConj_z_of_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 he he2 he1
  have heD0 : e ∈ centralizer ({D.t0} : Set G) := D.AG_le_centralizer he
  have hC := isPGroup_centralizer_inf_of_isConj D hF3 heD0 he2 he1 hez
  exact hC.to_le (by
    intro x hx
    exact ⟨hx.1, D.AG_le_centralizer hx.2⟩)

private noncomputable def configT (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Sylow 2 ↥D.AG :=
  let h2 : IsPGroup 2 D.T0G := (D.isPGroup_TG hF3).to_le (T0G_le_TG D)
  (h2.comap_subtype).toSylow (by
    change ¬ 2 ∣ (D.T0G.subgroupOf D.AG).index
    exact D.not_two_dvd_relIndex_T0G hF1 hF1M hF2 hF3 hF4 hF5 hF8)

private theorem coe_configT (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) =
      D.T0G.subgroupOf D.AG :=
  rfl

private theorem card_configT (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Nat.card (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8) = 64 := by
  rw [show Nat.card (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8) =
      Nat.card ↥(D.T0G.subgroupOf D.AG) by rw [coe_configT]]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)).toEquiv]
  exact card_T0G D

private theorem Lsub_le_configT (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    D.L.subgroupOf D.AG ≤ (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) := by
  rw [coe_configT]
  intro x hx
  exact L_le_T0G D hF5 (Subgroup.mem_subgroupOf.mp hx)

private theorem Msub_le_configT (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    D.M2G.subgroupOf D.AG ≤ (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) := by
  rw [coe_configT]
  intro x hx
  exact M2G_le_T0G D hF5 (Subgroup.mem_subgroupOf.mp hx)

private theorem card_Lsub (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Nat.card ↥(D.L.subgroupOf D.AG) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)).toEquiv]
  exact card_L D hF1

private theorem card_Msub (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Nat.card ↥(D.M2G.subgroupOf D.AG) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)).toEquiv]
  exact card_M2G D hF1 hF5

private theorem Lsub_inf_Msub :
    D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG =
      (D.L ⊓ D.M2G).subgroupOf D.AG := by
  rw [← Subgroup.comap_subtype, ← Subgroup.comap_subtype, ← Subgroup.comap_inf,
    Subgroup.comap_subtype]

private theorem card_inf_Lsub_Msub (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Nat.card ↥(D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG) = 4 := by
  rw [Lsub_inf_Msub]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (le_trans inf_le_left (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8))).toEquiv]
  exact card_inf_M2G D hF5

private theorem config_eq_or_eq (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop)
    {E : Subgroup ↥D.AG} (hE : E ≤ configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
    (hEa : IsElemAbelian 2 E) (hE16 : Nat.card ↥E = 16) :
    E = D.L.subgroupOf D.AG ∨ E = D.M2G.subgroupOf D.AG := by
  have hEle : E ≤ D.T0G.subgroupOf D.AG := by
    rwa [coe_configT] at hE
  have hE'le : E.map D.AG.subtype ≤ D.T0G := by
    calc E.map D.AG.subtype ≤ (D.T0G.subgroupOf D.AG).map D.AG.subtype :=
          Subgroup.map_mono hEle
      _ = D.T0G ⊓ D.AG := Subgroup.subgroupOf_map_subtype _ _
      _ = D.T0G := inf_eq_left.mpr (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  have hE'a : IsElemAbelian 2 (E.map D.AG.subtype) := IsElemAbelian.map hEa _
  have hE'16 : Nat.card ↥(E.map D.AG.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective D.AG.subtype_injective, hE16]
  rcases eq_or_eq_of_le_T0G D hF1 hF5 hE'le hE'a hE'16 with h | h
  · left
    have hmap : E.map D.AG.subtype = (D.L.subgroupOf D.AG).map D.AG.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8), h]
    ext x
    constructor
    · intro hx
      have hx' : (x:G) ∈ E.map D.AG.subtype := ⟨x, hx, rfl⟩
      rw [hmap, Subgroup.map_subgroupOf_eq_of_le
        (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)] at hx'
      exact hx'
    · intro hx
      have hx' : (x:G) ∈ (D.L.subgroupOf D.AG).map D.AG.subtype := ⟨x, hx, rfl⟩
      rw [← hmap] at hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      rwa [show y = x from Subtype.ext hyx] at hy
  · right
    have hmap : E.map D.AG.subtype = (D.M2G.subgroupOf D.AG).map D.AG.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8), h]
    ext x
    constructor
    · intro hx
      have hx' : (x:G) ∈ E.map D.AG.subtype := ⟨x, hx, rfl⟩
      rw [hmap, Subgroup.map_subgroupOf_eq_of_le
        (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)] at hx'
      exact hx'
    · intro hx
      have hx' : (x:G) ∈ (D.M2G.subgroupOf D.AG).map D.AG.subtype := ⟨x, hx, rfl⟩
      rw [← hmap] at hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      rwa [show y = x from Subtype.ext hyx] at hy

private theorem config_inf_le_centralizer (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG ≤
      Subgroup.centralizer (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Set ↥D.AG) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hxG : (x:G) ∈ D.L ⊓ D.M2G := by
    have hx' : x ∈ (D.L ⊓ D.M2G).subgroupOf D.AG := by
      rwa [← Lsub_inf_Msub]
    exact hx'
  have hyG : (y:G) ∈ D.T0G := by
    have hy' : y ∈ (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) := hy
    rwa [coe_configT] at hy'
  exact Subgroup.mem_centralizer_iff.mp (inf_M2G_le_centralizer D hF5 hxG) (y:G) hyG

private theorem config_mul_self_mem (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ∀ x ∈ (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG),
      x * x ∈ D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG := by
  intro x hx
  rw [Lsub_inf_Msub]
  have hxG : (x:G) ∈ D.T0G := by
    rwa [coe_configT] at hx
  exact mul_self_mem_inf_M2G D hF5 (x:G) hxG

private theorem config_mem_or_mem (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ∀ x ∈ (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG),
      x * x = 1 → x ∈ D.L.subgroupOf D.AG ∨ x ∈ D.M2G.subgroupOf D.AG := by
  intro x hx hx2
  have hxG : (x:G) ∈ D.T0G := by
    rwa [coe_configT] at hx
  have hx2G : (x:G) * (x:G) = 1 := by
    simpa using congrArg (fun y : ↥D.AG => (y:G)) hx2
  rcases mem_or_mem_M2G D hF5 (x:G) hxG hx2G with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem map_subtype_centralizer_singleton (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop)
    (x : ↥D.AG) :
    (Subgroup.centralizer ({x} : Set ↥D.AG) ⊓ D.T0G.subgroupOf D.AG).map
        D.AG.subtype =
      Subgroup.centralizer ({(x:G)} : Set G) ⊓ D.T0G := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hcent : (z:G) ∈ Subgroup.centralizer ({(x:G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz.1))
    exact ⟨hcent, hz.2⟩
  · rintro ⟨hycent, hyT0⟩
    have hyAG : y ∈ D.AG := T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hyT0
    refine ⟨⟨y, hyAG⟩, ⟨?_, hyT0⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hycent))

private theorem config_centralizer_L (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    ∀ x ∈ D.L.subgroupOf D.AG, x ∉ D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG →
      Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
        (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) =
          D.L.subgroupOf D.AG := by
  intro x hxL hxZ
  have hxL' : (x:G) ∈ D.L := hxL
  have hxZ' : (x:G) ∉ D.L ⊓ D.M2G := by
    intro h
    apply hxZ
    rw [Lsub_inf_Msub]
    exact h
  have hG := centralizer_inf_T0G_L D hF1 hF5 (x:G) hxL' hxZ'
  have hmap : (Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
      (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG)).map D.AG.subtype =
      (D.L.subgroupOf D.AG).map D.AG.subtype := by
    rw [coe_configT,
      map_subtype_centralizer_singleton D hF1 hF1M hF2 hF3 hF4 hF5 hF8,
      hG, Subgroup.map_subgroupOf_eq_of_le (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)]
  ext y
  constructor
  · intro hy
    have hy' : (y:G) ∈ (Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
        (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG)).map
          D.AG.subtype := ⟨y, hy, rfl⟩
    rw [hmap] at hy'
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    rwa [show z = y from Subtype.ext hzy] at hz
  · intro hy
    have hy' : (y:G) ∈ (D.L.subgroupOf D.AG).map D.AG.subtype := ⟨y, hy, rfl⟩
    rw [← hmap] at hy'
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    rwa [show z = y from Subtype.ext hzy] at hz

private theorem config_centralizer_M (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    ∀ x ∈ D.M2G.subgroupOf D.AG, x ∉ D.L.subgroupOf D.AG ⊓ D.M2G.subgroupOf D.AG →
      Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
        (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG) =
          D.M2G.subgroupOf D.AG := by
  intro x hxM hxZ
  have hxM' : (x:G) ∈ D.M2G := hxM
  have hxZ' : (x:G) ∉ D.L ⊓ D.M2G := by
    intro h
    apply hxZ
    rw [Lsub_inf_Msub]
    exact h
  have hG := centralizer_inf_T0G_M2G D hF1 hF5 (x:G) hxM' hxZ'
  have hmap : (Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
      (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG)).map D.AG.subtype =
      (D.M2G.subgroupOf D.AG).map D.AG.subtype := by
    rw [coe_configT,
      map_subtype_centralizer_singleton D hF1 hF1M hF2 hF3 hF4 hF5 hF8,
      hG, Subgroup.map_subgroupOf_eq_of_le (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)]
  ext y
  constructor
  · intro hy
    have hy' : (y:G) ∈ (Subgroup.centralizer ({x} : Set ↥D.AG) ⊓
        (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8 : Subgroup ↥D.AG)).map
          D.AG.subtype := ⟨y, hy, rfl⟩
    rw [hmap] at hy'
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    rwa [show z = y from Subtype.ext hzy] at hz
  · intro hy
    have hy' : (y:G) ∈ (D.M2G.subgroupOf D.AG).map D.AG.subtype := ⟨y, hy, rfl⟩
    rw [← hmap] at hy'
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    rwa [show z = y from Subtype.ext hzy] at hz

private theorem config_isPGroup_centralizer (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop)
    (e : ↥D.AG) (he2 : e * e = 1) (he1 : e ≠ 1) :
    IsPGroup 2 ↥(Subgroup.centralizer ({e} : Set ↥D.AG)) := by
  have hmap : (Subgroup.centralizer ({e} : Set ↥D.AG)).map D.AG.subtype =
      Subgroup.centralizer ({(e:G)} : Set G) ⊓ D.AG := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hcent : (z:G) ∈ Subgroup.centralizer ({(e:G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz))
      exact ⟨hcent, z.2⟩
    · rintro ⟨hycent, hyAG⟩
      refine ⟨⟨y, hyAG⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hycent))
  have he2G : (e:G) * (e:G) = 1 := by
    simpa using congrArg (fun x : ↥D.AG => (x:G)) he2
  have he1G : (e:G) ≠ 1 := by
    intro h
    exact he1 (Subtype.ext h)
  have hbase := isPGroup_centralizer_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8
    e.2 he2G he1G
  rw [← hmap] at hbase
  exact hbase.of_equiv (Subgroup.equivMapOfInjective
    (Subgroup.centralizer ({e} : Set ↥D.AG)) D.AG.subtype D.AG.subtype_injective).symm

private theorem config_centralizer_L_le (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    Subgroup.centralizer (D.L.subgroupOf D.AG : Set ↥D.AG) ≤ D.L.subgroupOf D.AG := by
  intro x hx
  have hxG : (x:G) ∈ Subgroup.centralizer (D.L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlA : l ∈ D.AG := L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hl
    have hcomm := Subgroup.mem_centralizer_iff.mp hx (⟨l, hlA⟩ : ↥D.AG) hl
    exact congrArg Subtype.val hcomm
  have hxinf : (x:G) ∈ Subgroup.centralizer (D.L : Set G) ⊓ D.AG := ⟨hxG, x.2⟩
  rwa [centralizer_L_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8] at hxinf

private theorem config_centralizer_M_le (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF8 : F8Prop) :
    Subgroup.centralizer (D.M2G.subgroupOf D.AG : Set ↥D.AG) ≤ D.M2G.subgroupOf D.AG := by
  intro x hx
  have hτnorm : D.tauG ∈ normalizer (D.AG : Set G) := tauG_mem_normalizer_AG D hF5
  have hτinv : D.tauG⁻¹ ∈ normalizer (D.AG : Set G) := inv_mem hτnorm
  have hyAG : D.tauG⁻¹ * (x:G) * D.tauG ∈ D.AG := by
    have h := (Subgroup.mem_normalizer_iff.mp hτinv (x:G)).mp x.2
    simpa using h
  have hycent : D.tauG⁻¹ * (x:G) * D.tauG ∈ centralizer (D.L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlM2 : D.tauG * l * D.tauG⁻¹ ∈ D.M2G := by
      rw [M2G_eq_map D hF1 hF5]
      exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
    have hxcent : (x:G) ∈ centralizer (D.M2G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hmA : m ∈ D.AG := M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hm
      have hcomm := Subgroup.mem_centralizer_iff.mp hx (⟨m, hmA⟩ : ↥D.AG) hm
      exact congrArg Subtype.val hcomm
    have hcomm := Subgroup.mem_centralizer_iff.mp hxcent
      (D.tauG * l * D.tauG⁻¹) hlM2
    calc l * (D.tauG⁻¹ * (x:G) * D.tauG)
        = D.tauG⁻¹ * ((D.tauG * l * D.tauG⁻¹) * (x:G)) * D.tauG := by group
      _ = D.tauG⁻¹ * ((x:G) * (D.tauG * l * D.tauG⁻¹)) * D.tauG := by
          rw [hcomm]
      _ = (D.tauG⁻¹ * (x:G) * D.tauG) * l := by group
  have hyL : D.tauG⁻¹ * (x:G) * D.tauG ∈ D.L := by
    have hyinf : D.tauG⁻¹ * (x:G) * D.tauG ∈
        Subgroup.centralizer (D.L : Set G) ⊓ D.AG := ⟨hycent, hyAG⟩
    rwa [centralizer_L_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8] at hyinf
  have hxM : (x:G) ∈ D.M2G := by
    rw [M2G_eq_map D hF1 hF5]
    refine Subgroup.mem_map.mpr ⟨D.tauG⁻¹ * (x:G) * D.tauG, hyL, ?_⟩
    change D.tauG * (D.tauG⁻¹ * (x:G) * D.tauG) * D.tauG⁻¹ = (x:G)
    group
  exact hxM

private noncomputable def normalizerEquivOfLe (H : Subgroup G) (hH : H ≤ D.AG) :
    ↥(Subgroup.normalizer (H.subgroupOf D.AG : Set ↥D.AG)) ≃*
      ↥(Subgroup.normalizer (H : Set G) ⊓ D.AG) where
  toFun n := by
    refine ⟨(n.1 : G), ⟨?_, n.1.2⟩⟩
    change (n.1 : G) ∈ Subgroup.normalizer (H : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp n.2 (⟨l, hH hl⟩ : ↥D.AG)).mp hl
    · rw [Subgroup.card_map_of_injective (MulAut.conj (n.1 : G)).injective]
  invFun m := by
    refine ⟨⟨(m.1 : G), m.2.2⟩, ?_⟩
    change (⟨(m.1 : G), m.2.2⟩ : ↥D.AG) ∈
      Subgroup.normalizer (H.subgroupOf D.AG : Set ↥D.AG)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp m.2.1 (l : G)).mp hl
    · rw [Subgroup.card_map_of_injective
        (MulAut.conj (⟨(m.1 : G), m.2.2⟩ : ↥D.AG)).injective]
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv m := by
    apply Subtype.ext
    rfl
  map_mul' n m := by
    apply Subtype.ext
    rfl

private theorem config_exists_conj_L (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    ∀ x ∈ D.L.subgroupOf D.AG, ∀ y ∈ D.L.subgroupOf D.AG, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG),
        k * x * k⁻¹ = y := by
  intro x hx y hy hx1 hy1
  have hx1' : (x:G) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext h)
  have hy1' : (y:G) ≠ 1 := by
    intro h
    exact hy1 (Subtype.ext h)
  obtain ⟨k, hk, hkconj⟩ :=
    exists_conj_L_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
      hx hy hx1' hy1'
  let e := normalizerEquivOfLe D D.L (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  refine ⟨e.symm ⟨k, hk⟩, (e.symm ⟨k, hk⟩).2, ?_⟩
  apply Subtype.ext
  change k * (x:G) * k⁻¹ = (y:G)
  exact hkconj

private theorem config_exists_fpf_L (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ∃ f ∈ Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG),
      ∀ l ∈ D.L.subgroupOf D.AG, f * l = l * f → l = 1 := by
  obtain ⟨f, hfN, hf5, hffix, hft⟩ := exists_five D hF1 hF1M hF2 hF3 hF4 hF5
  have hfAG : f ∈ D.AG :=
    CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd
      (Subgroup.mem_centralizer_singleton_iff.mpr hft) (by rw [hf5]; decide)
  let e := normalizerEquivOfLe D D.L (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  refine ⟨e.symm ⟨f, ⟨hfN, hfAG⟩⟩, (e.symm ⟨f, ⟨hfN, hfAG⟩⟩).2, ?_⟩
  intro l hl hcomm
  have hcoe : ((e.symm ⟨f, ⟨hfN, hfAG⟩⟩ : ↥D.AG) : G) = f := rfl
  have hcomm' : f * (l:G) = (l:G) * f := by
    have h := congrArg (fun z : ↥D.AG => (z:G)) hcomm
    simp only [Subgroup.coe_mul] at h
    rwa [hcoe] at h
  exact Subtype.ext (hffix (l:G) hl hcomm')

private theorem config_exists_conj_M (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    ∀ x ∈ D.M2G.subgroupOf D.AG, ∀ y ∈ D.M2G.subgroupOf D.AG, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG),
        k * x * k⁻¹ = y := by
  intro x hx y hy hx1 hy1
  have hM2map : D.M2G = D.L.map (MulAut.conj D.tauG).toMonoidHom := M2G_eq_map D hF1 hF5
  have hxM : (x:G) ∈ D.M2G := hx
  have hyM : (y:G) ∈ D.M2G := hy
  rw [hM2map] at hxM hyM
  obtain ⟨x', hx'L, hx'x⟩ := Subgroup.mem_map.mp hxM
  obtain ⟨y', hy'L, hy'y⟩ := Subgroup.mem_map.mp hyM
  have hx'x' : D.tauG * x' * D.tauG⁻¹ = (x:G) := by
    simpa [MulAut.conj_apply] using hx'x
  have hy'y' : D.tauG * y' * D.tauG⁻¹ = (y:G) := by
    simpa [MulAut.conj_apply] using hy'y
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    rw [← hx'x', h]
    simp
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    apply Subtype.ext
    rw [← hy'y', h]
    simp
  obtain ⟨k, hk, hkconj⟩ :=
    exists_conj_L_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
      hx'L hy'L hx'1 hy'1
  let kM : G := D.tauG * k * D.tauG⁻¹
  have hkMnorm : kM ∈ Subgroup.normalizer (D.M2G : Set G) := by
    rw [hM2map, ← Subgroup.map_equiv_normalizer_eq (D.L : Subgroup G) (MulAut.conj D.tauG)]
    exact Subgroup.mem_map.mpr ⟨k, hk.1, rfl⟩
  have hkMA : kM ∈ D.AG := by
    have hτnorm : D.tauG ∈ Subgroup.normalizer (D.AG : Set G) :=
      tauG_mem_normalizer_AG D hF5
    exact (Subgroup.mem_normalizer_iff.mp hτnorm k).mp hk.2
  let e := normalizerEquivOfLe D D.M2G (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  refine ⟨e.symm ⟨kM, ⟨hkMnorm, hkMA⟩⟩,
    (e.symm ⟨kM, ⟨hkMnorm, hkMA⟩⟩).2, ?_⟩
  apply Subtype.ext
  change kM * (x:G) * kM⁻¹ = (y:G)
  calc kM * (x:G) * kM⁻¹ = D.tauG * (k * x' * k⁻¹) * D.tauG⁻¹ := by
        rw [← hx'x']
        simp only [kM]
        group
    _ = D.tauG * y' * D.tauG⁻¹ := by rw [hkconj]
    _ = (y:G) := hy'y'

private theorem config_exists_fpf_M (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ∃ f ∈ Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG),
      ∀ l ∈ D.M2G.subgroupOf D.AG, f * l = l * f → l = 1 := by
  obtain ⟨f, hfN, hf5, hffix, hft⟩ := exists_five D hF1 hF1M hF2 hF3 hF4 hF5
  have hfAG : f ∈ D.AG :=
    CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd
      (Subgroup.mem_centralizer_singleton_iff.mpr hft) (by rw [hf5]; decide)
  have hM2map : D.M2G = D.L.map (MulAut.conj D.tauG).toMonoidHom := M2G_eq_map D hF1 hF5
  let fM : G := D.tauG * f * D.tauG⁻¹
  have hfMnorm : fM ∈ Subgroup.normalizer (D.M2G : Set G) := by
    rw [hM2map, ← Subgroup.map_equiv_normalizer_eq (D.L : Subgroup G) (MulAut.conj D.tauG)]
    exact Subgroup.mem_map.mpr ⟨f, hfN, rfl⟩
  have hfMAG : fM ∈ D.AG := by
    have hτnorm : D.tauG ∈ Subgroup.normalizer (D.AG : Set G) :=
      tauG_mem_normalizer_AG D hF5
    exact (Subgroup.mem_normalizer_iff.mp hτnorm f).mp hfAG
  let e := normalizerEquivOfLe D D.M2G (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
  refine ⟨e.symm ⟨fM, ⟨hfMnorm, hfMAG⟩⟩, (e.symm ⟨fM, ⟨hfMnorm, hfMAG⟩⟩).2, ?_⟩
  intro l hl hcomm
  rw [hM2map] at hl
  obtain ⟨l', hl'L, hl'l⟩ := Subgroup.mem_map.mp hl
  have hl'l' : D.tauG * l' * D.tauG⁻¹ = (l:G) := by
    simpa [MulAut.conj_apply] using hl'l
  have hcomm' : f * l' = l' * f := by
    have h := congrArg (fun z : ↥D.AG => (z:G)) hcomm
    have h' : fM * (l:G) = (l:G) * fM := h
    rw [← hl'l'] at h'
    simp only [fM] at h'
    calc f * l' = D.tauG⁻¹ * (D.tauG * f * D.tauG⁻¹ * (D.tauG * l' * D.tauG⁻¹)) *
          D.tauG := by group
      _ = D.tauG⁻¹ * ((D.tauG * l' * D.tauG⁻¹) * (D.tauG * f * D.tauG⁻¹)) *
          D.tauG := by rw [h']
      _ = l' * f := by group
  have hl'1 : l' = 1 := hffix l' hl'L hcomm'
  apply Subtype.ext
  rw [← hl'l', hl'1]
  simp

private noncomputable abbrev configN (D : LocalData G z) : Subgroup G := normalizer (D.L : Set G)

private noncomputable abbrev configK1 (D : LocalData G z) : Subgroup G := configN D ⊓ D.AG

private noncomputable def configEL (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ↥(Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG)) ≃*
      ↥(configK1 D) :=
  normalizerEquivOfLe D D.L (L_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)

private noncomputable def configKMap (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {i : ℕ}
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    ↥(configK1 D) →* ↥(X16 i) :=
  let g : ↥(configK1 D) →* Equiv.Perm (Fin 16) :=
    (bitAction (D.lEquiv hF1)).comp
      (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D))
  g.codRestrict (X16 i) fun k => by
    have hmem : g k ∈ ((configK1 D).subgroupOf (configN D)).map
        (bitAction (D.lEquiv hF1)) := by
      rw [Subgroup.mem_map]
      exact ⟨Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D) k,
        Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    rwa [hX16] at hmem

private noncomputable def configQuotL
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    ↥(Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG)) →*
      alternatingGroup (Fin 5) :=
  (x16EquivA5 hF9 hi).toMonoidHom.comp
    ((configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16).comp
      (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8).toMonoidHom)

private theorem configKMap_surjective (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {i : ℕ}
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    Function.Surjective (configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16) := by
  intro x
  have hxmem : (x : Equiv.Perm (Fin 16)) ∈
      ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) := by
    rw [hX16]
    exact x.2
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxmem
  let k : ↥(configK1 D) := ⟨n.1, Subgroup.mem_subgroupOf.mp hn⟩
  have hk : Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D) k = n :=
    Subtype.ext rfl
  have hg : (bitAction (D.lEquiv hF1)).comp
      (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D)) k =
        (x : Equiv.Perm (Fin 16)) := by
    change (bitAction (D.lEquiv hF1))
      (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D) k) =
        (x : Equiv.Perm (Fin 16))
    rw [hk, hnx]
  refine ⟨k, ?_⟩
  apply Subtype.ext
  exact hg

private theorem configQuotL_surjective
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    Function.Surjective
      (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16) := by
  intro y
  obtain ⟨x, hx⟩ := (x16EquivA5 hF9 hi).surjective y
  obtain ⟨k, hk⟩ := configKMap_surjective D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16 x
  obtain ⟨n, hn⟩ := (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8).surjective k
  refine ⟨n, ?_⟩
  change (x16EquivA5 hF9 hi) (configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16
    (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = y
  rw [hn, hk, hx]

private theorem configQuotL_ker
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16).ker =
      (D.L.subgroupOf D.AG).subgroupOf
        (Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hn
    have h1 : configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16
        (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n) = 1 := by
      apply (x16EquivA5 hF9 hi).injective
      have h := hn
      change (x16EquivA5 hF9 hi) (configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16
        (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = 1 at h
      simpa using h
    have hρ : (bitAction (D.lEquiv hF1))
        (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D)
          (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = 1 := by
      have h := congrArg Subtype.val h1
      simpa [configKMap] using h
    have hcent : ((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 : G) ∈
        Subgroup.centralizer (D.L : Set G) :=
      (bitAction_eq_one_iff (D.lEquiv hF1)
        (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D)
          (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n))).mp hρ
    have hAG : ((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 : G) ∈ D.AG :=
      (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).2.2
    have hL : ((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 : G) ∈ D.L := by
      have hinf : ((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 : G) ∈
          Subgroup.centralizer (D.L : Set G) ⊓ D.AG := ⟨hcent, hAG⟩
      rwa [centralizer_L_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8] at hinf
    change ((n.1 : ↥D.AG) : G) ∈ D.L
    exact hL
  · intro hn
    have hnL : ((n.1 : ↥D.AG) : G) ∈ D.L := hn
    have hρ : (bitAction (D.lEquiv hF1))
        (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D)
          (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = 1 := by
      rw [bitAction_eq_one_iff]
      change ((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 : G) ∈
        Subgroup.centralizer (D.L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      change l * ((n.1 : ↥D.AG) : G) = ((n.1 : ↥D.AG) : G) * l
      haveI : IsMulCommutative ↥D.L := (D.isElemAbelian_L hF1).1
      simpa only [Subgroup.coe_mul] using
        (congrArg Subtype.val (mul_comm' (⟨((n.1 : ↥D.AG) : G), hnL⟩ : ↥D.L)
          ⟨l, hl⟩)).symm
    have h1 : configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16
        (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n) = 1 := by
      apply Subtype.ext
      change (bitAction (D.lEquiv hF1))
        (Subgroup.inclusion (inf_le_left : configK1 D ≤ configN D)
          (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = 1
      exact hρ
    have h := h1
    change (x16EquivA5 hF9 hi) (configKMap D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hX16
      (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n)) = 1
    rw [h, map_one]

private noncomputable abbrev configNM (D : LocalData G z) : Subgroup G :=
  normalizer (D.M2G : Set G)

private noncomputable abbrev configK1M (D : LocalData G z) : Subgroup G :=
  configNM D ⊓ D.AG

private theorem map_conj_tau_normalizer_L (hF1 : F1Prop) (hF5 : F5Prop) :
    (Subgroup.normalizer (D.L : Set G)).map (MulAut.conj D.tauG).toMonoidHom =
      Subgroup.normalizer (D.M2G : Set G) := by
  rw [M2G_eq_map D hF1 hF5]
  exact Subgroup.map_equiv_normalizer_eq (D.L : Subgroup G) (MulAut.conj D.tauG)

private theorem map_conj_tau_inv_normalizer_M (hF1 : F1Prop) (hF5 : F5Prop) :
    (Subgroup.normalizer (D.M2G : Set G)).map (MulAut.conj D.tauG⁻¹).toMonoidHom =
      Subgroup.normalizer (D.L : Set G) := by
  rw [M2G_eq_map D hF1 hF5,
    Subgroup.map_equiv_normalizer_eq (D.L.map (MulAut.conj D.tauG).toMonoidHom)
      (MulAut.conj D.tauG⁻¹), Subgroup.map_map]
  have hcomp : ((MulAut.conj D.tauG⁻¹).toMonoidHom).comp
      ((MulAut.conj D.tauG).toMonoidHom) = MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

private noncomputable def configELM (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ↥(Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG)) ≃*
      ↥(configK1M D) :=
  normalizerEquivOfLe D D.M2G (M2G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)

private theorem coe_configELM (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop)
    (m : ↥(Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG))) :
    (((configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m : ↥(configK1M D)) : G)) =
      (m.1 : G) := rfl

private noncomputable def configConjMtoL (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    ↥(Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG)) →*
      ↥(Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG)) where
  toFun m := by
    let kM : ↥(configK1M D) := configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m
    have hmN : (m.1 : G) ∈ Subgroup.normalizer (D.M2G : Set G) := by
      rw [← coe_configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m]
      exact kM.2.1
    have hmA : (m.1 : G) ∈ D.AG := by
      rw [← coe_configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m]
      exact kM.2.2
    have hyAG : D.tauG⁻¹ * (m.1 : G) * D.tauG ∈ D.AG := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (inv_mem (tauG_mem_normalizer_AG D hF5)) (m.1 : G)).mp hmA
      simpa using h
    have hyNormL : D.tauG⁻¹ * (m.1 : G) * D.tauG ∈
        Subgroup.normalizer (D.L : Set G) := by
      rw [← map_conj_tau_inv_normalizer_M D hF1 hF5]
      exact Subgroup.mem_map.mpr ⟨(m.1 : G), hmN, by simp [MulAut.conj_apply]⟩
    exact (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8).symm
      ⟨D.tauG⁻¹ * (m.1 : G) * D.tauG, ⟨hyNormL, hyAG⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change D.tauG⁻¹ * (1 : G) * D.tauG = 1
    group
  map_mul' := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    change D.tauG⁻¹ * ((a : G) * (b : G)) * D.tauG =
      (D.tauG⁻¹ * (a : G) * D.tauG) * (D.tauG⁻¹ * (b : G) * D.tauG)
    group

private theorem configConjMtoL_surjective (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    Function.Surjective (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8) := by
  intro n
  have hnN : (n.1 : G) ∈ Subgroup.normalizer (D.L : Set G) := by
    have hnK : (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).1 ∈ configK1 D :=
      (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).2
    rw [← show (((configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n :
      ↥(configK1 D)) : G)) = (n.1 : G) from rfl]
    exact hnK.1
  have hnA : (n.1 : G) ∈ D.AG := (configEL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n).2.2
  have hmAG : D.tauG * (n.1 : G) * D.tauG⁻¹ ∈ D.AG :=
    (Subgroup.mem_normalizer_iff.mp (tauG_mem_normalizer_AG D hF5) (n.1 : G)).mp hnA
  have hmNormM : D.tauG * (n.1 : G) * D.tauG⁻¹ ∈
      Subgroup.normalizer (D.M2G : Set G) := by
    rw [← map_conj_tau_normalizer_L D hF1 hF5]
    exact Subgroup.mem_map.mpr ⟨(n.1 : G), hnN, by simp [MulAut.conj_apply]⟩
  let m : ↥(Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG)) :=
    (configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8).symm
      ⟨D.tauG * (n.1 : G) * D.tauG⁻¹, ⟨hmNormM, hmAG⟩⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  dsimp [configConjMtoL]
  change D.tauG⁻¹ * (m.1 : G) * D.tauG = (n.1 : G)
  have hmcoe : (m.1 : G) = D.tauG * (n.1 : G) * D.tauG⁻¹ := by
    change (((configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8
      ((configELM D hF1 hF1M hF2 hF3 hF4 hF5 hF8).symm
        ⟨D.tauG * (n.1 : G) * D.tauG⁻¹, ⟨hmNormM, hmAG⟩⟩) : ↥(configK1M D)) : G)) =
      D.tauG * (n.1 : G) * D.tauG⁻¹
    simp
  rw [hmcoe]
  group

private noncomputable def configQuotM
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    ↥(Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG)) →*
      alternatingGroup (Fin 5) :=
  (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16).comp
    (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8)

private theorem configQuotM_surjective
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    Function.Surjective
      (configQuotM D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16) := by
  intro y
  obtain ⟨n, hn⟩ := configQuotL_surjective D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b
    hF8 hF9 hF11 hi hX16 y
  obtain ⟨m, hm⟩ := configConjMtoL_surjective D hF1 hF1M hF2 hF3 hF4 hF5 hF8 n
  refine ⟨m, ?_⟩
  change (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16)
    (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m) = y
  rw [hm, hn]

private theorem configQuotM_ker
    (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop)
    (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    (hX16 : ((configK1 D).subgroupOf (configN D)).map (bitAction (D.lEquiv hF1)) =
      X16 i) :
    (configQuotM D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16).ker =
      (D.M2G.subgroupOf D.AG).subgroupOf
        (Subgroup.normalizer (D.M2G.subgroupOf D.AG : Set ↥D.AG)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hker := configQuotL_ker D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16
  have hcomp : configQuotM D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16 m =
      configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16
        (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m) := rfl
  rw [hcomp]
  have hin : configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16
        (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m) = 1 ↔
      (configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m) ∈
        (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16).ker :=
    Iff.rfl
  rw [hin, hker, Subgroup.mem_subgroupOf]
  have hcoe : (((configConjMtoL D hF1 hF1M hF2 hF3 hF4 hF5 hF8 m :
      ↥(Subgroup.normalizer (D.L.subgroupOf D.AG : Set ↥D.AG))) : ↥D.AG) : G) =
      D.tauG⁻¹ * (m.1 : G) * D.tauG := by
    dsimp [configConjMtoL]
    rfl
  constructor
  · intro hm
    rw [Subgroup.mem_subgroupOf] at hm
    rw [hcoe] at hm
    let xG : G := ((m : ↥D.AG) : G)
    have hm' : D.tauG⁻¹ * xG * D.tauG ∈ D.L := by
      simpa [xG] using hm
    have hmM2 : xG ∈ D.L.map (MulAut.conj D.tauG).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨D.tauG⁻¹ * xG * D.tauG, hm', ?_⟩
      change D.tauG * (D.tauG⁻¹ * xG * D.tauG) * D.tauG⁻¹ = xG
      group
    rw [Subgroup.mem_subgroupOf]
    change xG ∈ D.M2G
    rwa [M2G_eq_map D hF1 hF5]
  · intro hm
    rw [Subgroup.mem_subgroupOf] at hm
    let xG : G := ((m : ↥D.AG) : G)
    have hmG : xG ∈ D.M2G := by
      simpa [xG] using hm
    have hmM2 : xG ∈ D.L.map (MulAut.conj D.tauG).toMonoidHom := by
      rwa [M2G_eq_map D hF1 hF5] at hmG
    obtain ⟨l, hl, hlm⟩ := Subgroup.mem_map.mp hmM2
    have hlm' : D.tauG * l * D.tauG⁻¹ = xG := by
      simpa [MulAut.conj_apply] using hlm
    rw [Subgroup.mem_subgroupOf]
    rw [hcoe]
    have heq : D.tauG⁻¹ * xG * D.tauG = l := by
      rw [← hlm']
      group
    rw [heq]
    exact hl

theorem exists_config (hF1 : F1Prop)
    (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop)
    (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    ∃ C : CFSG.Quasithin.L34CIT.Config ↥D.AG,
      (C.T : Subgroup ↥D.AG) = D.T0G.subgroupOf D.AG ∧ C.L = D.L.subgroupOf D.AG ∧
        C.M = D.M2G.subgroupOf D.AG := by
  classical
  obtain ⟨i, hi, hX16⟩ :=
    exists_X16_map_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  let C : CFSG.Quasithin.L34CIT.Config ↥D.AG :=
    { T := (configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      L := (D.L.subgroupOf D.AG)
      M := (D.M2G.subgroupOf D.AG)
      card_T := (card_configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      L_le := (Lsub_le_configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      M_le := (Msub_le_configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      isElemAbelian_L := (IsElemAbelian.subgroupOf (D.isElemAbelian_L hF1) D.AG)
      isElemAbelian_M := (IsElemAbelian.subgroupOf (D.isElemAbelian_M2G hF1 hF5) D.AG)
      card_L := (card_Lsub D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      card_M := (card_Msub D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      eq_or_eq := (fun E hE hEa hE16 => config_eq_or_eq D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hE hEa hE16)
      card_inf := (card_inf_Lsub_Msub D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      inf_le_centralizer := (config_inf_le_centralizer D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      mul_self_mem := (config_mul_self_mem D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      mem_or_mem := (config_mem_or_mem D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      centralizer_L := (config_centralizer_L D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8)
      centralizer_M := (config_centralizer_M D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8)
      isPGroup_centralizer := (config_isPGroup_centralizer D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      centralizer_L_le := (config_centralizer_L_le D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8)
      centralizer_M_le := (config_centralizer_M_le D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF8)
      quotL := (configQuotL D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16)
      quotL_surjective := (configQuotL_surjective D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b
        hF8 hF9 hF11 hi hX16)
      ker_quotL := (configQuotL_ker D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16)
      quotM := (configQuotM D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16)
      quotM_surjective := (configQuotM_surjective D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b
        hF8 hF9 hF11 hi hX16)
      ker_quotM := (configQuotM_ker D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 hi hX16)
      exists_conj_L := (config_exists_conj_L D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11)
      exists_conj_M := (config_exists_conj_M D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11)
      exists_fpf_L := (config_exists_fpf_L D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
      exists_fpf_M := (config_exists_fpf_M D hF1 hF1M hF2 hF3 hF4 hF5 hF8) }
  refine ⟨C, ?_, ?_, ?_⟩
  · exact coe_configT D hF1 hF1M hF2 hF3 hF4 hF5 hF8
  · rfl
  · rfl

end CFSG.Sporadic.SuzRecog.SuzL34.LocalData
