module

public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.Quasithin.Background.A312SporJ1Inputs
public import CFSG.Quasithin.Background.E2TwoProofSporJ1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.J1Centralizer
public import Certificates.Certificate7128
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

section Centralizer

variable {G H : Type} [Group G] [Group H]

theorem map_centralizer_equiv (e : G ≃* H) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show e y * e g = e g * e y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx

theorem map_centralizer_subtype {M : Type} [Group M] (P : Subgroup M) (x : ↥P) :
    (Subgroup.centralizer ({x} : Set ↥P)).map P.subtype =
      CFSG.Sporadic.Schreier.centralizerIn P (x : M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
    CFSG.Sporadic.Schreier.centralizerIn, Subgroup.mem_inf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hyP, hy⟩
    exact ⟨⟨y, hyP⟩, Subtype.ext hy, rfl⟩

end Centralizer

section J1

open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Quasithin.A312S.J1
open CFSG.Sporadic.J1

theorem false_of_solvable_member {Γ : Type} [Group Γ] [Finite Γ] {S B Y : Subgroup Γ}
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hs : Group.IsSolvable ↥Y) : False :=
  not_isSolvable_sup hB (hY ▸ hs)

theorem j1_case15
    {j : ℕ} (hj : j < 17)
    (h15 : (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! = 15)
    {B : Subgroup ↥J} (hB : B ∈ lFamily j1S) (hY : B ⊔ j1S = j1Y j) :
    A312Case B ⊤ := by
  have hcardY : Nat.card (j1Y j) = 120 := by rw [j1_Y_card hj, h15]; norm_num
  obtain ⟨u, -, hou, hYle⟩ := (Certificates.certificate7128 (j1Y j)
    (by rw [j1_S_eq]; exact j1_S_le_Y j)).2 hcardY
  set t : CFSG.Blueprint.NativeSporadic.J1 := nativeEquiv.symm u with ht
  have hot : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq]; exact hou
  set u' : Equiv.Perm (Fin 3080) :=
    ((CFSG.Sporadic.Schreier.j1PermEquiv t : CFSG.Sporadic.Schreier.j1P) :
      Equiv.Perm (Fin 3080)) with hu'
  have hu'P : u' ∈ CFSG.Sporadic.Schreier.j1P := (CFSG.Sporadic.Schreier.j1PermEquiv t).2
  have hou' : orderOf u' = 2 := by
    rw [hu', Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hot
  obtain ⟨h120, -, -⟩ := CFSG.Sporadic.Schreier.j1P_involution_centralizer u' hu'P hou'
  set φ := CFSG.Sporadic.Schreier.j1PermEquiv with hφ
  have hCt : Nat.card (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)) =
      120 := by
    have e1 : Nat.card (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)) =
        Nat.card ((Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)).map
          φ.toMonoidHom) := (Subgroup.card_map_of_injective φ.injective).symm
    rw [map_centralizer_equiv φ t] at e1
    have e2 : Nat.card (Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)) =
        Nat.card ((Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)).map
          CFSG.Sporadic.Schreier.j1P.subtype) :=
      (Subgroup.card_map_of_injective CFSG.Sporadic.Schreier.j1P.subtype_injective).symm
    rw [map_centralizer_subtype] at e2
    rw [e1, e2, ← h120]
  have hCu : Nat.card (Subgroup.centralizer ({u} : Set ↥J)) = 120 := by
    have e1 := map_centralizer_equiv nativeEquiv t
    have hut' : nativeEquiv t = u := by rw [ht, MulEquiv.apply_symm_apply]
    rw [hut'] at e1
    rw [← e1, Subgroup.card_map_of_injective nativeEquiv.injective, hCt]
  have hYeq : j1Y j = Subgroup.centralizer ({u} : Set ↥J) :=
    Subgroup.eq_of_le_of_card_ge hYle (by rw [hCu, hcardY])
  obtain ⟨K, -, hKs, hK60, hKna, -⟩ :=
    CFSG.Sporadic.Schreier.qt_unique_j1_involution_centralizer_normal_simple_subgroup t hot
  set KJ : Subgroup ↥J :=
    (K.map (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)).subtype).map
      nativeEquiv.toMonoidHom with hKJ
  have eK : ↥KJ ≃* ↥K :=
    ((K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      ((K.map _).equivMapOfInjective nativeEquiv.toMonoidHom nativeEquiv.injective)).symm
  have hKJ60 : Nat.card ↥KJ = 60 := by rw [Nat.card_congr eK.toEquiv, hK60]
  have hKJle : KJ ≤ j1Y j := by
    rw [hYeq]
    have h1 := map_centralizer_equiv nativeEquiv t
    rw [ht, MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← ht]
    exact Subgroup.map_mono (Subgroup.map_subtype_le K)
  have hKJs : IsSimpleGroup ↥KJ := eK.isSimpleGroup
  have hperf : ⁅KJ, KJ⁆ = KJ := Seven.perfect_of_equiv_simple hKna eK
  have hpc : perfectCore (j1Y j) = KJ :=
    perfectCore_eq_of_index_two hKJle (by rw [hcardY, hKJ60]) hperf
  have hpc' : perfectCore (B ⊔ j1S) = KJ := by rw [hY, hpc]
  have : IsSimpleGroup ↥(perfectCore (B ⊔ j1S)) := by rw [hpc']; exact hKJs
  have hA5 : IsAlt 5 ↥B := isAlt5_of_perfectCore hB (by rw [hpc', hKJ60])
  iterate 13 right
  left
  exact ⟨hA5, ⟨Subgroup.topEquiv.trans nativeEquiv.symm⟩⟩

theorem j1_solvable21 :
    Group.IsSolvable ↥(j1Y 16) := by
  have hcY : Nat.card (j1Y 16) = 168 := by rw [j1_Y_card (by norm_num)]; rfl
  have hSY : j1S ≤ j1Y 16 := j1_S_le_Y 16
  have hYN : j1Y 16 ≤ Subgroup.normalizer (j1S : Set ↥J) := by
    have h := (Certificates.certificate7128 (j1Y 16) (by rw [j1_S_eq]; exact hSY)).1 hcY
    rwa [j1_S_eq] at h
  have hSs : Group.IsSolvable ↥j1S := by
    have := (j1_S_isPGroup).isNilpotent
    infer_instance
  refine isSolvable_of_normal hSY hYN hSs ?_
  intro _
  have hcS : Nat.card ↥(j1S.subgroupOf (j1Y 16)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, j1_card_S]
    rfl
  have hq : Nat.card (↥(j1Y 16) ⧸ j1S.subgroupOf (j1Y 16)) = 3 ^ 1 * 7 ^ 1 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (j1S.subgroupOf (j1Y 16))
    rw [hcY, hcS] at h
    omega
  let _ : Fintype (↥(j1Y 16) ⧸ j1S.subgroupOf (j1Y 16)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three
    (q := 7) (by norm_num) (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hq)

theorem a312For_J1
    (hq : CFSG.IsQuasisimple ↥J) : A312For ↥J := by
  refine a312For_of_members hq j1_sylow j1_all fun j hj B hB hY => ?_
  have hj17 : j < 17 := by simpa using hj
  have hc := j1_Y_card hj17
  have h23 : ∀ {a b : ℕ}, Nat.card (j1Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    false_of_solvable_member hB hY
      (isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) h)
  have h27 : ∀ {a b : ℕ}, Nat.card (j1Y j) = 2 ^ a * 7 ^ b → False := fun h =>
    false_of_solvable_member hB hY
      (isSolvable_of_card_pq Nat.prime_two (by norm_num) (by norm_num) h)
  interval_cases j
  · exact (h23 (a := 3) (b := 0) (by rw [hc]; rfl)).elim
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  · exact (h27 (a := 3) (b := 1) (by rw [hc]; rfl)).elim
  · exact (h23 (a := 3) (b := 1) (by rw [hc]; rfl)).elim
  · exact j1_case15 (by norm_num) (by rfl) hB hY
  all_goals first
    | exact (h23 (a := 3) (b := 1) (by rw [hc]; rfl)).elim
    | exact (false_of_solvable_member hB hY j1_solvable21).elim

theorem famJ1 :
    FamJ1 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* ↥J := e.trans nativeEquiv
  exact A312For.of_mulEquiv e' (a312For_J1 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end J1

end CFSG.Quasithin.A312S
