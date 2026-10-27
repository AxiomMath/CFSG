module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen
public import CFSG.RankThree.PartTwo.Sec4.HeringK419U33Data
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocU33
public import CFSG.Milestones.ASVolI.F4Small
import all CFSG.Milestones.ASVolI.F4Small
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Quasithin HeringK419 HeringK419U33
open Item419Res3
open scoped commutatorElement
open CFSG.Assembly.RankThreeEven (projSU)


namespace HeringK419U33

@[expose] def pwG (w : List ℕ) : U33G := (w.map u33GenPG).prod

section Certs


theorem phi_pwG (w : List ℕ) : u33PresHom (pwG w) = pwP w := by
  unfold pwG pwP
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => u33PresHom_genPG i

@[expose] def xg : U33G := u33GenPG 3

@[expose] def yg : U33G := u33GenPG 4

@[expose] def xg' : U33G := pwG wX'

@[expose] def S3 : Subgroup U33G := Subgroup.closure {xg, xg'}

theorem phi_xg : u33PresHom xg = pwP [3] := by
  rw [xg, u33PresHom_genPG]
  simp [pwP]

theorem phi_yg : u33PresHom yg = pwP [4] := by
  rw [yg, u33PresHom_genPG]
  simp [pwP]

theorem phi_xg' : u33PresHom xg' = pwP wX' := phi_pwG _

theorem Epm_zero : Epm 0 = 1 := by
  simp [Epm, Ew, pwP]

theorem mem_S3 : ∀ g ∈ S3, ∃ i : Fin 27, u33PresHom g = Epm i := by
  intro g hg
  refine Subgroup.closure_induction_right (p := fun g _ => ∃ i : Fin 27, u33PresHom g = Epm i)
    ?_ ?_ ?_ hg
  · exact ⟨0, by rw [map_one, Epm_zero]⟩
  · rintro g _ y hy ⟨i, hi⟩
    obtain ⟨⟨j₁, h₁⟩, ⟨j₂, h₂⟩, -, -⟩ := Epm_closed i
    rcases hy with rfl | rfl
    · exact ⟨j₁, by rw [map_mul, hi, phi_xg, h₁]⟩
    · exact ⟨j₂, by rw [map_mul, hi, phi_xg', h₂]⟩
  · rintro g _ y hy ⟨i, hi⟩
    obtain ⟨-, -, ⟨j₃, h₃⟩, ⟨j₄, h₄⟩⟩ := Epm_closed i
    rcases hy with rfl | rfl
    · exact ⟨j₃, by rw [map_mul, map_inv, hi, phi_xg, ← h₃]; group⟩
    · exact ⟨j₄, by rw [map_mul, map_inv, hi, phi_xg', ← h₄]; group⟩

theorem S3_cube : ∀ g ∈ S3, g ^ 3 = 1 := by
  intro g hg
  obtain ⟨i, hi⟩ := mem_S3 g hg
  apply u33PresHom_injective
  rw [map_pow, map_one, hi]
  exact Epm_cube i

theorem S3_isPGroup : IsPGroup 3 S3 := fun g =>
  ⟨1, Subtype.ext (by simpa using S3_cube g g.2)⟩

theorem xg_mem : xg ∈ S3 := Subgroup.subset_closure (by simp)

theorem xg'_mem : xg' ∈ S3 := Subgroup.subset_closure (by simp)

theorem xg_xg'_ne : xg * xg' ≠ xg' * xg := fun h => x_x'_ne (by
  have := congrArg u33PresHom h
  simpa only [map_mul, phi_xg, phi_xg'] using this)

theorem card_S3 : Nat.card S3 = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := S3_isPGroup.exists_card_eq
  have hdvd : Nat.card S3 ∣ 6048 := by
    rw [← card_u33Pres]
    exact Subgroup.card_subgroup_dvd_card S3
  have hn3 : n ≤ 3 := by
    by_contra h
    push Not at h
    have h4 : 3 ^ 4 ∣ 3 ^ n := pow_dvd_pow 3 h
    rw [← hn] at h4
    have := h4.trans hdvd
    norm_num at this
  have hnn : 3 ≤ n := by
    by_contra h
    push Not at h
    have hcomm : ∀ a b : S3, a * b = b * a := by
      interval_cases n
      · intro a b
        have : Subsingleton S3 := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
        exact Subsingleton.elim _ _
      · have hc : IsCyclic S3 := isCyclic_of_prime_card (p := 3) (by simpa using hn)
        intro a b
        letI := IsCyclic.commGroup (α := S3)
        exact mul_comm a b
      · exact IsPGroup.commutative_of_card_eq_prime_sq hn
    exact xg_xg'_ne (congrArg Subtype.val (hcomm ⟨xg, xg_mem⟩ ⟨xg', xg'_mem⟩))
  rw [hn, le_antisymm hn3 hnn]
  norm_num

@[expose] noncomputable def S3sylow : Sylow 3 U33G :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  S3_isPGroup.toSylow (by
    have h := Subgroup.card_mul_index S3
    rw [card_S3, card_u33Pres] at h
    have : S3.index = 224 := by omega
    rw [this]
    omega)

theorem exists_conj_mem_S3 {z : U33G} (hz3 : z ^ 3 = 1) : ∃ g : U33G, g * z * g⁻¹ ∈ S3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : IsPGroup 3 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  obtain ⟨T, hzT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U33G S3sylow T
  have hzT' : z ∈ (T : Subgroup U33G) := hzT (Subgroup.mem_zpowers z)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzT'
  have hS : g⁻¹ * z * g ∈ (S3sylow : Subgroup U33G) := by
    simpa [MulAut.smul_def, mul_assoc] using hzT'
  have hS' : g⁻¹ * z * g⁻¹⁻¹ ∈ (S3sylow : Subgroup U33G) := by simpa using hS
  exact ⟨g⁻¹, hS'⟩

theorem exists_conj_xg_or_yg {z : U33G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ c : U33G, c * z * c⁻¹ = xg ∨ c * z * c⁻¹ = yg := by
  obtain ⟨g, hg⟩ := exists_conj_mem_S3 hz3
  obtain ⟨i, hi⟩ := mem_S3 _ hg
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]
    group
  rcases Epm_table i with h1 | h2
  · exact absurd (u33PresHom_injective (by rw [hi, h1, map_one])) hne
  · set w := (conjTable.getD i ([], false)).1 with hw
    refine ⟨pwG w * g, ?_⟩
    have key : u33PresHom (pwG w * (g * z * g⁻¹) * (pwG w)⁻¹) =
        pwP (if (conjTable.getD i ([], false)).2 then [4] else [3]) := by
      rw [map_mul, map_mul, map_inv, phi_pwG, hi, h2]
      group
    have hmul : pwG w * g * z * (pwG w * g)⁻¹ = pwG w * (g * z * g⁻¹) * (pwG w)⁻¹ := by group
    rw [hmul]
    cases hb : (conjTable.getD i ([], false)).2
    · left
      apply u33PresHom_injective
      rw [key, phi_xg, hb]
      rfl
    · right
      apply u33PresHom_injective
      rw [key, phi_yg, hb]
      rfl

theorem hasTwoWitness_xg : HasTwoWitness xg := by
  refine ⟨Subgroup.closure GoldC3.u33NSet, u33_syl.1.to_le GoldC3.u33NSet_le_T,
    fun t ht => (Subgroup.mem_normalizer_iff.mp (GoldC3.u33_conj_N 3) t).mp ht, u33GenPG 0,
    Subgroup.subset_closure ⟨1, 0, by rw [u33PresHom_genPG]; simp⟩, fun h => GoldC3.u33_comm_ne ?_⟩
  have h1 : u33PresHom (xg * u33GenPG 0 * xg⁻¹) = u33PresHom (u33GenPG 0) := by rw [h]
  rw [map_mul, map_mul, map_inv, xg, u33PresHom_genPG, u33PresHom_genPG] at h1
  have h2 : u33GenP 3 * u33GenP 0 = u33GenP 0 * u33GenP 3 := by
    have := congrArg (· * u33GenP 3) h1
    simpa [mul_assoc] using this
  have h3 : ⁅u33GenP 0, u33GenP 3⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h2.symm
  rw [h3, commutatorElement_one_left, one_pow]

theorem y_moves : ∃ i ∈ CFSG.ASVolI.ChF.burnsideF4c_qIdx,
    u33GenP 4 * u33Tel u33GenP i ≠ u33Tel u33GenP i * u33GenP 4 := by
  decide +kernel

theorem hasTwoWitness_yg : HasTwoWitness yg := by
  obtain ⟨i, hi, hne⟩ := y_moves
  refine ⟨Subgroup.closure CFSG.ASVolI.ChF.burnsideF4c_Qset,
    u33_syl.1.to_le CFSG.ASVolI.ChF.burnsideF4c_Qset_le_T,
    fun t ht => (Subgroup.mem_normalizer_iff.mp
      (CFSG.ASVolI.ChF.burnsideF4c_gen_norm 4 (by simp)) t).mp ht,
    u33Tel u33GenPG i, Subgroup.subset_closure ⟨i, hi, rfl⟩, fun h => hne ?_⟩
  have h1 : u33PresHom (yg * u33Tel u33GenPG i * yg⁻¹) = u33PresHom (u33Tel u33GenPG i) := by
    rw [h]
  rw [map_mul, map_mul, map_inv, u33Tel_hom, yg, u33PresHom_genPG] at h1
  have := congrArg (· * u33GenP 4) h1
  simpa [mul_assoc] using this

theorem hasTwoWitness_u33G {z : U33G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : HasTwoWitness z := by
  obtain ⟨c, hc⟩ := exists_conj_xg_or_yg hz3 hz1
  rcases hc with hc | hc
  · exact hasTwoWitness_of_conj c⁻¹ xg z (by rw [← hc]; group) hasTwoWitness_xg
  · exact hasTwoWitness_of_conj c⁻¹ yg z (by rw [← hc]; group) hasTwoWitness_yg

end Certs

end HeringK419U33

theorem k419AutThreeInnerU33_holds :
    K419AutThreeInnerU33 := by
  intro k hk3 hk1
  have hU : CFSG.Open.StatedClassicalModel (projSU 3 3 1) .PSU 3 3 1 := by
    refine ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1), inferInstance,
      inferInstance, ?_, ⟨projSUEquivStatedProj 3 3 1⟩⟩
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_mulEquiv_u33G_of_statedClassicalModel
      hU
  exact hasTwoWitness_of_mulEquiv e (HeringK419U33.hasTwoWitness_u33G
    (by rw [← map_pow, hk3, map_one]) (fun h => hk1 (EmbeddingLike.map_eq_one_iff.mp h)))

end CFSG.RankThree.PartTwo.Sec4
