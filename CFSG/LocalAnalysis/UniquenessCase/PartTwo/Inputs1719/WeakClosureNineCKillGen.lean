module

public import CFSG.RankThree.PartOne.K159.InnLayerComb
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914.Kill

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

theorem le_centralizer_of_commutator_mem_center {L K : Subgroup X} (hL : Group.IsPerfect ↥L)
    (h : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ (center ↥L).map L.subtype) :
    K ≤ centralizer (L : Set X) := by
  have hZc : ∀ a ∈ (center ↥L).map L.subtype, ∀ b ∈ L, b * a = a * b := by
    rintro _ ⟨z, hz, rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b, hb⟩)
  have hLK : ⁅L, K⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator hL ?_
    have h1 : ⁅L, K⁆ ≤ (center ↥L).map L.subtype := by
      rw [commutator_le]
      intro l hl k hk
      rw [← commutatorElement_inv]
      exact inv_mem (h k hk l hl)
    have h2 : ⁅(center ↥L).map L.subtype, L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
        mem_centralizer_iff.mpr fun b hb => hZc a ha b hb
    exact le_bot_iff.mp (h2 ▸ commutator_mono_left h1)
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLK)

theorem le_of_not_le_centralizer {L D K : Subgroup X} (hq : CFSG.IsQuasisimple ↥L)
    (hLD : L ≤ normalizer (D : Set X)) (hKD : K ≤ D) (hKL : K ≤ normalizer (L : Set X))
    (hK : ¬ K ≤ centralizer (L : Set X)) : L ≤ D := by
  have hn : ((D ⊓ L).subgroupOf L).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact fun l hl => NFW.mem_normalizer_inf (hLD hl) (le_normalizer hl)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hZ
  · intro l hl
    have h : (⟨l, hl⟩ : ↥L) ∈ (D ⊓ L).subgroupOf L := htop ▸ mem_top _
    exact (mem_subgroupOf.mp h).1
  · refine absurd (le_centralizer_of_commutator_mem_center hq.1 fun k hk l hl => ?_) hK
    have hcD : k * l * k⁻¹ * l⁻¹ ∈ D := by
      have h1 : l * k⁻¹ * l⁻¹ ∈ D := (mem_normalizer_iff.mp (hLD hl) k⁻¹).mp (inv_mem (hKD hk))
      simpa [mul_assoc] using mul_mem (hKD hk) h1
    have hcL : k * l * k⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((mem_normalizer_iff.mp (hKL hk) l).mp hl) (inv_mem hl)
    exact ⟨⟨_, hcL⟩, hZ (mem_subgroupOf.mpr ⟨hcD, hcL⟩), rfl⟩

theorem isPGroup_iSup_inf_centralizer [Finite X] {ι : Type*} [Finite ι] {p : ℕ}
    [hp : Fact p.Prime] (L : ι → Subgroup X)
    (hcomm : ∀ i j, L i ≠ L j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hz : ∀ i, IsPGroup p ↥(L i ⊓ centralizer (L i : Set X))) :
    IsPGroup p ↥((⨆ i, L i) ⊓ centralizer ((⨆ i, L i : Subgroup X) : Set X)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hsup : (Finset.univ.image L).sup id = ⨆ i, L i := by
    rw [Finset.sup_image, Function.id_comp, Finset.sup_univ_eq_iSup]
  have hcomm' : ∀ Y ∈ Finset.univ.image L, ∀ Y' ∈ Finset.univ.image L, Y ≠ Y' →
      ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a := by
    intro Y hY Y' hY' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hY'
    exact hcomm i j hne
  rw [IsPGroup.iff_orderOf]
  rintro ⟨z, hz'⟩
  rw [orderOf_mk]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos z).ne' fun {q} hq hqz => ?_⟩
  by_contra hqp
  refine CFSG.RankThree.PartOne.K159.noP_finset_sup hq _ hcomm' ?_ z (by rw [hsup]; exact hz')
    hqz
  intro Y hY w hw hqw
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hY
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hz i) ⟨w, hw⟩
  rw [orderOf_mk] at hk
  rw [hk] at hqw
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow hqw))

theorem mem_of_isSylowIn_of_le_normalizer [Finite X] {p : ℕ} [Fact p.Prime]
    {R C : Subgroup X} (hR : IsSylowIn p R C) (hCR : C ≤ normalizer (R : Set X)) {y : X}
    (hyC : y ∈ C) {j : ℕ} (hy : y ^ p ^ j = 1) : y ∈ R := by
  have hn : (hR.toSylow : Subgroup ↥C).Normal := by
    rw [IsSylowIn.coe_toSylow]
    exact (normal_subgroupOf_iff_le_normalizer hR.le).mpr hCR
  have h : (⟨y, hyC⟩ : ↥C) ∈ (hR.toSylow : Subgroup ↥C) :=
    CFSG.GroupTheory.mem_sylow_of_pow_eq_one hn (k := j) (Subtype.ext (by simpa using hy))
  rw [IsSylowIn.coe_toSylow] at h
  exact mem_subgroupOf.mp h

theorem exists_pow_two_mem_of_sup {P S : Subgroup X} (hHP : P ⊔ S ≤ normalizer (P : Set X))
    (hS : IsPGroup 2 ↥S) {h : X} (hh : h ∈ P ⊔ S) : ∃ j : ℕ, h ^ 2 ^ j ∈ P := by
  have : (P.subgroupOf (P ⊔ S)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHP
  have hsup : P.subgroupOf (P ⊔ S) ⊔ S.subgroupOf (P ⊔ S) = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hS' : IsPGroup 2 ↥(S.subgroupOf (P ⊔ S)) :=
    hS.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  obtain ⟨j, hj⟩ := UniquenessCase.PartTwo.NF914.isPGroup_quotient_of_sup_eq_top hS' hsup
    (QuotientGroup.mk' (P.subgroupOf (P ⊔ S)) ⟨h, hh⟩)
  refine ⟨j, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hj
  simpa using hj

theorem exists_relCent {H Y R : Subgroup X} (hY : H ≤ normalizer (Y : Set X))
    (hR : H ≤ normalizer (R : Set X)) :
    ∃ M : Subgroup X, M ≤ H ∧ H ≤ normalizer (M : Set X) ∧
      ∀ h ∈ H, (h ∈ M ↔ ∀ y ∈ Y, h * y * h⁻¹ * y⁻¹ ∈ R) := by
  let M : Subgroup X :=
    { carrier := {h | h ∈ H ∧ ∀ y ∈ Y, h * y * h⁻¹ * y⁻¹ ∈ R}
      one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun y hy => ?_⟩
        have h1 : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ ∈ R :=
          (mem_normalizer_iff.mp (hR ha) _).mp (hb' y hy)
        have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
            a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
        rw [e]
        exact R.mul_mem h1 (ha' y hy)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun y hy => ?_⟩
        have hy' : a⁻¹ * y * a ∈ Y := by
          simpa using (mem_normalizer_iff.mp (hY (H.inv_mem ha)) y).mp hy
        have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by
          group
        rw [e]
        exact R.inv_mem (ha' _ hy') }
  have hmem : ∀ h, h ∈ M ↔ h ∈ H ∧ ∀ y ∈ Y, h * y * h⁻¹ * y⁻¹ ∈ R := fun h => Iff.rfl
  refine ⟨M, fun h hh => ((hmem h).mp hh).1, ?_, fun h hh => ?_⟩
  · refine NFW.le_normalizer_of_conj_mem fun g hg h hh => (hmem _).mpr ⟨?_, fun y hy => ?_⟩
    · exact H.mul_mem (H.mul_mem hg ((hmem h).mp hh).1) (H.inv_mem hg)
    · have hy' : g⁻¹ * y * g ∈ Y := by
        simpa using (mem_normalizer_iff.mp (hY (H.inv_mem hg)) y).mp hy
      have h1 := (mem_normalizer_iff.mp (hR hg) _).mp (((hmem h).mp hh).2 _ hy')
      have e : g * h * g⁻¹ * y * (g * h * g⁻¹)⁻¹ * y⁻¹ =
          g * (h * (g⁻¹ * y * g) * h⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact h1
  · exact ⟨fun hm => ((hmem h).mp hm).2, fun hm => (hmem h).mpr ⟨hh, hm⟩⟩

theorem eq_bot_of_le_of_isPGroup_three {K Z : Subgroup X} (hK : IsPGroup 2 ↥K)
    (hZ : IsPGroup 3 ↥Z) (hKZ : K ≤ Z) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact disjoint_self.mp ((IsPGroup.disjoint_of_ne 2 3 (by norm_num) K Z hK hZ).mono_right hKZ)

end CFSG.LocalAnalysis.WeakClosure81.TC914.Kill
