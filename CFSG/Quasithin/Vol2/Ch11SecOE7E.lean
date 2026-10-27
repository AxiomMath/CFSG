module

public import CFSG.Quasithin.Vol2.Ch11SecOE7D
public import CFSG.Quasithin.Vol2.Ch11SecE3LieLow
public import CFSG.Quasithin.Vol2.Ch3E213MP4C5
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.Quasithin.Vol2.Ch3E213MP4C4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple le_nParam_of_almostSimple)

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

include hJ hf hcard hfixed in
theorem psu_nonabelian : ∃ a b : ProjectiveSpecialUnitaryMatrixGroup J, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hN : Subgroup.normalizer ((rootU J hJ : Subgroup _) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_
    rw [show g * h * g⁻¹ = h by rw [hc g h]; group]
  rw [Ch3E213M.P4C.normalizer_root_eq J hf hcard hfixed hJ] at hN
  exact (Ch3E213M.P4C.isCoatom_stabilizer J hf hcard hfixed hJ).1 hN

end Model

theorem coe_smul_sylow {X : Type*} [Group X] {p : ℕ} (g : X) (S : Sylow p X) :
    ((g • S : Sylow p X) : Subgroup X) = A1b.conjSub g (S : Subgroup X) := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  rfl

theorem conjSub_sup' {X : Type*} [Group X] (g : X) (A B : Subgroup X) :
    A1b.conjSub g (A ⊔ B) = A1b.conjSub g A ⊔ A1b.conjSub g B :=
  Subgroup.map_sup A B _

theorem conjSub_top' {X : Type*} [Group X] (g : X) : A1b.conjSub g (⊤ : Subgroup X) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

section Transport

variable {G : Type} [Group G] [Finite G]

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

abbrev psuEmb {L : Subgroup G} (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J →* G :=
  L.subtype.comp e.symm.toMonoidHom

omit [Finite G] [Finite K] in
theorem psuEmb_injective {L : Subgroup G} (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Function.Injective (psuEmb J e) :=
  L.subtype_injective.comp e.symm.injective

omit [Finite G] [Finite K] in
theorem psuEmb_range {L : Subgroup G} (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (psuEmb J e).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

include hJ hf hcard hfixed in
theorem exists_conj_rootU_eq {L T : Subgroup G} [L.Normal] (hT : quasithinIsSylowTwo T)
    (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      (A1b.conjSub g (rootU J hJ)).map (psuEmb J e) = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨S, hS⟩, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  set ψ := psuEmb J e with hψdef
  have hψi := psuEmb_injective J e
  have hψr := psuEmb_range J e
  set P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := (T ⊓ L).comap ψ with hPdef
  have hUP : P.map ψ = T ⊓ L := Subgroup.map_comap_eq_self (hψr ▸ inf_le_right)
  have hP2 : IsPGroup 2 P := IsPGroup.comap_of_injective (hT.1.to_inf_left) ψ hψi
  have hPidx : ¬ 2 ∣ P.index := by
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (hT.1.toSylow hT.2) (N := L)
    have hQidx := Q.not_dvd_index
    have e1 : P = ((T ⊓ L).subgroupOf L).comap e.symm.toMonoidHom := by
      rw [hPdef, hψdef, ← Subgroup.comap_comap]
      rfl
    rw [e1, Subgroup.index_comap_of_surjective _ e.symm.surjective]
    rwa [hQ] at hQidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S
    (hP2.toSylow hPidx)
  refine ⟨g, ?_⟩
  have h1 := coe_smul_sylow g S
  rw [hg, hS] at h1
  change P = _ at h1
  rw [← h1, hUP]

include hJ hf hcard hfixed in
theorem le_sup_conjSub_of_psu3 {L T : Subgroup G} [L.Normal] (hT : quasithinIsSylowTwo T)
    (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) {l : G} (hl : l ∈ L)
    (hne : A1b.conjSub l (T ⊓ L) ≠ T ⊓ L) : L ≤ (T ⊓ L) ⊔ A1b.conjSub l (T ⊓ L) := by
  obtain ⟨g, hg⟩ := exists_conj_rootU_eq J hJ hf hcard hfixed hT e
  set ψ := psuEmb J e with hψdef
  set U := T ⊓ L with hU
  set P := A1b.conjSub g (rootU J hJ) with hP
  set M : ProjectiveSpecialUnitaryMatrixGroup J := e ⟨l, hl⟩ with hM
  have hψM : ψ M = l := by simp [hψdef, hM]
  have hcU : A1b.conjSub l U = (A1b.conjSub M P).map ψ := by
    rw [SecE3.map_conjSub, hψM, hg]
  have hMP : A1b.conjSub M P ≠ P := fun hc => hne (by rw [hcU, hc, hg])
  have e1 : A1b.conjSub M P = A1b.conjSub g (A1b.conjSub (g⁻¹ * M * g) (rootU J hJ)) := by
    rw [hP, ← A1b.conjSub_mul, ← A1b.conjSub_mul]
    congr 1
    group
  have hM' : A1b.conjSub (g⁻¹ * M * g) (rootU J hJ) ≠ rootU J hJ := fun hc =>
    hMP (by rw [e1, hc])
  have hPtop : P ⊔ A1b.conjSub M P = ⊤ := by
    rw [e1, hP, ← conjSub_sup', rootU_sup_conjSub_eq_top J hJ hf hcard hfixed hM', conjSub_top']
  rw [hcU, ← hg, ← Subgroup.map_sup, hPtop, ← MonoidHom.range_eq_map, psuEmb_range]

include hJ hf hcard hfixed in
theorem le_nParam_of_psu3 {L T : Subgroup G} (h : AlmostSimple L) (hT : quasithinIsSylowTwo T)
    (hLT : L ⊔ T = ⊤) (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (f : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨g, hg⟩ := exists_conj_rootU_eq J hJ hf hcard hfixed hT e
  set U : Subgroup G := T ⊓ L with hUdef
  set ψ := psuEmb J e with hψdef
  have hψi := psuEmb_injective J e
  set A : Subgroup G := (A1b.conjSub g (rootZ J hJ)).map ψ with hAdef
  have hAU : A ≤ U := by
    rw [← hg]
    exact Subgroup.map_mono (A1b.conjSub_mono g (rootZ_le_rootU J hJ))
  have hA : IsElemAbelian 2 A :=
    isElemAbelian_map' ψ (isElemAbelian_map' _ (isElemAbelian_rootZ J hJ))
  have hAcard : Nat.card A = 2 ^ f := by
    rw [hAdef, Subgroup.card_map_of_injective hψi, SecE3.card_conjSub, card_rootZ J hJ hfixed]
  have hA1 : A ≠ ⊥ := by
    intro h0
    have h1 : Nat.card A = 1 := by rw [h0, Subgroup.card_bot]
    have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have hUA : U ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hg]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hxy := commute_of_mem_rootZ J hJ hy hx
    rw [← map_mul ψ, ← map_mul ψ, ← map_mul, ← map_mul, hxy]
  have huniq : ∀ x : G, A1b.conjSub x A ≤ T → A1b.conjSub x A = A := by
    intro x hx
    have hxL : A1b.conjSub x A ≤ L := by
      rintro _ ⟨u, hu, rfl⟩
      show x * u * x⁻¹ ∈ L
      exact hLn.conj_mem u (hAU hu).2 x
    have hxU : A1b.conjSub x A ≤ U := le_inf hx hxL
    have hle : A1b.conjSub x A ≤ A := by
      intro z hz
      have hz2 : z ^ 2 = 1 := (isElemAbelian_map' _ hA).2 z hz
      have hzU : z ∈ U := hxU hz
      rw [← hg] at hzU
      obtain ⟨w, hw, rfl⟩ := hzU
      have hw' : g⁻¹ * w * g ∈ rootU J hJ := A1b.mem_conjSub_iff.mp hw
      have hwsq : w ^ 2 = 1 := hψi (by rw [map_pow, hz2, map_one])
      have hw2 : (g⁻¹ * w * g) ^ 2 = 1 := by
        rw [sq] at hwsq ⊢
        rw [show g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g by group, hwsq]
        group
      refine ⟨w, ?_, rfl⟩
      rw [SetLike.mem_coe, A1b.mem_conjSub_iff]
      exact mem_rootZ_of_sq_eq_one J hJ hw' hw2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [SecE3.card_conjSub]
  have hNA : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    rw [← A1b.conjSub_eq_iff_mem_normalizer]
    refine huniq x ((A1b.conjSub_mono x hAU).trans ?_)
    rw [A1b.conjSub_eq_iff_mem_normalizer.mpr hx]
    exact inf_le_left
  exact le_nParam_of_almostSimple h ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
    hLT inf_le_left hAU inf_le_right hA hA1 hAcard hf hUA huniq SecE3.le_normalizer_inf hNA
    fun l hl hne => le_sup_conjSub_of_psu3 J hJ hf hcard hfixed hT e hl hne

theorem two_le_of_isPSU {X : Type} [Group X] {n : ℕ} (h : IsPSU 3 2 n X) : 2 ≤ n := by
  obtain ⟨⟨-, hn1, -, hne⟩, -⟩ := h
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact hne (by simp)

theorem le_nParam_of_isPSU3 {T : Subgroup G} {n : ℕ}
    (hU : IsPSU 3 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hn := two_le_of_isPSU hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hU
  obtain ⟨J, hJ, -, hfix⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := k) 2 n hk
  obtain ⟨e'⟩ := CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J (2 ^ n) hk hfix
  set e₁ := e.trans e'.symm with he₁
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := psu_nonabelian J hJ hn hk hfix
    refine ⟨e₁.symm x, e₁.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e₁ hc
  exact le_nParam_of_psu3 J hJ hn hk hfix
    (SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT) hT hFT e₁

end Transport

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
