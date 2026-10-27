module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4MTor

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace L436

theorem exists_sl2_mulVec_single {F : Type} [Field F] {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F,
      (M : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = w := by
  by_cases ha : w 0 = 0
  · have hb : w 1 ≠ 0 := fun hb => hw (funext fun i => by fin_cases i <;> simp [ha, hb])
    refine ⟨⟨!![0, -(w 1)⁻¹; w 1, 0], by simp [Matrix.det_fin_two, hb]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [ha, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], by simp [Matrix.det_fin_two, ha]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec {F : Type} [Field F] {w₀ w : Fin 2 → F} (h₀ : w₀ ≠ 0) (hw : w ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F).mulVec w₀ = w := by
  obtain ⟨M₀, h₀'⟩ := exists_sl2_mulVec_single h₀
  obtain ⟨M, hM⟩ := exists_sl2_mulVec_single hw
  refine ⟨M * M₀⁻¹, ?_⟩
  rw [← h₀', Matrix.mulVec_mulVec, ← hM]
  congr 1
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

variable {G : Type} [Group G]

theorem eq_of_sp4Coord {n : ℕ} {P S R V : Subgroup G} (hc : Sp4Coord n P S R)
    (hcomm : ⁅R, perfectCore P⁆ = R) (hVR : V ≤ R)
    (hN : perfectCore P ≤ Subgroup.normalizer (V : Set G))
    (hC : ¬ perfectCore P ≤ Subgroup.centralizer (V : Set G)) : V = R := by
  obtain ⟨F, _, _, -, α, β, hαs, -, -, hβk, heq, -, -⟩ := hc
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v₀ : G, ∃ h : v₀ ∈ V, β ⟨v₀, hVR h⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hC
    intro ℓ hℓ
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (hβk ⟨v, hVR hv⟩).mp (hall v hv)
    exact (Subgroup.mem_centralizer_iff.mp this.2 ℓ hℓ).symm
  have hdec : ∀ r : ↥R, ∃ v ∈ V, ∃ c ∈ sp4C P R, (r : G) = v * c := by
    intro r
    by_cases hr : β r = 1
    · exact ⟨1, V.one_mem, r, (hβk r).mp hr, (one_mul _).symm⟩
    · have hw₀ : Multiplicative.toAdd (β ⟨v₀, hVR hv₀V⟩) ≠ 0 := fun h => hv₀ (by
        rw [← toAdd_eq_zero]
        exact h)
      have hw : Multiplicative.toAdd (β r) ≠ 0 := fun h => hr (by
        rw [← toAdd_eq_zero]
        exact h)
      obtain ⟨M, hM⟩ := exists_sl2_mulVec hw₀ hw
      obtain ⟨ℓ, hℓ⟩ := hαs (specialLinearGroupEquivStatedSL 2 F M)
      have hv₁V : (ℓ : G) * v₀ * (ℓ : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hN ℓ.2) v₀).mp hv₀V
      have hβv₁ := heq ℓ ⟨v₀, hVR hv₀V⟩ ⟨_, hVR hv₁V⟩ (by simp)
      rw [hℓ, specialLinearGroupEquivStatedSL_coe, hM] at hβv₁
      refine ⟨_, hv₁V, ((ℓ : G) * v₀ * (ℓ : G)⁻¹)⁻¹ * r, ?_, by group⟩
      have hc : β (⟨_, hVR hv₁V⟩⁻¹ * r) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβv₁, neg_add_cancel, toAdd_one]
      exact (hβk _).mp hc
  refine le_antisymm hVR ?_
  rw [← hcomm, Subgroup.commutator_le]
  intro r hr ℓ hℓ
  obtain ⟨v, hv, c, hc, hrvc⟩ := hdec ⟨r, hr⟩
  have hcℓ : c * ℓ = ℓ * c := Subgroup.mem_centralizer_iff.mp hc.2 ℓ hℓ |>.symm
  have hrvc' : r = v * c := hrvc
  have e : ⁅r, ℓ⁆ = v * (ℓ * v⁻¹ * ℓ⁻¹) := by
    rw [commutatorElement_def, hrvc']
    calc v * c * ℓ * (v * c)⁻¹ * ℓ⁻¹ = v * (c * ℓ) * c⁻¹ * v⁻¹ * ℓ⁻¹ := by group
      _ = v * (ℓ * c) * c⁻¹ * v⁻¹ * ℓ⁻¹ := by rw [hcℓ]
      _ = v * (ℓ * v⁻¹ * ℓ⁻¹) := by group
  rw [e]
  refine V.mul_mem hv ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN hℓ) v⁻¹).mp (V.inv_mem hv)

theorem natural_of_sp4Coord {n : ℕ} {P S V : Subgroup G} (hV : V = pCoreOf 2 (perfectCore P))
    (h : Sp4Coord n P S V) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (perfectCore P) V (sp4C P V) (CFSG.pCore 2 ↥(perfectCore P))
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F) := by
  obtain ⟨F, _, _, hF, α, β, hαs, hαk, hβs, hβk, heq, -, -⟩ := h
  refine ⟨F, inferInstance, inferInstance, hF, ?_, α, hαs, ?_, β, hβs, ?_, heq⟩
  · rw [hV]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  · ext ℓ
    rw [MonoidHom.mem_ker, hαk, hV]
    exact Subgroup.mem_map_iff_mem (perfectCore P).subtype_injective
  · ext v
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]

section Pullback

variable {Y : Type} [Group Y] (ι : Y →* G) (hι : Function.Injective ι)
include hι

theorem isSylowTwoOf_of_map {A B : Subgroup Y} (h : IsSylowTwoOf (A.map ι) (B.map ι)) :
    IsSylowTwoOf A B := by
  refine ⟨(Subgroup.map_le_map_iff_of_injective hι).mp h.1,
    h.2.1.of_equiv (A.equivMapOfInjective ι hι).symm, ?_⟩
  change ¬ 2 ∣ A.relIndex B
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hι]
  exact h.2.2

theorem isParabolic2_comap {K Q : Subgroup G} (hK : K = ι.range) (h : IsParabolic2 K Q) :
    IsParabolic2 ⊤ (Q.comap ι) := by
  obtain ⟨hQK, S₁, hS₁, hN⟩ := h
  have hS₁K : S₁ ≤ ι.range := hK ▸ hS₁.1
  refine ⟨le_top, S₁.comap ι, ?_, ?_⟩
  · apply isSylowTwoOf_of_map ι hι
    rw [Subgroup.map_comap_eq_self hS₁K, ← MonoidHom.range_eq_map, ← hK]
    exact hS₁
  · rw [← Subgroup.map_le_map_iff_of_injective hι, map_inf_normalizer ι hι,
      Subgroup.map_comap_eq_self hS₁K, Subgroup.map_comap_eq_self (hK ▸ hQK),
      ← MonoidHom.range_eq_map, ← hK]
    exact hN

theorem isParabolic2_map {K : Subgroup G} {Q : Subgroup Y} (hK : K = ι.range)
    (h : IsParabolic2 ⊤ Q) : IsParabolic2 K (Q.map ι) := by
  obtain ⟨-, S₂, hS₂, hN⟩ := h
  refine ⟨hK ▸ Subgroup.map_le_range ι Q, S₂.map ι, ?_, ?_⟩
  · rw [hK, MonoidHom.range_eq_map]
    exact isSylowTwoOf_map ι hι hS₂
  · rw [hK, MonoidHom.range_eq_map, ← map_inf_normalizer ι hι]
    exact Subgroup.map_mono hN

theorem isMaxParabolic2_comap {K P : Subgroup G} (hK : K = ι.range) (h : IsMaxParabolic2 K P) :
    IsMaxParabolic2 ⊤ (P.comap ι) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  have hPK : P ≤ ι.range := hK ▸ hpar.1
  refine ⟨isParabolic2_comap ι hι hK hpar, fun htop => hne ?_, fun Q hQ hQne hPQ => ?_⟩
  · rw [← Subgroup.map_comap_eq_self hPK, htop, ← MonoidHom.range_eq_map, ← hK]
  · have hQK : Q.map ι ≠ K := fun hQK => hQne (Subgroup.map_injective hι (by
      rw [hQK, hK, MonoidHom.range_eq_map]))
    have hPQ' : P ≤ Q.map ι := by
      rw [← Subgroup.map_comap_eq_self hPK]
      exact Subgroup.map_mono hPQ
    have h1 := hmax (Q.map ι) (isParabolic2_map ι hι hK hQ) hQK hPQ'
    rw [← h1, Subgroup.comap_map_eq_self_of_injective hι]

end Pullback

end L436

namespace Sp4M

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.Quasithin.Lie2Parabolic L436
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem tau_map_Q0_le : (Q2 F 0).map (tauEquiv (F := F)).toMonoidHom ≤ Q2 F 1 := by
  rintro _ ⟨g, hg, rfl⟩
  exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_two hg

theorem tau_map_Q1_le : (Q2 F 1).map (tauEquiv (F := F)).toMonoidHom ≤ Q2 F 0 := by
  rintro _ ⟨g, hg, rfl⟩
  exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_one hg

theorem map_tau_Q1 : (Q2 F 1).map (tauEquiv (F := F)).toMonoidHom = Q2 F 0 := by
  refine Subgroup.eq_of_le_of_card_ge tau_map_Q1_le ?_
  rw [Subgroup.card_map_of_injective (f := (tauEquiv (F := F)).toMonoidHom)
    (tauEquiv (F := F)).injective]
  calc Nat.card ↥(Q2 F 0) = Nat.card ↥((Q2 F 0).map (tauEquiv (F := F)).toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := (tauEquiv (F := F)).toMonoidHom)
          (tauEquiv (F := F)).injective).symm
    _ ≤ Nat.card ↥(Q2 F 1) := Subgroup.card_le_of_le tau_map_Q0_le

theorem map_tau_R1 :
    (pCoreOf 2 (perfectCore (Q2 F 1))).map (tauEquiv (F := F)).toMonoidHom =
      pCoreOf 2 (perfectCore (Q2 F 0)) := by
  rw [← pCoreOf_map_of_injective (tauEquiv (F := F)).toMonoidHom (tauEquiv (F := F)).injective,
    CFSG.Quasithin.map_perfectCore, map_tau_Q1]

theorem sp4Coord_zero (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Sp4Coord n (Q2 F 0) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 0))) := by
  have h := (sp4Coord_one hn hF).map (tauEquiv (F := F)).toMonoidHom
    (tauEquiv (F := F)).injective
  rwa [map_tau_Q1, CFSG.Quasithin.F134.Sp4.map_tauEquiv_unipotent, map_tau_R1] at h

theorem sp4K₂_eq (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    sp4K₂ ⊤ (Q2 F 1) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 1))) =
      perfectCore (Q2 F 0) := by
  rw [sp4K₂, sp4Z_eq hn hF, top_inf_eq, normalizer_XC]

theorem sp4Q₁_eq (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    sp4Q₁ ⊤ (Q2 F 1) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 1))) =
      pCoreOf 2 (perfectCore (Q2 F 0)) := by
  rw [sp4Q₁, sp4K₂_eq hn hF]

theorem sp4ParConcl_Q1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Sp4ParConcl n ⊤ (Q2 F 1) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 1))) where
  V_eq := rfl
  V_sq := by
    intro v hv
    obtain ⟨C, -, rfl⟩ := exists_rad1_of_mem_R1 hn hF hv
    rw [sq, rad1_mul']
    have h2 : C + C = 0 := by
      ext i k
      exact CharTwo.add_self_eq_zero _
    rw [h2, rad1_zero]
  card_V := card_R1 hn hF
  comm_V := commutator_pCoreOf_perfectCore_Q2 hn hF 1
  card_C := by rw [sp4C_eq hn hF, card_XAB, hF]
  S_le := unipotent_le_perfectCore (NQCat.exists_finset_card_four_of_card hn hF) 1
  S_syl := CFSG.Quasithin.F134.Sp4.isSylowTwoOf_unipotent
  card_Z := by rw [sp4Z_eq hn hF, card_XC, hF]
  C_inf_Z := by rw [sp4C_eq hn hF, sp4Z_eq hn hF, inf_comm, XC_inf_XAB]
  cent_S := by rw [R1_inf_centralizer_U hn hF, sp4C_eq hn hF, sp4Z_eq hn hF, sup_comm]
  K₂_le := by
    rw [sp4K₂_eq hn hF, sp4Z_eq hn hF]
    exact L0_le_centralizer_XC
  sup_eq := by
    rw [sp4K₂_eq hn hF, sup_comm]
    exact perfectCore_sup_eq_top ⟨n, hF⟩ (NQCat.exists_finset_card_four_of_card hn hF)
  V_le_K₂ := by
    rw [sp4K₂_eq hn hF]
    exact (R1_le_unipotent hn hF).trans
      (unipotent_le_perfectCore (NQCat.exists_finset_card_four_of_card hn hF) 0)
  K₂_closure := by
    rw [sp4K₂_eq hn hF]
    exact conjClosure_R1_L0 hn hF
  psl := by
    rw [sp4K₂_eq hn hF]
    exact psl0 hn hF
  natural := by
    rw [sp4K₂_eq hn hF, sp4Q₁_eq hn hF, sp4Z_eq hn hF, ← R0_inf_centralizer_L0 hn hF]
    exact natural_of_sp4Coord rfl (sp4Coord_zero hn hF)
  Q₁_closure := by
    rw [sp4C_eq hn hF, sp4K₂_eq hn hF, sp4Q₁_eq hn hF]
    exact conjClosure_XAB_L0 hn hF
  card_Q₁ := by
    rw [sp4Q₁_eq hn hF]
    exact card_R0 hn hF
  Q₁_cent := by
    rw [sp4Q₁_eq hn hF, sp4K₂_eq hn hF, sp4Z_eq hn hF]
    exact R0_inf_centralizer_L0 hn hF
  S_eq := by
    rw [sp4Q₁_eq hn hF]
    exact unipotent_eq_sup hn hF
  V_inf_Q₁ := by rw [sp4Q₁_eq hn hF, sp4C_eq hn hF, sp4Z_eq hn hF, R1_inf_R0 hn hF, sup_comm]
  V_cent_Q₁ := by
    rw [sp4Q₁_eq hn hF]
    exact R1_inf_centralizer_R0 hn hF
  Q₁_cent_V := by
    rw [sp4Q₁_eq hn hF]
    exact R0_inf_centralizer_R1 hn hF
  index_V := by
    rw [sp4Q₁_eq hn hF]
    exact relIndex_R1 hn hF
  index_Q₁ := by
    rw [sp4Q₁_eq hn hF]
    exact relIndex_R0 hn hF
  torus := by
    rw [sp4C_eq hn hF, sp4Z_eq hn hF, sp4K₂_eq hn hF, sp4Q₁_eq hn hF]
    exact sp4Torus_model hn hF
  coord := sp4Coord_one hn hF

theorem sp4ParConcl_Q0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Sp4ParConcl n ⊤ (Q2 F 0) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 0))) := by
  have h := (sp4ParConcl_Q1 hn hF).map (tauEquiv (F := F)).toMonoidHom
    (tauEquiv (F := F)).injective
  rwa [Subgroup.map_top_of_surjective (tauEquiv (F := F)).toMonoidHom
    (tauEquiv (F := F)).surjective, map_tau_Q1,
    CFSG.Quasithin.F134.Sp4.map_tauEquiv_unipotent, map_tau_R1] at h

omit [Finite F] [CharP F 2] in
theorem Q2_ne_top (j : Fin 2) : Q2 F j ≠ ⊤ := by
  intro h
  have hj := j.isLt
  have hw : weylRep F j ∈ Q2 F j := h ▸ Subgroup.mem_top _
  rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by omega)] at hw
  exact hw rfl

theorem eq_R (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2) {V : Subgroup (StatedSp 2 F)}
    (hV : V ≤ pCoreOf 2 (perfectCore (Q2 F j)))
    (hN : perfectCore (Q2 F j) ≤ Subgroup.normalizer (V : Set (StatedSp 2 F)))
    (hC : ¬ perfectCore (Q2 F j) ≤ Subgroup.centralizer (V : Set (StatedSp 2 F))) :
    V = pCoreOf 2 (perfectCore (Q2 F j)) := by
  rcases fin_two_cases j with rfl | rfl
  · exact eq_of_sp4Coord (sp4Coord_zero hn hF) (commutator_pCoreOf_perfectCore_Q2 hn hF 0) hV hN
      hC
  · exact eq_of_sp4Coord (sp4Coord_one hn hF) (commutator_pCoreOf_perfectCore_Q2 hn hF 1) hV hN
      hC

theorem sp4ParConcl_Qj (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2)
    {V : Subgroup (StatedSp 2 F)} (hV : V ≤ pCoreOf 2 (perfectCore (Q2 F j)))
    (hN : perfectCore (Q2 F j) ≤ Subgroup.normalizer (V : Set (StatedSp 2 F)))
    (hC : ¬ perfectCore (Q2 F j) ≤ Subgroup.centralizer (V : Set (StatedSp 2 F))) :
    Sp4ParConcl n ⊤ (Q2 F j) (unipotent 2 F) V := by
  rw [eq_R hn hF j hV hN hC]
  rcases fin_two_cases j with rfl | rfl
  · exact sp4ParConcl_Q0 hn hF
  · exact sp4ParConcl_Q1 hn hF

theorem model_main (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {P S V : Subgroup (StatedSp 2 F)}
    (hP : IsMaxParabolic2 ⊤ P) (hS : IsSylowTwoOf S P) (hV : V ≤ pCoreOf 2 (perfectCore P))
    (hN : perfectCore P ≤ Subgroup.normalizer (V : Set (StatedSp 2 F)))
    (hC : ¬ perfectCore P ≤ Subgroup.centralizer (V : Set (StatedSp 2 F))) :
    Sp4ParConcl n ⊤ P S V := by
  obtain ⟨S₁, hS₁, hNS₁, hcov⟩ := exists_sylow_of_isMaxParabolic2 hP
  have hS₁P : S₁ ≤ P := Subgroup.le_normalizer.trans hNS₁
  have hPodd : ¬ 2 ∣ P.relIndex ⊤ := by
    intro h2
    apply hS₁.2.2
    change 2 ∣ S₁.relIndex ⊤
    rw [← Subgroup.relIndex_mul_relIndex S₁ P ⊤ hS₁P le_top]
    exact Dvd.dvd.mul_left h2 _
  have hSsyl : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hS.2.1, ?_⟩
    change ¬ 2 ∣ S.relIndex ⊤
    rw [← Subgroup.relIndex_mul_relIndex S P ⊤ hS.1 le_top]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hS.2.2 h
    · exact hPodd h
  obtain ⟨g, hg⟩ := NQCat.exists_conj_map_eq hSsyl CFSG.Quasithin.F134.Sp4.isSylowTwoOf_unipotent
  have hUP : unipotent 2 F ≤ P.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono hS.1
  have hcov' : P.map (MulAut.conj g).toMonoidHom ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective]
    exact (apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))).mpr hcov
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, P.map (MulAut.conj g).toMonoidHom = Q2 F j := by
    have hle : ∃ j : Fin 2, P.map (MulAut.conj g).toMonoidHom ≤ Q2 F j := by
      rcases contained_in_Q2 hUP hcov'.lt.ne with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨j, hj⟩ := hle
    refine ⟨j, ?_⟩
    rcases hcov'.eq_or_eq hj le_top with h | h
    · exact h.symm
    · exact absurd h (Q2_ne_top j)
  have hmapP : perfectCore (Q2 F j) = (perfectCore P).map (MulAut.conj g).toMonoidHom := by
    rw [← hj, CFSG.Quasithin.map_perfectCore]
  have hV' : V.map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 (perfectCore (Q2 F j)) := by
    rw [hmapP, pCoreOf_map_of_injective _ (MulAut.conj g).injective]
    exact Subgroup.map_mono hV
  have hN' : perfectCore (Q2 F j) ≤
      Subgroup.normalizer (V.map (MulAut.conj g).toMonoidHom : Set (StatedSp 2 F)) := by
    rw [hmapP]
    exact map_le_normalizer _ (MulAut.conj g).injective hN
  have hC' : ¬ perfectCore (Q2 F j) ≤
      Subgroup.centralizer (V.map (MulAut.conj g).toMonoidHom : Set (StatedSp 2 F)) := by
    intro h
    apply hC
    rw [hmapP] at h
    have := map_le_centralizer (MulAut.conj g).symm.toMonoidHom (MulAut.conj g).symm.injective h
    rwa [Vol2Native.A312L.map_map_symm, Vol2Native.A312L.map_map_symm] at this
  have h := (sp4ParConcl_Qj hn hF j hV' hN' hC').map (MulAut.conj g).symm.toMonoidHom
    (MulAut.conj g).symm.injective
  rwa [Subgroup.map_top_of_surjective (MulAut.conj g).symm.toMonoidHom
    (MulAut.conj g).symm.surjective, ← hj, ← hg, Vol2Native.A312L.map_map_symm,
    Vol2Native.A312L.map_map_symm, Vol2Native.A312L.map_map_symm] at h

end Sp4M

open L436

theorem sp4ParabolicFacts_holds : Sp4ParabolicFacts := by
  intro G _ _ n K P S V hn hK hP hS hV _ hN hC
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  let ψ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F)
      ⟨CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo,
        QuotientGroup.mk'_surjective _⟩
  let ι : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) →* G :=
    K.subtype.comp (ψ.trans e.symm).toMonoidHom
  have hι : Function.Injective ι := K.subtype_injective.comp (ψ.trans e.symm).injective
  have hrange : K = ι.range := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (ψ.trans e.symm).surjective ⟨x, hx⟩
      exact ⟨y, by rw [show ι y = ((ψ.trans e.symm) y : G) from rfl, hy]⟩
    · rintro ⟨y, rfl⟩
      exact ((ψ.trans e.symm) y).2
  have hPK : P ≤ ι.range := hrange ▸ hP.1.1
  have hSK : S ≤ ι.range := hS.1.trans hPK
  have hVK : V ≤ ι.range :=
    (hV.trans ((Subgroup.map_subtype_le _).trans (perfectCore_le P))).trans hPK
  have hcoreP : (perfectCore (P.comap ι)).map ι = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_comap_eq_self hPK]
  have hP' := isMaxParabolic2_comap ι hι hrange hP
  have hS' : IsSylowTwoOf (S.comap ι) (P.comap ι) := by
    apply isSylowTwoOf_of_map ι hι
    rw [Subgroup.map_comap_eq_self hSK, Subgroup.map_comap_eq_self hPK]
    exact hS
  have hV' : V.comap ι ≤ pCoreOf 2 (perfectCore (P.comap ι)) := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, Subgroup.map_comap_eq_self hVK,
      ← Lie2Parabolic.pCoreOf_map_of_injective ι hι, hcoreP]
    exact hV
  have hN' : perfectCore (P.comap ι) ≤
      Subgroup.normalizer (V.comap ι : Set ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
    have h1 := map_inf_normalizer ι hι (perfectCore (P.comap ι)) (V.comap ι)
    rw [hcoreP, Subgroup.map_comap_eq_self hVK, inf_eq_left.mpr hN, ← hcoreP] at h1
    rw [← Subgroup.map_injective hι h1]
    exact inf_le_right
  have hC' : ¬ perfectCore (P.comap ι) ≤
      Subgroup.centralizer (V.comap ι : Set ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
    intro h
    apply hC
    have := map_le_centralizer ι hι h
    rwa [hcoreP, Subgroup.map_comap_eq_self hVK] at this
  have h := (Sp4M.model_main hn hF hP' hS' hV' hN' hC').map ι hι
  rwa [← MonoidHom.range_eq_map, ← hrange, Subgroup.map_comap_eq_self hPK,
    Subgroup.map_comap_eq_self hSK, Subgroup.map_comap_eq_self hVK] at h

end CFSG.Quasithin.H13.Ch4
