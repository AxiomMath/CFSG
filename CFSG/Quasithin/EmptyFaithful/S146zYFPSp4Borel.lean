module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.EmptyFaithful.S146zYFPSp4Flag
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main

public section

namespace CFSG.Quasithin.S146zY

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher SymplecticFour Submodule
open CFSG.Quasithin.F134.Sp4
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv)

variable {K : Type} [Field K]

local notation "M[" g "]" => Units.val (Subtype.val g)

theorem false_of_le_stabilizer_two_five [Finite K] [CharP K 2] {P : Subgroup (StatedSp 2 K)}
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hP25 : Nat.card P = 25)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) (hq5 : ¬ 5 ∣ Nat.card K) (hq51 : ¬ 5 ∣ Nat.card K - 1) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Q := P.subgroupOf (stabilizer 2 K (flag 2 K 2))
  let ρ : Q →* GL (Fin 2) K := (blockHom (K := K)).toHomUnits.comp Q.subtype
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have h1 : blockHom (q : stabilizer 2 K (flag 2 K 2)) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hq)
      simpa [ρ] using this
    have h2 := sq_eq_one_of_blockHom (q : stabilizer 2 K (flag 2 K 2)) h1
    have h5 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) ^ 5 = 1 :=
      hexp _ (Subgroup.mem_subgroupOf.mp q.2)
    have hq1 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) = 1 := by
      calc ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K)
          = ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) ^ 5 *
            (((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) ^ 2)⁻¹ ^ 2 := by group
        _ = 1 := by rw [h2, h5]; simp
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext hq1)
  have hQ25 : Nat.card Q = 25 := by
    rw [← hP25]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv
  have hR25 : Nat.card ρ.range = 25 := by
    rw [← hQ25]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hRexp : ∀ x ∈ ρ.range, x ^ 5 = 1 := by
    rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have : q ^ 5 = 1 := Subtype.ext (Subtype.ext (hexp _ (Subgroup.mem_subgroupOf.mp q.2)))
    rw [this, map_one]
  have hR5 : IsPGroup 5 ρ.range := IsPGroup.of_card (n := 2) (by rw [hR25]; norm_num)
  exact not_isCyclic_of_card_twentyFive hR25 hRexp (isCyclic_of_isPGroup_GL_two hq5 hq51 hR5)

theorem le_stabilizer_one_of_le_stabilizer_two_five [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hP25 : Nat.card P ∣ 25)
    (hq : 5 ∣ Nat.card K - 1) : P ≤ stabilizer 2 K (flag 2 K 1) := by
  set e := (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with he
  have he0 : e ≠ 0 := single_inl_zero_ne_zero
  have heF : e ∈ flag 2 K 2 := by
    rw [mem_flag_two_iff]
    simp [he]
  suffices hfix : ∀ y ∈ P, M[y] *ᵥ e ∈ flag 2 K 1 by
    intro y hy
    refine mem_stabilizer_of_mulVec_mem' fun v hv => ?_
    rw [eq_smul_e1_of_mem_flag_one hv, mulVec_smul]
    exact Submodule.smul_mem _ _ (hfix y hy)
  by_contra hne
  obtain ⟨y₀, hy₀, hv₀⟩ := not_forall₂.mp hne
  set v := M[y₀] *ᵥ e with hv
  have hvF : v ∈ flag 2 K 2 := mulVec_mem_of_mem_stabilizer (hPF hy₀) heF
  obtain ⟨hv0, hv1⟩ := mem_flag_two_iff.mp hvF
  have hvl : v (Sum.inl 1) ≠ 0 := fun h => hv₀ (mem_flag_one_iff.mpr ⟨hv0, hv1, h⟩)
  set p₀ := SpPoint.ofVec e he0
  have hsmul : ∀ y : P, y • p₀ = SpPoint.ofVec (M[(y : StatedSp 2 K)] *ᵥ e)
      (fun h => he0 (spAct_injective (y : StatedSp 2 K) (h.trans (map_zero _).symm))) :=
    fun y => smul_ofVec (y : StatedSp 2 K) e he0
  have horbit : MulAction.orbit P p₀ = {M : SpPoint 2 K | M.line ≤ flag 2 K 2} := by
    ext Mp
    constructor
    · rintro ⟨y, rfl⟩
      change (y • p₀).line ≤ flag 2 K 2
      rw [hsmul y, line_ofVec, span_le, Set.singleton_subset_iff]
      exact mulVec_mem_of_mem_stabilizer (hPF y.2) heF
    · intro hM
      obtain ⟨w, hw, rfl⟩ := Mp.exists_ofVec
      have hwF : w ∈ flag 2 K 2 := by
        apply hM
        rw [line_ofVec]
        exact mem_span_singleton_self w
      obtain ⟨hw0, hw1⟩ := mem_flag_two_iff.mp hwF
      by_cases hwl : w (Sum.inl 1) = 0
      · have hw' : w = w (Sum.inl 0) • e := eq_smul_e1_of_mem_flag_one
          (mem_flag_one_iff.mpr ⟨hw0, hw1, hwl⟩)
        have hc : w (Sum.inl 0) ≠ 0 := fun h => hw (by rw [hw', h, zero_smul])
        refine ⟨1, ?_⟩
        change (1 : P) • p₀ = _
        rw [one_smul]
        exact (ofVec_smul_eq he0 hc (hw' ▸ hw)).symm.trans (by congr 1; exact hw'.symm)
      · set a := w (Sum.inl 0) / w (Sum.inl 1) - v (Sum.inl 0) / v (Sum.inl 1)
        obtain ⟨y, hy, hyv⟩ := exists_mulVec_e1 hPU (lam_mem_unipotent a) hy₀
        set c := v (Sum.inl 1) / w (Sum.inl 1)
        have hc : c ≠ 0 := div_ne_zero hvl hwl
        have hlam : M[lam a] *ᵥ v = c • w := by
          rw [lam_mulVec_of_mem_flag_two a hvF]
          ext i
          rcases i with i | i <;> fin_cases i <;> simp [c, a, hw0, hw1]
          · field_simp
            ring
          · field_simp
        refine ⟨⟨y, hy⟩, ?_⟩
        change (⟨y, hy⟩ : P) • p₀ = _
        rw [hsmul]
        have hcw : c • w ≠ 0 := smul_ne_zero hc hw
        refine (SpPoint.ext ?_).trans (ofVec_smul_eq hw hc hcw)
        rw [line_ofVec, line_ofVec]
        congr 1
        rw [Set.singleton_eq_singleton_iff]
        change M[y] *ᵥ e = c • w
        rw [hyv, ← hlam]
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hpts : Nat.card {M : SpPoint 2 K // M.line ≤ flag 2 K 2} = Nat.card K + 1 := by
    have h := card_pointsLe_mul (flag 2 K 2)
    rw [finrank_flag (by norm_num)] at h
    have h2 := Nat.sq_sub_sq (Nat.card K) 1
    rw [one_pow] at h2
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hcardO : Nat.card (MulAction.orbit P p₀) = Nat.card K + 1 := by
    rw [horbit]
    exact hpts
  have hdvd : Nat.card (MulAction.orbit P p₀) ∣ Nat.card P := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  rw [hcardO] at hdvd
  have h25 := hdvd.trans hP25
  have hle := Nat.le_of_dvd (by norm_num) h25
  have hK24 : Nat.card K ≤ 24 := by omega
  obtain ⟨k, hk⟩ := h25
  interval_cases h : Nat.card K <;> omega

theorem le_borelSubgroup_of_le_stabilizer_two_five [Finite K] [CharP K 2]
    {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hP25 : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) (hq5 : ¬ 5 ∣ Nat.card K)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) : P ≤ borelSubgroup 2 K ∧ 5 ∣ Nat.card K - 1 := by
  have h5 : 5 ∣ Nat.card K - 1 := by
    by_contra h
    exact false_of_le_stabilizer_two_five hPF hP25 hexp hq5 h
  refine ⟨fun y hy => mem_borelSubgroup_iff.mpr ⟨?_, hPF hy⟩, h5⟩
  exact le_stabilizer_one_of_le_stabilizer_two_five hPU hPF (by rw [hP25]) h5 hy

theorem le_borelSubgroup_of_mul_five [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hP25 : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) :
    P ≤ borelSubgroup 2 K ∧ 5 ∣ Nat.card K - 1 := by
  have hq5 : ¬ 5 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    intro h
    have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  have hcard : Nat.card P < Nat.card K ^ 3 := by
    rw [hP25]
    calc 25 < 4 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK 3
  obtain ⟨d, hd, hPd⟩ := exists_le_stabilizer_flag_of_card_lt_cube hPU hcard
  rcases hd with rfl | rfl
  ·
    set τ := (tauEquiv (F := K)).toMonoidHom with hτ
    have hτF : P.map τ ≤ stabilizer 2 K (flag 2 K 2) := by
      rintro _ ⟨y, hy, rfl⟩
      exact tauSp_mem_stabilizer_two (hPd hy)
    have hτ25 : Nat.card (P.map τ) = 25 := by
      rw [Subgroup.card_map_of_injective (f := τ) (tauEquiv (F := K)).injective, hP25]
    have hτexp : ∀ x ∈ P.map τ, x ^ 5 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hexp y hy, map_one]
    have hτU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P.map τ, ∃ y ∈ P.map τ, ∃ s ∈ unipotent 2 K,
        u * x = y * s := by
      intro u hu x hx
      rw [← map_tauEquiv_unipotent] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, s, hs, hzs⟩ := hPU u' hu' y hy
      refine ⟨τ z, ⟨z, hz, rfl⟩, τ s, ?_, by rw [← map_mul, hzs, map_mul]⟩
      rw [← map_tauEquiv_unipotent]
      exact ⟨s, hs, rfl⟩
    obtain ⟨hB, h5⟩ := le_borelSubgroup_of_le_stabilizer_two_five hτU hτ25 hτexp hq5 hτF
    refine ⟨fun y hy => ?_, h5⟩
    have hy' : τ y ∈ borelSubgroup 2 K := hB ⟨y, hy, rfl⟩
    rw [← map_tauEquiv_borelSubgroup] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    rwa [(tauEquiv (F := K)).injective hzy] at hz
  · exact le_borelSubgroup_of_le_stabilizer_two_five hPU hP25 hexp hq5 hPd

end CFSG.Quasithin.S146zY
